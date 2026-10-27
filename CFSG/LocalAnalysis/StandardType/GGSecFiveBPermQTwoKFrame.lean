module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
import CFSG.LocalAnalysis.StandardType.GGFFSLSylow
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Frame
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKSigned
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent

public section

namespace CFSG.StandardType

open Polynomial Multiplicative
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem qtwoK_exists_hom {M : Type} [Group M] {Bs K : Subgroup G} {D : M →* G}
    (hD : Function.Injective D) (hDK : ∀ t, D t ∈ K)
    (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1)
    (htor : ∀ b ∈ Bs, ∃ t, ∀ x ∈ K, b * x * b⁻¹ = D t * x * (D t)⁻¹) :
    ∃ T : ↥Bs →* M,
      ∀ (b : ↥Bs), ∀ x ∈ K, (b : G) * x * (b : G)⁻¹ = D (T b) * x * (D (T b))⁻¹ := by
  choose t ht using htor
  have huniq : ∀ (b : ↥Bs) (u : M),
      (∀ x ∈ K, (b : G) * x * (b : G)⁻¹ = D u * x * (D u)⁻¹) → u = t b b.2 := by
    intro b u hu
    have hz : (D (t b b.2))⁻¹ * D u = 1 := by
      refine hZ _ (K.mul_mem (K.inv_mem (hDK _)) (hDK _)) fun x hx => ?_
      have h1 : D u * x * (D u)⁻¹ = D (t b b.2) * x * (D (t b b.2))⁻¹ := by
        rw [← hu x hx, ht b b.2 x hx]
      calc (D (t b b.2))⁻¹ * D u * x
          = (D (t b b.2))⁻¹ * (D u * x * (D u)⁻¹) * D u := by group
        _ = (D (t b b.2))⁻¹ * (D (t b b.2) * x * (D (t b b.2))⁻¹) * D u := by rw [h1]
        _ = x * ((D (t b b.2))⁻¹ * D u) := by group
    exact hD (inv_mul_eq_one.mp hz).symm
  refine ⟨MonoidHom.mk' (fun b => t b b.2) fun b c => (huniq (b * c) _ fun x hx => ?_).symm,
    fun b => ht b b.2⟩
  have hcx : (c : G) * x * (c : G)⁻¹ ∈ K := by
    rw [ht c c.2 x hx]
    exact K.mul_mem (K.mul_mem (hDK _) hx) (K.inv_mem (hDK _))
  calc ((b * c : ↥Bs) : G) * x * ((b * c : ↥Bs) : G)⁻¹
      = (b : G) * ((c : G) * x * (c : G)⁻¹) * (b : G)⁻¹ := by
        rw [Subgroup.coe_mul]
        group
    _ = D (t b b.2) * (D (t c c.2) * x * (D (t c c.2))⁻¹) * (D (t b b.2))⁻¹ := by
        rw [ht b b.2 _ hcx, ht c c.2 x hx]
    _ = D (t b b.2 * t c c.2) * x * (D (t b b.2 * t c c.2))⁻¹ := by
        rw [map_mul]
        group

private theorem qtwoK_card_le [Finite G] {M : Type} [Group M] {Bs K : Subgroup G}
    (T : ↥Bs →* M)
    (hker : ∀ b : ↥Bs, T b = 1 → (b : G) ∈ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) * Nat.card T.range := by
  have hker_card : Nat.card T.ker ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun b : T.ker => ⟨(b.1 : G), b.1.2, hker b.1 (MonoidHom.mem_ker.mp b.2)⟩) ?_
    intro b c h
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) => (z : G)) h))
  calc Nat.card ↥Bs = Nat.card T.ker * Nat.card T.range := by
        rw [← Subgroup.index_ker T]
        exact (Subgroup.card_mul_index T.ker).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hker_card

theorem ggSecFiveBPermQTwoK_exists_frame [Finite G]
    {n r m : ℕ} (hrn : r + 2 = n) (hr : 2 ≤ r) (hm : m = 2 * r + 2 ∨ m = 2 * r + 3)
    {Bs K : Subgroup G} (hNK : Bs ≤ Subgroup.normalizer (K : Set G)) (θ : ↥K ≃* SL(m, ZMod 2))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0) :
    ∃ π : Fin (r + 2) ≃ Fin n, π 0 = i0 ∧
      ∃ (g : (ZMod 2)[X]) (_ : Fact (Irreducible g)) (d : ℕ)
        (ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin (r + 1)) ⊕ Fin d)
        (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
        (κ : SL(m, ZMod 2) →* G),
        (CoordSL.rootPB g).dim = 2 ∧ d ≤ 1 ∧ GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ := by
  classical
  subst hrn
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : SL(m, ZMod 2) →* G, ∀ u, κ₀ u = ((θ.symm u : ↥K) : G) :=
    ⟨K.subtype.comp θ.symm.toMonoidHom, fun _ => rfl⟩
  have hκ₀inj : Function.Injective κ₀ := by
    intro u v huv
    rw [hκ₀, hκ₀] at huv
    exact θ.symm.injective (Subtype.ext huv)
  have hκ₀K : ∀ u, κ₀ u ∈ K := fun u => by
    rw [hκ₀]
    exact (θ.symm u).2
  have hκ₀θ : ∀ x (hx : x ∈ K), κ₀ (θ ⟨x, hx⟩) = x := fun x hx => by
    rw [hκ₀, MulEquiv.symm_apply_apply]
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hZ : Subgroup.center SL(m, ZMod 2) = ⊥ := LineL2.center_eq_bot_two hK2
  have hZK : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1 := by
    intro z hz hc
    have hw : θ ⟨z, hz⟩ ∈ Subgroup.center SL(m, ZMod 2) := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply hκ₀inj
      rw [map_mul, map_mul, hκ₀θ]
      exact (hc _ (hκ₀K u)).symm
    rw [hZ, Subgroup.mem_bot] at hw
    have h1 := hκ₀θ z hz
    rw [hw, map_one] at h1
    exact h1.symm
  have hb3 : ∀ b ∈ Bs, b ^ 3 = 1 := by
    intro b hb
    have h1 : (⟨b, hb⟩ : ↥Bs) ^ 3 = 1 := by
      apply eta.injective
      rw [map_pow, map_one]
      funext i
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
    simpa using congrArg Subtype.val h1
  have hBcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b := by
    intro b hb c hc
    have h1 : (⟨b, hb⟩ : ↥Bs) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨b, hb⟩ :=
      eta.injective (by rw [map_mul, map_mul, mul_comm])
    simpa using congrArg Subtype.val h1
  have hm3 : 3 ≤ m := by omega
  have hinner : ∀ b ∈ Bs, ∃ h : SL(m, ZMod 2), ∀ u, b * κ₀ u * b⁻¹ = κ₀ (h * u * h⁻¹) := by
    intro b hb
    let β : ↥(Subgroup.normalizer (K : Set G)) := ⟨b, hNK hb⟩
    have hβ : β ^ 3 = 1 := Subtype.ext (by simpa [β] using hb3 b hb)
    have hα : MulAut.congr θ (K.normalizerMonoidHom β) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hβ, map_one, map_one]
    obtain ⟨h, hh⟩ := GGFF.inner_odd_SL hm3 _ 3 (by decide) hα
    refine ⟨h, fun u => ?_⟩
    have h1 := congrArg (fun φ : MulAut SL(m, ZMod 2) => κ₀ (φ u)) hh
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply] at h1
    rw [← h1, hκ₀, hκ₀, MulEquiv.symm_apply_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  choose hb hhb using hinner
  have huniq : ∀ h h' : SL(m, ZMod 2), (∀ u, κ₀ (h * u * h⁻¹) = κ₀ (h' * u * h'⁻¹)) → h = h' := by
    intro h h' hh
    have hz : h'⁻¹ * h ∈ Subgroup.center SL(m, ZMod 2) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h1 := hκ₀inj (hh u)
      calc u * (h'⁻¹ * h) = h'⁻¹ * (h' * u * h'⁻¹) * h := by group
        _ = h'⁻¹ * (h * u * h⁻¹) * h := by rw [h1]
        _ = h'⁻¹ * h * u := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact (inv_mul_eq_one.mp hz).symm
  have hconj2 : ∀ (b c : G) (hb' : b ∈ Bs) (hc' : c ∈ Bs) (u : SL(m, ZMod 2)),
      (b * c) * κ₀ u * (b * c)⁻¹ = κ₀ ((hb b hb' * hb c hc') * u * (hb b hb' * hb c hc')⁻¹) := by
    intro b c hb' hc' u
    calc (b * c) * κ₀ u * (b * c)⁻¹ = b * (c * κ₀ u * c⁻¹) * b⁻¹ := by group
      _ = κ₀ (hb b hb' * (hb c hc' * u * (hb c hc')⁻¹) * (hb b hb')⁻¹) := by
          rw [hhb c hc' u, hhb b hb']
      _ = κ₀ ((hb b hb' * hb c hc') * u * (hb b hb' * hb c hc')⁻¹) := by
          congr 1
          group
  have hcomm : ∀ (b c : G) (hb' : b ∈ Bs) (hc' : c ∈ Bs),
      hb b hb' * hb c hc' = hb c hc' * hb b hb' := by
    intro b c hb' hc'
    refine huniq _ _ fun u => ?_
    rw [← hconj2 b c hb' hc' u, ← hconj2 c b hc' hb' u, hBcomm b hb' c hc']
  have hpow3 : ∀ (b : G) (hb' : b ∈ Bs), hb b hb' ^ 3 = 1 := by
    intro b hb'
    refine huniq _ _ fun u => ?_
    calc κ₀ (hb b hb' ^ 3 * u * (hb b hb' ^ 3)⁻¹)
        = κ₀ (hb b hb' * (hb b hb' * (hb b hb' * u * (hb b hb')⁻¹) * (hb b hb')⁻¹) *
            (hb b hb')⁻¹) := by
          congr 1
          rw [pow_three']
          group
      _ = b * (b * (b * κ₀ u * b⁻¹) * b⁻¹) * b⁻¹ := by
          rw [hhb b hb' u, hhb b hb', hhb b hb']
      _ = b ^ 3 * κ₀ u * (b ^ 3)⁻¹ := by
          rw [pow_three']
          group
      _ = κ₀ (1 * u * 1⁻¹) := by rw [hb3 b hb']; simp
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three (ZMod 2)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hp3 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hnsplit : ¬ 3 ∣ Nat.card (ZMod 2) - 1 := by
    rw [hK2]
    decide
  have hC : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : CoordSL.rootMat g ^ 3 = 1 := CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : ZMod 2, IsUnit (CoordSL.rootMat g ^ j - c • 1) :=
    fun j hj c => CoordSL.isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd j hj c
  have he2 : 2 ≤ (CoordSL.rootPB g).dim :=
    LinTwoTv.two_le_rootPB_dim (fun c => hunit 1 (by decide) c)
  obtain ⟨s, d, ε, A₀, hframe⟩ := CoordSL.exists_frame g Nat.prime_three hp3 hgd
    (Set.range fun b : ↥Bs => ((hb b b.2 : SL(m, ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
    (by
      rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
      have h := congrArg (fun z : SL(m, ZMod 2) => (z : Matrix (Fin m) (Fin m) (ZMod 2)))
        (hcomm b c b.2 c.2)
      simpa [Commute, SemiconjBy] using h)
    (by
      rintro _ ⟨b, rfl⟩
      rw [← Matrix.SpecialLinearGroup.coe_pow, hpow3 b b.2, Matrix.SpecialLinearGroup.coe_one])
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : SL(m, ZMod 2) →* G, ∀ u, κ₁ u = κ₀ (A₀ * u * A₀⁻¹) :=
    ⟨SLRep.ggFrame κ₀ A₀, fun _ => rfl⟩
  have hκ₁inj : Function.Injective κ₁ := by
    intro u v huv
    rw [hκ₁, hκ₁] at huv
    simpa using hκ₀inj huv
  have hκ₁K : ∀ u, κ₁ u ∈ K := fun u => by
    rw [hκ₁]
    exact hκ₀K _
  have hκ₁range : κ₁.range = K := by
    refine le_antisymm (fun _ ⟨u, hu⟩ => hu ▸ hκ₁K u) fun x hx => ⟨A₀⁻¹ * θ ⟨x, hx⟩ * A₀, ?_⟩
    rw [hκ₁, show A₀ * (A₀⁻¹ * θ ⟨x, hx⟩ * A₀) * A₀⁻¹ = θ ⟨x, hx⟩ by group, hκ₀θ]
  have hι₁ : ∀ t : Fin s → ZMod 3, CoordSL.frameHom κ₁ 1 ε hC hCp (ofAdd t) =
      κ₁ (SLNS.nsSL ε hC fun i => (t i).val) := by
    intro t
    rw [CoordSL.frameHom_apply, one_mul, inv_one, mul_one]
  have hι₁inj : Function.Injective (CoordSL.frameHom κ₁ 1 ε hC hCp) := by
    refine CoordSL.frameHom_injective κ₁ 1 ε hC hCp ?_ (CoordSL.rootPB_dim_pos g) hunit
    intro u hu
    rw [hκ₁inj (hu.trans (map_one κ₁).symm)]
    exact Subgroup.one_mem _
  have hι₁K : ∀ t, CoordSL.frameHom κ₁ 1 ε hC hCp t ∈ K := fun t => by
    rw [← ofAdd_toAdd t, hι₁]
    exact hκ₁K _
  have htor : ∀ b ∈ Bs, ∃ t, ∀ x ∈ K, b * x * b⁻¹ =
      CoordSL.frameHom κ₁ 1 ε hC hCp t * x * (CoordSL.frameHom κ₁ 1 ε hC hCp t)⁻¹ := by
    intro b hb'
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb'⟩, rfl⟩
    have hh : hb b hb' = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
      have h1 : hb b hb' * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
      rw [← h1, mul_inv_cancel_right]
    refine ⟨ofAdd fun i => (k i : ZMod 3), fun x hx => ?_⟩
    have hι : CoordSL.frameHom κ₁ 1 ε hC hCp (ofAdd fun i => (k i : ZMod 3)) = κ₀ (hb b hb') := by
      rw [CoordSL.frameHom_natCast, SLRep.ggFrame_apply, one_mul, inv_one, mul_one, hκ₁, hh]
    rw [hι, ← hκ₀θ x hx, hhb b hb', map_mul, map_mul, map_inv]
  obtain ⟨T, hT⟩ := qtwoK_exists_hom hι₁inj hι₁K hZK htor
  have hTker : ∀ b : ↥Bs, T b = 1 → (b : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro b hb1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hT b x hx
    rw [hb1, map_one, one_mul, inv_one, mul_one] at h
    calc x * (b : G) = ((b : G) * x * (b : G)⁻¹) * b := by rw [h]
      _ = (b : G) * x := by group
  have hcent := ggSecFiveBPermSpK_card_inf_centralizer_le (by decide : (3 : ℕ) ≠ 2) hA
  have hcardBs : Nat.card ↥Bs = 3 ^ (r + 2) := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_fin]
  have hcardM : Nat.card (Multiplicative (Fin s → ZMod 3)) = 3 ^ s := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hle := qtwoK_card_le T hTker
  have hrange_le : Nat.card T.range ≤ 3 ^ s := by
    rw [← hcardM]
    exact Nat.card_le_card_of_injective (Subgroup.subtype T.range)
      (Subgroup.subtype_injective T.range)
  have hs1 : r + 1 ≤ s := by
    have h1 : 3 ^ (r + 2) ≤ 3 ^ (s + 1) := by
      calc 3 ^ (r + 2) = Nat.card ↥Bs := hcardBs.symm
        _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) * Nat.card T.range := hle
        _ ≤ 3 * 3 ^ s := Nat.mul_le_mul hcent hrange_le
        _ = 3 ^ (s + 1) := by ring
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  have hcardm : m = (CoordSL.rootPB g).dim * s + d := by
    have h := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod] using h
  have hs : s = r + 1 := by
    refine le_antisymm ?_ hs1
    have : 2 * s ≤ m := by nlinarith
    omega
  subst hs
  have hdim : (CoordSL.rootPB g).dim = 2 := by
    by_contra hne
    have h3 : 3 * (r + 1) ≤ (CoordSL.rootPB g).dim * (r + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hd : d ≤ 1 := by
    rw [hdim] at hcardm
    omega
  have hTs : Function.Surjective T := by
    have hge : 3 ^ (r + 1) ≤ Nat.card T.range := by
      have h1 : 3 * 3 ^ (r + 1) ≤ 3 * Nat.card T.range := by
        calc 3 * 3 ^ (r + 1) = Nat.card ↥Bs := by rw [hcardBs]; ring
          _ ≤ _ := hle
          _ ≤ 3 * Nat.card T.range := Nat.mul_le_mul_right _ hcent
      exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
    refine MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq T.range ?_)
    rw [hcardM]
    exact le_antisymm hrange_le hge
  obtain ⟨π', hπ'0, σ', hσ', halign⟩ := ggSecFiveBPermQTwoK_exists_align hK2 hgd hr hκ₁inj
    hκ₁range ε 1 hC hCp eta hA T hTs fun b u => hT b (κ₁ u) (hκ₁K u)
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  have hσ0 : ∀ k, σ' k ≠ 0 := by
    intro k
    rcases hσ' k with h | h <;> rw [h] <;> decide
  let ηu : Fin (r + 1) → (ZMod 3)ˣ := fun k => Units.mk0 (σ' k) (hσ0 k)
  have hη : ∀ k, ηu k ∈ CoordSL.galExp g hζ := by
    intro k
    have hpm : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide
    rcases hpm (ηu k) with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact LineL2.neg_one_mem_galExp hK2 hζ
  obtain ⟨M, hM⟩ := CoordSL.exists_conj_frameHom g κ₁ 1 ε hC hCp hζ (Equiv.refl _) ηu hη
  obtain ⟨κ, hκ⟩ : ∃ κ : SL(m, ZMod 2) →* G, ∀ u, κ u = κ₁ (M⁻¹ * u * M) :=
    ⟨SLRep.ggFrame κ₁ M⁻¹, fun u => by rw [SLRep.ggFrame_apply, inv_inv]⟩
  have hκinj : Function.Injective κ := by
    intro u v huv
    rw [hκ, hκ] at huv
    simpa using hκ₁inj huv
  have hκK : ∀ u, κ u ∈ K := fun u => by
    rw [hκ]
    exact hκ₁K _
  have hκrange : κ.range = K := by
    refine le_antisymm (fun _ ⟨u, hu⟩ => hu ▸ hκK u) fun x hx => ?_
    rw [← hκ₁range] at hx
    obtain ⟨v, rfl⟩ := hx
    exact ⟨M * v * M⁻¹, by rw [hκ, show M⁻¹ * (M * v * M⁻¹) * M = v by group]⟩
  have hκι : ∀ t : Fin (r + 1) → ZMod 3, CoordSL.frameHom κ 1 ε hC hCp (ofAdd t) =
      CoordSL.frameHom κ₁ 1 ε hC hCp (ofAdd fun i => (ηu i : ZMod 3) * t i) := by
    intro t
    have h := hM t
    simp only [Equiv.refl_apply] at h
    rw [← h, CoordSL.frameHom_apply, CoordSL.frameHom_apply, SLRep.ggFrame_apply, one_mul,
      inv_one, mul_one, one_mul, mul_one, hκ, map_mul, map_mul, map_inv]
  refine ⟨π', hπ'0, g, inferInstance, d, ε, hC, hCp, κ, hdim, hd, hκinj, hκrange, hgd,
    fun b u => ?_⟩
  have hcoord : CoordSL.frameHom κ 1 ε hC hCp (ggSecFiveBPermQTwoCoords eta π' b) =
      CoordSL.frameHom κ₁ 1 ε hC hCp (T b) := by
    rw [ggSecFiveBPermQTwoCoords, hκι]
    congr 1
    apply Multiplicative.toAdd.injective
    funext k
    simp only [toAdd_ofAdd, ηu, Units.val_mk0]
    exact (halign b k).symm
  rw [hcoord]
  exact hT b (κ u) (hκK u)

end CFSG.StandardType

end
