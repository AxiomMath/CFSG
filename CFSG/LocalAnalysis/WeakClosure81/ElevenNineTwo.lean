module

public import CFSG.LocalAnalysis.WeakClosure81.SLTwoNormalizer
public import CFSG.LocalAnalysis.WeakClosure81.ElevenNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open Matrix
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)
open CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.SL2Modules

variable {G : Type} [Group G] [Finite G]

private theorem eleven_nine_mem_centralizer_conjugate_iff {L : Subgroup G} {x y : G}
    (hx : conjugate L x = L) :
    y ∈ Subgroup.centralizer (L : Set G) ↔
      x * y * x⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have hxinv : conjugate L x⁻¹ = L := by
    have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
      eleven_nine_mem_normalizer_of_conjugate_eq hx
    apply le_antisymm
    · intro y hy
      rw [ThreeFromEight.mem_conjugate_iff] at hy
      have hy' : x⁻¹ * y * x ∈ L := by simpa using hy
      have h := (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * y * x)).mp hy'
      simpa [mul_assoc] using h
    · intro y hy
      rw [ThreeFromEight.mem_conjugate_iff]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hxN) y).mp hy
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro l hl
    have hl' : x⁻¹ * l * x ∈ L := by
      have hmem : x⁻¹ * l * x ∈ conjugate L x := by
        show x⁻¹ * l * x ∈ (L.map (MulAut.conj x⁻¹).toMonoidHom)
        exact Subgroup.mem_map.mpr ⟨l, hl, by simp [MulAut.conj_apply]⟩
      rwa [hx] at hmem
    have h := hy (x⁻¹ * l * x) hl'
    calc l * (x * y * x⁻¹) = x * ((x⁻¹ * l * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * l * x)) * x⁻¹ := by rw [h]
      _ = (x * y * x⁻¹) * l := by group
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro l hl
    have hl' : x * l * x⁻¹ ∈ L := by
      rw [← ThreeFromEight.mem_conjugate_iff, hx]
      exact hl
    have h := hy (x * l * x⁻¹) hl'
    calc l * y = x⁻¹ * ((x * l * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * l * x⁻¹)) * x := by rw [h]
      _ = y * l := by group

private theorem eleven_nine_conjugate_eq_self_of_le_centralizer {A V : Subgroup G} {q : G}
    (hA : A ≤ V) (hq : q ∈ Subgroup.centralizer (V : Set G)) :
    conjugate A q = A := by
  have hqinv : q⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.centralizer (V : Set G)).inv_mem hq
  apply le_antisymm
  · intro x hx
    rw [ThreeFromEight.mem_conjugate_iff] at hx
    have hxV : q * x * q⁻¹ ∈ V := hA hx
    have hfix : q⁻¹ * (q * x * q⁻¹) * q = q * x * q⁻¹ := by
      have hc := Subgroup.mem_centralizer_iff.mp hqinv (q * x * q⁻¹) hxV
      rw [← hc]; group
    have hxeq : x = q * x * q⁻¹ := by
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = q * x * q⁻¹ := hfix
    rw [hxeq]
    exact hx
  · intro x hx
    rw [ThreeFromEight.mem_conjugate_iff]
    have hc := Subgroup.mem_centralizer_iff.mp hq x (hA hx)
    have hfix : q * x * q⁻¹ = x := by rw [← hc]; group
    rw [hfix]; exact hx

private theorem eleven_nine_addEquiv_of_ker_invariant
    {A : Type*} [Group A] {W : Type*} [AddCommGroup W]
    (Ψ : A →* Multiplicative W) (hΨ : Function.Surjective Ψ)
    (α : A ≃* A) (hα : ∀ a : A, Ψ a = 1 ↔ Ψ (α a) = 1) :
    ∃ Φ : W ≃+ W, ∀ a : A,
      Φ (Multiplicative.toAdd (Ψ a)) = Multiplicative.toAdd (Ψ (α a)) := by
  classical
  have hmap : (Ψ.ker).map (α : A →* A) = Ψ.ker := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      show Ψ (α a) = 1
      exact (hα a).mp ha
    · intro hx
      refine ⟨α.symm x, ?_, by simp⟩
      show Ψ (α.symm x) = 1
      exact (hα (α.symm x)).mpr (by simpa using hx)
  let e : A ⧸ Ψ.ker ≃* Multiplicative W :=
    QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ
  let αq : A ⧸ Ψ.ker ≃* A ⧸ Ψ.ker :=
    QuotientGroup.congr Ψ.ker Ψ.ker α hmap
  let Φm : Multiplicative W ≃* Multiplicative W := e.symm.trans (αq.trans e)
  have he : ∀ a : A, e (QuotientGroup.mk a) = Ψ a := fun a => rfl
  have hαq : ∀ a : A, αq (QuotientGroup.mk a) = QuotientGroup.mk (α a) := fun a =>
    QuotientGroup.congr_mk Ψ.ker Ψ.ker α hmap a
  have hΦm : ∀ a : A, Φm (Ψ a) = Ψ (α a) := by
    intro a
    calc Φm (Ψ a) = e (αq (e.symm (Ψ a))) := rfl
      _ = e (αq (QuotientGroup.mk a)) := by
            rw [← he a, MulEquiv.symm_apply_apply]
      _ = e (QuotientGroup.mk (α a)) := by rw [hαq a]
      _ = Ψ (α a) := he (α a)
  refine ⟨AddEquiv.toMultiplicative.symm Φm, ?_⟩
  intro a
  show Multiplicative.toAdd (Φm (Multiplicative.ofAdd (Multiplicative.toAdd (Ψ a)))) =
    Multiplicative.toAdd (Ψ (α a))
  rw [ofAdd_toAdd, hΦm a]

private theorem eleven_nine_conjugate_eq_of_mem_normalizer {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) : conjugate L x = L := by
  apply le_antisymm
  · intro y hy
    rw [ThreeFromEight.mem_conjugate_iff] at hy
    exact (Subgroup.mem_normalizer_iff.mp hxN y).mpr hy
  · intro y hy
    rw [ThreeFromEight.mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy

private noncomputable def eleven_nine_conjEquiv (L : Subgroup G) (x : G)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) : ↥(blockU L) ≃* ↥(blockU L) where
  toFun u := ⟨x * (u : G) * x⁻¹, conj_mem_blockU hxN u.2⟩
  invFun u := ⟨x⁻¹ * (u : G) * x, by
    simpa using conj_mem_blockU ((Subgroup.normalizer (L : Set G)).inv_mem hxN) u.2⟩
  left_inv u := Subtype.ext (by group)
  right_inv u := Subtype.ext (by group)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem eleven_nine_conjEquiv_ker {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G))
    {n : ℕ} {ψ : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 n)}
    (hψker : ψ.ker = (blockZ L).subgroupOf (blockU L)) :
    ∀ u : ↥(blockU L), ψ u = 1 ↔ ψ (eleven_nine_conjEquiv L x hxN u) = 1 := by
  have hx : conjugate L x = L := eleven_nine_conjugate_eq_of_mem_normalizer hxN
  have hconjU : conjugate (blockU L) x = blockU L := by
    apply le_antisymm
    · intro y hy
      rw [ThreeFromEight.mem_conjugate_iff] at hy
      have h := conj_mem_blockU ((Subgroup.normalizer (L : Set G)).inv_mem hxN) hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y from by group] at h
    · intro y hy
      rw [ThreeFromEight.mem_conjugate_iff]
      exact conj_mem_blockU hxN hy
  have hconjC : conjugate (Subgroup.centralizer (L : Set G)) x =
      Subgroup.centralizer (L : Set G) := by
    ext y
    rw [ThreeFromEight.mem_conjugate_iff]
    exact (eleven_nine_mem_centralizer_conjugate_iff hx).symm
  have hconjZ : conjugate (blockZ L) x = blockZ L := by
    have hmap : conjugate (blockU L ⊓ Subgroup.centralizer (L : Set G)) x =
        conjugate (blockU L) x ⊓ conjugate (Subgroup.centralizer (L : Set G)) x := by
      show (blockU L ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
        (blockU L).map (MulAut.conj x⁻¹).toMonoidHom ⊓
          (Subgroup.centralizer (L : Set G)).map (MulAut.conj x⁻¹).toMonoidHom
      rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective]
    rw [blockZ, hmap, hconjU, hconjC]
  have hker : ∀ w : ↥(blockU L), ψ w = 1 ↔ (w : G) ∈ blockZ L := by
    intro w
    constructor
    · intro hw
      have h : w ∈ ψ.ker := hw
      rwa [hψker, Subgroup.mem_subgroupOf] at h
    · intro hw
      have h : w ∈ (blockZ L).subgroupOf (blockU L) := Subgroup.mem_subgroupOf.mpr hw
      rw [← hψker] at h
      exact h
  intro u
  have hiff : (u : G) ∈ blockZ L ↔ (eleven_nine_conjEquiv L x hxN u : G) ∈ blockZ L := by
    change (u : G) ∈ blockZ L ↔ x * (u : G) * x⁻¹ ∈ blockZ L
    rw [← ThreeFromEight.mem_conjugate_iff, hconjZ]
  exact (hker u).trans (hiff.trans (hker (eleven_nine_conjEquiv L x hxN u)).symm)

private theorem eleven_nine_normalizes_of_conjEquiv {L : Subgroup G} {n : ℕ}
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hαsurj : Function.Surjective α)
    {ψ : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 n)}
    (hψsurj : Function.Surjective ψ)
    (hψeq : ∀ (e : ↥L) (w : ↥(blockU L))
      (hw : (e : G) * (w : G) * (e : G)⁻¹ ∈ blockU L),
      ψ ⟨(e : G) * (w : G) * (e : G)⁻¹, hw⟩ =
        Multiplicative.ofAdd (((α e : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ w))))
    {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (Φ : (Fin 2 → GaloisField 2 n) ≃+ (Fin 2 → GaloisField 2 n))
    (hΦ : ∀ u : ↥(blockU L),
      Φ (Multiplicative.toAdd (ψ u)) =
        Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L x hxN u)))
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      ∀ w, Φ (g • w) = g' • Φ w := by
  obtain ⟨e, he⟩ := hαsurj g
  have hxe : x * (e : G) * x⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hxN (e : G)).mp e.2
  refine ⟨α ⟨x * (e : G) * x⁻¹, hxe⟩, fun w => ?_⟩
  obtain ⟨u, hu⟩ := hψsurj (Multiplicative.ofAdd w)
  have hwu : Multiplicative.toAdd (ψ u) = w := by rw [hu, toAdd_ofAdd]
  rw [← hwu]
  have hψconj : ∀ (e' : ↥L) (u' : ↥(blockU L))
      (h : (e' : G) * (u' : G) * (e' : G)⁻¹ ∈ blockU L),
      Multiplicative.toAdd (ψ ⟨(e' : G) * (u' : G) * (e' : G)⁻¹, h⟩) =
        (α e') • Multiplicative.toAdd (ψ u') := by
    intro e' u' h
    have := congrArg Multiplicative.toAdd (hψeq e' u' h)
    simpa [Matrix.SpecialLinearGroup.smul_def] using this
  have heu : (e : G) * (u : G) * (e : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer e.2) u.2
  have hxu : x * (u : G) * x⁻¹ ∈ blockU L := conj_mem_blockU hxN u.2
  have hconj : (x * (e : G) * x⁻¹) * (x * (u : G) * x⁻¹) * (x * (e : G) * x⁻¹)⁻¹ ∈
      blockU L := conj_mem_blockU (Subgroup.le_normalizer hxe) hxu
  have hg : g • Multiplicative.toAdd (ψ u) =
      Multiplicative.toAdd (ψ ⟨(e : G) * (u : G) * (e : G)⁻¹, heu⟩) := by
    rw [← he]
    exact (hψconj e u heu).symm
  calc Φ (g • Multiplicative.toAdd (ψ u))
      = Φ (Multiplicative.toAdd (ψ ⟨(e : G) * (u : G) * (e : G)⁻¹, heu⟩)) := by rw [hg]
    _ = Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L x hxN
          ⟨(e : G) * (u : G) * (e : G)⁻¹, heu⟩)) := hΦ _
    _ = Multiplicative.toAdd (ψ ⟨(x * (e : G) * x⁻¹) * (x * (u : G) * x⁻¹) *
          (x * (e : G) * x⁻¹)⁻¹, hconj⟩) := by
        apply congrArg Multiplicative.toAdd
        apply congrArg ψ
        apply Subtype.ext
        show x * ((e : G) * (u : G) * (e : G)⁻¹) * x⁻¹ =
          (x * (e : G) * x⁻¹) * (x * (u : G) * x⁻¹) * (x * (e : G) * x⁻¹)⁻¹
        group
    _ = (α ⟨x * (e : G) * x⁻¹, hxe⟩) •
          Multiplicative.toAdd (ψ ⟨x * (u : G) * x⁻¹, hxu⟩) :=
        hψconj ⟨x * (e : G) * x⁻¹, hxe⟩ ⟨x * (u : G) * x⁻¹, hxu⟩ hconj
    _ = (α ⟨x * (e : G) * x⁻¹, hxe⟩) • Φ (Multiplicative.toAdd (ψ u)) := by
        congr 1
        exact (hΦ u).symm

theorem eleven_nine_le_normalizer
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    Q ≤ Subgroup.normalizer (L : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQCV : Q ≤ Subgroup.centralizer (V : Set G) := hset.sylowQ.1.trans inf_le_right
  have hQCU : Q ≤ Subgroup.centralizer (U : Set G) := hQCV.trans (Subgroup.centralizer_le hU.1)
  have hchar : IsCharacteristicP 2 ↥(Subgroup.centralizer (U : Set G)) :=
    eleven_e hset.charTwo hU.2.1
      ((B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hU.1)
  intro q hq
  by_contra hne
  have hconj_ne : conjugate L q ≠ L := fun h => hne (eleven_nine_mem_normalizer_of_conjugate_eq h)
  set L' : Subgroup G := conjugate L q with hL'def
  have hL' : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' :=
    isBlockOfInX_conjugate hL (hQCU hq)
  have hcomm : ⁅L, L'⁆ = ⊥ :=
    distinct_blocks_commute_of_isBlockOfInX hchar hL hL' (Ne.symm hconj_ne)
  have hCL : L ≤ Subgroup.centralizer (L' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨D, hD⟩ := eleven_nine_exists_hall hset hU hL hLM h78
  have hcommVD_le_V : ⁅V, D⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    have hdv : d * v * d⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hset.normal (hD.1 hd).2) v).mp hv
    rw [show ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ from by group]
    exact V.mul_mem hv (V.inv_mem hdv)
  have hcommVD_le_U : ⁅V, D⁆ ≤ blockU L := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    exact ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp
      (eleven_nine_V_le_centralizerModCore hset hU hL h78 hv)).2 d (hD.1 hd).1
  have hconj_comm : conjugate ⁅V, D⁆ q = ⁅V, D⁆ :=
    eleven_nine_conjugate_eq_self_of_le_centralizer hcommVD_le_V (hQCV hq)
  have hle_L' : ⁅V, D⁆ ≤ L' := by
    have h1 : conjugate ⁅V, D⁆ q ≤ conjugate (blockU L) q :=
      CFSG.GroupTheory.conjugate_mono q hcommVD_le_U
    have h2 : conjugate (blockU L) q ≤ conjugate L q :=
      CFSG.GroupTheory.conjugate_mono q (blockU_le L)
    rw [hconj_comm] at h1
    rw [← hL'def] at h2
    exact h1.trans h2
  have hle_C : ⁅V, D⁆ ≤ Subgroup.centralizer (L : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hCL hl) x (hle_L' hx)).symm
  have hleZ : ⁅V, D⁆ ≤ blockZ L := le_inf hcommVD_le_U hle_C
  have hbot : ⁅V, D⁆ = ⊥ := by
    have h1 : ⁅V, D⁆ ⊓ blockZ L = ⁅V, D⁆ := inf_eq_left.mpr hleZ
    rw [eleven_nine_commutator_inf_blockZ_eq_bot hset hU hL hLM h78 hD] at h1
    exact h1.symm
  have hcard := eleven_nine_card_commutator_hall hset hU hL hLM h78 hD
  rw [hbot, Subgroup.card_bot] at hcard
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h78.1)
  omega

theorem eleven_nine_two
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    ∀ x ∈ Q, ∃ s ∈ L ⊓ Q, ∃ c ∈ Q ⊓ centralizerModCore L, x = s * c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hxQ
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  obtain ⟨D, hD⟩ := eleven_nine_exists_hall hset hU hL hLM h78
  obtain ⟨hfixed, hfix⟩ :=
    eleven_nine_fixed_line hset hU hL hLM h78 hD hαsurj hαker hαS hψker hψeq
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    eleven_nine_le_normalizer hset hU hL hLM h78 hxQ
  have hkerαx : ∀ u : ↥(blockU L),
      ψ u = 1 ↔ ψ (eleven_nine_conjEquiv L x hxN u) = 1 :=
    eleven_nine_conjEquiv_ker hxN hψker
  obtain ⟨Φx, hΦx⟩ :=
    eleven_nine_addEquiv_of_ker_invariant ψ hψsurj (eleven_nine_conjEquiv L x hxN) hkerαx
  have hψconj : ∀ (e : ↥L) (u : ↥(blockU L))
      (h : (e : G) * (u : G) * (e : G)⁻¹ ∈ blockU L),
      Multiplicative.toAdd (ψ ⟨(e : G) * (u : G) * (e : G)⁻¹, h⟩) =
        (α e) • Multiplicative.toAdd (ψ u) := by
    intro e u h
    have := congrArg Multiplicative.toAdd (hψeq e u h)
    simpa [Matrix.SpecialLinearGroup.smul_def] using this
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hset.sylowQ.1.trans inf_le_right)
  have hfixp : ∀ w ∈ p.submodule, Φx w = w := by
    intro w hw
    obtain ⟨u, huV, huψ⟩ := (hfix w).mpr hw
    have hxu : x * (u : G) * x⁻¹ = (u : G) := by
      have hc := Subgroup.mem_centralizer_iff.mp (hVcQ huV) x hxQ
      rw [hc]; group
    have hαu : eleven_nine_conjEquiv L x hxN u = u := by
      apply Subtype.ext
      show x * (u : G) * x⁻¹ = (u : G)
      exact hxu
    calc Φx w = Φx (Multiplicative.toAdd (ψ u)) := by rw [huψ]
      _ = Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L x hxN u)) := hΦx u
      _ = Multiplicative.toAdd (ψ u) := by rw [hαu]
      _ = w := huψ
  have horder : ∃ k : ℕ, ∀ w, (⇑Φx)^[2 ^ k] w = w := by
    obtain ⟨k, hk⟩ := (hset.sylowQ.2.1).exists_pow_pow_eq_one ⟨x, hxQ⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, fun w => ?_⟩
    obtain ⟨u, hu⟩ := hψsurj (Multiplicative.ofAdd w)
    have hwu : Multiplicative.toAdd (ψ u) = w := by rw [hu, toAdd_ofAdd]
    rw [← hwu]
    have hiter : ∀ m : ℕ, (⇑Φx)^[m] (Multiplicative.toAdd (ψ u)) =
        Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L (x ^ m)
          ((Subgroup.normalizer (L : Set G)).pow_mem hxN m) u)) := by
      intro m
      induction m with
      | zero =>
        apply congrArg Multiplicative.toAdd
        apply congrArg ψ
        apply Subtype.ext
        show (u : G) = x ^ 0 * (u : G) * (x ^ 0)⁻¹
        rw [pow_zero]
        group
      | succ m ih =>
        rw [Function.iterate_succ_apply', ih, hΦx]
        apply congrArg Multiplicative.toAdd
        apply congrArg ψ
        apply Subtype.ext
        show x * ((eleven_nine_conjEquiv L (x ^ m) _ u : G)) * x⁻¹ =
          x ^ (m + 1) * (u : G) * (x ^ (m + 1))⁻¹
        rw [show (eleven_nine_conjEquiv L (x ^ m) _ u : G) =
          x ^ m * (u : G) * (x ^ m)⁻¹ from rfl]
        rw [pow_succ]
        group
    rw [hiter]
    have hlast : eleven_nine_conjEquiv L (x ^ 2 ^ k)
        ((Subgroup.normalizer (L : Set G)).pow_mem hxN (2 ^ k)) u = u := by
      apply Subtype.ext
      show x ^ 2 ^ k * (u : G) * (x ^ 2 ^ k)⁻¹ = (u : G)
      rw [hxk]
      group
    rw [hlast]
  obtain ⟨g, hgmem, hgact⟩ :=
    exists_mem_rootGrp_of_normalizes_of_fix p Φx
      (fun g' => eleven_nine_normalizes_of_conjEquiv hαsurj hψsurj hψeq hxN Φx hΦx g')
      hfixp horder
  have hgS : g ∈ ((L ⊓ Q).subgroupOf L).map α := by rw [hαS]; exact hgmem
  obtain ⟨s, hs, hsα⟩ := Subgroup.mem_map.mp hgS
  have hsLQ : (s : G) ∈ L ⊓ Q := Subgroup.mem_subgroupOf.mp hs
  have hsL : (s : G) ∈ L := hsLQ.1
  have hsQ : (s : G) ∈ Q := hsLQ.2
  have hrel : ∀ u : ↥(blockU L),
      ψ (eleven_nine_conjEquiv L x hxN u) =
        ψ (eleven_nine_conjEquiv L (s : G) (Subgroup.le_normalizer hsL) u) := by
    intro u
    have h1 : Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L x hxN u)) =
        g • Multiplicative.toAdd (ψ u) := (hΦx u).symm.trans (hgact _)
    have h2 : g • Multiplicative.toAdd (ψ u) =
        Multiplicative.toAdd (ψ (eleven_nine_conjEquiv L (s : G)
          (Subgroup.le_normalizer hsL) u)) := by
      rw [← hsα]
      exact (hψconj s u (conj_mem_blockU (Subgroup.le_normalizer hsL) u.2)).symm
    exact Multiplicative.toAdd.injective (h1.trans h2)
  let c : G := (s : G)⁻¹ * x
  have hcQ : c ∈ Q := Q.mul_mem (Q.inv_mem hsQ) hxQ
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hsL)) hxN
  have hψc : ∀ (u : ↥(blockU L)) (hu : c * (u : G) * c⁻¹ ∈ blockU L),
      ψ ⟨c * (u : G) * c⁻¹, hu⟩ = ψ u := by
    intro u hu
    have hxu : x * (u : G) * x⁻¹ ∈ blockU L := conj_mem_blockU hxN u.2
    have hsxu : (s : G)⁻¹ * (x * (u : G) * x⁻¹) * ((s : G)⁻¹)⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer (L.inv_mem hsL)) hxu
    have h1 : c * (u : G) * c⁻¹ =
        (s : G)⁻¹ * (x * (u : G) * x⁻¹) * ((s : G)⁻¹)⁻¹ := by simp only [c]; group
    have h2 : Multiplicative.toAdd (ψ ⟨c * (u : G) * c⁻¹, hu⟩) =
        Multiplicative.toAdd (ψ ⟨(s : G)⁻¹ * (x * (u : G) * x⁻¹) * ((s : G)⁻¹)⁻¹,
          hsxu⟩) := by
      apply congrArg Multiplicative.toAdd
      apply congrArg ψ
      exact Subtype.ext h1
    have h3 : Multiplicative.toAdd (ψ ⟨(s : G)⁻¹ * (x * (u : G) * x⁻¹) * ((s : G)⁻¹)⁻¹,
          hsxu⟩) =
        (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) •
          Multiplicative.toAdd (ψ ⟨x * (u : G) * x⁻¹, hxu⟩) :=
      hψconj ⟨(s : G)⁻¹, L.inv_mem hsL⟩ ⟨x * (u : G) * x⁻¹, hxu⟩ hsxu
    have h4 : Multiplicative.toAdd (ψ ⟨x * (u : G) * x⁻¹, hxu⟩) =
        Multiplicative.toAdd (ψ ⟨(s : G) * (u : G) * (s : G)⁻¹,
          conj_mem_blockU (Subgroup.le_normalizer hsL) u.2⟩) :=
      congrArg Multiplicative.toAdd (hrel u)
    have h5 : Multiplicative.toAdd (ψ ⟨(s : G) * (u : G) * (s : G)⁻¹,
          conj_mem_blockU (Subgroup.le_normalizer hsL) u.2⟩) =
        (α ⟨(s : G), hsL⟩) • Multiplicative.toAdd (ψ u) :=
      hψconj ⟨(s : G), hsL⟩ u (conj_mem_blockU (Subgroup.le_normalizer hsL) u.2)
    have h6 : (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) •
        ((α ⟨(s : G), hsL⟩) • Multiplicative.toAdd (ψ u)) =
        Multiplicative.toAdd (ψ u) := by
      rw [← smul_assoc]
      have hmul : (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) • (α ⟨(s : G), hsL⟩) = 1 := by
        change (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) * (α ⟨(s : G), hsL⟩) = 1
        calc (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) * (α ⟨(s : G), hsL⟩)
            = α ((⟨(s : G)⁻¹, L.inv_mem hsL⟩ : ↥L) * ⟨(s : G), hsL⟩) :=
              (map_mul α _ _).symm
          _ = α 1 := by rw [show (⟨(s : G)⁻¹, L.inv_mem hsL⟩ : ↥L) * ⟨(s : G), hsL⟩ = 1 from
                Subtype.ext (by simp)]
          _ = 1 := map_one α
      rw [hmul, one_smul]
    exact Multiplicative.toAdd.injective <| by
      calc Multiplicative.toAdd (ψ ⟨c * (u : G) * c⁻¹, hu⟩)
          = Multiplicative.toAdd (ψ ⟨(s : G)⁻¹ * (x * (u : G) * x⁻¹) * ((s : G)⁻¹)⁻¹,
              hsxu⟩) := h2
        _ = (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) •
              Multiplicative.toAdd (ψ ⟨x * (u : G) * x⁻¹, hxu⟩) := h3
        _ = (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) •
              Multiplicative.toAdd (ψ ⟨(s : G) * (u : G) * (s : G)⁻¹,
                conj_mem_blockU (Subgroup.le_normalizer hsL) u.2⟩) := by rw [h4]
        _ = (α ⟨(s : G)⁻¹, L.inv_mem hsL⟩) •
              ((α ⟨(s : G), hsL⟩) • Multiplicative.toAdd (ψ u)) := by rw [h5]
        _ = Multiplicative.toAdd (ψ u) := h6
  have hψcinv : ∀ (u : ↥(blockU L)) (hu : c⁻¹ * (u : G) * c ∈ blockU L),
      ψ ⟨c⁻¹ * (u : G) * c, hu⟩ = ψ u := by
    intro u hu
    have h1 : c * (c⁻¹ * (u : G) * c) * c⁻¹ ∈ blockU L := conj_mem_blockU hcN hu
    have h2 := hψc ⟨c⁻¹ * (u : G) * c, hu⟩ h1
    have h3 : (⟨c * (c⁻¹ * (u : G) * c) * c⁻¹, h1⟩ : ↥(blockU L)) = u :=
      Subtype.ext (by group)
    have h4 : ψ ⟨c * (c⁻¹ * (u : G) * c) * c⁻¹, h1⟩ = ψ u := by rw [h3]
    exact h2.symm.trans h4
  have hcCM : c ∈ centralizerModCore L := by
    rw [mem_centralizerModCore_iff]
    refine ⟨hcN, fun l hl => ?_⟩
    have hcl : c * l * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN l).mp hl
    have hcll : c * l * c⁻¹ * l⁻¹ ∈ L := L.mul_mem hcl (L.inv_mem hl)
    have hαcl : α ⟨c * l * c⁻¹, hcl⟩ = α ⟨l, hl⟩ := by
      apply Subtype.ext
      apply Matrix.ext_of_mulVec_single
      intro j
      obtain ⟨u, hu⟩ := hψsurj (Multiplicative.ofAdd (Pi.single j 1))
      have hvu : Multiplicative.toAdd (ψ u) = Pi.single j 1 := by rw [hu, toAdd_ofAdd]
      have hclu : c * l * c⁻¹ * (u : G) * (c * l * c⁻¹)⁻¹ ∈ blockU L :=
        conj_mem_blockU (Subgroup.le_normalizer hcl) u.2
      have hcinvu : c⁻¹ * (u : G) * c ∈ blockU L := by
        simpa using conj_mem_blockU ((Subgroup.normalizer (L : Set G)).inv_mem hcN) u.2
      have hlc : l * (c⁻¹ * (u : G) * c) * l⁻¹ ∈ blockU L :=
        conj_mem_blockU (Subgroup.le_normalizer hl) hcinvu
      have hclc : c * (l * (c⁻¹ * (u : G) * c) * l⁻¹) * c⁻¹ ∈ blockU L :=
        conj_mem_blockU hcN hlc
      have hgoal : (α ⟨c * l * c⁻¹, hcl⟩) • Multiplicative.toAdd (ψ u) =
          (α ⟨l, hl⟩) • Multiplicative.toAdd (ψ u) := by
        calc (α ⟨c * l * c⁻¹, hcl⟩) • Multiplicative.toAdd (ψ u)
            = Multiplicative.toAdd (ψ ⟨c * l * c⁻¹ * (u : G) * (c * l * c⁻¹)⁻¹,
                hclu⟩) := (hψconj ⟨c * l * c⁻¹, hcl⟩ u hclu).symm
          _ = Multiplicative.toAdd (ψ ⟨c * (l * (c⁻¹ * (u : G) * c) * l⁻¹) * c⁻¹,
                hclc⟩) := by
              apply congrArg Multiplicative.toAdd
              apply congrArg ψ
              exact Subtype.ext (by group)
          _ = Multiplicative.toAdd (ψ ⟨l * (c⁻¹ * (u : G) * c) * l⁻¹, hlc⟩) :=
              congrArg Multiplicative.toAdd (hψc ⟨l * (c⁻¹ * (u : G) * c) * l⁻¹, hlc⟩ hclc)
          _ = (α ⟨l, hl⟩) • Multiplicative.toAdd (ψ ⟨c⁻¹ * (u : G) * c, hcinvu⟩) :=
              hψconj ⟨l, hl⟩ ⟨c⁻¹ * (u : G) * c, hcinvu⟩ hlc
          _ = (α ⟨l, hl⟩) • Multiplicative.toAdd (ψ u) := by rw [hψcinv u hcinvu]
      rw [← hvu]
      simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using hgoal
    have hker : (⟨c * l * c⁻¹ * l⁻¹, hcll⟩ : ↥L) ∈ α.ker := by
      show α ⟨c * l * c⁻¹ * l⁻¹, hcll⟩ = 1
      have hprod : (⟨c * l * c⁻¹ * l⁻¹, hcll⟩ : ↥L) =
          ⟨c * l * c⁻¹, hcl⟩ * ⟨l, hl⟩⁻¹ := Subtype.ext (by simp [Subgroup.coe_mul])
      rw [hprod, map_mul, map_inv, hαcl, mul_inv_cancel]
    rw [hαker'] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  exact ⟨(s : G), hsLQ, c, ⟨hcQ, hcCM⟩, by simp only [c]; group⟩

end CFSG.LocalAnalysis.WeakClosure81
