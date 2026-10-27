module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4Nor
public import CFSG.Quasithin.Vol2.KGFactC31J4
import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4M4
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

variable {A : Type} [Group A]

theorem summand_of_card_ten [Finite A] {M₀ R V : Subgroup A} (hV : Nat.card V = 2 ^ 10) :
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k →
      k ≤ 2 := by
  intro m k hm _ h
  obtain ⟨-, -, -, -, -, β, hβ, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have hcard := Nat.card_eq_of_bijective β ⟨hinj, hβ⟩
  have hc : Nat.card (Multiplicative (Fin k → Fin m → ZMod 2)) = 2 ^ (k * m) := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card, ← pow_mul, mul_comm]
  rw [hc, hV] at hcard
  have h10 := Nat.pow_right_injective (le_refl 2) hcard
  rcases hm with rfl | rfl <;> omega

theorem isQuasisimple_statedSL5 :
    CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 4) (by norm_num) (ZMod 2)

theorem concl_of_L5block [Finite A] {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V)
    {H E : Subgroup A} (hEH : E ≤ H) (hEn : H ≤ Subgroup.normalizer (E : Set A))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 2 ^ 10)
    (hmin : ∀ N : Subgroup A, N ≤ E → H ≤ Subgroup.normalizer (N : Set A) → N = ⊥ ∨ N = E)
    (hmax : ∀ N : Subgroup A, E ≤ N → N ≤ H → H ≤ Subgroup.normalizer (N : Set A) →
      N = E ∨ N = H)
    (hCE : H ⊓ Subgroup.centralizer (E : Set A) ≤ E)
    (ψ : ↥H →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) (hψ : Function.Surjective ψ)
    (hψk : ψ.ker = E.subgroupOf H) (hM₀H : M₀ ≤ H) (hHM : H ≤ M) : Concl S M₀ R M V := by
  have hM₀eq : M₀ = H := eq_of_perfect_normal hEH hEn hcomm hmin hmax hCE hM₀H
    (hHM.trans h.hMN) h.hper h.hM₀ne
  have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
    exact hsq g g.2)⟩
  have hH2 : ¬ IsPGroup 2 ↥H := fun h2 =>
    h.hM₀ne (eq_bot_of_perfect_of_isPGroup h.hper (by rw [hM₀eq]; exact h2))
  have hOE : pCoreOf 2 H = E := pCoreOf_eq_of_max hEH hEn hE2 hmax hH2
  have hVE : V = E := by
    have hVO := h.hVO
    have hVn := h.hM₀V
    rw [hM₀eq, hOE] at hVO
    rw [hM₀eq] at hVn
    exact (hmin V hVO hVn).resolve_left h.hVne
  have hE1 : E ≠ ⊥ := by rw [← hVE]; exact h.hVne
  have hpc : CFSG.pCore 2 ↥H = ψ.ker := by rw [hψk, ← Hex.pCoreOf_subgroupOf', hOE]
  have eQ : ModO2 H ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hshort : IsShort2 H := isShort2_of_irred hEn hcomm hsq hE1 hmin hCE hOE
    (hM₀eq ▸ h.hper) (hM₀eq ▸ h.hM₀ne)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm isQuasisimple_statedSL5)
  have hext : CFSG.Quasithin.C31Case6L5 M H := by
    show IsExt ↥(conjClosure H M) _ _
    rw [conjClosure_eq_self' (hM₀eq ▸ h.hMN)]
    refine ⟨ψ.ker, inferInstance, ?_,
      isPSL_of_equiv5 (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩
    rw [hψk]
    exact CFSG.Quasithin.J4Fam.isE2_of_elementary E hcomm hsq hcard |>.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hEH).symm
  subst hM₀eq hVE
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨h.hSs, Or.inr (Or.inr hext)⟩))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.hSs, hshort, Or.inr ⟨isPSL_of_equiv5 eQ, hext⟩⟩))))),
    summand_of_card_ten hcard⟩

theorem two_pow_eleven_le [Finite A] {B : Subgroup A} (hB : IsElemAbelian 2 B)
    (hlt : 2 ^ 10 < Nat.card B) : 2 ^ 11 ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥B := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow]
    exact hB.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk] at hlt ⊢
  have h10 : 10 < k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  exact Nat.pow_le_pow_right (by norm_num) h10

theorem m4Branch
    (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) : M4Branch := by
  intro A _ _ S M₀ R M V h hS κ hκ hNR hB
  have hF := CFSG.Sporadic.J4.j4Facts
  have hc := chkF_true
  have hk := chkKW_true
  have hO := map_pCoreOf_le h hκ hNR
  rw [pCoreOf_M4 hF.mat hc hcard] at hO
  have hRX : R ≤ CFSG.Quasithin.KGJ4.M4.map κ := Subgroup.le_normalizer.trans hNR
  have hb := fJ_basis hF.mat hc
  have hFc : ∀ a ∈ (F4 hF.mat hc).map κ, ∀ b ∈ (F4 hF.mat hc).map κ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
    rw [← map_mul, ← map_mul, eSub_comm _ a b ha hb']
  have hFs : ∀ a ∈ (F4 hF.mat hc).map κ, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, eSub_sq _ a ha, map_one]
  have hFe : IsElemAbelian 2 ((F4 hF.mat hc).map κ) :=
    ⟨⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩, fun a ha => by rw [pow_two]; exact hFs a ha⟩
  have hFcard : Nat.card ↥((F4 hF.mat hc).map κ) = 2 ^ 10 := by
    rw [hκ.card_map, card_F4]
  have hle : ∀ B : Subgroup A, B ≤ R → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 10 :=
    fun B hBR hBe => not_lt.mp fun hlt => hB ⟨B, hBR, hBe, two_pow_eleven_le hBe hlt⟩
  have hFmax : CFSG.Quasithin.IsMaxElemAbelian R ((F4 hF.mat hc).map κ) :=
    ⟨hO, hFe, fun B hBR hBe => hFcard ▸ hle B hBR hBe⟩
  by_cases hJ : ∀ B : Subgroup A, CFSG.Quasithin.IsMaxElemAbelian R B →
      B = (F4 hF.mat hc).map κ
  ·
    have hJR := thompsonJ_eq_of_unique hFmax hJ
    have hEn : CFSG.Quasithin.KGJ4.M4.map κ ≤
        Subgroup.normalizer (((F4 hF.mat hc).map κ : Subgroup A) : Set A) := by
      rw [← hκ.map_normalizer]
      exact Subgroup.map_mono (M4_le_eNorm hF.mat hc)
    have hHM : CFSG.Quasithin.KGJ4.M4.map κ ≤ M := by
      have h1 := h.hJ
      rw [hJR] at h1
      exact hEn.trans h1
    have hmin : ∀ N : Subgroup A, N ≤ (F4 hF.mat hc).map κ →
        CFSG.Quasithin.KGJ4.M4.map κ ≤ Subgroup.normalizer (N : Set A) →
        N = ⊥ ∨ N = (F4 hF.mat hc).map κ := by
      intro N hNF hHN
      have hN : (N.comap κ).map κ = N := hκ.map_comap N
      have hN'F : N.comap κ ≤ F4 hF.mat hc := by
        rw [← hκ.map_le_iff, hN]
        exact hNF
      have hMN' : CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer ((N.comap κ : Subgroup G₀) :
          Set G₀) := by
        rw [← hκ.map_le_iff, hκ.map_normalizer, hN]
        exact hHN
      rcases m4_min hF.mat hc _ hN'F hMN' with h0 | h0
      · left
        rw [← hN, h0, Subgroup.map_bot]
      · right
        rw [← hN, h0]
    have hCE : CFSG.Quasithin.KGJ4.M4.map κ ⊓
        Subgroup.centralizer (((F4 hF.mat hc).map κ : Subgroup A) : Set A) ≤
          (F4 hF.mat hc).map κ := by
      rw [← hκ.map_centralizer, ← Subgroup.map_inf_eq _ _ κ hκ.inj]
      exact Subgroup.map_mono (m4_CE hF.mat hc hcard)
    obtain ⟨ψ, hψ, hψk⟩ := exists_surj_map κ hκ.inj (piM4 hF.mat hc) (piM4_surjective hF.mat hc)
      (ker_piM4 hF.mat hc hcard)
    exact concl_of_L5block h (Subgroup.map_mono (F4_le_M4 hF.mat hc)) hEn hFc hFs hFcard hmin
      (simple_map κ hκ.inj (m4_max hF.mat hc hcard)) hCE ψ hψ hψk (h.hM₀R.trans hNR) hHM
  ·
    exfalso
    obtain ⟨B, hBmax, hBne⟩ : ∃ B : Subgroup A, CFSG.Quasithin.IsMaxElemAbelian R B ∧
        B ≠ (F4 hF.mat hc).map κ := by
      by_contra hcon
      exact hJ fun B hBm => by_contra fun hne => hcon ⟨B, hBm, hne⟩
    obtain ⟨hBR, hBe, hBm⟩ := hBmax
    have hBcard : Nat.card B = 2 ^ 10 :=
      le_antisymm (hle B hBR hBe) (hFcard ▸ hBm _ hO hFe)
    have hRM : R.comap κ ≤ CFSG.Quasithin.KGJ4.M4 := by
      rw [← hκ.map_le_iff, hκ.map_comap]
      exact hRX
    set R₀ := (R.comap κ).subgroupOf CFSG.Quasithin.KGJ4.M4 with hR₀
    set X := (B.comap κ).subgroupOf CFSG.Quasithin.KGJ4.M4 with hX
    have hR₀2 : IsPGroup 2 ↥R₀ :=
      (h.hR2.comap_of_injective κ hκ.inj).comap_of_injective _
        CFSG.Quasithin.KGJ4.M4.subtype_injective
    have hXR : X ≤ R₀ := fun x hx => hBR hx
    have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
      intro a ha b hb'
      have e := hBe.1.is_comm.comm ⟨κ a, ha⟩ ⟨κ b, hb'⟩
      have e' : κ ((a : G₀) * b) = κ ((b : G₀) * a) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val e
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hκ.inj e')
    have hXs : ∀ a ∈ X, a * a = 1 := by
      intro a ha
      have e := hBe.2 (κ a) ha
      rw [pow_two, ← map_mul] at e
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hκ.inj (by rw [e,
        map_one]))
    have hBM : B.comap κ ≤ CFSG.Quasithin.KGJ4.M4 := fun x hx => hRM (hBR hx)
    have hXcard : Nat.card X = 2 ^ 10 := by
      rw [hX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, ← hκ.card_map,
        hκ.map_comap, hBcard]
    have hXF : ¬ X ≤ (F4 hF.mat hc).subgroupOf CFSG.Quasithin.KGJ4.M4 := by
      intro hXF
      apply hBne
      have hBF : B.comap κ ≤ F4 hF.mat hc := fun x hx => by
        have h1 : (⟨x, hBM hx⟩ : ↥CFSG.Quasithin.KGJ4.M4) ∈ X := hx
        exact hXF h1
      have h2 : B ≤ (F4 hF.mat hc).map κ := by
        rw [← hκ.map_comap B]
        exact Subgroup.map_mono hBF
      exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hFcard, hBcard])
    obtain ⟨m, hm⟩ := exists_conj_stab0 hF.mat hc hcard hR₀2 hXR hXc hXs hXcard hXF
    have hκ' := hκ.conj (κ ((m : G₀) * gJ⁻¹))
    refine hB (branch_H h hκ' fun x hx => ?_)
    obtain ⟨y, hyM, rfl⟩ := hNR hx
    have hyN : (⟨y, hyM⟩ : ↥CFSG.Quasithin.KGJ4.M4) ∈
        Subgroup.normalizer (R₀ : Set ↥CFSG.Quasithin.KGJ4.M4) := by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      rw [hR₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
        Subgroup.mem_comap, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul,
        map_inv]
      exact Subgroup.mem_normalizer_iff.mp hx (κ r)
    have h1 := kw3 hF hc hk (hm _ hyN)
    refine ⟨gJ * ((m : G₀)⁻¹ * y * m) * gJ⁻¹, ?_, ?_⟩
    · have e : ((m⁻¹ * ⟨y, hyM⟩ * m : ↥CFSG.Quasithin.KGJ4.M4) : G₀) = (m : G₀)⁻¹ * y * m := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← e]
      exact h1
    · show κ ((m : G₀) * gJ⁻¹) * κ (gJ * ((m : G₀)⁻¹ * y * m) * gJ⁻¹) *
          (κ ((m : G₀) * gJ⁻¹))⁻¹ = κ y
      rw [← map_inv, ← map_mul, ← map_mul]
      refine congrArg κ ?_
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
        mul_inv_cancel, mul_one]

theorem inspC31SporadicAtJ_j4_of'
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (hD3 : Subgroup.centralizer ((pCoreOf 2 (Subgroup.centralizer
      ({CFSG.Quasithin.J4Loc.z0} : Set G₀)) : Subgroup G₀) : Set G₀) ≤
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0)
    {KL : Subgroup G₀} {v0 : Fin 3 → G₀} {hv0 : EBasis v0} (hM3 : M3Facts KL hv0)
    (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    CFSG.Quasithin.InspC31SporadicAtJ .J4 :=
  inspC31SporadicAtJ_j4_of hKW hD3 hM3 (m4Branch hcard)

end CFSG.Quasithin.KGC31.J4

end
