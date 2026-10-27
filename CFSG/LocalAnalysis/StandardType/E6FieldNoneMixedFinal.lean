module

public import CFSG.LocalAnalysis.StandardType.E6MixedULift
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddLift

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem exists_conj_torusGroup_of_odd_order_unconditional
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {m : ℕ} (hm : Odd m) {x : ModGL Tag.E6 L}
    (hx : x ∈ adjointGroup Tag.E6 L) (hxm : x ^ m = 1) :
    ∃ g ∈ adjointGroup Tag.E6 L, g⁻¹ * x * g ∈ torusGroup Tag.E6 L := by
  revert hm hx hxm x
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm x hx hxm
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.pos.ne') with h1 | h1
    ·
      obtain rfl : m = 1 := h1.symm
      have hx1 : x = 1 := by simpa using hxm
      refine ⟨1, one_mem _, ?_⟩
      rw [hx1]
      group
      exact one_mem _
    ·
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      have hp2 : p ≠ 2 := hm.ne_two_of_dvd_nat hpdvd
      by_cases hmp : m = p
      ·
        subst hmp
        exact exists_conj_torusGroup_of_prime_order halg hp hp2 hx hxm
      ·
        have hlt : m / p < m := Nat.div_lt_self (by omega) hp.one_lt
        have hodd' : Odd (m / p) := Odd.of_dvd_nat hm (Nat.div_dvd_of_dvd hpdvd)
        have hx' : x ^ p ∈ adjointGroup Tag.E6 L := pow_mem hx p
        have hx'pow : (x ^ p) ^ (m / p) = 1 := by
          rw [← pow_mul, Nat.mul_div_cancel' hpdvd, hxm]
        obtain ⟨h, hh, hht⟩ := ih (m / p) hlt hodd' hx' hx'pow
        exact exists_conj_torusGroup_of_odd_order_lift halg hm hp hx hxm ⟨h, hh, hht⟩

theorem exists_conj_torusGroup_of_odd_order_orderOf
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {x : ModGL Tag.E6 L} (hx : x ∈ adjointGroup Tag.E6 L) (hodd : Odd (orderOf x)) :
    ∃ g ∈ adjointGroup Tag.E6 L, g⁻¹ * x * g ∈ torusGroup Tag.E6 L :=
  exists_conj_torusGroup_of_odd_order_unconditional halg hodd hx (pow_orderOf_eq_one x)

theorem exists_fixed_odd_order_u_of_mem_sup_inn_diag {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (β : MulAut (adjointGroup Tag.E6 K))
    (hβ : β ∈ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ⊔
      (AutSt.e6DiagHom K).range)
    (hodd : Odd (orderOf β)) :
    ∃ u ∈ adjointGroup Tag.E6 (AlgebraicClosure K), Odd (orderOf u) ∧
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 f u = u ∧
      ∀ c : adjointGroup Tag.E6 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          u * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.E6 K) * u⁻¹ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hNormal :
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range.Normal :=
    AutSt.normal_range_conj
  obtain ⟨_, hx, _, hd, hxd⟩ :=
    (Subgroup.mem_sup_of_normal_left (hs := hNormal)).mp hβ
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hd
  let g : ModGL Tag.E6 K := (x : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b
  have hconj : ∀ c : adjointGroup Tag.E6 K,
      ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        g * (c : ModGL Tag.E6 K) * g⁻¹ := by
    intro c
    have happ := congrArg (fun f : MulAut (adjointGroup Tag.E6 K) =>
      (f c : ModGL Tag.E6 K)) hxd
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at happ
    have hdcoe : ((AutSt.e6DiagHom K b c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 b * (c : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹ := by
      change (exactNormalAut Tag.E6 K b 1 0 c : ModGL Tag.E6 K) = _
      rw [coe_exactNormalAut, exactQ_zero, AutSt.units_map_entrywiseHom_one, inv_one, mul_one,
        mul_one]
    calc ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
        = (x : ModGL Tag.E6 K) *
            ((AutSt.e6DiagHom K b c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
            (x : ModGL Tag.E6 K)⁻¹ := happ.symm
      _ = (x : ModGL Tag.E6 K) *
            (rootDiagUnit Tag.E6 b * (c : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹) *
            (x : ModGL Tag.E6 K)⁻¹ := by rw [hdcoe]
      _ = g * (c : ModGL Tag.E6 K) * g⁻¹ := by
        dsimp only [g]
        group
  have hgN : g ∈ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
    dsimp only [g]
    exact mul_mem (Subgroup.le_normalizer x.2)
      (root_diagonal_conjugation Tag.E6 K b).2.2
  let N := Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K))
  let gN : N := ⟨g, hgN⟩
  let φ : N →* MulAut (adjointGroup Tag.E6 K) :=
    Subgroup.normalizerMonoidHom (H := adjointGroup Tag.E6 K)
  have hφ : φ gN = β := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change ((((Subgroup.normalizerMonoidHom (H := adjointGroup Tag.E6 K)) gN) c :
        adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa only [gN] using (hconj c).symm
  have hoddφ : Odd (orderOf (φ gN)) := by
    rw [hφ]
    exact hodd
  have hModGL : Finite (ModGL Tag.E6 K) := finite_modGL (τ := Tag.E6) (K := K)
  have hN : Finite N := @Subtype.finite (ModGL Tag.E6 K) hModGL (fun x => x ∈ N)
  obtain ⟨k, hkodd, hkφ⟩ :=
    @exists_pow_odd_order_of_odd_order_map N (MulAut (adjointGroup Tag.E6 K))
      inferInstance hN inferInstance φ gN hoddφ
  have hmem : baseChangeGL (algebraMap K (AlgebraicClosure K)) g ∈
      adjointGroup Tag.E6 (AlgebraicClosure K) := by
    dsimp only [g]
    rw [map_mul]
    refine mul_mem (baseChangeGL_mem_adjointGroup (f := algebraMap K (AlgebraicClosure K)) x.2) ?_
    rw [baseChangeGL_rootDiagUnit]
    exact torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup _)
  have hcomp : (iterateFrobenius (AlgebraicClosure K) 2 f).comp
      (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun c => ?_
    change (iterateFrobenius (AlgebraicClosure K) 2 f)
      (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) c
    rw [iterateFrobenius_def, ← map_pow]
    congr 1
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  refine ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)) (g ^ k), ?_, ?_, ?_, ?_⟩
  · rw [map_pow]
    exact pow_mem hmem k
  · have hgk : orderOf (g ^ k) = orderOf (gN ^ k) := by
      simp [gN]
    rw [orderOf_injective (baseChangeGL (algebraMap K (AlgebraicClosure K)))
      (baseChangeGL_injective _)]
    rw [hgk]
    exact hkodd
  · rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  · intro c
    have hφk : φ (gN ^ k) = β := hkφ.trans hφ
    have hconjk : ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        g ^ k * (c : ModGL Tag.E6 K) * (g ^ k)⁻¹ := by
      have h := congrArg (fun f : MulAut (adjointGroup Tag.E6 K) =>
        ((f c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) hφk
      change ((((Subgroup.normalizerMonoidHom (H := adjointGroup Tag.E6 K)) (gN ^ k)) c :
          adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((β c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) at h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      simpa [gN] using h.symm
    rw [hconjk, map_mul, map_mul, map_inv]

theorem e6FieldNone_mixed {f : ℕ} (K : Type) [Field K] [Finite K]
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (hε : ε < 2) (hσ : σ ≠ 1)
    (β : MulAut (adjointGroup Tag.E6 K))
    (hβ : β ∈ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ⊔
      (AutSt.e6DiagHom K).range)
    (hodd : Odd (orderOf β))
    (_hα2 : (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) *
      (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) = 1)
    (_hcomm : (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) * β =
      β * (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε))
    (hfix : ∀ x, β x = x → (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) x = x)
    (L₁ : Subgroup (adjointGroup Tag.E6 K)) (hL₁ : ∀ y ∈ L₁, β y = y) :
    Group.IsSolvable L₁ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card hf hK
  have : CharP K 2 := hchar ▸ ringChar.charP K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  by_cases hβ1 : β = 1
  ·
    have hα1 : MulAut.conj g * exactNormalAut Tag.E6 K a σ ε = 1 := by
      apply MulEquiv.ext
      intro x
      exact hfix x (by rw [hβ1]; rfl)
    obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
      CFSG.LieType.Chevalley.ordinary_E_field_graph_quotient_and_involutions Tag.E6
        (Or.inl rfl) K
    have hpt : ∀ h : adjointGroup Tag.E6 K,
        ((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) h : ModGL Tag.E6 K) =
          (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε *
            Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E6 K) *
            (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹ := by
      intro h
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_exactNormalAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    have hΘα : Θ (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) =
        (σ, Multiplicative.ofAdd
          ((((⟨ε, hε⟩ : Fin (exactE Tag.E6)) : ℕ) : ZMod (exactE Tag.E6)))) :=
      hΘ _ g a σ (⟨ε, hε⟩ : Fin (exactE Tag.E6)) hpt
    rw [hα1, map_one] at hΘα
    exact (hσ (congrArg Prod.fst hΘα.symm)).elim
  ·
    obtain ⟨u, huG, hoddU, hfixU, huβ⟩ :=
      exists_fixed_odd_order_u_of_mem_sup_inn_diag (f := f) hK β hβ hodd
    have hu1 : u ≠ 1 := by
      intro hu
      apply hβ1
      apply MulEquiv.ext
      intro c
      have h := huβ c
      rw [hu, one_mul, inv_one, mul_one] at h
      exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h)
    set L := AlgebraicClosure K with hL
    have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
    have : ExpChar L 2 := ExpChar.prime Nat.prime_two
    have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
    have halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L :=
      CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 K
    have hconj : ∃ g' ∈ adjointGroup Tag.E6 L, g'⁻¹ * u * g' ∈ torusGroup Tag.E6 L :=
      exists_conj_torusGroup_of_odd_order_orderOf (L := L) halg huG hoddU
    have hpq : Nat.Coprime (orderOf u) (2 ^ f) := (hoddU.coprime_two_right).pow_right f
    obtain ⟨D, hDΦ, hDq, hmemD⟩ :=
      exists_langDatum_of_toral_untw (τ := Tag.E6) (L := L) (ℓ := 2) f hf hpq
        (pow_orderOf_eq_one u) hfixU hconj
    set ιK : K →+* L := algebraMap K L with hιK
    set ι₀ : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 L :=
      (baseChangeGL ιK).comp (adjointGroup Tag.E6 K).subtype with hι₀
    have hι₀inj : Function.Injective ι₀ :=
      (baseChangeGL_injective ιK).comp (Subgroup.subtype_injective _)
    have hFrCard : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
      rw [hK]
      exact iterateFrobenius_def 2 f c
    have hd : LangDescent D 7 ι₀ :=
      langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFrCard D hDΦ Nat.prime_seven (by norm_num)
        (commutator_adjointGroup_E6_eq_top K)
    have huβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := by
      intro c
      simpa [ι₀, ιK] using huβ c
    obtain ⟨S, a₀, ι, hSD, hT, hap, h1, hinj, hrange, hιform, hιconj⟩ :=
      exists_langSetup_of_toral_datum_of_prime_formula (L := L) (ℓ := 2) (f := f) (p₀ := 5)
        (p := orderOf u) Nat.prime_two hf D hDq Nat.prime_five (by norm_num) (Or.inl le_rfl)
        hd.finite_model ι₀ hι₀inj hd.Γ_eq β huβ' hmemD (pow_orderOf_eq_one u) hu1
    have hDqS : S.D.q = 2 ^ f := by rw [hSD]; exact hDq
    have hιformS : ∀ c, ι c = S.D.g0⁻¹ * ι₀ c * S.D.g0 := by
      intro c
      rw [hSD]
      exact hιform c
    obtain ⟨s, hs, hσpow, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq hf hK σ
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h
      · exfalso
        apply hσ
        ext c
        rw [hσpow c, h0]
        simp
      · exact h
    have hcomp' : (iterateFrobenius L 2 s).comp ιK = ιK.comp σ.toRingHom := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      change iterateFrobenius L 2 s (algebraMap K L c) = algebraMap K L (σ c)
      rw [hσpow c, map_pow, iterateFrobenius_def]
    by_cases hKerEmpty : familyKernel (fun _ : Unit => a₀) = ∅
    · have hsol : Group.IsSolvable
          ↥(adjointGroup Tag.E6 L ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a₀}) :=
        isSolvable_centralizer_of_familyKernel_empty_of_odd_inter hoddU a₀ hap hKerEmpty
      exact e6_solvable_of_ambient_centralizer_of_diag β S a₀ ι hsol hinj hrange hιconj L₁ hL₁
    · obtain ⟨a0, ha0mem⟩ := Set.nonempty_iff_ne_empty.mpr hKerEmpty
      have hker : a0 ∈ kernelRoots (rootCharHom a₀) := ⟨ha0mem.1, ha0mem.2 ()⟩
      let i : KernelComponent (rootCharHom a₀) :=
        (⟦⟨a0, hker⟩⟧ : KernelComponent (rootCharHom a₀))
      obtain ⟨z', hz'⟩ := e6_conjAction hcomp' g a ε S ι hιformS
      exact (e6_false_of_component_fixed_of_diag g a ε β S a₀ ι i hT hιconj hinj hrange hDqS
        hs0 hs z' hz' hfix).elim

theorem e6FieldNone_holds : E6FieldNone := by
  intro f K _ _ hf hK g a σ ε hε hσ β hβ hodd
  dsimp only
  intro hα2 hcomm hfix L₁ hL₁
  exact e6FieldNone_mixed (f := f) K hf hK g a σ ε hε hσ β hβ hodd hα2 hcomm hfix L₁ hL₁

theorem ggOuterInvAt_E6_of_fieldNone (h2 : GGO2CentralizerG0At .E6) (hD2 : E6GraphNone) :
    GGOuterInvAt .E6 :=
  ggOuterInvAt_E6_of h2 e6FieldNone_holds hD2

end CFSG.StandardType
