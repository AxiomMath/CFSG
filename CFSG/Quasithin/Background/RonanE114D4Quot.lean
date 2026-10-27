module

public import CFSG.Quasithin.Background.RonanE17
public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1
open scoped MatrixGroups

theorem inE_top_of_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') {i : ℕ} (h : InE i (⊤ : Subgroup G)) : InE i (⊤ : Subgroup G') := by
  have := E1.Eleven.inE_map_mulEquiv e h
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at this

theorem inE_of_solvable_quotient {i : ℕ} (hi : 1 ≤ i) :
    ∀ (k : ℕ) (Q : Type) [Group Q] [Finite Q], Nat.card Q ≤ k →
      ∀ (R : Subgroup Q) [R.Normal], Group.IsSolvable ↥R →
        InE i (⊤ : Subgroup (Q ⧸ R)) → InE i (⊤ : Subgroup Q) := by
  intro k
  induction k with
  | zero =>
    intro Q _ _ h
    exact absurd h (by have := Nat.card_pos (α := Q); omega)
  | succ k ih =>
    intro Q _ _ hk R _ hRs hI
    by_cases hR : R = ⊥
    · subst hR
      exact inE_top_of_mulEquiv (QuotientGroup.quotientBot : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q) hI
    obtain ⟨N, hNn, hNR, hN1, hNmin⟩ := CFSG.exists_minimal_normal_le R ‹R.Normal› hR
    haveI : N.Normal := hNn
    have hNs : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNR)
    have hIM : CFSG.IsMinimalNormal N := ⟨fun K _ hKN => by
      by_cases hK : K = ⊥
      · exact Or.inl hK
      · exact Or.inr (hNmin K ‹_› hKN hK)⟩
    obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
    have hNp : IsPGroup r N := CFSG.IsElementaryAbelian.isPGroup r N
    have hQN : Nat.card (Q ⧸ N) ≤ k := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN1
      have h3 := Nat.card_pos (α := Q ⧸ N)
      nlinarith
    set R' : Subgroup (Q ⧸ N) := R.map (QuotientGroup.mk' N) with hR'
    haveI : R'.Normal := Subgroup.Normal.map ‹R.Normal› _ (QuotientGroup.mk'_surjective N)
    have hR's : Group.IsSolvable ↥R' :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).subgroupMap R)
        ((QuotientGroup.mk' N).subgroupMap_surjective R)
    let e3 : ((Q ⧸ N) ⧸ R') ≃* (Q ⧸ R) := QuotientGroup.quotientQuotientEquivQuotient N R hNR
    have hI' : InE i (⊤ : Subgroup ((Q ⧸ N) ⧸ R')) := inE_top_of_mulEquiv e3.symm hI
    have hIH : InE i (⊤ : Subgroup (Q ⧸ N)) := ih (Q ⧸ N) hQN R' hR's hI'
    intro T hT
    refine inEFor_of_quotient hIH hT ?_
    intro Ω hΩ
    have hTM : T ≤ eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set Q)) :=
      fun x hx => Subgroup.mem_sup_right ⟨Subgroup.mem_top x, le_normalizer_weakClosure hΩ hx⟩
    by_cases hr2 : r = 2
    · subst hr2
      exact (hT.le_of_normal le_top Subgroup.normal_subgroupOf hNp).trans hTM
    · exact normal_pGroup_le hr hr2 hT hNp hΩ ((eGen_mono hi ⊤ T Ω).trans le_sup_left)
        (fun x hx => Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩)


section Levi

variable {Q : Type} [Group Q] [Finite Q]

open CFSG.QuasithinUnique.Vol2Native.A312L (exists_finset_card_four sl2_isSimple sl2_nonabelian)

theorem nParam_top_le_of_levi {N : Subgroup Q} [N.Normal]
    (hQN : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ N) {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m) (π : ↥N →* SL(2, F)) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 ↥π.ker) : E1.nParam (⊤ : Subgroup Q) ≤ (m : ℕ∞) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCharP : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hL4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hsimple : IsSimpleGroup SL(2, F) := sl2_isSimple hL4
  have hnab : ∃ a b : SL(2, F), a * b ≠ b * a := sl2_nonabelian hL4
  have hperf : Group.IsPerfect SL(2, F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  have hpc : CFSG.pCore 2 ↥N = π.ker := by
    refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker π) hker)
    have hnorm : ((CFSG.pCore 2 ↥N).map π).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map π hπ
    haveI := hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥N).map π) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h
      exact h
    · exfalso
      have h2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥N).map π) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥N)).map π
      rw [h] at h2
      have h3 : IsPGroup 2 SL(2, F) := h2.of_equiv Subgroup.topEquiv
      have := h3.isNilpotent
      obtain ⟨a, b, hab⟩ := hnab
      have hnt : Nontrivial SL(2, F) := ⟨⟨a * b, b * a, hab⟩⟩
      haveI := hperf
      exact Group.IsPerfect.not_isSolvable SL(2, F) inferInstance
  set R : Subgroup Q := CFSG.pCore 2 Q with hRdef
  haveI hRn : R.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hVR : pCoreOf 2 N ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCore 2 ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    refine Subgroup.normalizer_eq_top_iff.mp ?_
    refine eq_top_iff.mpr ?_
    rw [← Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
  set ρ := (QuotientGroup.mk' R).subgroupMap N with hρdef
  have hρs : Function.Surjective ρ := (QuotientGroup.mk' R).subgroupMap_surjective N
  have hkerρ : ρ.ker = π.ker := by
    rw [← hpc]
    refine le_antisymm ?_ ?_
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ρ) ?_
      intro x
      have hx : ((x : ↥N) : Q) ∈ R := by
        have h1 : ρ (x : ↥N) = 1 := x.2
        have h2 := congrArg Subtype.val h1
        simpa [hρdef, QuotientGroup.eq_one_iff] using h2
      obtain ⟨k, hk⟩ := hR2 ⟨_, hx⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    · intro x hx
      have hxV : ((x : ↥N) : Q) ∈ pCoreOf 2 N := ⟨x, hx, rfl⟩
      have hxR : ((x : ↥N) : Q) ∈ R := hVR hxV
      refine Subtype.ext ?_
      simpa [hρdef, QuotientGroup.eq_one_iff] using hxR
  let e : ↥(N.map (QuotientGroup.mk' R)) ≃* SL(2, F) :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerρ).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ))
  haveI hLn : (N.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective R)
  haveI hLsimple : IsSimpleGroup ↥(N.map (QuotientGroup.mk' R)) := e.isSimpleGroup
  have hLnab : ∃ a b : ↥(N.map (QuotientGroup.mk' R)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hX2 : ∀ x : Q ⧸ R, ∃ k : ℕ, x ^ 2 ^ k ∈ N.map (QuotientGroup.mk' R) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hQN q
    exact ⟨k, ⟨q ^ 2 ^ k, hk, by simp⟩⟩
  have hAS : CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple (N.map (QuotientGroup.mk' R)) := by
    refine ⟨hLn, hLsimple, hLnab, ?_, hX2⟩
    set C : Subgroup (Q ⧸ R) :=
      Subgroup.centralizer ((N.map (QuotientGroup.mk' R) : Subgroup (Q ⧸ R)) : Set (Q ⧸ R))
      with hCdef
    have hCn : C.Normal := by
      refine ⟨fun c hc g l hl => ?_⟩
      have hl' : g⁻¹ * l * g ∈ N.map (QuotientGroup.mk' R) := by
        have := hLn.conj_mem l hl g⁻¹
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hc _ hl'
      have : l * (g * c * g⁻¹) = (g * c * g⁻¹) * l := by
        calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
          _ = (g * c * g⁻¹) * l := by group
      exact this
    have hC2 : ∀ c ∈ C, ∃ k : ℕ, c ^ 2 ^ k = 1 := by
      intro c hc
      obtain ⟨k, hk⟩ := hX2 c
      have hkC : c ^ 2 ^ k ∈ C := Subgroup.pow_mem C hc _
      refine ⟨k, ?_⟩
      have hz : (⟨c ^ 2 ^ k, hk⟩ : ↥(N.map (QuotientGroup.mk' R))) ∈
          Subgroup.center ↥(N.map (QuotientGroup.mk' R)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkC y y.2)
      rw [CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple hLnab, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    set C' : Subgroup Q := C.comap (QuotientGroup.mk' R) with hC'def
    haveI hC'n : C'.Normal := Subgroup.normal_comap _
    have hC'2 : IsPGroup 2 ↥C' := by
      intro g
      obtain ⟨k, hk⟩ := hC2 (QuotientGroup.mk' R (g : Q)) g.2
      have hk' : ((g : Q) ^ 2 ^ k) ∈ R := by
        rw [← QuotientGroup.eq_one_iff]
        simpa using hk
      obtain ⟨l, hl⟩ := hR2 ⟨(g : Q) ^ 2 ^ k, hk'⟩
      refine ⟨k + l, Subtype.ext ?_⟩
      have := congrArg Subtype.val hl
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hC'R : C' ≤ R := CFSG.LieType.BorelTits.le_pCore 2 hC'n hC'2
    refine le_bot_iff.mp fun c hc => ?_
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective c
    have : q ∈ C' := hc
    exact (QuotientGroup.eq_one_iff q).mpr (hC'R this)
  have hbound : ∀ A : Subgroup (Q ⧸ R), IsElemAbelian 2 A → Nat.card A ≤ 2 ^ m := fun A hA =>
    CFSG.Quasithin.Vol2.Ch11.SecE3.card_le_of_isElemAbelian_sl2 hAS e hF hA
  have hrank : CFSG.Open.twoRank (Q ⧸ R) ≤ m := by
    refine csSup_le' ?_
    rintro k ⟨E, -, hE, hEk⟩
    have h1 := hbound E hE
    rw [hEk] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have hnX : E1.nParam (⊤ : Subgroup (Q ⧸ R)) ≤ (m : ℕ∞) :=
    (RonanE17.nParam_top_le_twoRank (Q ⧸ R)).trans (by exact_mod_cast hrank)
  have hInE : InE m (⊤ : Subgroup (Q ⧸ R)) := (E1.nParam_le_iff (by omega)).mp hnX
  have hRs : Group.IsSolvable ↥R := by
    have := hR2.isNilpotent
    infer_instance
  have hInQ : InE m (⊤ : Subgroup Q) :=
    inE_of_solvable_quotient (by omega) (Nat.card Q) Q le_rfl R hRs hInE
  exact (E1.nParam_le_iff (by omega)).mpr hInQ

end Levi

end CFSG.Quasithin.RonanE114
