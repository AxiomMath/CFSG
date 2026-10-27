module

public import CFSG.Quasithin.Background.E6EighteenHeInner
public import CFSG.Quasithin.Background.E6EighteenE

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique

theorem center_eq_pCore_of_isHeQuot {Y : Type} [Group Y]
    [Finite Y] {K : Subgroup Y} (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) :
    Subgroup.center ↥K = CFSG.pCore 2 ↥K := by
  obtain ⟨ψ⟩ := hHe
  have : IsSimpleGroup Blueprint.NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := ψ.isSimpleGroup_congr.mpr this
  have hO2 : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq
        (N := CFSG.pCore 2 ↥K) CFSG.pCore_normal with hN | hN
    · exfalso
      have : Group.IsPerfect ↥K := hKq.1
      have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
      have hp : IsPGroup 2 ↥K := by
        have h1 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
        rw [hN] at h1
        exact h1.of_equiv Subgroup.topEquiv
      exact Group.IsPerfect.not_isNilpotent ↥K hp.isNilpotent
    · exact hN
  exact center_eq_of_quot_simple hKq hO2 hsimple

theorem nonempty_qbar_mulEquiv_he {Y : Type} [Group Y]
    [Finite Y] {K : Subgroup Y} (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) :
    Nonempty (Bar.Qbar K ≃* Blueprint.NativeSporadic.He) := by
  obtain ⟨ψ⟩ := hHe
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_pCore_of_isHeQuot hKq ⟨ψ⟩)).trans ψ⟩

open Bar in
theorem relIndex_inf_centralizer_le_two_of_isHeQuot
    {G : Type} [Group G] [Finite G] {K L P : Subgroup G} (hKq : CFSG.IsQuasisimple ↥K)
    (hHe : IsHeQuot K) (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hP2 : ∀ u ∈ P, u * u = 1)
    (hLK : L ≤ K) (hLP : L ≤ Subgroup.centralizer (P : Set G)) (hLq : CFSG.IsQuasisimple ↥L)
    (hL7 : IsA7Type L) : (P ⊓ Subgroup.centralizer (K : Set G)).relIndex P ≤ 2 := by
  classical
  obtain ⟨φ⟩ := nonempty_qbar_mulEquiv_he hKq hHe
  set ρ : ↥P →* MulAut (Qbar K) := (barHom K).comp (Subgroup.inclusion hPN) with hρ
  have hZ : Subgroup.center (Qbar K) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hKq
  set f : ↥L →* Qbar K := (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hLK)
    with hfdef
  have hfker : f.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hl
    rw [Subgroup.mem_center_iff] at hl ⊢
    intro m
    apply Subtype.ext
    have := congrArg Subtype.val (hl (Subgroup.inclusion hLK m))
    simpa using this
  have h7 : IsA7Group ↥f.range := IsA7Group.range hLq hL7 f hfker
  have hinner : ∀ u : ↥P,
      ρ u ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Qbar K) → ρ u = 1 := by
    rintro u ⟨x, hx⟩
    by_cases hx1 : x = 1
    · rw [← hx, hx1, map_one]
    exfalso
    have huu : ρ u * ρ u = 1 := by
      rw [← map_mul, show u * u = 1 from Subtype.ext (hP2 u u.2), map_one]
    have hxx : x * x = 1 := by
      apply Id2519.conj_injective_of_center_bot hZ
      rw [map_mul, hx, huu, map_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two, hxx]) hx1
    have hle : f.range ≤ Subgroup.centralizer ({x} : Set (Qbar K)) := by
      rintro _ ⟨l, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : ((Subgroup.inclusion hPN u : ↥(Subgroup.normalizer (K : Set G))) : G) *
          ((Subgroup.inclusion hLK l : ↥K) : G) =
          ((Subgroup.inclusion hLK l : ↥K) : G) *
            ((Subgroup.inclusion hPN u : ↥(Subgroup.normalizer (K : Set G))) : G) :=
        Subgroup.mem_centralizer_iff.1 (hLP l.2) u u.2
      have h1 : ρ u (f l) = f l := barHom_mk_of_comm _ _ hcomm
      rw [← hx, MulAut.conj_apply] at h1
      calc f l * x = (x * f l * x⁻¹) * x := by rw [h1]
        _ = x * f l := by group
    exact factHeInnerNoA7_holds (Qbar K) ⟨φ⟩ x hord f.range hle h7
  set ρ' : ↥P →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Qbar K) :=
    (QuotientGroup.mk' _).comp ρ with hρ'
  have hker : ρ'.ker = (P ⊓ Subgroup.centralizer (K : Set G)).subgroupOf P := by
    ext u
    rw [MonoidHom.mem_ker, hρ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 := hinner u h
      rw [hρ, MonoidHom.comp_apply, barHom_eq_one_iff hKq.1] at h1
      exact ⟨u.2, Subgroup.mem_centralizer_iff.2 fun k hk => (h1 ⟨k, hk⟩).symm⟩
    · rintro ⟨-, hu⟩
      have h1 : ρ u = 1 := by
        rw [hρ, MonoidHom.comp_apply, barHom_eq_one_iff hKq.1]
        intro k
        exact (Subgroup.mem_centralizer_iff.1 hu k k.2).symm
      rw [h1]
      exact Subgroup.one_mem _
  have hcardOut :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Qbar K)) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (φ.trans CFSG.Sporadic.HeldB.heEquivP)).toEquiv]
    exact CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model.2.2.2.2.1
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Qbar K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardOut]; norm_num)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, ← hcardOut]
  exact Nat.card_mono Set.finite_univ (Set.subset_univ _) |>.trans_eq (Nat.card_univ)

end E6

end CFSG.Quasithin
