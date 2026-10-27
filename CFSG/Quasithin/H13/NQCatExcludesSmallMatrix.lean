module

public import CFSG.Quasithin.H13.NQCatCharTwoDegreeThree
public import CFSG.Quasithin.H13.NQTermSymplecticFour
public import CFSG.Quasithin.H13.NQCatDegreeTwo

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem quotient_pCore_mulEquiv_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A →* B) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) :
    Nonempty (A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective φ hφ
  have hAn : (CFSG.pCore 2 A).Normal := CFSG.pCore_normal
  have hBn : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  have hcomap : (CFSG.pCore 2 B).comap φ = CFSG.pCore 2 A := by
    apply le_antisymm
    · exact le_sSup ⟨hBn.comap φ, CFSG.pCore_isPGroup.comap_of_ker_isPGroup φ hker⟩
    · rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup ⟨hAn.map φ hφ, CFSG.pCore_isPGroup.map φ⟩
  let ψ : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' _).comp φ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = CFSG.pCore 2 A := by
    rw [← hcomap]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_comap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

theorem quasithinIsSylowTwo_of_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) :
    CFSG.Open.quasithinIsSylowTwo (P : Subgroup G) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ⟨P.isPGroup', P.not_dvd_index⟩

theorem isQuasisimple_quotient_pCore_of_isQuasisimple {B : Type*} [Group B] [Finite B]
    (hq : CFSG.IsQuasisimple B) : CFSG.IsQuasisimple (B ⧸ CFSG.pCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hOn with htop | hc
  · exfalso
    apply not_isSolvable_of_isQuasisimple hq
    have h2 : IsPGroup 2 (⊤ : Subgroup B) := htop ▸ CFSG.pCore_isPGroup
    have := (h2.of_equiv Subgroup.topEquiv).isNilpotent
    infer_instance
  · exact (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hq hc).1

theorem isQuasisimple_of_mem_cComp_degree_two_quotient {k : Type*} [Field k] [Finite k]
    {Γ : Subgroup (GL (Fin 2) k)} (D : Subgroup Γ) [D.Normal] (hDs : Group.IsSolvable D)
    {Bst : Subgroup (Γ ⧸ D)} (hBst : Bst ∈ cComp Bst) : CFSG.IsQuasisimple ↥Bst := by
  classical
  have : Finite (GL (Fin 2) k) := Finite.of_injective _ Units.val_injective
  set π : Γ →* Γ ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  let f : Bst.comap π →* Bst := (π.comp (Bst.comap π).subtype).codRestrict Bst fun x => x.2
  have hfs : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := hπs b
    exact ⟨⟨g, hb⟩, rfl⟩
  have hmemD : ∀ x : f.ker, (((x : Bst.comap π) : Γ)) ∈ D := by
    intro x
    have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    have h1 : π ((x : Bst.comap π) : Γ) = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hfker : Group.IsSolvable f.ker := by
    let i : f.ker →* D :=
      { toFun := fun x => ⟨((x : Bst.comap π) : Γ), hmemD x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := fun a b hab => by
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    exact Group.isSolvable_of_isSolvable_injective (f := i) hi
  have htop : (⊤ : Subgroup ↥Bst) ∈ cComp (⊤ : Subgroup ↥Bst) := by
    have h := subgroupOf_mem_cComp hBst
    rwa [Subgroup.subgroupOf_self] at h
  obtain ⟨L₀, hL₀, hL₀B⟩ := map_surjOn_cComp_top f hfs hfker htop
  let ι : Bst.comap π →* GL (Fin 2) k := Γ.subtype.comp (Bst.comap π).subtype
  have hι : Function.Injective ι := Γ.subtype_injective.comp (Bst.comap π).subtype_injective
  have hιker : Group.IsSolvable ι.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ι).mpr hι]
    infer_instance
  have hL₀' := LocDbl.map_mem_cComp_of_ker ι hιker hL₀
  have hq := (degree_two_matrix_Ccomponents_quasisimple_and_unique
    ((⊤ : Subgroup ↥(Bst.comap π)).map ι)).1 _ hL₀'
  have hqL₀ : CFSG.IsQuasisimple ↥L₀ :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (L₀.equivMapOfInjective ι hι)).2 hq
  let g : L₀ →* Bst := f.comp L₀.subtype
  have hgs : Function.Surjective g := by
    intro b
    have hb : b ∈ L₀.map f := hL₀B ▸ mem_top b
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgker : g.ker ≤ center L₀ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqL₀ g.normal_ker with htop' | hc
    · exfalso
      apply ne_bot_of_mem_cComp hBst
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨x, hx⟩ := hgs ⟨b, hb⟩
      have hx1 : g x = 1 := MonoidHom.mem_ker.mp (htop' ▸ mem_top x)
      rw [hx1] at hx
      rw [mem_bot]
      exact (congrArg Subtype.val hx).symm
    · exact hc
  have hquot := (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hqL₀ hgker).1
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)).1 hquot

theorem nonquasisimple_local_two_core_quotient_excludes_small_matrix_ambient_quotients
    {K : Type*} [Group K] [Finite K] (N : Subgroup K) [N.Normal] (hN : IsPGroup 2 N)
    (S : Sylow 2 K) {A : Subgroup K} (hA : A ∈ cComp (A ⊔ (S : Subgroup K)))
    (hKN : CFSG.IsQuasisimple (K ⧸ N)) (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) :
    (∀ (k : Type) [Field k] [Finite k] (Γ : Subgroup (GL (Fin 2) k)) (D : Subgroup Γ)
      [D.Normal], Group.IsSolvable D → IsEmpty (K ⧸ N ≃* Γ ⧸ D)) ∧
    (∀ (p f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData p f F)
      (D : Subgroup (unitarySU p f F 3)) [D.Normal], D ≤ unitaryScalars h 3 →
        IsEmpty (K ⧸ N ≃* unitarySU p f F 3 ⧸ D)) ∧
    (∀ (k : Type) [Field k] [Finite k] [CharP k 2] (Γ : Subgroup (GL (Fin 3) k))
      (D : Subgroup Γ) [D.Normal], (∀ d ∈ D, ∃ c : kˣ,
        (d : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c) →
        IsEmpty (K ⧸ N ≃* Γ ⧸ D)) ∧
    (∀ (k : Type) [Field k] [Finite k] [CharP k 2],
      IsEmpty (K ⧸ N ≃* CFSG.Assembly.LowTwoRank.StatedSp 2 k)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set η : K →* K ⧸ N := QuotientGroup.mk' N with hη
  have hηs : Function.Surjective η := QuotientGroup.mk'_surjective N
  have hηker : Group.IsSolvable η.ker := by
    rw [hη, QuotientGroup.ker_mk']
    have := hN.isNilpotent
    infer_instance
  set B : Subgroup (K ⧸ N) := A.map η with hBdef
  have hB1 : B ∈ cComp ((A ⊔ (S : Subgroup K)).map η) := LocDbl.map_mem_cComp_of_ker η hηker hA
  have hB : B ∈ cComp B := cComp_mem_of_le hB1 le_rfl (map_mono le_sup_left)
  have hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
    intro hq
    apply hAq
    have hker : IsPGroup 2 (η.subgroupMap A).ker := by
      intro x
      have hxN : ((x : A) : K) ∈ N := by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        have h1 : η ((x : A) : K) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨n, hn⟩ := hN ⟨_, hxN⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have h2 := congrArg Subtype.val hn
      simpa using h2
    obtain ⟨e⟩ := quotient_pCore_mulEquiv_of_surjective (η.subgroupMap A)
      (η.subgroupMap_surjective A) hker
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  have hBnq : ¬ CFSG.IsQuasisimple ↥B := fun h =>
    hBq (isQuasisimple_quotient_pCore_of_isQuasisimple h)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro k _ _ Γ D _ hDs
    refine ⟨fun α => hBnq ?_⟩
    have hq := isQuasisimple_of_mem_cComp_degree_two_quotient D hDs (cComp_map_mulEquiv α hB)
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (B.equivMapOfInjective α.toMonoidHom α.injective)).2 hq
  ·
    intro p f F _ h D _ hD
    refine ⟨fun α => hBnq ?_⟩
    exact unitary_three_embeddable_Ccomponent_quasisimple hB h D hD
      (α.toMonoidHom.comp B.subtype) (α.injective.comp B.subtype_injective)
  ·
    intro k _ _ _ Γ D _ hD
    refine ⟨fun α => hBq ?_⟩
    exact char_two_degree_three_scalar_quotient_Ccomponents_quasisimple_two_core_quotient D hD hB
      (α.toMonoidHom.comp B.subtype) (α.injective.comp B.subtype_injective)
  ·
    intro k _ _ _
    refine ⟨fun α => hBq ?_⟩
    have hαs : Function.Surjective α.toMonoidHom := α.surjective
    have : Finite (GL (Fin 2 ⊕ Fin 2) k) := Finite.of_injective _ Units.val_injective
    have hT := quasithinIsSylowTwo_of_sylow ((S.mapSurjective hηs).mapSurjective hαs)
    have hBst := cComp_map_mulEquiv α hB
    have hlt : B.map α.toMonoidHom ⊔
        (((S.mapSurjective hηs).mapSurjective hαs : Sylow 2 _) : Subgroup _) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hBnq ?_
      have h1 : B ⊔ (S : Subgroup K).map η = ⊤ := by
        have h2 : (B ⊔ (S : Subgroup K).map η).map α.toMonoidHom = ⊤ := by
          rw [Subgroup.map_sup, ← Sylow.coe_mapSurjective, ← Sylow.coe_mapSurjective]
          exact htop
        have h3 := congrArg (Subgroup.comap α.toMonoidHom) h2
        rwa [comap_map_eq_self_of_injective α.injective, comap_top] at h3
      have hsub : CFSG.Open.IsSubnormal B ⊤ := by
        have h4 := subnormal_of_mem_cComp hB1
        rwa [Subgroup.map_sup, ← hBdef, h1] at h4
      have hsub' : B.IsSubnormal :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib B).1
          ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open B ⊤).2 hsub)
      rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKN hsub' with
        hBtop | hcen
      · rw [hBtop]
        exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).2 hKN
      · exfalso
        apply ne_bot_of_mem_cComp hB
        have hcomm : ⁅B, B⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          exact hcen.trans (Subgroup.center_le_centralizer _)
        rw [← perfect_of_mem_cComp hB, hcomm]
    have hq :=
      NQTerm.characteristic_two_symplectic_four_Ccomponents_have_quasisimple_two_core_quotient
        hT hBst hlt
    exact isQuasisimple_quotient_pCore_of_mulEquiv
      (B.equivMapOfInjective α.toMonoidHom α.injective) hq

end CFSG.Quasithin.H13.NQCat
