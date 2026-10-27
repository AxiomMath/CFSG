module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBA7Perm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBSetup
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCommuting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.C58NS.MPB

open Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.L246A7

local notation "A₇" => alternatingGroup (Fin 7)

variable {G : Type} [Group G] [Finite G]

@[expose] def hat (L : Subgroup G) (α : ↥L →* A₇) (Y : Subgroup A₇) : Subgroup G :=
  (Y.comap α).map L.subtype

omit [Finite G] in
theorem mem_hat {L : Subgroup G} {α : ↥L →* A₇} {Y : Subgroup A₇} {x : G} :
    x ∈ hat L α Y ↔ ∃ h : x ∈ L, α ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, hy, rfl⟩

omit [Finite G] in
theorem hat_le {L : Subgroup G} {α : ↥L →* A₇} {Y : Subgroup A₇} : hat L α Y ≤ L := by
  rintro x hx
  exact (mem_hat.1 hx).1

omit [Finite G] in
theorem exists_normalised {L S : Subgroup G} (hS : IsSylowTwoOf S L) (α : ↥L →* A₇)
    (hα : Function.Surjective α) :
    ∃ β : ↥L →* A₇, Function.Surjective β ∧ β.ker = α.ker ∧
      (S.subgroupOf L).map β = Pstd.subgroupOf A₇ := by
  have hSbar := Setup.Family.isSylowTwoOf_map_range α hS
  rw [MonoidHom.range_eq_top.2 hα] at hSbar
  obtain ⟨-, hp, hodd⟩ := hSbar
  have hodd' : ¬ 2 ∣ ((S.subgroupOf L).map α).index := by
    have : (((S.subgroupOf L).map α).subgroupOf ⊤).index = ((S.subgroupOf L).map α).index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rwa [this] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 A₇ := hp.toSylow hodd'
  obtain ⟨σ, hσ⟩ := exists_conj_Pstd P
  refine ⟨(MulAut.conj σ).toMonoidHom.comp α, (MulAut.conj σ).surjective.comp hα, ?_, ?_⟩
  · exact MonoidHom.ker_comp_of_injective α (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective
  · rw [← Subgroup.map_map]
    exact hσ

omit [Finite G] in
theorem exists_perm_pres {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥L →* A₇) (hβ : Function.Surjective β) (hker : β.ker = CFSG.pCore 2 ↥L)
    (hS : (((T ⊓ L).subgroupOf L).map β) = Pstd.subgroupOf A₇) {t : G} (ht : t ∈ T) :
    ∃ π : Perm (Fin 7), π 6 = 6 ∧ ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) ∧
      ∀ (l : G) (hl : l ∈ L) (hl' : t * l * t⁻¹ ∈ L),
        ((β ⟨t * l * t⁻¹, hl'⟩ : A₇) : Perm (Fin 7)) = π * (β ⟨l, hl⟩ : Perm (Fin 7)) * π⁻¹ := by
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hTL ht
  set κ : MulAut ↥L := conjAct L ⟨t, htN⟩ with hκ
  have hκc : ∀ l : ↥L, ((κ l : ↥L) : G) = t * (l : G) * t⁻¹ := fun l => conj_coe_apply L ⟨t, htN⟩ l
  have hk : ∀ x ∈ β.ker, κ.toMonoidHom x ∈ β.ker := by
    intro x hx
    rw [hker] at hx ⊢
    have h1 : (x : G) ∈ pCoreOf 2 L := (L246.mem_blockQ_iff x).2 hx
    have h2 : t * (x : G) * t⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L htN) _).1 h1
    exact (L246.mem_blockQ_iff _).1 (by
      show ((κ x : ↥L) : G) ∈ pCoreOf 2 L
      rw [hκc]
      exact h2)
  obtain ⟨π, hπ⟩ := exists_perm_of_endo β hβ κ.toMonoidHom κ.surjective hk
  have hπl : ∀ (l : G) (hl : l ∈ L) (hl' : t * l * t⁻¹ ∈ L),
      ((β ⟨t * l * t⁻¹, hl'⟩ : A₇) : Perm (Fin 7)) = π * (β ⟨l, hl⟩ : Perm (Fin 7)) * π⁻¹ := by
    intro l hl hl'
    have := hπ ⟨l, hl⟩
    have e : κ.toMonoidHom ⟨l, hl⟩ = ⟨t * l * t⁻¹, hl'⟩ := Subtype.ext (hκc ⟨l, hl⟩)
    rw [e] at this
    exact this
  have hnorm : ∀ a ∈ Pstd, π * a * π⁻¹ ∈ Pstd := by
    intro a ha
    have ha' : (⟨a, Pstd_le_alt ha⟩ : A₇) ∈ (((T ⊓ L).subgroupOf L).map β) := by
      rw [hS]
      exact ha
    obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 ha'
    have hsT : (s : G) ∈ T := (Subgroup.mem_subgroupOf.1 hs).1
    have hconj : t * (s : G) * t⁻¹ ∈ T ⊓ L := by
      refine ⟨T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht), ?_⟩
      rw [← hκc]
      exact (κ s).2
    have hmem : β ⟨t * (s : G) * t⁻¹, hconj.2⟩ ∈ ((T ⊓ L).subgroupOf L).map β :=
      Subgroup.mem_map.2 ⟨⟨t * (s : G) * t⁻¹, hconj.2⟩, hconj, rfl⟩
    rw [hS] at hmem
    have h3 := hπl (s : G) s.2 hconj.2
    have h4 : ((β s : A₇) : Perm (Fin 7)) = a := congrArg Subtype.val hsa
    have h5 : ((β ⟨(s : G), s.2⟩ : A₇) : Perm (Fin 7)) = a := h4
    rw [h5] at h3
    rw [← h3]
    exact hmem
  have hN := normalizer_Pstd (τ := π⁻¹) (fun a ha => by simpa using hnorm a ha)
  refine ⟨π, ?_, ?_, hπl⟩
  · have := congrArg π hN.1
    simpa using this.symm
  · rcases hN.2 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · left
      exact ⟨by simpa using (congrArg π h4).symm, by simpa using (congrArg π h5).symm⟩
    · right
      exact ⟨by simpa using (congrArg π h5).symm, by simpa using (congrArg π h4).symm⟩

omit [Finite G] in
theorem conj_mem_hat {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥L →* A₇) (hβ : Function.Surjective β) (hker : β.ker = CFSG.pCore 2 ↥L)
    (hS : (((T ⊓ L).subgroupOf L).map β) = Pstd.subgroupOf A₇) {Y : Subgroup A₇}
    (hY : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
      ∀ a ∈ Y, MulAut.conjNormal π a ∈ Y) {t : G} (ht : t ∈ T) {x : G} (hx : x ∈ hat L β Y) :
    t * x * t⁻¹ ∈ hat L β Y := by
  obtain ⟨π, h6, h45, hπ⟩ := exists_perm_pres hTL β hβ hker hS ht
  obtain ⟨hxL, hxY⟩ := mem_hat.1 hx
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hTL ht
  have hl' : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 htN x).1 hxL
  refine mem_hat.2 ⟨hl', ?_⟩
  have e : β ⟨t * x * t⁻¹, hl'⟩ = MulAut.conjNormal π (β ⟨x, hxL⟩) :=
    Subtype.ext (by rw [hπ x hxL hl', MulAut.conjNormal_apply])
  rw [e]
  exact hY π h6 h45 _ hxY

omit [Finite G] in
theorem T_le_normalizer_hat {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥L →* A₇) (hβ : Function.Surjective β) (hker : β.ker = CFSG.pCore 2 ↥L)
    (hS : (((T ⊓ L).subgroupOf L).map β) = Pstd.subgroupOf A₇) {Y : Subgroup A₇}
    (hY : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
      ∀ a ∈ Y, MulAut.conjNormal π a ∈ Y) :
    T ≤ Subgroup.normalizer (hat L β Y : Set G) := fun t ht =>
  Setup.Campbell.mem_normalizer_of_conj_mem (fun _ hx => conj_mem_hat hTL β hβ hker hS hY ht hx)
    (fun _ hx => by
      simpa using conj_mem_hat hTL β hβ hker hS hY (T.inv_mem ht) hx)

omit [Finite G] in
theorem sup_ne_of_ne_top {H T L : Subgroup G} (hLH : L ≤ H)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (β : ↥L →* A₇) (hβ : Function.Surjective β)
    (hker : β.ker = CFSG.pCore 2 ↥L) (hS : (((T ⊓ L).subgroupOf L).map β) = Pstd.subgroupOf A₇)
    {Y : Subgroup A₇}
    (hY : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
      ∀ a ∈ Y, MulAut.conjNormal π a ∈ Y)
    (hPY : Pstd.subgroupOf A₇ ≤ Y) (hYtop : Y ≠ ⊤) : T ⊔ hat L β Y ≠ H := by
  intro hZ
  obtain ⟨g, hg⟩ : ∃ g : A₇, g ∉ Y := by
    by_contra h
    push Not at h
    exact hYtop (Subgroup.eq_top_iff' Y |>.2 h)
  obtain ⟨l₀, rfl⟩ := hβ g
  have hTY := T_le_normalizer_hat hTL β hβ hker hS hY
  have hl₀ : (l₀ : G) ∈ (hat L β Y ⊔ T : Subgroup G) := by
    rw [sup_comm, hZ]
    exact hLH l₀.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTY] at hl₀
  obtain ⟨y, hy, t, ht, hyt⟩ := Set.mem_mul.1 hl₀
  obtain ⟨hyL, hyY⟩ := mem_hat.1 hy
  have htL : t ∈ L := by
    have : t = y⁻¹ * (l₀ : G) := by rw [← hyt]; group
    rw [this]
    exact L.mul_mem (L.inv_mem hyL) l₀.2
  have htS : β ⟨t, htL⟩ ∈ Pstd.subgroupOf A₇ := by
    rw [← hS]
    exact Subgroup.mem_map.2 ⟨⟨t, htL⟩, ⟨ht, htL⟩, rfl⟩
  have hl₀' : l₀ = ⟨y, hyL⟩ * ⟨t, htL⟩ := Subtype.ext hyt.symm
  apply hg
  rw [hl₀', map_mul]
  exact Y.mul_mem hyY (hPY htS)

theorem le_of_seven {H T N L : Subgroup G} (hmin : MinParabolic H T N) (hLsub : IsSubnormal L H)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (α : ↥L →* A₇) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : L ≤ N := by
  have hLH : L ≤ H := A4.subnormal_le hLsub
  have hSyl : IsSylowTwoOf (T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hLsub hmin.isSylow
  obtain ⟨β, hβ, hβk, hS⟩ := exists_normalised hSyl α hα
  have hker' : β.ker = CFSG.pCore 2 ↥L := hβk.trans hker
  have hY1 : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
      ∀ a ∈ Y1, MulAut.conjNormal π a ∈ Y1 := fun π h6 _ a ha => by
    have := conj_mem_Y1 h6 (show (a : Perm (Fin 7)) ∈ S6 from ha)
    rw [mem_Y1, MulAut.conjNormal_apply]
    exact this
  have hY2 : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
      ∀ a ∈ Y2, MulAut.conjNormal π a ∈ Y2 := fun π h6 h45 a ha => by
    have := conj_mem_Y2 h6 h45 (show (a : Perm (Fin 7)) ∈ PB from ha)
    show ((MulAut.conjNormal π a : A₇) : Perm (Fin 7)) ∈ PB
    rw [MulAut.conjNormal_apply]
    exact this
  have hTH : T ≤ H := hmin.isSylow.1
  have hZ1 : T ⊔ hat L β Y1 ≤ N := le_of_proper_over hmin (sup_le hTH (hat_le.trans hLH))
    le_sup_left (sup_ne_of_ne_top hLH hTL β hβ hker' hS hY1 P0_le_Y1 Y1_ne_top)
  have hZ2 : T ⊔ hat L β Y2 ≤ N := le_of_proper_over hmin (sup_le hTH (hat_le.trans hLH))
    le_sup_left (sup_ne_of_ne_top hLH hTL β hβ hker' hS hY2 P0_le_Y2 Y2_ne_top)
  have hL : L ≤ hat L β Y1 ⊔ hat L β Y2 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥L) ∈ Y1.comap β ⊔ Y2.comap β := by
      rw [Subgroup.comap_sup_eq β Y1 Y2 hβ, Y1_sup_Y2]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem L.subtype h1
    rwa [Subgroup.map_sup] at h2
  exact hL.trans (sup_le (le_sup_right.trans hZ1) (le_sup_right.trans hZ2))

end CFSG.Quasithin.C58NS.MPB
