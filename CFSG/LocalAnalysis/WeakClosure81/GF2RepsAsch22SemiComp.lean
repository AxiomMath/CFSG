module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiCenter
import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
import CFSG.LocalAnalysis.ComponentClassification.Sol78Semisimple
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem center_eq_bot_of_isComponent_of_layer_eq_top {G : Type*} [Group G] [Finite G]
    (hE : CFSG.layer G = ⊤) (hZ : Subgroup.center G = ⊥) {K : Subgroup G}
    (hK : IsComponent K) : Subgroup.center K = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzC : (z : G) ∈ Subgroup.centralizer (CFSG.layer G : Set G) :=
    CFSG.LocalCores.center_component_le_centralizer_layer hK
      (Subgroup.mem_map_of_mem K.subtype hz)
  have hzG : (z : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_iff.mp (by simpa [hE] using hzC) g
      (Subgroup.mem_top g)
  rw [hZ, Subgroup.mem_bot] at hzG
  exact Subtype.ext hzG

theorem commutator_eq_self_of_normal_of_layer_eq_top {G : Type*} [Group G] [Finite G]
    (hE : CFSG.layer G = ⊤) (hZ : Subgroup.center G = ⊥) {N : Subgroup G}
    (hN : N.Normal) : ⁅N, N⁆ = N := by
  refine CFSG.AGLEmbedding.commutator_eq_self_of_le_layer ?_ hN ?_
  · intro K hK
    exact center_eq_bot_of_isComponent_of_layer_eq_top hE hZ
      ((CFSG.isComponent_iff_open K).mpr hK)
  · rw [hE]
    exact le_top

theorem center_eq_bot_of_normal_of_layer_eq_top {G : Type*} [Group G] [Finite G]
    (hE : CFSG.layer G = ⊤) (hZ : Subgroup.center G = ⊥) {N : Subgroup G}
    (hN : N.Normal) : Subgroup.center ↥N = ⊥ := by
  let A : Subgroup G := (Subgroup.center ↥N).map N.subtype
  let hNnormal : N.Normal := hN
  let hZchar : (Subgroup.center ↥N).Characteristic := Subgroup.centerCharacteristic
  have hAn : A.Normal := ConjAct.normal_of_characteristic_of_normal
  let hAnormal : A.Normal := hAn
  have hAsolv : Group.IsSolvable A := by
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨w, hw, hwb⟩ := Subgroup.mem_map.mp b.2
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hza, ← hwb]
    exact congrArg N.subtype ((Subgroup.mem_center_iff.mp hz w).symm)
  have hAle : A ≤ Subgroup.center G :=
    (CFSG.SectionRank.semisimple_solvable_quotient hE A hAsolv).1
  have hAbot : A = ⊥ := le_bot_iff.mp (hAle.trans (le_of_eq hZ))
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzA : (z : G) ∈ A := Subgroup.mem_map_of_mem N.subtype hz
  rw [hAbot, Subgroup.mem_bot] at hzA
  exact Subtype.ext hzA

theorem exists_le_centralizer_inf_eq_bot (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y]
    (hKY : CFSG.Open.IsKGroup Y) (hrk : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3)
    (Q : Subgroup Y) [Q.Normal] (hQ : IsPGroup p Q)
    (hE : CFSG.layer (Y ⧸ Q) = ⊤) (hZ : Subgroup.center (Y ⧸ Q) = ⊥) :
    ∃ I : Subgroup Y, I ≤ Subgroup.centralizer (Q : Set Y) ∧ I ⊓ Q = ⊥ ∧
      I ⊔ Q = Subgroup.centralizer (Q : Set Y) ⊔ Q := by
  classical
  have hpFact : Fact p.Prime := ⟨hp⟩
  let π : Y →* Y ⧸ Q := QuotientGroup.mk' Q
  let C : Subgroup Y := Subgroup.centralizer (Q : Set Y)
  let Cbar : Subgroup (Y ⧸ Q) := C.map π
  let D : Subgroup ↥C := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C
  let I : Subgroup Y := D.map C.subtype
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCbar_n : Cbar.Normal :=
    Subgroup.Normal.map hCn π (QuotientGroup.mk'_surjective Q)
  have hCbar_perfect : ⁅Cbar, Cbar⁆ = Cbar :=
    commutator_eq_self_of_normal_of_layer_eq_top hE hZ hCbar_n
  let hCbarPerfect : Group.IsPerfect ↥Cbar := Subgroup.isPerfect_iff.mpr hCbar_perfect
  have hCbar_layer : CFSG.layer ↥Cbar = ⊤ :=
    CFSG.ComponentClassification.Sol78.layer_eq_top_of_normal_of_perfect hE hCbar_n
      hCbar_perfect
  have hCbar_center : Subgroup.center ↥Cbar = ⊥ :=
    center_eq_bot_of_normal_of_layer_eq_top hE hZ hCbar_n
  let fC : ↥C →* ↥Cbar :=
    (π.comp C.subtype).codRestrict Cbar fun c => Subgroup.mem_map_of_mem π c.2
  have hfC : Function.Surjective fC := by
    intro x
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp x.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩
  have hDtop : D.map fC = ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
      fC hfC
  have hDmap : D.map (π.comp C.subtype) = Cbar := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map_of_mem π d.2
    · intro y hy
      have hy' : (⟨y, hy⟩ : ↥Cbar) ∈ D.map fC := by
        rw [hDtop]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdf⟩ := Subgroup.mem_map.mp hy'
      exact ⟨d, hd, congrArg Subtype.val hdf⟩
  have hI_le_C : I ≤ C := by
    dsimp [I]
    exact Subgroup.map_subtype_le D
  have hImap : I.map π = Cbar := by
    dsimp [I]
    rw [Subgroup.map_map]
    exact hDmap
  have hIsup : I ⊔ Q = C ⊔ Q := by
    have hker : π.ker = Q := QuotientGroup.ker_mk' Q
    calc I ⊔ Q = I ⊔ π.ker := by rw [hker]
      _ = (I.map π).comap π := (Subgroup.comap_map_eq (f := π) (H := I)).symm
      _ = (C.map π).comap π := by rw [hImap]
      _ = C ⊔ π.ker := Subgroup.comap_map_eq (f := π) (H := C)
      _ = C ⊔ Q := by rw [hker]
  let gI : ↥I →* ↥Cbar :=
    (π.comp I.subtype).codRestrict Cbar fun x =>
      hImap ▸ Subgroup.mem_map_of_mem π x.2
  have hgI : Function.Surjective gI := by
    intro y
    have hy : y.1 ∈ I.map π := by
      rw [hImap]
      exact y.2
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxπ⟩
  have hker_center : gI.ker ≤ Subgroup.center ↥I := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro i
    apply Subtype.ext
    have hx1 : gI x = 1 := MonoidHom.mem_ker.mp hx
    have hxQ : (x : Y) ∈ Q := by
      have hxker : (x : Y) ∈ π.ker := MonoidHom.mem_ker.mpr (by
        have h := congrArg Subtype.val hx1
        simpa [gI] using h)
      simpa [π, QuotientGroup.ker_mk'] using hxker
    exact (Subgroup.mem_centralizer_iff.mp (hI_le_C i.2) (x : Y) hxQ).symm
  have hIperf : Group.IsPerfect ↥I :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect C
  have hquotlayer : CFSG.layer (↥I ⧸ gI.ker) = ⊤ :=
    CFSG.ComponentClassification.Sol78.layer_eq_top_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective gI hgI).symm hCbar_layer
  have hIlayer : CFSG.layer ↥I = ⊤ :=
    CFSG.SectionRank.perfect_central_semisimple_extension hIperf gI.ker
      hker_center hquotlayer
  have hcenter_map_bot : (Subgroup.center ↥I).map gI = ⊥ := by
    refine le_bot_iff.mp fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hzC : gI z ∈ Subgroup.center ↥Cbar := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨x, rfl⟩ := hgI w
      exact congrArg gI (Subgroup.mem_center_iff.mp hz x)
    rw [hCbar_center, Subgroup.mem_bot] at hzC
    exact hzC
  have hcenter_le_Q : ∀ z : ↥(Subgroup.center ↥I), ((z : ↥I) : Y) ∈ Q := by
    intro z
    have hzker : (z : ↥I) ∈ gI.ker := by
      have hzbot : gI (z : ↥I) ∈ (⊥ : Subgroup ↥Cbar) :=
        hcenter_map_bot ▸ Subgroup.mem_map_of_mem gI z.2
      exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hzbot)
    have hz1 : gI (z : ↥I) = 1 := MonoidHom.mem_ker.mp hzker
    have hzker' : ((z : ↥I) : Y) ∈ π.ker := MonoidHom.mem_ker.mpr (by
      have h := congrArg Subtype.val hz1
      simpa [gI] using h)
    simpa [π, QuotientGroup.ker_mk'] using hzker'
  have hcenterP : IsPGroup p ↥(Subgroup.center ↥I) := by
    let f : ↥(Subgroup.center ↥I) →* Y :=
      I.subtype.comp (Subgroup.center ↥I).subtype
    have hf : Function.Injective f := by
      intro a b h
      exact Subtype.ext (Subtype.ext h)
    have hcomap : Q.comap f = ⊤ := by
      ext z
      constructor
      · intro _
        exact Subgroup.mem_top z
      · intro _
        exact hcenter_le_Q z
    have h := hQ.comap_of_injective f hf
    rw [hcomap] at h
    exact IsPGroup.of_equiv h Subgroup.topEquiv
  have hcenterI : Subgroup.center ↥I = ⊥ := by
    have hnd := not_dvd_card_center_of_layer_eq_top hC5 hKY hp hp5 hrk I
      (MonoidHom.id ↥I) (fun x => ⟨x, rfl⟩) hIlayer
    rcases IsPGroup.card_eq_or_dvd (p := p) (G := ↥(Subgroup.center ↥I))
      hcenterP with hcard | hdvd
    · exact (Subgroup.card_eq_one (H := Subgroup.center ↥I)).mp hcard
    · exact absurd hdvd hnd
  have hIinf : I ⊓ Q = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_inf] at hx
    have hxcenter : (⟨x, hx.1⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro i
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hI_le_C i.2) x hx.2).symm
    rw [hcenterI, Subgroup.mem_bot] at hxcenter
    exact congrArg Subtype.val hxcenter
  exact ⟨I, hI_le_C, hIinf, hIsup⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch22
