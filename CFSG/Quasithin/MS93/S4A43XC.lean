module

public import CFSG.Quasithin.MS93.S4A43XB

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Comm

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem vv_comm_of_dist {x y : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) (hy : IsMVtx _ y)
    (hd : (puAmalgam h.le).treeGraph.dist x y + 4 < critDist (puAmalgam h.le)) :
    Vv (puAmalgam h.le) y ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) x : Set (puAmalgam h.le).Universal) := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hy hρ
  refine hρμ.trans ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨μ', hμ', hdμ', hρμ'⟩ := exists_zv_le_zm h hx hρ'
  refine hρμ'.trans (zm_le_centralizer_zm h hμ' hμ ?_)
  have h1 := dist_triangle (puAmalgam h.le) μ' x μ
  have h2 := dist_triangle (puAmalgam h.le) x y μ
  rw [tdist_comm _ μ' x] at h1
  omega

end Comm

section Gab

variable {A B : Type} {C : Type} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem gab_le_normalizer_usup (α ρ : Vtx X) :
    Gab X α ρ ≤ Subgroup.normalizer (Usup X α ρ : Set X.Universal) := by
  rw [Usup]
  refine le_normalizer_commutator ?_ inf_le_right
  exact inf_le_left.trans (stab_le_normalizer_of_smul _ (fun g δ => zv_smul _ g δ) α)

end Gab

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem eq_bot_or_eq_uloc {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {N : Subgroup 𝔘}
    (hN : N ≤ Uloc h.le L μ) (hn : stab 𝔛 μ ≤ Subgroup.normalizer (N : Set 𝔘)) :
    N = ⊥ ∨ N = Uloc h.le L μ := by
  obtain ⟨ψ, hsurj, hψ⟩ := exists_natural_Uloc h c.via hμ
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : ↥(Uloc h.le L μ), (u : 𝔘) ∈ N ∧ natVec hψ u = v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', N.mul_mem hu hu', natVec_mul hψ u u'⟩
      zero_mem' := ⟨1, N.one_mem, natVec_one hψ⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, N.inv_mem hu, natVec_inv hψ u⟩ }
  have hS : ∀ (g : SL3 F), ∀ v ∈ S, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ S := by
    rintro g _ ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := toSL3_surjective hsurj g
    have hmem : (a : 𝔘) * u * (a : 𝔘)⁻¹ ∈ Uloc h.le L μ :=
      (Subgroup.mem_normalizer_iff.mp (hψ.1 a.2) u).mp u.2
    refine ⟨⟨_, hmem⟩, (Subgroup.mem_normalizer_iff.mp (hn a.2) u).mp hu, ?_⟩
    exact (natVec_conj hψ a u ⟨_, hmem⟩ rfl)
  have hx0 : natVec hψ ⟨x, hN hxN⟩ ≠ 0 := by
    intro h0
    apply hx1
    have : (⟨x, hN hxN⟩ : ↥(Uloc h.le L μ)) = 1 :=
      natVec_injective hψ (by rw [h0, natVec_one])
    have hx' : x = 1 := congrArg Subtype.val this
    exact Subtype.ext hx'
  refine le_antisymm hN fun y hy => ?_
  obtain ⟨u, hu, huy⟩ := mem_of_invariant S hS ⟨⟨x, hN hxN⟩, hxN, rfl⟩ hx0
    (natVec hψ ⟨y, hy⟩)
  have := natVec_injective hψ huy
  rw [show y = (u : 𝔘) from (congrArg Subtype.val this).symm]
  exact hu

theorem commutator_uloc_le_of_inf_ne_bot {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {A B : Subgroup 𝔘}
    (hA : A ≤ stab 𝔛 μ) (hB : B ≤ stab 𝔛 μ)
    (hq : Nat.card ↥⁅Uloc h.le L μ, A⁆ = Fintype.card F)
    (hne : ⁅Uloc h.le L μ, A⁆ ⊓ ⁅Uloc h.le L μ, B⁆ ≠ ⊥) :
    ⁅Uloc h.le L μ, A⁆ ≤ ⁅Uloc h.le L μ, B⁆ := by
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hμ
  have hUA : ⁅Uloc h.le L μ, A⁆ ≤ Uloc h.le L μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans hψ.1)
  have h1 : Module.finrank F (commN (natImage ψ A)) = 1 := by
    have := hq
    rw [card_commutator_eq hψ hA, Module.natCard_eq_pow_finrank (K := F),
      ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq2 (show Nat.card F ^ _ = Nat.card F ^ 1 by
      rw [this, pow_one])
  obtain ⟨⟨x, hxA, hxB⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1 : x ≠ 1 := fun e => hx1' (Subtype.ext e)
  have hxU : (x : 𝔘) ∈ Uloc h.le L μ := hUA hxA
  have hvA := (mem_commutator_iff_natVec hψ hA ⟨x, hxU⟩).mp hxA
  have hvB := (mem_commutator_iff_natVec hψ hB ⟨x, hxU⟩).mp hxB
  have hv0 : natVec hψ ⟨x, hxU⟩ ≠ 0 := by
    intro h0
    apply hx1
    have : (⟨x, hxU⟩ : ↥(Uloc h.le L μ)) = 1 := natVec_injective hψ (by rw [h0, natVec_one])
    exact congrArg Subtype.val this
  have hspan : Submodule.span F {natVec hψ ⟨x, hxU⟩} = commN (natImage ψ A) :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hvA)
      (by rw [finrank_span_singleton hv0, h1])
  have hAB : commN (natImage ψ A) ≤ commN (natImage ψ B) := by
    rw [← hspan]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hvB
  intro y hy
  have hyU := hUA hy
  exact (mem_commutator_iff_natVec hψ hB ⟨y, hyU⟩).mpr
    (hAB ((mem_commutator_iff_natVec hψ hA ⟨y, hyU⟩).mp hy))

theorem not_le_normalizer_usup {μ ρ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμρ : 𝔄 μ ρ) :
    ¬ stab 𝔛 μ ≤ Subgroup.normalizer (Usup 𝔛 μ ρ : Set 𝔘) := by
  intro hn
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hμ
  have hc := c.card_usup hμ hμρ
  rcases c.eq_bot_or_eq_uloc hμ (c.usup_le_uloc hμ hμρ) hn with h0 | h0
  · rw [h0, Subgroup.card_bot] at hc
    have : 4 ≤ Fintype.card F ^ 2 := by nlinarith
    omega
  · rw [h0, card_eq_of_natural hψ, Nat.card_eq_fintype_card] at hc
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

theorem not_critR_le_usup_of_gen {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α) : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ρ := by
  intro hRU
  apply c.not_le_normalizer_usup hs.1.1 hαρ
  rw [← hgen]
  refine sup_le (gab_le_normalizer_usup _ α ρ) ?_
  have hUZ : Usup 𝔛 α ρ ≤ ZM 𝔛 α := (c.usup_le_uloc hs.1.1 hαρ).trans (uloc_le_zm h c.full hs.1.1)
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rintro _ ⟨u, hu, rfl⟩
  have e : (MulAut.conj z).toMonoidHom u = ⁅z, u⁆ * u := by simp [commutatorElement_def]
  rw [e]
  refine Subgroup.mul_mem _ (hRU ?_) hu
  rw [critR, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hz (hUZ hu)

theorem eight_le_critDist : 8 ≤ critDist 𝔛 := by
  have h6 := c.six_lt_critDist
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  omega

theorem concl436 {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : Concl436 h.le L α α' := by
  intro hnC
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hα'M : IsMVtx 𝔛 α' := (c.crit_symm hs).1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hs.1.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by rw [tdist_comm]; exact hd
  have hα'ε : 𝔄 α' (geo 𝔛 α' α 1) := adj_geo_one _ (by omega)
  have hεγ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hγζ : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := adj_geo _ (i := 2) (by omega)
  have hζη : 𝔄 (geo 𝔛 α' α 3) (geo 𝔛 α' α 4) := adj_geo _ (i := 3) (by omega)
  have hηκ : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := adj_geo _ (i := 4) (by omega)
  have hγM : IsMVtx 𝔛 (geo 𝔛 α' α 2) := c.isMVtx_geo_two' hs
  have hζH : ¬ IsMVtx 𝔛 (geo 𝔛 α' α 3) := by rw [← isMVtx_iff_of_adj _ hγζ]; exact hγM
  have hηM : IsMVtx 𝔛 (geo 𝔛 α' α 4) := by have := isMVtx_iff_of_adj _ hζη; tauto
  have hdαη : (puAmalgam h.le).treeGraph.dist α (geo 𝔛 α' α 4) = critDist 𝔛 - 4 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd']
  have hdακ : (puAmalgam h.le).treeGraph.dist α (geo 𝔛 α' α 5) = critDist 𝔛 - 5 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd']
  obtain ⟨g, hg, hgε⟩ := exists_mem_stab_smul _ hεγ.symm hγζ
  have hgγ : g • geo 𝔛 α' α 2 = geo 𝔛 α' α 2 := (mem_stab _).mp hg
  have hlM : IsMVtx 𝔛 (g • α') := (isMVtx_smul _ g α').mpr hα'M
  have hlζ : 𝔄 (geo 𝔛 α' α 3) (g • α') := by
    have := (adj_smul _ g _ _).mpr hα'ε.symm
    rwa [hgε] at this
  have hR0 : critR0 𝔛 α α' = Usup 𝔛 (g • α') (geo 𝔛 α' α 3) := by
    rw [← hgε, usup_smul, ← c.critR0_eq hs, map_conj_eq_of_le_centralizer
      (c.critR0_le_centralizer hs) hg]
  have hlN : g • α' ∈ nablaSet h.le L (geo 𝔛 α' α 2) := by
    rw [← hgγ]
    exact (mem_nablaSet_smul h g _ α').mpr (c.mem_nablaSet_geo_two' hs.1)
  have hR0U : critR0 𝔛 α α' ≤ Uloc h.le L (g • α') := hR0 ▸ c.usup_le_uloc hlM hlζ.symm
  have hR0Z : critR0 𝔛 α α' ≤ ZM 𝔛 (geo 𝔛 α' α 4) :=
    hR0 ▸ (c.usup_le_zh hlM hlζ.symm).trans (zh_le_zm _ hζη.symm)
  have hZ := c.concl434 _ _ _ hζH hlζ hζη fun hle => hnC ((le_inf hR0U hR0Z).trans hle)
  have hdγη : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) (geo 𝔛 α' α 4) = 2 := by
    rw [dist_geo_geo _ (by omega) (by omega)]
  have hηN : geo 𝔛 α' α 4 ∈ nablaSet h.le L (geo 𝔛 α' α 2) := by
    refine ⟨hdγη, ?_⟩
    rw [zv_of_isMVtx _ hηM, ← hZ, ← zv_of_isMVtx _ hlM]
    exact hlN.2
  have hR0η : critR0 𝔛 α α' = Usup 𝔛 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := by
    rw [hR0, Usup, Usup, zv_of_isMVtx _ hlM, zv_of_isMVtx _ hηM, hZ]
  refine ⟨hηN, fun ρ hαρ hgen => ?_⟩
  by_contra hW
  have hρH : ¬ IsMVtx 𝔛 ρ := by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα
  obtain ⟨μ, ⟨hρμ, hαμ⟩, hVμ⟩ : ∃ μ ∈ {μ : Vtx 𝔛 | 𝔄 ρ μ ∧ α ∈ nablaSet h.le L μ},
      ¬ Vv 𝔛 μ ≤ Qv 𝔛 (geo 𝔛 α' α 4) := by
    by_contra hall
    push Not at hall
    exact hW (iSup₂_le hall)
  have hμM : IsMVtx 𝔛 μ := by have := isMVtx_iff_of_adj _ hρμ; tauto
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 2 := hαμ.1
  obtain ⟨ν, hνM, hμν, hZν⟩ : ∃ ν, IsMVtx 𝔛 ν ∧ (puAmalgam h.le).treeGraph.dist μ ν ≤ 2 ∧
      ¬ ZM 𝔛 ν ≤ Qv 𝔛 (geo 𝔛 α' α 4) := by
    by_contra hall
    push Not at hall
    apply hVμ
    refine iSup₂_le fun x hx => ?_
    obtain ⟨ν, hνM, hdν, hxν⟩ := exists_zv_le_zm h hμM hx
    exact hxν.trans (hall ν hνM hdν)
  have hge : critDist 𝔛 ≤ (puAmalgam h.le).treeGraph.dist ν (geo 𝔛 α' α 4) := by
    by_contra hlt
    exact hZν (zm_le_qv_of_dist_lt _ hνM (by omega))
  have ht1 := dist_triangle (puAmalgam h.le) ν μ (geo 𝔛 α' α 4)
  have ht2 := dist_triangle (puAmalgam h.le) μ α (geo 𝔛 α' α 4)
  rw [tdist_comm _ ν μ] at ht1
  have hdνη : (puAmalgam h.le).treeGraph.dist ν (geo 𝔛 α' α 4) = critDist 𝔛 := by omega
  have hdνμ : (puAmalgam h.le).treeGraph.dist ν μ = 2 := by rw [tdist_comm]; omega
  have hdμη : (puAmalgam h.le).treeGraph.dist μ (geo 𝔛 α' α 4) = critDist 𝔛 - 2 := by omega
  have hcrit : IsCritical 𝔛 ν (geo 𝔛 α' α 4) := ⟨hνM, hdνη, hZν⟩
  have hgeo2 : geo 𝔛 ν (geo 𝔛 α' α 4) 2 = μ :=
    (eq_geo_of_dist _ hdνμ (by rw [hdνμ, hdμη, hdνη]; omega)).symm
  have hνN : ν ∈ nablaSet h.le L μ := hgeo2 ▸ c.mem_nablaSet_geo_two hcrit
  have hρgeo : geo 𝔛 μ α 1 = ρ :=
    (eq_geo_one _ hρμ.symm (by rw [dist_eq_one_of_adj _ hαρ.symm, hdμα])).symm
  have hH := c.concl432 hμM
  have hνQ : ⁅ZM 𝔛 ν, Qv 𝔛 μ⁆ = Usup 𝔛 α ρ := by
    rw [← (hH.2 ν hνN).1, (hH.2 α hαμ).1, (hH.2 α hαμ).2, hρgeo]
  have hZηQ : ZM 𝔛 (geo 𝔛 α' α 4) ≤ Qv 𝔛 μ :=
    zm_le_qv_of_dist_lt _ hηM (by rw [tdist_comm, hdμη]; omega)
  have hN1 : ⁅ZM 𝔛 ν, ZM 𝔛 (geo 𝔛 α' α 4)⁆ ≤ Usup 𝔛 α ρ :=
    hνQ ▸ Subgroup.commutator_mono le_rfl hZηQ
  have hgenW : ∀ μ' ∈ {μ : Vtx 𝔛 | 𝔄 ρ μ ∧ α ∈ nablaSet h.le L μ}, IsMVtx 𝔛 μ' ∧
      (puAmalgam h.le).treeGraph.dist α μ' ≤ 2 := fun μ' hμ' => by
    have hμ'M : IsMVtx 𝔛 μ' := by have := isMVtx_iff_of_adj _ hμ'.1; tauto
    refine ⟨hμ'M, ?_⟩
    have := dist_triangle (puAmalgam h.le) α ρ μ'
    rw [dist_eq_one_of_adj _ hαρ, dist_eq_one_of_adj _ hμ'.1] at this
    exact this
  have hWκ : Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 5) := iSup₂_le fun μ' hμ' => by
    obtain ⟨hμ'M, hdμ'⟩ := hgenW μ' hμ'
    refine vv_le_qv_of_dist h hμ'M ?_
    have := dist_triangle (puAmalgam h.le) μ' α (geo 𝔛 α' α 5)
    rw [tdist_comm _ μ' α, hdακ] at this
    omega
  have hWc : Wnab h.le L α ρ ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) := iSup₂_le fun μ' hμ' => by
    obtain ⟨hμ'M, hdμ'⟩ := hgenW μ' hμ'
    exact vv_comm_of_dist h hα hμ'M (by omega)
  obtain ⟨x, hxW, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  have hR0Uη : critR0 𝔛 α α' ≤ Uloc h.le L (geo 𝔛 α' α 4) :=
    hR0η ▸ c.usup_le_uloc hηM hζη.symm
  have hR0le : critR0 𝔛 α α' ≤ Usup 𝔛 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := fun r hr =>
    c.mem_usup_of_commute hηM hηκ (hWκ hxW) hxQ (hR0Uη hr)
      (Subgroup.mem_centralizer_iff.mp (hWc hxW) r (critR0_le_vv h hs hr)).symm
  have hfinU : Finite ↥(Usup 𝔛 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5)) := by
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hηκ]; exact hηM)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_zh hηM hηκ).trans (zh_le_qv _ _)))
  have hR0eq : critR0 𝔛 α α' = Usup 𝔛 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) :=
    Subgroup.eq_of_le_of_card_ge hR0le (by rw [c.card_usup hηM hηκ, c.card_critR0 hs])
  have hZνκ : ZM 𝔛 ν ≤ Qv 𝔛 (geo 𝔛 α' α 5) := by
    refine le_trans ?_ hWκ
    refine le_trans ?_ (le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx 𝔛 | 𝔄 ρ μ ∧
      α ∈ nablaSet h.le L μ}) => Vv 𝔛 μ) μ ⟨hρμ, hαμ⟩ le_rfl)
    rw [← zv_of_isMVtx _ hνM]
    exact zv_le_vv h hμν
  have hN2 : ⁅ZM 𝔛 ν, ZM 𝔛 (geo 𝔛 α' α 4)⁆ ≤ critR0 𝔛 α α' := by
    rw [hR0eq, Usup, zv_of_isMVtx _ hηM, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hZνκ
  have hN3 : ⁅ZM 𝔛 ν, ZM 𝔛 (geo 𝔛 α' α 4)⁆ ≤ critR 𝔛 α α' := by
    rw [← c.critR0_inf_zm hs]
    exact le_inf hN2 (hN1.trans ((c.usup_le_uloc hα hαρ).trans (uloc_le_zm h c.full hα)))
  have hNne : ⁅ZM 𝔛 ν, ZM 𝔛 (geo 𝔛 α' α 4)⁆ ≠ ⊥ :=
    ms22_ii _ h.hyp20 h.critDist_pos c.cent hcrit
  have hRU : critR 𝔛 α α' ≤ Usup 𝔛 α ρ := by
    have hZs := zm_le_stab_of_star h hs
    have hTs : Qv 𝔛 ρ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαρ.symm
    rw [critR, commutator_zm_eq_uloc h c.full hα hZs, usup_eq_commutator_uloc h c.full hα hαρ]
    refine c.commutator_uloc_le_of_inf_ne_bot hα hZs hTs ?_ ?_
    · rw [← commutator_zm_eq_uloc h c.full hα hZs]
      exact c.card_critR hs
    · intro hbot
      apply hNne
      rw [eq_bot_iff, ← hbot, ← commutator_zm_eq_uloc h c.full hα hZs,
        ← usup_eq_commutator_uloc h c.full hα hαρ]
      exact le_inf hN3 hN1
  exact c.not_critR_le_usup_of_gen hs hαρ hgen hRU

end Ctx43

end CFSG.Quasithin.MS93.S4A
