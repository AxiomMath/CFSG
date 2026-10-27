module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8HypMod
public import CFSG.Quasithin.Vol2.Ch12Sec4C8NoOff
public import CFSG.Quasithin.Background.E6Fourteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Orbit

open G2Hyp

namespace G2HypFin

theorem card_g2Derived_two :
    Nat.card ↥(g2Derived (ZMod 2)) = 6048 := by
  rw [g2Derived, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.commutator_le_self _ : ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≤ _)).toEquiv]
  exact S1549D.card_commutator_quasithinG2_two (Nat.card_zmod 2)

theorem index_g2Derived_two :
    (g2Derived (ZMod 2)).index = 2 := by
  have h1 := (g2Derived (ZMod 2)).card_mul_index
  rw [card_g2Derived_two, card_g2Two] at h1
  omega

theorem le_Mb0_of_le_normalizer
    {X : Subgroup (MulAut ModO)} (hX : X ≤ Subgroup.normalizer (Lb0 : Set (MulAut ModO))) :
    X ≤ Mb0 := fun x hx =>
  normalizer_two_O x fun h => Subgroup.mem_normalizer_iff.1 (hX hx) h

theorem Mb0_le_of_lt
    {Mb : Subgroup (MulAut ModO)} (hlt : Lb0 < Mb) (hMb : Mb ≤ Mb0) : Mb0 ≤ Mb := by
  obtain ⟨m, hm, hmL⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨gm, rfl⟩ := hMb hm
  have hgm : gm ∉ g2Derived (ZMod 2) := fun h => hmL ⟨gm, h, rfl⟩
  rintro _ ⟨g, rfl⟩
  by_cases hg : g ∈ g2Derived (ZMod 2)
  · exact hlt.le ⟨g, hg, rfl⟩
  · have h2 : gm⁻¹ * g ∈ g2Derived (ZMod 2) := by
      rw [Subgroup.mul_mem_iff_of_index_two index_g2Derived_two]
      exact iff_of_false (fun h => hgm (by simpa using Subgroup.inv_mem _ h)) hg
    have e : g2OAct (ZMod 2) g = g2OAct (ZMod 2) gm * g2OAct (ZMod 2) (gm⁻¹ * g) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [e]
    exact Mb.mul_mem hm (hlt.le ⟨_, h2, rfl⟩)

theorem eq_of_mem_fixV {w : ModO} (hw : w ∈ fixV Lb0) : w = 1 ∨ w = cO 129 := by
  obtain ⟨c, hc, rfl⟩ := exists_cO w
  have hfix : ∀ t, t = 1 ∨ t = 2 → applyG [t] c = c := by
    intro t ht
    have h1 := hw _ (act_mem_Lb0 [t])
    rw [cO_of_mem hc, g2OAct_codeO] at h1
    have h2 := congrArg Subtype.val (codeO_injective h1)
    rw [o0Act_wordGG (by simpa using ht)] at h2
    exact h2
  rcases cent_fixO c hc (hfix 1 (Or.inl rfl)) (hfix 2 (Or.inr rfl)) with rfl | rfl
  · exact Or.inl cO_zero
  · exact Or.inr rfl

theorem map_symm_map {W W' : Type} [Group W] [Group W'] (e : W ≃* W') (H : Subgroup W) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id W := by
    ext v
    simp
  rw [this, Subgroup.map_id]

theorem map_congr_symm_map {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    (H : Subgroup (MulAut W)) :
    (H.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext a v
    simp [MulAut.congr_apply]
  rw [this, Subgroup.map_id]

theorem cO_129_not_mem_map {V : Type} [CommGroup V] {Lb : Subgroup (MulAut V)}
    (e : V ≃* ModO) (he : Lb.map (MulAut.congr e).toMonoidHom = Lb0) {U : Subgroup V}
    (hnot : ¬ fixV Lb ≤ U) : cO 129 ∉ U.map e.toMonoidHom := by
  obtain ⟨v, hv, hvU⟩ : ∃ v ∈ fixV Lb, v ∉ U := by
    by_contra h
    push Not at h
    exact hnot h
  have hev : e v ∈ fixV Lb0 := by
    rw [← he, fixV_map_congr]
    exact ⟨v, hv, rfl⟩
  have hevU : e v ∉ U.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hvU
  rcases eq_of_mem_fixV hev with h1 | h129
  · exact absurd (h1 ▸ one_mem _ : e v ∈ U.map e.toMonoidHom) hevU
  · rwa [h129] at hevU

end G2HypFin

open G2HypFin

theorem g2HypXFact1248 :
    G2HypXFact1248 := by
  intro V _ _ hV2 Lb hcomm hfix hnat Mb hlt hMbN U hU hnot
  obtain ⟨e, he⟩ := G2NoOff.exists_weylEquiv hV2 hcomm hfix hnat
  have he' : Lb.map (MulAut.congr e).toMonoidHom = Lb0 := he
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hN : Mb.map (MulAut.congr e).toMonoidHom ≤
      Subgroup.normalizer (Lb0 : Set (MulAut ModO)) := by
    rw [← he']
    exact (Subgroup.map_mono hMbN).trans (Subgroup.le_normalizer_map _)
  have hMr := le_Mb0_of_le_normalizer hN
  have hlt' : Lb0 < Mb.map (MulAut.congr e).toMonoidHom := by
    rw [← he']
    exact (Subgroup.map_lt_map_iff_of_injective hinj).2 hlt
  have hU' : (U.map e.toMonoidHom).index = 2 := (Subgroup.index_map_equiv (H := U) e).trans hU
  have h := ((hypX_model hU' (cO_129_not_mem_map e he' hnot)).mono
    (Mb0_le_of_lt hlt' hMr)).map e.symm
  rwa [← he', map_congr_symm_map, map_congr_symm_map, map_symm_map] at h

theorem g2HyperplaneFact1248 :
    G2HyperplaneFact1248 := by
  intro V _ _ hV2 X Lb hLX hXN _ hcomm hfix hnat U hU hnot
  obtain ⟨e, he⟩ := G2NoOff.exists_weylEquiv hV2 hcomm hfix hnat
  have he' : Lb.map (MulAut.congr e).toMonoidHom = Lb0 := he
  have hN : X.map (MulAut.congr e).toMonoidHom ≤
      Subgroup.normalizer (Lb0 : Set (MulAut ModO)) := by
    rw [← he']
    exact (Subgroup.map_mono hXN).trans (Subgroup.le_normalizer_map _)
  have hLX' : Lb0 ≤ X.map (MulAut.congr e).toMonoidHom := by
    rw [← he']
    exact Subgroup.map_mono hLX
  have hU' : (U.map e.toMonoidHom).index = 2 := (Subgroup.index_map_equiv (H := U) e).trans hU
  have h := (hyp_model hLX' (le_Mb0_of_le_normalizer hN) hU'
    (cO_129_not_mem_map e he' hnot)).map e.symm
  rwa [← he', map_congr_symm_map, map_congr_symm_map, map_symm_map] at h

theorem hypX1248_of_g2
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1229 : Stmt12_2_9) (hpre : Pre1242) :
    HypX1248 :=
  hypX1248_of_outer h331 h1222 h1229 hpre g2DerivedNoOffender1248 g2HypXFact1248

theorem lemma12_4_8_of_charTwo
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hchar : CharTwo1248) : Lemma12_4_8 :=
  lemma12_4_8_of_g2 h331 h1222 h323 hpre h3228 (E6.as_E_6_14_of hC129) g2HyperplaneFact1248 hchar

end CFSG.Quasithin.H13
