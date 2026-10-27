module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

section Module

variable {V : Type*} [CommGroup V]

theorem fixV_map_conj (A : Subgroup (MulAut V)) (k : MulAut V) :
    fixV (A.map (MulAut.conj k).toMonoidHom) = (fixV A).map k.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq A k

theorem isFFModule_map_conj {A : Subgroup (MulAut V)} (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) (k : MulAut V) :
    IsFFModule (A.map (MulAut.conj k).toMonoidHom) := by
  refine ⟨_, le_rfl, fun h => hA1 ?_, ⟨?_, ?_⟩, ?_⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj k).injective).mp h
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hA.1 a ha b hb]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (k * a * k⁻¹) ^ 2 = k * a ^ 2 * k⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hA.2 a ha]; group
  · rw [fixV_map_conj, Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective k.injective]
    exact hcard

variable [Finite V]

theorem isFFModule_of_isSylowTwoOf {X Y : Subgroup (MulAut V)} (hY : IsSylowTwoOf Y X)
    (h : IsFFModule X) : IsFFModule Y := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun e : MulAut V => (e : V → V)) fun a b h => MulEquiv.ext (congrFun h)
  obtain ⟨A, hAX, hA1, hA, hcard⟩ := h
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  obtain ⟨S, hAS, hS⟩ := exists_isSylowTwoOf_of_le hAX hA2
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hY hS
  obtain ⟨B, hB, hB1, hBe, hBc⟩ := isFFModule_map_conj hA1 hA hcard g⁻¹
  refine ⟨B, hB.trans ?_, hB1, hBe, hBc⟩
  rintro _ ⟨a, ha, rfl⟩
  have := (hg a).mp (hAS ha)
  simpa [MulAut.conj_apply] using this

end Module

variable {G : Type} [Group G]

theorem isSylowTwoOf_autOn {H T V : Subgroup G} (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (autOn T V) (autOn H V) := by
  have hTH := hT.1
  set φ : ↥H →* ↥(autOn H V) := MonoidHom.codRestrict
    ((conjAct V).comp (Subgroup.inclusion hHN)) (autOn H V)
    (fun h => mem_autOn_iff'.mpr ⟨⟨h, hHN h.2⟩, h.2, rfl⟩) with hφ
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.mp ha
    exact ⟨⟨n, hn⟩, rfl⟩
  have hmap : (T.subgroupOf H).map φ = (autOn T V).subgroupOf (autOn H V) := by
    ext ⟨a, ha⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, he⟩
      rw [← he]
      exact mem_autOn_iff'.mpr ⟨⟨h, hHN h.2⟩, hh, rfl⟩
    · intro haT
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.mp haT
      exact ⟨⟨n, hTH hn⟩, hn, rfl⟩
  refine ⟨autOn_mono' hTH, ?_, fun h2 => hT.2.2 ?_⟩
  · exact (hT.2.1.comap_subtype (K := Subgroup.normalizer (V : Set G))).map (conjAct V)
  · rw [← hmap] at h2
    exact h2.trans (Subgroup.index_map_dvd _ hsurj)

end CFSG.Quasithin.H13.Ch4.E443
