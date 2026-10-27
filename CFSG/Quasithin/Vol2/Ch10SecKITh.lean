module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.A5.G3
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

@[expose] def AbO2 (X : Type) [Group X] : Prop :=
  (∀ u v : ↥(CFSG.pCore 2 X), u * v = v * u) ∧ ¬ IsPGroup 2 X

theorem AbO2.of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : AbO2 X) : AbO2 Y := by
  refine ⟨fun u v => ?_, fun hP => h.2 (hP.of_equiv e.symm)⟩
  have hmap := CFSG.pCore_map_iso 2 e.symm
  have hu : e.symm u ∈ CFSG.pCore 2 X := hmap ▸ ⟨u, u.2, rfl⟩
  have hv : e.symm v ∈ CFSG.pCore 2 X := hmap ▸ ⟨v, v.2, rfl⟩
  have h1 := congrArg Subtype.val (h.1 ⟨_, hu⟩ ⟨_, hv⟩)
  simp only [Subgroup.coe_mul] at h1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have h2 := congrArg e h1
  simpa using h2

theorem not_abO2_bot {G : Type} [Group G] : ¬ AbO2 ↥(⊥ : Subgroup G) := fun h =>
  h.2 IsPGroup.of_bot

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_abO2_of_parabolicFacts {P Q : Subgroup G} (hF : ParabolicFacts P Q) :
    ¬ AbO2 ↥(perfectCore P) := by
  rintro ⟨hab, hn2⟩
  rcases hF.levi with hPQ | ⟨hgen, -⟩
  · exact hn2 (hF.pGroup.to_le hPQ)
  · have hQP : Q ≤ perfectCore P := hgen.trans (by
      refine Subgroup.commutator_le.2 fun q hq x hx => ?_
      have hN := CFSG.Quasithin.normalizer_le_normalizer_perfectCore P
        (Subgroup.le_normalizer (hF.le hq))
      have : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact (perfectCore P).mul_mem ((Subgroup.mem_normalizer_iff.1 hN x).1 hx)
        ((perfectCore P).inv_mem hx))
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hPinf : perfectCore P ≤ Subgroup.normalizer (Q : Set G) :=
      (perfectCore_le P).trans hF.normalizes
    have hnorm : (Q.subgroupOf (perfectCore P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2 hPinf
    have hQ2 : IsPGroup 2 (Q.subgroupOf (perfectCore P)) :=
      hF.pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
    have hle : Q.subgroupOf (perfectCore P) ≤ CFSG.pCore 2 ↥(perfectCore P) :=
      CFSG.QuasithinUnique.Vol2Native.L239.le_pCore_of_normal hQ2
    have hcomm := hab ⟨⟨x, hQP hx⟩, hle (Subgroup.mem_subgroupOf.2 hx)⟩
      ⟨⟨y, hQP hy⟩, hle (Subgroup.mem_subgroupOf.2 hy)⟩
    apply hxy
    have := congrArg (fun w : ↥(CFSG.pCore 2 ↥(perfectCore P)) =>
      ((w : ↥(perfectCore P)) : G)) hcomm
    simpa using this

theorem not_abO2_perfectCore_parabolic {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, ¬ AbO2 ↥(perfectCore (P j))) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ AbO2 ↥(perfectCore Pa) := by
  intro hD
  rcases perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h] at hD
    exact not_abO2_bot hD
  · exact hPj j (hD.of_equiv e)

theorem not_abO2_perfectCore_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) {Pa : Subgroup X} (h : ¬ AbO2 ↥(perfectCore (Pa.map e.toMonoidHom))) :
    ¬ AbO2 ↥(perfectCore Pa) := fun hD =>
  h (hD.of_equiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))))

theorem not_abO2_perfectCore_of_subgroupOf {L P : Subgroup G} (hP : IsParabolic2 L P)
    (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      ¬ AbO2 ↥(perfectCore Pa)) : ¬ AbO2 ↥(perfectCore P) := by
  have hPL : P ≤ L := hP.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  intro hD
  refine h _ hpar hne' ?_
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact hD.of_equiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm

theorem not_abO2_perfectCore_subgroupOf_of {C P : Subgroup G} (hPC : P ≤ C)
    (h : ¬ AbO2 ↥(perfectCore P)) : ¬ AbO2 ↥(perfectCore (P.subgroupOf C)) := fun hD => by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h (hD.of_equiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective C.subtype
    C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
