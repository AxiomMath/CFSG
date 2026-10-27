module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG

theorem isSolvable_of_solvable_ker_range {A B : Type*} [Group A] [Group B]
    (f : A →* B) [Group.IsSolvable f.ker] [Group.IsSolvable f.range] :
    Group.IsSolvable A :=
  Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end CFSG

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem Hinf_eq_bot_of_isSolvable {H : Subgroup G} (h : Group.IsSolvable ↥H) :
    Hinf H = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := ↥H)
  unfold Hinf CFSG.inSubgroup
  rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective, ← le_bot_iff]
  exact (iInf_le (fun k => derivedSeries ↥H k) n).trans hn.le

private noncomputable def barMap (c : Ctx23L D Ch) : ↥c.L →* Bar2 c.L :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)

private noncomputable def barImageInf (c : Ctx23L D Ch) : Subgroup (Bar2 c.L) :=
  ((D.M ⊓ c.L).subgroupOf c.L).map (barMap c)

private noncomputable def barSylowInf (c : Ctx23L D Ch) : Sylow 2 (Bar2 c.L) :=
  (Ctx23L.sylowL c).mapSurjective (f := barMap c) (QuotientGroup.mk'_surjective _)

private theorem barSylow_le_barImage (c : Ctx23L D Ch) :
    (barSylowInf c : Subgroup (Bar2 c.L)) ≤ barImageInf c := by
  have hcoe : (barSylowInf c : Subgroup (Bar2 c.L)) =
      (Ctx23L.sylowL c : Subgroup ↥c.L).map (barMap c) :=
    Sylow.coe_mapSurjective (P := Ctx23L.sylowL c) (f := barMap c)
      (QuotientGroup.mk'_surjective _)
  rw [hcoe]
  refine Subgroup.map_mono fun x hx => ?_
  rw [Ctx23L.sylowL_coe] at hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨D.sylowM.le hx, x.2⟩

private theorem barImage_ne_top (c : Ctx23L D Ch) (hO2 : S23_9_O2L D Ch)
    (h1930 : H1930 D) : barImageInf c ≠ ⊤ := by
  intro hXtop
  have hker : (barMap c).ker = CFSG.pCore 2 ↥c.L := QuotientGroup.ker_mk' _
  have hsup : (D.M ⊓ c.L).subgroupOf c.L ⊔ CFSG.pCore 2 ↥c.L = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : barMap c x ∈ barImageInf c := by rw [hXtop]; exact Subgroup.mem_top _
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have hmem : a⁻¹ * x ∈ CFSG.pCore 2 ↥c.L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hax, inv_mul_cancel]
    have hxeq : a * (a⁻¹ * x) = x := by group
    rw [← hxeq]
    exact Subgroup.mul_mem_sup ha hmem
  have hsupG : c.L = (D.M ⊓ c.L) ⊔ CFSG.Open.pCoreOf 2 c.L := by
    have h := congrArg (Subgroup.map c.L.subtype) hsup
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D.M ⊓ c.L ≤ c.L)] at h
    simpa [CFSG.Open.pCoreOf] using h.symm
  have hLle : c.L ≤ D.M := by
    rw [hsupG]
    exact sup_le inf_le_left (hO2 h1930 c)
  exact uc22p20i_not_le_M D c.hL.1 hLle

private theorem card_map_barSylow (c : Ctx23L D Ch) {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : Bar2 c.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card ((barSylowInf c : Subgroup (Bar2 c.L)).map e.toMonoidHom) = Nat.card F := by
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (barSylowInf c).mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (barSylowInf c : Subgroup (Bar2 c.L)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (P := barSylowInf c) (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_utri_eq_of_sylow Q
  rw [← hQ, ← hg]
  rw [show Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.CGT.Timmesfeld75.utri F)) =
      Nat.card (CFSG.CGT.Timmesfeld75.utri F) from
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact CFSG.CGT.Timmesfeld75.card_utri

private theorem isSolvable_map_barImage (c : Ctx23L D Ch) (hO2 : S23_9_O2L D Ch)
    (h1930 : H1930 D) {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : Bar2 c.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Group.IsSolvable ↥((barImageInf c).map e.toMonoidHom) := by
  have hSle := barSylow_le_barImage c
  have hXne := barImage_ne_top c hO2 h1930
  let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (barSylowInf c).mapSurjective (f := e.toMonoidHom) e.surjective
  let R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (barImageInf c).map e.toMonoidHom
  have hPcoe : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (barSylowInf c : Subgroup (Bar2 c.L)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (P := barSylowInf c) (f := e.toMonoidHom) e.surjective
  have hPleR : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ R := by
    rw [hPcoe]
    exact Subgroup.map_mono hSle
  have hPcard : Nat.card (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = Nat.card F := by
    rw [hPcoe]
    exact card_map_barSylow c e
  have hRne : R ≠ ⊤ := by
    intro hRtop
    apply hXne
    have hEq : (barImageInf c).map e.toMonoidHom =
        (⊤ : Subgroup (Bar2 c.L)).map e.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      exact hRtop
    exact Subgroup.map_injective e.injective hEq
  have hNsolv : Group.IsSolvable ↥(Subgroup.normalizer
      ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    CFSG.Quasithin.E1.RootLift.isSolvable_normalizer P.isPGroup' hPcard
  have hRle : R ≤ Subgroup.normalizer
      ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    (CFSG.Quasithin.E1.RootLift.le_normalizer_or_eq_top P.isPGroup' hPcard hPleR).resolve_right
      hRne
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRle)
    (Subgroup.inclusion_injective hRle)

private theorem isSolvable_barImage (c : Ctx23L D Ch) (hO2 : S23_9_O2L D Ch)
    (h1930 : H1930 D) {a : ℕ} (hL2 : IsL2 (Bar2 c.L) a) :
    Group.IsSolvable ↥(barImageInf c) := by
  obtain ⟨F, hF, hFfin, hFchar, -, ⟨e⟩⟩ :=
    P22y.exists_equiv_sl2 (P22fin.isL2Ev_of_isL2 hL2).1
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  haveI : Group.IsSolvable ↥((barImageInf c).map e.toMonoidHom) :=
    isSolvable_map_barImage c hO2 h1930 e
  let ee := Subgroup.equivMapOfInjective (barImageInf c) e.toMonoidHom e.injective
  exact Group.isSolvable_of_surjective (f := ee.symm.toMonoidHom) ee.symm.surjective

private theorem isSolvable_inf_of_isSolvable_barImage (c : Ctx23L D Ch)
    (h : Group.IsSolvable ↥(barImageInf c)) :
    Group.IsSolvable ↥(D.M ⊓ c.L) := by
  let A : Subgroup ↥c.L := (D.M ⊓ c.L).subgroupOf c.L
  have hrange : Group.IsSolvable ↥((barMap c).domRestrict A).range := by
    rw [MonoidHom.domRestrict_range]
    exact h
  have hker : Group.IsSolvable ↥((barMap c).domRestrict A).ker := by
    have hKp : IsPGroup 2 ((barMap c).domRestrict A).ker := by
      rw [MonoidHom.ker_domRestrict, show (barMap c).ker = CFSG.pCore 2 ↥c.L from
        QuotientGroup.ker_mk' _]
      exact CFSG.pCore_isPGroup.comap_of_injective A.subtype A.subtype_injective
    haveI : Group.IsNilpotent ↥((barMap c).domRestrict A).ker := hKp.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hAsolv : Group.IsSolvable ↥A := by
    haveI : Group.IsSolvable ((barMap c).domRestrict A).ker := hker
    haveI : Group.IsSolvable ((barMap c).domRestrict A).range := hrange
    exact CFSG.isSolvable_of_solvable_ker_range ((barMap c).domRestrict A)
  haveI : Group.IsSolvable ↥A := hAsolv
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : D.M ⊓ c.L ≤ c.L)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : D.M ⊓ c.L ≤ c.L)).surjective

private theorem isSolvable_inf_of_isL2 (c : Ctx23L D Ch) (hO2 : S23_9_O2L D Ch)
    (h1930 : H1930 D) {a : ℕ} (hL2 : IsL2 (Bar2 c.L) a) :
    Group.IsSolvable ↥(D.M ⊓ c.L) :=
  isSolvable_inf_of_isSolvable_barImage c (isSolvable_barImage c hO2 h1930 hL2)

theorem s23_9_PointStab_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (hO2 : S23_9_O2L D Ch) : S23_9_PointStab D Ch := by
  intro h1930 c
  refine ⟨?_, ?_, ?_⟩
  · have hUZ : D.U = D.Z := (h4 h1930 c).1
    have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
      rw [← hUZ]
      exact Data.normalizer_U_eq D
    rw [hNZ, inf_comm]
  · intro a hL2
    exact Hinf_eq_bot_of_isSolvable (isSolvable_inf_of_isL2 c hO2 h1930 hL2)
  · intro a hO
    have hO' := hO
    obtain ⟨-, K, hK, hKfin, b, d, hKcard, -, -⟩ := hO'
    letI : Field K := hK
    letI : Finite K := hKfin
    have hK2 : 2 ≤ Nat.card K := by
      have h := Finite.one_lt_card (α := K)
      omega
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, pow_zero] at hKcard
        omega
      · exact h
    exact Hinf_eq_bot_of_isSolvable
      (isSolvable_inf_of_isL2 c hO2 h1930 (isL2_two_mul_of_isOmegaMinus_four ha hO))

end CFSG.LocalAnalysis.UniquenessCase.UC22
