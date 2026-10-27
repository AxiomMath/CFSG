module

public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.H13.U4ParOuterO2
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.F112R

open scoped Pointwise

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Ch9.F112Pf CFSG.ClassicalGroups.UnitaryFlag

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem parP_inf_parP2_eq_hypBorel : parP h ⊓ parP2 h = hypBorel h 2 0 := by
  ext g
  rw [Subgroup.mem_inf, mem_hypBorel]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact MulAction.mem_stabilizer_iff.mp h1
    · exact MulAction.mem_stabilizer_iff.mp h2
  · intro hg
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hg 1 le_rfl (by norm_num)),
      MulAction.mem_stabilizer_iff.mpr (hg 2 (by norm_num) le_rfl)⟩

private theorem isSolvable_hypBorel : Group.IsSolvable ↥(hypBorel h 2 0) := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI hU : Group.IsSolvable ↥((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)) :=
    @IsNilpotent.to_isSolvable _ _ ((isSylowTwoOf_hypUnitriangular h).2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (hypUnitriangular_le_hypBorel h)).symm).isNilpotent
  haveI hK : Group.IsSolvable (Fin 2 → Kˣ) :=
    Group.isSolvable_of_comm fun a b => mul_comm a b
  have hker : (hypDiagHom h 2 0 (Nat.zero_le 1)).ker ≤
      ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)).subtype.range := by
    rw [ker_hypDiagHom, Subgroup.range_subtype]
  exact Group.isSolvable_of_ker_le_range
    ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)).subtype
    (hypDiagHom h 2 0 (Nat.zero_le 1)) hker

theorem isSolvable_parP_inf_parP2 :
    Group.IsSolvable ↥(parP h ⊓ parP2 h) := by
  rw [parP_inf_parP2_eq_hypBorel]
  exact isSolvable_hypBorel h

private theorem genComm_perfectCore_parP (hm : 2 ≤ m) :
    GenComm (perfectCore (parP h)) := by
  rw [GenComm, pCoreOf_perfectCore_parP h hm, commutator_radQ_perfectCore h hm]

private theorem radQ2_le_commutator_radQ2_perfectCore (hm : 2 ≤ m) :
    radQ2 h ≤ ⁅radQ2 h, perfectCore (parP2 h)⁆ := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_torus_param h hm
  set d : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![c, 0; 0, c⁻¹], by simp [det_fin_two_of, hc0]⟩ with hd
  set t := lev2Hom h d with ht
  have htC : t ∈ perfectCore (parP2 h) := lev2Hom_range_le_perfectCore h ⟨d, rfl⟩
  have htP : t ∈ parP2 h := lev2Hom_le_parP2 h ⟨d, rfl⟩
  have hmaps : ∀ x ∈ radQ2 h, x * t * x⁻¹ * t⁻¹ ∈ radQ2 h := fun x hx => by
    have h1 : t * x⁻¹ * t⁻¹ ∈ radQ2 h :=
      (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h htP) x⁻¹).mp
        ((radQ2 h).inv_mem hx)
    have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [e]
    exact (radQ2 h).mul_mem hx h1
  let f : ↥(radQ2 h) → ↥(radQ2 h) := fun x =>
    ⟨(x : hypSU h 2 0) * t * (x : hypSU h 2 0)⁻¹ * t⁻¹, hmaps x x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hxy
    have e : a * t * a⁻¹ * t⁻¹ = b * t * b⁻¹ * t⁻¹ := congrArg Subtype.val hxy
    have hz : b⁻¹ * a ∈ radQ2 h := (radQ2 h).mul_mem ((radQ2 h).inv_mem hb) ha
    have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
      calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹ * t⁻¹) * t * a := by group
        _ = b⁻¹ * (b * t * b⁻¹ * t⁻¹) * t * a := by rw [e]
        _ = t * (b⁻¹ * a) := by group
    have h1 := eq_one_of_comm_lev2 h hc0 hc1 hc2 (d := d) rfl hz hc
    apply Subtype.ext
    show a = b
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  intro z hz
  obtain ⟨⟨a, ha⟩, hx⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
  have e : z = a * t * a⁻¹ * t⁻¹ := (congrArg Subtype.val hx).symm
  rw [e]
  exact Subgroup.commutator_mem_commutator ha htC

private theorem genComm_perfectCore_parP2 (hm : 2 ≤ m) :
    GenComm (perfectCore (parP2 h)) := by
  rw [GenComm, pCoreOf_perfectCore_parP2_eq h hm]
  exact radQ2_le_commutator_radQ2_perfectCore h hm

private theorem vFact_parP (hm : 2 ≤ m) : VFact (parP h) := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  refine ⟨not_two_dvd_relIndex (isSylowTwoOf_hypUnitriangular h)
    (hypUnitriangular_le_perfectCore_parP h hm), genComm_perfectCore_parP h hm⟩

private theorem vFact_parP2 (hm : 2 ≤ m) : VFact (parP2 h) := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  refine ⟨not_two_dvd_relIndex (isSylowTwoOf_hypUnitriangular h)
    (hypUnitriangular_le_perfectCore_parP2 h hm), genComm_perfectCore_parP2 h hm⟩

theorem eq_parP_or_parP2_of_isYAmalgamPair
    {T M1 M2 : Subgroup (hypSU h 2 0)} (hpair : IsYAmalgamPair T M1 M2)
    (hT : T = hypUnitriangular h 2 0) :
    (M1 = parP h ∧ M2 = parP2 h) ∨ (M1 = parP2 h ∧ M2 = parP h) := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  subst hT
  have hrange : (MonoidHom.id (hypSU h 2 0)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr Function.surjective_id
  have hid : (MonoidHom.id (hypSU h 2 0)).range.index ≤ 2 := by
    rw [hrange, Subgroup.index_top]
    norm_num
  have hU : (hypUnitriangular h 2 0).map (MonoidHom.id (hypSU h 2 0)) =
      hypUnitriangular h 2 0 ⊓ (MonoidHom.id (hypSU h 2 0)).range := by
    rw [Subgroup.map_id, hrange, inf_top_eq]
  obtain ⟨i1, -, hM1⟩ := CFSG.Quasithin.H13.U4V.inf_eq_of_adapted h
    (MonoidHom.id _) Function.injective_id hid
    (CFSG.Quasithin.H13.U4V.isYAmalgamPair_swap hpair) hU
  obtain ⟨i2, -, hM2⟩ := CFSG.Quasithin.H13.U4V.inf_eq_of_adapted h
    (MonoidHom.id _) Function.injective_id hid hpair hU
  have hM1' : M1 = ![parP h, parP2 h] i1 := by simpa [hrange] using hM1
  have hM2' : M2 = ![parP h, parP2 h] i2 := by simpa [hrange] using hM2
  have hne : M1 ≠ M2 := hpair.2.1
  fin_cases i1 <;> fin_cases i2
  · exact absurd (hM1'.trans hM2'.symm) hne
  · exact Or.inl ⟨hM1', hM2'⟩
  · exact Or.inr ⟨hM1', hM2'⟩
  · exact absurd (hM1'.trans hM2'.symm) hne

theorem isSolvable_inf_and_vFact_of_isYAmalgamPair {Y : Type} [Group Y] {n : ℕ}
    (hY : CFSG.Blueprint.LieModel Y .PSU 4 2 n) (hn : 2 ≤ n)
    {T M1 M2 : Subgroup Y} (hpair : IsYAmalgamPair T M1 M2) :
    Group.IsSolvable ↥(M1 ⊓ M2) ∧ VFact M1 ∧ VFact M2 := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY
  haveI : Finite Y := Finite.of_equiv _ e.toEquiv
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hpair0 : IsYAmalgamPair (T.map e.symm.toMonoidHom)
      (M1.map e.symm.toMonoidHom) (M2.map e.symm.toMonoidHom) :=
    IsYAmalgamPair.map e.symm hpair
  obtain ⟨c, -, hc⟩ := IsSylowTwoOf.exists_conj hpair0.1 (isSylowTwoOf_hypUnitriangular h)
  have hpair1 : IsYAmalgamPair (hypUnitriangular h 2 0)
      ((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom)
      ((M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
    have h' := IsYAmalgamPair.map (MulAut.conj c) hpair0
    rwa [← hc] at h'
  have hV : ((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom = parP h ∧
        (M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom = parP2 h) ∨
      ((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom = parP2 h ∧
        (M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom = parP h) :=
    eq_parP_or_parP2_of_isYAmalgamPair h hpair1 rfl
  have hsolv1 : Group.IsSolvable
      ↥((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom ⊓
        (M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
    rcases hV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact isSolvable_parP_inf_parP2 h
    · rw [h1, h2, inf_comm]
      exact isSolvable_parP_inf_parP2 h
  have hmap1 : ((M1.map e.symm.toMonoidHom) ⊓ (M2.map e.symm.toMonoidHom)).map
      (MulAut.conj c).toMonoidHom =
      (M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom ⊓
        (M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom :=
    Subgroup.map_inf _ _ _ (MulAut.conj c).injective
  haveI : Group.IsSolvable
      ↥(((M1.map e.symm.toMonoidHom) ⊓ (M2.map e.symm.toMonoidHom)).map
        (MulAut.conj c).toMonoidHom) := hmap1.symm ▸ hsolv1
  have hsolv2 : Group.IsSolvable
      ↥((M1.map e.symm.toMonoidHom) ⊓ (M2.map e.symm.toMonoidHom)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (MulAut.conj c).toMonoidHom.subgroupMap
        ((M1.map e.symm.toMonoidHom) ⊓ (M2.map e.symm.toMonoidHom)))
      (MonoidHom.subgroupMap_injective _ _ (MulAut.conj c).injective)
  have hmap2 : (M1 ⊓ M2).map e.symm.toMonoidHom =
      M1.map e.symm.toMonoidHom ⊓ M2.map e.symm.toMonoidHom :=
    Subgroup.map_inf _ _ _ e.symm.injective
  haveI : Group.IsSolvable ↥((M1 ⊓ M2).map e.symm.toMonoidHom) := hmap2.symm ▸ hsolv2
  have hsolv : Group.IsSolvable ↥(M1 ⊓ M2) :=
    Group.isSolvable_of_isSolvable_injective
      (f := e.symm.toMonoidHom.subgroupMap (M1 ⊓ M2))
      (MonoidHom.subgroupMap_injective _ _ e.symm.injective)
  have hV1 : VFact M1 := by
    have h' : VFact ((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
      rcases hV with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1.symm ▸ vFact_parP h hn
      · exact h1.symm ▸ vFact_parP2 h hn
    have h'' : VFact (M1.map e.symm.toMonoidHom) :=
      (vFact_map_iff (MulAut.conj c).injective (M1.map e.symm.toMonoidHom)).1 h'
    exact (vFact_map_iff e.symm.injective M1).1 h''
  have hV2 : VFact M2 := by
    have h' : VFact ((M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
      rcases hV with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact h2.symm ▸ vFact_parP2 h hn
      · exact h2.symm ▸ vFact_parP h hn
    have h'' : VFact (M2.map e.symm.toMonoidHom) :=
      (vFact_map_iff (MulAut.conj c).injective (M2.map e.symm.toMonoidHom)).1 h'
    exact (vFact_map_iff e.symm.injective M2).1 h''
  exact ⟨hsolv, hV1, hV2⟩

theorem perfectOver_u4q {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hH : Hyp111 L1 L2 S) {f : ℕ} (hf : 2 ≤ f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot (2 * f) (oTwoQuot ↥L2))
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f)) :
    PerfectOver L1 L2 S := by
  obtain ⟨Y, _, hY, T, M1, M2, hpair, ⟨iso⟩⟩ := hA
  have hY' : CFSG.Blueprint.LieModel Y .PSU 4 2 f := hY
  obtain ⟨_, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY'
  haveI : Finite Y := Finite.of_equiv _ e.toEquiv
  obtain ⟨hsolv, hV1, hV2⟩ :=
    isSolvable_inf_and_vFact_of_isYAmalgamPair hY' hf hpair
  haveI : Group.IsSolvable (RankTwoAmalgam.ofSubgroups M1 M2).G12 := hsolv
  haveI : Group.IsSolvable
      ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) :=
    Group.isSolvable_of_isSolvable_injective (f := iso.φ12.toMonoidHom) iso.φ12.injective
  have hB : Group.IsSolvable ↥(bigB L1 L2 S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_inf le_sup_right le_sup_right :
        bigB L1 L2 S ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)))
      (Subgroup.inclusion_injective _)
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hH
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  obtain ⟨hS1, hp1⟩ := le_and_perfect_of_vFact_of_isL2Quot hSB hB1 hB
    (vFact_of_mulEquiv iso.φ1 hV1) hH.h1.pgroup hf h1
  have hf2 : 2 ≤ 2 * f := by omega
  obtain ⟨hS2, hp2⟩ := le_and_perfect_of_vFact_of_isL2Quot hSB hB2 hB
    (vFact_of_mulEquiv iso.φ2 hV2) hH.h1.pgroup hf2 h2
  exact ⟨perfectCore_eq_self_of_perfect hp1, perfectCore_eq_self_of_perfect hp2, hS1, hS2⟩

end CFSG.Quasithin.F112R
