module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4OverAux1
public import CFSG.Quasithin.Recognition.St84.Gen.U4qVFact
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSUTorus
public import CFSG.Quasithin.H13.U4ParPointStable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSU4Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNinePointStab
public import CFSG.ClassicalGroups.Unitary.ComponentBorelUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.U4Par
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Quasithin.LieOver
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem s16c6_ne_bot_of_isL2 {H : Subgroup (hypSU h 2 0)} {k : ℕ} (hk : 1 ≤ k)
    (hL2 : IsL2 (Bar2 H) k) : H ≠ ⊥ := by
  have hcard := (CFSG.Quasithin.S153H.card_psl_two_two
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mp hL2)).2
  have hgt : 1 < Nat.card (Bar2 H) := by
    rw [hcard]
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h3 : 3 ≤ (2 ^ k) ^ 2 - 1 := by
      have h4 : 4 ≤ (2 ^ k) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (2 ^ k) ^ 2 := by gcongr
      omega
    have := Nat.mul_le_mul h2k h3
    omega
  haveI hnt : Nontrivial (Bar2 H) := Finite.one_lt_card_iff_nontrivial.mp hgt
  intro hbot
  rw [hbot] at hnt
  obtain ⟨a, b, hab⟩ := hnt
  exact hab (Subsingleton.elim a b)

private theorem s16c6_core (hm : 2 ≤ m) {R : Subgroup (hypSU h 2 0)}
    (hR : perfectCore (parP2 h) ≤ R) : R = ⊤ ∨ R ≤ parP2 h := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  by_cases htop : R = ⊤
  · exact Or.inl htop
  right
  have hU : hypUnitriangular h 2 0 ≤ R :=
    (hypUnitriangular_le_perfectCore_parP2 h hm).trans hR
  have hUm : hypProjUnitriangular h 2 0 ≤ R.map (hypProj h 2 0) := by
    rw [hypProjUnitriangular]
    exact Subgroup.map_mono hU
  have hA : R.map (hypProj h 2 0) ≠ ⊤ := by
    intro hmap
    apply htop
    have hker : (hypProj h 2 0).ker ≤ R := by
      rw [ker_hypProj, hypScalars_eq_bot]
      exact bot_le
    have h1 : (R.map (hypProj h 2 0)).comap (hypProj h 2 0) = ⊤ := by
      rw [hmap, Subgroup.comap_top]
    rw [Subgroup.comap_map_eq] at h1
    rwa [sup_eq_left.mpr hker] at h1
  obtain ⟨d, hd1, hd2, hdR⟩ :=
    psuCover_all_of_torus psuTorusOvergroup_holds m K h 2 0 (le_refl 2) (by norm_num)
      (R.map (hypProj h 2 0)) hA hUm
  have hRiso : R ≤ isoStabilizer h 2 0 (hypFlag h 2 0 d) := by
    intro x hx
    have hx' : hypProj h 2 0 x ∈ projIsoStabilizer h 2 0 (hypFlag h 2 0 d) :=
      hdR (Subgroup.mem_map_of_mem _ hx)
    rw [← comap_projIsoStabilizer]
    exact Subgroup.mem_comap.mpr hx'
  have hd : d = 1 ∨ d = 2 := by omega
  rcases hd with rfl | rfl
  · exfalso
    have hXparP : perfectCore (parP2 h) ≤ parP h := by
      simpa [parP] using hR.trans hRiso
    have hXinf : perfectCore (parP2 h) ≤ parP h ⊓ parP2 h :=
      le_inf hXparP (perfectCore_le (parP2 h))
    haveI : Group.IsSolvable ↥(parP h ⊓ parP2 h) :=
      CFSG.Quasithin.F112R.isSolvable_parP_inf_parP2 h
    haveI hsolv : Group.IsSolvable ↥(perfectCore (parP2 h)) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXinf)
        (Subgroup.inclusion_injective hXinf)
    haveI hperf : Group.IsPerfect ↥(perfectCore (parP2 h)) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect (parP2 h))
    have hnt : Nontrivial ↥(perfectCore (parP2 h)) := by
      have hcard : Nat.card (ModO2 (perfectCore (parP2 h))) =
          2 ^ (2 * m) * ((2 ^ (2 * m)) ^ 2 - 1) :=
        (CFSG.Quasithin.S153H.card_psl_two_two (isPSL_modO2_perfectCore_parP2 h)).2
      have hgt : 1 < Nat.card (ModO2 (perfectCore (parP2 h))) := by
        rw [hcard]
        have hk : 2 ≤ 2 * m := by omega
        have h2k : 4 ≤ 2 ^ (2 * m) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hk
        have h3 : 15 ≤ (2 ^ (2 * m)) ^ 2 - 1 := by
          have h16 : 16 ≤ (2 ^ (2 * m)) ^ 2 := by
            calc 16 = 4 ^ 2 := by norm_num
              _ ≤ (2 ^ (2 * m)) ^ 2 := by gcongr
          omega
        have := Nat.mul_le_mul h2k h3
        omega
      have hntq : Nontrivial (ModO2 (perfectCore (parP2 h))) :=
        Finite.one_lt_card_iff_nontrivial.mp hgt
      exact Function.Surjective.nontrivial
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(perfectCore (parP2 h))))
    exact Group.IsPerfect.not_isSolvable (G := ↥(perfectCore (parP2 h))) inferInstance
  · simpa [parP2] using hRiso

private theorem s16c6_model_borel (hm : 2 ≤ m) {P X R : Subgroup (hypSU h 2 0)}
    (hB : hypBorel h 2 0 ≤ P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * m)) (hXR : X ≤ R) : R = ⊤ ∨ R ≤ P := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  rcases overgroups_hypBorel_model h hB with hPB | hPP | hPP2 | hPT
  · exfalso
    have hsolv : Group.IsSolvable ↥(hypBorel h 2 0) :=
      CFSG.ClassicalGroups.UnitaryFlag.isSolvable_hypBorel h (by norm_num) (by norm_num)
    have hXbot : X = ⊥ := by
      rw [hX, hPB, ← hinf_eq_derInf]
      exact Hinf_eq_bot_of_isSolvable hsolv
    rw [hXbot] at hL2
    exact (s16c6_ne_bot_of_isL2 h (by omega) hL2) rfl
  · exfalso
    have hXp : X = perfectCore (parP h) := by
      rw [hX, hPP, ← hinf_eq_derInf]
      exact Hinf_eq_perfectCore (parP h)
    rw [hXp] at hL2
    have hL2m : IsL2 (Bar2 (perfectCore (parP h))) m :=
      lieModel_modO2_perfectCore_parP h hm
    have heq : m = 2 * m := s16c6_isL2_param_unique hL2m hL2
    omega
  · rw [hPP2] at hX ⊢
    have hXp : X = perfectCore (parP2 h) := by
      rw [hX, ← hinf_eq_derInf]
      exact Hinf_eq_perfectCore (parP2 h)
    rw [hXp] at hXR
    exact s16c6_core h hm hXR
  · exact Or.inr (hPT ▸ le_top)

private theorem s16c6_map_conj_eq_top_iff {G : Type} [Group G] (g : G) {A : Subgroup G} :
    A.map (MulAut.conj g).toMonoidHom = ⊤ ↔ A = ⊤ := by
  constructor
  · intro htop
    have h2 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) htop
    rw [Subgroup.map_map] at h2
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h2
    exact h2
  · intro htop
    rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

private theorem s16c6_map_conj_le_iff {G : Type} [Group G] (g : G) {A B : Subgroup G} :
    A.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj g).toMonoidHom ↔ A ≤ B := by
  constructor
  · intro hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle
  · exact Subgroup.map_mono

theorem s16c6_model (hm : 2 ≤ m) {P X R : Subgroup (hypSU h 2 0)}
    (hP : IsParabolicTwo (hypSU h 2 0) P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * m)) (hXR : X ≤ R) : R = ⊤ ∨ R ≤ P := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨S, hS⟩ := hP
  have hSyl : IsSylowTwoOf (hypUnitriangular h 2 0) ⊤ := isSylowTwoOf_hypUnitriangular h
  have hSsyl : IsSylowTwoOf (S : Subgroup (hypSU h 2 0)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨g, -, hg⟩ := IsSylowTwoOf.exists_conj hSsyl hSyl
  have hB : hypBorel h 2 0 ≤ P.map (MulAut.conj g).toMonoidHom := by
    have hNB : hypBorel h 2 0 =
        (Subgroup.normalizer (S : Set (hypSU h 2 0))).map (MulAut.conj g).toMonoidHom := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular h
        (by norm_num) (by norm_num), hg]
      exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup (hypSU h 2 0))
        (MulAut.conj g)).symm
    rw [hNB]
    exact Subgroup.map_mono hS
  have hX' : X.map (MulAut.conj g).toMonoidHom =
      F07.DerInf (P.map (MulAut.conj g).toMonoidHom) := by
    rw [hX, s16c6_derInf_map_equiv]
  have hL2' : IsL2 (Bar2 (X.map (MulAut.conj g).toMonoidHom)) (2 * m) :=
    s16c6_isL2_bar2_map_equiv (MulAut.conj g) X hL2
  have hXR' : X.map (MulAut.conj g).toMonoidHom ≤ R.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hXR
  rcases s16c6_model_borel h hm hB hX' hL2' hXR' with htop | hle
  · exact Or.inl ((s16c6_map_conj_eq_top_iff g).mp htop)
  · exact Or.inr ((s16c6_map_conj_le_iff g).mp hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
