module

public import CFSG.Quasithin.H13.NQCatLieOverRank2
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6 (ResidualOvergroups ResidualOvergroupsAt)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open Matrix

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem isSolvable_of_normal_sylow {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) (hn : U.Normal) :
    Group.IsSolvable Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUs : Group.IsSolvable ↥U := by
    have := hU.2.1.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (Y ⧸ U)) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex_top_right]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hU.2.2)
  have hQs : Group.IsSolvable (Y ⧸ U) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range U.subtype (QuotientGroup.mk' U)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem false_of_solvOver [Group.IsPerfect Y] [Nontrivial Y] {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) (hres : ResidualOvergroups Y U) (hS : NQCat.SolvOver Y U)
    (hmax : ∃ U' P : Subgroup Y, IsSylowTwoOf U' ⊤ ∧ U' ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P) :
    False := by
  obtain ⟨Q, hQ⟩ := hres
  obtain ⟨U', P, hU', hU'P, hP, hPs⟩ := hmax
  obtain ⟨g, hg⟩ := NQCat.exists_conj_map_eq hU' hU
  set M := P.map (MulAut.conj g).toMonoidHom with hMdef
  have hUM : U ≤ M := hg ▸ Subgroup.map_mono hU'P
  have hM : M ⋖ ⊤ := by
    have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))).mpr hP
    rwa [MulEquiv.mapSubgroup_apply, MulEquiv.mapSubgroup_apply,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  have hMs : Group.IsSolvable ↥M := Group.isSolvable_of_surjective
    (f := (P.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom) (MulEquiv.surjective _)
  have hYs : ¬ Group.IsSolvable Y := Group.IsPerfect.not_isSolvable Y
  have hNU : Subgroup.normalizer (U : Set Y) ≠ ⊤ := fun htop =>
    hYs (isSolvable_of_normal_sylow hU (Subgroup.normalizer_eq_top_iff.mp htop))
  have hMN : M = Subgroup.normalizer (U : Set Y) := by
    rcases hM.eq_or_eq (hS M hUM hMs) le_top with h | h
    · exact h.symm
    · exact absurd h hNU
  obtain ⟨i, hi⟩ := (hQ.2.2.1 M hUM).mp hM
  obtain ⟨j, hji⟩ : ∃ j : Fin 2, Q j ≠ Q i := by
    rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h | h
    · exact ⟨1, fun h1 => hQ.1 (by rw [show (0 : Fin 2) = i from Fin.ext h.symm, ← h1])⟩
    · exact ⟨0, fun h1 => hQ.1 (by rw [show (1 : Fin 2) = i from Fin.ext h.symm, ← h1])⟩
  have hQj : Q j ⋖ ⊤ := (hQ.2.2.1 (Q j) (hQ.2.1 j)).mpr ⟨j, rfl⟩
  have hNQ : Subgroup.normalizer (U : Set Y) ≤ Subgroup.normalizer (Q j : Set Y) := by
    intro n hn
    rw [← A38.map_conj_eq_iff]
    have hUn : U.map (MulAut.conj n).toMonoidHom = U := A38.map_conj_eq_iff.mpr hn
    have hcov : (Q j).map (MulAut.conj n).toMonoidHom ⋖ ⊤ := by
      have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj n))).mpr hQj
      rwa [MulEquiv.mapSubgroup_apply, MulEquiv.mapSubgroup_apply,
        Subgroup.map_top_of_surjective _ (MulAut.conj n).surjective] at h1
    have hUQ : U ≤ (Q j).map (MulAut.conj n).toMonoidHom :=
      hUn ▸ Subgroup.map_mono (hQ.2.1 j)
    obtain ⟨l, hl⟩ := (hQ.2.2.1 _ hUQ).mp hcov
    by_cases hli : Q l = Q i
    · exfalso
      apply hji
      have hni : n⁻¹ ∈ Subgroup.normalizer (Q i : Set Y) :=
        Subgroup.le_normalizer (by rw [← hi, hMN]; exact inv_mem hn)
      have h2 : (Q i).map (MulAut.conj n⁻¹).toMonoidHom = Q i := A38.map_conj_eq_iff.mpr hni
      rw [← h2, ← hli, ← hl, Subgroup.map_map]
      convert (Subgroup.map_id (Q j)).symm
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    · rw [hl]
      have hij : (j : ℕ) ≠ (i : ℕ) := fun h => hji (by rw [Fin.ext h])
      have hli' : (l : ℕ) ≠ (i : ℕ) := fun h => hli (by rw [Fin.ext h])
      rw [show l = j from Fin.ext (by omega)]
  have hsup : Q i ⊔ Q j = ⊤ := by
    rw [← hi]
    rcases hM.eq_or_eq (le_sup_left : M ≤ M ⊔ Q j) le_top with h | h
    · exfalso
      have hQjM : Q j ≤ M := h ▸ le_sup_right
      rcases hQj.eq_or_eq hQjM le_top with h2 | h2
      · exact hji (h2.symm.trans hi)
      · exact hM.lt.ne h2
    · exact h
  have hnorm : (Q j).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (by rw [← hi, hMN]; exact hNQ) Subgroup.le_normalizer
  have hsurj : Function.Surjective ((QuotientGroup.mk' (Q j)).comp (Q i).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q j) y
    have hx : x ∈ Q i ⊔ Q j := hsup ▸ Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_right] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using inv_mem hb
  have hQis : Group.IsSolvable ↥(Q i) := hi ▸ hMs
  have hqs : Group.IsSolvable (Y ⧸ Q j) := Group.isSolvable_of_surjective hsurj
  have hqp : Group.IsPerfect (Y ⧸ Q j) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Q j))
  have hsub : Subsingleton (Y ⧸ Q j) := by
    by_contra hns
    have : Nontrivial (Y ⧸ Q j) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (Y ⧸ Q j) hqs
  refine hQj.lt.ne (eq_top_iff.mpr fun y _ => ?_)
  have h1 := Subsingleton.elim (QuotientGroup.mk' (Q j) y) 1
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

end Core

section Classical

variable {Y : Type} [Group Y] [Finite Y]

theorem solvOver_of_isPSL3 {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver Y U := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  exact NQCat.solvOver_of_sylow
    (NQCat.solvOver_projectiveSL (NQCat.exists_finset_card_four_of_card hf hcard)) hU₀
    ((e.trans (statedSLEquivProjectiveSL 3 K)).symm) hU

theorem solvOver_of_isSL3 {f : ℕ} (hf : 2 ≤ f) (h : IsSL3 (2 ^ f) Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver Y U := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hS : NQCat.SolvOver (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K) := by
    intro X hUX hX
    rw [normalizer_unitriangular]
    exact NQCat.SL3.le_upperTriangular_of_isSolvable
      (NQCat.exists_finset_card_four_of_card hf hcard) hUX hX
  exact NQCat.solvOver_of_sylow hS hU₀
    ((e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).symm) hU

theorem solvOver_of_isPSp4 {f : ℕ} (hf : 2 ≤ f) (h : IsPSp4 2 f Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver Y U := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  exact NQCat.solvOver_of_sylow
    (NQCat.solvOver_projSp (NQCat.exists_finset_card_four_of_card hf hcard)) hU₀ e.symm hU

omit [Finite Y] in
theorem card_eq_168_of_isPSL3 (h : IsPSL 3 2 1 Y) : Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

omit [Finite Y] in
theorem card_eq_168_of_isSL3 (h : IsSL3 (2 ^ 1) Y) : Nat.card Y = 168 := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
    card_SL_eq (by norm_num), hcard]
  decide

omit [Finite Y] in
theorem not_dvd_of_card_168 {W : Subgroup Y} (hY : Nat.card Y = 168) {k : ℕ} (hk : 2 ≤ k)
    (hWk : 2 ^ k * (4 ^ k - 1) ∣ Nat.card ↥W) : False := by
  have h1 : 2 ^ k * (4 ^ k - 1) ∣ 168 := hY ▸ hWk.trans (Subgroup.card_subgroup_dvd_card W)
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · have hk2 : k = 2 := by omega
    subst hk2
    norm_num at h1
  · have h2 := Nat.le_of_dvd (by norm_num) h1
    have h4 : 2 ^ 3 * (4 ^ 3 - 1) ≤ 2 ^ k * (4 ^ k - 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h3) 1)
    norm_num at h4
    omega

end Classical

end CFSG.Quasithin.H13.D42
