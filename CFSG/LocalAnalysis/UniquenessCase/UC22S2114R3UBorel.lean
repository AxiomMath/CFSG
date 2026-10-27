module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {G : Type} [Group G] [Finite G]

section Hyp

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem uc22s2114r3u_pow_mem_hypUnitriangular (hε : ε ≤ 1) {g : hypSU h r ε}
    (hg : g ∈ hypBorel h r ε) : g ^ (Nat.card K - 1) ∈ hypUnitriangular h r ε := by
  set g' : hypBorel h r ε := ⟨g, hg⟩
  have hmem : g' ^ (Nat.card K - 1) ∈ (hypDiagHom h r ε hε).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    funext i
    have h1 := pow_card_eq_one' (G := Kˣ) (x := hypDiagHom h r ε hε g' i)
    rw [Nat.card_units] at h1
    simpa using h1
  rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hmem
  simpa [g'] using hmem

theorem uc22s2114r3u_pow_mem_hypProjUnitriangular (hε : ε ≤ 1) {x : hypPSU h r ε}
    (hx : x ∈ hypProjBorel h r ε) : x ^ (Nat.card K - 1) ∈ hypProjUnitriangular h r ε := by
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨_, uc22s2114r3u_pow_mem_hypUnitriangular h hε hg, map_pow _ _ _⟩

theorem uc22s2114r3u_pow_mem_hypPSU (hr : 1 ≤ r) (hε : ε ≤ 1) (S : Sylow p (hypPSU h r ε))
    {y : hypPSU h r ε} (hy : y ∈ normalizer ((S : Subgroup (hypPSU h r ε)) : Set _)) :
    y ^ (Nat.card K - 1) ∈ (S : Subgroup (hypPSU h r ε)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, -, -, -, ⟨U₀, hU₀⟩, -, -⟩ := unitary_order_and_Sylow h hr hε
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq (hypPSU h r ε) U₀ S
  have hN : normalizer (((c • U₀ : Sylow p (hypPSU h r ε)) : Subgroup (hypPSU h r ε)) :
      Set (hypPSU h r ε)) = (hypProjBorel h r ε).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul,
      ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypProjUnitriangular h hr hε,
      Subgroup.map_equiv_normalizer_eq, hU₀]
    rfl
  rw [hN] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← map_pow, Sylow.coe_subgroup_smul, hU₀]
  exact Subgroup.smul_mem_pointwise_smul _ _ _
    (uc22s2114r3u_pow_mem_hypProjUnitriangular h hε hx)

end Hyp

theorem uc22s2114r3u_pow_mem {Y : Type} [Group Y] [Finite Y] {m f : ℕ} (hm : 3 ≤ m)
    (hY : LieModel Y .PSU m 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {y : Y}
    (hy : y ∈ normalizer (U : Set Y)) : y ^ (2 ^ (2 * f) - 1) ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := (LieModel.admissible hY).2.1
  rw [show m = 2 * (m / 2) + m % 2 from (Nat.div_add_mod m 2).symm] at hY
  obtain ⟨K, _, _, h, ⟨e⟩⟩ := uc22pwliu_exists_hypPSU hf (by omega) hY
  have hidx : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let S : Sylow 2 Y := hU.2.1.toSylow hidx
  let S' : Sylow 2 (hypPSU h (m / 2) (m % 2)) := Sylow.mapSurjective (f := e.toMonoidHom)
    e.surjective S
  have hS' : (S' : Subgroup (hypPSU h (m / 2) (m % 2))) = U.map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hy' : e y ∈ normalizer ((S' : Subgroup (hypPSU h (m / 2) (m % 2))) : Set _) := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hy
  have hpow := uc22s2114r3u_pow_mem_hypPSU h (by omega) (by omega) S' hy'
  rw [hS', ← map_pow] at hpow
  have hU' := (Subgroup.mem_map_equiv (f := e)).1 hpow
  rwa [MulEquiv.symm_apply_apply, h.card] at hU'

theorem uc22s2114r3u_not_dvd_out_bound {m f r : ℕ} (hm : m = 6 ∨ m = 7) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ 2 * f * Nat.gcd m (2 ^ f + 1) := by
  intro hd
  rcases (Nat.Prime.dvd_mul hr).1 hd with h2f | hg
  · rcases (Nat.Prime.dvd_mul hr).1 h2f with h2 | hf
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact hrf hf
  · have hrq : r ∣ 2 ^ f + 1 := hg.trans (Nat.gcd_dvd_right _ _)
    have hrm : r ∣ m := hg.trans (Nat.gcd_dvd_left _ _)
    rcases hm with rfl | rfl
    · rcases (Nat.Prime.dvd_mul hr).1 (show r ∣ 2 * 3 from hrm) with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega
    · have h7 : r = 7 := by
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_seven r hrm with h | h <;> omega
      subst h7
      have := uc22pwliu_two_pow_mod_seven f
      omega

theorem uc22s2114r3u_inner {X : Type} [Group X] [Finite X] {m f r : ℕ} (hm : m = 6 ∨ m = 7)
    (hX : LieModel X .PSU m 2 f) (hr : r.Prime) (hr7 : 7 ≤ r) (hrf : ¬ r ∣ f) {α : MulAut X}
    (hα : α ^ r = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) (by omega) Nat.prime_two (LieModel.admissible hX).2.1
    (LieModel.statedClassicalModel hX (by decide))).1
  exact uc22p2214_out_mem_of_card_dvd hd hr (uc22s2114r3u_not_dvd_out_bound hm hr (by omega) hrf)
    hα

theorem uc22s2114r3u_dvd_of_borel {M L T : Subgroup G} (hL : L ∈ calC M)
    (hTL : IsSylowOf 2 (T ⊓ L) L) {m f : ℕ} (hm : m = 6 ∨ m = 7)
    (hX : LieModel (BarInf L) .PSU m 2 f) {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hbT : b ∈ normalizer (T : Set G)) {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hrf : ¬ r ∣ f)
    (hbr : b ^ r = 1) (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1) :
    r ∣ 2 ^ (2 * f) - 1 := by
  obtain ⟨U, hU, y, hy, hy1, hyr⟩ := uc22s2114_exists_of_borel hL hTL hbL hbT hbr hb1
    fun _ hα => uc22s2114r3u_inner hm hX hr hr7 hrf hα
  exact by_contra fun hrn => hy1 (uc22s2114_eq_one_of_pow_mem hU.2.1 hr (by omega) hrn
    (uc22s2114r3u_pow_mem (by omega) hX hU hy) hyr)

end CFSG.LocalAnalysis.UniquenessCase.UC22
