module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Scalar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1_bdh_three_dvd_orderOf {x : G} (hx1 : x ≠ 1)
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) : 3 ∣ orderOf x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hx3.card_eq_or_dvd
  rw [Nat.card_zpowers] at h
  rcases h with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h1

private theorem s16c4v1_bdh_bad_conj (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    {g : G} (hg : g ∉ D.M) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hgu : g * u * g⁻¹ ∈ V) : s16c4v1_Bad D (g * u * g⁻¹) := by
  intro hle
  obtain ⟨x, hxM, hx1, hx3, hxu⟩ := s16c4v1_exists_three_fix S hu
  have hcomm : x * u = u * x := mul_inv_eq_iff_eq_mul.mp hxu
  have hgxg : g * x * g⁻¹ ∈ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hcomm]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
  have hxconj : x ∈ conjSubgroup D.M g := by
    rw [mem_conjSubgroup_iff]
    exact hle hgxg
  have hle2 : Subgroup.zpowers x ≤ D.M ⊓ conjSubgroup D.M g :=
    Subgroup.zpowers_le.mpr ⟨hxM, hxconj⟩
  have h3dvd : 3 ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g) := by
    have hdvd := Subgroup.card_dvd_of_le hle2
    rw [Nat.card_zpowers] at hdvd
    exact (s16c4v1_bdh_three_dvd_orderOf hx1 hx3).trans hdvd
  have h3sig : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have h3sig1 : 3 ∈ D.sig1 := by
    rw [← hstd.h1219 ⊥ V S.sect.setting.hyp16.hyp125]
    exact h3sig
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    hstd.sigmaStd.sig1_sp 3 h3sig1
  have hginv : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  exact (hse.2.2 g⁻¹ hginv) (by simpa [conjSubgroup] using h3dvd)

theorem s16c4v1_bad_sing (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) (hbad : s16c4v1_Bad D v) :
    s16c4v1_vec S v ≠ 0 ∧ herm S.F.σ (s16c4v1_vec S v) (s16c4v1_vec S v) = 0 := by
  by_contra hcon
  have h3 : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have hcase : s16c4v1_vec S v = 0 ∨
      herm S.F.σ (s16c4v1_vec S v) (s16c4v1_vec S v) ≠ 0 := by
    by_cases h0 : s16c4v1_vec S v = 0
    · exact Or.inl h0
    · exact Or.inr fun hh => hcon ⟨h0, hh⟩
  obtain ⟨P, hPM, hP3, hPnc, hPv⟩ := s16c4v1_noncyclic_centralizer S hv hcase
  exact hbad (centralizer_le_of_noncyclic D hstd.r61 h3 hPM hP3 hPnc hv1
    ⟨1, by simpa using hV.2 v hv⟩ hPv)

theorem s16c4v1_bad_of_mem_inf (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {g : G}
    (hg : g ∉ D.M) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hgv : g * v * g⁻¹ ∈ V) :
    s16c4v1_Bad D v ∧ s16c4v1_Bad D (g * v * g⁻¹) := by
  have he : g⁻¹ * (g * v * g⁻¹) * (g⁻¹)⁻¹ = v := by group
  have hmem : g⁻¹ * (g * v * g⁻¹) * (g⁻¹)⁻¹ ∈ V := by rw [he]; exact hv
  have hgv1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hginv : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  exact ⟨he ▸ s16c4v1_bdh_bad_conj S hstd hginv hgv hgv1 hmem,
    s16c4v1_bdh_bad_conj S hstd hg hv hv1 hgv⟩

theorem s16c4v1_rMV_ge_six (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) : (6 : ℕ∞) ≤ rMV D.M V := by
  obtain ⟨k, hk1, hk⟩ := s16c4v1_card_v1 S hstd.r1217 hz
  have hcardV : Nat.card V = 2 ^ (8 + 2 * k) := by
    rw [s16c4v1_card_V S, hk,
      show (4 : ℕ) ^ k = 2 ^ (2 * k) by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul],
      ← pow_add]
  have hmV : mSub V = 8 + 2 * k := by
    have h := card_eq_two_pow_mSub (U := V) hV.isPGroup
    rw [hcardV] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUC⟩ := hU
  have hbad_of : ∀ u ∈ U, u ≠ 1 → s16c4v1_Bad D u := fun u huU hu1 hle =>
    hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)).trans hle)
  have hmU : mSub U ≤ 4 := by
    have hU1bot : U ⊓ v1Sub D.M ⊥ V hV L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      obtain ⟨huU, hu1⟩ := Subgroup.mem_inf.1 hu
      by_contra hune
      exact (s16c4v1_bad_sing S hstd (hUV huU) hune (hbad_of u huU hune)).1
        ((s16c4v1_vec_eq_zero_iff S (hUV huU)).2 hu1)
    have hts : ∀ x : IntMod V hV, x.val ∈ U →
        S.F.Sing (mkTil (v1Sub D.M ⊥ V hV L) V hV x) := by
      intro x hxU
      have hvec : s16c4v1_vec S x.val = S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x) := by
        unfold s16c4v1_vec
        rw [dif_pos x.val_mem,
          show IntMod.mk hV ⟨x.val, x.val_mem⟩ = x from Subtype.ext rfl]
      show herm S.F.σ (S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x))
        (S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x)) = 0
      rw [← hvec]
      by_cases hx1 : x.val = 1
      · rw [hx1, s16c4v1_vec_one]
        simp [herm]
      · exact (s16c4v1_bad_sing S hstd x.val_mem hx1 (hbad_of x.val hxU hx1)).2
    have hrk := s16c4_rk_imgTil_le_four S.F hts
    have h := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M ⊥ V hV L) V U hV hUV
    have hbot : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, rk_bot]
    rw [hU1bot, hbot, add_zero] at h
    rw [h]
    exact hrk
  have hquot : 6 ≤ E3.mQuot V U := by
    have h := mSub_eq_mQuot_add V U hV hUV
    omega
  exact_mod_cast hquot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
