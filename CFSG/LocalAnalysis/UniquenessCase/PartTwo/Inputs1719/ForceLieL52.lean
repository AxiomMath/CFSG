module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.GroupTheory.GL52.SylowThree
public import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter
public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
public import CFSG.RankThree.PartOne.SEITZ7.D4CentN
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

section GL52

open CFSG.GroupTheory.GL52

private theorem l52_gen_facts : ∀ i j : Fin 3, ((i : ℕ) ≠ 0 ∨ (j : ℕ) ≠ 0) →
    (∃ k l : Fin 3, ord3T2M = (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) ^ (k : ℕ) *
      (syl3DM (.r 1) * (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) * syl3DM (.r 1)⁻¹) ^ (l : ℕ)) ∧
    (∃ k l : Fin 3, syl3TbM = (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) ^ (k : ℕ) *
      (syl3DM (.r 1) * (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) * syl3DM (.r 1)⁻¹) ^ (l : ℕ)) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem syl3R_irreducible {U : Subgroup G52} (hU : U ≤ syl3R) (hU1 : U ≠ ⊥)
    (hN : normalizer (syl3R : Set G52) ≤ normalizer (U : Set G52)) : U = syl3R := by
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨i, hi, j, hj, rfl⟩ := syl3_mem_R (hU huU)
  set r : G52 := syl3DHom (DihedralGroup.r 1) with hr
  have hrN : r ∈ normalizer (U : Set G52) := hN (syl3_T_le_normalizer ⟨_, rfl⟩)
  have hv : r * (ord3T2 ^ i * syl3Tb ^ j) * r⁻¹ ∈ U := (mem_normalizer_iff.mp hrN _).mp huU
  have hij : ((⟨i, hi⟩ : Fin 3) : ℕ) ≠ 0 ∨ ((⟨j, hj⟩ : Fin 3) : ℕ) ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    apply hu1'
    rw [h.1, h.2, pow_zero, pow_zero, mul_one]
  obtain ⟨⟨k, l, hkl⟩, ⟨m, n, hmn⟩⟩ := l52_gen_facts ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hum : ((ord3T2 ^ i * syl3Tb ^ j : G52) : M5) = ord3T2M ^ i * syl3TbM ^ j := by
    rw [Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]
  have hvm : ((r * (ord3T2 ^ i * syl3Tb ^ j) * r⁻¹ : G52) : M5) =
      syl3DM (.r 1) * (ord3T2M ^ i * syl3TbM ^ j) * syl3DM (.r 1)⁻¹ := by
    rw [Units.val_mul, Units.val_mul, hum]
    rfl
  have ha : ord3T2 = (ord3T2 ^ i * syl3Tb ^ j) ^ (k : ℕ) *
      (r * (ord3T2 ^ i * syl3Tb ^ j) * r⁻¹) ^ (l : ℕ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hum, hvm]
    exact hkl
  have hb : syl3Tb = (ord3T2 ^ i * syl3Tb ^ j) ^ (m : ℕ) *
      (r * (ord3T2 ^ i * syl3Tb ^ j) * r⁻¹) ^ (n : ℕ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hum, hvm]
    exact hmn
  have haU : ord3T2 ∈ U := ha ▸ U.mul_mem (U.pow_mem huU _) (U.pow_mem hv _)
  have hbU : syl3Tb ∈ U := hb ▸ U.mul_mem (U.pow_mem huU _) (U.pow_mem hv _)
  exact le_antisymm hU (sup_le (zpowers_le.mpr haU) (zpowers_le.mpr hbU))

end GL52

theorem normalizer_irreducible_of_mulEquiv {G H : Type} [Group G] [Group H] (ψ : G ≃* H)
    {S : Subgroup G} {S' : Subgroup H} (hS : S.map ψ.toMonoidHom = S')
    (h : ∀ U : Subgroup H, U ≤ S' → U ≠ ⊥ → normalizer (S' : Set H) ≤ normalizer (U : Set H) →
      U = S') :
    ∀ U : Subgroup G, U ≤ S → U ≠ ⊥ → normalizer (S : Set G) ≤ normalizer (U : Set G) →
      U = S := by
  intro U hUS hU1 hN
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  apply Subgroup.map_injective hinj
  rw [hS]
  apply h
  · rw [← hS]
    exact Subgroup.map_mono hUS
  · intro hb
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hb)
  · rw [← hS, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hN

theorem l52_sylow_three {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 5 2 1)
    (S : Sylow 3 X) :
    Nat.card (normalizer ((S : Subgroup X) : Set X)) = 72 ∧
    ∀ U : Subgroup X, U ≤ S → U ≠ ⊥ →
      normalizer ((S : Subgroup X) : Set X) ≤ normalizer (U : Set X) → U = S := by
  obtain ⟨φ⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hX.statedClassicalModel_of_ne_zero (by norm_num))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀, hR₀⟩ := CFSG.GroupTheory.GL52.exists_sylow_eq_of_card_pow (p := 3) (k := 2)
    (by rw [CFSG.GroupTheory.GL52.syl3_card_R]; norm_num)
    (fun P => by rw [CFSG.GroupTheory.GL52.syl3_card_sylow P]; norm_num)
  let S' : Sylow 3 CFSG.GroupTheory.GL52.G52 :=
    S.mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨c, hc⟩ := CFSG.GroupTheory.GL52.exists_eq_map_conj_sylow R₀ S'
  set ψ : X ≃* CFSG.GroupTheory.GL52.G52 := φ.trans (MulAut.conj c⁻¹) with hψ
  have hSψ : (S : Subgroup X).map ψ.toMonoidHom = CFSG.GroupTheory.GL52.syl3R := by
    have h1 : (S : Subgroup X).map ψ.toMonoidHom =
        ((S : Subgroup X).map φ.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    have h2 : ((S : Subgroup X).map φ.toMonoidHom) = (S' : Subgroup _) :=
      (Sylow.coe_mapSurjective _ _).symm
    have hid : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id CFSG.GroupTheory.GL52.G52 := by
      ext1 x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [h1, h2, hc, Subgroup.map_map, hid, Subgroup.map_id, hR₀]
  refine ⟨?_, normalizer_irreducible_of_mulEquiv ψ hSψ fun U hU hU1 hN =>
    syl3R_irreducible ?_ hU1 ?_⟩
  · have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_equiv_normalizer_eq, hSψ,
      CFSG.GroupTheory.GL52.syl3_card_normalizer]
  · exact hU
  · exact hN

theorem false_of_frattini_five {X : Type} [Group X] [Finite X]
    (hX : Nat.card X = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31) (S : Sylow 3 X)
    (hNS : ¬ 5 ∣ Nat.card (normalizer ((S : Subgroup X) : Set X)))
    (hirr : ∀ U : Subgroup X, U ≤ S → U ≠ ⊥ →
      normalizer ((S : Subgroup X) : Set X) ≤ normalizer (U : Set X) → U = S)
    {Y : Subgroup X} (hNY : normalizer ((S : Subgroup X) : Set X) ≤ Y) (T : Sylow 2 X)
    (hTY : (T : Subgroup X) ≤ Y) {Nn : Subgroup X} (hNnY : Nn ≤ Y)
    (hNn : (Nn.subgroupOf Y).Normal) (h3 : 3 ∣ Nat.card Nn)
    (h23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSY : (S : Subgroup X) ≤ Y := le_normalizer.trans hNY
  have hYN : Y ≤ normalizer (Nn : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNnY).mp hNn
  have hStop : CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  have hSN : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup X) ⊓ Nn) Nn :=
    (hStop.of_le hSY le_top).inf_of_le_normalizer hNnY hYN
  have hne : (S : Subgroup X) ⊓ Nn ≠ ⊥ := by
    intro hb
    rw [CFSG.ABGLocalTools.isSylowOf_iff, hb, Subgroup.relIndex_bot_left] at hSN
    exact hSN.2.2 h3
  have hnorm : normalizer ((S : Subgroup X) : Set X) ≤
      normalizer (((S : Subgroup X) ⊓ Nn : Subgroup X) : Set X) := by
    intro g hg
    have hgY : g ∈ normalizer (Nn : Set X) := hYN (hNY hg)
    rw [mem_normalizer_iff] at hg hgY ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hg x, hgY x]
  have hSNn : (S : Subgroup X) ≤ Nn := by
    rw [← hirr _ inf_le_left hne hnorm]
    exact inf_le_right
  have := hNn
  set N' : Subgroup Y := Nn.subgroupOf Y with hN'
  set P : Sylow 3 Y := S.subtype hSY with hP
  have hPN : (P : Subgroup Y) ≤ N' := by
    intro x hx
    rw [hP, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hx
    exact Subgroup.mem_subgroupOf.mpr (hSNn hx)
  have hfr : normalizer ((P : Subgroup Y) : Set Y) ⊔ N' = ⊤ := Sylow.normalizer_sup_eq_top' P hPN
  have hidx : N'.index = N'.relIndex (normalizer ((P : Subgroup Y) : Set Y)) := by
    rw [← Subgroup.relIndex_sup_right, hfr, Subgroup.relIndex_top_right]
  have hdvdN : N'.relIndex (normalizer ((P : Subgroup Y) : Set Y)) ∣
      Nat.card (normalizer ((P : Subgroup Y) : Set Y)) :=
    Dvd.intro _ (Subgroup.relIndex_mul_card _ _)
  have hcardNP : Nat.card (normalizer ((P : Subgroup Y) : Set Y)) =
      Nat.card (normalizer ((S : Subgroup X) : Set X)) := by
    rw [hP, Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hSY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
  have hcardN' : Nat.card N' = Nat.card Nn :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNnY).toEquiv
  have hY : Nat.card Y ∣ Nat.card Nn * Nat.card (normalizer ((S : Subgroup X) : Set X)) := by
    rw [← N'.card_mul_index, hcardN', hidx, ← hcardNP]
    exact Nat.mul_dvd_mul_left _ hdvdN
  have h5Y : ¬ 5 ∣ Nat.card Y := by
    intro h5
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp (h5.trans hY) with h | h
    · rcases h23 5 (by norm_num) h with h' | h' <;> omega
    · exact hNS h
  have h5i : 5 ∣ Y.index := by
    have h := Y.card_mul_index
    rw [hX] at h
    have h5 : 5 ∣ Nat.card Y * Y.index := by rw [h]; norm_num
    exact ((Nat.Prime.dvd_mul (by norm_num)).mp h5).resolve_left h5Y
  have h9765 : Y.index ∣ 9765 :=
    index_dvd_of_sylow_le (p := 2) (k := 10) (by rw [hX]; norm_num) (by norm_num) T hTY
  have h1111040 : Y.index ∣ 1111040 :=
    index_dvd_of_sylow_le (p := 3) (k := 2) (by rw [hX]; norm_num) (by norm_num) S hSY
  have hmod : Y.index ≡ 1 [MOD 3] :=
    CFSG.RankThree.PartOne.SEITZ7.index_modEq_one_of_normalizer_le S hNY
  have h1085 : Y.index ∣ 1085 := Nat.dvd_gcd h9765 h1111040
  obtain ⟨k, hk⟩ := h5i
  rw [hk] at h1085 hmod
  have hk217 : k ∣ 217 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) (by simpa using h1085)
  have hle : k ≤ 217 := Nat.le_of_dvd (by norm_num) hk217
  unfold Nat.ModEq at hmod
  exact (by decide +kernel : ∀ k ≤ 217, k ∣ 217 → 5 * k % 3 = 1 % 3 → False) k hle hk217 hmod

theorem false_of_cover_L52
    {X Q : Type} [Group X] [Finite X] [Group Q] {Y : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple X) (hQ : Nonempty (Q ≃* X ⧸ center X))
    (hL : LieModel Q .PSL 5 2 1) (hpar : IsNontrivialParabolic X Y)
    (hT2 : (∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y)
    (hT3 : ∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3) : False := by
  obtain ⟨e⟩ := hQ
  have hq' : CFSG.IsQuasisimple X := ⟨⟨hq.1⟩, hq.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian X hq⟩
  have hZ : center X = ⊥ :=
    CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psl52 hq' (LieModel.of_mulEquiv e hL)
  obtain ⟨f⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hZ e.symm
  have hX : LieModel X .PSL 5 2 1 := LieModel.of_mulEquiv f.symm hL
  obtain ⟨K, _, _, hK, ⟨g⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one
      (hX.statedClassicalModel_of_ne_zero (by norm_num))
  have hinn : ∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range :=
    CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.mem_range_conj_of_mulEquiv g
      fun β hβ => by
        obtain ⟨y, hy⟩ :=
          CFSG.RankThree.PartTwo.Sec21.Hering214.inner_of_pow_three_eq_one hK (by norm_num) hβ
        exact MonoidHom.mem_range.mpr ⟨y, hy.symm⟩
  obtain ⟨S, hS⟩ := exists_sylow_three_normalizer_le hT2 hinn hZ
  obtain ⟨T, hT⟩ := exists_sylow_two_le_of_isNontrivialParabolic hpar
  obtain ⟨hN72, hirr⟩ := l52_sylow_three hX S
  obtain ⟨φ⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hX.statedClassicalModel_of_ne_zero (by norm_num))
  have hcard : Nat.card X = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.GroupTheory.GL52.card_G52
  obtain ⟨Nn, hNnY, hNn, h3, h23⟩ := hT3
  exact false_of_frattini_five hcard S (by rw [hN72]; norm_num) hirr hS T hT hNnY hNn h3 h23

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
