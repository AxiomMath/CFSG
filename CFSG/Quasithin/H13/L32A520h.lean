module

public import CFSG.Quasithin.H13.L32A520f
public import CFSG.Quasithin.H13.L32A520g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev linesY (Y : Subgroup G) : Set (Subgroup G) :=
  {W | pCoreOf 2 Y ≤ W ∧ W ≤ Y ∧ (pCoreOf 2 Y).relIndex W = 3}

abbrev lineOf (Y : Subgroup G) (w : G) : Subgroup G := Subgroup.zpowers w ⊔ pCoreOf 2 Y

omit [Finite G] in
theorem relIndex_lineOf {Y : Subgroup G} {w : G} (hwY : w ∈ Y) (hwQ : w ∉ pCoreOf 2 Y)
    (hw3 : w ^ 3 ∈ pCoreOf 2 Y) : (pCoreOf 2 Y).relIndex (lineOf Y w) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := (pCoreOf 2 Y).subgroupOf Y with hN
  have hle : lineOf Y w ≤ Y := sup_le (Subgroup.zpowers_le.mpr hwY) (pCoreOf_le 2 Y)
  rw [relIndex_eq_card_map hle]
  have e : ((lineOf Y w).subgroupOf Y).map (QuotientGroup.mk' N) =
      Subgroup.zpowers (QuotientGroup.mk' N ⟨w, hwY⟩) := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : (z : G) ∈ pCoreOf 2 Y ⊔ Subgroup.zpowers w := by
        rw [sup_comm]
        exact Subgroup.mem_subgroupOf.mp hz
      obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        (Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 Y hwY))).mp hz'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      refine ⟨m, ?_⟩
      have hzq : z = ⟨a, pCoreOf_le 2 Y ha⟩ * ⟨w, hwY⟩ ^ m := Subtype.ext (by simp [hab])
      have ha1 : QuotientGroup.mk' N ⟨a, pCoreOf_le 2 Y ha⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr ha
      rw [hzq, map_mul, ha1, one_mul, map_zpow]
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers w)),
        rfl⟩
  rw [e, Nat.card_zpowers]
  apply orderOf_eq_prime
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hw3)
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hwQ (Subgroup.mem_subgroupOf.mp h)

namespace E9Ctx

variable {T L V H Y : Subgroup G} (C : E9Ctx T L V H Y)
include C

theorem mem_cSec {y : G} (hy : y ∈ kY T V Y) (hodd : Odd (orderOf y)) :
    y ∈ centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) := by
  have hMod := stmtL32NModule_of_inputs C.h1332 C.h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of C.h1332) hMod C.h1222
  have S14 := Hyp147.set14 C.S.hyp C.h1222 C.h1332 C.h1334 hV2
  have hsq := S14.sq_mem_cent hy.2
  have hyV : y ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hsq) (A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hodd))
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := C.Y_le_M hy.1
  refine mem_centralizerSection.mpr ⟨hyL, hyL, normalizer_le_normalizer_pCoreOf 2 L hyL,
    fun l hl => ?_⟩
  rw [← S14.cent_eq]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h2 : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp (inv_mem hl)
    rw [show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) by group]
    exact mul_mem hl h2
  · have h2 : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer _ (S14.LV hl))
        y).mp hyV
    exact mul_mem h2 (inv_mem hyV)

theorem normalizer_K_le :
    Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hK3 := C.K3
  have hKQ : ¬ kY T V Y ≤ pCoreOf 2 Y := fun h => by
    rw [Subgroup.relIndex_eq_one.mpr h] at hK3
    exact absurd hK3 (by norm_num)
  have hX1 : oTwoUpper (kY T V Y) ≠ ⊥ :=
    oTwoUpper_ne_bot_of_not_le Nat.prime_three (by norm_num) C.Y3 (kY_le T V Y) hKQ
  have hXC : oTwoUpper (kY T V Y) ≤
      centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) :=
    (Subgroup.closure_le _).mpr fun y hy => C.mem_cSec hy.1 hy.2
  have hN := normalizer_le_of_le_cSec C.h1332 C.S
    ((oTwoUpper_le _).trans ((kY_le T V Y).trans C.YH))
    (C.T_le_N_K.trans (normalizer_le_normalizer_oTwoUpper _)) (oTwoUpper_oTwoUpper _) hX1 hXC
  exact (normalizer_le_normalizer_oTwoUpper _).trans hN

theorem not_H_le_N_K : ¬ H ≤ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) :=
  fun h => C.S.hz.2.2 (h.trans C.normalizer_K_le)

theorem lineOf_mem {w : G} (hwY : w ∈ Y) (hwQ : w ∉ pCoreOf 2 Y) : lineOf Y w ∈ linesY Y :=
  ⟨le_sup_right, sup_le (Subgroup.zpowers_le.mpr hwY) (pCoreOf_le 2 Y),
    relIndex_lineOf hwY hwQ (C.Y3 w hwY)⟩

theorem eq_lineOf {W : Subgroup G} (hW : W ∈ linesY Y) {w : G} (hw : w ∈ W)
    (hwQ : w ∉ pCoreOf 2 Y) : W = lineOf Y w := by
  have hle : lineOf Y w ≤ W := sup_le (Subgroup.zpowers_le.mpr hw) hW.1
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : pCoreOf 2 Y ≤ lineOf Y w) hle
  rw [(C.lineOf_mem (hW.2.1 hw) hwQ).2.2, hW.2.2] at hm
  have h1 : (lineOf Y w).relIndex W = 1 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (hm.trans (mul_one 3).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle

theorem line_eq {W W' : Subgroup G} (hW : W ∈ linesY Y) (hW' : W' ∈ linesY Y) {w : G}
    (hw : w ∈ W) (hw' : w ∈ W') (hwQ : w ∉ pCoreOf 2 Y) : W = W' :=
  (C.eq_lineOf hW hw hwQ).trans (C.eq_lineOf hW' hw' hwQ).symm

theorem K_mem_lines : kY T V Y ∈ linesY Y := ⟨C.Q_le_K, kY_le T V Y, C.K3⟩

theorem conjSub_mem_lines {h : G} (hh : h ∈ H) {W : Subgroup G} (hW : W ∈ linesY Y) :
    conjSub h W ∈ linesY Y := by
  have hQ : conjSub h (pCoreOf 2 Y) = pCoreOf 2 Y := conjSub_eq_iff.mpr (C.HQ hh)
  have hY : conjSub h Y = Y := conjSub_eq_iff.mpr (C.HY hh)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hQ]
    exact Subgroup.map_mono hW.1
  · rw [← hY]
    exact Subgroup.map_mono hW.2.1
  · rw [← hQ, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective]
    exact hW.2.2

theorem mem_Q_of_two {w : G} (hwY : w ∈ Y) {n : ℕ} (hw : w ^ 2 ^ n = 1) : w ∈ pCoreOf 2 Y := by
  have hcop : Nat.Coprime 3 (orderOf w) :=
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hw)
  exact (Subgroup.zpowers_le.mpr (C.Y3 w hwY)) (A4.mem_zpowers_pow_of_coprime hcop)

theorem mem_lines_cases {x k : G} (hx : x ∈ l1 T L V ⊔ pCoreOf 2 Y) (hkK : k ∈ kY T V Y)
    (hkQ : k ∉ pCoreOf 2 Y) {W : Subgroup G} (hW : W ∈ linesY Y) :
    W = kY T V Y ∨ ∃ j : ℕ, j < 3 ∧ x * k ^ j ∈ W := by
  by_cases hWK : W = kY T V Y
  · exact Or.inl hWK
  right
  have hxY : x ∈ Y := C.L1Q_le hx
  have hkY : k ∈ Y := kY_le T V Y hkK
  have hinf : W ⊓ kY T V Y = pCoreOf 2 Y := by
    refine le_antisymm (fun w hw => ?_) (le_inf hW.1 C.Q_le_K)
    by_contra hwQ
    exact hWK (C.line_eq hW C.K_mem_lines hw.1 hw.2 hwQ)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := le_normalizer_of_comm_mem hW.1 C.comm hW.2.1
  have hsup : W ⊔ kY T V Y = Y := by
    have h1 := U3.relIndex_sup_eq (K := W) (T := kY T V Y) ((kY_le T V Y).trans hYW)
    rw [hinf, hW.2.2] at h1
    have hle : W ⊔ kY T V Y ≤ Y := sup_le hW.2.1 (kY_le T V Y)
    have hKY : (kY T V Y).relIndex Y = 3 := by
      have hm := Subgroup.relIndex_mul_relIndex _ _ _ C.Q_le_K (kY_le T V Y)
      rw [C.card, C.K3] at hm
      omega
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : kY T V Y ≤ W ⊔ kY T V Y) hle
    rw [h1, hKY] at hm
    have h2 : (W ⊔ kY T V Y).relIndex Y = 1 := by omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes ((kY_le T V Y).trans hYW)).mp (hsup ▸ hxY)
  have hbK : b⁻¹ ∈ pCoreOf 2 Y ⊔ Subgroup.zpowers k := by
    have hKl := C.eq_lineOf C.K_mem_lines hkK hkQ
    have hb' : b⁻¹ ∈ lineOf Y k := hKl ▸ (kY T V Y).inv_mem hb
    rw [sup_comm]
    exact hb'
  obtain ⟨q, hq, c, hc, hqc⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 Y hkY))).mp hbK
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hxq : x * q * x⁻¹ ∈ pCoreOf 2 Y :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hxY) q).mp hq
  have h1 : x * k ^ m ∈ W := by
    have ha' : a = x * (q * k ^ m) := by rw [← hqc, hab]; group
    have e : x * k ^ m = (x * q * x⁻¹)⁻¹ * a := by rw [ha']; group
    rw [e]
    exact mul_mem (inv_mem (hW.1 hxq)) ha
  have hdecomp : k ^ m = k ^ (m % 3) * (k ^ 3) ^ (m / 3) := by
    rw [← zpow_natCast k 3, ← zpow_mul, ← zpow_add]
    congr 1
    omega
  have h2 : x * k ^ (m % 3) ∈ W := by
    have e : x * k ^ (m % 3) = x * k ^ m * ((k ^ 3) ^ (m / 3))⁻¹ := by rw [hdecomp]; group
    rw [e]
    have hq3 : (k ^ 3) ^ (m / 3) ∈ pCoreOf 2 Y := (pCoreOf 2 Y).zpow_mem (C.Y3 k hkY) _
    exact W.mul_mem h1 (W.inv_mem (hW.1 hq3))
  have hnn : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have hlt : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  refine ⟨(m % 3).toNat, by omega, ?_⟩
  have e : (k ^ (m % 3).toNat : G) = k ^ (m % 3) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  rw [e]
  exact h2

theorem mul_pow_not_mem_K {x k : G} (hx : x ∈ l1 T L V ⊔ pCoreOf 2 Y) (hxQ : x ∉ pCoreOf 2 Y)
    (hkK : k ∈ kY T V Y) (j : ℕ) : x * k ^ j ∉ kY T V Y := by
  intro h
  apply hxQ
  rw [← C.K_inf]
  refine ⟨?_, hx⟩
  have hkj : (k ^ j)⁻¹ ∈ kY T V Y := (kY T V Y).inv_mem ((kY T V Y).pow_mem hkK j)
  rw [show x = x * k ^ j * (k ^ j)⁻¹ by group]
  exact (kY T V Y).mul_mem h hkj

theorem lines_eq {x k : G} (hx : x ∈ l1 T L V ⊔ pCoreOf 2 Y) (hxQ : x ∉ pCoreOf 2 Y)
    (hkK : k ∈ kY T V Y) (hkQ : k ∉ pCoreOf 2 Y) :
    linesY Y = {kY T V Y, lineOf Y x, lineOf Y (x * k), lineOf Y (x * k ^ 2)} := by
  have hxY : x ∈ Y := C.L1Q_le hx
  have hkY : k ∈ Y := kY_le T V Y hkK
  have hnQ : ∀ j : ℕ, x * k ^ j ∉ pCoreOf 2 Y := fun j h =>
    C.mul_pow_not_mem_K hx hxQ hkK j (C.Q_le_K h)
  have hmem : ∀ j : ℕ, lineOf Y (x * k ^ j) ∈ linesY Y := fun j =>
    C.lineOf_mem (mul_mem hxY (pow_mem hkY j)) (hnQ j)
  ext W
  constructor
  · intro hW
    rcases C.mem_lines_cases hx hkK hkQ hW with h | ⟨j, hj, hxj⟩
    · exact Or.inl h
    · have h' := C.eq_lineOf hW hxj (hnQ j)
      interval_cases j
      · right; left; simpa using h'
      · right; right; left; simpa using h'
      · right; right; right; exact h'
  · rintro (rfl | rfl | rfl | rfl)
    · exact C.K_mem_lines
    · simpa using hmem 0
    · simpa using hmem 1
    · exact hmem 2

theorem ncard_lines {x k : G} (hx : x ∈ l1 T L V ⊔ pCoreOf 2 Y) (hxQ : x ∉ pCoreOf 2 Y)
    (hkK : k ∈ kY T V Y) (hkQ : k ∉ pCoreOf 2 Y) : (linesY Y).ncard = 4 := by
  have hxY : x ∈ Y := C.L1Q_le hx
  have hkY : k ∈ Y := kY_le T V Y hkK
  have hnQ : ∀ j : ℕ, x * k ^ j ∉ pCoreOf 2 Y := fun j h =>
    C.mul_pow_not_mem_K hx hxQ hkK j (C.Q_le_K h)
  have hmem : ∀ j : ℕ, lineOf Y (x * k ^ j) ∈ linesY Y := fun j =>
    C.lineOf_mem (mul_mem hxY (pow_mem hkY j)) (hnQ j)
  have hk2 : k ^ 2 ∉ pCoreOf 2 Y := fun h => hkQ (by
    rw [show k = k ^ 3 * (k ^ 2)⁻¹ by group]
    exact mul_mem (C.Y3 k hkY) (inv_mem h))
  have hK : ∀ j : ℕ, kY T V Y ≠ lineOf Y (x * k ^ j) := fun j h =>
    C.mul_pow_not_mem_K hx hxQ hkK j (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hne : ∀ i d : ℕ, k ^ d ∉ pCoreOf 2 Y →
      lineOf Y (x * k ^ i) ≠ lineOf Y (x * k ^ (i + d)) := by
    intro i d hd h
    have hkd : k ^ d ∈ lineOf Y (x * k ^ i) := by
      have h1 : x * k ^ (i + d) ∈ lineOf Y (x * k ^ i) := h ▸ Subgroup.mem_sup_left
        (Subgroup.mem_zpowers _)
      have h2 : x * k ^ i ∈ lineOf Y (x * k ^ i) := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      have e : k ^ d = (x * k ^ i)⁻¹ * (x * k ^ (i + d)) := by rw [pow_add]; group
      rw [e]
      exact mul_mem (inv_mem h2) h1
    exact hK i (C.line_eq C.K_mem_lines (hmem i) (pow_mem hkK d) hkd hd)
  rw [C.lines_eq hx hxQ hkK hkQ]
  have h01 := hne 0 1 (by simpa using hkQ)
  have h02 := hne 0 2 hk2
  have h12 := hne 1 1 (by simpa using hkQ)
  simp only [pow_zero, mul_one, zero_add, pow_one] at h01 h02
  rw [show (1 : ℕ) + 1 = 2 from rfl, pow_one] at h12
  have hK0 := hK 0
  have hK1 := hK 1
  have hK2 := hK 2
  simp only [pow_zero, mul_one, pow_one] at hK0 hK1
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h12]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h01, h02⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hK0, hK1, hK2⟩

theorem H_le_N_L1Q :
    H ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 Y : Subgroup G) : Set G) ∧
      ((Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G)).subgroupOf H).index = 3 := by
  obtain ⟨x₀, hx₀, hx₀K⟩ := C.psi_facts.2.1
  have hxQ : x₀ ∉ pCoreOf 2 Y := fun h => hx₀K (C.psi_facts.1 h)
  have hx : x₀ ∈ l1 T L V ⊔ pCoreOf 2 Y := Subgroup.mem_sup_left hx₀
  obtain ⟨k, hkK, hkQ⟩ : ∃ k ∈ kY T V Y, k ∉ pCoreOf 2 Y := by
    by_contra h
    push Not at h
    have h3 := C.K3
    rw [Subgroup.relIndex_eq_one.mpr h] at h3
    exact absurd h3 (by norm_num)
  have hΛ4 := C.ncard_lines hx hxQ hkK hkQ
  have hΛfin : (linesY Y).Finite := by
    rw [C.lines_eq hx hxQ hkK hkQ]
    exact Set.toFinite _
  set O : Set (Subgroup G) := {W | ∃ h ∈ H, W = conjSub h (kY T V Y)} with hO
  have hOΛ : O ⊆ linesY Y := by
    rintro _ ⟨h, hh, rfl⟩
    exact C.conjSub_mem_lines hh C.K_mem_lines
  have hKO : kY T V Y ∈ O := ⟨1, one_mem H, (conjSub_one _).symm⟩
  have hOcard : O.ncard =
      ((Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G)).subgroupOf H).index := by
    rw [← Nat.card_coe_set_eq]
    exact card_conjOrbit H (kY T V Y)
  have hodd : ¬ 2 ∣ O.ncard := by
    rw [hOcard]
    intro h2
    have hsyl := isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.TH
    refine hsyl.2.2 (h2.trans (Subgroup.index_dvd_of_le fun t ht => ?_))
    exact Subgroup.mem_subgroupOf.mpr (C.T_le_N_K (Subgroup.mem_subgroupOf.mp ht))
  have hne1 : O.ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    apply C.not_H_le_N_K
    intro h hh
    have h2 : conjSub h (kY T V Y) ∈ O := ⟨h, hh, rfl⟩
    rw [ha] at h2 hKO
    rw [Set.mem_singleton_iff] at h2 hKO
    exact conjSub_eq_iff.mp (h2.trans hKO.symm)
  have hle4 : O.ncard ≤ 4 := hΛ4 ▸ Set.ncard_le_ncard hOΛ hΛfin
  have hpos : 0 < O.ncard := (Set.ncard_pos (hΛfin.subset hOΛ)).mpr ⟨_, hKO⟩
  have hO3 : O.ncard = 3 := by omega
  have hdiff : (linesY Y \ O).ncard = 1 := by
    rw [Set.ncard_sdiff hOΛ (hΛfin.subset hOΛ), hΛ4, hO3]
  obtain ⟨W₀, hW₀⟩ := Set.ncard_eq_one.mp hdiff
  have hW₀m : W₀ ∈ linesY Y \ O := by rw [hW₀]; rfl
  have hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G) := fun h hh => by
    have h1 : conjSub h W₀ ∈ linesY Y \ O := by
      refine ⟨C.conjSub_mem_lines hh hW₀m.1, fun hO' => ?_⟩
      obtain ⟨h', hh', he⟩ := hO'
      apply hW₀m.2
      refine ⟨h⁻¹ * h', mul_mem (inv_mem hh) hh', ?_⟩
      rw [conjSub_mul, ← he, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [hW₀, Set.mem_singleton_iff] at h1
    exact conjSub_eq_iff.mp h1
  have hW₀Y : W₀ ≤ Y := hW₀m.1.2.1
  have hW₀3 : ∀ w ∈ W₀, w ^ 3 ∈ pCoreOf 2 W₀ := fun w hw =>
    le_pCoreOf_of_le_normalizer 2 hW₀m.1.1 (hW₀Y.trans (le_normalizer_pCoreOf 2 Y))
      (pCoreOf_isPGroup 2 Y) (C.Y3 w (hW₀Y hw))
  have hL : l1 T L V ≤ W₀ := by
    rcases lemma14_5_20A C.h1222 C.h1332 C.h1334 C.S Nat.prime_three (hW₀Y.trans C.YH) hHW₀
      hW₀3 with h | ⟨-, h⟩
    · exfalso
      rw [inf_eq_left.mpr (hW₀Y.trans C.Y_le_M)] at h
      have h2 : W₀ ≤ pCoreOf 2 Y := fun w hw => by
        have hp := pCoreOf_isPGroup 2 W₀ ⟨w, h ▸ hw⟩
        obtain ⟨n, hn⟩ := hp
        exact C.mem_Q_of_two (hW₀Y hw) (n := n) (by simpa using congrArg Subtype.val hn)
      have h3 := hW₀m.1.2.2
      rw [Subgroup.relIndex_eq_one.mpr h2] at h3
      exact absurd h3 (by norm_num)
    · exact h
  have hW₀eq : l1 T L V ⊔ pCoreOf 2 Y = W₀ := by
    have hle : l1 T L V ⊔ pCoreOf 2 Y ≤ W₀ := sup_le hL hW₀m.1.1
    have hm := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : pCoreOf 2 Y ≤ l1 T L V ⊔ pCoreOf 2 Y) hle
    rw [C.L1Q3, hW₀m.1.2.2] at hm
    have h1 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex W₀ = 1 := by omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
  exact ⟨hW₀eq ▸ hHW₀, hOcard ▸ hO3⟩

end E9Ctx

end CFSG.Quasithin.H13.L32A
