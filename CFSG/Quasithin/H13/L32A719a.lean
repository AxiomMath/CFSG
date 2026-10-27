module

public import CFSG.Quasithin.H13.L32A718a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A
open scoped commutatorElement

namespace HeisMod

variable {W : Type} [CommGroup W]

theorem mem_of_mul_inv_mem (hW2 : ∀ w : W, w * w = 1) {c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) {A : Subgroup W} (hcA : ∀ x ∈ A, c x ∈ A) {x : W}
    (hx : c x * x⁻¹ ∈ A) : x ∈ A := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  have horb := orbit_prod hc3 hfpf x
  have h1 : c (c x * x⁻¹) = x := by
    rw [map_mul, map_inv, hinv]
    calc c (c x) * c x = x * (x * c x * c (c x)) := by
          rw [← mul_assoc, ← mul_assoc, hW2, one_mul]
          ac_rfl
      _ = x := by rw [horb, mul_one]
  rw [← h1]
  exact hcA _ hx

theorem mem_of_pow_mul_inv_mem (hW2 : ∀ w : W, w * w = 1) {c : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) {A : Subgroup W} (hcA : ∀ x ∈ A, c x ∈ A) {x : W}
    {n : ℕ} (hn : ¬ 3 ∣ n) (hx : (c ^ n) x * x⁻¹ ∈ A) : x ∈ A := by
  have hcn : (c ^ n) = c ^ (n % 3) := pow_mod_three hc3 n
  have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hcn] at hx
  rcases hn3 with h | h
  · rw [h, pow_one] at hx
    exact mem_of_mul_inv_mem hW2 hc3 hfpf hcA hx
  · rw [h] at hx
    have h1 : c ((c ^ 2) x * x⁻¹) ∈ A := hcA _ hx
    have e3 : c ((c ^ 2) x) = x := by
      rw [← MulAut.mul_apply, ← pow_succ', hc3, MulAut.one_apply]
    have e : c ((c ^ 2) x * x⁻¹) = (c x * x⁻¹)⁻¹ := by
      rw [map_mul, map_inv, e3, mul_inv, inv_inv, mul_comm]
    rw [e] at h1
    exact mem_of_mul_inv_mem hW2 hc3 hfpf hcA (A.inv_mem_iff.mp h1)

theorem fix_mod_of_stable [Finite W] (hW2 : ∀ w : W, w * w = 1) {c q : MulAut W}
    (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1) (hqc : q * c = c * q)
    {A B : Subgroup W} (hcA : ∀ x ∈ A, c x ∈ A) (hcB : ∀ x ∈ B, c x ∈ B)
    (hqA : ∀ x ∈ A, q x ∈ A) (hqB : ∀ x ∈ B, q x ∈ B) (hcard : A.relIndex B = 4) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hqm : q ^ m = 1) : ∀ x ∈ B, q x * x⁻¹ ∈ A := by
  classical
  have hcomm : ∀ (n : ℕ) (w : W), q ((c ^ n) w) = (c ^ n) (q w) := fun n w =>
    comm_apply ((Commute.pow_right (show Commute q c from hqc) n).eq) w
  have hcnA : ∀ (n : ℕ), ∀ x ∈ A, (c ^ n) x ∈ A := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ', MulAut.mul_apply]; exact hcA _ (ih x hx)
  have hcnB : ∀ (n : ℕ), ∀ x ∈ B, (c ^ n) x ∈ B := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ', MulAut.mul_apply]; exact hcB _ (ih x hx)
  have hqnA : ∀ (n : ℕ), ∀ x ∈ A, (q ^ n) x ∈ A := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ', MulAut.mul_apply]; exact hqA _ (ih x hx)
  intro x hxB
  by_cases hxA : x ∈ A
  · exact A.mul_mem (hqA x hxA) (A.inv_mem hxA)
  have hqxA : q x ∉ A := by
    intro h
    apply hxA
    have h1 : (q ^ (m - 1 + 1)) x ∈ A := by
      rw [pow_succ, MulAut.mul_apply]
      exact hqnA _ _ h
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
    rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), hqm, MulAut.one_apply] at h1
  obtain ⟨i, hi3, hqi⟩ : ∃ i : ℕ, i < 3 ∧ q x * ((c ^ i) x)⁻¹ ∈ A := by
    by_contra hno
    push Not at hno
    let π := QuotientGroup.mk' (A.subgroupOf B)
    have := Fintype.ofFinite (↥B ⧸ A.subgroupOf B)
    have hcardQ : Fintype.card (↥B ⧸ A.subgroupOf B) = 4 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index, ← Subgroup.relIndex, hcard]
    have heq : ∀ (u v : W) (hu : u ∈ B) (hv : v ∈ B),
        π ⟨u, hu⟩ = π ⟨v, hv⟩ ↔ u * v⁻¹ ∈ A := by
      intro u v hu hv
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← A.inv_mem_iff, mul_inv, inv_inv]
    have hd : ∀ (n : ℕ), n < 3 → ∀ (n' : ℕ), n' < 3 → n ≠ n' →
        π ⟨(c ^ n) x, hcnB n x hxB⟩ ≠ π ⟨(c ^ n') x, hcnB n' x hxB⟩ := by
      intro n hn n' hn' hnn' e
      rw [heq] at e
      rcases lt_or_gt_of_ne hnn' with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
        have e' : (c ^ (n + d + 1 - n)) ((c ^ n) x) * ((c ^ n) x)⁻¹ ∈ A := by
          have : (c ^ (n + d + 1 - n)) ((c ^ n) x) = (c ^ (n + d + 1)) x := by
            rw [pow_pow_apply, Nat.sub_add_cancel (by omega)]
          rw [this, ← A.inv_mem_iff, mul_inv, inv_inv, mul_comm]
          exact e
        have := mem_of_pow_mul_inv_mem hW2 hc3 hfpf hcA (by omega) e'
        apply hxA
        have h2 := hcnA (3 - n % 3) _ this
        rwa [pow_pow_apply, show 3 - n % 3 + n = 3 * (n / 3 + 1) by omega, pow_mul, hc3,
          one_pow, MulAut.one_apply] at h2
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
        have e' : (c ^ (n' + d + 1 - n')) ((c ^ n') x) * ((c ^ n') x)⁻¹ ∈ A := by
          have : (c ^ (n' + d + 1 - n')) ((c ^ n') x) = (c ^ (n' + d + 1)) x := by
            rw [pow_pow_apply, Nat.sub_add_cancel (by omega)]
          rw [this]
          exact e
        have := mem_of_pow_mul_inv_mem hW2 hc3 hfpf hcA (by omega) e'
        apply hxA
        have h2 := hcnA (3 - n' % 3) _ this
        rwa [pow_pow_apply, show 3 - n' % 3 + n' = 3 * (n' / 3 + 1) by omega, pow_mul, hc3,
          one_pow, MulAut.one_apply] at h2
    have hne0 : ∀ (n : ℕ), n < 3 → π ⟨(c ^ n) x, hcnB n x hxB⟩ ≠ 1 := by
      intro n hn e
      have : (c ^ n) x ∈ A := by
        have e' : π ⟨(c ^ n) x, hcnB n x hxB⟩ = π ⟨1, B.one_mem⟩ := e.trans (map_one π).symm
        rw [heq] at e'
        simpa using e'
      apply hxA
      have h2 := hcnA (3 - n % 3) _ this
      rwa [pow_pow_apply, show 3 - n % 3 + n = 3 * (n / 3 + 1) by omega, pow_mul, hc3,
        one_pow, MulAut.one_apply] at h2
    have hq1 : π ⟨q x, hqB x hxB⟩ ≠ 1 := by
      intro e
      have e' : π ⟨q x, hqB x hxB⟩ = π ⟨1, B.one_mem⟩ := e.trans (map_one π).symm
      rw [heq] at e'
      exact hqxA (by simpa using e')
    have hqn : ∀ (n : ℕ), n < 3 → π ⟨q x, hqB x hxB⟩ ≠ π ⟨(c ^ n) x, hcnB n x hxB⟩ := by
      intro n hn e
      rw [heq] at e
      exact hno n hn e
    let S : Finset (↥B ⧸ A.subgroupOf B) :=
      {1, π ⟨(c ^ 0) x, hcnB 0 x hxB⟩, π ⟨(c ^ 1) x, hcnB 1 x hxB⟩,
        π ⟨(c ^ 2) x, hcnB 2 x hxB⟩, π ⟨q x, hqB x hxB⟩}
    have hS : S.card = 5 := by
      simp only [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (hqn 2 (by norm_num)).symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hd 1 (by norm_num) 2 (by norm_num) (by norm_num), (hqn 1 (by norm_num)).symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hd 0 (by norm_num) 1 (by norm_num) (by norm_num),
          hd 0 (by norm_num) 2 (by norm_num) (by norm_num), (hqn 0 (by norm_num)).symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hne0 0 (by norm_num)).symm, (hne0 1 (by norm_num)).symm,
          (hne0 2 (by norm_num)).symm, hq1.symm⟩
    have := Finset.card_le_univ S
    rw [hS, hcardQ] at this
    omega
  have hit : ∀ j : ℕ, (q ^ j) x * ((c ^ (i * j)) x)⁻¹ ∈ A := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : (q ^ (j + 1)) x = q ((q ^ j) x) := by rw [pow_succ', MulAut.mul_apply]
      have e2 : (c ^ (i * (j + 1))) x = (c ^ (i * j)) ((c ^ i) x) := by
        rw [pow_pow_apply, mul_add, mul_one]
      rw [e1, e2]
      have h1 := hqA _ ih
      rw [map_mul, map_inv, hcomm] at h1
      have h2 := hcnA (i * j) _ hqi
      rw [map_mul, map_inv] at h2
      have := A.mul_mem h1 h2
      rw [show q ((q ^ j) x) * ((c ^ (i * j)) ((c ^ i) x))⁻¹ =
          (q ((q ^ j) x) * ((c ^ (i * j)) (q x))⁻¹) *
            ((c ^ (i * j)) (q x) * ((c ^ (i * j)) ((c ^ i) x))⁻¹) by group]
      exact this
  have hm' := hit m
  rw [hqm, MulAut.one_apply] at hm'
  have hi0 : i = 0 := by
    by_contra hi
    have hnd : ¬ 3 ∣ i * m := by
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · have : i = 0 := Nat.eq_zero_of_dvd_of_lt h hi3
        exact hi this
      · exact hm h
    apply hxA
    refine mem_of_pow_mul_inv_mem hW2 hc3 hfpf hcA hnd ?_
    rw [← A.inv_mem_iff, mul_inv, inv_inv, mul_comm]
    exact hm'
  rw [hi0, pow_zero, MulAut.one_apply] at hqi
  exact hqi

end HeisMod

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem t_le_normalizer_e :
    T ≤ Subgroup.normalizer ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  intro t ht
  exact mem_normalizer_commutator ((E.t_le_hz.trans (hz_le_normalizer_U E.S.hyp hMod)) ht)
    ((le_sup_right.trans (le_normalizer_pCoreOf 2 _)) ht)

theorem v1_le_of_normal {X : Subgroup G} (hXV : X ≤ V)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) : fsuV1 T V ≤ X := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVT : V ≤ T :=
    (V_le_pCoreOf_LT E.S.hyp h13322).trans (pCoreOf_le_of_le E.S.hyp le_sup_right)
  have hXT : X ≤ T := hXV.trans hVT
  have hT2 : IsPGroup 2 ↥T := E.S.hyp.fsu.sylow.1
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have : (X.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTX
  have hne : X.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨x, hxNZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne))
  obtain ⟨hxX, hxZ⟩ := hxNZ
  have hxX' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext (Subtype.ext e))
  have hxV1 : (x : G) ∈ fsuV1 T V := by
    refine ⟨hXV hxX', Subgroup.subset_closure ⟨⟨x.2, ?_⟩, ?_⟩⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩)
    · obtain ⟨hVe, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
      exact hVe.2 _ (hXV hxX')
  refine le_of_card_eq_two_of_inf_ne_bot E.card_v1 ?_
  intro hb
  apply hx1'
  have : (x : G) ∈ fsuV1 T V ⊓ X := ⟨hxV1, hxX'⟩
  rw [hb] at this
  exact this

theorem q_comm {c y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hcL : c ∈ modO2Image (hz T V) (l1 T L V)) (hyT : y ∈ modO2Image (hz T V) T)
    (hyC : y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    (hy2 : y ^ 2 ≠ 1) (hy4 : y ^ 4 = 1)
    (huniq : ∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2)
    {q : ↥(hz T V)} (hq : (q : G) ∈ pCoreOf 2 (L ⊔ T)) :
    (QuotientGroup.mk q : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) * c = c * QuotientGroup.mk q ∧
      (QuotientGroup.mk q : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) * y ^ 2 =
        y ^ 2 * QuotientGroup.mk q ∧
      ∃ n : ℕ, (QuotientGroup.mk q : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ^ 2 ^ n = 1 := by
  obtain ⟨-, -, -, hR1Q, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have hqR : (QuotientGroup.mk q : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ∈
      modO2Image (hz T V) T ⊓ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
    rw [← hR1C, hR1Q]
    exact mem_modO2Image_iff.mpr ⟨q, hq, rfl⟩
  set q' := (QuotientGroup.mk q : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) with hq'
  refine ⟨(Subgroup.mem_centralizer_iff.mp hqR.2 c hcL).symm, ?_, ?_⟩
  · have : (modO2Image (hz T V) (l1 T L V)).Normal := E.l1dot_normal
    have hCn : (Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)))).Normal := inferInstance
    have hyT2 : y ^ 2 ∈ modO2Image (hz T V) T := Subgroup.pow_mem _ hyT 2
    have h1 : q' * y ^ 2 * q'⁻¹ = y ^ 2 := by
      refine huniq _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hqR.1 hyT2)
        (Subgroup.inv_mem _ hqR.1)) (hCn.conj_mem _ (Subgroup.pow_mem _ hyC 2) q') ?_ ?_
      · rw [sq, show q' * y ^ 2 * q'⁻¹ * (q' * y ^ 2 * q'⁻¹) = q' * (y ^ 2 * y ^ 2) * q'⁻¹ by
          group, hy22, mul_one, mul_inv_cancel]
      · intro e
        apply hy2
        have : y ^ 2 = q'⁻¹ * (q' * y ^ 2 * q'⁻¹) * q' := by group
        rw [this, e, mul_one, inv_mul_cancel]
    calc q' * y ^ 2 = q' * y ^ 2 * q'⁻¹ * q' := by group
      _ = y ^ 2 * q' := by rw [h1]
  · have hT2 : IsPGroup 2 ↥(modO2Image (hz T V) T) := E.isPGroup_tdot
    obtain ⟨n, hn⟩ := hT2 ⟨q', hqR.1⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

theorem comm_e_q : ⁅⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, pCoreOf 2 (L ⊔ T)⁆ = V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, hLTV, hV1c, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  obtain ⟨-, -, c, y, -, -, hcL, -, hc3, -, -, hyT, hyC, hy2, hy4, huniq, -, hfpf, -, -, h64, -,
    h4c⟩ := E.exists_frame hF
  obtain ⟨hfixy, hcommt⟩ := E.fixV_y hF hcL hc3 hyT hyC hy4 hfpf h64 h4c
  obtain ⟨heqE, h16⟩ := E.wsub_e_eq hF hcL hc3 hyT hyC hy2 hy4 huniq hfpf h64 h4c
  obtain ⟨-, hrange⟩ := E.wsub_e_le hF hcL hc3 hyT hyC hy2 hy4 huniq hfpf h4c
  obtain ⟨-, -, -, hR1Q, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hcardV := E.card_wsub_v hF
  have hyQ : y ∈ modO2Image (hz T V) (pCoreOf 2 (L ⊔ T)) := by
    rw [← hR1Q, hR1C]
    exact ⟨hyT, hyC⟩
  obtain ⟨q₀, hq₀Q, hq₀y⟩ := mem_modO2Image_iff.mp hyQ
  set hh := hF.toHypF91 with hhdef
  have hW2 := umod_sq hh
  have hinv : ∀ w : UMod hh, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hQhz : pCoreOf 2 (L ⊔ T) ≤ hz T V :=
    (pCoreOf_le_of_le E.S.hyp le_sup_right).trans E.t_le_hz
  have hEU : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ fsuU T V := commutator_fsuU_le E.S.hyp hMod
  have hEU' : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ conjClosure V (hz T V) := hUe ▸ hEU
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (V : Set G) :=
    (pCoreOf_le_of_le E.S.hyp le_sup_right).trans (le_sup_right.trans hLTV)
  have hsq : ∀ u ∈ conjClosure V (hz T V), u * u = 1 := fun u hu => by
    have := (hF.F911_3).2 u hu
    rwa [sq] at this
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have ht2 : rhoDot hh (y ^ 2) * rhoDot hh (y ^ 2) = 1 := by rw [← map_mul, hy22, map_one]
  have hy2c : y ^ 2 * c = c * y ^ 2 :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC 2) c hcL).symm
  have hyc : y * c = c * y := (Subgroup.mem_centralizer_iff.mp hyC c hcL).symm
  have hmul : ∀ x x' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V), x * x' = x' * x →
      rhoDot hh x * rhoDot hh x' = rhoDot hh x' * rhoDot hh x :=
    fun x x' e => by rw [← map_mul, e, map_mul]
  have hρc3 : rhoDot hh c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hcV : ∀ x ∈ Wsub hh V, rhoDot hh c x ∈ Wsub hh V := by
    intro x hx
    rw [← hfixy] at hx ⊢
    rw [HeisMod.mem_fixV_zpowers] at hx ⊢
    rw [HeisMod.comm_apply (hmul _ _ hyc), hx]
  have hcF : ∀ x ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))), rhoDot hh c x ∈
      fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
    intro x hx
    rw [HeisMod.mem_fixV_zpowers] at hx ⊢
    rw [HeisMod.comm_apply (hmul _ _ hy2c), hx]
  have hVF : Wsub hh V ≤ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
    rw [← hcommt]
    exact HeisMod.commV_le_fixV hW2 ht2
  have hrel : (Wsub hh V).relIndex (fixV (Subgroup.zpowers (rhoDot hh (y ^ 2)))) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (Wsub hh V) (fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))))
    rw [inf_eq_left.mpr hVF, hcardV, h16] at h1
    omega
  have hQtriv : ∀ q : ↥(hz T V), (q : G) ∈ pCoreOf 2 (L ⊔ T) →
      ∀ x ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))),
        C1Pack.rhoH hh q x * x⁻¹ ∈ Wsub hh V := by
    intro q hq x hx
    obtain ⟨hqc, hqt, n, hn⟩ := E.q_comm hcL hyT hyC hy2 hy4 huniq hq
    have hm : ¬ 3 ∣ 2 ^ n := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hqA : ∀ w ∈ Wsub hh V, rhoDot hh (QuotientGroup.mk q) w ∈ Wsub hh V := fun w hw =>
      rhoH_mem_Wsub hh q hVU (conjSub_eq_self_iff.mpr (hQV hq)) hw
    have hqB : ∀ w ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))),
        rhoDot hh (QuotientGroup.mk q) w ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
      intro w hw
      rw [HeisMod.mem_fixV_zpowers] at hw ⊢
      rw [← HeisMod.comm_apply (hmul _ _ hqt), hw]
    exact HeisMod.fix_mod_of_stable hW2 hρc3 hfpf (hmul _ _ hqc) hcV hcF hqA hqB hrel hm
      (by rw [← map_pow, hn, map_one]) x hx
  have hle : ⁅⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, pCoreOf 2 (L ⊔ T)⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro e he q hq
    have heU : e ∈ conjClosure V (hz T V) := hEU' he
    have hqhz : q ∈ hz T V := hQhz hq
    have h1 : q * e * q⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH hqhz heU
    have hceq : ⁅e, q⁆ = e * (q * e * q⁻¹) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_left (hsq e heU)]
      group
    have hmem : ⁅e, q⁆ ∈ conjClosure V (hz T V) := by
      rw [hceq]
      exact (conjClosure V (hz T V)).mul_mem heU h1
    have hx : clsU hh heU ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
      rw [← heqE]
      exact clsU_mem_Wsub hh heU he
    have h2 := hQtriv ⟨q, hqhz⟩ hq _ hx
    have e1 : clsU hh hmem = clsU hh heU * C1Pack.rhoH hh ⟨q, hqhz⟩ (clsU hh heU) := by
      rw [rhoH_clsU, clsU_mul]
      exact clsU_congr hh _ _ hceq
    have h3 : clsU hh hmem ∈ Wsub hh V := by
      rw [e1, mul_comm]
      rw [hinv] at h2
      exact h2
    obtain ⟨v, hvU, hvV, hve⟩ := exists_clsU_of_mem_Wsub hh hVU h3
    have h4 : v⁻¹ * ⁅e, q⁆ ∈ fsuV1 T V := (clsU_eq_iff _ hvU hmem).mp hve
    have e2 : ⁅e, q⁆ = v * (v⁻¹ * ⁅e, q⁆) := by group
    rw [e2]
    exact V.mul_mem hvV (Subgroup.mem_inf.mp h4).1
  have hstep : ∀ v ∈ V, ∃ w ∈ ⁅⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, pCoreOf 2 (L ⊔ T)⁆,
      w⁻¹ * v ∈ fsuV1 T V := by
    intro v hv
    have hvU : v ∈ conjClosure V (hz T V) := hVU hv
    have hvW : clsU hh hvU ∈ commV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
      rw [hcommt]
      exact clsU_mem_Wsub hh hvU hv
    rw [HeisMod.commV_zpowers_eq_range hW2 ht2] at hvW
    obtain ⟨w, hw⟩ := hvW
    have hxE : HeisMod.trHom (rhoDot hh y) w ∈ Wsub hh ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
      hrange ⟨w, rfl⟩
    obtain ⟨e, heU, heE, hex⟩ := exists_clsU_of_mem_Wsub hh hEU' hxE
    have h1 : (q₀ : G) * e * (q₀ : G)⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH q₀.2 heU
    have hceq : ⁅e, (q₀ : G)⁆ = e * ((q₀ : G) * e * (q₀ : G)⁻¹) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_left (hsq e heU)]
      group
    have hmem : ⁅e, (q₀ : G)⁆ ∈ conjClosure V (hz T V) := by
      rw [hceq]
      exact (conjClosure V (hz T V)).mul_mem heU h1
    have hyy : rhoDot hh y (rhoDot hh y w) = rhoDot hh (y ^ 2) w := by
      rw [sq, map_mul, MulAut.mul_apply]
    have hval : clsU hh hmem = clsU hh hvU := by
      have e1 : clsU hh hmem = clsU hh heU * rhoDot hh y (clsU hh heU) := by
        rw [← hq₀y, QuotientGroup.mk'_apply, rhoDot_mk, rhoH_clsU, clsU_mul]
        exact clsU_congr hh _ _ hceq
      rw [e1, hex, ← hw, HeisMod.trHom_apply, HeisMod.trHom_apply, map_mul, hyy, mul_assoc,
        ← mul_assoc (rhoDot hh y w), hW2, one_mul]
    exact ⟨⁅e, (q₀ : G)⁆, Subgroup.commutator_mem_commutator heE hq₀Q,
      (clsU_eq_iff hh hmem hvU).mp hval⟩
  have hTX : T ≤ Subgroup.normalizer
      ((⁅⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_commutator (E.t_le_normalizer_e ht)
      ((le_sup_right.trans (le_normalizer_pCoreOf 2 _)) ht)
  have hne : ⁅⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, pCoreOf 2 (L ⊔ T)⁆ ≠ ⊥ := by
    intro hb
    have hVV1 : V ≤ fsuV1 T V := by
      intro v hv
      obtain ⟨w, hw, hwv⟩ := hstep v hv
      rw [hb, Subgroup.mem_bot] at hw
      rw [hw, inv_one, one_mul] at hwv
      exact hwv
    have := Subgroup.card_le_of_le hVV1
    rw [hV8, hV1c] at this
    omega
  have hV1 := E.v1_le_of_normal hle hTX hne
  refine le_antisymm hle fun v hv => ?_
  obtain ⟨w, hw, hwv⟩ := hstep v hv
  have e : v = w * (w⁻¹ * v) := by group
  rw [e]
  exact Subgroup.mul_mem _ hw (hV1 hwv)

theorem comm_s_q :
    ⁅L32A.sL T L V, pCoreOf 2 (L ⊔ T)⁆ = conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
  lemma14_7_13_one E.setting_hz hF (stmtL32NModule_of_inputs E.h1332 E.h1334)

theorem comm_r_q :
    ⁅conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L, pCoreOf 2 (L ⊔ T)⁆ = V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hEU := commutator_fsuU_le E.S.hyp hMod
  have hQE : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer
      ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := fun q hq =>
    mem_normalizer_commutator (pCoreOf_sup_le_normalizer_fsuU E.S.hyp hMod hq)
      (Subgroup.le_normalizer hq)
  have hRQ : conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ pCoreOf 2 (L ⊔ T) :=
    (conjClosure_mono hEU le_rfl).trans (sL_le_pCoreOf E.setting_hz hF hMod)
  rw [commutator_conjClosure_eq (le_normalizer_pCoreOf_sup T L) hQE hRQ, E.comm_e_q hF]
  exact le_antisymm (conjClosure_le fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp ((le_sup_left.trans hLTV) hl) v).mp hv) (le_conjClosure V L)

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem r_le_center :
    conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ centerOf (L32A.sL T L V) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  have hne : Quasithin.conjSub l₀ (fsuU T V) ≠ fsuU T V := by
    rw [← hl₀U]
    exact E.ualpha_ne hF N
  refine lemma14_7_13_three E.setting_hz hF h13322 hMod hl₀ hne fun x hx y hy => ?_
  rw [← E.centralizer_ualpha_eq hF N] at hx
  rw [← hl₀U] at hy
  exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm

theorem frattini_s :
    frattiniOf (L32A.sL T L V) = ⁅L32A.sL T L V, L32A.sL T L V⁆ ∧
      ⁅L32A.sL T L V, L32A.sL T L V⁆ = V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  obtain ⟨hV, hZ⟩ := E.comm_ualpha hF N
  have hne : Quasithin.conjSub l₀ (fsuU T V) ≠ fsuU T V := by
    rw [← hl₀U]
    exact E.ualpha_ne hF N
  rw [hl₀U] at hV hZ
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hAV : ⁅fsuU T V, Quasithin.conjSub l₀ (fsuU T V)⁆ ≤ V := le_sup_left.trans hV.le
  have hVα : V ≤ Quasithin.conjSub l₀ (fsuU T V) := by
    intro v hv
    rw [Quasithin.mem_conjSub]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hLV (inv_mem hl₀)) v).mp hv
    rw [inv_inv] at h1
    rw [hUe]
    exact le_conjClosure V _ h1
  have hN : fsuU T V ≤ Subgroup.normalizer (Quasithin.conjSub l₀ (fsuU T V) : Set G) := by
    intro u hu
    refine mem_normalizer_of_forall_conj (fun u' hu' x hx => ?_) hu
    have hc : ⁅u', x⁆ ∈ Quasithin.conjSub l₀ (fsuU T V) :=
      hVα (hAV (Subgroup.commutator_mem_commutator hu' hx))
    have e : u' * x * u'⁻¹ = ⁅u', x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hc hx
  obtain ⟨hΦ, hSS⟩ := lemma14_7_13_four E.setting_hz hF h13322 hMod hl₀ hne hN
  refine ⟨hΦ, ?_⟩
  have hVL : conjClosure V L = V :=
    le_antisymm (conjClosure_le fun l hl v hv =>
      (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv) (le_conjClosure V L)
  have hle : ⁅L32A.sL T L V, L32A.sL T L V⁆ ≤ V := by
    rw [hSS]
    exact (conjClosure_mono hAV le_rfl).trans hVL.le
  have hTS : T ≤ Subgroup.normalizer (L32A.sL T L V : Set G) :=
    le_normalizer_conjClosure_of_normalizes
      (E.t_le_hz.trans (hz_le_normalizer_U E.S.hyp hMod)) (E.S.hyp.normalizes h13322)
  have hTSS : T ≤ Subgroup.normalizer
      ((⁅L32A.sL T L V, L32A.sL T L V⁆ : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_commutator (hTS ht) (hTS ht)
  have hAS : ⁅fsuU T V, Quasithin.conjSub l₀ (fsuU T V)⁆ ≤ ⁅L32A.sL T L V, L32A.sL T L V⁆ := by
    rw [hSS]
    exact le_conjClosure _ _
  have hne' : ⁅L32A.sL T L V, L32A.sL T L V⁆ ≠ ⊥ := by
    intro hb
    have hc := Subgroup.card_le_of_le (hZ.trans (hAS.trans hb.le))
    rw [Subgroup.card_bot, Quasithin.conjSub,
      Subgroup.card_map_of_injective (MulAut.conj _).injective, E.card_v1] at hc
    omega
  have hV1 := E.v1_le_of_normal hle hTSS hne'
  exact le_antisymm hle (hV.symm.le.trans (sup_le hAS hV1))

end Ctx7153

end CFSG.Quasithin.H13.L32A
