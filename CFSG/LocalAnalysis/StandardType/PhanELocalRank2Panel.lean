module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane
import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
import CFSG.LocalAnalysis.StandardType.PhanELocalGate
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

section Helpers

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem plpa_mem_Vsub_one (v : Fin 3 → K) :
    v ∈ Vsub (K := K) 3 1 ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    exact ⟨h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j <;> simp_all

private theorem plpa_zvec_not_mem_V1 (c : K) :
    (![0, 1, c] : Fin 3 → K) ∉ Vsub (K := K) 3 1 := by
  intro h
  have h1 : (![0, 1, c] : Fin 3 → K) 1 = 0 := (plpa_mem_Vsub_one _).mp h |>.1
  simpa using h1

private theorem plpa_dir_eq_imp {u : Fin 3 → K} {c : K}
    (h : Submodule.span K {u} ⊔ Vsub (K := K) 3 1 =
      Submodule.span K {(![0, 1, c] : Fin 3 → K)} ⊔ Vsub (K := K) 3 1) :
    c * u 1 = u 2 := by
  have hz : (![0, 1, c] : Fin 3 → K) ∈
      Submodule.span K {u} ⊔ Vsub (K := K) 3 1 := by
    rw [h]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hz
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨hw1, hw2⟩ := (plpa_mem_Vsub_one w).mp hw
  have h1 : b * u 1 = 1 := by
    have := congrFun haw 1
    simpa [hw1, Pi.add_apply, Pi.smul_apply] using this
  have h2 : b * u 2 = c := by
    have := congrFun haw 2
    simpa [hw2, Pi.add_apply, Pi.smul_apply] using this
  calc c * u 1 = (b * u 2) * u 1 := by rw [h2]
    _ = (b * u 1) * u 2 := by ring
    _ = u 2 := by rw [h1, one_mul]

private theorem plpa_dir_ne_of_mul_ne {u : Fin 3 → K} {c : K} (hcu : c * u 1 ≠ u 2) :
    Submodule.span K {u} ⊔ Vsub (K := K) 3 1 ≠
      Submodule.span K {(![0, 1, c] : Fin 3 → K)} ⊔ Vsub (K := K) 3 1 :=
  fun h => hcu (plpa_dir_eq_imp h)

private theorem plpa_sgS_zdir_ne (hK : Nat.card K = (2 ^ f) ^ 2) {c : K}
    (hc : sg K f c ≠ c) :
    sgS K f 3 (Submodule.span K {(![0, 1, c] : Fin 3 → K)} ⊔ Vsub (K := K) 3 1) ≠
      Submodule.span K {(![0, 1, c] : Fin 3 → K)} ⊔ Vsub (K := K) 3 1 := by
  rw [sgS_sup hK, sgS_Vsub, sgS_span_singleton hK]
  have hsz : sgv K f 3 (![0, 1, c] : Fin 3 → K) = ![0, 1, sg K f c] := by
    ext i
    fin_cases i <;> simp [sgv_apply]
  rw [hsz]
  intro h
  have h' := plpa_dir_eq_imp (u := (![0, 1, sg K f c] : Fin 3 → K)) (c := c) h
  simp at h'
  exact hc h'.symm

private theorem plpa_mul_ne_of_ne_inv {u : Fin 3 → K} (hu1 : u 1 ≠ 0) {c : K}
    (h : c ≠ u 2 * (u 1)⁻¹) : c * u 1 ≠ u 2 := by
  intro hcu
  apply h
  calc c = c * u 1 * (u 1)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu1, mul_one]
    _ = u 2 * (u 1)⁻¹ := by rw [hcu]

private theorem plpa_mul_ne_of_eq_zero {u : Fin 3 → K} (hu1 : u 1 = 0) (hu2 : u 2 ≠ 0)
    (c : K) : c * u 1 ≠ u 2 := by
  rw [hu1, mul_zero]
  exact fun h => hu2 h.symm

private theorem plpa_exists_moved_avoid_mul (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (u v : Fin 3 → K) (hu : u ∉ Vsub (K := K) 3 1)
    (hv : v ∉ Vsub (K := K) 3 1) :
    ∃ c : K, sg K f c ≠ c ∧ c * u 1 ≠ u 2 ∧ c * v 1 ≠ v 2 := by
  classical
  by_cases hu1 : u 1 = 0
  · have hu2 : u 2 ≠ 0 := by
      intro h2
      exact hu ((plpa_mem_Vsub_one u).mpr ⟨hu1, h2⟩)
    by_cases hv1 : v 1 = 0
    · have hv2 : v 2 ≠ 0 := by
        intro h2
        exact hv ((plpa_mem_Vsub_one v).mpr ⟨hv1, h2⟩)
      obtain ⟨c, hc, -, -⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq (0 : K) (0 : K)
      exact ⟨c, hc, plpa_mul_ne_of_eq_zero hu1 hu2 c, plpa_mul_ne_of_eq_zero hv1 hv2 c⟩
    · obtain ⟨c, hc, -, hc2⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq
        (0 : K) (v 2 * (v 1)⁻¹)
      exact ⟨c, hc, plpa_mul_ne_of_eq_zero hu1 hu2 c, plpa_mul_ne_of_ne_inv hv1 hc2⟩
  · by_cases hv1 : v 1 = 0
    · have hv2 : v 2 ≠ 0 := by
        intro h2
        exact hv ((plpa_mem_Vsub_one v).mpr ⟨hv1, h2⟩)
      obtain ⟨c, hc, hc1, -⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq
        (u 2 * (u 1)⁻¹) (0 : K)
      exact ⟨c, hc, plpa_mul_ne_of_ne_inv hu1 hc1, plpa_mul_ne_of_eq_zero hv1 hv2 c⟩
    · obtain ⟨c, hc, hc1, hc2⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq
        (u 2 * (u 1)⁻¹) (v 2 * (v 1)⁻¹)
      exact ⟨c, hc, plpa_mul_ne_of_ne_inv hu1 hc1, plpa_mul_ne_of_ne_inv hv1 hc2⟩

private theorem plpa_span_zvec_inf_Vsub (c : K) :
    Submodule.span K {(![0, 1, c] : Fin 3 → K)} ⊓ Vsub (K := K) 3 1 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvspan, hvV⟩ := hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvspan
  have h1 : (a • (![0, 1, c] : Fin 3 → K)) 1 = 0 := (plpa_mem_Vsub_one _).mp hvV |>.1
  have ha : a = 0 := by simpa using h1
  rw [ha, zero_smul]

private theorem plpa_finrank_sup_one {p z : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hz : finrank K z = 1) (hne : z ≠ p) :
    finrank K ↥(p ⊔ z) = 2 := by
  classical
  have hdisj : p ⊓ z = ⊥ := by
    by_contra h
    have h0 : finrank K ↥(p ⊓ z) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(p ⊓ z) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : p ⊓ z ≤ p)
      rwa [hp] at this
    have h1 : finrank K ↥(p ⊓ z) = 1 := by omega
    have e1 : p ⊓ z = p := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hp])
    have e2 : p ⊓ z = z := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hz])
    exact hne (e2.symm.trans e1)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq p z
  rw [hdisj, finrank_bot, add_zero, hp, hz] at hsum
  exact hsum

private theorem plpa_finrank_dir {p : Submodule K (Fin 3 → K)} (hp : finrank K p = 1)
    (hpV : p ⊓ Vsub (K := K) 3 1 = ⊥) :
    finrank K ↥(p ⊔ Vsub (K := K) 3 1) = 2 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq p (Vsub (K := K) 3 1)
  rw [hpV, finrank_bot, add_zero, hp,
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
  omega

private theorem plpa_sup_Vsub_eq_top {m : Submodule K (Fin 3 → K)} (hm : finrank K m = 2)
    (hmV : m ⊓ Vsub (K := K) 3 1 = ⊥) : m ⊔ Vsub (K := K) 3 1 = ⊤ := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq m (Vsub (K := K) 3 1)
  rw [hmV, finrank_bot, add_zero, hm,
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Module.finrank_fin_fun K]
  exact hsum

private theorem plpa_inf_Vsub_one_eq_bot_of_not_le {m : Submodule K (Fin 3 → K)}
    (h : ¬ Vsub (K := K) 3 1 ≤ m) : m ⊓ Vsub (K := K) 3 1 = ⊥ := by
  classical
  rw [← Submodule.finrank_eq_zero]
  have hle1 : finrank K ↥(m ⊓ Vsub (K := K) 3 1) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_right : m ⊓ Vsub (K := K) 3 1 ≤
      Vsub (K := K) 3 1)
    rwa [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at this
  by_contra hne
  have h1 : finrank K ↥(m ⊓ Vsub (K := K) 3 1) = 1 := by
    have hpos : 0 < finrank K ↥(m ⊓ Vsub (K := K) 3 1) := Nat.pos_of_ne_zero hne
    omega
  have hEq : m ⊓ Vsub (K := K) 3 1 = Vsub (K := K) 3 1 :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right
      (by rw [h1, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)])
  exact h (by rw [← hEq]; exact inf_le_left)

private theorem plpa_inf_sgS_eq_of_ne (hK : Nat.card K = (2 ^ f) ^ 2)
    {p : Submodule K (Fin 3 → K)} (hp : finrank K p = 1)
    (hpV : p ⊓ Vsub (K := K) 3 1 = ⊥)
    (hne : sgS K f 3 (p ⊔ Vsub (K := K) 3 1) ≠ p ⊔ Vsub (K := K) 3 1) :
    (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) =
      Vsub (K := K) 3 1 := by
  have hDfin : finrank K ↥(p ⊔ Vsub (K := K) 3 1) = 2 := plpa_finrank_dir hp hpV
  have hD'fin : finrank K ↥(sgS K f 3 (p ⊔ Vsub (K := K) 3 1)) = 2 := by
    rw [finrank_sgS hK, hDfin]
  have hV1le : Vsub (K := K) 3 1 ≤ p ⊔ Vsub (K := K) 3 1 := le_sup_right
  have hV1le' : Vsub (K := K) 3 1 ≤ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) := by
    have h : sgS K f 3 (Vsub (K := K) 3 1) ≤ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) :=
      sgS_mono (le_sup_right : Vsub (K := K) 3 1 ≤ p ⊔ Vsub (K := K) 3 1)
    rwa [sgS_Vsub] at h
  have hJle : (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) ≤
      p ⊔ Vsub (K := K) 3 1 := inf_le_left
  have hJle2 : finrank K ↥((p ⊔ Vsub (K := K) 3 1) ⊓
      sgS K f 3 (p ⊔ Vsub (K := K) 3 1)) ≤ 2 := by
    have := Submodule.finrank_mono hJle
    rwa [hDfin] at this
  have hJne : finrank K ↥((p ⊔ Vsub (K := K) 3 1) ⊓
      sgS K f 3 (p ⊔ Vsub (K := K) 3 1)) ≠ 2 := by
    intro h2
    have hJD : (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) =
        p ⊔ Vsub (K := K) 3 1 :=
      Submodule.eq_of_le_of_finrank_eq hJle (by rw [h2, hDfin])
    have hle : p ⊔ Vsub (K := K) 3 1 ≤ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) :=
      calc p ⊔ Vsub (K := K) 3 1 =
          (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) := hJD.symm
        _ ≤ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) := inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hD'fin, hDfin])).symm
  have hJge : 1 ≤ finrank K ↥((p ⊔ Vsub (K := K) 3 1) ⊓
      sgS K f 3 (p ⊔ Vsub (K := K) 3 1)) := by
    have := Submodule.finrank_mono (le_inf hV1le hV1le')
    rwa [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at this
  have hJfin : finrank K ↥((p ⊔ Vsub (K := K) 3 1) ⊓
      sgS K f 3 (p ⊔ Vsub (K := K) 3 1)) = 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq (le_inf hV1le hV1le')
    (by rw [hJfin, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)])).symm

private theorem plpa_inf_sgS_eq_iff (hK : Nat.card K = (2 ^ f) ^ 2)
    {p : Submodule K (Fin 3 → K)} (hp : finrank K p = 1)
    (hpV : p ⊓ Vsub (K := K) 3 1 = ⊥) :
    (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) =
        Vsub (K := K) 3 1 ↔
      sgS K f 3 (p ⊔ Vsub (K := K) 3 1) ≠ p ⊔ Vsub (K := K) 3 1 := by
  constructor
  · intro hint heq
    have hD : (p ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (p ⊔ Vsub (K := K) 3 1) =
        p ⊔ Vsub (K := K) 3 1 := by
      rw [heq, inf_idem]
    have hV : Vsub (K := K) 3 1 = p ⊔ Vsub (K := K) 3 1 := hint.symm.trans hD
    have h2 : finrank K ↥(Vsub (K := K) 3 1) =
        finrank K ↥(p ⊔ Vsub (K := K) 3 1) :=
      congrArg (fun s : Submodule K (Fin 3 → K) => finrank K ↥s) hV
    rw [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num),
      plpa_finrank_dir hp hpV] at h2
    omega
  · intro hne
    exact plpa_inf_sgS_eq_of_ne hK hp hpV hne

private theorem plpa_blockU_one (E : ℕ → Submodule K (Fin 3 → K)) (r : ℕ) :
    blockU K 3 [0, 1, 3] E 1 r = E r ⊔ Vsub (K := K) 3 1 := by
  show (E (3 - [0, 1, 3].getD (1 + 1) 0 + r) ⊓ Vsub 3 ([0, 1, 3].getD (1 + 1) 0)) ⊔
      Vsub 3 ([0, 1, 3].getD 1 0) = E r ⊔ Vsub 3 1
  rw [show [0, 1, 3].getD (1 + 1) 0 = 3 by decide,
    show [0, 1, 3].getD 1 0 = 1 by decide, Vsub_self, inf_top_eq,
    show 3 - 3 + r = r by omega]

private theorem plpa_mem_genSet_iff (x : FlagK K 3) :
    x ∈ genSet K f 3 [0, 1, 3] [] ↔
      x.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ ∧ x.E 2 ⊓ Vsub (K := K) 3 1 = ⊥ ∧
        (x.E 1 ⊔ Vsub (K := K) 3 1) ⊓ sgS K f 3 (x.E 1 ⊔ Vsub (K := K) 3 1) =
          Vsub (K := K) 3 1 := by
  have hle : ∀ i, i < [0, 1, 3].length → [0, 1, 3].getD i 0 ≤ 3 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < [0, 1, 3].length →
      [0, 1, 3].getD i 0 ≤ [0, 1, 3].getD (i + 1) 0 := by
    intro i hi
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i <;> decide
  constructor
  · rintro ⟨hfar, hok⟩
    refine ⟨?_, ?_, ?_⟩
    · exact ((mem_farSet_iff (K := K) hle).mp hfar 1 (by decide) 1 (by decide)).1
        (by decide)
    · exact ((mem_farSet_iff (K := K) hle).mp hfar 1 (by decide) 2 (by decide)).1
        (by decide)
    · have h1 := (blockOK_iff_of_far f hle hmono hfar (i := 1) (by decide)).mp
        (hok 1 (by decide))
      have h1' := h1 1 (by norm_num) (by decide)
      simpa [plpa_blockU_one, show (3 - 1 - 1 : ℕ) = 1 by norm_num,
        show [0, 1, 3].getD 1 0 = 1 by decide] using h1'
  · rintro ⟨h1, h2, h3⟩
    have hfar : x ∈ farSet 3 [0, 1, 3] := by
      refine (mem_farSet_iff (K := K) hle).mpr ?_
      intro i hi j hj
      have hi3 : i < 3 := by simpa using hi
      interval_cases i
      · rw [show [0, 1, 3].getD 0 0 = 0 by decide]
        constructor
        · intro _
          rw [Vsub_zero, inf_bot_eq]
        · intro hj3
          have hj' : j = 3 := by omega
          subst hj'
          rw [Vsub_zero, sup_bot_eq, x.top 3 (by norm_num)]
      · rw [show [0, 1, 3].getD 1 0 = 1 by decide]
        constructor
        · intro hjc
          have hj2 : j ≤ 2 := by omega
          interval_cases j
          · rw [FlagK.E_zero, bot_inf_eq]
          · exact h1
          · exact h2
        · intro hnjc
          have hj2 : 2 ≤ j := by omega
          interval_cases j
          · exact plpa_sup_Vsub_eq_top (x.dim 2 (by norm_num)) h2
          · rw [x.top 3 (by norm_num), top_sup_eq]
      · rw [show [0, 1, 3].getD 2 0 = 3 by decide]
        constructor
        · intro hjc
          have hj0 : j = 0 := by omega
          subst hj0
          rw [FlagK.E_zero, Vsub_self, inf_top_eq]
        · intro _
          rw [Vsub_self, sup_top_eq]
    refine ⟨hfar, ?_⟩
    intro i hi
    have hi1 : i = 0 ∨ i = 1 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    rcases hi1 with rfl | rfl
    · exact blockOK_of_size_one f hle hmono hfar (i := 0) (by decide) (by decide)
    · refine (blockOK_iff_of_far f hle hmono hfar (i := 1) (by decide)).mpr ?_
      intro r hr0 hrm
      have hr : r = 1 := by
        have : r < 3 - 1 := by simpa using hrm
        omega
      subst hr
      simpa [plpa_blockU_one, show (3 - 1 - 1 : ℕ) = 1 by norm_num,
        show [0, 1, 3].getD 1 0 = 1 by decide] using h3

private theorem plpa_hasFl (hK : Nat.card K = (2 ^ f) ^ 2) {p m : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hm : finrank K m = 2) (hpm : p ≤ m)
    (hpV : p ⊓ Vsub (K := K) 3 1 = ⊥) (hmV : m ⊓ Vsub (K := K) 3 1 = ⊥)
    (hpd : sgS K f 3 (p ⊔ Vsub (K := K) 3 1) ≠ p ⊔ Vsub (K := K) 3 1) :
    Plane.HasFl (genSet K f 3 [0, 1, 3] []) p m := by
  refine Plane.hasFl_ofChain hp hm hpm ?_
  rw [plpa_mem_genSet_iff, Plane.ofChain_E_one p m hp hm hpm,
    Plane.ofChain_E_two p m hp hm hpm]
  exact ⟨hpV, hmV, (plpa_inf_sgS_eq_iff hK hp hpV).mpr hpd⟩

private theorem plpa_moved_nbr (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {x y : FlagK K 3} (hpV : x.E 1 ⊓ Vsub (K := K) 3 1 = ⊥)
    (hpd : sgS K f 3 (x.E 1 ⊔ Vsub (K := K) 3 1) ≠ x.E 1 ⊔ Vsub (K := K) 3 1)
    (hpV' : y.E 1 ⊓ Vsub (K := K) 3 1 = ⊥)
    (hpd' : sgS K f 3 (y.E 1 ⊔ Vsub (K := K) 3 1) ≠ y.E 1 ⊔ Vsub (K := K) 3 1) :
    ∃ z m m' : Submodule K (Fin 3 → K),
      finrank K z = 1 ∧ z ⊓ Vsub (K := K) 3 1 = ⊥ ∧
      sgS K f 3 (z ⊔ Vsub (K := K) 3 1) ≠ z ⊔ Vsub (K := K) 3 1 ∧
      finrank K m = 2 ∧ m ⊓ Vsub (K := K) 3 1 = ⊥ ∧ x.E 1 ≤ m ∧ z ≤ m ∧
      finrank K m' = 2 ∧ m' ⊓ Vsub (K := K) 3 1 = ⊥ ∧ y.E 1 ≤ m' ∧ z ≤ m' := by
  classical
  have hp : finrank K (x.E 1) = 1 := Plane.finrank_E_one x
  have hp' : finrank K (y.E 1) = 1 := Plane.finrank_E_one y
  obtain ⟨u, hu_mem, hu0⟩ : ∃ u : Fin 3 → K, u ∈ x.E 1 ∧ u ≠ 0 := by
    have hpne : x.E 1 ≠ ⊥ := by
      intro hbot
      have h0 : finrank K (x.E 1) = 0 := by rw [hbot]; simp
      rw [hp] at h0
      norm_num at h0
    exact (Submodule.ne_bot_iff (x.E 1)).mp hpne
  obtain ⟨u', hu'_mem, hu'0⟩ : ∃ u' : Fin 3 → K, u' ∈ y.E 1 ∧ u' ≠ 0 := by
    have hpne : y.E 1 ≠ ⊥ := by
      intro hbot
      have h0 : finrank K (y.E 1) = 0 := by rw [hbot]; simp
      rw [hp'] at h0
      norm_num at h0
    exact (Submodule.ne_bot_iff (y.E 1)).mp hpne
  have hpu : x.E 1 = Submodule.span K {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp hu_mem hu0
  have hp'u : y.E 1 = Submodule.span K {u'} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp' hu'_mem hu'0
  have huV : u ∉ Vsub (K := K) 3 1 := by
    intro hmem
    have : u ∈ x.E 1 ⊓ Vsub (K := K) 3 1 := ⟨hu_mem, hmem⟩
    rw [hpV] at this
    exact hu0 ((Submodule.mem_bot K).mp this)
  have hu'V : u' ∉ Vsub (K := K) 3 1 := by
    intro hmem
    have : u' ∈ y.E 1 ⊓ Vsub (K := K) 3 1 := ⟨hu'_mem, hmem⟩
    rw [hpV'] at this
    exact hu'0 ((Submodule.mem_bot K).mp this)
  obtain ⟨c, hc_sg, hcu, hcu'⟩ := plpa_exists_moved_avoid_mul hK hq u u' huV hu'V
  set z : Submodule K (Fin 3 → K) :=
    Submodule.span K {(![0, 1, c] : Fin 3 → K)} with hzdef
  have hz1 : finrank K z = 1 := by
    rw [hzdef]
    exact finrank_span_singleton (fun hzero => by
      have h1 := congrFun hzero (1 : Fin 3)
      simp at h1)
  have hzV : z ⊓ Vsub (K := K) 3 1 = ⊥ := by
    rw [hzdef]
    exact plpa_span_zvec_inf_Vsub c
  have hzd : sgS K f 3 (z ⊔ Vsub (K := K) 3 1) ≠ z ⊔ Vsub (K := K) 3 1 := by
    rw [hzdef]
    exact plpa_sgS_zdir_ne hK hc_sg
  have hzdir : z ⊔ Vsub (K := K) 3 1 ≠ x.E 1 ⊔ Vsub (K := K) 3 1 := by
    rw [hpu, hzdef]
    exact (plpa_dir_ne_of_mul_ne hcu).symm
  have hzdir' : z ⊔ Vsub (K := K) 3 1 ≠ y.E 1 ⊔ Vsub (K := K) 3 1 := by
    rw [hp'u, hzdef]
    exact (plpa_dir_ne_of_mul_ne hcu').symm
  have hzx : z ≠ x.E 1 := fun h => hzdir (by rw [h])
  have hzy : z ≠ y.E 1 := fun h => hzdir' (by rw [h])
  have hm : finrank K ↥(x.E 1 ⊔ z) = 2 :=
    plpa_finrank_sup_one (p := x.E 1) (z := z) hp hz1 hzx
  have hmV : (x.E 1 ⊔ z) ⊓ Vsub (K := K) 3 1 = ⊥ := by
    apply plpa_inf_Vsub_one_eq_bot_of_not_le
    intro hle
    have h1 : x.E 1 ⊔ Vsub (K := K) 3 1 = x.E 1 ⊔ z :=
      Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hle)
        (by rw [plpa_finrank_dir hp hpV, hm])
    have h2 : z ⊔ Vsub (K := K) 3 1 ≤ x.E 1 ⊔ z := sup_le le_sup_right hle
    have h3 : z ⊔ Vsub (K := K) 3 1 = x.E 1 ⊔ z :=
      Submodule.eq_of_le_of_finrank_eq h2 (by rw [plpa_finrank_dir hz1 hzV, hm])
    exact hzdir (h3.trans h1.symm)
  have hm' : finrank K ↥(y.E 1 ⊔ z) = 2 :=
    plpa_finrank_sup_one (p := y.E 1) (z := z) hp' hz1 hzy
  have hm'V : (y.E 1 ⊔ z) ⊓ Vsub (K := K) 3 1 = ⊥ := by
    apply plpa_inf_Vsub_one_eq_bot_of_not_le
    intro hle
    have h1 : y.E 1 ⊔ Vsub (K := K) 3 1 = y.E 1 ⊔ z :=
      Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hle)
        (by rw [plpa_finrank_dir hp' hpV', hm'])
    have h2 : z ⊔ Vsub (K := K) 3 1 ≤ y.E 1 ⊔ z := sup_le le_sup_right hle
    have h3 : z ⊔ Vsub (K := K) 3 1 = y.E 1 ⊔ z :=
      Submodule.eq_of_le_of_finrank_eq h2 (by rw [plpa_finrank_dir hz1 hzV, hm'])
    exact hzdir' (h3.trans h1.symm)
  exact ⟨z, x.E 1 ⊔ z, y.E 1 ⊔ z, hz1, hzV, hzd, hm, hmV, le_sup_left, le_sup_right,
    hm', hm'V, le_sup_left, le_sup_right⟩

end Helpers

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a2panel_connected (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 2).restrict (genSet K f 3 [0, 1, 3] [])).Connected := by
  classical
  refine Plane.connected_of_common_nbr _ ?_
  intro x hx y hy
  have hxr := (plpa_mem_genSet_iff x).mp hx
  have hyr := (plpa_mem_genSet_iff y).mp hy
  have hp : finrank K (x.E 1) = 1 := Plane.finrank_E_one x
  have hp' : finrank K (y.E 1) = 1 := Plane.finrank_E_one y
  have hpV : x.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ := hxr.1
  have hpV' : y.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ := hyr.1
  have hpd : sgS K f 3 (x.E 1 ⊔ Vsub (K := K) 3 1) ≠
      x.E 1 ⊔ Vsub (K := K) 3 1 :=
    (plpa_inf_sgS_eq_iff hK hp hpV).mp hxr.2.2
  have hpd' : sgS K f 3 (y.E 1 ⊔ Vsub (K := K) 3 1) ≠
      y.E 1 ⊔ Vsub (K := K) 3 1 :=
    (plpa_inf_sgS_eq_iff hK hp' hpV').mp hyr.2.2
  obtain ⟨z, m, m', hz1, hzV, hzd, hm, hmV, hxm, hzm, hm', hm'V, hym', hzm'⟩ :=
    plpa_moved_nbr hK hq hpV hpd hpV' hpd'
  exact ⟨z, m, m', plpa_hasFl hK hp hm hxm hpV hmV hpd,
    plpa_hasFl hK hz1 hm hzm hzV hmV hzd,
    plpa_hasFl hK hz1 hm' hzm' hzV hm'V hzd,
    plpa_hasFl hK hp' hm' hym' hpV' hm'V hpd'⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
