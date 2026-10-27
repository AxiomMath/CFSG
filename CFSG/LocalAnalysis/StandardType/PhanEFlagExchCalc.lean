module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]


@[expose] noncomputable def jShift (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (v : Fin 4 → K) : Fin 4 → K :=
  ![0, 0, sg K f (v 0), sg K f (v 1)]

@[expose] noncomputable def jShiftInv (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (v : Fin 4 → K) : Fin 4 → K :=
  ![sg K f (v 2), sg K f (v 3), 0, 0]

@[expose] noncomputable def q2cFX_JInv (f : ℕ) (H : Submodule K (Fin 4 → K)) :
    Submodule K (Fin 4 → K) :=
  Submodule.span K (jShiftInv K f '' (H : Set (Fin 4 → K)))

@[expose] noncomputable def q2cFX_Phi (f : ℕ) (L : Submodule K (Fin 4 → K)) :
    Submodule K (Fin 4 → K) :=
  Vsub (K := K) 4 2 ⊔ Submodule.span K (jShift K f '' (L : Set (Fin 4 → K)))

private theorem q2cFX_jShift_zero : jShift K f (0 : Fin 4 → K) = 0 := by
  funext i; fin_cases i <;> simp [jShift]

private theorem q2cFX_jShiftInv_zero : jShiftInv K f (0 : Fin 4 → K) = 0 := by
  funext i; fin_cases i <;> simp [jShiftInv]

private theorem q2cFX_jShift_add (v w : Fin 4 → K) :
    jShift K f (v + w) = jShift K f v + jShift K f w := by
  funext i; fin_cases i <;> simp [jShift, map_add]

private theorem q2cFX_jShiftInv_add (v w : Fin 4 → K) :
    jShiftInv K f (v + w) = jShiftInv K f v + jShiftInv K f w := by
  funext i; fin_cases i <;> simp [jShiftInv, map_add]

private theorem q2cFX_jShift_smul (c : K) (v : Fin 4 → K) :
    jShift K f (c • v) = sg K f c • jShift K f v := by
  funext i; fin_cases i <;> simp [jShift, map_mul]

private theorem q2cFX_jShiftInv_smul (c : K) (v : Fin 4 → K) :
    jShiftInv K f (c • v) = sg K f c • jShiftInv K f v := by
  funext i; fin_cases i <;> simp [jShiftInv, map_mul]

private def q2cFX_lift (v : Fin 4 → K) : Fin 4 → K := ![v 0, v 1, 0, 0]

private theorem q2cFX_lift_mem (v : Fin 4 → K) :
    q2cFX_lift v ∈ Vsub (K := K) 4 2 := by
  intro j hj; fin_cases j <;> simp_all [q2cFX_lift]

private theorem q2cFX_lift_add (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin 4 → K) :
    q2cFX_lift v + jShift K f (jShiftInv K f v) = v := by
  funext i; fin_cases i
  · simp [q2cFX_lift, jShift, jShiftInv]
  · simp [q2cFX_lift, jShift, jShiftInv]
  · change (0 : K) + sg K f (sg K f (v 2)) = v 2
    rw [sg_sg hK, zero_add]
  · change (0 : K) + sg K f (sg K f (v 3)) = v 3
    rw [sg_sg hK, zero_add]

private theorem q2cFX_lift_add' (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin 4 → K) :
    jShift K f (jShiftInv K f v) = v - q2cFX_lift v := by
  calc jShift K f (jShiftInv K f v) = q2cFX_lift v + jShift K f (jShiftInv K f v) -
        q2cFX_lift v := by abel
    _ = v - q2cFX_lift v := by rw [q2cFX_lift_add hK v]

private theorem q2cFX_jShiftInv_mem_eq_zero {v : Fin 4 → K}
    (hv : v ∈ Vsub (K := K) 4 2) : jShiftInv K f v = 0 := by
  funext i; fin_cases i
  · simp [jShiftInv, hv 2 (by norm_num)]
  · simp [jShiftInv, hv 3 (by norm_num)]
  · simp [jShiftInv]
  · simp [jShiftInv]

private theorem q2cFX_jShiftInv_jShift (hK : Nat.card K = (2 ^ f) ^ 2) {w : Fin 4 → K}
    (hw : w ∈ Vsub (K := K) 4 2) : jShiftInv K f (jShift K f w) = w := by
  funext i; fin_cases i
  · change sg K f (sg K f (w 0)) = w 0
    rw [sg_sg hK]
  · change sg K f (sg K f (w 1)) = w 1
    rw [sg_sg hK]
  · simp [jShift, jShiftInv, hw 2 (by norm_num)]
  · simp [jShift, jShiftInv, hw 3 (by norm_num)]

private def q2cFX_W : Submodule K (Fin 4 → K) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  add_mem' := by rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩; exact ⟨by simp [ha0, hb0],
    by simp [ha1, hb1]⟩
  zero_mem' := by simp
  smul_mem' := by rintro c a ⟨ha0, ha1⟩; exact ⟨by simp [ha0], by simp [ha1]⟩

private theorem q2cFX_span_jShift_le_W (L : Submodule K (Fin 4 → K)) :
    Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) ≤ q2cFX_W (K := K) := by
  rw [Submodule.span_le]
  rintro v ⟨l, -, rfl⟩
  exact ⟨by simp [jShift], by simp [jShift]⟩

private theorem q2cFX_jShiftInv_mem_Vsub (v : Fin 4 → K) :
    jShiftInv K f v ∈ Vsub (K := K) 4 2 := by
  intro j hj; fin_cases j <;> simp_all [jShiftInv]

theorem q2cFX_span_jShiftInv_le_Vsub (L : Submodule K (Fin 4 → K)) :
    Submodule.span K (jShiftInv K f '' (L : Set (Fin 4 → K))) ≤ Vsub (K := K) 4 2 := by
  rw [Submodule.span_le]
  rintro v ⟨l, -, rfl⟩
  exact q2cFX_jShiftInv_mem_Vsub l

private def q2cFX_preInv (L : Submodule K (Fin 4 → K)) : Submodule K (Fin 4 → K) where
  carrier := {b | jShiftInv K f b ∈ L}
  add_mem' := by
    intro a b ha hb
    show jShiftInv K f (a + b) ∈ L
    rw [q2cFX_jShiftInv_add]
    exact L.add_mem ha hb
  zero_mem' := by
    show jShiftInv K f 0 ∈ L
    rw [q2cFX_jShiftInv_zero]
    exact L.zero_mem
  smul_mem' := by
    intro c b hb
    show jShiftInv K f (c • b) ∈ L
    rw [q2cFX_jShiftInv_smul]
    exact L.smul_mem (sg K f c) hb

private def q2cFX_preFwd (H : Submodule K (Fin 4 → K)) : Submodule K (Fin 4 → K) where
  carrier := {b | jShift K f b ∈ H}
  add_mem' := by
    intro a b ha hb
    show jShift K f (a + b) ∈ H
    rw [q2cFX_jShift_add]
    exact H.add_mem ha hb
  zero_mem' := by
    show jShift K f 0 ∈ H
    rw [q2cFX_jShift_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c b hb
    show jShift K f (c • b) ∈ H
    rw [q2cFX_jShift_smul]
    exact H.smul_mem (sg K f c) hb

private theorem q2cFX_preInv_Vsub (L : Submodule K (Fin 4 → K)) :
    Vsub (K := K) 4 2 ≤ q2cFX_preInv (K := K) (f := f) L := by
  intro a ha
  show jShiftInv K f a ∈ L
  rw [q2cFX_jShiftInv_mem_eq_zero ha]
  exact L.zero_mem

private theorem q2cFX_span_jShift_le_preInv (hK : Nat.card K = (2 ^ f) ^ 2)
    {L : Submodule K (Fin 4 → K)} (hL : L ≤ Vsub (K := K) 4 2) :
    Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) ≤
      q2cFX_preInv (K := K) (f := f) L := by
  rw [Submodule.span_le]
  rintro v ⟨w, hw, rfl⟩
  show jShiftInv K f (jShift K f w) ∈ L
  rw [q2cFX_jShiftInv_jShift hK (hL hw)]
  exact hw

private theorem q2cFX_span_jShiftInv_le_preFwd (hK : Nat.card K = (2 ^ f) ^ 2)
    {H : Submodule K (Fin 4 → K)} (hH : Vsub (K := K) 4 2 ≤ H) :
    q2cFX_JInv f H ≤ q2cFX_preFwd (K := K) (f := f) H := by
  rw [q2cFX_JInv, Submodule.span_le]
  rintro v ⟨h, hh, rfl⟩
  show jShift K f (jShiftInv K f h) ∈ H
  rw [q2cFX_lift_add' hK h]
  exact H.sub_mem hh (hH (q2cFX_lift_mem h))

theorem q2cFX_mem_sup_jShift_iff (hK : Nat.card K = (2 ^ f) ^ 2)
    {L : Submodule K (Fin 4 → K)} (hL : L ≤ Vsub (K := K) 4 2) (v : Fin 4 → K) :
    v ∈ q2cFX_Phi f L ↔ jShiftInv K f v ∈ L := by
  have hsplit : q2cFX_Phi f L = Vsub (K := K) 4 2 ⊔
      Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) := rfl
  rw [hsplit]
  constructor
  · intro hv
    have hsup : Vsub (K := K) 4 2 ⊔
        Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) ≤
          q2cFX_preInv (K := K) (f := f) L :=
      sup_le (q2cFX_preInv_Vsub L) (q2cFX_span_jShift_le_preInv hK hL)
    exact hsup hv
  · intro hv
    have hmem : jShift K f (jShiftInv K f v) ∈
        Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) :=
      Submodule.subset_span ⟨jShiftInv K f v, hv, rfl⟩
    have hsum : q2cFX_lift v + jShift K f (jShiftInv K f v) ∈
        Vsub (K := K) 4 2 ⊔ Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) :=
      Submodule.mem_sup.mpr ⟨q2cFX_lift v, q2cFX_lift_mem v,
        jShift K f (jShiftInv K f v), hmem, rfl⟩
    rwa [q2cFX_lift_add hK v] at hsum

theorem q2cFX_jInv_image_phi (hK : Nat.card K = (2 ^ f) ^ 2)
    {L : Submodule K (Fin 4 → K)} (hL : L ≤ Vsub (K := K) 4 2) :
    q2cFX_JInv f (q2cFX_Phi f L) = L := by
  unfold q2cFX_JInv q2cFX_Phi
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    exact (q2cFX_mem_sup_jShift_iff hK hL w).mp hw
  · intro w hw
    refine Submodule.subset_span ⟨jShift K f w, ?_, q2cFX_jShiftInv_jShift hK (hL hw)⟩
    exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, jShift K f w,
      Submodule.subset_span ⟨w, hw, rfl⟩, zero_add _⟩

theorem q2cFX_phi_jInv_image (hK : Nat.card K = (2 ^ f) ^ 2)
    {H : Submodule K (Fin 4 → K)} (hH : Vsub (K := K) 4 2 ≤ H) :
    q2cFX_Phi f (q2cFX_JInv f H) = H := by
  unfold q2cFX_Phi q2cFX_JInv
  apply le_antisymm
  · refine sup_le hH ?_
    rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    exact (q2cFX_span_jShiftInv_le_preFwd hK hH) hw
  · intro h hh
    have hdecomp := q2cFX_lift_add hK h
    rw [← hdecomp]
    refine Submodule.mem_sup.mpr ⟨q2cFX_lift h, q2cFX_lift_mem h,
      jShift K f (jShiftInv K f h), Submodule.subset_span
        ⟨jShiftInv K f h, Submodule.subset_span ⟨h, hh, rfl⟩, rfl⟩, rfl⟩

private theorem q2cFX_finrank_span_jShift (hK : Nat.card K = (2 ^ f) ^ 2)
    {L : Submodule K (Fin 4 → K)} (hL : L ≤ Vsub (K := K) 4 2)
    (hL1 : finrank K L = 1) :
    finrank K (Submodule.span K (jShift K f '' (L : Set (Fin 4 → K)))) = 1 := by
  have hne : L ≠ ⊥ := by
    intro hb
    have hpos : 0 < finrank K L := by omega
    rw [hb, finrank_bot] at hpos
    omega
  obtain ⟨p, hpL, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hLspan : L = Submodule.span K {p} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hL1 hpL hp0
  have hspan : Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) =
      Submodule.span K {jShift K f p} := by
    rw [hLspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨l, hl, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hl
      rw [← hc, q2cFX_jShift_smul]
      exact Submodule.mem_span_singleton.mpr ⟨sg K f c, rfl⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨p, Submodule.mem_span_singleton_self p, rfl⟩
  have hjp : jShift K f p ≠ 0 := by
    intro hjp
    have hinv := q2cFX_jShiftInv_jShift hK (hL hpL)
    rw [hjp, q2cFX_jShiftInv_zero] at hinv
    exact hp0 hinv.symm
  rw [hspan, finrank_span_singleton hjp]

theorem q2cFX_finrank_Phi (hK : Nat.card K = (2 ^ f) ^ 2)
    {L : Submodule K (Fin 4 → K)} (hL : L ≤ Vsub (K := K) 4 2)
    (hL1 : finrank K L = 1) : finrank K (q2cFX_Phi f L) = 3 := by
  have hdisj : Vsub (K := K) 4 2 ⊓
      Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvW⟩ := Submodule.mem_inf.mp hv
    have hvW' := q2cFX_span_jShift_le_W (K := K) (f := f) L hvW
    funext i; fin_cases i
    · exact hvW'.1
    · exact hvW'.2
    · exact hvV 2 (by norm_num)
    · exact hvV 3 (by norm_num)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) 4 2)
    (Submodule.span K (jShift K f '' (L : Set (Fin 4 → K))))
  rw [hdisj, finrank_bot, finrank_Vsub (K := K) (n := 4) (by norm_num),
    q2cFX_finrank_span_jShift hK hL hL1] at hsup
  rw [q2cFX_Phi]
  omega

@[expose] def q2cFX_e0 : Fin 4 → K := ![1, 0, 0, 0]
@[expose] def q2cFX_e1 : Fin 4 → K := ![0, 1, 0, 0]
private def q2cFX_e2 : Fin 4 → K := ![0, 0, 1, 0]
private def q2cFX_e3 : Fin 4 → K := ![0, 0, 0, 1]

private theorem q2cFX_jShift_e0 : jShift K f q2cFX_e0 = q2cFX_e2 (K := K) := by
  funext i; fin_cases i <;> simp [jShift, q2cFX_e0, q2cFX_e2]

private theorem q2cFX_span_jShift_e0 :
    Submodule.span K (jShift K f '' ((Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) :
        Submodule K (Fin 4 → K)) : Set (Fin 4 → K))) =
      Submodule.span K ({q2cFX_e2} : Set (Fin 4 → K)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (show w ∈ (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) : Submodule K (Fin 4 → K)) from hw)
    rw [← hc, q2cFX_jShift_smul, q2cFX_jShift_e0]
    exact Submodule.mem_span_singleton.mpr ⟨sg K f c, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨q2cFX_e0, Submodule.mem_span_singleton_self _, q2cFX_jShift_e0⟩

private theorem q2cFX_jShift_e1 : jShift K f q2cFX_e1 = q2cFX_e3 (K := K) := by
  funext i; fin_cases i <;> simp [jShift, q2cFX_e1, q2cFX_e3]

private theorem q2cFX_span_jShift_e1 :
    Submodule.span K (jShift K f '' ((Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)) :
        Submodule K (Fin 4 → K)) : Set (Fin 4 → K))) =
      Submodule.span K ({q2cFX_e3} : Set (Fin 4 → K)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (show w ∈ (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)) : Submodule K (Fin 4 → K)) from hw)
    rw [← hc, q2cFX_jShift_smul, q2cFX_jShift_e1]
    exact Submodule.mem_span_singleton.mpr ⟨sg K f c, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨q2cFX_e1, Submodule.mem_span_singleton_self _, q2cFX_jShift_e1⟩

theorem q2cFX_e0_le_Vsub :
    (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) : Submodule K (Fin 4 → K)) <=
      Vsub (K := K) 4 2 :=
  Submodule.span_le.mpr (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    intro j hj; fin_cases j <;> simp_all [q2cFX_e0])

theorem q2cFX_finrank_JInv (hK : Nat.card K = (2 ^ f) ^ 2)
    {H : Submodule K (Fin 4 → K)} (hH : Vsub (K := K) 4 2 ≤ H)
    (hH3 : finrank K H = 3) : finrank K (q2cFX_JInv f H) = 1 := by
  have hex : ∃ q ∈ H, q ∉ Vsub (K := K) 4 2 := by
    by_contra h
    have hle : H ≤ Vsub (K := K) 4 2 := by
      intro q hq
      by_contra hqV
      exact h ⟨q, hq, hqV⟩
    have hmono := Submodule.finrank_mono hle
    rw [hH3, finrank_Vsub (K := K) (n := 4) (by norm_num)] at hmono
    omega
  obtain ⟨q, hqH, hqV⟩ := hex
  have hq0 : q ≠ 0 := by
    intro h0; exact hqV (by rw [h0]; exact Submodule.zero_mem _)
  have hVle : Vsub (K := K) 4 2 ⊔ Submodule.span K {q} = H :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hH (Submodule.span_le.mpr (by
        intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ hqH)))
      (by
        have hdisj : Vsub (K := K) 4 2 ⊓ (Submodule.span K {q}) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro v hv
          obtain ⟨hvV, hvq⟩ := Submodule.mem_inf.mp hv
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvq
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact hc.symm
          · exfalso; apply hqV
            have hcq : q = c⁻¹ • v := by
              rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
            rw [hcq]; exact Submodule.smul_mem _ c⁻¹ hvV
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) 4 2)
          (Submodule.span K {q})
        rw [hdisj, finrank_bot, finrank_Vsub (K := K) (n := 4) (by norm_num),
          finrank_span_singleton hq0] at hsup
        omega)
  have hspan : q2cFX_JInv f H = Submodule.span K {jShiftInv K f q} := by
    rw [q2cFX_JInv, ← hVle]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨h, hh, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
        (show h ∈ (Vsub (K := K) 4 2 ⊔ Submodule.span K {q} :
          Submodule K (Fin 4 → K)) from hh)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
      rw [← hab, q2cFX_jShiftInv_add, q2cFX_jShiftInv_mem_eq_zero ha, zero_add, ← hc,
        q2cFX_jShiftInv_smul]
      exact Submodule.mem_span_singleton.mpr ⟨sg K f c, rfl⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨q, Submodule.mem_sup.mpr
        ⟨0, Submodule.zero_mem _, q, Submodule.mem_span_singleton_self q, zero_add _⟩, rfl⟩
  have hjq : jShiftInv K f q ≠ 0 := by
    intro hjq
    apply hqV
    have hdecomp := q2cFX_lift_add hK q
    rw [hjq, q2cFX_jShift_zero, add_zero] at hdecomp
    rw [← hdecomp]
    exact q2cFX_lift_mem q
  rw [hspan, finrank_span_singleton hjq]

theorem q2cFX_JInv_Phi_e1 (hK : Nat.card K = (2 ^ f) ^ 2) :
    q2cFX_JInv f (q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)))) =
      Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)) :=
  q2cFX_jInv_image_phi hK (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    intro j hj; fin_cases j <;> simp_all [q2cFX_e1])

theorem q2cFX_inf_e0_e1 :
    (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) : Submodule K (Fin 4 → K)) ⊓
      Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨hv0, hv1⟩ := Submodule.mem_inf.mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv0
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hv1
  have hd0 : d = 0 := by
    have h := congrFun (hc.trans hd.symm) 1
    simpa [q2cFX_e0, q2cFX_e1] using h.symm
  rw [← hd, hd0, zero_smul]

theorem q2cFX_Phi_e1_inf_Phi_e0 :
    q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K))) ⊓
        q2cFX_Phi f (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K))) = Vsub (K := K) 4 2 := by
  unfold q2cFX_Phi
  rw [q2cFX_span_jShift_e1, q2cFX_span_jShift_e0]
  apply le_antisymm
  · intro v hv
    obtain ⟨hv13, hv12⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show v ∈ (Vsub (K := K) 4 2 ⊔ Submodule.span K ({q2cFX_e3} : Set (Fin 4 → K)) :
        Submodule K (Fin 4 → K)) from hv13)
    obtain ⟨a', ha', b', hb', ha'b'⟩ := Submodule.mem_sup.mp
      (show v ∈ (Vsub (K := K) 4 2 ⊔ Submodule.span K ({q2cFX_e2} : Set (Fin 4 → K)) :
        Submodule K (Fin 4 → K)) from hv12)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hb'
    have hv2 : v 2 = 0 := by
      rw [← hab, ← hc, Pi.add_apply, Pi.smul_apply, ha 2 (by norm_num)]
      simp [q2cFX_e3]
    have hv3 : v 3 = 0 := by
      rw [← ha'b', ← hd, Pi.add_apply, Pi.smul_apply, ha' 3 (by norm_num)]
      simp [q2cFX_e2]
    intro j hj
    fin_cases j <;> simp_all
  · exact le_inf le_sup_left le_sup_left

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
