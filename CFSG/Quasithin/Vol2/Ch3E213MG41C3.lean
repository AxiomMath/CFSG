module

public import CFSG.Quasithin.Vol2.Ch3E213MG41C2

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.GH74.Uniqueness.Bender

variable {k : Type} [Field k] [CharP k 2]

@[expose] def rootGrp (G₀ : Subgroup (antiSp k)) (v : Fin 4 → k) : Subgroup (antiSp k) where
  carrier := {g | ∃ c ∈ Lam G₀ v, g = trv v c}
  one_mem' := ⟨0, (Lam G₀ v).zero_mem, (trv_zero v).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, (Lam G₀ v).add_mem hc hd, (trv_add v c d).symm⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, trv_inv v c⟩

variable {G₀ : Subgroup (antiSp k)}

theorem trv_mem_rootGrp {v : Fin 4 → k} {c : k} (hc : c ∈ Lam G₀ v) : trv v c ∈ rootGrp G₀ v :=
  ⟨c, hc, rfl⟩

theorem rootGrp_le (v : Fin 4 → k) : rootGrp G₀ v ≤ G₀ := by
  rintro _ ⟨c, hc, rfl⟩
  exact hc

theorem rootGrp_le_fixPerp_left (v w : Fin 4 → k) : rootGrp G₀ v ≤ fixPerp v w := by
  rintro _ ⟨c, -, rfl⟩
  exact trv_mem_fixPerp_left v w c

theorem rootGrp_le_fixPerp_right (v w : Fin 4 → k) : rootGrp G₀ w ≤ fixPerp v w := by
  rintro _ ⟨c, -, rfl⟩
  exact trv_mem_fixPerp_right v w c

theorem card_rootGrp {v : Fin 4 → k} (hv : v ≠ 0) :
    Nat.card (rootGrp G₀ v) = Nat.card (Lam G₀ v) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun c : Lam G₀ v => (⟨trv v c, trv_mem_rootGrp c.2⟩ : rootGrp G₀ v)) ⟨?_, ?_⟩
  · intro c d h
    exact Subtype.ext (trv_param_inj hv (congrArg Subtype.val h))
  · rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

theorem isPGroup_rootGrp (v : Fin 4 → k) : IsPGroup 2 (rootGrp G₀ v) := by
  rintro ⟨_, c, hc, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp [sq, trv_mul_self]

theorem eq_one_of_sq_eq_one {μ : k} (h : μ ^ 2 = 1) : μ = 1 := by
  have h0 : (μ - 1) ^ 2 = 0 := by
    linear_combination h + (1 - μ) * (CharTwo.two_eq_zero : (2 : k) = 0)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)

omit [CharP k 2] in
theorem ne_zero_of_bil_eq_one {v w : Fin 4 → k} (hvw : spBil v w = 1) : v ≠ 0 := by
  rintro rfl
  simp at hvw

theorem card_lam_eq [Finite k] {v w : Fin 4 → k}
    (hvw : spBil v w = 1) {H : Subgroup (antiSp k)} (hHle : H ≤ fixPerp v w) (hHG : H ≤ G₀)
    (hX : rootGrp G₀ v ≤ H) {c₀ : k} (hc₀ : c₀ ≠ 0) (hc₀L : c₀ ∈ Lam G₀ v) {m : ℕ}
    (hB : BenderType H m 1 1) : Nat.card (Lam G₀ v) = 2 ^ m := by
  have hv : v ≠ 0 := ne_zero_of_bil_eq_one hvw
  have hwv := bil_wv hvw
  set X := (rootGrp G₀ v).subgroupOf H with hXdef
  have hXp : IsPGroup 2 X := (isPGroup_rootGrp v).comap_of_injective H.subtype
    Subtype.coe_injective
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  obtain ⟨hScard, hScomm⟩ := benderType_sylow hB S
  have ht : (⟨trv v c₀, hX (trv_mem_rootGrp hc₀L)⟩ : H) ∈ X := by
    rw [hXdef, Subgroup.mem_subgroupOf]
    exact trv_mem_rootGrp hc₀L
  have hSX : (S : Subgroup H) ≤ X := by
    intro s hs
    have hcomm : (s : antiSp k) * trv v c₀ = trv v c₀ * s :=
      congrArg Subtype.val (hScomm s hs _ (hXS ht))
    have hconj : trv (natAct s v) c₀ = trv v c₀ := by
      rw [← conj_trv, hcomm, mul_inv_cancel_right]
    obtain ⟨μ, -, hμv, hμ⟩ := trv_eq_trv hv hc₀ hconj
    have hμ1 : μ = 1 :=
      eq_one_of_sq_eq_one (mul_right_cancel₀ hc₀ (hμ.trans (one_mul c₀).symm))
    have hsv : natAct (s : antiSp k) v = v := by rw [hμv, hμ1, one_smul]
    have hsF : (s : antiSp k) ∈ fixPerp v w := hHle s.2
    have hsw : natAct (s : antiSp k) w =
        natAct (trv v (spBil (natAct (s : antiSp k) w) w)) w := by
      have h1 : spBil (natAct (s : antiSp k) w) v = 1 := by
        rw [← hsv, bil_act, hwv]
      conv_lhs => rw [act_w_eq hvw hsF, h1, one_smul]
      rw [act_trv, hwv, mul_one, add_comm]
    have hs_eq : (s : antiSp k) = trv v (spBil (natAct (s : antiSp k) w) w) := by
      refine eq_of_agree hvw hsF (trv_mem_fixPerp_left v w _) ?_ hsw
      rw [hsv, act_trv, bil_self, mul_zero, zero_smul, add_zero]
    rw [hXdef, Subgroup.mem_subgroupOf, hs_eq]
    apply trv_mem_rootGrp
    rw [mem_Lam, ← hs_eq]
    exact hHG s.2
  have hXeq : X = S := le_antisymm hXS hSX
  have hcardX : Nat.card X = Nat.card (rootGrp G₀ v) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rw [← card_rootGrp hv, ← hcardX, hXeq, hScard]

theorem exists_benderType_pair [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) {v w : Fin 4 → k}
    (hvw : spBil v w = 1) (h1 : (1 : k) ∈ Lam G₀ v) (h4 : 4 ≤ Nat.card (Lam G₀ v)) {b₀ : k}
    (hb₀ : b₀ ≠ 0) (hb₀L : b₀ ∈ Lam G₀ w) :
    ∃ m, 2 ≤ m ∧ BenderType (rootGrp G₀ v ⊔ rootGrp G₀ w : Subgroup (antiSp k)) m 1 1 := by
  classical
  set H : Subgroup (antiSp k) := rootGrp G₀ v ⊔ rootGrp G₀ w with hHdef
  have hHle : H ≤ fixPerp v w :=
    sup_le (rootGrp_le_fixPerp_left v w) (rootGrp_le_fixPerp_right v w)
  have hv : v ≠ 0 := ne_zero_of_bil_eq_one hvw
  have hn : 2 ≤ n := by
    have hle : Nat.card (Lam G₀ v) ≤ Nat.card k :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hk] at hle
    by_contra hlt
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp at hle <;> omega
  have hK := benderType_psl2 (k := k) hn hk
  have hρ := rhoP_injective (k := k) hvw
  set J := (H.subgroupOf (fixPerp v w)).map (rhoP hvw) with hJdef
  let eH : H ≃* J := (Subgroup.subgroupOfEquivOfLe hHle).symm.trans
    ((H.subgroupOf (fixPerp v w)).equivMapOfInjective (rhoP hvw) hρ)
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hg : trv v 1 * trv w b₀ ∈ H :=
    H.mul_mem (Subgroup.mem_sup_left (trv_mem_rootGrp h1))
      (Subgroup.mem_sup_right (trv_mem_rootGrp hb₀L))
  have htr : Matrix.trace (glMat ((trv v 1 * trv w b₀ : antiSp k) : GL (Fin 4) k)) = b₀ := by
    rw [trace_trv_mul_trv, hvw]
    ring
  have hnot2 : ∀ j : ℕ, (trv v 1 * trv w b₀) ^ 2 ^ j ≠ 1 := by
    intro j hj
    have := trace_eq_zero_of_pow_two_pow hj
    rw [htr] at this
    exact hb₀ this
  have hnotP : ¬ IsPGroup 2 H := by
    intro hP
    obtain ⟨j, hj⟩ := hP ⟨_, hg⟩
    exact hnot2 j (by simpa using congrArg Subtype.val hj)
  have h4H : 4 ∣ Nat.card H := by
    have hdvd := Subgroup.card_dvd_of_le (le_sup_left : rootGrp G₀ v ≤ H)
    obtain ⟨a, ha⟩ := (isPGroup_rootGrp (G₀ := G₀) v).exists_card_eq
    have h4a : 4 ≤ 2 ^ a := by rw [← ha, card_rootGrp hv]; exact h4
    have ha2 : 2 ≤ a := by
      by_contra hlt
      have : a = 0 ∨ a = 1 := by omega
      rcases this with rfl | rfl <;> simp at h4a
    have h4d : 4 ∣ 2 ^ a := by
      have := pow_dvd_pow 2 ha2
      simpa using this
    rw [ha] at hdvd
    exact h4d.trans hdvd
  rcases hK.linear_subgroup_cases J with hP | ⟨-, -, hodd⟩ | ⟨z, -, hz, hcz, -⟩ | ⟨-, Q, hJQ⟩ |
      ⟨m, hm, -, ⟨φ⟩⟩ | h6
  · exact absurd (hP.of_equiv eH.symm) hnotP
  · rw [← hcard] at hodd
    exact absurd (even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4H))
      (Nat.not_even_iff_odd.mpr hodd)
  · rw [← hcard] at hcz
    rw [hcz] at h4H
    obtain ⟨t, rfl⟩ := hz
    omega
  · exfalso
    have key : ∀ x : fixPerp v w, (x : antiSp k) ∈ H → x * x = 1 →
        rhoP hvw x ∈ (Q : Subgroup _) := by
      intro x hxH hx2
      have hxJ : rhoP hvw x ∈ J :=
        Subgroup.mem_map_of_mem (rhoP hvw) (by rw [Subgroup.mem_subgroupOf]; exact hxH)
      have hzp : IsPGroup 2 (Subgroup.zpowers (rhoP hvw x)) :=
        isPGroup_two_zpowers_of_mul_self_eq_one (by rw [← map_mul, hx2, map_one])
      have hle : Subgroup.zpowers (rhoP hvw x) ≤
          borel (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) :=
        Subgroup.zpowers_le.mpr (hJQ hxJ)
      have hmax := Q.is_maximal' (hzp.to_sup_of_normal_right' Q.isPGroup' hle) le_sup_right
      exact (sup_eq_right.mp hmax) (Subgroup.mem_zpowers _)
    set xv : fixPerp v w := ⟨trv v 1, trv_mem_fixPerp_left v w 1⟩
    set xw : fixPerp v w := ⟨trv w b₀, trv_mem_fixPerp_right v w b₀⟩
    have hxv := key xv (Subgroup.mem_sup_left (trv_mem_rootGrp h1))
      (Subtype.ext (trv_mul_self v 1))
    have hxw := key xw (Subgroup.mem_sup_right (trv_mem_rootGrp hb₀L))
      (Subtype.ext (trv_mul_self w b₀))
    have hprod : rhoP hvw (xv * xw) ∈ (Q : Subgroup _) := by
      rw [map_mul]
      exact (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)).mul_mem hxv hxw
    obtain ⟨j, hj⟩ := Q.isPGroup' ⟨_, hprod⟩
    have h2 : rhoP hvw ((xv * xw) ^ 2 ^ j) = rhoP hvw 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val hj
    have h3 := congrArg Subtype.val (hρ h2)
    exact hnot2 j (by simpa [xv, xw] using h3)
  · exact ⟨m, hm, BenderType.linear m hm (eH.trans φ)⟩
  · rw [← hcard] at h6
    rw [h6] at h4H
    norm_num at h4H

theorem pair_lemma [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) {v w : Fin 4 → k} (hvw : spBil v w = 1)
    (h1 : (1 : k) ∈ Lam G₀ v) (h4 : 4 ≤ Nat.card (Lam G₀ v)) {b₀ : k} (hb₀ : b₀ ≠ 0)
    (hb₀L : b₀ ∈ Lam G₀ w) :
    ∃ F₀ : Subfield k, (Lam G₀ v : Set k) = F₀ ∧ (Lam G₀ w : Set k) = F₀ := by
  obtain ⟨m, hm, hB⟩ := exists_benderType_pair hk hvw h1 h4 hb₀ hb₀L
  set H : Subgroup (antiSp k) := rootGrp G₀ v ⊔ rootGrp G₀ w with hHdef
  have hHle : H ≤ fixPerp v w :=
    sup_le (rootGrp_le_fixPerp_left v w) (rootGrp_le_fixPerp_right v w)
  have hHG : H ≤ G₀ := sup_le (rootGrp_le v) (rootGrp_le w)
  have hwv := bil_wv hvw
  have hcv : Nat.card (Lam G₀ v) = 2 ^ m :=
    card_lam_eq hvw hHle hHG le_sup_left one_ne_zero h1 hB
  have hcw : Nat.card (Lam G₀ w) = 2 ^ m :=
    card_lam_eq hwv (fixPerp_comm v w ▸ hHle) hHG le_sup_right hb₀ hb₀L hB
  have htrace : ∀ g ∈ H, Matrix.trace (glMat (g : GL (Fin 4) k)) ∈ fixField k m := by
    intro g hg
    rw [mem_fixField]
    apply trace_frob
    rcases benderType_pow_cases hB ⟨g, hg⟩ with h | h | h
    · left
      simpa using congrArg Subtype.val h
    · right; left
      simpa using congrArg Subtype.val h
    · right; right
      simpa using congrArg Subtype.val h
  have hwF : ∀ b ∈ Lam G₀ w, b ∈ fixField k m := by
    intro b hb
    have := htrace _ (H.mul_mem (Subgroup.mem_sup_left (trv_mem_rootGrp h1))
      (Subgroup.mem_sup_right (trv_mem_rootGrp hb)))
    rwa [trace_trv_mul_trv, hvw, one_pow, one_mul, mul_one] at this
  have hvF : ∀ a ∈ Lam G₀ v, a ∈ fixField k m := by
    intro a ha
    have hab := htrace _ (H.mul_mem (Subgroup.mem_sup_left (trv_mem_rootGrp ha))
      (Subgroup.mem_sup_right (trv_mem_rootGrp hb₀L)))
    rw [trace_trv_mul_trv, hvw, one_pow, mul_one] at hab
    have : a = a * b₀ * b₀⁻¹ := by field_simp
    rw [this]
    exact (fixField k m).mul_mem hab ((fixField k m).inv_mem (hwF b₀ hb₀L))
  have hle : (fixField k m : Set k).ncard ≤ 2 ^ m := ncard_fixField_le k (by omega)
  refine ⟨fixField k m, ?_, ?_⟩
  · apply Set.eq_of_subset_of_ncard_le (fun a ha => hvF a ha)
    have e : Nat.card (Lam G₀ v) = (Lam G₀ v : Set k).ncard := Nat.card_coe_set_eq _
    rw [← e, hcv]
    exact hle
  · apply Set.eq_of_subset_of_ncard_le (fun a ha => hwF a ha)
    have e : Nat.card (Lam G₀ w) = (Lam G₀ w : Set k).ncard := Nat.card_coe_set_eq _
    rw [← e, hcw]
    exact hle

end CFSG.Quasithin.Ch3E213M.G41
