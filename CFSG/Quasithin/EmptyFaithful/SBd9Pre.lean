module

public import CFSG.Quasithin.EmptyFaithful.SBd9Borel
public import CFSG.Quasithin.EmptyFaithful.R3c9Lie

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

section Elementary

omit [Finite G] in
theorem eq_mul_center_of_same_action {x x' : G} (hx : x ∈ L) (hx' : x' ∈ L)
    (h : ∀ y ∈ L, x⁻¹ * y * x = x'⁻¹ * y * x') : x' * x⁻¹ ∈ centerOf L := by
  refine ⟨L.mul_mem hx' (L.inv_mem hx), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := h y hy
  calc y * (x' * x⁻¹) = (x' * x⁻¹) * ((x' * x⁻¹)⁻¹ * y * (x' * x⁻¹)) := by group
    _ = (x' * x⁻¹) * y := by
      congr 1
      have e : (x' * x⁻¹)⁻¹ * y * (x' * x⁻¹) = x * (x'⁻¹ * y * x') * x⁻¹ := by group
      rw [e, ← h1]
      group

omit [Finite G] in
theorem commutator_eq_one_of_odd {y v z : G} (hodd : Odd (orderOf y)) (hz : z = y * v * y⁻¹ * v⁻¹)
    (hzc : y * z = z * y) (hz2 : z * z = 1) : z = 1 := by
  have hzy : ∀ k : ℕ, y ^ k * v * (y ^ k)⁻¹ = z ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : y ^ (k + 1) * v * (y ^ (k + 1))⁻¹ = y * (y ^ k * v * (y ^ k)⁻¹) * y⁻¹ := by group
      rw [e, ih]
      have e2 : y * (z ^ k * v) * y⁻¹ = (y * z ^ k * y⁻¹) * (y * v * y⁻¹) := by group
      rw [e2]
      have e3 : y * z ^ k * y⁻¹ = z ^ k := by
        have : Commute y z := hzc
        rw [(this.pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      have e4 : y * v * y⁻¹ = z * v := by rw [hz]; group
      rw [e3, e4, pow_succ, mul_assoc]
  have h1 := hzy (orderOf y)
  rw [pow_orderOf_eq_one] at h1
  have h2 : z ^ orderOf y = 1 := by
    have h3 : z ^ orderOf y * v = 1 * v := by rw [one_mul]; simpa using h1.symm
    exact mul_right_cancel h3
  obtain ⟨j, hj⟩ := hodd
  have hz2' : z ^ 2 = 1 := by rw [sq]; exact hz2
  have : z ^ orderOf y = z := by
    rw [hj, pow_succ, pow_mul, hz2', one_pow, one_mul]
  rw [← this]
  exact h2

omit [Finite G] in
theorem odd_orderOf_threePow [Finite G] (hF : Facts15311 T M V₁ Yp I) {x : G} (hx : x ∈ Yp)
    (hodd : Odd (orderOf x)) : ∃ k : ℕ, orderOf x = 3 ^ k := by
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
    IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
  obtain ⟨e, he⟩ : ∃ e : ℕ, Nat.card (OTwoQuot Yp) = 3 ^ e := by
    rcases hF.struct_Yp with he9 | ⟨-, hc, -⟩
    · obtain ⟨e9⟩ := he9
      exact ⟨2, by rw [Nat.card_congr e9.toEquiv]; simp⟩
    · exact ⟨3, hc⟩
  have hcard : Nat.card ↥Yp = 2 ^ a * 3 ^ e := by
    have h3 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 ^ e := he
    rw [h1, ha, h3]
    ring
  have hd : orderOf x ∣ 2 ^ a * 3 ^ e := hcard ▸ Subgroup.orderOf_dvd_natCard Yp hx
  have hcop : Nat.Coprime (orderOf x) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  have h3' : orderOf x ∣ 3 ^ e := hcop.dvd_of_dvd_mul_left hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3'
  exact ⟨k, hk⟩

theorem exists_orderThree_of_YL (hF : Facts15311 T M V₁ Yp I) (hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥) :
    ∃ y ∈ oTwoUpper (Yp ⊓ L), orderOf y = 3 := by
  classical
  obtain ⟨x, hxYL, hxodd, hx1⟩ : ∃ x ∈ Yp ⊓ L, Odd (orderOf x) ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hYL
    rw [eq_bot_iff, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, hxodd⟩
    exact Subgroup.mem_bot.mpr (hno x hx hxodd)
  obtain ⟨k, hk⟩ := odd_orderOf_threePow hF hxYL.1 hxodd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  refine ⟨x ^ 3 ^ (k - 1), Subgroup.pow_mem _ (mem_oTwoUpper_of_odd hxYL hxodd) _, ?_⟩
  have h3 : orderOf (x ^ 3 ^ (k - 1)) = 3 ^ k / Nat.gcd (3 ^ k) (3 ^ (k - 1)) := by
    rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hk]
  rw [h3]
  have : Nat.gcd (3 ^ k) (3 ^ (k - 1)) = 3 ^ (k - 1) :=
    Nat.gcd_eq_right (pow_dvd_pow 3 (Nat.sub_le k 1))
  rw [this]
  have h33 : 3 ^ k = 3 ^ (k - 1) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h33, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]

end Elementary

section Main

theorem n_eq_two (h37 : A37ForSQTK) (h38 : A38ForSQTK) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) (2 ^ n)) (hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥) :
    n = 2 ∧ ∃ y ∈ oTwoUpper (Yp ⊓ L), ∃ v ∈ VZ T M, ⁅v, y⁆ ∉ centerOf L := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hQ := sylow_inf_Sgp c hL0
  have hQn := borel_stage h37 h38 c hL0 hLie
  have hBM := borel_le_MI h37 h38 c hL0 hLie
  have hQV := sylow_le_centralizer_V h37 h38 c hL0 hLie
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH c.c33.mem
  have hSL := Sgp_le_normalizer_L hL0
  have hVS := VZ_le_Sgp153 hh
  have hYpMI := Yp_le_MI c
  have hMIY := MI_le_normalizer_Yp c
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := hh.hyp.isHv_of_inM' hh.hyp.inM
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  set YL := oTwoUpper (Yp ⊓ L) with hYLdef
  set B := L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) with hBdef
  have hYLL : YL ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hYLY : YL ≤ Yp := (oTwoUpper_le _).trans inf_le_left
  have hYLB : YL ≤ B := le_inf hYLL (fun y hy => hQn (Subgroup.mem_sup_left (hYLY hy)))
  have hYLM : YL ≤ M := (hYLY.trans hYpMI).trans inf_le_left
  have hYLV : YL ≤ Subgroup.normalizer (VZ T M : Set G) := fun y hy => hMV (hYLM hy)
  have hBYL : B ≤ Subgroup.normalizer (YL : Set G) := by
    intro b hb
    have h1 : b ∈ Subgroup.normalizer ((Yp ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hMIY (hBM hb), Subgroup.le_normalizer hb.1⟩
    exact normalizer_le_normalizer_oTwoUpper _ h1
  have hBV : B ≤ Subgroup.normalizer (VZ T M : Set G) := fun b hb => hMV (hBM hb).1
  have hVC : ∀ v ∈ VZ T M, v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr fun q' hq' =>
      (Subgroup.mem_centralizer_iff.mp (hQV hq') v hv).symm
  have hn2 : 2 ^ n - 1 ∣ 72 → n = 2 := by
    intro h
    have h1 : 2 ^ n - 1 ≤ 72 := Nat.le_of_dvd (by norm_num) h
    have h2 : n ≤ 6 := by
      by_contra hlt
      have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n
    · rfl
    all_goals (exfalso; revert h; decide)
  by_cases hP1 : ∃ y ∈ YL, ∃ v ∈ VZ T M, ⁅v, y⁆ ∉ centerOf L
  ·
    refine ⟨?_, hP1⟩
    obtain ⟨y₀, hy₀, v₀, hv₀, hnot⟩ := hP1
    set W : Subgroup G := ⁅VZ T M, YL⁆ with hWdef
    have hWV : W ≤ VZ T M := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv y hy
      have h1 : y * v⁻¹ * y⁻¹ ∈ VZ T M :=
        (Subgroup.mem_normalizer_iff.mp (hYLV hy) v⁻¹).mp ((VZ T M).inv_mem hv)
      have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (VZ T M).mul_mem hv h1
    have hWL : W ≤ L := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (L : Set G) := hSL (hVS hv)
      have h1 : v * y * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hvN y).mp (hYLL hy)
      have e : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [e]
      exact L.mul_mem h1 (L.inv_mem (hYLL hy))
    have hWC : W ≤ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := fun w hw =>
      hVC w (hWV hw)
    have hBW : B ≤ Subgroup.normalizer (W : Set G) := by
      intro b hb
      refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
      rw [hWdef, Subgroup.commutator_def] at hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
        have h1 : b * g₁ * b⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hBV hb) g₁).mp hg₁
        have h2 : b * g₂ * b⁻¹ ∈ YL := (Subgroup.mem_normalizer_iff.mp (hBYL hb) g₂).mp hg₂
        have e : b * ⁅g₁, g₂⁆ * b⁻¹ = ⁅b * g₁ * b⁻¹, b * g₂ * b⁻¹⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact Subgroup.commutator_mem_commutator h1 h2
      | one => simp
      | mul x y hx hy ihx ihy =>
        have e : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
        rw [e]
        exact W.mul_mem ihx ihy
      | inv x hx ih =>
        have e : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        rw [e]
        exact W.inv_mem ih
    have hWnot : ¬ W ≤ centerOf L := fun hle =>
      hnot (hle (Subgroup.commutator_mem_commutator hv₀ hy₀))
    have hexp := hLie.exp W (le_inf hWL hWC) hBW hWnot 72 (fun b hb w hw => by
      have h1 := pow72_mem_centralizer hh (hBM hb).1
      have h2 : w * b ^ 72 = b ^ 72 * w := Subgroup.mem_centralizer_iff.mp h1 w (hWV hw)
      have h3 : ⁅b ^ 72, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h2.symm
      rw [h3]
      exact (centerOf L).one_mem)
    exact hn2 hexp
  · exfalso
    push Not at hP1
    have hYC : ∀ y ∈ YL, ∀ v ∈ VZ T M, y * v = v * y := by
      have hle : YL ≤ Subgroup.centralizer (VZ T M : Set G) := by
        rw [hYLdef, oTwoUpper, Subgroup.closure_le]
        rintro y ⟨hy, hyodd⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro v hv
        have hyL : y ∈ L := hy.2
        have hyYL : y ∈ YL := mem_oTwoUpper_of_odd hy hyodd
        have hzmem : ⁅y, v⁆ ∈ centerOf L := by
          have := (centerOf L).inv_mem (hP1 y hyYL v hv)
          simpa [commutatorElement_inv] using this
        have hzV : ⁅y, v⁆ ∈ VZ T M := by
          have h1 : y * v * y⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hYLV hyYL) v).mp hv
          have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
          rw [e]
          exact (VZ T M).mul_mem h1 ((VZ T M).inv_mem hv)
        have hzc : y * ⁅y, v⁆ = ⁅y, v⁆ * y := Subgroup.mem_centralizer_iff.mp hzmem.2 y hyL
        have hz2 : ⁅y, v⁆ * ⁅y, v⁆ = 1 := by
          rw [← sq]
          exact hh.hyp.elemAbelian.2 _ hzV
        have h1 := commutator_eq_one_of_odd hyodd rfl hzc hz2
        have h2 : y * v = v * y := commutatorElement_eq_one_iff_mul_comm.mp (by
          have : ⁅y, v⁆ = 1 := h1
          exact this)
        exact h2.symm
      intro y hy v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) v hv).symm
    have hinner : ∀ v ∈ VZ T M, ∃ x ∈ L, ∀ y ∈ L, v⁻¹ * y * v = x⁻¹ * y * x := fun v hv =>
      hLie.inner v (hSL (hVS hv)) (hVC v hv)
    choose! xf hxL hxf using hinner
    have hxQ : ∀ v ∈ VZ T M, xf v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
      intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_
      have h1 := hxf v hv q' hq'.2
      have h2 : q' * v = v * q' := (Subgroup.mem_centralizer_iff.mp (hQV hq') v hv).symm
      have h3 : v⁻¹ * q' * v = q' := by rw [mul_assoc, h2]; group
      rw [h3] at h1
      calc q' * xf v = xf v * ((xf v)⁻¹ * q' * xf v) := by group
        _ = xf v * q' := by rw [← h1]
    have hxY : ∀ v ∈ VZ T M, ∀ y ∈ YL, xf v * y = y * xf v := by
      intro v hv y hy
      have h1 := hxf v hv y (hYLL hy)
      have h3 : v⁻¹ * y * v = y := by rw [mul_assoc, hYC y hy v hv]; group
      rw [h3] at h1
      calc xf v * y = xf v * ((xf v)⁻¹ * y * xf v) := by rw [← h1]
        _ = y * xf v := by group
    by_cases hA : ∀ v ∈ VZ T M, xf v ∈ centerOf L
    ·
      apply c.c33.not_le
      rw [hHv]
      intro l hl
      apply Subgroup.centralizer_le_normalizer
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have h1 := hxf v hv l hl
      have h2 : xf v * l = l * xf v := (Subgroup.mem_centralizer_iff.mp (hA v hv).2 l hl).symm
      have h3 : (xf v)⁻¹ * l * xf v = l := by rw [mul_assoc, ← h2]; group
      rw [h3] at h1
      calc v * l = v * (v⁻¹ * l * v) := by rw [h1]
        _ = l * v := by group
    · push Not at hA
      obtain ⟨v₀, hv₀, hv₀n⟩ := hA
      have hBL : ∀ b ∈ B, b ∈ L := fun b hb => hb.1
      have hconj : ∀ b ∈ B, ∀ v ∈ VZ T M, ∃ z ∈ centerOf L,
          b * xf v * b⁻¹ = z * xf (b * v * b⁻¹) := by
        intro b hb v hv
        have hv' : b * v * b⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hBV hb) v).mp hv
        have hbL := hBL b hb
        have hx1 : b * xf v * b⁻¹ ∈ L := L.mul_mem (L.mul_mem hbL (hxL v hv)) (L.inv_mem hbL)
        have hx2 := hxL _ hv'
        have hsame : ∀ y ∈ L, (b * xf v * b⁻¹)⁻¹ * y * (b * xf v * b⁻¹) =
            (xf (b * v * b⁻¹))⁻¹ * y * xf (b * v * b⁻¹) := by
          intro y hy
          have hy' : b⁻¹ * y * b ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hbL) hy) hbL
          have h1 := hxf v hv _ hy'
          have h2 := hxf _ hv' y hy
          calc (b * xf v * b⁻¹)⁻¹ * y * (b * xf v * b⁻¹)
              = b * ((xf v)⁻¹ * (b⁻¹ * y * b) * xf v) * b⁻¹ := by group
            _ = b * (v⁻¹ * (b⁻¹ * y * b) * v) * b⁻¹ := by rw [← h1]
            _ = (b * v * b⁻¹)⁻¹ * y * (b * v * b⁻¹) := by group
            _ = (xf (b * v * b⁻¹))⁻¹ * y * xf (b * v * b⁻¹) := h2
        have hz := eq_mul_center_of_same_action hx1 hx2 hsame
        refine ⟨(xf (b * v * b⁻¹) * (b * xf v * b⁻¹)⁻¹)⁻¹, (centerOf L).inv_mem hz, ?_⟩
        group
      set W : Subgroup G := Subgroup.closure ((centerOf L : Set G) ∪ xf '' (VZ T M : Set G)) with hWdef
      have hgenL : ∀ g ∈ ((centerOf L : Set G) ∪ xf '' (VZ T M : Set G)), g ∈ L := by
        rintro g (hg | ⟨v, hv, rfl⟩)
        · exact hg.1
        · exact hxL v hv
      have hWL : W ≤ L := (Subgroup.closure_le L).mpr hgenL
      have hWC : W ≤ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro g (hg | ⟨v, hv, rfl⟩)
        · exact Subgroup.mem_centralizer_iff.mpr fun q' hq' =>
            (Subgroup.mem_centralizer_iff.mp hg.2 q' hq'.2)
        · exact hxQ v hv
      have hBW : B ≤ Subgroup.normalizer (W : Set G) := by
        intro b hb
        refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
        induction hw using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with hx | ⟨v, hv, rfl⟩
          · have : b * x * b⁻¹ = x := by
              have h1 : b * x = x * b := Subgroup.mem_centralizer_iff.mp hx.2 b (hBL b hb)
              rw [h1]
              group
            rw [this]
            exact Subgroup.subset_closure (Or.inl hx)
          · obtain ⟨z, hz, hbz⟩ := hconj b hb v hv
            rw [hbz]
            have hv' : b * v * b⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hBV hb) v).mp hv
            exact W.mul_mem (Subgroup.subset_closure (Or.inl hz))
              (Subgroup.subset_closure (Or.inr ⟨_, hv', rfl⟩))
        | one => simp
        | mul x y hx hy ihx ihy =>
          have e : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
          rw [e]
          exact W.mul_mem ihx ihy
        | inv x hx ih =>
          have e : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
          rw [e]
          exact W.inv_mem ih
      have hWnot : ¬ W ≤ centerOf L := fun hle =>
        hv₀n (hle (Subgroup.subset_closure (Or.inr ⟨v₀, hv₀, rfl⟩)))
      have hexp : ∀ b ∈ B, ∀ w ∈ W, ⁅b ^ 72, w⁆ ∈ centerOf L := by
        intro b hb w hw
        have hb72 : b ^ 72 ∈ B := B.pow_mem hb 72
        have hbL72 := hBL _ hb72
        have hcv : ∀ v ∈ VZ T M, b ^ 72 * v * (b ^ 72)⁻¹ = v := by
          intro v hv
          have h1 := pow72_mem_centralizer hh (hBM hb).1
          have h2 : v * b ^ 72 = b ^ 72 * v := Subgroup.mem_centralizer_iff.mp h1 v hv
          rw [← h2]
          group
        induction hw using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with hx | ⟨v, hv, rfl⟩
          · have h1 : b ^ 72 * x = x * b ^ 72 :=
              Subgroup.mem_centralizer_iff.mp hx.2 _ hbL72
            have : ⁅b ^ 72, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h1
            rw [this]
            exact (centerOf L).one_mem
          · obtain ⟨z, hz, hbz⟩ := hconj _ hb72 v hv
            rw [hcv v hv] at hbz
            have e : ⁅b ^ 72, xf v⁆ = z := by
              have : b ^ 72 * xf v * (b ^ 72)⁻¹ = z * xf v := hbz
              calc ⁅b ^ 72, xf v⁆ = (b ^ 72 * xf v * (b ^ 72)⁻¹) * (xf v)⁻¹ := rfl
                _ = z := by rw [this]; group
            rw [e]
            exact hz
        | one => simp
        | mul x y hx hy ihx ihy =>
          have hxL' := hWL hx
          have e : ⁅b ^ 72, x * y⁆ = ⁅b ^ 72, x⁆ * (x * ⁅b ^ 72, y⁆ * x⁻¹) := by
            simp [commutatorElement_def]
            group
          rw [e]
          have hc : x * ⁅b ^ 72, y⁆ * x⁻¹ = ⁅b ^ 72, y⁆ := by
            have := Subgroup.mem_centralizer_iff.mp ihy.2 x hxL'
            rw [this]
            group
          rw [hc]
          exact (centerOf L).mul_mem ihx ihy
        | inv x hx ih =>
          have hxL' := hWL hx
          have e : ⁅b ^ 72, x⁻¹⁆ = x⁻¹ * ⁅b ^ 72, x⁆⁻¹ * x := by
            simp [commutatorElement_def]
            group
          rw [e]
          have hc : x⁻¹ * ⁅b ^ 72, x⁆⁻¹ * x = ⁅b ^ 72, x⁆⁻¹ := by
            have := Subgroup.mem_centralizer_iff.mp ((centerOf L).inv_mem ih).2 x⁻¹ (L.inv_mem hxL')
            rw [this]
            group
          rw [hc]
          exact (centerOf L).inv_mem ih
      have hq : 2 ^ n - 1 ∣ 72 := hLie.exp W (le_inf hWL hWC) hBW hWnot 72 hexp
      have hn2' := hn2 hq
      subst hn2'
      obtain ⟨y₃, hy₃, hy₃3⟩ := exists_orderThree_of_YL c.facts11 hYL
      exact hv₀n (hLie.reg4 (by norm_num) y₃ (hYLB hy₃) hy₃3 (xf v₀)
        ⟨hxL v₀ hv₀, hxQ v₀ hv₀⟩ (hxY v₀ hv₀ y₃ hy₃))


omit [Finite G] in
theorem mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have e : A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [e] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    obtain ⟨a', ha', b', hb', rfl⟩ := ihy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have := h a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← this]
      _ = a * a' * (b * b') := by group
  | inv x hx ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ih
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a ha b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a * b = b * a := this
        calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
          _ = (b * a)⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem fixed_eq_one_of_gen' {Y V : Subgroup G} (hV4 : Nat.card V = 4)
    (hgen : Y ≤ Subgroup.closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k})
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hact : ¬ ∀ y ∈ Y, ∀ v ∈ V, y * v = v * y) :
    ∀ x ∈ V, (∀ a ∈ Y, a * x = x * a) → x = 1 := by
  intro x hx hc
  by_contra hx1
  apply hact
  have hle : Y ≤ Subgroup.centralizer (V : Set G) := by
    refine hgen.trans ((Subgroup.closure_le (Subgroup.centralizer (V : Set G))).mpr fun y hy => ?_)
    obtain ⟨hyY, k, hk⟩ := hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hall : ∀ w ∈ V, y * w = w * y
    · exact (hall v hv).symm
    · exfalso
      have h1 := R3c9.fpf_of_orderOf_threePow hV4 hk (hYN hyY) hall x hx hx1
      apply h1
      have h2 := hc y hyY
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [h2]
        _ = x := by group
  intro y hy v hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) v hv).symm


theorem centralizes_L_of_centralizes_YL (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁))
    (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) 4) (hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥) {v : G}
    (hv : v ∈ VZ T M) (hvY : ∀ y ∈ oTwoUpper (Yp ⊓ L), y * v = v * y) :
    v ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hQV := sylow_le_centralizer_V h37 h38 c hL0 hLie
  have hBM := borel_le_MI h37 h38 c hL0 hLie
  have hQn := borel_stage h37 h38 c hL0 hLie
  have hSL := Sgp_le_normalizer_L hL0
  have hVS := VZ_le_Sgp153 hh
  have hYLL : oTwoUpper (Yp ⊓ L) ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hYLY : oTwoUpper (Yp ⊓ L) ≤ Yp := (oTwoUpper_le _).trans inf_le_left
  have hYLB : oTwoUpper (Yp ⊓ L) ≤
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    le_inf hYLL (fun y hy => hQn (Subgroup.mem_sup_left (hYLY hy)))
  have hvC : v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q' hq' =>
      (Subgroup.mem_centralizer_iff.mp (hQV hq') v hv).symm
  obtain ⟨x, hxL, hx⟩ := hLie.inner v (hSL (hVS hv)) hvC
  have hxQ : x ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_
    have h1 := hx q' hq'.2
    have h2 : q' * v = v * q' := (Subgroup.mem_centralizer_iff.mp (hQV hq') v hv).symm
    have h3 : v⁻¹ * q' * v = q' := by rw [mul_assoc, h2]; group
    rw [h3] at h1
    calc q' * x = x * (x⁻¹ * q' * x) := by group
      _ = x * q' := by rw [← h1]
  obtain ⟨y₃, hy₃, hy₃3⟩ := exists_orderThree_of_YL c.facts11 hYL
  have hxy : x * y₃ = y₃ * x := by
    have h1 := hx y₃ (hYLL hy₃)
    have h3 : v⁻¹ * y₃ * v = y₃ := by rw [mul_assoc, hvY y₃ hy₃]; group
    rw [h3] at h1
    calc x * y₃ = x * (x⁻¹ * y₃ * x) := by rw [← h1]
      _ = y₃ * x := by group
  have hxZ : x ∈ centerOf L := hLie.reg4 rfl y₃ (hYLB hy₃) hy₃3 x ⟨hxL, hxQ⟩ hxy
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have h1 := hx l hl
  have h2 : x * l = l * x := (Subgroup.mem_centralizer_iff.mp hxZ.2 l hl).symm
  have h3 : x⁻¹ * l * x = l := by rw [mul_assoc, ← h2]; group
  rw [h3] at h1
  calc l * v = v * (v⁻¹ * l * v) := by group
    _ = v * l := by rw [h1]


theorem prefix38 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) (2 ^ n)) (hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥) :
    n = 2 ∧ Yp = Y153 Mc M ∧
      ((V₁ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∧ V₂ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∨
        (V₂ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∧ V₁ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y)) := by
  classical
  obtain ⟨hn2, y₁, hy₁, v₁, hv₁, hnot⟩ := n_eq_two h37 h38 c hL0 hn hLie hYL
  subst hn2
  have hLie4 : LieL3 L (Sgp153 T V₁ ⊓ L) 4 := by simpa using hLie
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hQV := sylow_le_centralizer_V h37 h38 c hL0 hLie
  have hQn := borel_stage h37 h38 c hL0 hLie
  have hSL := Sgp_le_normalizer_L hL0
  have hVS := VZ_le_Sgp153 hh
  have hYpMI := Yp_le_MI c
  have hMIY := MI_le_normalizer_Yp c
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYLL : oTwoUpper (Yp ⊓ L) ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hYLY : oTwoUpper (Yp ⊓ L) ≤ Yp := (oTwoUpper_le _).trans inf_le_left
  have hVC : ∀ v ∈ VZ T M, v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr fun q' hq' =>
      (Subgroup.mem_centralizer_iff.mp (hQV hq') v hv).symm
  have hYLgen : oTwoUpper (Yp ⊓ L) ≤
      Subgroup.closure {x : G | x ∈ oTwoUpper (Yp ⊓ L) ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    rw [oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure ⟨?_, ?_⟩
    · exact mem_oTwoUpper_of_odd hx.1 hx.2
    · exact odd_orderOf_threePow c.facts11 hx.1.1 hx.2
  have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer ((oTwoUpper (Yp ⊓ L) : Subgroup G) : Set G) := by
    intro s hs
    have h1 : s ∈ Subgroup.normalizer ((Yp ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hMIY ⟨hSM hs, hSI hs⟩, hSL hs⟩
    exact normalizer_le_normalizer_oTwoUpper _ h1
  obtain ⟨hY₁, hY₂⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
  have hYpY : Yp ≤ Y153 Mc M := hh.Yp_le_Y153
  have hV₁S : V₁ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₁ hv)
  have hV₂S : V₂ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₂ hv)
  have d1 := R3c9.centralizes_or_le_of_generated_by_threePow hYLgen (fun v hv => hSYL (hV₁S hv))
    (hYLY.trans (hYpY.trans hY₁)) hh.decomp.card₁
  have d2 := R3c9.centralizes_or_le_of_generated_by_threePow hYLgen (fun v hv => hSYL (hV₂S hv))
    (hYLY.trans (hYpY.trans hY₂)) hh.decomp.card₂
  have hVcom : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb => by
    have := hh.hyp.elemAbelian.1.is_comm.comm ⟨a, hh.decomp.le₁ ha⟩ ⟨b, hh.decomp.le₂ hb⟩
    exact congrArg Subtype.val this
  have key : (¬ (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∨
      ¬ (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y)) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨h1, h2⟩ := hboth
    apply hnot
    have hcv : y₁ * v₁ = v₁ * y₁ := by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hVcom (hh.decomp.sup ▸ hv₁)
      have e1 := h1 y₁ hy₁ a ha
      have e2 := h2 y₁ hy₁ b hb
      calc y₁ * (a * b) = (y₁ * a) * b := by group
        _ = (a * y₁) * b := by rw [e1]
        _ = a * (y₁ * b) := by group
        _ = a * (b * y₁) := by rw [e2]
        _ = (a * b) * y₁ := by group
    have : ⁅v₁, y₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcv.symm
    rw [this]
    exact (centerOf L).one_mem
  have hcase : ((∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∧ V₂ ≤ oTwoUpper (Yp ⊓ L) ∧
        ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∨
      ((∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∧ V₁ ≤ oTwoUpper (Yp ⊓ L) ∧
        ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) := by
    rcases d1 with h1 | ⟨hV1, hn1⟩ <;> rcases d2 with h2 | ⟨hV2, hn2⟩
    · exfalso
      rcases key with k | k
      · exact k h1
      · exact k h2
    · exact Or.inl ⟨h1, hV2, hn2⟩
    · exact Or.inr ⟨h2, hV1, hn1⟩
    · exfalso
      have hVYL : VZ T M ≤ oTwoUpper (Yp ⊓ L) := by
        rw [← hh.decomp.sup]
        exact sup_le hV1 hV2
      have hVL : VZ T M ≤ L := hVYL.trans hYLL
      have hVZ : VZ T M ⊓ centerOf L = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxV, hxZ⟩
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hVcom (hh.decomp.sup ▸ hxV)
        have hcomm : ∀ y ∈ oTwoUpper (Yp ⊓ L), y * (a * b) = (a * b) * y := fun y hy =>
          (Subgroup.mem_centralizer_iff.mp hxZ.2 y (hYLL hy))
        have hfix : ∀ y ∈ oTwoUpper (Yp ⊓ L), y * a * y⁻¹ = a ∧ y * b * y⁻¹ = b := by
          intro y hy
          have ha' : y * a * y⁻¹ ∈ V₁ :=
            (Subgroup.mem_normalizer_iff.mp (hYLY.trans (hYpY.trans hY₁) hy) a).mp ha
          have hb' : y * b * y⁻¹ ∈ V₂ :=
            (Subgroup.mem_normalizer_iff.mp (hYLY.trans (hYpY.trans hY₂) hy) b).mp hb
          have e : (y * a * y⁻¹) * (y * b * y⁻¹) = a * b := by
            calc (y * a * y⁻¹) * (y * b * y⁻¹) = y * (a * b) * y⁻¹ := by group
              _ = a * b := by rw [hcomm y hy]; group
          have hm : (a⁻¹ * (y * a * y⁻¹)) = b * (y * b * y⁻¹)⁻¹ := by
            have h3 : (y * a * y⁻¹) = a * (b * (y * b * y⁻¹)⁻¹) := by
              have hcb : b * (y * b * y⁻¹)⁻¹ ∈ V₂ := V₂.mul_mem hb (V₂.inv_mem hb')
              calc y * a * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) * (y * b * y⁻¹)⁻¹ := by group
                _ = a * b * (y * b * y⁻¹)⁻¹ := by rw [e]
                _ = a * (b * (y * b * y⁻¹)⁻¹) := by group
            calc a⁻¹ * (y * a * y⁻¹) = a⁻¹ * (a * (b * (y * b * y⁻¹)⁻¹)) := by rw [← h3]
              _ = b * (y * b * y⁻¹)⁻¹ := by group
          have hm1 : a⁻¹ * (y * a * y⁻¹) ∈ V₁ := V₁.mul_mem (V₁.inv_mem ha) ha'
          have hm2 : b * (y * b * y⁻¹)⁻¹ ∈ V₂ := V₂.mul_mem hb (V₂.inv_mem hb')
          have hmem : a⁻¹ * (y * a * y⁻¹) ∈ V₁ ⊓ V₂ := ⟨hm1, hm ▸ hm2⟩
          rw [hh.decomp.inf, Subgroup.mem_bot] at hmem
          have hya : y * a * y⁻¹ = a := by
            calc y * a * y⁻¹ = a * (a⁻¹ * (y * a * y⁻¹)) := by group
              _ = a := by rw [hmem]; group
          refine ⟨hya, ?_⟩
          have : y * b * y⁻¹ = (a * b) * (a⁻¹) := by
            calc y * b * y⁻¹ = (y * a * y⁻¹)⁻¹ * ((y * a * y⁻¹) * (y * b * y⁻¹)) := by group
              _ = a⁻¹ * (a * b) := by rw [e, hya]
              _ = b := by group
              _ = (a * b) * a⁻¹ := by
                have := hVcom a ha b hb
                calc b = (b * a) * a⁻¹ := by group
                  _ = (a * b) * a⁻¹ := by rw [this]
          rw [this]
          have := hVcom a ha b hb
          calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [this]
            _ = b := by group
        have ha1 : a = 1 := fixed_eq_one_of_gen' hh.decomp.card₁ hYLgen
          (fun y hy => hYLY.trans (hYpY.trans hY₁) hy) hn1 a ha fun y hy => by
            have := (hfix y hy).1
            calc y * a = (y * a * y⁻¹) * y := by group
              _ = a * y := by rw [this]
        have hb1 : b = 1 := fixed_eq_one_of_gen' hh.decomp.card₂ hYLgen
          (fun y hy => hYLY.trans (hYpY.trans hY₂) hy) hn2 b hb fun y hy => by
            have := (hfix y hy).2
            calc y * b = (y * b * y⁻¹) * y := by group
              _ = b * y := by rw [this]
        rw [ha1, hb1]
        simp
      have hcardV := hLie4.card (VZ T M) (le_inf hVL (fun v hv => hVC v hv)) hVZ
      rw [hh.hyp.card_VZ] at hcardV
      omega
  have hcen : ∀ v ∈ VZ T M, (∀ y ∈ oTwoUpper (Yp ⊓ L), y * v = v * y) →
      v ∈ Subgroup.centralizer (L : Set G) := fun v hv hvY =>
    centralizes_L_of_centralizes_YL h37 h38 c hL0 hLie4 hYL hv hvY
  have hcase' : (V₁ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∧ V₂ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∨
        (V₂ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∧ V₁ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨fun v hv => hcen v (hh.decomp.le₁ hv) (fun y hy => h1 y hy v hv), h1, h2, h3⟩
    · exact Or.inr ⟨fun v hv => hcen v (hh.decomp.le₂ hv) (fun y hy => h1 y hy v hv), h1, h2, h3⟩
  refine ⟨rfl, ?_, hcase'⟩
  rcases hh.cases with hY | ⟨hU, -⟩
  · exact hY
  · exfalso
    obtain ⟨hN1, hN2⟩ := Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU
    have hLM : L ≤ M := by
      rcases hcase' with ⟨h1, -⟩ | ⟨h1, -⟩
      · intro l hl
        exact hN1 (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
          fun v hv => (Subgroup.mem_centralizer_iff.mp (h1 hv) l hl).symm))
      · intro l hl
        exact hN2 (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
          fun v hv => (Subgroup.mem_centralizer_iff.mp (h1 hv) l hl).symm))
    exact c.c33.not_le hLM

end Main

end CFSG.Quasithin.SBd9
