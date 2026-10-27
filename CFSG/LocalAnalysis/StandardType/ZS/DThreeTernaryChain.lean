module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeChain
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.Fischer.Classification.PartIII.U.SixForms
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs
import CFSG.Fischer.Uniq.CompTau
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) ternaryChainAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

theorem orderOf_reflBar_mul_reflBar_eq_three {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f) (hm : 4 ≤ m)
    {v w : Fin m → ZMod 3} (hv : f v v = 1) (hw : f w w = 1) (hvw : f v w ≠ 0)
    (hne : w ≠ v ∧ w ≠ -v) : orderOf (reflBar f v * reflBar f w) = 3 := by
  have h3 : (reflBar f v * reflBar f w) ^ 3 = 1 := reflBar_mul_pow_three hf hv hw hvw
  have hdvd : orderOf (reflBar f v * reflBar f w) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hne1 : orderOf (reflBar f v * reflBar f w) ≠ 1 := by
    intro h1
    have h1' : reflBar f v * reflBar f w = 1 := orderOf_eq_one_iff.1 h1
    have hw' : reflBar f w = reflBar f v := by
      rw [eq_inv_of_mul_eq_one_right h1', inv_eq_of_mul_eq_one_right (reflBar_mul_self v)]
    rcases (reflBar_eq_reflBar_iff hf hm hv hw).1 hw'.symm with h | h
    · exact hne.1 h
    · exact hne.2 h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem reflBar_mul_reflBar_pow_eq_one {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    {v w : Fin m → ZMod 3} (hv : f v v = 1) (hw : f w w = 1) :
    (reflBar f v * reflBar f w) ^ (if f v w = 0 then 2 else 3) = 1 := by
  split_ifs with h
  · exact reflBar_mul_pow_two hf hv hw h
  · exact reflBar_mul_pow_three hf hv hw h

theorem affineTriangle_reflBar {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 4 ≤ m) {a b c : Fin m → ZMod 3} (ha : f a a = 1) (hb : f b b = 1)
    (hc : f c c = 1) (hab : f a b ≠ 0) (hac : f a c ≠ 0) (hbc : f b c ≠ 0)
    (hab' : b ≠ a ∧ b ≠ -a) (hac' : c ≠ a ∧ c ≠ -a) (hbc' : c ≠ b ∧ c ≠ -b)
    (hd : f (a + f a c • c) b ≠ 0) (hdb : b ≠ a + f a c • c ∧ b ≠ -(a + f a c • c)) :
    AffineTriangle (D3 f) (reflBar f a) (reflBar f b) (reflBar f c) := by
  have hv : f (a + f a c • c) (a + f a c • c) = 1 := F3.norm_add_pair hf ha hc
  have hab3 : orderOf (reflBar f a * reflBar f b) = 3 :=
    orderOf_reflBar_mul_reflBar_eq_three hf hm ha hb hab hab'
  have hac3 : orderOf (reflBar f a * reflBar f c) = 3 :=
    orderOf_reflBar_mul_reflBar_eq_three hf hm ha hc hac hac'
  have hbc3 : orderOf (reflBar f b * reflBar f c) = 3 :=
    orderOf_reflBar_mul_reflBar_eq_three hf hm hb hc hbc hbc'
  have hconj : reflBar f c * reflBar f a * reflBar f c =
      reflBar f (a + f a c • c) := by
    rw [reflBar_conj hf, F3.act_refl hc]
  have hd3 : orderOf (reflBar f c * reflBar f a * reflBar f c * reflBar f b) = 3 := by
    rw [hconj]
    exact orderOf_reflBar_mul_reflBar_eq_three hf hm hv hb hd hdb
  exact ⟨reflBar_mem_D3 ha, reflBar_mem_D3 hb, reflBar_mem_D3 hc, hab3, hac3, hbc3, hd3⟩

theorem act_prod_ofFn_refl {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} {w : Fin m → ZMod 3} :
    ∀ (n : ℕ) (v : Fin n → Fin m → ZMod 3), (∀ i, f (v i) (v i) = 1) →
      (∀ i j, i ≠ j → f (v i) (v j) = 0) →
      F3.act ((List.ofFn fun i => F3.refl f (v i)).prod) w =
        w + ∑ i : Fin n, f w (v i) • v i := by
  intro n
  induction n with
  | zero => intro v _ _; simp
  | succ n ih =>
    intro v hunit horth
    rw [List.ofFn_succ, List.prod_cons, F3.act_mul]
    have hstep := ih (fun i => v i.succ) (fun i => hunit i.succ)
      (fun i j hij => horth i.succ j.succ (fun h => hij (Fin.succ_injective n h)))
    rw [hstep, F3.act_refl (hunit 0)]
    have hS : f (∑ i : Fin n, f w (v i.succ) • v i.succ) (v 0) = 0 := by
      rw [LinearMap.BilinForm.sum_left]
      apply Finset.sum_eq_zero
      intro i _
      rw [LinearMap.BilinForm.smul_left, horth i.succ 0 (Fin.succ_ne_zero i), mul_zero]
    rw [LinearMap.BilinForm.add_left, hS, add_zero, Fin.sum_univ_succ]
    abel

private theorem ztc_diagF3_one_apply (m : ℕ) (x : Fin m → ZMod 3) (i : Fin m) :
    diagF3 m 1 x (Pi.single i 1) = x i := by
  rw [diagF3_apply, Finset.sum_eq_single i]
  · have h : diagF3Entry m 1 i = 1 := by
      rw [diagF3Entry]
      split_ifs <;> rfl
    rw [Pi.single_eq_same, h, one_mul, mul_one]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem ztc_diagF3_one_pair (m : ℕ) (i j : Fin m) :
    diagF3 m 1 (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [CFSG.Fischer.Classification.LocalU.diagF3_single]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
    rw [diagF3Entry]
    split_ifs <;> rfl
  · rw [if_neg hij, if_neg hij]

theorem coe_prod_ofFn_reflElt_single (m : ℕ) :
    (((List.ofFn fun i : Fin m => reflElt (diagF3 m 1) (Pi.single i 1)).prod :
      F3.reflGroup (diagF3 m 1)) : GL (Fin m) (ZMod 3)) = -1 := by
  have hunit : ∀ i : Fin m, diagF3 m 1 (Pi.single i 1) (Pi.single i 1) = 1 := by
    intro i
    rw [ztc_diagF3_one_pair, if_pos rfl]
  have horth : ∀ i j : Fin m, i ≠ j →
      diagF3 m 1 (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro i j hij
    rw [ztc_diagF3_one_pair, if_neg hij]
  rw [Subgroup.val_list_prod, List.map_ofFn]
  apply F3.gl_ext
  intro w
  have hprod : F3.act
      ((List.ofFn fun i : Fin m => F3.refl (diagF3 m 1) (Pi.single i 1)).prod) w =
        w + ∑ i : Fin m, diagF3 m 1 w (Pi.single i 1) • Pi.single i 1 :=
    act_prod_ofFn_refl (n := m) (v := fun i : Fin m => Pi.single i 1) hunit horth
  simp only [Function.comp_def, coe_reflElt] at hprod ⊢
  rw [hprod]
  have hsum : (∑ i : Fin m, diagF3 m 1 w (Pi.single i 1) • Pi.single i 1) = w := by
    calc (∑ i : Fin m, diagF3 m 1 w (Pi.single i 1) • Pi.single i 1)
        = ∑ i : Fin m, Pi.single i (w i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ztc_diagF3_one_apply, ← Pi.single_smul' i (w i) 1, smul_eq_mul, mul_one]
      _ = w := Finset.univ_sum_single w
  rw [hsum, F3.act_neg_one]
  have h2 : ∀ x : ZMod 3, x + x = -x := by decide
  funext k
  exact h2 (w k)

theorem prod_ofFn_reflElt_single_mem_center (m : ℕ) :
    (List.ofFn fun i : Fin m => reflElt (diagF3 m 1) (Pi.single i 1)).prod ∈
      Subgroup.center (F3.reflGroup (diagF3 m 1)) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_prod_ofFn_reflElt_single m]
  rw [mul_neg_one, neg_one_mul]

theorem frame_reflBar_diagF3_one {m : ℕ} (hm : 4 ≤ m) :
    (∀ i : Fin m, reflBar (diagF3 m 1) (Pi.single i 1) ∈ D3 (diagF3 m 1)) ∧
      Function.Injective (fun i : Fin m => reflBar (diagF3 m 1) (Pi.single i 1)) ∧
      (Pairwise fun i j : Fin m => Commute (reflBar (diagF3 m 1) (Pi.single i 1))
        (reflBar (diagF3 m 1) (Pi.single j 1))) ∧
      (List.ofFn fun i : Fin m => reflBar (diagF3 m 1) (Pi.single i 1)).prod = 1 := by
  have hf : IsF3Form (diagF3 m 1) := isF3Form_diagF3 one_ne_zero
  have hunit : ∀ i : Fin m, diagF3 m 1 (Pi.single i 1) (Pi.single i 1) = 1 := by
    intro i
    rw [ztc_diagF3_one_pair, if_pos rfl]
  have horth : ∀ i j : Fin m, i ≠ j →
      diagF3 m 1 (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro i j hij
    rw [ztc_diagF3_one_pair, if_neg hij]
  have hmem : ∀ i : Fin m, reflBar (diagF3 m 1) (Pi.single i 1) ∈ D3 (diagF3 m 1) :=
    fun i => reflBar_mem_D3 (hunit i)
  have hinj : Function.Injective
      (fun i : Fin m => reflBar (diagF3 m 1) (Pi.single i 1)) := by
    intro i j hij
    by_contra hne
    rcases (reflBar_eq_reflBar_iff hf hm (hunit i) (hunit j)).1 hij with h | h
    · have h0 := congrFun h i
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_same] at h0
      exact one_ne_zero h0.symm
    · have h0 := congrFun h i
      rw [Pi.single_eq_of_ne hne, Pi.neg_apply, Pi.single_eq_same] at h0
      exact absurd h0 (by decide)
  have hcomm : Pairwise fun i j : Fin m =>
      Commute (reflBar (diagF3 m 1) (Pi.single i 1))
        (reflBar (diagF3 m 1) (Pi.single j 1)) := by
    intro i j hij
    exact (reflBar_commute_iff hf hm (hunit i) (hunit j)).2 (Or.inl (horth i j hij))
  have hprod : (List.ofFn fun i : Fin m => reflBar (diagF3 m 1) (Pi.single i 1)).prod = 1 := by
    let g : F3.reflGroup (diagF3 m 1) :=
      (List.ofFn fun i : Fin m => reflElt (diagF3 m 1) (Pi.single i 1)).prod
    have hgc : g ∈ Subgroup.center (F3.reflGroup (diagF3 m 1)) :=
      prod_ofFn_reflElt_single_mem_center m
    have hmap : (List.ofFn fun i : Fin m => reflBar (diagF3 m 1) (Pi.single i 1)).prod =
        (QuotientGroup.mk g : R3 (diagF3 m 1)) := by
      have h := List.prod_hom (List.ofFn fun i : Fin m =>
        reflElt (diagF3 m 1) (Pi.single i 1))
        (QuotientGroup.mk' (Subgroup.center (F3.reflGroup (diagF3 m 1))))
      rw [List.map_ofFn] at h
      simpa [g, reflBar, Function.comp_def] using h
    rw [hmap, QuotientGroup.eq_one_iff]
    exact hgc
  exact ⟨hmem, hinj, hcomm, hprod⟩

@[expose] def ternaryCode {n : ℕ} (v : Fin n → ZMod 3) : ℕ :=
  ∑ i : Fin n, 3 ^ (i : ℕ) * (v i).val

@[expose] def ternaryDecode (n k : ℕ) : Fin n → ZMod 3 :=
  fun i => ((k / 3 ^ (i : ℕ) % 3 : ℕ) : ZMod 3)

private theorem ztc_ternaryCode_succ {n : ℕ} (v : Fin (n + 1) → ZMod 3) :
    ternaryCode v = (v 0).val + 3 * ternaryCode (fun i : Fin n => v i.succ) := by
  simp only [ternaryCode]
  conv_lhs => rw [Fin.sum_univ_succ]
  rw [Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_succ, pow_succ]
    ring

theorem ternaryDecode_ternaryCode {n : ℕ} (v : Fin n → ZMod 3) :
    ternaryDecode n (ternaryCode v) = v := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      rw [ztc_ternaryCode_succ]
      refine Fin.cases ?_ ?_ i
      · have hmod : ((v 0).val + 3 * ternaryCode (fun i : Fin n => v i.succ)) % 3 =
            (v 0).val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt (v 0))]
        simp only [ternaryDecode, Fin.val_zero, pow_zero, Nat.div_one, hmod,
          ZMod.natCast_zmod_val]
      · intro j
        have h3 : ((v 0).val + 3 * ternaryCode (fun i : Fin n => v i.succ)) / 3 =
            ternaryCode (fun i : Fin n => v i.succ) := by
          rw [Nat.add_mul_div_left (v 0).val
            (ternaryCode (fun i : Fin n => v i.succ)) (by norm_num : (0 : ℕ) < 3)]
          rw [Nat.div_eq_of_lt (ZMod.val_lt (v 0))]
          simp
        have hdiv : ((v 0).val + 3 * ternaryCode (fun i : Fin n => v i.succ)) /
            3 ^ ((j : ℕ) + 1) = ternaryCode (fun i : Fin n => v i.succ) / 3 ^ (j : ℕ) := by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_right_comm, h3]
        simp only [ternaryDecode, Fin.val_succ]
        rw [hdiv]
        simpa [ternaryDecode] using congrFun (ih (fun i : Fin n => v i.succ)) j

theorem ternaryCode_lt {n : ℕ} (v : Fin n → ZMod 3) : ternaryCode v < 3 ^ n := by
  induction n with
  | zero => simp [ternaryCode]
  | succ n ih =>
      rw [ztc_ternaryCode_succ, pow_succ]
      have ha : (v 0).val < 3 := ZMod.val_lt _
      have hb : ternaryCode (fun i : Fin n => v i.succ) < 3 ^ n := ih _
      omega

@[expose] def diagDot (m : ℕ) (δ : ZMod 3) (x y : Fin m → ZMod 3) : ZMod 3 :=
  ∑ i, diagF3Entry m δ i * x i * y i

theorem diagF3_eq_diagDot (m : ℕ) (δ : ZMod 3) (x y : Fin m → ZMod 3) :
    diagF3 m δ x y = diagDot m δ x y :=
  diagF3_apply m δ x y

@[expose] def diagNext (m : ℕ) (δ : ZMod 3) (a b : ℕ) : ℕ :=
  ternaryCode (ternaryDecode m a +
    diagDot m δ (ternaryDecode m a) (ternaryDecode m b) • ternaryDecode m b)

@[expose] def diagOk (m : ℕ) (δ : ZMod 3) (_a b : ℕ) : Bool :=
  decide (diagDot m δ (ternaryDecode m b) (ternaryDecode m b) = 1)

theorem eq_top_of_diagChain {m : ℕ} (hm : 4 ≤ m) {δ : ZMod 3} (hδ : δ ≠ 0)
    {H : Subgroup (R3 (diagF3 m δ))} {init : List ℕ} {steps : List (ℕ × ℕ)}
    (hinit : ∀ k ∈ init, reflBar (diagF3 m δ) (ternaryDecode m k) ∈ H)
    (hok : chainOK (diagNext m δ) (diagOk m δ) init steps = true)
    (hcover : ∀ k < 3 ^ m, diagDot m δ (ternaryDecode m k) (ternaryDecode m k) = 1 →
      k ∈ chainLabels (diagNext m δ) init steps) : H = ⊤ := by
  have hf : IsF3Form (diagF3 m δ) := isF3Form_diagF3 hδ
  let τ : ℕ → R3 (diagF3 m δ) := fun k => reflBar (diagF3 m δ) (ternaryDecode m k)
  have hstep : ∀ a b, τ a ∈ H → τ b ∈ H → diagOk m δ a b = true →
      τ (diagNext m δ a b) ∈ H := by
    intro a b ha hb hab
    simp only [diagOk, decide_eq_true_eq] at hab
    have hnb : diagF3 m δ (ternaryDecode m b) (ternaryDecode m b) = 1 := by
      rw [diagF3_eq_diagDot]
      exact hab
    have hact : ternaryDecode m a +
        diagDot m δ (ternaryDecode m a) (ternaryDecode m b) • ternaryDecode m b =
          F3.act (F3.refl (diagF3 m δ) (ternaryDecode m b)) (ternaryDecode m a) := by
      rw [F3.act_refl hnb, diagF3_eq_diagDot]
    have hτnext : τ (diagNext m δ a b) = τ b * τ a * τ b := by
      dsimp only [τ]
      rw [diagNext, ternaryDecode_ternaryCode, hact]
      exact (reflBar_conj hf (ternaryDecode m b) (ternaryDecode m a)).symm
    rw [hτnext]
    exact mul_mem (mul_mem hb ha) hb
  have hmemD : ∀ q ∈ D3 (diagF3 m δ), q ∈ H := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 hq
    let k := ternaryCode v
    have hklt : k < 3 ^ m := ternaryCode_lt v
    have hknorm : diagDot m δ (ternaryDecode m k) (ternaryDecode m k) = 1 := by
      dsimp only [k]
      rw [ternaryDecode_ternaryCode, ← diagF3_eq_diagDot]
      exact hv
    have hklabels : k ∈ chainLabels (diagNext m δ) init steps := hcover k hklt hknorm
    have hτk := mem_of_chainOK H τ (diagNext m δ) (diagOk m δ) hstep steps init hinit hok
      k hklabels
    simpa [τ, k, ternaryDecode_ternaryCode] using hτk
  have hle : Subgroup.closure (D3 (diagF3 m δ)) ≤ H := (Subgroup.closure_le H).2 hmemD
  rw [CFSG.Fischer.Pair.closure_eq (pair_R3 hf hm)] at hle
  exact le_antisymm le_top hle

end CFSG.StandardType.ZS
