module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47CoordDefs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped commutatorElement

variable {G : Type} [Group G]

private theorem s16c1_G47_additive_matrix (F : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))
    (hF : ∀ y y', F (y + y') = F y + F y') :
    ∃ S : Matrix (Fin 4) (Fin 4) (ZMod 2), ∀ y, F y = S.mulVec y := by
  let f : (Fin 4 → ZMod 2) →+ (Fin 4 → ZMod 2) := AddMonoidHom.mk' F hF
  refine ⟨LinearMap.toMatrix' (f.toZModLinearMap 2), fun y => ?_⟩
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

private lemma s16c1_G47_add_three {K U B N : Subgroup G} {κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2)}
    (hκ : G47Coord K U B N κ) {a b c : G} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    κ (a * b * c) = κ a + κ b + κ c := by
  rw [hκ.add (a * b) (K.mul_mem ha hb) c hc, hκ.add a ha b hb]

private lemma s16c1_G47_commutator_mul (w a b : G) :
    ⁅w, a * b⁆ = ⁅w, a⁆ * ⁅a, ⁅w, b⁆⁆ * ⁅w, b⁆ := by
  simp only [commutatorElement_def]
  group

private lemma s16c1_G47_g47Up_mulVec (S : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (x y : Fin 4 → ZMod 2) :
    (g47Up S).mulVec (Sum.elim x y) = Sum.elim (x + S.mulVec y) y := by
  rw [g47Up, Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  funext s; rcases s with i | i <;> simp

private lemma s16c1_G47_g47Lo_mulVec (T : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (x y : Fin 4 → ZMod 2) :
    (g47Lo T).mulVec (Sum.elim x y) = Sum.elim x (y + T.mulVec x) := by
  rw [g47Lo, Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  funext s; rcases s with i | i <;> simp [add_comm]

theorem s16c1_G47_siegel_left {K U B N : Subgroup G} {κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2)}
    (hκ : G47Coord K U B N κ) (hUK : U ≤ K) (hBK : B ≤ K) (hN : N = U ⊓ B)
    (hKUB : ∀ k ∈ K, ∃ u ∈ U, ∃ b ∈ B, k = u * b) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hBsq : ∀ x ∈ B, x * x = 1) {w : G} (hwU : ∀ u ∈ U, w * u * w⁻¹ = u)
    (hwB : ∀ b ∈ B, ⁅w, b⁆ ∈ U) :
    ∃ S : Matrix (Fin 4) (Fin 4) (ZMod 2), (∀ y : Fin 4 → ZMod 2, dotProduct (S.mulVec y) y = 0) ∧
      ∀ k ∈ K, w * k * w⁻¹ ∈ K ∧
        κ (w * k * w⁻¹) = (g47Up S).mulVec (κ k) := by
  have hNK : N ≤ K := by rw [hN]; exact inf_le_left.trans hUK
  have hNU : N ≤ U := by rw [hN]; exact inf_le_left
  have h1K : (1 : G) ∈ K := K.one_mem
  have hκ1 : κ 1 = 0 := (hκ.eq_zero_iff 1 h1K).2 N.one_mem
  have hκinv : ∀ k ∈ K, κ k⁻¹ = -κ k := by
    intro k hk
    have h := hκ.add k hk k⁻¹ (K.inv_mem hk)
    rw [mul_inv_cancel, hκ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hcb_conj : ∀ b ∈ B, w * b * w⁻¹ = ⁅w, b⁆ * b := by
    intro b _
    rw [commutatorElement_def]
    group
  let fb : G → (Fin 4 → ZMod 2) := fun b i => κ ⁅w, b⁆ (Sum.inl i)
  have hfbadd : ∀ b ∈ B, ∀ b' ∈ B, fb (b * b') = fb b + fb b' := by
    intro b hb b' hb'
    have hbK : b ∈ K := hBK hb
    have hcbK : ⁅w, b⁆ ∈ K := hUK (hwB b hb)
    have hcb'K : ⁅w, b'⁆ ∈ K := hUK (hwB b' hb')
    have hcommK : ⁅b, ⁅w, b'⁆⁆ ∈ K := hNK (hKcomm b hbK ⁅w, b'⁆ hcb'K)
    have hκcm : κ ⁅w, b * b'⁆ = κ ⁅w, b⁆ + κ ⁅b, ⁅w, b'⁆⁆ + κ ⁅w, b'⁆ := by
      rw [s16c1_G47_commutator_mul, s16c1_G47_add_three hκ hcbK hcommK hcb'K]
    have hz : κ ⁅b, ⁅w, b'⁆⁆ = 0 :=
      (hκ.eq_zero_iff ⁅b, ⁅w, b'⁆⁆ hcommK).2 (hKcomm b hbK ⁅w, b'⁆ hcb'K)
    have hsum : κ ⁅w, b * b'⁆ = κ ⁅w, b⁆ + κ ⁅w, b'⁆ := by
      rw [hκcm, hz, add_zero]
    funext i
    exact congrFun hsum (Sum.inl i)
  have hfb_dep : ∀ b ∈ B, ∀ b' ∈ B, κ b = κ b' → fb b = fb b' := by
    intro b hb b' hb' heq
    have hnN : b' * b⁻¹ ∈ N := by
      rw [← hκ.eq_zero_iff (b' * b⁻¹) (hBK (B.mul_mem hb' (B.inv_mem hb)))]
      rw [hκ.add b' (hBK hb') b⁻¹ (hBK (B.inv_mem hb)), hκinv b (hBK hb), heq]
      exact add_neg_cancel _
    have hnu : b' * b⁻¹ ∈ U := hNU hnN
    have hnb : b' = (b' * b⁻¹) * b := by group
    have hzero : fb (b' * b⁻¹) = 0 := by
      funext i
      have hcomm : w * (b' * b⁻¹) = (b' * b⁻¹) * w := by
        calc w * (b' * b⁻¹) = w * (b' * b⁻¹) * w⁻¹ * w := by group
          _ = (b' * b⁻¹) * w := by rw [hwU (b' * b⁻¹) hnu]
      have h1 : ⁅w, b' * b⁻¹⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).2 hcomm
      show κ ⁅w, b' * b⁻¹⁆ (Sum.inl i) = 0
      rw [h1, hκ1]
      rfl
    have hcalc : fb b' = fb b := by
      calc fb b' = fb ((b' * b⁻¹) * b) := congrArg fb hnb
        _ = fb (b' * b⁻¹) + fb b := hfbadd (b' * b⁻¹) (B.mul_mem hb' (B.inv_mem hb)) b hb
        _ = fb b := by rw [hzero, zero_add]
    exact hcalc.symm
  choose bs hbsB hbsκ using hκ.right_surj
  let F : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun y => fb (bs y)
  have hF : ∀ y y', F (y + y') = F y + F y' := by
    intro y y'
    show fb (bs (y + y')) = fb (bs y) + fb (bs y')
    have h1 : κ (bs (y + y')) = κ (bs y * bs y') := by
      rw [hbsκ (y + y'), hκ.add (bs y) (hBK (hbsB y)) (bs y') (hBK (hbsB y')),
        hbsκ y, hbsκ y']
      funext s; rcases s with i | i <;> simp
    rw [hfb_dep (bs (y + y')) (hbsB _) (bs y * bs y')
      (B.mul_mem (hbsB y) (hbsB y')) h1]
    exact hfbadd (bs y) (hbsB y) (bs y') (hbsB y')
  obtain ⟨S, hS⟩ := s16c1_G47_additive_matrix F hF
  have hkey : ∀ b ∈ B, fb b = S.mulVec (fun i => κ b (Sum.inr i)) := by
    intro b hb
    have hbκ : κ b = Sum.elim (0 : Fin 4 → ZMod 2) (fun i => κ b (Sum.inr i)) := by
      funext s; rcases s with i | i <;> simp [hκ.left_of_B b hb i]
    have heq : κ b = κ (bs (fun i => κ b (Sum.inr i))) :=
      hbκ.trans (hbsκ (fun i => κ b (Sum.inr i))).symm
    rw [hfb_dep b hb (bs (fun i => κ b (Sum.inr i))) (hbsB _) heq]
    exact hS _
  have hact : ∀ k ∈ K, w * k * w⁻¹ ∈ K ∧
      κ (w * k * w⁻¹) = (g47Up S).mulVec (κ k) := by
    intro k hk
    obtain ⟨u, hu, b, hb, rfl⟩ := hKUB k hk
    have hconj : w * (u * b) * w⁻¹ = u * ⁅w, b⁆ * b := by
      calc w * (u * b) * w⁻¹ = (w * u * w⁻¹) * (w * b * w⁻¹) := by group
        _ = u * ⁅w, b⁆ * b := by rw [hwU u hu, hcb_conj b hb, ← mul_assoc]
    let x : Fin 4 → ZMod 2 := fun i => κ u (Sum.inl i)
    let y : Fin 4 → ZMod 2 := fun i => κ b (Sum.inr i)
    have hx : κ u = Sum.elim x (0 : Fin 4 → ZMod 2) := by
      funext s; rcases s with i | i <;> simp [x, hκ.right_of_U u hu i]
    have hy : κ b = Sum.elim (0 : Fin 4 → ZMod 2) y := by
      funext s; rcases s with i | i <;> simp [y, hκ.left_of_B b hb i]
    have hcu : κ ⁅w, b⁆ = Sum.elim (fb b) (0 : Fin 4 → ZMod 2) := by
      funext s; rcases s with i | i <;> simp [fb, hκ.right_of_U ⁅w, b⁆ (hwB b hb) i]
    have hkeyy : fb b = S.mulVec y := hkey b hb
    have hκk : κ (u * b) = Sum.elim x y := by
      rw [hκ.add u (hUK hu) b (hBK hb), hx, hy]
      funext s; rcases s with i | i <;> simp [x, y]
    have hκact : κ (w * (u * b) * w⁻¹) = Sum.elim (x + S.mulVec y) y := by
      rw [hconj, s16c1_G47_add_three hκ (hUK hu) (hUK (hwB b hb)) (hBK hb),
        hx, hcu, hkeyy, hy]
      funext s; rcases s with i | i <;> simp [Pi.add_apply]
    refine ⟨?_, ?_⟩
    · rw [hconj]
      exact K.mul_mem (K.mul_mem (hUK hu) (hUK (hwB b hb))) (hBK hb)
    · rw [hκact, hκk, s16c1_G47_g47Up_mulVec]
  refine ⟨S, ?_, hact⟩
  intro y
  have hb : bs y ∈ B := hbsB y
  have hsq : (w * bs y * w⁻¹) * (w * bs y * w⁻¹) = 1 := by
    calc (w * bs y * w⁻¹) * (w * bs y * w⁻¹) = w * (bs y * bs y) * w⁻¹ := by group
      _ = 1 := by rw [hBsq (bs y) hb]; group
  have hk'coord : κ (w * bs y * w⁻¹) = Sum.elim (S.mulVec y) y := by
    rw [(hact (bs y) (hBK hb)).2, hbsκ y, s16c1_G47_g47Up_mulVec]
    funext s; rcases s with i | i <;> simp
  have hdot := (hκ.sq_iff (w * bs y * w⁻¹) (hact (bs y) (hBK hb)).1).1 hsq
  rw [hk'coord] at hdot
  simpa using hdot

theorem s16c1_G47_siegel_right {K U B N : Subgroup G} {κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2)}
    (hκ : G47Coord K U B N κ) (hUK : U ≤ K) (hBK : B ≤ K) (hN : N = U ⊓ B)
    (hKUB : ∀ k ∈ K, ∃ u ∈ U, ∃ b ∈ B, k = u * b) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hUsq : ∀ x ∈ U, x * x = 1) {w' : G} (hwB : ∀ b ∈ B, w' * b * w'⁻¹ = b)
    (hwU : ∀ u ∈ U, ⁅w', u⁆ ∈ B) :
    ∃ T : Matrix (Fin 4) (Fin 4) (ZMod 2), (∀ x : Fin 4 → ZMod 2, dotProduct (T.mulVec x) x = 0) ∧
      ∀ k ∈ K, w' * k * w'⁻¹ ∈ K ∧
        κ (w' * k * w'⁻¹) = (g47Lo T).mulVec (κ k) := by
  have hNK : N ≤ K := by rw [hN]; exact inf_le_left.trans hUK
  have hNB : N ≤ B := by rw [hN]; exact inf_le_right
  have h1K : (1 : G) ∈ K := K.one_mem
  have hκ1 : κ 1 = 0 := (hκ.eq_zero_iff 1 h1K).2 N.one_mem
  have hκinv : ∀ k ∈ K, κ k⁻¹ = -κ k := by
    intro k hk
    have h := hκ.add k hk k⁻¹ (K.inv_mem hk)
    rw [mul_inv_cancel, hκ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hcu_conj : ∀ u ∈ U, w' * u * w'⁻¹ = ⁅w', u⁆ * u := by
    intro u _
    rw [commutatorElement_def]
    group
  let fu : G → (Fin 4 → ZMod 2) := fun u i => κ ⁅w', u⁆ (Sum.inr i)
  have hfu : ∀ u ∈ U, κ ⁅w', u⁆ = Sum.elim (0 : Fin 4 → ZMod 2) (fu u) := by
    intro u hu
    funext s; rcases s with i | i <;> simp [fu, hκ.left_of_B ⁅w', u⁆ (hwU u hu) i]
  have hfuadd : ∀ u ∈ U, ∀ u' ∈ U, fu (u * u') = fu u + fu u' := by
    intro u hu u' hu'
    have huK : u ∈ K := hUK hu
    have hcuK : ⁅w', u⁆ ∈ K := hBK (hwU u hu)
    have hcu'K : ⁅w', u'⁆ ∈ K := hBK (hwU u' hu')
    have hcommK : ⁅u, ⁅w', u'⁆⁆ ∈ K := hNK (hKcomm u huK ⁅w', u'⁆ hcu'K)
    have hκcm : κ ⁅w', u * u'⁆ = κ ⁅w', u⁆ + κ ⁅u, ⁅w', u'⁆⁆ + κ ⁅w', u'⁆ := by
      rw [s16c1_G47_commutator_mul, s16c1_G47_add_three hκ hcuK hcommK hcu'K]
    have hz : κ ⁅u, ⁅w', u'⁆⁆ = 0 :=
      (hκ.eq_zero_iff ⁅u, ⁅w', u'⁆⁆ hcommK).2 (hKcomm u huK ⁅w', u'⁆ hcu'K)
    have hsum : κ ⁅w', u * u'⁆ = κ ⁅w', u⁆ + κ ⁅w', u'⁆ := by
      rw [hκcm, hz, add_zero]
    funext i
    exact congrFun hsum (Sum.inr i)
  have hfu_dep : ∀ u ∈ U, ∀ u' ∈ U, κ u = κ u' → fu u = fu u' := by
    intro u hu u' hu' heq
    have hnN : u' * u⁻¹ ∈ N := by
      rw [← hκ.eq_zero_iff (u' * u⁻¹) (hUK (U.mul_mem hu' (U.inv_mem hu)))]
      rw [hκ.add u' (hUK hu') u⁻¹ (hUK (U.inv_mem hu)), hκinv u (hUK hu), heq]
      exact add_neg_cancel _
    have hnu : u' * u⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem hu)
    have hnB : u' * u⁻¹ ∈ B := hNB hnN
    have hnu' : u' = (u' * u⁻¹) * u := by group
    have hzero : fu (u' * u⁻¹) = 0 := by
      funext i
      have hcomm : w' * (u' * u⁻¹) = (u' * u⁻¹) * w' := by
        calc w' * (u' * u⁻¹) = w' * (u' * u⁻¹) * w'⁻¹ * w' := by group
          _ = (u' * u⁻¹) * w' := by rw [hwB (u' * u⁻¹) hnB]
      have h1 : ⁅w', u' * u⁻¹⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).2 hcomm
      show κ ⁅w', u' * u⁻¹⁆ (Sum.inr i) = 0
      rw [h1, hκ1]
      rfl
    have hcalc : fu u' = fu u := by
      calc fu u' = fu ((u' * u⁻¹) * u) := congrArg fu hnu'
        _ = fu (u' * u⁻¹) + fu u := hfuadd (u' * u⁻¹) hnu u hu
        _ = fu u := by rw [hzero, zero_add]
    exact hcalc.symm
  choose us husU husκ using hκ.left_surj
  let Gm : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun x => fu (us x)
  have hGm : ∀ x x', Gm (x + x') = Gm x + Gm x' := by
    intro x x'
    show fu (us (x + x')) = fu (us x) + fu (us x')
    have h1 : κ (us (x + x')) = κ (us x * us x') := by
      rw [husκ (x + x'), hκ.add (us x) (hUK (husU x)) (us x') (hUK (husU x')),
        husκ x, husκ x']
      funext s; rcases s with i | i <;> simp
    rw [hfu_dep (us (x + x')) (husU _) (us x * us x')
      (U.mul_mem (husU x) (husU x')) h1]
    exact hfuadd (us x) (husU x) (us x') (husU x')
  obtain ⟨T, hT⟩ := s16c1_G47_additive_matrix Gm hGm
  have hkey : ∀ u ∈ U, fu u = T.mulVec (fun i => κ u (Sum.inl i)) := by
    intro u hu
    have huκ : κ u = Sum.elim (fun i => κ u (Sum.inl i)) (0 : Fin 4 → ZMod 2) := by
      funext s; rcases s with i | i <;> simp [hκ.right_of_U u hu i]
    have heq : κ u = κ (us (fun i => κ u (Sum.inl i))) :=
      huκ.trans (husκ (fun i => κ u (Sum.inl i))).symm
    rw [hfu_dep u hu (us (fun i => κ u (Sum.inl i))) (husU _) heq]
    exact hT _
  have hact : ∀ k ∈ K, w' * k * w'⁻¹ ∈ K ∧
      κ (w' * k * w'⁻¹) = (g47Lo T).mulVec (κ k) := by
    intro k hk
    obtain ⟨u, hu, b, hb, rfl⟩ := hKUB k hk
    have hconj : w' * (u * b) * w'⁻¹ = ⁅w', u⁆ * u * b := by
      calc w' * (u * b) * w'⁻¹ = (w' * u * w'⁻¹) * (w' * b * w'⁻¹) := by group
        _ = ⁅w', u⁆ * u * b := by rw [hcu_conj u hu, hwB b hb]
    let x : Fin 4 → ZMod 2 := fun i => κ u (Sum.inl i)
    let y : Fin 4 → ZMod 2 := fun i => κ b (Sum.inr i)
    have hx : κ u = Sum.elim x (0 : Fin 4 → ZMod 2) := by
      funext s; rcases s with i | i <;> simp [x, hκ.right_of_U u hu i]
    have hy : κ b = Sum.elim (0 : Fin 4 → ZMod 2) y := by
      funext s; rcases s with i | i <;> simp [y, hκ.left_of_B b hb i]
    have hcu : κ ⁅w', u⁆ = Sum.elim (0 : Fin 4 → ZMod 2) (fu u) := hfu u hu
    have hkeyy : fu u = T.mulVec x := hkey u hu
    have hκk : κ (u * b) = Sum.elim x y := by
      rw [hκ.add u (hUK hu) b (hBK hb), hx, hy]
      funext s; rcases s with i | i <;> simp [x, y]
    have hκact : κ (w' * (u * b) * w'⁻¹) = Sum.elim x (y + T.mulVec x) := by
      rw [hconj, s16c1_G47_add_three hκ (hBK (hwU u hu)) (hUK hu) (hBK hb),
        hcu, hkeyy, hx, hy]
      funext s; rcases s with i | i <;> simp [Pi.add_apply, add_comm, add_left_comm, add_assoc]
    refine ⟨?_, ?_⟩
    · rw [hconj]
      exact K.mul_mem (K.mul_mem (hBK (hwU u hu)) (hUK hu)) (hBK hb)
    · rw [hκact, hκk, s16c1_G47_g47Lo_mulVec]
  refine ⟨T, ?_, hact⟩
  intro x
  have hu : us x ∈ U := husU x
  have hsq : (w' * us x * w'⁻¹) * (w' * us x * w'⁻¹) = 1 := by
    calc (w' * us x * w'⁻¹) * (w' * us x * w'⁻¹) = w' * (us x * us x) * w'⁻¹ := by group
      _ = 1 := by rw [hUsq (us x) hu]; group
  have hk'coord : κ (w' * us x * w'⁻¹) = Sum.elim x (T.mulVec x) := by
    rw [(hact (us x) (hUK hu)).2, husκ x, s16c1_G47_g47Lo_mulVec]
    funext s; rcases s with i | i <;> simp
  have hdot := (hκ.sq_iff (w' * us x * w'⁻¹) (hact (us x) (hUK hu)).1).1 hsq
  rw [hk'coord] at hdot
  rw [dotProduct_comm]
  simpa using hdot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
