module

public import CFSG.OddTranspositions.PartThree.Ten.TenTwoWreath
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
import CFSG.OddTranspositions.PartThree.Ten.SwapBlocks
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.Timmesfeld.Bridge.Asc72WreathConn

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

namespace TenTwoQ

open Equiv SemidirectProduct WreathEndgame

theorem commute_coordHom {f n : ℕ} {k : Fin n} {w : L2Wreath f n} (hk1 : w.left k = 1)
    (hk2 : w.right k = k) (b : PSL2Model f) : Commute (SetupQ.coordHom f n k b) w := by
  show SetupQ.coordHom f n k b * w = w * SetupQ.coordHom f n k b
  rw [SetupQ.coordHom_apply]
  refine SemidirectProduct.ext ?_ (by simp)
  funext p
  rw [WreathClass.mul_left_apply, WreathClass.mul_left_apply, left_inl, right_inl]
  by_cases hp : p = k
  · subst hp
    have hinv : w.right⁻¹ p = p := by
      rw [Perm.inv_def]
      exact (Equiv.symm_apply_eq _).2 hk2.symm
    simp [hk1, hinv, Pi.mulSingle_eq_same]
  · have hinv : w.right⁻¹ p ≠ k := by
      intro h
      apply hp
      have := congrArg w.right h
      simpa [hk2] using this
    rw [Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hinv]
    simp

theorem center_le_coordComm_of_three_le {Hs : Type*} [Group Hs] [Finite Hs] {f n : ℕ}
    (hf : 2 ≤ f) (hn : 3 ≤ n) {E : Set Hs} (hE : IsOddTranspClass E) {q : Hs →* L2Wreath f n}
    (hq : Function.Surjective q) (hker : q.ker = Subgroup.center Hs) (k : Fin n) :
    Subgroup.center Hs ≤ SetupQ.coordComm q k :=
  SetupQ.le_of_le_iSup (SetupQ.coordComm q) k
    (fun _ _ hij _ hx _ hy => SetupQ.commute_of_mem_coordComm q hker hij hx hy)
    (fun _ _ hz hc => SetupQ.mem_center_of_commute q hq hf hker hz hc)
    (fun i => SetupQ.exists_conj_coordComm_le q hq i k)
    (SetupQ.center_le_iSup_coordComm q hq hf hker
      (commutator_comap_base_eq_of_three_le hf hn q hq hker.le hE))

theorem commute_of_mem_coordComm_of_ker_eq {Hs : Type*} [Group Hs] {f n : ℕ}
    {q : Hs →* L2Wreath f n} (hker : q.ker = Subgroup.center Hs) (k : Fin n) {v : Hs}
    (hvk : ∀ b : PSL2Model f, Commute (SetupQ.coordHom f n k b) (q v)) :
    ∀ h ∈ SetupQ.coordComm q k, Commute h v := by
  set U : Subgroup Hs := Subgroup.zpowers v with hU
  have h1 : ⁅SetupQ.coordPre q k, U⁆ ≤ Subgroup.center Hs := by
    rw [Subgroup.commutator_le]
    intro a ha u hu
    obtain ⟨b, hb⟩ := ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement, map_zpow, ← hb]
    exact commutatorElement_eq_one_iff_commute.2 ((hvk b).zpow_right m)
  have h2 : ⁅U, SetupQ.coordPre q k⁆ ≤ Subgroup.center Hs := by
    rw [Subgroup.commutator_comm]
    exact h1
  have h3 : ⁅SetupQ.coordComm q k, U⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact eq_bot_iff.2
        ((Subgroup.commutator_mono_left h1).trans (Subgroup.commutator_center_left _).le)
    · exact eq_bot_iff.2
        ((Subgroup.commutator_mono_left h2).trans (Subgroup.commutator_center_left _).le)
  intro h hh
  have hmem := Subgroup.commutator_mem_commutator hh (Subgroup.mem_zpowers v)
  rw [h3, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_commute.1 hmem

structure WreathCover (Hs : Type*) [Group Hs] (f n : ℕ) (E : Set Hs)
    (q : Hs →* L2Wreath f n) : Prop where
  two_le : 2 ≤ f
  five_le : 5 ≤ n
  surj : Function.Surjective q
  ker_eq : q.ker = Subgroup.center Hs
  isClass : IsOddTranspClass E
  image : q '' E = swapSet f n

namespace WreathCover

variable {Hs : Type*} [Group Hs] {f n : ℕ} {E : Set Hs} {q : Hs →* L2Wreath f n}
  (hW : WreathCover Hs f n E q)
include hW

theorem conj_mem {x : Hs} (hx : x ∈ E) (h : Hs) : h * x * h⁻¹ ∈ E := by
  obtain ⟨⟨d₀, hd₀⟩, -, -⟩ := hW.isClass
  rw [hd₀] at hx ⊢
  exact hx.trans (isConj_iff.2 ⟨h, rfl⟩)

theorem image_mem_swapSet {x : Hs} (hx : x ∈ E) : q x ∈ swapSet f n :=
  hW.image ▸ Set.mem_image_of_mem q hx

theorem exists_lift {s : L2Wreath f n} (hs : s ∈ swapSet f n) : ∃ x ∈ E, q x = s := by
  have : s ∈ q '' E := hW.image ▸ hs
  obtain ⟨x, hx, hxs⟩ := this
  exact ⟨x, hx, hxs⟩

theorem lc {x y : Hs} (hx : x ∈ E) (hy : y ∈ E) (h : Commute (q x) (q y)) : Commute x y := by
  by_contra hnc
  have hodd := hW.isClass.2.1
  have hxx : x * x = 1 := hodd.mul_self_eq_one hx
  have hyy : y * y = 1 := hodd.mul_self_eq_one hy
  have hoddxy : Odd (orderOf (x * y)) := hodd.odd_of_not_commute hx hy hnc
  have hcen : (x * y) ^ 2 ∈ Subgroup.center Hs := by
    rw [← hW.ker_eq, MonoidHom.mem_ker, map_pow, map_mul, h.mul_pow, pow_two (q x),
      pow_two (q y), ← map_mul, ← map_mul, hxx, hyy, map_one, mul_one]
  have h1 : (x * y) ^ 2 = (y * x) ^ 2 := by
    have hc := Subgroup.mem_center_iff.1 hcen x
    calc (x * y) ^ 2 = x⁻¹ * (x * (x * y) ^ 2) := by group
      _ = x⁻¹ * ((x * y) ^ 2 * x) := by rw [hc]
      _ = (y * x) ^ 2 := by simp only [pow_two]; group
  have h2 : (x * y) ^ 4 = 1 := by
    have h3 : (y * x) = (x * y)⁻¹ := by rw [mul_inv_rev, hodd.inv_eq hx, hodd.inv_eq hy]
    have h4 : (x * y) ^ 2 * (x * y) ^ 2 = 1 := by
      calc (x * y) ^ 2 * (x * y) ^ 2 = (x * y) ^ 2 * (y * x) ^ 2 := by rw [← h1]
        _ = 1 := by rw [h3, inv_pow, mul_inv_cancel]
    calc (x * y) ^ 4 = (x * y) ^ 2 * (x * y) ^ 2 := by group
      _ = 1 := h4
  have hdvd : orderOf (x * y) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h2)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hoddxy
    exact (Nat.not_even_iff_odd.2 hoddxy) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  have hxy : x = y := hodd.eq_of_mul_eq_one hx hi
  exact hnc (hxy ▸ Commute.refl x)

theorem center_le_coordComm [Finite Hs] (k : Fin n) :
    Subgroup.center Hs ≤ SetupQ.coordComm q k :=
  center_le_coordComm_of_three_le hW.two_le (by have := hW.five_le; omega) hW.isClass hW.surj
    hW.ker_eq k

theorem commute_of_mem_coordComm (k : Fin n) {v : Hs}
    (hvk : ∀ b : PSL2Model f, Commute (SetupQ.coordHom f n k b) (q v)) :
    ∀ h ∈ SetupQ.coordComm q k, Commute h v :=
  commute_of_mem_coordComm_of_ker_eq hW.ker_eq k hvk

theorem q_eq_one_of_commute {v c : Hs} (hv : v ∈ E) (hsign : Perm.sign (q c).right = 1)
    (hc : ∀ x ∈ E, Commute x v → Commute c x) : q c = 1 := by
  refine eq_one_of_commute_swaps hW.two_le hW.five_le (hW.image_mem_swapSet hv) ?_ hsign
  intro s hs hsv
  obtain ⟨x, hx, rfl⟩ := hW.exists_lift hs
  exact (hc x hx (hW.lc hx hv hsv)).map q

theorem coordComm_le_commutator {Y : Subgroup Hs} {k l : Fin n} (hkl : k ≠ l)
    (hY : ∀ a : PSL2Model f, ∃ y ∈ Y, q y = swp a k l) :
    SetupQ.coordComm q k ≤ ⁅Y, Y⁆ := by
  have hΓ : ∀ a : PSL2Model f, swp a k l ∈ Y.map q := fun a => by
    obtain ⟨y, hy, h⟩ := hY a
    exact ⟨y, hy, h⟩
  have hcoord := coordHom_mem_of_swp_mem hW.two_le hkl (Y.map q) hΓ
  refine SetupQ.commutator_le_of_central_decomp (fun x hx => ?_)
  obtain ⟨b, hb⟩ := hx
  obtain ⟨y, hy, hyb⟩ := hcoord b
  refine ⟨x * y⁻¹, ?_, y, hy, by group⟩
  rw [← hW.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hyb, ← hb, mul_inv_cancel]

theorem exists_over {a b : Fin n} (hab : a ≠ b) : ∃ x ∈ E, (q x).right = swap a b := by
  obtain ⟨x, hx, hxs⟩ := hW.exists_lift (swp_mem (a := (1 : PSL2Model f)) hab)
  exact ⟨x, hx, by rw [hxs, swp_right]⟩

theorem exists_support {x : Hs} (hx : x ∈ E) :
    ∃ a b : Fin n, a ≠ b ∧ (q x).right = swap a b := by
  obtain ⟨a, b, hab, hr, -⟩ := hW.image_mem_swapSet hx
  exact ⟨a, b, hab, hr⟩

theorem commute_of_disjoint {x y : Hs} (hx : x ∈ E) (hy : y ∈ E) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hxr : (q x).right = swap a b) (hyr : (q y).right = swap c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Commute x y := by
  refine hW.lc hx hy (commute_of_disjoint_right (hW.image_mem_swapSet hx)
    (hW.image_mem_swapSet hy) ?_)
  rw [hxr, hyr]
  exact (swapDisjoint_iff hab hcd).2 ⟨hac, had, hbc, hbd⟩

omit hW in
theorem eq_or_disjoint_of_commute {x y : Hs} (hxy : Commute x y) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hxr : (q x).right = swap a b) (hyr : (q y).right = swap c d) :
    swap a b = swap c d ∨ (swap a b).Disjoint (swap c d) := by
  have h := (hxy.map q).map (SemidirectProduct.rightHom : L2Wreath f n →* Perm (Fin n))
  have h' : Commute (q x).right (q y).right := h
  rw [hxr, hyr] at h'
  exact swap_commute_cases hab hcd h'

theorem exists_outside {β : Set Hs}
    (hP : ∀ y ∈ E, y ∉ β → ∀ u ∈ β, Commute y u → ∀ u' ∈ β, Commute y u')
    {v : Hs} (hv : v ∈ β) (hne : ∃ y ∈ E, y ∉ β)
    {i j : Fin n} (hij : i ≠ j) (hvr : (q v).right = swap i j) :
    ∃ x ∈ E, x ∉ β ∧ ∃ k l : Fin n, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
      (q x).right = swap k l := by
  classical
  by_contra hcon
  push Not at hcon
  have claim : ∀ y ∈ E, y ∉ β → ∀ a b : Fin n, a ≠ b → (q y).right = swap a b →
      (a = i ∨ a = j ∨ b = i ∨ b = j) →
      (∀ u ∈ β, Commute y u) ∧ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) := by
    intro y hy hyβ a b hab hyr hmeet
    obtain ⟨k', l', hkl', hk'a, hk'b, hk'i, hk'j, hl'a, hl'b, hl'i, hl'j⟩ :=
      WreathConn.exists_pair_avoid_of_five_le hW.five_le hmeet
    obtain ⟨x₁, hx₁E, hx₁r⟩ := hW.exists_over hkl'
    have hx₁β : x₁ ∈ β := by
      by_contra h
      exact hcon x₁ hx₁E h k' l' hkl' hk'i hk'j hl'i hl'j hx₁r
    have hall := hP y hy hyβ x₁ hx₁β (hW.commute_of_disjoint hy hx₁E hab hkl' hyr hx₁r
      hk'a.symm hl'a.symm hk'b.symm hl'b.symm)
    refine ⟨hall, ?_⟩
    rcases eq_or_disjoint_of_commute (hall v hv) hab hij hyr hvr with h | h
    · exact swap_eq_swap_cases hab hij h
    · exfalso
      obtain ⟨h1, h2, h3, h4⟩ := (swapDisjoint_iff hab hij).1 h
      rcases hmeet with h' | h' | h' | h'
      exacts [h1 h', h2 h', h3 h', h4 h']
  obtain ⟨y, hyE, hyβ⟩ := hne
  obtain ⟨a, b, hab, hyr⟩ := hW.exists_support hyE
  have hmeet : a = i ∨ a = j ∨ b = i ∨ b = j := by
    by_contra hn
    push Not at hn
    exact hcon y hyE hyβ a b hab hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 hyr
  obtain ⟨hallY, hsupp⟩ := claim y hyE hyβ a b hab hyr hmeet
  obtain ⟨m, l₀, -, hmi, hmj, -, -⟩ := exists_two_off hW.five_le i j i
  obtain ⟨x₂, hx₂E, hx₂r⟩ := hW.exists_over hmi.symm
  have hx₂β : x₂ ∈ β := by
    by_contra h
    obtain ⟨-, hs⟩ := claim x₂ hx₂E h i m hmi.symm hx₂r (Or.inl rfl)
    rcases hs with ⟨-, hmj'⟩ | ⟨hij', -⟩
    · exact hmj hmj'
    · exact hij hij'
  rcases eq_or_disjoint_of_commute (hallY x₂ hx₂β) hab hmi.symm hyr hx₂r with h | h
  · rcases swap_eq_swap_cases hab hmi.symm h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hsupp with ⟨h3, h4⟩ | ⟨h3, h4⟩
    exacts [hmj (h2.symm.trans h4), hij (h1.symm.trans h3), hmi (h1.symm.trans h3),
      hmj (h1.symm.trans h3)]
  · obtain ⟨h1, h2, h3, h4⟩ := (swapDisjoint_iff hab hmi.symm).1 h
    rcases hsupp with ⟨h5, -⟩ | ⟨-, h5⟩
    exacts [h1 h5, h3 h5]

theorem center_le_commutator [Finite Hs] {β : Set Hs}
    (hP : ∀ y ∈ E, y ∉ β → ∀ u ∈ β, Commute y u → ∀ u' ∈ β, Commute y u')
    {v : Hs} (hv : v ∈ β) (hvE : v ∈ E)
    (hB : ∀ h : Hs, Commute h v → ∀ y : Hs, h * y * h⁻¹ ∈ β ↔ y ∈ β)
    (hne : ∃ y ∈ E, y ∉ β) :
    Subgroup.center Hs ≤ ⁅Subgroup.closure {y | y ∈ E ∧ y ∉ β ∧ Commute y v},
      Subgroup.closure {y | y ∈ E ∧ y ∉ β ∧ Commute y v}⁆ := by
  classical
  set X : Set Hs := {y | y ∈ E ∧ y ∉ β ∧ Commute y v} with hX
  obtain ⟨i, j, hij, hvr, hvl, -⟩ := hW.image_mem_swapSet hvE
  obtain ⟨x₀, hx₀E, hx₀β, k, l, hkl, hki, hkj, hli, hlj, hx₀r⟩ :=
    hW.exists_outside hP hv hne hij hvr
  have hx₀S := hW.image_mem_swapSet hx₀E
  have hx₀v : Commute x₀ v :=
    hW.commute_of_disjoint hx₀E hvE hkl hij hx₀r hvr hki hkj hli hlj
  have hvk : ∀ b : PSL2Model f, Commute (SetupQ.coordHom f n k b) (q v) := fun b =>
    commute_coordHom (hvl k hki hkj) (by rw [hvr, swap_apply_of_ne_of_ne hki hkj]) b
  have hq : ∀ a : PSL2Model f, ∃ y ∈ Subgroup.closure X, q y = swp a k l := by
    intro a
    obtain ⟨a₀, hx₀eq⟩ : ∃ a₀, q x₀ = swp a₀ k l := ⟨_, eq_swp_of_right_eq hx₀S hkl hx₀r⟩
    obtain ⟨h, hh, hhq⟩ : ∃ h ∈ SetupQ.coordComm q k,
        q h = SetupQ.coordHom f n k (a * a₀⁻¹) := by
      have : SetupQ.coordHom f n k (a * a₀⁻¹) ∈
          (SetupQ.coordComm q k).map q := by
        rw [SetupQ.map_coordComm q hW.surj hW.two_le k]
        exact ⟨_, rfl⟩
      obtain ⟨h, hh, hhq⟩ := this
      exact ⟨h, hh, hhq⟩
    have hhv : Commute h v := hW.commute_of_mem_coordComm k hvk h hh
    refine ⟨h * x₀ * h⁻¹, Subgroup.subset_closure ⟨hW.conj_mem hx₀E h, ?_, ?_⟩, ?_⟩
    · rw [hB h hhv]
      exact hx₀β
    · exact (hhv.mul_left hx₀v).mul_left hhv.inv_left
    · rw [map_mul, map_mul, map_inv, hhq, hx₀eq, SetupQ.coordHom_apply,
        SwapBlocks.inl_conj_swp _ _ hkl]
      congr 1
      simp [Pi.mulSingle_eq_of_ne hkl.symm]
  exact (hW.center_le_coordComm k).trans (hW.coordComm_le_commutator hkl hq)

end WreathCover

end TenTwoQ

end CFSG.OddTranspositions.PartThree

end
