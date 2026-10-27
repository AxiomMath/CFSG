module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCfg

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

namespace WStr

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

section Commutator

variable (S : Setting G M X n)
include S

theorem commutator_WX_normalized {m : G} (hm : m ∈ M) {z : G} (hz : z ∈ ⁅blockU X, X⁆) :
    m * z * m⁻¹ ∈ ⁅blockU X, X⁆ := by
  have hW := Setting.map_conj_eq_of_normalized (H := blockU X) (m := m)
    (fun x hx => S.W_normalized hm hx) (fun x hx => S.W_normalized (M.inv_mem hm) hx)
  have hX := Setting.map_conj_eq_of_normalized (H := X) (m := m)
    (fun x hx => S.normal hm hx) (fun x hx => S.normal (M.inv_mem hm) hx)
  have h : (⁅blockU X, X⁆).map (MulAut.conj m).toMonoidHom = ⁅blockU X, X⁆ := by
    rw [Subgroup.map_commutator, hW, hX]
  rw [← h]
  exact ⟨z, hz, rfl⟩

theorem commutator_W_eq : ⁅blockU X, X⁆ = blockU X := by
  have hS := S.block.1
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro w hw x hx
    rw [commutatorElement_def]
    have h1 := S.W_normalized (S.le hx) ((blockU X).inv_mem hw)
    have e : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
    rw [e]
    exact (blockU X).mul_mem hw h1
  · have hY : ∀ x ∈ X, ∀ y ∈ CFSG.Open.pCoreOf 2 X, x * y * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
      fun x hx y hy => CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized X hx hy
    have hN0 : ∀ x ∈ X, ∀ z ∈ ⁅blockU X, X⁆, x * z * x⁻¹ ∈ ⁅blockU X, X⁆ :=
      fun x hx z hz => commutator_WX_normalized S (S.le hx) hz
    have hcomm : ∀ x ∈ X, ∀ y ∈ CFSG.Open.pCoreOf 2 X, ⁅x, y⁆ ∈ blockU X := by
      intro x hx y hy
      have h1 : ⁅y, x⁆ ∈ ⁅blockQ X, X⁆ := Subgroup.commutator_mem_commutator hy hx
      rw [← commutatorElement_inv]
      exact (blockU X).inv_mem h1
    have hsq : ∀ w ∈ blockU X, w * w = 1 := fun w hw => by
      have := S.elemU.2 w hw
      rwa [pow_two] at this
    let N : Subgroup ↥X :=
      { carrier := {x | ∀ y ∈ CFSG.Open.pCoreOf 2 X, ⁅(x : G), y⁆ ∈ ⁅blockU X, X⁆}
        one_mem' := by
          intro y hy
          simp
        mul_mem' := by
          intro a b ha hb y hy
          have e : ⁅((a * b : ↥X) : G), y⁆ = (a : G) * ⁅(b : G), y⁆ * (a : G)⁻¹ * ⁅(a : G), y⁆ := by
            simp only [commutatorElement_def, Subgroup.coe_mul]; group
          rw [e]
          exact (⁅blockU X, X⁆).mul_mem (hN0 a a.2 _ (hb y hy)) (ha y hy)
        inv_mem' := by
          intro a ha y hy
          have e : ⁅((a⁻¹ : ↥X) : G), y⁆ =
              ((a⁻¹ : ↥X) : G) * ⁅(a : G), y⁆⁻¹ * ((a⁻¹ : ↥X) : G)⁻¹ := by
            simp only [commutatorElement_def, Subgroup.coe_inv]; group
          rw [e]
          exact hN0 _ (a⁻¹).2 _ ((⁅blockU X, X⁆).inv_mem (ha y hy)) }
    haveI hNn : N.Normal := ⟨by
      intro a ha g y hy
      have e : ⁅((g * a * g⁻¹ : ↥X) : G), y⁆ =
          (g : G) * ⁅(a : G), ((g⁻¹ : ↥X) : G) * y * ((g⁻¹ : ↥X) : G)⁻¹⁆ * (g : G)⁻¹ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]
      exact hN0 g g.2 _ (ha _ (hY _ (g⁻¹).2 y hy))⟩
    have hsqN : ∀ x : ↥X, x * x ∈ N := by
      intro x y hy
      have hw : ⁅(x : G), y⁆ ∈ blockU X := hcomm x x.2 y hy
      have e : ⁅((x * x : ↥X) : G), y⁆ =
          ⁅(x : G), ⁅(x : G), y⁆⁆ * (⁅(x : G), y⁆ * ⁅(x : G), y⁆) := by
        simp only [commutatorElement_def, Subgroup.coe_mul]; group
      rw [e, hsq _ hw, mul_one, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator x.2 hw
    have hpg : IsPGroup 2 (↥X ⧸ N) := by
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨1, ?_⟩
      rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hsqN x
    have hNtop : N = ⊤ := hS.eq_twoResidual N hpg
    refine (Subgroup.commutator_le (H₁ := blockQ X) (H₂ := X) (H₃ := ⁅blockU X, X⁆)).2 ?_
    intro y hy x hx
    have hx' : (⟨x, hx⟩ : ↥X) ∈ N := hNtop ▸ Subgroup.mem_top _
    have h2 := hx' y hy
    rw [← commutatorElement_inv]
    exact (⁅blockU X, X⁆).inv_mem h2

end Commutator

section Basics

variable (C : Cfg G M X n)

@[expose] def act (m : ↥M) : MulAut ↥(blockU X) where
  toFun u := ⟨(m : G) * u * (m : G)⁻¹, C.S.W_normalized m.2 u.2⟩
  invFun u := ⟨(m : G)⁻¹ * u * ((m : G)⁻¹)⁻¹, C.S.W_normalized (M.inv_mem m.2) u.2⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' u v := by ext; simp [mul_assoc]

theorem act_coe (m : ↥M) (u : ↥(blockU X)) :
    ((act C m u : ↥(blockU X)) : G) = m * u * (m : G)⁻¹ := rfl

@[expose] def actHom : ↥M →* MulAut ↥(blockU X) where
  toFun := act C
  map_one' := MulEquiv.ext fun u => by ext; simp [act_coe]
  map_mul' m m' := MulEquiv.ext fun u => by
    ext; simp [MulAut.mul_apply, act_coe, mul_assoc]

@[expose] def inclX : ↥X →* ↥M := Subgroup.inclusion C.S.le

@[expose] def actX : ↥X →* MulAut ↥(blockU X) := (actHom C).comp (inclX C)

theorem actX_coe (x : ↥X) (u : ↥(blockU X)) :
    ((actX C x u : ↥(blockU X)) : G) = x * u * (x : G)⁻¹ := rfl

abbrev pm (x : ↥X) : Perm (Fin n) := (C.α x : Perm (Fin n))

theorem pm_mul (x y : ↥X) : pm C (x * y) = pm C x * pm C y := by simp [pm]

theorem pm_inv (x : ↥X) : pm C x⁻¹ = (pm C x)⁻¹ := by simp [pm]

theorem exists_lift {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    ∃ x : ↥X, pm C x = σ := by
  obtain ⟨x, hx⟩ := C.α_surj ⟨σ, hσ⟩
  exact ⟨x, by simp [pm, hx]⟩

theorem theta_inclX (x : ↥X) : C.θ (inclX C x) = pm C x := C.θ_X x

theorem α_eq_one_of_pm_eq_one {x : ↥X} (h : pm C x = 1) : C.α x = 1 := Subtype.ext h

@[expose] def bet (u : ↥(blockU X)) : altHeart n := Multiplicative.toAdd (C.β u)

theorem bet_mul (u v : ↥(blockU X)) : bet C (u * v) = bet C u + bet C v := by simp [bet]

theorem bet_one : bet C (1 : ↥(blockU X)) = 0 := by simp [bet]

theorem bet_inv (u : ↥(blockU X)) : bet C u⁻¹ = - bet C u := by simp [bet]

theorem bet_act (m : ↥M) (u : ↥(blockU X)) :
    bet C (act C m u) = altAct (C.θ m) (bet C u) :=
  C.θ_spec m u (act C m u) rfl

theorem bet_actX (x : ↥X) (u : ↥(blockU X)) :
    bet C (actX C x u) = altAct (pm C x) (bet C u) := by
  have h := bet_act C (inclX C x) u
  rw [theta_inclX] at h
  exact h

theorem bet_eq_zero_iff (u : ↥(blockU X)) : bet C u = 0 ↔ (u : G) ∈ blockZ X := by
  rw [bet, toAdd_eq_zero, ← MonoidHom.mem_ker, C.β_ker, Subgroup.mem_subgroupOf]

theorem actX_eq_of_bet_eq_zero (x : ↥X) {u : ↥(blockU X)} (hu : bet C u = 0) :
    actX C x u = u := by
  have hz : (u : G) ∈ blockZ X := (bet_eq_zero_iff C u).1 hu
  have hc : (u : G) ∈ Subgroup.centralizer (X : Set G) := hz.2
  have h := Subgroup.mem_centralizer_iff.1 hc x x.2
  apply Subtype.ext
  rw [actX_coe, h]
  group

theorem actX_eq_of_α_eq_one (y : ↥X) (hy : C.α y = 1) (u : ↥(blockU X)) : actX C y u = u := by
  have hyk : y ∈ C.α.ker := hy
  rw [C.α_ker] at hyk
  have hyQ : (y : G) ∈ blockQ X := ⟨y, hyk, rfl⟩
  have hu := C.S.block.1.blockU_le_center u.2
  have hc := Subgroup.mem_centralizer_iff.1 hu.2 (y : G) hyQ
  apply Subtype.ext
  rw [actX_coe, hc]
  group

theorem W_sq (S : Setting G M X n) (u : ↥(blockU X)) : u * u = 1 := by
  apply Subtype.ext
  have := S.elemU.2 u u.2
  simpa [pow_two] using this

end Basics

section Trick

open scoped IsMulCommutative in
theorem three_cycle_trick {Γ W : Type*} [Group Γ] [Group W] [IsMulCommutative W]
    (hW : ∀ w : W, w * w = 1) (ρ : Γ →* MulAut W) (x c : Γ) (u χ : W)
    (hy : ∀ w, ρ (c * x * c * x⁻¹) w = w)
    (hχ : ρ x u = u * χ) (hχc : ρ c χ = χ) (hχc' : ρ c⁻¹ χ = χ)
    (hs : ρ x (u * ρ c u * ρ c⁻¹ u) = u * ρ c u * ρ c⁻¹ u) : χ = 1 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = c * x * c * x⁻¹ := ⟨_, rfl⟩
  rw [← hy₀] at hy
  have hy' : ∀ w, ρ y₀⁻¹ w = w := by
    intro w
    have h := hy (ρ y₀⁻¹ w)
    have h2 : ρ y₀ (ρ y₀⁻¹ w) = w := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [h2] at h
    exact h.symm
  have h1 : ρ x (ρ c u) = ρ c⁻¹ u * χ := by
    have e : x * c = c⁻¹ * y₀ * x := by rw [hy₀]; group
    have e2 : ρ x (ρ c u) = ρ (x * c) u := by rw [map_mul]; rfl
    rw [e2, e]
    simp only [map_mul, MulAut.mul_apply]
    rw [hχ, hy, map_mul, hχc']
  have h2 : ρ x (ρ c⁻¹ u) = ρ c u * χ := by
    have e : x * c⁻¹ = y₀⁻¹ * c * x := by rw [hy₀]; group
    have e2 : ρ x (ρ c⁻¹ u) = ρ (x * c⁻¹) u := by rw [map_mul]; rfl
    rw [e2, e]
    simp only [map_mul, MulAut.mul_apply]
    rw [hχ, map_mul, hχc, hy']
  rw [map_mul, map_mul, hχ, h1, h2] at hs
  have key : (u * ρ c u * ρ c⁻¹ u) * (χ * χ * χ) = (u * ρ c u * ρ c⁻¹ u) * 1 := by
    calc (u * ρ c u * ρ c⁻¹ u) * (χ * χ * χ) = (u * χ) * (ρ c⁻¹ u * χ) * (ρ c u * χ) := by
          ac_rfl
      _ = u * ρ c u * ρ c⁻¹ u := hs
      _ = (u * ρ c u * ρ c⁻¹ u) * 1 := (mul_one _).symm
  have h3 : χ * χ * χ = 1 := mul_left_cancel key
  calc χ = χ * χ * χ := by rw [hW χ, one_mul]
    _ = 1 := h3

end Trick

section PermLemmas

theorem exists_alt_triple (hn : 5 ≤ n) {i j k i' j' k' : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hij' : i' ≠ j') (hjk' : j' ≠ k')
    (hik' : i' ≠ k') :
    ∃ σ : Perm (Fin n), σ ∈ alternatingGroup (Fin n) ∧ σ i = i' ∧ σ j = j' ∧ σ k = k' := by
  have hf : Function.Injective (![i, j, k] : Fin 3 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp at h <;>
      first | rfl | exact absurd h ‹_› | exact absurd h.symm ‹_›
  have hf' : Function.Injective (![i', j', k'] : Fin 3 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp at h <;>
      first | rfl | exact absurd h ‹_› | exact absurd h.symm ‹_›
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hf'
  have h0 : σ i = i' := hσ 0
  have h1 : σ j = j' := hσ 1
  have h2 : σ k = k' := hσ 2
  by_cases hs : sign σ = 1
  · exact ⟨σ, mem_alternatingGroup.2 hs, h0, h1, h2⟩
  · obtain ⟨a, ha1, ha2, ha3, -⟩ := exists_ne_four hn i' j' k' k'
    obtain ⟨b, hb1, hb2, hb3, hba⟩ := exists_ne_four hn i' j' k' a
    refine ⟨swap a b * σ, ?_, ?_, ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm hba)]
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact absurd h hs
      · rw [h]; decide
    · rw [Perm.mul_apply, h0, swap_apply_of_ne_of_ne (Ne.symm ha1) (Ne.symm hb1)]
    · rw [Perm.mul_apply, h1, swap_apply_of_ne_of_ne (Ne.symm ha2) (Ne.symm hb2)]
    · rw [Perm.mul_apply, h2, swap_apply_of_ne_of_ne (Ne.symm ha3) (Ne.symm hb3)]

theorem c3_conj {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {σ : Perm (Fin n)}
    (hi : σ i = j) (hj : σ j = i) (hk : σ k = k) :
    (swap i j * swap j k) * σ * (swap i j * swap j k) * σ⁻¹ = 1 := by
  have e1 := swap_apply_apply σ i j
  have e2 := swap_apply_apply σ j k
  rw [hi, hj] at e1
  rw [hj, hk] at e2
  have e3 : (swap i j * swap j k) * σ * (swap i j * swap j k) * σ⁻¹ =
      (swap i j * swap j k) * ((σ * swap i j * σ⁻¹) * (σ * swap j k * σ⁻¹)) := by group
  rw [e3, ← e1, ← e2]
  ext p
  simp only [Perm.mul_apply, Perm.one_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem c3_apply_left {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (swap i j * swap j k) i = j := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, swap_apply_left]

theorem c3_apply_mid {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (swap i j * swap j k) j = k := by
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hik.symm hjk.symm]

theorem exists_three_distinct (hn : 3 ≤ n) : ∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ i ≠ k :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
    by simp [Fin.ext_iff]⟩

end PermLemmas

section FibreFixed

variable (C : Cfg G M X n)

theorem exists_lift_pair (hn : 5 ≤ n) {p q p' q' : Fin n} (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ x : ↥X, pm C x p = p' ∧ pm C x q = q' := by
  obtain ⟨k, hkp, hkq, -, -⟩ := exists_ne_four hn p q q q
  obtain ⟨k', hkp', hkq', -, -⟩ := exists_ne_four hn p' q' q' q'
  obtain ⟨σ, hσA, h1, h2, -⟩ :=
    exists_alt_triple hn hpq hkq.symm hkp.symm hpq' hkq'.symm hkp'.symm
  obtain ⟨x, hx⟩ := exists_lift C hσA
  exact ⟨x, by rw [hx]; exact h1, by rw [hx]; exact h2⟩

theorem zmod2_aux (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    ((if a then 1 else 0) + (if b then 1 else 0)) + ((if b then 1 else 0) + (if c then 1 else 0)) +
      ((if c then 1 else 0) + (if a then 1 else 0)) = (0 : ZMod 2) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc] <;> decide

theorem pairEW_self (i : Fin n) : (pairEW i i : evenWeight n) = 0 := by
  apply Subtype.ext
  funext p
  rw [pairEW_apply]
  show _ = (0 : ZMod 2)
  split_ifs <;> decide

theorem pairEW_tri (i j k : Fin n) :
    (pairEW i j : altHeart n) + (pairEW j k : altHeart n) + (pairEW k i : altHeart n) = 0 := by
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
  have : pairEW i j + pairEW j k + pairEW k i = (0 : evenWeight n) := by
    apply Subtype.ext
    funext p
    simp only [AddSubgroup.coe_add, Pi.add_apply, pairEW_apply]
    show _ = (0 : ZMod 2)
    exact zmod2_aux (p = i) (p = j) (p = k)
  rw [this]
  rfl

theorem good_inv {x : ↥X} {u : ↥(blockU X)} (h : actX C x u = u) : actX C x⁻¹ u = u := by
  have : actX C x⁻¹ (actX C x u) = u := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rwa [h] at this

theorem good_mul {x y : ↥X} {u : ↥(blockU X)} (hx : actX C x u = u) (hy : actX C y u = u) :
    actX C (x * y) u = u := by
  rw [map_mul, MulAut.mul_apply, hy, hx]

theorem fibre_fixed_three {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {u : ↥(blockU X)} (hu : bet C u = (pairEW i j : altHeart n)) {x : ↥X}
    (hxi : pm C x i = j) (hxj : pm C x j = i) (hxk : pm C x k = k) : actX C x u = u := by
  haveI : IsMulCommutative ↥(blockU X) := C.S.elemU.1
  have hc₀A : (swap i j * swap j k : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap hij, sign_swap hjk]
    decide
  obtain ⟨c, hc⟩ := exists_lift C hc₀A
  have hyα : C.α (c * x * c * x⁻¹) = 1 := by
    apply α_eq_one_of_pm_eq_one
    simp only [pm_mul, pm_inv, hc]
    exact c3_conj hij hjk hik hxi hxj hxk
  obtain ⟨χ, hχdef⟩ : ∃ χ : ↥(blockU X), χ = u⁻¹ * actX C x u := ⟨_, rfl⟩
  have hχ : actX C x u = u * χ := by rw [hχdef]; group
  have hbχ : bet C χ = 0 := by
    rw [hχdef, bet_mul, bet_inv, bet_actX, hu, altAct_mk, evenWeightPerm_pairEW, hxi, hxj,
      pairEW_comm, neg_add_cancel]
  have hχc : actX C c χ = χ := actX_eq_of_bet_eq_zero C c hbχ
  have hχc' : actX C c⁻¹ χ = χ := actX_eq_of_bet_eq_zero C c⁻¹ hbχ
  have hc1 : (swap i j * swap j k : Perm (Fin n)) i = j := c3_apply_left hij hjk hik
  have hc2 : (swap i j * swap j k : Perm (Fin n)) j = k := c3_apply_mid hij hjk hik
  have hc3 : (swap i j * swap j k : Perm (Fin n)) k = i := by
    rw [Perm.mul_apply, swap_apply_right, swap_apply_right]
  have hci : (swap i j * swap j k : Perm (Fin n))⁻¹ i = k := by
    rw [Perm.inv_eq_iff_eq, hc3]
  have hcj : (swap i j * swap j k : Perm (Fin n))⁻¹ j = i := by
    rw [Perm.inv_eq_iff_eq, hc1]
  have hbs : bet C (u * actX C c u * actX C c⁻¹ u) = 0 := by
    rw [bet_mul, bet_mul, bet_actX, bet_actX, hu, altAct_mk, altAct_mk, evenWeightPerm_pairEW,
      evenWeightPerm_pairEW, pm_inv, hc, hc1, hc2, hci, hcj]
    exact pairEW_tri i j k
  have hs := actX_eq_of_bet_eq_zero C x hbs
  have hχ1 : χ = 1 :=
    three_cycle_trick (W_sq C.S) (actX C) x c u χ
      (fun w => actX_eq_of_α_eq_one C _ hyα w) hχ hχc hχc' hs
  rw [hχ, hχ1, mul_one]

theorem fibre_fixed_fix (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j) {u : ↥(blockU X)}
    (hu : bet C u = (pairEW i j : altHeart n)) {x : ↥X}
    (hxi : pm C x i = i) (hxj : pm C x j = j) : actX C x u = u := by
  by_cases h1 : pm C x = 1
  · exact actX_eq_of_α_eq_one C x (α_eq_one_of_pm_eq_one C h1) u
  · obtain ⟨b, hb⟩ : ∃ b, pm C x b ≠ b := by
      by_contra hcon
      push Not at hcon
      exact h1 (Equiv.ext hcon)
    obtain ⟨a, ha⟩ : ∃ a, a = pm C x b := ⟨_, rfl⟩
    rw [← ha] at hb
    have hbi : b ≠ i := fun h => hb (by rw [ha, h, hxi])
    have hbj : b ≠ j := fun h => hb (by rw [ha, h, hxj])
    have hai : a ≠ i := fun h => hbi ((pm C x).injective (by rw [← ha, h, hxi]))
    have haj : a ≠ j := fun h => hbj ((pm C x).injective (by rw [← ha, h, hxj]))
    have hab : a ≠ b := hb
    have hτA : (swap i j * swap a b : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, map_mul, sign_swap hij, sign_swap hab]
      decide
    obtain ⟨x', hx'⟩ := exists_lift C hτA
    obtain ⟨k, hki, hkj, hka, hkb⟩ := exists_ne_four hn i j a b
    have hτi : (swap i j * swap a b : Perm (Fin n)) i = j := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hai.symm hbi.symm, swap_apply_left]
    have hτj : (swap i j * swap a b : Perm (Fin n)) j = i := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne haj.symm hbj.symm, swap_apply_right]
    have hτk : (swap i j * swap a b : Perm (Fin n)) k = k := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hka hkb, swap_apply_of_ne_of_ne hki hkj]
    have hτa : (swap i j * swap a b : Perm (Fin n)) a = b := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hbi hbj]
    have g1 : actX C x' u = u :=
      fibre_fixed_three C hij hkj.symm hki.symm hu (by rw [hx', hτi]) (by rw [hx', hτj])
        (by rw [hx', hτk])
    have g2 : actX C (x * x') u = u := by
      refine fibre_fixed_three C hij haj.symm hai.symm hu ?_ ?_ ?_
      · rw [pm_mul, Perm.mul_apply, hx', hτi, hxj]
      · rw [pm_mul, Perm.mul_apply, hx', hτj, hxi]
      · rw [pm_mul, Perm.mul_apply, hx', hτa, ha]
    have := good_mul C g2 (good_inv C g1)
    simpa using this

theorem fibre_fixed_swap (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j) {u : ↥(blockU X)}
    (hu : bet C u = (pairEW i j : altHeart n)) {x : ↥X}
    (hxi : pm C x i = j) (hxj : pm C x j = i) : actX C x u = u := by
  obtain ⟨a, hai, haj, -, -⟩ := exists_ne_four hn i j j j
  obtain ⟨b, hbi, hbj, hba, -⟩ := exists_ne_four hn i j a a
  have hab : a ≠ b := hba.symm
  have hτA : (swap i j * swap a b : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap hij, sign_swap hab]
    decide
  obtain ⟨x', hx'⟩ := exists_lift C hτA
  obtain ⟨k, hki, hkj, hka, hkb⟩ := exists_ne_four hn i j a b
  have hτi : (swap i j * swap a b : Perm (Fin n)) i = j := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hai.symm hbi.symm, swap_apply_left]
  have hτj : (swap i j * swap a b : Perm (Fin n)) j = i := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne haj.symm hbj.symm, swap_apply_right]
  have hτk : (swap i j * swap a b : Perm (Fin n)) k = k := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hka hkb, swap_apply_of_ne_of_ne hki hkj]
  have g1 : actX C x' u = u :=
    fibre_fixed_three C hij hkj.symm hki.symm hu (by rw [hx', hτi]) (by rw [hx', hτj])
      (by rw [hx', hτk])
  have g2 : actX C (x * x') u = u := by
    refine fibre_fixed_fix C hn hij hu ?_ ?_
    · rw [pm_mul, Perm.mul_apply, hx', hτi, hxj]
    · rw [pm_mul, Perm.mul_apply, hx', hτj, hxi]
  have := good_mul C g2 (good_inv C g1)
  simpa using this

theorem fibre_fixed_aux (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j) {u : ↥(blockU X)}
    (hu : bet C u = (pairEW i j : altHeart n)) {x : ↥X}
    (hx : (pm C x i = i ∧ pm C x j = j) ∨ (pm C x i = j ∧ pm C x j = i)) : actX C x u = u :=
  hx.elim (fun h => fibre_fixed_fix C hn hij hu h.1 h.2)
    (fun h => fibre_fixed_swap C hn hij hu h.1 h.2)

end FibreFixed

section PairLift

variable (C : Cfg G M X n)

structure PairLift where
  w : Fin n → Fin n → ↥(blockU X)
  bet_w : ∀ p q, bet C (w p q) = (pairEW p q : altHeart n)
  w_self : ∀ p, w p p = 1
  w_comm : ∀ p q, w p q = w q p
  equivar : ∀ (x : ↥X) p q, actX C x (w p q) = w (pm C x p) (pm C x q)
  triangle : ∀ p q r, w p q * w q r * w r p = 1

theorem nonempty_pairLift (hn : 5 ≤ n) : Nonempty (PairLift C) := by
  haveI : IsMulCommutative ↥(blockU X) := C.S.elemU.1
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, i₀ = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, j₀ = ⟨1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin n, k₀ = ⟨2, by omega⟩ := ⟨_, rfl⟩
  have h01 : i₀ ≠ j₀ := by rw [hi₀, hj₀]; simp [Fin.ext_iff]
  have h12 : j₀ ≠ k₀ := by rw [hj₀, hk₀]; simp [Fin.ext_iff]
  have h02 : i₀ ≠ k₀ := by rw [hi₀, hk₀]; simp [Fin.ext_iff]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ↥(blockU X), bet C u₀ = (pairEW i₀ j₀ : altHeart n) := by
    obtain ⟨u, hu⟩ := C.β_surj (Multiplicative.ofAdd (pairEW i₀ j₀ : altHeart n))
    exact ⟨u, by simpa [bet] using congrArg Multiplicative.toAdd hu⟩
  have hex : ∀ p q : Fin n, p ≠ q → ∃ x : ↥X, pm C x i₀ = p ∧ pm C x j₀ = q := fun p q hpq =>
    exists_lift_pair C hn h01 hpq
  have hunique : ∀ x x' : ↥X,
      ((pm C x i₀ = pm C x' i₀ ∧ pm C x j₀ = pm C x' j₀) ∨
        (pm C x i₀ = pm C x' j₀ ∧ pm C x j₀ = pm C x' i₀)) →
      actX C x u₀ = actX C x' u₀ := by
    intro x x' h
    have h1 : actX C (x⁻¹ * x') u₀ = u₀ := by
      refine fibre_fixed_aux C hn h01 hu₀ ?_
      rw [pm_mul, pm_inv]
      simp only [Perm.mul_apply, Perm.inv_eq_iff_eq]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    have h2 : actX C x' u₀ = actX C x u₀ := by
      have : x' = x * (x⁻¹ * x') := by group
      rw [this, map_mul, MulAut.mul_apply, h1]
    exact h2.symm
  let w₁ : Fin n → Fin n → ↥(blockU X) := fun p q =>
    if h : p ≠ q then actX C (Classical.choose (hex p q h)) u₀ else 1
  have w₁_eq : ∀ (x : ↥X) p q, p ≠ q → pm C x i₀ = p → pm C x j₀ = q →
      w₁ p q = actX C x u₀ := by
    intro x p q hpq h1 h2
    simp only [w₁, dif_pos hpq]
    obtain ⟨c1, c2⟩ := Classical.choose_spec (hex p q hpq)
    exact hunique _ _ (Or.inl ⟨by rw [c1, h1], by rw [c2, h2]⟩)
  have w₁_self : ∀ p, w₁ p p = 1 := fun p => by simp [w₁]
  have w₁_comm : ∀ p q, w₁ p q = w₁ q p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · obtain ⟨x, hx1, hx2⟩ := hex p q hpq
      obtain ⟨x', hx1', hx2'⟩ := hex q p (Ne.symm hpq)
      rw [w₁_eq x p q hpq hx1 hx2, w₁_eq x' q p (Ne.symm hpq) hx1' hx2']
      exact hunique _ _ (Or.inr ⟨by rw [hx1, hx2'], by rw [hx2, hx1']⟩)
  have w₁_equivar : ∀ (x : ↥X) p q, actX C x (w₁ p q) = w₁ (pm C x p) (pm C x q) := by
    intro x p q
    by_cases hpq : p = q
    · subst hpq
      rw [w₁_self, w₁_self, map_one]
    · obtain ⟨y, hy1, hy2⟩ := hex p q hpq
      have hne : pm C x p ≠ pm C x q := fun h => hpq ((pm C x).injective h)
      rw [w₁_eq y p q hpq hy1 hy2, w₁_eq (x * y) _ _ hne (by rw [pm_mul, Perm.mul_apply, hy1])
        (by rw [pm_mul, Perm.mul_apply, hy2]), map_mul, MulAut.mul_apply]
  have w₁_bet : ∀ p q, bet C (w₁ p q) = (pairEW p q : altHeart n) := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      rw [w₁_self, bet_one, pairEW_self]
      rfl
    · obtain ⟨x, hx1, hx2⟩ := hex p q hpq
      rw [w₁_eq x p q hpq hx1 hx2, bet_actX, hu₀, altAct_mk, evenWeightPerm_pairEW, hx1, hx2]
  let t : Fin n → Fin n → Fin n → ↥(blockU X) := fun p q r => w₁ p q * w₁ q r * w₁ r p
  have t_bet : ∀ p q r, bet C (t p q r) = 0 := by
    intro p q r
    simp only [t, bet_mul, w₁_bet]
    exact pairEW_tri p q r
  have t_equivar : ∀ (x : ↥X) p q r,
      actX C x (t p q r) = t (pm C x p) (pm C x q) (pm C x r) := by
    intro x p q r
    simp only [t, map_mul, w₁_equivar]
  obtain ⟨s, hs⟩ : ∃ s, s = t i₀ j₀ k₀ := ⟨_, rfl⟩
  have hs_bet : bet C s = 0 := by rw [hs]; exact t_bet _ _ _
  have t_eq : ∀ p q r, p ≠ q → q ≠ r → p ≠ r → t p q r = s := by
    intro p q r hpq hqr hpr
    obtain ⟨σ, hσA, h0, h1, h2⟩ := exists_alt_triple hn h01 h12 h02 hpq hqr hpr
    obtain ⟨x, hx⟩ := exists_lift C hσA
    have h := t_equivar x i₀ j₀ k₀
    rw [actX_eq_of_bet_eq_zero C x (t_bet _ _ _), hx, h0, h1, h2] at h
    rw [← h, hs]
  let w : Fin n → Fin n → ↥(blockU X) := fun p q => if p = q then 1 else w₁ p q * s
  have w_self : ∀ p, w p p = 1 := fun p => by simp [w]
  have w_comm : ∀ p q, w p q = w q p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · simp only [w, if_neg hpq, if_neg (Ne.symm hpq), w₁_comm]
  refine ⟨⟨w, ?_, w_self, w_comm, ?_, ?_⟩⟩
  · intro p q
    by_cases hpq : p = q
    · subst hpq
      rw [w_self, bet_one, pairEW_self]
      rfl
    · simp only [w, if_neg hpq, bet_mul, w₁_bet, hs_bet, add_zero]
  · intro x p q
    by_cases hpq : p = q
    · subst hpq
      rw [w_self, w_self, map_one]
    · have hne : pm C x p ≠ pm C x q := fun h => hpq ((pm C x).injective h)
      simp only [w, if_neg hpq, if_neg hne, map_mul, w₁_equivar,
        actX_eq_of_bet_eq_zero C x hs_bet]
  · intro p q r
    by_cases hpq : p = q
    · subst hpq
      rw [w_self, one_mul, w_comm r p, W_sq C.S]
    · by_cases hqr : q = r
      · subst hqr
        rw [w_self, mul_one, w_comm q p, W_sq C.S]
      · by_cases hpr : p = r
        · subst hpr
          rw [w_self, mul_one, w_comm q p, W_sq C.S]
        · simp only [w, if_neg hpq, if_neg hqr, if_neg (Ne.symm hpr)]
          have ht : w₁ p q * w₁ q r * w₁ r p = s := t_eq p q r hpq hqr hpr
          calc (w₁ p q * s) * (w₁ q r * s) * (w₁ r p * s)
              = (w₁ p q * w₁ q r * w₁ r p) * (s * s * s) := by ac_rfl
            _ = s * (s * s * s) := by rw [ht]
            _ = (s * s) * (s * s) := by ac_rfl
            _ = 1 := by rw [W_sq C.S s, mul_one]

end PairLift

section Cocycle

variable {A : Type*} [Group A] [IsMulCommutative A]

theorem ite_add_zmod2 {B : Type*} [Group B] (a b : ZMod 2) (g : B) (hg : g * g = 1) :
    (if a + b = 1 then g else 1) = (if a = 1 then g else 1) * (if b = 1 then g else 1) := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [hg] <;> decide

theorem eq_sum_pairEW (a₀ : Fin n) (v : evenWeight n) :
    v = ∑ i, if (v : Fin n → ZMod 2) i = 1 then pairEW a₀ i else 0 := by
  apply Subtype.ext
  funext p
  have hv : ∑ i, (v : Fin n → ZMod 2) i = 0 := v.2
  have key : ∀ i, ((if (v : Fin n → ZMod 2) i = 1 then pairEW a₀ i else 0 : evenWeight n) :
      Fin n → ZMod 2) p =
      (v : Fin n → ZMod 2) i * ((if p = a₀ then 1 else 0) + (if p = i then 1 else 0)) := by
    intro i
    by_cases h : (v : Fin n → ZMod 2) i = 1
    · simp [h, pairEW_apply]
    · have h0 : (v : Fin n → ZMod 2) i = 0 := (zmod_two_eq_zero_iff_ne_one _).2 h
      simp [h, h0]
  rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  simp_rw [key, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hv, zero_mul, zero_add]
  simp [mul_ite]

open scoped IsMulCommutative in
theorem exists_hom_of_cocycle (hA : ∀ a : A, a * a = 1) (a₀ : Fin n) (w : Fin n → Fin n → A)
    (hself : ∀ p, w p p = 1) (hcomm : ∀ p q, w p q = w q p)
    (htri : ∀ p q r, w p q * w q r * w r p = 1) :
    ∃ ψ : Multiplicative (evenWeight n) →* A,
      ∀ p q, ψ (Multiplicative.ofAdd (pairEW p q)) = w p q := by
  let f : Multiplicative (evenWeight n) → A := fun v =>
    ∏ i, if ((Multiplicative.toAdd v : evenWeight n) : Fin n → ZMod 2) i = 1 then w a₀ i else 1
  have hf : ∀ v v', f (v * v') = f v * f v' := by
    intro v v'
    simp only [f, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul]
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    exact ite_add_zmod2 _ _ _ (hA _)
  have hpair : ∀ p q, f (Multiplicative.ofAdd (pairEW p q)) = w p q := by
    intro p q
    simp only [f, toAdd_ofAdd]
    by_cases hpq : p = q
    · subst hpq
      rw [hself]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [pairEW_self]
      simp
    · rw [← Finset.prod_filter]
      have hfil : Finset.univ.filter (fun i => ((pairEW p q : evenWeight n) : Fin n → ZMod 2) i = 1)
          = {p, q} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, pairEW_apply]
        by_cases hip : i = p <;> by_cases hiq : i = q <;> simp [hip, hiq, hpq, Ne.symm hpq]
      rw [hfil, Finset.prod_pair hpq]
      have h := htri a₀ p q
      rw [hcomm q a₀] at h
      have h2 : w p q = (w a₀ p * w a₀ q)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← h]
        ac_rfl
      rw [h2]
      exact (inv_eq_of_mul_eq_one_right (hA _)).symm
  exact ⟨MonoidHom.mk' f hf, hpair⟩

theorem hom_ext_pairEW {B : Type*} [Group B] (a₀ : Fin n)
    {f g : Multiplicative (evenWeight n) →* B}
    (h : ∀ p q, f (Multiplicative.ofAdd (pairEW p q)) = g (Multiplicative.ofAdd (pairEW p q))) :
    f = g := by
  refine MonoidHom.ext fun v => ?_
  have hv : v = ∏ i, Multiplicative.ofAdd (if ((Multiplicative.toAdd v : evenWeight n) :
      Fin n → ZMod 2) i = 1 then pairEW a₀ i else 0) := by
    rw [← ofAdd_sum, ← eq_sum_pairEW a₀]
    rfl
  have key : f (∏ i, Multiplicative.ofAdd (if ((Multiplicative.toAdd v : evenWeight n) :
      Fin n → ZMod 2) i = 1 then pairEW a₀ i else 0)) =
      g (∏ i, Multiplicative.ofAdd (if ((Multiplicative.toAdd v : evenWeight n) :
      Fin n → ZMod 2) i = 1 then pairEW a₀ i else 0)) := by
    refine Finset.prod_induction _ (fun w => f w = g w)
      (fun a b ha hb => by rw [map_mul, map_mul, ha, hb]) (by rw [map_one, map_one]) ?_
    intro i _
    split_ifs
    · exact h a₀ i
    · rw [ofAdd_zero, map_one, map_one]
  rwa [← hv] at key

end Cocycle

section Psi

variable (C : Cfg G M X n)

theorem PairLift.act_w (hn : 5 ≤ n) (pl : PairLift C) (m : ↥M) (p q : Fin n) :
    act C m (pl.w p q) = pl.w (C.θ m p) (C.θ m q) := by
  haveI : IsMulCommutative ↥(blockU X) := C.S.elemU.1
  obtain ⟨ε, hεdef⟩ : ∃ ε : Fin n → Fin n → ↥(blockU X),
      ε = fun p q => (pl.w (C.θ m p) (C.θ m q))⁻¹ * act C m (pl.w p q) := ⟨_, rfl⟩
  have hdec : ∀ p q, act C m (pl.w p q) = pl.w (C.θ m p) (C.θ m q) * ε p q := by
    intro p q
    rw [hεdef]
    simp
  have ε_bet : ∀ p q, bet C (ε p q) = 0 := by
    intro p q
    rw [hεdef]
    simp only [bet_mul, bet_inv, bet_act, pl.bet_w, altAct_mk, evenWeightPerm_pairEW]
    exact neg_add_cancel _
  have ε_fix : ∀ (x : ↥X) p q, actX C x (ε p q) = ε p q := fun x p q =>
    actX_eq_of_bet_eq_zero C x (ε_bet p q)
  have hconst : ∀ p q p' q', p ≠ q → p' ≠ q' → ε p' q' = ε p q := by
    intro p q p' q' hpq hpq'
    obtain ⟨x, hx1, hx2⟩ := exists_lift_pair C hn hpq hpq'
    have hmx : (m : G) * (x : G) * (m : G)⁻¹ ∈ X := C.S.normal m.2 x.2
    obtain ⟨g, hgdef⟩ : ∃ g : ↥X, g = ⟨(m : G) * x * (m : G)⁻¹, hmx⟩ := ⟨_, rfl⟩
    have hg : inclX C g = m * inclX C x * m⁻¹ := by
      apply Subtype.ext
      rw [hgdef]
      rfl
    have hpm_g : pm C g = C.θ m * pm C x * (C.θ m)⁻¹ := by
      rw [← theta_inclX, hg, map_mul, map_mul, map_inv, theta_inclX]
    have hpg : ∀ r, pm C g (C.θ m r) = C.θ m (pm C x r) := by
      intro r
      rw [hpm_g]
      simp [Perm.mul_apply]
    have hcomm : ∀ v : ↥(blockU X), act C m (actX C x v) = actX C g (act C m v) := by
      intro v
      have h : m * inclX C x = inclX C g * m := by rw [hg]; group
      have e1 : act C m (actX C x v) = actHom C (m * inclX C x) v := by
        rw [map_mul, MulAut.mul_apply]
        rfl
      have e2 : actX C g (act C m v) = actHom C (inclX C g * m) v := by
        rw [map_mul, MulAut.mul_apply]
        rfl
      rw [e1, e2, h]
    have key : act C m (pl.w p' q') = pl.w (C.θ m p') (C.θ m q') * ε p q := by
      have h1 : pl.w p' q' = actX C x (pl.w p q) := by rw [pl.equivar, hx1, hx2]
      rw [h1, hcomm, hdec p q, map_mul, pl.equivar, ε_fix, hpg, hpg, hx1, hx2]
    exact mul_left_cancel ((hdec p' q').symm.trans key)
  have htri : ∀ p q r, ε p q * ε q r * ε r p = 1 := by
    intro p q r
    have h1 := pl.triangle (C.θ m p) (C.θ m q) (C.θ m r)
    have h2 := pl.triangle p q r
    have h3 : act C m (pl.w p q) * act C m (pl.w q r) * act C m (pl.w r p) = 1 := by
      rw [← map_mul, ← map_mul, h2, map_one]
    have h4 : (pl.w (C.θ m p) (C.θ m q) * pl.w (C.θ m q) (C.θ m r) * pl.w (C.θ m r) (C.θ m p)) *
        (ε p q * ε q r * ε r p) = 1 := by
      rw [← h3, hdec p q, hdec q r, hdec r p]
      ac_rfl
    rwa [h1, one_mul] at h4
  have hε1 : ∀ p q, p ≠ q → ε p q = 1 := by
    intro p q hpq
    obtain ⟨i₀, j₀, k₀, h01, h12, h02⟩ := exists_three_distinct (n := n) (by omega)
    have e1 : ε j₀ k₀ = ε i₀ j₀ := hconst i₀ j₀ j₀ k₀ h01 h12
    have e2 : ε k₀ i₀ = ε i₀ j₀ := hconst i₀ j₀ k₀ i₀ h01 h02.symm
    have e3 := htri i₀ j₀ k₀
    rw [e1, e2] at e3
    have e4 : ε i₀ j₀ = 1 := by
      have hsq := W_sq C.S (ε i₀ j₀)
      calc ε i₀ j₀ = ε i₀ j₀ * (ε i₀ j₀ * ε i₀ j₀) := by rw [hsq, mul_one]
        _ = ε i₀ j₀ * ε i₀ j₀ * ε i₀ j₀ := by rw [mul_assoc]
        _ = 1 := e3
    rw [hconst i₀ j₀ p q h01 hpq, e4]
  by_cases hpq : p = q
  · subst hpq
    rw [pl.w_self, pl.w_self, map_one]
  · have h := hdec p q
    rwa [hε1 p q hpq, mul_one] at h

theorem exists_psi (hn : 5 ≤ n) :
    ∃ ψ : Multiplicative (evenWeight n) →* ↥(blockU X),
      (∀ v, bet C (ψ v) = ((Multiplicative.toAdd v : evenWeight n) : altHeart n)) ∧
      (∀ (m : ↥M) v, act C m (ψ v) =
        ψ (Multiplicative.ofAdd (evenWeightPerm (C.θ m) (Multiplicative.toAdd v)))) := by
  haveI : IsMulCommutative ↥(blockU X) := C.S.elemU.1
  obtain ⟨pl⟩ := nonempty_pairLift C hn
  obtain ⟨a₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_hom_of_cocycle (W_sq C.S) a₀ pl.w pl.w_self pl.w_comm pl.triangle
  refine ⟨ψ, ?_, ?_⟩
  · intro v
    have h : C.β.comp ψ = AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (evenWeightOnes n)) :=
      hom_ext_pairEW a₀ (fun p q => by
        have := pl.bet_w p q
        simp only [MonoidHom.comp_apply, hψ]
        apply Multiplicative.toAdd.injective
        simpa [bet] using this)
    have := congrArg (fun f => Multiplicative.toAdd (f v)) h
    simpa [bet] using this
  · intro m
    have h : (act C m).toMonoidHom.comp ψ =
        ψ.comp (AddMonoidHom.toMultiplicative (evenWeightPermHom (C.θ m))) :=
      hom_ext_pairEW a₀ (fun p q => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ,
          AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
        rw [PairLift.act_w C hn pl m p q]
        show _ = ψ (Multiplicative.ofAdd (evenWeightPerm (C.θ m) (pairEW p q)))
        rw [evenWeightPerm_pairEW, hψ])
    intro v
    exact DFunLike.congr_fun h v

theorem psi_surjective (ψ : Multiplicative (evenWeight n) →* ↥(blockU X))
    (hβ : ∀ v, bet C (ψ v) = ((Multiplicative.toAdd v : evenWeight n) : altHeart n))
    (hX : ∀ (x : ↥X) v, actX C x (ψ v) =
      ψ (Multiplicative.ofAdd (evenWeightPerm (pm C x) (Multiplicative.toAdd v)))) :
    Function.Surjective ψ := by
  have hR : ∀ (u : ↥(blockU X)) (x : ↥X), u * (actX C x u)⁻¹ ∈ ψ.range := by
    intro u x
    obtain ⟨v₀, hv₀⟩ := QuotientAddGroup.mk_surjective (bet C u)
    obtain ⟨v, hv⟩ : ∃ v : Multiplicative (evenWeight n), v = Multiplicative.ofAdd v₀ := ⟨_, rfl⟩
    have hbe : bet C ((ψ v)⁻¹ * u) = 0 := by
      rw [bet_mul, bet_inv, hβ, hv, toAdd_ofAdd, hv₀]
      exact neg_add_cancel _
    have hfix : actX C x ((ψ v)⁻¹ * u) = (ψ v)⁻¹ * u := actX_eq_of_bet_eq_zero C x hbe
    have hu : u = ψ v * ((ψ v)⁻¹ * u) := by group
    have h1 : actX C x u = actX C x (ψ v) * ((ψ v)⁻¹ * u) := by
      conv_lhs => rw [hu]
      rw [map_mul, hfix]
    have h2 : u * (actX C x u)⁻¹ = ψ v * (actX C x (ψ v))⁻¹ := by
      rw [h1]
      group
    rw [h2, hX x v, ← map_inv, ← map_mul]
    exact ⟨_, rfl⟩
  intro u
  have hu : (u : G) ∈ ⁅blockU X, X⁆ := by
    rw [commutator_W_eq C.S]
    exact u.2
  have hle : ⁅blockU X, X⁆ ≤ ψ.range.map (blockU X).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⟨g₁, hg₁⟩ * (actX C ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩)⁻¹, hR ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, actX_coe,
      commutatorElement_def]
    group
  obtain ⟨r, hr, hru⟩ := hle hu
  have hru' : r = u := Subtype.ext hru
  rw [hru'] at hr
  exact hr

end Psi

section Cardinality

variable (C : Cfg G M X n)
include C

theorem card_blockU_eq : Nat.card ↥(blockU X) = Nat.card ↥(blockZ X) * Nat.card (altHeart n) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C.β.ker
  have h2 : Nat.card (↥(blockU X) ⧸ C.β.ker) = Nat.card (altHeart n) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective C.β C.β_surj).toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have h3 : Nat.card C.β.ker = Nat.card ↥(blockZ X) := by
    rw [C.β_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockZ_le_blockU X)).toEquiv
  rw [h1, h2, h3, mul_comm]

end Cardinality

theorem card_evenWeightOnes_eq_two {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    Nat.card (evenWeightOnes n) = 2 := by
  have hmem : allOnes n ∈ evenWeight n := by
    show ∑ _i : Fin n, (1 : ZMod 2) = 0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_eq_zero_iff_even).mpr he
  let a : evenWeight n := ⟨allOnes n, hmem⟩
  have ha : (0 : evenWeight n) ≠ a := by
    intro h
    have := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
    exact zero_ne_one this
  have hset : ((evenWeightOnes n : AddSubgroup (evenWeight n)) : Set (evenWeight n)) = {0, a} := by
    ext z
    rw [SetLike.mem_coe, evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
      mem_zmultiples_allOnes_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair ha]

theorem card_evenWeight_eq_mul (n : ℕ) :
    Nat.card (evenWeight n) = Nat.card (altHeart n) * Nat.card (evenWeightOnes n) :=
  AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes n)

theorem six_le_degree (C : Cfg G M X n) : 6 ≤ n := by
  rcases C.S.n_mem with h | h | h <;> omega

theorem even_degree (C : Cfg G M X n) : Even n := by
  rcases C.S.n_mem with h | h | h
  · exact ⟨3, by omega⟩
  · exact ⟨4, by omega⟩
  · exact ⟨5, by omega⟩

end WStr

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)
include C

theorem commutator_W_eq : ⁅blockU X, X⁆ = blockU X :=
  WStr.commutator_W_eq C.S

theorem exists_psi0 :
    ∃ ψ : Multiplicative (evenWeight n) →* ↥(blockU X),
      (∀ v : evenWeight n,
        Multiplicative.toAdd (C.β (ψ (Multiplicative.ofAdd v))) = (v : altHeart n)) ∧
      (∀ (m : ↥M) (v : evenWeight n),
        (m : G) * (ψ (Multiplicative.ofAdd v) : G) * (m : G)⁻¹ =
          (ψ (Multiplicative.ofAdd (evenWeightPerm (C.θ m) v)) : G)) ∧
      Function.Surjective ψ := by
  have hn : 5 ≤ n := by have := WStr.six_le_degree C; omega
  obtain ⟨ψ, hβ, hM⟩ := WStr.exists_psi C hn
  have hX : ∀ (x : ↥X) (v : Multiplicative (evenWeight n)), WStr.actX C x (ψ v) =
      ψ (Multiplicative.ofAdd (evenWeightPerm (WStr.pm C x) (Multiplicative.toAdd v))) := by
    intro x v
    have h := hM (WStr.inclX C x) v
    rw [WStr.theta_inclX] at h
    exact h
  refine ⟨ψ, fun v => ?_, fun m v => ?_, WStr.psi_surjective C ψ hβ hX⟩
  · simpa [WStr.bet] using hβ (Multiplicative.ofAdd v)
  · have h := congrArg Subtype.val (hM m (Multiplicative.ofAdd v))
    simpa [WStr.act_coe] using h

theorem card_blockZ_le_two : Nat.card ↥(blockZ X) ≤ 2 := by
  obtain ⟨ψ, -, -, hsurj⟩ := C.exists_psi0
  have hn : 1 ≤ n := by have := WStr.six_le_degree C; omega
  have h1 : Nat.card ↥(blockU X) ≤ Nat.card (Multiplicative (evenWeight n)) :=
    Nat.card_le_card_of_surjective ψ hsurj
  rw [WStr.card_blockU_eq C, Nat.card_congr Multiplicative.toAdd, WStr.card_evenWeight_eq_mul,
    WStr.card_evenWeightOnes_eq_two hn (WStr.even_degree C), mul_comm (Nat.card (altHeart n)) 2]
    at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem nonempty_uIso (h : Nat.card ↥(blockZ X) = 2) : Nonempty C.UIso := by
  obtain ⟨ψ, hβ, hM, hsurj⟩ := C.exists_psi0
  have hn : 1 ≤ n := by have := WStr.six_le_degree C; omega
  have hcard : Nat.card (Multiplicative (evenWeight n)) ≤ Nat.card ↥(blockU X) := by
    rw [WStr.card_blockU_eq C, h, Nat.card_congr Multiplicative.toAdd,
      WStr.card_evenWeight_eq_mul, WStr.card_evenWeightOnes_eq_two hn (WStr.even_degree C),
      mul_comm]
  have hbij : Function.Bijective ψ := hsurj.bijective_of_nat_card_le hcard
  exact ⟨{ ψ := MulEquiv.ofBijective ψ hbij, equivar := hM, β_ψ := hβ }⟩

theorem beta_injective_of_card (h : Nat.card ↥(blockZ X) = 1) : Function.Injective C.β := by
  have hbot : blockZ X = ⊥ := Subgroup.card_eq_one.1 h
  rw [← MonoidHom.ker_eq_bot_iff, C.β_ker, hbot, Subgroup.bot_subgroupOf]

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
