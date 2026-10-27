module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF79KOneFive
import CFSG.RankThree.PartTwo.Sec18.Item188Abs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G]

theorem mem_nor_cenS_of_mem_nor {H : Subgroup G} {g : G} (hg : g ∈ Nor H) : g ∈ Nor (CenS H) :=
  Subgroup.mem_normalizer_fintype fun c hc => by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) h).mp hh
      rwa [inv_inv] at this
    have hch : (g⁻¹ * h * g) * c = c * (g⁻¹ * h * g) := Subgroup.mem_centralizer_iff.mp hc _ hh'
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hch]
      _ = g * c * g⁻¹ * h := by group

theorem conjBy_eq_of_mem_nor {T : Subgroup G} {g : G} (hg : g ∈ Nor T) : conjBy g T = T :=
  Subgroup.eq_of_le_of_card_ge
    (by rintro _ ⟨t, ht, rfl⟩; exact (Subgroup.mem_normalizer_iff.mp hg t).mp ht)
    (by rw [card_conjBy])

theorem mem_nor_commutator {T : Subgroup G} {g : G} (hg : g ∈ Nor T) : g ∈ Nor ⁅T, T⁆ :=
  Subgroup.mem_normalizer_fintype fun c hc => by
    have h : g * c * g⁻¹ ∈ (⁅T, T⁆).map (MulAut.conj g).toMonoidHom := ⟨c, hc, rfl⟩
    rw [Subgroup.map_commutator] at h
    change _ ∈ ⁅conjBy g T, conjBy g T⁆ at h
    rwa [conjBy_eq_of_mem_nor hg] at h

theorem mem_nor_sup {X Y : Subgroup G} {g : G} (hX : g ∈ Nor X) (hY : g ∈ Nor Y) :
    g ∈ Nor (X ⊔ Y) :=
  Subgroup.mem_normalizer_fintype fun c hc => by
    have h : g * c * g⁻¹ ∈ (X ⊔ Y).map (MulAut.conj g).toMonoidHom := ⟨c, hc, rfl⟩
    rw [Subgroup.map_sup] at h
    change _ ∈ conjBy g X ⊔ conjBy g Y at h
    rwa [conjBy_eq_of_mem_nor hX, conjBy_eq_of_mem_nor hY] at h

theorem mem_nor_zpowers {t g : G} (h : g * t = t * g) : g ∈ Nor (Subgroup.zpowers t) :=
  Subgroup.mem_normalizer_fintype fun c hc => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [(Commute.zpow_right h k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t k

theorem dot_sub_smul (f w x : Fin 3 → ZMod 3) (c : ZMod 3) :
    dot f (w - c • x) = dot f w - c * dot f x := by
  simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem exists_mem_hyp_not_mem : ∀ i j : Fin 13, i ≠ j →
    ∃ x : Fin 3 → ZMod 3, dot (hypF j) x = 0 ∧ dot (hypF i) x ≠ 0 := by
  decide

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem cenS_hyp_inf_cen_of (hB : FF81Basis b L B b₁ b₂ b₃) (i : Fin 13)
    {x : Fin 3 → ZMod 3} (hx : dot (hypF i) x ≠ 0) :
    CenS (hyp b₁ b₂ b₃ i) ⊓ Cen (ε3 b₁ b₂ b₃ x) = CenS (Subgroup.closure {b₁, b₂, b₃}) := by
  have he : dot (hypF i) x * dot (hypF i) x = 1 :=
    (by decide : ∀ e : ZMod 3, e ≠ 0 → e * e = 1) _ hx
  refine le_antisymm (fun c hc => ?_) (le_inf ?_ ?_)
  · obtain ⟨hcA, hcz⟩ := hc
    refine Subgroup.mem_centralizer_iff.mpr fun β hβ => ?_
    obtain ⟨w, rfl⟩ := hB.exists_ε3 hβ
    set d := dot (hypF i) w * dot (hypF i) x
    have hsplit : ε3 b₁ b₂ b₃ w = ε3 b₁ b₂ b₃ (w - d • x) * ε3 b₁ b₂ b₃ x ^ d.val := by
      rw [← hB.ε3_smul, ← hB.ε3_add, sub_add_cancel]
    have hA : ε3 b₁ b₂ b₃ (w - d • x) ∈ hyp b₁ b₂ b₃ i := by
      refine (hB.mem_hyp i _).2 ?_
      rw [dot_sub_smul, mul_assoc, he, mul_one, sub_self]
    have h1 : ε3 b₁ b₂ b₃ (w - d • x) * c = c * ε3 b₁ b₂ b₃ (w - d • x) :=
      Subgroup.mem_centralizer_iff.mp hcA _ hA
    have h2 : c * ε3 b₁ b₂ b₃ x = ε3 b₁ b₂ b₃ x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcz
    have h2' : ε3 b₁ b₂ b₃ x ^ d.val * c = c * ε3 b₁ b₂ b₃ x ^ d.val :=
      (Commute.pow_left h2.symm d.val).eq
    rw [hsplit, mul_assoc, h2', ← mul_assoc, h1, mul_assoc]
  · exact Subgroup.centralizer_le (hyp_le i)
  · intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hc _ (ε3_mem _)).symm

theorem inf_cenS_hyp_inf_cen (hB : FF81Basis b L B b₁ b₂ b₃) (X : Subgroup G) (i : Fin 13)
    {x : Fin 3 → ZMod 3} (hx : dot (hypF i) x ≠ 0) :
    X ⊓ CenS (hyp b₁ b₂ b₃ i) ⊓ Cen (ε3 b₁ b₂ b₃ x) =
      X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) := by
  rw [inf_assoc, cenS_hyp_inf_cen_of hB i hx]

theorem mem_nor_inf_cenS_hyp (hB : FF81Basis b L B b₁ b₂ b₃) {X : Subgroup G} {β : G}
    (hβ : β ∈ Subgroup.closure {b₁, b₂, b₃}) (hβX : β ∈ Nor X) (i : Fin 13) :
    β ∈ Nor (X ⊓ CenS (hyp b₁ b₂ b₃ i)) :=
  mem_nor_inf hβX (mem_nor_cenS fun h hh => hB.B₁_comm hβ (hyp_le i hh))

variable {t₀ : G}

theorem le_cen_of_cenS (ht₀L : t₀ ∈ CenS L) : L ≤ Cen t₀ := fun l hl =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht₀L l hl)

theorem cen_le_nor_op_two : Cen t₀ ≤ Nor (Op 2 (Cen t₀)) := fun _ hg =>
  Subgroup.mem_normalizer_fintype fun _ hu => op_two_conj hg hu

theorem card_zpowers_t₀ (ht₀ : orderOf t₀ = 2) : Nat.card (Subgroup.zpowers t₀) = 2 := by
  rw [Nat.card_zpowers, ht₀]

theorem zpowers_le_inf_cenS (ht₀L : t₀ ∈ CenS L) {X H : Subgroup G} (ht₀X : t₀ ∈ X)
    (hH : H ≤ L) : Subgroup.zpowers t₀ ≤ X ⊓ CenS H :=
  Subgroup.zpowers_le.mpr ⟨ht₀X, Subgroup.centralizer_le hH ht₀L⟩

theorem eq_zpowers_of_card (ht₀ : orderOf t₀ = 2) {X : Subgroup G} (ht₀X : t₀ ∈ X)
    (hX : Nat.card X ≤ 2) : X = Subgroup.zpowers t₀ :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht₀X)
    (by rw [card_zpowers_t₀ ht₀]; exact hX)).symm

theorem pow_le_two_pow {e n : ℕ} (h : 2 ^ e ≤ 2 ^ n) : e ≤ n :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem exps_of_le (hKF : KF_Sp6RefS)
    (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B) (ht₀ : orderOf t₀ = 2)
    (ht₀L : t₀ ∈ CenS L) (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹) {X : Subgroup G} (hXL : L ≤ Nor X)
    (ht₀X : t₀ ∈ X) (hXT : X ≤ Op 2 (Cen t₀)) :
    ∃ α γ e₀ ey : ℕ, (α = 1 ∨ α = 3) ∧ (γ = 1 ∨ γ = 3) ∧ e₀ + 9 = 6 * α + 4 * γ ∧
      ey + 2 = α + 2 * γ ∧ Nat.card X = 2 ^ e₀ ∧ Nat.card ↥(X ⊓ Cen (b₁ * b₂)) = 2 ^ ey ∧
      X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.zpowers t₀ ∧
      (∀ i, hypW i = 1 → X ⊓ CenS (hyp b₁ b₂ b₃ i) = Subgroup.zpowers t₀) ∧
      (∀ i, hypW i = 2 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ α) ∧
      (∀ i, hypW i = 3 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ γ) := by
  have hXp : IsPGroup 2 X := (op_two_isPGroup t₀).to_le hXT
  obtain ⟨e₀, eB, ey, e₁, e₂, e₃, he₀, heB, hey, he₁, he₂, he₃, h12, h3⟩ :=
    exp_identities hB hXp hXL
  have hmono : ∀ i, Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤
      Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) := fun i =>
    Subgroup.card_le_of_le (inf_le_inf_right _ hXT)
  have hlow : ∀ H : Subgroup G, H ≤ L → 2 ≤ Nat.card ↥(X ⊓ CenS H) := fun H hH => by
    rw [← card_zpowers_t₀ ht₀]
    exact Subgroup.card_le_of_le (zpowers_le_inf_cenS ht₀L ht₀X hH)
  have hB₁L : Subgroup.closure {b₁, b₂, b₃} ≤ L := hB.B₁_le
  have hhL : ∀ i, hyp b₁ b₂ b₃ i ≤ L := fun i => (hyp_le i).trans hB₁L
  have hw1 : ∀ i, hypW i = 1 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 2 := fun i h =>
    (hmono i).trans ((local_bound hKF hB hbad ht₀ ht₀L ht₀b i).1 h)
  have hw1' : ∀ i, hypW i = 1 → X ⊓ CenS (hyp b₁ b₂ b₃ i) = Subgroup.zpowers t₀ := fun i h =>
    eq_zpowers_of_card ht₀ ⟨ht₀X, Subgroup.centralizer_le (hhL i) ht₀L⟩ (hw1 i h)
  have h1 : e₁ = 1 := by
    have hc := he₁ 2 rfl
    have := hw1 2 rfl
    have := hlow _ (hhL 2)
    rw [hc] at *
    have := pow_le_two_pow (n := 1) (by omega)
    have := pow_le_two_pow (e := 1) (by omega)
    omega
  have hBz : X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.zpowers t₀ := by
    refine eq_zpowers_of_card ht₀ ⟨ht₀X, Subgroup.centralizer_le hB₁L ht₀L⟩ ?_
    exact (Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le (hyp_le 2)))).trans
      (hw1 2 rfl)
  have hB1 : eB = 1 := by
    rw [hBz, card_zpowers_t₀ ht₀] at heB
    have := pow_le_two_pow (n := 1) (e := eB) (by omega)
    have := pow_le_two_pow (e := 1) (n := eB) (by omega)
    omega
  have hodd : ∀ i e, Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ e → e % 2 = 1 := by
    intro i e he
    have hE := card_hyp_modEq hB (hB₁L.trans hXL) i
    rw [he, hBz, card_zpowers_t₀ ht₀] at hE
    exact two_pow_odd_of_modEq hE
  have hle3 : ∀ i e, Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ e →
      Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 8 → e ≤ 3 := by
    intro i e he h8
    have := (hmono i).trans h8
    rw [he] at this
    exact pow_le_two_pow (n := 3) this
  have h2a := hodd 4 e₂ (he₂ 4 rfl)
  have h2b := hle3 4 e₂ (he₂ 4 rfl) ((local_bound hKF hB hbad ht₀ ht₀L ht₀b 4).2.1 rfl).1
  have h3a := hodd 11 e₃ (he₃ 11 rfl)
  have h3b := hle3 11 e₃ (he₃ 11 rfl) ((local_bound hKF hB hbad ht₀ ht₀L ht₀b 11).2.2 rfl).1
  refine ⟨e₂, e₃, e₀, ey, by omega, by omega, by omega, by omega, he₀, hey, hBz, hw1', he₂, he₃⟩

theorem orderOf_b₁b₂ (hB : FF81Basis b L B b₁ b₂ b₃) : orderOf (b₁ * b₂) = 3 := by
  rw [← ε3_y]; exact hB.orderOf_ε3 (by decide)

theorem sl3_ineq (hKF2 : KF_Sp6SL3) (hKF3 : KF_SL32Fix) (hB : FF81Basis b L B b₁ b₂ b₃)
    {U W : Subgroup G} (hU : IsPGroup 2 U) (hWU : W ≤ U)
    (hn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hUL : L ≤ Nor U) (hWL : L ≤ Nor W) :
    Nat.card U * Nat.card ↥(W ⊓ Cen (b₁ * b₂)) ^ 4 ≤
      Nat.card W * Nat.card ↥(U ⊓ Cen (b₁ * b₂)) ^ 4 := by
  obtain ⟨K, hKL, hK, hyK⟩ := hKF2 G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem
    hB.selfcen hB.monoL_stab
  exact hKF3 G K U W hK hU hWU hn (hKL.trans hUL) (hKL.trans hWL) _ hyK (orderOf_b₁b₂ hB)

theorem sl3_exp (hKF2 : KF_Sp6SL3) (hKF3 : KF_SL32Fix) (hB : FF81Basis b L B b₁ b₂ b₃)
    {U W : Subgroup G} (hU : IsPGroup 2 U) (hWU : W ≤ U)
    (hn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hUL : L ≤ Nor U) (hWL : L ≤ Nor W)
    {eU eW eUy eWy : ℕ} (hcU : Nat.card U = 2 ^ eU) (hcW : Nat.card W = 2 ^ eW)
    (hcUy : Nat.card ↥(U ⊓ Cen (b₁ * b₂)) = 2 ^ eUy)
    (hcWy : Nat.card ↥(W ⊓ Cen (b₁ * b₂)) = 2 ^ eWy) : eU + 4 * eWy ≤ eW + 4 * eUy := by
  have h := sl3_ineq hKF2 hKF3 hB hU hWU hn hUL hWL
  rw [hcU, hcW, hcUy, hcWy, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at h
  have := pow_le_two_pow h
  omega

theorem comm_of_hyp_ne (hB : FF81Basis b L B b₁ b₂ b₃) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTt : T ≤ Cen t₀) (hTN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor T) (ht₀ : t₀ * t₀ = 1)
    (hT' : ⁅T, T⁆ ≤ Subgroup.zpowers t₀)
    (hTB : T ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) ≤ Subgroup.zpowers t₀) {i j : Fin 13}
    (hij : i ≠ j) {u v : G} (hu : u ∈ T ⊓ CenS (hyp b₁ b₂ b₃ i))
    (hv : v ∈ T ⊓ CenS (hyp b₁ b₂ b₃ j)) : u * v = v * u := by
  obtain ⟨x, hxj, hxi⟩ := exists_mem_hyp_not_mem i j hij
  have hx0 : x ≠ 0 := fun h => hxi (by rw [h]; simp [dot])
  have hxj' : ε3 b₁ b₂ b₃ x ∈ hyp b₁ b₂ b₃ j := (hB.mem_hyp j x).2 hxj
  have hvt : v * t₀ = t₀ * v := Subgroup.mem_centralizer_singleton_iff.mp (hTt hv.1)
  have hY := le_cen_of_comm_mem (Y := T ⊓ CenS (hyp b₁ b₂ b₃ i)) (t := v) (t₀ := t₀)
    (x := ε3 b₁ b₂ b₃ x) (hT.to_le inf_le_left) ht₀ (inf_le_left.trans hTt)
    (fun y hy => by
      have := hT' (Subgroup.commutator_mem_commutator hy.1 hv.1)
      rwa [commutatorElement_def] at this)
    (hB.orderOf_ε3 hx0) (mem_nor_inf_cenS_hyp hB (ε3_mem x) (hTN (ε3_mem x)) i)
    (Subgroup.mem_centralizer_iff.mp hv.2 _ hxj')
    (by
      rw [inf_cenS_hyp_inf_cen hB T i hxi]
      refine hTB.trans (Subgroup.zpowers_le.mpr ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hvt.symm)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hY hu)

theorem le_cenS_of_axb {Y S : Subgroup G} {x : G} (hY : IsPGroup 2 Y) (hY8 : Nat.card Y = 8)
    (hS : IsPGroup 2 S) (hSY : S ≤ Nor Y) (hx : orderOf x = 3) (hxY : x ∈ Nor Y)
    (hxS : ∀ s ∈ S, x * s = s * x) (ht₀ : orderOf t₀ = 2) (ht₀Y : t₀ ∈ Y)
    (ht₀S : ∀ s ∈ S, t₀ * s = s * t₀) (ht₀x : t₀ * x = x * t₀)
    (hfix : Y ⊓ Cen x ≤ Subgroup.zpowers t₀) : Y ≤ CenS S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Y ⊓ CenS S with hD
  have ht₀D : t₀ ∈ D := ⟨ht₀Y, Subgroup.mem_centralizer_iff.mpr fun s hs => (ht₀S s hs).symm⟩
  have hxc : x ∈ Cen t₀ := Subgroup.mem_centralizer_singleton_iff.mpr ht₀x.symm
  have hDx : ¬ D ≤ Cen x := by
    intro hle
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) 2 := by
      rw [Nat.card_zpowers, hx]; norm_num
    have hRB : ⁅Subgroup.zpowers x, S⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr fun s hs => (hxS s hs).symm)
    have hYx := CFSG.RankThree.PartTwo.Sec18.Item188Proof.centralizes_of_thompson_AxB
      (p := 2) (P := Y) (R := Subgroup.zpowers x) (B := S) hY hcop hS
      (Subgroup.zpowers_le.mpr hxY) hSY hRB (by
        intro d hd
        have : d ∈ Cen x := hle hd
        rw [← cenS_zpowers] at this
        exact this)
    rw [← CenS, cenS_zpowers] at hYx
    have h := Subgroup.card_le_of_le ((le_inf le_rfl hYx).trans hfix)
    rw [hY8, card_zpowers_t₀ ht₀] at h
    omega
  have hDcx : D ⊓ Cen x = Subgroup.zpowers t₀ :=
    le_antisymm ((inf_le_inf_right _ inf_le_left).trans hfix)
      (Subgroup.zpowers_le.mpr ⟨ht₀D, Subgroup.mem_centralizer_singleton_iff.mpr ht₀x⟩)
  have hxD : x ∈ Nor D :=
    mem_nor_inf hxY (mem_nor_cenS fun s hs => hxS s hs)
  have hE := card_modEq_card_inf_cen hx hxD
  rw [hDcx, card_zpowers_t₀ ht₀] at hE
  obtain ⟨n, hn⟩ := card_eq_two_pow (hY.to_le (inf_le_left : D ≤ Y))
  rw [hn] at hE
  have hodd := two_pow_odd_of_modEq hE
  have hn3 : n ≤ 3 := by
    have := Subgroup.card_le_of_le (inf_le_left : D ≤ Y)
    rw [hn, hY8] at this
    exact pow_le_two_pow (n := 3) this
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hDx ((eq_zpowers_of_card ht₀ ht₀D (by rw [hn]; norm_num)).le.trans
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ht₀x)))
  have hn3' : n = 3 := by omega
  have hDY : D = Y := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hn, hY8, hn3']; norm_num)
  rw [← hDY]
  exact inf_le_right

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
