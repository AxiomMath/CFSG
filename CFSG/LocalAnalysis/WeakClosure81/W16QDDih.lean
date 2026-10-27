module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDCfg
public import CFSG.Quasithin.Background.D2Z2
public import CFSG.Quasithin.Background.C1PackC127Aux
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Dihedral2p (X : Type) [Group X] (Y : Subgroup X) (p : ℕ) : Prop where
  card_Y : Nat.card Y = 2
  sup_eq : Y ⊔ fusionOddCore X = ⊤
  prime : p.Prime
  card_O : Nat.card (fusionOddCore X) = p
  gen : Subgroup.normalClosure (Y : Set X) = ⊤

private theorem w16q_fusionOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    fusionOddCore H = CFSG.pPrimeCore 2 H := by
  unfold fusionOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

namespace Dihedral2p

variable {X : Type} [Group X] {Y : Subgroup X} {p : ℕ}

private theorem w16q_sq_eq_one [Finite X] (h : Dihedral2p X Y p) {y : X} (hy : y ∈ Y) :
    y ^ 2 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 = orderOf y * k := by
    have h1 := Subgroup.orderOf_dvd_natCard Y hy
    rwa [h.card_Y] at h1
  calc y ^ 2 = (y ^ orderOf y) ^ k := by rw [← pow_mul, ← hk]
    _ = 1 := by rw [pow_orderOf_eq_one, one_pow]

theorem odd [Finite X] (h : Dihedral2p X Y p) : Odd p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
  rw [← w16q_fusionOddCore_eq_pPrimeCore X, h.card_O] at hcop
  exact Nat.coprime_two_left.mp hcop

private theorem w16q_inf_eq_bot [Finite X] (h : Dihedral2p X Y p) :
    Y ⊓ fusionOddCore X = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxY, hxO⟩ := hx
  have h1 : orderOf x ∣ 2 := by
    have h2 := Subgroup.orderOf_dvd_natCard Y hxY
    rwa [h.card_Y] at h2
  have h2 : orderOf x ∣ p := by
    have h3 := Subgroup.orderOf_dvd_natCard (fusionOddCore X) hxO
    rwa [h.card_O] at h3
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr h.odd
  have hdvd : orderOf x ∣ 1 := by
    have hg := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd 2 p = 1 from hcop] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem card_eq [Finite X] (h : Dihedral2p X Y p) : Nat.card X = 2 * p := by
  have hinf := h.w16q_inf_eq_bot
  have h1 := Subgroup.relIndex_mul_card (H := fusionOddCore X) (K := Y ⊔ fusionOddCore X)
  rw [Subgroup.relIndex_sup_right Y (fusionOddCore X), inf_eq_left.mpr le_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := fusionOddCore X) (K := Y)
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, h.card_Y] at h2
  rw [h2, h.card_O] at h1
  rw [h.sup_eq, Subgroup.card_top] at h1
  exact h1.symm

theorem inv [Finite X] (h : Dihedral2p X Y p) {y : X} (hy : y ∈ Y) (hy1 : y ≠ 1) {o : X}
    (ho : o ∈ fusionOddCore X) : y * o * y⁻¹ = o⁻¹ := by
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hodd := h.odd
  have hy2 : y ^ 2 = 1 := h.w16q_sq_eq_one hy
  have hyinv : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
  have hp2 : p ≠ 2 := by
    intro hp
    rw [hp] at hodd
    norm_num at hodd
  have hOpg : IsPGroup p (fusionOddCore X) :=
    IsPGroup.of_card (show Nat.card ↥(fusionOddCore X) = p ^ 1 by
      rw [pow_one]; exact h.card_O)
  have hOcyc : IsCyclic (fusionOddCore X) := isCyclic_of_prime_card h.card_O
  have hnorm : ∀ z ∈ fusionOddCore X, y * z * y⁻¹ ∈ fusionOddCore X :=
    fun z hz => (inferInstance : (fusionOddCore X).Normal).conj_mem z hz y
  rcases CFSG.Quasithin.involution_on_cyclic hp2 hOpg hOcyc hy2 hnorm with hfix | hinv
  · exfalso
    have hy_cent : y ∈ Subgroup.centralizer (fusionOddCore X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h3 := hfix z hz
      rw [hyinv] at h3
      calc z * y = (y * z * y) * y := by rw [h3]
        _ = y * z := by rw [mul_assoc, ← pow_two, hy2, mul_one]
    have ho2 : orderOf y = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hy2) with h1 | h2
      · exact absurd h1 (fun hh => hy1 (orderOf_eq_one_iff.mp hh))
      · exact h2
    have hYcent : Y ≤ Subgroup.centralizer (fusionOddCore X : Set X) := by
      have hYeq : Subgroup.zpowers y = Y :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
          (by rw [Nat.card_zpowers, ho2, h.card_Y])
      rw [← hYeq]
      exact Subgroup.zpowers_le.mpr hy_cent
    have hcomm' : ∀ o ∈ fusionOddCore X, ∀ y' ∈ Y, o * y' * o⁻¹ = y' := by
      intro o ho y' hy'
      have h4 := Subgroup.mem_centralizer_iff.mp (hYcent hy') o ho
      rw [h4]; group
    have hOnorm : fusionOddCore X ≤ Subgroup.normalizer (Y : Set X) := by
      intro o ho
      rw [Subgroup.mem_normalizer_iff]
      intro y'
      constructor
      · intro hy'
        rw [hcomm' o ho y' hy']
        exact hy'
      · intro h'
        have h4 := hcomm' o⁻¹ (Subgroup.inv_mem _ ho) (o * y' * o⁻¹) h'
        rw [show o⁻¹ * (o * y' * o⁻¹) * (o⁻¹)⁻¹ = y' by group] at h4
        rwa [h4]
    have htop : (⊤ : Subgroup X) ≤ Subgroup.normalizer (Y : Set X) := by
      rw [← h.sup_eq]
      exact sup_le le_normalizer hOnorm
    have hYN : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
    have hYtop : Y = ⊤ := by
      rw [← Subgroup.normalClosure_eq_self Y, h.gen]
    have hc : Nat.card Y = Nat.card X := by rw [hYtop, Subgroup.card_top]
    rw [h.card_Y, h.card_eq] at hc
    have hp2' : 2 ≤ p := h.prime.two_le
    omega
  · exact hinv o ho

theorem mem_of_conj_le [Finite X] (h : Dihedral2p X Y p) {z : X}
    (hz : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) : z ∈ Y := by
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hinf := h.w16q_inf_eq_bot
  have hzX : z ∈ Y ⊔ fusionOddCore X := by
    rw [h.sup_eq]; exact Subgroup.mem_top z
  obtain ⟨y', hy'Y, o', ho'O, rfl⟩ := (Subgroup.mem_sup_of_normal_right.mp hzX)
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have h2 := h.card_Y
    rw [hbot, Subgroup.card_bot] at h2
    norm_num at h2
  obtain ⟨y₁, hy₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
  have hmemY : (y₁ : X) ∈ Y := y₁.2
  have hy₁1' : (y₁ : X) ≠ 1 := fun hh => hy₁1 (Subtype.ext hh)
  have hmain : o' * (y₁ : X) * o'⁻¹ ∈ Y := by
    have h1 := hz (y₁ : X) y₁.2
    have h2 : o' * (y₁ : X) * o'⁻¹ =
        y'⁻¹ * ((y' * o') * (y₁ : X) * (y' * o')⁻¹) * y' := by group
    rw [h2]
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy'Y) h1) hy'Y
  have ho'inv : (y₁ : X) * o'⁻¹ * (y₁ : X)⁻¹ = o' := by
    have h3 := h.inv hmemY hy₁1' (Subgroup.inv_mem _ ho'O)
    simpa using h3
  have ho2Y : o' ^ 2 ∈ Y := by
    have h3 : o' * (y₁ : X) * o'⁻¹ = o' ^ 2 * (y₁ : X) := by
      calc o' * (y₁ : X) * o'⁻¹
          = o' * ((y₁ : X) * o'⁻¹ * (y₁ : X)⁻¹) * (y₁ : X) := by group
        _ = o' * o' * (y₁ : X) := by rw [ho'inv]
        _ = o' ^ 2 * (y₁ : X) := by rw [pow_two]
    rw [h3] at hmain
    have h4 := Y.mul_mem hmain (Y.inv_mem hmemY)
    simpa [mul_assoc] using h4
  have ho2 : o' ^ 2 = 1 := by
    have h4 : o' ^ 2 ∈ Y ⊓ fusionOddCore X :=
      ⟨ho2Y, (fusionOddCore X).pow_mem ho'O 2⟩
    rwa [hinf, Subgroup.mem_bot] at h4
  have ho'1 : o' = 1 := by
    have hodd' : Odd (orderOf o') := by
      have hdvd : orderOf o' ∣ Nat.card (fusionOddCore X) :=
        Subgroup.orderOf_dvd_natCard _ ho'O
      rw [h.card_O] at hdvd
      exact Odd.of_dvd_nat h.odd hdvd
    have h2 : orderOf o' ∣ 2 := orderOf_dvd_of_pow_eq_one ho2
    have hone : orderOf o' = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
      · exact h1
      · rw [h2'] at hodd'; norm_num at hodd'
    exact orderOf_eq_one_iff.mp hone
  simpa [ho'1] using hy'Y

theorem orderOf_prod [Finite X] (h : Dihedral2p X Y p) {y : X} (hy : y ∈ Y) (hy1 : y ≠ 1)
    {o : X} (ho : o ∈ fusionOddCore X) (ho1 : o ≠ 1) : orderOf (y * (o⁻¹ * y * o)) = p := by
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hodd := h.odd
  have hy2 : y ^ 2 = 1 := h.w16q_sq_eq_one hy
  have hyinv : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
  have hop : orderOf o = p := by
    have hdvd : orderOf o ∣ Nat.card (fusionOddCore X) :=
      Subgroup.orderOf_dvd_natCard _ ho
    rw [h.card_O] at hdvd
    rcases (Nat.dvd_prime h.prime).1 hdvd with h1 | hp
    · exact absurd h1 (fun hh => ho1 (orderOf_eq_one_iff.mp hh))
    · exact hp
  have hinv : y * o⁻¹ * y = o := by
    have h3 := h.inv hy hy1 (Subgroup.inv_mem _ ho)
    rw [hyinv, inv_inv] at h3
    exact h3
  have hprod : y * (o⁻¹ * y * o) = o ^ 2 := by
    rw [show y * (o⁻¹ * y * o) = (y * o⁻¹ * y) * o by group, hinv, pow_two]
  rw [hprod]
  have hcop : (orderOf o).Coprime 2 := by
    rw [hop]
    exact Nat.coprime_two_right.mpr hodd
  rw [Nat.Coprime.orderOf_pow hcop, hop]

theorem exists_mulEquiv_psl [Finite X] (h : Dihedral2p X Y 3) :
    Nonempty (X ≃* PSL(2, GaloisField 2 1)) := by
  have hcard : Nat.card X = 6 := by simpa using h.card_eq
  have hO3 : Nat.card (fusionOddCore X) = 3 := h.card_O
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have h2 := h.card_Y
    rw [hbot, Subgroup.card_bot] at h2
    norm_num at h2
  have hOne : fusionOddCore X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hO3
    norm_num at hO3
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
  obtain ⟨o, ho1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hOne
  have hyY : (y : X) ∈ Y := y.2
  have hoO : (o : X) ∈ fusionOddCore X := o.2
  have hy1' : (y : X) ≠ 1 := fun hh => hy1 (Subtype.ext hh)
  have ho1' : (o : X) ≠ 1 := fun hh => ho1 (Subtype.ext hh)
  have ho3 : orderOf (o : X) = 3 := by
    have hdvd : orderOf (o : X) ∣ Nat.card (fusionOddCore X) :=
      Subgroup.orderOf_dvd_natCard _ hoO
    rw [hO3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd h1 (fun hh => ho1' (orderOf_eq_one_iff.mp hh))
    · exact h3
  have hnc : (y : X) * (o : X) ≠ (o : X) * (y : X) := by
    intro hcomm
    have hy2 : (y : X) ^ 2 = 1 := h.w16q_sq_eq_one hyY
    have hyinv : (y : X)⁻¹ = (y : X) := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
    have h3 := h.inv hyY hy1' hoO
    rw [hyinv] at h3
    have h4 : (y : X) * (o : X) * (y : X) = (o : X) := by
      calc (y : X) * (o : X) * (y : X) = ((y : X) * (o : X)) * (y : X) := rfl
        _ = ((o : X) * (y : X)) * (y : X) := by rw [hcomm]
        _ = (o : X) * ((y : X) * (y : X)) := by rw [mul_assoc]
        _ = (o : X) := by rw [← pow_two, hy2, mul_one]
    have hoinv : (o : X) = (o : X)⁻¹ := by
      calc (o : X) = (y : X) * (o : X) * (y : X) := h4.symm
        _ = (o : X)⁻¹ := h3
    have ho2 : (o : X) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hoinv]
      exact inv_mul_cancel _
    have hdvd : orderOf (o : X) ∣ 2 := orderOf_dvd_of_pow_eq_one ho2
    rw [ho3] at hdvd
    norm_num at hdvd
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six hcard
    ⟨(y : X), (o : X), hnc⟩
  exact ⟨e.trans CFSG.Quasithin.permThreeEquivPSL⟩

end Dihedral2p

theorem pow_comm_mem {I W : Subgroup G} {y : G} (hyI : y ∈ normalizer (I : Set G))
    (hyt : ∀ i ∈ I, y * i * y⁻¹ * i⁻¹ ∈ W) (k : ℕ) :
    ∀ i ∈ I, y ^ k * i * (y ^ k)⁻¹ * i⁻¹ ∈ W := by
  induction k with
  | zero =>
    intro i _
    simpa using W.one_mem
  | succ k ih =>
    intro i hi
    have hyk : y ^ k ∈ Subgroup.normalizer (I : Set G) :=
      Subgroup.pow_mem (Subgroup.normalizer (I : Set G)) hyI k
    have hjI : y ^ k * i * (y ^ k)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp hyk i).1 hi
    have h1 : y * (y ^ k * i * (y ^ k)⁻¹) * y⁻¹ * (y ^ k * i * (y ^ k)⁻¹)⁻¹ ∈ W :=
      hyt _ hjI
    have h2 : y ^ k * i * (y ^ k)⁻¹ * i⁻¹ ∈ W := ih i hi
    have hsplit : y ^ (k + 1) * i * (y ^ (k + 1))⁻¹ * i⁻¹ =
        (y * (y ^ k * i * (y ^ k)⁻¹) * y⁻¹ * (y ^ k * i * (y ^ k)⁻¹)⁻¹) *
          (y ^ k * i * (y ^ k)⁻¹ * i⁻¹) := by
      rw [pow_succ']
      group
    rw [hsplit]
    exact W.mul_mem h1 h2

private theorem w16q_cube_centralizes_of_card_le_four {W : Subgroup G} {y : G}
    (hyW : y ∈ normalizer (W : Set G)) (hW : Nat.card W ≤ 4) (hy : Odd (orderOf y)) :
    ∀ w ∈ W, y ^ 3 * w * (y ^ 3)⁻¹ = w := by
  let σ : Equiv.Perm W :=
    { toFun := fun w => ⟨y * (w : G) * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyW (w : G)).1 w.2⟩
      invFun := fun w => ⟨y⁻¹ * (w : G) * y,
        (Subgroup.mem_normalizer_iff''.mp hyW (w : G)).1 w.2⟩
      left_inv := by intro w; apply Subtype.ext; group
      right_inv := by intro w; apply Subtype.ext; group }
  have hpow : ∀ k : ℕ, ∀ w : W, ((σ ^ k) w : G) = y ^ k * (w : G) * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      have h1 : (σ ^ (k + 1)) w = (σ ^ k) (σ w) := by rw [pow_succ]; rfl
      have h2 : (σ w : G) = y * (w : G) * y⁻¹ := rfl
      calc ((σ ^ (k + 1)) w : G) = ((σ ^ k) (σ w) : G) := by rw [h1]
        _ = y ^ k * ((σ w : W) : G) * (y ^ k)⁻¹ := ih (σ w)
        _ = y ^ k * (y * (w : G) * y⁻¹) * (y ^ k)⁻¹ := by rw [h2]
        _ = y ^ (k + 1) * (w : G) * (y ^ (k + 1))⁻¹ := by rw [pow_succ]; group
  have horder : orderOf σ ∣ orderOf y := by
    apply orderOf_dvd_of_pow_eq_one
    ext w
    rw [hpow (orderOf y) w, pow_orderOf_eq_one]
    simp
  have h24 : orderOf σ ∣ 24 := by
    have h1 : orderOf σ ∣ Nat.card (Equiv.Perm W) := by
      simpa using Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (Equiv.Perm W))
        (Subgroup.mem_top σ)
    rw [Nat.card_perm] at h1
    have h2 : (Nat.card W).factorial ∣ 24 := by
      simpa [show Nat.factorial 4 = 24 by decide] using Nat.factorial_dvd_factorial hW
    exact h1.trans h2
  have h3dvd : orderOf σ ∣ 3 := by
    have hodd : Odd (orderOf σ) := Odd.of_dvd_nat hy horder
    have hcop : Nat.Coprime (orderOf σ) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
    have h24' : orderOf σ ∣ 2 ^ 3 * 3 := by simpa using h24
    exact hcop.dvd_of_dvd_mul_left h24'
  have hσ3 : σ ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).1 h3dvd
  intro w hw
  have h1 := hpow 3 ⟨w, hw⟩
  have h2 : (σ ^ 3) ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hσ3]; rfl
  have h3 := congrArg Subtype.val h2
  rw [h1] at h3
  exact h3

theorem cube_mem_centralizer_of_odd {I W : Subgroup G} (hI : IsElemAbelian 2 I) (hWI : W ≤ I)
    (hW : Nat.card W ≤ 4) {y : G} (hyI : y ∈ normalizer (I : Set G))
    (hyW : y ∈ normalizer (W : Set G)) (hyt : ∀ i ∈ I, y * i * y⁻¹ * i⁻¹ ∈ W)
    (hy : Odd (orderOf y)) : y ^ 3 ∈ centralizer (I : Set G) := by
  have hodd3 : Odd (orderOf (y ^ 3)) := Odd.of_dvd_nat hy (orderOf_pow_dvd (x := y) 3)
  have hV2 : ∀ v ∈ W, v ^ 2 = 1 := fun v hv => hI.2 v (hWI hv)
  have haV : ∀ v ∈ W, y ^ 3 * v * (y ^ 3)⁻¹ = v :=
    w16q_cube_centralizes_of_card_le_four hyW hW hy
  have hY : ∀ i ∈ I, y ^ 3 * i * (y ^ 3)⁻¹ * i⁻¹ ∈ W :=
    pow_comm_mem hyI hyt 3
  have hcent : ∀ i ∈ I, y ^ 3 * i * (y ^ 3)⁻¹ = i :=
    CFSG.Quasithin.C1Pack.eq_of_odd_order_stable hodd3 hV2 haV hY
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  have h3 := hcent i hi
  calc i * y ^ 3 = y ^ 3 * i * (y ^ 3)⁻¹ * y ^ 3 := by rw [h3]
    _ = y ^ 3 * i := by group

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

private theorem w16q_V₀_conj_le_iSub16 (d : DichCfg M V₀ V U S H φ) {x : G}
    (hx : x ∈ conjClosure V H) :
    V₀ ≤ iSub16 V H ∧ conjSubgroup V₀ x ≤ iSub16 V H := by
  have hxH : x ∈ H := d.cfg.conjClosure_le_H hx
  have hxN : x ∈ normalizer (iSub16 V H : Set G) := by
    have h := le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hxH
    simpa [iSub16] using h
  have hV₀I : V₀ ≤ iSub16 V H := le_sup_right.trans d.cfg.le_iSub16
  refine ⟨hV₀I, ?_⟩
  intro y hy
  have hy' : x * y * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hy
  exact (Subgroup.mem_normalizer_iff.mp hxN y).2 (hV₀I hy')

theorem sup_conj_le (d : DichCfg M V₀ V U S H φ) (hV₀ : mSub V₀ = 1) {x : G}
    (hx : x ∈ conjClosure V H) :
    V₀ ⊔ conjSubgroup V₀ x ≤ iSub16 V H ∧ Nat.card ↥(V₀ ⊔ conjSubgroup V₀ x) ≤ 4 := by
  obtain ⟨hV₀I, hJI⟩ := d.w16q_V₀_conj_le_iSub16 hx
  have hIab := Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  refine ⟨sup_le hV₀I hJI, ?_⟩
  have hV₀card : Nat.card V₀ = 2 := by
    have hp : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup d.cfg.cex.hyp.elemAbelian₀
    rw [card_eq_two_pow_mSub hp, hV₀, pow_one]
  have hJcard : Nat.card ↥(conjSubgroup V₀ x) = 2 := by
    rw [E3.card_conjSubgroup, hV₀card]
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ conjSubgroup V₀ x, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hIab (hV₀I ha) (hJI hb)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V₀
    (conjSubgroup V₀ x) hcomm).1
  rw [hV₀card, hJcard] at hprod
  have hprod' : Nat.card ↥(V₀ ⊔ conjSubgroup V₀ x) *
      Nat.card ↥(V₀ ⊓ conjSubgroup V₀ x) = 4 := by
    rw [hprod]
  have hdvd : Nat.card ↥(V₀ ⊔ conjSubgroup V₀ x) ∣ 4 := ⟨_, hprod'.symm⟩
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem prod_acts (d : DichCfg M V₀ V U S H φ) {v x : G} (hv : v ∈ V)
    (hx : x ∈ conjClosure V H) :
    v * (x⁻¹ * v * x) ∈ normalizer ((V₀ ⊔ conjSubgroup V₀ x : Subgroup G) : Set G) ∧
      ∀ i ∈ iSub16 V H, (v * (x⁻¹ * v * x)) * i * (v * (x⁻¹ * v * x))⁻¹ * i⁻¹ ∈
        V₀ ⊔ conjSubgroup V₀ x := by
  obtain ⟨hV₀I, hJI⟩ := d.w16q_V₀_conj_le_iSub16 hx
  have hIab := Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hxH : x ∈ H := d.cfg.conjClosure_le_H hx
  have hxN : x ∈ normalizer (iSub16 V H : Set G) := by
    have h := le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hxH
    simpa [iSub16] using h
  have hVcommJ : ∀ a ∈ V₀, ∀ b ∈ conjSubgroup V₀ x, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hIab (hV₀I ha) (hJI hb)
  have hdec : (↑(V₀ ⊔ conjSubgroup V₀ x) : Set G) =
      (↑V₀ : Set G) * (↑(conjSubgroup V₀ x) : Set G) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V₀ (conjSubgroup V₀ x) hVcommJ).2
  have hvfix : ∀ a ∈ V₀, v * a * v⁻¹ = a := by
    intro a ha
    have hcomm := B2F.isElemAbelian_comm d.cfg.cex.hyp.h6.elemAbelian hv
      (d.cfg.cex.hyp.h6.le ha)
    rw [hcomm]; group
  have hvJ : ∀ b ∈ conjSubgroup V₀ x, v * b * v⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ x := by
    intro b hb
    have hbI : b ∈ iSub16 V H := hJI hb
    have hconj := Cex16.comm_mem_V₀ d.cfg.cex (d.cfg.iSub16_le_tSub16 hbI).1 hv
    have h2 : v * b * v⁻¹ * b⁻¹ ∈ V₀ := by
      have := V₀.inv_mem hconj
      rwa [show (b * v * b⁻¹ * v⁻¹)⁻¹ = v * b * v⁻¹ * b⁻¹ by group] at this
    have h3 : v * b * v⁻¹ = (v * b * v⁻¹ * b⁻¹) * b := by group
    rw [h3]
    exact (V₀ ⊔ conjSubgroup V₀ x).mul_mem (Subgroup.mem_sup_left h2)
      (Subgroup.mem_sup_right hb)
  have hvW : ∀ w ∈ V₀ ⊔ conjSubgroup V₀ x, v * w * v⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ x := by
    intro w hw
    have hw' : w ∈ (↑V₀ : Set G) * (↑(conjSubgroup V₀ x) : Set G) := hdec ▸ hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    have h3 : v * (a * b) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) := by group
    rw [h3, hvfix a ha]
    exact (V₀ ⊔ conjSubgroup V₀ x).mul_mem (Subgroup.mem_sup_left ha) (hvJ b hb)
  have hv2 : v * v = 1 := by
    have h := d.cfg.cex.hyp.h6.elemAbelian.2 v hv
    rwa [pow_two] at h
  have hvN : v ∈ normalizer ((V₀ ⊔ conjSubgroup V₀ x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hvW w
    · intro h
      have h2 := hvW (v * w * v⁻¹) h
      have hvv : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, hv2]
      rw [hvv] at h2
      rwa [show v * (v * w * v) * v = w by
        calc v * (v * w * v) * v = (v * v) * w * (v * v) := by group
          _ = w := by rw [hv2, one_mul, mul_one]] at h2
  have hv'fix : ∀ b ∈ conjSubgroup V₀ x, (x⁻¹ * v * x) * b * (x⁻¹ * v * x)⁻¹ = b := by
    intro b hb
    have hbx : x * b * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hb
    have hcomm := B2F.isElemAbelian_comm d.cfg.cex.hyp.h6.elemAbelian hv
      (d.cfg.cex.hyp.h6.le hbx)
    calc (x⁻¹ * v * x) * b * (x⁻¹ * v * x)⁻¹
        = x⁻¹ * (v * (x * b * x⁻¹) * v⁻¹) * x := by group
      _ = x⁻¹ * (x * b * x⁻¹) * x := by rw [hcomm]; group
      _ = b := by group
  have hv'V₀ : ∀ a ∈ V₀, (x⁻¹ * v * x) * a * (x⁻¹ * v * x)⁻¹ ∈
      V₀ ⊔ conjSubgroup V₀ x := by
    intro a ha
    have hai : x * a * x⁻¹ ∈ iSub16 V H :=
      (Subgroup.mem_normalizer_iff.mp hxN a).1 (hV₀I ha)
    have h := Cex16.comm_mem_V₀ d.cfg.cex (d.cfg.iSub16_le_tSub16 hai).1 hv
    have h2 : v * (x * a * x⁻¹) * v⁻¹ * (x * a * x⁻¹)⁻¹ ∈ V₀ := by
      have := V₀.inv_mem h
      rwa [show ((x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ * v⁻¹)⁻¹ =
        v * (x * a * x⁻¹) * v⁻¹ * (x * a * x⁻¹)⁻¹ by group] at this
    have h4 : (x⁻¹ * v * x) * a * (x⁻¹ * v * x)⁻¹ =
        (x⁻¹ * (v * (x * a * x⁻¹) * v⁻¹ * (x * a * x⁻¹)⁻¹) * x) * a := by group
    rw [h4]
    refine (V₀ ⊔ conjSubgroup V₀ x).mul_mem (Subgroup.mem_sup_right ?_)
      (Subgroup.mem_sup_left ha)
    rw [mem_conjSubgroup_iff]
    rw [show x * (x⁻¹ * (v * (x * a * x⁻¹) * v⁻¹ * (x * a * x⁻¹)⁻¹) * x) * x⁻¹ =
      v * (x * a * x⁻¹) * v⁻¹ * (x * a * x⁻¹)⁻¹ by group]
    exact h2
  have hv'W : ∀ w ∈ V₀ ⊔ conjSubgroup V₀ x,
      (x⁻¹ * v * x) * w * (x⁻¹ * v * x)⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ x := by
    intro w hw
    have hw' : w ∈ (↑V₀ : Set G) * (↑(conjSubgroup V₀ x) : Set G) := hdec ▸ hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    have h3 : (x⁻¹ * v * x) * (a * b) * (x⁻¹ * v * x)⁻¹ =
        ((x⁻¹ * v * x) * a * (x⁻¹ * v * x)⁻¹) *
          ((x⁻¹ * v * x) * b * (x⁻¹ * v * x)⁻¹) := by group
    rw [h3, hv'fix b hb]
    exact (V₀ ⊔ conjSubgroup V₀ x).mul_mem (hv'V₀ a ha) (Subgroup.mem_sup_right hb)
  have hv'2 : (x⁻¹ * v * x) * (x⁻¹ * v * x) = 1 := by
    calc (x⁻¹ * v * x) * (x⁻¹ * v * x) = x⁻¹ * (v * v) * x := by group
      _ = 1 := by rw [hv2]; group
  have hv'N : (x⁻¹ * v * x) ∈
      normalizer ((V₀ ⊔ conjSubgroup V₀ x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hv'W w
    · intro h
      have h2 := hv'W (x⁻¹ * v * x * w * (x⁻¹ * v * x)⁻¹) h
      have hv'inv : (x⁻¹ * v * x)⁻¹ = x⁻¹ * v * x := by
        rw [inv_eq_iff_mul_eq_one, hv'2]
      rw [hv'inv] at h2
      rwa [show (x⁻¹ * v * x) * ((x⁻¹ * v * x) * w * (x⁻¹ * v * x)) *
        (x⁻¹ * v * x) = w by
        calc (x⁻¹ * v * x) * ((x⁻¹ * v * x) * w * (x⁻¹ * v * x)) * (x⁻¹ * v * x)
            = ((x⁻¹ * v * x) * (x⁻¹ * v * x)) * w *
              ((x⁻¹ * v * x) * (x⁻¹ * v * x)) := by group
          _ = w := by rw [hv'2, one_mul, mul_one]] at h2
  refine ⟨?_, ?_⟩
  · exact (Subgroup.normalizer
      ((V₀ ⊔ conjSubgroup V₀ x : Subgroup G) : Set G)).mul_mem hvN hv'N
  · intro i hi
    have hj : (x⁻¹ * v * x) * i * (x⁻¹ * v * x)⁻¹ * i⁻¹ ∈ conjSubgroup V₀ x := by
      have hai : x * i * x⁻¹ ∈ iSub16 V H := (Subgroup.mem_normalizer_iff.mp hxN i).1 hi
      have h := Cex16.comm_mem_V₀ d.cfg.cex (d.cfg.iSub16_le_tSub16 hai).1 hv
      have h2 : v * (x * i * x⁻¹) * v⁻¹ * (x * i * x⁻¹)⁻¹ ∈ V₀ := by
        have := V₀.inv_mem h
        rwa [show ((x * i * x⁻¹) * v * (x * i * x⁻¹)⁻¹ * v⁻¹)⁻¹ =
          v * (x * i * x⁻¹) * v⁻¹ * (x * i * x⁻¹)⁻¹ by group] at this
      rw [mem_conjSubgroup_iff]
      rw [show x * ((x⁻¹ * v * x) * i * (x⁻¹ * v * x)⁻¹ * i⁻¹) * x⁻¹ =
        v * (x * i * x⁻¹) * v⁻¹ * (x * i * x⁻¹)⁻¹ by group]
      exact h2
    have hvi : v * i * v⁻¹ * i⁻¹ ∈ V₀ := by
      have h := Cex16.comm_mem_V₀ d.cfg.cex (d.cfg.iSub16_le_tSub16 hi).1 hv
      have := V₀.inv_mem h
      rwa [show (i * v * i⁻¹ * v⁻¹)⁻¹ = v * i * v⁻¹ * i⁻¹ by group] at this
    have hsplit : (v * (x⁻¹ * v * x)) * i * (v * (x⁻¹ * v * x))⁻¹ * i⁻¹ =
        (v * ((x⁻¹ * v * x) * i * (x⁻¹ * v * x)⁻¹ * i⁻¹) * v⁻¹) *
          (v * i * v⁻¹ * i⁻¹) := by group
    rw [hsplit]
    refine (V₀ ⊔ conjSubgroup V₀ x).mul_mem ?_ (Subgroup.mem_sup_left hvi)
    exact (Subgroup.mem_normalizer_iff.mp hvN
      ((x⁻¹ * v * x) * i * (x⁻¹ * v * x)⁻¹ * i⁻¹)).1 (Subgroup.mem_sup_right hj)

private theorem w16q_odd_div_pow_padicValNat {n : ℕ} (hn : n ≠ 0) :
    Odd (n / 2 ^ padicValNat 2 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h
  obtain ⟨k, hk⟩ := h
  have hdvd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have hn_eq : n = 2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n) :=
    (Nat.mul_div_cancel' hdvd).symm
  have h2dvd : 2 ^ (padicValNat 2 n + 1) ∣ n := by
    refine ⟨k, ?_⟩
    conv_lhs => rw [hn_eq, hk]
    rw [pow_succ]
    ring
  have hle := (padicValNat_dvd_iff_le (p := 2) (a := n)
    (n := padicValNat 2 n + 1) hn).1 h2dvd
  omega

theorem exists_psl_of_dihedral [Finite X] (d : DichCfg M V₀ V U S H φ)
    (hn : E3.mQuot V (iSub16 V H) = 1) (hX : SevenK.barSub (conjClosure V H) φ V ⊔
      fusionOddCore X = ⊤) (hp : ∃ p : ℕ, p.Prime ∧ Nat.card (fusionOddCore X) = p)
    (hV₀ : mSub V₀ = 1) :
    ∃ ψ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H))),
      Function.Surjective ψ ∧ ψ.ker = (iSub16 V H).subgroupOf (conjClosure V H) := by
  obtain ⟨p, hpprime, hpcard⟩ := hp
  have hY2 : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := by
    rw [d.shape.1, hn, pow_one]
  have hD : Dihedral2p X (SevenK.barSub (conjClosure V H) φ V) p :=
    ⟨hY2, hX, hpprime, hpcard, d.normalClosure_eq_top⟩
  have hYne : SevenK.barSub (conjClosure V H) φ V ≠ ⊥ := by
    intro hbot
    have h2 := hY2
    rw [hbot, Subgroup.card_bot] at h2
    norm_num at h2
  have hOne : fusionOddCore X ≠ ⊥ := by
    intro hbot
    have h2 := hpcard
    rw [hbot, Subgroup.card_bot] at h2
    exact hpprime.ne_one h2.symm
  obtain ⟨ybar, hybar1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
  obtain ⟨obar, hobar1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hOne
  have hybarY : (ybar : X) ∈ SevenK.barSub (conjClosure V H) φ V := ybar.2
  have hobarO : (obar : X) ∈ fusionOddCore X := obar.2
  have hybar1' : (ybar : X) ≠ 1 := fun hh => hybar1 (Subtype.ext hh)
  have hobar1' : (obar : X) ≠ 1 := fun hh => hobar1 (Subtype.ext hh)
  obtain ⟨vk, hvkV, hφvk⟩ := SevenK.mem_barSub.mp hybarY
  obtain ⟨xk, hφxk⟩ := d.bar.surjective (⟨(obar : X), hobarO⟩ : ↥(fusionOddCore X))
  have hφvk' : φ vk = (ybar : X) := hφvk
  have hφxk' : φ xk = (obar : X) := hφxk
  let yk : ↥(conjClosure V H) := vk * (xk⁻¹ * vk * xk)
  have hykval : (yk : G) = (vk : G) * ((xk : G)⁻¹ * (vk : G) * (xk : G)) := rfl
  have hφyk : φ yk = (ybar : X) * ((obar : X)⁻¹ * (ybar : X) * (obar : X)) := by
    dsimp only [yk]
    simp only [map_mul, map_inv, hφvk', hφxk']
  have horder_φyk : orderOf (φ yk) = p := by
    rw [hφyk]
    exact hD.orderOf_prod ybar.2 hybar1' hobarO hobar1'
  let e : ℕ := 2 ^ padicValNat 2 (orderOf (yk : G))
  let y0k : ↥(conjClosure V H) := yk ^ e
  let y0 : G := y0k
  have he_dvd : e ∣ orderOf (yk : G) := pow_padicValNat_dvd
  have he_ne : e ≠ 0 := by dsimp only [e]; exact pow_ne_zero _ (by norm_num)
  have horder_y0 : orderOf y0 = orderOf (yk : G) / e := by
    have h := orderOf_pow' (yk : G) he_ne
    rw [Nat.gcd_eq_right he_dvd] at h
    simpa [y0, y0k] using h
  have hodd_y0 : Odd (orderOf y0) := by
    rw [horder_y0]
    exact w16q_odd_div_pow_padicValNat (n := orderOf (yk : G))
      (Nat.pos_iff_ne_zero.mp (orderOf_pos (yk : G)))
  have hφy0 : φ y0k = (φ yk) ^ e := by
    dsimp only [y0k]
    rw [map_pow]
  have horder_φy0 : orderOf (φ y0k) = p := by
    rw [hφy0]
    have hcop : (orderOf (φ yk)).Coprime e := by
      rw [horder_φyk]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hD.odd)
    rw [Nat.Coprime.orderOf_pow hcop, horder_φyk]
  have hodd_φy0 : Odd (orderOf (φ y0k)) := by rw [horder_φy0]; exact hD.odd
  have hykN : (yk : G) ∈ normalizer (iSub16 V H : Set G) := by
    have h := le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
      (d.cfg.conjClosure_le_H yk.2)
    simpa [iSub16] using h
  have hy0N : (y0 : G) ∈ normalizer (iSub16 V H : Set G) := by
    have hval : (y0 : G) = (yk : G) ^ e := rfl
    rw [hval]
    exact Subgroup.pow_mem (Subgroup.normalizer (iSub16 V H : Set G)) hykN e
  have hprod := d.prod_acts hvkV xk.2
  have hykW : (yk : G) ∈
      normalizer ((V₀ ⊔ conjSubgroup V₀ (xk : G) : Subgroup G) : Set G) := by
    have h := hprod.1
    rwa [← hykval] at h
  have hy0W : (y0 : G) ∈
      normalizer ((V₀ ⊔ conjSubgroup V₀ (xk : G) : Subgroup G) : Set G) := by
    have hval : (y0 : G) = (yk : G) ^ e := rfl
    rw [hval]
    exact Subgroup.pow_mem
      (Subgroup.normalizer ((V₀ ⊔ conjSubgroup V₀ (xk : G) : Subgroup G) : Set G)) hykW e
  have hyt : ∀ i ∈ iSub16 V H,
      (yk : G) * i * (yk : G)⁻¹ * i⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ (xk : G) := by
    intro i hi
    have h := hprod.2 i hi
    rwa [← hykval] at h
  have hyt0 : ∀ i ∈ iSub16 V H,
      (y0 : G) * i * (y0 : G)⁻¹ * i⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ (xk : G) := by
    intro i hi
    have hval : (y0 : G) = (yk : G) ^ e := rfl
    rw [hval]
    exact pow_comm_mem hykN hyt e i hi
  have hIab := Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hsup := d.sup_conj_le hV₀ xk.2
  have hcube : (y0 : G) ^ 3 ∈ centralizer (iSub16 V H : Set G) :=
    cube_mem_centralizer_of_odd hIab hsup.1 hsup.2 hy0N hy0W hyt0 hodd_y0
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 d.cfg.cex.hyp.ne_bot
  have hwV₀ : (w : G) ∈ V₀ := w.2
  have hwI : (w : G) ∈ iSub16 V H := d.cfg.le_iSub16 (Subgroup.mem_sup_right hwV₀)
  have hw1' : (w : G) ≠ 1 := fun hh => hw1 (Subtype.ext hh)
  have hzM : (y0 : G) ^ 3 ∈ M :=
    d.cfg.cex.hyp.centralizer_le hwV₀ hw1'
      ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwI)) hcube)
  have hzNV : (y0 : G) ^ 3 ∈ normalizer (V : Set G) := by
    rw [d.cfg.cex.hyp.h6.normalizer_eq]
    exact hzM
  have hnormY : ∀ y' ∈ SevenK.barSub (conjClosure V H) φ V,
      φ (y0k ^ 3) * y' * (φ (y0k ^ 3))⁻¹ ∈ SevenK.barSub (conjClosure V H) φ V := by
    intro y' hy'
    obtain ⟨k', hk'V, hφk'⟩ := SevenK.mem_barSub.mp hy'
    have hzkV : (y0 : G) ^ 3 * (k' : G) * ((y0 : G) ^ 3)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hzNV (k' : G)).1 hk'V
    refine SevenK.mem_barSub.mpr ⟨y0k ^ 3 * k' * (y0k ^ 3)⁻¹, ?_, ?_⟩
    · have hval : ((y0k ^ 3 * k' * (y0k ^ 3)⁻¹ : ↥(conjClosure V H)) : G) =
          (y0 : G) ^ 3 * (k' : G) * ((y0 : G) ^ 3)⁻¹ := rfl
      rw [hval]; exact hzkV
    · simp only [map_mul, map_inv, hφk']
  have hφzY : φ (y0k ^ 3) ∈ SevenK.barSub (conjClosure V H) φ V :=
    hD.mem_of_conj_le hnormY
  have hord2 : orderOf (φ (y0k ^ 3)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (hD.w16q_sq_eq_one hφzY)
  have hodd_φz : Odd (orderOf (φ (y0k ^ 3))) := by
    have hdvd : orderOf (φ (y0k ^ 3)) ∣ orderOf (φ y0k) := by
      have h : φ (y0k ^ 3) = (φ y0k) ^ 3 := by rw [map_pow]
      rw [h]; exact orderOf_pow_dvd (x := φ y0k) 3
    exact Odd.of_dvd_nat hodd_φy0 hdvd
  have hφz1 : φ (y0k ^ 3) = 1 := by
    have hone : orderOf (φ (y0k ^ 3)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h1 | h2
      · exact h1
      · rw [h2] at hodd_φz; norm_num at hodd_φz
    exact orderOf_eq_one_iff.mp hone
  have hφy03 : (φ y0k) ^ 3 = 1 := by
    rw [← map_pow (φ) y0k 3]
    exact hφz1
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by
      rw [← horder_φy0]
      exact orderOf_dvd_of_pow_eq_one hφy03
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd h1 hpprime.ne_one
    · exact h3
  have hD3 : Dihedral2p X (SevenK.barSub (conjClosure V H) φ V) 3 := hp3 ▸ hD
  obtain ⟨eiso⟩ := hD3.exists_mulEquiv_psl
  rw [hn]
  refine ⟨eiso.toMonoidHom.comp φ, eiso.surjective.comp d.bar.surjective, ?_⟩
  have hker : (eiso.toMonoidHom.comp φ).ker = φ.ker := by
    ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      refine eiso.injective ?_
      change eiso.toMonoidHom (φ k) = eiso.toMonoidHom 1
      rw [h, map_one]
    · intro h
      rw [h, map_one]
  rw [hker]
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact d.bar.ker_iff k


end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
