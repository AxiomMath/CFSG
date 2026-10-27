module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichAut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X}

private theorem w16ex_odd_card_fusionOddCore (H : Type) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  have h : fusionOddCore H = CFSG.pPrimeCore 2 H := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))

private theorem w16ex_card_eq_two_of_shape166 {Y : Subgroup X} (hX : Shape166 X Y 1) :
    Nat.card Y = 2 := by
  simpa using hX.1

private theorem w16ex_sup_oddCore_eq_top_of_shape166 {Y : Subgroup X} (hX : Shape166 X Y 1) :
    Y ⊔ fusionOddCore X = ⊤ := by
  rcases hX.2 with ⟨h1, -⟩ | ⟨-, hsup, -⟩
  · exact absurd h1 (by norm_num)
  · exact hsup

private theorem w16ex_zpowers_eq_of_isElemAbelian_card_two {Y : Subgroup X}
    (hY : IsElemAbelian 2 Y) (hYcard : Nat.card Y = 2) {t : X} (ht : t ∈ Y) (ht1 : t ≠ 1) :
    Subgroup.zpowers t = Y := by
  have ht2 : t * t = 1 := by
    have h := hY.2 t ht
    simpa [pow_two] using h
  have horder : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ht1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ht) ?_
  simp [hYcard, Nat.card_zpowers, horder]

private theorem w16ex_inf_oddCore_eq_bot_of_card_two {Y : Subgroup X} (hYcard : Nat.card Y = 2)
    (hodd : Odd (Nat.card (fusionOddCore X))) : Y ⊓ fusionOddCore X = ⊥ := by
  have hcop : Nat.Coprime 2 (Nat.card (fusionOddCore X)) := Nat.coprime_two_left.mpr hodd
  have hdvdY : Nat.card ↥(Y ⊓ fusionOddCore X) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdN : Nat.card ↥(Y ⊓ fusionOddCore X) ∣ Nat.card (fusionOddCore X) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hdvd1 : Nat.card ↥(Y ⊓ fusionOddCore X) ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (hYcard ▸ hdvdY) hdvdN
  exact Subgroup.eq_bot_of_card_eq (Y ⊓ fusionOddCore X) (Nat.dvd_one.1 hdvd1)

private theorem w16ex_commutator_zpowers_eq_oddCore_of_shape166
    (hY : IsElemAbelian 2 Y) (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y 1)
    {t : X} (ht : t ∈ Y) (ht1 : t ≠ 1) :
    ⁅fusionOddCore X, Subgroup.zpowers t⁆ = fusionOddCore X := by
  let N : Subgroup X := fusionOddCore X
  haveI hNnormal : N.Normal := fusionOddCore_normal X
  have hYcard : Nat.card Y = 2 := w16ex_card_eq_two_of_shape166 hX
  have hsup : Y ⊔ N = ⊤ := w16ex_sup_oddCore_eq_top_of_shape166 hX
  have hYt : Subgroup.zpowers t = Y :=
    w16ex_zpowers_eq_of_isElemAbelian_card_two hY hYcard ht ht1
  have hodd : Odd (Nat.card N) := w16ex_odd_card_fusionOddCore X
  have hinf : Y ⊓ N = ⊥ := w16ex_inf_oddCore_eq_bot_of_card_two hYcard hodd
  set M : Subgroup X := ⁅N, Subgroup.zpowers t⁆ with hM
  have hMnle : M ≤ N := by
    rw [hM]
    exact Subgroup.commutator_le_left (H₁ := N) (H₂ := Subgroup.zpowers t)
  have ht_norm : t ∈ Subgroup.normalizer (M : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hM, Subgroup.map_commutator]
    congr 1
    · exact Subgroup.Normal.map_conj_eq (H := N) t
    · rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure]
      congr 1
      ext z
      simp [MulAut.conj_apply]
  have hYnorm : Y ≤ Subgroup.normalizer (M : Set X) := by
    rw [← hYt]; exact Subgroup.zpowers_le.mpr ht_norm
  have hKmul : (↑(M ⊔ Y) : Set X) = ((M : Set X) * (Y : Set X) : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M Y hYnorm
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hY.1.is_comm.comm (⟨a, ha⟩ : Y) ⟨b, hb⟩)
  have hconjK : ∀ y ∈ Y, ∀ k ∈ M ⊔ Y, y * k * y⁻¹ ∈ M ⊔ Y := by
    intro y hy k hk
    have hk' : k ∈ ((M : Set X) * (Y : Set X) : Set X) := by
      rw [← hKmul]; exact hk
    rw [Set.mem_mul] at hk'
    obtain ⟨m, hm, y2, hy2, rfl⟩ := hk'
    have h1 : y * m * y⁻¹ ∈ M :=
      ((Subgroup.mem_normalizer_iff.mp (hYnorm hy)) m).mp hm
    have h2 : y * y2 * y⁻¹ ∈ Y := by
      rw [hYcomm y hy y2 hy2, mul_assoc, mul_inv_cancel, mul_one]
      exact hy2
    rw [show y * (m * y2) * y⁻¹ = (y * m * y⁻¹) * (y * y2 * y⁻¹) by group]
    exact Subgroup.mul_mem_sup h1 h2
  have hle : normalClosure (Y : Set X) ≤ M ⊔ Y := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    rw [Group.mem_conjugatesOfSet_iff] at hz
    obtain ⟨y, hy, hconj⟩ := hz
    rw [isConj_iff] at hconj
    obtain ⟨c, rfl⟩ := hconj
    have hc : c ∈ ((Y : Set X) * (N : Set X) : Set X) := by
      have htop' : c ∈ (↑(Y ⊔ N) : Set X) := by rw [hsup]; trivial
      rwa [Subgroup.mul_normal Y N] at htop'
    rw [Set.mem_mul] at hc
    obtain ⟨y1, hy1, n1, hn1, rfl⟩ := hc
    rw [← hYt] at hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hnt : n1 * t ^ j * n1⁻¹ = (n1 * t * n1⁻¹) ^ j :=
      (conj_zpow (a := n1) (b := t) (i := j)).symm
    have hct : n1 * t * n1⁻¹ = ⁅n1, t⁆ * t := by
      simp only [commutatorElement_def]; group
    have htY : t ∈ Y := by rw [← hYt]; exact Subgroup.mem_zpowers t
    have hmem : n1 * t * n1⁻¹ ∈ M ⊔ Y := by
      rw [hct]
      exact Subgroup.mul_mem_sup
        (by rw [hM]; exact Subgroup.commutator_mem_commutator hn1 (Subgroup.mem_zpowers t))
        htY
    have hmemj : n1 * t ^ j * n1⁻¹ ∈ M ⊔ Y := by
      rw [hnt]; exact Subgroup.zpow_mem (K := M ⊔ Y) hmem j
    rw [show (y1 * n1) * t ^ j * (y1 * n1)⁻¹ = y1 * (n1 * t ^ j * n1⁻¹) * y1⁻¹ by group]
    exact hconjK y1 hy1 _ hmemj
  have htop : M ⊔ Y = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]; exact hle
  have hNleM : N ≤ M := by
    intro n hn
    have hnK : n ∈ M ⊔ Y := by rw [htop]; trivial
    have hnK' : n ∈ ((M : Set X) * (Y : Set X) : Set X) := by
      rw [← hKmul]; exact hnK
    rw [Set.mem_mul] at hnK'
    obtain ⟨m, hm, y, hy, hmy⟩ := hnK'
    have hyN : y ∈ N := by
      have hy' : y = m⁻¹ * n := by rw [← hmy]; group
      rw [hy']
      exact N.mul_mem (N.inv_mem (hMnle hm)) hn
    have hy1 : y = 1 := by
      have hybot : y ∈ Y ⊓ N := ⟨hy, hyN⟩
      rw [hinf] at hybot
      exact Subgroup.mem_bot.mp hybot
    rw [hy1, mul_one] at hmy
    rwa [← hmy]
  exact le_antisymm hMnle hNleM

section ConjData

variable {G : Type*} [Group G]

private lemma w16ex_zpow_eq_one_or_self {v : G} (hv : v * v = 1) (n : ℤ) :
    v ^ n = 1 ∨ v ^ n = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, hv2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private theorem w16ex_commutator_eq_center_of_isExtraspecial {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [CFSG.IsExtraspecial p H] : commutator H = Subgroup.center H := by
  have hZtop : Subgroup.center H ≠ ⊤ := by
    intro h
    haveI : Nontrivial (H ⧸ Subgroup.center H) := CFSG.IsExtraspecial.quotient_nontrivial p H
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial (H ⧸ Subgroup.center H)›)
      (QuotientGroup.subsingleton_iff.mpr h)
  have hle : commutator H ≤ Subgroup.center H := by
    haveI : IsElementaryAbelian p (H ⧸ Subgroup.center H) :=
      CFSG.IsExtraspecial.quotient_elementary_abelian p H
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff (⁅a, b⁆)]
    change (QuotientGroup.mk' (Subgroup.center H)) ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hbot : commutator H ≠ ⊥ := by
    intro h
    have hc : IsMulCommutative H := (commutator_eq_bot_iff H).mp h
    haveI : IsMulCommutative H := hc
    exact hZtop Subgroup.center_eq_top
  have hdiv : Nat.card (commutator H) ∣ p := by
    rw [← CFSG.IsExtraspecial.center_order_p p H]
    exact Subgroup.card_dvd_of_le hle
  have hne1 : Nat.card (commutator H) ≠ 1 := fun h =>
    hbot (Subgroup.eq_bot_of_card_eq (commutator H) h)
  have hpc : Nat.card (commutator H) = p := by
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ hdiv with h1 | hp
    · exact absurd h1 hne1
    · exact hp
  haveI : Finite (Subgroup.center H) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.IsExtraspecial.center_order_p p H]; exact (Fact.out : Nat.Prime p).ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [CFSG.IsExtraspecial.center_order_p p H, hpc])

private lemma w16ex_commutatorElement_mul_mem_center {H : Type*} [Group H] (x y : H) {c d : H}
    (hc : c ∈ Subgroup.center H) (hd : d ∈ Subgroup.center H) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g : H, c * g * c⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
  have hd' : ∀ g : H, d * g * d⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hd g, mul_inv_cancel_right]
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ := by rw [hc']; group
    _ = ⁅x, y⁆ := by rw [hd', commutatorElement_def]

private lemma w16ex_conj_eq_self_of_mem_center {H : Type*} [Group H] {z : H}
    (hz : z ∈ Subgroup.center H) (g : H) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]

private lemma w16ex_commutatorElement_inv_inv_of_mem_center {H : Type*} [Group H] {a b : H}
    (hab : ⁅a, b⁆ ∈ Subgroup.center H) : ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have h1 : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using w16ex_conj_eq_self_of_mem_center ((Subgroup.center H).inv_mem hab) a⁻¹
  calc ⁅a⁻¹, b⁻¹⁆ = b⁻¹ * ⁅b, a⁻¹⁆ * b := commutatorElement_inv_right a⁻¹ b
    _ = b⁻¹ * ⁅a, b⁆ * b := by rw [← commutatorElement_inv, h1, inv_inv]
    _ = ⁅a, b⁆ := by simpa using w16ex_conj_eq_self_of_mem_center hab b⁻¹

private lemma w16ex_conj_commutator_mul_self {H : Type*} [Group H] {p v : H} (hv : v * v = 1) :
    v * ⁅p, v⁆ * v⁻¹ * ⁅p, v⁆ = 1 := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [commutatorElement_def, hv']
  calc v * (p * v * p⁻¹ * v) * v * (p * v * p⁻¹ * v)
      = v * p * v * p⁻¹ * (v * v) * p * v * p⁻¹ * v := by group
    _ = v * p * v * p⁻¹ * p * v * p⁻¹ * v := by rw [hv, mul_one]
    _ = v * p * (v * v) * p⁻¹ * v := by group
    _ = v * p * p⁻¹ * v := by rw [hv, mul_one]
    _ = v * v := by group
    _ = 1 := hv

private theorem w16ex_exists_conj_data_of_isExtraspecial {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Subgroup G} {v : G} [CFSG.IsExtraspecial p ↥P] (hcard : Nat.card ↥P = p ^ 3)
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hPv : ⁅P, Subgroup.zpowers v⁆ = P) :
    ∃ σ : ↥P → ↥P,
      (∀ y : ↥P, (σ y : G) = v * (y : G) * v⁻¹) ∧
      (∀ y : ↥P, σ y * y ∈ Subgroup.center ↥P) ∧
      (∀ z ∈ Subgroup.center ↥P, σ z = z) := by

  haveI : Finite ↥P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Fact.out : Nat.Prime p).ne_zero)
  haveI : IsElementaryAbelian p (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p ↥P
  let Z : Subgroup ↥P := Subgroup.center ↥P
  have hcommZ : commutator ↥P = Z := w16ex_commutator_eq_center_of_isExtraspecial (p := p)
  have hHH : commutator ↥P ≤ Z := le_of_eq hcommZ
  let σ : ↥P → ↥P := fun y =>
    ⟨v * (y : G) * v⁻¹, ((Subgroup.mem_normalizer_iff.mp hvP) (y : G)).mp y.2⟩
  have hσ : ∀ y : ↥P, (σ y : G) = v * (y : G) * v⁻¹ := fun _ => rfl
  have hσ_mul : ∀ a b : ↥P, σ (a * b) = σ a * σ b := by
    intro a b; apply Subtype.ext
    simp only [Subgroup.coe_mul, hσ]; group
  have hσ_inv : ∀ a : ↥P, σ a⁻¹ = (σ a)⁻¹ := by
    intro a; apply Subtype.ext
    simp only [Subgroup.coe_inv, hσ]; group
  have hσ_one : σ 1 = 1 := by
    apply Subtype.ext; simp only [Subgroup.coe_one, hσ]; group
  let ψ : ↥P →* (↥P ⧸ Z) :=
    MonoidHom.mk' (fun y => (σ y * y : ↥P ⧸ Z)) (by
      intro a b
      change (QuotientGroup.mk' Z) (σ (a * b) * (a * b)) =
        (QuotientGroup.mk' Z) (σ a * a) * (QuotientGroup.mk' Z) (σ b * b)
      rw [hσ_mul]
      letI : CommMonoid (↥P ⧸ Z) :=
        { (inferInstance : Group (↥P ⧸ Z)) with mul_comm := fun x y => mul_comm' x y }
      simp only [map_mul]
      ac_rfl)
  have hψ : ∀ y : ↥P, ψ y = (σ y * y : ↥P ⧸ Z) := fun _ => rfl
  have hS : ∀ y : ↥P, y ∈ ψ.ker ↔ σ y * y ∈ Z := by
    intro y
    rw [MonoidHom.mem_ker, hψ]
    exact QuotientGroup.eq_one_iff (σ y * y)
  have hgen : ⁅P, Subgroup.zpowers v⁆ ≤ ψ.ker.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro p hp w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases w16ex_zpow_eq_one_or_self hv k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact (ψ.ker.map P.subtype).one_mem
    · rw [hk]
      have hmemP : ⁅p, v⁆ ∈ P := by
        rw [← hPv]
        exact Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers v)
      refine Subgroup.mem_map.mpr ⟨⟨⁅p, v⁆, hmemP⟩, ?_, rfl⟩
      rw [hS]
      have h1 : σ ⟨⁅p, v⁆, hmemP⟩ * ⟨⁅p, v⁆, hmemP⟩ = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one, hσ]
        exact w16ex_conj_commutator_mul_self hv
      rw [h1]
      exact Z.one_mem
  have hker_map : ψ.ker.map P.subtype = P := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨s, -, rfl⟩
      exact s.2
    · exact (le_of_eq hPv.symm).trans hgen
  have hσy_mem : ∀ y : ↥P, σ y * y ∈ Z := by
    intro y
    have hy : (y : G) ∈ ψ.ker.map P.subtype := by rw [hker_map]; exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨s, hs, hsy⟩
    have hsy' : s = y := Subtype.ext hsy
    rw [← hsy']
    exact (hS s).mp hs
  let Fix : Subgroup ↥P :=
    { carrier := {z | σ z = z}
      one_mem' := hσ_one
      mul_mem' := fun {a b} ha hb => by
        show σ (a * b) = a * b
        rw [hσ_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show σ a⁻¹ = a⁻¹
        rw [hσ_inv, ha] }
  have hfix : commutator ↥P ≤ Fix := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show σ ⁅a, b⁆ = ⁅a, b⁆
    have hσc : σ ⁅a, b⁆ = ⁅σ a, σ b⁆ := by
      apply Subtype.ext
      simp only [hσ, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [hσc]
    have hca : σ a = a⁻¹ * (σ a * a) := by
      conv_lhs => rw [show σ a = (σ a * a) * a⁻¹ by group]
      rw [← Subgroup.mem_center_iff.1 (hσy_mem a) a⁻¹]
    have hcb : σ b = b⁻¹ * (σ b * b) := by
      conv_lhs => rw [show σ b = (σ b * b) * b⁻¹ by group]
      rw [← Subgroup.mem_center_iff.1 (hσy_mem b) b⁻¹]
    have hab : ⁅a, b⁆ ∈ Subgroup.center ↥P := by
      change ⁅a, b⁆ ∈ Z
      rw [← hcommZ]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hca, hcb, w16ex_commutatorElement_mul_mem_center a⁻¹ b⁻¹ (hσy_mem a) (hσy_mem b)]
    exact w16ex_commutatorElement_inv_inv_of_mem_center hab
  have hσz : ∀ z ∈ Z, σ z = z := fun z hz => hfix (hcommZ.symm ▸ hz)
  exact ⟨σ, hσ, hσy_mem, hσz⟩

end ConjData

theorem Shape166.mul_mem_center_of_extraspecial (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3)
    {t : X} (ht : t ∈ Y) (ht1 : t ≠ 1) {m : X} (hm : m ∈ fusionOddCore X) :
    t * m * t⁻¹ * m ∈ (center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hNinst : CFSG.IsExtraspecial p ↥(fusionOddCore X) := hN
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hodd := w16ex_odd_card_fusionOddCore X
    rw [hNc, hp2] at hodd
    norm_num at hodd
  have ht2 : t * t = 1 := by
    have h := hY.2 t ht
    simpa [pow_two] using h
  have hnorm : t ∈ Subgroup.normalizer ((fusionOddCore X : Subgroup X) : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.Normal.map_conj_eq (H := fusionOddCore X) t)
  have hPv : ⁅fusionOddCore X, Subgroup.zpowers t⁆ = fusionOddCore X :=
    w16ex_commutator_zpowers_eq_oddCore_of_shape166 hY hgen hX ht ht1
  obtain ⟨σ, hσ, hσy, -⟩ :=
    w16ex_exists_conj_data_of_isExtraspecial hp_ne_two hNc ht2 hnorm hPv
  refine Subgroup.mem_map.mpr ⟨σ ⟨m, hm⟩ * ⟨m, hm⟩, hσy ⟨m, hm⟩, ?_⟩
  change ((σ ⟨m, hm⟩ * ⟨m, hm⟩ : ↥(fusionOddCore X)) : X) = t * m * t⁻¹ * m
  rw [Subgroup.coe_mul, hσ]

theorem Shape166.center_le_centralizer_of_extraspecial (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3) :
    (center ↥(fusionOddCore X)).map (fusionOddCore X).subtype ≤ centralizer (Y : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hNinst : CFSG.IsExtraspecial p ↥(fusionOddCore X) := hN
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hodd := w16ex_odd_card_fusionOddCore X
    rw [hNc, hp2] at hodd
    norm_num at hodd
  have hYcard : Nat.card Y = 2 := w16ex_card_eq_two_of_shape166 hX
  have hYnt : Nontrivial ↥Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hYcard]
    norm_num
  obtain ⟨t, ht1⟩ := exists_ne (1 : ↥Y)
  have ht : (t : X) ∈ Y := t.2
  have htne : (t : X) ≠ 1 := by
    intro h; exact ht1 (Subtype.ext h)
  have hYt : Subgroup.zpowers (t : X) = Y :=
    w16ex_zpowers_eq_of_isElemAbelian_card_two hY hYcard ht htne
  have ht2 : (t : X) * (t : X) = 1 := by
    have h := hY.2 (t : X) ht
    simpa [pow_two] using h
  have hnorm : (t : X) ∈ Subgroup.normalizer ((fusionOddCore X : Subgroup X) : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.Normal.map_conj_eq (H := fusionOddCore X) (t : X))
  have hPv : ⁅fusionOddCore X, Subgroup.zpowers (t : X)⁆ = fusionOddCore X :=
    w16ex_commutator_zpowers_eq_oddCore_of_shape166 hY hgen hX ht htne
  obtain ⟨σ, hσ, -, hσz⟩ :=
    w16ex_exists_conj_data_of_isExtraspecial hp_ne_two hNc ht2 hnorm hPv
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [← hYt] at hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h1 : (σ c : X) = (t : X) * (c : X) * (t : X)⁻¹ := hσ c
  rw [hσz c hc] at h1
  have hcomm : Commute (c : X) (t : X) := by
    rw [commute_iff_eq]
    calc (c : X) * (t : X) = ((t : X) * (c : X) * (t : X)⁻¹) * (t : X) := by
          conv_lhs => rw [h1]
      _ = (t : X) * (c : X) := by group
  exact (hcomm.zpow_right j).eq.symm

theorem Shape166.inv_center_of_extraspecial (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3)
    (α : MulAut X) (hα : α * α = 1) (hαY : ∀ y ∈ Y, α y = y)
    (hne : ∀ y ∈ Y, α ≠ MulAut.conj y) :
    ∀ z ∈ (center ↥(fusionOddCore X)).map (fusionOddCore X).subtype, α z = z⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hNinst : CFSG.IsExtraspecial p ↥(fusionOddCore X) := hN
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hodd := w16ex_odd_card_fusionOddCore X
    rw [hNc, hp2] at hodd
    norm_num at hodd
  have hYcard : Nat.card Y = 2 := w16ex_card_eq_two_of_shape166 hX
  have hYnt : Nontrivial ↥Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hYcard]
    norm_num
  obtain ⟨t, ht1⟩ := exists_ne (1 : ↥Y)
  have ht : (t : X) ∈ Y := t.2
  have htne : (t : X) ≠ 1 := by
    intro h; exact ht1 (Subtype.ext h)
  have hYt : Subgroup.zpowers (t : X) = Y :=
    w16ex_zpowers_eq_of_isElemAbelian_card_two hY hYcard ht htne
  have ht2 : (t : X) * (t : X) = 1 := by
    have h := hY.2 (t : X) ht
    simpa [pow_two] using h
  have hsup : Y ⊔ fusionOddCore X = ⊤ := w16ex_sup_oddCore_eq_top_of_shape166 hX
  have hmap_le : (fusionOddCore X).map α.toMonoidHom ≤ fusionOddCore X := by
    change _ ≤ sSup {M : Subgroup X | M.Normal ∧ Odd (Nat.card M)}
    apply le_sSup
    refine ⟨?_, ?_⟩
    · exact (inferInstance : (fusionOddCore X).Normal).map α.toMonoidHom α.surjective
    · rw [Subgroup.card_map_of_injective α.injective]
      exact w16ex_odd_card_fusionOddCore X
  have hαN : (fusionOddCore X).map α.toMonoidHom = fusionOddCore X := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective α.injective]
  let σ : MulAut ↥(fusionOddCore X) :=
    (α.subgroupMap (fusionOddCore X)).trans (MulEquiv.subgroupCongr hαN)
  have hσ : ∀ y : ↥(fusionOddCore X), (σ y : X) = α (y : X) := fun _ => rfl
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    rw [hσ, hσ]
    have := congrArg (fun e : MulAut X => e (x : X)) hα
    simpa [MulAut.mul_apply] using this
  let cj : MulAut X := MulAut.conj (t : X)
  have hcjN : (fusionOddCore X).map cj.toMonoidHom = fusionOddCore X :=
    Subgroup.Normal.map_conj_eq (H := fusionOddCore X) (t : X)
  let τ : MulAut ↥(fusionOddCore X) :=
    (cj.subgroupMap (fusionOddCore X)).trans (MulEquiv.subgroupCongr hcjN)
  have hτ : ∀ y : ↥(fusionOddCore X), (τ y : X) = (t : X) * (y : X) * (t : X)⁻¹ :=
    fun _ => rfl
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    rw [hτ, hτ, inv_eq_of_mul_eq_one_right ht2]
    calc (t : X) * ((t : X) * (x : X) * (t : X)) * (t : X)
        = ((t : X) * (t : X)) * (x : X) * ((t : X) * (t : X)) := by group
      _ = (x : X) := by rw [ht2, one_mul, mul_one]
  have hτinv : ∀ x, τ x * x ∈ Subgroup.center ↥(fusionOddCore X) := by
    intro x
    have h := Shape166.mul_mem_center_of_extraspecial hY hgen hX hp hN hNc ht htne
      (m := (x : X)) x.2
    rcases Subgroup.mem_map.mp h with ⟨c, hc, hcx⟩
    have hc' : τ x * x = c := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hτ x]
      exact hcx.symm
    rw [hc']
    exact hc
  have hτZ : ∀ z ∈ Subgroup.center ↥(fusionOddCore X), τ z = z := by
    intro z hz
    apply Subtype.ext
    rw [hτ]
    have hcent := Shape166.center_le_centralizer_of_extraspecial hY hgen hX hp hN hNc
      (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcent) (t : X) ht
    have hz' : (z : X) = ((fusionOddCore X).subtype z) := rfl
    rw [hz', hcomm]; group
  have hdecomp : ∀ x : X, ∃ n : ↥(fusionOddCore X), ∃ y ∈ Y, (n : X) * y = x := by
    intro x
    have hx : x ∈ ((fusionOddCore X : Set X) * (Y : Set X) : Set X) := by
      have htop : x ∈ (↑(fusionOddCore X ⊔ Y) : Set X) := by
        rw [sup_comm, hsup]; trivial
      rwa [Subgroup.normal_mul] at htop
    rw [Set.mem_mul] at hx
    obtain ⟨n, hn, y, hy, hny⟩ := hx
    exact ⟨⟨n, hn⟩, y, hy, hny⟩
  refine fun z hz => ?_
  rcases Subgroup.mem_map.mp hz with ⟨c, hc, rfl⟩
  rcases mulAut_fix_or_inv_center (p := p) σ hσσ with hfix | hinv
  · rcases mulAut_pm_of_isExtraspecial (p := p) hp_ne_two hNc σ hσσ hfix with hid | hinv'
    · have hσone : σ = 1 := by
        refine MulEquiv.ext fun x => ?_
        exact mulAut_apply_eq_of_forall_mul_inv_mem_center (p := p) hp_ne_two σ hσσ hfix hid x
      have hα_one : α = 1 := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨n, y, hy, rfl⟩ := hdecomp x
        rw [map_mul, MulAut.one_apply]
        have hαn : α (n : X) = (n : X) := by
          have h : σ n = n := by rw [hσone]; rfl
          rw [← hσ n, h]
        rw [hαn, hαY y hy]
      exact absurd hα_one (by simpa using hne 1 (one_mem Y))
    · have hcomm : ∀ x, σ (τ x) = τ (σ x) := by
        intro x
        apply Subtype.ext
        simp only [hσ, hτ, map_mul, map_inv, hαY (t : X) ht]
      have hcomp : ∀ x, σ (τ x) = x := fun x =>
        mulAut_comp_apply_eq_of_pm (p := p) hp_ne_two σ τ hσσ hττ hcomm hfix hτZ hinv'
          hτinv x
      have hprod : σ * τ = 1 := MulEquiv.ext hcomp
      have hττ1 : τ * τ = 1 := MulEquiv.ext hττ
      have hσ_eq_τ : σ = τ := by
        calc σ = σ * 1 := by rw [mul_one]
          _ = σ * (τ * τ) := by rw [hττ1]
          _ = (σ * τ) * τ := by rw [mul_assoc]
          _ = 1 * τ := by rw [hprod]
          _ = τ := by rw [one_mul]
      have hα_conj : α = MulAut.conj (t : X) := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨n, y, hy, rfl⟩ := hdecomp x
        rw [MulAut.conj_apply, map_mul]
        have hαn : α (n : X) = (t : X) * (n : X) * (t : X)⁻¹ := by
          have h : σ n = τ n := by rw [hσ_eq_τ]
          rw [← hσ n, h, hτ n]
        have hαy : α y = (t : X) * y * (t : X)⁻¹ := by
          rw [hαY y hy]
          rw [← hYt] at hy
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          rw [← conj_zpow (a := (t : X)) (b := (t : X)) (i := j)]
          simp
        rw [hαn, hαy]
        group
      exact absurd hα_conj (hne (t : X) ht)
  · have h := congrArg Subtype.val (hinv c hc)
    simp only [hσ, Subgroup.coe_inv] at h
    exact h

end CFSG.LocalAnalysis.WeakClosure81

end
