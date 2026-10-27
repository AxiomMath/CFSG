module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36C
import CFSG.RankThree.PartTwo.Sec21.FF79KOneFive
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Loc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G]

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg (by omega), if_pos (by omega)]

theorem two_pow_odd_of_modEq {n : ℕ} (h : 2 ^ n ≡ 2 [MOD 3]) : n % 2 = 1 := by
  have h' : 2 ^ n % 3 = 2 := h
  rw [two_pow_mod_three] at h'
  split_ifs at h' with h2 <;> omega

theorem card_eq_two_pow {X : Subgroup G} (hX : IsPGroup 2 X) : ∃ n, Nat.card X = 2 ^ n :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hX.exists_card_eq

theorem mem_nor_inf {X Y : Subgroup G} {g : G} (hX : g ∈ Nor X) (hY : g ∈ Nor Y) :
    g ∈ Nor (X ⊓ Y) :=
  Subgroup.mem_normalizer_fintype fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hX y).mp hy.1, (Subgroup.mem_normalizer_iff.mp hY y).mp hy.2⟩

theorem mem_nor_cen {x g : G} (h : g * x = x * g) : g ∈ Nor (Cen x) :=
  Subgroup.mem_normalizer_fintype fun y hy => by
    have hy' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * y * g⁻¹ * x = g * y * (g⁻¹ * x) := by group
      _ = g * y * (x * g⁻¹) := by
          rw [show g⁻¹ * x = x * g⁻¹ by
            calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
              _ = g⁻¹ * (g * x) * g⁻¹ := by rw [h]
              _ = x * g⁻¹ := by group]
      _ = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy']
      _ = x * (g * y * g⁻¹) := by rw [← mul_assoc g x, h]; group

theorem eq_of_card_dvd_two_mul {Y K : Subgroup G} (hY : IsPGroup 2 Y) (hKY : K ≤ Y) {x : G}
    (hx : orderOf x = 3) (hxY : x ∈ Nor Y) (hxK : x ∈ Nor K) (hidx : Nat.card Y ∣ 2 * Nat.card K)
    (hfix : Y ⊓ Cen x ≤ K) : K = Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY3 := card_modEq_card_inf_cen hx hxY
  have hK3 := card_modEq_card_inf_cen hx hxK
  have heq : Y ⊓ Cen x = K ⊓ Cen x :=
    le_antisymm (le_inf hfix inf_le_right) (inf_le_inf_right _ hKY)
  rw [heq] at hY3
  have hYK : Nat.card Y ≡ Nat.card K [MOD 3] := hY3.trans hK3.symm
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hKY
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hd2 : d ∣ 2 := by
    rw [hd, mul_comm 2] at hidx
    exact (Nat.mul_dvd_mul_iff_left hKpos).mp hidx
  obtain ⟨n, hn⟩ := card_eq_two_pow (hY.to_le hKY)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
  · exact Subgroup.eq_of_le_of_card_ge hKY (by rw [hd, mul_one])
  · exfalso
    rw [hd, hn] at hYK
    have h1 : 2 ^ n * 2 % 3 = 2 ^ n % 3 := hYK
    rw [Nat.mul_mod, two_pow_mod_three] at h1
    split_ifs at h1 <;> omega

theorem le_cen_of_comm_mem {Y : Subgroup G} (hY : IsPGroup 2 Y) {t t₀ x : G}
    (ht₀ : t₀ * t₀ = 1) (hYt₀ : Y ≤ Cen t₀)
    (hcomm : ∀ y ∈ Y, y * t * y⁻¹ * t⁻¹ ∈ Subgroup.zpowers t₀) (hx : orderOf x = 3)
    (hxY : x ∈ Nor Y) (hxt : x * t = t * x) (hfix : Y ⊓ Cen x ≤ Cen t) : Y ≤ Cen t := by
  have hcz : ∀ c ∈ Subgroup.zpowers t₀, ∀ y ∈ Y, c * y = y * c := by
    intro c hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hYt₀ hy)).symm k)).eq
  have hzc : ∀ c ∈ Subgroup.zpowers t₀, ∀ d ∈ Subgroup.zpowers t₀, c * d = d * c := by
    intro c hc d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (Commute.zpow_zpow_self t₀ k j).eq
  let f : ↥Y → ↥(Subgroup.zpowers t₀) := fun y => ⟨y * t * (y : G)⁻¹ * t⁻¹, hcomm y y.2⟩
  have hf : ∀ y₁ y₂ : ↥Y, f (y₁ * y₂) = f y₁ * f y₂ := by
    intro y₁ y₂
    apply Subtype.ext
    show (y₁ * y₂ : G) * t * ((y₁ : G) * y₂)⁻¹ * t⁻¹ =
      ((y₁ : G) * t * (y₁ : G)⁻¹ * t⁻¹) * ((y₂ : G) * t * (y₂ : G)⁻¹ * t⁻¹)
    set c₁ := (y₁ : G) * t * (y₁ : G)⁻¹ * t⁻¹
    set c₂ := (y₂ : G) * t * (y₂ : G)⁻¹ * t⁻¹ with hc₂
    have h2 : c₂ * y₁ = y₁ * c₂ := hcz _ (hcomm y₂ y₂.2) y₁ y₁.2
    calc (y₁ * y₂ : G) * t * ((y₁ : G) * y₂)⁻¹ * t⁻¹ = (y₁ : G) * c₂ * t * (y₁ : G)⁻¹ * t⁻¹ := by
          rw [hc₂]; group
      _ = c₂ * ((y₁ : G) * t * (y₁ : G)⁻¹ * t⁻¹) := by rw [← h2]; group
      _ = c₁ * c₂ := hzc _ (hcomm y₂ y₂.2) _ (hcomm y₁ y₁.2)
  let ψ : ↥Y →* ↥(Subgroup.zpowers t₀) := MonoidHom.mk' f hf
  have hker : Nat.card ψ.ker = Nat.card ↥(Y ⊓ Cen t) := by
    have : ψ.ker = (Y ⊓ Cen t).subgroupOf Y := by
      ext y
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem,
        true_and]
      change f y = 1 ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
      change (y : G) * t * (y : G)⁻¹ * t⁻¹ = 1 ↔ _
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hrange : Nat.card ψ.range ∣ 2 := by
    have h1 : Nat.card ψ.range ∣ Nat.card (Subgroup.zpowers t₀) := by
      rw [← Subgroup.card_top (G := ↥(Subgroup.zpowers t₀))]
      exact Subgroup.card_dvd_of_le le_top
    rw [Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_two, ht₀]))
  have hidx : Nat.card Y ∣ 2 * Nat.card ↥(Y ⊓ Cen t) := by
    rw [← Subgroup.card_ker_mul_card_range ψ, hker, mul_comm 2]
    exact Nat.mul_dvd_mul_left _ hrange
  have hK := eq_of_card_dvd_two_mul hY inf_le_left hx hxY (mem_nor_inf hxY (mem_nor_cen hxt)) hidx
    (le_inf inf_le_left hfix)
  rw [← hK]
  exact inf_le_right

theorem coprime_solvable_of_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    Nat.Coprime (Nat.card X) 3 ∧ Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := card_eq_two_pow hX
  haveI := hX.isNilpotent
  exact ⟨hn ▸ Nat.Coprime.pow_left n (by norm_num), inferInstance⟩

theorem mem_nor_cenS {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, g * h = h * g) :
    g ∈ Nor (CenS H) :=
  Subgroup.mem_normalizer_fintype fun c hc => by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hch : h * c = c * h := Subgroup.mem_centralizer_iff.mp hc h hh
    have hgh : g * h = h * g := hg h hh
    have hgh' : g⁻¹ * h = h * g⁻¹ := by
      calc g⁻¹ * h = g⁻¹ * (h * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * h) * g⁻¹ := by rw [hgh]
        _ = h * g⁻¹ := by group
    calc h * (g * c * g⁻¹) = (h * g) * c * g⁻¹ := by group
      _ = g * (h * c) * g⁻¹ := by rw [← hgh]; group
      _ = g * c * (h * g⁻¹) := by rw [hch]; group
      _ = g * c * g⁻¹ * h := by rw [← hgh']; group

theorem hypZ_ne : ∀ i : Fin 13, hypZ i ≠ 0 := by decide

theorem dot_sub_hypZ : ∀ i : Fin 13, ∀ w0 w1 w2 : ZMod 3,
    dot (hypF i) (![w0, w1, w2] - dot (hypF i) ![w0, w1, w2] • hypZ i) = 0 := by
  decide +kernel

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem cenS_hyp_inf_cen (hB : FF81Basis b L B b₁ b₂ b₃) (i : Fin 13) :
    CenS (hyp b₁ b₂ b₃ i) ⊓ Cen (ε3 b₁ b₂ b₃ (hypZ i)) =
      CenS (Subgroup.closure {b₁, b₂, b₃}) := by
  refine le_antisymm (fun c hc => ?_) (le_inf ?_ ?_)
  · obtain ⟨hcA, hcz⟩ := hc
    refine Subgroup.mem_centralizer_iff.mpr fun β hβ => ?_
    obtain ⟨w, rfl⟩ := hB.exists_ε3 hβ
    set d := dot (hypF i) w
    have hsplit : ε3 b₁ b₂ b₃ w =
        ε3 b₁ b₂ b₃ (w - d • hypZ i) * ε3 b₁ b₂ b₃ (hypZ i) ^ d.val := by
      rw [← hB.ε3_smul, ← hB.ε3_add, sub_add_cancel]
    have hA : ε3 b₁ b₂ b₃ (w - d • hypZ i) ∈ hyp b₁ b₂ b₃ i := by
      refine (hB.mem_hyp i _).2 ?_
      rw [vec3_eta w]
      exact dot_sub_hypZ i _ _ _
    have h1 : ε3 b₁ b₂ b₃ (w - d • hypZ i) * c = c * ε3 b₁ b₂ b₃ (w - d • hypZ i) :=
      Subgroup.mem_centralizer_iff.mp hcA _ hA
    have h2 : c * ε3 b₁ b₂ b₃ (hypZ i) = ε3 b₁ b₂ b₃ (hypZ i) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcz
    have h2' : ε3 b₁ b₂ b₃ (hypZ i) ^ d.val * c = c * ε3 b₁ b₂ b₃ (hypZ i) ^ d.val :=
      ((Commute.pow_left h2.symm d.val)).eq
    rw [hsplit, mul_assoc, h2', ← mul_assoc, h1, mul_assoc]
  · exact Subgroup.centralizer_le (hyp_le i)
  · intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hc _ (ε3_mem _)).symm

theorem card_hyp_modEq (hB : FF81Basis b L B b₁ b₂ b₃) {X : Subgroup G}
    (hX : Subgroup.closure {b₁, b₂, b₃} ≤ Nor X) (i : Fin 13) :
    Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) ≡
      Nat.card ↥(X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z := ε3 b₁ b₂ b₃ (hypZ i)
  have hzA : ∀ h ∈ hyp b₁ b₂ b₃ i, z * h = h * z := fun h hh =>
    hB.B₁_comm (ε3_mem _) (hyp_le i hh)
  have h := card_modEq_card_inf_cen (hB.orderOf_ε3 (hypZ_ne i))
    (mem_nor_inf (hX (ε3_mem (hypZ i))) (mem_nor_cenS hzA))
  rwa [inf_assoc, cenS_hyp_inf_cen hB i] at h

theorem eq_of_cen_hyp_le (hB : FF81Basis b L B b₁ b₂ b₃) {N X : Subgroup G} (hXp : IsPGroup 2 X)
    (hNX : N ≤ X) (hN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor N)
    (hX : Subgroup.closure {b₁, b₂, b₃} ≤ Nor X)
    (hle : ∀ i, X ⊓ CenS (hyp b₁ b₂ b₃ i) ≤ N) : N = X := by
  have hNp : IsPGroup 2 N := hXp.to_le hNX
  have heq : ∀ H : Subgroup G, X ⊓ CenS H ≤ N → N ⊓ CenS H = X ⊓ CenS H := fun H h =>
    le_antisymm (inf_le_inf_right _ hNX) (le_inf h inf_le_right)
  have hB₁ : X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) ≤ N :=
    (inf_le_inf_left _ (Subgroup.centralizer_le (hyp_le 0))).trans (hle 0)
  obtain ⟨hXc, hXs⟩ := coprime_solvable_of_two hXp
  obtain ⟨hNc, hNs⟩ := coprime_solvable_of_two hNp
  have hXw := card_mul_pow_twelve hB hX hXc hXs
  have hNw := card_mul_pow_twelve hB hN hNc hNs
  simp only [heq _ hB₁, fun i => heq _ (hle i)] at hNw
  rw [← hXw] at hNw
  have hpos : 0 < Nat.card ↥(X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) ^ 12 :=
    pow_pos Nat.card_pos _
  exact Subgroup.eq_of_le_of_card_ge hNX (Nat.le_of_eq (Nat.eq_of_mul_eq_mul_right hpos hNw).symm)

theorem prod_hypW (c : ℕ → ℕ) :
    ∏ i : Fin 13, c (hypW i) = c 1 ^ 3 * c 2 ^ 6 * c 3 ^ 4 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, hypW]
  simp
  ring

theorem filter_y : Finset.univ.filter (fun i : Fin 13 => dot (hypF i) ![1, 1, 0] = 0) =
    {2, 4, 11, 12} := by decide

theorem ε3_y : ε3 b₁ b₂ b₃ ![1, 1, 0] = b₁ * b₂ := by simp [ε3, val_one3]

theorem exp_identities (hB : FF81Basis b L B b₁ b₂ b₃) {X : Subgroup G} (hXp : IsPGroup 2 X)
    (hX : L ≤ Nor X) :
    ∃ e₀ eB ey e₁ e₂ e₃ : ℕ, Nat.card X = 2 ^ e₀ ∧
      Nat.card ↥(X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) = 2 ^ eB ∧
      Nat.card ↥(X ⊓ Cen (b₁ * b₂)) = 2 ^ ey ∧
      (∀ i, hypW i = 1 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ e₁) ∧
      (∀ i, hypW i = 2 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ e₂) ∧
      (∀ i, hypW i = 3 → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ e₃) ∧
      e₀ + 12 * eB = 3 * e₁ + 6 * e₂ + 4 * e₃ ∧ ey + 3 * eB = e₁ + e₂ + 2 * e₃ := by
  have hX₁ : Subgroup.closure {b₁, b₂, b₃} ≤ Nor X := hB.B₁_le.trans hX
  obtain ⟨hXc, hXs⟩ := coprime_solvable_of_two hXp
  set c : ℕ → ℕ := fun w => Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ (rep w))) with hc
  have hci : ∀ i, Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = c (hypW i) := card_hyp_rep hB hX
  have h2 : ∀ H : Subgroup G, H ≤ X → ∃ e, Nat.card H = 2 ^ e := fun H hH =>
    card_eq_two_pow (hXp.to_le hH)
  obtain ⟨e₀, he₀⟩ := card_eq_two_pow hXp
  obtain ⟨eB, heB⟩ := h2 _ (inf_le_left : X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) ≤ X)
  obtain ⟨ey, hey⟩ := h2 _ (inf_le_left : X ⊓ Cen (b₁ * b₂) ≤ X)
  obtain ⟨e₁, he₁⟩ := h2 _ (inf_le_left : X ⊓ CenS (hyp b₁ b₂ b₃ (rep 1)) ≤ X)
  obtain ⟨e₂, he₂⟩ := h2 _ (inf_le_left : X ⊓ CenS (hyp b₁ b₂ b₃ (rep 2)) ≤ X)
  obtain ⟨e₃, he₃⟩ := h2 _ (inf_le_left : X ⊓ CenS (hyp b₁ b₂ b₃ (rep 3)) ≤ X)
  have hw : ∀ i w, hypW i = w → Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = c w := fun i w h =>
    h ▸ hci i
  refine ⟨e₀, eB, ey, e₁, e₂, e₃, he₀, heB, hey, fun i h => (hw i 1 h).trans he₁,
    fun i h => (hw i 2 h).trans he₂, fun i h => (hw i 3 h).trans he₃, ?_, ?_⟩
  · have h := card_mul_pow_twelve hB hX₁ hXc hXs
    simp only [hci] at h
    rw [prod_hypW, he₀, heB, show c 1 = 2 ^ e₁ from he₁, show c 2 = 2 ^ e₂ from he₂,
      show c 3 = 2 ^ e₃ from he₃] at h
    simp only [← pow_mul, ← pow_add] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  · have hy : (![1, 1, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
    have h := card_cen_mul_pow_three hB hX₁ hXc hXs hy
    rw [ε3_y, filter_y] at h
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton, hw 2 1 rfl, hw 4 2 rfl, hw 11 3 rfl,
      hw 12 3 rfl, hey, heB, show c 1 = 2 ^ e₁ from he₁, show c 2 = 2 ^ e₂ from he₂,
      show c 3 = 2 ^ e₃ from he₃] at h
    simp only [← pow_mul, ← pow_add] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
