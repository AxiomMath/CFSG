module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolClassTwo

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_MCalc_comm_zpow {G : Type*} [Group G] (A : Subgroup G) (y : G)
    (hAy : ∀ u ∈ A, u * y = y * u) (w : G) (hw : w ∈ A) (n : ℤ) :
    y ^ n * w = w * y ^ n :=
  (Commute.zpow_left (show Commute y w from (hAy w hw).symm) n).eq

theorem aux_MCalc_commute_pair {G : Type*} [Group G] (A : Subgroup G) (y r : G)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (w : G) (hw : w ∈ A) (m n : ℤ) : Commute w (y ^ m * r ^ n) :=
  Commute.mul_right (Commute.zpow_right (show Commute w y from hAy w hw) m)
    (Commute.zpow_right (show Commute w r from hAr w hw) n)

theorem aux_MCalc_zpow_three {G : Type*} [Group G] (g : G) (n : ℤ) :
    (g ^ n) ^ 3 = g ^ (3 * n) := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem cube_formula {G : Type*} [Group G] (A : Subgroup G) (y r : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hk : y * r * y⁻¹ * r⁻¹ ∈ A) (α β : ℤ) (u : G) (hu : u ∈ A) :
    (y ^ α * r ^ β * u) ^ 3 = y ^ (3 * α) * r ^ (3 * β) := by
  have hku : y * (y * r * y⁻¹ * r⁻¹) = (y * r * y⁻¹ * r⁻¹) * y := (hAy _ hk).symm
  have hkv : r * (y * r * y⁻¹ * r⁻¹) = (y * r * y⁻¹ * r⁻¹) * r := (hAr _ hk).symm
  have hκ : (y * r * y⁻¹ * r⁻¹) ^ (α * β) ∈ A := A.zpow_mem hk (α * β)
  have hc : y ^ α * r ^ β * (y ^ α)⁻¹ * (r ^ β)⁻¹ = (y * r * y⁻¹ * r⁻¹) ^ (α * β) :=
    comm_zpow_zpow y r _ rfl hku hkv α β
  have h1 : y ^ α * (y * r * y⁻¹ * r⁻¹) ^ (α * β) = (y * r * y⁻¹ * r⁻¹) ^ (α * β) * y ^ α :=
    aux_MCalc_comm_zpow A y hAy _ hκ α
  have h2 : r ^ β * (y * r * y⁻¹ * r⁻¹) ^ (α * β) = (y * r * y⁻¹ * r⁻¹) ^ (α * β) * r ^ β :=
    aux_MCalc_comm_zpow A r hAr _ hκ β
  have h3 : (y ^ α * r ^ β) ^ 3 = (y ^ α) ^ 3 * (r ^ β) ^ 3 :=
    pow_three_of_comm_central (y ^ α) (r ^ β) _ hc h1 h2 (hAexp _ hκ)
  have hC : Commute (y ^ α * r ^ β) u :=
    (aux_MCalc_commute_pair A y r hAy hAr u hu α β).symm
  calc (y ^ α * r ^ β * u) ^ 3 = (y ^ α * r ^ β) ^ 3 * u ^ 3 := hC.mul_pow 3
    _ = (y ^ α * r ^ β) ^ 3 := by rw [hAexp u hu, mul_one]
    _ = (y ^ α) ^ 3 * (r ^ β) ^ 3 := h3
    _ = y ^ (3 * α) * r ^ (3 * β) := by rw [aux_MCalc_zpow_three, aux_MCalc_zpow_three]

theorem aux_MCalc_comm_rel {G : Type*} [Group G] (a b k : G) (h : a * b * a⁻¹ * b⁻¹ = k) :
    a * b = k * (b * a) := by
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = k * (b * a) := by rw [h]

theorem aux_MCalc_comm_of_mul_eq {G : Type*} [Group G] (M N κ : G)
    (h : M * N = κ * (N * M)) : M * N * M⁻¹ * N⁻¹ = κ := by
  calc M * N * M⁻¹ * N⁻¹ = M * N * (N * M)⁻¹ := by group
    _ = κ * (N * M) * (N * M)⁻¹ := by rw [h]
    _ = κ := by group

theorem aux_MCalc_key {G : Type*} [Group G] (a b a' b' k : G) (p q : ℤ)
    (haa : a * a' = a' * a) (hbb : b * b' = b' * b)
    (hab : a * b' = k ^ p * (b' * a)) (hba : a' * b = k ^ q * (b * a'))
    (hka : ∀ m : ℤ, a * k ^ m = k ^ m * a) (hka' : ∀ m : ℤ, a' * k ^ m = k ^ m * a') :
    a * b * (a' * b') = k ^ (p - q) * (a' * b' * (a * b)) := by
  have hA : b * a' = k ^ (-q) * (a' * b) := by
    rw [zpow_neg, hba, inv_mul_cancel_left]
  calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
    _ = a * (k ^ (-q) * (a' * b)) * b' := by rw [hA]
    _ = (a * k ^ (-q)) * a' * b * b' := by simp only [mul_assoc]
    _ = (k ^ (-q) * a) * a' * b * b' := by rw [hka (-q)]
    _ = k ^ (-q) * (a * a') * (b * b') := by simp only [mul_assoc]
    _ = k ^ (-q) * (a' * a) * (b' * b) := by rw [haa, hbb]
    _ = k ^ (-q) * a' * (a * b') * b := by simp only [mul_assoc]
    _ = k ^ (-q) * a' * (k ^ p * (b' * a)) * b := by rw [hab]
    _ = (k ^ (-q) * (a' * k ^ p)) * b' * a * b := by simp only [mul_assoc]
    _ = (k ^ (-q) * (k ^ p * a')) * b' * a * b := by rw [hka' p]
    _ = (k ^ (-q) * k ^ p) * (a' * b' * (a * b)) := by simp only [mul_assoc]
    _ = k ^ (p - q) * (a' * b' * (a * b)) := by
      rw [show p - q = -q + p by ring, zpow_add]

theorem aux_MCalc_assemble {G : Type*} [Group G] (P Q u₁ u₂ κ : G)
    (hPQ : P * Q = κ * (Q * P))
    (hu₁Q : u₁ * Q = Q * u₁) (hu₂P : u₂ * P = P * u₂)
    (hcQP : (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (Q * P) = (Q * P) * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹)) :
    (P * u₁) * (Q * u₂) * (P * u₁)⁻¹ * (Q * u₂)⁻¹ = κ * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) := by
  have hc : u₁ * u₂ = (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (u₂ * u₁) := by group
  have hNM : (Q * u₂) * (P * u₁) = (Q * P) * (u₂ * u₁) := by
    calc (Q * u₂) * (P * u₁) = Q * (u₂ * P) * u₁ := by simp only [mul_assoc]
      _ = Q * (P * u₂) * u₁ := by rw [hu₂P]
      _ = (Q * P) * (u₂ * u₁) := by simp only [mul_assoc]
  have hMN : (P * u₁) * (Q * u₂) = κ * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * ((Q * u₂) * (P * u₁)) := by
    rw [hNM]
    calc (P * u₁) * (Q * u₂) = P * (u₁ * Q) * u₂ := by simp only [mul_assoc]
      _ = P * (Q * u₁) * u₂ := by rw [hu₁Q]
      _ = (P * Q) * (u₁ * u₂) := by simp only [mul_assoc]
      _ = κ * (Q * P) * (u₁ * u₂) := by rw [hPQ]
      _ = κ * (Q * P) * ((u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (u₂ * u₁)) := by rw [← hc]
      _ = κ * ((Q * P) * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹)) * (u₂ * u₁) := by simp only [mul_assoc]
      _ = κ * ((u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (Q * P)) * (u₂ * u₁) := by rw [hcQP]
      _ = κ * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * ((Q * P) * (u₂ * u₁)) := by simp only [mul_assoc]
  exact aux_MCalc_comm_of_mul_eq (P * u₁) (Q * u₂) (κ * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹)) hMN

theorem aux_MCalc_comm_gen {G : Type*} [Group G] (A : Subgroup G) (y r : G)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hk : y * r * y⁻¹ * r⁻¹ ∈ A) (α β γ ε : ℤ) (u₁ u₂ : G) (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A) :
    (y ^ α * r ^ β * u₁) * (y ^ γ * r ^ ε * u₂) * (y ^ α * r ^ β * u₁)⁻¹ *
        (y ^ γ * r ^ ε * u₂)⁻¹ =
      (y * r * y⁻¹ * r⁻¹) ^ (α * ε - β * γ) * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) := by
  have hku : y * (y * r * y⁻¹ * r⁻¹) = (y * r * y⁻¹ * r⁻¹) * y := (hAy _ hk).symm
  have hkv : r * (y * r * y⁻¹ * r⁻¹) = (y * r * y⁻¹ * r⁻¹) * r := (hAr _ hk).symm
  have hE : ∀ i j : ℤ, y ^ i * r ^ j * (y ^ i)⁻¹ * (r ^ j)⁻¹ = (y * r * y⁻¹ * r⁻¹) ^ (i * j) :=
    fun i j => comm_zpow_zpow y r _ rfl hku hkv i j
  have hKA : ∀ m : ℤ, (y * r * y⁻¹ * r⁻¹) ^ m ∈ A := fun m => A.zpow_mem hk m
  have hab : y ^ α * r ^ ε = (y * r * y⁻¹ * r⁻¹) ^ (α * ε) * (r ^ ε * y ^ α) :=
    aux_MCalc_comm_rel _ _ _ (hE α ε)
  have hba : y ^ γ * r ^ β = (y * r * y⁻¹ * r⁻¹) ^ (γ * β) * (r ^ β * y ^ γ) :=
    aux_MCalc_comm_rel _ _ _ (hE γ β)
  have hPQ := aux_MCalc_key (y ^ α) (r ^ β) (y ^ γ) (r ^ ε) (y * r * y⁻¹ * r⁻¹)
    (α * ε) (γ * β) (Commute.zpow_zpow_self y α γ).eq (Commute.zpow_zpow_self r β ε).eq
    hab hba (fun m => aux_MCalc_comm_zpow A y hAy _ (hKA m) α)
    (fun m => aux_MCalc_comm_zpow A y hAy _ (hKA m) γ)
  have hq : α * ε - β * γ = α * ε - γ * β := by ring
  rw [hq]
  have hcA : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hu₁ hu₂) (A.inv_mem hu₁)) (A.inv_mem hu₂)
  exact aux_MCalc_assemble (y ^ α * r ^ β) (y ^ γ * r ^ ε) u₁ u₂ _ hPQ
    (aux_MCalc_commute_pair A y r hAy hAr u₁ hu₁ γ ε).eq
    (aux_MCalc_commute_pair A y r hAy hAr u₂ hu₂ α β).eq
    (Commute.mul_right (aux_MCalc_commute_pair A y r hAy hAr _ hcA γ ε)
      (aux_MCalc_commute_pair A y r hAy hAr _ hcA α β)).eq

theorem comm_formula_of_comm {G : Type*} [Group G] (A : Subgroup G) (y r : G)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hk : y * r * y⁻¹ * r⁻¹ ∈ A) (α β γ ε : ℤ) (u₁ u₂ : G) (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A)
    (hc : u₁ * u₂ = u₂ * u₁) :
    (y ^ α * r ^ β * u₁) * (y ^ γ * r ^ ε * u₂) * (y ^ α * r ^ β * u₁)⁻¹ *
        (y ^ γ * r ^ ε * u₂)⁻¹ = (y * r * y⁻¹ * r⁻¹) ^ (α * ε - β * γ) := by
  have h1 : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ = 1 := by
    rw [hc]
    group
  rw [aux_MCalc_comm_gen A y r hAy hAr hk α β γ ε u₁ u₂ hu₁ hu₂, h1, mul_one]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
