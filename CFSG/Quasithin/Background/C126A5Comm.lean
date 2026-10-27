module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.C1 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem card_evenWeight_three : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
  have h1 : Nat.card (evenWeight 3) = Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} :=
    Nat.card_congr (Equiv.refl _)
  have h2 : Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [← h2, ← h1]
  exact Nat.card_congr (Equiv.refl _)

theorem norm_comm_eq_one {x q : G} (hx : x ^ 3 = 1) :
    (x * (x * (x * q * x⁻¹ * q⁻¹) * x⁻¹) * x⁻¹) * (x * (x * q * x⁻¹ * q⁻¹) * x⁻¹) *
      (x * q * x⁻¹ * q⁻¹) = 1 := by
  have h3 : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx
  calc _ = (x * x * x) * q * (x * x * x)⁻¹ * q⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem exists_comm_blockU {Y Q : Subgroup G} {x : G} (hY : IsShort2 Y) (hx : x ∈ Y)
    (hx3 : orderOf x = 3) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y * q⁻¹ ∈ Y)
    (hYQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQc : ∀ c ∈ Y, c ∈ Q → c ∈ blockQ Y) :
    ∀ q ∈ Q, ∃ u ∈ blockU Y, x * q * x⁻¹ * q⁻¹ = x * u * x⁻¹ * u⁻¹ := by
  intro q hq
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ : ∃ c : G, c = x * q * x⁻¹ * q⁻¹ := ⟨_, rfl⟩
  have hnorm0 := norm_comm_eq_one (x := x) (q := q) hx3'
  rw [← hc] at hnorm0 ⊢
  have hcY : c ∈ Y := by
    have := Y.mul_mem hx (hQY q hq x⁻¹ (Y.inv_mem hx))
    simpa [hc, mul_assoc] using this
  have hcQ : c ∈ Q := by
    have := Q.mul_mem (hYQ x hx q hq) (Q.inv_mem hq)
    simpa [hc, mul_assoc] using this
  have hcO : c ∈ blockQ Y := hQc c hcY hcQ
  have hN : ∀ y ∈ Y, ∀ d ∈ blockQ Y, y * d * y⁻¹ ∈ blockQ Y := fun y hy d hd =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockQ Y hy) d).1 hd
  have hNU : ∀ y ∈ Y, ∀ d ∈ blockU Y, y * d * y⁻¹ ∈ blockU Y := fun y hy d hd =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockU Y hy) d).1 hd
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : G, c₁ = x * c * x⁻¹ := ⟨_, rfl⟩
  have hc₁O : c₁ ∈ blockQ Y := hc₁ ▸ hN x hx c hcO
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : G, c₂ = x * c₁ * x⁻¹ := ⟨_, rfl⟩
  have hu₁ : c₁ * c⁻¹ ∈ blockU Y := hc₁ ▸ commutator_mem_blockU' hx hcO
  have hu₂ : c₂ * c₁⁻¹ ∈ blockU Y := hc₂ ▸ commutator_mem_blockU' hx hc₁O
  have hnorm : c₂ * c₁ * c = 1 := by rw [hc₂, hc₁]; exact hnorm0
  have hc3 : c ^ 3 ∈ blockU Y := by
    have e1 : c₁ = (c₁ * c⁻¹) * c := by group
    have e2 : c₂ = (c₂ * c₁⁻¹) * c₁ := by group
    obtain ⟨u₁, hu₁'⟩ : ∃ u₁ : G, u₁ = c₁ * c⁻¹ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂'⟩ : ∃ u₂ : G, u₂ = c₂ * c₁⁻¹ := ⟨_, rfl⟩
    rw [← hu₁'] at hu₁ e1
    rw [← hu₂'] at hu₂ e2
    have hcu : c * u₁ * c⁻¹ ∈ blockU Y := hNU c hcY u₁ hu₁
    have : c ^ 3 = (u₂ * u₁ * (c * u₁ * c⁻¹))⁻¹ := by
      have h := hnorm
      rw [e2, e1] at h
      calc c ^ 3 = (u₂ * u₁ * (c * u₁ * c⁻¹))⁻¹ * ((u₂ * u₁ * (c * u₁ * c⁻¹)) * c ^ 3) := by group
        _ = (u₂ * u₁ * (c * u₁ * c⁻¹))⁻¹ := by
          have : (u₂ * u₁ * (c * u₁ * c⁻¹)) * c ^ 3 = 1 := by rw [← h]; simp [pow_succ, mul_assoc]
          rw [this, mul_one]
    rw [this]
    exact (blockU Y).inv_mem ((blockU Y).mul_mem ((blockU Y).mul_mem hu₂ hu₁) hcu)
  have hcU : c ∈ blockU Y := by
    obtain ⟨k, hk⟩ := hQ2 c hcQ
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hbez := Nat.gcd_eq_gcd_ab 3 (2 ^ k)
    rw [hcop] at hbez
    set a := Nat.gcdA 3 (2 ^ k)
    set b := Nat.gcdB 3 (2 ^ k)
    have : c = (c ^ 3) ^ a := by
      calc c = c ^ (1 : ℤ) := (zpow_one c).symm
        _ = c ^ (((3 : ℕ) : ℤ) * a + ((2 ^ k : ℕ) : ℤ) * b) := by rw [← hbez]; simp
        _ = (c ^ 3) ^ a * (c ^ 2 ^ k) ^ b := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
        _ = (c ^ 3) ^ a := by rw [hk]; simp
    rw [this]
    exact (blockU Y).zpow_mem hc3 a
  have hc₁U : c₁ ∈ blockU Y := hc₁ ▸ hNU x hx c hcU
  have hc2 : c ^ 2 = 1 := blockU_sq hY c hcU
  have hc12 : c₁ ^ 2 = 1 := blockU_sq hY c₁ hc₁U
  refine ⟨c₁, hc₁U, ?_⟩
  have e3 : x * c₁ * x⁻¹ * c₁⁻¹ = c₂ * c₁⁻¹ := by rw [hc₂]
  have hc1inv : c₁⁻¹ = c₁ := by
    have : c₁ * c₁ = 1 := by simpa [sq] using hc12
    exact (inv_eq_of_mul_eq_one_right this)
  have hcinv : c⁻¹ = c := by
    have : c * c = 1 := by simpa [sq] using hc2
    exact (inv_eq_of_mul_eq_one_right this)
  rw [e3, hc1inv]
  have : c₂ * c₁ = c⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  rw [this, hcinv]

theorem blockU_le' (Y : Subgroup G) : blockU Y ≤ Y := by
  unfold blockU
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ Y := blockQ_le Y ha
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha' hb) (Y.inv_mem ha')) (Y.inv_mem hb)

theorem ncard_commutators_le {Y : Subgroup G} {x : G} (hx : x ∈ Y) (hA3 : IsAltType Y 3) :
    {c : G | ∃ u ∈ blockU Y, c = x * u * x⁻¹ * u⁻¹}.ncard ≤ 4 := by
  obtain ⟨α, -, -, β, hβs, hβk, -⟩ := hA3
  choose f hf using hβs
  let g : Multiplicative (evenWeight 3) → G := fun b => x * (f b : G) * x⁻¹ * (f b : G)⁻¹
  have hsub : {c : G | ∃ u ∈ blockU Y, c = x * u * x⁻¹ * u⁻¹} ⊆ g '' Set.univ := by
    rintro c ⟨u, hu, rfl⟩
    refine ⟨β ⟨u, hu⟩, Set.mem_univ _, ?_⟩
    have hker : (f (β ⟨u, hu⟩)) * ⟨u, hu⟩⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hf, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hker
    have hz : ((f (β ⟨u, hu⟩) : G) * u⁻¹) ∈ Subgroup.centralizer (Y : Set G) := hker.2
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = (f (β ⟨u, hu⟩) : G) * u⁻¹ := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have hfu : (f (β ⟨u, hu⟩) : G) = z * u := by rw [hzdef]; group
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.1 hz x hx).symm
    have hcomm : x * u * x⁻¹ * u⁻¹ ∈ Y := by
      have hu' : u ∈ Y := blockU_le' Y hu
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hx hu') (Y.inv_mem hx)) (Y.inv_mem hu')
    have hzc : z * (x * u * x⁻¹ * u⁻¹) = (x * u * x⁻¹ * u⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hz _ hcomm).symm
    show x * (f (β ⟨u, hu⟩) : G) * x⁻¹ * (f (β ⟨u, hu⟩) : G)⁻¹ = x * u * x⁻¹ * u⁻¹
    rw [hfu]
    calc x * (z * u) * x⁻¹ * (z * u)⁻¹ = (x * z) * u * x⁻¹ * u⁻¹ * z⁻¹ := by group
      _ = (z * x) * u * x⁻¹ * u⁻¹ * z⁻¹ := by rw [hzx]
      _ = z * (x * u * x⁻¹ * u⁻¹) * z⁻¹ := by group
      _ = (x * u * x⁻¹ * u⁻¹) * z * z⁻¹ := by rw [hzc]
      _ = x * u * x⁻¹ * u⁻¹ := by group
  calc _ ≤ (g '' Set.univ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set (Multiplicative (evenWeight 3))).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ = 4 := by rw [Set.ncard_univ, card_evenWeight_three]

theorem exists_comm_V {Y Q V : Subgroup G} {x : G} (hY : IsShort2 Y) (hA3 : IsAltType Y 3)
    (hx : x ∈ Y) (hx3 : orderOf x = 3) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y * q⁻¹ ∈ Y)
    (hYQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQc : ∀ c ∈ Y, c ∈ Q → c ∈ blockQ Y) (hVQ : V ≤ Q)
    (hfour : 4 ≤ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹}.ncard) :
    ∀ q ∈ Q, ∃ v ∈ V, x * q * x⁻¹ * q⁻¹ = x * v * x⁻¹ * v⁻¹ := by
  have hQU := exists_comm_blockU hY hx hx3 hQY hYQ hQ2 hQc
  have hsub : {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹} ⊆
      {c : G | ∃ u ∈ blockU Y, c = x * u * x⁻¹ * u⁻¹} := by
    rintro c ⟨v, hv, rfl⟩
    exact hQU v (hVQ hv)
  have heq := Set.eq_of_subset_of_ncard_le hsub ((ncard_commutators_le hx hA3).trans hfour)
    (Set.toFinite _)
  intro q hq
  obtain ⟨u, hu, hqu⟩ := hQU q hq
  have : x * q * x⁻¹ * q⁻¹ ∈ {c : G | ∃ u ∈ blockU Y, c = x * u * x⁻¹ * u⁻¹} := ⟨u, hu, hqu⟩
  rw [← heq] at this
  exact this

end CFSG.Quasithin.C126.A5
