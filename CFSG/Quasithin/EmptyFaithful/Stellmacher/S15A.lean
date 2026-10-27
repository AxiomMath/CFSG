module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S15

variable {G : Type} [Group G]

theorem comm_mem_of_cube {B : Subgroup G} {d a : G} (hd3 : d ^ 3 = 1)
    (hc2 : d * a * d⁻¹ * a⁻¹ * (d * a * d⁻¹ * a⁻¹) = 1)
    (hdB : ∀ b ∈ B, d * b * d⁻¹ ∈ B)
    (hb : d * (d * a * d⁻¹ * a⁻¹) * d⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ ∈ B) :
    d * a * d⁻¹ * a⁻¹ ∈ B := by
  obtain ⟨c, hc⟩ : ∃ c, d * a * d⁻¹ * a⁻¹ = c := ⟨_, rfl⟩
  rw [hc] at hc2 hb ⊢
  obtain ⟨b, hbd⟩ : ∃ b, d * c * d⁻¹ * c⁻¹ = b := ⟨_, rfl⟩
  rw [hbd] at hb
  have e1 : d * a * d⁻¹ = c * a := by rw [← hc]; group
  have e2 : d * c * d⁻¹ = b * c := by rw [← hbd]; group
  have e3 : d * (d * a * d⁻¹) * d⁻¹ = b * a := by
    rw [e1, show d * (c * a) * d⁻¹ = (d * c * d⁻¹) * (d * a * d⁻¹) by group, e2, e1,
      show b * c * (c * a) = b * (c * c) * a by group, hc2, mul_one]
  have e4 : d * (d * (d * a * d⁻¹) * d⁻¹) * d⁻¹ = (d * b * d⁻¹) * c * a := by
    rw [e3, show d * (b * a) * d⁻¹ = (d * b * d⁻¹) * (d * a * d⁻¹) by group, e1]
    group
  have hddd : d * d * d = 1 := by rw [← pow_three', hd3]
  have e5 : d * (d * (d * a * d⁻¹) * d⁻¹) * d⁻¹ = a := by
    have h : d * (d * (d * a * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * a * (d * d * d)⁻¹ := by group
    rw [h, hddd]
    group
  have e6 : (d * b * d⁻¹) * c = 1 := mul_eq_right.mp (e4.symm.trans e5)
  rw [eq_inv_of_mul_eq_one_right e6]
  exact B.inv_mem (hdB b hb)

theorem exists_chiefStep_of_cube [Finite G] {X V : Subgroup G} (hV2 : ∀ v ∈ V, v * v = 1)
    {d : G} (hdX : d ∈ X) (hd3 : d ^ 3 = 1) :
    ∀ (n : ℕ) (A B : Subgroup G), Nat.card A ≤ Nat.card B + n → IsNormalIn X V A →
      IsNormalIn X V B → B ≤ A → (∃ a ∈ A, d * a * d⁻¹ * a⁻¹ ∉ B) →
      ∃ L N : Subgroup G, IsChiefStep X V L N ∧ ∃ x ∈ N, d * x * d⁻¹ * x⁻¹ ∉ L := by
  intro n
  induction n with
  | zero =>
    rintro A B hn hA - hBA ⟨a, ha, hab⟩
    have hBA' : B = A := Subgroup.eq_of_le_of_card_ge hBA (by omega)
    exact absurd (hBA' ▸ A.mul_mem (hA.2 d hdX a ha) (A.inv_mem ha)) hab
  | succ n ih =>
    rintro A B hn hA hB hBA ⟨a, ha, hab⟩
    have hdA : ∀ x ∈ A, d * x * d⁻¹ * x⁻¹ ∈ A := fun x hx =>
      A.mul_mem (hA.2 d hdX x hx) (A.inv_mem hx)
    by_cases hch : IsChiefStep X V B A
    · exact ⟨B, A, hch, a, ha, hab⟩
    obtain ⟨K, hK, hBK, hKA, hKB, hKA'⟩ :
        ∃ K : Subgroup G, IsNormalIn X V K ∧ B ≤ K ∧ K ≤ A ∧ K ≠ B ∧ K ≠ A := by
      by_contra hno
      push Not at hno
      exact hch ⟨hA, hB, lt_of_le_of_ne hBA (fun h => hab (h ▸ hdA a ha)),
        fun K hK hBK hKA => (em (K = B)).imp id (hno K hK hBK hKA)⟩
    have hcBK : Nat.card B < Nat.card K :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hBK (Ne.symm hKB))
    have hcKA : Nat.card K < Nat.card A := Subgroup.card_lt_of_lt (lt_of_le_of_ne hKA hKA')
    by_cases hk : ∃ k ∈ K, d * k * d⁻¹ * k⁻¹ ∉ B
    · exact ih K B (by omega) hK hB hBK hk
    push Not at hk
    refine ih A K (by omega) hA hK hKA ?_
    by_contra hno
    push Not at hno
    exact hab (comm_mem_of_cube hd3 (hV2 _ (hK.1 (hno a ha))) (fun b hb => hB.2 d hdX b hb)
      (hk _ (hno a ha)))

theorem comm_eq_one_or_eq {V : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {s : G}
    (hsV : ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hs : (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V = 2) {n₀ : G} (hn₀ : n₀ ∈ V)
    (hn₀s : s * n₀ * s⁻¹ * n₀⁻¹ ≠ 1) :
    ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ = 1 ∨ s * v * s⁻¹ * v⁻¹ = s * n₀ * s⁻¹ * n₀⁻¹ := by
  intro v hv
  set H : Subgroup ↥V := (V ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf V with hHdef
  have hH : H.index = 2 := hs
  have memH : ∀ w : ↥V, w ∈ H ↔ (w : G) * s = s * (w : G) := fun w => by
    rw [hHdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have comm_one : ∀ w : G, w * s = s * w → s * w * s⁻¹ * w⁻¹ = 1 := fun w h => by
    rw [← h]; group
  by_cases h1 : s * v * s⁻¹ * v⁻¹ = 1
  · exact Or.inl h1
  right
  have hvH : (⟨v, hv⟩ : ↥V) ∉ H := fun h => h1 (comm_one v ((memH _).mp h))
  have hnH : (⟨n₀, hn₀⟩ : ↥V)⁻¹ ∉ H := fun h =>
    hn₀s (comm_one n₀ ((memH _).mp (H.inv_mem_iff.mp h)))
  have hmul := (Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false hvH hnH)
  have hcomm : (v * n₀⁻¹) * s = s * (v * n₀⁻¹) := (memH _).mp hmul
  have hB : s * n₀ * s⁻¹ ∈ V := hsV n₀ hn₀
  have h2 : n₀⁻¹ * (s * n₀ * s⁻¹) ∈ V := V.mul_mem (V.inv_mem hn₀) hB
  have hA : s * v * s⁻¹ = v * (n₀⁻¹ * (s * n₀ * s⁻¹)) := by
    calc s * v * s⁻¹ = s * (v * n₀⁻¹) * s⁻¹ * (s * n₀ * s⁻¹) := by group
      _ = (v * n₀⁻¹) * s * s⁻¹ * (s * n₀ * s⁻¹) := by rw [← hcomm]
      _ = v * (n₀⁻¹ * (s * n₀ * s⁻¹)) := by group
  calc s * v * s⁻¹ * v⁻¹ = v * (n₀⁻¹ * (s * n₀ * s⁻¹)) * v⁻¹ := by rw [hA]
    _ = (n₀⁻¹ * (s * n₀ * s⁻¹)) * v * v⁻¹ := by rw [hVc v hv _ h2]
    _ = n₀⁻¹ * (s * n₀ * s⁻¹) := by group
    _ = s * n₀ * s⁻¹ * n₀⁻¹ := hVc _ (V.inv_mem hn₀) _ hB

theorem le_of_conj_swap_mem {X K : Subgroup G} (θ : ↥X →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ) (hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ K) {s : G} (hs : s ∈ X)
    (hswap : (θ ⟨s, hs⟩).IsSwap) (hconj : ∀ x ∈ X, x * s * x⁻¹ ∈ K) : X ≤ K := by
  set K' : Subgroup (Equiv.Perm (Fin 5)) := (K.subgroupOf X).map θ
  have hsw : ∀ τ : Equiv.Perm (Fin 5), τ.IsSwap → τ ∈ K' := by
    intro τ hτ
    have hc : IsConj (θ ⟨s, hs⟩) τ := by
      obtain ⟨a, b, hab, hsab⟩ := hswap
      obtain ⟨c, e, hce, rfl⟩ := hτ
      rw [hsab]
      exact Equiv.Perm.isConj_swap hab hce
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    obtain ⟨x, rfl⟩ := hθ c
    refine Subgroup.mem_map.mpr ⟨x * ⟨s, hs⟩ * x⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hconj x x.2
    · rw [map_mul, map_mul, map_inv]
      exact hc
  have htop : K' = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    exact hsw
  intro y hy
  have hyK : θ ⟨y, hy⟩ ∈ K' := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hk, hky⟩ := hyK
  have h1 : θ (⟨y, hy⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hky, mul_inv_cancel]
  have h2 := K.mul_mem (hker _ h1) (Subgroup.mem_subgroupOf.mp hk)
  simpa using h2

private theorem orth_fixed_check :
    ∀ w : orth.W, orth.act (finRotate 5) w = w → w = 1 := by
  decide +kernel

theorem orth_eq_one_of_fixed {w : orth.W} (hw : ∀ σ : Equiv.Perm (Fin 5), orth.act σ w = w) :
    w = 1 :=
  orth_fixed_check w (hw _)

end F53.Stellmacher.S15

end CFSG.Quasithin
