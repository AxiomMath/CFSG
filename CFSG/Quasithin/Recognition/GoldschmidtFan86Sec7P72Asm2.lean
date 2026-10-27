module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open scoped IsMulCommutative

namespace P72

theorem fin5_cover : ∀ k a b c d : Fin 5, [k, a, b, c, d].Nodup → ∀ x : Fin 5,
    x ∈ [k, a, b, c, d] := by
  decide +kernel

theorem prod_ofFn_five {M : Type*} [Monoid M] (f : Fin 5 → M) (hc : ∀ i j, f i * f j = f j * f i)
    (k a b c d : Fin 5) (hnd : [k, a, b, c, d].Nodup) :
    (List.ofFn f).prod = f k * f a * f b * f c * f d := by
  have hperm : (List.ofFn f).Perm [f k, f a, f b, f c, f d] := by
    rw [List.ofFn_eq_map]
    have : (List.finRange 5).Perm [k, a, b, c, d] := by
      rw [List.perm_ext_iff_of_nodup (List.nodup_finRange 5) hnd]
      intro x
      simp only [List.mem_finRange, true_iff]
      exact fin5_cover k a b c d hnd x
    simpa using this.map f
  rw [hperm.prod_eq' (List.pairwise_ofFn.2 fun i j _ => hc i j)]
  simp [mul_assoc]

theorem pm_mul {M : Type*} [CommGroup M] {u a b : M} (hu : u * u = 1) (ha : a = 1 ∨ a = u)
    (hb : b = 1 ∨ b = u) : a * b = 1 ∨ a * b = u := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hu]

theorem alg5 {M : Type*} [CommGroup M] {K A A' B C C' D X u : M}
    (hA : A * A' * C * C' = X) (hX : X = K ∨ X = K * u) (hB : B = A' ∨ B = A' * u)
    (hD : D = C' ∨ D = C' * u) (hK : K * K = 1) (hu : u * u = 1) :
    K * A * B * C * D = 1 ∨ K * A * B * C * D = u := by
  have h1 : ∀ w₁ w₂ : M, K * A * (A' * w₁) * C * (C' * w₂) = (K * X) * (w₁ * w₂) := by
    intro w₁ w₂
    rw [← hA]
    simp only [mul_comm, mul_left_comm]
  have hKX : K * X = 1 ∨ K * X = u := by
    rcases hX with rfl | rfl
    · exact Or.inl hK
    · right
      rw [← mul_assoc, hK, one_mul]
  have hB' : ∃ w : M, (w = 1 ∨ w = u) ∧ B = A' * w := by
    rcases hB with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨u, Or.inr rfl, rfl⟩
  have hD' : ∃ w : M, (w = 1 ∨ w = u) ∧ D = C' * w := by
    rcases hD with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨u, Or.inr rfl, rfl⟩
  obtain ⟨w₁, hw₁, rfl⟩ := hB'
  obtain ⟨w₂, hw₂, rfl⟩ := hD'
  rw [h1]
  exact pm_mul hu hKX (pm_mul hu hw₁ hw₂)

theorem alg5_sub {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H]
    {K A A' B C C' D X u : G} (hK' : K ∈ H) (hA' : A ∈ H) (hA'' : A' ∈ H) (hB' : B ∈ H)
    (hC' : C ∈ H) (hC'' : C' ∈ H) (hD' : D ∈ H) (hX' : X ∈ H) (hu' : u ∈ H)
    (hA : A * A' * C * C' = X) (hX : X = K ∨ X = K * u) (hB : B = A' ∨ B = A' * u)
    (hD : D = C' ∨ D = C' * u) (hK : K * K = 1) (hu : u * u = 1) :
    K * A * B * C * D = 1 ∨ K * A * B * C * D = u := by
  have := alg5 (M := H) (K := ⟨K, hK'⟩) (A := ⟨A, hA'⟩) (A' := ⟨A', hA''⟩) (B := ⟨B, hB'⟩)
    (C := ⟨C, hC'⟩) (C' := ⟨C', hC''⟩) (D := ⟨D, hD'⟩) (X := ⟨X, hX'⟩) (u := ⟨u, hu'⟩)
    (Subtype.ext hA)
    (hX.imp (fun e => Subtype.ext e) (fun e => Subtype.ext e))
    (hB.imp (fun e => Subtype.ext e) (fun e => Subtype.ext e))
    (hD.imp (fun e => Subtype.ext e) (fun e => Subtype.ext e))
    (Subtype.ext hK) (Subtype.ext hu)
  exact this.imp (fun e => congrArg Subtype.val e) (fun e => congrArg Subtype.val e)

end P72

end CFSG.Quasithin.Fan86
