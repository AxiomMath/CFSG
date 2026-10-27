module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.QuasithinUnique

section Checks

private instance instDecEqPermFin5 : DecidableEq (Equiv.Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

private instance instDecMemA5 :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Equiv.Perm.sign.decidableMemKer

theorem a5_pow_eight : ∀ x : alternatingGroup (Fin 5), x ^ 8 = 1 → x ^ 2 = 1 := by
  decide +kernel

theorem a5_center : ∀ z : alternatingGroup (Fin 5), (∀ y, z * y = y * z) → z = 1 := by
  decide +kernel

theorem d8_nonabelian : ∃ x y : DihedralGroup 4, x * y ≠ y * x := by
  decide

end Checks

theorem comm_of_inner {G : Type} [Group G] [Finite G] {R B : Subgroup G}
    (hR : IsSylowTwoOf R ⊤) (hRB : R ≤ Subgroup.normalizer (B : Set G))
    (hZ : ∀ z ∈ B, (∀ y ∈ B, z * y = y * z) → z = 1)
    (hexp : ∀ x ∈ B, x ^ 8 = 1 → x ^ 2 = 1) (hR8 : ∀ x ∈ R, x ^ 8 = 1)
    (hidx : (B.subgroupOf R).index = 2)
    (hinn : ∀ r ∈ R, ∃ b ∈ B, ∀ y ∈ B, r * y * r⁻¹ = b * y * b⁻¹) :
    ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ x ∈ R, ∀ y ∈ R, x ∉ B → y ∉ B → x * y ∈ B := by
    intro x hx y hy hxB hyB
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
      (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false hxB hyB)
    rwa [Subgroup.mem_subgroupOf] at this
  obtain ⟨r₀, hr₀, hr₀B⟩ : ∃ r ∈ R, r ∉ B := by
    by_contra h
    push Not at h
    have htop : B.subgroupOf R = ⊤ :=
      eq_top_iff.mpr fun r _ => (Subgroup.mem_subgroupOf).mpr (h r r.2)
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨b₀, hb₀, hb₀y⟩ := hinn r₀ hr₀
  obtain ⟨c, hc⟩ : ∃ c, c = b₀⁻¹ * r₀ := ⟨_, rfl⟩
  have hcB : ∀ y ∈ B, c * y = y * c := by
    intro y hy
    have h := hb₀y y hy
    calc c * y = b₀⁻¹ * (r₀ * y * r₀⁻¹) * r₀ := by rw [hc]; group
      _ = b₀⁻¹ * (b₀ * y * b₀⁻¹) * r₀ := by rw [h]
      _ = y * c := by rw [hc]; group
  have hcnB : c ∉ B := fun h => hr₀B (by
    have : r₀ = b₀ * c := by rw [hc]; group
    rw [this]
    exact mul_mem hb₀ h)
  have hc2B : c * c ∈ B := by
    have h1 : r₀ * b₀⁻¹ * r₀⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hRB hr₀) b₀⁻¹).mp
      (inv_mem hb₀)
    have : c * c = b₀⁻¹ * (r₀ * b₀⁻¹ * r₀⁻¹) * (r₀ * r₀) := by rw [hc]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hb₀) h1) (h2 r₀ hr₀ r₀ hr₀ hr₀B hr₀B)
  have hc2 : c * c = 1 := hZ _ hc2B fun y hy => by
    rw [mul_assoc, hcB y hy, ← mul_assoc, hcB y hy, mul_assoc]
  have hcR : ∀ x ∈ R, c * x = x * c := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact hcB x hxB
    · have hw : x * r₀⁻¹ * b₀ ∈ B :=
        mul_mem (h2 x hx r₀⁻¹ (inv_mem hr₀) hxB (fun h => hr₀B (by simpa using inv_mem h))) hb₀
      have hx' : x = x * r₀⁻¹ * b₀ * c := by rw [hc]; group
      rw [hx', mul_assoc (x * r₀⁻¹ * b₀) c c, ← mul_assoc c, hcB _ hw, mul_assoc]
  have hcR' : c ∈ R := by
    have hs2 : IsPGroup 2 (Subgroup.zpowers c) := by
      have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hc2])
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [hcR x hx, mul_inv_cancel_right]
        exact hx
      · have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
        have hcx := hcR _ hx
        rw [hci] at hcx hx
        have e : c * x = x * c := by
          have h1 : c * (c * x * c) = x * c := by rw [← mul_assoc, ← mul_assoc, hc2, one_mul]
          have h2 : c * x * c * c = c * x := by rw [mul_assoc, hc2, mul_one]
          rw [h1, h2] at hcx
          exact hcx.symm
        have h3 : c * x * c = x := by rw [e, mul_assoc, hc2, mul_one]
        rwa [h3] at hx
    have hX := hR.eq_of_le (le_sup_right : R ≤ Subgroup.zpowers c ⊔ R) le_top
      (hs2.to_sup_of_normal_right' hR.2.1 hN)
    have : c ∈ Subgroup.zpowers c ⊔ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    rwa [hX] at this
  have hcomm : ∀ x ∈ R, x ∈ B → ∀ y ∈ R, y ∈ B → Commute x y := by
    intro x hx hxB y hy hyB
    have ex : x * x = 1 := by rw [← sq]; exact hexp x hxB (hR8 x hx)
    have ey : y * y = 1 := by rw [← sq]; exact hexp y hyB (hR8 y hy)
    have exy : x * y * (x * y) = 1 := by
      rw [← sq]; exact hexp _ (mul_mem hxB hyB) (hR8 _ (mul_mem hx hy))
    show x * y = y * x
    calc x * y = x * y * (x * (y * y) * x) := by rw [ey, mul_one, ex, mul_one]
      _ = x * y * (x * y) * (y * x) := by group
      _ = y * x := by rw [exy, one_mul]
  have hdec : ∀ x ∈ R, ∃ y ∈ R, y ∈ B ∧ (x = y ∨ x = y * c) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact ⟨x, hx, hxB, Or.inl rfl⟩
    · refine ⟨x * c, mul_mem hx hcR', h2 x hx c hcR' hxB hcnB, Or.inr ?_⟩
      rw [mul_assoc, hc2, mul_one]
  intro x hx y hy
  obtain ⟨u, hu, huB, hxu⟩ := hdec x hx
  obtain ⟨v, hv, hvB, hyv⟩ := hdec y hy
  have huv := hcomm u hu huB v hv hvB
  have hcu : Commute c u := hcR u hu
  have hcv : Commute c v := hcR v hv
  rcases hxu with rfl | rfl <;> rcases hyv with rfl | rfl
  · exact huv.eq
  · exact (huv.mul_right hcu.symm).eq
  · exact (huv.mul_left hcv).eq
  · exact ((huv.mul_right hcu.symm).mul_left (hcv.mul_right (Commute.refl c))).eq

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
