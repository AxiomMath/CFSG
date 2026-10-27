module

public import CFSG.Quasithin.Vol2.Ch3zCmp
public import CFSG.Quasithin.Vol2.Ch3zWreath
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 RegularWreathProduct CFSG.Quasithin.Ch3z

namespace Ch3w

section WreathAlg

variable {D : Type*} [Group D]

theorem wrI₁_one : wrI₁ (1 : D) = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrI₁]
  · rfl

theorem wrI₁_mul (σ τ : D) : wrI₁ (σ * τ) = wrI₁ σ * wrI₁ τ := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrI₁]
  · simp [wrI₁]

theorem wrI₂_one : wrI₂ (1 : D) = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrI₂]
  · rfl

theorem wrI₂_mul (σ τ : D) : wrI₂ (σ * τ) = wrI₂ σ * wrI₂ τ := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrI₂]
  · simp [wrI₂]

@[expose] def wrI₁hom : D →* D ≀ᵣ Q2 where
  toFun := wrI₁
  map_one' := wrI₁_one
  map_mul' := wrI₁_mul

@[expose] def wrI₂hom : D →* D ≀ᵣ Q2 where
  toFun := wrI₂
  map_one' := wrI₂_one
  map_mul' := wrI₂_mul

@[expose] def wrSwap : D ≀ᵣ Q2 := ⟨1, gQ⟩

theorem wrSwap_conj₁ (σ : D) : wrSwap * wrI₁ σ * wrSwap⁻¹ = wrI₂ σ := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrSwap, wrI₁, wrI₂, gQ]
  · simp +decide [wrSwap, wrI₁, wrI₂, gQ]

theorem wrSwap_conj₂ (σ : D) : wrSwap * wrI₂ σ * wrSwap⁻¹ = wrI₁ σ := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrSwap, wrI₁, wrI₂, gQ]
  · simp +decide [wrSwap, wrI₁, wrI₂, gQ]

theorem eq_wrI_mul (w : D ≀ᵣ Q2) (hw : w.right = 1) : w = wrI₁ (w.left 1) * wrI₂ (w.left gQ) := by
  apply RegularWreathProduct.ext
  · funext q
    rcases Q2_cases q with rfl | rfl <;> simp +decide [wrI₁, wrI₂, gQ]
  · simp [wrI₁, wrI₂, hw]

variable (D) in
@[expose] def baseEquiv : ↥(RegularWreathProduct.rightHom : D ≀ᵣ Q2 →* Q2).ker ≃* D × D where
  toFun w := ((w : D ≀ᵣ Q2).left 1, (w : D ≀ᵣ Q2).left gQ)
  invFun p := ⟨⟨fun q => if q = 1 then p.1 else p.2, 1⟩, rfl⟩
  left_inv w := by
    have hr : (w : D ≀ᵣ Q2).right = 1 := MonoidHom.mem_ker.mp w.2
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext q
      rcases Q2_cases q with rfl | rfl <;> simp +decide [gQ]
    · exact hr.symm
  right_inv p := by
    simp +decide
  map_mul' a b := by
    have hr : (a : D ≀ᵣ Q2).right = 1 := MonoidHom.mem_ker.mp a.2
    have e1 : (a : D ≀ᵣ Q2).right⁻¹ * 1 = 1 := by rw [hr]; decide
    have e2 : (a : D ≀ᵣ Q2).right⁻¹ * gQ = gQ := by rw [hr]; decide
    refine Prod.ext ?_ ?_
    · show ((a : D ≀ᵣ Q2) * (b : D ≀ᵣ Q2)).left 1 = (a : D ≀ᵣ Q2).left 1 * (b : D ≀ᵣ Q2).left 1
      rw [mul_left]
      show (a : D ≀ᵣ Q2).left 1 * (b : D ≀ᵣ Q2).left ((a : D ≀ᵣ Q2).right⁻¹ * 1) = _
      rw [e1]
    · show ((a : D ≀ᵣ Q2) * (b : D ≀ᵣ Q2)).left gQ =
        (a : D ≀ᵣ Q2).left gQ * (b : D ≀ᵣ Q2).left gQ
      rw [mul_left]
      show (a : D ≀ᵣ Q2).left gQ * (b : D ≀ᵣ Q2).left ((a : D ≀ᵣ Q2).right⁻¹ * gQ) = _
      rw [e2]

end WreathAlg

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_oTwoUpper {H : Subgroup G} {Γ : Type*} [Group Γ] (φ : ↥H →* Γ)
    (hφ : Function.Surjective φ) {y : Γ} (hy : Odd (orderOf y)) :
    ∃ x : ↥H, φ x = y ∧ (x : G) ∈ oTwoUpper H := by
  obtain ⟨h, rfl⟩ := hφ y
  obtain ⟨n, hn, hψ⟩ := exists_odd_pow_eq φ (isOfFinOrder_of_finite h) hy
  refine ⟨h ^ n, hψ, mem_oTwoUpper_of_odd (h ^ n).2 ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hn

theorem map_eq_top_of_sign {H J : Subgroup G} (hKJ : oTwoUpper H ≤ J) {m : ℕ}
    (φ : ↥H →* Equiv.Perm (Fin m)) (hφ : Function.Surjective φ) {x : ↥H} (hxJ : (x : G) ∈ J)
    (hx : Equiv.Perm.sign (φ x) = -1) : (J.subgroupOf H).map φ = ⊤ := by
  set Y := (J.subgroupOf H).map φ with hY
  have h3 : ∀ c : Equiv.Perm (Fin m), c.IsThreeCycle → c ∈ Y := by
    intro c hc
    have hodd : Odd (orderOf c) := by rw [hc.orderOf]; decide
    obtain ⟨x', hx'c, hx'K⟩ := exists_lift_oTwoUpper φ hφ hodd
    exact ⟨x', Subgroup.mem_subgroupOf.mpr (hKJ hx'K), hx'c⟩
  have hA : alternatingGroup (Fin m) ≤ Y := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    exact (Subgroup.closure_le Y).mpr h3
  refine eq_top_iff.mpr fun σ _ => ?_
  have hxY : φ x ∈ Y := ⟨x, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr hs)
  · have : σ * (φ x)⁻¹ ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, hx]
      decide
    have h2 := Y.mul_mem (hA this) hxY
    simpa using h2

theorem map_eq_base {H J : Subgroup G} (hKJ : oTwoUpper H ≤ J)
    (hJn : ∀ g ∈ H, ∀ x ∈ J, g * x * g⁻¹ ∈ J) {m : ℕ}
    (Φ : ↥H →* (Equiv.Perm (Fin m) ≀ᵣ Q2)) (hΦ : Function.Surjective Φ)
    (hle : ∀ x : ↥H, (x : G) ∈ J → (Φ x).right = 1)
    (hodd : ∃ x : ↥H, (x : G) ∈ J ∧ ∃ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ = -1 ∧
      (Φ x = wrI₁ σ ∨ Φ x = wrI₂ σ)) :
    (J.subgroupOf H).map Φ =
      (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker := by
  set Y := (J.subgroupOf H).map Φ with hY
  apply le_antisymm
  · rintro _ ⟨x, hxJ, rfl⟩
    exact hle x (Subgroup.mem_subgroupOf.mp hxJ)
  · have hYn : ∀ s : Equiv.Perm (Fin m) ≀ᵣ Q2, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
      intro s y hy
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨h, rfl⟩ := hΦ s
      refine ⟨h * j * h⁻¹, ?_, by simp⟩
      exact Subgroup.mem_subgroupOf.mpr (hJn h h.2 j (Subgroup.mem_subgroupOf.mp hj))
    have hodd3 : ∀ {c : Equiv.Perm (Fin m)}, c.IsThreeCycle → Odd (orderOf c) := by
      intro c hc
      rw [hc.orderOf]
      decide
    have h3₁ : ∀ c : Equiv.Perm (Fin m), c.IsThreeCycle → wrI₁ c ∈ Y := by
      intro c hc
      have hd : orderOf (wrI₁hom c) ∣ orderOf c := orderOf_map_dvd wrI₁hom c
      have hodd' : Odd (orderOf (wrI₁ c)) := (hodd3 hc).of_dvd_nat hd
      obtain ⟨x', hx'c, hx'K⟩ := exists_lift_oTwoUpper Φ hΦ hodd'
      exact ⟨x', Subgroup.mem_subgroupOf.mpr (hKJ hx'K), hx'c⟩
    have h3₂ : ∀ c : Equiv.Perm (Fin m), c.IsThreeCycle → wrI₂ c ∈ Y := by
      intro c hc
      have hd : orderOf (wrI₂hom c) ∣ orderOf c := orderOf_map_dvd wrI₂hom c
      have hodd' : Odd (orderOf (wrI₂ c)) := (hodd3 hc).of_dvd_nat hd
      obtain ⟨x', hx'c, hx'K⟩ := exists_lift_oTwoUpper Φ hΦ hodd'
      exact ⟨x', Subgroup.mem_subgroupOf.mpr (hKJ hx'K), hx'c⟩
    have hA₁ : alternatingGroup (Fin m) ≤ Y.comap wrI₁hom := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
      exact (Subgroup.closure_le _).mpr h3₁
    have hA₂ : alternatingGroup (Fin m) ≤ Y.comap wrI₂hom := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
      exact (Subgroup.closure_le _).mpr h3₂
    obtain ⟨x, hxJ, σ₀, hσ₀, hx⟩ := hodd
    have hΦx : Φ x ∈ Y := ⟨x, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
    have hb : wrI₁ σ₀ ∈ Y ∧ wrI₂ σ₀ ∈ Y := by
      rcases hx with hx | hx
      · rw [hx] at hΦx
        refine ⟨hΦx, ?_⟩
        rw [← wrSwap_conj₁ σ₀]
        exact hYn _ _ hΦx
      · rw [hx] at hΦx
        refine ⟨?_, hΦx⟩
        rw [← wrSwap_conj₂ σ₀]
        exact hYn _ _ hΦx
    have hall : ∀ σ : Equiv.Perm (Fin m), wrI₁ σ ∈ Y ∧ wrI₂ σ ∈ Y := by
      intro σ
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · exact ⟨hA₁ (Equiv.Perm.mem_alternatingGroup.mpr hs),
          hA₂ (Equiv.Perm.mem_alternatingGroup.mpr hs)⟩
      · have hmem : σ * σ₀⁻¹ ∈ alternatingGroup (Fin m) := by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, hσ₀]
          decide
        have e : σ = (σ * σ₀⁻¹) * σ₀ := by group
        refine ⟨?_, ?_⟩
        · have h1 : wrI₁ (σ * σ₀⁻¹) ∈ Y := hA₁ hmem
          have := Y.mul_mem h1 hb.1
          rwa [← wrI₁_mul, ← e] at this
        · have h1 : wrI₂ (σ * σ₀⁻¹) ∈ Y := hA₂ hmem
          have := Y.mul_mem h1 hb.2
          rwa [← wrI₂_mul, ← e] at this
    intro w hw
    have hr : w.right = 1 := hw
    rw [eq_wrI_mul w hr]
    exact Y.mul_mem (hall _).1 (hall _).2

end Lift

end Ch3w

end CFSG.Quasithin
