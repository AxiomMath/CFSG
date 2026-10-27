module

public import CFSG.Quasithin.Background.ONanE68LieFacts

public section

namespace CFSG.Quasithin.E6.E68Proof.Lin3

variable {S G : Type} [Group S] [Group G] {φ : S ≃* G} {P : Subgroup S} {Q : Subgroup G}

theorem mem_iff_of_map (hPQ : P.map φ.toMonoidHom = Q) (x : S) : φ x ∈ Q ↔ x ∈ P := by
  rw [← hPQ]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := φ.injective hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_mem_normalizer_iff (hPQ : P.map φ.toMonoidHom = Q) (x : S) :
    φ x ∈ Subgroup.normalizer (Q : Set G) ↔ x ∈ Subgroup.normalizer (P : Set S) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    have := hx (φ y)
    rw [mem_iff_of_map hPQ, show φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) by simp,
      mem_iff_of_map hPQ] at this
    exact this
  · intro hx y'
    obtain ⟨y, rfl⟩ := φ.surjective y'
    rw [mem_iff_of_map hPQ, show φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) by simp,
      mem_iff_of_map hPQ]
    exact hx y

theorem map_normalizer (hPQ : P.map φ.toMonoidHom = Q) :
    (Subgroup.normalizer (P : Set S)).map φ.toMonoidHom = Subgroup.normalizer (Q : Set G) := by
  ext z
  obtain ⟨x, rfl⟩ := φ.surjective z
  rw [map_mem_normalizer_iff hPQ]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := φ.injective hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_inf_centralizer (hPQ : P.map φ.toMonoidHom = Q) (c : S) :
    (P ⊓ Subgroup.centralizer ({c} : Set S)).map φ.toMonoidHom =
      Q ⊓ Subgroup.centralizer ({φ c} : Set G) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyP, hyc⟩, rfl⟩
    refine ⟨(mem_iff_of_map hPQ y).mpr hyP, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    have := Subgroup.mem_centralizer_iff.mp hyc c rfl
    change φ c * φ y = φ y * φ c
    rw [← map_mul, ← map_mul, this]
  · rintro ⟨hzQ, hzc⟩
    obtain ⟨y, rfl⟩ := φ.surjective z
    refine ⟨y, ⟨(mem_iff_of_map hPQ y).mp hzQ, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    have := Subgroup.mem_centralizer_iff.mp hzc (φ c) rfl
    apply φ.injective
    rw [map_mul, map_mul]
    exact this

theorem map_omegaCenter (hPQ : P.map φ.toMonoidHom = Q) :
    (omegaCenter P).map φ.toMonoidHom = omegaCenter Q := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyP, hyc, hy2⟩, rfl⟩
    refine ⟨(mem_iff_of_map hPQ y).mpr hyP, fun w hw => ?_, ?_⟩
    · obtain ⟨w', rfl⟩ := φ.surjective w
      have hw' := (mem_iff_of_map hPQ w').mp hw
      change φ y * φ w' = φ w' * φ y
      rw [← map_mul, ← map_mul, hyc w' hw']
    · change φ y * φ y = 1
      rw [← map_mul, hy2, map_one]
  · rintro ⟨hzQ, hzc, hz2⟩
    obtain ⟨y, rfl⟩ := φ.surjective z
    refine ⟨y, ⟨(mem_iff_of_map hPQ y).mp hzQ, fun w hw => ?_, ?_⟩, rfl⟩
    · apply φ.injective
      rw [map_mul, map_mul]
      exact hzc (φ w) ((mem_iff_of_map hPQ w).mpr hw)
    · apply φ.injective
      rw [map_mul, map_one]
      exact hz2

theorem e68Lin3Data_of_mulEquiv (hPQ : P.map φ.toMonoidHom = Q) {n : ℕ}
    (h : E68Lin3Data Q n) : E68Lin3Data P n := by
  have hN := map_mem_normalizer_iff hPQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    have := h.quot_comm (φ a) ((hN a).mpr ha) (φ b) ((hN b).mpr hb)
    rw [show φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹ = φ (a * b * a⁻¹ * b⁻¹) by simp,
      mem_iff_of_map hPQ] at this
    exact this
  · intro c hc h3
    have h3' : orderOf (φ c) = 3 := (orderOf_injective φ.toMonoidHom φ.injective c).trans h3
    have hidx : (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P =
        (Q ⊓ Subgroup.centralizer ({φ c} : Set G)).relIndex Q := by
      rw [← map_inf_centralizer hPQ, ← hPQ]
      exact (Subgroup.relIndex_map_map_of_injective _ _ φ.injective).symm
    rw [hidx]
    exact h.order_three (φ c) ((hN c).mpr hc) h3'
  · rw [← h.card_root, ← map_omegaCenter hPQ]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).toEquiv
  · obtain ⟨x, hx, hxs⟩ := h.singer
    refine ⟨φ.symm x, ?_, fun z hz hz1 w hw hw1 => ?_⟩
    · have := (hN (φ.symm x)).mp
      rw [MulEquiv.apply_symm_apply] at this
      exact this hx
    · have hz' : φ z ∈ omegaCenter Q := by
        rw [← map_omegaCenter hPQ]
        exact ⟨z, hz, rfl⟩
      have hw' : φ w ∈ omegaCenter Q := by
        rw [← map_omegaCenter hPQ]
        exact ⟨w, hw, rfl⟩
      obtain ⟨j, hj⟩ := hxs (φ z) hz' (fun h1 => hz1 (φ.injective (by rw [h1, map_one])))
        (φ w) hw' (fun h1 => hw1 (φ.injective (by rw [h1, map_one])))
      refine ⟨j, φ.injective ?_⟩
      rw [← hj]
      simp
  · intro g hg hg1 y hy
    have hg' : φ g ∈ omegaCenter Q := by
      rw [← map_omegaCenter hPQ]
      exact ⟨g, hg, rfl⟩
    have := h.centralizer_root (φ g) hg' (fun h1 => hg1 (φ.injective (by rw [h1, map_one])))
      (φ y) (by rw [← map_mul, ← map_mul, hy])
    exact (hN y).mp this
  · intro Y hY hYt
    have hY' : Subgroup.normalizer (Q : Set G) < Y.map φ.toMonoidHom := by
      rw [← map_normalizer hPQ]
      exact (Subgroup.map_lt_map_iff_of_injective φ.injective).mpr hY
    have hYt' : Y.map φ.toMonoidHom ≠ ⊤ := fun h1 => hYt (Subgroup.map_injective φ.injective
      (by rw [h1, Subgroup.map_top_of_surjective _ φ.surjective]))
    intro hsol
    exact h.not_solvable _ hY' hYt'
      (Group.isSolvable_of_isSolvable_injective (f := (φ.subgroupMap Y).symm.toMonoidHom)
        (MulEquiv.injective _))

end CFSG.Quasithin.E6.E68Proof.Lin3
