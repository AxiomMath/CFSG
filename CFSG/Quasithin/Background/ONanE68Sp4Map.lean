module

public import CFSG.Quasithin.Background.ONanE68LieFacts

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

section Map

variable {S T : Type} [Group S] [Group T] (e : S ≃* T)

theorem mem_normalizer_map_iff {H : Subgroup S} {x : T} :
    x ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup T) : Set T) ↔
      e.symm x ∈ Subgroup.normalizer (H : Set S) := by
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv]

theorem mem_centralizer_map_iff {H : Subgroup S} {x : T} :
    x ∈ Subgroup.centralizer ((H.map e.toMonoidHom : Subgroup T) : Set T) ↔
      e.symm x ∈ Subgroup.centralizer (H : Set S) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := h (e y) (Subgroup.mem_map_of_mem _ hy)
    apply e.injective
    simpa using this
  · intro h y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have := congrArg e (h y' hy')
    simpa using this

theorem mem_centralizer_singleton_map_iff {c : S} {x : T} :
    x ∈ Subgroup.centralizer ({e c} : Set T) ↔ e.symm x ∈ Subgroup.centralizer ({c} : Set S) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply e.injective
    simpa using h (e y) rfl
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using congrArg e (h c rfl)

theorem omegaCenter_map (P : Subgroup S) :
    omegaCenter (P.map e.toMonoidHom) = (omegaCenter P).map e.toMonoidHom := by
  ext z
  rw [Subgroup.mem_map_equiv (K := omegaCenter P), mem_omegaCenter, mem_omegaCenter,
    Subgroup.mem_map_equiv (K := P)]
  constructor
  · rintro ⟨hz, hc, h2⟩
    refine ⟨hz, fun y hy => ?_, ?_⟩
    · have := hc (e y) (Subgroup.mem_map_of_mem _ hy)
      apply e.injective
      simpa using this
    · apply e.injective
      simpa using h2
  · rintro ⟨hz, hc, h2⟩
    refine ⟨hz, fun y hy => ?_, ?_⟩
    · have hy' := Subgroup.mem_map_equiv.1 hy
      have := hc _ hy'
      apply e.symm.injective
      simpa using this
    · apply e.symm.injective
      simpa using h2

theorem inv_map {P Z : Subgroup S}
    (h : ∀ b ∈ Subgroup.normalizer (P : Set S), ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) :
    ∀ b ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T),
      ∀ z ∈ Z.map e.toMonoidHom, b * z * b⁻¹ ∈ Z.map e.toMonoidHom := by
  intro b hb z hz
  obtain ⟨z', hz', rfl⟩ := hz
  have := Subgroup.mem_map_of_mem e.toMonoidHom (h _ ((mem_normalizer_map_iff e).1 hb) z' hz')
  simpa using this

theorem singer_map {P Z W : Subgroup S}
    (h : ∃ x ∈ Subgroup.normalizer (P : Set S), (∀ z ∈ W, x * z = z * x) ∧
      ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w) :
    ∃ x ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T),
      (∀ z ∈ W.map e.toMonoidHom, x * z = z * x) ∧
      ∀ z ∈ Z.map e.toMonoidHom, z ≠ 1 → ∀ w ∈ Z.map e.toMonoidHom, w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w := by
  obtain ⟨x, hx, hxW, hxZ⟩ := h
  refine ⟨e x, (mem_normalizer_map_iff e).2 (by simpa using hx), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    simpa using congrArg e (hxW z hz)
  · rintro _ ⟨z, hz, rfl⟩ hz1 _ ⟨w, hw, rfl⟩ hw1
    have hz1' : z ≠ 1 := fun h' => hz1 (by simp [h'])
    have hw1' : w ≠ 1 := fun h' => hw1 (by simp [h'])
    obtain ⟨j, hj⟩ := hxZ z hz hz1' w hw hw1'
    exact ⟨j, by simpa using congrArg e hj⟩

theorem aut_map {P Z : Subgroup S}
    (h : ∀ y ∈ Subgroup.normalizer (Z : Set S), ∃ b ∈ Subgroup.normalizer (P : Set S),
      ∀ z ∈ Z, y * z * y⁻¹ = b * z * b⁻¹) :
    ∀ y ∈ Subgroup.normalizer ((Z.map e.toMonoidHom : Subgroup T) : Set T),
      ∃ b ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T),
        ∀ z ∈ Z.map e.toMonoidHom, y * z * y⁻¹ = b * z * b⁻¹ := by
  intro y hy
  obtain ⟨b, hb, hbz⟩ := h _ ((mem_normalizer_map_iff e).1 hy)
  refine ⟨e b, (mem_normalizer_map_iff e).2 (by simpa using hb), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have := congrArg e (hbz z hz)
  have hy' : e (e.symm y) = y := e.apply_symm_apply y
  simp only [map_mul, map_inv, hy'] at this
  simpa using this

theorem not_centralizer_map {P Z : Subgroup S}
    (h : ¬ Subgroup.centralizer (Z : Set S) ≤ Subgroup.normalizer (P : Set S)) :
    ¬ Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup T) : Set T) ≤
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T) := by
  intro hle
  apply h
  intro g hg
  have := hle ((mem_centralizer_map_iff e).2 (by simpa using hg) : e g ∈ _)
  simpa using (mem_normalizer_map_iff e).1 this

theorem E68Sp4Data.map {P : Subgroup S} {n : ℕ} (h : E68Sp4Data P n) :
    E68Sp4Data (P.map e.toMonoidHom) n where
  quot_comm a ha b hb := by
    have := Subgroup.mem_map_of_mem e.toMonoidHom (h.quot_comm _ ((mem_normalizer_map_iff e).1 ha)
      _ ((mem_normalizer_map_iff e).1 hb))
    simpa using this
  order_three c hc h3 := by
    obtain ⟨c', rfl⟩ := e.surjective c
    have hc' : c' ∈ Subgroup.normalizer (P : Set S) := by
      simpa using (mem_normalizer_map_iff e).1 hc
    have h3' : orderOf c' = 3 := by rw [← MulEquiv.orderOf_eq e c']; exact h3
    have hmap : Subgroup.centralizer ({e c'} : Set T) =
        (Subgroup.centralizer ({c'} : Set S)).map e.toMonoidHom := by
      ext x
      rw [mem_centralizer_singleton_map_iff, Subgroup.mem_map_equiv]
    rw [hmap, ← Subgroup.map_inf_eq _ _ _ e.injective,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact h.order_three c' hc' h3'
  card_root := by
    rw [omegaCenter_map, Subgroup.card_map_of_injective e.injective]
    exact h.card_root
  split := by
    obtain ⟨Zs, Zl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h.split
    refine ⟨Zs.map e.toMonoidHom, Zl.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, inv_map e h7,
      inv_map e h8, singer_map e h9, singer_map e h10, aut_map e h11, aut_map e h12,
      not_centralizer_map e h13, not_centralizer_map e h14⟩
    · rw [omegaCenter_map]
      exact Subgroup.map_mono h1
    · rw [omegaCenter_map]
      exact Subgroup.map_mono h2
    · rw [← Subgroup.map_inf_eq _ _ _ e.injective, h3, Subgroup.map_bot]
    · rw [← Subgroup.map_sup, h4, omegaCenter_map]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact h5
    · rw [Subgroup.card_map_of_injective e.injective]
      exact h6
  centralizer_root := by
    intro x hx
    rw [omegaCenter_map] at hx
    exact (mem_normalizer_map_iff e).2 (h.centralizer_root ((mem_centralizer_map_iff e).1 hx))
  not_solvable := by
    intro Y hlt hY hsolv
    have hlt' : Subgroup.normalizer (P : Set S) < Y.comap e.toMonoidHom := by
      have h1 : Subgroup.normalizer (P : Set S) =
          (Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T)).comap
            e.toMonoidHom := by
        ext x
        rw [Subgroup.mem_comap, mem_normalizer_map_iff]
        simp
      rw [h1]
      exact (Subgroup.comap_lt_comap_of_surjective e.surjective).2 hlt
    have hY' : Y.comap e.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hY
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y, htop,
        Subgroup.map_top_of_surjective _ e.surjective]
    have hsolv' : Group.IsSolvable ↥(Y.comap e.toMonoidHom) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom.subgroupComap Y)
        (fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)))
    exact h.not_solvable _ hlt' hY' hsolv'

end Map

end E68Proof

end E6

end CFSG.Quasithin
