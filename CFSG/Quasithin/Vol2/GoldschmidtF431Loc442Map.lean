module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap

public section

namespace CFSG.Quasithin

universe u v

section Map

variable {Mb : Type u} [Group Mb] {Mb' : Type v} [Group Mb'] (θ : Mb ≃* Mb')
  {T M1 M2 : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb}

theorem PairLink.map {p p' : Mb × Mb} (h : PairLink T M1 M2 p p') :
    PairLink (T.map θ.toMonoidHom) (M1.map θ.toMonoidHom) (M2.map θ.toMonoidHom)
      (θ p.1, θ p.2) (θ p'.1, θ p'.2) := by
  obtain ⟨h1, h2, h3, h4, c, hc, e1, e2⟩ := h
  refine ⟨Subgroup.mem_map_of_mem _ h1, Subgroup.mem_map_of_mem _ h2,
    Subgroup.mem_map_of_mem _ h3, Subgroup.mem_map_of_mem _ h4, θ c, ?_, ?_, ?_⟩
  · rcases hc with hc | hc
    · exact Or.inl (Subgroup.mem_map_of_mem _ hc)
    · exact Or.inr (Subgroup.mem_map_of_mem _ hc)
  · simp [e1]
  · simp [e2]

theorem reflTransGen_pairLink_map {p p' : Mb × Mb}
    (h : Relation.ReflTransGen (PairLink T M1 M2) p p') :
    Relation.ReflTransGen (PairLink (T.map θ.toMonoidHom) (M1.map θ.toMonoidHom)
      (M2.map θ.toMonoidHom)) (θ p.1, θ p.2) (θ p'.1, θ p'.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.map θ)

theorem Loc442Datum.map (D : Loc442Datum M1 M2 T z t Vb q) :
    Loc442Datum (M1.map θ.toMonoidHom) (M2.map θ.toMonoidHom) (T.map θ.toMonoidHom) (θ z) (θ t)
      (Vb.map θ.toMonoidHom) (θ q) where
  lie := F431LieI.map θ D.lie
  V_le := by
    rw [map_centralizer_singleton]
    exact Subgroup.map_mono D.V_le
  V_card := by
    rw [Subgroup.card_map_of_injective θ.injective]
    exact D.V_card
  V_comm a ha b hb := by
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, D.V_comm a₀ ha₀ b₀ hb₀]
  V_sq a ha := by
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, D.V_sq a₀ ha₀, map_one]
  V_norm x hx v hv := by
    rw [map_centralizer_singleton] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv
    exact ⟨x₀ * v₀ * x₀⁻¹, D.V_norm x₀ hx₀ v₀ hv₀, by simp⟩
  V_conj v hv hne := by
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv
    have hne' : v₀ ≠ 1 := fun h => hne (by simp [h])
    obtain ⟨x₀, hx₀, hxv⟩ := D.V_conj v₀ hv₀ hne'
    refine ⟨θ x₀, ?_, ?_⟩
    · rw [map_centralizer_singleton]
      exact Subgroup.mem_map_of_mem _ hx₀
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [hxv]
      simp
  q_mem := by
    rw [map_centralizer_singleton]
    exact Subgroup.mem_map_of_mem _ D.q_mem
  q_comm v hv := by
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, D.q_comm v₀ hv₀]
  q_sq := by
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ D.q_sq
  q_sq_ne h := D.q_sq_ne (θ.injective (by simpa [map_pow] using h))
  M2_card := by
    rw [Subgroup.card_map_of_injective θ.injective]
    exact D.M2_card
  fusion u hu hconj := by
    rw [map_centralizer_singleton] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
    simp only [MulEquiv.coe_toMonoidHom] at hconj ⊢
    rcases D.fusion u₀ hu₀ ((isConj_map_iff θ).1 hconj) with hV | ⟨n, hn, a, ha, b, hb, hua, htb,
      b', hb', hch, hne⟩
    · exact Or.inl (Subgroup.mem_map_of_mem _ hV)
    · refine Or.inr ⟨θ n, Subgroup.mem_map_of_mem _ hn, θ a, Subgroup.mem_map_of_mem _ ha, θ b,
        Subgroup.mem_map_of_mem _ hb, by rw [hua]; simp, by rw [htb]; simp, θ b',
        Subgroup.mem_map_of_mem _ hb', reflTransGen_pairLink_map θ hch, ?_⟩
      intro h hh heq
      obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.1 hh
      simp only [MulEquiv.coe_toMonoidHom] at heq
      apply hne h₀ hh₀
      apply θ.injective
      simpa using heq

end Map

end CFSG.Quasithin
