
module

public import CFSG.Quasithin.Background.A3Structure38Facts

public section

namespace CFSG.Quasithin

namespace A38

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem mem_map_conj {t x : G} {K : Subgroup G} :
    x ∈ K.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * x * t ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : t⁻¹ * ((MulAut.conj t).toMonoidHom y) * t = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [h]
  · intro h
    exact ⟨t⁻¹ * x * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_eq_iff {t : G} {K : Subgroup G} :
    K.map (MulAut.conj t).toMonoidHom = K ↔ t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have h1 : t * x * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom ↔ x ∈ K := by
      rw [mem_map_conj]
      simp [mul_assoc]
    rw [h] at h1
    exact h1.symm
  · intro h
    ext x
    rw [mem_map_conj]
    have := h (t⁻¹ * x * t)
    simpa [mul_assoc] using this

theorem exists_not_mem_normalizer {K : Subgroup G} (h : ¬ K.Normal) :
    ∃ t : G, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  push Not at hcon
  exact h (Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun t _ => hcon t))

theorem isComponent_conj {t : G} {K : Subgroup G} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK

noncomputable def conjEquiv (t : G) (K : Subgroup G) :
    ↥K ≃* ↥(K.map (MulAut.conj t).toMonoidHom) :=
  K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective

theorem cComp_conj [Finite G] {t : G} {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) :
    L.map (MulAut.conj t).toMonoidHom ∈ cComp (⊤ : Subgroup G) := by
  have := cComp_map_mulEquiv (MulAut.conj t) hL
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj t).surjective] at this

theorem A134Types.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : A134Types Y) : A134Types X := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | h | ⟨p, k, hp, hp3, hk1, hk2, h⟩
  · exact Or.inl ⟨n, statedClassicalModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨n, suzukiModel_of_mulEquiv e h⟩)
  · obtain ⟨c⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans c⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, k, hp, hp3, hk1, hk2, statedClassicalModel_of_mulEquiv e h⟩))

theorem part12_strong (hF : A38Facts) (H : Type) [Group H] [Finite H] (hq : IsQuasithin H)
    (hK : CFSG.SectionRank.IsKGroupCat H) {K : Subgroup H} (hKc : CFSG.IsComponent K)
    (hO2 : CFSG.pCore 2 ↥K = ⊥) (hnorm : ¬ K.Normal) :
    ∃ t : H, t ∉ Subgroup.normalizer (K : Set H) ∧
      (∀ g : H, K.map (MulAut.conj g).toMonoidHom = K ∨
        K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) ∧
      ((Subgroup.center ↥K = ⊥ ∧ A134Types ↥K) ∨
        (IsSU3 8 ↥K ∧ 3 ≤ CFSG.Open.pRank 3 (K ⊔ K.map (MulAut.conj t).toMonoidHom))) := by
  obtain ⟨t, ht⟩ := exists_not_mem_normalizer hnorm
  have hK'c : CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) := isComponent_conj hKc
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom := fun h => ht (map_conj_eq_iff.mp h.symm)
  obtain ⟨h2, h3⟩ := hF.a134 H hq hK K (K.map (MulAut.conj t).toMonoidHom) hKc hK'c hne
    ⟨conjEquiv t K⟩
  refine ⟨t, ht, fun g => ?_, ?_⟩
  · exact h2 _ (isComponent_conj hKc) ⟨(conjEquiv g K).symm⟩
  · rcases h3 with h3 | ⟨h3, h3r⟩
    · left
      have hcenter : IsPGroup 2 (Subgroup.center ↥K) := hF.mult2 ↥K hKc.1 h3
      have hle : Subgroup.center ↥K ≤ CFSG.pCore 2 ↥K :=
        le_sSup ⟨inferInstance, hcenter⟩
      have hbot : Subgroup.center ↥K = ⊥ := le_bot_iff.mp (hO2 ▸ hle)
      refine ⟨hbot, ?_⟩
      exact A134Types.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm h3
    · exact Or.inr ⟨h3, h3r.ge⟩

theorem conjClosure_eq_sup {K : Subgroup G} {t : G}
    (hconj : ∀ g : G, K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    conjClosure K ⊤ = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  refine le_antisymm (conjClosure_le fun h _ z hz => ?_) (sup_le (le_conjClosure K ⊤) ?_)
  · have hmem : h * z * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rcases hconj h with h1 | h1
    · rw [h1] at hmem
      exact Subgroup.mem_sup_left hmem
    · rw [h1] at hmem
      exact Subgroup.mem_sup_right hmem
  · rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using mem_conjClosure (Subgroup.mem_top t) hz

theorem a38_part12 (hF : A38Facts) (H : Type) [Group H] [Finite H] : A38Part12 H := by
  intro hq hK K hKc hO2 hnorm
  obtain ⟨t, ht, hconj, hlist⟩ := part12_strong hF H hq hK hKc hO2 hnorm
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom := fun h => ht (map_conj_eq_iff.mp h.symm)
  have hset : conjSubgroups K = {K, K.map (MulAut.conj t).toMonoidHom} := by
    ext K'
    constructor
    · rintro ⟨g, hg⟩
      rw [hg]
      exact hconj g
    · intro h
      rcases h with h | h
      · exact ⟨1, h.trans (map_conj_eq_iff.mpr (Subgroup.one_mem _)).symm⟩
      · exact ⟨t, h⟩
  have hother : ∀ t' : H, t' ∉ Subgroup.normalizer (K : Set H) →
      K.map (MulAut.conj t').toMonoidHom = K.map (MulAut.conj t).toMonoidHom := fun t' ht' =>
    (hconj t').resolve_left fun h => ht' (map_conj_eq_iff.mp h)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hset]
    exact Set.ncard_pair hne
  · intro t' ht'
    rw [hother t' ht']
    exact conjClosure_eq_sup hconj
  · rcases hlist with ⟨-, h | h | h | h⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end A38

end CFSG.Quasithin
