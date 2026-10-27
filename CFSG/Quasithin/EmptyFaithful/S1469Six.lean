module

public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Stage1466Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      ¬ I ⊓ M ≤ mcOf T →
        yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) ∧
          yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.tI_lt (S : Setting146 G T M) {u : G} {I : Subgroup G} (hI : IsI T M u I) :
    T ⊓ I < T := by
  refine lt_of_le_of_ne inf_le_left fun h => hI.2.1 ?_
  have hTI : T ≤ I := inf_eq_left.mp h
  exact S.le_mcOf (⟨⟨hTI, hI.1.2⟩, hI.2.2⟩ : IsHTM T M I)

theorem Setting146.card_tI_gt (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : IsInvU T M H u) {I : Subgroup G}
    (hcases : T ⊓ I = tU T u ∨ T ⊓ I = tZero T u) (hbig : 2 ^ 11 < Nat.card T) :
    2 ^ 9 < Nat.card (T ⊓ I : Subgroup G) := by
  have h4 : (T ⊓ I).relIndex T = 4 ∨ (T ⊓ I).relIndex T = 2 := by
    rcases hcases with h | h
    · left; rw [h]; exact S.relIndex_tU_T hH hu
    · right; rw [h]; exact hu.index_two
  have hmul := Subgroup.relIndex_mul_card (H := T ⊓ I) (K := T)
  rw [inf_eq_left.mpr (inf_le_left : T ⊓ I ≤ T)] at hmul
  by_contra hle
  push Not at hle
  rcases h4 with h | h <;> rw [h] at hmul <;> omega

theorem exists_isIMin_le {u : G} {I : Subgroup G} (hI : IsIStar T M u I) :
    ∃ J : Subgroup G, IsIMin T M u J ∧ J ≤ I := by
  classical
  obtain ⟨J, ⟨hJ, hJI⟩, hmin⟩ := Set.exists_min_image
    {J : Subgroup G | IsIStar T M u J ∧ J ≤ I} (fun J => Nat.card J) (Set.toFinite _)
    ⟨I, hI, le_rfl⟩
  refine ⟨J, ⟨hJ, fun K hK hKJ => ?_⟩, hJI⟩
  exact Subgroup.eq_of_le_of_card_ge hKJ (hmin K ⟨hK, hKJ.trans hJI⟩)

omit [Finite G] in
theorem tI_eq_of_le {u : G} {I J : Subgroup G} (hI : IsIStar T M u I) (hJ : IsIStar T M u J)
    (hJI : J ≤ I) : T ⊓ J = T ⊓ I :=
  eq_of_le_of_not_lt (inf_le_inf_left T hJI) (hJ.2 I hI.1)

omit [Finite G] in
theorem mem_normalizer_of_characteristic_subgroupOf {R C : Subgroup G}
    (hC : (C.subgroupOf R).Characteristic) (hCR : C ≤ R) {t : G}
    (ht : t ∈ Subgroup.normalizer (R : Set G)) : t ∈ Subgroup.normalizer (C : Set G) := by
  have key : ∀ t ∈ Subgroup.normalizer (R : Set G), ∀ x ∈ C, t * x * t⁻¹ ∈ C := by
    intro t ht x hx
    have hmem : ∀ r : R, t * (r : G) * t⁻¹ ∈ R := fun r =>
      (Subgroup.mem_normalizer_iff.mp ht r).mp r.2
    have hmem' : ∀ r : R, t⁻¹ * (r : G) * t ∈ R := fun r => by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) r).mp r.2
      simpa using this
    let φ : R ≃* R :=
      { toFun := fun r => ⟨t * (r : G) * t⁻¹, hmem r⟩
        invFun := fun r => ⟨t⁻¹ * (r : G) * t, hmem' r⟩
        left_inv := fun r => Subtype.ext (by simp [mul_assoc])
        right_inv := fun r => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have h1 := Subgroup.characteristic_iff_map_eq.mp hC φ
    have h2 : φ ⟨x, hCR hx⟩ ∈ (C.subgroupOf R).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem stage1466_four_of (h3 : Stage1466Three) :
    ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
      IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
        cgsIn I (T ⊓ I) ≤ I ⊓ mcOf T ∨
          (yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) ∧
            yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) := by
  intro G _ _ T M H u S hH hu I hI
  by_cases hc : cgsIn I (T ⊓ I) ≤ I ⊓ mcOf T
  · exact Or.inl hc
  right
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have key : ∃ C : Subgroup G, C ≤ T ⊓ I ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ I)).Characteristic ∧
      ¬ I ⊓ Subgroup.normalizer (C : Set G) ≤ mcOf T := by
    by_contra hno
    push Not at hno
    exact hc (iSup_le fun C => iSup_le fun hCle => iSup_le fun hC1 => iSup_le fun hch =>
      le_inf inf_le_left (hno C hCle hC1 hch))
  obtain ⟨C, hCle, hC1, hCchar, hnle⟩ := key
  obtain ⟨n, hn, hnG⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hmemN : ∀ t ∈ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G),
      t ∈ Subgroup.normalizer (C : Set G) := fun t ht =>
    mem_normalizer_of_characteristic_subgroupOf hCchar hCle ht
  have hTIJ : T ⊓ I ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    hmemN t (Subgroup.le_normalizer ht)
  obtain ⟨x, hxT, hxn, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hT2 (S.tI_lt hI.1)
  have hxJ : x ∈ Subgroup.normalizer (C : Set G) := hmemN x hxN
  by_cases hJM : Subgroup.normalizer (C : Set G) ≤ M
  · exact h3 G T M H u S hH hu I hI fun hle => hnG (hle ⟨hn.1, hJM hn.2⟩)
  · exfalso
    have hCJ : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (hT2.to_le (hCle.trans inf_le_left))
    have hTu : tU T u ≤ T ⊓ I := le_inf inf_le_left hI.1.1.1
    have hJ : IsI T M u (Subgroup.normalizer (C : Set G)) :=
      ⟨⟨hTu.trans hTIJ, fun hbot => hC1 (le_bot_iff.mp (hCJ.trans hbot.le))⟩,
        fun h => hnG (h hn.2), hJM⟩
    have heq := (hI.of_le_inf hJ hTIJ).2
    exact hxn (heq ▸ (⟨hxT, hxJ⟩ : x ∈ T ⊓ Subgroup.normalizer (C : Set G)))

theorem stage1466_five_of (h3 : Stage1466Three) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) :
    ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
      IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIMin T M u I →
        IsUniqueMaxOver I (T ⊓ I) (I ⊓ mcOf T) ∨
          (yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) ∧
            yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) := by
  intro G _ _ T M H u S hH hu I hI
  by_cases h3c : I ⊓ M ≤ mcOf T
  · left
    have hsyl := (isIStar_sylow_cases S hu (h1 G T M S H hH u hu).2.1 (h2 G T M S H hH u hu)
      (h4 G T M S H hH u hu).1 hI.1).1
    have hprop : ∀ K : Subgroup G, T ⊓ I ≤ K → K < I → K ≤ mcOf T := by
      intro K hTK hKI
      by_contra hKG
      have hKM : ¬ K ≤ M := fun hKM => hKG ((le_inf hKI.le hKM).trans h3c)
      have hQK : pCoreOf 2 I ≤ pCoreOf 2 K :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsyl).trans hTK)
          (hKI.le.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
      have hTu : tU T u ≤ T ⊓ I := le_inf inf_le_left hI.1.1.1.1
      have hK : IsI T M u K :=
        ⟨⟨hTu.trans hTK, fun hbot => hI.1.1.1.2 (le_bot_iff.mp (hQK.trans hbot.le))⟩, hKG, hKM⟩
      exact hKI.ne (hI.2 K (hI.1.of_le_inf hK hTK).1 hKI.le)
    have hz_lt : I ⊓ mcOf T < I :=
      lt_of_le_of_ne inf_le_left fun h => hI.1.1.2.1 (inf_eq_left.mp h)
    have hTz : T ⊓ I ≤ I ⊓ mcOf T :=
      le_inf inf_le_right (inf_le_left.trans (le_centralizer_quasithinOmegaOneCenter T))
    refine Set.ext fun N => ⟨?_, ?_⟩
    · rintro ⟨⟨hNI, hNmax⟩, hTN⟩
      have hNz : N ≤ I ⊓ mcOf T := le_inf hNI.le (hprop N hTN hNI)
      rcases hNz.lt_or_eq with h | h
      · exact absurd (hNmax _ h inf_le_left) hz_lt.ne
      · exact h
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      refine ⟨⟨hz_lt, fun K hK hKI => ?_⟩, hTz⟩
      by_contra hKne
      exact hK.not_ge (le_inf hKI (hprop K (hTz.trans hK.le) (lt_of_le_of_ne hKI hKne)))
  · exact Or.inr (h3 G T M H u S hH hu I hI.1 h3c)

omit [Finite G] in
theorem tI_not_normal {u : G} {I : Subgroup G} (hI : IsIStar T M u I)
    (hcases : T ⊓ I = tU T u ∨ T ⊓ I = tZero T u)
    (hN0 : Subgroup.normalizer (tZero T u : Set G) = T)
    (hNu : Subgroup.normalizer (tU T u : Set G) = tZero T u) :
    ¬ I ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
  intro hN
  have hT0 : tZero T u ≤ mcOf T :=
    (centralizerMod_le_left _ _ _).trans (le_centralizer_quasithinOmegaOneCenter T)
  apply hI.1.2.1
  rcases hcases with e | e
  · rw [e] at hN
    exact (hN.trans hNu.le).trans hT0
  · rw [e] at hN
    exact (hN.trans hN0.le).trans (le_centralizer_quasithinOmegaOneCenter T)

end CFSG.Quasithin
