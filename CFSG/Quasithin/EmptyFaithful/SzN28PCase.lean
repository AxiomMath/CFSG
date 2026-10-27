module

public import CFSG.Quasithin.EmptyFaithful.SzN28PRank
public import CFSG.Quasithin.EmptyFaithful.SzN28PLift
public import CFSG.Quasithin.EmptyFaithful.S142Bridge
public import CFSG.Quasithin.EmptyFaithful.S143VSq
public import CFSG.Quasithin.EmptyFaithful.S143WCl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN28P

section Card

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem card_subgroupOf_eq {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (hXΓ : X ≤ Γ) :
    Nat.card (X.subgroupOf Γ) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv

omit [Finite V] in
theorem subgroupOf_elemAbelian {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    (∀ x ∈ X.subgroupOf Γ, x * x = 1) ∧
      (∀ x ∈ X.subgroupOf Γ, ∀ y ∈ X.subgroupOf Γ, x * y = y * x) :=
  ⟨fun _ hx => Subtype.ext (hX2 _ hx), fun _ hx _ hy => Subtype.ext (hXc _ hx _ hy)⟩

theorem card_le_eight_of_concl9 {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl9 Γ)
    (hXΓ : X ≤ Γ) (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 8 := by
  obtain ⟨hY2, hYc⟩ := subgroupOf_elemAbelian (Γ := Γ) hX2 hXc
  rw [← card_subgroupOf_eq hXΓ]
  obtain ⟨-, h9⟩ := h
  rcases h9 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact card_le_eight_of_S3S5 e hY2 hYc
  · exact card_le_eight_of_S3A5 e hY2

theorem card_le_eight_of_concl10 {Γ X X' : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl10 Γ X')
    (hXΓ : X ≤ Γ) (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 8 := by
  obtain ⟨hY2, hYc⟩ := subgroupOf_elemAbelian (Γ := Γ) hX2 hXc
  rw [← card_subgroupOf_eq hXΓ]
  obtain ⟨-, hcard, ⟨e⟩, -⟩ := h
  exact card_le_eight_of_A6 hcard _ e hY2 hYc

omit [Finite V] in
theorem exists_normal_three_of_mulEquiv {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {Y : Type} [Group Y]
    (e : ↥Γ ≃* Equiv.Perm (Fin 3) × Y) :
    ∃ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧
      Nat.card N = 3 := by
  let N₀ : Subgroup (Equiv.Perm (Fin 3) × Y) :=
    (alternatingGroup (Fin 3)).map (MonoidHom.inl _ _)
  let N' : Subgroup ↥Γ := N₀.map e.symm.toMonoidHom
  refine ⟨N'.map Γ.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro γ hγ _ ⟨n', hn', rfl⟩
    refine ⟨(⟨γ, hγ⟩ : ↥Γ) * n' * (⟨γ, hγ⟩ : ↥Γ)⁻¹, ?_, rfl⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hn'
    refine ⟨e (⟨γ, hγ⟩ : ↥Γ) * (MonoidHom.inl _ _ a) * (e (⟨γ, hγ⟩ : ↥Γ))⁻¹, ?_, ?_⟩
    · obtain ⟨b, y⟩ := e (⟨γ, hγ⟩ : ↥Γ)
      refine ⟨b * a * b⁻¹, ?_, ?_⟩
      · exact (alternatingGroup.normal : (alternatingGroup (Fin 3)).Normal).conj_mem a ha b
      · simp [MonoidHom.inl]
    · simp
  · rw [Subgroup.card_map_of_injective Γ.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      Subgroup.card_map_of_injective (f := MonoidHom.inl (Equiv.Perm (Fin 3)) Y) (fun a b hab => by
        simpa [MonoidHom.inl] using congrArg Prod.fst hab),
      Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]

omit [Finite V] in
theorem exists_normal_three_of_concl9 {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl9 Γ) :
    ∃ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧
      Nat.card N = 3 := by
  obtain ⟨-, h9⟩ := h
  rcases h9 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact exists_normal_three_of_mulEquiv e
  · exact exists_normal_three_of_mulEquiv e

omit [Finite V] in
theorem exists_normal_three_of_concl10 {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl10 Γ X) :
    ∃ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧
      Nat.card N = 3 := by
  obtain ⟨-, -, -, hc, -⟩ := h
  refine ⟨(CFSG.pCore 3 ↥Γ).map Γ.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro γ hγ _ ⟨n', hn', rfl⟩
    exact ⟨(⟨γ, hγ⟩ : ↥Γ) * n' * (⟨γ, hγ⟩ : ↥Γ)⁻¹,
      (CFSG.pCore_normal (G := ↥Γ) (p := 3)).conj_mem n' hn' ⟨γ, hγ⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective Γ.subtype_injective]
    exact hc

end Card

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}




section Excl

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem not_concl9 (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) : ¬ G112Concl9 (D.img (mcOf T)) := by
  intro hc
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h1281.exists_goodElt_L
  have h101 := (h1281.lemma_12_8_12_three hU hg D haV haZ).toG101Hyp
  have hd : Module.finrank (ZMod 2) D.V = 8 := hc.1
  have hX8 := card_le_eight_of_concl9 hc h101.X_le h101.X_sq h101.X_comm
  have hbot : D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := h101.exists_card_X
    have hrank := S143W.rank_le_of_ne_bot h101 hne hk
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    omega
  have hZU := zu_eq_v1_of_img_rconj_bot h1281 hU hg D hbot
  have hker := S143V.centralizerHat_le_T h1281 hZU
  obtain ⟨N, hNΓ, hNn, hN⟩ := exists_normal_three_of_concl9 hc
  have h35' : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M :=
    fun K hK hidx => h35 G T M hyp hnot K hK hidx
  exact S143V.no_normal_three_five h1281 hU hg D haV haZ h35' hker hNΓ hNn (Or.inl hN)

theorem not_concl10 (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) (X' : Subgroup (D.V ≃ₗ[ZMod 2] D.V)) :
    ¬ G112Concl10 (D.img (mcOf T)) X' := by
  intro hc
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h1281.exists_goodElt_L
  have h101 := (h1281.lemma_12_8_12_three hU hg D haV haZ).toG101Hyp
  have hd : Module.finrank (ZMod 2) D.V = 8 := hc.1
  have hX8 := card_le_eight_of_concl10 hc h101.X_le h101.X_sq h101.X_comm
  have hbot : D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := h101.exists_card_X
    have hrank := S143W.rank_le_of_ne_bot h101 hne hk
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    omega
  have hZU := zu_eq_v1_of_img_rconj_bot h1281 hU hg D hbot
  have hker := S143V.centralizerHat_le_T h1281 hZU
  obtain ⟨N, hNΓ, hNn, hN⟩ := exists_normal_three_of_concl10 hc
  have h35' : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M :=
    fun K hK hidx => h35 G T M hyp hnot K hK hidx
  exact S143V.no_normal_three_five h1281 hU hg D haV haZ h35' hker hNΓ hNn (Or.inl hN)

end Excl

end SzN28P

end CFSG.Quasithin
