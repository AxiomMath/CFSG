module

public import CFSG.Quasithin.Background.RonanH155Vocab
public import CFSG.Quasithin.Background.RonanH154Tconj
public import CFSG.Quasithin.Background.RonanH143NF

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.H.Mathieu

theorem h155_conjSubg_centralizer (c i : P24) :
    conjSubg c (Subgroup.centralizer ({i} : Set P24)) =
      Subgroup.centralizer ({c * i * c⁻¹} : Set P24) := by
  ext x
  rw [mem_conjSubg_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc c * i * c⁻¹ * x = c * (i * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * x * c * i) * c⁻¹ := by rw [h]
      _ = x * (c * i * c⁻¹) := by group
  · intro h
    calc i * (c⁻¹ * x * c) = c⁻¹ * (c * i * c⁻¹ * x) * c := by group
      _ = c⁻¹ * (x * (c * i * c⁻¹)) * c := by rw [h]
      _ = c⁻¹ * x * c * i := by group

theorem h155_conjSubg_inf_centralizer (c i : P24) (Γ : Subgroup P24) :
    conjSubg c (Γ ⊓ Subgroup.centralizer ({i} : Set P24)) =
      conjSubg c Γ ⊓ Subgroup.centralizer ({c * i * c⁻¹} : Set P24) := by
  rw [conjSubg_inf, h155_conjSubg_centralizer]

theorem h155_mem_fixedSetR_iff (z : P24) (x : Fin 24) : x ∈ fixedSetR z ↔ z x = x := by
  simp [fixedSetR]

theorem h155_fixedSetR_conj (c i : P24) :
    fixedSetR i = c⁻¹ • fixedSetR (c * i * c⁻¹) := by
  rw [CFSG.Quasithin.RonanH143.smul_finset_eq_map]
  ext x
  rw [h155_mem_fixedSetR_iff, Finset.mem_map_equiv, h155_mem_fixedSetR_iff]
  show i x = x ↔ (c * i * c⁻¹) (c x) = c x
  have hcx : c⁻¹ (c x) = x := by simp
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcx]
  exact c.injective.eq_iff.symm

theorem h155_mem_smul_inv_iff (c : P24) (x : Fin 24) (T : Finset (Fin 24)) :
    x ∈ c⁻¹ • T ↔ c x ∈ T := by
  rw [CFSG.Quasithin.RonanH143.smul_finset_eq_map, Finset.mem_map_equiv]
  rfl

theorem h155_isOct_smul_inv {c : P24} (hc : c ∈ AutPerm) {O : Finset (Fin 24)} (hO : IsOctR O) :
    IsOctR (c⁻¹ • O) := by
  rw [CFSG.Quasithin.RonanH143.smul_finset_eq_map]
  exact (CFSG.Quasithin.RonanH143.isOct_map_iff (inv_mem hc) O).2 hO

theorem h155_conj_mem (c i : P24) (Γ : Subgroup P24) {x : P24}
    (hx : x ∈ Γ ⊓ Subgroup.centralizer ({i} : Set P24)) :
    c * x * c⁻¹ ∈ conjSubg c Γ ⊓ Subgroup.centralizer ({c * i * c⁻¹} : Set P24) := by
  have h0 : c * x * c⁻¹ ∈ conjSubg c (Γ ⊓ Subgroup.centralizer ({i} : Set P24)) :=
    h164w_mem_conj hx
  rwa [h155_conjSubg_inf_centralizer] at h0

@[expose] def h155ConjHom (c i : P24) (Γ : Subgroup P24) :
    ↥(Γ ⊓ Subgroup.centralizer ({i} : Set P24)) →*
      ↥(conjSubg c Γ ⊓ Subgroup.centralizer ({c * i * c⁻¹} : Set P24)) where
  toFun x := ⟨c * (x : P24) * c⁻¹, h155_conj_mem c i Γ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem h155ConjHom_surjective (c i : P24) (Γ : Subgroup P24) :
    Function.Surjective (h155ConjHom c i Γ) := by
  intro y
  have hy : (y : P24) ∈ conjSubg c (Γ ⊓ Subgroup.centralizer ({i} : Set P24)) := by
    rw [h155_conjSubg_inf_centralizer]
    exact y.2
  refine ⟨⟨c⁻¹ * (y : P24) * c, mem_conjSubg_iff.1 hy⟩, ?_⟩
  apply Subtype.ext
  show c * (c⁻¹ * (y : P24) * c) * c⁻¹ = (y : P24)
  group

theorem Alt3Struct_conj {Γ Γ' A : Subgroup P24} (c : P24) (hc : c ∈ AutPerm)
    (hΓ : conjSubg c Γ = Γ') (a b : Fin 24) :
    Alt3Struct Γ' (conjSubg c A) (c a) (c b) → Alt3Struct Γ A a b := by
  subst hΓ
  unfold Alt3Struct
  rintro ⟨i', hi'A, hi'M, ⟨O'', hO'', hnO'', hfix''⟩, hAeq, π', hπ'surj, hπ'ker⟩
  obtain ⟨i, rfl⟩ : ∃ i : P24, i' = c * i * c⁻¹ := ⟨c⁻¹ * i' * c, by group⟩
  have hiA : i ∈ A := by
    have h0 := h164w_mem_conj_inv hi'A
    rwa [show c⁻¹ * (c * i * c⁻¹) * c = i by group] at h0
  have hiM : i ∉ M22g a b := by
    intro hi
    apply hi'M
    have h0 := h164w_mem_conj (c := c) hi
    rwa [M22g_conj hc a b] at h0
  refine ⟨i, hiA, hiM, ⟨c⁻¹ • O'', h155_isOct_smul_inv hc hO'', ?_, ?_⟩, ?_,
    π'.comp (h155ConjHom c i Γ), ?_, ?_⟩
  · rw [h155_mem_smul_inv_iff, h155_mem_smul_inv_iff]
    exact hnO''
  · rw [← hfix'']
    exact h155_fixedSetR_conj c i
  · refine (conjSubg_inj (c := c)).1 ?_
    rw [hAeq, ← pCoreOf_conjSubg, h155_conjSubg_inf_centralizer]
  · intro g
    obtain ⟨y, hy⟩ := hπ'surj g
    obtain ⟨x, rfl⟩ := h155ConjHom_surjective c i Γ y
    exact ⟨x, hy⟩
  · ext x
    have key : π' (h155ConjHom c i Γ x) = 1 ↔ (x : P24) ∈ A := by
      rw [← MonoidHom.mem_ker, hπ'ker, Subgroup.mem_subgroupOf, mem_conjSubg_iff]
      show c⁻¹ * (c * (x : P24) * c⁻¹) * c ∈ A ↔ (x : P24) ∈ A
      rw [show c⁻¹ * (c * (x : P24) * c⁻¹) * c = (x : P24) by group]
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact key

theorem h155_rk_conjSubg (c : P24) (Y : Subgroup P24) :
    CFSG.Quasithin.rk ↥(conjSubg c Y) = CFSG.Quasithin.rk ↥Y := by
  unfold CFSG.Quasithin.rk
  rw [card_conjSubg]

theorem Concl155_comp {V : Type*} [CommGroup V] {Γ Γ' : Subgroup P24} (c : P24)
    (hc : c ∈ AutPerm) (hΓ : conjSubg c Γ = Γ') (ρ' : ↥Γ' →* MulAut V) (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (a b : Fin 24)
    (O : Finset (Fin 24)) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup P24) :
    Concl155 ρ' (c a) (c b) (c • O) (c • S) (c • B) (conjSubg c T₀) →
      Concl155 (ρ'.comp φ) a b O S B T₀ := by
  intro h
  unfold Concl155 at h ⊢
  intro A hA hE
  have hA' : conjSubg c A ≤ conjSubg c T₀ ⊓ Γ' := by
    have h0 := (conjSubg_le_conjSubg_iff (c := c)).2 hA
    rwa [conjSubg_inf, hΓ] at h0
  have hE' : IsE2k 4 (conjSubg c A) := (IsE2k_conjSubg_iff c 4 A).2 hE
  have h' := h (conjSubg c A) hA' hE'
  have hO : ((c • O).erase (c a)).erase (c b) = c • ((O.erase a).erase b) := by
    rw [smul_erase_finset, smul_erase_finset]
  rw [hO, ← smul_erase_finset_finset, h164w_KY_comp hΓ ((O.erase a).erase b),
    h164w_KY_comp hΓ (S.erase B)] at h'
  rw [rImg_comp c hΓ ρ' φ hφ A]
  rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨conjSubg_inj.1 h1, h2, h3⟩
  · obtain ⟨g', hg', hle⟩ := h1
    have hg : c⁻¹ * g' * c ∈ Γ := by
      rw [← hΓ] at hg'
      exact mem_conjSubg_iff.1 hg'
    refine Or.inr (Or.inl ⟨⟨c⁻¹ * g' * c, hg, ?_⟩, h2, h3⟩)
    refine (conjSubg_le_conjSubg_iff (c := c)).1 ?_
    have key : conjSubg c (conjSubg (c⁻¹ * g' * c) A) = conjSubg g' (conjSubg c A) := by
      rw [← conjSubg_mul c (c⁻¹ * g' * c) A, show c * (c⁻¹ * g' * c) = g' * c by group,
        conjSubg_mul g' c A]
    rw [key]
    exact hle
  · exact Or.inr (Or.inr (Or.inl ⟨Alt3Struct_conj c hc hΓ a b h1, h2, h3⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨?_, h2, h3⟩))
    rw [← conjSubg_inf, h155_rk_conjSubg] at h1
    exact h1

theorem h155_map_e_eq_top_iff {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (X : Subgroup V) : X.map e.toMonoidHom = ⊤ ↔ X = ⊤ := by
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  rw [← hT]
  exact (Subgroup.map_injective (e_toMonoidHom_injective e)).eq_iff

theorem h155_rkIdx_map {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (U : Subgroup V) :
    CFSG.Quasithin.rkIdx (U.map e.toMonoidHom) = CFSG.Quasithin.rkIdx U := by
  unfold CFSG.Quasithin.rkIdx
  exact congrArg (padicValNat 2) (Subgroup.index_map_equiv U e)

theorem Concl155_map {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ : Subgroup P24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v)) (a b : Fin 24)
    (O : Finset (Fin 24)) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup P24) :
    Concl155 ρ a b O S B T₀ → Concl155 ρ' a b O S B T₀ := by
  intro h
  unfold Concl155 at h ⊢
  intro A hA hE
  have h' := h A hA hE
  rw [← rImg_map ρ ρ' e he A, fixV_map, CFSG.Quasithin.RonanH154.xiV_map]
  simpa only [rk_map, h155_rkIdx_map, h155_map_e_eq_top_iff] using h'

theorem Concl155_iff_of_iso {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ : Subgroup P24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v)) (a b : Fin 24)
    (O : Finset (Fin 24)) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup P24) :
    Concl155 ρ a b O S B T₀ ↔ Concl155 ρ' a b O S B T₀ := by
  refine ⟨Concl155_map ρ ρ' e he a b O S B T₀, Concl155_map ρ' ρ e.symm ?_ a b O S B T₀⟩
  intro g v'
  have h := he g (e.symm v')
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, MulEquiv.symm_apply_apply]

theorem Concl155_of_transport {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ Γ' : Subgroup P24}
    (c : P24) (hc : c ∈ AutPerm) (hΓ : conjSubg c Γ = Γ')
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (a b : Fin 24)
    (O : Finset (Fin 24)) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24)) (T₀ : Subgroup P24) :
    Concl155 ρ' (c a) (c b) (c • O) (c • S) (c • B) (conjSubg c T₀) → Concl155 ρ a b O S B T₀ := by
  intro h
  exact (Concl155_iff_of_iso ρ (ρ'.comp φ) e he a b O S B T₀).2
    (Concl155_comp c hc hΓ ρ' φ hφ a b O S B T₀ h)

end CFSG.Quasithin.RonanH155
