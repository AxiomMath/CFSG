module

public import CFSG.Quasithin.Background.RonanH164Vocab
public import CFSG.Quasithin.Background.RonanH163Tiso

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

variable {V V' : Type*} [CommGroup V] [CommGroup V']

theorem commV_map (e : V ≃* V') (G : Subgroup (MulAut V)) :
    commV (G.map (cH e)) = (commV G).map e.toMonoidHom := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, v', rfl⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, rfl⟩ := e.surjective v'
    refine ⟨g v * v⁻¹, ⟨g, hg, v, rfl⟩, ?_⟩
    rw [cH_apply]
    show e (g v * v⁻¹) = e (g v) * (e v)⁻¹
    rw [map_mul, map_inv]
  · rintro ⟨w, ⟨g, hg, v, rfl⟩, rfl⟩
    refine ⟨cH e g, Subgroup.mem_map_of_mem (cH e) hg, e v, ?_⟩
    rw [cH_apply]
    show e (g v) * (e v)⁻¹ = e (g v * v⁻¹)
    rw [map_mul, map_inv]

theorem fullTranspCenter_map (e : V ≃* V') (G X : Subgroup (MulAut V)) (A V₁ : Subgroup V) :
    FullTranspCenter (G.map (cH e)) (X.map (cH e)) (A.map e.toMonoidHom) (V₁.map e.toMonoidHom) ↔
      FullTranspCenter G X A V₁ := by
  have c1 : (∀ g ∈ X.map (cH e), ∀ x ∈ A.map e.toMonoidHom, g x * x⁻¹ ∈ V₁.map e.toMonoidHom) ↔
      (∀ g ∈ X, ∀ x ∈ A, g x * x⁻¹ ∈ V₁) := by
    constructor
    · intro h g hg x hx
      have h1 := h (cH e g) (Subgroup.mem_map_of_mem (cH e) hg) (e x)
        ((mem_map_e_iff e A x).mpr hx)
      rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff] at h1
      exact h1
    · intro h g' hg' x' hx'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨x, rfl⟩ := e.surjective x'
      rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff]
      exact h g hg x ((mem_map_e_iff e A x).mp hx')
  have c2 : (∀ τ' : MulAut ↥(A.map e.toMonoidHom),
      (∀ x' : ↥(A.map e.toMonoidHom),
        ((τ' x' : ↥(A.map e.toMonoidHom)) : V') * ((x' : ↥(A.map e.toMonoidHom)) : V')⁻¹ ∈
          V₁.map e.toMonoidHom) →
        ∃ g ∈ X.map (cH e), ∀ x' : ↥(A.map e.toMonoidHom),
          g (x' : V') = ((τ' x' : ↥(A.map e.toMonoidHom)) : V')) ↔
      (∀ τ : MulAut ↥A, (∀ x : ↥A, ((τ x : ↥A) : V) * ((x : ↥A) : V)⁻¹ ∈ V₁) →
        ∃ g ∈ X, ∀ x : ↥A, g (x : V) = ((τ x : ↥A) : V)) := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥A ≃* ↥(A.map e.toMonoidHom), ∀ x : ↥A,
        ((ψ x : ↥(A.map e.toMonoidHom)) : V') = e (x : V) :=
      ⟨A.equivMapOfInjective e.toMonoidHom (e_toMonoidHom_injective e),
        fun x => Subgroup.coe_equivMapOfInjective_apply A e.toMonoidHom
          (e_toMonoidHom_injective e) x⟩
    have hψsymm : ∀ y : ↥(A.map e.toMonoidHom), e ((ψ.symm y : ↥A) : V) = (y : V') := by
      intro y
      rw [← hψ (ψ.symm y), MulEquiv.apply_symm_apply]
    constructor
    · intro h τ hτ
      have hτ' : ∀ x' : ↥(A.map e.toMonoidHom),
          (((ψ.symm.trans (MulEquiv.trans τ ψ)) x' : ↥(A.map e.toMonoidHom)) : V') *
            ((x' : ↥(A.map e.toMonoidHom)) : V')⁻¹ ∈ V₁.map e.toMonoidHom := by
        intro x'
        obtain ⟨x, rfl⟩ := ψ.surjective x'
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hψ, hψ,
          ← map_inv e, ← map_mul e, mem_map_e_iff]
        exact hτ x
      obtain ⟨g, hg, hgx⟩ := h (ψ.symm.trans (MulEquiv.trans τ ψ)) hτ'
      obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
      refine ⟨g₀, hg₀, fun x => ?_⟩
      have h1 := hgx (ψ x)
      rw [hψ, cH_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        hψ] at h1
      exact e.injective h1
    · intro h τ' hτ'
      have hτx : ∀ x : ↥A, e (((ψ.trans (MulEquiv.trans τ' ψ.symm)) x : ↥A) : V) =
          ((τ' (ψ x) : ↥(A.map e.toMonoidHom)) : V') := by
        intro x
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψsymm]
      have hτ : ∀ x : ↥A, (((ψ.trans (MulEquiv.trans τ' ψ.symm)) x : ↥A) : V) *
          ((x : ↥A) : V)⁻¹ ∈ V₁ := by
        intro x
        refine (mem_map_e_iff e V₁ _).mp ?_
        rw [map_mul, map_inv, hτx x, ← hψ x]
        exact hτ' (ψ x)
      obtain ⟨g, hg, hgx⟩ := h (ψ.trans (MulEquiv.trans τ' ψ.symm)) hτ
      refine ⟨cH e g, Subgroup.mem_map_of_mem (cH e) hg, fun x' => ?_⟩
      obtain ⟨x, rfl⟩ := ψ.surjective x'
      rw [hψ, cH_apply, hgx x]
      exact hτx x
  have c3 : (∀ g ∈ X.map (cH e), (∀ x ∈ A.map e.toMonoidHom, g x = x) → g = 1) ↔
      (∀ g ∈ X, (∀ x ∈ A, g x = x) → g = 1) := by
    constructor
    · intro h g hg hfix
      have h1 : cH e g = 1 := by
        apply h (cH e g) (Subgroup.mem_map_of_mem (cH e) hg)
        intro x' hx'
        obtain ⟨x, rfl⟩ := e.surjective x'
        rw [cH_apply, hfix x ((mem_map_e_iff e A x).mp hx')]
      exact cH_injective e (h1.trans (map_one (cH e)).symm)
    · intro h g' hg' hfix
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      have h1 : g = 1 := by
        apply h g hg
        intro x hx
        apply e.injective
        have h2 := hfix (e x) ((mem_map_e_iff e A x).mpr hx)
        rw [cH_apply] at h2
        exact h2
      rw [h1, map_one]
  have c4 : (∀ y ∈ G.map (cH e), ∀ z ∈ X.map (cH e), y * z * y⁻¹ ∈ X.map (cH e)) ↔
      (∀ y ∈ G, ∀ z ∈ X, y * z * y⁻¹ ∈ X) := by
    constructor
    · intro hc a ha g hg
      obtain ⟨g', hg', hg'eq⟩ := Subgroup.mem_map.mp
        (hc (cH e a) (Subgroup.mem_map_of_mem (cH e) ha) (cH e g)
          (Subgroup.mem_map_of_mem (cH e) hg))
      have h2 : cH e g' = cH e (a * g * a⁻¹) := by
        rw [cH_conj]
        exact hg'eq
      have h3 : g' = a * g * a⁻¹ := cH_injective e h2
      rw [← h3]
      exact hg'
    · intro hc y hy z hz
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← cH_conj e a g]
      exact Subgroup.mem_map_of_mem (cH e) (hc a ha g hg)
  unfold FullTranspCenter
  exact and_congr c1 (and_congr c2 (and_congr c3 c4))

section Rep

variable {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
  (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v))

include he

theorem isDualOfConj_map (G : Subgroup P24) (A B : Subgroup V) (K : Subgroup P24) :
    IsDualOfConj ρ' G (A.map e.toMonoidHom) (B.map e.toMonoidHom) K ↔ IsDualOfConj ρ G A B K := by
  have memA : ∀ x' : V', x' ∈ A.map e.toMonoidHom ↔ e.symm x' ∈ A := fun x' => by
    rw [← mem_map_e_iff e A (e.symm x'), MulEquiv.apply_symm_apply]
  have memB : ∀ x' : V', x' ∈ B.map e.toMonoidHom ↔ e.symm x' ∈ B := fun x' => by
    rw [← mem_map_e_iff e B (e.symm x'), MulEquiv.apply_symm_apply]
  have hsym : ∀ (g : ↥Γ) (x' : V'), e.symm (ρ' g x') = ρ g (e.symm x') := by
    intro g x'
    have h := he g (e.symm x')
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, MulEquiv.symm_apply_apply]
  unfold IsDualOfConj
  constructor
  · rintro ⟨pr', h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun x k => pr' (e x) k, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx k hk k' hk'
      exact h1 (e x) ((mem_map_e_iff e A x).mpr hx) k hk k' hk'
    · intro x hx x' hx' k hk
      show pr' (e (x * x')) k = pr' (e x) k + pr' (e x') k
      rw [map_mul]
      exact h2 (e x) ((mem_map_e_iff e A x).mpr hx) (e x') ((mem_map_e_iff e A x').mpr hx') k hk
    · intro x hx k hk
      exact h3 (e x) ((mem_map_e_iff e B x).mpr hx) k hk
    · intro x hx hxB
      obtain ⟨k, hk, hne⟩ := h4 (e x) ((mem_map_e_iff e A x).mpr hx)
        (fun h => hxB ((mem_map_e_iff e B x).mp h))
      exact ⟨k, hk, hne⟩
    · intro k hk hk1
      obtain ⟨x', hx', hne⟩ := h5 k hk hk1
      refine ⟨e.symm x', (memA x').mp hx', ?_⟩
      show pr' (e (e.symm x')) k ≠ 0
      rw [MulEquiv.apply_symm_apply]
      exact hne
    · intro g hg x hx k hk
      show pr' (e (ρ g x)) ((g : P24) * k * (g : P24)⁻¹) = pr' (e x) k
      rw [he]
      exact h6 g hg (e x) ((mem_map_e_iff e A x).mpr hx) k hk
  · rintro ⟨pr, h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun x' k => pr (e.symm x') k, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx k hk k' hk'
      exact h1 (e.symm x) ((memA x).mp hx) k hk k' hk'
    · intro x hx x' hx' k hk
      show pr (e.symm (x * x')) k = pr (e.symm x) k + pr (e.symm x') k
      rw [map_mul]
      exact h2 (e.symm x) ((memA x).mp hx) (e.symm x') ((memA x').mp hx') k hk
    · intro x hx k hk
      exact h3 (e.symm x) ((memB x).mp hx) k hk
    · intro x hx hxB
      obtain ⟨k, hk, hne⟩ := h4 (e.symm x) ((memA x).mp hx)
        (fun h => hxB ((memB x).mpr h))
      exact ⟨k, hk, hne⟩
    · intro k hk hk1
      obtain ⟨x, hx, hne⟩ := h5 k hk hk1
      refine ⟨e x, (mem_map_e_iff e A x).mpr hx, ?_⟩
      show pr (e.symm (e x)) k ≠ 0
      rw [MulEquiv.symm_apply_apply]
      exact hne
    · intro g hg x' hx' k hk
      show pr (e.symm (ρ' g x')) ((g : P24) * k * (g : P24)⁻¹) = pr (e.symm x') k
      rw [hsym]
      exact h6 g hg (e.symm x') ((memA x').mp hx') k hk

theorem chain163_map (Q : Finset (Finset (Fin 24))) (V₈ V₉ : Subgroup V) :
    Chain163 ρ' Q (V₈.map e.toMonoidHom) (V₉.map e.toMonoidHom) ↔ Chain163 ρ Q V₈ V₉ := by
  have hM := rImg_map ρ ρ' e he (MY Γ Q)
  have hK := rImg_map ρ ρ' e he (KY Γ Q)
  have hF : fixV (rImg ρ' (KY Γ Q)) = (fixV (rImg ρ (KY Γ Q))).map e.toMonoidHom := by
    rw [← hK, fixV_map]
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  have L1 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Q))) ⊥ (fixV (rImg ρ' (KY Γ Q))) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) ⊥ (fixV (rImg ρ (KY Γ Q))) := by
    have h := chief_map e (rImg ρ (MY Γ Q)) ⊥ (fixV (rImg ρ (KY Γ Q)))
    rw [Subgroup.map_bot, hM, ← hF] at h
    exact h
  have R1 : rk ↥(fixV (rImg ρ' (KY Γ Q))) = rk ↥(fixV (rImg ρ (KY Γ Q))) := by
    rw [hF, rk_map]
  have L3 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Q))) (fixV (rImg ρ' (KY Γ Q)))
      (V₈.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) (fixV (rImg ρ (KY Γ Q))) V₈ := by
    have h := chief_map e (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q))) V₈
    rw [hM, ← hF] at h
    exact h
  have R3 : rk ↥(V₈.map e.toMonoidHom) = rk ↥V₈ := rk_map e V₈
  have L5 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Q))) (V₈.map e.toMonoidHom)
      (V₉.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₈ V₉ := by
    have h := chief_map e (rImg ρ (MY Γ Q)) V₈ V₉
    rw [hM] at h
    exact h
  have R5 : rk ↥(V₉.map e.toMonoidHom) = rk ↥V₉ := rk_map e V₉
  have L7 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Q))) (V₉.map e.toMonoidHom) ⊤ ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₉ ⊤ := by
    have h := chief_map e (rImg ρ (MY Γ Q)) V₉ ⊤
    rw [hM, hT] at h
    exact h
  unfold Chain163
  rw [L1, R1, L3, R3, L5, R5, L7]

theorem chain164_map (Hx : Finset (Fin 24)) (V₅ V₆ : Subgroup V) :
    Chain164 ρ' Hx (V₅.map e.toMonoidHom) (V₆.map e.toMonoidHom) ↔ Chain164 ρ Hx V₅ V₆ := by
  have hM := rImg_map ρ ρ' e he (MY Γ Hx)
  have hK := rImg_map ρ ρ' e he (KY Γ Hx)
  have hF : fixV (rImg ρ' (KY Γ Hx)) = (fixV (rImg ρ (KY Γ Hx))).map e.toMonoidHom := by
    rw [← hK, fixV_map]
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  have L1 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Hx))) ⊥ (fixV (rImg ρ' (KY Γ Hx))) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) ⊥ (fixV (rImg ρ (KY Γ Hx))) := by
    have h := chief_map e (rImg ρ (MY Γ Hx)) ⊥ (fixV (rImg ρ (KY Γ Hx)))
    rw [Subgroup.map_bot, hM, ← hF] at h
    exact h
  have R1 : rk ↥(fixV (rImg ρ' (KY Γ Hx))) = rk ↥(fixV (rImg ρ (KY Γ Hx))) := by
    rw [hF, rk_map]
  have L3 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Hx))) (fixV (rImg ρ' (KY Γ Hx)))
      (V₅.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) (fixV (rImg ρ (KY Γ Hx))) V₅ := by
    have h := chief_map e (rImg ρ (MY Γ Hx)) (fixV (rImg ρ (KY Γ Hx))) V₅
    rw [hM, ← hF] at h
    exact h
  have R3 : rk ↥(V₅.map e.toMonoidHom) = rk ↥V₅ := rk_map e V₅
  have L5 : V₅.map e.toMonoidHom = commV (rImg ρ' (KY Γ Hx)) ↔
      V₅ = commV (rImg ρ (KY Γ Hx)) := by
    rw [← hK, commV_map]
    exact ⟨fun h => Subgroup.map_injective (e_toMonoidHom_injective e) h, fun h => by rw [h]⟩
  have L6 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Hx))) (V₅.map e.toMonoidHom)
      (V₆.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₅ V₆ := by
    have h := chief_map e (rImg ρ (MY Γ Hx)) V₅ V₆
    rw [hM] at h
    exact h
  have R6 : rk ↥(V₆.map e.toMonoidHom) = rk ↥V₆ := rk_map e V₆
  have L8 : IsChiefFactorUnder (actsOnModule (rImg ρ' (MY Γ Hx))) (V₆.map e.toMonoidHom) ⊤ ↔
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₆ ⊤ := by
    have h := chief_map e (rImg ρ (MY Γ Hx)) V₆ ⊤
    rw [hM, hT] at h
    exact h
  unfold Chain164
  rw [L1, R1, L3, R3, L5, L6, R6, L8]

theorem Concl164_map (Hx : Finset (Fin 24)) (Q : Finset (Finset (Fin 24))) :
    Concl164 ρ Hx Q → Concl164 ρ' Hx Q := by
  rintro ⟨V₅, V₆, h1, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩, h4, h5⟩
  have hM := rImg_map ρ ρ' e he (MY Γ Hx)
  have hK := rImg_map ρ ρ' e he (KY Γ Hx)
  have hF : fixV (rImg ρ' (KY Γ Hx)) = (fixV (rImg ρ (KY Γ Hx))).map e.toMonoidHom := by
    rw [← hK, fixV_map]
  have hKQ := rImg_map ρ ρ' e he (KY Γ Q)
  have hFQ : fixV (rImg ρ' (KY Γ Q)) = (fixV (rImg ρ (KY Γ Q))).map e.toMonoidHom := by
    rw [← hKQ, fixV_map]
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  refine ⟨V₅.map e.toMonoidHom, V₆.map e.toMonoidHom,
    (chain164_map ρ ρ' e he Hx V₅ V₆).mpr h1, ?_, ?_, ?_, ?_⟩
  · constructor
    · have h := (fullTranspCenter_map e (rImg ρ (MY Γ Hx)) (rImg ρ (KY Γ Hx)) V₅
        (fixV (rImg ρ (KY Γ Hx)))).mpr h2a
      rw [hM, hK, ← hF] at h
      exact h
    · have h := (isDualOfConj_map ρ ρ' e he (MY Γ Hx) V₅ (fixV (rImg ρ (KY Γ Hx)))
        (KY Γ Hx)).mpr h2b
      rw [← hF] at h
      exact h
  · refine ⟨h3a, ?_⟩
    have h := (inducesOnSub_map e (rImg ρ (MY Γ Hx)) ⊤ V₅ (G6.coreMod 6)
      (G6.permAct 6).range).mpr h3b
    rw [hM, hT] at h
    exact h
  · obtain ⟨⟨V₈, V₉, h4a, h4b, h4c⟩, h4d⟩ := h4
    constructor
    · refine ⟨V₈.map e.toMonoidHom, V₉.map e.toMonoidHom,
        (chain163_map ρ ρ' e he Q V₈ V₉).mpr h4a, ?_, ?_⟩
      · exact (Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mpr h4b
      · intro hle
        apply h4c
        rw [hFQ] at hle
        exact (Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mp hle
    · intro V₈' V₉' hc
      obtain ⟨V₈, rfl⟩ : ∃ W : Subgroup V, W.map e.toMonoidHom = V₈' :=
        ⟨V₈'.comap e.toMonoidHom,
          Subgroup.map_comap_eq_self_of_surjective (e_toMonoidHom_surjective e) V₈'⟩
      obtain ⟨V₉, rfl⟩ : ∃ W : Subgroup V, W.map e.toMonoidHom = V₉' :=
        ⟨V₉'.comap e.toMonoidHom,
          Subgroup.map_comap_eq_self_of_surjective (e_toMonoidHom_surjective e) V₉'⟩
      obtain ⟨hA, hB⟩ := h4d V₈ V₉ ((chain163_map ρ ρ' e he Q V₈ V₉).mp hc)
      refine ⟨(Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mpr hA, ?_⟩
      intro hle
      apply hB
      rw [hFQ] at hle
      exact (Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mp hle
  · intro x'
    obtain ⟨y, rfl⟩ := e.surjective x'
    rw [mem_map_e_iff, h5 y, hF, ← hK]
    constructor
    · intro h g' hg'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      rw [cH_apply, ← map_inv e y, ← map_mul e, mem_map_e_iff]
      exact h g hg
    · intro h g hg
      have h1' := h (cH e g) (Subgroup.mem_map_of_mem (cH e) hg)
      rw [cH_apply, ← map_inv e y, ← map_mul e, mem_map_e_iff] at h1'
      exact h1'

end Rep

theorem Concl164_iff_of_iso {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V')
    (e : V ≃* V') (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v))
    (Hx : Finset (Fin 24)) (Q : Finset (Finset (Fin 24))) : Concl164 ρ Hx Q ↔ Concl164 ρ' Hx Q := by
  refine ⟨Concl164_map ρ ρ' e he Hx Q, Concl164_map ρ' ρ e.symm ?_ Hx Q⟩
  intro g v'
  have := he g (e.symm v')
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.RonanH163
