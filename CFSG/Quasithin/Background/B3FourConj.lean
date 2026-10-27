module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.B3Four3

public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {n : ℕ} {k : Mod}

theorem act_inv_act (g : Gp n) (w : Mod.V n k) : Mod.act n k g⁻¹ (Mod.act n k g w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem act_act_inv (g : Gp n) (w : Mod.V n k) : Mod.act n k g (Mod.act n k g⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

@[expose] noncomputable def gmap (g : Gp n) (W : Subgroup (Mod.V n k)) : Subgroup (Mod.V n k) :=
  W.map (Mod.act n k g).toMonoidHom

theorem mem_gmap {g : Gp n} {W : Subgroup (Mod.V n k)} {w : Mod.V n k} :
    w ∈ gmap g W ↔ Mod.act n k g⁻¹ w ∈ W := by
  unfold gmap
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : Mod.act n k g⁻¹ ((Mod.act n k g).toMonoidHom x) = x := act_inv_act g x
    rw [h]
    exact hx
  · intro h
    exact ⟨Mod.act n k g⁻¹ w, h, act_act_inv g w⟩

theorem gmap_le_iff {g : Gp n} {A B : Subgroup (Mod.V n k)} : gmap g A ≤ gmap g B ↔ A ≤ B := by
  constructor
  · intro h a ha
    have h1 : Mod.act n k g a ∈ gmap g A := mem_gmap.2 (by rw [act_inv_act]; exact ha)
    have h2 := mem_gmap.1 (h h1)
    rwa [act_inv_act] at h2
  · intro h w hw
    exact mem_gmap.2 (h (mem_gmap.1 hw))

theorem gmap_gmap_inv (g : Gp n) (W : Subgroup (Mod.V n k)) : gmap g (gmap g⁻¹ W) = W := by
  ext w
  rw [mem_gmap, mem_gmap, inv_inv, act_act_inv]

theorem card_gmap (g : Gp n) (W : Subgroup (Mod.V n k)) : Nat.card (gmap g W) = Nat.card W :=
  Subgroup.card_map_of_injective (Mod.act n k g).injective

theorem gmap_fixV {H : Subgroup (Gp n)} {g : Gp n} (hg : g ∈ H) :
    gmap g (fixV (H.map (Mod.act n k))) = fixV (H.map (Mod.act n k)) := by
  ext w
  rw [mem_gmap, mem_fixV, mem_fixV]
  constructor
  · intro h x hx
    have h1 := h (Mod.act n k g) (Subgroup.mem_map_of_mem _ hg)
    rw [act_act_inv] at h1
    have h2 := h x hx
    rw [← h1] at h2
    exact h2
  · intro h x hx
    have h1 := h (Mod.act n k g⁻¹) (Subgroup.mem_map_of_mem _ (H.inv_mem hg))
    rw [h1]
    exact h x hx

theorem act_mul3 (a b c : Gp n) (w : Mod.V n k) :
    Mod.act n k (a * b * c) w = Mod.act n k a (Mod.act n k b (Mod.act n k c w)) := by
  simp [map_mul, MulAut.mul_apply]

theorem conj_mem_cj {G : Type*} [Group G] {g t : G} {A : Subgroup G} :
    g * t * g⁻¹ ∈ cj g A ↔ t ∈ A := by
  rw [mem_cj]
  have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  rw [e]

theorem isTinv_cj_gmap {T : Subgroup (Gp n)} {W : Subgroup (Mod.V n k)} {g : Gp n} :
    IsTinv (cj g T) (gmap g W) ↔ IsTinv T W := by
  constructor
  · intro h t ht s hs
    have h1 := h (g * t * g⁻¹) (conj_mem_cj.2 ht) (Mod.act n k g s)
      (mem_gmap.2 (by rw [act_inv_act]; exact hs))
    have h2 := mem_gmap.1 h1
    rwa [act_mul3, act_inv_act, act_inv_act] at h2
  · intro h t' ht' s' hs'
    have ht : g⁻¹ * t' * g ∈ T := mem_cj.1 ht'
    have hs : Mod.act n k g⁻¹ s' ∈ W := mem_gmap.1 hs'
    have h1 := h _ ht _ hs
    refine mem_gmap.2 ?_
    have e : Mod.act n k g⁻¹ (Mod.act n k t' s') =
        Mod.act n k (g⁻¹ * t' * g) (Mod.act n k g⁻¹ s') := by
      rw [act_mul3, act_act_inv]
    rw [e]
    exact h1

@[expose] def IsFlagSpace (n : ℕ) (k : Mod) (H T : Subgroup (Gp n)) (i : ℕ)
    (W : Subgroup (Mod.V n k)) : Prop :=
  fixV (H.map (Mod.act n k)) ≤ W ∧ Nat.card W = 2 ^ i * Nat.card (fixV (H.map (Mod.act n k))) ∧
    IsTinv T W

theorem isFlagSpace_gmap {H T : Subgroup (Gp n)} {i : ℕ} {W : Subgroup (Mod.V n k)} {g : Gp n}
    (hg : g ∈ H) : IsFlagSpace n k H (cj g T) i (gmap g W) ↔ IsFlagSpace n k H T i W := by
  have hC := gmap_fixV (k := k) hg
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, isTinv_cj_gmap.1 h3⟩
    · have h1' : gmap g (fixV (H.map (Mod.act n k))) ≤ gmap g W := by rw [hC]; exact h1
      exact gmap_le_iff.1 h1'
    · rwa [card_gmap] at h2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, isTinv_cj_gmap.2 h3⟩
    · have h1' := (gmap_le_iff (g := g)).2 h1
      rwa [hC] at h1'
    · rwa [card_gmap]

theorem rAV_conjAut {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    rAV (B1.conjAut g A) = rAV A :=
  CFSG.Quasithin.RAV.rAV_conjAut g A

theorem conjAut_inj {W : Type*} [CommGroup W] (g : MulAut W) {A B : Subgroup (MulAut W)} :
    B1.conjAut g A = B1.conjAut g B ↔ A = B :=
  ⟨fun h => le_antisymm (B1.conjAut_le_iff.1 h.le) (B1.conjAut_le_iff.1 h.ge), congrArg _⟩

theorem conjAut_bot {W : Type*} [CommGroup W] (g : MulAut W) :
    B1.conjAut g (⊥ : Subgroup (MulAut W)) = ⊥ := by
  rw [conjAut_eq_map_conj, Subgroup.map_bot]

theorem conjAut_eq_bot {W : Type*} [CommGroup W] (g : MulAut W) {A : Subgroup (MulAut W)} :
    B1.conjAut g A = ⊥ ↔ A = ⊥ := by
  constructor
  · intro h
    exact (conjAut_inj g).1 (h.trans (conjAut_bot g).symm)
  · intro h
    rw [h]
    exact conjAut_bot g

theorem mem_of_conjAut_mem {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    {P : Set (Subgroup (MulAut W))} (hP : IsStableFF X P) {γ : MulAut W} (hγ : γ ∈ X)
    {A : Subgroup (MulAut W)} : B1.conjAut γ A ∈ P ↔ A ∈ P := by
  constructor
  · intro h
    have h1 := hP.2.2.1 _ h γ⁻¹ (X.inv_mem hγ)
    rwa [← conjAut_eq_map_conj, B1.conjAut_inv_conjAut] at h1
  · intro h
    rw [conjAut_eq_map_conj]
    exact hP.2.2.1 A h γ hγ

theorem isStrong_conjAut_iff {W : Type*} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {γ : MulAut W} (hγ : γ ∈ X) {A : Subgroup (MulAut W)} :
    IsStrongFFStarOffender X (B1.conjAut γ A) ↔ IsStrongFFStarOffender X A := by
  have key : ∀ δ : MulAut W, δ ∈ X → ∀ B : Subgroup (MulAut W),
      IsStrongFFStarOffender X B → IsStrongFFStarOffender X (B1.conjAut δ B) := by
    intro δ hδ B hB
    exact ⟨B1.isFFStarOffender_conjAut hB.1 hδ, by rw [rAV_conjAut]; exact hB.2⟩
  refine ⟨fun h => ?_, key γ hγ A⟩
  have h1 := key γ⁻¹ (X.inv_mem hγ) _ h
  rwa [B1.conjAut_inv_conjAut] at h1

theorem conjAut_le_iff_le_inv {W : Type*} [CommGroup W] (γ : MulAut W)
    (A B : Subgroup (MulAut W)) : B1.conjAut γ A ≤ B ↔ A ≤ B1.conjAut γ⁻¹ B := by
  have h := B1.conjAut_le_iff (g := γ⁻¹) (A := B) (B := B1.conjAut γ A)
  rw [B1.conjAut_inv_conjAut] at h
  exact h.symm

theorem normal_subgroupOf_iff {G : Type*} [Group G] {J Y : Subgroup G} (hJY : J ≤ Y) :
    (J.subgroupOf Y).Normal ↔ ∀ x ∈ Y, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  constructor
  · intro hN x hx j hj
    have h := hN.conj_mem ⟨j, hJY hj⟩ (Subgroup.mem_subgroupOf.2 hj) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 h
  · exact normal_subgroupOf_of_conj

theorem normal_conjAut {W : Type*} [CommGroup W] (γ : MulAut W) {J Y : Subgroup (MulAut W)}
    (hJY : J ≤ Y) (h : (J.subgroupOf Y).Normal) :
    B1.conjAut γ J ≤ B1.conjAut γ Y ∧ ((B1.conjAut γ J).subgroupOf (B1.conjAut γ Y)).Normal := by
  have hle : B1.conjAut γ J ≤ B1.conjAut γ Y := B1.conjAut_le_iff.2 hJY
  refine ⟨hle, (normal_subgroupOf_iff hle).2 ?_⟩
  intro x hx j hj
  rw [B1.mem_conjAut] at hx hj ⊢
  have h1 := ((normal_subgroupOf_iff hJY).1 h) _ hx _ hj
  have e : γ⁻¹ * (x * j * x⁻¹) * γ = (γ⁻¹ * x * γ) * (γ⁻¹ * j * γ) * (γ⁻¹ * x * γ)⁻¹ := by group
  rw [e]
  exact h1

@[expose] def FourL (k : Mod) (R₂ : Subgroup (Gp 6)) (J J₁ : Subgroup (MulAut (Mod.V 6 k))) :
    Prop :=
  J = R₂.map (Mod.act 6 k) ∧ rk R₂ = 2 ∧
    (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₂.map (Mod.act 6 k) →
      ¬ IsStrongFFStarOffender ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) A) ∧ J₁ = ⊥

@[expose] def FourG (k : Mod) (P : Set (Subgroup (MulAut (Mod.V 6 k))))
    (T R₁ R₂ L₁ L₂ : Subgroup (Gp 6)) (J J₁ : Subgroup (MulAut (Mod.V 6 k))) : Prop :=
  (rk R₂ = 3 ∧ ∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ T.map (Mod.act 6 k) →
    (IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A ↔
      A = R₂.map (Mod.act 6 k))) ∧
  (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₁.map (Mod.act 6 k) →
    ¬ IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A) ∧
  ((∀ A ∈ P, IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A) →
      J₁ = ⊥ ∧ J = R₂.map (Mod.act 6 k)) ∧
  (J₁ = ⊥ →
    (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧ (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal) ∧
    ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆) ∧
  (J₁ ≠ ⊥ →
    ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆ ∧
    ((∃ τ ∈ R₁, τ.IsSwap ∧ J₁ = (Subgroup.zpowers τ).map (Mod.act 6 k)) ∧
        (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧ (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal) ∨
      (J₁ = R₁.map (Mod.act 6 k) ∧ J = T.map (Mod.act 6 k)))) ∧
  ((∀ A ∈ P, Nat.card A = 2) ∨
    ∃ A ∈ P, ∃ B : Subgroup (MulAut (Mod.V 6 k)), B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      B ≤ T.map (Mod.act 6 k) ∧ ¬ B ≤ R₂.map (Mod.act 6 k))

theorem conjAut_commutator {W : Type*} [CommGroup W] (γ : MulAut W) (A B : Subgroup (MulAut W)) :
    ⁅B1.conjAut γ A, B1.conjAut γ B⁆ = B1.conjAut γ ⁅A, B⁆ := by
  rw [conjAut_eq_map_conj, conjAut_eq_map_conj, conjAut_eq_map_conj, Subgroup.map_commutator]

theorem eq_conjAut_iff {W : Type*} [CommGroup W] (γ : MulAut W) (A B : Subgroup (MulAut W)) :
    A = B1.conjAut γ B ↔ B1.conjAut γ⁻¹ A = B := by
  constructor
  · intro h
    rw [h, B1.conjAut_inv_conjAut]
  · intro h
    rw [← h, B1.conjAut_conjAut_inv]

theorem isSwap_conj {α : Type*} [DecidableEq α] [Fintype α] (g τ : Equiv.Perm α)
    (h : τ.IsSwap) : (g * τ * g⁻¹).IsSwap := by
  rw [Equiv.Perm.isSwap_iff_cycleType] at h ⊢
  rw [Equiv.Perm.cycleType_conj]
  exact h

theorem FourL_conj {k : Mod} {g : Gp 6} (hg : g ∈ alternatingGroup (Fin 6)) {R₂ : Subgroup (Gp 6)}
    {J J₁ : Subgroup (MulAut (Mod.V 6 k))} (h : FourL k R₂ J J₁) :
    FourL k (cj g R₂) (B1.conjAut (Mod.act 6 k g) J) (B1.conjAut (Mod.act 6 k g) J₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hγ : Mod.act 6 k g ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 k) :=
    Subgroup.mem_map_of_mem _ hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, map_cj]
  · rw [rk_cj]
    exact h2
  · intro A hA hstr
    rw [map_cj] at hA
    have hA0 : B1.conjAut (Mod.act 6 k g)⁻¹ A ≤ R₂.map (Mod.act 6 k) := by
      have h5 := conjAut_le_iff_le_inv (Mod.act 6 k g)⁻¹ A (R₂.map (Mod.act 6 k))
      rw [inv_inv] at h5
      exact h5.2 hA
    exact h3 _ hA0
      ((isStrong_conjAut_iff (((alternatingGroup (Fin 6)).map (Mod.act 6 k)).inv_mem hγ)).2 hstr)
  · rw [h4]
    exact conjAut_bot _

theorem cj_zpowers {G : Type*} [Group G] (g τ : G) :
    cj g (Subgroup.zpowers τ) = Subgroup.zpowers (g * τ * g⁻¹) := by
  unfold cj
  rw [MonoidHom.map_zpowers]
  rfl

theorem FourG_conj {k : Mod} {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) P) (g : Gp 6)
    {T R₁ R₂ L₁ L₂ : Subgroup (Gp 6)} {J J₁ : Subgroup (MulAut (Mod.V 6 k))}
    (h : FourG k P T R₁ R₂ L₁ L₂ J J₁) :
    FourG k P (cj g T) (cj g R₁) (cj g R₂) (cj g L₁) (cj g L₂)
      (B1.conjAut (Mod.act 6 k g) J) (B1.conjAut (Mod.act 6 k g) J₁) := by
  obtain ⟨⟨hi1, hi2⟩, hii, hiii, hiv, hv, hvi⟩ := h
  have hγ : Mod.act 6 k g ∈ (⊤ : Subgroup (Gp 6)).map (Mod.act 6 k) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_top g)
  have hγ' := ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)).inv_mem hγ
  have hle : ∀ (A : Subgroup (MulAut (Mod.V 6 k))) (B : Subgroup (Gp 6)),
      A ≤ (cj g B).map (Mod.act 6 k) ↔
        B1.conjAut (Mod.act 6 k g)⁻¹ A ≤ B.map (Mod.act 6 k) := by
    intro A B
    have h5 := conjAut_le_iff_le_inv (Mod.act 6 k g)⁻¹ A (B.map (Mod.act 6 k))
    rw [inv_inv] at h5
    rw [map_cj]
    exact h5.symm
  have heq : ∀ (A : Subgroup (MulAut (Mod.V 6 k))) (B : Subgroup (Gp 6)),
      A = (cj g B).map (Mod.act 6 k) ↔
        B1.conjAut (Mod.act 6 k g)⁻¹ A = B.map (Mod.act 6 k) := by
    intro A B
    rw [map_cj]
    exact eq_conjAut_iff _ _ _
  have hsum : cj g L₂ ⊔ cj g T = cj g (L₂ ⊔ T) := (Subgroup.map_sup _ _ _).symm
  have hnorm : J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧
      (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal →
      B1.conjAut (Mod.act 6 k g) J ≤ (cj g L₂ ⊔ cj g T).map (Mod.act 6 k) ∧
      ((B1.conjAut (Mod.act 6 k g) J).subgroupOf
        ((cj g L₂ ⊔ cj g T).map (Mod.act 6 k))).Normal := by
    rintro ⟨h1, h2⟩
    rw [hsum, map_cj]
    exact normal_conjAut _ h1 h2
  have hcomm : ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆ →
      ⁅(cj g L₁).map (Mod.act 6 k), B1.conjAut (Mod.act 6 k g) J⁆ =
        ⁅(cj g L₁).map (Mod.act 6 k), (cj g L₁).map (Mod.act 6 k)⁆ := by
    intro h1
    rw [map_cj, conjAut_commutator, conjAut_commutator, h1]
  refine ⟨⟨by rw [rk_cj]; exact hi1, fun A hA => ?_⟩, fun A hA => ?_, fun hall => ?_,
    fun hJ1 => ?_, fun hJ1 => ?_, ?_⟩
  · rw [heq, ← isStrong_conjAut_iff (X := (⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) hγ']
    exact hi2 _ ((hle A T).1 hA)
  · intro hstr
    rw [← isStrong_conjAut_iff (X := (⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) hγ'] at hstr
    exact hii _ ((hle A R₁).1 hA) hstr
  · obtain ⟨h1, h2⟩ := hiii hall
    refine ⟨by rw [h1]; exact conjAut_bot _, by rw [h2, map_cj]⟩
  · have hJ1' : J₁ = ⊥ := (conjAut_eq_bot _).1 hJ1
    obtain ⟨h1, h2⟩ := hiv hJ1'
    exact ⟨hnorm h1, hcomm h2⟩
  · have hJ1' : J₁ ≠ ⊥ := fun h => hJ1 (by rw [h]; exact conjAut_bot _)
    obtain ⟨h1, h2⟩ := hv hJ1'
    refine ⟨hcomm h1, ?_⟩
    rcases h2 with ⟨⟨τ, hτR, hτs, hτJ⟩, hN⟩ | ⟨hR, hT⟩
    · refine Or.inl ⟨⟨g * τ * g⁻¹, conj_mem_cj.2 hτR, isSwap_conj g τ hτs, ?_⟩, hnorm hN⟩
      rw [hτJ, ← map_cj, cj_zpowers]
    · refine Or.inr ⟨by rw [hR, map_cj], by rw [hT, map_cj]⟩
  · rcases hvi with hall | ⟨A, hA, B, hBA, hcard, hBT, hBR⟩
    · exact Or.inl hall
    · refine Or.inr ⟨B1.conjAut (Mod.act 6 k g) A, (mem_of_conjAut_mem hP hγ).2 hA,
        B1.conjAut (Mod.act 6 k g) B, B1.conjAut_le_iff.2 hBA, ?_, ?_, ?_⟩
      · rw [B1.card_conjAut, B1.card_conjAut]
        exact hcard
      · rw [map_cj]
        exact B1.conjAut_le_iff.2 hBT
      · rw [map_cj]
        intro hh
        exact hBR (B1.conjAut_le_iff.1 hh)

theorem stabW_gmap {H : Subgroup (Gp n)} {g : Gp n} (hg : g ∈ H) (F : Subgroup (Mod.V n k)) :
    stabW H (gmap g F) = cj g (stabW H F) := by
  ext x
  rw [mem_cj]
  show (x ∈ H ∧ ∀ w, w ∈ gmap g F ↔ Mod.act n k x w ∈ gmap g F) ↔
    (g⁻¹ * x * g ∈ H ∧ ∀ w, w ∈ F ↔ Mod.act n k (g⁻¹ * x * g) w ∈ F)
  have hH : g⁻¹ * x * g ∈ H ↔ x ∈ H := by
    constructor
    · intro h
      have h1 := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [e] at h1
    · intro h
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
  rw [hH]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h v
    have h1 := h (Mod.act n k g v)
    rw [mem_gmap, mem_gmap, act_inv_act] at h1
    rw [act_mul3]
    exact h1
  · intro h w
    have h1 := h (Mod.act n k g⁻¹ w)
    rw [act_mul3, act_act_inv] at h1
    rw [mem_gmap, mem_gmap]
    exact h1

theorem O2s_map_conj {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    O2s (X.map ((MulAut.conj g : G ≃* G) : G →* G)) =
      (O2s X).map ((MulAut.conj g : G ≃* G) : G →* G) := by
  have h1 : (CFSG.pCore 2 ↥X).map ((MulAut.conj g).subgroupMap X).toMonoidHom =
      CFSG.pCore 2 ↥(X.map ((MulAut.conj g : G ≃* G) : G →* G)) := CFSG.pCore_map_iso 2 _
  have hcomp : (X.map ((MulAut.conj g : G ≃* G) : G →* G)).subtype.comp
      ((MulAut.conj g).subgroupMap X).toMonoidHom =
      ((MulAut.conj g : G ≃* G) : G →* G).comp X.subtype := by
    ext y
    simp
  unfold O2s
  rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem O2s_cj {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    O2s (cj g X) = cj g (O2s X) := by
  unfold cj
  rw [MulEquiv.toMonoidHom_eq_coe]
  exact O2s_map_conj g X

theorem cj_inf {G : Type*} [Group G] (g : G) (X Y : Subgroup G) :
    cj g (X ⊓ Y) = cj g X ⊓ cj g Y := by
  ext x
  simp only [mem_cj, Subgroup.mem_inf]

theorem cj_normal {G : Type*} [Group G] (g : G) (N : Subgroup G) [N.Normal] : cj g N = N := by
  ext x
  rw [mem_cj]
  constructor
  · intro h
    have h1 := Subgroup.Normal.conj_mem inferInstance _ h g
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  · intro h
    have h1 := Subgroup.Normal.conj_mem inferInstance _ h g⁻¹
    rwa [inv_inv] at h1

theorem ffJP_conjAut_le {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    {P : Set (Subgroup (MulAut W))} (hP : IsStableFF X P) {γ : MulAut W} (hγ : γ ∈ X)
    (Y : Subgroup (MulAut W)) :
    ffJP P (B1.conjAut γ Y) ≤ B1.conjAut γ (ffJP P Y) := by
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAY => ?_
  have hA0 : B1.conjAut γ⁻¹ A ∈ P := (mem_of_conjAut_mem hP (X.inv_mem hγ)).2 hA
  have hA0Y : B1.conjAut γ⁻¹ A ≤ Y := by
    have h1 := (B1.conjAut_le_iff (g := γ⁻¹) (A := B1.conjAut γ Y) (B := A)).2 hAY
    rwa [B1.conjAut_inv_conjAut] at h1
  have hle : B1.conjAut γ⁻¹ A ≤ ffJP P Y :=
    le_iSup_of_le _ (le_iSup_of_le hA0 (le_iSup_of_le hA0Y le_rfl))
  have h2 := conjAut_le_iff_le_inv γ⁻¹ A (ffJP P Y)
  rw [inv_inv] at h2
  exact h2.1 hle

theorem ffJP_conjAut {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    {P : Set (Subgroup (MulAut W))} (hP : IsStableFF X P) {γ : MulAut W} (hγ : γ ∈ X)
    (Y : Subgroup (MulAut W)) : ffJP P (B1.conjAut γ Y) = B1.conjAut γ (ffJP P Y) := by
  refine le_antisymm (ffJP_conjAut_le hP hγ Y) ?_
  have h := ffJP_conjAut_le hP (X.inv_mem hγ) (B1.conjAut γ Y)
  rw [B1.conjAut_inv_conjAut] at h
  exact (conjAut_le_iff_le_inv γ _ _).2 h

theorem ffJP_le {W : Type*} [CommGroup W] (P : Set (Subgroup (MulAut W))) (Y : Subgroup (MulAut W)) :
    ffJP P Y ≤ Y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun h => h

@[expose] def IsSylow2In {G : Type*} [Group G] (H T : Subgroup G) : Prop :=
  T ≤ H ∧ IsPGroup 2 T ∧ ¬ 2 ∣ (T.subgroupOf H).index

theorem card_sylow {G : Type*} [Group G] [Finite G] {H S : Subgroup G} (hS : IsSylow2In H S) :
    Nat.card S = 2 ^ padicValNat 2 (Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS.2.1
  have h1 := Subgroup.card_mul_index (S.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ha] at h1
  have hm : padicValNat 2 (S.subgroupOf H).index = 0 := padicValNat.eq_zero_of_not_dvd hS.2.2
  have hpos : (S.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← h1, padicValNat.mul (by positivity) hpos, padicValNat.prime_pow, hm, add_zero, ha]

theorem exists_conj_eq_sylow {G : Type*} [Group G] [Finite G] {H T T₀ : Subgroup G}
    (hT : IsSylow2In H T) (hT₀ : IsSylow2In H T₀) : ∃ g ∈ H, cj g T₀ = T := by
  obtain ⟨g, hgH, hle⟩ := exists_conj_le_sylow_sub hT.1 hT.2.1 hT.2.2 hT₀.1 hT₀.2.1
  refine ⟨g, hgH, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_sylow hT, show Nat.card (cj g T₀) = Nat.card T₀ from
    Subgroup.card_map_of_injective (MulAut.conj g).injective, card_sylow hT₀]

end CFSG.Quasithin.B3
