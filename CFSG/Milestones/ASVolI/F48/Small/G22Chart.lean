module

public import CFSG.Milestones.ASVolI.F48.Small.G22Base
public import CFSG.Milestones.ASVolI.F48.Id
public import CFSG.Milestones.ASVolI.F4Aut

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G] {H : Subgroup G} {τ : G}

theorem burnsideF48s_g22c_mem_sup_of_mul (hτ : τ * τ = 1) {g : G} (hg : g * τ ∈ H) :
    g ∈ H ⊔ Subgroup.zpowers τ := by
  rw [show g = g * τ * τ by rw [mul_assoc, hτ, mul_one]]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ))

theorem burnsideF48s_g22c_mem_sup_iff (hτ : τ * τ = 1) (hH : ∀ h ∈ H, τ * h * τ ∈ H) (g : G) :
    g ∈ H ⊔ Subgroup.zpowers τ ↔ g ∈ H ∨ g * τ ∈ H := by
  refine ⟨fun hg => ?_, fun hg => hg.elim (fun h => Subgroup.mem_sup_left h)
    (burnsideF48s_g22c_mem_sup_of_mul hτ)⟩
  let S : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * τ ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem ha hb
        · refine Or.inr ?_
          have e : a * b * τ = (a * τ) * (τ * b * τ) := by
            rw [show (a * τ) * (τ * b * τ) = a * (τ * τ) * b * τ by group, hτ, mul_one]
          rw [e]
          exact H.mul_mem ha (hH b hb)
        · refine Or.inl ?_
          have e : a * b = (a * τ) * (τ * (b * τ) * τ) := by
            rw [show (a * τ) * (τ * (b * τ) * τ) = a * (τ * τ) * b * (τ * τ) by group, hτ,
              mul_one, mul_one]
          rw [e]
          exact H.mul_mem ha (hH _ hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · refine Or.inr ?_
          have e : a⁻¹ * τ = τ * (a * τ)⁻¹ * τ := by group
          rw [e]
          exact hH _ (H.inv_mem ha) }
  have hle : H ⊔ Subgroup.zpowers τ ≤ S := by
    refine sup_le (fun h hh => Or.inl hh) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hτ]; exact H.one_mem)
  exact hle hg

theorem burnsideF48s_g22c_index_sup (hτ : τ * τ = 1) (hH : ∀ h ∈ H, τ * h * τ ∈ H)
    (hτH : τ ∉ H) : (H.subgroupOf (H ⊔ Subgroup.zpowers τ)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨τ, Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)⟩, fun b => ?_⟩
  rw [xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hb := (burnsideF48s_g22c_mem_sup_iff hτ hH b).1 b.2
  constructor
  · intro h1 h2
    apply hτH
    have := H.mul_mem (H.inv_mem h2) h1
    rwa [inv_mul_cancel_left] at this
  · intro h
    exact hb.resolve_left h

theorem burnsideF48s_g22c_card_sup (hτ : τ * τ = 1) (hH : ∀ h ∈ H, τ * h * τ ∈ H)
    (hτH : τ ∉ H) : Nat.card ↥(H ⊔ Subgroup.zpowers τ) = 2 * Nat.card H := by
  have h := Subgroup.card_mul_index (H.subgroupOf (H ⊔ Subgroup.zpowers τ))
  rw [burnsideF48s_g22c_index_sup hτ hH hτH,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h
  omega

end Generic

theorem burnsideF48s_g22c_mem_X
    (g : Equiv.Perm (Fin 28)) : g ∈ burnsideF48s_g22X ↔ g ∈ u33J ∨ g * u33Pi ∈ u33J :=
  burnsideF48s_g22c_mem_sup_iff u33Pi_sq (fun _ hh => u33Pi_conj_mem hh) g

theorem burnsideF48s_g22c_card_X :
    Nat.card ↥burnsideF48s_g22X = 12096 := by
  have h := burnsideF48s_g22c_card_sup u33Pi_sq (fun _ hh => u33Pi_conj_mem hh) u33Pi_not_mem
  show Nat.card ↥(u33J ⊔ Subgroup.zpowers u33Pi) = 12096
  rw [h, card_u33J]

section Model

theorem burnsideF48s_g22c_J_le : u33J ≤ burnsideF48s_g22X := le_sup_left

theorem burnsideF48s_g22c_range : u33PresHom.range = u33J := range_u33PresHom

theorem burnsideF48s_g22c_mem_J (u : U33G) : u33PresHom u ∈ u33J := by
  rw [← burnsideF48s_g22c_range]
  exact ⟨u, rfl⟩

@[expose] noncomputable def burnsideF48s_g22c_incl : U33G →* ↥burnsideF48s_g22X where
  toFun u := ⟨u33PresHom u, burnsideF48s_g22c_J_le (burnsideF48s_g22c_mem_J u)⟩
  map_one' := Subtype.ext (map_one u33PresHom)
  map_mul' x y := Subtype.ext (map_mul u33PresHom x y)

theorem burnsideF48s_g22c_L_coe (k : ℕ) (hk : k < 5) :
    ((burnsideF48s_g22L ⟨k, by omega⟩ : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG k) := by
  rw [burnsideF48s_g22L_coe, u33PresHom_genPG]
  simp [burnsideF48s_g22Gen, u33GenP, hk]

theorem burnsideF48s_g22c_L0 :
    ((burnsideF48s_g22L 0 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG 0) :=
  burnsideF48s_g22c_L_coe 0 (by norm_num)

theorem burnsideF48s_g22c_L1 :
    ((burnsideF48s_g22L 1 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG 1) :=
  burnsideF48s_g22c_L_coe 1 (by norm_num)

theorem burnsideF48s_g22c_L2 :
    ((burnsideF48s_g22L 2 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG 2) :=
  burnsideF48s_g22c_L_coe 2 (by norm_num)

theorem burnsideF48s_g22c_L3 :
    ((burnsideF48s_g22L 3 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG 3) :=
  burnsideF48s_g22c_L_coe 3 (by norm_num)

theorem burnsideF48s_g22c_L4 :
    ((burnsideF48s_g22L 4 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      u33PresHom (u33GenPG 4) :=
  burnsideF48s_g22c_L_coe 4 (by norm_num)

theorem burnsideF48s_g22c_L5 :
    ((burnsideF48s_g22L 5 : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) = u33Pi := by
  rw [burnsideF48s_g22L_coe]
  rfl

@[expose] noncomputable def burnsideF48s_g22c_F (R : Subgroup U33G) :
    Subgroup (Equiv.Perm (Fin 28)) :=
  R.map u33PresHom ⊔ Subgroup.zpowers u33Pi

theorem burnsideF48s_g22c_stable {R : Subgroup U33G} (hR : ∀ x ∈ R, u33Phi' x ∈ R) :
    ∀ h ∈ R.map u33PresHom, u33Pi * h * u33Pi ∈ R.map u33PresHom := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u33Phi' u, hR u hu, u33PresHom_phi' u⟩

theorem burnsideF48s_g22c_mem_F {R : Subgroup U33G} (hR : ∀ x ∈ R, u33Phi' x ∈ R)
    (g : Equiv.Perm (Fin 28)) :
    g ∈ burnsideF48s_g22c_F R ↔ g ∈ R.map u33PresHom ∨ g * u33Pi ∈ R.map u33PresHom :=
  burnsideF48s_g22c_mem_sup_iff u33Pi_sq (burnsideF48s_g22c_stable hR) g

theorem burnsideF48s_g22c_map_le_J (R : Subgroup U33G) : R.map u33PresHom ≤ u33J := by
  rw [← burnsideF48s_g22c_range]
  exact Subgroup.map_le_range _ _

theorem burnsideF48s_g22c_not_both {g : Equiv.Perm (Fin 28)} (h1 : g ∈ u33J)
    (h2 : g * u33Pi ∈ u33J) : False := by
  apply u33Pi_not_mem
  have := u33J.mul_mem (u33J.inv_mem h1) h2
  rwa [inv_mul_cancel_left] at this

theorem burnsideF48s_g22c_F_inf_J {R : Subgroup U33G} (hR : ∀ x ∈ R, u33Phi' x ∈ R) :
    burnsideF48s_g22c_F R ⊓ u33J = R.map u33PresHom := by
  refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left (burnsideF48s_g22c_map_le_J R))
  rcases (burnsideF48s_g22c_mem_F hR g).1 hg.1 with h | h
  · exact h
  · exact (burnsideF48s_g22c_not_both hg.2 (burnsideF48s_g22c_map_le_J R h)).elim

theorem burnsideF48s_g22c_F_inj {R₁ R₂ : Subgroup U33G} (h₁ : ∀ x ∈ R₁, u33Phi' x ∈ R₁)
    (h₂ : ∀ x ∈ R₂, u33Phi' x ∈ R₂) (h : burnsideF48s_g22c_F R₁ = burnsideF48s_g22c_F R₂) :
    R₁ = R₂ := by
  apply Subgroup.map_injective u33PresHom_injective
  rw [← burnsideF48s_g22c_F_inf_J h₁, ← burnsideF48s_g22c_F_inf_J h₂, h]

theorem burnsideF48s_g22c_F_inf {R₁ R₂ : Subgroup U33G} (h₁ : ∀ x ∈ R₁, u33Phi' x ∈ R₁)
    (h₂ : ∀ x ∈ R₂, u33Phi' x ∈ R₂) :
    burnsideF48s_g22c_F R₁ ⊓ burnsideF48s_g22c_F R₂ = burnsideF48s_g22c_F (R₁ ⊓ R₂) := by
  have h₁₂ : ∀ x ∈ R₁ ⊓ R₂, u33Phi' x ∈ R₁ ⊓ R₂ := fun x hx => ⟨h₁ x hx.1, h₂ x hx.2⟩
  have hmap : (R₁ ⊓ R₂).map u33PresHom = R₁.map u33PresHom ⊓ R₂.map u33PresHom :=
    Subgroup.map_inf_eq _ _ _ u33PresHom_injective
  have hJ := burnsideF48s_g22c_map_le_J
  ext g
  rw [Subgroup.mem_inf, burnsideF48s_g22c_mem_F h₁, burnsideF48s_g22c_mem_F h₂,
    burnsideF48s_g22c_mem_F h₁₂, hmap, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact (burnsideF48s_g22c_not_both (hJ R₁ h1) (hJ R₂ h2)).elim
    · exact (burnsideF48s_g22c_not_both (hJ R₂ h2) (hJ R₁ h1)).elim
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl h1, Or.inl h2⟩
    · exact ⟨Or.inr h1, Or.inr h2⟩

theorem burnsideF48s_g22c_map_closure (S : Set ↥burnsideF48s_g22X) (S₀ : Set U33G)
    (h1 : ∀ s ∈ S, (s : Equiv.Perm (Fin 28)) ∈ u33PresHom '' S₀ ∨
      (s : Equiv.Perm (Fin 28)) = u33Pi)
    (h2 : ∀ s ∈ S₀, ∃ x ∈ S, (x : Equiv.Perm (Fin 28)) = u33PresHom s)
    (h3 : ∃ x ∈ S, (x : Equiv.Perm (Fin 28)) = u33Pi) :
    (Subgroup.closure S).map burnsideF48s_g22X.subtype =
      burnsideF48s_g22c_F (Subgroup.closure S₀) := by
  apply le_antisymm
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rcases h1 s hs with ⟨s₀, hs₀, he⟩ | he
    · exact Subgroup.mem_sup_left ⟨s₀, Subgroup.subset_closure hs₀, he⟩
    · have he' : burnsideF48s_g22X.subtype s = u33Pi := he
      rw [SetLike.mem_coe, he']
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u33Pi)
  · refine sup_le ?_ ?_
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s₀, hs₀, rfl⟩
      obtain ⟨x, hx, hxe⟩ := h2 s₀ hs₀
      exact ⟨x, Subgroup.subset_closure hx, hxe⟩
    · rw [Subgroup.zpowers_le]
      obtain ⟨x, hx, hxe⟩ := h3
      exact ⟨x, Subgroup.subset_closure hx, hxe⟩

theorem burnsideF48s_g22c_T_map :
    burnsideF48s_g22T.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F u33Data.T := by
  show (Subgroup.closure _).map _ =
    burnsideF48s_g22c_F (Subgroup.closure {u33GenPG 0, u33GenPG 1, u33GenPG 2})
  refine burnsideF48s_g22c_map_closure _ _ ?_ ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨u33GenPG 0, by simp, burnsideF48s_g22c_L0.symm⟩
    · exact Or.inl ⟨u33GenPG 1, by simp, burnsideF48s_g22c_L1.symm⟩
    · exact Or.inl ⟨u33GenPG 2, by simp, burnsideF48s_g22c_L2.symm⟩
    · exact Or.inr burnsideF48s_g22c_L5
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨burnsideF48s_g22L 0, by simp, burnsideF48s_g22c_L0⟩
    · exact ⟨burnsideF48s_g22L 1, by simp, burnsideF48s_g22c_L1⟩
    · exact ⟨burnsideF48s_g22L 2, by simp, burnsideF48s_g22c_L2⟩
  · exact ⟨burnsideF48s_g22L 5, by simp, burnsideF48s_g22c_L5⟩

theorem burnsideF48s_g22c_P2_map :
    burnsideF48s_g22P2.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F u33Data.A := by
  show (Subgroup.closure _).map _ =
    burnsideF48s_g22c_F (Subgroup.closure {u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3})
  refine burnsideF48s_g22c_map_closure _ _ ?_ ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨u33GenPG 0, by simp, burnsideF48s_g22c_L0.symm⟩
    · exact Or.inl ⟨u33GenPG 1, by simp, burnsideF48s_g22c_L1.symm⟩
    · exact Or.inl ⟨u33GenPG 2, by simp, burnsideF48s_g22c_L2.symm⟩
    · exact Or.inl ⟨u33GenPG 3, by simp, burnsideF48s_g22c_L3.symm⟩
    · exact Or.inr burnsideF48s_g22c_L5
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨burnsideF48s_g22L 0, by simp, burnsideF48s_g22c_L0⟩
    · exact ⟨burnsideF48s_g22L 1, by simp, burnsideF48s_g22c_L1⟩
    · exact ⟨burnsideF48s_g22L 2, by simp, burnsideF48s_g22c_L2⟩
    · exact ⟨burnsideF48s_g22L 3, by simp, burnsideF48s_g22c_L3⟩
  · exact ⟨burnsideF48s_g22L 5, by simp, burnsideF48s_g22c_L5⟩

theorem burnsideF48s_g22c_P1_map :
    burnsideF48s_g22P1.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F u33Data.B := by
  show (Subgroup.closure _).map _ =
    burnsideF48s_g22c_F (Subgroup.closure {u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4})
  refine burnsideF48s_g22c_map_closure _ _ ?_ ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨u33GenPG 0, by simp, burnsideF48s_g22c_L0.symm⟩
    · exact Or.inl ⟨u33GenPG 1, by simp, burnsideF48s_g22c_L1.symm⟩
    · exact Or.inl ⟨u33GenPG 2, by simp, burnsideF48s_g22c_L2.symm⟩
    · exact Or.inl ⟨u33GenPG 4, by simp, burnsideF48s_g22c_L4.symm⟩
    · exact Or.inr burnsideF48s_g22c_L5
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨burnsideF48s_g22L 0, by simp, burnsideF48s_g22c_L0⟩
    · exact ⟨burnsideF48s_g22L 1, by simp, burnsideF48s_g22c_L1⟩
    · exact ⟨burnsideF48s_g22L 2, by simp, burnsideF48s_g22c_L2⟩
    · exact ⟨burnsideF48s_g22L 4, by simp, burnsideF48s_g22c_L4⟩
  · exact ⟨burnsideF48s_g22L 5, by simp, burnsideF48s_g22c_L5⟩

theorem burnsideF48s_g22c_top_map :
    (⊤ : Subgroup ↥burnsideF48s_g22X).map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F ⊤ := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show u33J ⊔ Subgroup.zpowers u33Pi = (⊤ : Subgroup U33G).map u33PresHom ⊔ Subgroup.zpowers u33Pi
  rw [← MonoidHom.range_eq_map, burnsideF48s_g22c_range]

theorem burnsideF48s_g22c_overgroup (Q : Subgroup ↥burnsideF48s_g22X) (hQ : burnsideF48s_g22T ≤ Q) :
    Q.map burnsideF48s_g22X.subtype =
        burnsideF48s_g22c_F ((Q.map burnsideF48s_g22X.subtype).comap u33PresHom) ∧
      u33Data.T ≤ (Q.map burnsideF48s_g22X.subtype).comap u33PresHom := by
  have hTQ : burnsideF48s_g22c_F u33Data.T ≤ Q.map burnsideF48s_g22X.subtype := by
    rw [← burnsideF48s_g22c_T_map]
    exact Subgroup.map_mono hQ
  have hτ : u33Pi ∈ Q.map burnsideF48s_g22X.subtype :=
    hTQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers u33Pi))
  have hT0 : u33Data.T.map u33PresHom ≤ Q.map burnsideF48s_g22X.subtype :=
    le_sup_left.trans hTQ
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (Subgroup.map_comap_le _ _)
    ((Subgroup.zpowers_le).2 hτ)), Subgroup.map_le_iff_le_comap.1 hT0⟩
  have hgX : g ∈ burnsideF48s_g22X := Subgroup.map_subtype_le Q hg
  rcases (burnsideF48s_g22c_mem_X g).1 hgX with h | h
  · rw [← burnsideF48s_g22c_range] at h
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 h
    exact Subgroup.mem_sup_left ⟨u, hg, rfl⟩
  · rw [← burnsideF48s_g22c_range] at h
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 h
    have hu' : u ∈ (Q.map burnsideF48s_g22X.subtype).comap u33PresHom := by
      show u33PresHom u ∈ Q.map burnsideF48s_g22X.subtype
      rw [hu]
      exact Subgroup.mul_mem _ hg hτ
    exact burnsideF48s_g22c_mem_sup_of_mul u33Pi_sq ⟨u, hu', hu⟩

theorem burnsideF48s_g22c_lattice (Q : Subgroup ↥burnsideF48s_g22X) (hQ : burnsideF48s_g22T ≤ Q) :
    Q = burnsideF48s_g22T ∨ Q = burnsideF48s_g22P2 ∨ Q = burnsideF48s_g22P1 ∨ Q = ⊤ := by
  obtain ⟨hQe, hTR⟩ := burnsideF48s_g22c_overgroup Q hQ
  have hinj := Subgroup.map_injective burnsideF48s_g22X.subtype_injective
  rcases u33Data.lattice _ hTR with h | h | h | h <;> rw [h] at hQe
  · exact Or.inl (hinj (hQe.trans burnsideF48s_g22c_T_map.symm))
  · exact Or.inr (Or.inl (hinj (hQe.trans burnsideF48s_g22c_P2_map.symm)))
  · exact Or.inr (Or.inr (Or.inl (hinj (hQe.trans burnsideF48s_g22c_P1_map.symm))))
  · exact Or.inr (Or.inr (Or.inr (hinj (hQe.trans burnsideF48s_g22c_top_map.symm))))

theorem burnsideF48s_g22c_incl_mem_iff {R : Subgroup U33G} (hR : ∀ x ∈ R, u33Phi' x ∈ R)
    {Q : Subgroup ↥burnsideF48s_g22X}
    (hQ : Q.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F R) (t : U33G) :
    burnsideF48s_g22c_incl t ∈ Q ↔ t ∈ R := by
  rw [← Subgroup.mem_map_iff_mem burnsideF48s_g22X.subtype_injective, hQ]
  change u33PresHom t ∈ burnsideF48s_g22c_F R ↔ t ∈ R
  constructor
  · intro h
    have h' : u33PresHom t ∈ burnsideF48s_g22c_F R ⊓ u33J := ⟨h, burnsideF48s_g22c_mem_J t⟩
    rw [burnsideF48s_g22c_F_inf_J hR] at h'
    exact (Subgroup.mem_map_iff_mem u33PresHom_injective).1 h'
  · intro h
    exact Subgroup.mem_sup_left ⟨t, h, rfl⟩

theorem burnsideF48s_g22c_normalizer :
    Subgroup.normalizer (burnsideF48s_g22T : Set ↥burnsideF48s_g22X) = burnsideF48s_g22T := by
  set N := Subgroup.normalizer (burnsideF48s_g22T : Set ↥burnsideF48s_g22X) with hNdef
  have hTN : burnsideF48s_g22T ≤ N := Subgroup.le_normalizer
  obtain ⟨hNe, hTR⟩ := burnsideF48s_g22c_overgroup N hTN
  have hRN : (N.map burnsideF48s_g22X.subtype).comap u33PresHom ≤
      Subgroup.normalizer (u33Data.T : Set U33G) := by
    intro u hu
    have hu1 : burnsideF48s_g22X.subtype (burnsideF48s_g22c_incl u) ∈
        N.map burnsideF48s_g22X.subtype := hu
    have hu' : burnsideF48s_g22c_incl u ∈ N :=
      (Subgroup.mem_map_iff_mem burnsideF48s_g22X.subtype_injective).1 hu1
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have h1 := burnsideF48s_g22c_incl_mem_iff u33Phi'_T burnsideF48s_g22c_T_map t
    have h2 := burnsideF48s_g22c_incl_mem_iff u33Phi'_T burnsideF48s_g22c_T_map (u * t * u⁻¹)
    have h3 := Subgroup.mem_normalizer_iff.1 hu' (burnsideF48s_g22c_incl t)
    rw [map_mul, map_mul, map_inv] at h2
    exact h1.symm.trans (h3.trans h2)
  rw [u33Extra.normalizer_T] at hRN
  have hR : (N.map burnsideF48s_g22X.subtype).comap u33PresHom = u33Data.T := le_antisymm hRN hTR
  rw [hR] at hNe
  exact Subgroup.map_injective burnsideF48s_g22X.subtype_injective
    (hNe.trans burnsideF48s_g22c_T_map.symm)

theorem burnsideF48s_g22c_card_T : Nat.card ↥burnsideF48s_g22T = 64 := by
  have h1 := Subgroup.card_map_of_injective (K := burnsideF48s_g22T)
    burnsideF48s_g22X.subtype_injective
  rw [burnsideF48s_g22c_T_map] at h1
  have h2 := burnsideF48s_g22c_card_sup u33Pi_sq (burnsideF48s_g22c_stable u33Phi'_T)
    (fun h => u33Pi_not_mem (burnsideF48s_g22c_map_le_J _ h))
  rw [Subgroup.card_map_of_injective u33PresHom_injective, u33_card_T] at h2
  have h3 : Nat.card ↥(burnsideF48s_g22c_F u33Data.T) = 64 := by
    show Nat.card ↥(u33Data.T.map u33PresHom ⊔ Subgroup.zpowers u33Pi) = 64
    omega
  omega

theorem burnsideF48s_g22c_sylow : ChF.IsSylowOf 2 burnsideF48s_g22T ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 6) (by rw [burnsideF48s_g22c_card_T]; norm_num), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index burnsideF48s_g22T
  rw [burnsideF48s_g22c_card_T, burnsideF48s_g22c_card_X] at h
  have h189 : burnsideF48s_g22T.index = 189 := by omega
  rw [h189]
  norm_num

theorem burnsideF48s_g22c_ne {Q₁ Q₂ : Subgroup ↥burnsideF48s_g22X} {R₁ R₂ : Subgroup U33G}
    (h₁ : ∀ x ∈ R₁, u33Phi' x ∈ R₁) (h₂ : ∀ x ∈ R₂, u33Phi' x ∈ R₂)
    (e₁ : Q₁.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F R₁)
    (e₂ : Q₂.map burnsideF48s_g22X.subtype = burnsideF48s_g22c_F R₂) (hne : R₁ ≠ R₂) :
    Q₁ ≠ Q₂ := by
  rintro rfl
  exact hne (burnsideF48s_g22c_F_inj h₁ h₂ (e₁.symm.trans e₂))

theorem burnsideF48s_g22c_T_le_P1 : burnsideF48s_g22T ≤ burnsideF48s_g22P1 := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem burnsideF48s_g22c_T_le_P2 : burnsideF48s_g22T ≤ burnsideF48s_g22P2 := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem burnsideF48s_g22c_inf : burnsideF48s_g22P1 ⊓ burnsideF48s_g22P2 = burnsideF48s_g22T := by
  apply Subgroup.map_injective burnsideF48s_g22X.subtype_injective
  rw [Subgroup.map_inf_eq _ _ _ burnsideF48s_g22X.subtype_injective, burnsideF48s_g22c_P1_map,
    burnsideF48s_g22c_P2_map, burnsideF48s_g22c_F_inf u33Phi'_B u33Phi'_A, inf_comm,
    u33Data.inf_AB, burnsideF48s_g22c_T_map]

theorem burnsideF48s_g22c_isLieParabolics :
    ChF.IsLieParabolics 2 (⊤ : Subgroup ↥burnsideF48s_g22X) burnsideF48s_g22T burnsideF48s_g22P1
      burnsideF48s_g22P2 := by
  have hB : ∀ x ∈ u33Data.B, u33Phi' x ∈ u33Data.B := u33Phi'_B
  have hA : ∀ x ∈ u33Data.A, u33Phi' x ∈ u33Data.A := u33Phi'_A
  have hT : ∀ x ∈ u33Data.T, u33Phi' x ∈ u33Data.T := u33Phi'_T
  have htop : ∀ x ∈ (⊤ : Subgroup U33G), u33Phi' x ∈ (⊤ : Subgroup U33G) :=
    fun _ _ => Subgroup.mem_top _
  have hBA : u33Data.B ≠ u33Data.A := fun h => u33Data.T_ne_A (by
    rw [← u33Data.inf_AB, h, inf_idem])
  exact (burnsideF4h_g2_isLie_of_lattice burnsideF48s_g22c_sylow burnsideF48s_g22c_normalizer
    burnsideF48s_g22c_lattice burnsideF48s_g22c_T_le_P1 burnsideF48s_g22c_T_le_P2
    (burnsideF48s_g22c_ne hB hA burnsideF48s_g22c_P1_map burnsideF48s_g22c_P2_map hBA)
    (burnsideF48s_g22c_ne hB hT burnsideF48s_g22c_P1_map burnsideF48s_g22c_T_map
      u33Data.T_ne_B.symm)
    (burnsideF48s_g22c_ne hA hT burnsideF48s_g22c_P2_map burnsideF48s_g22c_T_map
      u33Data.T_ne_A.symm)
    (burnsideF48s_g22c_ne hB htop burnsideF48s_g22c_P1_map burnsideF48s_g22c_top_map u33B_ne_top)
    (burnsideF48s_g22c_ne hA htop burnsideF48s_g22c_P2_map burnsideF48s_g22c_top_map u33A_ne_top)
    burnsideF48s_g22c_inf).1

theorem burnsideF48s_g22c_index_J : (u33J.subgroupOf burnsideF48s_g22X).index = 2 :=
  burnsideF48s_g22c_index_sup u33Pi_sq (fun _ hh => u33Pi_conj_mem hh) u33Pi_not_mem

theorem burnsideF48s_g22c_J_normal : (u33J.subgroupOf burnsideF48s_g22X).Normal :=
  Subgroup.normal_of_index_eq_two burnsideF48s_g22c_index_J

theorem burnsideF48s_g22c_centJ (x : ↥burnsideF48s_g22X)
    (h : ∀ d ∈ u33J.subgroupOf burnsideF48s_g22X, x * d = d * x) : x = 1 :=
  Subtype.ext (u33_centralizer_trivial x.1 fun g hg =>
    congrArg Subtype.val (h ⟨g, burnsideF48s_g22c_J_le hg⟩ hg))

@[expose] noncomputable def burnsideF48s_g22c_conjJ : ↥burnsideF48s_g22X →* MulAut ↥u33J :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe burnsideF48s_g22c_J_le)).toMonoidHom.comp
    (@MulAut.conjNormal _ _ (u33J.subgroupOf burnsideF48s_g22X) burnsideF48s_g22c_J_normal)

theorem burnsideF48s_g22c_conjJ_apply (x : ↥burnsideF48s_g22X) (g : ↥u33J) :
    ((burnsideF48s_g22c_conjJ x g : ↥u33J) : Equiv.Perm (Fin 28)) =
      x * g * (x : Equiv.Perm (Fin 28))⁻¹ :=
  rfl

theorem burnsideF48s_g22c_conjJ_injective : Function.Injective burnsideF48s_g22c_conjJ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply u33_centralizer_trivial
  intro g hg
  have e := congrArg (fun α : MulAut ↥u33J => ((α ⟨g, hg⟩ : ↥u33J) : Equiv.Perm (Fin 28)))
    (MonoidHom.mem_ker.1 hx)
  simp only [burnsideF48s_g22c_conjJ_apply, MulAut.one_apply] at e
  calc (x : Equiv.Perm (Fin 28)) * g
      = (x * g * (x : Equiv.Perm (Fin 28))⁻¹) * x := by group
    _ = g * x := by rw [e]

theorem burnsideF48s_g22c_conjJ_bijective : Function.Bijective burnsideF48s_g22c_conjJ := by
  haveI : Finite (MulAut ↥u33J) :=
    Finite.of_injective (fun α : MulAut ↥u33J => (α : ↥u33J → ↥u33J)) fun _ _ h =>
      MulEquiv.ext fun x => congrFun h x
  refine burnsideF48s_g22c_conjJ_injective.bijective_of_nat_card_le ?_
  rw [burnsideF48s_g22c_card_X, ← Nat.card_congr (MulAut.congr u33ToJ).toEquiv]
  exact card_mulAut_u33Pres_le

theorem burnsideF48s_g22c_commutator_J : ⁅u33J, u33J⁆ = u33J := by
  haveI := isSimpleGroup_u33J
  have htop : ⁅(⊤ : Subgroup ↥u33J), (⊤ : Subgroup ↥u33J)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (⁅(⊤ : Subgroup ↥u33J), (⊤ : Subgroup ↥u33J)⁆) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := u33J_nonabelian
      have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) (Subgroup.mem_top x)
      rw [Subgroup.mem_centralizer_iff] at hc
      exact hxy (hc y (Subgroup.mem_top y)).symm
    · exact h
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥u33J) ⊤ u33J.subtype
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.symm

theorem burnsideF48s_g22c_J_eq_commutator :
    u33J.subgroupOf burnsideF48s_g22X =
      ⁅(⊤ : Subgroup ↥burnsideF48s_g22X), (⊤ : Subgroup ↥burnsideF48s_g22X)⁆ := by
  apply le_antisymm
  · have hp : ⁅u33J.subgroupOf burnsideF48s_g22X, u33J.subgroupOf burnsideF48s_g22X⁆ =
        u33J.subgroupOf burnsideF48s_g22X := by
      apply Subgroup.map_injective burnsideF48s_g22X.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le burnsideF48s_g22c_J_le]
      exact burnsideF48s_g22c_commutator_J
    calc u33J.subgroupOf burnsideF48s_g22X
        = ⁅u33J.subgroupOf burnsideF48s_g22X, u33J.subgroupOf burnsideF48s_g22X⁆ := hp.symm
      _ ≤ ⁅(⊤ : Subgroup ↥burnsideF48s_g22X), (⊤ : Subgroup ↥burnsideF48s_g22X)⁆ :=
          Subgroup.commutator_mono le_top le_top
  · haveI : (u33J.subgroupOf burnsideF48s_g22X).Normal := burnsideF48s_g22c_J_normal
    have hc2 : Nat.card (↥burnsideF48s_g22X ⧸ u33J.subgroupOf burnsideF48s_g22X) = 2 := by
      rw [← Subgroup.index_eq_card, burnsideF48s_g22c_index_J]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hcyc : IsCyclic (↥burnsideF48s_g22X ⧸ u33J.subgroupOf burnsideF48s_g22X) :=
      isCyclic_of_prime_card hc2
    have hcomm : commutator ↥burnsideF48s_g22X ≤ u33J.subgroupOf burnsideF48s_g22X := by
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      exact ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
    exact hcomm

theorem burnsideF48s_g22c_complete (α : MulAut ↥burnsideF48s_g22X) :
    ∃ m : ↥burnsideF48s_g22X, ∀ x : ↥burnsideF48s_g22X, α x = m * x * m⁻¹ := by
  haveI hchar : (u33J.subgroupOf burnsideF48s_g22X).Characteristic := by
    rw [burnsideF48s_g22c_J_eq_commutator]
    infer_instance
  haveI : (u33J.subgroupOf burnsideF48s_g22X).Normal := burnsideF48s_g22c_J_normal
  let e0 : ↥(u33J.subgroupOf burnsideF48s_g22X) ≃* ↥u33J :=
    Subgroup.subgroupOfEquivOfLe burnsideF48s_g22c_J_le
  obtain ⟨m, hm⟩ := burnsideF48s_g22c_conjJ_bijective.2
    (MulAut.congr e0 (burnsideF4gF4Two_restrict (u33J.subgroupOf burnsideF48s_g22X) α))
  have hD : ∀ d : ↥burnsideF48s_g22X, d ∈ u33J.subgroupOf burnsideF48s_g22X →
      α d = m * d * m⁻¹ := by
    intro d hd
    have h1 := congrArg (fun β : MulAut ↥u33J =>
      ((β (e0 ⟨d, hd⟩) : ↥u33J) : Equiv.Perm (Fin 28))) hm
    apply Subtype.ext
    exact h1.symm
  refine ⟨m, fun x => ?_⟩
  have hbx : ∀ d : ↥burnsideF48s_g22X, d ∈ u33J.subgroupOf burnsideF48s_g22X →
      (m⁻¹ * α x * m) * d * (m⁻¹ * α x * m)⁻¹ = x * d * x⁻¹ := by
    intro d hd
    have e1 : α (x * d * x⁻¹) = α x * (m * d * m⁻¹) * (α x)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hD d hd]
    have e2 : α (x * d * x⁻¹) = m * (x * d * x⁻¹) * m⁻¹ :=
      hD _ ((inferInstance : (u33J.subgroupOf burnsideF48s_g22X).Normal).conj_mem d hd x)
    calc (m⁻¹ * α x * m) * d * (m⁻¹ * α x * m)⁻¹
        = m⁻¹ * (α x * (m * d * m⁻¹) * (α x)⁻¹) * m := by group
      _ = m⁻¹ * (m * (x * d * x⁻¹) * m⁻¹) * m := by rw [← e1, e2]
      _ = x * d * x⁻¹ := by group
  have hy : x⁻¹ * (m⁻¹ * α x * m) = 1 := by
    apply burnsideF48s_g22c_centJ
    intro d hd
    calc x⁻¹ * (m⁻¹ * α x * m) * d
        = x⁻¹ * ((m⁻¹ * α x * m) * d * (m⁻¹ * α x * m)⁻¹) * (m⁻¹ * α x * m) := by group
      _ = x⁻¹ * (x * d * x⁻¹) * (m⁻¹ * α x * m) := by rw [hbx d hd]
      _ = d * (x⁻¹ * (m⁻¹ * α x * m)) := by group
  have hz : m⁻¹ * α x * m = x := by
    calc m⁻¹ * α x * m = x * (x⁻¹ * (m⁻¹ * α x * m)) := by group
      _ = x := by rw [hy, mul_one]
  calc α x = m * (m⁻¹ * α x * m) * m⁻¹ := by group
    _ = m * x * m⁻¹ := by rw [hz]

theorem burnsideF48s_g22c_eq_top {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hcen : Subgroup.centralizer (Gp : Set E) = ⊥) (Ψ : ↥Gp ≃* ↥burnsideF48s_g22X) : Gp = ⊤ := by
  rw [eq_top_iff]
  intro e _
  obtain ⟨m, hm⟩ := burnsideF48s_g22c_complete
    ((Ψ.symm.trans (MulAut.conjNormal (H := Gp) e)).trans Ψ)
  set g : ↥Gp := Ψ.symm m with hg
  have hx : ∀ x : ↥Gp, e * (x : E) * e⁻¹ = (g : E) * x * (g : E)⁻¹ := by
    intro x
    have h1 := hm (Ψ x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Ψ.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    have h3 := congrArg (fun z : ↥Gp => (z : E)) h2
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h3
    simpa [MulAut.conjNormal_apply, hg] using h3
  have hmem : (g : E)⁻¹ * e ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := hx ⟨h, hh⟩
    calc h * ((g : E)⁻¹ * e) = (g : E)⁻¹ * ((g : E) * h * (g : E)⁻¹) * e := by group
      _ = (g : E)⁻¹ * (e * h * e⁻¹) * e := by rw [← this]
      _ = ((g : E)⁻¹ * e) * h := by group
  rw [hcen, Subgroup.mem_bot] at hmem
  have : e = (g : E) := by
    calc e = (g : E) * ((g : E)⁻¹ * e) := by group
      _ = (g : E) := by rw [hmem, mul_one]
  rw [this]
  exact g.2

end Model

section Chart

theorem burnsideF48s_g22c_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 2 1 Gp M₁ M₂) :
    Gp = ⊤ ∧ ∃ θ : ↥burnsideF48s_g22X ≃* E, M₁ ⊓ M₂ = burnsideF48s_g22T.map θ.toMonoidHom ∧
      ((M₁ = burnsideF48s_g22P1.map θ.toMonoidHom ∧ M₂ = burnsideF48s_g22P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48s_g22P2.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_g22P1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, fK, finK, hK, marking, -, -⟩ := burnsideF4gG2Two_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  let ε₀ : ↥burnsideF48s_g22X ≃* ↥Gp :=
    (MulEquiv.ofBijective burnsideF48s_g22c_conjJ burnsideF48s_g22c_conjJ_bijective).trans
      ((MulAut.congr u33ToJ.symm).trans ((MulAut.congr (burnsideF4h_g2_psi K hK2)).trans
        ((MulEquiv.ofBijective _ (burnsideF45_g2_conj_bijective hK2)).symm.trans marking)))
  have hGp : Gp = ⊤ := burnsideF48s_g22c_eq_top hyp.centralizer_trivial ε₀.symm
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  subst hGp
  obtain ⟨ε, hεT, hε⟩ := burnsideF48_identify ε₀ burnsideF48s_g22c_isLieParabolics hP
  let θ : ↥burnsideF48s_g22X ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup ↥burnsideF48s_g22X, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  refine ⟨rfl, θ, ?_, ?_⟩
  · rw [← himg, hεT, top_inf_eq]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← himg, h1, top_inf_eq], by rw [← himg, h2, top_inf_eq]⟩
    · exact Or.inr ⟨by rw [← himg, h2, top_inf_eq], by rw [← himg, h1, top_inf_eq]⟩

end Chart

end CFSG.ASVolI
