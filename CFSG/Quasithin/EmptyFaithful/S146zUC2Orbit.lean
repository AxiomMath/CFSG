module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Comm
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.EmptyFaithful.S146zUC2Off

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Model

variable {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂] {L₁ L₂ : Subgroup (MulAut V)}
  {C : Subgroup V} {Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V}
  {Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)}

theorem IsPairModel.fixV_eq_comap [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    (Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) (hAl : ∀ g ∈ Al, g ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ))) :
    fixV (Al.map Φ) = ((fixNat (Al.map (MonoidHom.fst _ _))).prod
      (fixNat (Al.map (MonoidHom.snd _ _)))).comap Θ := by
  obtain ⟨A₁, A₂, -, -, -, -, -, -, hfix, hA₁, hA₂⟩ := hM.offender_core hK₁ hK₂ Al hAl hge
  subst hA₁ hA₂
  have hle : fixV (Al.map Φ) ≤ ((fixNat (Al.map (MonoidHom.fst _ _))).prod
      (fixNat (Al.map (MonoidHom.snd _ _)))).comap Θ := fun v hv =>
    hM.map_fixV_le Al ⟨v, hv, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hfix, ← card_subgroup_prod]
  exact card_le_of_map_le Θ hM.ker _ _ (Subgroup.map_comap_le _ _)

theorem IsPairModel.sixteen_mul_card_stab_le [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    (Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) (hAl : ∀ g ∈ Al, g ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ))) {s : V}
    (hs : s ∉ fixV (Al.map Φ)) :
    16 * Nat.card ↥(Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥(Al.map Φ) := by
  have hK₁' : Nat.card K₁ = 2 ^ 4 := by rw [hK₁]; norm_num
  have hK₂' : Nat.card K₂ = 2 ^ 4 := by rw [hK₂]; norm_num
  have hcomap := hM.fixV_eq_comap hK₁ hK₂ Al hAl hge
  obtain ⟨A₁, A₂, hmem, hcardAl, h₁, h₂, e₁, e₂, -, hA₁, hA₂⟩ :=
    hM.offender_core hK₁ hK₂ Al hAl hge
  rw [← hA₁, ← hA₂] at hcomap
  have hsq₁ : ∀ y ∈ A₁, y ^ 2 = 1 := fun y hy => by
    have := congrArg Prod.fst (hAl (y, 1) ((hmem (y, 1)).mpr ⟨hy, one_mem _⟩))
    simpa using this
  have hsq₂ : ∀ y ∈ A₂, y ^ 2 = 1 := fun y hy => by
    have := congrArg Prod.snd (hAl (1, y) ((hmem (1, y)).mpr ⟨one_mem _, hy⟩))
    simpa using this
  have hcardA : Nat.card ↥(Al.map Φ) = Nat.card ↥A₁ * Nat.card ↥A₂ := by
    have h1 : Nat.card ↥(Al.map Φ) = Nat.card ↥Al := Subgroup.card_map_of_injective hM.inj
    rw [h1, hcardAl]
  have hsΘ : ¬ ((Θ s).1 ∈ fixNat A₁ ∧ (Θ s).2 ∈ fixNat A₂) := fun h => by
    apply hs
    rw [hcomap]
    exact h
  let ι₁ : ↥(StatedSL 2 K₁) →* MulAut V := Φ.comp (MonoidHom.inl _ _)
  let ι₂ : ↥(StatedSL 2 K₂) →* MulAut V := Φ.comp (MonoidHom.inr _ _)
  have hι₁ : Function.Injective ι₁ := fun x y h => by
    simpa using congrArg Prod.fst (hM.inj h)
  have hι₂ : Function.Injective ι₂ := fun x y h => by
    simpa using congrArg Prod.snd (hM.inj h)
  by_cases hfirst : (Θ s).1 ∈ fixNat A₁
  ·
    have hθ : (Θ s).2 ∉ fixNat A₂ := fun h => hsΘ ⟨hfirst, h⟩
    have hbot : A₂ ≠ ⊥ := by
      intro hb
      apply hθ
      intro g hg
      rw [hb, Subgroup.mem_bot] at hg
      rw [hg]
      exact SzN15.natAct_one' _
    have hc16 : Nat.card ↥A₂ = 16 := h₂.resolve_left hbot
    have hle : Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s ≤ A₁.map ι₁ := by
      rintro _ ⟨ha, hst⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      have hg' := (hmem g).mp hg
      have h1 : Φ g s = s := by
        have := MulAction.mem_stabilizer_iff.mp hst
        simpa using this
      have h2 := hM.equiv g s
      rw [h1] at h2
      have h3 : natAct (StatedSL 2 K₂) g.2 (Θ s).2 = natAct (StatedSL 2 K₂) 1 (Θ s).2 := by
        rw [SzN15.natAct_one']
        exact congrArg Prod.snd h2.symm
      have h4 : g.2 = 1 := eq_of_natAct_eq hK₂' hsq₂ hbot (by rw [hK₂]; exact e₂) hθ hg'.2
        (one_mem _) h3
      have h5 : Φ g = ι₁ g.1 := by
        show Φ g = Φ (g.1, 1)
        rw [← h4]
      rw [h5]
      exact Subgroup.mem_map_of_mem ι₁ hg'.1
    have hcard1 : Nat.card ↥(Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥A₁ := by
      refine (Subgroup.card_le_of_le hle).trans ?_
      exact (Subgroup.card_map_of_injective hι₁).le
    rw [hcardA, hc16]
    calc 16 * Nat.card ↥(Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s) ≤ 16 * Nat.card ↥A₁ :=
          Nat.mul_le_mul_left _ hcard1
      _ = Nat.card ↥A₁ * 16 := by ring
  ·
    have hbot : A₁ ≠ ⊥ := by
      intro hb
      apply hfirst
      intro g hg
      rw [hb, Subgroup.mem_bot] at hg
      rw [hg]
      exact SzN15.natAct_one' _
    have hc16 : Nat.card ↥A₁ = 16 := h₁.resolve_left hbot
    have hle : Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s ≤ A₂.map ι₂ := by
      rintro _ ⟨ha, hst⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      have hg' := (hmem g).mp hg
      have h1 : Φ g s = s := by
        have := MulAction.mem_stabilizer_iff.mp hst
        simpa using this
      have h2 := hM.equiv g s
      rw [h1] at h2
      have h3 : natAct (StatedSL 2 K₁) g.1 (Θ s).1 = natAct (StatedSL 2 K₁) 1 (Θ s).1 := by
        rw [SzN15.natAct_one']
        exact congrArg Prod.fst h2.symm
      have h4 : g.1 = 1 := eq_of_natAct_eq hK₁' hsq₁ hbot (by rw [hK₁]; exact e₁) hfirst hg'.1
        (one_mem _) h3
      have h5 : Φ g = ι₂ g.2 := by
        show Φ g = Φ (1, g.2)
        rw [← h4]
      rw [h5]
      exact Subgroup.mem_map_of_mem ι₂ hg'.2
    have hcard2 : Nat.card ↥(Al.map Φ ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥A₂ := by
      refine (Subgroup.card_le_of_le hle).trans ?_
      exact (Subgroup.card_map_of_injective hι₂).le
    rw [hcardA, hc16]
    exact Nat.mul_le_mul_left _ hcard2

end Model

section Headline

variable {V : Type} [CommGroup V] [Finite V]

theorem sixteen_mul_card_stabilizer_le {Γ L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₁ : Nat.card ↥L₁ = 4080) (hL₂ : Nat.card ↥L₂ = 4080) (hΓ : ffJ Γ = L₁ ⊔ L₂)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender Γ A) {s : V} (hs : s ∉ fixV A) :
    16 * Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥A := by
  obtain ⟨K₁, K₂, _, _, _, _, Φ, Θ, hK₁, hK₂, hM⟩ := exists_pairModel h hcomm hL₁ hL₂
  have hAJ : A ≤ L₁ ⊔ L₂ := hΓ ▸ B6.le_ffJ hA
  obtain ⟨Al, hAmap, hcard, hsq'⟩ := hM.exists_lift hAJ
  have hsq : ∀ g ∈ Al, g ^ 2 = 1 := hsq' hA.2.2.1.2
  have hge : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ)) := by
    rw [hAmap, hcard]
    exact card_le_of_isFFStarOffender hA
  have := hM.sixteen_mul_card_stab_le hK₁ hK₂ Al hsq hge (s := s) (by rw [hAmap]; exact hs)
  rwa [hAmap] at this

theorem four_mul_card_stabilizer_le {Γ L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₁ : Nat.card ↥L₁ = 4080) (hL₂ : Nat.card ↥L₂ = 4080) (hΓ : ffJ Γ = L₁ ⊔ L₂)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender Γ A) {s : V} (hs : s ∉ fixV A) :
    4 * Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥A :=
  le_trans (Nat.mul_le_mul_right _ (by norm_num))
    (sixteen_mul_card_stabilizer_le h hcomm hL₁ hL₂ hΓ hA hs)

end Headline

end CFSG.Quasithin.S146zU.UC2
