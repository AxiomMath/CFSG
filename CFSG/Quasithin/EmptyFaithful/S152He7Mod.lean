module

public import CFSG.Quasithin.EmptyFaithful.S152He6Pair
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He6 CFSG.QuasithinUnique.Setup.X1

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem sq_eq_one_of_index_two (hW : ∀ w : W, w * w = 1) {x : MulAut W}
    (hx : (fixV (Subgroup.zpowers x)).index = 2) : x * x = 1 := by
  have hc : Nat.card (cmt x ⊤) = 2 := by
    rw [← index_fixV_zpowers_eq_card_cmt]
    exact hx
  obtain ⟨c, hc1, hcu⟩ := (Nat.card_eq_two_iff' (1 : ↥(cmt x ⊤))).1 hc
  have hRc : ∀ r : ↥(cmt x ⊤), r = 1 ∨ r = c := fun r => by
    by_cases h : r = 1
    · exact Or.inl h
    · exact Or.inr (hcu r h)
  have hfixR : ∀ r : ↥(cmt x ⊤), x (r : W) = r := by
    intro r
    have h1 : x (r : W) * (r : W)⁻¹ ∈ cmt x ⊤ := dsp_mem_cmt (Subgroup.mem_top _)
    rcases hRc ⟨_, h1⟩ with h | h
    · have := congrArg Subtype.val h
      simpa [mul_inv_eq_one] using this
    · exfalso
      have h2 : x (r : W) * (r : W)⁻¹ = (c : W) := congrArg Subtype.val h
      rcases hRc r with hr | hr
      · rw [hr] at h2
        apply hc1
        apply Subtype.ext
        simpa using h2.symm
      · rw [hr] at h2
        have h3 : x (c : W) = 1 := by
          have h4 : x (c : W) = (c : W) * (c : W) :=
            calc x (c : W) = x (c : W) * (c : W)⁻¹ * (c : W) := by rw [inv_mul_cancel_right]
              _ = (c : W) * (c : W) := by rw [h2]
          rw [h4]
          exact hW _
        apply hc1
        apply Subtype.ext
        have h5 : x (c : W) = x 1 := by rw [h3, map_one]
        exact x.injective h5
  refine MulEquiv.ext fun w => ?_
  have hr : x w * w⁻¹ ∈ cmt x ⊤ := dsp_mem_cmt (Subgroup.mem_top _)
  set r : ↥(cmt x ⊤) := ⟨_, hr⟩ with hrdef
  have hxr := hfixR r
  have hrr : (r : W) * (r : W) = 1 := hW _
  have h1 : x w = (r : W) * w := by
    show x w = x w * w⁻¹ * w
    rw [inv_mul_cancel_right]
  calc (x * x) w = x (x w) := rfl
    _ = x ((r : W) * w) := by rw [← h1]
    _ = (r : W) * ((r : W) * w) := by rw [map_mul, hxr, ← h1]
    _ = w := by rw [← mul_assoc, hrr, one_mul]

theorem eq_bot_of_irr_of_isPGroup (hW : ∀ w : W, w * w = 1) [Nontrivial W] {G : Subgroup (MulAut W)}
    (hG : IsPGroup 2 ↥G)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) : G = ⊥ := by
  have hpW : IsPGroup 2 W := fun w => ⟨1, by simpa [sq] using hW w⟩
  obtain ⟨m, hm⟩ := hpW.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := W)
    simp at hm
    omega
  have hmod := CFSG.Quasithin.card_modEq_card_fixV (q := 2) hG
  have h2W : 2 ∣ Nat.card W := hm ▸ dvd_pow_self 2 hm0
  have h2F : 2 ∣ Nat.card (fixV G) := (hmod.dvd_iff dvd_rfl).1 h2W
  have hFne : fixV G ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2F
    exact absurd h2F (by norm_num)
  have hFtop : fixV G = ⊤ :=
    (hirr (fixV G) (fun g hg u hu => by rw [mem_fixV.1 hu g hg]; exact hu)).resolve_left hFne
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => MulEquiv.ext fun w => ?_
  exact mem_fixV.1 (hFtop ▸ Subgroup.mem_top w) g hg

theorem irr_of_transvection {G Λ : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ G, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hsimp : IsSimpleGroup ↥Λ) {ζ : MulAut W} (hζ : ζ ∈ Λ) (hζ1 : ζ ≠ 1)
    (hζi : (fixV (Subgroup.zpowers ζ)).index = 2) :
    ∀ U : Subgroup W, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  have hnorm' : ∀ g ∈ G, ∀ l ∈ Λ, g⁻¹ * l * g ∈ Λ := fun g hg l hl => by
    simpa using hnorm g⁻¹ (G.inv_mem hg) l hl
  have hcomm : ∀ (g l : MulAut W) (u : W), g ((g⁻¹ * l * g) u) = l (g u) := fun g l u => by
    have : g * (g⁻¹ * l * g) = l * g := by group
    exact congrArg (fun m : MulAut W => m u) this
  have hfixΛ : fixV Λ = ⊥ := by
    have hinv : ∀ g ∈ G, ∀ c ∈ fixV Λ, g c ∈ fixV Λ := by
      intro g hg c hc l hl
      have h2 := mem_fixV.1 hc _ (hnorm' g hg l hl)
      rw [← hcomm g l c, h2]
    refine (hirr (fixV Λ) hinv).resolve_right fun htop => hζ1 ?_
    exact MulEquiv.ext fun w => mem_fixV.1 (htop ▸ Subgroup.mem_top w) ζ hζ
  have hR : Nat.card (cmt ζ ⊤) = 2 := by
    rw [← index_fixV_zpowers_eq_card_cmt]
    exact hζi
  have hR1 : cmt ζ ⊤ ≠ ⊥ := by
    intro h
    rw [h] at hR
    simp at hR
  have hRle : ∀ U : Subgroup W, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U ≠ ⊥ → cmt ζ ⊤ ≤ U := by
    intro U hU hUne
    have hne : cmt ζ U ≠ ⊥ := by
      intro h
      have htriv := acts_trivially_of_simple hsimp hU hζ hζ1 (cmt_eq_bot_iff.1 h)
      apply hUne
      rw [eq_bot_iff]
      intro u hu
      have : u ∈ fixV Λ := fun l hl => htriv l hl u hu
      rwa [hfixΛ] at this
    have heq : cmt ζ U = cmt ζ ⊤ :=
      PairData.eq_of_le_of_card_le_two (cmt_mono le_top) hne hR.le
    rw [← heq]
    exact cmt_le_of_invariant (hU ζ hζ)
  have htopne : (⊤ : Subgroup W) ≠ ⊥ := fun h => hR1 (by
    rw [h]
    exact Subgroup.map_bot _)
  let 𝒮 : Set (Subgroup W) := {U | (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) ∧ U ≠ ⊥}
  have htopS : (⊤ : Subgroup W) ∈ 𝒮 := ⟨fun l _ u _ => Subgroup.mem_top _, htopne⟩
  obtain ⟨U₀, ⟨hU₀, hU₀ne⟩, hmin⟩ :=
    Set.exists_min_image 𝒮 (fun U => Nat.card U) (Set.toFinite _) ⟨⊤, htopS⟩
  have hRU₀ : cmt ζ ⊤ ≤ U₀ := hRle U₀ hU₀ hU₀ne
  have hG₀ : ∀ g ∈ G, ∀ u ∈ U₀, g u ∈ U₀ := by
    intro g hg
    set gU : Subgroup W := U₀.map (g : MulAut W).toMonoidHom with hgU
    have hgUinv : ∀ l ∈ Λ, ∀ u ∈ gU, l u ∈ gU := by
      rintro l hl _ ⟨u, hu, rfl⟩
      exact ⟨(g⁻¹ * l * g) u, hU₀ _ (hnorm' g hg l hl) u hu, hcomm g l u⟩
    have hgcard : Nat.card gU = Nat.card U₀ :=
      Subgroup.card_map_of_injective (f := (g : MulAut W).toMonoidHom) (g : MulAut W).injective
    have hgUne : gU ≠ ⊥ := by
      intro h
      have : Nat.card gU = 1 := by rw [h]; exact Subgroup.card_bot
      have h1 : 1 < Nat.card U₀ := (Subgroup.one_lt_card_iff_ne_bot U₀).2 hU₀ne
      omega
    have hRgU : cmt ζ ⊤ ≤ gU := hRle gU hgUinv hgUne
    have hinter : U₀ ⊓ gU ∈ 𝒮 := by
      refine ⟨fun l hl u hu => ⟨hU₀ l hl u hu.1, hgUinv l hl u hu.2⟩, fun h => hR1 ?_⟩
      rw [eq_bot_iff]
      exact (le_inf hRU₀ hRgU).trans h.le
    have hc1 : Nat.card U₀ ≤ Nat.card ↥(U₀ ⊓ gU) := hmin _ hinter
    have heq1 : U₀ ⊓ gU = U₀ := Subgroup.eq_of_le_of_card_ge inf_le_left hc1
    have hle : U₀ ≤ gU := by
      rw [← heq1]
      exact inf_le_right
    have heq2 : U₀ = gU := Subgroup.eq_of_le_of_card_ge hle hgcard.le
    intro u hu
    have : g u ∈ gU := ⟨u, hu, rfl⟩
    rwa [← heq2] at this
  have hU₀top : U₀ = ⊤ := (hirr U₀ hG₀).resolve_left hU₀ne
  intro U hU
  by_cases hUne : U = ⊥
  · exact Or.inl hUne
  · right
    have hcard := hmin U ⟨hU, hUne⟩
    rw [hU₀top, Subgroup.card_top] at hcard
    exact Subgroup.eq_top_of_le_card U hcard

end CFSG.Quasithin.He7
