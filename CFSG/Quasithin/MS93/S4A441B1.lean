module

public import CFSG.Quasithin.MS93.M16Main
public import CFSG.Quasithin.MS93.M16Dual
public import CFSG.Quasithin.MS93.M16Split

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.Quasithin.MS93 Matrix

open M16 in
theorem ms16_of_nontrivial {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ρ : SL3 F →* MulAut V}
    (hρ : ∃ (g : SL3 F) (v : V), ρ g v ≠ v) {W₀ : Subgroup V}
    (hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀)
    (hgen : G6.submoduleClosure ρ.range W₀ = ⊤)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
      Nat.card F) :
    wOff ρ W₀ ⊔ fixV ρ.range = ⊤ ∧ commV ρ.range ⊓ fixV ρ.range = ⊥ ∧
      commV ρ.range ⊔ fixV ρ.range = ⊤ ∧
      ∃ (dual : Bool) (β : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F)),
        Function.Bijective β ∧
        ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
          Multiplicative.toAdd (β w) =
            (if dual then dualMat g else ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
              Multiplicative.toAdd (β v) := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  set Z := fixV ρ.range with hZdef
  have hZ : ∀ g : SL3 F, ∀ z ∈ Z, ρ g z ∈ Z := fun g _ hz => rho_mem_fixV ρ g hz
  set π := QuotientGroup.mk' Z with hπ
  set ρ' := quotAct ρ Z hZ with hρ'
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπρ : ∀ (g : SL3 F) (v : V), π (ρ g v) = ρ' g (π v) := fun _ _ => rfl
  have hV' : ∀ x : V ⧸ Z, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hV, QuotientGroup.mk_one]
  have hVne : (⊤ : Subgroup (V ⧸ Z)) ≠ ⊥ := by
    intro htop
    obtain ⟨g, v, hgv⟩ := hρ
    apply hgv
    have h1 : (π v : V ⧸ Z) = 1 := by
      have := Subgroup.mem_top (π v)
      rw [htop, Subgroup.mem_bot] at this
      exact this
    have hvZ : v ∈ Z := (QuotientGroup.eq_one_iff v).mp h1
    exact (mem_fixV_range.mp hvZ) g
  have hfixV' : fixV ρ'.range = ⊥ := fixV_quotAct_eq_bot
  have hW₀' : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀.map π, ρ' g w ∈ W₀.map π := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨ρ g w, hW₀ g hg w hw, rfl⟩
  have hgen' : G6.submoduleClosure ρ'.range (W₀.map π) = ⊤ := by
    rw [← map_mk_submoduleClosure hZ, hgen, Subgroup.map_top_of_surjective _ hπs]
  have hR' : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ')
      (wOff ρ' (W₀.map π))) ≤ Nat.card F := by
    rw [← map_mk_wOff hZ, ← map_mk_commOn hZ]
    exact (card_map_le' _ _).trans hR
  obtain ⟨hW', hC', dual, β', hβ'⟩ := core hV' hVne hfixV' hW₀' hgen' hR'
  have hWZ : wOff ρ W₀ ⊔ Z = ⊤ := sup_eq_top_of_map_mk (by rw [map_mk_wOff hZ]; exact hW')
  have hCmap : (commV ρ.range).map π = ⊤ := by rw [map_mk_commV hZ]; exact hC'
  have hCZ : commV ρ.range ⊔ Z = ⊤ := sup_eq_top_of_map_mk hCmap
  have hmem : ∀ c : ↥(commV ρ.range), π (c : V) ∈ commV ρ'.range := fun c => by
    rw [← map_mk_commV hZ]; exact Subgroup.mem_map_of_mem _ c.2
  set φ : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F) :=
    β'.toMonoidHom.comp ((π.comp (commV ρ.range).subtype).codRestrict _ hmem) with hφ
  have hφapp : ∀ c : ↥(commV ρ.range), φ c = β' ⟨π c, hmem c⟩ := fun _ => rfl
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨⟨x, hx⟩, hxy⟩ := β'.surjective y
    rw [← map_mk_commV hZ] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨⟨c, hc⟩, by rw [hφapp, ← hxy]⟩
  have hφeq : ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
      Multiplicative.toAdd (φ w) =
        (if dual then dualMat g else ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
          Multiplicative.toAdd (φ v) := by
    intro g v w hvw
    rw [hφapp, hφapp]
    exact hβ' g _ _ (by change π w = ρ' g (π v); rw [hvw]; exact hπρ g v)
  have hRC : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (commV ρ.range)) ≤
      Nat.card F :=
    (Subgroup.card_le_of_le (commOn_le_of_sup_fixV (hWZ ▸ le_top))).trans hR
  have hinj : Function.Injective φ := by
    cases dual
    · refine injective_of_natural_quotient rfl hCZ hRC φ hφs fun g v w hvw => ?_
      simpa using hφeq g v w hvw
    · have hrange := range_comp_transposeInv ρ
      refine injective_of_natural_quotient (ρ := ρ.comp transposeInv) (by rw [hrange])
        (by rw [hrange]; exact hCZ) ?_ φ hφs fun g v w hvw => ?_
      · have hX : (rootGroup 0 2 : Subgroup (SL3 F)).map (ρ.comp transposeInv) =
            (rootGroup 2 0 : Subgroup (SL3 F)).map ρ := by
          rw [← Subgroup.map_map, map_transposeInv_rootGroup]
        have hconj := rootGroup_conj_pmat (F := F) (Equiv.swap 0 2) 0 2
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at hconj
        have hmap := map_commOn_eq (ρ := ρ) (A := commV ρ.range) hconj.1 hconj.2
          (map_rho_eq_self (fun g c hc => rho_mem_commV ρ g hc) _)
        rw [hX, ← hmap, Subgroup.card_map_of_injective (ρ _).injective]
        exact hRC
      · have h := hφeq (transposeInv g) v w hvw
        simp only [↓reduceIte] at h
        rw [h, ← coe_transposeInv, transposeInv_transposeInv]
  refine ⟨hWZ, ?_, hCZ, dual, φ, ⟨hinj, hφs⟩, hφeq⟩
  rw [eq_bot_iff]
  intro v ⟨hvC, hvZ⟩
  have h1 : φ ⟨v, hvC⟩ = 1 := by
    rw [hφapp]
    have : (⟨π v, hmem ⟨v, hvC⟩⟩ : ↥(commV ρ'.range)) = 1 :=
      Subtype.ext ((QuotientGroup.eq_one_iff v).mpr hvZ)
    rw [this, map_one]
  have h2 := hinj (h1.trans (map_one φ).symm)
  exact congrArg Subtype.val h2

end CFSG.Quasithin.MS93.S4A.C441
