module

public import CFSG.Quasithin.EmptyFaithful.S152N10
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152O4Facts

public section

namespace CFSG.Quasithin.S152Z6

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152O4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem tau_core_fin : ∀ θ τ : Gam, θ ^ 2 = 1 → θ ≠ 1 → τ ^ 2 = 1 → θ * τ = τ * θ →
    (∀ u : Vec, act θ (act τ u * u⁻¹) = act τ u * u⁻¹) → τ = 1 ∨ τ = θ := by
  decide +kernel

private theorem tau_eq_of_omegaFourPlus {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (hX : IsOmegaFourPlus X) {θ τ : MulAut W} (hθX : θ ∈ X)
    (hτX : τ ∈ X) (hθ2 : θ * θ = 1) (hθ1 : θ ≠ 1) (hτ2 : τ * τ = 1) (hcomm : θ * τ = τ * θ)
    (hfix : ∀ v : W, θ (τ v * v⁻¹) = τ v * v⁻¹) : τ = 1 ∨ τ = θ := by
  obtain ⟨c, hc⟩ := om4_model hX
  obtain ⟨γθ, rfl⟩ := exists_rhoV_eq c hc hθX
  obtain ⟨γτ, rfl⟩ := exists_rhoV_eq c hc hτX
  have h1 : γθ ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one, pow_two]; exact hθ2)
  have h2 : γθ ≠ 1 := fun h => hθ1 (by rw [h, map_one])
  have h3 : γτ ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one, pow_two]; exact hτ2)
  have h4 : γθ * γτ = γτ * γθ := rhoV_injective c (by rw [map_mul, map_mul]; exact hcomm)
  have h5 : ∀ u : Vec, act γθ (act γτ u * u⁻¹) = act γτ u * u⁻¹ := by
    intro u
    have := congrArg c (hfix (c.symm u))
    rw [rhoV_apply, map_mul, rhoV_apply, map_inv, MulEquiv.apply_symm_apply] at this
    exact this
  rcases tau_core_fin γθ γτ h1 h2 h3 h4 h5 with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

section Claim

variable {T Mc M : Subgroup G}

private theorem tau_claim (hs : Setting152 T Mc M) (h15201 : Lemma15201Concl T Mc M)
    (hV : IsElemAbelian 2 (V154 T Mc M))
    {θ τ : MulAut (IntMod (V154 T Mc M) hV)} (hθT : θ ∈ autI hV T) (hτT : τ ∈ autI hV T)
    (hθ2 : θ * θ = 1) (hθ1 : θ ≠ 1) (hτ2 : τ * τ = 1)
    (hfix : ∀ v : IntMod (V154 T Mc M) hV, θ (τ v * v⁻¹) = τ v * v⁻¹) : τ = 1 ∨ τ = θ := by
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M)) :=
    B2F.isSylowTwoOf_autI hV hMN (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM)
  obtain ⟨hcomm, -⟩ := S152N.tbar_props hs h15201 hV
  have hθτ : θ * τ = τ * θ := hcomm θ hθT τ hτT
  have huniq : (∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 → b ^ 2 = 1 →
      a ≠ 1 → b ≠ 1 → a = b) → τ = 1 ∨ τ = θ := by
    intro hu
    by_cases hτ1 : τ = 1
    · exact Or.inl hτ1
    · exact Or.inr (hu τ hτT θ hθT ((pow_two τ).trans hτ2) ((pow_two θ).trans hθ2) hτ1 hθ1)
  have hsmall : ¬ 4 ∣ Nat.card (autOn M (V154 T Mc M)) → τ = 1 ∨ τ = θ := by
    intro h4
    apply huniq
    have hcard : Nat.card (autOn T (V154 T Mc M)) ≤ 2 :=
      S152N.card_le_two_of_dvd hsyl.2.1 (Subgroup.card_dvd_of_le hsyl.1) h4
    exact fun a ha b hb _ _ ha1 hb1 => S152N.eq_of_card_le_two hcard ha hb ha1 hb1
  rcases h15201.cases with ⟨-, hA, ⟨e⟩⟩ | ⟨-, ⟨e⟩, ⟨e'⟩⟩ | ⟨-, hA, hΩ⟩ | ⟨-, ⟨e⟩, hT, -⟩
  ·
    refine hsmall ?_
    have : Nat.card (autOn M (V154 T Mc M)) = 6 := by
      rw [hA, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  ·
    refine hsmall ?_
    have : Nat.card (autOn M (V154 T Mc M)) = 18 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      have : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [this]
    omega
  ·
    obtain ⟨hV', hX⟩ := hΩ
    exact tau_eq_of_omegaFourPlus (W := IntMod (V154 T Mc M) hV) hX (autI_mono hV hTM hθT)
      (autI_mono hV hTM hτT) hθ2 hθ1 hτ2 hθτ hfix
  ·
    apply huniq
    have key : ∀ {n : ℕ} (f : ↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod n)),
        (∀ x y : Multiplicative (ZMod n), x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y) →
        ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 → b ^ 2 = 1 →
          a ≠ 1 → b ≠ 1 → a = b := by
      intro n f hall a ha b hb ha2 hb2 ha1 hb1
      have h1 : f ⟨a, ha⟩ ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨a, ha⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext ha2
        rw [this, map_one]
      have h2 : f ⟨b, hb⟩ ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨b, hb⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext hb2
        rw [this, map_one]
      have h3 : f ⟨a, ha⟩ ≠ 1 := fun h =>
        ha1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
      have h4 : f ⟨b, hb⟩ ≠ 1 := fun h =>
        hb1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
      exact congrArg Subtype.val (f.injective (hall _ _ h1 h2 h3 h4))
    rcases hT with hT | hT
    · obtain ⟨f⟩ := hT
      exact key f (by decide)
    · obtain ⟨f⟩ := hT
      exact key f (by decide)

end Claim

section Correction

variable {T Mc M : Subgroup G}

private theorem exists_correction (hs : Setting152 T Mc M) (h15201 : Lemma15201Concl T Mc M)
    {B : Subgroup G} (hBT : B ≤ T)
    (hB2 : (B ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex B = 2)
    {x : G} (hxT : x ∈ T) (hx2 : x * x = 1)
    (hcomm : ∀ v ∈ V154 T Mc M, ∀ b ∈ B,
      b * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * b) :
    ∃ b ∈ B, x * b ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hV := S152N.isElemAbelian_V154 hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hTM.trans (le_normalizer_V154 T Mc M)
  have hBN : B ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hBT.trans hTN
  have hcard : Nat.card (autI hV B) = 2 := by
    rw [card_autI_eq hV hBN]
    exact hB2
  obtain ⟨θ, hθB, hθ1, hθ2, -⟩ := exists_eq_zpowers_of_card_two hcard
  have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hTN hxT
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut (IntMod (V154 T Mc M) hV), τ = convI hV ⟨x, hxN⟩ := ⟨_, rfl⟩
  have hτT : τ ∈ autI hV T := hτ ▸ convI_mem_autI hV hxT hxN
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) * ⟨x, hxN⟩ = 1 :=
      Subtype.ext hx2
    rw [this, map_one]
  obtain ⟨b, hbB, hbθ⟩ := (mem_autI hV).1 hθB
  have hfix : ∀ v : IntMod (V154 T Mc M) hV, θ (τ v * v⁻¹) = τ v * v⁻¹ := by
    intro v
    apply IntMod.val_injective
    rw [← hbθ, convI_apply_val]
    have hw : (τ v * v⁻¹).val = x * v.val * x⁻¹ * v.val⁻¹ := by
      rw [IntMod.val_mul, IntMod.val_inv, hτ, convI_apply_val]
    rw [hw, mul_inv_eq_iff_eq_mul]
    exact hcomm v.val v.val_mem b hbB
  rcases tau_claim hs h15201 hV (autI_mono hV hBT hθB) hτT hθ2 hθ1 hτ2 hfix with h1 | h1
  · refine ⟨1, B.one_mem, ?_⟩
    rw [mul_one]
    exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 (hτ ▸ h1)
  · refine ⟨b, hbB, ?_⟩
    have h2 : convI hV (⟨x, hxN⟩ * b) = 1 := by
      rw [map_mul, hbθ, ← hτ, h1]
      exact hθ2
    exact (convI_eq_one_iff hV _).1 h2

end Correction

omit [Finite G] in
private theorem cjSub_conjSubgroup (A : Subgroup G) (g : G) : cjSub g (conjSubgroup A g) = A := by
  ext y
  rw [mem_cjSub, mem_conjSubgroup_iff]
  have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [this]

theorem tau_lemma {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h15201 : Lemma15201Concl T Mc M) (φ : OTwoQuot H ≃* S152N.W3)
    {B : Subgroup G} (hBQ : B ≤ pCoreOf 2 H) {h : G} (hh : h ∈ H)
    (hB2 : (B ⊓ Subgroup.centralizer (conjSubgroup (V154 T Mc M) h : Set G)).relIndex B = 2)
    (hC4 : Nat.card (conjSubgroup (V154 T Mc M) h) =
      4 * Nat.card ↥(conjSubgroup (V154 T Mc M) h ⊓ Subgroup.centralizer (B : Set G)))
    {x : G} (hxH : x ∈ H) (hxN : x ∈ Subgroup.normalizer (conjSubgroup (V154 T Mc M) h : Set G))
    (hx2 : x * x = 1)
    (hcomm : ⁅conjSubgroup (V154 T Mc M) h, Subgroup.zpowers x⁆ ≤
      conjSubgroup (V154 T Mc M) h ⊓ Subgroup.centralizer (B : Set G)) :
    ∃ b ∈ B, x * b ∈ Subgroup.centralizer (conjSubgroup (V154 T Mc M) h : Set G) := by
  have _ := hC4
  have hsyl := S152N.isSylowTwoOf_hStar hs hH
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hx'N : h * x * h⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.1 hxN (h⁻¹ * w * h)
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff] at h1
    have e1 : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    have e2 : h * (x * (h⁻¹ * w * h) * x⁻¹) * h⁻¹ = h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have hx'T : h * x * h⁻¹ ∈ T := by
    rw [← S152N.inf_normalizer_eq_of_W3 hs hH φ]
    exact ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), hx'N⟩
  have hB'T : cjSub h B ≤ T := (cjSub_le (le_normalizer_pCoreOf 2 H hh) hBQ).trans hQT
  have hB'2 : (cjSub h B ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex (cjSub h B) = 2 := by
    have e : cjSub h B ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
        cjSub h (B ⊓ Subgroup.centralizer (conjSubgroup (V154 T Mc M) h : Set G)) := by
      rw [B2F.cjSub_inf, B2F.cjSub_centralizer, cjSub_conjSubgroup]
    rw [e]
    exact (Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective).trans hB2
  have hx'2 : h * x * h⁻¹ * (h * x * h⁻¹) = 1 := by
    have : h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
    rw [this, hx2]
    group
  have hcomm' : ∀ v ∈ V154 T Mc M, ∀ b ∈ cjSub h B,
      b * (h * x * h⁻¹ * v * (h * x * h⁻¹)⁻¹ * v⁻¹) =
        (h * x * h⁻¹ * v * (h * x * h⁻¹)⁻¹ * v⁻¹) * b := by
    intro v hv b hb
    have hv' : h⁻¹ * v * h ∈ conjSubgroup (V154 T Mc M) h := by
      rw [mem_conjSubgroup_iff]
      have : h * (h⁻¹ * v * h) * h⁻¹ = v := by group
      rwa [this]
    have hxz : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have h1 : ⁅h⁻¹ * v * h, x⁆ ∈ Subgroup.centralizer (B : Set G) :=
      (hcomm (Subgroup.commutator_mem_commutator hv' hxz)).2
    have h2 : ⁅x, h⁻¹ * v * h⁆ ∈ Subgroup.centralizer (B : Set G) := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ h1
    have h3 := Subgroup.mem_centralizer_iff.1 h2 (h⁻¹ * b * h) (mem_cjSub.1 hb)
    rw [commutatorElement_def] at h3
    have h4 := congrArg (fun t => h * t * h⁻¹) h3
    have e1 : b * (h * x * h⁻¹ * v * (h * x * h⁻¹)⁻¹ * v⁻¹) =
        h * (h⁻¹ * b * h * (x * (h⁻¹ * v * h) * x⁻¹ * (h⁻¹ * v * h)⁻¹)) * h⁻¹ := by group
    have e2 : (h * x * h⁻¹ * v * (h * x * h⁻¹)⁻¹ * v⁻¹) * b =
        h * (x * (h⁻¹ * v * h) * x⁻¹ * (h⁻¹ * v * h)⁻¹ * (h⁻¹ * b * h)) * h⁻¹ := by group
    rw [e1, e2]
    exact h4
  obtain ⟨b', hb'B', hb'⟩ := exists_correction hs h15201 hB'T hB'2 hx'T hx'2 hcomm'
  refine ⟨h⁻¹ * b' * h, mem_cjSub.1 hb'B', ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hu : h * w * h⁻¹ ∈ V154 T Mc M := mem_conjSubgroup_iff.1 hw
  have h5 := Subgroup.mem_centralizer_iff.1 hb' _ hu
  have h6 := congrArg (fun t => h⁻¹ * t * h) h5
  have e1 : w * (x * (h⁻¹ * b' * h)) = h⁻¹ * ((h * w * h⁻¹) * (h * x * h⁻¹ * b')) * h := by group
  have e2 : x * (h⁻¹ * b' * h) * w = h⁻¹ * ((h * x * h⁻¹ * b') * (h * w * h⁻¹)) * h := by group
  rw [e1, e2]
  exact h6

end CFSG.Quasithin.S152Z6
