module

public import CFSG.Quasithin.MS93.S46I467TLab

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open scoped Matrix

section Transv

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

theorem ffSplitT (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    {t : SL3 F} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV ((Subgroup.zpowers t).map ρ))) :
    commV ρ.range ⊔ fixV ρ.range = ⊤ := by
  by_cases hnt : ∃ g x, ρ g x ≠ x
  swap
  · push Not at hnt
    rw [eq_top_iff]
    intro x _
    refine Subgroup.mem_sup_right ?_
    rintro _ ⟨g, rfl⟩
    exact hnt g x
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  set B : Subgroup (SL3 F) := Subgroup.zpowers t with hBdef
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := zpowers_sq_eq_one ht2'
  have hB : B ≠ ⊥ := by
    intro h
    apply ht1
    have : t ∈ B := Subgroup.mem_zpowers t
    rwa [h, Subgroup.mem_bot] at this
  set Y := commV ρ.range with hYdef
  have hYinv : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y := fun g x hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, -, hM₀Y, hirrS, hntS⟩ := exists_irr_sec ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le
    (commV_range_ne_bot ρ hnt).symm
  set ρS := secRho ρ hYinv hM₀inv with hρS
  set A : Subgroup (MulAut X) := B.map ρ with hA
  have hAK : A ≤ ρ.range := Subgroup.map_le_range ρ B
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hcX : Nat.card (commV A) ≤ Nat.card F := by
    have h1 : Nat.card (commV A) * Nat.card (fixV A) = Nat.card X := by
      rw [hA, hBdef, MonoidHom.map_zpowers]
      exact card_commV_mul_card_fixV_zpowers (ρ t)
    have h0 : 0 < Nat.card (fixV A) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ h0
    rw [h1]
    exact hidx
  have hcS : Nat.card (commV (Subgroup.zpowers (ρS t))) ≤ Nat.card F := by
    have h1 := card_commV_sec_le ρ hYinv hM₀inv hM₀Y B
    have e : Subgroup.zpowers (ρS t) = B.map ρS := by rw [hBdef, MonoidHom.map_zpowers]
    rw [e]
    exact h1.trans hcX
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ : ∃ (F' : Type) (_ : Field F') (_ : Finite F'),
      Nat.card F' = Nat.card F ∧ ∃ (σ : SL3 F' ≃* ↥ρS.range)
        (θ : Sec Y M₀ ≃* Multiplicative (Fin 3 → F')), IsNatCoord σ θ := by
    rcases natCoord_or_large hF (sec_sq hX2) ρS hirrS hntS ht1 ht2 with ⟨σ, θ, hθ⟩ | hbig
    · exact ⟨F, inferInstance, inferInstance, rfl, σ, θ, hθ⟩
    · exfalso
      have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
      nlinarith [hbig.trans hcS]
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF)
  have hb := S4A.F.card_mul_card_fixV_le hθ (Subgroup.map_le_range ρS B)
    (map_ne_bot ρS hntS hB hB2)
  rw [hFF', hρS, map_secRho] at hb
  have hAY : A ≤ stabSub Y := hAK.trans (range_le_stabSub ρ hYinv)
  have hd := card_inf_fixV_le_autSec hM₀Y hAY (U := M₀)
  have hcs := card_sec_mul hM₀Y
  have he := card_sup_mul_card_inf Y (fixV A)
  have hfu : Nat.card ↥(Y ⊔ fixV A) ≤ Nat.card X := Subgroup.card_le_card_group _
  have hmc : Nat.card ↥(M₀ ⊓ fixV A) ≤ Nat.card M₀ := Subgroup.card_le_of_le inf_le_left
  have hc0 : 0 < Nat.card (fixV A) := Nat.card_pos
  have hcs0 : 0 < Nat.card (fixV (autSec A Y M₀)) := Nat.card_pos
  have hq0 : 0 < Nat.card F := Nat.card_pos
  have hi0 : 0 < Nat.card ↥(Y ⊓ fixV A) := Nat.card_pos
  have h1 : Nat.card Y ≤ Nat.card F * Nat.card (fixV (autSec A Y M₀)) *
      Nat.card ↥(M₀ ⊓ fixV A) := by
    refine Nat.le_of_mul_le_mul_right ?_ hc0
    calc Nat.card Y * Nat.card (fixV A) = Nat.card ↥(Y ⊔ fixV A) * Nat.card ↥(Y ⊓ fixV A) :=
          he.symm
      _ ≤ (Nat.card F * Nat.card (fixV A)) *
            (Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A)) :=
          Nat.mul_le_mul (hfu.trans hidx) hd
      _ = Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A) *
            Nat.card (fixV A) := by ring
  have h2 : Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card M₀ ≤ Nat.card Y := by
    rw [← hcs]
    exact Nat.mul_le_mul_right _ hb
  have hpos : 0 < Nat.card F * Nat.card (fixV (autSec A Y M₀)) := Nat.mul_pos hq0 hcs0
  have hmm : Nat.card M₀ ≤ Nat.card ↥(M₀ ⊓ fixV A) :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) hpos
  have hM₀A : M₀ ≤ fixV A := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : M₀ ⊓ fixV A ≤ M₀) hmm
    rw [← this]
    exact inf_le_right
  have hM₀fix : ∀ g, ∀ m ∈ M₀, ρ g m = m :=
    fix_of_fix ρ hM₀inv hB hB2 fun b hb m hm => hM₀A hm (ρ b) ⟨b, hb, rfl⟩
  have hYC : Y ⊔ fixV A = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    refine le_antisymm hfu ?_
    refine Nat.le_of_mul_le_mul_right ?_ hi0
    calc Nat.card X * Nat.card ↥(Y ⊓ fixV A)
        ≤ (Nat.card F * Nat.card (fixV A)) *
            (Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A)) :=
          Nat.mul_le_mul hidx hd
      _ = Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A) *
            Nat.card (fixV A) := by ring
      _ ≤ Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card M₀ * Nat.card (fixV A) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmc)
      _ ≤ Nat.card Y * Nat.card (fixV A) := Nat.mul_le_mul_right _ h2
      _ = Nat.card ↥(Y ⊔ fixV A) * Nat.card ↥(Y ⊓ fixV A) := he.symm
  set τ : SL3 F →* SL3 F' := σ.symm.toMonoidHom.comp ρS.rangeRestrict with hτ
  have hτs : Function.Surjective τ :=
    σ.symm.surjective.comp ρS.rangeRestrict_surjective
  have hστ : ∀ g, (σ (τ g) : MulAut (Sec Y M₀)) = ρS g := by
    intro g
    simp [hτ]
  have hτc : ∀ k, τ k = 1 → k ^ 3 = 1 := by
    intro k hk
    have h1 : ρS k = 1 := by rw [← hστ k, hk, map_one]; rfl
    exact pow_three_eq_one_of_mem_center (ker_le_center ρS hntS (MonoidHom.mem_ker.mpr h1))
  have hBτ : B.map τ ≠ ⊥ := by
    intro hbot
    apply hB
    rw [← inf_eq_left.mpr (show B ≤ ρS.ker from fun b hb => by
      have h1 : τ b = 1 := by
        have : τ b ∈ B.map τ := ⟨b, hb, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at this
      rw [MonoidHom.mem_ker, ← hστ b, h1, map_one]
      rfl)]
    exact inf_ker_eq_bot ρS hntS hB2
  set π : ↥Y →* Multiplicative (Fin 3 → F') :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (M₀.subgroupOf Y)) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : ∀ u : ↥Y, π u = 1 → (u : X) ∈ M₀ := by
    intro u hu
    have h1 : (QuotientGroup.mk' (M₀.subgroupOf Y) u) = 1 := θ.injective (by rw [map_one]; exact hu)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have hπe : ∀ g (u : ↥Y), π (resRho ρ Y hYinv g u) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (π u)) := by
    intro g u
    have h1 : QuotientGroup.mk' (M₀.subgroupOf Y) (resRho ρ Y hYinv g u) =
        (σ (τ g) : MulAut (Sec Y M₀)) (QuotientGroup.mk' (M₀.subgroupOf Y) u) := by
      rw [hστ]
      rfl
    simp only [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, hθ]
  have hfixY : ∀ y ∈ fixV A, y ∈ Y ⊔ fixV ρ.range := by
    intro y hy
    obtain ⟨u, huY, hu⟩ := exists_fix_of_cocycle ρ hYinv hM₀fix τ hτs hτc π hπs hπk hπe
      (isPGroup_of_sq hB2) hBτ (y := y) (fun g => Subgroup.subset_closure
        ⟨ρ g, mem_range_apply ρ g, y, rfl⟩) fun t ht => hy (ρ t) ⟨t, ht, rfl⟩
    have e : y = (y * u⁻¹) * u := by group
    rw [e, mul_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huY) (Subgroup.mem_sup_right hu)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Y ⊔ fixV A := by rw [hYC]; trivial
  obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy₁) (hfixY c₁ hc₁)



theorem transvDecomp (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1)
    (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x) {t : SL3 F} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hcomm : Nat.card (commV ((Subgroup.zpowers t).map ρ)) ≤ Nat.card F) :
    commV ρ.range ⊓ fixV ρ.range = ⊥ ∧ commV ρ.range ⊔ fixV ρ.range = ⊤ ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : SL3 F →* SL3 F') (θ : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ ∀ g (p : ↥(commV ρ.range)),
            θ (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) g p) =
              Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (θ p)) := by
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  set B : Subgroup (SL3 F) := Subgroup.zpowers t with hBdef
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := zpowers_sq_eq_one ht2'
  have hB : B ≠ ⊥ := by
    intro h
    apply ht1
    have : t ∈ B := Subgroup.mem_zpowers t
    rwa [h, Subgroup.mem_bot] at this
  set P := commV ρ.range with hPdef
  set C := fixV ρ.range with hCdef
  have hPinv : ∀ g, ∀ x ∈ P, ρ g x ∈ P := fun g _ hx => commV_inv ρ g hx
  have hPC : P ⊓ C = ⊥ := by
    have hidx : Nat.card (DualGrp X) ≤ Nat.card F * Nat.card (fixV (B.map (dualRho ρ))) := by
      rw [fixV_map_dualRho, card_dualGrp hX2, ← dualAnn_card hX2 (commV (B.map ρ)), mul_comm]
      exact Nat.mul_le_mul_right _ hcomm
    have hsplit := ffSplitT hF dualGrp_sq (dualRho ρ) ht1 ht2 hidx
    rw [commV_range_dualRho hX2, fixV_range_dualRho] at hsplit
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨f, hf⟩ := exists_dualChar_ne_one hX2 hx1
    have hf' : f ∈ dualAnn C ⊔ dualAnn P := by rw [hsplit]; trivial
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Subgroup.mem_sup.mp hf'
    apply hf
    change f₁ x * f₂ x = 1
    rw [hf₁ x hx.2, hf₂ x hx.1, mul_one]
  have hirrP : ∀ J : Subgroup X, (∀ g, ∀ u ∈ J, ρ g u ∈ J) → J ≤ P → J = ⊥ ∨ J = P := by
    intro J hJ hJP
    by_cases hJe : J = P
    · exact Or.inr hJe
    left
    obtain ⟨M₀, hM₀inv, hJM₀, hM₀P, -, hntS⟩ := exists_irr_sec ρ hJ hJP hJe
    have hlow : Nat.card F ≤ Nat.card (commV (B.map (secRho ρ hPinv hM₀inv))) := by
      have := le_card_commV_zpowers hF (sec_sq hX2) (secRho ρ hPinv hM₀inv) hntS ht1 ht2
      rwa [hBdef, MonoidHom.map_zpowers]
    have hmul := card_commV_sec_mul_le ρ hPinv hM₀inv hM₀P B
    have hle := Subgroup.card_le_of_le (commOn_le_commV (B.map ρ) P)
    have h1 : Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀) ≤ 1 := by
      have hq0 : 0 < Nat.card F := Nat.card_pos
      refine Nat.le_of_mul_le_mul_left ?_ hq0
      calc Nat.card F * Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀)
          ≤ Nat.card (commV (B.map (secRho ρ hPinv hM₀inv))) *
              Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀) := Nat.mul_le_mul_right _ hlow
        _ ≤ Nat.card (G6.commOn (B.map ρ) P) := hmul
        _ ≤ Nat.card F * 1 := by rw [mul_one]; exact hle.trans hcomm
    have h2 : G6.commOn (B.map ρ) P ⊓ M₀ = ⊥ := Subgroup.eq_bot_of_card_le _ h1
    have hBM : ∀ b ∈ B, ∀ m ∈ M₀, ρ b m = m := by
      intro b hb m hm
      have h3 : ρ b m * m⁻¹ ∈ G6.commOn (B.map ρ) P ⊓ M₀ :=
        ⟨Subgroup.subset_closure ⟨ρ b, ⟨b, hb, rfl⟩, m, hM₀P hm, rfl⟩,
          M₀.mul_mem (hM₀inv b m hm) (M₀.inv_mem hm)⟩
      rw [h2, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact h3
    have hM₀fix := fix_of_fix ρ hM₀inv hB hB2 hBM
    have hM₀C : M₀ ≤ P ⊓ C := fun m hm => ⟨hM₀P hm, by rintro _ ⟨g, rfl⟩; exact hM₀fix g m hm⟩
    rw [hPC] at hM₀C
    exact eq_bot_iff.mpr (hJM₀.trans hM₀C)
  set ρP := resRho ρ P hPinv with hρP
  have hirrP' : ∀ W : Subgroup ↥P, (∀ g : SL3 F, ∀ w ∈ W, ρP g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinv : ∀ g, ∀ u ∈ W.map P.subtype, ρ g u ∈ W.map P.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨ρP g w, hW g w hw, rfl⟩
    rcases hirrP _ hinv (Subgroup.map_subtype_le W) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : X) ∈ W.map P.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', he⟩ := hw
      rwa [← Subtype.ext he]
  have hntP : ∃ g p, ρP g p ≠ p := by
    by_contra hcon
    push Not at hcon
    apply commV_range_ne_bot ρ hnt
    rw [eq_bot_iff]
    refine commV_le_of_isPerfect ρ fun g x hx => ?_
    have h1 := congrArg Subtype.val (hcon g ⟨x, hx⟩)
    rw [coe_resRho_apply] at h1
    rw [Subgroup.mem_bot, h1, mul_inv_cancel]
  have hcommP : Nat.card (commV (B.map ρP)) ≤ Nat.card (commV (B.map ρ)) := by
    have hle : (commV (B.map ρP)).map P.subtype ≤ commV (B.map ρ) := by
      rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨b, hb, rfl⟩, p, rfl⟩
      exact Subgroup.subset_closure ⟨ρ b, ⟨b, hb, rfl⟩, p, rfl⟩
    rw [← Subgroup.card_map_of_injective P.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hP2 : ∀ p : ↥P, p ^ 2 = 1 := fun p => Subtype.ext (by
    rw [Subgroup.coe_pow, hX2, Subgroup.coe_one])
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ : ∃ (F' : Type) (_ : Field F') (_ : Finite F'),
      Nat.card F' = Nat.card F ∧ ∃ (σ : SL3 F' ≃* ↥ρP.range)
        (θ : ↥P ≃* Multiplicative (Fin 3 → F')), IsNatCoord σ θ := by
    rcases natCoord_or_large hF hP2 ρP hirrP' hntP ht1 ht2 with ⟨σ, θ, hθ⟩ | hbig
    · exact ⟨F, inferInstance, inferInstance, rfl, σ, θ, hθ⟩
    · exfalso
      have h1 : Nat.card (commV (Subgroup.zpowers (ρP t))) ≤ Nat.card F := by
        have e : Subgroup.zpowers (ρP t) = B.map ρP := by rw [hBdef, MonoidHom.map_zpowers]
        rw [e]
        exact hcommP.trans hcomm
      have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
      nlinarith [hbig.trans h1]
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF)
  set τ : SL3 F →* SL3 F' := σ.symm.toMonoidHom.comp ρP.rangeRestrict with hτ
  have hτs : Function.Surjective τ := σ.symm.surjective.comp ρP.rangeRestrict_surjective
  have hστ : ∀ g, (σ (τ g) : MulAut ↥P) = ρP g := by
    intro g
    simp [hτ]
  have hτe : ∀ g (p : ↥P), θ (ρP g p) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (θ p)) := by
    intro g p
    rw [← hστ g, hθ]
  have hτc : ∀ k, τ k = 1 → k ^ 3 = 1 := by
    intro k hk
    have h1 : ρP k = 1 := by rw [← hστ k, hk, map_one]; rfl
    exact pow_three_eq_one_of_mem_center (ker_le_center ρP hntP (MonoidHom.mem_ker.mpr h1))
  refine ⟨hPC, ?_, F', iF', fF', hFF', τ, θ, hτs, hτe⟩
  have htB : t ∈ B := Subgroup.mem_zpowers t
  have ht1' : t ≠ 1 := ht1
  have hτt : τ t ≠ 1 := by
    intro h
    apply ht1'
    have h3 := hτc t h
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, ht2', inv_one, one_mul]
  set δ : ↥P →* ↥P :=
    { toFun := fun p => ρP t p * p⁻¹
      map_one' := by simp
      map_mul' := fun p p' => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ } with hδ
  set ℓ : (Fin 3 → F') →ₗ[F'] (Fin 3 → F') :=
    Matrix.mulVecLin ((τ t : SL3 F') : Matrix (Fin 3) (Fin 3) F') - LinearMap.id with hℓ
  have hℓne : LinearMap.range ℓ ≠ ⊥ := by
    intro hbot
    apply hτt
    refine eq_one_of_mulVec_eq_self fun x => ?_
    have h1 : ℓ x ∈ LinearMap.range ℓ := LinearMap.mem_range_self ℓ x
    rw [hbot, Submodule.mem_bot, hℓ, LinearMap.sub_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply, sub_eq_zero] at h1
    exact h1
  have hTθ : ∀ v : ↥P, v ∈ δ.range ↔
      Multiplicative.toAdd (θ v) ∈ (LinearMap.range ℓ : Set (Fin 3 → F')) := by
    intro v
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨Multiplicative.toAdd (θ p), ?_⟩
      rw [hℓ, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
      show _ = Multiplicative.toAdd (θ (ρP t p * p⁻¹))
      rw [map_mul, map_inv, hτe, toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
    · rintro ⟨x, hx⟩
      refine ⟨θ.symm (Multiplicative.ofAdd x), θ.injective ?_⟩
      show θ (ρP t (θ.symm (Multiplicative.ofAdd x)) * (θ.symm (Multiplicative.ofAdd x))⁻¹) = θ v
      rw [map_mul, map_inv, hτe, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, ← hx, hℓ, LinearMap.sub_apply,
        Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_add_neg]
  have hTcard : Nat.card F ≤ Nat.card δ.range := by
    rw [card_eq_of_coord θ hTθ, ← hFF']
    exact card_le_of_ne_bot hℓne
  have hTle : δ.range.map P.subtype ≤ commV (B.map ρ) := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨ρ t, ⟨t, htB, rfl⟩, p, rfl⟩
  have hTeq : δ.range.map P.subtype = commV (B.map ρ) := by
    refine Subgroup.eq_of_le_of_card_ge hTle ?_
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hcomm.trans hTcard
  have hzt2 := zpowers_sq_eq_one ht2'
  have hztτ : (Subgroup.zpowers t).map τ ≠ ⊥ := by
    intro hbot
    apply hτt
    have : τ t ∈ (Subgroup.zpowers t).map τ := ⟨t, Subgroup.mem_zpowers t, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  rw [eq_top_iff]
  intro x _
  have hx : ρ t x * x⁻¹ ∈ δ.range.map P.subtype := by
    rw [hTeq]
    exact Subgroup.subset_closure ⟨ρ t, ⟨t, htB, rfl⟩, x, rfl⟩
  obtain ⟨_, ⟨p, rfl⟩, hpx⟩ := hx
  set w : X := x * (p : X)⁻¹ with hw
  have hpx' : ρ t p * (p : X)⁻¹ = ρ t x * x⁻¹ := hpx
  have hwt : ρ t w = w := by
    rw [hw, map_mul, map_inv]
    have e : ρ t x = (ρ t p * (p : X)⁻¹) * x := by rw [hpx', inv_mul_cancel_right]
    rw [e]
    simp only [mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨u, huP, hu⟩ := exists_fix_of_cocycle ρ hPinv (M₀ := ⊥)
    (fun _ m hm => by rw [Subgroup.mem_bot.mp hm, map_one]) τ hτs hτc θ.toMonoidHom θ.surjective
    (fun u hu => by
      rw [Subgroup.mem_bot]
      have : u = 1 := θ.injective (by rw [map_one]; exact hu)
      rw [this, Subgroup.coe_one]) hτe (isPGroup_of_sq hzt2) hztτ (y := w)
    (fun g => Subgroup.subset_closure ⟨ρ g, mem_range_apply ρ g, w, rfl⟩) (by
      rintro _ ⟨k, rfl⟩
      rw [map_zpow]
      have hst : ρ t ∈ MulAction.stabilizer (MulAut X) w := hwt
      exact (Subgroup.zpowers_le.mpr hst) ⟨k, rfl⟩)
  have e : x = (w * u⁻¹) * (u * p) := by rw [hw]; group
  rw [e, mul_comm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (P.mul_mem huP p.2)) (Subgroup.mem_sup_right hu)


end Transv

end CFSG.Quasithin.MS93.S4A.F
