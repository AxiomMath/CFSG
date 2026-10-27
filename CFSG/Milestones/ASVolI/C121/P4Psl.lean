module

public import CFSG.Milestones.ASVolI.C121.P4Glob
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.C126NatSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Lift
  CFSG.QuasithinUnique.Setup.Offender
open scoped MatrixGroups Matrix LinearAlgebra.Projectivization

section Simple

variable {F : Type} [Field F] [Fintype F]

theorem burnsideC121_p4_isSimpleGroup_sl2 {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n) :
    IsSimpleGroup SL(2, F) := by
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hFc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr (C126.Nat.exists_finset_card_four h4))
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq B42L2.center_sl2_eq_bot).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e₂.symm

theorem burnsideC121_p4_isPerfect_sl2 {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n) :
    Group.IsPerfect SL(2, F) := by
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hFc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect (C126.Nat.exists_finset_card_four h4)

end Simple

section Module

variable {𝕎 : Type} [CommGroup 𝕎] [Finite 𝕎]

theorem burnsideC121_p4_normal_cases {G : Subgroup (MulAut 𝕎)} [IsSimpleGroup ↥G]
    (N : Subgroup (MulAut 𝕎)) (hNG : N ≤ G) (hN : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    N = ⊥ ∨ N = G := by
  have hnorm : (N.subgroupOf G).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hN g g.2 x hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf G) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNG hx⟩ : ↥G) ∈ N.subgroupOf G := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hNG fun x hx => ?_
    have : (⟨x, hx⟩ : ↥G) ∈ N.subgroupOf G := by rw [h]; trivial
    exact this

theorem burnsideC121_p4_comm_aux {M : Type*} [CommGroup M] (a b c d : M) :
    (a * d⁻¹)⁻¹ * (b * d⁻¹ * (c * d⁻¹)) = (a * b⁻¹ * (c * d⁻¹)⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem burnsideC121_p4_perfect_two_step {G : Subgroup (MulAut 𝕎)}
    (hperf : commutator ↥G = ⊤) {U₁ J U₂ : Subgroup 𝕎} (hG₁ : G ≤ stabSub U₁)
    (h1 : G ≤ centSec U₁ J) (h3 : G ≤ centSec J U₂) : G ≤ centSec U₁ U₂ := by
  let d : ↥G →* (↥U₁ → Sec J U₂) :=
    { toFun := fun g u => QuotientGroup.mk ⟨(g : MulAut 𝕎) u * (u : 𝕎)⁻¹, (h1 g.2).2 u u.2⟩
      map_one' := by
        funext u
        show (QuotientGroup.mk _ : Sec J U₂) = 1
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simp
      map_mul' := by
        intro g h
        funext u
        show (QuotientGroup.mk _ : Sec J U₂) = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hb : (h : MulAut 𝕎) u * (u : 𝕎)⁻¹ ∈ J := (h1 h.2).2 u u.2
        have hgb := (h3 g.2).2 _ hb
        have key : (((⟨((g * h : ↥G) : MulAut 𝕎) u * (u : 𝕎)⁻¹, (h1 (g * h).2).2 u u.2⟩ : ↥J)⁻¹ *
            ((⟨(g : MulAut 𝕎) u * (u : 𝕎)⁻¹, (h1 g.2).2 u u.2⟩ : ↥J) *
            ⟨(h : MulAut 𝕎) u * (u : 𝕎)⁻¹, hb⟩) : ↥J) : 𝕎) =
            ((g : MulAut 𝕎) ((h : MulAut 𝕎) u * (u : 𝕎)⁻¹) *
              ((h : MulAut 𝕎) u * (u : 𝕎)⁻¹)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul, map_inv]
          exact burnsideC121_p4_comm_aux _ _ _ _
        rw [key]
        exact U₂.inv_mem hgb }
  have hker : d.ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker d
  intro g hg
  refine ⟨hG₁ hg, fun u hu => ?_⟩
  have h0 : d ⟨g, hg⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    trivial
  have := congrFun h0 ⟨u, hu⟩
  change (QuotientGroup.mk _ : Sec J U₂) = 1 at this
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  exact this

theorem burnsideC121_p4_le_stabSub {G : Subgroup (MulAut 𝕎)} {J : Subgroup 𝕎}
    (h : ∀ x ∈ G, ∀ w ∈ J, x w ∈ J) : G ≤ stabSub J := by
  intro g hg u
  refine ⟨fun hu => ?_, h g hg u⟩
  have := h g⁻¹ (G.inv_mem hg) _ hu
  simpa using this

theorem burnsideC121_p4_exists_irr_section {G : Subgroup (MulAut 𝕎)}
    (hperf : commutator ↥G = ⊤) (hG1 : G ≠ ⊥) :
    ∃ U₁ U₂ : Subgroup 𝕎, U₂ ≤ U₁ ∧ G ≤ stabSub U₁ ∧ G ≤ stabSub U₂ ∧ ¬ G ≤ centSec U₁ U₂ ∧
      ∀ J : Subgroup 𝕎, (∀ x ∈ G, ∀ w ∈ J, x w ∈ J) → U₂ ≤ J → J ≤ U₁ → J = U₂ ∨ J = U₁ := by
  classical
  let P : Set (Subgroup 𝕎 × Subgroup 𝕎) :=
    {p | p.2 ≤ p.1 ∧ G ≤ stabSub p.1 ∧ G ≤ stabSub p.2 ∧ ¬ G ≤ centSec p.1 p.2}
  have hP : ((⊤ : Subgroup 𝕎), (⊥ : Subgroup 𝕎)) ∈ P := by
    refine ⟨bot_le, fun g _ u => by simp, fun g _ u => by simp, fun hle => hG1 ?_⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    have := (hle hg).2 w (Subgroup.mem_top w)
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image P (fun p => p.2.relIndex p.1) (Set.toFinite P)
    ⟨_, hP⟩
  obtain ⟨U₁, U₂⟩ := p
  obtain ⟨hU, hG₁, hG₂, hnt⟩ := hp
  refine ⟨U₁, U₂, hU, hG₁, hG₂, hnt, fun J hJ h2J hJ1 => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne2, hne1⟩ := hne
  have hGJ : G ≤ stabSub J := burnsideC121_p4_le_stabSub hJ
  have hlt2 : U₂ < J := lt_of_le_of_ne h2J (Ne.symm hne2)
  have hlt1 : J < U₁ := lt_of_le_of_ne hJ1 hne1
  have hmul := Subgroup.relIndex_mul_relIndex U₂ J U₁ h2J hJ1
  have hpos1 : 0 < U₂.relIndex J :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := U₂.subgroupOf J))
  have hpos2 : 0 < J.relIndex U₁ :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := J.subgroupOf U₁))
  have hne1' : U₂.relIndex J ≠ 1 := fun h => hne2 (le_antisymm (Subgroup.relIndex_eq_one.1 h) h2J)
  have hne2' : J.relIndex U₁ ≠ 1 := fun h => hne1 (le_antisymm hJ1 (Subgroup.relIndex_eq_one.1 h))
  have hA : G ≤ centSec J U₂ := by
    by_contra hc
    have h0 := hmin (J, U₂) ⟨h2J, hGJ, hG₂, hc⟩
    simp only at h0
    rw [← hmul] at h0
    have h1 : U₂.relIndex J * J.relIndex U₁ ≤ U₂.relIndex J * 1 := by rw [mul_one]; exact h0
    have h2 := Nat.le_of_mul_le_mul_left h1 hpos1
    omega
  have hB : G ≤ centSec U₁ J := by
    by_contra hc
    have h0 := hmin (U₁, J) ⟨hJ1, hG₁, hGJ, hc⟩
    simp only at h0
    rw [← hmul] at h0
    have h1 : U₂.relIndex J * J.relIndex U₁ ≤ 1 * J.relIndex U₁ := by rw [one_mul]; exact h0
    have h2 := Nat.le_of_mul_le_mul_right h1 hpos2
    omega
  exact hnt (burnsideC121_p4_perfect_two_step hperf hG₁ hB hA)

theorem burnsideC121_p4_sec_offender {U₁ U₂ : Subgroup 𝕎} (hU : U₂ ≤ U₁)
    {A : Subgroup (MulAut 𝕎)} (hAU₁ : A ≤ stabSub U₁)
    (hFF : Nat.card 𝕎 ≤ Nat.card A * Nat.card (fixV A)) :
    Nat.card (Sec U₁ U₂) ≤ Nat.card A * Nat.card (fixV (autSec A U₁ U₂)) := by
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ fixV A, a * b = b * a := fun a _ b _ => mul_comm a b
  have hsup := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf := card_inf_fixV_le_autSec hU hAU₁
  have hsec := card_sec_mul hU
  have hsupW : Nat.card ↥(U₁ ⊔ fixV A) ≤ Nat.card 𝕎 := Subgroup.card_le_card_group _
  have hinf2 : Nat.card ↥(U₂ ⊓ fixV A) ≤ Nat.card U₂ := Subgroup.card_le_of_le inf_le_left
  have hU2pos : 0 < Nat.card U₂ := Nat.card_pos
  have hcpos : 0 < Nat.card (fixV A) := Nat.card_pos
  set s := Nat.card (Sec U₁ U₂)
  set u₂ := Nat.card U₂
  set c := Nat.card (fixV A)
  set w := Nat.card 𝕎
  set j := Nat.card ↥(U₁ ⊔ fixV A)
  set i₁ := Nat.card ↥(U₁ ⊓ fixV A)
  set cm := Nat.card (fixV (autSec A U₁ U₂))
  set i₂ := Nat.card ↥(U₂ ⊓ fixV A)
  set a := Nat.card A
  have h1 : s * u₂ * c ≤ (a * cm) * (u₂ * c) := by
    calc s * u₂ * c = j * i₁ := by rw [hsec, hsup]
      _ ≤ w * i₁ := Nat.mul_le_mul_right _ hsupW
      _ ≤ w * (cm * i₂) := Nat.mul_le_mul_left _ hinf
      _ ≤ w * (cm * u₂) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinf2)
      _ ≤ (a * c) * (cm * u₂) := Nat.mul_le_mul_right _ hFF
      _ = (a * cm) * (u₂ * c) := by ring
  have h2 : s * (u₂ * c) ≤ (a * cm) * (u₂ * c) := by
    calc s * (u₂ * c) = s * u₂ * c := by ring
      _ ≤ _ := h1
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

theorem burnsideC121_p4_psl_section
    (h2 : ∀ w : 𝕎, w ^ 2 = 1) {G : Subgroup (MulAut 𝕎)}
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (θ : ↥G ≃* SL(2, F)) {A : Subgroup (MulAut 𝕎)} (hAG : A ≤ G) (hA1 : A ≠ ⊥)
    (hAe : IsElemAbelian2 A) (hFF : Nat.card 𝕎 ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ (U₁ U₂ : Subgroup 𝕎) (hU : U₂ ≤ U₁) (hG₁ : G ≤ stabSub U₁) (hG₂ : G ≤ stabSub U₂)
      (e : Sec U₁ U₂ ≃* Multiplicative (Fin 2 → F)),
      ∀ (g : ↥G) (x : Sec U₁ U₂), e (B5.secHom G hG₁ hG₂ g x) =
        Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (e x)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have : IsSimpleGroup SL(2, F) := burnsideC121_p4_isSimpleGroup_sl2 hn hF
  have : IsSimpleGroup ↥G := MulEquiv.isSimpleGroup θ
  have hperfSL := burnsideC121_p4_isPerfect_sl2 hn hF
  have hperfG : Group.IsPerfect ↥G := Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom)
    θ.symm.surjective
  have hcommG : commutator ↥G = ⊤ := hperfG.commutator_eq_top
  have hG1 : G ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥G = 1 := by rw [h]; exact Subgroup.card_bot
    have h2 : Nat.card SL(2, F) = 1 := (Nat.card_congr θ.toEquiv).symm.trans h1
    have : Nontrivial SL(2, F) := IsSimpleGroup.toNontrivial
    have := Finite.one_lt_card (α := SL(2, F))
    omega
  obtain ⟨U₁, U₂, hU, hG₁, hG₂, hnt, hirr⟩ := burnsideC121_p4_exists_irr_section hcommG hG1
  have hfaith : G ⊓ centSec U₁ U₂ = ⊥ := by
    rcases burnsideC121_p4_normal_cases (G ⊓ centSec U₁ U₂) inf_le_left (by
      intro g hg x hx
      refine ⟨G.mul_mem (G.mul_mem hg hx.1) (G.inv_mem hg), (stabSub U₁).mul_mem
        ((stabSub U₁).mul_mem (hG₁ hg) hx.2.1) ((stabSub U₁).inv_mem (hG₁ hg)), fun u hu => ?_⟩
      have h1 : g⁻¹ u ∈ U₁ := ((hG₁ (G.inv_mem hg)) u).2 hu
      have h2 := hx.2.2 _ h1
      have h3 : g (x (g⁻¹ u) * (g⁻¹ u)⁻¹) ∈ U₂ := ((hG₂ hg) _).2 h2
      have h4 : (g * x * g⁻¹) u * u⁻¹ = g (x (g⁻¹ u) * (g⁻¹ u)⁻¹) := by
        rw [map_mul, map_inv]
        have : g (g⁻¹ u) = u := by simp
        rw [this]
        rfl
      rw [h4]
      exact h3) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hnt
  set M := Sec U₁ U₂
  set GM : Subgroup (MulAut M) := autSec G U₁ U₂ with hGM
  let sE : ↥G ≃* ↥GM := B5.secEquiv G hG₁ hG₂ hfaith
  let θM : ↥GM ≃* SL(2, F) := sE.symm.trans θ
  have hθM : ∀ g : ↥G, θM (sE g) = θ g := fun g => by
    show θ (sE.symm (sE g)) = θ g
    rw [MulEquiv.symm_apply_apply]
  set AM : Subgroup (MulAut M) := autSec A U₁ U₂ with hAM
  have hAMmap : (A.subgroupOf G).map (B5.secHom G hG₁ hG₂) = AM :=
    B5.map_secHom_eq_autSec G hG₁ hG₂ hAG
  have hinj : Function.Injective (B5.secHom G hG₁ hG₂) :=
    (MonoidHom.ker_eq_bot_iff _).1 (B5.ker_secHom_eq_bot G hG₁ hG₂ hfaith)
  have hAMc : Nat.card AM = Nat.card A := by
    rw [← hAMmap, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv
  have hAMG : AM ≤ GM := autSec_mono hAG U₁ U₂
  have hAMe : IsElemAbelian2 AM := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · rw [← hAMmap] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · rw [← hAMmap] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_subgroupOf.1 ha))
      rw [this, map_one]
  have hAM1 : AM ≠ ⊥ := by
    intro h
    have h1 : Nat.card A = 1 := by rw [← hAMc, h]; exact Subgroup.card_bot
    exact hA1 (Subgroup.eq_bot_of_card_eq A h1)
  have hoffM : Nat.card M ≤ Nat.card AM * Nat.card (fixV AM) := by
    rw [hAMc]
    exact burnsideC121_p4_sec_offender hU (hAG.trans hG₁) hFF
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below (X := GM) ⟨hAMG, hAM1, hAMe⟩ 0
    (by simpa using hoffM)
  obtain ⟨Q, -, hQ, hQq, hQw, -⟩ := exists_quadratic_offender_le (V := M)
    (fun x => by
      induction x using QuotientGroup.induction_on with
      | H u =>
        rw [← QuotientGroup.mk_pow]
        have : u ^ 2 = 1 := Subtype.ext (by simpa using h2 u)
        rw [this]
        rfl) hB
  have hM2 : ∀ x : M, x * x = 1 := fun x => by
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [← QuotientGroup.mk_mul]
      have : u * u = 1 := Subtype.ext (by simpa [pow_two] using h2 u)
      rw [this]
      rfl
  obtain ⟨Wl, _, _, _, ⟨θb⟩⟩ := exists_binModel_of_binary hM2
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  set ψ := binPsi θb with hψ
  set L₀ := GM.map ψ.toMonoidHom with hL₀
  set A₀ := Q.map ψ.toMonoidHom with hA₀
  let eL : ↥GM ≃* ↥L₀ := GM.equivMapOfInjective ψ.toMonoidHom ψ.injective
  have hZ₀ : Subgroup.center ↥L₀ = ⊥ := by
    have h1 := center_map_equiv (eL.symm.trans θM)
    rw [B42L2.center_sl2_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (eL.symm.trans θM).injective).1 h1
  let α₀ : (↥L₀ ⧸ Subgroup.center ↥L₀) ≃* SL(2, F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ₀).trans QuotientGroup.quotientBot).trans
      (eL.symm.trans θM)
  have hα : ∀ x : ↥L₀, α₀ (QuotientGroup.mk x) = θM (eL.symm x) := fun x => rfl
  have hntW : Nontrivial Wl := by
    obtain ⟨u, hu1, hu2⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hU (fun h => hnt (by
      rw [h]
      intro g hg
      exact ⟨hG₁ hg, fun w hw => U₁.mul_mem (((hG₁ hg) w).2 hw) (U₁.inv_mem hw)⟩)))
    have hv : (QuotientGroup.mk ⟨u, hu1⟩ : M) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hu2
    refine ⟨⟨Multiplicative.toAdd (θb (QuotientGroup.mk ⟨u, hu1⟩)), 0, fun h => hv ?_⟩⟩
    have h1 : θb (QuotientGroup.mk ⟨u, hu1⟩) = 1 := Multiplicative.toAdd.injective (by simpa using h)
    have h3 := congrArg θb.symm h1
    rw [MulEquiv.symm_apply_apply, map_one] at h3
    exact h3
  have : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θb Q).1 hQ.2.2.1
  have hA₀1 : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff_of_injective Q ψ.injective]
    exact hQ.2.1
  have hA₀L : A₀ ≤ L₀ := Subgroup.map_mono hQ.1
  have hAN : A₀ ≤ Subgroup.normalizer (L₀ : Set (Wl ≃ₗ[ZMod 2] Wl)) :=
    hA₀L.trans (Subgroup.le_normalizer)
  have hoff : Nat.card Wl ≤ weight (MonoidHom.id (Wl ≃ₗ[ZMod 2] Wl)) A₀ := by
    rw [hA₀, weight_map θb Q, ← natCard_eq θb]
    rw [hQw]
    simpa using hBc
  have hirrM : ∀ J : Subgroup M, (∀ l ∈ GM, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
    Bridge.TypeList.irr_of_isIrrSec (B5.isIrrSec_autSec (lt_of_le_of_ne hU (fun h => hnt (by
      rw [h]
      intro g hg
      exact ⟨hG₁ hg, fun w hw => U₁.mul_mem (((hG₁ hg) w).2 hw) (U₁.inv_mem hw)⟩)))
      (fun J hJ h2J hJ1 => hirr J hJ h2J hJ1) hG₁ hG₂)
  have hperfL : Group.IsPerfect ↥L₀ :=
    Group.IsPerfect.ofSurjective (f := (θM.symm.trans eL).toMonoidHom) (θM.symm.trans eL).surjective
  obtain ⟨-, θ₀, hθ₀, halt, -⟩ := central_quotient_SL2_alternatives_GL hn hF L₀ A₀
    ⟨hntW, fun U hU => B42L2.irr_map θb hirrM U hU⟩ hperfL α₀ hA₀1 hAN (B42L2.quad_map θb hQq)
    hoff
  rcases halt with ⟨-, β₀, hβ₀, -⟩ | hdel
  · refine ⟨U₁, U₂, hU, hG₁, hG₂, θb.trans (AddEquiv.toMultiplicative β₀), fun g x => ?_⟩
    have hx₀ : ((eL (sE g) : ↥L₀) : Wl ≃ₗ[ZMod 2] Wl) = ψ (B5.secHom G hG₁ hG₂ g) := rfl
    have h1 := hβ₀ (eL (sE g)) (Multiplicative.toAdd (θb x))
    rw [hθ₀, hα, MulEquiv.symm_apply_apply, hθM, hx₀, B42L2.toAdd_binPsi] at h1
    show Multiplicative.ofAdd (β₀ (Multiplicative.toAdd (θb (B5.secHom G hG₁ hG₂ g x)))) =
      Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ β₀ (Multiplicative.toAdd (θb x)))
    rw [h1]
  · exact absurd hA₀L hdel.1

theorem burnsideC121_p4_psl_natural
    (h2 : ∀ w : 𝕎, w ^ 2 = 1) {G : Subgroup (MulAut 𝕎)}
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (θ : ↥G ≃* SL(2, F)) {A : Subgroup (MulAut 𝕎)} (hAG : A ≤ G) (hA1 : A ≠ ⊥)
    (hAe : IsElemAbelian2 A) (hFF : Nat.card 𝕎 ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ β : 𝕎 →* Multiplicative (Fin 2 → F), Function.Surjective β ∧ β.ker = fixV G ∧
      ∀ (g : ↥G) (w : 𝕎), β ((g : MulAut 𝕎) w) =
        Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β w)) := by
  have : IsSimpleGroup SL(2, F) := burnsideC121_p4_isSimpleGroup_sl2 hn hF
  have : IsSimpleGroup ↥G := MulEquiv.isSimpleGroup θ
  obtain ⟨U₁, U₂, hU, hG₁, hG₂, e, he⟩ := burnsideC121_p4_psl_section h2 hn hF θ hAG hA1 hAe hFF
  refine burnsideC121_p4_global_of_section h2 (by omega) hF θ hU hG₁ hG₂ e he hAG hA1 hAe hFF ?_
  intro N hNG hN hAN
  rcases burnsideC121_p4_normal_cases N hNG hN with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hAN)) hA1
  · exact h

end Module

end CFSG.Quasithin
