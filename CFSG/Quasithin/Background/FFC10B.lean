module

public import CFSG.Quasithin.Background.B69Alt
public import CFSG.Quasithin.Background.FFC10A
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin

open CFSG.Open G6
open CFSG.Quasithin.H
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_act_alt {X L A : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) {k : ℕ}
    {W : Subgroup V} {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A)}
    (hreal : (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π)
    (hLeq : L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π))
    {g : MulAut V} (hgst : g ∈ stabSub W) (hgn' : ∀ l ∈ L, g⁻¹ * l * g ∈ L) :
    ∃ y ∈ L ⊔ A, ∀ w ∈ W, y w = g w := by
  classical
  have hn : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  have hn5 : 5 ≤ 2 * k + 1 := by
    by_contra hlt
    have hk1 : k = 1 ∨ k = 0 := by omega
    rcases hk1 with hk1 | hk1
    · subst hk1
      refine Group.IsPerfect.not_isMulCommutative ↥L
        (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
      rw [hLeq] at ha hb
      obtain ⟨σ₁, hσ₁, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨σ₂, hσ₂, rfl⟩ := Subgroup.mem_map.1 hb
      have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := by decide
      have := congrArg (fun x : alternatingGroup (Fin (2 * 1 + 1)) =>
          ((L ⊔ A).subtype.comp π) (x : Equiv.Perm (Fin (2 * 1 + 1))))
        (hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩)
      simpa using this
    · subst hk1
      refine Group.IsPerfect.not_isMulCommutative ↥L
        (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
      rw [hLeq] at ha hb
      obtain ⟨σ₁, hσ₁, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨σ₂, hσ₂, rfl⟩ := Subgroup.mem_map.1 hb
      have hcomm : ∀ a b : alternatingGroup (Fin (2 * 0 + 1)), a * b = b * a := by decide
      have := congrArg (fun x : alternatingGroup (Fin (2 * 0 + 1)) =>
          ((L ⊔ A).subtype.comp π) (x : Equiv.Perm (Fin (2 * 0 + 1))))
        (hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩)
      simpa using this
  obtain ⟨e, he⟩ := exists_core_equiv hn hreal
  have hπst : ∀ σ : Equiv.Perm (Fin (2 * k + 1)), ∀ w : ↥W,
      ((π σ : ↥(L ⊔ A)) : MulAut V) (w : V) ∈ W := fun σ w => hreal.2.2.2.1 (π σ) w w.2
  let rg : ↥W ≃* ↥W := resAut W ⟨g, hgst⟩
  have hrg : ∀ w : ↥W, ((rg w : ↥W) : V) = g (w : V) := fun w => rfl
  let ψ : MulAut ↥(coreMod (2 * k + 1)) := (e.symm.trans rg).trans e
  have hψapp : ∀ w : ↥W, ψ (e w) = e (rg w) := fun w => by
    show e (rg (e.symm (e w))) = _
    rw [e.symm_apply_apply]
  have hψ : ∀ σ ∈ alternatingGroup (Fin (2 * k + 1)), ∃ τ ∈ alternatingGroup (Fin (2 * k + 1)),
      ∀ y : ↥(coreMod (2 * k + 1)), coreAct (2 * k + 1) σ (ψ y) = ψ (coreAct (2 * k + 1) τ y) := by
    intro σ hσ
    have h1 : ((π σ : ↥(L ⊔ A)) : MulAut V) ∈
        (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) :=
      Subgroup.mem_map.2 ⟨σ, hσ, rfl⟩
    have h1' : ((π σ : ↥(L ⊔ A)) : MulAut V) ∈ L := hLeq.ge h1
    have h2 : g⁻¹ * ((π σ : ↥(L ⊔ A)) : MulAut V) * g ∈ L := hgn' _ h1'
    have h2' := hLeq.le h2
    obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.1 h2'
    have hτeq' : ((π τ : ↥(L ⊔ A)) : MulAut V) =
        g⁻¹ * ((π σ : ↥(L ⊔ A)) : MulAut V) * g := hτeq
    refine ⟨τ, hτ, fun y => ?_⟩
    obtain ⟨u, rfl⟩ := e.surjective y
    have hval : ((π σ : ↥(L ⊔ A)) : MulAut V) (g (u : V)) =
        g (((π τ : ↥(L ⊔ A)) : MulAut V) (u : V)) := by
      rw [hτeq']
      simp [MulAut.mul_apply]
    have hu1 := hπst σ (rg u)
    have hu2 := hπst τ u
    have e1 : coreAct (2 * k + 1) σ (ψ (e u)) = e ⟨_, hu1⟩ := by
      rw [hψapp]
      exact (he σ (rg u) hu1).symm
    have e2 : ψ (coreAct (2 * k + 1) τ (e u)) = e (rg ⟨_, hu2⟩) := by
      rw [← he τ u hu2, hψapp]
    rw [e1, e2]
    refine congrArg e (Subtype.ext ?_)
    exact hval
  obtain ⟨ρ, hρ⟩ := exists_perm_of_normalizes hn hn5 ψ hψ
  refine ⟨((π ρ : ↥(L ⊔ A)) : MulAut V), (π ρ).2, fun w hw => ?_⟩
  have h1 := he ρ ⟨w, hw⟩ (hπst ρ ⟨w, hw⟩)
  have h2 : e ⟨_, hπst ρ ⟨w, hw⟩⟩ = e (rg ⟨w, hw⟩) := by
    rw [h1, ← hρ, hψapp]
  exact congrArg Subtype.val (e.injective h2)

theorem sec_card_le_of_offender {X A L : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hnt : commSub W A ≠ ⊥) :
    Nat.card (Sec W (W ⊓ fixV L)) ≤
      Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) := by
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAut := B1_5_1 hA hAW hnt
  have h1 : Nat.card W ≤ Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) := by
    have h := hAut.2.2.2 ⊥ bot_le
    have e : fixV (⊥ : Subgroup (MulAut ↥W)) = ⊤ := eq_top_iff.2 fun v _ x hx => by
      rw [Subgroup.mem_bot.1 hx]
      rfl
    rwa [Subgroup.card_bot, one_mul, e, Subgroup.card_top] at h
  have hUW : W ⊓ fixV L ≤ W := inf_le_left
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hker : A ⊓ centSec W (W ⊓ fixV L) = A ⊓ centSub W := by
    apply le_antisymm
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, ?_⟩
      have := sec_triv_imp_triv hL hAn hW hAW haA fun w hw => (ha.2 w hw).2
      intro w hw
      exact this w hw
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, hAst haA, fun w hw => ?_⟩
      rw [ha w hw, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hcard : Nat.card (autSub A W) = Nat.card (autSec A W (W ⊓ fixV L)) := by
    have e1 := card_autSub_mul hAst
    have e2 := card_autSec_mul hAst hAU
    rw [hker] at e2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e1.trans e2.symm)
  have hfix : Nat.card (fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAst, Subgroup.card_map_of_injective W.subtype_injective]
  have h2 := card_inf_fixV_le_autSec hUW hAst
  have h3 : Nat.card ↥((W ⊓ fixV L) ⊓ fixV A) ≤ Nat.card ↥(W ⊓ fixV L) :=
    Subgroup.card_le_of_le inf_le_left
  have h4 := card_sec_mul hUW
  rw [hcard, hfix] at h1
  have h5 : Nat.card (Sec W (W ⊓ fixV L)) * Nat.card ↥(W ⊓ fixV L) ≤
      (Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L)))) *
        Nat.card ↥(W ⊓ fixV L) := by
    calc Nat.card (Sec W (W ⊓ fixV L)) * Nat.card ↥(W ⊓ fixV L) = Nat.card W := h4
      _ ≤ Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card ↥(W ⊓ fixV A) := h1
      _ ≤ Nat.card (autSec A W (W ⊓ fixV L)) *
          (Nat.card (fixV (autSec A W (W ⊓ fixV L))) * Nat.card ↥((W ⊓ fixV L) ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (autSec A W (W ⊓ fixV L)) *
          (Nat.card (fixV (autSec A W (W ⊓ fixV L))) * Nat.card ↥(W ⊓ fixV L)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ = (Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L)))) *
          Nat.card ↥(W ⊓ fixV L) := by ring
  exact Nat.le_of_mul_le_mul_right h5 Nat.card_pos

theorem exists_act_natural {X L B : Subgroup (MulAut V)} (hL : CFSG.Open.IsQuasisimple ↥L)
    {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e) (hB : IsFFStarOffender X B)
    (hBn : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) (hBW : ∀ b ∈ B, ∀ w ∈ W, b w ∈ W) :
    ∀ b ∈ B, ∃ l ∈ L, ∀ w ∈ W, l w = b w := by
  classical
  by_cases hnt : commSub W B = ⊥
  · intro b hb
    refine ⟨1, L.one_mem, fun w hw => ?_⟩
    exact ((commSub_eq_bot_iff.1 hnt) hw b hb).symm
  obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
  let π : ↥(StatedSL 2 K) →* ↥L := π₀
  have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
  obtain ⟨ε, hε⟩ := exists_sec_equiv (StatedSL 2 K) hπ
  have hπs : Function.Surjective π := hπ.1
  have hLinv := (mem_irrPlus_top_iff.1 hW).1
  have hBnorm : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun b hb =>
    (Subgroup.mem_normalizer_iff).2 fun l => ⟨fun hl => hBn b hb l hl, fun hl => by
      have := hBn b⁻¹ (B.inv_mem hb) _ hl
      simpa [mul_assoc] using this⟩
  have hLU : ∀ l ∈ L, ∀ u ∈ W ⊓ fixV L, l u ∈ W ⊓ fixV L := isInv_inf hLinv (isInv_fixV L)
  have hBU : ∀ b ∈ B, ∀ u ∈ W ⊓ fixV L, b u ∈ W ⊓ fixV L :=
    isInv_inf hBW (B1Red.fixV_inv_of_normalizes hBn)
  set X' : Subgroup (MulAut V) := stabSub W ⊓ stabSub (W ⊓ fixV L) with hX'
  have hX'W : X' ≤ stabSub W := inf_le_left
  have hX'Z : X' ≤ stabSub (W ⊓ fixV L) := inf_le_right
  have hLX' : L ≤ X' := le_inf (B1.le_stabSub_of_invariant hLinv) (B1.le_stabSub_of_invariant hLU)
  have hBX' : B ≤ X' := le_inf (B1.le_stabSub_of_invariant hBW) (B1.le_stabSub_of_invariant hBU)
  set Φ : ↥X' →* MulAut (StdMod (Fin 2) K) :=
    (congrHom ε).comp (B5.secHom X' hX'W hX'Z) with hΦ
  have hΦπ : ∀ γ : ↥(StatedSL 2 K),
      Φ ⟨((π γ : ↥L) : MulAut V), hLX' (π γ).2⟩ = natAut (StatedSL 2 K) γ := by
    intro γ
    apply MulEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := ε.surjective x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    have hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ W := (hLinv _ (π γ).2) u u.2
    have h1 := hε γ u hu
    rw [hΦ, MonoidHom.comp_apply, congrHom_apply, MulEquiv.symm_apply_apply]
    show ε (B5.secHom X' hX'W hX'Z _ (QuotientGroup.mk u)) = natAct (StatedSL 2 K) γ _
    rw [B5.secHom_mk]
    exact h1
  have hconj : ∀ b : ↥X', (b : MulAut V) ∈ B → ∀ γ : ↥(StatedSL 2 K),
      ∃ γ' : ↥(StatedSL 2 K), Φ b * natAut (StatedSL 2 K) γ * (Φ b)⁻¹ = natAut (StatedSL 2 K) γ' := by
    intro b hb γ
    have hmem : (b : MulAut V) * ((π γ : ↥L) : MulAut V) * (b : MulAut V)⁻¹ ∈ L := hBn _ hb _ (π γ).2
    obtain ⟨γ', hγ'⟩ := hπs ⟨_, hmem⟩
    refine ⟨γ', ?_⟩
    rw [← hΦπ γ, ← hΦπ γ', ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (congrArg Subtype.val hγ').symm
  have hbX' : ∀ b ∈ B, b ∈ X' := fun b hb => hBX' hb
  set E : Subgroup (MulAut (StdMod (Fin 2) K)) := (B.subgroupOf X').map Φ with hE
  have hEN : E ≤ natNorm (StatedSL 2 K) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyB : (y : MulAut V) ∈ B := hy
    have hyinv : ((y⁻¹ : ↥X') : MulAut V) ∈ B := B.inv_mem hyB
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨γ, rfl⟩
      obtain ⟨γ', hγ'⟩ := hconj y hyB γ
      exact ⟨γ', hγ'.symm⟩
    · rintro ⟨γ₂, hγ₂⟩
      obtain ⟨γ₃, hγ₃⟩ := hconj y⁻¹ hyinv γ₂
      refine ⟨γ₃, ?_⟩
      rw [← hγ₃, map_inv, hγ₂]
      group
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyB : (y : MulAut V) ∈ B := hy
    rw [← map_pow]
    have : y ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hB.2.2.1.2 _ hyB)
    rw [this, map_one]
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.2.2.1.1 _ hx' _ hy')
  have hEeq : E = (autSec B W (W ⊓ fixV L)).map (congrHom ε) := by
    rw [hE, hΦ, ← Subgroup.map_map, B5.map_secHom_eq_autSec X' hX'W hX'Z hBX']
  have hcardE : Nat.card E = Nat.card (autSec B W (W ⊓ fixV L)) := by
    rw [hEeq]
    exact card_map_congrHom ε _
  have hfixE : Nat.card ↥(fixV E) = Nat.card (fixV (autSec B W (W ⊓ fixV L))) := by
    rw [hEeq, fixV_map_congrHom]
    exact Subgroup.card_map_of_injective ε.injective
  have hSec : Nat.card (StdMod (Fin 2) K) = Nat.card (Sec W (W ⊓ fixV L)) :=
    (Nat.card_congr ε.toEquiv).symm
  have hoffE : Nat.card (StdMod (Fin 2) K) ≤ Nat.card E * Nat.card ↥(fixV E) := by
    rw [hcardE, hfixE, hSec]
    exact sec_card_le_of_offender hB hL hBn hW hBW hnt
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hEim := le_natImage_of_offender he hK hEN hE2 hEc hoffE
  intro b hb
  have hbE : Φ ⟨b, hbX' b hb⟩ ∈ E :=
    Subgroup.mem_map.2 ⟨⟨b, hbX' b hb⟩, by rw [Subgroup.mem_subgroupOf]; exact hb, rfl⟩
  obtain ⟨γ, hγ⟩ := hEim hbE
  refine ⟨((π γ : ↥L) : MulAut V), (π γ).2, ?_⟩
  have hlX' : ((π γ : ↥L) : MulAut V) ∈ X' := hLX' (π γ).2
  have hΦl : Φ ⟨((π γ : ↥L) : MulAut V), hlX'⟩ = Φ ⟨b, hbX' b hb⟩ := by
    rw [hΦπ γ]
    exact hγ
  have hsec : ∀ w ∈ W, (((π γ : ↥L) : MulAut V) w)⁻¹ * b w ∈ W ⊓ fixV L := by
    intro w hw
    have h1 : B5.secHom X' hX'W hX'Z ⟨((π γ : ↥L) : MulAut V), hlX'⟩ =
        B5.secHom X' hX'W hX'Z ⟨b, hbX' b hb⟩ := congrHom_injective ε hΦl
    have h2 := congrArg (fun φ : MulAut (Sec W (W ⊓ fixV L)) => φ (QuotientGroup.mk ⟨w, hw⟩)) h1
    simp only [B5.secHom_mk] at h2
    have h3 := QuotientGroup.eq.1 h2
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3
  have hLB : L ⊔ B ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hBnorm
  have hLBn : ∀ a ∈ L ⊔ B, ∀ x ∈ L, a * x * a⁻¹ ∈ L := fun a ha x hx =>
    B19Aux.conj_mem_of_le_normalizer hLB ha hx
  have hLBW : ∀ a ∈ L ⊔ B, ∀ w ∈ W, a w ∈ W := fun a ha w hw =>
    (hX'W (sup_le hLX' hBX' ha) (w)).2 hw
  have ha : ((π γ : ↥L) : MulAut V)⁻¹ * b ∈ L ⊔ B :=
    (L ⊔ B).mul_mem ((L ⊔ B).inv_mem (Subgroup.mem_sup_left (π γ).2)) (Subgroup.mem_sup_right hb)
  have hfix := sec_triv_imp_triv hL hLBn hW hLBW ha (fun w hw => by
    have hz := hsec w hw
    set l : MulAut V := ((π γ : ↥L) : MulAut V) with hl
    have hbw : b w = l w * ((l w)⁻¹ * b w) := by simp
    have hlz : l⁻¹ ((l w)⁻¹ * b w) = (l w)⁻¹ * b w := by
      have := hz.2 l⁻¹ (L.inv_mem (π γ).2)
      exact this
    have : (l⁻¹ * b) w * w⁻¹ = (l w)⁻¹ * b w := by
      show l⁻¹ (b w) * w⁻¹ = _
      conv_lhs => rw [hbw]
      rw [map_mul, hlz]
      simp [mul_comm]
    rw [this]
    exact hz.2)
  intro w hw
  have h1 := congrArg ((π γ : ↥L) : MulAut V) (hfix w hw)
  have h2 : b w = ((π γ : ↥L) : MulAut V) w := by simpa using h1
  exact h2.symm

theorem exists_act_blk (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X T M B L : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M) (hact : ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L) (hB : IsFFStarOffender X B)
    (hL : CFSG.Open.IsComponentOf L X) :
    ∀ b ∈ B, ∃ y ∈ blk X L, ∀ w ∈ commV L, y w = b w := by
  obtain ⟨A, hA, hLA⟩ := hact
  have hW : commV L ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hV hctx hA hL hLA
  have hBnorm : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := hP4 V hV X B hB L hL
  have hBn : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hBnorm hb hl
  have hBW : ∀ b ∈ B, ∀ w ∈ commV L, b w ∈ commV L := by
    intro b hb w hw
    have h1 := map_mem_commV_conj b w hw
    have h2 : B6.conjSub b L = L := by
      ext x
      rw [B6.mem_conjSub]
      have := Subgroup.mem_normalizer_iff.1 (hBnorm (B.inv_mem hb)) x
      simpa using this.symm
    rwa [h2] at h1
  have hshape := hctx A L hA hL hLA (commV L) hW
  rcases hshape with ⟨⟨e, he, hnat⟩, -, -⟩ | ⟨k, -, π, -, hreal, hLeq, -, -⟩
  · intro b hb
    obtain ⟨l, hl, hlb⟩ := exists_act_natural hL.2.2 hW he hnat hB hBn hBW b hb
    exact ⟨l, le_blk_self hl, hlb⟩
  · intro b hb
    have hgst : b ∈ stabSub (commV L) := B1.le_stabSub_of_invariant hBW hb
    have hgn' : ∀ l ∈ L, b⁻¹ * l * b ∈ L := fun l hl => by
      have := hBn b⁻¹ (B.inv_mem hb) l hl
      simpa using this
    obtain ⟨y, hy, hyb⟩ := exists_act_alt hL hreal hLeq hgst hgn'
    exact ⟨y, sup_le le_blk_self (le_blk_of hA hLA) hy, hyb⟩

end B69

end CFSG.Quasithin
