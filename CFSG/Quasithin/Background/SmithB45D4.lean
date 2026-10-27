module

public import CFSG.Quasithin.Background.SmithB45TorD4
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate123

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace B45D4

open scoped commutatorElement
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp CFSG.Quasithin.B42D4

@[expose] def outerPrimes (f ℓ : ℕ) : Prop :=
  ∃ e : ℕ, 2 * e = f ∧ orderOf (2 : ZMod ℓ) = 12 * e

section Criterion

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hf hK hσ in
theorem dispAtOut_outer (α : MulAut C₀) (hα : α * α = 1)
    (hαo : α ∉ (MulAut.conj : C₀ →* MulAut C₀).range) :
    Even f ∧ DispAtOut C₀ (outerPrimes f) α (2 ^ (2 * f + 1)) := by
  classical
  have hα2 : α ^ 2 = 1 := by rw [sq, hα]
  obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ α hα2 hαo
  refine ⟨hev, ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨r, hr⟩ := hev; omega⟩
  have he : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (6 * e) := by rw [hK, ← pow_mul]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e) := hσ
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ]; congr 2; omega
  obtain ⟨-, hδ2, hδ1, -, -⟩ := triality_field_facts he hK' hσ' hδ'
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq (12 * e) (by omega) (by omega)
  obtain ⟨hℓ3, hℓd⟩ := ppd_twelve hℓ he hord
  obtain ⟨y, t, hy, hyt, hto, hfy, hft⟩ :=
    exists_fixed_inverting he K hK' σ hσ' δ hδ' hℓ hℓ3 hℓd
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hδ₀2 : (fieldActor (t := TwistTag.D4) σ δ) * fieldActor σ δ = 1 := by
    rw [← fieldActor_mul, ← sq, hδ2, fieldActor_one]
  have hconjδ : ∀ g : C₀,
      fieldActor σ δ * MulAut.conj g = MulAut.conj (fieldActor σ δ g) * fieldActor σ δ := by
    intro g
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hβ2 : MulAut.conj y * fieldActor σ δ * (MulAut.conj y * fieldActor σ δ) = 1 := by
    rw [mul_assoc, ← mul_assoc (fieldActor σ δ), hconjδ, hfy, mul_assoc, hδ₀2, mul_one, ← map_mul,
      hy, map_one]
  have hβt : (MulAut.conj y * fieldActor σ δ : MulAut C₀) t = t⁻¹ := by
    rw [MulAut.mul_apply, hft, MulAut.conj_apply, hyt]
  have hβy : (MulAut.conj y * fieldActor σ δ : MulAut C₀) y = y := by
    rw [MulAut.mul_apply, hfy, MulAut.conj_apply]
    group
  have hlt : (2 ^ (2 * (2 * e) + 1)) ^ 2 < 2 ^ orderOf (2 : ZMod ℓ) := by
    rw [hord, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hβo : MulAut.conj y * fieldActor σ δ ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    rintro ⟨g, hg⟩
    have e1 : fieldActor σ δ = MulAut.conj (y⁻¹ * g) * fieldActor σ 1 := by
      rw [fieldActor_one, mul_one, map_mul, hg, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : fieldActor (t := TwistTag.D4) σ δ = MulAut.conj 1 * fieldActor σ δ := by
      rw [map_one, one_mul]
    obtain ⟨⟨g', δ'⟩, -, huniq⟩ := hNF (fieldActor σ δ)
    have h1 := huniq (y⁻¹ * g, 1) e1
    have h2 := huniq (1, δ) e2
    have : (1 : K ≃+* K) = δ := (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
    exact hδ1 this.symm
  have hβ2' : (MulAut.conj y * fieldActor σ δ) ^ 2 = 1 := by rw [sq, hβ2]
  obtain ⟨-, δ', hδ'c, -, ψ', hψ', -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ _ hβ2' hβo
  have hδδ' : δ' = δ := RingEquiv.ext fun c => by rw [hδ'c, hδ]
  rw [hδδ'] at hψ'
  have hαβ : α = (ψ⁻¹ * ψ') * (MulAut.conj y * fieldActor σ δ) * (ψ⁻¹ * ψ')⁻¹ := by
    have e1 : α = ψ⁻¹ * fieldActor σ δ * ψ := by rw [← hψ]; group
    have e2 : (ψ⁻¹ * ψ') * (MulAut.conj y * fieldActor σ δ) * (ψ⁻¹ * ψ')⁻¹ =
        ψ⁻¹ * (ψ' * (MulAut.conj y * fieldActor σ δ) * ψ'⁻¹) * ψ := by group
    rw [e2, hψ', e1]
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut C₀, φ = ψ⁻¹ * ψ' := ⟨_, rfl⟩
  rw [← hφ] at hαβ
  have hαc : α (φ t) = (φ t)⁻¹ := by
    rw [hαβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hβt, map_inv]
  refine ⟨ℓ, φ t, φ y, ⟨e, rfl, hord⟩, hℓ, hℓ2, hαo, hαc, by rw [MulEquiv.orderOf_eq, hto],
    ?_, ?_, hlt⟩
  · rw [hαβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hβy, ← map_mul, hy,
      map_one]
  · rw [hαc, ← map_inv φ t, ← map_inv φ y, ← map_mul, ← map_mul]
    congr 1
    calc y * t⁻¹ * y⁻¹ = (y * t * y⁻¹)⁻¹ := by group
      _ = t := by rw [hyt, inv_inv]

include hf hK hσ in
theorem lineGenTop_of_pure (E : Subgroup C₀) (hE : E ≠ ⊥) (hEa : IsElem2 E)
    (hB : ∀ ξ ∈ E, ξ ≠ 1 → ¬ ConjC σ (ξ : ModGL TwistTag.D4.tag K) (ox₁ σ 1)) {n : ℕ}
    (hn : 2 ^ (20 * f) < n) : B45Tor.LineGenTop C₀ E n := by
  classical
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hk := card_fixedField hf hK σ hσ
  have hσ1 := exists_sigma_ne hf hK σ hσ
  obtain ⟨t₁, t₂, t₃, hspan⟩ := exists_spanning hf hK σ hσ
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEa.2 x hx
  obtain ⟨g₀, hg₀, hline₀⟩ := elem_line σ hσ3 E hEa.1 hsq hB
  have hline : ∀ x ∈ E, ∃ e f : K, σ e = e ∧ σ f = f ∧
      (x : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹ := hline₀
  obtain ⟨⟨v, hvE⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨e₀, f₀, he₀, hf₀, hv⟩ := hline v hvE
  have hne : e₀ ≠ 0 ∨ f₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hv1'
    apply Subtype.ext
    rw [hv, h.1, h.2]
    simp [lam, pinnedX_zero]
  set G₀ : C₀ := ⟨g₀, hg₀⟩ with hG₀
  have : Fintype (trialityFixedField K σ.toRingHom) := Fintype.ofFinite _
  let u : trialityFixedField K σ.toRingHom × trialityFixedField K σ.toRingHom ×
      trialityFixedField K σ.toRingHom → ModGL TwistTag.D4.tag K :=
    fun p => Xr d4C p.1 * Xr (-d4C) p.2.1 * Xr d4C p.2.2
  have hu : ∀ p, u p ∈ C₀ := fun p => mul_mem (mul_mem (Xr_C_mem_C0 σ hσ3 p.1.2)
    (negC_mem_C0 hf hK σ hσ p.2.1.2)) (Xr_C_mem_C0 σ hσ3 p.2.2.2)
  set hs : List C₀ := (Finset.univ.toList).map fun p => G₀ * ⟨u p, hu p⟩ * G₀⁻¹ with hhs
  have hmem_hs : ∀ h ∈ hs, ∃ p, (h : ModGL TwistTag.D4.tag K) = g₀ * u p * g₀⁻¹ := by
    intro h hh
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
    exact ⟨p, rfl⟩
  let ΛM : Subgroup C₀ :=
    { carrier := {x | ∃ e f : K, σ e = e ∧ σ f = f ∧
        (x : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹}
      mul_mem' := by
        rintro x y ⟨e, f, he, hf, hx⟩ ⟨e', f', he', hf', hy⟩
        refine ⟨e + e', f + f', by rw [map_add, he, he'], by rw [map_add, hf, hf'], ?_⟩
        rw [Subgroup.coe_mul, hx, hy, ← lam_mul]
        group
      one_mem' := ⟨0, 0, map_zero σ, map_zero σ, by
        simp [lam, pinnedX_zero]⟩
      inv_mem' := by
        rintro x ⟨e, f, he, hf, hx⟩
        refine ⟨e, f, he, hf, ?_⟩
        rw [Subgroup.coe_inv, hx, mul_inv_rev, mul_inv_rev, inv_inv, lam_inv, mul_assoc] }
  have hconj : ∀ h ∈ hs, ∀ a ∈ E, h * a * h⁻¹ ∈ ΛM := by
    intro h hh a ha
    obtain ⟨p, hp⟩ := hmem_hs h hh
    obtain ⟨e, f, he, hf, hae⟩ := hline a ha
    have e1 : ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K) =
        g₀ * (u p * lam K e f * (u p)⁻¹) * g₀⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hp, hae]; group
    rw [conj3_lam] at e1
    have hp1 : σ (p.1 : K) = p.1 := p.1.2
    have hp2 : σ (p.2.1 : K) = p.2.1 := p.2.1.2
    have hp3 : σ (p.2.2 : K) = p.2.2 := p.2.2.2
    refine ⟨_, _, ?_, ?_, e1⟩
    · simp only [map_add, map_mul, he, hf, hp2, hp3]
    · simp only [map_add, map_mul, he, hf, hp1, hp2, hp3]
  set gsM : List C₀ := [1, ⟨nW0 K, nW0_mem σ⟩,
    ⟨ox₁ σ t₁ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₁) (nA_mem σ)⟩,
    ⟨ox₁ σ t₂ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₂) (nA_mem σ)⟩,
    ⟨ox₁ σ t₃ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₃) (nA_mem σ)⟩] with hgsM
  set gs : List C₀ := gsM.map fun g => g * G₀⁻¹ with hgs
  refine ⟨hs, gs, ?_, ?_, ?_⟩
  ·
    intro h hh h' hh' a ha b hb
    obtain ⟨e, f, -, -, hx⟩ := hconj h hh a ha
    obtain ⟨e', f', -, -, hy⟩ := hconj h' hh' b hb
    apply Subtype.ext
    change ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K) *
        ((h' * b * h'⁻¹ : C₀) : ModGL TwistTag.D4.tag K) =
      ((h' * b * h'⁻¹ : C₀) : ModGL TwistTag.D4.tag K) *
        ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K)
    rw [hx, hy]
    calc g₀ * lam K e f * g₀⁻¹ * (g₀ * lam K e' f' * g₀⁻¹) =
        g₀ * (lam K e f * lam K e' f') * g₀⁻¹ := by group
      _ = g₀ * (lam K e' f' * lam K e f) * g₀⁻¹ := by rw [lam_comm]
      _ = _ := by group
  ·
    set T := {y : C₀ | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} with hT
    set S := {y : C₀ | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹} with hS
    have hΛT : ∀ e f : K, σ e = e → σ f = f →
        ∃ w ∈ Subgroup.closure T, (w : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹ := by
      intro e f he hf
      set S₀ : Subgroup (ModGL TwistTag.D4.tag K) :=
        ((Subgroup.closure T).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).map
            (MulAut.conj g₀⁻¹).toMonoidHom
      have hS₀ : ∀ γ γ' γ'' : K, σ γ = γ → σ γ' = γ' → σ γ'' = γ'' →
          (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * lam K e₀ f₀ *
            (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'')⁻¹ ∈ S₀ := by
        intro γ γ' γ'' h1 h2 h3
        have hUC : Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'' ∈ graphFixedRootGroup TwistTag.D4 K
            σ.toRingHom := hu (⟨γ, h1⟩, ⟨γ', h2⟩, ⟨γ'', h3⟩)
        have hh : G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹ ∈ hs :=
          List.mem_map.2 ⟨(⟨γ, h1⟩, ⟨γ', h2⟩, ⟨γ'', h3⟩), Finset.mem_toList.2
            (Finset.mem_univ _), rfl⟩
        have hw : (G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹) * v *
            (G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹)⁻¹ ∈
              Subgroup.closure T := Subgroup.subset_closure ⟨_, hh, v, hvE, rfl⟩
        refine ⟨_, ⟨_, hw, rfl⟩, ?_⟩
        change g₀⁻¹ * (g₀ * (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * g₀⁻¹ * (v : ModGL
          TwistTag.D4.tag K) * (g₀ * (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * g₀⁻¹)⁻¹) *
            g₀⁻¹⁻¹ = _
        rw [hv]
        group
      have hl := lam_closure (S := S₀) he₀ hf₀ hne hS₀ he hf
      obtain ⟨_, ⟨w, hw, rfl⟩, hw'⟩ := hl
      refine ⟨w, hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Subgroup.coe_subtype] at hw'
      rw [← hw']; group
    have hTS : ∀ g ∈ gs, ∀ w ∈ Subgroup.closure T, g * w * g⁻¹ ∈ Subgroup.closure S := by
      intro g hg w hw
      have hle : (Subgroup.closure T).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨y, ⟨h, hh, a, ha, rfl⟩, rfl⟩
        exact Subgroup.subset_closure ⟨g, hg, h, hh, a, ha, rfl⟩
      exact hle ⟨w, hw, rfl⟩
    set H' := (Subgroup.closure S).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hH'
    have hgen : ∀ g ∈ gsM, ∀ e f : K, σ e = e → σ f = f →
        (g : ModGL TwistTag.D4.tag K) * lam K e f * (g : ModGL TwistTag.D4.tag K)⁻¹ ∈ H' := by
      intro g hg e f he hf
      obtain ⟨w, hw, hw'⟩ := hΛT e f he hf
      refine ⟨g * G₀⁻¹ * w * (g * G₀⁻¹)⁻¹, hTS _ (List.mem_map.2 ⟨g, hg, rfl⟩) w hw, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hw', hG₀]
      group
    have hm1 : (1 : C₀) ∈ gsM := List.mem_cons_self
    have hm2 : (⟨nW0 K, nW0_mem σ⟩ : C₀) ∈ gsM := List.mem_cons_of_mem _ List.mem_cons_self
    have hm3 : ∀ s ∈ ({t₁, t₂, t₃} : Set K),
        (⟨ox₁ σ s * nA K, mul_mem (ox₁_mem_C0 σ hσ3 s) (nA_mem σ)⟩ : C₀) ∈ gsM := by
      intro s hs'
      rcases hs' with h | h | h
      · subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))
    have hC : C₀ ≤ H' := by
      refine five_lines_generate σ hσ3 hσ1 hspan (fun e f he hf => ?_) (fun e f he hf => ?_)
        (fun s hs' e f he hf => hgen _ (hm3 s hs') e f he hf)
      · have := hgen 1 hm1 e f he hf
        rwa [Subgroup.coe_one, one_mul, inv_one, mul_one] at this
      · exact hgen ⟨nW0 K, nW0_mem σ⟩ hm2 e f he hf
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hC x.2
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  ·
    have hle : Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} ≤ ΛM := by
      rw [Subgroup.closure_le]
      rintro _ ⟨h, hh, a, ha, rfl⟩
      exact hconj h hh a ha
    have hcardΛ : Nat.card ΛM ≤ 2 ^ (2 * f) := by
      choose e f' he hf' hx using fun x : ΛM => x.2
      let F : ΛM → trialityFixedField K σ.toRingHom × trialityFixedField K σ.toRingHom :=
        fun x => (⟨e x, he x⟩, ⟨f' x, hf' x⟩)
      have hF : Function.Injective F := by
        intro x y hxy
        have h1 : e x = e y := congrArg (fun p => (p.1 : K)) hxy
        have h2 : f' x = f' y := congrArg (fun p => (p.2 : K)) hxy
        apply Subtype.ext; apply Subtype.ext
        rw [hx x, hx y, h1, h2]
      calc Nat.card ΛM ≤ Nat.card (trialityFixedField K σ.toRingHom ×
            trialityFixedField K σ.toRingHom) := Nat.card_le_card_of_injective F hF
        _ = 2 ^ (2 * f) := by rw [Nat.card_prod, hk, ← pow_add, two_mul]
    have hlen : gs.length = 5 := by rw [hgs, List.length_map]; rfl
    rw [hlen]
    calc Nat.card (Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹}) ^ (2 * 5) ≤
        (2 ^ (2 * f)) ^ (2 * 5) :=
          Nat.pow_le_pow_left ((Subgroup.card_le_of_le hle).trans hcardΛ) _
      _ = 2 ^ (20 * f) := by rw [← pow_mul]; ring_nf
      _ < n := hn

include hf hK hσ in
theorem classTests_trialityD4 {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L) (hZL : Subgroup.center L = ⊥)
    (e : L ⧸ Subgroup.center L ≃* C₀) :
    B45Tor.ClassTests V L e (fun ξ => ConjC σ (ξ : ModGL TwistTag.D4.tag K) (ox₁ σ 1))
      (5 * f) (2 * f) (if Even f then 1 else 0) := by
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hk := card_fixedField hf hK σ hσ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro E hE
    have hK' : Nat.card K = Nat.card (trialityFixedField K σ.toRingHom) ^ 3 := by rw [hK, hk]
    have h := card_le_of_elemAbelian σ hσ3 hK' E hE.1 hE.2
    rwa [hk, ← pow_mul, mul_comm] at h
  ·
    intro E hE hB
    have h := card_le_of_pure σ hσ3 E hE.1 (fun x hx => by rw [← sq]; exact hE.2 x hx) hB
    rwa [hk, ← pow_mul, mul_comm] at h
  ·
    intro F hF
    exact card_le_index hf K hK σ hσ F hF
  ·
    intro x _ _ hxB
    refine lt_of_lt_of_le ?_ (B45Tor.two_pow_le_index_classB hf hK σ hσ hV L hZL e hxB)
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    by_cases hev : Even f
    · simp only [hev, ↓reduceIte]
      obtain ⟨r, hr⟩ := hev
      omega
    · simp only [hev, ↓reduceIte]
      omega
  ·
    intro x hx2 hxo
    have hα : modelAct L e x * modelAct L e x = 1 := by
      rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]
    obtain ⟨hev, hD⟩ := dispAtOut_outer hf hK σ hσ _ hα hxo
    have h := sq_lt_index_of_dispAtOut L hperf hZL e (Q := outerPrimes f)
      (B45Tor.doubleDispOut_trialityD4 hf hK σ hσ hV L hZL e) x hx2 hD
    simp only [hev, ↓reduceIte]
    calc 2 ^ (2 * (2 * f + 1)) = (2 ^ (2 * f + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
      _ < _ := h
  ·
    intro E hE hEa hB
    refine Or.inr (lineGenTop_of_pure hf hK σ hσ E hE hEa hB ?_)
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (B45Tor.two_pow_le_card hf hK σ hσ hV L hZL e)

end Criterion

end B45D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley B45D4 B45Disp in
theorem asB45TrialityD4_holds :
    AsB45TrialityD4 := by
  refine B45Tor.asB45No2FFor_of_classTests fun V _ _ hV L hq hirr hT => ?_
  obtain ⟨f, hf, hX⟩ := hT
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hX
  have hZL : Subgroup.center ↥L = ⊥ := by
    have : Group.IsPerfect ↥L := hq.1
    have : Finite (MulAut V) := B42Disp.finite_mulAut
    have h0 := CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hX
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le
      (by rw [QuotientGroup.ker_mk']; exact odd_card_center_of_isIrrSec hV hirr)
    rwa [QuotientGroup.ker_mk'] at h0
  exact ⟨hZL, graphFixedRootGroup TwistTag.D4 K σ.toRingHom, inferInstance, e, _, _, _, _,
    classTests_trialityD4 hf hK σ hσ (fun v => by rw [← pow_two]; exact hV v) L hq.1 hZL e⟩

end CFSG.Quasithin
