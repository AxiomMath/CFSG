module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusWitt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

theorem charSum_bot {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : OrdPNsOm.charSum Q (⊥ : Submodule K V) = 1 := by
  rw [OrdPNsOm.charSum, finsum_unique]
  change OrdPNsOm.chi (Q 0) = 1
  rw [QuadraticMap.map_zero, OrdPNsOm.chi_zero]

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private theorem exists_torus_frame_of_block {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [Nontrivial D] {c : D →ₗ[K] D} {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x) (hcp : cE ^ p = 1)
    (hD : SpNS.SpBlockExists K p D c) (hc1 : ∀ u : D, ∃ u₀, c u₀ - u₀ = u)
    (hfix : ∀ x, c x = x → x = 0) (htr : CoordSpNs.FormTransitive K D cE)
    (hO : ∀ ω : LinearMap.BilinForm K D, ω.IsAlt → ω.Nondegenerate →
      (∀ x y, ω (cE x) (cE y) = ω x y) →
        CoordSpNs.galSigns p (Nat.card K) ≤ CoordSpNs.twistGroup ω cE hcp)
    (hdim : finrank K D = 2)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (cE x) = (cE ^ e.val) (θ x)) → e = 1 ∨ e = -1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V))
      (F : SevOm.Frame Q p A r),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ (∀ j, finrank K (F.U j) = 2) ∧
      finrank K V ≤ 2 * r + 2 ∧ Function.Injective τ ∧
      τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧ finrank K V = 2 * r + 2 ∧
          ∀ i : Fin r, ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) := by
  classical
  have hpp : p.Prime := Fact.out
  have : Finite D := Module.finite_of_finite K
  have : Finite V := Module.finite_of_finite K
  have hAO : ∀ b ∈ A, b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun b hb =>
    OmMv.orthDerived_le_O Q (hAΩ hb)
  set S : Set (Module.End K V) := {x | ∃ b ∈ A, x = (b : V →ₗ[K] V)} with hS
  have hAlt : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    change (b : V →ₗ[K] V) * b' = b' * b
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hAcomm b hb b' hb']
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [OmMv.toLinearMap_pow, hApow b hb]
    rfl
  have hSB : ∀ x ∈ S, ∀ u w, polarBilin Q (x u) (x w) = polarBilin Q u w := by
    rintro _ ⟨b, hb, rfl⟩ u w
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO b hb) u w
  have hS1 : ∃ x ∈ S, x ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    exact ⟨b, ⟨b, hb, rfl⟩, fun h => hb1 (LinearEquiv.toLinearMap_injective h)⟩
  obtain ⟨s, κ, _, Φ, ω, hωa, hωnd, hωc, hΦS, hdec⟩ := CoordSpNs.exists_normFrame hcE hD
    hpp.one_lt.le hc1 htr hAlt hQ S hSc hSp hSB hS1
  have hΦS' : ∀ b ∈ A, ∃ k : Fin s → ℕ, ∀ d w, b (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w) :=
    fun b hb => hΦS _ ⟨b, hb, rfl⟩
  obtain ⟨r, a, F, ha, hFι, hblk, hFU⟩ :=
    OmMv.exists_frame hQ hT hp2 hAΩ hmax hcE hcp hfix hωnd hΦS' hdec
  have hpiece : ∀ j, finrank K (F.U j) = 2 := fun j => by
    rw [hFU j]
    exact (finrank_pieceSub Φ a j).trans hdim
  have hc1E : ∀ u, ∃ u₀, cE u₀ - u₀ = u := fun u => by
    obtain ⟨u₀, h⟩ := hc1 u
    exact ⟨u₀, by rw [hcE]; exact h⟩
  have hfixE : ∀ x, cE x = x → x = 0 := fun x h => hfix x (by rw [← hcE]; exact h)
  set τ := coordTorus Φ hcp a with hτ
  have hτF : ∀ f, τ f = F.ι (piMul r p f) := fun f => by rw [hτ, coordTorus_eq, hFι]
  have hτinj : Function.Injective τ := fun f f' h =>
    (piMul r p).injective (F.inj (by rw [← hτF, ← hτF]; exact h))
  have hτrange : τ.range = A := by
    rw [← F.range]
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨piMul r p f, (hτF f).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(piMul r p).symm t, by rw [hτF, MulEquiv.apply_symm_apply]⟩
  have hτA : ∀ f, τ f ∈ A := fun f => hτrange ▸ ⟨f, rfl⟩
  have hτO : ∀ f, τ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hAO _ (hτA f)
  have hτiso : ∀ f v, Q (τ f v) = Q v := fun f v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hτO f) v
  have hsw : ∀ i j : Fin r, i ≠ j → CoordOm.RealizedIn F (orthDerived Q) (Equiv.swap i j) 1 :=
    fun i j hij => OmMv.realizedIn_swap hQ hT hdec hωa hωnd hcp hc1E ha F hFι hblk hij
  have htw : ∀ i : Fin r, CoordOm.RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1
      (CoordOm.singleTw (-1) i) := by
    intro i
    obtain ⟨T, hT'⟩ := CoordSpNs.mem_twistGroup.mp
      (hO ω hωa hωnd hωc (CoordSpNs.neg_one_mem_galSigns p (Nat.card K)))
    exact OmMv.realizedIn_twist hdec hcp hc1E ha F hFι hblk i hT'
  have hconj : ∀ {H : Subgroup (V ≃ₗ[K] V)} {π : Equiv.Perm (Fin r)} {η : Fin r → (ZMod p)ˣ},
      CoordOm.RealizedIn F H π η → ∃ w ∈ H, ∀ f : Fin r → Multiplicative (ZMod p),
        w * τ f * w⁻¹ = F.ι (ofAdd fun k => (η k : ZMod p) * toAdd (f (π k))) := by
    intro H π η h
    obtain ⟨w, hw, hws⟩ := exists_conj_of_realizedIn h
    exact ⟨w, hw, fun f => by rw [hτF]; exact hws f⟩
  have hperm : ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f,
      w * τ f * w⁻¹ = τ (permAut σ f) := by
    intro σ
    obtain ⟨w, hw, hws⟩ := hconj (CoordOm.realizedIn_perm hsw σ⁻¹)
    exact ⟨w, hw, fun f => by rw [hws, hτF, piMul_permAut]⟩
  have hdinv : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f,
      w * τ f * w⁻¹ = τ (dinv i j f) := by
    intro i j hij
    obtain ⟨w, hw, hws⟩ := hconj (CoordOm.realizedIn_pairTw hij (hsw i j hij) (htw i))
    exact ⟨w, hw, fun f => by rw [hws, hτF, piMul_dinv hij]; rfl⟩
  have hsgnO : ∀ i : Fin r, ∃ σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ f,
      σ * τ f * σ⁻¹ = τ (sgnAut i f) := by
    intro i
    obtain ⟨w, hw, hws⟩ := hconj (htw i)
    exact ⟨w, hw, fun f => by rw [hws, hτF, piMul_sgnAut]; rfl⟩
  have hnorm : ∀ g : V ≃ₗ[K] V, (∀ b ∈ A, g * b * g⁻¹ ∈ A) →
      ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
    intro g hg
    refine coordTorus_normalizer Φ hcp hfixE hc1E ha hτinj hroots g fun f => ?_
    have h1 : g * τ f * g⁻¹ ∈ τ.range := by
      rw [hτrange]
      exact hg _ (hτA f)
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', hf'.symm⟩
  have hr : 0 < r := by
    obtain ⟨b, hb, hb1⟩ := hne
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      rw [← hτrange] at hb
      obtain ⟨f, rfl⟩ := hb
      exact absurd (by rw [show f = 1 from funext fun i => i.elim0, map_one]) hb1
    · exact hr0
  have hdimV : finrank K V ≤ 2 * r + 2 := by
    have hV := Submodule.finrank_sup_add_finrank_inf_eq (actSub Φ a) (fixSub Φ a)
    rw [actSub_sup_fixSub, actSub_inf_fixSub, finrank_top, finrank_bot] at hV
    have hV' : finrank K V = finrank K (actSub Φ a) + finrank K (fixSub Φ a) := by
      simpa using hV
    have h1 : finrank K (actSub Φ a) ≤ 2 * r := by
      rw [finrank_actSub Φ a ha, hdim]
      omega
    have h2 := finrank_fixSub_le_two Φ hcp hQ hfixE ha hdec hωnd hdim hτrange hAΩ hmax hr
    omega
  have htop := charSum_top_eq Φ a hdec (Q := Q)
  have hact := charSum_actSub_modEq Φ hcp hfixE ha hτiso
  refine ⟨r, τ, F, hτF, hpiece, hdimV, hτinj, hτrange, hperm, hdinv, hnorm, ?_⟩
  by_cases hW : fixSub Φ a = ⊥
  · refine Or.inl ⟨?_, ?_⟩
    · rw [htop, hW, charSum_bot, mul_one]
      exact hact
    · rw [finrank_eq_of_fixSub_eq_bot Φ ha hW, hdim, mul_comm]
  · refine Or.inr ⟨?_, ?_, fun i => ?_⟩
    · rw [htop]
      have h1 := hact.mul (charSum_fixSub_modEq_neg_one Φ hcp hQ hfixE ha hdec hωnd hdim hτrange
        hAΩ hmax hτiso hr hW)
      rwa [one_mul] at h1
    · have hV := Submodule.finrank_sup_add_finrank_inf_eq (actSub Φ a) (fixSub Φ a)
      rw [actSub_sup_fixSub, actSub_inf_fixSub, finrank_top, finrank_bot, finrank_actSub Φ a ha,
        hdim] at hV
      have h2 := finrank_fixSub_le_two Φ hcp hQ hfixE ha hdec hωnd hdim hτrange hAΩ hmax hr
      have hpos : 0 < finrank K (fixSub Φ a) :=
        Nat.pos_of_ne_zero fun h => hW (Submodule.finrank_eq_zero.mp h)
      have hnd := nondegOn_fixSub Φ (a := a) hQ hdec
      have heven : Even (finrank K (fixSub Φ a)) := by
        refine LinearMap.BilinForm.IsAlt.even_finrank
          (B := LinearMap.BilinForm.restrict (polarBilin Q) (fixSub Φ a)) (fun x => ?_) ?_
        · change QuadraticMap.polar Q x x = 0
          rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
        · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
          · exact Subtype.ext (hnd x x.2 fun n hn => by
              have := hx ⟨n, hn⟩
              simpa [LinearMap.BilinForm.restrict_apply, polarBilin_apply_apply,
                QuadraticMap.polar_comm] using this)
          · exact Subtype.ext (hnd x x.2 fun n hn => hx ⟨n, hn⟩)
      obtain ⟨k, hk⟩ := heven
      omega
    · obtain ⟨σ, hσO, hσ⟩ := hsgnO i
      exact exists_sgn_mem_orthDerived Φ hcp hQ hT hfixE ha hdec hτO hW i hσO hσ

private theorem exists_torus_frame_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V))
      (F : SevOm.Frame Q p A r),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ (∀ j, finrank K (F.U j) = 2) ∧
      finrank K V ≤ 2 * r + 2 ∧ Function.Injective τ ∧
      τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧ finrank K V = 2 * r + 2 ∧
          ∀ i : Fin r, ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) := by
  classical
  have hpp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h2).symm
  have hne' : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hpp]
    have := hpp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne' (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hpp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζ.pow_eq_one
  have hζ0 : AdjoinRoot.root g ≠ 0 := hζ.ne_zero hpp.ne_zero
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζ.ne_one hpp.one_lt
  have hζ1' : AdjoinRoot.root g ^ (p - 1) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by have := hpp.two_le; omega) (by have := hpp.pos; omega)
  have hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ0
  have hfix : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ d : AdjoinRoot g, μ * d = d → d = 0 :=
    fun μ hμ d hd => by
      have h0 : (μ - 1) * d = 0 := by rw [sub_mul, hd, one_mul, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  have hsurj : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ u : AdjoinRoot g, ∃ u₀, μ * u₀ - u₀ = u :=
    fun μ hμ u => ⟨(μ - 1)⁻¹ * u, by
      rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hμ), one_mul]⟩
  rcases hpq with hpq | hpq
  ·
    have hσ := aeval_pred_ne_zero hpp hp2 hpK hpq hgd
    exact exists_torus_frame_of_block hp2 hQ hT hAΩ hApow hAcomm hmax hne
      (c := (LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft K (AdjoinRoot.root g ^ (p - 1))))
      (cE := CoordSpNs.prC hζ0 hζ0') (fun x => rfl) (CoordSpNs.prC_pow_eq_one hζ0 hζ0' hζp)
      (SpNS.spBlockExists_paired hpp hpK hgd hσ)
      (fun u => by
        obtain ⟨u₁, hu₁⟩ := hsurj _ hζ1 u.1
        obtain ⟨u₂, hu₂⟩ := hsurj _ hζ1' u.2
        exact ⟨(u₁, u₂), Prod.ext hu₁ hu₂⟩)
      (fun d hd => by
        obtain ⟨μ, ν⟩ := d
        rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
        exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
      (CoordSpNs.formTransitive_pr hζ0 hζ0' hζp hζ hσ)
      (fun ω hωa hωnd hωc => CoordSpNs.galSigns_le_twistGroup_pr hζ0 hζ0' hζp hζ hσ hωa hωnd hωc)
      (finrank_pr hpp hp2 hpq hgd)
      (fun e θ hθ hθc => eq_one_or_neg_one_pr hpp hp2 hpK hpq hgd hζ0 hζ0' e θ hθ hθc)
  ·
    have hσ := SpNS.aeval_root_pow_pred hpp hpK hgd hpq
    exact exists_torus_frame_of_block hp2 hQ hT hAΩ hApow hAcomm hmax hne
      (c := LinearMap.mulLeft K (AdjoinRoot.root g)) (cE := CoordSpNs.sdC hζ0) (fun x => rfl)
      (CoordSpNs.sdC_pow_eq_one hζ0 hζp) (SpNS.spBlockExists_selfDual hpp hp2 hpK hgd hσ)
      (hsurj _ hζ1) (fun d hd => hfix _ hζ1 d hd) (CoordSpNs.formTransitive_sd hζp hζ0)
      (fun ω hωa hωnd hωc => CoordSpNs.galSigns_le_twistGroup_sd hζp hζ hσ hζ0 hωa hωnd hωc)
      (finrank_sd hpp hp2 hpK hgd hpq)
      (fun e θ hθ hθc => eq_one_or_neg_one_sd hpp hp2 hpK hgd hpq hζ0 e θ hθ hθc)

theorem exists_torus {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)), Function.Injective τ ∧
      τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧
          ∀ i : Fin r, ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) := by
  obtain ⟨r, τ, F, -, -, -, hτinj, hτrange, hperm, hdinv, hnorm, hchar⟩ :=
    exists_torus_frame_aux hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  exact ⟨r, τ, hτinj, hτrange, hperm, hdinv, hnorm, hchar.imp id fun h => ⟨h.1, h.2.2⟩⟩

theorem exists_torus_frame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)) (F : SevOm.Frame Q p A r),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ (∀ j, finrank K (F.U j) = 2) ∧
      finrank K V ≤ 2 * r + 2 ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) := by
  obtain ⟨r, τ, F, hτF, hpiece, hdimV, -, -, hperm, hdinv, -, -⟩ :=
    exists_torus_frame_aux hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  exact ⟨r, τ, F, hτF, hpiece, hdimV, hperm, hdinv⟩

theorem three_dvd_card_sub_or_add : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hK' : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hK]
  have h3not : ¬ 3 ∣ Nat.card K := by
    rw [hK']
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32
  have hmod : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by
    have hlt : Nat.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : Nat.card K % 3 ≠ 0 := fun h => h3not (Nat.dvd_of_mod_eq_zero h)
    omega
  have hdecomp : Nat.card K = 3 * (Nat.card K / 3) + Nat.card K % 3 := by
    have := Nat.div_add_mod (Nat.card K) 3
    omega
  rcases hmod with hmod | hmod
  · left
    refine ⟨Nat.card K / 3, ?_⟩
    omega
  · right
    refine ⟨Nat.card K / 3 + 1, ?_⟩
    omega

theorem exists_torus_orthDerived_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (E : Subgroup ↥(orthDerived Q)) (hE : IsElemAbelian p E)
    (hne : ∃ b ∈ E, b ≠ 1)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* ↥(orthDerived Q)),
      Function.Injective τ ∧ τ.range = E ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : ↥(orthDerived Q), (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧
          ∀ i : Fin r, ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A := E.map (orthDerived Q).subtype
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE hx hy]
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, hsc ⟨g, hg⟩ (fun e he => Subtype.ext (hgc _ ⟨e, he, rfl⟩))
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)), rfl⟩
  have hneA : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    refine ⟨(b : V ≃ₗ[K] V), ?_, ?_⟩
    · exact ⟨b, hb, rfl⟩
    · intro h
      apply hb1
      exact Subtype.ext h
  obtain ⟨r, τ, hτinj, hτA, hperm, hdinv, hnorm, hW⟩ :=
    exists_torus (p := p) (K := K) (V := V) (Q := Q) hp2 hpq hQ hT hAΩ hApow hAcomm hmax hneA
  have hτmem : ∀ f, τ f ∈ orthDerived Q := fun f => hAΩ (hτA ▸ ⟨f, rfl⟩)
  set τ' : (Fin r → Multiplicative (ZMod p)) →* ↥(orthDerived Q) := τ.codRestrict _ hτmem
  have hrange : τ'.range = E := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      have h1 : τ f ∈ A := hτA ▸ ⟨f, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = τ' f := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      have h1 : (x : V ≃ₗ[K] V) ∈ τ.range := hτA ▸ ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := h1
      exact ⟨f, Subtype.ext hf⟩
  refine ⟨r, τ', fun f f' h => hτinj (congrArg Subtype.val h), hrange, fun σ => ?_,
    fun i j hij => ?_, fun g hg => ?_, ?_⟩
  · obtain ⟨w, hw, hws⟩ := hperm σ
    exact ⟨⟨w, hw⟩, fun f => Subtype.ext (hws f)⟩
  · obtain ⟨w, hw, hws⟩ := hdinv i j hij
    exact ⟨⟨w, hw⟩, fun f => Subtype.ext (hws f)⟩
  · obtain ⟨π, ε, hε, hrel⟩ := hnorm (g : V ≃ₗ[K] V) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨g * x * g⁻¹, hg x hx, rfl⟩)
    exact ⟨π, ε, hε, fun f f' h i => hrel f f' (congrArg Subtype.val h) i⟩
  · rcases hW with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, fun i => ?_⟩
      obtain ⟨w, hw, hws⟩ := h2 i
      exact ⟨⟨w, hw⟩, fun f => Subtype.ext (hws f)⟩

theorem exists_torus_frame_full {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V))
      (F : SevOm.Frame Q p A r),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ (∀ j, finrank K (F.U j) = 2) ∧
      finrank K V ≤ 2 * r + 2 ∧ Function.Injective τ ∧
      τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧ finrank K V = 2 * r + 2 ∧
          ∀ i : Fin r, ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) :=
  exists_torus_frame_aux hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne

end Core

end OrthTorus

end CFSG.StandardType

end
