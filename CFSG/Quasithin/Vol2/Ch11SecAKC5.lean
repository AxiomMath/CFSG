module

public import CFSG.Quasithin.Vol2.Ch11SecAKC4
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGD
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAKC3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Quasithin.Vol2.Ch11.SecS (gammaW centW)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (map_inf_sectionCentralizer pCoreOf_map_of_injective)

namespace KC5

variable {K : Type} [Field K] [CharP K 2]

theorem frobConj_mul (σ : K ≃+* K) (a b : ↥(cayleyGroup K)) :
    frobConj σ (a * b) = frobConj σ a * frobConj σ b := by
  apply cayley_ext
  intro w
  rw [← frobQ_symm σ w, g2Act_frobConj, g2Act_mul_apply, g2Act_mul_apply, g2Act_frobConj,
    g2Act_frobConj]

theorem frobConj_one (σ : K ≃+* K) : frobConj σ (1 : ↥(cayleyGroup K)) = 1 := by
  apply cayley_ext
  intro w
  rw [← frobQ_symm σ w, g2Act_frobConj]
  simp only [map_one]
  rfl

theorem frobConj_inv (σ : K ≃+* K) (a : ↥(cayleyGroup K)) :
    frobConj σ a⁻¹ = (frobConj σ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← frobConj_mul, inv_mul_cancel, frobConj_one])

theorem frobConj_refl (a : ↥(cayleyGroup K)) : frobConj (RingEquiv.refl K) a = a := by
  apply cayley_ext
  intro w
  have h := g2Act_frobConj (RingEquiv.refl K) a w
  have e : ∀ v : Ix3 → K, frobQ ((RingEquiv.refl K : K ≃+* K) : K →+* K) v = v := fun v => by
    funext j
    rfl
  rwa [e, e] at h

omit [CharP K 2] in
theorem frobQ_eu (σ : K ≃+* K) (t : K) : frobQ (σ : K →+* K) (eu 0 t) = eu 0 (σ t) := by
  funext j
  simp [frobQ, eu, Pi.single_apply]
  split_ifs <;> simp

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem conj_rhoG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    {τ : MulAut W} (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {c : K} (hc : c ≠ 0)
    {γ : ↥(cayleyGroup K)} {σ : K ≃+* K} (hτ : ∀ w, f (τ w) = c • g2Act γ (frobQ σ (f w)))
    (δ : ↥(cayleyGroup K)) :
    τ * ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) * τ⁻¹ =
      ((rhoG hc0 hc1 π (γ * frobConj σ δ * γ⁻¹) : ↥H) : MulAut W) := by
  obtain ⟨ε, hε⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hτH _ (rhoG hc0 hc1 π δ).2⟩
  have hτi : ∀ w, f (τ⁻¹ w) =
      frobQ (σ.symm : K →+* K) (g2Act γ⁻¹ (c⁻¹ • f w)) := fun w => by
    have h := hτ (τ⁻¹ w)
    rw [MulAut.apply_inv_self] at h
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul, g2Act_inv_apply, frobQ_symm']
  have key : ε = γ * frobConj σ δ * γ⁻¹ := by
    apply cayley_ext
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [← IsCoord.actG hf hc0 hc1, hε]
    change f ((τ * _ * τ⁻¹) w) = _
    rw [MulAut.mul_apply, MulAut.mul_apply, hτ, IsCoord.actG hf hc0 hc1, hτi,
      ← g2Act_frobConj, frobQ_symm, G2Q8.g2Act_smul, G2Q8.g2Act_smul, G2Q8.g2Act_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul, g2Act_mul_apply, g2Act_mul_apply]
  rw [← key, hε]

end KC5

open KC3 KC4 KC5 in
theorem factFieldAutPointG2_holds : FactFieldAutPointG2 := by
  intro K _ _ hK W _ _ hW H Z π hπ _ P hP U₁ hU₁ D hD
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK'
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 : 4 ≤ Nat.card K := by omega
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card (le_refl 2) hK'
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK' (by omega) hf hc0 hc1 hP
  rw [eq_map_psiG_of_sylow hg, inf_normalizer_eqG hf hc0 hc1 g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torusG hf hc0 hc1 hK' (by omega) g hD
  have hg' := sylow_conj_mulG hg hx
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg' (by rw [hK]; exact hU₁)
  subst hU1 hDx
  set g' := g * x with hg'def
  set ψ := psiG hc0 hc1 π g' with hψdef
  have hψ : Function.Injective ψ := psiG_injective hf hc0 hc1 g'
  have hΓ1 : gammaW H (hf.pre (gmapG g' (stdF K 1)).toAddSubgroup) = (stabV0 K).map ψ :=
    gammaW_one_eqG h4 hf hc0 hc1 g'
  have hC₁ : centW ((torusG K).map ψ) (gammaW H (hf.pre (gmapG g' (stdF K 1)).toAddSubgroup)) =
      ((g2T (F := K)).comp (torHomC1 K)).range.map ψ := by
    rw [centW, hΓ1, pCoreOf_map_of_injective _ hψ, map_inf_sectionCentralizer _ hψ,
      torusG_inf_sc1]
  have hNU : H ⊓ stabW (hf.pre (gmapG g' (stdF K 1)).toAddSubgroup) =
      (stabQ (stdF K 1)).map ψ := (map_stabQ_eq hf hc0 hc1 g' (stdF K 1)).symm
  intro τ hτH hτZ hτU ⟨k, hk⟩ hout d hd
  have hτZz : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (mem_stabW.mp hτZ z).mp hz
  have hτZz' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz =>
    (mem_stabW.mp ((stabW Z).inv_mem hτZ) z).mp hz
  have hτH' : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := fun h hh =>
    inv_conj_mem hk (S := (H : Set (MulAut W))) hτH hh
  obtain ⟨c, γ, σ, hc, hτf⟩ :=
    exists_smul_frob_of_normalizes hf hc0 hc1 hK' (le_refl 2) τ hτZz hτZz' hτH hτH'
  set γ₂ := g'⁻¹ * γ * frobConj σ g' with hγ₂def
  have hconj : ∀ δ, τ * ψ δ * τ⁻¹ = ψ (γ₂ * frobConj σ δ * γ₂⁻¹) := fun δ => by
    have e : γ * frobConj σ (g' * δ * g'⁻¹) * γ⁻¹ = g' * (γ₂ * frobConj σ δ * γ₂⁻¹) * g'⁻¹ := by
      rw [frobConj_mul, frobConj_mul, frobConj_inv, hγ₂def]
      group
    rw [hψdef, psiG_apply, conj_rhoG hf hc0 hc1 hτH hc hτf, psiG_apply, e]
  have hγ₂F : ∀ y ∈ stdF K 1, g2Act γ₂ y ∈ stdF K 1 := by
    intro y hy
    obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hy
    obtain ⟨w, hw⟩ := hf.surj (g2Act g' (eu 0 (σ.symm t)))
    have hwU : w ∈ hf.pre (gmapG g' (stdF K 1)).toAddSubgroup := by
      change f w ∈ gmapG g' (stdF K 1)
      rw [hw, mem_gmapG, g2Act_inv_apply]
      exact mem_stdF_one_iff.mpr ⟨σ.symm t, by rw [smul_eu, mul_one]⟩
    have h1 : f (τ w) ∈ gmapG g' (stdF K 1) := (mem_stabW.mp hτU w).mp hwU
    rw [hτf, hw, ← g2Act_frobConj, frobQ_eu, RingEquiv.apply_symm_apply, mem_gmapG,
      G2Q8.g2Act_smul, ← g2Act_mul_apply, ← g2Act_mul_apply] at h1
    rw [smul_eu, mul_one, show g2Act γ₂ (eu 0 t) = c⁻¹ • (c • g2Act γ₂ (eu 0 t)) by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]]
    exact (stdF K 1).smul_mem _ h1
  have hγ₂ : γ₂ ∈ stabQ (stdF K 1) := by
    rw [mem_stabQ]
    intro w
    refine ⟨hγ₂F w, fun hw => ?_⟩
    let φ : ↥(stdF K 1) → ↥(stdF K 1) := fun y => ⟨g2Act γ₂ y, hγ₂F y y.2⟩
    have hφ : Function.Injective φ := fun a b hab => Subtype.ext (by
      have h := congrArg (fun y : ↥(stdF K 1) => g2Act γ₂⁻¹ (y : Ix3 → K)) hab
      simpa [φ, g2Act_inv_apply] using h)
    obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hφ) ⟨_, hw⟩
    have e := congrArg (fun y : ↥(stdF K 1) => g2Act γ₂⁻¹ (y : Ix3 → K)) hy
    simp only [φ, g2Act_inv_apply] at e
    rw [← e]
    exact y.2
  rw [hΓ1] at hout
  rcases C11P9B.ringHom_eq_id_or_sq hK (σ : K →+* K) with hid | hsq
  ·
    exfalso
    have hσ1 : σ = RingEquiv.refl K := RingEquiv.ext hid
    obtain ⟨γ', hγ'S, hγ'⟩ := inner_of_mem_stabQ_one hγ₂
    obtain ⟨g₀, hg₀, hg₀n⟩ := hout (ψ γ') ⟨γ', hγ'S, rfl⟩
    apply hg₀n
    obtain ⟨s, hs, rfl⟩ := hg₀
    rw [hconj, hσ1, frobConj_refl, pCoreOf_map_of_injective _ hψ]
    exact ⟨_, inKer_iff.mp (hγ' s hs), by simp only [map_mul, map_inv]⟩
  ·
    rw [hC₁] at hd
    obtain ⟨_, ⟨c', rfl⟩, rfl⟩ := hd
    have h3 : ∀ u : Kˣ, u ^ 3 = 1 := fun u => by
      have h := pow_card_eq_one' (G := Kˣ) (x := u)
      rwa [Nat.card_units, hK] at h
    have hσu : ∀ u : Kˣ, Units.map (σ : K →* K) u = u⁻¹ := fun u => by
      have hsq' : u ^ 2 = u⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
      apply Units.ext
      rw [Units.coe_map, MonoidHom.coe_ofClass, ← hsq', Units.val_pow_eq_pow_val]
      have h1 := hsq (u : K)
      rwa [RingEquiv.coe_toRingHom] at h1
    have hft : frobConj σ (g2T (torHomC1 K c')) = g2T (torHomC1 K c'⁻¹) := by
      rw [frobConj_g2T, torHomC1_apply, torHomC1_apply, hσu, hσu, _root_.mul_inv_rev]
    have hcomm := comm_torC1_mem c'⁻¹ hγ₂
    rw [MonoidHom.comp_apply, hconj, hft, hNU, pCoreOf_map_of_injective _ hψ]
    refine ⟨_, pCoreOf_stabV0_le (inKer_iff.mp hcomm), ?_⟩
    simp only [map_mul, map_inv, inv_inv]

end CFSG.Quasithin.Vol2.Ch11.SecA
