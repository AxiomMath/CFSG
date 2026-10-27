module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrameMap
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggL45E67_torusElt_pow {F : Type} [Field F]
    (i : Fin Tag.E6.rank) (u : Fˣ) (m : ℕ) :
    torusElt Tag.E6 F i u ^ m = torusElt Tag.E6 F i (u ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ n ih => rw [pow_succ, ih, ← torusElt_mul, ← pow_succ]

private theorem ggL45E67_torusElt_pow_eq_one {K : Type} [Field K]
    (i : Fin Tag.E6.rank)
    {u : Kˣ} {m : ℕ} (hu : u ^ m = 1) :
    (⟨torusElt Tag.E6 K i u, torusElt_mem_adjointGroup i u⟩ :
      ↥(adjointGroup Tag.E6 K)) ^ m = 1 := by
  apply Subtype.ext
  change ((torusElt Tag.E6 K i u) ^ m : ModGL Tag.E6 K) = 1
  rw [ggL45E67_torusElt_pow, hu, torusElt_one]

private theorem ggL45E67_pair_indep {F : Type} [Field F]
    {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {a b : ℕ}
    (h : torusElt Tag.E6 F 0 ω ^ a * torusElt Tag.E6 F 1 ω ^ b = 1) :
    3 ∣ a ∧ 3 ∣ b := by
  have h00 : Tag.E6.cartan (0 : Fin Tag.E6.rank) 0 = 2 := by decide
  have h01 : Tag.E6.cartan (0 : Fin Tag.E6.rank) 1 = 0 := by decide
  have h10 : Tag.E6.cartan (1 : Fin Tag.E6.rank) 0 = 0 := by decide
  have h11 : Tag.E6.cartan (1 : Fin Tag.E6.rank) 1 = 2 := by decide
  have hord : orderOf ω = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hω3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hω1
    · exact h1
  have htuple : (fun l => ω ^ Tag.E6.cartan 0 l) ^ a *
      (fun l => ω ^ Tag.E6.cartan 1 l) ^ b = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := F)
    rw [rootDiagUnit_mul, ← rootDiagUnit_pow, ← rootDiagUnit_pow, rootDiagUnit_one,
      ← torusElt_eq_rootDiagUnit, ← torusElt_eq_rootDiagUnit, h]
  have h2a : ω ^ (2 * a) = 1 := by
    have h1 := congrFun htuple 0
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply] at h1
    rw [h00, h10] at h1
    have h2 : (ω ^ 2) ^ a = 1 := by simpa using h1
    rwa [← pow_mul] at h2
  have h2b : ω ^ (2 * b) = 1 := by
    have h1 := congrFun htuple 1
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply] at h1
    rw [h01, h11] at h1
    have h2 : (ω ^ 2) ^ b = 1 := by simpa using h1
    rwa [← pow_mul] at h2
  have hc : Nat.Coprime 3 2 := by norm_num
  exact ⟨hc.dvd_of_dvd_mul_left (by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h2a),
    hc.dvd_of_dvd_mul_left (by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h2b)⟩

private theorem ggL45E67_indep_of_hom {F : Type} [Field F]
    {R : Type} [Group R] {Ψ : R →* ModGL Tag.E6 F}
    {t₁ t₂ : R} {ω : Fˣ} {k : ℕ}
    (h₁ : Ψ t₁ = torusElt Tag.E6 F 0 ω) (h₂ : Ψ t₂ = torusElt Tag.E6 F 1 ω)
    (hω3 : (ω ^ k) ^ 3 = 1) (hω1 : ω ^ k ≠ 1) (i j : ℕ)
    (h : (t₁ ^ k) ^ i * (t₂ ^ k) ^ j = 1) : 3 ∣ i ∧ 3 ∣ j := by
  have h1 : Ψ (t₁ ^ k) = torusElt Tag.E6 F 0 (ω ^ k) := by
    rw [map_pow, h₁, ggL45E67_torusElt_pow]
  have h2 : Ψ (t₂ ^ k) = torusElt Tag.E6 F 1 (ω ^ k) := by
    rw [map_pow, h₂, ggL45E67_torusElt_pow]
  have h3 : (torusElt Tag.E6 F 0 (ω ^ k)) ^ i * (torusElt Tag.E6 F 1 (ω ^ k)) ^ j = 1 := by
    have h4 := congrArg Ψ h
    rw [map_mul, map_one, map_pow, h1, map_pow, h2] at h4
    exact h4
  exact ggL45E67_pair_indep hω3 hω1 h3

private theorem ggL45E67_pow_sub_one {F : Type} [Field F] {ω : Fˣ} {s : ℕ}
    (hω : orderOf ω = 3 ^ s) (hs1 : 1 ≤ s) :
    (ω ^ 3 ^ (s - 1)) ^ 3 = 1 ∧ ω ^ 3 ^ (s - 1) ≠ 1 := by
  have hωs : ω ^ 3 ^ s = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hs1, hωs]
  · intro hone
    have hdvd : 3 ^ s ∣ 3 ^ (s - 1) := by rw [← hω]; exact orderOf_dvd_of_pow_eq_one hone
    have hlt : 3 ^ (s - 1) < 3 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hle : 3 ^ s ≤ 3 ^ (s - 1) := Nat.le_of_dvd (by positivity) hdvd
    omega

private theorem ggL45E67_mem_map_conj {G : Type} [Group G] (T : Subgroup G) (x y : G) :
    y ∈ T.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ T := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hty⟩
    rw [← hty, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert ht using 1
    group
  · intro h
    exact ⟨x⁻¹ * y * x, h, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

private theorem ggL45E67_pair_exists_E6 {K : Type} [Field K] [Finite K]
    {R : Type} [Group R]
    (T : Subgroup R) (ε : R ≃* ↥(adjointGroup Tag.E6 K)) (Θ : MulAut R)
    (hfT : ∀ u : ↥(adjointGroup Tag.E6 K),
      u ∈ (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K) → Θ (ε.symm u) ∈ T)
    (s : ℕ) (hs1 : 1 ≤ s) (hs : 3 ^ s ∣ Nat.card K - 1) :
    ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 ^ s :=
    CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (d := 3 ^ s) hs
  obtain ⟨hω3, hω1⟩ := ggL45E67_pow_sub_one hω hs1
  have hωs : ω ^ 3 ^ s = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  set y₁ : ↥(adjointGroup Tag.E6 K) := ⟨torusElt Tag.E6 K 0 ω, torusElt_mem_adjointGroup 0 ω⟩
    with hy₁
  set y₂ : ↥(adjointGroup Tag.E6 K) := ⟨torusElt Tag.E6 K 1 ω, torusElt_mem_adjointGroup 1 ω⟩
    with hy₂
  let Ψ : R →* ModGL Tag.E6 K :=
    (adjointGroup Tag.E6 K).subtype.comp (ε.toMonoidHom.comp Θ.symm.toMonoidHom)
  have happ : ∀ y : R, Ψ y = (ε (Θ.symm y) : ModGL Tag.E6 K) := fun y => rfl
  refine ⟨Θ (ε.symm y₁), ?_, Θ (ε.symm y₂), ?_, ?_, ?_, ?_⟩
  · exact hfT y₁ (by rw [hy₁]; exact torusElt_mem_torusGroup 0 ω)
  · exact hfT y₂ (by rw [hy₂]; exact torusElt_mem_torusGroup 1 ω)
  · have hy : y₁ ^ 3 ^ s = 1 := by
      rw [hy₁]
      exact ggL45E67_torusElt_pow_eq_one 0 hωs
    rw [← map_pow, ← map_pow, hy, map_one, map_one]
  · have hy : y₂ ^ 3 ^ s = 1 := by
      rw [hy₂]
      exact ggL45E67_torusElt_pow_eq_one 1 hωs
    rw [← map_pow, ← map_pow, hy, map_one, map_one]
  · intro i j hij
    have h₁ : Ψ (Θ (ε.symm y₁)) = torusElt Tag.E6 K 0 ω := by
      rw [happ, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, hy₁]
    have h₂ : Ψ (Θ (ε.symm y₂)) = torusElt Tag.E6 K 1 ω := by
      rw [happ, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, hy₂]
    exact ggL45E67_indep_of_hom h₁ h₂ hω3 hω1 i j hij

private theorem ggL45E67_tFrame_good
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {g : ModGL Tag.E6 Ω} (hL : E6ThreeModel.IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3)
    {D : E6ThreeModel.FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : E6ThreeModel.TSpec hn hK σ hσ Fr hFr g hζ D) : D.Good :=
  { center := E6ThreeModel.tFrame_center hn hK σ hσ
    faithful := E6ThreeModel.tFrame_faithful hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    shape := E6ThreeModel.tFrame_shape hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    torus := E6ThreeModel.tFrame_torus hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    cent := E6ThreeModel.tFrame_cent hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    inner := E6ThreeModel.tFrame_inner hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    weyl := E6ThreeModel.tFrame_weyl hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    modules := E6ThreeModel.tFrame_modules hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    norm := E6ThreeModel.tFrame_norm hn hK σ hσ Fr hFr h3 hL hζ hζo hD
    aut := E6ThreeModel.tFrame_aut hn hK σ hσ Fr hFr h3 hL hζ hζo hD }

private theorem ggL45E67_twE6_elt
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {x : ModGL Tag.E6 Ω} (hx : E6ThreeModel.IsLang Fr x)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    {D : E6ThreeModel.FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : E6ThreeModel.TSpec hn hK σ hσ Fr hFr x hζ D)
    {R : Type} [Group R] (ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (i : Fin Tag.E6.rank) (s : ℕ) (ω : Ωˣ) (hωs : ω ^ 3 ^ s = 1)
    (hωq : ω ^ (2 ^ n + 1) = 1) :
    ∃ t ∈ (D.map ε.symm).Tor, t ^ 3 ^ s = 1 ∧
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε t : ModGL TwistTag.E6.tag K) =
        x * torusElt Tag.E6 Ω i ω * x⁻¹ := by
  classical
  obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp
    (E6ThreeModel.torusElt_mem_Cgrp hn hK σ hσ Fr hFr h3 hx hζ hD i ω hωq)
  refine ⟨ε.symm ⟨c, hc⟩, ?_, ?_, ?_⟩
  · rw [E6ThreeModel.FrameData.mem_map_tor, MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
      hD.tor_eq]
    change baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c ∈
      (torusGroup Tag.E6 Ω).map (MulAut.conj x).toMonoidHom
    rw [ggL45E67_mem_map_conj, hceq,
      show x⁻¹ * (x * torusElt Tag.E6 Ω i ω * x⁻¹) * x = torusElt Tag.E6 Ω i ω by group]
    exact torusElt_mem_torusGroup i ω
  · have h1 : (⟨c, hc⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ^ 3 ^ s = 1 := by
      apply Subtype.ext
      change (c : ModGL Tag.E6 K) ^ 3 ^ s = 1
      apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω)
      erw [map_pow]
      rw [map_one, hceq,
        show x * torusElt Tag.E6 Ω i ω * x⁻¹ =
          MulAut.conj x (torusElt Tag.E6 Ω i ω) from rfl,
        ← map_pow, MulAut.conj_apply,
        show (torusElt Tag.E6 Ω i ω) ^ 3 ^ s = 1 by
          rw [ggL45E67_torusElt_pow, hωs, torusElt_one]]
      group
    rw [← map_pow, h1, map_one]
  · rw [show ε (ε.symm ⟨c, hc⟩) = ⟨c, hc⟩ from MulEquiv.apply_symm_apply ε ⟨c, hc⟩]
    exact hceq

private theorem ggL45E67_exists_root_twE6 {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {Ω : Type} [Field Ω] [Algebra K Ω]
    (s : ℕ) (hs1 : 1 ≤ s) (hs : 3 ^ s ∣ 2 ^ n + 1) :
    ∃ ω : Ωˣ, orderOf ω = 3 ^ s ∧ ω ^ (2 ^ n + 1) = 1 ∧ (ω ^ 3 ^ (s - 1)) ^ 3 = 1 ∧
      ω ^ 3 ^ (s - 1) ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have hdvd : 3 ^ s ∣ Nat.card K - 1 := by
    have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [← Nat.sq_sub_sq, one_pow]
    rw [hK, h1]
    exact dvd_mul_of_dvd_left hs _
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Kˣ, orderOf ω₀ = 3 ^ s :=
    CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (d := 3 ^ s) hdvd
  set ω : Ωˣ := Units.map (algebraMap K Ω).toMonoidHom ω₀ with hωdef
  have hω : orderOf ω = 3 ^ s := by
    rw [hωdef, orderOf_injective (Units.map (algebraMap K Ω).toMonoidHom)
      (Units.map_injective (RingHom.injective (algebraMap K Ω))) ω₀, hω₀]
  have hωq : ω ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hω]; exact hs)
  obtain ⟨hω3, hω1⟩ := ggL45E67_pow_sub_one hω hs1
  exact ⟨ω, hω, hωq, hω3, hω1⟩

private theorem ggL45E67_pair_exists_twE6
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {x : ModGL Tag.E6 Ω} (hx : E6ThreeModel.IsLang Fr x)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    {D : E6ThreeModel.FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : E6ThreeModel.TSpec hn hK σ hσ Fr hFr x hζ D)
    {R : Type} [Group R] (ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (s : ℕ) (hs1 : 1 ≤ s) (hs : 3 ^ s ∣ 2 ^ n + 1) :
    ∃ t₁ ∈ (D.map ε.symm).Tor, ∃ t₂ ∈ (D.map ε.symm).Tor,
      t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨ω, hω, hωq, hω3, hω1⟩ := ggL45E67_exists_root_twE6 (Ω := Ω) hK s hs1 hs
  have hωs : ω ^ 3 ^ s = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨t₁, ht₁T, ht₁pow, ht₁eq⟩ :=
    ggL45E67_twE6_elt hK σ hσ hn h3 Fr hFr hx hζ hD ε 0 s ω hωs hωq
  obtain ⟨t₂, ht₂T, ht₂pow, ht₂eq⟩ :=
    ggL45E67_twE6_elt hK σ hσ hn h3 Fr hFr hx hζ hD ε 1 s ω hωs hωq
  refine ⟨t₁, ht₁T, t₂, ht₂T, ht₁pow, ht₂pow, ?_⟩
  intro i j hij
  let Ψ : R →* ModGL Tag.E6 Ω :=
    (MulAut.conj x⁻¹).toMonoidHom.comp
      ((baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom))
  have hΨapp : ∀ y : R, Ψ y = x⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
      (ε y : ModGL TwistTag.E6.tag K) * x := by
    intro y
    change (MulAut.conj x⁻¹) (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
      (ε y : ModGL TwistTag.E6.tag K)) = x⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (ε y : ModGL TwistTag.E6.tag K) * x
    rw [MulAut.conj_apply, inv_inv]
  have h₁ : Ψ t₁ = torusElt Tag.E6 Ω 0 ω := by
    rw [hΨapp, ht₁eq]
    group
  have h₂ : Ψ t₂ = torusElt Tag.E6 Ω 1 ω := by
    rw [hΨapp, ht₂eq]
    group
  exact ggL45E67_indep_of_hom h₁ h₂ hω3 hω1 i j hij

theorem ggL45E67_frame_exists_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) {L : Type} [Field L] [Algebra K L] {R : Type} [Group R]
    (ε : R ≃* ↥(adjointGroup Tag.E6 K)) {H : Subgroup (ModGL Tag.E6 L)} (Θ : H →* MulAut R)
    (hρΘ : ∀ g r, baseChangeGL (algebraMap K L) (ε (Θ g r) : ModGL Tag.E6 K) =
      g * baseChangeGL (algebraMap K L) (ε r : ModGL Tag.E6 K) * (g : ModGL Tag.E6 L)⁻¹)
    (x : H) :
    ∃ D : E6ThreeModel.FrameData R, D.Good ∧
      (∀ r, r ∈ D.Tor ↔ (x : ModGL Tag.E6 L)⁻¹ *
        baseChangeGL (algebraMap K L) (ε r : ModGL Tag.E6 K) * x ∈ torusGroup Tag.E6 L) ∧
      ∀ s : ℕ, 1 ≤ s → 3 ^ s ∣ 2 ^ n - 1 → ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor,
        t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
        ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
  classical
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (d := 3) (by rw [hK]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hgood : (E6ThreeModel.eFrame K ζ hζ).Good := E6ThreeModel.eFrame_good hζo hζ
  have hmemTor : ∀ u : ↥(adjointGroup Tag.E6 K),
      Θ x (ε.symm u) ∈ (((E6ThreeModel.eFrame K ζ hζ).map ε.symm).map (Θ x)).Tor ↔
        (u : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K := by
    intro u
    rw [E6ThreeModel.FrameData.mem_map_tor, E6ThreeModel.FrameData.mem_map_tor,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply,
      show (E6ThreeModel.eFrame K ζ hζ).Tor =
        (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K) from rfl,
      Subgroup.mem_subgroupOf]
  refine ⟨((E6ThreeModel.eFrame K ζ hζ).map ε.symm).map (Θ x),
    (hgood.map ε.symm).map (Θ x), ?_, ?_⟩
  · intro r
    have hkey : (x : ModGL Tag.E6 L)⁻¹ *
        baseChangeGL (algebraMap K L) (ε r : ModGL Tag.E6 K) * (x : ModGL Tag.E6 L) =
        baseChangeGL (algebraMap K L) (ε ((Θ x).symm r) : ModGL Tag.E6 K) := by
      have h := hρΘ x ((Θ x).symm r)
      rw [MulEquiv.apply_symm_apply] at h
      rw [h]
      group
    rw [E6ThreeModel.FrameData.mem_map_tor, E6ThreeModel.FrameData.mem_map_tor,
      MulEquiv.symm_symm,
      show (E6ThreeModel.eFrame K ζ hζ).Tor =
        (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K) from rfl,
      Subgroup.mem_subgroupOf, hkey]
    exact ⟨fun h => baseChangeGL_mem_torusGroup (algebraMap K L) h,
      fun h => mem_torusGroup_of_baseChangeGL_mem (algebraMap K L) (ε _).2 h⟩
  · intro s hs1 hs3
    exact ggL45E67_pair_exists_E6 _ ε (Θ x)
      (fun u hu => (hmemTor u).mpr hu) s hs1 (by rw [hK]; exact hs3)

theorem ggL45E67_frame_exists_twE6
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {R : Type} [Group R]
    (ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) {x : ModGL Tag.E6 Ω}
    (hx : E6ThreeModel.IsLang Fr x) :
    ∃ D : E6ThreeModel.FrameData R, D.Good ∧
      (∀ r, r ∈ D.Tor ↔ x⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (ε r : ModGL TwistTag.E6.tag K) * x ∈ torusGroup Tag.E6 Ω) ∧
      ∀ s : ℕ, 1 ≤ s → 3 ^ s ∣ 2 ^ n + 1 → ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor,
        t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
        ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at h3
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  obtain ⟨D, hD⟩ := E6ThreeModel.exists_tFrame hn hK σ hσ Fr hFr h3 hx hζ hζo
  have hgood : D.Good := ggL45E67_tFrame_good hn hK σ hσ Fr hFr h3 hx hζ hζo hD
  refine ⟨D.map ε.symm, hgood.map ε.symm, ?_, ?_⟩
  · intro r
    rw [E6ThreeModel.FrameData.mem_map_tor, hD.tor_eq]
    exact ggL45E67_mem_map_conj _ x _
  · intro s hs1 hs3
    exact ggL45E67_pair_exists_twE6 hK σ hσ hn h3 Fr hFr hx hζ hD ε s hs1 hs3

end CFSG.StandardType
