module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6RGenA
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6RGenB
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6RGenC
import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def genSubgroup {R : Type} [Group R] (D : FrameData R) (J : Subgroup R) : Subgroup R :=
  Subgroup.closure (⋃ n ∈ (Subgroup.closure (Set.range D.nb) : Set R),
    (fun s => n * s * n⁻¹) '' {s : R | s ∈ J ∧ s ∈ D.Tor ∧ ∃ k : ℕ, s ^ 3 ^ k = 1})

private lemma corootTuple_pow {L : Type} [Field L] (δ : Fin Tag.E6.rank → ℤ) (s : Lˣ) (r : ℕ) :
    CFSG.SeitzReduction.E6Pilot.corootTuple δ (s ^ r) =
      (CFSG.SeitzReduction.E6Pilot.corootTuple δ s) ^ r := by
  induction r with
  | zero => simp [CFSG.SeitzReduction.E6Pilot.corootTuple_one]
  | succ r ih =>
      rw [pow_succ, CFSG.SeitzReduction.E6Pilot.corootTuple_mul, ih, pow_succ]

private lemma rootDiagUnit_pow {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (r : ℕ) :
    (rootDiagUnit Tag.E6 a) ^ r = rootDiagUnit Tag.E6 (a ^ r) := by
  induction r with
  | zero => simp [rootDiagUnit_one]
  | succ r ih => rw [pow_succ, ih, pow_succ, rootDiagUnit_mul]

lemma coroot_pow_eq_one {L : Type} [Field L] (α : Fin Tag.E6.rank → ℤ) (s : Lˣ)
    (a : ℕ) (hs : s ^ 3 ^ a = 1) : (TwE6Coroot.coroot α s) ^ 3 ^ a = 1 := by
  unfold TwE6Coroot.coroot
  rw [rootDiagUnit_pow, ← corootTuple_pow, hs, CFSG.SeitzReduction.E6Pilot.corootTuple_one,
    rootDiagUnit_one]

lemma torusElt_eq_coroot_single
    {L : Type} [Field L] (j : Fin Tag.E6.rank) (s : Lˣ) :
    torusElt Tag.E6 L j s = TwE6Coroot.coroot (Pi.single j 1) s := by
  rw [torusElt_eq_rootDiagUnit]
  unfold TwE6Coroot.coroot
  congr 1
  funext k
  rw [CFSG.SeitzReduction.E6Pilot.corootTuple, CFSG.SeitzReduction.E6Pilot.iform_single_single_E6]

private theorem exists_list_nb_conj
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D)
    (ω : List (Fin Tag.E6.rank)) {δ : Fin Tag.E6.rank → ℤ} {s : Ωˣ}
    {u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hu : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (u : ModGL TwistTag.E6.tag K) =
      g * TwE6Coroot.coroot δ s * g⁻¹) :
    ∃ m ∈ (Subgroup.closure (Set.range D.nb) : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
          ((m * u * m⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
        g * TwE6Coroot.coroot (((coxeterSystem Tag.E6).wordProd ω) • δ) s * g⁻¹ := by
  induction ω generalizing δ u with
  | nil =>
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      have h1 : (1 : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) * u *
          1⁻¹ = u := by group
      rw [h1]
      have hw : (coxeterSystem Tag.E6).wordProd ([] : List (Fin Tag.E6.rank)) = 1 :=
        CoxeterSystem.wordProd_nil (coxeterSystem Tag.E6)
      rw [hw, one_smul]
      exact hu
  | cons i ω ih =>
      obtain ⟨m, hm, hmu⟩ := ih hu
      have hq := tspec_conj_coroot (n := n) hn hK σ hσ Fr hFr h3 hL hζ hζo hD i
        (((coxeterSystem Tag.E6).wordProd ω) • δ) s (u := m * u * m⁻¹) hmu
      refine ⟨D.nb i * m, (Subgroup.closure (Set.range D.nb)).mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hm, ?_⟩
      have hgroup : (D.nb i * m) * u * (D.nb i * m)⁻¹ =
          D.nb i * (m * u * m⁻¹) * (D.nb i)⁻¹ := by group
      rw [hgroup, hq, (coxeterSystem Tag.E6).wordProd_cons, mul_smul]

private theorem gen_contains_generator
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D)
    (G : CartanGen D (rootsOfUnity (2 ^ n + 1) Ω))
    (hG : ∀ (j : Fin 6) (s : rootsOfUnity (2 ^ n + 1) Ω),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
          ((G.d j s : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
        g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hJ : IsComponentOf J (ggFix (D.ad x)))
    (j : Fin 6) (t : rootsOfUnity (2 ^ n + 1) Ω)
    (ht3 : ∃ a : ℕ, ((t : Ωˣ)) ^ 3 ^ a = 1) :
    (G.d j t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∈ genSubgroup D J := by
  obtain ⟨α, hα, hu⟩ :=
    tspec_exists_coroot_in_component (n := n) hn hK σ hσ Fr hFr h3 hL hζ hζo hD hx hJ
  obtain ⟨u, huJ, huTor, hubc⟩ := hu (t : Ωˣ) t.2
  obtain ⟨w, hw⟩ :=
    CFSG.StandardType.GGFinModel.G5.ggG5_orbit_simplyLaced (τ := Tag.E6) (Or.inl rfl) hα
      (IsRoot.basis (τ := Tag.E6) j)
  obtain ⟨ω, _hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  obtain ⟨m, hm, hbc⟩ := exists_list_nb_conj hn hK σ hσ Fr hFr h3 hL hζ hζo hD ω hubc
  have hbc' : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        ((m * u * m⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      g * TwE6Coroot.coroot (Pi.single j 1) (t : Ωˣ) * g⁻¹ := by
    rw [hbc, hw]
  have hGbc : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (((G.d j t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) : ModGL TwistTag.E6.tag K) =
      g * TwE6Coroot.coroot (Pi.single j 1) (t : Ωˣ) * g⁻¹ := by
    rw [hG j t, torusElt_eq_coroot_single (L := Ω) j (t : Ωˣ)]
  have heqMod : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        ((m * u * m⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (((G.d j t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) : ModGL TwistTag.E6.tag K) :=
    hbc'.trans hGbc.symm
  have heq : (m * u * m⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
      (G.d j t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    Subtype.coe_injective (baseChangeGL_injective (f := algebraMap K Ω) heqMod)
  rw [← heq]
  obtain ⟨a, ha⟩ := ht3
  have hcor : (TwE6Coroot.coroot α (t : Ωˣ)) ^ 3 ^ a = 1 :=
    coroot_pow_eq_one α (t : Ωˣ) a ha
  let w : ModGL Tag.E6 K := (u : ModGL TwistTag.E6.tag K)
  have hw : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) w =
      g * TwE6Coroot.coroot α (t : Ωˣ) * g⁻¹ := hubc
  have hcoe : ((u ^ 3 ^ a : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) = w ^ 3 ^ a := by
    rw [Subgroup.coe_pow]
    rfl
  have hubc_pow : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (w ^ 3 ^ a) = 1 := by
    rw [map_pow, hw]
    have hp : (g * TwE6Coroot.coroot α (t : Ωˣ) * g⁻¹) ^ (3 ^ a) = 1 := by
      have hconj : g * TwE6Coroot.coroot α (t : Ωˣ) * g⁻¹ =
          MulAut.conj g (TwE6Coroot.coroot α (t : Ωˣ)) := by
        simp [MulAut.conj_apply]
      rw [hconj, ← map_pow, hcor, map_one]
    rw [hp]
  have hpoweq : u ^ 3 ^ a = 1 := by
    apply Subtype.coe_injective
    change ((u ^ 3 ^ a : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) = (1 : ModGL TwistTag.E6.tag K)
    rw [hcoe]
    change w ^ 3 ^ a = (1 : ModGL Tag.E6 K)
    exact baseChangeGL_injective (f := algebraMap K Ω) (by simpa using hubc_pow)
  refine Subgroup.subset_closure ?_
  exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm,
    ⟨u, ⟨huJ, huTor, ⟨a, hpoweq⟩⟩, rfl⟩⟩⟩

private theorem tor_three_mem
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) (hgood : D.Good)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hJ : IsComponentOf J (ggFix (D.ad x)))
    {c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hcT : c ∈ D.Tor)
    (hc3 : ∃ k : ℕ, c ^ 3 ^ k = 1) : c ∈ genSubgroup D J := by
  obtain ⟨G, hG⟩ := tFrame_cartanGen_bc (n := n) hn hK σ hσ Fr hFr h3 hL hζ hζo hD
  let N : ℕ := 2 ^ n + 1
  let a : ℕ := padicValNat 3 N
  let m : ℕ := Nat.divMaxPow N 3
  have hNpos : N ≠ 0 := by
    have h0 : 0 < 2 ^ n := pow_pos (by norm_num) n
    show 2 ^ n + 1 ≠ 0
    omega
  have hmN : m * 3 ^ a = N := Nat.divMaxPow_mul_pow_padicValNat 3 N
  have hm3 : ¬ 3 ∣ m := Nat.not_dvd_divMaxPow (p := 3) (n := N) (by norm_num) hNpos
  have hcT' : c ∈ ⨆ j : Fin 6, (G.d j).range := by
    rw [← G.tor_eq]
    exact hcT
  have hcm : c ^ m ∈ genSubgroup D J := by
    refine (Subgroup.iSup_induction (S := fun j : Fin 6 => (G.d j).range)
      (C := fun r => r ∈ D.Tor ∧ r ^ m ∈ genSubgroup D J) hcT' ?_ ?_ ?_).2
    · rintro j y hy
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hy
      have hTor : G.d j s ∈ D.Tor := by
        rw [G.tor_eq]
        exact Subgroup.mem_iSup_of_mem j ⟨s, rfl⟩
      have hpow3 : ∃ b : ℕ, ((s ^ m : rootsOfUnity (2 ^ n + 1) Ω) : Ωˣ) ^ 3 ^ b = 1 := by
        refine ⟨a, ?_⟩
        have hs : ((s : Ωˣ)) ^ (2 ^ n + 1) = 1 :=
          (mem_rootsOfUnity (2 ^ n + 1) (s : Ωˣ)).1 s.2
        calc ((s ^ m : rootsOfUnity (2 ^ n + 1) Ω) : Ωˣ) ^ 3 ^ a
            = ((s : Ωˣ) ^ m) ^ 3 ^ a := by rw [Subgroup.coe_pow]
          _ = (s : Ωˣ) ^ (m * 3 ^ a) := by rw [pow_mul]
          _ = (s : Ωˣ) ^ (2 ^ n + 1) := by rw [hmN]
          _ = 1 := hs
      have hgen := gen_contains_generator (n := n) hn hK σ hσ Fr hFr h3 hL hζ hζo hD
        G hG hx hJ j (s ^ m) hpow3
      refine ⟨hTor, ?_⟩
      simpa only [map_pow] using hgen
    · refine ⟨D.Tor.one_mem, ?_⟩
      rw [one_pow]
      exact (genSubgroup D J).one_mem
    · rintro y z ⟨hyT, hyH⟩ ⟨hzT, hzH⟩
      refine ⟨D.Tor.mul_mem hyT hzT, ?_⟩
      have hcomm : Commute y z := hgood.torus.1 y hyT z hzT
      rw [hcomm.mul_pow]
      exact (genSubgroup D J).mul_mem hyH hzH
  rcases hc3 with ⟨k, hk⟩
  rcases k with _ | k
  · simp only [pow_zero, pow_one] at hk
    rw [hk]
    exact (genSubgroup D J).one_mem
  · have he : 1 < 3 ^ (k + 1) := by
      have h3gt : 1 < 3 := by norm_num
      exact Nat.one_lt_pow (by omega) h3gt
    have hcop : Nat.Coprime m (3 ^ (k + 1)) :=
      Nat.Prime.coprime_pow_of_not_dvd (p := 3) (by norm_num) hm3
    obtain ⟨r, _hrlt, hr⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime (k := 3 ^ (k + 1)) (n := m) hcop he
    have hmod : 1 ≡ m * r [MOD 3 ^ (k + 1)] := by
      show 1 % 3 ^ (k + 1) = m * r % 3 ^ (k + 1)
      rw [hr, Nat.mod_eq_of_lt he]
    have hmr_pos : 1 ≤ m * r := by
      rcases Nat.eq_zero_or_pos (m * r) with h | h
      · rw [h] at hr
        simp at hr
      · exact h
    have hdvd : 3 ^ (k + 1) ∣ m * r - 1 :=
      (Nat.modEq_iff_dvd' (n := 3 ^ (k + 1)) (a := 1) (b := m * r) hmr_pos).1 hmod
    obtain ⟨t, ht⟩ := hdvd
    have hmr_eq : m * r = 3 ^ (k + 1) * t + 1 := by omega
    have hceq : c = (c ^ m) ^ r := by
      rw [← pow_mul, hmr_eq, pow_add, pow_mul, hk, one_pow, one_mul, pow_one]
    rw [hceq]
    exact (genSubgroup D J).pow_mem hcm r

theorem rGen_of_tspec
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) (hgood : D.Good) : GGE6ThreeRGen D := by
  intro x hx J hJ c hcT hc3
  exact tor_three_mem (n := n) hn hK σ hσ Fr hFr h3 hL hζ hζo hD hgood hx hJ hcT hc3

end CFSG.StandardType.E6ThreeModel
