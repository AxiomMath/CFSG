module

public import CFSG.Quasithin.Background.D36GluedL24
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.Quasithin

open Matrix CFSG.Open

section LinAlg

variable {K : Type} [Field K]

noncomputable def kerN24 (N : Matrix (Fin 2) (Fin 2) K) : Submodule K (Fin 2 → K) :=
  LinearMap.ker (Matrix.toLin' N)

theorem mem_kerN24 {N : Matrix (Fin 2) (Fin 2) K} {y : Fin 2 → K} :
    y ∈ kerN24 N ↔ N *ᵥ y = 0 := by
  simp [kerN24, LinearMap.mem_ker]

theorem exists_mulVec_ne_zero24 {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0) :
    ∃ w, N *ᵥ w ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem finrank_kerN24_eq_and_range {N : Matrix (Fin 2) (Fin 2) K} (hN2 : N * N = 0)
    (hN : N ≠ 0) :
    Module.finrank K (kerN24 N) = 1 ∧ LinearMap.range (Matrix.toLin' N) = kerN24 N := by
  have hle : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => Matrix.toLin' M x) hN2
    simpa [Matrix.toLin'_mul] using h
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
  have hdim : Module.finrank K (Fin 2 → K) = 2 := by simp
  rw [hdim] at hsum
  obtain ⟨w, hw⟩ := exists_mulVec_ne_zero24 hN
  have hkerne : LinearMap.ker (Matrix.toLin' N) ≠ ⊤ := fun h => hw (by
    have : w ∈ LinearMap.ker (Matrix.toLin' N) := by rw [h]; trivial
    simpa [LinearMap.mem_ker] using this)
  have h1 : Module.finrank K (LinearMap.ker (Matrix.toLin' N)) < 2 := by
    have := Submodule.finrank_lt hkerne
    simpa [hdim] using this
  have h2 : 1 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' N)) := by
    have hpos : LinearMap.range (Matrix.toLin' N) ≠ ⊥ := by
      intro hb
      apply hw
      have : Matrix.toLin' N w ∈ LinearMap.range (Matrix.toLin' N) := ⟨w, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      simpa using this
    exact Submodule.one_le_finrank_iff.mpr hpos
  have h3 : Module.finrank K (LinearMap.range (Matrix.toLin' N)) ≤
      Module.finrank K (LinearMap.ker (Matrix.toLin' N)) := Submodule.finrank_mono hle
  have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' N)) = 1 := by omega
  have heq : LinearMap.range (Matrix.toLin' N) = LinearMap.ker (Matrix.toLin' N) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact ⟨hk, heq⟩

theorem card_kerN24 {N : Matrix (Fin 2) (Fin 2) K} [Finite K] (hN2 : N * N = 0) (hN : N ≠ 0) :
    Nat.card (kerN24 N) = Nat.card K := by
  have h := (finrank_kerN24_eq_and_range hN2 hN).1
  have := Module.natCard_eq_pow_finrank (K := K) (V := kerN24 N)
  rw [h, pow_one] at this
  exact this

theorem exists_eq_of_mem_kerN24 {N : Matrix (Fin 2) (Fin 2) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    {y : Fin 2 → K} (hy : N *ᵥ y = 0) : ∃ x, N *ᵥ x = y := by
  have h := (finrank_kerN24_eq_and_range hN2 hN).2
  have : y ∈ LinearMap.range (Matrix.toLin' N) := by
    rw [h]; exact mem_kerN24.mpr hy
  obtain ⟨x, hx⟩ := this
  exact ⟨x, by simpa using hx⟩

theorem exists_smul_of_mem_kerN24 {N : Matrix (Fin 2) (Fin 2) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    {v y : Fin 2 → K} (hv : N *ᵥ v = 0) (hv0 : v ≠ 0) (hy : N *ᵥ y = 0) :
    ∃ c : K, c • v = y := by
  have h := (finrank_kerN24_eq_and_range hN2 hN).1
  have hv' : (⟨v, mem_kerN24.mpr hv⟩ : kerN24 N) ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv').mp h ⟨y, mem_kerN24.mpr hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem mulVec_eq_zero_of_comm24 {N N' : Matrix (Fin 2) (Fin 2) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (hN'2 : N' * N' = 0) (hcomm : N * N' = N' * N) {v : Fin 2 → K} (hv : N *ᵥ v = 0) :
    N' *ᵥ v = 0 := by
  by_cases hv0 : v = 0
  · rw [hv0]; simp
  by_contra hne
  have h1 : N *ᵥ (N' *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  obtain ⟨c, hc⟩ := exists_smul_of_mem_kerN24 hN2 hN hv hv0 h1
  have h2 : N' *ᵥ (N' *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hN'2, Matrix.zero_mulVec]
  rw [← hc, Matrix.mulVec_smul] at h2
  have h3 : c = 0 := (smul_eq_zero.mp h2).resolve_right hne
  exact hne (by rw [← hc, h3, zero_smul])

theorem eq_of_agree24 {N₁ N₂ N₃ : Matrix (Fin 2) (Fin 2) K} (h1 : N₁ * N₁ = 0) (h1' : N₁ ≠ 0)
    {w : Fin 2 → K} (hw : N₁ *ᵥ w ≠ 0)
    (h2 : N₂ *ᵥ (N₁ *ᵥ w) = 0) (h3 : N₃ *ᵥ (N₁ *ᵥ w) = 0) (h23 : N₂ *ᵥ w = N₃ *ᵥ w) :
    N₂ = N₃ := by
  have hv : N₁ *ᵥ (N₁ *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
  have key : ∀ y, N₂ *ᵥ y = N₃ *ᵥ y := by
    intro y
    have hy : N₁ *ᵥ (N₁ *ᵥ y) = 0 := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
    obtain ⟨c, hc⟩ := exists_smul_of_mem_kerN24 h1 h1' hv hw hy
    have hy' : N₁ *ᵥ (y - c • w) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hc, sub_self]
    obtain ⟨c', hc'⟩ := exists_smul_of_mem_kerN24 h1 h1' hv hw hy'
    have hy2 : y = c • w + c' • (N₁ *ᵥ w) := by
      rw [hc', add_sub_cancel]
    rw [hy2, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, h2, h3, h23]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end LinAlg

section Coords

variable {V : Type} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem natural_section_coords {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ φ : ↥U →* Multiplicative (ι → K), Function.Surjective φ ∧
      (∀ u : ↥U, φ u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        φ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
            Multiplicative.toAdd (φ u)) := by
  obtain ⟨hs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let N := ((FFModel.nat Γ).ker).subgroupOf ((FFModel.nat Γ).sec)
  let e : (↥(FFModel.nat Γ).sec ⧸ N) →* Multiplicative (ι → K) :=
    QuotientGroup.lift N (Subgroup.subtype _) (by
      intro x hx
      have := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_bot.mp this)
  have he : ∀ m : ↥(FFModel.nat Γ).sec,
      e (QuotientGroup.mk m) = ((m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)) :=
    fun m => rfl
  have heinj : ∀ q q' : (↥(FFModel.nat Γ).sec ⧸ N), e q = e q' → q = q' := by
    intro q q' hqq'
    induction q using QuotientGroup.induction_on with | H m => ?_
    induction q' using QuotientGroup.induction_on with | H m' => ?_
    rw [he, he] at hqq'
    have : m = m' := Subtype.ext hqq'
    rw [this]
  refine ⟨e.comp β, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨a, trivial⟩)
    exact ⟨u, by simp [MonoidHom.comp_apply, hu, he]⟩
  · intro u
    constructor
    · intro hu
      have : β u = 1 := heinj _ _ (by simpa using hu)
      exact (hβk u).mp this
    · intro hu
      have := (hβk u).mpr hu
      simp [MonoidHom.comp_apply, this]
  · intro γ u hu
    have hm : (FFModel.nat Γ).act γ ((e (β u) : Multiplicative (ι → K))) ∈ (FFModel.nat Γ).sec :=
      trivial
    have hβu : β u = QuotientGroup.mk ⟨e (β u), trivial⟩ := by
      apply heinj
      rw [he]
    have h' := hβe γ u ⟨e (β u), trivial⟩ hu hm hβu
    exact (congrArg e h').trans (he _)

end Coords

theorem charTwo_of_card_four (K : Type) [Field K] [Finite K] (h : Nat.card K = 4) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have h4 : p ^ (n : ℕ) = 4 := by
    rw [← hn]
    simpa [Nat.card_eq_fintype_card] using h
  have hdvd : p ∣ 2 ^ 2 := by
    have : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
    rw [h4] at this
    simpa using this
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
  rw [hp2] at hp
  exact hp

section Data

variable {V : Type} [CommGroup V]

structure Nat24 (H : Subgroup (MulAut V)) (U Z : Subgroup V) (K : Type) [Field K] where
  M : ↥H → Matrix (Fin 2) (Fin 2) K
  φ : ↥U →* Multiplicative (Fin 2 → K)
  M_mul : ∀ a b, M (a * b) = M a * M b
  M_one : M 1 = 1
  M_inj : ∀ a b, M a = M b → a = b
  φ_surj : Function.Surjective φ
  φ_ker : ∀ u : ↥U, φ u = 1 ↔ (u : V) ∈ Z
  φ_act : ∀ (a : ↥H) (u : ↥U) (hu : (a : MulAut V) (u : V) ∈ U),
    φ ⟨(a : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (M a *ᵥ Multiplicative.toAdd (φ u))
  H_U : ∀ a : ↥H, ∀ u ∈ U, (a : MulAut V) u ∈ U

variable {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem natural24_data (h : BinaryNaturalSL H U Z 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧ Z ≤ U ∧
      Nonempty (Nat24 H U Z K) := by
  obtain ⟨K, hK, hKfin, hcard, π₀, hπ₀⟩ := h
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥H,
      (FFModel.nat (StatedSL 2 K)).RealizesVia H U Z π := ⟨π₀, hπ₀⟩
  have hcard4 : Nat.card K = 4 := by rw [hcard]; norm_num
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hπ
  have hπsurj : Function.Surjective π := hπ.1
  have hHU : ∀ a : ↥H, ∀ u ∈ U, (a : MulAut V) u ∈ U := hπ.2.2.2.1
  obtain ⟨φ, hφs, hφk, hφe⟩ := natural_section_coords hπ
  refine ⟨K, hK, hKfin, charTwo_of_card_four K hcard4, hcard4, hπ.2.1, ⟨?_⟩⟩
  refine ⟨fun a => (((Function.surjInv hπsurj a : ↥(StatedSL 2 K)) :
      Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), φ, ?_, ?_, ?_, hφs, hφk,
    ?_, hHU⟩
  · intro a b
    have h1 : Function.surjInv hπsurj (a * b) =
        Function.surjInv hπsurj a * Function.surjInv hπsurj b := by
      apply hπinj
      rw [map_mul, Function.surjInv_eq hπsurj, Function.surjInv_eq hπsurj,
        Function.surjInv_eq hπsurj]
    simp only [h1]
    rfl
  · have h1 : Function.surjInv hπsurj (1 : ↥H) = 1 := by
      apply hπinj
      rw [map_one, Function.surjInv_eq hπsurj]
    simp only [h1]
    rfl
  · intro a b hab
    have : Function.surjInv hπsurj a = Function.surjInv hπsurj b := by
      apply Subtype.ext
      apply Units.ext
      exact hab
    have h2 := congrArg π this
    rwa [Function.surjInv_eq hπsurj, Function.surjInv_eq hπsurj] at h2
  · intro a u hu
    have hπa : π (Function.surjInv hπsurj a) = a := Function.surjInv_eq hπsurj a
    have hu' : ((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V) ∈ U := by
      rw [hπa]; exact hu
    have h1 := hφe (Function.surjInv hπsurj a) u hu'
    have h2 : (⟨((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) =
        ⟨(a : MulAut V) (u : V), hu⟩ :=
      Subtype.ext (show ((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V) =
        (a : MulAut V) (u : V) by rw [hπa])
    rw [h2] at h1
    exact h1

end Data

section Counting

variable {K : Type} [Field K] [Finite K]

theorem card_coord24 (hcard : Nat.card K = 4) :
    Nat.card (Multiplicative (Fin 2 → K)) = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hcard]
  simp

theorem card_eq_ker_mul24 {U : Type} [Group U] [Finite U] (hcard : Nat.card K = 4)
    (φ : U →* Multiplicative (Fin 2 → K)) (hφ : Function.Surjective φ) :
    Nat.card φ.ker * 16 = Nat.card U := by
  have h := Subgroup.card_ker_mul_card_range φ
  rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, card_coord24 hcard] at h
  exact h

theorem card_subgroup_mul_four_le {U : Type} [Group U] [Finite U] (hcard : Nat.card K = 4)
    {N : Matrix (Fin 2) (Fin 2) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (φ : U →* Multiplicative (Fin 2 → K)) (hφ : Function.Surjective φ) (S : Subgroup U)
    (hS : ∀ s ∈ S, N *ᵥ Multiplicative.toAdd (φ s) = 0) :
    Nat.card S * 4 ≤ Nat.card U := by
  classical
  let ψ : ↥S →* Multiplicative (Fin 2 → K) := φ.comp S.subtype
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := card_eq_ker_mul24 hcard φ hφ
  have h3 : Nat.card ψ.ker ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x.1 : ↥S) : U), x.2⟩) ?_
    intro x y hxy
    have := congrArg (fun z : ↥φ.ker => (z : U)) hxy
    exact Subtype.ext (Subtype.ext this)
  have h4 : Nat.card ψ.range ≤ 4 := by
    have hk := card_kerN24 hN2 hN
    rw [hcard] at hk
    rw [← hk]
    refine Nat.card_le_card_of_injective
      (fun a => (⟨Multiplicative.toAdd (a : Multiplicative (Fin 2 → K)), ?_⟩ : kerN24 N)) ?_
    · obtain ⟨s, hs⟩ := a.2
      rw [mem_kerN24, ← hs]
      exact hS s s.2
    · intro a b hab
      have := congrArg (fun z : kerN24 N => (z : Fin 2 → K)) hab
      exact Subtype.ext (Multiplicative.toAdd.injective this)
  calc Nat.card S * 4 = Nat.card ψ.ker * Nat.card ψ.range * 4 := by rw [h1]
    _ ≤ Nat.card φ.ker * 4 * 4 := by
        have := Nat.mul_le_mul h3 h4
        exact Nat.mul_le_mul_right 4 this
    _ = Nat.card U := by rw [← h2]; ring

end Counting

namespace Nat24

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {K : Type}
  [Field K] (D : Nat24 H U Z K)

noncomputable def N (a : ↥H) : Matrix (Fin 2) (Fin 2) K := D.M a - 1

theorem N_sq [CharP K 2] {a : ↥H} (ha : a * a = 1) : D.N a * D.N a = 0 := by
  have hMM : D.M a * D.M a = 1 := by rw [← D.M_mul, ha, D.M_one]
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  unfold N
  calc (D.M a - 1) * (D.M a - 1) = D.M a * D.M a - D.M a - D.M a + 1 := by noncomm_ring
    _ = 1 - D.M a - D.M a + 1 := by rw [hMM]
    _ = (2 : K) • (1 - D.M a) := by rw [two_smul]; abel
    _ = 0 := by rw [h2, zero_smul]

theorem N_comm {a b : ↥H} (hab : a * b = b * a) : D.N a * D.N b = D.N b * D.N a := by
  have h1 : D.M a * D.M b = D.M b * D.M a := by rw [← D.M_mul, ← D.M_mul, hab]
  unfold N
  calc (D.M a - 1) * (D.M b - 1) = D.M a * D.M b - D.M a - D.M b + 1 := by noncomm_ring
    _ = D.M b * D.M a - D.M a - D.M b + 1 := by rw [h1]
    _ = (D.M b - 1) * (D.M a - 1) := by noncomm_ring

theorem N_ne {a : ↥H} (ha : a ≠ 1) : D.N a ≠ 0 := by
  intro h0
  apply ha
  apply D.M_inj
  rw [D.M_one]
  exact sub_eq_zero.mp h0

theorem key (a : ↥H) (u : ↥U) :
    (a : MulAut V) (u : V) * (u : V)⁻¹ ∈ Z ↔
      D.N a *ᵥ Multiplicative.toAdd (D.φ u) = 0 := by
  have hau : (a : MulAut V) (u : V) ∈ U := D.H_U a u u.2
  have h2 := D.φ_ker ⟨(a : MulAut V) (u : V) * (u : V)⁻¹, U.mul_mem hau (U.inv_mem u.2)⟩
  have h1 : (⟨(a : MulAut V) (u : V) * (u : V)⁻¹, U.mul_mem hau (U.inv_mem u.2)⟩ : ↥U) =
      ⟨(a : MulAut V) (u : V), hau⟩ * u⁻¹ := rfl
  rw [← h2, h1, map_mul, map_inv, D.φ_act a u hau, mul_inv_eq_one]
  unfold N
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective h
  · intro h
    rw [h]
    rfl

end Nat24

namespace Nat24

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {K : Type}
  [Field K] [Finite K] [CharP K 2] (D : Nat24 H U Z K)

include D

theorem rk_eq [Finite V] (hcard : Nat.card K = 4) (hZU : Z ≤ U) : rk ↥U = rk ↥Z + 4 := by
  have hker : D.φ.ker = Z.subgroupOf U := by
    ext u
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, D.φ_ker]
  have h := card_eq_ker_mul24 hcard D.φ D.φ_surj
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h
  unfold rk
  rw [← h, padicValNat.mul Nat.card_pos.ne' (by norm_num)]
  have : padicValNat 2 16 = 4 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  rw [this]

theorem card_elem_le (hcard : Nat.card K = 4) {R : Subgroup (MulAut V)} (hRH : R ≤ H)
    (hR : IsElemAbelian2 R) : Nat.card ↥R ≤ 4 := by
  by_cases hR1 : R = ⊥
  · subst hR1
    simp
  obtain ⟨r₁, hr₁R, hr₁1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    exact hR1 (eq_bot_iff.mpr fun g hg => h g hg)
  set ι := Subgroup.inclusion hRH with hι
  have hsq : ∀ ρ : ↥R, ι ρ * ι ρ = 1 := fun ρ => by
    apply Subtype.ext
    have := hR.2 (ρ : MulAut V) ρ.2
    simpa [pow_two, hι] using this
  have hcm : ∀ ρ σ : ↥R, ι ρ * ι σ = ι σ * ι ρ := fun ρ σ => by
    apply Subtype.ext
    exact hR.1 (ρ : MulAut V) ρ.2 σ σ.2
  let ρ₁ : ↥R := ⟨r₁, hr₁R⟩
  have hρ₁ne : ι ρ₁ ≠ 1 := fun h => hr₁1 (congrArg Subtype.val h)
  have hN₁sq := D.N_sq (hsq ρ₁)
  have hN₁ne := D.N_ne hρ₁ne
  obtain ⟨w, hw⟩ := exists_mulVec_ne_zero24 hN₁ne
  have hv : D.N (ι ρ₁) *ᵥ (D.N (ι ρ₁) *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hN₁sq, Matrix.zero_mulVec]
  have hkill : ∀ ρ : ↥R, D.N (ι ρ) *ᵥ (D.N (ι ρ₁) *ᵥ w) = 0 := fun ρ =>
    mulVec_eq_zero_of_comm24 hN₁sq hN₁ne (D.N_sq (hsq ρ)) (D.N_comm (hcm ρ₁ ρ)) hv
  have hmem : ∀ ρ : ↥R, D.N (ι ρ₁) *ᵥ (D.N (ι ρ) *ᵥ w) = 0 := fun ρ => by
    rw [Matrix.mulVec_mulVec, D.N_comm (hcm ρ₁ ρ), ← Matrix.mulVec_mulVec]
    exact hkill ρ
  have hinj : Function.Injective
      (fun ρ : ↥R => (⟨D.N (ι ρ) *ᵥ w, mem_kerN24.mpr (hmem ρ)⟩ : kerN24 (D.N (ι ρ₁)))) := by
    intro ρ σ h
    have h23 : D.N (ι ρ) *ᵥ w = D.N (ι σ) *ᵥ w := congrArg Subtype.val h
    have hN := eq_of_agree24 hN₁sq hN₁ne hw (hkill ρ) (hkill σ) h23
    have hM : D.M (ι ρ) = D.M (ι σ) := by
      unfold Nat24.N at hN
      exact sub_left_injective hN
    have h' := congrArg Subtype.val (D.M_inj _ _ hM)
    exact Subtype.ext h'
  have := Nat.card_le_card_of_injective _ hinj
  rw [card_kerN24 hN₁sq hN₁ne, hcard] at this
  exact this

theorem rk_commModSub_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card K = 4)
    {R : Subgroup (MulAut V)} (hRH : R ≤ H) (hR : IsElemAbelian2 R) (hR1 : R ≠ ⊥) :
    rk ↥(commModSub U R Z) + 2 ≤ rk ↥U := by
  obtain ⟨r₁, hr₁R, hr₁1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    exact hR1 (eq_bot_iff.mpr fun g hg => h g hg)
  let a₁ : ↥H := ⟨r₁, hRH hr₁R⟩
  have ha₁ : a₁ ≠ 1 := fun h => hr₁1 (congrArg Subtype.val h)
  have hasq : a₁ * a₁ = 1 := Subtype.ext (by simpa [pow_two] using hR.2 r₁ hr₁R)
  have hNsq := D.N_sq hasq
  have hNne := D.N_ne ha₁
  let S : Subgroup ↥U := (commModSub U R Z).subgroupOf U
  have hS : ∀ s ∈ S, D.N a₁ *ᵥ Multiplicative.toAdd (D.φ s) = 0 := fun s hs =>
    (D.key a₁ s).mp (hs.2 r₁ hr₁R)
  have hcardS := card_subgroup_mul_four_le hcard hNsq hNne D.φ D.φ_surj S hS
  have hSeq : Nat.card S = Nat.card ↥(commModSub U R Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commModSub_le U R Z)).toEquiv
  rw [hSeq, card_eq_two_pow hV (commModSub U R Z), card_eq_two_pow hV U] at hcardS
  have : 2 ^ (rk ↥(commModSub U R Z) + 2) ≤ 2 ^ rk ↥U := by
    rw [pow_add]
    simpa using hcardS
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

theorem commutator_lift {R : Subgroup (MulAut V)} (hRH : R ≤ H) (hR : IsElemAbelian2 R)
    {x : V} (hx : x ∈ commModSub U R Z) {r : MulAut V} (hr : r ∈ R) (hr1 : r ≠ 1) :
    ∃ z ∈ U, (r z * z⁻¹) * x⁻¹ ∈ Z := by
  obtain ⟨hxU, hxR⟩ := hx
  let a : ↥H := ⟨r, hRH hr⟩
  have ha1 : a ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
  have hasq : a * a = 1 := Subtype.ext (by simpa [pow_two] using hR.2 r hr)
  have hNsq := D.N_sq hasq
  have hNne := D.N_ne ha1
  let x' : ↥U := ⟨x, hxU⟩
  have hNx : D.N a *ᵥ Multiplicative.toAdd (D.φ x') = 0 := (D.key a x').mp (hxR r hr)
  obtain ⟨y, hy⟩ := exists_eq_of_mem_kerN24 hNsq hNne hNx
  obtain ⟨z', hz'⟩ := D.φ_surj (Multiplicative.ofAdd y)
  refine ⟨(z' : V), z'.2, ?_⟩
  have hraz : (r : MulAut V) (z' : V) ∈ U := D.H_U a z' z'.2
  have hmem : (r : MulAut V) (z' : V) * (z' : V)⁻¹ * x⁻¹ ∈ U :=
    U.mul_mem (U.mul_mem hraz (U.inv_mem z'.2)) (U.inv_mem hxU)
  rw [← D.φ_ker ⟨_, hmem⟩]
  have hc : (⟨(r : MulAut V) (z' : V) * (z' : V)⁻¹ * x⁻¹, hmem⟩ : ↥U) =
      ⟨(r : MulAut V) (z' : V), hraz⟩ * z'⁻¹ * x'⁻¹ := rfl
  rw [hc, map_mul, map_mul, map_inv, map_inv, D.φ_act a z' hraz, hz']
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one]
  have : D.N a *ᵥ y = (D.M a *ᵥ y) - y := by
    unfold Nat24.N
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [← hy, this]
  abel

end Nat24

theorem l24NaturalSection_holds : L24NaturalSection := by
  intro V _ _ hV H U Z hnat
  obtain ⟨K, hK, hKfin, hchar, hcard, hZU, ⟨D⟩⟩ := natural24_data hnat
  refine ⟨D.rk_eq hcard hZU, ?_, ?_⟩
  · intro R hRH hR
    have h4 := D.card_elem_le hcard hRH hR
    rw [card_eq_two_pow_of_isPGroup hR.isPGroup] at h4
    have : 2 ^ rk ↥R ≤ 2 ^ 2 := by simpa using h4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  · intro R hRH hR hR1
    exact ⟨D.rk_commModSub_le hV hcard hRH hR hR1,
      fun x hx r hr hr1 => D.commutator_lift hRH hR hx hr hr1⟩

end CFSG.Quasithin
