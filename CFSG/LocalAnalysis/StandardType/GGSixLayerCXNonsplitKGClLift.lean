module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSL

public section

namespace CFSG.StandardType

namespace ClNonsplit

open Matrix LayerCores

section Adj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)

include hadj in
theorem adj_eq_inv {g : GL ι K} (hg : g ∈ unitaryOf hadj) :
    adj (g : Matrix ι ι K) = ((g⁻¹ : GL ι K) : Matrix ι ι K) := by
  calc adj (g : Matrix ι ι K) = adj g * ((g * g⁻¹ : GL ι K) : Matrix ι ι K) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = _ := by rw [Units.val_mul, ← Matrix.mul_assoc, mem_unitaryOf.mp hg, Matrix.one_mul]

theorem adj_mul_comm {g : GL ι K} (hg : g ∈ unitaryOf hadj) {X : Matrix ι ι K}
    (hX : X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) :
    adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X := by
  have hgi : adj ((g⁻¹ : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K) := by
    rw [adj_eq_inv hadj (Subgroup.inv_mem _ hg), inv_inv]
  have hXi : X * ((g⁻¹ : GL ι K) : Matrix ι ι K) = ((g⁻¹ : GL ι K) : Matrix ι ι K) * X :=
    (Commute.units_inv_right (show Commute X (g : Matrix ι ι K) from hX)).eq
  rw [← hgi, ← hadj.map_mul, ← hadj.map_mul, hXi]

theorem adj_stab_zpowers {A : GL ι K} (hA : A ∈ unitaryOf hadj) (X : Matrix ι ι K)
    (hX : ∀ g ∈ Subgroup.zpowers A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) :
    ∀ g ∈ Subgroup.zpowers A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X :=
  fun g hg => adj_mul_comm hadj (Subgroup.zpowers_le.mpr hA hg) (hX g hg)

theorem commute_of_mem_zpowers {A : GL ι K} {X : Matrix ι ι K}
    (hX : X * (A : Matrix ι ι K) = (A : Matrix ι ι K) * X) {g : GL ι K}
    (hg : g ∈ Subgroup.zpowers A) : X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (Commute.units_zpow_right (show Commute X (A : Matrix ι ι K) from hX) k).eq

theorem natCast_card_zpowers_ne_zero [CharP K 2] {g : GL ι K} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hg : g ^ p = 1) : (Nat.card (Subgroup.zpowers g) : K) ≠ 0 := by
  rw [Nat.card_zpowers]
  intro h
  have h2 : 2 ∣ orderOf g := (CharP.cast_eq_zero_iff K 2 _).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (h2.trans (orderOf_dvd_of_pow_eq_one hg))).symm

end Adj

section Unique

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_of_coord_eq_one {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ} [∀ i, Field (D i)]
    [∀ i, Algebra K (D i)] [hd : ∀ i, NeZero (d i)]
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[K] Matrix ι ι K)
    (hΦinj : Function.Injective Φ) {B : Matrix ι ι K}
    (hrange : ∀ X : Matrix ι ι K, X * B = B * X → X ∈ Set.range Φ)
    {w : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)} (hw : Φ w = B) {j₁ j₂ : Fin r}
    (h₁ : w j₁ = 1) (h₂ : w j₂ = 1) : j₁ = j₂ := by
  classical
  by_contra hne
  set e₁ : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single j₁ 1 with he₁
  set e₂ : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single j₂ 1 with he₂
  have hwe₁ : w * e₁ = e₁ := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁, h₁]
    · simp [he₁, hi]
  have he₂w : e₂ * w = e₂ := by
    funext i
    by_cases hi : i = j₂
    · subst hi
      simp [he₂, h₂]
    · simp [he₂, hi]
  have he₂₁ : e₂ * e₁ = 0 := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁, he₂, Ne.symm hne]
    · simp [he₁, hi]
  have he₁₁ : e₁ * e₁ = e₁ := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁]
    · simp [he₁, hi]
  have hcent : ∀ c, e₁ * c = c * e₁ := by
    intro c
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁]
    · simp [he₁, hi]
  have hzero : ∀ M : Matrix ι ι K, Φ e₁ * M * Φ e₂ = 0 := by
    intro M
    have hXB : Φ e₁ * M * Φ e₂ * B = Φ e₁ * M * Φ e₂ := by
      rw [← hw, mul_assoc (Φ e₁ * M), ← map_mul, he₂w]
    have hBX : B * (Φ e₁ * M * Φ e₂) = Φ e₁ * M * Φ e₂ := by
      rw [← hw, ← mul_assoc, ← mul_assoc, ← map_mul, hwe₁]
    obtain ⟨c, hc⟩ := hrange _ (hXB.trans hBX.symm)
    calc Φ e₁ * M * Φ e₂ = Φ e₁ * (Φ e₁ * M * Φ e₂) := by
          rw [← mul_assoc, ← mul_assoc, ← map_mul, he₁₁]
      _ = Φ e₁ * Φ c := by rw [hc]
      _ = Φ c * Φ e₁ := by rw [← map_mul, ← map_mul, hcent]
      _ = Φ e₁ * M * Φ e₂ * Φ e₁ := by rw [hc]
      _ = 0 := by rw [mul_assoc (Φ e₁ * M), ← map_mul, he₂₁, map_zero, mul_zero]
  have hne₀ : ∀ j, (Pi.single j 1 : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≠ 0 := by
    intro j h
    have h1 := congrFun h j
    have := hd j
    simp at h1
  have hne₁ : Φ e₁ ≠ 0 := fun h => hne₀ j₁ (hΦinj (h.trans (map_zero Φ).symm))
  have hne₂ : Φ e₂ ≠ 0 := fun h => hne₀ j₂ (hΦinj (h.trans (map_zero Φ).symm))
  obtain ⟨a, k, hak⟩ : ∃ a k, Φ e₁ a k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₁ (Matrix.ext fun a k => h a k)
  obtain ⟨l, b, hlb⟩ : ∃ l b, Φ e₂ l b ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₂ (Matrix.ext fun l b => h l b)
  have h0 := congrFun (congrFun (hzero (Matrix.single k l 1)) a) b
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h0
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.zero_apply] at h0
    exact mul_ne_zero hak hlb h0
  · intro c _ hc
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ l) h

end Unique

section Factors

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ} [∀ i, NeZero (d i)]
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

theorem apply_perm_eq_one (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {w : (PiMat D d)ˣ} (hw : w ∈ unitaryOf hτ) {b : Fin r} (hb : (w : PiMat D d) b = 1) :
    (w : PiMat D d) (π b) = 1 := by
  have h2 := tau_apply_mul_eq_one hτ hw (π b)
  rw [apply_tau_eq hτ hπ _ (perm_perm hτ hπ b), hb,
    show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
      rfl, tau_piE_apply hτ hπ (perm_perm hτ hπ b), Matrix.one_mul] at h2
  exact h2

theorem isCoreFamily_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (hSn : ∀ b, ∀ u ∈ factorGroup π hτ hπ b, ∀ s ∈ Sf b, u * s * u⁻¹ ∈ Sf b)
    (hder : ∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b)
    (hq : ∀ b, Sf b = ⊥ ∨ (CFSG.IsQuasisimple (Sf b) ∧
      ∀ z ∈ Sf b, (∀ y ∈ Sf b, z * y = y * z) → z ^ 2 = 1 → z = 1)) :
    IsCoreFamily (unitaryOf hτ)
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} => coreOf π hτ Sf c.1) :=
  ⟨fun c => coreOf_le hτ Sf c.1, fun _ _ hu _ hs => conj_mem_coreOf hτ hπ hSn hu hs,
    fun c => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm
      ((hq c.1).resolve_left c.2.2).1,
    exists_ggDer_le_iSup_coreOf hτ hπ hSle hder,
    fun _ hz hzc hz2 => eq_one_of_mem_iSup_coreOf hτ hπ hSle
      (fun b hb => ((hq b).resolve_left hb).2) hz hzc hz2⟩

theorem coord_eq_one_of_not_dvd [∀ i, Finite (D i)] [∀ i, CharP (D i) 2] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (hy : ∃ y, y + τ y = 1)
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (hder : ∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b) {b : Fin r}
    (hq : CFSG.IsQuasisimple (Sf b)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpS : ¬ p ∣ Nat.card (Sf b)) {w : (PiMat D d)ˣ} (hw : w ∈ unitaryOf hτ) (hwp : w ^ p = 1) :
    (w : PiMat D d) b = 1 := by
  have hg := coordHom_mem_factorGroup hτ hπ b hw
  have hgp : coordHom D d b w ^ p = 1 := by rw [← map_pow, hwp, map_one]
  have hSb := hSle b
  have hderb := hder b
  suffices h : coordHom D d b w = 1 by
    have h1 := congrArg (fun g : GL (Fin (d b)) (D b) => (g : Matrix (Fin (d b)) (Fin (d b)) (D b)))
      h
    simpa [coe_coordHom] using h1
  by_cases hb : π b = b
  · have hfg : factorGroup π hτ hπ b = matUnitary (isInvol_tauFix hτ hπ hb) := by
      unfold factorGroup
      split_ifs
      rfl
    rw [hfg] at hg hSb hderb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      have hYb : Y b + tauFix τ b (Y b) = 1 := by
        have h1 := congrFun hY b
        rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
      exact eq_one_of_pow_eq_one_alt (isInvol_tauFix hτ hπ hb) hk ⟨Y b, hYb⟩ hSb hderb hq hp
        hp2 hpS hg hgp
    · push Not at hk
      exact eq_one_of_pow_eq_one_herm (isInvol_tauFix hτ hπ hb) hk hSb hderb hq hp hp2 hpS hg
        hgp
  · have hfg : factorGroup π hτ hπ b = ⊤ := by
      unfold factorGroup
      split_ifs
      rfl
    rw [hfg] at hderb
    exact eq_one_of_pow_eq_one_gl hderb hq hp hpS hgp

end Factors

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)

theorem exists_coreData {A : Subgroup (GL ι K)} (hA : (Nat.card A : K) ≠ 0)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra K (D i)) (_ : ∀ i, NeZero (d i)) (_ : ∀ i, CharP (D i) 2)
      (Φ : PiMat D d →ₐ[K] Matrix ι ι K) (τ : PiMat D d → PiMat D d) (hτ : IsInvol τ)
      (π : Fin r → Fin r) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
      (Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))),
      Function.Injective Φ ∧
      (∀ X : Matrix ι ι K, X ∈ Set.range Φ ↔
        ∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) ∧
      (∀ y, Φ (τ y) = adj (Φ y)) ∧
      (unitaryOf hτ).map (Units.map Φ.toMonoidHom) = adjCent A hadj ∧ (∃ y, y + τ y = 1) ∧
      (∀ b, Sf b ≤ factorGroup π hτ hπ b) ∧
      (∀ b, ∀ u ∈ factorGroup π hτ hπ b, ∀ s ∈ Sf b, u * s * u⁻¹ ∈ Sf b) ∧
      (∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b) ∧
      ∀ b, Sf b = ⊥ ∨ (CFSG.IsQuasisimple (Sf b) ∧
        ∀ z ∈ Sf b, (∀ y ∈ Sf b, z * y = y * z) → z ^ 2 = 1 → z = 1) := by
  obtain ⟨r, D, d, hF, hfin, halg, hnz, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have hch : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR hadj fun X hX =>
    (hR _).mpr (hstab X ((hR X).mp hX))
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine altCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
      have h1 := congrFun hY b
      rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
    · push Not at hk
      exact hermCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk
  choose Sf hSle hSn hder hq using
    hasCore_factorGroup hτ hπ hfix (fun b _ => hasCore_top_GL (d b))
  exact ⟨r, D, d, hF, hfin, halg, hnz, hch, Φ, τ, hτ, π, hπ, Sf, hΦ, hR, hτΦ, himg, hy, hSle, hSn,
    hder, hq⟩

end Data

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)

omit [Finite K] [CharP K 2] in
theorem fix_of_not_dvd {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)]
    [∀ i, Algebra K (D i)] [∀ i, CharP (D i) 2] {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    {Φ : PiMat D d →ₐ[K] Matrix ι ι K} (hΦ : Function.Injective Φ) {τ : PiMat D d → PiMat D d}
    (hτ : IsInvol τ) {π : Fin r → Fin r} (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {A : GL ι K}
    (himg : (unitaryOf hτ).map (Units.map Φ.toMonoidHom) = adjCent (Subgroup.zpowers A) hadj)
    (hy : ∃ y, y + τ y = 1) {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))}
    (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (hder : ∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b) {b : Fin r}
    (hqb : CFSG.IsQuasisimple (Sf b)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpS : ¬ p ∣ Nat.card (Sf b)) {B : GL ι K} (hBu : B ∈ unitaryOf hadj) (hBp : B ^ p = 1)
    (hAB : A * B = B * A) :
    ∀ M ∈ (coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom), M * B = B * M ∧
      (M : Matrix ι ι K) * ((B : Matrix ι ι K) - 1) = (B : Matrix ι ι K) - 1 := by
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hBA : B ∈ adjCent (Subgroup.zpowers A) hadj := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hBu⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute A B from hAB) k).eq
  rw [← himg] at hBA
  obtain ⟨w, hwU, hwB⟩ := hBA
  have hwp : w ^ p = 1 := hΦu (by rw [map_pow, hwB, hBp, map_one])
  have hwb : (w : PiMat D d) b = 1 :=
    coord_eq_one_of_not_dvd hτ hπ hy hSle hder hqb hp hp2 hpS hwU hwp
  have hwπb : (w : PiMat D d) (π b) = 1 := apply_perm_eq_one hτ hπ hwU hwb
  have hBw : (B : Matrix ι ι K) = Φ (w : PiMat D d) := by rw [← hwB]; rfl
  rintro _ ⟨s, hs, rfl⟩
  have hso := (Subgroup.mem_inf.mp hs).2
  have hk : ∀ k, (s : PiMat D d) k * (w : PiMat D d) k = (w : PiMat D d) k * (s : PiMat D d) k ∧
      (s : PiMat D d) k * ((w : PiMat D d) k - 1) = (w : PiMat D d) k - 1 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      rw [hwb]
      simp
    by_cases hkπ : k = π b
    · subst hkπ
      rw [hwπb]
      simp
    rw [hso.2 k hkb hkπ]
    simp
  have h1 : (s : PiMat D d) * (w : PiMat D d) = (w : PiMat D d) * (s : PiMat D d) :=
    funext fun k => (hk k).1
  have h2 : (s : PiMat D d) * ((w : PiMat D d) - 1) = (w : PiMat D d) - 1 :=
    funext fun k => (hk k).2
  have hsΦ : ((Units.map Φ.toMonoidHom s : GL ι K) : Matrix ι ι K) = Φ (s : PiMat D d) := rfl
  constructor
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsΦ, hBw, ← map_mul, h1, map_mul]
  · rw [hsΦ, hBw, ← map_one Φ, ← map_sub, ← map_mul, h2]

omit [Finite K] [CharP K 2] in
theorem exists_le_coreOf_of_fix {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    [∀ i, Algebra K (D i)] {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    {Φ : PiMat D d →ₐ[K] Matrix ι ι K} (hΦ : Function.Injective Φ) {B : GL ι K}
    (hR : ∀ X : Matrix ι ι K, X ∈ Set.range Φ ↔
      ∀ g ∈ Subgroup.zpowers B, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X)
    {τ : PiMat D d → PiMat D d} (hτ : IsInvol τ) {π : Fin r → Fin r}
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (himg : (unitaryOf hτ).map (Units.map Φ.toMonoidHom) = adjCent (Subgroup.zpowers B) hadj)
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))}
    (hder : ∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b)
    {S : Subgroup (GL ι K)} (hSq : CFSG.IsQuasisimple S) (hSU : S ≤ unitaryOf hadj)
    (hSB : ∀ M ∈ S, M * B = B * M ∧
      (M : Matrix ι ι K) * ((B : Matrix ι ι K) - 1) = (B : Matrix ι ι K) - 1) :
    ∃ j₀ : Fin r, Φ (Pi.single j₀ 1) * (B : Matrix ι ι K) = Φ (Pi.single j₀ 1) ∧
      (B : Matrix ι ι K) * Φ (Pi.single j₀ 1) = Φ (Pi.single j₀ 1) ∧ π j₀ = j₀ ∧ Sf j₀ ≠ ⊥ ∧
      S ≤ (coreOf π hτ Sf j₀).map (Units.map Φ.toMonoidHom) := by
  classical
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hBR : (B : Matrix ι ι K) ∈ Set.range Φ :=
    (hR _).mpr fun g hg => commute_of_mem_zpowers rfl hg
  obtain ⟨v, hv⟩ := hBR
  have hvc : ∀ z : PiMat D d, z * v = v * z := by
    intro z
    apply hΦ
    have hz := (hR (Φ z)).mp ⟨z, rfl⟩ B (Subgroup.mem_zpowers B)
    rw [map_mul, map_mul, hv]
    exact hz
  choose cv hcv using exists_scalar_of_central hvc
  have huniq : ∀ j₁ j₂, v j₁ = 1 → v j₂ = 1 → j₁ = j₂ := fun j₁ j₂ h₁ h₂ =>
    eq_of_coord_eq_one Φ hΦ (B := (B : Matrix ι ι K))
      (fun X hX => (hR X).mpr fun g hg => commute_of_mem_zpowers hX hg) hv h₁ h₂
  have hγ : ∀ M ∈ S, ∃ γ ∈ unitaryOf hτ, Units.map Φ.toMonoidHom γ = M := by
    intro M hM
    have hMc : M ∈ adjCent (Subgroup.zpowers B) hadj := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hSU hM⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute B M from (hSB M hM).1.symm) k).eq
    rw [← himg] at hMc
    exact hMc
  have hkey : ∀ M ∈ S, ∀ γ : (PiMat D d)ˣ, Units.map Φ.toMonoidHom γ = M →
      ∀ j, v j ≠ 1 → (γ : PiMat D d) j = 1 := by
    intro M hM γ hγM j hj
    have hγΦ : ((Units.map Φ.toMonoidHom γ : GL ι K) : Matrix ι ι K) = Φ (γ : PiMat D d) :=
      rfl
    have h1 : Φ ((γ : PiMat D d) * (v - 1)) = Φ (v - 1) := by
      rw [map_mul, map_sub, map_one, hv, ← hγΦ, hγM]
      exact (hSB M hM).2
    have h2 := congrFun (hΦ h1) j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h2
    rw [hcv j] at h2
    have hcj : cv j ≠ 1 := fun h => hj (by rw [hcv j, h, map_one])
    have h3 := LinNonsplit.eq_one_of_mul_scalar_sub_one (g := coordHom D d j γ) hcj h2
    have h4 := congrArg (fun g : GL (Fin (d j)) (D j) =>
      (g : Matrix (Fin (d j)) (Fin (d j)) (D j))) h3
    simpa [coe_coordHom] using h4
  obtain ⟨M₀, hM₀, hM₀1⟩ : ∃ M ∈ S, M ≠ 1 := by
    obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
    by_contra hall
    push Not at hall
    apply haa
    have ha : a = 1 := Subtype.ext (hall a a.2)
    rw [ha, one_mul, mul_one]
  obtain ⟨γ₀, hγ₀U, hγ₀M⟩ := hγ M₀ hM₀
  obtain ⟨j₀, hj₀⟩ : ∃ j, (γ₀ : PiMat D d) j ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hM₀1
    rw [← hγ₀M]
    have h1 : γ₀ = 1 := Units.ext (funext hall)
    rw [h1, map_one]
  have hvj₀ : v j₀ = 1 := by
    by_contra h
    exact hj₀ (hkey M₀ hM₀ γ₀ hγ₀M j₀ h)
  have hsupp : ∀ M ∈ S, ∀ γ : (PiMat D d)ˣ, Units.map Φ.toMonoidHom γ = M →
      ∀ j, j ≠ j₀ → (γ : PiMat D d) j = 1 :=
    fun M hM γ hγ j hj => hkey M hM γ hγ j fun h => hj (huniq j j₀ h hvj₀)
  have hπj₀ : π j₀ = j₀ := by
    by_contra hne
    apply hj₀
    have hmem : γ₀ ∈ orbitGroup π hτ (π j₀) := ⟨hγ₀U, fun k _ hk2 =>
      hsupp M₀ hM₀ γ₀ hγ₀M k (by rwa [perm_perm hτ hπ] at hk2)⟩
    have h1 : (γ₀ : PiMat D d) (π j₀) = 1 := hsupp M₀ hM₀ γ₀ hγ₀M _ hne
    rw [eq_one_of_mem_orbitGroup hτ hπ hmem h1]
    rfl
  set Γ := S.comap (Units.map Φ.toMonoidHom) with hΓ
  have hΓmap : Γ.map (Units.map Φ.toMonoidHom) = S :=
    Subgroup.map_comap_eq_self fun M hM => by
      obtain ⟨γ, -, h⟩ := hγ M hM
      exact ⟨γ, h⟩
  have hΓperf : ⁅Γ, Γ⁆ = Γ := by
    apply Subgroup.map_injective hΦu
    rw [Subgroup.map_commutator, hΓmap]
    exact LayerFacts.ggCommutator_eq_of_isQuasisimple hSq
  have hΓorb : Γ ≤ orbitGroup π hτ j₀ := by
    intro γ hγΓ
    obtain ⟨γ', hγ'U, hγ'⟩ := hγ _ hγΓ
    have h1 : γ' = γ := hΦu hγ'
    subst h1
    exact ⟨hγ'U, fun k hk _ => hsupp _ hγΓ γ' rfl k hk⟩
  have hΓcore : Γ ≤ coreOf π hτ Sf j₀ := by
    have hfg : Γ.map (coordHom D d j₀) ≤ factorGroup π hτ hπ j₀ := by
      rintro _ ⟨γ, hγΓ, rfl⟩
      exact coordHom_mem_factorGroup hτ hπ j₀ (hΓorb hγΓ).1
    have hperf' : ⁅Γ.map (coordHom D d j₀), Γ.map (coordHom D d j₀)⁆ =
        Γ.map (coordHom D d j₀) := by
      rw [← Subgroup.map_commutator, hΓperf]
    obtain ⟨k, hk⟩ := hder j₀
    have hle := le_of_ggDer_le hperf' hfg hk
    intro γ hγΓ
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (hle ⟨γ, hγΓ, rfl⟩), hΓorb hγΓ⟩
  have hSfne : Sf j₀ ≠ ⊥ := by
    intro hbot
    have hγ₀Γ : γ₀ ∈ Γ := by
      show Units.map Φ.toMonoidHom γ₀ ∈ S
      rw [hγ₀M]
      exact hM₀
    have h1 := (Subgroup.mem_inf.mp (hΓcore hγ₀Γ)).1
    rw [Subgroup.mem_comap, hbot, Subgroup.mem_bot] at h1
    apply hj₀
    have h4 := congrArg (fun g : GL (Fin (d j₀)) (D j₀) =>
      (g : Matrix (Fin (d j₀)) (Fin (d j₀)) (D j₀))) h1
    simpa [coe_coordHom] using h4
  have hev : (Pi.single j₀ 1 : PiMat D d) * v = Pi.single j₀ 1 := by
    funext i
    by_cases hi : i = j₀
    · subst hi
      simp [hvj₀]
    · simp [hi]
  have hve : v * (Pi.single j₀ 1 : PiMat D d) = Pi.single j₀ 1 := by
    funext i
    by_cases hi : i = j₀
    · subst hi
      simp [hvj₀]
    · simp [hi]
  refine ⟨j₀, by rw [← hv, ← map_mul, hev], by rw [← hv, ← map_mul, hve], hπj₀, hSfne, ?_⟩
  rw [← hΓmap]
  exact Subgroup.map_mono hΓcore

theorem exists_coreFamilies_lift {A B : GL ι K} (hAu : A ∈ unitaryOf hadj)
    (hBu : B ∈ unitaryOf hadj) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hAp : A ^ p = 1)
    (hBp : B ^ p = 1) (hAB : A * B = B * A)
    (hsymdA : ∃ Y : Matrix ι ι K, Y * (A : Matrix ι ι K) = (A : Matrix ι ι K) * Y ∧
      Y + adj Y = 1)
    (hsymdB : ∃ Y : Matrix ι ι K, Y * (B : Matrix ι ι K) = (B : Matrix ι ι K) * Y ∧
      Y + adj Y = 1) :
    ∃ (β : Type) (Sx : β → Subgroup (GL ι K)),
      IsCoreFamily (adjCent (Subgroup.zpowers A) hadj) Sx ∧
      ∃ (β' : Type) (Sy : β' → Subgroup (GL ι K)),
        IsCoreFamily (adjCent (Subgroup.zpowers B) hadj) Sy ∧
        ∀ c, ¬ p ∣ Nat.card (Sx c) → ∃ c', Sx c ≤ Sy c' := by
  classical
  have hsym : ∀ {C : GL ι K}, (∃ Y : Matrix ι ι K, Y * (C : Matrix ι ι K) =
      (C : Matrix ι ι K) * Y ∧ Y + adj Y = 1) → ∃ Y : Matrix ι ι K,
      (∀ g ∈ Subgroup.zpowers C, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
        Y + adj Y = 1 := fun ⟨Y, hYC, hY⟩ => ⟨Y, fun _ hg => commute_of_mem_zpowers hYC hg, hY⟩
  obtain ⟨r, D, d, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, -, -, himg, hy, hSle, hSn, hder,
    hq⟩ := exists_coreData hadj (natCast_card_zpowers_ne_zero hp hp2 hAp)
      (adj_stab_zpowers hadj hAu) (hsym hsymdA)
  obtain ⟨r', D', d', _, _, _, _, _, Φ', τ', hτ', π', hπ', Sf', hΦ', hR', -, himg', -, hSle', hSn',
    hder', hq'⟩ := exists_coreData hadj (natCast_card_zpowers_ne_zero hp hp2 hBp)
      (adj_stab_zpowers hadj hBu) (hsym hsymdB)
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hΦu' : Function.Injective (Units.map Φ'.toMonoidHom) :=
    Units.map_injective (f := Φ'.toMonoidHom) hΦ'
  have hFx : IsCoreFamily (adjCent (Subgroup.zpowers A) hadj)
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h
  have hFy : IsCoreFamily (adjCent (Subgroup.zpowers B) hadj)
      (fun c : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} =>
        (coreOf π' hτ' Sf' c.1).map (Units.map Φ'.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ' hπ' hSle' hSn' hder' hq').map _ hΦu'
    rwa [himg'] at h
  refine ⟨_, _, hFx, _, _, hFy, fun c hpc => ?_⟩
  obtain ⟨b, hbπ, hSb⟩ := c
  have hpS : ¬ p ∣ Nat.card (Sf b) := by
    intro h
    apply hpc
    show p ∣ Nat.card ((coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom))
    rw [Subgroup.card_map_of_injective hΦu,
      Nat.card_congr (Equiv.ofBijective _ (bijective_coreOf hτ hπ hSle b))]
    exact h
  have hMB := fix_of_not_dvd hadj hΦ hτ hπ himg hy hSle hder ((hq b).resolve_left hSb).1 hp hp2
    hpS hBu hBp hAB
  obtain ⟨j₀, -, -, hπj₀, hSf'ne, hle⟩ := exists_le_coreOf_of_fix hadj hΦ' hR' hτ' hπ' himg' hder'
    (hFx.2.2.1 ⟨b, hbπ, hSb⟩) ((hFx.1 ⟨b, hbπ, hSb⟩).trans inf_le_right) hMB
  exact ⟨⟨j₀, le_of_eq hπj₀.symm, hSf'ne⟩, hle⟩

end Lift

end ClNonsplit

end CFSG.StandardType
