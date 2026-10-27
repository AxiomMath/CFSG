module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Swap
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Cv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Pre

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open CFSG.LieType.BorelTits (pCoreOf_isPGroup le_normalizer_pCoreOf)
open scoped commutatorElement

namespace CFSG.Quasithin.S15223P4.D1

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

omit [Finite G] in
theorem key_identity {Γ : Type*} [Group Γ] (Y y' g : Γ) :
    (y' * Y⁻¹)⁻¹ * (g * (y' * Y⁻¹) * g⁻¹) =
      (Y * (g * Y * g⁻¹)⁻¹) * ((g * Y * g⁻¹) * (y'⁻¹ * (g * y' * g⁻¹)) * (g * Y * g⁻¹)⁻¹) := by
  group

theorem actionOn_ne_one (c : P4Ctx T Mc M H B₀ I X) (hpre : P4N1pre T Mc M H B₀ I X) {y : G}
    (hy : y ∈ X ⊓ M) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    A4.actionOn (V154 T Mc M) M (le_normalizer_V154 T Mc M) ⟨y, hy.2⟩ ≠ 1 := by
  intro h
  have hC : y ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    ⟨hy.2, (A4.actionOn_eq_one_iff (le_normalizer_V154 T Mc M) ⟨y, hy.2⟩).mp h⟩
  have h1 : y ∈ X ⊓ (Mc ⊓ I) ⊓ (X ⊓ M) := ⟨⟨hy.1, cv_le_inf152 c.setting c.inputs hC⟩, hy⟩
  rw [hpre.M0_inf_MX] at h1
  exact false_of_isPGroup_two c.sylow.isPGroup h1.1 hy3 hy1

theorem false_of_swap (c : P4Ctx T Mc M H B₀ I X) (hpre : P4N1pre T Mc M H B₀ I X)
    (ψ : OTwoQuot X ≃* SL3F2) {s : G} (hsS : s ∈ sOf152 T Mc M B₀)
    (hcomm : ⁅X, conjSub s X⁆ ≤ pCoreOf 2 I) : False := by
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3MX : 3 ∣ Nat.card ↥(X ⊓ M) := ⟨_, hpre.card_MX⟩
  obtain ⟨y0, hy0⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ M)) 3 h3MX
  have hyXM : (y0 : G) ∈ X ⊓ M := y0.2
  have hy3 : (y0 : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y0
    rw [hy0] at this
    exact congrArg Subtype.val this
  have hy1 : (y0 : G) ≠ 1 := fun h => by
    have : y0 = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy0; omega
  set y : G := (y0 : G) with hydef
  have hyN : y ∈ M ⊓ I := ⟨hyXM.2, c.X_le_I hyXM.1⟩
  have hSN : sOf152 T Mc M B₀ ≤ M ⊓ I := c.S_le_N
  have hsN : s ∈ M ⊓ I := hSN hsS
  set y' : G := s * y * s⁻¹ with hy'def
  have hy'N : y' ∈ M ⊓ I := (M ⊓ I).mul_mem ((M ⊓ I).mul_mem hsN hyN) ((M ⊓ I).inv_mem hsN)
  have hy'3 : y' ^ 3 = 1 := by rw [hy'def, conj_pow, hy3, mul_one, mul_inv_cancel]
  have hy'X' : y' ∈ conjSub s X := by
    rw [mem_conjSub]
    have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
    rw [hy'def, e]
    exact hyXM.1
  have hyM : y ∈ M := hyXM.2
  have hy'M : y' ∈ M := hy'N.1
  obtain ⟨g, hgXM, hginv⟩ := hpre.inv_MX y hyXM (by rw [hy3]; exact one_mem _)
    (fun h => false_of_isPGroup_two (pCoreOf_isPGroup 2 X) h hy3 hy1)
  have hgM : g ∈ M := hgXM.2
  have hgX : g ∈ X := hgXM.1
  have hgI : g ∈ I := c.X_le_I hgX
  have hsM : s ∈ M := hsN.1
  let yM : ↥M := ⟨y, hyM⟩
  let y'M : ↥M := ⟨y', hy'M⟩
  let gM : ↥M := ⟨g, hgM⟩
  let sM : ↥M := ⟨s, hsM⟩
  have hρy : ρ yM ≠ 1 := actionOn_ne_one c hpre hyXM hy3 hy1
  have hyM3 : yM ^ 3 = 1 := Subtype.ext hy3
  have hρy3 : ρ yM ^ 3 = 1 := by rw [← map_pow, hyM3, map_one]
  have hy'eq : y'M = sM * yM * sM⁻¹ := rfl
  have hρy'ne : ρ y'M ≠ 1 := by
    intro h
    apply hρy
    have : ρ y'M = ρ sM * ρ yM * (ρ sM)⁻¹ := by rw [hy'eq, map_mul, map_mul, map_inv]
    rw [this] at h
    have h2 := congrArg (fun z => (ρ sM)⁻¹ * z * ρ sM) h
    simpa [mul_assoc] using h2
  obtain ⟨k, hk⟩ := exists_zpow_of_cube c hyN hy'N hy3 hy'3 hρy
  have hmem : ρ y'M ∈ Subgroup.zpowers (ρ yM) := Subgroup.mem_zpowers_iff.mpr ⟨k, hk.symm⟩
  obtain ⟨ε, hε, hρε⟩ : ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ ρ y'M = ρ yM ^ ε := by
    rcases mem_zpowers_cases hρy3 hmem with h | h | h
    · exact absurd h hρy'ne
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨2, Or.inr rfl, h⟩
  let Y : ↥M := yM ^ ε
  let ygM : ↥M := gM * yM * gM⁻¹
  let uM : ↥M := y'M * Y⁻¹
  have hu : ρ uM = 1 := by
    show ρ (y'M * Y⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hρε, mul_inv_cancel]
  let wM : ↥M := uM⁻¹ * (gM * uM * gM⁻¹)
  have hw1 : ρ wM = 1 := by
    show ρ (uM⁻¹ * (gM * uM * gM⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu]
    simp
  let aM : ↥M := Y * (gM * Y * gM⁻¹)⁻¹
  let cM : ↥M := y'M⁻¹ * (gM * y'M * gM⁻¹)
  let c'M : ↥M := (gM * Y * gM⁻¹) * cM * (gM * Y * gM⁻¹)⁻¹
  have hw : wM = aM * c'M := key_identity Y y'M gM
  have hy'inv : y'⁻¹ ∈ conjSub s X := (conjSub s X).inv_mem hy'X'
  have hcI : (cM : G) ∈ pCoreOf 2 I := by
    have h1 : ⁅y'⁻¹, g⁆ ∈ ⁅conjSub s X, X⁆ := Subgroup.commutator_mem_commutator hy'inv hgX
    rw [Subgroup.commutator_comm] at h1
    have h2 := hcomm h1
    have e : ⁅y'⁻¹, g⁆ = (cM : G) := by
      show y'⁻¹ * g * y'⁻¹⁻¹ * g⁻¹ = y'⁻¹ * (g * y' * g⁻¹)
      group
    rwa [e] at h2
  have hYgI : ((gM * Y * gM⁻¹ : ↥M) : G) ∈ I := by
    have : ((gM * Y * gM⁻¹ : ↥M) : G) = g * y ^ ε * g⁻¹ := by
      simp [Y, gM, yM]
    rw [this]
    exact I.mul_mem (I.mul_mem hgI (I.pow_mem hyN.2 ε)) (I.inv_mem hgI)
  have hc'I : (c'M : G) ∈ pCoreOf 2 I := by
    have hnorm := le_normalizer_pCoreOf 2 I hYgI
    exact (Subgroup.mem_normalizer_iff.mp hnorm (cM : G)).mp hcI
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 I ⟨(c'M : G), hc'I⟩
  have hc'm : c'M ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hρc' : ρ c'M ^ 2 ^ m = 1 := by rw [← map_pow, hc'm, map_one]
  have hρa : ρ aM = (ρ c'M)⁻¹ := by
    have : aM = wM * c'M⁻¹ := by rw [hw]; group
    rw [this, map_mul, map_inv, hw1, one_mul]
  have hygN : g * y * g⁻¹ ∈ M ⊓ I :=
    (M ⊓ I).mul_mem ((M ⊓ I).mul_mem ⟨hgM, hgI⟩ hyN) ((M ⊓ I).inv_mem ⟨hgM, hgI⟩)
  have hyg3 : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  obtain ⟨k', hk'⟩ := exists_zpow_of_cube c hyN hygN hy3 hyg3 hρy
  have hρyg : ρ ygM ∈ Subgroup.zpowers (ρ yM) := Subgroup.mem_zpowers_iff.mpr ⟨k', hk'.symm⟩
  have hρa_mem : ρ aM ∈ Subgroup.zpowers (ρ yM) := by
    have e : gM * Y * gM⁻¹ = ygM ^ ε := by simp only [Y, ygM, conj_pow]
    show ρ (Y * (gM * Y * gM⁻¹)⁻¹) ∈ _
    rw [e, map_mul, map_inv, map_pow, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ hρyg _))
  have hρa3 : ρ aM ^ 3 = 1 := by
    rcases mem_zpowers_cases hρy3 hρa_mem with h | h | h
    · rw [h, one_pow]
    · rw [h, hρy3]
    · rw [h, ← pow_mul, mul_comm, pow_mul, hρy3, one_pow]
  have hρa1 : ρ aM = 1 := by
    have h2 : ρ aM ^ 2 ^ m = 1 := by rw [hρa, inv_pow, hρc', inv_one]
    exact C1Pack12.eq_one_of_pow_two_pow_of_pow_three' h2 hρa3
  have haC : (aM : G) ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (A4.actionOn_eq_one_iff hMV aM).mp hρa1
  have haXM : (aM : G) ∈ X ⊓ M := by
    have hY : y ^ ε ∈ X ⊓ M := (X ⊓ M).pow_mem hyXM ε
    have hYg : g * y ^ ε * g⁻¹ ∈ X ⊓ M :=
      (X ⊓ M).mul_mem ((X ⊓ M).mul_mem hgXM hY) ((X ⊓ M).inv_mem hgXM)
    exact (X ⊓ M).mul_mem hY ((X ⊓ M).inv_mem hYg)
  have haS : (aM : G) ∈ sOf152 T Mc M B₀ ⊓ X := by
    have h1 : (aM : G) ∈ X ⊓ (Mc ⊓ I) ⊓ (X ⊓ M) :=
      ⟨⟨haXM.1, cv_le_inf152 c.setting c.inputs ⟨haXM.2, haC⟩⟩, haXM⟩
    rwa [hpre.M0_inf_MX] at h1
  have hyX : y ∈ X := hyXM.1
  let yX : ↥X := ⟨y, hyX⟩
  let gX : ↥X := ⟨g, hgX⟩
  let ρX := rhoOf ψ
  have hη3 : ρX yX ^ 3 = 1 := by
    rw [← map_pow]
    have : yX ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  have hη1 : ρX yX ≠ 1 := fun h =>
    false_of_isPGroup_two (pCoreOf_isPGroup 2 X) ((rhoOf_eq_one_iff ψ hyX).mp h) hy3 hy1
  have hginvη : ρX (gX * yX * gX⁻¹) * ρX yX = 1 := by
    rw [← map_mul]
    exact (rhoOf_eq_one_iff ψ (X.mul_mem (X.mul_mem (X.mul_mem hgX hyX) (X.inv_mem hgX)) hyX)).mpr
      hginv
  have hηg : ρX (gX * yX * gX⁻¹) = (ρX yX)⁻¹ := eq_inv_of_mul_eq_one_left hginvη
  let aX : ↥X := ⟨(aM : G), haS.2⟩
  have haXeq : aX = yX ^ ε * (gX * yX ^ ε * gX⁻¹)⁻¹ := rfl
  have hρXa : ρX aX = ρX yX ^ ε * ρX yX ^ ε := by
    rw [haXeq, map_mul, map_inv, ← conj_pow, map_pow, map_pow, hηg, inv_pow, inv_inv]
  have hρXa3 : ρX aX ^ 3 = 1 := by
    rw [hρXa, ← pow_add, ← pow_mul, mul_comm, pow_mul, hη3, one_pow]
  obtain ⟨j, hj⟩ := c.sylow.isPGroup ⟨(aM : G), haS.1⟩
  have hajX : aX ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
  have hρXa1 : ρX aX = 1 := by
    have h2 : ρX aX ^ 2 ^ j = 1 := by rw [← map_pow, hajX, map_one]
    exact C1Pack12.eq_one_of_pow_two_pow_of_pow_three' h2 hρXa3
  rw [hρXa, ← pow_add] at hρXa1
  apply hη1
  rcases hε with rfl | rfl
  · calc ρX yX = ρX yX ^ 3 * (ρX yX ^ (1 + 1))⁻¹ := by group
      _ = 1 := by rw [hη3, hρXa1]; simp
  · calc ρX yX = ρX yX ^ (2 + 2) * (ρX yX ^ 3)⁻¹ := by group
      _ = 1 := by rw [hη3, hρXa1]; simp

theorem normal_of_pre (c : P4Ctx T Mc M H B₀ I X) (hpre : P4N1pre T Mc M H B₀ I X)
    (ψ : OTwoQuot X ≃* SL3F2) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    I ≤ Subgroup.normalizer (X : Set G) := by
  rcases normal_or_swap c h37 h38 with h | ⟨s, hsS, -, -, hcomm⟩
  · exact h
  · exact (false_of_swap c hpre ψ hsS hcomm).elim

end CFSG.Quasithin.S15223P4.D1
