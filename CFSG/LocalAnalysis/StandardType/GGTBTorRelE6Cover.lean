module

public import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.StandardType.GGTBE6Cover CFSG.StandardType.TableBExc

def recipeE6Cover {K : Type} [Field K] [Finite K] :
    ↥(e6Data_valid.minGroup K) →* RecipeGroup .E6 K :=
  (recipeEquiv .E6 K).symm.toMonoidHom.comp (e6Isogeny K)

theorem recipeE6Cover_ker_eq {K : Type} [Field K] [Finite K] :
    (recipeE6Cover (K := K)).ker = (e6Isogeny K).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (recipeEquiv .E6 K).symm (e6Isogeny K x) = 1 ↔ e6Isogeny K x = 1
  exact (recipeEquiv .E6 K).symm.map_eq_one_iff

private theorem card_ker_dvd_of_surjective_lift {U L R : Type} [Group U] [Group L] [Group R]
    (φ : U →* L) (hφ : Function.Surjective φ) (ψ : L →* R) (π : U →* R)
    (hcomp : ∀ x, ψ (φ x) = π x) : Nat.card ψ.ker ∣ Nat.card π.ker := by
  have hmap : π.ker.map φ = ψ.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ψ (φ y) = 1
      rw [hcomp]
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hφ x
      refine ⟨y, ?_, rfl⟩
      change π y = 1
      rw [← hcomp]
      exact hx
  rw [← hmap]
  exact Subgroup.card_map_dvd _ _

theorem card_ker_recipeE6Cover_dvd_three {K : Type} [Field K] [Finite K] :
    Nat.card (recipeE6Cover (K := K)).ker ∣ 3 := by
  rw [recipeE6Cover_ker_eq, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
    (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := K)).1]
  exact Nat.gcd_dvd_left 3 _

theorem exists_cover_phi_recipe_E6 (K : Type) [Field K] [Finite K] [CharP K 2]
    (L : Type) [Group L] [Finite L]
    (ψ : L →* RecipeGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    ∃ φ : ↥(e6Data_valid.minGroup K) →* L,
      Function.Surjective φ ∧ (∀ x, ψ (φ x) = recipeE6Cover (K := K) x) ∧
      φ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) ∧ Nat.card φ.ker ∣ 3 := by
  classical
  let ε := recipeEquiv .E6 K
  let ψ' : L →* adjointGroup .E6 K := ε.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := ε.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : ε (ψ x) = 1 := by simpa [ψ'] using hx
    exact ε.injective (by rw [hx', map_one])
  obtain ⟨φ, hφs, hφ, hφk⟩ := exists_cover_phi K L ψ' hψ' hker' hperf
  have hφπ : ∀ x, ψ (φ x) = recipeE6Cover (K := K) x := by
    intro x
    have h1 := congrArg (⇑ε.symm) (hφ x)
    simpa [ψ', recipeE6Cover, ε] using h1
  have hkerφ : φ.ker ≤ (recipeE6Cover (K := K)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hφπ x, hx, map_one]
  refine ⟨φ, hφs, hφπ, hφk, ?_⟩
  exact (Subgroup.card_dvd_of_le hkerφ).trans card_ker_recipeE6Cover_dvd_three

theorem exists_innerModel_recipe_E6 {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hIp : GGOutdiagPrime p (RecipeGroup .E6 K) (RecipeID .E6 K))
    (hcp : GGCenterPrime p (RecipeGroup .E6 K))
    {L : Type} [Group L] [Finite L] (ψ : L →* RecipeGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) {A : Subgroup (MulAut L)} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ RecipeID .E6 K, ∀ l : L, φ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ Λ : RecipeGroup .E6 K →* MulAut L,
      (∀ {e : RecipeGroup .E6 K} {x : L}, ψ x = e → Λ e = MulAut.conj x) ∧
      Function.Injective Λ ∧
      (∀ (e : RecipeGroup .E6 K) (l : L), ψ (Λ e l) = e * ψ l * e⁻¹) ∧
      (∀ a ∈ A, ∃ e : RecipeGroup .E6 K, Λ e = a) ∧
      IsElemAbelian p (A.comap Λ) ∧ Nat.card (A.comap Λ) = Nat.card A ∧
      (A.comap Λ).map Λ = A ∧
      (∀ g : RecipeGroup .E6 K, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 →
        g ∈ A.comap Λ) := by
  obtain ⟨Λ, hΛ, hΛi, hΛm, hAΛ, hEab, hEcard, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E6 K) hIp hcp ψ hψ hker hperf
      hA hAI hsc
  have hAle : A ≤ Λ.range := fun a ha => by
    obtain ⟨e, he⟩ := hAΛ a ha
    exact ⟨e, he⟩
  exact ⟨Λ, hΛ, hΛi, hΛm, hAΛ, hEab, hEcard, by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hAle], hEsc⟩

theorem exists_section_twistedE6Group_four :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 2),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : twistedE6Group 2 2 →* E, ∀ g, π (s g) = g := by
  intro E _ _ π hπ hcen
  have hK : Nat.card (GaloisField 2 (2 * 2)) = 4 ^ 2 := by
    have h := CFSG.LieType.Universal.card_galoisField_two_mul 2 2 (by norm_num)
    simpa using h
  have hθq : ∀ c, frobQ 2 2 c = c ^ 4 := by
    intro c
    rw [frobQ_apply]
    norm_num
  exact CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_four_exists_section
    (K := GaloisField 2 (2 * 2)) (θ := frobQ 2 2) hK hθq hπ hcen

theorem exists_section_twistedE6Group_of_five {n : ℕ} (hn : 3 ≤ n) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : twistedE6Group 2 n →* E, ∀ g, π (s g) = g := by
  intro E _ _ π hπ hcen
  have hq : 5 ≤ 2 ^ n := by
    calc 5 ≤ 8 := by norm_num
      _ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 n (by omega)
  have hθq : ∀ c, frobQ 2 n c = c ^ (2 ^ n) := by
    intro c
    rw [frobQ_apply]
  exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_central
    (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n) (q := 2 ^ n) hq hk hθq hπ hcen

theorem exists_section_twistedE6Group {n : ℕ} (hn : 2 ≤ n) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : twistedE6Group 2 n →* E, ∀ g, π (s g) = g := by
  intro E _ _ π hπ hcen
  rcases eq_or_lt_of_le hn with h2 | h3
  · subst h2
    exact exists_section_twistedE6Group_four E π hπ hcen
  · exact exists_section_twistedE6Group_of_five (n := n) (by omega) E π hπ hcen

theorem exists_cover_phi_recipe_twE6 {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (L : Type) [Group L] [Finite L]
    (ψ : L →* TwE6Delta.RecipeR K n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    ∃ (π : twistedE6Group 2 n →* TwE6Delta.RecipeR K n)
      (φ : twistedE6Group 2 n →* L),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center (twistedE6Group 2 n) ∧
      Function.Surjective φ ∧ (∀ x, ψ (φ x) = π x) ∧
      φ.ker ≤ Subgroup.center (twistedE6Group 2 n) ∧ Nat.card φ.ker ∣ 3 := by
  classical
  obtain ⟨π, hπ, hπk⟩ := TwE6Delta.exists_sc_surjection (K := K) (n := n) (by omega) hK
  let : Finite (twistedE6Group 2 n) := TwE6DD2.finite_twistedE6Group n
  obtain ⟨φ, hφ, hφs⟩ := E6ThreeKernel.exists_surjective_of_split hπ
    (exists_section_twistedE6Group hn) hψ hker hperf
  have hφk : φ.ker ≤ Subgroup.center (twistedE6Group 2 n) := by
    intro x hx
    apply hπk
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 := hφ x
    rw [hx, map_one] at h1
    exact h1.symm
  have hπ3 : Nat.card π.ker ∣ 3 :=
    (Subgroup.card_dvd_of_le hπk).trans (TwE6DD2.card_center_dvd_three (n := n) (by omega))
  have hkerφ : φ.ker ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 := hφ x
    rw [hx, map_one] at h1
    exact h1.symm
  exact ⟨π, φ, hπ, hπk, hφs, hφ, hφk, (Subgroup.card_dvd_of_le hkerφ).trans hπ3⟩

theorem exists_innerModel_recipe_twE6 {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hIp : GGOutdiagPrime p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n))
    (hcp : GGCenterPrime p (TwE6Delta.RecipeR K n))
    {L : Type} [Group L] [Finite L] (ψ : L →* TwE6Delta.RecipeR K n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) {A : Subgroup (MulAut L)} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L, φ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ Λ : TwE6Delta.RecipeR K n →* MulAut L,
      (∀ {e : TwE6Delta.RecipeR K n} {x : L}, ψ x = e → Λ e = MulAut.conj x) ∧
      Function.Injective Λ ∧
      (∀ (e : TwE6Delta.RecipeR K n) (l : L), ψ (Λ e l) = e * ψ l * e⁻¹) ∧
      (∀ a ∈ A, ∃ e : TwE6Delta.RecipeR K n, Λ e = a) ∧
      IsElemAbelian p (A.comap Λ) ∧ Nat.card (A.comap Λ) = Nat.card A ∧
      (A.comap Λ).map Λ = A ∧
      (∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 →
        g ∈ A.comap Λ) := by
  obtain ⟨Λ, hΛ, hΛi, hΛm, hAΛ, hEab, hEcard, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (TwE6Delta.center_recipeR_eq_bot hn hK) hIp hcp ψ hψ hker
      hperf hA hAI hsc
  have hAle : A ≤ Λ.range := fun a ha => by
    obtain ⟨e, he⟩ := hAΛ a ha
    exact ⟨e, he⟩
  exact ⟨Λ, hΛ, hΛi, hΛm, hAΛ, hEab, hEcard, by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hAle], hEsc⟩

theorem card_ker_dvd_gcd_recipe_E6 {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] (ψ : L →* RecipeGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : Nat.card ψ.ker ∣ Nat.gcd 3 (Nat.card K - 1) := by
  obtain ⟨φ, hφs, hφ, -, -⟩ := exists_cover_phi_recipe_E6 K L ψ hψ hker hperf
  have hdiv := card_ker_dvd_of_surjective_lift φ hφs ψ (recipeE6Cover (K := K)) hφ
  have hc : Nat.card (recipeE6Cover (K := K)).ker = Nat.gcd 3 (Nat.card K - 1) := by
    rw [recipeE6Cover_ker_eq,
      CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := K)).1]
  exact hc ▸ hdiv

theorem card_ker_dvd_gcd_recipe_twE6 {n : ℕ} (hn : 2 ≤ n) {K L : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) [Group L] [Finite L]
    (ψ : L →* TwE6Delta.RecipeR K n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    Nat.card ψ.ker ∣ Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨π, φ, -, hπk, hφs, hφ, -, -⟩ :=
    exists_cover_phi_recipe_twE6 hn hK L ψ hψ hker hperf
  have hdiv := card_ker_dvd_of_surjective_lift φ hφs ψ π hφ
  have hc : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) := by
    change Nat.card (Subgroup.center
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n))) = _
    exact (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (q := 2 ^ n) (CFSG.LieType.Universal.card_galoisField_two_mul 2 n (by omega))
      (fun c => by rw [frobQ_apply])).1
  exact hdiv.trans (hc ▸ Subgroup.card_dvd_of_le hπk)

private theorem coprime_two_pow_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := by
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ := (Nat.even_pow.mpr ⟨even_two, by omega⟩ : Even (2 ^ n))
    exact ⟨k - 1, by have := (Nat.one_le_two_pow (n := n)); omega⟩
  have hsum : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by
    have := (Nat.one_le_two_pow (n := n))
    omega
  rw [hsum, Nat.coprime_self_add_right]
  exact hodd.coprime_two_right

theorem coprime_card_ker_recipe_E6_relative {n : ℕ} (hn : 1 ≤ n)
    {K L : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    [Group L] [Finite L] (ψ : L →* RecipeGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : Nat.Coprime (2 ^ n + 1) (Nat.card ψ.ker) := by
  have hdiv := (card_ker_dvd_gcd_recipe_E6 ψ hψ hker hperf).trans
    (Nat.gcd_dvd_right 3 (Nat.card K - 1))
  rw [hK] at hdiv
  exact Nat.Coprime.of_dvd_right hdiv (coprime_two_pow_sub_one_add_one hn).symm

theorem coprime_card_ker_recipe_twE6_relative {n : ℕ} (hn : 2 ≤ n)
    {K L : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    [Group L] [Finite L] (ψ : L →* TwE6Delta.RecipeR K n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : Nat.Coprime (2 ^ n - 1) (Nat.card ψ.ker) := by
  exact Nat.Coprime.of_dvd_right
    ((card_ker_dvd_gcd_recipe_twE6 hn hK ψ hψ hker hperf).trans
      (Nat.gcd_dvd_right 3 (2 ^ n + 1)))
    (coprime_two_pow_sub_one_add_one (by omega))

end CFSG.StandardType
