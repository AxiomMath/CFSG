module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Solvable
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.SettingAPI

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

omit [Finite G] in
theorem le_normalizer_iInf {ι : Sort*} {B : Subgroup G} {X : ι → Subgroup G}
    (h : ∀ i, B ≤ Subgroup.normalizer (X i : Set G)) :
    B ≤ Subgroup.normalizer ((⨅ i, X i : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_iInf]
  exact forall_congr' fun i => Subgroup.mem_normalizer_iff.mp (h i hb) x

@[expose] def primeComplement (p q : ℕ) (A : Subgroup G) (θ : Subgroup G → Subgroup G) :
    Subgroup G :=
  signalizerPrimeCompletion p 1 A θ (signalizerSpectrum p 1 A θ \ {q})

theorem primeComplement_spec (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    solvableSignalizerCompatible p 1 A θ (primeComplement p q A θ) ∧
      Nat.Coprime q (Nat.card (primeComplement p q A θ)) ∧
      signalizerCommonFixed p 1 A θ ≤ Subgroup.normalizer (primeComplement p q A θ : Set G) := by
  have hq' := prime_of_two_or_three hq
  have hcomplete := h.locallyComplete.2 q (mem_spectrum h hq)
  have hctrl := signalizer_prime_completion_control p 1 h.prime A h.elementary (large_two h) θ
    h.conditions (signalizerSpectrum p 1 A θ \ {q}) hcomplete.1
  refine ⟨⟨hctrl.1, hcomplete.2⟩, ?_, hctrl.2.2.1⟩
  apply (prime_supported_complement_singleton_iff_coprime q hq' _).mp
  intro ℓ hℓ hd
  exact (hctrl.2.1 ℓ hℓ hd).2

omit [Finite G] in
theorem hyperplaneMeet_le_primeCoreIn {q : ℕ} {B S : Subgroup G}
    (hS : S ∈ signalizerFunctorEk p 1 A) (hSB : S ≤ B) :
    hyperplaneMeet p q A B θ ≤ primeCoreIn ({q}ᶜ : Set ℕ) (θ S) :=
  (iInf_le _ S).trans ((iInf_le _ hS).trans (iInf_le _ hSB))

theorem hyperplaneMeetJoin_le_core (h : Setting p A θ) {q : ℕ} {B : Subgroup G}
    (hB : B ∈ Coprime.hyperplanes p A) :
    hyperplaneMeetJoin p q A θ ≤ signalizerHyperplaneCore p 1 q A B θ := by
  unfold hyperplaneMeetJoin
  refine iSup₂_le fun B₁ hB₁ => ?_
  obtain ⟨S, hS, hSB, hSB₁⟩ := exists_Ek_le_inf_hyperplanes h.prime h.elementary h.large hB hB₁
  exact (hyperplaneMeet_le_primeCoreIn hS hSB₁).trans
    (signalizer_hyperplane_core_contains p 1 q A B θ S hS hSB)

theorem core_le_primeComplement (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {B : Subgroup G} : signalizerHyperplaneCore p 1 q A B θ ≤ primeComplement p q A θ :=
  (signalizer_hyperplane_core_properties p 1 q h.prime (prime_of_two_or_three hq) A B
    h.elementary (large_two h) θ h.conditions h.locallyComplete (mem_spectrum h hq)).1

theorem hyperplaneCommonFixed_le_normalizer_core (h : Setting p A θ) {q : ℕ}
    (hq : q = 2 ∨ q = 3) {B : Subgroup G} :
    signalizerHyperplaneCommonFixed p 1 A B θ ≤
      Subgroup.normalizer (signalizerHyperplaneCore p 1 q A B θ : Set G) :=
  (signalizer_hyperplane_core_properties p 1 q h.prime (prime_of_two_or_three hq) A B
    h.elementary (large_two h) θ h.conditions h.locallyComplete (mem_spectrum h hq)).2.2

theorem hyperplaneMeetJoin_le_primeComplement (h : Setting p A θ) {q : ℕ}
    (hq : q = 2 ∨ q = 3) : hyperplaneMeetJoin p q A θ ≤ primeComplement p q A θ := by
  obtain ⟨B, hB⟩ := exists_mem_hyperplanes h.prime h.elementary (large_sq h)
  exact (hyperplaneMeetJoin_le_core h hB).trans (core_le_primeComplement h hq)

theorem actor_le_normalizer_hyperplaneMeetJoin (h : Setting p A θ) (q : ℕ) :
    A ≤ Subgroup.normalizer (hyperplaneMeetJoin p q A θ : Set G) := by
  unfold hyperplaneMeetJoin
  refine normalizer_biSup_of_le A _ (fun B => hyperplaneMeet p q A B θ) fun B _ => ?_
  unfold hyperplaneMeet
  refine le_normalizer_iInf fun S => le_normalizer_iInf fun hS => le_normalizer_iInf fun _ => ?_
  exact le_normalizer_primeCoreIn _ (h.conditions.normalized S hS)

theorem commonFixed_le_normalizer_hyperplaneMeetJoin (q : ℕ) :
    signalizerCommonFixed p 1 A θ ≤ Subgroup.normalizer (hyperplaneMeetJoin p q A θ : Set G) := by
  unfold hyperplaneMeetJoin
  refine normalizer_biSup_of_le _ _ (fun B => hyperplaneMeet p q A B θ) fun B _ => ?_
  unfold hyperplaneMeet
  refine le_normalizer_iInf fun S => le_normalizer_iInf fun hS => le_normalizer_iInf fun _ => ?_
  exact le_normalizer_primeCoreIn _ (commonFixed_le_normalizer_value hS)

theorem compat_hyperplaneMeetJoin (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    solvableSignalizerCompatible p 1 A θ (hyperplaneMeetJoin p q A θ) :=
  compat_of_le (primeComplement_spec h hq).1 (hyperplaneMeetJoin_le_primeComplement h hq)
    (actor_le_normalizer_hyperplaneMeetJoin h q)

theorem coprime_hyperplaneMeetJoin (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    Nat.Coprime q (Nat.card (hyperplaneMeetJoin p q A θ)) :=
  (primeComplement_spec h hq).2.1.of_dvd_right
    (Subgroup.card_dvd_of_le (hyperplaneMeetJoin_le_primeComplement h hq))

theorem le_hyperplaneMeetJoin (h : Setting p A θ) {q : ℕ} {H : Subgroup G}
    (hH : solvableSignalizerCompatible p 1 A θ H)
    (hcore : ∀ S ∈ signalizerFunctorEk p 1 A, H ⊓ θ S ≤ primeCoreIn ({q}ᶜ : Set ℕ) (θ S)) :
    H ≤ hyperplaneMeetJoin p q A θ := by
  have hgen := generation_hyperplanes h.prime h.elementary (large_sq h) hH.1.1
    (coprime_card h hH.1)
  refine le_trans (le_of_eq hgen.symm) ?_
  refine iSup₂_le fun B hB => ?_
  refine le_trans ?_ (le_iSup₂ (f := fun B (_ : B ∈ Coprime.hyperplanes p A) =>
    hyperplaneMeet p q A B θ) B hB)
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hSB => ?_
  refine le_trans ?_ (hcore S hS)
  exact le_inf inf_le_left
    ((inf_le_inf_left H (Subgroup.centralizer_le hSB)).trans (hH.1.2 S hS))

theorem hyperplaneMeetJoin_inf_le (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {H : Subgroup G} (hH : solvableSignalizerCompatible p 1 A θ H) :
    hyperplaneMeetJoin p q A θ ⊓ H ≤ primeCoreIn ({q}ᶜ : Set ℕ) H := by
  have hq' := prime_of_two_or_three hq
  refine le_primeCoreIn_of_commutators h.prime hq' (actor_ne h hq) h.elementary (large_sq h)
    hH.1.1 hH.2 (coprime_card h hH.1) inf_le_right
    ((coprime_hyperplaneMeetJoin h hq).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) ?_
  intro B hB
  have hfix := signalizer_compatible_hyperplane_fixed_le p 1 A B H θ hH.1
  have hle : ⁅hyperplaneMeetJoin p q A θ ⊓ H, H ⊓ Subgroup.centralizer (B : Set G)⁆ ≤
      primeComplement p q A θ := by
    rw [Subgroup.commutator_le]
    intro u hu c hc
    have hucore : u ∈ signalizerHyperplaneCore p 1 q A B θ :=
      hyperplaneMeetJoin_le_core h hB hu.1
    have hcN : c ∈ Subgroup.normalizer
        (signalizerHyperplaneCore p 1 q A B θ : Set G) :=
      hyperplaneCommonFixed_le_normalizer_core h hq (hfix hc)
    have hmem : u * (c * u⁻¹ * c⁻¹) ∈ signalizerHyperplaneCore p 1 q A B θ :=
      Subgroup.mul_mem _ hucore ((Subgroup.mem_normalizer_iff.mp hcN u⁻¹).mp
        (Subgroup.inv_mem _ hucore))
    have heq : ⁅u, c⁆ = u * (c * u⁻¹ * c⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [heq]
    exact core_le_primeComplement h hq hmem
  exact (primeComplement_spec h hq).2.1.of_dvd_right (Subgroup.card_dvd_of_le hle)

theorem primeCoreIn_thetaCentralizer_le (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {P : Subgroup G} (hP : IsPGroup q P) (hPCA : P ≤ signalizerCommonFixed p 1 A θ)
    (hP0 : P ≠ ⊥) :
    primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P) ≤ hyperplaneMeetJoin p q A θ := by
  have hq' := prime_of_two_or_three hq
  have hPcomp := compat_of_le_commonFixed hq' hP hPCA
  have hDcomp := compat_thetaCentralizer h hP0 hPcomp
  have hHcomp : solvableSignalizerCompatible p 1 A θ
      (primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P)) :=
    compat_of_le hDcomp (primeCoreIn_le _ _) (le_normalizer_primeCoreIn _ hDcomp.1.1)
  refine le_hyperplaneMeetJoin h hHcomp fun S hS => ?_
  have hLcomp := compat_value h hS
  have hPL : P ≤ θ S := hPCA.trans (commonFixed_le_value hS)
  have hLPcomp : signalizerCompatible p 1 A θ (θ S ⊓ Subgroup.centralizer (P : Set G)) :=
    signalizer_compatible_of_le p 1 A θ hLcomp.1 inf_le_left
      (normalizer_inf_of_le A _ _ hLcomp.1.1 (le_normalizer_centralizer hPcomp.1.1))
  have hLP_le_D : θ S ⊓ Subgroup.centralizer (P : Set G) ≤ thetaCentralizer p A θ P :=
    le_thetaCentralizer h hP0 hPcomp hLPcomp inf_le_right
  have hLPN : θ S ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer
      (primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P) : Set G) :=
    le_normalizer_primeCoreIn _ (hLP_le_D.trans Subgroup.le_normalizer)
  have hX_le : primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P) ⊓ θ S ≤
      θ S ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf inf_le_right (inf_le_left.trans ((primeCoreIn_le _ _).trans
      (thetaCentralizer_le_centralizer P)))
  have hXnorm : θ S ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer
      ((primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P) ⊓ θ S : Subgroup G) : Set G) :=
    normalizer_inf_of_le _ _ _ hLPN (inf_le_left.trans Subgroup.le_normalizer)
  have hXcop : Nat.Coprime q (Nat.card
      (primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ P) ⊓ θ S : Subgroup G)) :=
    (coprime_primeCoreIn hq' _).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  exact (le_primeCoreIn_compl hq' hX_le hXnorm hXcop).trans
    (primeCoreIn_inf_centralizer_le hq' (isSolvable_of_compat hLcomp) hPL hP)

theorem thetaCentralizer_le_normalizer (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {F : Subgroup G} (hF : IsElemAbelian q F) (hF2 : q ^ 2 ≤ Nat.card F)
    (hFCA : F ≤ signalizerCommonFixed p 1 A θ) :
    thetaCentralizer p A θ F ≤ Subgroup.normalizer (hyperplaneMeetJoin p q A θ : Set G) := by
  have hq' := prime_of_two_or_three hq
  have hKcop := coprime_hyperplaneMeetJoin h hq
  have hFK : F ≤ Subgroup.normalizer (hyperplaneMeetJoin p q A θ : Set G) :=
    hFCA.trans (commonFixed_le_normalizer_hyperplaneMeetJoin q)
  have hgen := elementary_abelian_centralizer_generation q 1 hq' F (hyperplaneMeetJoin p q A θ)
    hF hF2 hFK hKcop
  have hF0 : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hF2
    have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq'.one_lt
    omega
  have hFcomp := compat_of_le_commonFixed hq' (elementary_abelian_isPGroup q F hF) hFCA
  have hSF : ∀ S ∈ signalizerFunctorEk q 1 F, S ≤ F ∧ S ≠ ⊥ ∧ IsPGroup q S ∧
      S ≤ signalizerCommonFixed p 1 A θ := by
    intro S hS
    have hSq : IsPGroup q S := elementary_abelian_isPGroup q S
      (elementary_abelian_of_le q hF hS.1)
    refine ⟨hS.1, ?_, hSq, hS.1.trans hFCA⟩
    intro hbot
    have hcard := hS.2
    rw [hbot, Subgroup.card_bot] at hcard
    have h1 : 1 < q ^ 1 := by simpa using hq'.one_lt
    omega
  have hKeq : hyperplaneMeetJoin p q A θ = ⨆ S ∈ signalizerFunctorEk q 1 F,
      primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ S) := by
    apply le_antisymm
    · refine le_trans (le_of_eq hgen.symm) (iSup₂_le fun S hS => ?_)
      obtain ⟨-, hS0, hSq, hSCA⟩ := hSF S hS
      have hScomp := compat_of_le_commonFixed hq' hSq hSCA
      have hKC : signalizerCompatible p 1 A θ
          (hyperplaneMeetJoin p q A θ ⊓ Subgroup.centralizer (S : Set G)) :=
        signalizer_compatible_of_le p 1 A θ (compat_hyperplaneMeetJoin h hq).1 inf_le_left
          (normalizer_inf_of_le A _ _ (actor_le_normalizer_hyperplaneMeetJoin h q)
            (le_normalizer_centralizer hScomp.1.1))
      have h1 : hyperplaneMeetJoin p q A θ ⊓ Subgroup.centralizer (S : Set G) ≤
          thetaCentralizer p A θ S := le_thetaCentralizer h hS0 hScomp hKC inf_le_right
      have h2 := hyperplaneMeetJoin_inf_le h hq (compat_thetaCentralizer h hS0 hScomp)
      refine le_trans ?_ (le_iSup₂ (f := fun S (_ : S ∈ signalizerFunctorEk q 1 F) =>
        primeCoreIn ({q}ᶜ : Set ℕ) (thetaCentralizer p A θ S)) S hS)
      exact (le_inf inf_le_left h1).trans h2
    · exact iSup₂_le fun S hS => by
        obtain ⟨-, hS0, hSq, hSCA⟩ := hSF S hS
        exact primeCoreIn_thetaCentralizer_le h hq hSq hSCA hS0
  rw [hKeq]
  refine normalizer_biSup_of_le _ _ (fun S => primeCoreIn ({q}ᶜ : Set ℕ)
    (thetaCentralizer p A θ S)) fun S hS => ?_
  obtain ⟨hSle, hS0, hSq, hSCA⟩ := hSF S hS
  have hScomp := compat_of_le_commonFixed hq' hSq hSCA
  have hle := thetaCentralizer_mono h hS0 hScomp hF0 hFcomp hSle
  exact le_normalizer_primeCoreIn _ (hle.trans Subgroup.le_normalizer)

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
