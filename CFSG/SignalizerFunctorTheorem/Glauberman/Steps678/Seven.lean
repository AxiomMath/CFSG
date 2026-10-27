module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.KB

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

omit [Finite G] in
theorem mem_conjugateSubgroup {g x : G} {X : Subgroup G} :
    x ∈ conjugateSubgroup g X ↔ ∃ k ∈ X, g * k * g⁻¹ = x :=
  Iff.rfl

theorem mem_normalizer_of_conj_le {K : Subgroup G} {a : G} (h : conjugateSubgroup a K ≤ K) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  have hcard : Nat.card K ≤ Nat.card (conjugateSubgroup a K) := (conjugate_subgroup_card a K).ge
  have heq : conjugateSubgroup a K = K := Subgroup.eq_of_le_of_card_ge h hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem false_of_forall_le (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    (hK : hyperplaneMeetJoin p q A θ ≠ ⊥) {Q : Subgroup G}
    (hQN : IsSylowOf q Q (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ)))
    (hQA : A ≤ Subgroup.normalizer (Q : Set G)) (hQ0 : Q ≠ ⊥)
    (hSyl : ∀ S : Subgroup G, Maximal (signalizerPrimeCompatible p 1 q A θ) S →
      ¬ S ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ))
    (hU : ∀ U : Subgroup G, solvableSignalizerCompatible p 1 A θ U → Nat.Coprime q (Nat.card U) →
      Q ≤ Subgroup.normalizer (U : Set G) → U ≤ hyperplaneMeetJoin p q A θ) : False := by
  have hq' := prime_of_two_or_three hq
  have hKcomp := compat_hyperplaneMeetJoin h hq
  obtain ⟨hNcomp, -, hNle, hNmax⟩ := normalizerCompletion_spec h hK hKcomp
  have hQle : Q ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ) :=
    sylowOf_le hQN
  have hQq : IsPGroup q Q := sylowOf_isPGroup hQN
  have hQcomp : solvableSignalizerCompatible p 1 A θ Q :=
    compat_of_pGroup hq' hQq (signalizer_compatible_of_le p 1 A θ hNcomp.1 hQle hQA)
  obtain ⟨hU₁comp, hQU₁, hU₁le, hU₁max⟩ := normalizerCompletion_spec h hQ0 hQcomp
  obtain ⟨Q₁, hQQ₁, hQ₁syl, hQ₁A⟩ := exists_actor_sylow h hq' hU₁comp.1 hQq hQU₁ hQA
  have hQ₁q : IsPGroup q Q₁ := sylowOf_isPGroup hQ₁syl
  have hQ₁U₁ : Q₁ ≤ signalizerNormalizerCompletion p 1 A θ Q := sylowOf_le hQ₁syl
  have hQ₁comp : signalizerCompatible p 1 A θ Q₁ :=
    signalizer_compatible_of_le p 1 A θ hU₁comp.1 hQ₁U₁ hQ₁A
  have hQ₁N : Q₁ ≤ Subgroup.normalizer (Q : Set G) := hQ₁U₁.trans hU₁le
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subgroup G, K₀ = Subgroup.closure {x | ∃ y : G,
      (y ∈ Q₁ ∧ ∃ B ∈ Coprime.hyperplanes p A, y ∈ Subgroup.centralizer (B : Set G)) ∧
        ∃ k ∈ hyperplaneMeetJoin p q A θ, x = y * k * y⁻¹} := ⟨_, rfl⟩
  have hgen : ∀ y ∈ Q₁, (∃ B ∈ Coprime.hyperplanes p A, y ∈ Subgroup.centralizer (B : Set G)) →
      ∀ k ∈ hyperplaneMeetJoin p q A θ, y * k * y⁻¹ ∈ K₀ := by
    intro y hy hB k hk
    rw [hK₀]
    exact Subgroup.subset_closure ⟨y, ⟨hy, hB⟩, k, hk, rfl⟩
  have hK₀le : K₀ ≤ primeComplement p q A θ := by
    rw [hK₀]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨y, ⟨hyQ, B, hB, hyB⟩, k, hk, rfl⟩
    have hkcore : k ∈ signalizerHyperplaneCore p 1 q A B θ := hyperplaneMeetJoin_le_core h hB hk
    have hfix : y ∈ signalizerHyperplaneCommonFixed p 1 A B θ :=
      signalizer_compatible_hyperplane_fixed_le p 1 A B Q₁ θ hQ₁comp
        (show y ∈ Q₁ ⊓ Subgroup.centralizer (B : Set G) from ⟨hyQ, hyB⟩)
    have hyN : y ∈ Subgroup.normalizer (signalizerHyperplaneCore p 1 q A B θ : Set G) :=
      hyperplaneCommonFixed_le_normalizer_core h hq hfix
    have hmem : y * k * y⁻¹ ∈ signalizerHyperplaneCore p 1 q A B θ :=
      (Subgroup.mem_normalizer_iff.mp hyN k).mp hkcore
    exact core_le_primeComplement h hq hmem
  have hAK : A ≤ Subgroup.normalizer (hyperplaneMeetJoin p q A θ : Set G) :=
    actor_le_normalizer_hyperplaneMeetJoin h q
  have hAK₀ : A ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro a ha
    apply mem_normalizer_of_conj_le
    rw [hK₀]
    unfold conjugateSubgroup
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨y, ⟨hyQ, B, hB, hyB⟩, k, hk, rfl⟩, rfl⟩
    have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
      (elementary_abelian_le_centralizer p A B h.elementary hB.1).trans
        (Subgroup.centralizer_le_normalizer _)
    refine ⟨a * y * a⁻¹, ⟨?_, B, hB, ?_⟩, a * k * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hQ₁A ha) y).mp hyQ
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_centralizer hAB ha) y).mp hyB
    · exact (Subgroup.mem_normalizer_iff.mp (hAK ha) k).mp hk
    · change a * (y * k * y⁻¹) * a⁻¹ = a * y * a⁻¹ * (a * k * a⁻¹) * (a * y * a⁻¹)⁻¹
      group
  have hQK₀ : Q ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_le
    rw [hK₀]
    unfold conjugateSubgroup
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨y, ⟨hyQ, B, hB, hyB⟩, k, hk, rfl⟩, rfl⟩
    have hy' : y⁻¹ * g * y ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ₁N (Q₁.inv_mem hyQ)) g).mp hg
      simpa using this
    have hk' : (y⁻¹ * g * y) * k * (y⁻¹ * g * y)⁻¹ ∈ hyperplaneMeetJoin p q A θ :=
      (Subgroup.mem_normalizer_iff.mp (hNle (hQle hy')) k).mp hk
    refine ⟨y, ⟨hyQ, B, hB, hyB⟩, (y⁻¹ * g * y) * k * (y⁻¹ * g * y)⁻¹, hk', ?_⟩
    change g * (y * k * y⁻¹) * g⁻¹ = y * ((y⁻¹ * g * y) * k * (y⁻¹ * g * y)⁻¹) * y⁻¹
    group
  have hK₀comp : solvableSignalizerCompatible p 1 A θ K₀ :=
    compat_of_le (primeComplement_spec h hq).1 hK₀le hAK₀
  have hK₀cop : Nat.Coprime q (Nat.card K₀) :=
    (primeComplement_spec h hq).2.1.of_dvd_right (Subgroup.card_dvd_of_le hK₀le)
  have hK₀K : K₀ ≤ hyperplaneMeetJoin p q A θ := hU K₀ hK₀comp hK₀cop hQK₀
  have hQ₁B : ∀ B ∈ Coprime.hyperplanes p A, Q₁ ⊓ Subgroup.centralizer (B : Set G) ≤
      signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ) := by
    intro B hB
    have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
      (elementary_abelian_le_centralizer p A B h.elementary hB.1).trans
        (Subgroup.centralizer_le_normalizer _)
    refine hNmax _ (signalizer_compatible_of_le p 1 A θ hQ₁comp inf_le_left
      (normalizer_inf_of_le A _ _ hQ₁A (le_normalizer_centralizer hAB))) ?_
    intro y hy
    apply mem_normalizer_of_conj_le
    rintro _ ⟨k, hk, rfl⟩
    exact hK₀K (hgen y hy.1 ⟨B, hB, hy.2⟩ k hk)
  have hQ₁N' : Q₁ ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ) := by
    have hgenQ := generation_hyperplanes h.prime h.elementary (large_sq h) hQ₁comp.1
      (coprime_card h hQ₁comp)
    refine le_trans (le_of_eq hgenQ.symm) (iSup₂_le fun B hB => hQ₁B B hB)
  have hQQ : Q₁ = Q := sylowOf_eq_of_le hQN hQ₁q hQQ₁ hQ₁N'
  have hQmax : Maximal (signalizerPrimeCompatible p 1 q A θ) Q := by
    refine ⟨⟨hQcomp.1, hQq⟩, fun Q' hQ' hQQ' => ?_⟩
    have hAQ'N : A ≤ Subgroup.normalizer ((Q' ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) :
        Set G) := normalizer_inf_of_le A _ _ hQ'.1.1 (hQA.trans Subgroup.le_normalizer)
    have hQ''comp : signalizerCompatible p 1 A θ (Q' ⊓ Subgroup.normalizer (Q : Set G)) :=
      signalizer_compatible_of_le p 1 A θ hQ'.1 inf_le_left hAQ'N
    have hQ''U₁ : Q' ⊓ Subgroup.normalizer (Q : Set G) ≤
        signalizerNormalizerCompletion p 1 A θ Q := hU₁max _ hQ''comp inf_le_right
    have hQ''q : IsPGroup q (Q' ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) :=
      hQ'.2.to_le inf_le_left
    have hsyl : IsSylowOf q Q (signalizerNormalizerCompletion p 1 A θ Q) := by
      have h' := hQ₁syl
      rw [hQQ] at h'
      exact h'
    have hQ''eq : Q' ⊓ Subgroup.normalizer (Q : Set G) = Q :=
      sylowOf_eq_of_le hsyl hQ''q (le_inf hQQ' Subgroup.le_normalizer) hQ''U₁
    by_cases hQQ'eq : Q = Q'
    · exact le_of_eq hQQ'eq.symm
    · exact absurd hQ''eq.symm (ne_of_lt (lt_inf_normalizer_of_lt hq' hQ'.2 hQQ' hQQ'eq))
  exact hSyl Q hQmax hQle

theorem le_hyperplaneMeetJoin_of_two (h : Setting p A θ) (hK : hyperplaneMeetJoin p 2 A θ ≠ ⊥)
    {E Q U : Subgroup G} (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hECA : E ≤ signalizerCommonFixed p 1 A θ) (hEQ : E ≤ Q)
    (hQN : IsSylowOf 2 Q (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 2 A θ)))
    (hU : solvableSignalizerCompatible p 1 A θ U) (hUc : Nat.Coprime 2 (Nat.card U))
    (hQU : Q ≤ Subgroup.normalizer (U : Set G)) : U ≤ hyperplaneMeetJoin p 2 A θ := by
  have hq2 : (2 : ℕ) = 2 ∨ (2 : ℕ) = 3 := Or.inl rfl
  obtain ⟨hNcomp, -, -, hNmax⟩ := normalizerCompletion_spec h hK (compat_hyperplaneMeetJoin h hq2)
  have hEU : E ≤ Subgroup.normalizer (U : Set G) := hEQ.trans hQU
  have hgen := elementary_abelian_centralizer_generation 2 2 Nat.prime_two E U hE
    (by simp [hE8]) hEU hUc
  have hFprops : ∀ F ∈ signalizerFunctorEk 2 2 E,
      F ≤ signalizerCommonFixed p 1 A θ ∧ F ≠ ⊥ ∧ IsPGroup 2 F ∧ IsElemAbelian 2 F ∧
        2 ^ 2 ≤ Nat.card F := by
    intro F hF
    have hFe : IsElemAbelian 2 F := elementary_abelian_of_le 2 hE hF.1
    refine ⟨hF.1.trans hECA, ?_, elementary_abelian_isPGroup 2 F hFe, hFe, hF.2.ge⟩
    intro hbot
    have hcard := hF.2
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hUC : ∀ F ∈ signalizerFunctorEk 2 2 E, signalizerCompatible p 1 A θ
      (U ⊓ Subgroup.centralizer (F : Set G)) := by
    intro F hF
    obtain ⟨hFCA, -, hFp, -, -⟩ := hFprops F hF
    have hFcomp := compat_of_le_commonFixed Nat.prime_two hFp hFCA
    exact signalizer_compatible_of_le p 1 A θ hU.1 inf_le_left
      (normalizer_inf_of_le A _ _ hU.1.1 (le_normalizer_centralizer hFcomp.1.1))
  have hDN : ∀ F ∈ signalizerFunctorEk 2 2 E, thetaCentralizer p A θ F ≤
      signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 2 A θ) := by
    intro F hF
    obtain ⟨hFCA, hF0, hFp, hFe, hF2⟩ := hFprops F hF
    have hFcomp := compat_of_le_commonFixed Nat.prime_two hFp hFCA
    exact hNmax _ (compat_thetaCentralizer h hF0 hFcomp).1
      (thetaCentralizer_le_normalizer h hq2 hFe hF2 hFCA)
  have hUF : ∀ F ∈ signalizerFunctorEk 2 2 E, U ⊓ Subgroup.centralizer (F : Set G) ≤
      thetaCentralizer p A θ F := by
    intro F hF
    obtain ⟨hFCA, hF0, hFp, -, -⟩ := hFprops F hF
    exact le_thetaCentralizer h hF0 (compat_of_le_commonFixed Nat.prime_two hFp hFCA) (hUC F hF)
      inf_le_right
  have hUN : U ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 2 A θ) :=
    le_trans (le_of_eq hgen.symm) (iSup₂_le fun F hF => (hUF F hF).trans (hDN F hF))
  have hUO : U ≤ primeCoreIn ({2}ᶜ : Set ℕ)
      (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 2 A θ)) :=
    le_primeCoreIn_of_sylow_normalizes Nat.prime_two (isSolvable_of_compat hNcomp) hUN hUc hQN hQU
  refine le_trans (le_of_eq hgen.symm) (iSup₂_le fun F hF => ?_)
  obtain ⟨hFCA, hF0, hFp, -, -⟩ := hFprops F hF
  have h1 : U ⊓ Subgroup.centralizer (F : Set G) ≤
      primeCoreIn ({2}ᶜ : Set ℕ)
        (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 2 A θ)) ⊓
        thetaCentralizer p A θ F := le_inf (inf_le_left.trans hUO) (hUF F hF)
  exact (h1.trans (primeCoreIn_inf_le ({2}ᶜ : Set ℕ) (hDN F hF))).trans
    (primeCoreIn_thetaCentralizer_le h hq2 hFp hFCA hF0)

theorem inf_le_primeCoreIn_of_three (h : Setting p A θ) (hK : hyperplaneMeetJoin p 3 A θ ≠ ⊥)
    {E Q U S : Subgroup G} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hECA : E ≤ signalizerCommonFixed p 1 A θ)
    (hQN : IsSylowOf 3 Q (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 3 A θ)))
    (hQA : A ≤ Subgroup.normalizer (Q : Set G)) (hUc : Nat.Coprime 3 (Nat.card U))
    (hQU : Q ≤ Subgroup.normalizer (U : Set G)) (hS : S ∈ signalizerFunctorEk p 1 A) :
    U ⊓ θ S ≤ primeCoreIn ({3}ᶜ : Set ℕ) (θ S) := by
  have hq3 : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  obtain ⟨hNcomp, -, -, hNmax⟩ := normalizerCompletion_spec h hK (compat_hyperplaneMeetJoin h hq3)
  have hLcomp := compat_value h hS
  have hEp : IsPGroup 3 E := elementary_abelian_isPGroup 3 E hE
  have hE0 : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hE9
    norm_num at hE9
  have hEcomp := compat_of_le_commonFixed Nat.prime_three hEp hECA
  have hAE := actor_le_normalizer_of_le_commonFixed hECA
  have hEL : E ≤ θ S := hECA.trans (commonFixed_le_value hS)
  have hAY : A ≤ Subgroup.normalizer
      ((θ S ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
    normalizer_inf_of_le A _ _ hLcomp.1.1 (le_normalizer_centralizer hAE)
  have hYcomp : signalizerCompatible p 1 A θ (θ S ⊓ Subgroup.centralizer (E : Set G)) :=
    signalizer_compatible_of_le p 1 A θ hLcomp.1 inf_le_left hAY
  have hEY : E ≤ θ S ⊓ Subgroup.centralizer (E : Set G) :=
    le_inf hEL (elementary_abelian_le_centralizer 3 E E hE le_rfl)
  obtain ⟨S₀, hES₀, hS₀syl, hS₀A⟩ := exists_actor_sylow h Nat.prime_three hYcomp hEp hEY hAE
  have hS₀Y : S₀ ≤ θ S ⊓ Subgroup.centralizer (E : Set G) := sylowOf_le hS₀syl
  have hS₀q : IsPGroup 3 S₀ := sylowOf_isPGroup hS₀syl
  have hS₀comp : signalizerCompatible p 1 A θ S₀ :=
    signalizer_compatible_of_le p 1 A θ hYcomp hS₀Y hS₀A
  have hS₀N : S₀ ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 3 A θ) := by
    have hS₀D : S₀ ≤ thetaCentralizer p A θ E :=
      le_thetaCentralizer h hE0 hEcomp hS₀comp (hS₀Y.trans inf_le_right)
    exact hNmax _ hS₀comp
      (hS₀D.trans (thetaCentralizer_le_normalizer h hq3 hE (by simp [hE9]) hECA))
  obtain ⟨c, hc, hcS₀⟩ := exists_conj_le_sylow h Nat.prime_three hNcomp.1 hQN hQA hS₀q hS₀N hS₀A
  have hcCA : c ∈ signalizerCommonFixed p 1 A θ := inf_centralizer_le_commonFixed hNcomp.1 hc
  have hcL : c ∈ θ S := commonFixed_le_value hS hcCA
  have hS₀L : S₀ ≤ θ S := hS₀Y.trans inf_le_left
  have hTL : conjugateSubgroup c⁻¹ (U ⊓ θ S) ≤ θ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact (θ S).mul_mem ((θ S).mul_mem ((θ S).inv_mem hcL) hu.2)
      ((θ S).inv_mem ((θ S).inv_mem hcL))
  have hTc : Nat.Coprime 3 (Nat.card (conjugateSubgroup c⁻¹ (U ⊓ θ S))) := by
    rw [conjugate_subgroup_card]
    exact hUc.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hS₀T : S₀ ≤ Subgroup.normalizer (conjugateSubgroup c⁻¹ (U ⊓ θ S) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs t ht
    obtain ⟨u, hu, rfl⟩ := mem_conjugateSubgroup.mp ht
    have hs' : c * s * c⁻¹ ∈ Q := hcS₀ (mem_conjugateSubgroup.mpr ⟨s, hs, rfl⟩)
    have hsL : c * s * c⁻¹ ∈ θ S :=
      (θ S).mul_mem ((θ S).mul_mem hcL (hS₀L hs)) ((θ S).inv_mem hcL)
    have hu' : (c * s * c⁻¹) * u * (c * s * c⁻¹)⁻¹ ∈ U ⊓ θ S :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hQU hs') u).mp hu.1,
        (θ S).mul_mem ((θ S).mul_mem hsL hu.2) ((θ S).inv_mem hsL)⟩
    refine mem_conjugateSubgroup.mpr ⟨(c * s * c⁻¹) * u * (c * s * c⁻¹)⁻¹, hu', ?_⟩
    group
  have hz : ∀ V : Subgroup G, V ≤ θ S → IsPGroup 3 V →
      V ≤ Subgroup.centralizer (S₀ : Set G) → V ≤ S₀ := by
    intro V hVL hVq hVC
    have hVY : V ≤ θ S ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf hVL (hVC.trans (Subgroup.centralizer_le hES₀))
    have hVN : V ≤ Subgroup.normalizer (S₀ : Set G) :=
      hVC.trans (Subgroup.centralizer_le_normalizer _)
    have hsupp : primeSupported {3} (Nat.card (S₀ ⊔ V : Subgroup G)) :=
      prime_supported_sup_of_normalizing {3} S₀ V hVN
        ((prime_supported_singleton_iff_pgroup 3 Nat.prime_three _).mpr hS₀q)
        ((prime_supported_singleton_iff_pgroup 3 Nat.prime_three _).mpr hVq)
    have hWq : IsPGroup 3 (S₀ ⊔ V : Subgroup G) :=
      (prime_supported_singleton_iff_pgroup 3 Nat.prime_three _).mp hsupp
    have heq := sylowOf_eq_of_le hS₀syl hWq le_sup_left (sup_le hS₀Y hVY)
    exact le_trans le_sup_right (le_of_eq heq)
  have hTO := le_primeCoreIn_of_thompson Nat.prime_three (by norm_num) (isSolvable_of_compat hLcomp)
    hS₀L hS₀q hTL hTc hS₀T hz
  intro u hu
  have ht : c⁻¹ * u * c⁻¹⁻¹ ∈ primeCoreIn ({3}ᶜ : Set ℕ) (θ S) :=
    hTO (mem_conjugateSubgroup.mpr ⟨u, hu, rfl⟩)
  have hcN : c ∈ Subgroup.normalizer (primeCoreIn ({3}ᶜ : Set ℕ) (θ S) : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer hcL
  have hmem := (Subgroup.mem_normalizer_iff.mp hcN _).mp ht
  have heq : c * (c⁻¹ * u * c⁻¹⁻¹) * c⁻¹ = u := by group
  rw [heq] at hmem
  exact hmem

theorem le_hyperplaneMeetJoin_of_three (h : Setting p A θ) (hK : hyperplaneMeetJoin p 3 A θ ≠ ⊥)
    {E Q U : Subgroup G} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hECA : E ≤ signalizerCommonFixed p 1 A θ)
    (hQN : IsSylowOf 3 Q (signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p 3 A θ)))
    (hQA : A ≤ Subgroup.normalizer (Q : Set G))
    (hU : solvableSignalizerCompatible p 1 A θ U) (hUc : Nat.Coprime 3 (Nat.card U))
    (hQU : Q ≤ Subgroup.normalizer (U : Set G)) : U ≤ hyperplaneMeetJoin p 3 A θ :=
  le_hyperplaneMeetJoin h hU fun _ hS =>
    inf_le_primeCoreIn_of_three h hK hE hE9 hECA hQN hQA hUc hQU hS

theorem hyperplaneMeetJoin_eq_bot (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    hyperplaneMeetJoin p q A θ = ⊥ := by
  by_contra hK
  obtain ⟨hNcomp, -, -, hNmax⟩ :=
    normalizerCompletion_spec h hK (compat_hyperplaneMeetJoin h hq)
  have hCAN : signalizerCommonFixed p 1 A θ ≤
      signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ) :=
    hNmax _ (compat_commonFixed h).1 (commonFixed_le_normalizer_hyperplaneMeetJoin q)
  have hSyl : ∀ S : Subgroup G, Maximal (signalizerPrimeCompatible p 1 q A θ) S →
      ¬ S ≤ signalizerNormalizerCompletion p 1 A θ (hyperplaneMeetJoin p q A θ) := by
    intro S hS hSN
    obtain ⟨M, hM, hNM⟩ := exists_maximal_ge hNcomp
    obtain ⟨Q, -, -, -, -, hnot⟩ := h.exists_not_thompsonFactorizable hq hS hM (hSN.trans hNM)
    exact hnot (inf_le_right.trans (hCAN.trans hNM))
  obtain ⟨hnine, hneight⟩ := h.exists_elemAbelian_nine_eight
  rcases hq with rfl | rfl
  · obtain ⟨E, hECA, hE2, hE8⟩ := hneight
    have hEp := elementary_abelian_isPGroup 2 E hE2
    obtain ⟨Q, hEQ, hQN, hQA⟩ := exists_actor_sylow h Nat.prime_two hNcomp.1 hEp
      (hECA.trans hCAN) (actor_le_normalizer_of_le_commonFixed hECA)
    have hE0 : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hE8
      norm_num at hE8
    exact false_of_forall_le h (Or.inl rfl) hK hQN hQA (fun hb => hE0 (le_bot_iff.mp (hb ▸ hEQ)))
      hSyl fun U hU hUc hQU => le_hyperplaneMeetJoin_of_two h hK hE2 hE8 hECA hEQ hQN hU hUc hQU
  · obtain ⟨E, hECA, hE3, hE9⟩ := hnine
    have hEp := elementary_abelian_isPGroup 3 E hE3
    obtain ⟨Q, hEQ, hQN, hQA⟩ := exists_actor_sylow h Nat.prime_three hNcomp.1 hEp
      (hECA.trans hCAN) (actor_le_normalizer_of_le_commonFixed hECA)
    have hE0 : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hE9
      norm_num at hE9
    exact false_of_forall_le h (Or.inr rfl) hK hQN hQA (fun hb => hE0 (le_bot_iff.mp (hb ▸ hEQ)))
      hSyl fun U hU hUc hQU => le_hyperplaneMeetJoin_of_three h hK hE3 hE9 hECA hQN hQA hU hUc hQU

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
