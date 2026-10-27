module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofTwin
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesSetup
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsL
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Case1487 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (M : Subgroup G)
    [(ker148 A M).Normal] : Prop :=
  ∃ (a₁ a₂ : G) (L₁ L₂ J₁ J₂ : Subgroup G) (p₁ f₁ e₁ p₂ f₂ e₂ : ℕ)
      (_ : Fact p₁.Prime) (_ : Fact p₂.Prime),
    Subgroup.zpowers a₁ ∈ omegaA A ∧ Subgroup.zpowers a₂ ∈ omegaA A ∧
    L₁ ∈ lA A a₁ ∧ L₂ ∈ lA A a₂ ∧ J₁ ≤ L₁ ⊓ M ∧ J₂ ≤ L₂ ⊓ M ∧
    img148 A M J₁ ⊔ img148 A M J₂ = img148 A M (deltaZero A LB M) ∧
    img148 A M J₁ ⊓ img148 A M J₂ = ⊥ ∧ ⁅img148 A M J₁, img148 A M J₂⁆ = ⊥ ∧
    1 ≤ f₁ ∧ 1 ≤ e₁ ∧ 1 ≤ f₂ ∧ 1 ≤ e₂ ∧
    IsZ3PGLThreeAt ↥(img148 A M (J₁ ⊔ A)) p₁ f₁ ∧
    IsZ3PGLThreeAt ↥(img148 A M (J₂ ⊔ A)) p₂ f₂ ∧
    Sec4.IsoLThreePi (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁) p₁ (f₁ * e₁) ∧
    Sec4.IsoLThreePi (↥L₂ ⧸ aschbacherSolvableCore 3 ↥L₂) p₂ (f₂ * e₂)

@[expose] noncomputable def Claim153TwinCase7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ¬ M ≤ Subgroup.normalizer (Y : Set G) →
        ∀ hAN : A ≤ Subgroup.normalizer (M : Set G),
          letI := ker148_normal hAN
          ¬ Case1487 A (lB A) M

namespace Proof153Twin2

theorem not_sq_dvd_of_dvd_1080 {N : ℕ} (hN : N ∣ 1080) {p : ℕ} (hp : p.Prime)
    (hp6 : Nat.Coprime 6 p) : ¬ p ^ 2 ∣ N := by
  intro hd
  have h1 : p ∣ 1080 := (dvd_pow_self p two_ne_zero).trans (hd.trans hN)
  have h2 : Nat.Coprime p 2 := (Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 6) hp6).symm
  have h3 : Nat.Coprime p 3 := (Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) hp6).symm
  have h5 : p ∣ 5 := by
    have e : (1080 : ℕ) = 2 ^ 3 * (3 ^ 3 * 5) := by norm_num
    rw [e] at h1
    have h1' := (Nat.Coprime.pow_right 3 h2).dvd_of_dvd_mul_left h1
    exact (Nat.Coprime.pow_right 3 h3).dvd_of_dvd_mul_left h1'
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
  subst hp5
  have := (hd.trans hN)
  norm_num at this

theorem types_of_quot_equiv {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    (hY4 : Y ∈ scriptY4 A LB) (hE : ¬ HasFaithfulE9 Y) {U : Type*} [Group U] [Finite U]
    (eY : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* U)
    (hU : Nonempty (U ≃* alternatingGroup (Fin 5)) ∨
      ∃ g : U →* alternatingGroup (Fin 6), Function.Surjective g ∧
        g.ker = Subgroup.center U ∧ Nat.card (Subgroup.center U) ∣ 3) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY4.2.2.2
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have hcardU : Nat.card U ∣ 1080 := by
    rcases hU with ⟨⟨φ⟩⟩ | ⟨g, hg, hker, h3⟩
    · rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      norm_num
    · have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center U)
      rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv,
        card_alternatingGroup_six, hker] at hc
      rw [hc]
      exact Nat.mul_dvd_mul_left 360 h3
  have hcore : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 =>
      not_sq_dvd_of_dvd_1080 (by rw [Nat.card_congr eY.toEquiv]; exact hcardU) hp hp6
  set e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* U :=
    (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans eY with he
  rcases hU with ⟨⟨φ⟩⟩ | ⟨g, hg, hker, h3⟩
  · exact Or.inl ⟨e.trans φ⟩
  · set g' := g.comp e.toMonoidHom with hg'
    have hg's : Function.Surjective g' := hg.comp e.surjective
    have hZ : Subgroup.center U = (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)).map e.toMonoidHom :=
      (Subgroup.map_center_eq e).symm
    have hker' : g'.ker = Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      rw [hg', ← MonoidHom.comap_ker, hker, hZ,
        Subgroup.comap_map_eq_self_of_injective e.injective]
    have hcardZ : Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) =
        Nat.card (Subgroup.center U) := by
      rw [hZ, Subgroup.card_map_of_injective e.injective]
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
    ·
      exfalso
      have hbot : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ (hcardZ.trans h1)
      have hinj : Function.Injective g' := by
        rw [← MonoidHom.ker_eq_bot_iff, hker', hbot]
      exact hE (hasFaithfulE9_of_mulEquiv hq (MulEquiv.ofBijective g' ⟨hinj, hg's⟩)
        (alternatingGroup.center_eq_bot (by simp)) exists_e9_alternatingGroup_six)
    · right
      exact ⟨hcardZ.trans h3', ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective g' hg's)⟩⟩

theorem pair_map {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') {U V : Subgroup T}
    (hU : U.IsSubnormal) (hV : V.IsSubnormal) (hUp : Group.IsPerfect U)
    (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) :
    (U.map e.toMonoidHom).IsSubnormal ∧ (V.map e.toMonoidHom).IsSubnormal ∧
      Group.IsPerfect (U.map e.toMonoidHom) ∧ Group.IsPerfect (V.map e.toMonoidHom) ∧
      U.map e.toMonoidHom ≠ ⊥ ∧ V.map e.toMonoidHom ≠ ⊥ ∧
      ⁅U.map e.toMonoidHom, V.map e.toMonoidHom⁆ = ⊥ ∧
      Nat.card (U.map e.toMonoidHom) = Nat.card U ∧
      Nat.card (V.map e.toMonoidHom) = Nat.card V := by
  refine ⟨hU.map e.surjective, hV.map e.surjective, Group.IsPerfect.map _,
    Group.IsPerfect.map _, ?_, ?_, ?_, Subgroup.card_map_of_injective e.injective,
    Subgroup.card_map_of_injective e.injective⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rw [← Subgroup.map_commutator, hUV, Subgroup.map_bot]

end Proof153Twin2

open Proof153Twin2

theorem claim153TwinTypes_of
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h152 : Item152R) (h7 : Claim153TwinCase7) :
    Claim153TwinTypes := by
  intro G _ _ A c L hR Y hY hE M hM hMY
  have h := hR.toSec14Std
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hAN : A ≤ Subgroup.normalizer (M : Set G) := hM2.1.2
  let := ker148_normal hAN
  obtain ⟨U, V, hU, hV, hUp, hVp, hU1, hV1, hUV, hcard, ⟨eY⟩⟩ :=
    exists_pair_of_twin h (h149 G A c L h) (h152 G A c L hR) hY hM hMY hAN
  refine types_of_quot_equiv hY.prop.1 hE eY ?_
  have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA5Z : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hid : ∀ (X : Type) [Group X], (MonoidHom.id X).ker ≤ Subgroup.center X := fun X _ => by
    rw [MonoidHom.ker_id]
    exact bot_le
  rcases (h148 G A c L hR M hM2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    exfalso
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    apply hU1
    rw [eq_bot_iff]
    intro x _
    have hx : (x : ↥(M ⊔ A) ⧸ ker148 A M) ∈ (⊥ : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) := by
      rw [← hD]
      exact x.2
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp hx))
  ·
    exfalso
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact false_of_mulEquiv_quasisimple (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ
        hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · exact false_of_isTripleCover h6 hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, -, hU6, hV6⟩ |
        ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hU6, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · exfalso
      have := CFSG.Sporadic.ON.isSimpleGroup_ON
      exact false_of_isTripleCover hON hU hUp hVp hU1 hV1 hUV
    ·
      right
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      obtain ⟨hψ₂, hk₂⟩ := tripleCover_cover hV6.2.some
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id hψ₂ hk₂ (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, -⟩ | ⟨hUV₀, -⟩
      · exact exists_surjective_of_le_tripleCover hU6 hU hUp hU1 hUU
      · exact exists_surjective_of_le_tripleCover hV6 hU hUp hU1 hUV₀
    ·
      exfalso
      have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact Subgroup.commutator_le_inf U₀ V₀
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      have h360 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ U₀ → 360 ∣ Nat.card W := by
        intro W hW hWp hW1 hWU
        obtain ⟨g, hg, -, -⟩ := exists_surjective_of_le_tripleCover hU6 hW hWp hW1 hWU
        have := Subgroup.card_dvd_of_surjective hg
        rwa [card_alternatingGroup_six] at this
      have h60 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ V₀ → Nat.card W = 60 := by
        intro W hW hWp hW1 hWV
        rw [eq_of_le_simple_factor hA5Z eV hW hWp hW1 hWV, Nat.card_congr eV.toEquiv,
          card_alternatingGroup_five]
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id (ψ₂ := MonoidHom.id (alternatingGroup (Fin 5)))
          Function.surjective_id (hid _) (φ₂ := eV.symm.toMonoidHom) eV.symm.surjective hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, hVV⟩ | ⟨hUV₀, hVU⟩
      · have h1 := h360 hU hUp hU1 hUU
        rw [hcard, h60 hV hVp hV1 hVV] at h1
        norm_num at h1
      · have h1 := h360 hV hVp hV1 hVU
        rw [← hcard, h60 hU hUp hU1 hUV₀] at h1
        norm_num at h1
    ·
      left
      obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', -, -⟩ :=
        pair_map φ hU hV hUp hVp hU1 hV1 hUV
      rcases pair_prod hA5Z hA5Z hU' hV' hUp' hVp' hU1' hV1' hUV' with
        ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
    ·
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
    ·
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    exfalso
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 (3 * n))
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    exfalso
    obtain ⟨⟨φ⟩, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hJZ : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
    obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', hcU, hcV⟩ :=
      pair_map φ hU hV hUp hVp hU1 hV1 hUV
    rcases pair_prod hA5Z hJZ hU' hV' hUp' hVp' hU1' hV1' hUV' with
      ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩ | ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
  ·
    exact (h7 G A c L hR Y hY hE M hM hMY hAN h7').elim

end CFSG.RankThree.PartTwo.Sec15
