module

public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
import CFSG.LocalAnalysis.SteinbergBMEvenExceptionalFixedTools
import CFSG.LocalAnalysis.SteinbergCATrialityOddInner

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem two_pow_mul_odd_inj {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have key : ∀ {a b u v : ℕ}, Odd u → Odd v → 2 ^ a * u = 2 ^ b * v → a ≤ b := by
    intro a b u v _ hv h
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 2 ^ (b + 1) ∣ 2 ^ b * v := by
      rw [← h]
      exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hlt) u
    rw [pow_succ] at h1
    have h2 : 2 ∣ v := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    exact (Nat.not_even_iff_odd.2 hv) (even_iff_two_dvd.2 h2)
  have hab : a = b := le_antisymm (key hu hv h) (key hv hu h.symm)
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem pow_six_sub_one (r : ℕ) : r ^ 6 - 1 = (r ^ 2 - 1) * (r ^ 4 + r ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have h2 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ hr
  zify [h1, h2]
  ring

theorem card_SL2_ne_triality_order {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠
      (p ^ e) ^ 12 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 6 - 1) *
        ((p ^ e) ^ 8 + (p ^ e) ^ 4 + 1) := by
  intro h
  set r := p ^ e with hr
  have hr2 : 2 ≤ r := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  have hA : 1 ≤ r ^ 2 - 1 := by
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have hB : 1 ≤ r ^ 6 - 1 := by
    have : 2 ≤ r ^ 6 := le_trans hr2 (Nat.le_self_pow (by norm_num) r)
    omega
  have hC : 1 ≤ r ^ 8 + r ^ 4 + 1 := by omega
  rcases hp.eq_two_or_odd' with rfl | hodd
  ·
    have hr12 : r ^ 12 = 2 ^ (12 * e) := by rw [hr, ← pow_mul, mul_comm]
    have hreven : Even r := by
      rw [hr]
      exact (Nat.even_pow' (by omega)).2 even_two
    have hoddA : Odd (r ^ 2 - 1) := by
      have : Even (r ^ 2) := (Nat.even_pow' (by norm_num)).2 hreven
      exact Nat.Even.sub_odd (by omega) this odd_one
    have hoddB : Odd (r ^ 6 - 1) := by
      have : Even (r ^ 6) := (Nat.even_pow' (by norm_num)).2 hreven
      exact Nat.Even.sub_odd (by omega) this odd_one
    have hoddC : Odd (r ^ 8 + r ^ 4 + 1) := by
      have h8 : Even (r ^ 8) := (Nat.even_pow' (by norm_num)).2 hreven
      have h4 : Even (r ^ 4) := (Nat.even_pow' (by norm_num)).2 hreven
      exact (h8.add h4).add_odd odd_one
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pow_zero, one_pow, Nat.sub_self, mul_zero] at h
      have : 0 < r ^ 12 * (r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1) := by positivity
      omega
    have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hoddq : Odd ((2 ^ n) ^ 2 - 1) := by
      have : Even ((2 ^ n) ^ 2) := (Nat.even_pow' (by norm_num)).2
        ((Nat.even_pow' (by omega)).2 even_two)
      exact Nat.Even.sub_odd (by nlinarith) this odd_one
    have h' : 2 ^ n * ((2 ^ n) ^ 2 - 1) =
        2 ^ (12 * e) * ((r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1)) := by
      rw [h, ← hr12]
      ring
    obtain ⟨hn12, hX⟩ := two_pow_mul_odd_inj hoddq ((hoddA.mul hoddB).mul hoddC) h'
    have hq12 : 2 ^ n = r ^ 12 := by rw [hn12, hr12]
    rw [hq12, ← pow_mul] at hX
    have hb1 : r ^ 2 - 1 ≤ r ^ 2 := Nat.sub_le _ _
    have hb2 : r ^ 6 - 1 ≤ r ^ 6 := Nat.sub_le _ _
    have hb3 : r ^ 8 + r ^ 4 + 1 ≤ 3 * r ^ 8 := by
      have h48 : r ^ 4 ≤ r ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h18 : 1 ≤ r ^ 8 := Nat.one_le_pow _ _ (by omega)
      omega
    have hprod : (r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1) ≤ 3 * r ^ 16 := by
      calc (r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1) ≤ r ^ 2 * r ^ 6 * (3 * r ^ 8) :=
            Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2) hb3
        _ = 3 * r ^ 16 := by ring
    have hbig : 4 * r ^ 16 ≤ r ^ 24 - 1 := by
      have h8 : 256 ≤ r ^ 8 := by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ r ^ 8 := Nat.pow_le_pow_left hr2 8
      have h16 : 1 ≤ r ^ 16 := Nat.one_le_pow _ _ (by omega)
      have : r ^ 24 = r ^ 8 * r ^ 16 := by ring
      rw [this]
      have : 256 * r ^ 16 ≤ r ^ 8 * r ^ 16 := Nat.mul_le_mul_right _ h8
      omega
    have h16 : 1 ≤ r ^ 16 := Nat.one_le_pow _ _ (by omega)
    rw [show 12 * 2 = 24 from rfl] at hX
    omega
  ·
    have hroddr : Odd r := by rw [hr]; exact hodd.pow
    set q := 2 ^ n with hq
    have hcop : ∀ m : ℕ, Odd m → Nat.Coprime q m := fun m hm =>
      Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hm)
    have hoddD : Odd (r ^ 4 + r ^ 2 + 1) := by
      have h4 : Odd (r ^ 4) := hroddr.pow
      have h2 : Odd (r ^ 2) := hroddr.pow
      exact (h4.add_odd h2).add_odd odd_one
    have hoddC : Odd (r ^ 8 + r ^ 4 + 1) := by
      have h8 : Odd (r ^ 8) := hroddr.pow
      have h4 : Odd (r ^ 4) := hroddr.pow
      exact (h8.add_odd h4).add_odd odd_one
    have hdvd : q ∣ (r ^ 2 - 1) * (r ^ 2 - 1) *
        (r ^ 12 * (r ^ 4 + r ^ 2 + 1) * (r ^ 8 + r ^ 4 + 1)) := by
      refine ⟨(q ^ 2 - 1), ?_⟩
      rw [h, pow_six_sub_one]
      ring
    have hdvd' : q ∣ (r ^ 2 - 1) * (r ^ 2 - 1) :=
      (hcop _ ((hroddr.pow.mul hoddD).mul hoddC)).dvd_of_dvd_mul_right hdvd
    have hqle : q ≤ (r ^ 2 - 1) * (r ^ 2 - 1) := Nat.le_of_dvd (by positivity) hdvd'
    have hqlt : q < r ^ 4 := by
      have : (r ^ 2 - 1) * (r ^ 2 - 1) < r ^ 2 * r ^ 2 :=
        Nat.mul_lt_mul'' (by omega) (by omega)
      calc q ≤ (r ^ 2 - 1) * (r ^ 2 - 1) := hqle
        _ < r ^ 2 * r ^ 2 := this
        _ = r ^ 4 := by ring
    have hlhs : q * (q ^ 2 - 1) < r ^ 12 := by
      have h1 : q * (q ^ 2 - 1) ≤ q ^ 3 := by
        calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = q ^ 3 := by ring
      have h2 : q ^ 3 < (r ^ 4) ^ 3 := Nat.pow_lt_pow_left hqlt (by norm_num)
      calc q * (q ^ 2 - 1) ≤ q ^ 3 := h1
        _ < (r ^ 4) ^ 3 := h2
        _ = r ^ 12 := by ring
    have hrhs : r ^ 12 ≤ r ^ 12 * (r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1) := by
      calc r ^ 12 = r ^ 12 * 1 * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hA) hB) hC
    omega


section NormalForm

variable {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (F : Type) [Field F] [Finite F]
  (hF : Nat.card F = (p ^ f) ^ 3) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))

include hp hf hF hσ in
theorem triality_normal_form :
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom),
      ∃ g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom, ∃ δ : F ≃+* F,
        α = MulAut.conj g * fieldActor σ δ) ∧
    (∀ (g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (δ : F ≃+* F),
      MulAut.conj g * fieldActor σ δ ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 F
        σ.toRingHom →* MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)).range → δ = 1) ∧
    (∀ (g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (δ : F ≃+* F),
      (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 →
        δ = 1 ∨ (Even f ∧ ∀ c, δ c = c ^ (p ^ (3 * f / 2)))) ∧
    Subgroup.center (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = ⊥ ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 F σ.toRingHom) ≃*
      graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := by
  have key : ∀ (Θ : MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) →* (F ≃+* F)),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) →
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)).range →
      (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom), α ^ 2 = 1 →
        Θ α = 1 ∨ (Even f ∧ ∀ c, Θ α c = c ^ (p ^ (3 * f / 2)))) →
      (∀ (g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (δ : F ≃+* F),
        MulAut.conj g * fieldActor σ δ ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 F
          σ.toRingHom →* MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)).range →
            δ = 1) ∧
      ∀ (g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (δ : F ≃+* F),
        (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 →
          δ = 1 ∨ (Even f ∧ ∀ c, δ c = c ^ (p ^ (3 * f / 2))) := by
    intro Θ hΘ hker hinv
    refine ⟨fun g δ hmem => ?_, fun g δ h2 => ?_⟩
    · rw [← hker, MonoidHom.mem_ker, hΘ _ g δ rfl] at hmem
      exact hmem
    · rw [← hΘ _ g δ rfl]
      exact hinv _ h2
  rcases hp.eq_two_or_odd' with rfl | hodd
  · obtain ⟨-, hNF, ⟨Θ, hΘ, -, hker, hinv⟩, -, -, -, hZ, hDCQ⟩ :=
      even_triality_exact_automorphism_normal_form hf F hF σ hσ
    exact ⟨fun α => (hNF α).exists.elim fun gδ h => ⟨gδ.1, gδ.2, h⟩,
      (key Θ hΘ hker hinv).1, (key Θ hΘ hker hinv).2, hZ, hDCQ⟩
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) even_two
    obtain ⟨-, hNF, ⟨Θ, hΘ, -, hker, hinv⟩, -, -, -, hZ, hDCQ⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf F hF σ hσ
    exact ⟨fun α => (hNF α).exists.elim fun gδ h => ⟨gδ.1, gδ.2, h⟩,
      (key Θ hΘ hker hinv).1, (key Θ hΘ hker hinv).2, hZ, hDCQ⟩

end NormalForm

theorem triality_even_inner_fixed_no_simple
    {f : ℕ} (hf : 1 ≤ f) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ f) ^ 3) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (t : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (ht : orderOf (MulAut.conj t) = 2)
    (S : Subgroup ((MulAut.conj t).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) : False := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 3 * f) (by rw [hF, ← pow_mul, mul_comm])
  have hσ3 : σ ^ TwistTag.D4.order = 1 :=
    RingEquiv.ext fun c => ringEquiv_cube_apply_eq hF hσ c
  exact CFSG.LocalAnalysis.SteinbergBM.not_normal_simple_inner_of_rootWeightDatum
    (RootWeightDatum.fixed TwistTag.D4 σ hσ3) (exceptional_fixed_center_trivial TwistTag.D4 F σ)
    t ht S hSn hSs hSnab

theorem triality_field_coset_fixed_card
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (F : Type)
    [Field F] [Finite F] (hF : Nat.card F = p ^ (6 * e)) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ (2 * e))) (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ (3 * e)))
    (α ψ : MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))
    (hψ : ψ * α * ψ⁻¹ = fieldActor σ δ)
    (S : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) :
    Nat.card S = (p ^ e) ^ 12 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 6 - 1) *
      ((p ^ e) ^ 8 + (p ^ e) ^ 4 + 1) := by
  obtain ⟨-, -, hcard₀, hres, -, -, hfixJ, hJs, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      (m := 2) hp he le_rfl
      (by norm_num) F (by rw [hF]; ring_nf) σ (fun c => by rw [hσ]; ring_nf) δ hδ
  set E := (fieldActor σ δ).toMonoidHom.eqLocus
    (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) with hE
  have hmap := CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_conj ψ α
  rw [hψ] at hmap
  let eα : α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) ≃* E :=
    ((α.toMonoidHom.eqLocus (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))
      ).equivMapOfInjective _ ψ.injective).trans (MulEquiv.subgroupCongr hmap)
  let eJ : E ≃* trialityFieldImage σ δ :=
    (E.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype_injective
      ).trans (MulEquiv.subgroupCongr hfixJ)
  have := hJs
  have : IsSimpleGroup E := eJ.isSimpleGroup
  have hSE : S.map eα.toMonoidHom = ⊤ := by
    have hN : (S.map eα.toMonoidHom).Normal := hSn.map _ eα.surjective
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : S)
      apply hx
      have h1 : eα x ∈ S.map eα.toMonoidHom := ⟨x, x.2, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact Subtype.ext (eα.injective (h1.trans (map_one eα).symm))
    · exact h
  have hcardS : Nat.card S = Nat.card (trialityFieldImage σ δ) := by
    rw [← Subgroup.card_map_of_injective (f := eα.toMonoidHom) eα.injective, hSE,
      Subgroup.card_top,
      Nat.card_congr eJ.toEquiv]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((p ^ e) ^ 2) :=
    fun c => Subtype.ext (by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hres, hσ, SubmonoidClass.coe_pow,
        ← pow_mul, mul_comm 2 e])
  obtain ⟨hJcard, -, -⟩ := triality_both_orientations_exact_finite_order p e hp he
    (fixSubfield δ) (by rw [hcard₀, ← pow_mul, mul_comm]) 2 (Or.inr rfl)
    (fixSubfieldRestrict σ δ).toRingHom hσ₀
  rw [hcardS, trialityFieldImage, Subgroup.card_map_of_injective (baseChangeGL_injective _),
    hJcard]

theorem triality_involution_fixed_groups_have_no_normal_even_SL2
    {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 3)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ n)
    (S : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    IsEmpty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  refine ⟨fun eS => ?_⟩
  have hcardS : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  obtain ⟨hNF, hinner, hinv, hZ, -⟩ := triality_normal_form hp hf F hF σ hσ
  obtain ⟨g, δ, hα⟩ := hNF α
  by_cases hδ : δ = 1
  ·
    have hαg : α = MulAut.conj g := by rw [hα, hδ, fieldActor_one, mul_one]
    subst hαg
    have hg1 : g ≠ 1 := fun h => hα1 (by rw [h, map_one])
    have hg2 : g * g = 1 := mulAut_conj_injective_of_center_eq_bot hZ (by
      rw [map_mul, ← sq, hα2, map_one])
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact triality_even_inner_fixed_no_simple hf F hF σ hσ g (orderOf_eq_prime hα2 hα1) S hSn
        hSs hSnab
    · have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 hodd) even_two
      refine triality_odd_inner_fixed_no_even_simple hp hp2 hf F hF σ hσ g hg1 hg2 S hSn hSs
        hSnab ?_
      rw [hcardS]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  ·
    obtain ⟨⟨e, rfl⟩, hδc⟩ := (hinv g δ (hα ▸ hα2)).resolve_left hδ
    have he : 1 ≤ e := by omega
    have h3e : 3 * (e + e) / 2 = 3 * e := by omega
    rw [h3e] at hδc
    have hF6 : Nat.card F = p ^ (6 * e) := by
      rw [hF, ← pow_mul]
      ring_nf
    have hσ2 : ∀ c, σ c = c ^ (p ^ (2 * e)) := fun c => by
      rw [hσ]
      ring_nf
    obtain ⟨δ', ψ, hδ', hψ⟩ : ∃ (δ' : F ≃+* F) (ψ : MulAut (graphFixedRootGroup TwistTag.D4 F
        σ.toRingHom)), (∀ c, δ' c = c ^ (p ^ (3 * e))) ∧ ψ * α * ψ⁻¹ = fieldActor σ δ' := by
      rcases hp.eq_two_or_odd' with rfl | hodd
      · have hαo : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
            (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := fun hmem =>
          hδ (hinner g δ (hα ▸ hmem))
        obtain ⟨-, δ', hδ'c, -, ψ, hψ, -⟩ :=
          even_triality_outer_involutions_canonical_field hf F hF σ hσ α hα2 hαo
        refine ⟨δ', ψ, fun c => ?_, hψ⟩
        rw [hδ'c, h3e]
      · have hp2 : p ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.2 hodd) even_two
        obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components
          (r := p ^ e) (hp.isPrimePow.pow (by omega)) hodd.pow F
          (by rw [hF6, ← pow_mul]; ring_nf) σ (fun c => by rw [hσ2, ← pow_mul]; ring_nf) δ
          (fun c => by rw [hδc, ← pow_mul]; ring_nf) g (hα ▸ hα2)
        exact ⟨δ, ψ, hδc, hα ▸ hψ⟩
    exact card_SL2_ne_triality_order hp he
      (hcardS.symm.trans (triality_field_coset_fixed_card hp he F hF6 σ hσ2 δ' hδ' α ψ hψ S
        hSn hSs))

theorem triality_involution_fixed_groups_have_no_normal_even_SL2_derivedCentralQuotient
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (p ^ f) ^ 3) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 F σ.toRingHom)))
    (hα1 : α ≠ 1) (hα2 : α ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (S : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 F σ.toRingHom)))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    IsEmpty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨-, -, -, -, ⟨φ⟩⟩ := triality_normal_form hp hf F hF σ hσ
  set β := MulAut.congr φ α with hβ
  have hβ1 : β ≠ 1 := fun h => hα1 ((MulAut.congr φ).injective (h.trans (map_one _).symm))
  have hβ2 : β ^ 2 = 1 := by rw [hβ, ← map_pow, hα2, map_one]
  have hmap := CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv
      (((α.toMonoidHom.eqLocus _).equivMapOfInjective _ φ.injective).trans
        (MulEquiv.subgroupCongr hmap)) S hSn hSs hSnab
  have h := triality_involution_fixed_groups_have_no_normal_even_SL2 hp hf F hF σ hσ β hβ1 hβ2 hn
    K hK S' hS'n hS's hS'nab
  exact ⟨fun e => h.false (eS.symm.trans e)⟩

end CFSG.LocalAnalysis.SteinbergCA
