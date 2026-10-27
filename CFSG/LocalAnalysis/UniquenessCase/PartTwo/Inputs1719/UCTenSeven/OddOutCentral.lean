module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAction
public import CFSG.LieType.OutStructureRankFreeFive
import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def OutCentralAt (K : Type) [Group K] (p : ℕ) : Prop :=
  ∀ β : Outer K, β ^ p = 1 → ∀ R : Subgroup (Outer K), IsPGroup 2 R →
    β ∈ normalizer (R : Set (Outer K)) → ∀ ρ ∈ R, β * ρ = ρ * β

theorem outCentralAt_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {p : ℕ}
    (h : OutCentralAt K' p) : OutCentralAt K p := by
  intro β hβ R hR2 hβR ρ hρ
  let E : Outer K ≃* Outer K' := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  have hcomp : (MulAut.conj (E β)).toMonoidHom.comp E.toMonoidHom =
      E.toMonoidHom.comp (MulAut.conj β).toMonoidHom := by
    ext x
    change MulAut.conj (E β) (E x) = E (MulAut.conj β x)
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hmap : R.map (MulAut.conj β).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hβR
  have hnorm : E β ∈ normalizer (R.map E.toMonoidHom : Set (Outer K')) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc (R.map E.toMonoidHom).map (MulAut.conj (E β)).toMonoidHom
        = R.map ((MulAut.conj (E β)).toMonoidHom.comp E.toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = R.map (E.toMonoidHom.comp (MulAut.conj β).toMonoidHom) := by rw [hcomp]
      _ = (R.map (MulAut.conj β).toMonoidHom).map E.toMonoidHom := by rw [Subgroup.map_map]
      _ = R.map E.toMonoidHom := by rw [hmap]
  have hE := h (E β) (by rw [← map_pow, hβ, map_one])
    (R.map E.toMonoidHom) (hR2.map E.toMonoidHom) hnorm (E ρ)
    (Subgroup.mem_map_of_mem E.toMonoidHom hρ)
  apply E.injective
  rw [map_mul, map_mul]
  exact hE


theorem commute_of_mem_normal_comm {O : Type} [Group O] [Finite O] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Subgroup O) [N.Normal] (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    {β : O} (hβ : β ^ p = 1) (hβN : β ∈ N) {R : Subgroup O} (hR : IsPGroup 2 R)
    (hβR : β ∈ normalizer (R : Set O)) : ∀ ρ ∈ R, β * ρ = ρ * β := by
  intro ρ hρ
  let B : Subgroup O := Subgroup.zpowers β
  have hBp : IsPGroup p B := by
    have hcard : Nat.card ↥B = orderOf β := Nat.card_zpowers β
    have hdvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβ
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h, pow_one])
  have hBN : B ≤ N := Subgroup.zpowers_le.mpr hβN
  have hBT : B ≤ normalizer (R : Set O) := Subgroup.zpowers_le.mpr hβR
  have hdouble : ⁅⁅R, B⁆, B⁆ = ⁅R, B⁆ :=
    CFSG.LocalAnalysis.GLTheoremA.commutator_commutator_eq_of_isPGroup hp hBp hR hp2 hBT
  have hRN : ⁅R, B⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro r hr b hb
    rw [commutatorElement_def]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem b (hBN hb) r) (N.inv_mem (hBN hb))
  have hCB : ⁅⁅R, B⁆, B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hN b (hBN hb) c (hRN hc)
  have hRB : ⁅R, B⁆ = ⊥ := by
    rw [← hdouble]
    exact hCB
  have hmem : ⁅ρ, β⁆ ∈ ⁅R, B⁆ :=
    Subgroup.commutator_mem_commutator hρ (Subgroup.mem_zpowers β)
  rw [hRB, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm


theorem commute_of_cyclic_normal_comm_quotient {O : Type} [Group O] [Finite O] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup O) [N.Normal] (hN : IsCyclic N)
    (hQ : ∀ x y : O ⧸ N, x * y = y * x) {β : O} (hβ : β ^ p = 1) {R : Subgroup O}
    (hR : IsPGroup 2 R) (hβR : β ∈ normalizer (R : Set O)) : ∀ ρ ∈ R, β * ρ = ρ * β := by
  intro ρ hρ
  let B : Subgroup O := Subgroup.zpowers β
  have hBp : IsPGroup p B := by
    have hcard : Nat.card ↥B = orderOf β := Nat.card_zpowers β
    have hdvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβ
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h, pow_one])
  have hBT : B ≤ normalizer (R : Set O) := Subgroup.zpowers_le.mpr hβR
  have hdouble : ⁅⁅R, B⁆, B⁆ = ⁅R, B⁆ :=
    CFSG.LocalAnalysis.GLTheoremA.commutator_commutator_eq_of_isPGroup hp hBp hR hp2 hBT
  have hCR : ⁅R, B⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr b hb
    rw [commutatorElement_def, show r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) by group]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hBT hb) r⁻¹).mp (R.inv_mem hr))
  have hCN : ⁅R, B⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro r hr b hb
    have hq : QuotientGroup.mk' N ⁅r, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hQ _ _)
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hC2 : IsPGroup 2 ↥(⁅R, B⁆) := IsPGroup.to_le hR hCR
  have : IsCyclic ↥N := hN
  have hCcyc : IsCyclic ↥(⁅R, B⁆) := Subgroup.isCyclic_of_le hCN
  have hmapR : R.map (MulAut.conj β).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hβR
  have hmapB : B.map (MulAut.conj β).toMonoidHom = B := by
    rw [show B = Subgroup.zpowers β from rfl, MonoidHom.map_zpowers]
    have hβfix : (MulAut.conj β) β = β := by rw [MulAut.conj_apply]; group
    exact congrArg Subgroup.zpowers hβfix
  have hβC : β ∈ normalizer ((⁅R, B⁆ : Subgroup O) : Set O) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⁅R, B⁆ : Subgroup O).map (MulAut.conj β).toMonoidHom = ⁅R, B⁆
    rw [Subgroup.map_commutator, hmapR, hmapB]
  have : IsCyclic ↥(⁅R, B⁆) := hCcyc
  let σ : MulAut ↥(⁅R, B⁆) := (⁅R, B⁆ : Subgroup O).normalizerMonoidHom ⟨β, hβC⟩
  have hσp : σ ^ p = 1 := by
    have hβp : (⟨β, hβC⟩ : ↥(normalizer ((⁅R, B⁆ : Subgroup O) : Set O))) ^ p = 1 :=
      Subtype.ext (by simp [hβ])
    rw [← map_pow, hβp, map_one]
  have hσ1 : σ = 1 :=
    CFSG.LocalAnalysis.GorensteinLyons.mulAut_eq_one_of_odd hC2 (hp.odd_of_ne_two hp2) hσp
  have hβcent : β ∈ Subgroup.centralizer ((⁅R, B⁆ : Subgroup O) : Set O) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h := congrArg (fun f : MulAut ↥(⁅R, B⁆) => ((f ⟨c, hc⟩ : ↥(⁅R, B⁆)) : O)) hσ1
    simp only [MulAut.one_apply] at h
    have h2 : β * c * β⁻¹ = c := by simpa [σ] using h
    calc c * β = (β * c * β⁻¹) * β := by rw [h2]
      _ = β * c := by group
  have hCB : ⁅⁅R, B⁆, B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr hβcent
  have hRB : ⁅R, B⁆ = ⊥ := by
    rw [← hdouble]
    exact hCB
  have hmem : ⁅ρ, β⁆ ∈ ⁅R, B⁆ :=
    Subgroup.commutator_mem_commutator hρ (Subgroup.mem_zpowers β)
  rw [hRB, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm


theorem outCentralAt_of_fieldPart {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (h : ∃ F : Subgroup (MulAut K), (inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ inner K = ⊥ ∧
      ¬ p ∣ (inner K ⊔ F).index ∧
      ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ inner K ⊔ F) :
    OutCentralAt K p := by
  classical
  obtain ⟨F, hEnorm, hFcyc, -, hEidx, -⟩ := h
  intro β hβ R hR2 hβR ρ hρ
  let φ : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  let E : Subgroup (Outer K) := (inner K ⊔ F).map φ
  have hEeq : E = F.map φ := by
    dsimp only [E]; rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hEcyc : IsCyclic ↥E := by
    rw [hEeq]
    have : IsCyclic ↥F := hFcyc
    exact isCyclic_of_surjective (φ.subgroupMap F) (φ.subgroupMap_surjective F)
  have hEnorm' : E.Normal := by
    dsimp only [E]; exact hEnorm.map φ hφsurj
  have hEindex : E.index = (inner K ⊔ F).index := by
    dsimp only [E]
    rw [Subgroup.index_map_eq _ hφsurj (by rw [QuotientGroup.ker_mk']; exact le_sup_left)]
  have : E.Normal := hEnorm'
  have hβE : β ∈ E := by
    by_contra hβE
    let q : Outer K ⧸ E := QuotientGroup.mk' E β
    have hq1 : q ≠ 1 := by
      intro hq; exact hβE ((QuotientGroup.eq_one_iff β).mp hq)
    have hqp : q ^ p = 1 := by
      rw [show q = QuotientGroup.mk' E β from rfl, ← map_pow, hβ, map_one]
    have hqordp : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqp
    have hqordcard : orderOf q ∣ Nat.card (Outer K ⧸ E) := orderOf_dvd_natCard q
    have hpdvd : p ∣ E.index := by
      rcases (Nat.dvd_prime hp).1 hqordp with h1 | hp1
      · exact absurd (orderOf_eq_one_iff.mp h1) hq1
      · rw [← hp1, Subgroup.index_eq_card]
        exact hqordcard
    exact hEidx (by rwa [hEindex] at hpdvd)
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    have : IsCyclic ↥E := hEcyc
    intro x hx y hy
    have h := mul_comm' (⟨x, hx⟩ : ↥E) (⟨y, hy⟩ : ↥E)
    simpa using congrArg Subtype.val h
  exact commute_of_mem_normal_comm hp hp2 E hcommE hβ hβE hR2 hβR ρ hρ


theorem outCentralAt_of_clauseFive {i : TauCeti.CFSGIndex}
    (hi : CFSG.LieType.OutStructure.I713ClauseFreeFive i) {K : Type} [Group K] [Finite K]
    (hK : IsSimpleGroup K) (he : Nonempty (K ≃* i.Group)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OutCentralAt K p := by
  have hp2 : p ≠ 2 := by omega
  intro β hβ R hR2 hβR ρ hρ
  by_cases hnab : ∃ a b : K, a * b ≠ b * a
  · rcases hi K hK hnab he p hp hp5 with hOut | hfield | ⟨hp3, -, -⟩
    · have hβ1 : β = 1 := by
        have hpdvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβ
        have hcdvd : orderOf β ∣ Nat.card (Outer K) := orderOf_dvd_natCard β
        rcases (Nat.dvd_prime hp).1 hpdvd with h1 | hp1
        · exact orderOf_eq_one_iff.mp h1
        · exact absurd (hp1 ▸ hcdvd) hOut
      rw [hβ1]; simp
    · exact outCentralAt_of_fieldPart hp hp2 hfield β hβ R hR2 hβR ρ hρ
    · omega
  · push Not at hnab
    have : Nontrivial K := IsSimpleGroup.toNontrivial
    obtain ⟨x₀, hx₀⟩ := exists_ne (1 : K)
    have hnormal : (Subgroup.zpowers x₀).Normal := by
      constructor
      intro n hn g
      rw [show g * n * g⁻¹ = n by rw [hnab g n]; group]
      exact hn
    have : (Subgroup.zpowers x₀).Normal := hnormal
    have hne : Subgroup.zpowers x₀ ≠ ⊥ := by
      intro hbot
      have : x₀ ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers x₀
      exact hx₀ (Subgroup.mem_bot.mp this)
    have hgen : Subgroup.zpowers x₀ = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x₀) with h | h
      · exact absurd h hne
      · exact h
    have : IsCyclic K := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x₀, hgen⟩
    have hmulAut : ∀ x y : MulAut K, x * y = y * x := by
      intro x y
      exact (IsCyclic.mulAutMulEquiv K).injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    have hout : ∀ a b : Outer K, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (inner K) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (inner K) b
      rw [← map_mul, ← map_mul]
      exact congrArg (QuotientGroup.mk' (inner K)) (hmulAut x y)
    exact hout β ρ


theorem outCentralAt_of_projectiveSL {K : Type} [Field K] [Finite K] {N r f p : ℕ}
    (hr : r.Prime) (hf : 0 < f) (hK : Nat.card K = r ^ f) (hN : 2 ≤ N) (hp : p.Prime)
    (hp2 : p ≠ 2) : OutCentralAt (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K) p := by
  by_cases hN3 : 3 ≤ N
  · obtain ⟨N', hN'n, hN'cyc, -, hQ, -⟩ :=
      CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter.linear_outer_filtration (K := K) (n := N) hN3
    have : N'.Normal := hN'n
    exact fun β hβ R hR2 hβR ρ hρ =>
      commute_of_cyclic_normal_comm_quotient hp hp2 N' hN'cyc hQ hβ hR2 hβR ρ hρ
  · have hN2 : N = 2 := by omega
    rw [hN2]
    have hfield := CFSG.LieType.OutStructure.exists_fieldPart_coordinateG (K := K) hp hp2 hr hf hK
    have hcoord : OutCentralAt
        ↥(CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG K) p :=
      outCentralAt_of_fieldPart hp hp2 hfield
    have e : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K ≃*
        ↥(CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG K) :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG K)
    exact outCentralAt_of_mulEquiv e hcoord


theorem outCentralAt_of_lieModel_psl {X : Type} [Group X] [Finite X] {N r f p : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible .PSL N r f) (hX : CFSG.Blueprint.LieModel X .PSL N r f)
    (hp : p.Prime) (hp2 : p ≠ 2) : OutCentralAt X p := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  let hKfieldInst : Field K := hKfield
  have : Finite K := hKfin
  have hr : r.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  have hN : 2 ≤ N := hadm.2.2.1
  exact outCentralAt_of_mulEquiv e (outCentralAt_of_projectiveSL hr hf hKcard hN hp hp2)


theorem outCentralAt_of_statedPSU {X : Type} [Group X] [Finite X] {N r f p : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSU N r f) (hp : p.Prime) (hp2 : p ≠ 2) :
    OutCentralAt X p := by
  obtain ⟨⟨hr, hf, hN, h32⟩, K, hKfield, hKfin, hKcard, ⟨eL⟩⟩ := h
  let hKfieldInst : Field K := hKfield
  have : Finite K := hKfin
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K :=
    ⟨hr, hf, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have hq : ¬ (N = 3 ∧ r ^ f = 2) := by
    rintro ⟨h3, h2⟩
    exact h32 (by rw [h3, h2])
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv hU
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := N) (K := K))
  let eC : X ≃* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
    eL.trans ((eP.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega))).symm)
  obtain ⟨N', hN'n, hN'cyc, -, hQcyc⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter.unitary_outer_filtration hU hN hq
  have : N'.Normal := hN'n
  have hQ : ∀ x y : Outer (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⧸ N', x * y = y * x := by
    have : IsCyclic (Outer (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⧸ N') := hQcyc
    intro x y
    exact mul_comm' x y
  have hO : OutCentralAt (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) p := fun β hβ R hR2 hβR ρ hρ =>
    commute_of_cyclic_normal_comm_quotient hp hp2 N' hN'cyc hQ hβ hR2 hβR ρ hρ
  exact outCentralAt_of_mulEquiv eC hO


theorem outCentralAt_lie_odd
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic ≠ 2) {K : Type} [Group K]
    [Finite K] (hK : IsSimpleGroup K) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OutCentralAt K p := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hv⟩ := d
  cases d with
  | A n q =>
    by_cases h1 : n = 1
    · subst h1
      exact outCentralAt_of_clauseFive
        (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_A1 q hv) hK he hp hp5
    · have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      obtain ⟨eK⟩ := he
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      let Fq := GaloisField q.p q.exponent
      have hqcard : Nat.card Fq = q.p ^ q.exponent :=
        GaloisField.card q.p q.exponent q.exponent_pos.ne'
      let ePSL : (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group ≃*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (n + 1) Fq :=
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
          (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) Fq)
      exact outCentralAt_of_mulEquiv eK (outCentralAt_of_mulEquiv ePSL
        (outCentralAt_of_projectiveSL q.prime_p q.exponent_pos hqcard (by omega) hp hp2))
  | twistedA n q =>
    obtain ⟨eK⟩ := he
    exact outCentralAt_of_statedPSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv eK) hp hp2
  | B n q =>
    have hn2 : 2 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    by_cases h2 : n = 2
    · subst h2
      exact outCentralAt_of_clauseFive
        (CFSG.LieType.OutStructure.i713ClauseFree_lie_B2 q hv).toFive hK he hp hp5
    · by_cases hq2 : q.p = 2
      · exact outCentralAt_of_clauseFive
          (CFSG.LieType.OutStructure.i713ClauseFree_lie_B_even n q hv hq2 (by omega)).toFive hK he hp hp5
      · exact outCentralAt_of_clauseFive
          (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_B_odd n q hv hq2 (by omega)) hK he hp hp5
  | C n q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_C n q hv).toFive hK he hp hp5
  | D n q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_D n q hv) hK he hp hp5
  | twistedD n q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_twistedD n q hv) hK he hp hp5
  | E6 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_E6 q hv) hK he hp hp5
  | E7 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_E7 q hv).toFive hK he hp hp5
  | E8 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_E8 q hv).toFive hK he hp hp5
  | F4 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_F4 q hv).toFive hK he hp hp5
  | G2 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_G2 q hv).toFive hK he hp hp5
  | twistedE6 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFreeFive_lie_twistedE6 q hv) hK he hp hp5
  | trialityD4 q =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_trialityD4 q hv).toFive hK he hp hp5
  | suzuki m =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_twistedB2 m hv).toFive hK he hp hp5
  | reeG2 m =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_twistedG2 m hv).toFive hK he hp hp5
  | reeF4 m =>
    exact outCentralAt_of_clauseFive
      (CFSG.LieType.OutStructure.i713ClauseFree_lie_twistedF4 m hv).toFive hK he hp hp5
  | tits => exact absurd (by simp) hd

theorem kOddLieOutCentral_holds :
    KOddLieOutCentral := by
  intro X _ _ hXs t n r f hr2 hadm hmod _ p hp hp5
  change OutCentralAt X p
  have hp2 : p ≠ 2 := by omega
  by_cases hdup : CFSG.HardMathSupport.Dickson.Sec6.I1431.TauCetiDuplicate t n r f
  · rcases hdup with ⟨rfl, -⟩ | ⟨rfl, rfl, hpow⟩
    · exact outCentralAt_of_lieModel_psl hadm hmod hp hp2
    · have hr3 : r = 3 := by
        have hdvd : r ∣ 3 := by
          rw [← hpow]
          exact dvd_pow_self r (Nat.pos_iff_ne_zero.mp hadm.2.1)
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
        · exact absurd h hadm.1.ne_one
        · exact h
      have hf1 : f = 1 := by
        have h3f : 3 ^ f = 3 := by rwa [hr3] at hpow
        have h : 3 ^ f = 3 ^ 1 := by rw [h3f]; norm_num
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
      have hsc0 : CFSG.Open.StatedClassicalModel X .PSp 2 r f :=
        CFSG.Blueprint.LieModel.statedClassicalModel hmod (by decide)
      have hsc : CFSG.Open.StatedClassicalModel X .PSp 2 3 1 := by
        simpa [hr3, hf1] using hsc0
      exact outCentralAt_of_statedPSU
        (CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three hsc) hp hp2
  · obtain ⟨d, hchar, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_tauCeti_index_of_blueprint_lieModel_odd
        CFSG.TauCetiBridge.typewiseBridges hmod hr2 hdup
    exact outCentralAt_lie_odd d (by rw [hchar]; exact hr2) hXs ⟨eK⟩ hp hp5

theorem kOddLieNormSylowAlpha_of_autSylow
    (hA : KOddLieAutSylow) : KOddLieNormSylowAlpha :=
  kOddLieNormSylowAlpha_of_aut_out hA kOddLieOutCentral_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
