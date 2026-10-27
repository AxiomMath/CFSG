module

public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.C213NonQBasic

public section

namespace CFSG.Quasithin.C213NonQ

open CFSG.Open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

theorem map_pCore_le_pCore {K : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q)) (q : ℕ)
    [Fact q.Prime] : (CFSG.pCore q ↥K).map K.subtype ≤ CFSG.pCore q Q := by
  have h1 : (CFSG.pCore q ↥K).map K.subtype ≤ pCoreOf q (⊤ : Subgroup Q) := by
    have := SQTKHyp.pCoreOf_le_of_subnormal q (subnormal_of_mem_cComp hK)
    rwa [pCoreOf] at this
  rwa [CFSG.Quasithin.pCoreOf_top q] at h1

theorem map_pCore_le {K M : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hFM : CFSG.generalizedFitting Q ≤ M) (q : ℕ) [Fact q.Prime] :
    (CFSG.pCore q ↥K).map K.subtype ≤ M :=
  (map_pCore_le_pCore hK q).trans ((CFSG.pCore_le_fitting Q q).trans (le_sup_left.trans hFM))

omit [Finite Q] in
theorem le_normalizer_map_of_characteristic {K L : Subgroup Q}
    (hLK : L ≤ Subgroup.normalizer (K : Set Q)) (P : Subgroup ↥K) [P.Characteristic] :
    L ≤ Subgroup.normalizer ((P.map K.subtype : Subgroup Q) : Set Q) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set Q), ∀ x ∈ P.map K.subtype,
      g * x * g⁻¹ ∈ P.map K.subtype := by
    intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    set α : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨g, hg⟩ with hα
    have h1 : α x' ∈ P := by
      have := (inferInstance : P.Characteristic)
      rw [Subgroup.characteristic_iff_map_le] at this
      exact this α ⟨x', hx', rfl⟩
    exact ⟨α x', h1, rfl⟩
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key l (hLK hl) x, fun hx => ?_⟩
  have := key l⁻¹ (Subgroup.inv_mem _ (hLK hl)) _ hx
  simpa [mul_assoc] using this

omit [Finite Q] in
theorem commutator_eq_bot_of_commutator_eq_bot {K L P : Subgroup Q} (hKL : ⁅K, L⁆ = K)
    (hPK : K ≤ Subgroup.normalizer (P : Set Q)) (hPL : ⁅P, L⁆ = ⊥) : ⁅K, P⁆ = ⊥ := by
  have h1 : ⁅⁅L, P⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L P, hPL, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅P, K⁆, L⁆ = ⊥ := by
    have hPK' : ⁅P, K⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro x hx k hk
      have h3 : k * x⁻¹ * k⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hPK hk) x⁻¹).mp (P.inv_mem hx)
      rw [commutatorElement_def, show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
      exact P.mul_mem hx h3
    exact le_bot_iff.mp (hPL ▸ Subgroup.commutator_mono hPK' le_rfl)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hKL] at h3

theorem false_of_central {K : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q)) (hext : A36Extra ↥K)
    {q : ℕ} (hq : q.Prime) (hqF : q ∣ Nat.card (CFSG.fittingSubgroup ↥K))
    (hcen : ∀ x : ↥K, ∀ d ∈ CFSG.pCore q ↥K, x * d = d * x) : False := by
  obtain ⟨P, -, -, -, hact⟩ := hext q hq hqF
  have hall : ∀ x : ↥K, x ∈ CFSG.fittingSubgroup ↥K := by
    intro x
    refine (hact x).mp fun d hd => ?_
    obtain ⟨d', -, rfl⟩ := hd
    have h1 : x * (d' : ↥K) * x⁻¹ = d' := by
      rw [hcen x _ d'.2, mul_inv_cancel_right]
    rw [show (CFSG.pCore q ↥K).subtype d' = (d' : ↥K) from rfl, h1, inv_mul_cancel]
    exact Subgroup.one_mem _
  have htop : CFSG.fittingSubgroup ↥K = ⊤ := eq_top_iff.mpr fun x _ => hall x
  have hnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥K) := CFSG.fittingSubgroup_nilpotent
  rw [htop] at hnil
  have : Group.IsNilpotent ↥K := by
    have e : ↥(⊤ : Subgroup ↥K) ≃* ↥K := Subgroup.topEquiv
    exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  exact not_isSolvable_of_mem_cComp hK inferInstance

theorem map_pCore_le_of_card {K M L : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hext : A36Extra ↥K) (hFM : CFSG.generalizedFitting Q ≤ M) (hL : L ∈ cComp M)
    (hLK : L ≤ Subgroup.normalizer (K : Set Q)) (hKL : ⁅K, L⁆ = K) {q : ℕ} [Fact q.Prime]
    (hqF : q ∣ Nat.card (CFSG.fittingSubgroup ↥K))
    (hcard : Nat.card (↥(CFSG.pCore q ↥K) ⧸ frattini ↥(CFSG.pCore q ↥K)) = q ^ 2) :
    (CFSG.pCore q ↥K).map K.subtype ≤ L := by
  set P' : Subgroup Q := (CFSG.pCore q ↥K).map K.subtype with hP'
  have hP'q : IsPGroup q ↥P' := CFSG.pCore_isPGroup.map K.subtype
  have hcard' : Nat.card (↥P' ⧸ frattini ↥P') = q ^ 2 := by
    rw [← card_frattini_quotient_congr
      ((CFSG.pCore q ↥K).equivMapOfInjective K.subtype K.subtype_injective)]
    exact hcard
  have hLP' : L ≤ Subgroup.normalizer (P' : Set Q) := le_normalizer_map_of_characteristic hLK _
  rcases commutator_eq_or_eq_bot hP'q hcard' hLP' (perfect_of_mem_cComp hL) with h | h
  · exfalso
    have h2 := commutator_eq_bot_of_commutator_eq_bot hKL
      (le_normalizer_map_of_characteristic Subgroup.le_normalizer _) h
    refine false_of_central hK hext Fact.out hqF fun x d hd => ?_
    have h3 := Subgroup.commutator_mem_commutator x.2 (show (d : Q) ∈ P' from ⟨d, hd, rfl⟩)
    rw [h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subtype.ext h3
  · have hP'M := map_pCore_le hK hFM q
    have hsolv : Group.IsSolvable ↥P' := by
      have : Group.IsNilpotent ↥P' := hP'q.isNilpotent
      infer_instance
    have h3 := (cComp_commutator_perfectCore hL hP'M hsolv hLP').1
    rw [← h, Subgroup.commutator_comm]
    exact h3

theorem card_frattini_quotient_of_isElemAbelianOfRank {p : ℕ} [Fact p.Prime] {X : Type}
    [Group X] (hX : IsElemAbelianOfRank p 2 X) : Nat.card (X ⧸ frattini X) = p ^ 2 := by
  obtain ⟨e⟩ := hX
  let e₁ : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod (p ^ 1)) :=
    AddEquiv.piCongrRight fun _ => (ZMod.ringEquivCongr (pow_one p).symm).toAddEquiv
  rw [card_frattini_quotient_congr (e.trans (AddEquiv.toMultiplicative e₁)),
    Nat.card_congr (CFSG.standardHomocyclicCoverFrattiniQuotientEquiv (Fin 2) p 1 le_rfl).toEquiv,
    Nat.card_eq_fintype_card]
  simp [CFSG.StandardHomocyclicCover, ZMod.card]

theorem fitting_le_of_case34 {K M L : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q))
    (h36 : A36Strong K) (h34 : A36Case3 ↥K ∨ A36Case4 ↥K)
    (hFM : CFSG.generalizedFitting Q ≤ M) (hL : L ∈ cComp M)
    (hLK : L ≤ Subgroup.normalizer (K : Set Q)) (hKL : ⁅K, L⁆ = K) :
    (CFSG.fittingSubgroup ↥K).map K.subtype ≤ L := by
  have hext := h36.2.2 h34
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup, iSup_le_iff]
  rintro ⟨p, hp⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  by_cases hpF : p ∣ Nat.card (CFSG.fittingSubgroup ↥K)
  · refine map_pCore_le_of_card hK hext hFM hL hLK hKL hpF ?_
    rcases h34 with ⟨p', hp', -, -, hE, -⟩ | ⟨-, -, -, hshape⟩
    ·
      have : Fact p'.Prime := ⟨hp'⟩
      obtain ⟨e⟩ := id hE
      have hcardF : Nat.card (CFSG.fittingSubgroup ↥K) = p' ^ 2 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
        simp [ZMod.card]
      have hpp' : p = p' := by
        rw [hcardF] at hpF
        exact (Nat.prime_dvd_prime_iff_eq hpp hp').mp (hpp.dvd_of_dvd_pow hpF)
      subst hpp'
      have hFp : IsPGroup p ↥(CFSG.fittingSubgroup ↥K) := IsPGroup.of_card hcardF
      have heq : CFSG.pCore p ↥K = CFSG.fittingSubgroup ↥K :=
        le_antisymm (CFSG.pCore_le_fitting _ p)
          (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hFp)
      rw [card_frattini_quotient_congr (MulEquiv.subgroupCongr heq)]
      exact card_frattini_quotient_of_isElemAbelianOfRank hE
    · rcases (hshape p hpp hpF).2 with h1 | h1
      · exact card_frattini_quotient_of_isPOnePlusTwo h1
      · exact card_frattini_quotient_of_isHomocyclicRank2 h1
  · have hle : CFSG.pCore p ↥K ≤ CFSG.fittingSubgroup ↥K := CFSG.pCore_le_fitting _ p
    have hbot : CFSG.pCore p ↥K = ⊥ := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥K)).exists_card_eq
      have hdvd : Nat.card (CFSG.pCore p ↥K) ∣ Nat.card (CFSG.fittingSubgroup ↥K) :=
        Subgroup.card_dvd_of_le hle
      rcases k with _ | k
      · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
      · exfalso
        apply hpF
        rw [hk] at hdvd
        exact (dvd_pow_self p (by omega)).trans hdvd
    rw [hbot, Subgroup.map_bot]
    exact bot_le

end CFSG.Quasithin.C213NonQ
