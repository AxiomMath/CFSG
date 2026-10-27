module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72SLPiInndiag
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG.RankThree.PartTwo.Sec16.Steps166

@[expose] def KSGL3NoSz : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (X : Subgroup (GL (Fin 3) K)) (N : Subgroup X) [N.Normal]
    (p f : ℕ), ¬ CFSG.Blueprint.SuzukiModel (X ⧸ N) p f

namespace KSL3PiNoSzProof

theorem isPerfect_of_suzukiModel {H : Type} [Group H] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel H p f) : Group.IsPerfect H := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  have := (CFSG.LieType.Ree.suzuki_perfect (K := K) ha hcard).2
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem five_dvd_card_of_suzukiModel {H : Type} [Group H]
    {p f : ℕ} (h : CFSG.Blueprint.SuzukiModel H p f) : 5 ∣ Nat.card H := by
  obtain ⟨-, a, -, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hcard]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : ((2 : ℕ) ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [h1, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem false_of_surjective {H Q : Type} [Group H] [Group Q] (hH : NoSzSection H)
    (φ : H →* Q) (hφ : Function.Surjective φ) {p f : ℕ}
    (hQ : CFSG.Blueprint.SuzukiModel Q p f) : False := by
  set ψ : (⊤ : Subgroup H) →* Q := φ.comp (⊤ : Subgroup H).subtype with hψ
  have hψs : Function.Surjective ψ := fun q => by
    obtain ⟨x, rfl⟩ := hφ q
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  exact hH ⊤ ψ.ker p f
    (suzukiModel_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) hQ)

theorem noSzSection_of_surjective {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (hG : NoSzSection G) : NoSzSection H := by
  intro X N _ p f hSz
  set X' := X.comap φ with hX'
  set ψ : X' →* X ⧸ N := (QuotientGroup.mk' N).comp (φ.subgroupComap X)
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨g, hg⟩ := hφ (x : H)
    refine ⟨⟨g, show φ g ∈ X by rw [hg]; exact x.2⟩, ?_⟩
    simp only [ψ, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hg
  exact false_of_surjective (noSzSection_of_injective X'.subtype X'.subtype_injective hG) ψ hψs
    hSz

theorem noSzSection_of_commutator_le {M : Type} [Group M]
    {D : Subgroup M} (hD : commutator M ≤ D) (hDs : NoSzSection D) : NoSzSection M := by
  intro X N _ p f hSz
  have hperf := isPerfect_of_suzukiModel hSz
  set X₀ : Subgroup X := commutator X with hX₀
  set ψ : X₀ →* X ⧸ N := (QuotientGroup.mk' N).comp X₀.subtype with hψ
  have hψs : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, hψ, MonoidHom.range_comp, Subgroup.range_subtype, hX₀,
      commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact hperf.commutator_eq_top
  have hX₀D : ∀ x ∈ X₀, ((x : X) : M) ∈ D := by
    intro x hx
    apply hD
    have hle : X₀.map X.subtype ≤ commutator M := by
      rw [hX₀, commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact hle ⟨x, hx, rfl⟩
  set ι : X₀ →* D :=
    { toFun := fun x => ⟨((x : X) : M), hX₀D x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  have hιi : Function.Injective ι := by
    intro x y hxy
    have := congrArg (fun z : D => (z : M)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact false_of_surjective (noSzSection_of_injective ι hιi hDs) ψ hψs hSz

section SeventyTwo

variable {T : Type} [Group T] [Finite T]

theorem eq_one_of_pow_five {Y : Type} [Group Y] [Finite Y] (τ : MulAut Y) (hτ : τ ^ 5 = 1)
    (hcard : ∀ d, d ∣ Nat.card Y → d % 5 = Nat.card Y % 5 → d = Nat.card Y) : τ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set H := Subgroup.zpowers τ with hH
  have hH5 : IsPGroup 5 H := by
    intro h
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hτ, one_zpow, Subgroup.coe_one]
  have hmod := hH5.card_modEq_card_fixedPoints Y
  set C := FixedPoints.subgroup H Y with hC
  have hCcard : Nat.card C = Nat.card (MulAction.fixedPoints H Y) := rfl
  have hdvd : Nat.card C ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card C
  have hCY : Nat.card C = Nat.card Y :=
    hcard _ hdvd (by rw [hCcard]; exact hmod.symm)
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hCY
  ext y
  have hy : y ∈ C := htop ▸ Subgroup.mem_top y
  exact hy ⟨τ, Subgroup.mem_zpowers τ⟩

@[expose] def restrict (σ : MulAut T) (P : Subgroup T) (hP : P.map σ.toMonoidHom = P) :
    MulAut P :=
  (σ.subgroupMap P).trans (MulEquiv.subgroupCongr hP)

omit [Finite T] in
theorem coe_restrict (σ : MulAut T) (P : Subgroup T) (hP : P.map σ.toMonoidHom = P) (x : P) :
    ((restrict σ P hP x : P) : T) = σ x := rfl

theorem fixed_of_invariant {σ : MulAut T} (hσ : σ ^ 5 = 1) {P : Subgroup T}
    (hP : P.map σ.toMonoidHom = P)
    (hcard : ∀ d, d ∣ Nat.card P → d % 5 = Nat.card P % 5 → d = Nat.card P) :
    ∀ x ∈ P, σ x = x := by
  have hpow : ∀ k : ℕ, ∀ x : P, (((restrict σ P hP ^ k) x : P) : T) = (σ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, coe_restrict, ih, pow_succ', MulAut.mul_apply]
  have h5 : restrict σ P hP ^ 5 = 1 := by
    ext x
    rw [hpow, hσ]
    rfl
  have h1 := eq_one_of_pow_five _ h5 hcard
  intro x hx
  have := congrArg (fun τ : MulAut P => ((τ ⟨x, hx⟩ : P) : T)) h1
  simpa [coe_restrict] using this

theorem exists_sylow_fixed {p : ℕ} [Fact p.Prime] {σ : MulAut T} (hσ : σ ^ 5 = 1)
    (h5 : ¬ 5 ∣ Nat.card (Sylow p T)) :
    ∃ P : Sylow p T, (P : Subgroup T).map σ.toMonoidHom = P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set H := Subgroup.zpowers σ with hH
  have hH5 : IsPGroup 5 H := by
    intro h
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hσ, one_zpow, Subgroup.coe_one]
  have hmod := hH5.card_modEq_card_fixedPoints (Sylow p T)
  have hne : (MulAction.fixedPoints H (Sylow p T)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints H (Sylow p T)) = 0 := by
      rw [hemp]
      simp
    rw [h0] at hmod
    apply h5
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hmod
  obtain ⟨P, hP⟩ := hne
  refine ⟨P, ?_⟩
  have h1 : σ • P = P := hP ⟨σ, Subgroup.mem_zpowers σ⟩
  have h2 := congrArg (fun Q : Sylow p T => (Q : Subgroup T)) h1
  simp only [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h2
  exact h2

theorem eq_one_of_pow_five_of_card (hT : Nat.card T = 72) {σ : MulAut T} (hσ : σ ^ 5 = 1) :
    σ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p T),
      Nat.card (P : Subgroup T) * (P : Subgroup T).index = 72 := fun p _ P => by
    rw [Subgroup.card_mul_index, hT]
  have hnd : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p T), ¬ p ∣ (P : Subgroup T).index :=
    fun p _ P => P.not_dvd_index
  have hpg : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p T), ∃ k, Nat.card (P : Subgroup T) = p ^ k :=
    fun p _ P => IsPGroup.iff_card.mp P.isPGroup'
  have h3card : ∀ P : Sylow 3 T, Nat.card (P : Subgroup T) = 9 := by
    intro P
    obtain ⟨k, hk⟩ := hpg 3 P
    have h1 := hsyl 3 P
    have h2 := hnd 3 P
    rw [hk] at h1 ⊢
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
      omega
    interval_cases k <;> omega
  have h2card : ∀ Q : Sylow 2 T, Nat.card (Q : Subgroup T) = 8 := by
    intro Q
    obtain ⟨k, hk⟩ := hpg 2 Q
    have h1 := hsyl 2 Q
    have h2 := hnd 2 Q
    rw [hk] at h1 ⊢
    have hk3 : k ≤ 6 := by
      by_contra hk3
      have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
      omega
    interval_cases k <;> omega
  have hn3 : ¬ 5 ∣ Nat.card (Sylow 3 T) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 T))
    have hdvd := P.card_dvd_index
    have hidx : (P : Subgroup T).index = 8 := by
      have := hsyl 3 P
      rw [h3card P] at this
      omega
    rw [hidx] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    intro h5
    have hpos : 0 < Nat.card (Sylow 3 T) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 3 T) <;> omega
  have hn2 : ¬ 5 ∣ Nat.card (Sylow 2 T) := by
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 T))
    have hdvd := Q.card_dvd_index
    have hidx : (Q : Subgroup T).index = 9 := by
      have := hsyl 2 Q
      rw [h2card Q] at this
      omega
    rw [hidx] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    intro h5
    have hpos : 0 < Nat.card (Sylow 2 T) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 2 T) <;> omega
  obtain ⟨P, hP⟩ := exists_sylow_fixed hσ hn3
  obtain ⟨Q, hQ⟩ := exists_sylow_fixed hσ hn2
  have hPfix := fixed_of_invariant hσ hP (by
    rw [h3card P]
    intro d hd hd5
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp_all)
  have hQfix := fixed_of_invariant hσ hQ (by
    rw [h2card Q]
    intro d hd hd5
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp_all)
  have htop : (P : Subgroup T) ⊔ (Q : Subgroup T) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h9 : 9 ∣ Nat.card ((P : Subgroup T) ⊔ (Q : Subgroup T) : Subgroup T) := by
      rw [← h3card P]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h8 : 8 ∣ Nat.card ((P : Subgroup T) ⊔ (Q : Subgroup T) : Subgroup T) := by
      rw [← h2card Q]
      exact Subgroup.card_dvd_of_le le_sup_right
    have h72 : 72 ∣ Nat.card ((P : Subgroup T) ⊔ (Q : Subgroup T) : Subgroup T) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h8
    have hle : Nat.card ((P : Subgroup T) ⊔ (Q : Subgroup T) : Subgroup T) ≤ 72 := by
      rw [← hT]
      exact Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card ((P : Subgroup T) ⊔ (Q : Subgroup T) : Subgroup T) := Nat.card_pos
    rw [hT]
    exact le_antisymm hle (Nat.le_of_dvd hpos h72)
  set C := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id T) with hC
  have hPC : (P : Subgroup T) ≤ C := fun x hx => hPfix x hx
  have hQC : (Q : Subgroup T) ≤ C := fun x hx => hQfix x hx
  have hCtop : C = ⊤ := top_le_iff.mp (htop ▸ sup_le hPC hQC)
  ext x
  have hx : x ∈ C := hCtop ▸ Subgroup.mem_top x
  exact hx

theorem noSzSection_mulAut_of_card_seventyTwo
    (hT : Nat.card T = 72) : NoSzSection (MulAut T) := by
  have : Finite (MulAut T) :=
    Finite.of_injective (fun σ : MulAut T => (σ : T → T)) fun a b h => MulEquiv.ext (congrFun h)
  have h5 : ¬ 5 ∣ Nat.card (MulAut T) := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hσ5 : σ ^ 5 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have := eq_one_of_pow_five_of_card hT hσ5
    rw [this, orderOf_one] at hσ
    norm_num at hσ
  intro X N _ p f hSz
  apply h5
  have h1 := five_dvd_card_of_suzukiModel hSz
  exact h1.trans ((Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_subgroup_dvd_card X))

end SeventyTwo

end KSL3PiNoSzProof

open KSL3PiNoSzProof CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts in
theorem kSL3PiNoSz_of (h : KSGL3NoSz) : KSL3PiNoSz := by
  intro T _ hT X N _ p f hSz
  obtain ⟨p', e, _, he, hiso⟩ := hT
  suffices hTs : NoSzSection (MulAut T) from hTs X N p f hSz
  have hGL : ∀ (K : Type) [Field K] [Finite K], NoSzSection (GL (Fin 3) K) :=
    fun K _ _ X N _ p f => h K X N p f
  rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    obtain ⟨ψ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p' e)
    refine noSzSection_mulAut_of_mulEquiv (φ.trans ψ) ?_
    have hcomm : commutator (MulAut (projectiveSL 3 (GaloisField p' e))) ≤
        linearAutGroup 3 (GaloisField p' e) := by
      rw [commutator_def, Subgroup.commutator_le]
      intro α _ β _
      rw [commutatorElement_def]
      exact OuterDerived.commutator_mem_linearAutGroup (by norm_num) α β
    refine noSzSection_of_commutator_le hcomm ?_
    set c : GL (Fin 3) (GaloisField p' e) →* linearAutGroup 3 (GaloisField p' e) :=
      (conjAut 3 (GaloisField p' e)).codRestrict _ conjAut_mem_linearAutGroup with hc
    have hcs : Function.Surjective c := by
      rintro ⟨x, hx⟩
      have hle : linearAutGroup 3 (GaloisField p' e) ≤ (conjAut 3 (GaloisField p' e)).range :=
        (Subgroup.closure_le _).mpr fun y ⟨g, hg⟩ => ⟨g, hg⟩
      obtain ⟨g, hg⟩ := hle hx
      exact ⟨g, Subtype.ext hg⟩
    exact noSzSection_of_surjective c hcs (hGL _)
  · by_cases hq2 : 2 < p' ^ e
    ·
      have hU : UnitaryFieldData p' e (GaloisField p' (2 * e)) :=
        (Sec13.piField_galoisField_two p' e he).unitary
      obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU hU
      refine noSzSection_mulAut_of_mulEquiv (φ.trans ψ.symm) ?_
      refine noSzSection_of_commutator_le (commutator_le_psuConj_range hU hq2) ?_
      refine noSzSection_of_surjective (psuConj hU).rangeRestrict
        (psuConj hU).rangeRestrict_surjective ?_
      exact noSzSection_of_injective (unitaryIsom3 hU).subtype (unitaryIsom3 hU).subtype_injective
        (hGL _)
    ·
      have h2 : p' ^ e = 2 := by
        have : 2 ≤ p' ^ e := le_trans (Fact.out : p'.Prime).two_le (Nat.le_self_pow (by omega) _)
        omega
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two (Fact.out : Nat.Prime p') h2
      have hU : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
        (Sec13.piField_galoisField_two 2 1 le_rfl).unitary
      obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU hU
      have hcard : Nat.card T = 72 := by
        rw [Nat.card_congr (φ.trans ψ.symm).toEquiv, card_unitaryPSU_three_eq hU]
        decide
      have := hU.finite
      have : Finite T := Finite.of_equiv _ (φ.trans ψ.symm).symm.toEquiv
      exact noSzSection_mulAut_of_card_seventyTwo hcard

end CFSG.RankThree.PartTwo.Sec16
