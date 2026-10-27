module

public import CFSG.RankThree.PartTwo.Sec10.Item102
public import CFSG.RankThree.PartTwo.Sec11.Item112
public import CFSG.RankThree.PartTwo.Sec11.Item116Points
public import CFSG.RankThree.PartTwo.KFacts.K73L27

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Lemmas

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_left_eq {Z T X : Subgroup G} (hZT : Z ≤ Subgroup.centralizer (T : Set G))
    (hZX : Z ≤ Subgroup.centralizer (X : Set G)) :
    ⁅Z ⊔ T, X⁆ = ⁅T, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro y hy x hx
    have hZN : Z ≤ Subgroup.normalizer (T : Set G) :=
      hZT.trans (Subgroup.centralizer_le_normalizer _)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Z T hZN] at hy
    obtain ⟨z, hz, t, ht, rfl⟩ := hy
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.mp (hZX hz) x hx).symm
    have hzt : z * t = t * z := (Subgroup.mem_centralizer_iff.mp (hZT hz) t ht).symm
    have e : ⁅z * t, x⁆ = ⁅t, x⁆ := by
      have hc : Commute z (t * x * t⁻¹) :=
        ((Commute.mul_right (hzt : Commute z t) (hzx : Commute z x)).mul_right
          (Commute.inv_right (hzt : Commute z t)))
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc z * t * x * (t⁻¹ * z⁻¹) * x⁻¹ = z * (t * x * t⁻¹) * z⁻¹ * x⁻¹ := by group
        _ = t * x * t⁻¹ * x⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.commutator_mem_commutator ht hx
  · exact Subgroup.commutator_mono le_sup_right le_rfl


omit [Finite G] in
theorem closure_inf_le_eBase {e t : G} (hW : KFacts.WreathData e t) {L : Subgroup G}
    (hEL : KFacts.eBase e t ≤ L) (htL : t ∉ L) :
    Subgroup.closure {e, t} ⊓ L ≤ KFacts.eBase e t := by
  rintro x ⟨hxT, hxL⟩
  obtain ⟨w, rfl⟩ := hW.range_hom ▸ hxT
  have hval : hW.hom w = KFacts.eVec e t (KFacts.wVec w) *
      t ^ (Multiplicative.toAdd w.right).val := rfl
  rw [hval] at hxL ⊢
  set k := (Multiplicative.toAdd w.right).val with hk
  have hvL : KFacts.eVec e t (KFacts.wVec w) ∈ L := hEL (KFacts.eVec_mem_eBase _)
  have htk : t ^ k ∈ L := by
    have := L.mul_mem (L.inv_mem hvL) hxL
    simpa [mul_assoc] using this
  have hk3 : k < 3 := ZMod.val_lt _
  have hk0 : k = 0 := by
    by_contra hk0
    apply htL
    have ht3 := hW.pow_t
    obtain hk1 | hk2 : k = 1 ∨ k = 2 := by omega
    · rw [hk1, pow_one] at htk
      exact htk
    · rw [hk2] at htk
      have : t = (t ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ht3, one_mul, pow_one]
      rw [this]
      exact L.pow_mem htk 2
  rw [hk0, pow_zero, mul_one]
  exact KFacts.eVec_mem_eBase _

theorem commutator_commutator_omega_eq {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R : Subgroup G} (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hdo : orderOf d = 3)
    (hΩ : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} = Subgroup.zpowers a ⊔ sec10D c R L)
    {e : G} (heRL : e ∈ R ⊓ L) (hW : KFacts.WreathData e a)
    (hcl : Subgroup.closure {e, a} = Subgroup.zpowers a ⊔ (R ⊓ L)) :
    ⁅⁅Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}, Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆,
      Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆ = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hAR := le_of_hyp91 h.toHyp91
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcT : Subgroup.zpowers c ≤ Subgroup.centralizer (Subgroup.closure ({e, a} : Set G)) := by
    rw [Subgroup.zpowers_le, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hLc heRL.2)
    · exact hcomm _ haA c hcA
  have hΩeq : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} =
      Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) := by
    rw [hΩ, sec10D, hcl, ← sup_assoc, sup_comm (Subgroup.zpowers a), sup_assoc]
  have hcc : Subgroup.zpowers c ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (Commute.refl c) k)
  have hcΩ : Subgroup.zpowers c ≤
      Subgroup.centralizer ((Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) :
        Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hcc) (Subgroup.le_centralizer_iff.mp hcT)
  have hTT : ⁅Subgroup.closure ({e, a} : Set G), Subgroup.closure ({e, a} : Set G)⁆ ≤
      Subgroup.closure ({e, a} : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  have hcTT : Subgroup.zpowers c ≤ Subgroup.centralizer
      ((⁅Subgroup.closure ({e, a} : Set G), Subgroup.closure ({e, a} : Set G)⁆ :
        Subgroup G) : Set G) :=
    hcT.trans (Subgroup.centralizer_le hTT)
  have h1 : ⁅Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G),
      Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G)⁆ =
        ⁅Subgroup.closure ({e, a} : Set G), Subgroup.closure ({e, a} : Set G)⁆ := by
    rw [commutator_sup_left_eq hcT hcΩ, Subgroup.commutator_comm,
      commutator_sup_left_eq hcT hcT]
  have h2 : ⁅⁅Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G),
      Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G)⁆,
        Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G)⁆ =
      ⁅⁅Subgroup.closure ({e, a} : Set G), Subgroup.closure ({e, a} : Set G)⁆,
        Subgroup.closure ({e, a} : Set G)⁆ := by
    rw [h1, Subgroup.commutator_comm, commutator_sup_left_eq hcT hcTT, Subgroup.commutator_comm]
  rw [hΩeq, h2, hW.commutator_commutator]
  have haL : a ∉ L := by
    intro haL
    obtain ⟨haN, hout⟩ := h.toHyp81.inducesOuterTheta
    apply hout
    rw [show (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, Subgroup.le_normalizer haL⟩ from
      rfl, Sec11.thetaQuotMulAut_compAction_of_mem L haL]
    exact ⟨_, rfl⟩
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hEL : KFacts.eBase e a ≤ L := by
    rw [KFacts.eBase, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have hai : ∀ i : ℕ, a ^ i ∈ Subgroup.normalizer (L : Set G) := fun i => Subgroup.pow_mem _ haN i
    rcases hy with rfl | rfl | rfl <;>
      exact (Subgroup.mem_normalizer_iff.mp (hai _) e).mp heRL.2
  have hdT : d ∈ Subgroup.closure ({e, a} : Set G) := by
    rw [hcl]
    exact Subgroup.mem_sup_right ⟨hAR hdAL.1, hdAL.2⟩
  have hdE : d ∈ KFacts.eBase e a := closure_inf_le_eBase hW hEL haL ⟨hdT, hdAL.2⟩
  have hdC : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a haA d hdAL.1).symm
  have haT : a ∈ Subgroup.closure ({e, a} : Set G) := Subgroup.subset_closure (by simp)
  have haE : a ∉ KFacts.eBase e a := hW.not_mem
  have hcen := hW.eBase_inf_centralizer haT haE
  have hdz : d ∈ Subgroup.zpowers (KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2) :=
    hcen ▸ ⟨hdE, hdC⟩
  have hd3 : d ^ 3 = 1 := hexp d hdAL.1
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    exact absurd hdo (by norm_num)
  obtain ⟨h01, h12, h02⟩ := KFacts.commute_eConj_two hW.pow_t hW.comm
  have hx3 : (KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2) ^ 3 = 1 := by
    rw [(h02.mul_left h12).mul_pow, h01.mul_pow,
      KFacts.eConj_pow_three hW.pow_e, KFacts.eConj_pow_three hW.pow_e,
      KFacts.eConj_pow_three hW.pow_e, one_mul, one_mul]
  have hle := Subgroup.zpowers_le.mpr hdz
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)

theorem normalizer_le_normalizer_zpowers_of_omega {R D : Subgroup G}
    (hD : ⁅⁅Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}, Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆,
      Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆ = D) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  intro n hn
  have hΩ : (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).map (MulAut.conj n) =
      Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyR, hy3⟩, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨(Subgroup.mem_normalizer_iff.mp hn y).mp hyR, ?_⟩
      change (n * y * n⁻¹) ^ 3 = 1
      rw [conj_pow, hy3]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hD, Subgroup.map_commutator,
    Subgroup.map_commutator, hΩ]


theorem exists_conj_eq_of_map_eq {X : Type*} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {P Q : Subgroup X} (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hPQ : P.map (QuotientGroup.mk' N) = Q.map (QuotientGroup.mk' N)) :
    ∃ x : X, Q = P.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQM : Q ≤ N ⊔ Q := le_sup_right
  have hPM : P ≤ N ⊔ Q := by
    intro p hp
    have h1 : QuotientGroup.mk' N p ∈ Q.map (QuotientGroup.mk' N) := hPQ ▸ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := h1
    have h2 : q⁻¹ * p ∈ N := by
      rw [← QuotientGroup.eq]
      exact hqp
    have h3 : p = q * (q⁻¹ * p) := by group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left h2)
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])
  have hrelQ : ¬ 3 ∣ Q.relIndex (N ⊔ Q) := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal]
    intro h3
    exact hN (h3.trans (Subgroup.index_dvd_card _))
  have hrel : P.relIndex (N ⊔ Q) = Q.relIndex (N ⊔ Q) := by
    have h1 := Subgroup.relIndex_mul_card P (N ⊔ Q)
    have h2 := Subgroup.relIndex_mul_card Q (N ⊔ Q)
    rw [inf_eq_left.mpr hPM, hP] at h1
    rw [inf_eq_left.mpr hQM, hQ] at h2
    omega
  have hSP : CFSG.ABGLocalTools.IsSylowOf 3 P (N ⊔ Q) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPM, hP3, hrel ▸ hrelQ⟩
  have hSQ : CFSG.ABGLocalTools.IsSylowOf 3 Q (N ⊔ Q) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQM, hQ3, hrelQ⟩
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSP hSQ
  refine ⟨k, ?_⟩
  ext x
  rw [hk x]
  constructor
  · intro hx
    refine ⟨k⁻¹ * x * k, hx, ?_⟩
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  · rintro ⟨y, hy, rfl⟩
    change k⁻¹ * (k * y * k⁻¹) * k ∈ P
    simpa [mul_assoc] using hy

theorem exists_conj_eq_of_card_eq_three_of_quot {L P Q : Subgroup G}
    (hK : ∀ P Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L), Nat.card P = 3 → Nat.card Q = 3 →
      ∃ x, Q = P.map (MulAut.conj x).toMonoidHom)
    (hPL : P ≤ L) (hQL : Q ≤ L) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) :
    ∃ x ∈ L, Q = P.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  set π := QuotientGroup.mk' θ with hπ
  set PL := P.subgroupOf L with hPLdef
  set QL := Q.subgroupOf L with hQLdef
  have hPL3 : Nat.card PL = 3 := by
    rw [hPLdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hP]
  have hQL3 : Nat.card QL = 3 := by
    rw [hQLdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv, hQ]
  have himg : ∀ S : Subgroup L, Nat.card S = 3 → Nat.card (S.map π) = 3 := by
    intro S hS
    have h1 : Nat.card (S.map π) ∣ 3 := by
      have := Subgroup.card_map_dvd S π
      rwa [hS] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exfalso
      have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 1) (by rw [hS, pow_one])
      have hbot := KFacts.inf_eq_bot_of_coprime hS3 hθ3
      have hle : S ≤ θ := by
        intro y hy
        have : π y ∈ S.map π := ⟨y, hy, rfl⟩
        rw [Subgroup.card_eq_one.mp h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at this
        exact this
      rw [inf_eq_left.mpr hle] at hbot
      rw [hbot, Subgroup.card_bot] at hS
      norm_num at hS
    · exact h
  obtain ⟨xb, hxb⟩ := hK _ _ (himg PL hPL3) (himg QL hQL3)
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective θ xb
  have hmap : (PL.map (MulAut.conj x₀).toMonoidHom).map π =
      (PL.map π).map (MulAut.conj (π x₀)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hcard : Nat.card (PL.map (MulAut.conj x₀).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hPL3]
  obtain ⟨k, hk⟩ := exists_conj_eq_of_map_eq hθ3 hcard hQL3 (by rw [hmap, ← hxb])
  refine ⟨((k * x₀ : L) : G), (k * x₀).2, ?_⟩
  have hQeq : Q = QL.map L.subtype := by
    rw [hQLdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQL]
  have hPeq : P = PL.map L.subtype := by
    rw [hPLdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
  rw [hQeq, hk, hPeq, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem zpowers_eq_of_conj_eq {c d g' : G} {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hRd : R ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hg' : (Subgroup.zpowers c).map (MulAut.conj g').toMonoidHom = Subgroup.zpowers d) :
    Subgroup.zpowers c = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Hc := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHc
  set Hd := Subgroup.normalizer (Subgroup.zpowers d : Set G) with hHd
  have hmemd : ∀ y : G, y ∈ Subgroup.zpowers d ↔ g'⁻¹ * y * g' ∈ Subgroup.zpowers c := by
    intro y
    rw [← hg']
    constructor
    · rintro ⟨z, hz, rfl⟩
      change g'⁻¹ * (g' * z * g'⁻¹) * g' ∈ _
      simpa [mul_assoc] using hz
    · intro hy
      exact ⟨g'⁻¹ * y * g', hy, by change g' * (g'⁻¹ * y * g') * g'⁻¹ = y; group⟩
  have hconj : ∀ x : G, x ∈ Hd ↔ g'⁻¹ * x * g' ∈ Hc := by
    intro x
    simp only [hHd, hHc, Subgroup.mem_normalizer_iff]
    constructor
    · intro hx z
      have h1 := hx (g' * z * g'⁻¹)
      rw [hmemd, hmemd, show g'⁻¹ * (g' * z * g'⁻¹) * g' = z by group,
        show g'⁻¹ * (x * (g' * z * g'⁻¹) * x⁻¹) * g' =
          g'⁻¹ * x * g' * z * (g'⁻¹ * x * g')⁻¹ by group] at h1
      exact h1
    · intro hx y
      have h1 := hx (g'⁻¹ * y * g')
      rw [hmemd, hmemd]
      rw [show g'⁻¹ * x * g' * (g'⁻¹ * y * g') * (g'⁻¹ * x * g')⁻¹ =
        g'⁻¹ * (x * y * x⁻¹) * g' by group] at h1
      exact h1
  have hHdeq : Hd = Hc.map (MulAut.conj g').toMonoidHom := by
    ext x
    rw [hconj]
    constructor
    · intro hx
      exact ⟨g'⁻¹ * x * g', hx, by change g' * (g'⁻¹ * x * g') * g'⁻¹ = x; group⟩
    · rintro ⟨y, hy, rfl⟩
      change g'⁻¹ * (g' * y * g'⁻¹) * g' ∈ Hc
      simpa [mul_assoc] using hy
  have hcardHd : Nat.card Hd = Nat.card Hc := by
    rw [hHdeq, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hRd' : CFSG.ABGLocalTools.IsSylowOf 3 R Hd :=
    CFSG.ABGLocalTools.isSylowOf_of_card hRd (by rw [hR.card_eq, hcardHd])
  have hR'd : R.map (MulAut.conj g').toMonoidHom ≤ Hd := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hconj]
    change g'⁻¹ * (g' * r * g'⁻¹) * g' ∈ Hc
    simpa [mul_assoc] using hR.le hr
  have hR'syl : CFSG.ABGLocalTools.IsSylowOf 3 (R.map (MulAut.conj g').toMonoidHom) Hd :=
    CFSG.ABGLocalTools.isSylowOf_of_card hR'd (by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hR.card_eq, hcardHd])
  obtain ⟨n, hnHd, hn⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hRd' hR'syl
  have hzN : g'⁻¹ * n ∈ Subgroup.normalizer (R : Set G) := by
    apply Sec11.mem_normalizer_of_forall_conj_mem
    intro r hr
    have h1 : g' * r * g'⁻¹ ∈ R.map (MulAut.conj g').toMonoidHom := ⟨r, hr, rfl⟩
    have h2 := (hn _).mp h1
    rw [show (g'⁻¹ * n)⁻¹ * r * (g'⁻¹ * n) = n⁻¹ * (g' * r * g'⁻¹) * n by group]
    exact h2
  have hg'Hd : g' ∈ Hd := by
    have h1 := Hd.mul_mem (hNR hzN) (Hd.inv_mem hnHd)
    have h2 : g'⁻¹ = g'⁻¹ * n * n⁻¹ := by group
    rw [← h2] at h1
    simpa using Hd.inv_mem h1
  ext y
  have h1 := hmemd (g' * y * g'⁻¹)
  rw [show g'⁻¹ * (g' * y * g'⁻¹) * g' = y by group] at h1
  rw [← h1]
  exact (Subgroup.mem_normalizer_iff.mp hg'Hd y).symm

end Lemmas

section NotMem

variable {G : Type} [Group G] [Finite G]

theorem not_mem_of_sec10Std {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Sec10Std G A c L a R) : c ∉ L := by
  intro hcL
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  obtain ⟨eL⟩ := h.iso
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot (eL.trans (Sec4.projSLEquivPSL _))
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hcen : ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLc y.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have hθ : c ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨_, hcen, rfl⟩
  exact h.ne_one (Sec11.eq_one_of_mem_inSubgroup_theta hθ hc3)

end NotMem

theorem item103_of (h97 : Sec9.Item97) (h102 : Item102) : Item103 := by
  intro G _ _ A c L a R h g hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨d, hdL, hdo, -⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, -, -⟩ := h102 G A c L a R h
  have hD := commutator_commutator_omega_eq h hdL hdo hΩ heRL hW hcl
  have hNR := normalizer_le_normalizer_zpowers_of_omega hD
  have hRd : R ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun r hr =>
    hNR (Subgroup.le_normalizer hr)
  obtain ⟨eL⟩ := h.iso
  have hK : ∀ P Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L), Nat.card P = 3 →
      Nat.card Q = 3 → ∃ x, Q = P.map (MulAut.conj x).toMonoidHom := fun P Q hP hQ =>
    KFacts.exists_conj_eq_of_card_eq_three_of_mulEquiv_psl2_27
      (eL.trans (Sec4.projSLEquivPSL _)) hP hQ
  have hdLL : d ∈ L := by
    have : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    exact this.2
  have hgc3 : (g * c * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3]; group
  have hgc1 : g * c * g⁻¹ ≠ 1 := fun h1 => hc1 (by
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨ℓ, hℓL, hℓ⟩ := exists_conj_eq_of_card_eq_three_of_quot hK
    (P := Subgroup.zpowers (g * c * g⁻¹)) (Q := Subgroup.zpowers d)
    (Subgroup.zpowers_le.mpr hg) (Subgroup.zpowers_le.mpr hdLL)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hgc3 hgc1])
    (by rw [Nat.card_zpowers, hdo])
  have hg' : (Subgroup.zpowers c).map (MulAut.conj (ℓ * g)).toMonoidHom = Subgroup.zpowers d := by
    rw [hℓ, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    congr 1
    change ℓ * g * c * (ℓ * g)⁻¹ = ℓ * (g * c * g⁻¹) * ℓ⁻¹
    group
  have heq := zpowers_eq_of_conj_eq h.isSylowOf hRd hNR hg'
  apply not_mem_of_sec10Std h
  exact Subgroup.zpowers_le.mpr hdLL (heq ▸ Subgroup.mem_zpowers c)

end CFSG.RankThree.PartTwo.Sec10
