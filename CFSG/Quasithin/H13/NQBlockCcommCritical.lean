module

public import CFSG.Quasithin.H13.NQBlockCcommFittingCores
public import CFSG.Quasithin.H13.NQBlockCcommCommonKernels
public import CFSG.Quasithin.H13.NQBlockCcommKernelGeneration
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwoAction

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

@[expose] noncomputable def criticalAction {L : Type*} [Group L] {Q : Subgroup L} [Q.Normal]
    (D : Subgroup Q) [D.Characteristic] : L →* MulAut (D ⧸ frattini D) :=
  (frattiniAction D).comp MulAut.conjNormal

structure IsCriticalData {L : Type*} [Group L] (r : ℕ) (Q : Subgroup L) [Q.Normal]
    (D : Subgroup Q) [D.Characteristic] : Prop where
  ne_bot : D ≠ ⊥
  pow_eq_one : ∀ x ∈ D, x ^ r = 1
  commutator_le : ⁅D, ⊤⁆ ≤ D ⊓ centralizer (D : Set Q)
  torsion : ∀ x ∈ centralizer (D : Set Q), orderOf x = r → x ∈ D
  ker_isPGroup : IsPGroup r (frattiniAction D).ker
  card_quotient : Nat.card (D ⧸ frattini D) = r ^ 2
  five_le : 5 ≤ r
  range_ne_bot : (criticalAction D).range ≠ ⊥
  isQuasisimple : CFSG.IsQuasisimple (criticalAction D).range
  irreducible : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = r →
    ∃ g ∈ (criticalAction D).range, ∃ u ∈ U, g u ∉ U
  mem_center_iff : ∀ g : (criticalAction D).range, g ∈ center (criticalAction D).range ↔
    (g : MulAut (D ⧸ frattini D)) = 1 ∨ ∀ w, (g : MulAut (D ⧸ frattini D)) w = w⁻¹
  inv_mem : ∃ g ∈ (criticalAction D).range, g ≠ 1 ∧ ∀ w, g w = w⁻¹
  card_center : Nat.card (center (criticalAction D).range) = 2
  projective : ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = r ∨ s = 5) ∧
    Nonempty ((criticalAction D).range ⧸ center (criticalAction D).range ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))
  shape : (IsElementaryAbelian r D ∧ Nat.card D = r ^ 2) ∨
    (¬ IsMulCommutative D ∧ Nat.card D = r ^ 3 ∧ frattini D = center D ∧
      Nat.card (frattini D) = r)

theorem exists_inv_mem_of_perfect
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {W : Type*}
    [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W = p ^ 2) (J : Subgroup (MulAut W)) [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    ∃ g ∈ J, g ≠ 1 ∧ ∀ w, g w = w⁻¹ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hcard
  set ψ := elemAutEquivGL e with hψ
  set J' := J.map ψ.toMonoidHom with hJ'
  have : Group.IsPerfect J' := Group.IsPerfect.map _
  have hJ'ne : J' ≠ ⊥ := by
    rw [hJ', Ne, map_eq_bot_iff_of_injective _ ψ.injective]
    exact hJ
  obtain ⟨g, hg, hgψ⟩ := mem_map.mp (neg_one_mem_of_perfect hp2 J' hJ'ne)
  have hinv := (elemAutEquivGL_eq_neg_one_iff e g).mp hgψ
  refine ⟨g, hg, fun h1 => ?_, hinv⟩
  have hw1 : ∀ w : W, w = 1 := by
    intro w
    have h2 : w * w = 1 := by
      have h3 := hinv w
      rw [h1, MulAut.one_apply] at h3
      calc w * w = w * w⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel w
    have h3 : orderOf w ∣ Nat.gcd p 2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow w))
      (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2))
    rw [(Nat.coprime_primes hp.out Nat.prime_two).mpr hp2, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have h4 : Nat.card W = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hw1 a).trans (hw1 b).symm⟩, ⟨1⟩⟩
  rw [hcard] at h4
  have := Nat.one_lt_pow two_ne_zero hp.out.one_lt
  omega

theorem card_center_eq_two {W : Type*} [Group W] (J : Subgroup (MulAut W))
    (hcen : ∀ g : J, g ∈ center J ↔ (g : MulAut W) = 1 ∨ ∀ w, (g : MulAut W) w = w⁻¹)
    {g₀ : MulAut W} (hg₀ : g₀ ∈ J) (hg₀1 : g₀ ≠ 1) (hg₀inv : ∀ w, g₀ w = w⁻¹) :
    Nat.card (center J) = 2 := by
  rw [Nat.card_eq_two_iff]
  have hz : (⟨g₀, hg₀⟩ : J) ∈ center J := (hcen _).mpr (Or.inr hg₀inv)
  refine ⟨1, ⟨⟨g₀, hg₀⟩, hz⟩, fun h => hg₀1 ?_, ?_⟩
  · exact (congrArg (fun z : center J => ((z : J) : MulAut W)) h).symm
  · ext ⟨⟨g, hg⟩, hgz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hcen ⟨g, hg⟩).mp hgz with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext (MulEquiv.ext fun w => (h w).trans (hg₀inv w).symm))

theorem isCComponent_top_of_isCComponent {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.IsCComponent L) : CFSG.IsCComponent (⊤ : Subgroup L) := by
  obtain ⟨hL1, hLp, hLs, hLmin⟩ := hL
  have hmt : (⊤ : Subgroup L).map L.subtype = L := by rw [Subgroup.map_top, range_subtype]
  refine ⟨fun h => hL1 ?_, ?_, IsSubnormal.top, fun K hK hK1 hKp hKs => ?_⟩
  · rw [← hmt, h, Subgroup.map_bot]
  · apply map_injective L.subtype_injective
    rw [map_commutator, hmt, hLp]
  · refine hLmin (K.map L.subtype) ?_ ?_ ?_ (hKs.trans' hLs)
    · exact lt_of_lt_of_eq ((map_lt_map_iff_of_injective L.subtype_injective).mpr hK) hmt
    · exact fun h => hK1 ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp h)
    · rw [← map_commutator, hKp]

section Critical

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem conj_eq_of_conjNormal_eq_one {Q : Subgroup L} [Q.Normal] {g : L}
    (hg : (MulAut.conjNormal g : MulAut Q) = 1) (y : L) (hy : y ∈ Q) : g * y * g⁻¹ = y := by
  have h1 := congrArg (fun σ : MulAut Q => ((σ ⟨y, hy⟩ : Q) : L)) hg
  simpa using h1

theorem critical_data
    [Group.IsPerfect L] {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup r Q) (hrank : CFSG.pRank r Q ≤ 2)
    (hact : (MulAut.conjNormal : L →* MulAut Q) ≠ 1) :
    ∃ (D : Subgroup Q) (_ : D.Characteristic), IsCriticalData r Q D := by
  have hQnt : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hact
    ext l x
    exact congrArg Subtype.val (Subsingleton.elim _ _)
  obtain ⟨D, hDc, hDne, hexp, hDZ, htors, hker⟩ := supercritical_witness hr2 hQ
  have hrank' : CFSG.Open.pRank r (⊤ : Subgroup Q) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank
  obtain ⟨hW2, hJne, hJperf, hirr, h5, hJq, hcen, hs, hDstr⟩ :=
    critical_rank_two_action_recognition hr2 hQ hrank' D hexp hker MulAut.conjNormal hact
      (criticalAction D).range rfl
  have hDp : IsPGroup r D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  obtain ⟨g₀, hg₀, hg₀1, hg₀inv⟩ := exists_inv_mem_of_perfect hr2 hWcomm hWpow hW2 _ hJne
  refine ⟨D, hDc, ⟨hDne, hexp, hDZ, htors, hker, hW2, h5, hJne,
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJq, hirr, hcen, ⟨g₀, hg₀, hg₀1, hg₀inv⟩,
    card_center_eq_two _ hcen hg₀ hg₀1 hg₀inv, hs, ?_⟩⟩
  rcases hDstr with ⟨hab, hcard⟩ | h
  · left
    refine ⟨{ toIsMulCommutative := hab, exponent_dvd_p := ?_ }, hcard⟩
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, hexp _ x.2, OneMemClass.coe_one])
  · exact Or.inr h

theorem fitting_eq_iSup_pCore_fittingPrimes :
    CFSG.fittingSubgroup L =
      ⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors, CFSG.pCore (p : ℕ) L := by
  apply le_antisymm
  · intro x hx
    have hK : (⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        CFSG.pCore (p : ℕ) L).subgroupOf (CFSG.fittingSubgroup L) = ⊤ :=
      eq_top_of_forall_sylow_le _ fun r _ S => by
        by_cases hr : r ∣ Nat.card (CFSG.fittingSubgroup L)
        · intro y hy
          rw [mem_subgroupOf]
          have hyr : (y : L) ∈ CFSG.pCore r L := by
            rw [← sylow_fitting_map_eq_pCore S]
            exact ⟨y, hy, rfl⟩
          have hrmem : r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨Fact.out, hr, Nat.card_pos.ne'⟩
          exact le_iSup (fun p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors =>
            CFSG.pCore (p : ℕ) L) ⟨r, hrmem⟩ hyr
        · have h1 : (S : Subgroup (CFSG.fittingSubgroup L)) = ⊥ := by
            rw [← card_eq_one, S.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hr,
              pow_zero]
          rw [h1]
          exact bot_le
    have h1 : (⟨x, hx⟩ : CFSG.fittingSubgroup L) ∈
        (⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
          CFSG.pCore (p : ℕ) L).subgroupOf (CFSG.fittingSubgroup L) := by
      rw [hK]
      exact mem_top _
    exact h1
  · refine iSup_le fun p => ?_
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact CFSG.pCore_le_fitting L p

omit [Finite L] in
theorem pCore_commute_fittingPrimes :
    Pairwise fun p q : (Nat.card (CFSG.fittingSubgroup L)).primeFactors =>
      ∀ x y : L, x ∈ CFSG.pCore (p : ℕ) L → y ∈ CFSG.pCore (q : ℕ) L → Commute x y := by
  intro p q hpq x y hx hy
  have hne : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
  have hc := (CFSG.LocalCores.distinct_prime_cores_commute (G := L)
    (Nat.prime_of_mem_primeFactors p.2) (Nat.prime_of_mem_primeFactors q.2) hne).2
  have hmem : ⁅x, y⁆ ∈ ⁅CFSG.pCore (p : ℕ) L, CFSG.pCore (q : ℕ) L⁆ :=
    commutator_mem_commutator hx hy
  rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem iSupIndep_pCore_fittingPrimes :
    iSupIndep fun p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors =>
      CFSG.pCore (p : ℕ) L := by
  classical
  have : ∀ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      Fintype (CFSG.pCore (p : ℕ) L) := fun p => Fintype.ofFinite _
  refine Subgroup.independent_of_coprime_order pCore_commute_fittingPrimes fun p q hpq => ?_
  have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
  show Nat.Coprime (Fintype.card (CFSG.pCore (p : ℕ) L)) (Fintype.card (CFSG.pCore (q : ℕ) L))
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact IsPGroup.coprime_card_of_ne _ _ (fun h => hpq (Subtype.ext h)) _ _ CFSG.pCore_isPGroup
    CFSG.pCore_isPGroup

theorem pCore_commutator_eq_of_fitting {r : ℕ}
    (hr : r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors)
    (hF : ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ = CFSG.fittingSubgroup L) :
    ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L := by
  classical
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  set r' : (Nat.card (CFSG.fittingSubgroup L)).primeFactors := ⟨r, hr⟩ with hr'
  set O : Subgroup L := ⨆ (j : (Nat.card (CFSG.fittingSubgroup L)).primeFactors) (_ : j ≠ r'),
    CFSG.pCore (j : ℕ) L with hO
  have hOn : O.Normal := by
    rw [hO]
    infer_instance
  have hdisj : CFSG.pCore r L ⊓ O = ⊥ := (iSupIndep_pCore_fittingPrimes (L := L) r').eq_bot
  have hFle : CFSG.fittingSubgroup L ≤ CFSG.pCore r L ⊔ O := by
    rw [fitting_eq_iSup_pCore_fittingPrimes]
    refine iSup_le fun j => ?_
    by_cases hj : j = r'
    · rw [hj]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  set C := ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ with hC
  have hCle : C ≤ CFSG.pCore r L := commutator_le_left _ _
  have hFC : CFSG.fittingSubgroup L ≤ C ⊔ O := by
    calc CFSG.fittingSubgroup L = ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ := hF.symm
      _ ≤ ⁅CFSG.pCore r L ⊔ O, (⊤ : Subgroup L)⁆ := commutator_mono hFle le_rfl
      _ ≤ C ⊔ O := by
        rw [commutator_le]
        intro x hx l _
        have hx' : x ∈ ((CFSG.pCore r L ⊔ O : Subgroup L) : Set L) := hx
        rw [mul_normal] at hx'
        obtain ⟨a, ha, o, ho, rfl⟩ := hx'
        have h1 : ⁅a * o, l⁆ = (a * (o * (l * o⁻¹ * l⁻¹)) * a⁻¹) * ⁅a, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        refine mul_mem (mem_sup_right ?_) (mem_sup_left (commutator_mem_commutator ha (mem_top l)))
        exact hOn.conj_mem _ (mul_mem ho (hOn.conj_mem _ (inv_mem ho) l)) a
  refine le_antisymm hCle fun a ha => ?_
  have h1 : a ∈ ((C ⊔ O : Subgroup L) : Set L) := hFC (CFSG.pCore_le_fitting L r ha)
  rw [mul_normal] at h1
  obtain ⟨c, hc, o, ho, hco⟩ := h1
  have hco' : c * o = a := hco
  have hoQ : o ∈ CFSG.pCore r L := by
    have e : o = c⁻¹ * a := by
      rw [← hco']
      group
    rw [e]
    exact mul_mem (inv_mem (hCle hc)) ha
  have ho1 : o = 1 := by
    have h2 : o ∈ CFSG.pCore r L ⊓ O := mem_inf.mpr ⟨hoQ, ho⟩
    rwa [hdisj, mem_bot] at h2
  rw [← hco', ho1, mul_one]
  exact hc

theorem le_fitting_of_primewise (K : Subgroup L) [K.Normal]
    (hFK : CFSG.fittingSubgroup L ≤ K)
    (hC : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L)
    (hact : ∀ q : ℕ, q.Prime → q ∣ Nat.card (CFSG.fittingSubgroup L) → ∀ h ∈ K, ∃ k : ℕ,
      ∀ y ∈ CFSG.pCore q L, h ^ q ^ k * y * (h ^ q ^ k)⁻¹ = y) :
    K ≤ CFSG.fittingSubgroup L := by
  classical
  set N : Subgroup K := (CFSG.fittingSubgroup L).subgroupOf K with hN
  have eN : N ≃* CFSG.fittingSubgroup L := subgroupOfEquivOfLe hFK
  have hNnil : Group.IsNilpotent N :=
    Group.nilpotent_of_surjective eN.symm.toMonoidHom eN.symm.surjective
  have hNcard : Nat.card N = Nat.card (CFSG.fittingSubgroup L) := Nat.card_congr eN.toEquiv
  have hCN : centralizer (N : Set K) ≤ N := by
    intro x hx
    rw [hN, mem_subgroupOf]
    apply hC
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := mem_centralizer_iff.mp hx ⟨f, hFK hf⟩
      (show (⟨f, hFK hf⟩ : K) ∈ N by rw [hN, mem_subgroupOf]; exact hf)
    exact congrArg Subtype.val h1
  have hnil : Group.IsNilpotent K := by
    refine nilpotent_primewise_action_criterion N hNnil hCN fun q hq hqN Q h => ?_
    rw [hNcard] at hqN
    obtain ⟨k, hk⟩ := hact q hq hqN h h.2
    refine ⟨k, fun x hx => Subtype.ext ?_⟩
    have : Fact q.Prime := ⟨hq⟩
    have hxq : (x : L) ∈ CFSG.pCore q L := by
      set P : Subgroup L := ((Q : Subgroup N).map N.subtype).map K.subtype with hP
      have hPF : P ≤ CFSG.fittingSubgroup L := by
        rintro _ ⟨y, ⟨z, -, rfl⟩, rfl⟩
        exact z.2
      have hPq : IsPGroup q P := (Q.isPGroup'.map _).map _
      obtain ⟨S, hS⟩ :=
        (hPq.of_equiv (subgroupOfEquivOfLe hPF).symm :
          IsPGroup q (P.subgroupOf (CFSG.fittingSubgroup L))).exists_le_sylow
      rw [← sylow_fitting_map_eq_pCore S]
      exact ⟨⟨x, hPF ⟨x, hx, rfl⟩⟩, hS (mem_subgroupOf.mpr ⟨x, hx, rfl⟩), rfl⟩
    simpa using hk x hxq
  exact CFSG.LocalCores.fitting_characteristic.2.2 K inferInstance hnil

theorem fitting_le_ker_of_quasisimple {J : Type*} [Group J] (ρ : L →* J)
    (hJ : CFSG.IsQuasisimple ρ.range) (hZ : Nat.card (center ρ.range) = 2)
    (hodd : Odd (Nat.card (CFSG.fittingSubgroup L))) : CFSG.fittingSubgroup L ≤ ρ.ker := by
  set B := (CFSG.fittingSubgroup L).map ρ.rangeRestrict with hB
  have hBn : B.Normal := CFSG.fittingSubgroup_normal.map _ ρ.rangeRestrict_surjective
  have hBs : Group.IsSolvable B := Group.isSolvable_of_surjective
    (f := ρ.rangeRestrict.subgroupMap (CFSG.fittingSubgroup L))
    (ρ.rangeRestrict.subgroupMap_surjective _)
  have hBZ := le_center_of_isSolvable_of_isQuasisimple hJ B hBs
  have h1 : Nat.card B ∣ 2 := hZ ▸ card_dvd_of_le hBZ
  have h2 : Nat.card B ∣ Nat.card (CFSG.fittingSubgroup L) := card_map_dvd _ _
  have h3 : Nat.card B = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  have hB1 : B = ⊥ := card_eq_one.mp h3
  intro x hx
  have h4 : ρ.rangeRestrict x ∈ B := ⟨x, hx, rfl⟩
  rw [hB1, mem_bot] at h4
  rw [MonoidHom.mem_ker]
  exact congrArg Subtype.val h4

omit [Finite L] in
theorem commutator_eq_bot_of_conjNormal_eq_one {Q : Subgroup L} [Q.Normal]
    (h : (MulAut.conjNormal : L →* MulAut Q) = 1) : ⁅Q, (⊤ : Subgroup L)⁆ = ⊥ := by
  rw [eq_bot_iff, commutator_le]
  intro y hy l _
  rw [mem_bot, commutatorElement_def]
  have h1 := conj_eq_of_conjNormal_eq_one (congrArg (· l) h) y⁻¹ (inv_mem hy)
  calc y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    _ = y * y⁻¹ := by rw [h1]
    _ = 1 := mul_inv_cancel y

end Critical

theorem all_prime_critical_actions_core
    {L : Type*} [Group L] [Finite L]
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hCF : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L)
    (hodd : Odd (Nat.card (CFSG.fittingSubgroup L)))
    (hcomm : ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ ≠ ⊥)
    (hcores : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      CFSG.pCore r L ≠ ⊥ ∧ CFSG.pRank r (CFSG.pCore r L) ≤ 2) :
    ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ = CFSG.fittingSubgroup L ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L ∧
        ∃ (D : Subgroup (CFSG.pCore r L)) (_ : D.Characteristic),
          IsCriticalData r (CFSG.pCore r L) D ∧
          (criticalAction D).ker = CFSG.fittingSubgroup L := by
  classical
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr (by
    rw [commutator_def]
    exact hLC.2.1)
  have hPiPrime : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors, r.Prime :=
    fun r hr => Nat.prime_of_mem_primeFactors hr
  have hPiOdd : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors, r ≠ 2 := by
    rintro r hr rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hr))
  set Act := (Nat.card (CFSG.fittingSubgroup L)).primeFactors.filter
    (fun r => (MulAut.conjNormal : L →* MulAut (CFSG.pCore r L)) ≠ 1) with hAct
  have hActPi : ∀ r ∈ Act, r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors :=
    fun r hr => (Finset.mem_filter.mp hr).1
  have hdata : ∀ i : Act, ∃ (D : Subgroup (CFSG.pCore (i : ℕ) L)) (_ : D.Characteristic),
      IsCriticalData (i : ℕ) (CFSG.pCore (i : ℕ) L) D := by
    rintro ⟨r, hr⟩
    obtain ⟨hrPi, hract⟩ := Finset.mem_filter.mp hr
    have : Fact r.Prime := ⟨hPiPrime r hrPi⟩
    exact critical_data (hPiOdd r hrPi) (CFSG.pCore r L) CFSG.pCore_isPGroup
      (hcores r hrPi).2 hract
  choose D hDc hDdata using hdata
  have hActne : Nonempty Act := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hcomm
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer,
      fitting_eq_iSup_pCore_fittingPrimes]
    refine iSup_le fun p => ?_
    have hp1 : (MulAut.conjNormal : L →* MulAut (CFSG.pCore (p : ℕ) L)) = 1 := by
      by_contra hp1
      exact hne.false ⟨p, Finset.mem_filter.mpr ⟨p.2, hp1⟩⟩
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    have := commutator_eq_bot_of_conjNormal_eq_one hp1
    rwa [commutator_comm] at this
  have i₀ : Act := Classical.choice hActne
  set ρ : ∀ i : Act, L →* MulAut (D i ⧸ frattini (D i)) := fun i => criticalAction (D i)
    with hρ
  have hs := fun i : Act => (hDdata i).projective
  choose s hsp hs5 _hsr hψ using hs
  set eT : (⊤ : Subgroup L) ≃* L := topEquiv with heT
  obtain ⟨hkerEq, -⟩ := common_critical_kernels (⊤ : Subgroup L) hLC
    (fun i => (ρ i).rangeRestrict.comp eT.toMonoidHom)
    (fun i => (ρ i).rangeRestrict_surjective.comp eT.surjective)
    (fun i => (hDdata i).isQuasisimple) (fun i => (hDdata i).card_center) s hsp hs5
    (fun i => (hψ i).some)
  have hkerEq' : ∀ i j : Act, (ρ i).ker = (ρ j).ker := fun i j => by
    have h1 := hkerEq i j
    rw [← MonoidHom.comap_ker, ← MonoidHom.comap_ker] at h1
    have h2 := comap_injective eT.surjective h1
    rwa [MonoidHom.ker_rangeRestrict, MonoidHom.ker_rangeRestrict] at h2
  have hFK : ∀ i : Act, CFSG.fittingSubgroup L ≤ (ρ i).ker := fun i =>
    fitting_le_ker_of_quasisimple (ρ i) (hDdata i).isQuasisimple (hDdata i).card_center hodd
  have hKF : (ρ i₀).ker = CFSG.fittingSubgroup L := by
    refine le_antisymm ?_ (hFK i₀)
    refine le_fitting_of_primewise (ρ i₀).ker (hFK i₀) hCF fun q hq hqF h hh => ?_
    have hqPi : q ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqF, Nat.card_pos.ne'⟩
    by_cases hqact : (MulAut.conjNormal : L →* MulAut (CFSG.pCore q L)) = 1
    · refine ⟨0, fun y hy => ?_⟩
      rw [pow_zero, pow_one]
      exact conj_eq_of_conjNormal_eq_one (congrArg (· h) hqact) y hy
    · have hqA : q ∈ Act := Finset.mem_filter.mpr ⟨hqPi, hqact⟩
      have hh' : h ∈ (ρ ⟨q, hqA⟩).ker := by rw [hkerEq' ⟨q, hqA⟩ i₀]; exact hh
      have hσ : (MulAut.conjNormal h : MulAut (CFSG.pCore q L)) ∈
          (frattiniAction (D ⟨q, hqA⟩)).ker := hh'
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨k, hk⟩ := (hDdata ⟨q, hqA⟩).ker_isPGroup ⟨_, hσ⟩
      refine ⟨k, fun y hy => conj_eq_of_conjNormal_eq_one ?_ y hy⟩
      rw [map_pow]
      exact congrArg Subtype.val hk
  have hKFall : ∀ i : Act, (ρ i).ker = CFSG.fittingSubgroup L := fun i =>
    (hkerEq' i i₀).trans hKF
  have : Fact (s i₀).Prime := ⟨hsp i₀⟩
  set e : L ⧸ CFSG.fittingSubgroup L ≃* (ρ i₀).range :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [MonoidHom.ker_rangeRestrict, hKF])).trans
      (QuotientGroup.quotientKerEquivOfSurjective (ρ i₀).rangeRestrict
        (ρ i₀).rangeRestrict_surjective) with he
  have hcenmap : (center (L ⧸ CFSG.fittingSubgroup L)).map e.toMonoidHom =
      center (ρ i₀).range := map_center_eq e
  have hFL : ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ = CFSG.fittingSubgroup L := by
    refine perfect_odd_kernel_generation (CFSG.fittingSubgroup L) hodd
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hDdata i₀).isQuasisimple) ?_ (hs5 i₀)
      ((QuotientGroup.congr _ _ e hcenmap).trans (hψ i₀).some)
    rw [← (hDdata i₀).card_center, ← hcenmap, card_map_of_injective e.injective]
  refine ⟨hFL, fun r hr => ?_⟩
  have hQr := pCore_commutator_eq_of_fitting hr hFL
  have hrA : r ∈ Act := by
    refine Finset.mem_filter.mpr ⟨hr, fun hract => (hcores r hr).1 ?_⟩
    rw [← hQr]
    exact commutator_eq_bot_of_conjNormal_eq_one hract
  exact ⟨hQr, D ⟨r, hrA⟩, hDc ⟨r, hrA⟩, hDdata ⟨r, hrA⟩, hKFall ⟨r, hrA⟩⟩

theorem all_prime_critical_actions {G : Type*} [Group G] [Finite G]
    (hSQT : CFSG.IsStronglyQuasithin G) (hO2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G}
    (hL : CFSG.IsCComponent L) (hq : ¬ CFSG.IsQuasisimple L) :
    ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ = CFSG.fittingSubgroup L ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L ∧
        ∃ (D : Subgroup (CFSG.pCore r L)) (_ : D.Characteristic),
          IsCriticalData r (CFSG.pCore r L) D ∧
          (criticalAction D).ker = CFSG.fittingSubgroup L := by
  obtain ⟨hFstar, -, -, hodd, hcomm, -, -, hcores⟩ := odd_Fitting_cores hSQT hO2 hL hq
  have hLperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL.2.1
  have hCF : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L := by
    have h1 := CFSG.centralizer_generalizedFitting_le L
    rwa [hFstar] at h1
  exact all_prime_critical_actions_core (isCComponent_top_of_isCComponent hL) hCF hodd hcomm
    fun r hr => ⟨(hcores r hr).1, (hcores r hr).2.2.2⟩

end CFSG.Quasithin.H13.NQBlock
