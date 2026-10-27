module

public import CFSG.Walter.Bender1970.S3.TransitivityTools
public import CFSG.Walter.Bender1970.S3.PCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
public import CFSG.Walter.Bender1970.S3.OStar

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

structure Bender37 (G : Type) [Group G] [Finite G] where
  hG : BenderCounterexample G
  t : G
  ht : orderOf t = 2
  H : Subgroup G
  hH : IsCoatom H
  hCH : Subgroup.centralizer ({t} : Set G) ≤ H
  p : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  V : Subgroup G
  hVP : V ≤ qCoreOf H p
  hVcomm : IsMulCommutative V
  hVexp : ∀ x ∈ V, x ^ p = 1
  hV3 : p ^ 3 ≤ Nat.card V
  htV : V ≤ Subgroup.centralizer ({t} : Set G)
  htF : generalizedFittingSubgroupOf H ≤ Subgroup.centralizer ({t} : Set G)
  hCV : Subgroup.centralizer (V : Set G) ≤ H

namespace Bender37

variable {G : Type} [Group G] [Finite G] (S : Bender37 G)

@[expose] def primes : Set ℕ := primesOfOrder (CFSG.fittingSubgroupOf S.H)

@[expose] def W : Subgroup G :=
  generalizedFittingSubgroupOf S.H ⊓ Subgroup.centralizer (S.V : Set G)

@[expose] def pieces (X : Subgroup G) : Set (Subgroup G) :=
  {P | (∃ q : ℕ, q.Prime ∧ q ∉ S.primes ∧ P = qCoreOf X q) ∨ (IsComponentOf P X ∧ ¬ P ≤ S.H)}

@[expose] def Q (X : Subgroup G) : Subgroup G := sSup (S.pieces X)

@[expose] def U : Set (Subgroup G) :=
  {K | K ≠ ⊤ ∧ S.W ≤ Subgroup.normalizer (K : Set G) ∧ ⁅K, Subgroup.zpowers S.t⁆ = K}

@[expose] def orbit (L : Subgroup G) : Subgroup G :=
  sSup {L' | ∃ w ∈ S.W, L' = L.map (MulAut.conj w).toMonoidHom}

theorem t_mul_t : S.t * S.t = 1 := by rw [← pow_two, ← S.ht, pow_orderOf_eq_one]

theorem t_mem_centralizer : S.t ∈ Subgroup.centralizer ({S.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem t_mem_H : S.t ∈ S.H := S.hCH S.t_mem_centralizer

theorem t_mem_centralizer_F :
    S.t ∈ Subgroup.centralizer (generalizedFittingSubgroupOf S.H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (S.htF hx)

theorem t_mem_F : S.t ∈ generalizedFittingSubgroupOf S.H :=
  Bender35.inf_centralizer_le_generalizedFitting S.H ⟨S.t_mem_H, S.t_mem_centralizer_F⟩

theorem t_mem_fitting : S.t ∈ CFSG.fittingSubgroupOf S.H := by
  refine generalizedFittingSubgroupOf_inf_centralizer_le S.H ⟨S.t_mem_F, ?_⟩
  exact Subgroup.centralizer_le (le_sup_right : componentLayerOf S.H ≤ _) S.t_mem_centralizer_F

theorem V_isPGroup : IsPGroup S.p S.V := (qCoreOf_isPGroup S.H S.p).to_le S.hVP

theorem p_dvd_card_V : S.p ∣ Nat.card S.V := by
  have : Fact S.p.Prime := ⟨S.hp⟩
  obtain ⟨k, hk⟩ := S.V_isPGroup.exists_card_eq
  have h3 := S.hV3
  rw [hk] at h3 ⊢
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have : k = 0 := by omega
    rw [this, pow_zero] at h3
    have := Nat.pow_le_pow_right S.hp.pos (show 1 ≤ 3 by norm_num)
    have := S.hp.one_lt
    nlinarith
  exact dvd_pow_self S.p (by omega)

theorem V_ne_bot : S.V ≠ ⊥ := by
  intro h
  have h1 := S.p_dvd_card_V
  rw [h, Subgroup.card_bot] at h1
  exact S.hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem odd_card_V : Odd (Nat.card S.V) := by
  have : Fact S.p.Prime := ⟨S.hp⟩
  obtain ⟨k, hk⟩ := S.V_isPGroup.exists_card_eq
  rw [hk]
  exact (S.hp.odd_of_ne_two S.hp2).pow

theorem V_le_fitting : S.V ≤ CFSG.fittingSubgroupOf S.H :=
  S.hVP.trans (qCoreOf_le_fittingSubgroupOf S.H S.p S.hp)

theorem V_le_F : S.V ≤ generalizedFittingSubgroupOf S.H := S.V_le_fitting.trans le_sup_left

theorem V_le_W : S.V ≤ S.W := by
  refine le_inf S.V_le_F fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (S.hVcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem W_le_F : S.W ≤ generalizedFittingSubgroupOf S.H := inf_le_left

theorem W_le_H : S.W ≤ S.H := S.W_le_F.trans (generalizedFittingSubgroupOf_isNormalIn S.H).1

theorem W_le_centralizer_V : S.W ≤ Subgroup.centralizer (S.V : Set G) := inf_le_right

theorem W_le_centralizer_t : S.W ≤ Subgroup.centralizer ({S.t} : Set G) := S.W_le_F.trans S.htF

theorem t_mem_W : S.t ∈ S.W := by
  refine ⟨S.t_mem_F, ?_⟩
  show S.t ∈ Subgroup.centralizer (S.V : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (S.htV hv)

theorem W_isSubnormal : (S.W.subgroupOf (generalizedFittingSubgroupOf S.H)).IsSubnormal := by
  refine isSubnormal_of_componentLayerOf_le (le_inf le_sup_right ?_) S.W_le_F
  exact (componentLayerOf_le_centralizer_fitting S.H).trans (Subgroup.centralizer_le S.V_le_fitting)

theorem inf_centralizer_W_le :
    generalizedFittingSubgroupOf S.H ⊓ Subgroup.centralizer (S.W : Set G) ≤ S.W :=
  fun _ hx => ⟨hx.1, Subgroup.centralizer_le S.V_le_W hx.2⟩

theorem W_isSubnormal_H : (S.W.subgroupOf S.H).IsSubnormal :=
  isSubnormal_subgroupOf_trans S.W_le_F S.W_isSubnormal
    (isSubnormal_subgroupOf_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn S.H))

theorem commutatorElement_mem_center {h : G} (hh : h ∈ S.H) :
    ⁅h, S.t⁆ ∈ generalizedFittingSubgroupOf S.H ⊓
      Subgroup.centralizer (generalizedFittingSubgroupOf S.H : Set G) := by
  set F := generalizedFittingSubgroupOf S.H
  have hFn := generalizedFittingSubgroupOf_isNormalIn S.H
  have hZ : S.t ∈ F ⊓ Subgroup.centralizer (F : Set G) := ⟨S.t_mem_F, S.t_mem_centralizer_F⟩
  have hN : h ∈ Subgroup.normalizer ((F ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) :=
    mem_normalizer_inf (le_normalizer_of_isNormalIn hFn hh)
      (Bender35.mem_normalizer_centralizer (le_normalizer_of_isNormalIn hFn hh))
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN _).mp hZ) (Subgroup.inv_mem _ hZ)

theorem eq_bot_of_le_commutator {K : Subgroup G} (hKH : K ≤ S.H)
    (hK : K ≤ ⁅K, Subgroup.zpowers S.t⁆) : K = ⊥ := by
  set F := generalizedFittingSubgroupOf S.H
  have h1 : ⁅K, Subgroup.zpowers S.t⁆ ≤ F ⊓ Subgroup.centralizer (F : Set G) :=
    commutator_zpowers_le_of_forall S.ht fun k hk => S.commutatorElement_mem_center (hKH hk)
  have h2 : ⁅K, Subgroup.zpowers S.t⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    intro k hk
    have hk' := h1 (hK hk)
    exact ((Subgroup.mem_centralizer_iff.mp hk'.2) S.t S.t_mem_F).symm
  exact le_bot_iff.mp (h2 ▸ hK)

theorem two_mem_primes : 2 ∈ S.primes := by
  show 2 ∈ (Nat.card (CFSG.fittingSubgroupOf S.H)).primeFactors
  rw [Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, Nat.card_pos.ne'⟩
  have h := Subgroup.orderOf_dvd_natCard _ S.t_mem_fitting
  rwa [S.ht] at h

theorem p_mem_primes : S.p ∈ S.primes := by
  show S.p ∈ (Nat.card (CFSG.fittingSubgroupOf S.H)).primeFactors
  rw [Nat.mem_primeFactors]
  exact ⟨S.hp, S.p_dvd_card_V.trans (Subgroup.card_dvd_of_le S.V_le_fitting), Nat.card_pos.ne'⟩

theorem two_le_card_primes_F :
    2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf S.H)) := by
  have h2 : 2 ∈ primesOfOrder (generalizedFittingSubgroupOf S.H) := by
    show 2 ∈ (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, Nat.card_pos.ne'⟩
    have h := Subgroup.orderOf_dvd_natCard _ S.t_mem_F
    rwa [S.ht] at h
  have hp : S.p ∈ primesOfOrder (generalizedFittingSubgroupOf S.H) := by
    show S.p ∈ (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨S.hp, S.p_dvd_card_V.trans (Subgroup.card_dvd_of_le S.V_le_F), Nat.card_pos.ne'⟩
  have hfin : (primesOfOrder (generalizedFittingSubgroupOf S.H)).Finite :=
    (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors.finite_toSet
  rw [Nat.card_coe_set_eq, ← Set.ncard_pair (Ne.symm S.hp2)]
  exact Set.ncard_le_ncard (Set.insert_subset_iff.mpr ⟨h2, Set.singleton_subset_iff.mpr hp⟩) hfin

theorem V_le_oddCoreOf {X : Subgroup G} (hWX : S.W ≤ X) :
    S.V ≤ oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({S.t} : Set G))) := by
  have hVO : S.V ≤ oddCoreOf (CFSG.fittingSubgroupOf S.H) :=
    le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent S.H) S.V_le_fitting S.odd_card_V
  exact (le_inf hVO (le_inf (S.V_le_W.trans hWX) S.htV)).trans
    (oddCoreOf_fitting_inf_le (inf_le_right.trans S.hCH))

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this

omit [Finite G] in
theorem map_conj_map_conj (g h : G) (A : Subgroup G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext x
  simp

theorem map_conj_le_H_iff {A : Subgroup G} {h : G} (hh : h ∈ S.H) :
    A.map (MulAut.conj h).toMonoidHom ≤ S.H ↔ A ≤ S.H := by
  conv_lhs => rw [← map_conj_eq_self_of_mem hh]
  exact map_conj_le_map_conj_iff h

variable {X : Subgroup G}

theorem t_mem (hWX : S.W ≤ X) : S.t ∈ X := hWX S.t_mem_W

theorem qCoreOf_inf_H (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    qCoreOf X q ⊓ S.H = ⊥ :=
  bender1970_1_7_i_oddCoreDisjoint S.hG.isSimpleGroup S.H S.hH S.W S.W_le_F S.W_isSubnormal
    S.inf_centralizer_W_le hWX q hq hqπ

theorem qCoreOf_props (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    (∀ x ∈ qCoreOf X q, S.t * x * S.t⁻¹ = x⁻¹) ∧ IsMulCommutative (qCoreOf X q) ∧
      Odd (Nat.card (qCoreOf X q)) ∧
      ⁅qCoreOf X q, Subgroup.zpowers S.t⁆ = qCoreOf X q ∧
      generalizedFittingSubgroupOf X ≤ Subgroup.centralizer (qCoreOf X q : Set G) := by
  refine qCoreOf_props_of_fixedPointFree (S.t_mem hWX) S.ht hq ?_
  exact le_bot_iff.mp ((inf_le_inf_left _ S.hCH).trans (S.qCoreOf_inf_H hWX hq hqπ).le)

theorem ne_p_of_not_mem_primes {q : ℕ} (hqπ : q ∉ S.primes) : q ≠ S.p :=
  fun h => hqπ (h ▸ S.p_mem_primes)

theorem qCoreOf_le_centralizer (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hqπ : q ∈ S.primes) :
    qCoreOf X q ≤ Subgroup.centralizer ({S.t} : Set G) := by
  by_cases hq2 : q = 2
  · subst hq2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have htN : S.t ∈ Subgroup.normalizer (qCoreOf X 2 : Set G) :=
      le_normalizer_of_isNormalIn (qCoreOf_normal_in X 2) (S.t_mem hWX)
    have htp : IsPGroup 2 (Subgroup.zpowers S.t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.ht, pow_one])
    have hP : IsPGroup 2 (Subgroup.zpowers S.t ⊔ qCoreOf X 2 : Subgroup G) :=
      htp.to_sup_of_normal_right' (qCoreOf_isPGroup X 2) (Subgroup.zpowers_le.mpr htN)
    obtain ⟨T, hT⟩ := hP.exists_le_sylow
    have hTab := S.hG.hasAbelianSylowTwo T
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hTab.is_comm.comm
      ⟨x, hT ((le_sup_right : qCoreOf X 2 ≤ Subgroup.zpowers S.t ⊔ qCoreOf X 2) hx)⟩
      ⟨S.t, hT ((le_sup_left : Subgroup.zpowers S.t ≤ Subgroup.zpowers S.t ⊔ qCoreOf X 2)
        (Subgroup.mem_zpowers S.t))⟩)
  · have h17 := bender1970_1_7_ii_commutator_pResidual S.hG.isSimpleGroup S.H S.hH S.W
      S.W_le_F S.W_isSubnormal S.inf_centralizer_W_le hWX q hq hqπ
    have htR : S.t ∈ pResidualOf (generalizedFittingSubgroupOf S.H) q :=
      mem_pResidualOf_of_order_coprime _ q hq S.t_mem_F (by
        rw [S.ht]; exact (Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h17 hx
    exact ((Subgroup.mem_centralizer_iff.mp h) S.t htR).symm

omit [Finite G] in
theorem ne_bot_of_isComponentOf {L A : Subgroup G} (hL : IsComponentOf L A) : L ≠ ⊥ := by
  have : Nontrivial L := hL.2.2.1
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

theorem t_mem_normalizer_component (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G}
    (hL : IsComponentOf L X) : S.t ∈ Subgroup.normalizer (L : Set G) :=
  mem_normalizer_of_isComponentOf_of_orderOf (S.hG.isAStar X hX) hL (S.t_mem hWX) S.ht

theorem commutator_component_eq_bot (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G}
    (hL : IsComponentOf L X) (hLH : L ≤ S.H) : ⁅L, Subgroup.zpowers S.t⁆ = ⊥ := by
  rcases commutator_eq_bot_or_le_of_isComponentOf hL
      (Subgroup.zpowers_le.mpr (S.t_mem_normalizer_component hWX hX hL)) with h | h
  · exact h
  · exact absurd (S.eq_bot_of_le_commutator hLH h) (ne_bot_of_isComponentOf hL)

theorem le_commutator_component (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G}
    (hL : IsComponentOf L X) (hLH : ¬ L ≤ S.H) : L ≤ ⁅L, Subgroup.zpowers S.t⁆ := by
  rcases commutator_eq_bot_or_le_of_isComponentOf hL
      (Subgroup.zpowers_le.mpr (S.t_mem_normalizer_component hWX hX hL)) with h | h
  · exfalso
    apply hLH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq'] at h
    exact h.trans S.hCH
  · exact h

theorem le_of_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) : P ≤ X := by
  rcases hP with ⟨q, -, -, rfl⟩ | ⟨hL, -⟩
  · exact Subgroup.map_subtype_le _
  · exact hL.1

theorem Q_le : S.Q X ≤ X := sSup_le fun _ hP => S.le_of_mem_pieces hP

theorem le_Q_of_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) : P ≤ S.Q X := le_sSup hP

theorem le_commutator_of_mem_pieces (hWX : S.W ≤ X) (hX : X ≠ ⊤) {P : Subgroup G}
    (hP : P ∈ S.pieces X) : P ≤ ⁅P, Subgroup.zpowers S.t⁆ := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact (S.qCoreOf_props hWX hq hqπ).2.2.2.1.ge
  · exact S.le_commutator_component hWX hX hL hLH

theorem map_conj_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) {g : G} (hgX : g ∈ X)
    (hgH : g ∈ S.H) : P.map (MulAut.conj g).toMonoidHom ∈ S.pieces X := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact Or.inl ⟨q, hq, hqπ, map_conj_eq_of_mem_normalizer
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) hgX)⟩
  · exact Or.inr ⟨fstar_isComponentOf_conjugateSubgroup_of_mem hL g hgX,
      fun h => hLH ((S.map_conj_le_H_iff hgH).mp h)⟩

theorem W_le_normalizer_Q (hWX : S.W ≤ X) : S.W ≤ Subgroup.normalizer (S.Q X : Set G) :=
  fun _ hw => mem_normalizer_sSup_of_map_mem
    (fun _ hP => S.map_conj_mem_pieces hP (hWX hw) (S.W_le_H hw))
    (fun _ hP => S.map_conj_mem_pieces hP (X.inv_mem (hWX hw)) (S.H.inv_mem (S.W_le_H hw)))

theorem Q_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) : S.Q X ∈ S.U := by
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ S.Q_le)), S.W_le_normalizer_Q hWX, le_antisymm
    (commutator_zpowers_le_of_mem_normalizer (S.W_le_normalizer_Q hWX S.t_mem_W)) ?_⟩
  refine sSup_le fun P hP => (S.le_commutator_of_mem_pieces hWX hX hP).trans ?_
  exact Subgroup.commutator_mono (le_sSup hP) le_rfl

theorem Q_le_generalizedFitting : S.Q X ≤ generalizedFittingSubgroupOf X := by
  refine sSup_le fun P hP => ?_
  rcases hP with ⟨q, hq, -, rfl⟩ | ⟨hL, -⟩
  · exact (qCoreOf_le_fittingSubgroupOf X q hq).trans le_sup_left
  · exact (le_sSup (s := {E : Subgroup G | IsComponentOf E X}) hL).trans le_sup_right

theorem generalizedFitting_le_normalizer_component {L : Subgroup G} (hL : IsComponentOf L X) :
    generalizedFittingSubgroupOf X ≤ Subgroup.normalizer (L : Set G) := by
  refine sup_le ?_ (componentLayerOf_le_normalizer_of_isComponentOf hL)
  have h1 : L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) :=
    (le_sSup (s := {E : Subgroup G | IsComponentOf E X}) hL).trans
      (componentLayerOf_le_centralizer_fitting X)
  exact (Subgroup.le_centralizer_iff.mp h1).trans (Subgroup.centralizer_le_normalizer _)

theorem commutator_le_oStar (hWX : S.W ≤ X) (hX : X ≠ ⊤) :
    ⁅X, Subgroup.zpowers S.t⁆ ≤ (oStar X).map X.subtype := by
  have hO := mem_map_oStar_of_orderOf (S.hG.isAStar X hX) (S.t_mem hWX) S.ht
  refine commutator_zpowers_le_of_forall S.ht fun x hx => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (map_oStar_le_normalizer X hx) _).mp hO)
    (Subgroup.inv_mem _ hO)

theorem commutator_le_centralizer_fitting (hWX : S.W ≤ X) :
    ⁅X, Subgroup.zpowers S.t⁆ ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) := by
  refine commutator_zpowers_le_of_forall S.ht fun x hx => ?_
  rw [(show CFSG.fittingSubgroupOf X = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf X)]
  have hle : (⨆ q : (Nat.card X).primeFactors.attach, qCoreOf X q.1.1) ≤
      Subgroup.centralizer ({⁅x, S.t⁆} : Set G) := by
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hxN : x ∈ Subgroup.normalizer (qCoreOf X q.1.1 : Set G) :=
      le_normalizer_of_isNormalIn (qCoreOf_normal_in X _) hx
    have hs : (∀ n ∈ qCoreOf X q.1.1, S.t * n * S.t⁻¹ = n) ∨
        (∀ n ∈ qCoreOf X q.1.1, S.t * n * S.t⁻¹ = n⁻¹) := by
      by_cases hqπ : q.1.1 ∈ S.primes
      · left
        intro n hn
        have h := Subgroup.mem_centralizer_singleton_iff.mp (S.qCoreOf_le_centralizer hWX hq hqπ hn)
        rw [← h]
        group
      · exact Or.inr (S.qCoreOf_props hWX hq hqπ).1
    have h := commutatorElement_mem_centralizer_of_conj hxN hs
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h) n hn
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

theorem le_generalizedFitting_of_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {K : Subgroup G}
    (hK : K ∈ S.U) (hKX : K ≤ X) : K ≤ generalizedFittingSubgroupOf X := by
  calc K = ⁅K, Subgroup.zpowers S.t⁆ := hK.2.2.symm
    _ ≤ ⁅X, Subgroup.zpowers S.t⁆ := Subgroup.commutator_mono hKX le_rfl
    _ ≤ generalizedFittingSubgroupOf X :=
        le_generalizedFittingSubgroupOf_of_le_oStar (S.hG.isAStar X hX)
          (S.commutator_le_oStar hWX hX) (S.commutator_le_centralizer_fitting hWX)

omit S in
theorem generalizedFitting_le_sSup : generalizedFittingSubgroupOf X ≤
    sSup {A | (∃ q : ℕ, q.Prime ∧ A = qCoreOf X q) ∨ IsComponentOf A X} := by
  refine sup_le ?_ ?_
  · rw [fittingSubgroupOf_eq_iSup_qCoreOf X]
    exact iSup_le fun q => le_sSup (Or.inl ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2, rfl⟩)
  · exact sSup_le fun L hL => le_sSup (Or.inr hL)

theorem commutator_generalizedFitting_le_Q (hWX : S.W ≤ X) (hX : X ≠ ⊤) :
    ⁅generalizedFittingSubgroupOf X, Subgroup.zpowers S.t⁆ ≤ S.Q X := by
  refine (Subgroup.commutator_mono generalizedFitting_le_sSup le_rfl).trans ?_
  refine commutator_sSup_le _ _ _ (fun A hA => ?_) (fun A hA => ?_)
  · rcases hA with ⟨q, hq, rfl⟩ | hL
    · by_cases hqπ : q ∈ S.primes
      · have h : ⁅qCoreOf X q, Subgroup.zpowers S.t⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq']
          exact S.qCoreOf_le_centralizer hWX hq hqπ
        rw [h]
        exact bot_le
      · exact (commutator_zpowers_le_of_mem_normalizer (le_normalizer_of_isNormalIn
          (qCoreOf_normal_in X q) (S.t_mem hWX))).trans (le_sSup (Or.inl ⟨q, hq, hqπ, rfl⟩))
    · by_cases hLH : A ≤ S.H
      · rw [S.commutator_component_eq_bot hWX hX hL hLH]
        exact bot_le
      · exact (commutator_zpowers_le_of_mem_normalizer
          (S.t_mem_normalizer_component hWX hX hL)).trans (le_sSup (Or.inr ⟨hL, hLH⟩))
  · have hAX : A ≤ X := by
      rcases hA with ⟨q, -, rfl⟩ | hL
      · exact Subgroup.map_subtype_le _
      · exact hL.1
    intro a ha
    refine mem_normalizer_sSup fun P hP => ?_
    rcases hP with ⟨r, -, -, rfl⟩ | ⟨hL', -⟩
    · exact le_normalizer_of_isNormalIn (qCoreOf_normal_in X r) (hAX ha)
    · rcases hA with ⟨q, hq, rfl⟩ | hL
      · exact generalizedFitting_le_normalizer_component hL'
          ((qCoreOf_le_fittingSubgroupOf X q hq).trans le_sup_left ha)
      · exact componentLayerOf_le_normalizer_of_isComponentOf hL'
          (le_sSup (s := {E : Subgroup G | IsComponentOf E X}) hL ha)

theorem le_Q_of_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {K : Subgroup G} (hK : K ∈ S.U)
    (hKX : K ≤ X) : K ≤ S.Q X := by
  calc K = ⁅K, Subgroup.zpowers S.t⁆ := hK.2.2.symm
    _ ≤ ⁅generalizedFittingSubgroupOf X, Subgroup.zpowers S.t⁆ :=
        Subgroup.commutator_mono (S.le_generalizedFitting_of_mem_U hWX hX hK hKX) le_rfl
    _ ≤ S.Q X := S.commutator_generalizedFitting_le_Q hWX hX

theorem map_conj_mem_pieces_map {P : Subgroup G} (hP : P ∈ S.pieces X) {h : G} (hh : h ∈ S.H) :
    P.map (MulAut.conj h).toMonoidHom ∈ S.pieces (X.map (MulAut.conj h).toMonoidHom) := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact Or.inl ⟨q, hq, hqπ, (qCoreOf_conjugateSubgroup X h q).symm⟩
  · exact Or.inr ⟨IsComponentOf.map_conj hL h, fun h' => hLH ((S.map_conj_le_H_iff hh).mp h')⟩

theorem map_conj_Q_le {h : G} (hh : h ∈ S.H) :
    (S.Q X).map (MulAut.conj h).toMonoidHom ≤ S.Q (X.map (MulAut.conj h).toMonoidHom) := by
  rw [Q, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun P hP => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (S.map_conj_mem_pieces_map hP hh)

theorem map_conj_Q {h : G} (hh : h ∈ S.H) :
    (S.Q X).map (MulAut.conj h).toMonoidHom = S.Q (X.map (MulAut.conj h).toMonoidHom) := by
  refine le_antisymm (S.map_conj_Q_le hh) ?_
  have h1 := S.map_conj_Q_le (X := X.map (MulAut.conj h).toMonoidHom) (S.H.inv_mem hh)
  rw [map_conj_map_conj_inv] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) h1
  rwa [map_conj_inv_map_conj] at h2

theorem le_orbit (L : Subgroup G) : L ≤ S.orbit L :=
  le_sSup ⟨1, S.W.one_mem, (map_conj_one L).symm⟩

theorem orbit_le {L Y : Subgroup G} (hLY : L ≤ Y)
    (hWY : S.W ≤ Subgroup.normalizer (Y : Set G)) : S.orbit L ≤ Y := by
  refine sSup_le ?_
  rintro _ ⟨w, hw, rfl⟩
  rintro _ ⟨l, hl, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hWY hw) l).mp (hLY hl)

theorem W_le_normalizer_orbit (L : Subgroup G) :
    S.W ≤ Subgroup.normalizer (S.orbit L : Set G) := by
  intro w hw
  refine mem_normalizer_sSup_of_map_mem ?_ ?_
  · rintro _ ⟨w', hw', rfl⟩
    exact ⟨w * w', S.W.mul_mem hw hw', map_conj_map_conj w w' L⟩
  · rintro _ ⟨w', hw', rfl⟩
    exact ⟨w⁻¹ * w', S.W.mul_mem (S.W.inv_mem hw) hw', map_conj_map_conj w⁻¹ w' L⟩

theorem orbit_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G} (hL : IsComponentOf L X)
    (hLH : ¬ L ≤ S.H) : S.orbit L ∈ S.U := by
  have hOX : S.orbit L ≤ X := S.orbit_le hL.1 (hWX.trans X.le_normalizer)
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ hOX)), S.W_le_normalizer_orbit L, le_antisymm
    (commutator_zpowers_le_of_mem_normalizer (S.W_le_normalizer_orbit L S.t_mem_W)) ?_⟩
  refine sSup_le ?_
  rintro _ ⟨w, hw, rfl⟩
  have hLw : IsComponentOf (L.map (MulAut.conj w).toMonoidHom) X :=
    fstar_isComponentOf_conjugateSubgroup_of_mem hL w (hWX hw)
  have hLwH : ¬ L.map (MulAut.conj w).toMonoidHom ≤ S.H :=
    fun h => hLH ((S.map_conj_le_H_iff (S.W_le_H hw)).mp h)
  exact (S.le_commutator_component hWX hX hLw hLwH).trans
    (Subgroup.commutator_mono (le_sSup ⟨w, hw, rfl⟩) le_rfl)

end Bender37

end CFSG.Walter
