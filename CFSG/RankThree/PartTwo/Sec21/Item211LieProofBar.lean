module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G]

structure PairFacts (A E U : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  cE : c ∈ E
  cU : c ∈ Subgroup.centralizer (U : Set G)
  c1 : c ≠ 1
  cA : c ∈ A
  c3 : c ^ 3 = 1
  Ae : IsElemAbelian 3 A
  Ee : IsElemAbelian 3 E
  E27 : Nat.card E = 27
  EA : E ≤ A
  Lc : L ∈ thetaComponentsAt 3 c
  AL : A ≤ Subgroup.normalizer (L : Set G)
  q : IsQuasisimple (lBar L)
  UN : U ≤ Subgroup.normalizer (L : Set G)
  VN : lThreeV E U c ≤ Subgroup.normalizer (L : Set G)
  UL : ⁅L, U⁆ = L
  VL : ⁅L, lThreeV E U c⁆ = L
  EU : E ≤ Subgroup.normalizer (U : Set G)
  Ue : IsElemAbelian 2 U
  U4 : Nat.card U = 4
  CA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c

theorem pairFacts (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) : PairFacts A E U c L := by
  obtain ⟨⟨hcE, hcU⟩, hc1, hLs, hUN, hVN, hUL, hVL⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hEe : IsElemAbelian 3 E := hpair.mem_E.1.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcA : c ∈ A := hEA hcE
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  obtain ⟨hEU, hUe, hU4⟩ := mem_fourGroups_iff.mp hpair.mem_U
  have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
  rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
  exact ⟨hcE, hcU, hc1, hcA, hAe.2 c hcA, hAe, hEe, hpair.mem_E.1.2.1, hEA, hLc, hAL,
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc, hUN, hVN, hUL, hVL, hEU, hUe, hU4,
    SetLike.coe_injective hsc⟩

variable {A E U L : Subgroup G} {c : G}

namespace PairFacts

theorem EL (h : PairFacts A E U c L) : E ≤ Subgroup.normalizer (L : Set G) := h.EA.trans h.AL

theorem BL (h : PairFacts A E U c L) :
    E ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  inf_le_left.trans h.EL

theorem E_comm (h : PairFacts A E U c L) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.Ee.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem c_mem_K (h : PairFacts A E U c L) : c ∈ Sec4.thetaQuotCentralizer L := by
  have : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := by
    rw [h.CA]
    exact Subgroup.mem_zpowers c
  exact this.2

theorem EK (h : PairFacts A E U c L) : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨h.cE, h.c_mem_K⟩)
  rw [← h.CA]
  exact inf_le_inf_right _ h.EA

theorem orderOf_c (h : PairFacts A E U c L) : orderOf c = 3 := orderOf_eq_prime h.c3 h.c1

theorem L_le_centralizer (h : PairFacts A E U c L) : L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt h.Lc

theorem U2 (h : PairFacts A E U c L) : IsPGroup 2 U :=
  IsPGroup.of_card (n := 2) (by rw [h.U4]; norm_num)

theorem E_conj_U (h : PairFacts A E U c L) : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U :=
  fun _ he u hu => (Subgroup.mem_normalizer_iff.mp (h.EU he) u).mp hu

end PairFacts

structure VFacts (A E U : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  le_X0 : lThreeV E U c ≤
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ((U : Set G) ∪ {c}))
  comm_B : ⁅lThreeV E U c, E ⊓ Subgroup.centralizer (U : Set G)⁆ = lThreeV E U c
  comm_U : ∀ v ∈ lThreeV E U c, ∀ u ∈ U, v * u = u * v
  two : IsPGroup 2 (lThreeV E U c)
  E_conj : ∀ e ∈ E, ∀ v ∈ lThreeV E U c, e * v * e⁻¹ ∈ lThreeV E U c
  B_le : E ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer ((U : Set G) ∪ {c})
  E_conj_C : ∀ e ∈ E, ∀ x ∈ Subgroup.centralizer ((U : Set G) ∪ {c}),
    e * x * e⁻¹ ∈ Subgroup.centralizer ((U : Set G) ∪ {c})

theorem vFacts (h : PairFacts A E U c L) : VFacts A E U c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C' := Subgroup.centralizer ((U : Set G) ∪ {c}) with hC'
  set X0 := inSubgroup (CFSG.pCore 2) C' with hX0
  set B := E ⊓ Subgroup.centralizer (U : Set G) with hB
  set V := lThreeV E U c with hV
  have hVX0B : V = ⁅X0, B⁆ := rfl
  have hBC' : B ≤ C' := by
    intro b hb
    rw [hC', Subgroup.mem_centralizer_iff]
    rintro x (hx | hx)
    · exact (Subgroup.mem_centralizer_iff.mp hb.2) x hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h.E_comm c h.cE b hb.1
  have hBX0 : B ≤ Subgroup.normalizer (X0 : Set G) :=
    hBC'.trans (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 C')
  have hX02 : IsPGroup 2 X0 := (CFSG.pCore_isPGroup).map C'.subtype
  have hB3 : IsPGroup 3 B := fun g =>
    ⟨1, Subtype.ext (by simpa using h.Ee.2 _ (Subgroup.mem_inf.mp g.2).1)⟩
  have hX03 : ¬ 3 ∣ Nat.card X0 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX02
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hVB : ⁅V, B⁆ = V := by
    rw [hVX0B]
    exact CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three B X0 hB3 hX03 hBX0
  have hVX0 : V ≤ X0 := by
    rw [hVX0B, Subgroup.commutator_le]
    intro x hx b hb
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine X0.mul_mem hx ?_
    have h1 : b * x⁻¹ * b⁻¹ ∈ X0 :=
      (Subgroup.mem_normalizer_iff.mp (hBX0 hb) x⁻¹).mp (X0.inv_mem hx)
    rwa [mul_assoc] at h1
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := by
    intro v hv u hu
    have hvC : (v : G) ∈ C' := (Subgroup.map_subtype_le _) (hVX0 hv)
    exact ((Subgroup.mem_centralizer_iff.mp hvC) u (Or.inl hu)).symm
  have hEVc : ∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V := by
    intro e he v hv
    have hmap := map_lThreeV (MulAut.conj e) E U c
    rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer he),
      map_conj_eq_of_mem_normalizer (h.EU he)] at hmap
    have hce : (MulAut.conj e) c = c := by
      rw [MulAut.conj_apply, h.E_comm e he c h.cE, mul_inv_cancel_right]
    rw [hce, ← hV] at hmap
    rw [← hmap]
    exact ⟨v, hv, rfl⟩
  have hEC : ∀ e ∈ E, ∀ x ∈ C', e * x * e⁻¹ ∈ C' := by
    intro e he x hx
    rw [hC', Subgroup.mem_centralizer_iff] at hx ⊢
    rintro y (hy | hy)
    · have hy' : e⁻¹ * y * e ∈ U := by
        have := h.E_conj_U e⁻¹ (E.inv_mem he) y hy
        rwa [inv_inv] at this
      have h1 := hx _ (Or.inl hy')
      calc y * (e * x * e⁻¹) = e * ((e⁻¹ * y * e) * x) * e⁻¹ := by group
        _ = e * (x * (e⁻¹ * y * e)) * e⁻¹ := by rw [h1]
        _ = e * x * e⁻¹ * y := by group
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := hx c (Or.inr rfl)
      have hec : e * c = c * e := h.E_comm e he c h.cE
      calc c * (e * x * e⁻¹) = e * (c * x) * e⁻¹ := by
            rw [← mul_assoc, ← mul_assoc, ← hec]
            group
        _ = e * (x * c) * e⁻¹ := by rw [h1]
        _ = e * x * (c * e⁻¹) := by group
        _ = e * x * (e⁻¹ * c) := by
            rw [show c * e⁻¹ = e⁻¹ * c from by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hec, ← mul_assoc, inv_mul_cancel,
                one_mul]]
        _ = e * x * e⁻¹ * c := by group
  exact ⟨hVX0, hVB, hVU, hX02.to_le hVX0, hEVc, hBC', hEC⟩

theorem card_barImage_E (h : PairFacts A E U c L) : Nat.card (barImage L E) = 9 := by
  have h1 := card_barImage_mul h.EL
  rw [h.EK, Nat.card_zpowers, h.orderOf_c, h.E27] at h1
  omega

theorem card_barImage_A (h : PairFacts A E U c L) :
    Nat.card (barImage L A) * 3 = Nat.card A := by
  have h1 := card_barImage_mul h.AL
  rwa [h.CA, Nat.card_zpowers, h.orderOf_c] at h1

theorem isElemAbelian_barImage_E (h : PairFacts A E U c L) : IsElemAbelian 3 (barImage L E) :=
  isElemAbelian_barImage h.Ee

theorem isElemAbelian_barImage_A (h : PairFacts A E U c L) : IsElemAbelian 3 (barImage L A) :=
  isElemAbelian_barImage h.Ae

theorem isElemAbelian_barImage_U (h : PairFacts A E U c L) : IsElemAbelian 2 (barImage L U) :=
  isElemAbelian_barImage h.Ue

theorem isPGroup_barImage_U (h : PairFacts A E U c L) : IsPGroup 2 (barImage L U) :=
  isPGroup_barImage h.U2

theorem barImage_U_ne_bot (h : PairFacts A E U c L) : barImage L U ≠ ⊥ :=
  barImage_ne_bot h.UN h.UL h.q

theorem barImage_V_ne_bot (h : PairFacts A E U c L) : barImage L (lThreeV E U c) ≠ ⊥ :=
  barImage_ne_bot h.VN h.VL h.q

theorem card_barImage_U_mul (h : PairFacts A E U c L) :
    Nat.card (barImage L U) * Nat.card (U ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 4 := by
  rw [card_barImage_mul h.UN, h.U4]

theorem barImage_V_comm_B (h : PairFacts A E U c L) :
    ⁅barImage L (lThreeV E U c), barImage L (E ⊓ Subgroup.centralizer (U : Set G))⁆ =
      barImage L (lThreeV E U c) := by
  rw [← barImage_commutator h.VN h.BL, (vFacts h).comm_B]

theorem barImage_U_comm_B :
    ∀ a ∈ barImage L U, ∀ b ∈ barImage L (E ⊓ Subgroup.centralizer (U : Set G)),
      a * b = b * a :=
  barImage_commute fun u hu _ hb => Subgroup.mem_centralizer_iff.mp hb.2 u hu

theorem barImage_U_comm_V (h : PairFacts A E U c L) :
    ∀ a ∈ barImage L U, ∀ b ∈ barImage L (lThreeV E U c), a * b = b * a :=
  barImage_commute fun u hu v hv => ((vFacts h).comm_U v hv u hu).symm

theorem isPGroup_barImage_V (h : PairFacts A E U c L) : IsPGroup 2 (barImage L (lThreeV E U c)) :=
  isPGroup_barImage (vFacts h).two

theorem barImage_E_le_normalizer {X : Subgroup G}
    (hX : ∀ e ∈ E, ∀ x ∈ X, e * x * e⁻¹ ∈ X) :
    barImage L E ≤ Subgroup.normalizer (barImage L X : Set (MulAut (lBar L))) := by
  intro d hd
  obtain ⟨e, heN, heE, rfl⟩ := mem_barImage_iff.mp hd
  exact Subgroup.mem_normalizer_fintype (barImage_conj_mem heN (hX e heE))

theorem barImage_E_le_normalizer_U (h : PairFacts A E U c L) :
    barImage L E ≤ Subgroup.normalizer (barImage L U : Set (MulAut (lBar L))) :=
  barImage_E_le_normalizer h.E_conj_U

theorem barImage_E_le_normalizer_V (h : PairFacts A E U c L) :
    barImage L E ≤ Subgroup.normalizer (barImage L (lThreeV E U c) : Set (MulAut (lBar L))) :=
  barImage_E_le_normalizer (vFacts h).E_conj

theorem barImage_B_le_E : barImage L (E ⊓ Subgroup.centralizer (U : Set G)) ≤ barImage L E :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1

theorem barImage_U_comm_E_of_plus (hP : U ∈ fourGroupsPlus E) :
    ∀ a ∈ barImage L U, ∀ b ∈ barImage L E, a * b = b * a := by
  have hEC := (mem_fourGroupsPlus_iff.mp hP).2
  exact barImage_commute fun u hu e he => Subgroup.mem_centralizer_iff.mp (hEC he) u hu

theorem barImage_U_eq_comm_of_minus (h : PairFacts A E U c L) (hM : U ∈ fourGroupsMinus E) :
    barImage L U = ⁅barImage L U, barImage L E⁆ := by
  rw [← barImage_commutator h.UN h.EL, ← hM.2]

theorem le_centralizer_of_card_eq_two {M : Type*} [Group M] {T D : Subgroup M}
    (hT : Nat.card T = 2) (hD : D ≤ Subgroup.normalizer (T : Set M)) :
    D ≤ Subgroup.centralizer (T : Set M) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1, one_mul, mul_one]
  have hmem : d * t * d⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hD hd) t).mp ht
  have hne : d * t * d⁻¹ ≠ 1 := by
    intro h1
    apply ht1
    have : t = d⁻¹ * (d * t * d⁻¹) * d := by group
    rw [this, h1]
    group
  have key : ∀ x ∈ T, x = 1 ∨ x = t := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have h3 : 3 ≤ Nat.card T := by
      have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
      classical
      have hsub : (↑({1, t, x} : Finset M) : Set M) ⊆ (T : Set M) := by
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact T.one_mem
        · exact ht
        · exact hx
      have hcard : ({1, t, x} : Finset M).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm ht1, Ne.symm hcon.1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hcon.2]), Finset.card_singleton]
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at h1
      exact h1
    omega
  rcases key _ hmem with h1 | h1
  · exact absurd h1 hne
  · calc t * d = d * t * d⁻¹ * d := by rw [h1]
      _ = d * t := by group

theorem card_barImage_U_of_minus (h : PairFacts A E U c L) (hM : U ∈ fourGroupsMinus E) :
    Nat.card (barImage L U) = 4 := by
  have h4 := card_barImage_U_mul h
  have hdvd : Nat.card (barImage L U) ∣ 4 := Dvd.intro _ h4
  have hne : Nat.card (barImage L U) ≠ 1 := fun h1 =>
    barImage_U_ne_bot h ((Subgroup.card_eq_one).mp h1)
  have hle : Nat.card (barImage L U) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (barImage L U) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  interval_cases hc : Nat.card (barImage L U)
  · exact absurd rfl hne
  · exfalso
    have hC := le_centralizer_of_card_eq_two hc (barImage_E_le_normalizer_U h)
    apply barImage_U_ne_bot h
    rw [barImage_U_eq_comm_of_minus h hM, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hC hd) u hu).symm
  · omega
  · rfl

theorem inf_K_ne_bot_of_card_le_two (h : PairFacts A E U c L)
    (h2 : Nat.card (barImage L U) ≤ 2) : U ⊓ Sec4.thetaQuotCentralizer L ≠ ⊥ := by
  intro hbot
  have h1 := card_barImage_U_mul h
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  omega

section Inner

variable {X : Type*} [Group X]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot, ← Subgroup.mem_bot, ← hZ, Subgroup.mem_center_iff]
  intro y
  have h1 := congrArg (fun φ : MulAut X => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

theorem map_comap_conj {D : Subgroup (MulAut X)}
    (hD : D ≤ (MulAut.conj : X →* MulAut X).range) :
    (D.comap (MulAut.conj : X →* MulAut X)).map (MulAut.conj : X →* MulAut X) = D :=
  Subgroup.map_comap_eq_self hD

theorem commutator_le_range_conj {X : Type*} [Group X] (T D : Subgroup (MulAut X))
    (hD : D ≤ (MulAut.conj : X →* MulAut X).range) :
    ⁅T, D⁆ ≤ (MulAut.conj : X →* MulAut X).range := by
  rw [Subgroup.commutator_le]
  intro t _ d hd
  obtain ⟨y, rfl⟩ := hD hd
  rw [commutatorElement_def, KFacts.mul_mulAutConj_mul_inv]
  exact Subgroup.mul_mem _ ⟨_, rfl⟩ (Subgroup.inv_mem _ ⟨y, rfl⟩)

theorem card_comap_conj (hZ : Subgroup.center X = ⊥) {D : Subgroup (MulAut X)}
    (hD : D ≤ (MulAut.conj : X →* MulAut X).range) :
    Nat.card (D.comap (MulAut.conj : X →* MulAut X)) = Nat.card D := by
  conv_rhs => rw [← map_comap_conj hD]
  rw [Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hZ)]

theorem isElemAbelian_comap_of_injective {Y : Type*} [Group Y] {p : ℕ} {f : X →* Y}
    (hf : Function.Injective f) {D : Subgroup Y} (hD : IsElemAbelian p D) :
    IsElemAbelian p (D.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have h1 := hD.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rw [map_pow, map_one]
    exact hD.2 _ hx

end Inner

section Transport

variable {X M : Type*} [Group X] [Group M] {ψ : X →* M}

theorem card_comap_of_le_range (hψ : Function.Injective ψ) {D : Subgroup M}
    (hD : D ≤ ψ.range) : Nat.card (D.comap ψ) = Nat.card D := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self hD]
  rw [Subgroup.card_map_of_injective hψ]

theorem comap_centralizer_of_le_range (hψ : Function.Injective ψ) {T : Subgroup M}
    (hT : T ≤ ψ.range) :
    (Subgroup.centralizer (T : Set M)).comap ψ =
      Subgroup.centralizer ((T.comap ψ : Subgroup X) : Set X) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg t ht
    apply hψ
    rw [map_mul, map_mul]
    exact hg (ψ t) ht
  · intro hg t' ht'
    obtain ⟨t, rfl⟩ := hT ht'
    rw [← map_mul, ← map_mul, hg t (show t ∈ T.comap ψ from ht')]

theorem comap_commutator_of_le_range (hψ : Function.Injective ψ) {T D : Subgroup M}
    (hT : T ≤ ψ.range) (hD : D ≤ ψ.range) (h : ⁅T, D⁆ = T) :
    ⁅T.comap ψ, D.comap ψ⁆ = T.comap ψ := by
  apply Subgroup.map_injective hψ
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hT, Subgroup.map_comap_eq_self hD, h]

end Transport

end Item211LieProof

end CFSG.RankThree.PartTwo.Sec21
