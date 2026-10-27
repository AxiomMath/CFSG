module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofONModel
import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.RankThree.PartTwo.Sec21.Item211ProofIrred
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools
import CFSG.RankThree.PartOne.FIVES.Lift
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.RankThree.Native.ONTriple (GM)

open scoped commutatorElement

namespace Item211Res3Proof

open Item211Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem twoGroup_spec (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) :
    IsPGroup 2 (barImage L U ⊔ barImage L (lThreeV E U c) : Subgroup (MulAut (lBar L))) ∧
      8 ≤ Nat.card (barImage L U ⊔ barImage L (lThreeV E U c) : Subgroup (MulAut (lBar L))) ∧
      (∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G),
        ∀ x ∈ barImage L U ⊔ barImage L (lThreeV E U c),
          barAct L ⟨e, he⟩ * x * (barAct L ⟨e, he⟩)⁻¹ ∈
            barImage L U ⊔ barImage L (lThreeV E U c)) ∧
      ∀ v ∈ lThreeV E U c, v * c = c * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, hcU⟩, hc1, hLs, hUN, hVN, hUL, hVL⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hEe : IsElemAbelian 3 E := hpair.mem_E.1.1
  have hcA : c ∈ A := hEA hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hG := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L hLc
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAL
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hEU, -, hU4⟩ := mem_fourGroups_iff.mp hpair.mem_U
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
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
      exact hEcomm c hcE b hb.1
  have hBX0 : B ≤ Subgroup.normalizer (X0 : Set G) :=
    hBC'.trans (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 C')
  have hX02 : IsPGroup 2 X0 := (CFSG.pCore_isPGroup).map C'.subtype
  have hB3 : IsPGroup 3 B := fun g =>
    ⟨1, Subtype.ext (by simpa using hEe.2 _ (Subgroup.mem_inf.mp g.2).1)⟩
  have hX03 : ¬ 3 ∣ Nat.card X0 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX02
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
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
  have hVC' : ∀ v ∈ V, v ∈ C' := fun v hv => (Subgroup.map_subtype_le _) (hVX0 hv)
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu =>
    ((Subgroup.mem_centralizer_iff.mp (hVC' v hv)) u (Or.inl hu)).symm
  have hVc : ∀ v ∈ V, v * c = c * v := fun v hv =>
    ((Subgroup.mem_centralizer_iff.mp (hVC' v hv)) c (Or.inr rfl)).symm
  have hV2 : IsPGroup 2 V := hX02.to_le hVX0
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hEUc : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U := fun e he u hu =>
    (Subgroup.mem_normalizer_iff.mp (hEU he) u).mp hu
  have hEVc : ∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V := by
    intro e he v hv
    have hmap := map_lThreeV (MulAut.conj e) E U c
    rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer he),
      map_conj_eq_of_mem_normalizer (hEU he)] at hmap
    have hce : (MulAut.conj e) c = c := by
      rw [MulAut.conj_apply, hEcomm e he c hcE, mul_inv_cancel_right]
    rw [hce, ← hV] at hmap
    rw [← hmap]
    exact ⟨v, hv, rfl⟩
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hEL
  set Uα := barImage L U with hUα
  set Vα := barImage L V with hVα
  set Bα := barImage L B with hBα
  have hUa : Uα ≠ ⊥ := barImage_ne_bot hUN hUL hq
  have hVa : Vα ≠ ⊥ := barImage_ne_bot hVN hVL hq
  have hVBa : ⁅Vα, Bα⁆ = Vα := by rw [hVα, hBα, ← barImage_commutator hVN hBN, hVB]
  have hUBa : ∀ a ∈ Uα, ∀ b ∈ Bα, a * b = b * a :=
    barImage_commute fun u hu b hb => Subgroup.mem_centralizer_iff.mp hb.2 u hu
  have hUVa : ∀ a ∈ Uα, ∀ b ∈ Vα, a * b = b * a :=
    barImage_commute fun u hu v hv => (hVU v hv u hu).symm
  have hUa2 : IsPGroup 2 Uα := isPGroup_barImage hU2
  have hVa2 : IsPGroup 2 Vα := isPGroup_barImage hV2
  have hUVn : Uα ≤ Subgroup.normalizer (Vα : Set (MulAut (lBar L))) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUVa a ha v hv).symm
  have hT2 : IsPGroup 2 (Uα ⊔ Vα : Subgroup (MulAut (lBar L))) :=
    IsPGroup.to_sup_of_normal_right' hUa2 hVa2 hUVn
  have hET : ∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G),
      ∀ x ∈ Uα ⊔ Vα, barAct L ⟨e, he⟩ * x * (barAct L ⟨e, he⟩)⁻¹ ∈ Uα ⊔ Vα :=
    fun e heE he =>
      conj_mem_sup (barImage_conj_mem he (hEUc e heE)) (barImage_conj_mem he (hEVc e heE))
  have hex : ∃ b ∈ Bα, ∃ t ∈ Uα ⊔ Vα, b * t * b⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    apply hVa
    rw [← hVBa, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := hcon b hb v (Subgroup.mem_sup_right hv)
    calc b * v = b * v * b⁻¹ * b := by group
      _ = v * b := by rw [h1]
  obtain ⟨b, hb, t, htT, hbt⟩ := hex
  obtain ⟨g, hgN, hgB, rfl⟩ := mem_barImage_iff.mp hb
  have hg3 : barAct L ⟨g, hgN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hEe.2 g hgB.1)
    rw [this, map_one]
  have h5 := five_le_card_of_not_commute hg3 (hET g hgB.1 hgN) le_sup_left
    (fun u hu => by rw [← hUBa u hu _ hb, mul_inv_cancel_right]) hUa htT hbt
  exact ⟨hT2, eight_le_card_of_isPGroup hT2 h5, hET, hVc⟩

theorem exists_lift_of_fixed {A L : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {x : lBar L} (hx3 : x ^ 3 = 1)
    (hfix : ∀ a (ha : a ∈ A), barAct L ⟨a, hAN ha⟩ x = x) :
    ∃ y : L, (y : G) ^ 3 = 1 ∧ (∀ a ∈ A, a * (y : G) = y * a) ∧
      Subgroup.zpowers ((y : L) : lBar L) = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  let α : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hαN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    show (α a) n ∈ aschbacherSolvableCore 3 L
    rw [← Sec4.map_aschbacherSolvableCore (α a)]
    exact Subgroup.mem_map_of_mem _ hn
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hαN hN3
  have hxmem : x ∈ {q : L ⧸ N | ∀ a : A,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
    intro a
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact hfix a a.2
  rw [hlift] at hxmem
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxmem
  obtain ⟨e, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₁).ne' 3 (by norm_num)
  set y : L := x₁ ^ m with hy
  have hx₁A : ∀ a ∈ A, a * (x₁ : G) = x₁ * a := by
    intro a ha
    have h1 : (a : G) * x₁ * a⁻¹ = x₁ := congrArg Subtype.val (hx₁ ⟨a, ha⟩)
    calc a * (x₁ : G) = a * x₁ * a⁻¹ * a := by group
      _ = x₁ * a := by rw [h1]
  have hyA : ∀ a ∈ A, a * (y : G) = (y : G) * a := by
    intro a ha
    rw [hy, Subgroup.coe_pow]
    exact ((Commute.pow_right (hx₁A a ha) m)).eq
  have hy3e : y ^ 3 ^ e = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hπy : π y = x ^ m := by
    rw [hy, map_pow]
    exact congrArg (· ^ m) hx₁x
  have hy3 : y ^ 3 = 1 := by
    have hmemN : y ^ 3 ∈ N := by
      have h1 : π (y ^ 3) = 1 := by
        rw [map_pow, hπy, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 hmemN (k := e)
      (by rw [← pow_mul, mul_comm, pow_mul, hy3e, one_pow])
  refine ⟨y, by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one], hyA, ?_⟩
  have e1 : ((y : L) : lBar L) = x ^ m := hπy
  rw [e1]
  exact Sec13.ON134.zpowers_pow_of_cube hx3 (fun h => hm3 (Nat.dvd_of_mod_eq_zero h))

theorem mem_of_commute_of_maximal {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A) {y : G} (hy3 : y ^ 3 = 1)
    (hyA : ∀ a ∈ A, a * y = y * a) : y ∈ A := by
  have hE := Sec13.isElemAbelian_sup hAe (Sec13.isElemAbelian_zpowers hy3)
    (fun a ha z hz => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_right (hyA a ha) n).eq)
  rw [← hmax _ hE le_sup_left]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem barAct_of_mem {L : Subgroup G} {g : G} (hgL : g ∈ L)
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) :
    barAct L ⟨g, hgN⟩ = MulAut.conj ((⟨g, hgL⟩ : L) : lBar L) :=
  Sec13.ON134.thetaQuotMulAut_of_mem ⟨g, hgL⟩

theorem mem_of_tripleCover (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L)
    (hON : Sec4.IsTripleCover (lBar L) Blueprint.NativeSporadic.ON) : c ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax := hpair.mem_S.1.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
  rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hsc
  have hZ3 : Nat.card (Subgroup.center (lBar L)) = 3 := hON.1
  have : Nontrivial (Subgroup.center (lBar L)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ3]; norm_num)
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center (lBar L))
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center (lBar L)) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hzZ : Subgroup.zpowers z = Subgroup.center (lBar L) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [hZ3, Sec13.card_zpowers_of_pow_three hz3 hz1'])
  have hfix : ∀ a (ha : a ∈ A), barAct L ⟨a, hAL ha⟩ z = z := by
    intro a ha
    refine Sec14.Res148.fix_center_of_pow_three _ ?_ hZ3 z hz
    rw [← map_pow]
    have : (⟨a, hAL ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAe.2 a ha)
    rw [this, map_one]
  obtain ⟨y, hy3, hyA, hyz⟩ := exists_lift_of_fixed hAe hAL hz3 hfix
  have hyA' : (y : G) ∈ A := mem_of_commute_of_maximal hAe hmax hy3 hyA
  have hyZ : ((y : L) : lBar L) ∈ Subgroup.center (lBar L) := by
    rw [← hzZ, ← hyz]
    exact Subgroup.mem_zpowers _
  have hyC : (y : G) ∈ Sec4.thetaQuotCentralizer L := by
    refine ⟨⟨y, Subgroup.le_normalizer y.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    change barAct L ⟨y, Subgroup.le_normalizer y.2⟩ = 1
    rw [barAct_of_mem y.2]
    ext q
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hyZ q).symm,
      mul_inv_cancel_right]
  have hyc : (y : G) ∈ Subgroup.zpowers c := hCA ▸ ⟨hyA', hyC⟩
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have h1 : y = 1 := Subtype.ext h
    apply hz1'
    have h2 : Subgroup.zpowers z = ⊥ := by
      rw [← hyz, h1, QuotientGroup.mk_one, Subgroup.zpowers_one_eq_bot]
    rw [← Subgroup.mem_bot, ← h2]
    exact Subgroup.mem_zpowers z
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have heq : Subgroup.zpowers (y : G) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc)
      (by rw [Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three hy3 hy1])
  have hcy : c ∈ Subgroup.zpowers (y : G) := heq ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr y.2) hcy

section Inner


theorem exists_inner_of_commute {L : Subgroup G} (ψ : lBar L ≃* GM) {c : G} (hcL : c ∈ L)
    (hZ : Subgroup.center (lBar L) = Subgroup.zpowers ((⟨c, hcL⟩ : L) : lBar L)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hgc : g * c = c * g) :
    ∃ k : lBar L, ∀ x, barAct L ⟨g, hgN⟩ x = k * x * k⁻¹ := by
  refine Sec13.ON134.aut_inner ψ (barAct L ⟨g, hgN⟩) fun z hz => ?_
  rw [hZ] at hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [map_zpow]
  congr 1
  have hgcg : g * c * g⁻¹ = c := by rw [hgc, mul_inv_cancel_right]
  have hmem : g * c * g⁻¹ ∈ L := by rw [hgcg]; exact hcL
  have e : barAct L ⟨g, hgN⟩ ((⟨c, hcL⟩ : L) : lBar L) =
      ((⟨g * c * g⁻¹, hmem⟩ : L) : lBar L) := rfl
  rw [e]
  congr 1
  exact Subtype.ext hgcg

end Inner

theorem pow_three_of_inner
    {X : Type} [Group X] (ψ : X ≃* GM)
    (hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1) {σ : MulAut X} (hσ3 : σ ^ 3 = 1) {k : X}
    (hk : ∀ x, σ x = k * x * k⁻¹) : k ^ 3 = 1 := by
  have hkZ : k ^ 3 ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro q
    have h1 := Sec13.ON134.pow_apply_of_conj hk 3 q
    rw [hσ3, MulAut.one_apply] at h1
    calc q * k ^ 3 = k ^ 3 * q * (k ^ 3)⁻¹ * k ^ 3 := by rw [← h1]
      _ = k ^ 3 * q := by group
  refine Sec13.ON134.pow_three_eq_one ψ (k := 2) ?_
  rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
  exact hZ3 _ hkZ

theorem card_sup_zpowers_eq_nine {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hab : a * b = b * a) (haB : a ∉ Subgroup.zpowers b) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
  have ha1 : a ≠ 1 := fun h => haB (h ▸ Subgroup.one_mem _)
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow hab i j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [Sec13.zpowers_inf_eq_bot ha3 haB, Subgroup.card_bot, mul_one,
    Sec13.card_zpowers_of_pow_three ha3 ha1, Sec13.card_zpowers_of_pow_three hb3 hb1] at hcard
  exact hcard

theorem le_of_tripleCover
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (hON : Sec4.IsTripleCover (lBar L) Blueprint.NativeSporadic.ON) : A ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax := hpair.mem_S.1.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcL : c ∈ L := mem_of_tripleCover h45 h66 hpair hON
  obtain ⟨hZ, -, -⟩ := Sec13.ON134.center_eq_zpowers hcL hc3 hc1 hLC hON
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  have hZ3 : ∀ z ∈ Subgroup.center (lBar L), z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := Subgroup.center (lBar L)) (x := ⟨z, hz⟩)
    rw [hON.1] at h
    exact congrArg Subtype.val h
  have hcB : c ∈ A ⊓ L := ⟨hcA, hcL⟩
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 :=
    hA27 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_contra hAL'
  obtain ⟨a₁, ha₁A, ha₁L⟩ := Set.not_subset.mp hAL'
  have ha₁B : a₁ ∉ A ⊓ L := fun h => ha₁L h.2
  interval_cases k
  ·
    rw [pow_zero] at hkeq
    have h1 : A ⊓ L = ⊥ := Subgroup.eq_bot_of_card_eq _ hkeq
    rw [h1, Subgroup.mem_bot] at hcB
    exact hc1 hcB
  ·
    rw [pow_one] at hkeq
    have hBc : A ⊓ L = Subgroup.zpowers c :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcB)
        (by rw [hkeq, Sec13.card_zpowers_of_pow_three hc3 hc1])).symm
    have ha₁c : a₁ ∉ Subgroup.zpowers c := hBc ▸ ha₁B
    have ha₁3 : a₁ ^ 3 = 1 := hAe.2 a₁ ha₁A
    set B₁ := Subgroup.zpowers a₁ ⊔ Subgroup.zpowers c with hB₁
    have hB₁9 : Nat.card B₁ = 9 :=
      card_sup_zpowers_eq_nine ha₁3 hc3 hc1 (hcomm a₁ ha₁A c hcA) ha₁c
    have hB₁A : B₁ ≤ A := sup_le (Subgroup.zpowers_le.mpr ha₁A) (Subgroup.zpowers_le.mpr hcA)
    obtain ⟨a₂, ha₂A, ha₂B⟩ : ∃ a₂ ∈ A, a₂ ∉ B₁ := by
      by_contra hall
      push Not at hall
      have h := Subgroup.card_le_of_le (show A ≤ B₁ from hall)
      rw [hA27, hB₁9] at h
      norm_num at h
    have hAB : A = Subgroup.zpowers a₂ ⊔ B₁ :=
      Item2130Proof.eq_zpowers_sup ha₂A hB₁A ha₂B (by rw [hA27, hB₁9]; norm_num)
    have hσ3 : ∀ a (ha : a ∈ A), barAct L ⟨a, hAL ha⟩ ^ 3 = 1 := by
      intro a ha
      rw [← map_pow]
      have : (⟨a, hAL ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hAe.2 a ha)
      rw [this, map_one]
    obtain ⟨k₁, hk₁⟩ := exists_inner_of_commute ψ hcL hZ (hAL ha₁A) (hcomm a₁ ha₁A c hcA)
    obtain ⟨k₂, hk₂⟩ := exists_inner_of_commute ψ hcL hZ (hAL ha₂A) (hcomm a₂ ha₂A c hcA)
    have hk₁3 := pow_three_of_inner ψ hZ3 (hσ3 a₁ ha₁A) hk₁
    have hk₂3 := pow_three_of_inner ψ hZ3 (hσ3 a₂ ha₂A) hk₂
    have e₁ : barAct L ⟨a₁, hAL ha₁A⟩ = MulAut.conj k₁ := MulEquiv.ext fun x => by
      rw [hk₁, MulAut.conj_apply]
    have e₂ : barAct L ⟨a₂, hAL ha₂A⟩ = MulAut.conj k₂ := MulEquiv.ext fun x => by
      rw [hk₂, MulAut.conj_apply]
    have hk₁₂ : ⁅k₁, k₂⁆ ∈ Subgroup.center (lBar L) := by
      have hc12 : MulAut.conj k₁ * MulAut.conj k₂ = MulAut.conj k₂ * MulAut.conj k₁ := by
        rw [← e₁, ← e₂, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm a₁ ha₁A a₂ ha₂A)
      rw [Subgroup.mem_center_iff]
      intro q
      have h1 : k₁ * (k₂ * (k₁⁻¹ * k₂⁻¹ * q * k₂ * k₁) * k₂⁻¹) * k₁⁻¹ =
          k₂ * (k₁ * (k₁⁻¹ * k₂⁻¹ * q * k₂ * k₁) * k₁⁻¹) * k₂⁻¹ := by
        have := congrArg (fun σ : MulAut (lBar L) => σ (k₁⁻¹ * k₂⁻¹ * q * k₂ * k₁)) hc12
        simpa only [MulAut.mul_apply, MulAut.conj_apply] using this
      rw [commutatorElement_def]
      calc q * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)
          = k₂ * (k₁ * (k₁⁻¹ * k₂⁻¹ * q * k₂ * k₁) * k₁⁻¹) * k₂⁻¹ *
              (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) := by group
        _ = k₁ * (k₂ * (k₁⁻¹ * k₂⁻¹ * q * k₂ * k₁) * k₂⁻¹) * k₁⁻¹ *
              (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) := by rw [← h1]
        _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ * q := by group
    obtain ⟨x, hx3, hxk₁, hxk₂, hxZ⟩ := exists_centralizer_two ψ hk₁3 hk₂3 hk₁₂
    set S := (MulAction.stabilizer (MulAut (lBar L)) x).comap (barAct L) with hS
    have hgen : ∀ a (ha : a ∈ A), barAct L ⟨a, hAL ha⟩ x = x → a ∈ S.map
        (Subgroup.normalizer (L : Set G)).subtype := fun a ha h =>
      ⟨⟨a, hAL ha⟩, (MulAction.mem_stabilizer_iff).mpr h, rfl⟩
    have hAS : A ≤ S.map (Subgroup.normalizer (L : Set G)).subtype := by
      rw [hAB, hB₁]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le (Subgroup.zpowers_le.mpr ?_)
        (Subgroup.zpowers_le.mpr ?_))
      · refine hgen a₂ ha₂A ?_
        rw [hk₂, ← hxk₂, mul_inv_cancel_right]
      · refine hgen a₁ ha₁A ?_
        rw [hk₁, ← hxk₁, mul_inv_cancel_right]
      · refine hgen c hcA ?_
        rw [barAct_of_mem hcL, MulAut.conj_apply]
        have hcZ : ((⟨c, hcL⟩ : L) : lBar L) ∈ Subgroup.center (lBar L) :=
          hZ ▸ Subgroup.mem_zpowers _
        rw [(Subgroup.mem_center_iff.mp hcZ x).symm, mul_inv_cancel_right]
    have hfix : ∀ a (ha : a ∈ A), barAct L ⟨a, hAL ha⟩ x = x := by
      intro a ha
      obtain ⟨n, hn, hna⟩ := hAS ha
      have e : n = ⟨a, hAL ha⟩ := Subtype.ext hna
      rw [← e]
      exact (MulAction.mem_stabilizer_iff).mp hn
    obtain ⟨y, hy3, hyA, hyx⟩ := exists_lift_of_fixed hAe hAL hx3 hfix
    have hyA' : (y : G) ∈ A := mem_of_commute_of_maximal hAe hmax hy3 hyA
    have hyc : (y : G) ∈ Subgroup.zpowers c := hBc ▸ ⟨hyA', y.2⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyc
    have hyZ : ((y : L) : lBar L) ∈ Subgroup.center (lBar L) := by
      have e : y = (⟨c, hcL⟩ : L) ^ n := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
      rw [e, QuotientGroup.mk_zpow, hZ]
      exact Subgroup.zpow_mem_zpowers _ n
    apply hxZ
    have h1 : x ∈ Subgroup.zpowers ((y : L) : lBar L) := hyx ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr hyZ) h1
  ·
    have hAB : A = Subgroup.zpowers a₁ ⊔ (A ⊓ L) :=
      Item2130Proof.eq_zpowers_sup ha₁A inf_le_left ha₁B (by rw [hA27, hkeq]; norm_num)
    exact ha₁L (Sec13.ON134.mem_of_maximal hAe hmax ha₁A inf_le_left (by rw [hkeq]; norm_num)
      inf_le_right hAB (hAL ha₁A) hcB hc1 hLC hq hON)
  ·
    exact hAL' ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA27, hkeq])).symm ▸
      inf_le_right)

theorem card_map_of_injOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (K : Subgroup X)
    (hf : Set.InjOn f K) : Nat.card (K.map f) = Nat.card K := by
  have h := Nat.card_image_of_injOn hf
  rw [← Subgroup.coe_map] at h
  exact h

omit [Finite G] in
theorem isElemAbelian_subgroupOf {A : Subgroup G} (L : Subgroup G) (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hA L

theorem isE27_image {A L : Subgroup G} (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 3 ^ 3)
    (hAL : A ≤ L) :
    Late.IsE27 ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hP3 : IsPGroup 3 (A.subgroupOf L) := hA3.comap_subtype
  have hcard : Nat.card (A.subgroupOf L) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA27]
    norm_num
  refine ⟨Sec4.Item462Proof.isElemAbelian_map' _ (isElemAbelian_subgroupOf L hA), ?_⟩
  rw [card_map_of_injOn _ _ (CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3), hcard]

end Item211Res3Proof

open Item211Res3Proof Item211Res2Proof

section Certs


theorem item211ResidualON_of
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item211ResidualON := by
  intro G _ _ A E U c L hpair _ hA27 hON
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, hcU⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcL : c ∈ L := mem_of_tripleCover h45 h66 hpair hON
  obtain ⟨hZ, -, -⟩ := Sec13.ON134.center_eq_zpowers hcL hc3 hc1 hLC hON
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  have hAL' : A ≤ L := le_of_tripleCover h45 h66 hpair hA27 hON
  have hEA : E = A := Subgroup.eq_of_le_of_card_ge hpair.mem_E.2
    (by rw [hA27, hpair.mem_E.1.2.1]; norm_num)
  obtain ⟨hT2, hT8, hET, hVc⟩ := twoGroup_spec h45 hpair
  set T := barImage L U ⊔ barImage L (lThreeV E U c) with hT
  set κ : lBar L →* MulAut (lBar L) := MulAut.conj with hκ
  have hinner : ∀ n : Subgroup.normalizer (L : Set G), (n : G) * c = c * n →
      barAct L n ∈ κ.range := by
    rintro ⟨g, hgN⟩ hgc
    obtain ⟨k, hk⟩ := exists_inner_of_commute ψ hcL hZ hgN hgc
    exact ⟨k, MulEquiv.ext fun x => by rw [hk]; rfl⟩
  have hTinn : T ≤ κ.range := by
    refine sup_le ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hinner n (Subgroup.mem_centralizer_iff.mp hcU (n : G) (Subgroup.mem_subgroupOf.mp hn))
    · rintro _ ⟨n, hn, rfl⟩
      exact hinner n (hVc _ (Subgroup.mem_subgroupOf.mp hn))
  set Z := Subgroup.center (lBar L) with hZdef
  have hκker : ∀ z ∈ Z, κ z = 1 := fun z hz => MulEquiv.ext fun x => by
    rw [hκ, MulAut.conj_apply, ← (Subgroup.mem_center_iff.mp hz x), mul_inv_cancel_right,
      MulAut.one_apply]
  set That := T.comap κ with hThat
  set Q := That.map (QuotientGroup.mk' Z) with hQ
  have hZThat : Z ≤ That := fun z hz => by
    show κ z ∈ T
    rw [hκker z hz]
    exact T.one_mem
  have hQcomap : Q.comap (QuotientGroup.mk' Z) = That := by
    rw [hQ, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZThat]
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨q, hq⟩
    obtain ⟨t, ht, rfl⟩ := hq
    obtain ⟨n, hn⟩ := hT2 ⟨κ t, ht⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hk : κ (t ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have hc : t ^ 2 ^ n ∈ Z := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun σ : MulAut (lBar L) => σ g) hk
      simp only [hκ, MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * t ^ 2 ^ n = t ^ 2 ^ n * g * (t ^ 2 ^ n)⁻¹ * t ^ 2 ^ n := by rw [h1]
        _ = t ^ 2 ^ n * g := by group
    show (QuotientGroup.mk' Z t) ^ 2 ^ n = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc
  obtain ⟨U₂, hU₂2, hU₂Q, hU₂inv⟩ := CFSG.RankThree.PartOne.FIVES.exists_lift_two_subgroup Q hQ2
  have hnorm : ∀ a (ha : a ∈ A), ((⟨a, hAL' ha⟩ : L) : lBar L) ∈
      Subgroup.normalizer (U₂ : Set (lBar L)) := by
    intro a ha
    set ā : lBar L := ((⟨a, hAL' ha⟩ : L) : lBar L) with hā
    have hσ : barAct L ⟨a, hAL ha⟩ = κ ā := barAct_of_mem (hAL' ha) (hAL ha)
    have haE : a ∈ E := by rw [hEA]; exact ha
    have hle : That.map (MulAut.conj ā).toMonoidHom ≤ That := by
      rintro _ ⟨t, ht, rfl⟩
      show κ ((MulAut.conj ā) t) ∈ T
      have e : κ ((MulAut.conj ā) t) =
          barAct L ⟨a, hAL ha⟩ * κ t * (barAct L ⟨a, hAL ha⟩)⁻¹ := by
        rw [hσ, MulAut.conj_apply, map_mul, map_mul, map_inv]
      rw [e]
      exact hET a haE (hAL ha) (κ t) ht
    have heq : That.map (MulAut.conj ā).toMonoidHom = That :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj ā).injective])
    have h1 := hU₂inv (MulAut.conj ā) (by rw [hQcomap]; exact heq)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hĀ27 := isE27_image hAe hA27 hAL'
  have hĀN : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ≤
      Subgroup.normalizer (U₂ : Set (lBar L)) := by
    rintro _ ⟨⟨a, haL⟩, haA, rfl⟩
    exact hnorm a (Subgroup.mem_subgroupOf.mp haA)
  have h4 := card_le_four_of_isE27 ψ hĀ27 hU₂2 hĀN
  have hmapT : ∀ u ∈ U₂, κ u ∈ T := by
    intro u hu
    have h1 : u ∈ Q.comap (QuotientGroup.mk' Z) := by
      show QuotientGroup.mk' Z u ∈ Q
      rw [← hU₂Q]
      exact ⟨u, hu, rfl⟩
    rw [hQcomap] at h1
    exact h1
  let f : U₂ → T := fun u => ⟨κ u, hmapT u u.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp (hTinn ht)
    have hyQ : QuotientGroup.mk' Z y ∈ Q := ⟨y, ht, rfl⟩
    rw [← hU₂Q] at hyQ
    obtain ⟨u, hu, huy⟩ := hyQ
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    have hz : u⁻¹ * y ∈ Z := QuotientGroup.eq.mp huy
    show κ u = κ y
    have e : y = u * (u⁻¹ * y) := by group
    rw [e, map_mul, hκker _ hz, mul_one]
  have hcardT : Nat.card T ≤ Nat.card U₂ := Nat.card_le_card_of_surjective f hf
  exact absurd (hT8.trans (hcardT.trans h4)) (by norm_num)

end Certs

end CFSG.RankThree.PartTwo.Sec21
