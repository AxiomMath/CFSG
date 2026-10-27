module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res7ProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res7ProofModel
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofFinal
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res6ProofSylow
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofKernel
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

section Statements

@[expose] def Step1129PGLNotZ9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g e : G) (Y' : Subgroup G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      e ∈ A → e ∉ Subgroup.closure {c, d} →
      (⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d} ∨
        (g * x * g⁻¹ ∈ Subgroup.zpowers x ∧ ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d ∧
          ∀ w ∈ sec11P R g, ⁅e, w⁆ = w ^ 3)) →
      Y' ∈ thetaComponentsAt 3 e → sec11K L e ≤ Y' → ¬ KFacts.InducesStdKind Y' c .field →
      Sec8.IsZ3PGLThreePi (sec11YA e Y' A) →
      ∀ Q : Subgroup G, IsSylowOf 3 Q (Subgroup.centralizer {e}) →
        sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q →
        (∀ E : Subgroup G, E ≤ Q ⊓ Sec4.thetaQuotCentralizer Y' →
          CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 9) →
        ∀ v ∈ Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G),
          v * c ≠ c * v → v ^ 3 = 1

end Statements

namespace Item1117Res7Proof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem conj_mul_inv_mem_of_commutator_eq (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    (hPP : ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d}) :
    x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
  have hAe := h.mem_partTwoF.1
  have hdA := Item1117Proof.d_mem_A h
  have hxR := (Item1116Proof.mem_R h).2.1
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g hxR
  have heP : e ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 heA)
  have hc : ⁅x, e⁆ ∈ Subgroup.closure ({e, d} : Set G) :=
    hPP ▸ Subgroup.commutator_mem_commutator hxP heP
  have hz : x * e * x⁻¹ ∈ Subgroup.closure ({d, e} : Set G) := by
    rw [Set.pair_comm]
    have he : x * e * x⁻¹ = ⁅x, e⁆ * e := by rw [commutatorElement_def]; group
    rw [he]
    exact Subgroup.mul_mem _ hc (Subgroup.subset_closure (by simp))
  have hed : e ∉ Subgroup.zpowers d := fun hm =>
    hecd (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)
  obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  exact Sec12.conj_mul_inv_mem_zpowers_of_mem_closure
    (congrArg Subtype.val (hAe.1.is_comm.comm ⟨d, hdA⟩ ⟨e, heA⟩)) (hAe.2 d hdA) (hAe.2 e heA)
    hed (Item1117Proof.commute_d_x h).symm hk hz

theorem false_of_elemAbelian_le (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    (hxe : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y')
    (hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q) {E : Subgroup G}
    (hEQ : E ≤ Q ⊓ Sec4.thetaQuotCentralizer Y') (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have he3 : e ^ 3 = 1 := hAe.2 e heA
  have hdA := Item1117Proof.d_mem_A h
  have hd3 := Item1117Proof.orderOf_d h
  have hd3' : d ^ 3 = 1 := hAe.2 d hdA
  have hed : e ∉ Subgroup.zpowers d := fun hm =>
    hecd (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hYC : Y' ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY'
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  have hQY : Q ≤ Subgroup.normalizer (Y' : Set G) :=
    Item1117Res4Proof.le_normalizer_of_isPGroup h45 h.toTheoremFourHyp he1 he3 hQ3 hQ.le Y' hY'
  have hAQ : A ≤ Q := fun z hz =>
    hTQ ⟨Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hz), hAC hz⟩
  have hdY : d ∈ Y' := hKY' (hstdE.d_mem_sec11K h.inf_eq)
  have hdQ : d ∈ Q := hAQ hdA
  have hpow : ∀ z ∈ Q, ∃ k : ℕ, z ^ 3 ^ k = 1 := fun z hz => by
    obtain ⟨k, hk⟩ := hQ3 ⟨z, hz⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨hZ, E₀, hE₀Y, hE₀, hE₀9⟩ := facts_of_isZ3PGLThreePi hY' hAC hAY hAc hP
  obtain ⟨E', hE'T, hE', hE'9⟩ := exists_elemAbelian_le_of_isSylowOf
    (isSylowOf_inf_of_le_normalizer hQ hQY hYC) hE₀Y hE₀ hE₀9
  obtain ⟨w, hwQY, hw3, hwd, hwdc⟩ := exists_commute_not_mem_zpowers (hQ3.to_le inf_le_left)
    hE'T hE' hE'9 ⟨hdQ, hdY⟩ hd3
  have hN : ∀ t ∈ Subgroup.centralizer ({e} : Set G), (∃ k : ℕ, t ^ 3 ^ k = 1) →
      t ∈ Subgroup.normalizer (Y' : Set G) := fun t ht ⟨k, hk⟩ =>
    Item1117Res4Proof.le_normalizer_of_isPGroup h45 h.toTheoremFourHyp he1 he3
      (isPGroup_zpowers_of_pow hk) (Subgroup.zpowers_le.mpr ht) Y' hY' (Subgroup.mem_zpowers t)
  have hAE : A ∈ partTwoE G := by
    rw [h.partTwoE_eq h.card_eq]
    exact h.mem_partTwoF
  obtain ⟨-, -, U₀, hU₀, hU₀2, hAU₀⟩ := hAE
  have hxd : x * d = d * x := (Item1117Proof.commute_d_x h).symm
  set δ := x * e * x⁻¹ * e⁻¹ with hδdef
  have hδe : δ * e = e * δ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [← hk]
    exact (Commute.zpow_left (show Commute d e from hAc d hdA e heA) k).eq
  have hxeδ : x * e * x⁻¹ = e * δ := by
    rw [← hδe, hδdef]
    group
  have hδ1 : δ ≠ 1 := by
    intro h1
    have hxe' : x * e = e * x := by
      calc x * e = (x * e * x⁻¹ * e⁻¹) * e * x := by group
        _ = e * x := by rw [← hδdef, h1, one_mul]
    apply Item1116Proof.not_le_centralizer_of_isSylowOf hstdE (h.inf_L_eq ▸ hstdE.isSylowOf_inf_L)
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxe'
  obtain ⟨U, hU1, hU2, hUY, hdU⟩ := exists_two_subgroup_le h.toTheoremFourHyp.charTwoType hU₀ hU₀2
    hAU₀ heA hdA (hAc d hdA e heA) he3 hd3 hed hxd hxe hδ1 hxeδ hdY hN
  have hEd : ∀ u ∈ E, u * d = d * u := fun u hu => by
    obtain ⟨k, hk⟩ := hpow _ (Q.mul_mem (Q.inv_mem hdQ) (Q.mul_mem (Q.mul_mem (hEQ hu).1 hdQ)
      (Q.inv_mem (hEQ hu).1)))
    exact commute_of_mem_thetaQuotCentralizer (hEQ hu).2 hdY hk
  have hdE : d ∉ E := fun hd => by
    have h1 := eq_one_of_mem_thetaQuotCentralizer hZ hdY (hEQ hd).2 (k := 1)
      (by rw [pow_one]; exact hd3')
    rw [h1, orderOf_one] at hd3
    norm_num at hd3
  have hdC : d ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hEd u hu
  obtain ⟨hDcard, hDc, hDe⟩ := card_sup_zpowers_of_disjoint hdC hE.1 hE.2 hd3
    (Sec12.inf_zpowers_eq_bot_of_not_mem hd3 hdE)
  set D := E ⊔ Subgroup.zpowers d with hDdef
  have hD : CFSG.Assembly.IsElemAbelian 3 D := ⟨hDc, hDe⟩
  have hD27 : Nat.card D = 27 := by rw [hDdef, hDcard, hE9]
  have hD3 : IsPGroup 3 D := fun z => ⟨1, Subtype.ext (by simpa using hDe z z.2)⟩
  have hDM : D ≤ Subgroup.normalizer (thetaHull Y' U : Set G) :=
    sup_le (fun u hu => mem_normalizer_thetaHull_of_mem_thetaQuotCentralizer (hEQ hu).2)
      (Subgroup.zpowers_le.mpr (mem_normalizer_thetaHull_of_mem hdY hdU))
  obtain ⟨U', hU'1, hU'2, hDU'⟩ := exists_two_subgroup_of_thetaHull hUY hU1 hU2 hD3 hDM
  have hwE : ∀ u ∈ E, u * w = w * u := fun u hu => by
    obtain ⟨k, hk⟩ := hpow _ (Q.mul_mem (Q.inv_mem hwQY.1) (Q.mul_mem (Q.mul_mem (hEQ hu).1
      hwQY.1) (Q.inv_mem (hEQ hu).1)))
    exact commute_of_mem_thetaQuotCentralizer (hEQ hu).2 hwQY.2 hk
  have hwC : w ∈ Subgroup.centralizer (D : Set G) := by
    have hle : D ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hwE u hu)) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hwdc.symm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hwD : w ∉ D := by
    intro hwD
    have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (E : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hdC)
    have hmem : w ∈ (E : Set G) * (Subgroup.zpowers d : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E _ hdN]
      exact hwD
    obtain ⟨u, hu, t, ht, hut⟩ := Set.mem_mul.mp hmem
    have huY : u ∈ Y' := by
      have : u = w * t⁻¹ := by rw [← hut]; group
      rw [this]
      exact Y'.mul_mem hwQY.2 (Y'.inv_mem ((Subgroup.zpowers_le.mpr hdY) ht))
    have hu1 : u = 1 :=
      eq_one_of_mem_thetaQuotCentralizer hZ huY (hEQ hu).2 (k := 1)
        (by rw [pow_one]; exact hE.2 u hu)
    apply hwd
    rw [← hut, hu1, one_mul]
    exact ht
  exact Sec12.false_of_le_E81 (h.partTwoE_eq h.card_eq).symm hD hD27 hU'1 hU'2 hDU' hwC hw3 hwD

theorem le_centralizer_of_notZ9 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    (hxe : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y')
    (hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q)
    (hZ9 : (∀ E : Subgroup G, E ≤ Q ⊓ Sec4.thetaQuotCentralizer Y' →
        CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 9) →
      ∀ v ∈ Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G),
        v * c ≠ c * v → v ^ 3 = 1) :
    Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : ∀ E : Subgroup G, E ≤ Q ⊓ Sec4.thetaQuotCentralizer Y' →
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 9 := fun E hEQ hE hE9 =>
    false_of_elemAbelian_le h45 h heA hecd hxe hY' hKY' hP hQ hTQ hEQ hE hE9
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have he3 : e ^ 3 = 1 := hAe.2 e heA
  have he3o : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hdA := Item1117Proof.d_mem_A h
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAQ : A ≤ Q := fun z hz =>
    hTQ ⟨Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hz), hAC hz⟩
  have hdY : d ∈ Y' := hKY' (hstdE.d_mem_sec11K h.inf_eq)
  have heT : e ∈ Sec4.thetaQuotCentralizer Y' :=
    Item1119StepsProof.a_mem_thetaQuotCentralizer_Y hstdE
  intro v hv
  have hvQ : v ∈ Q := hv.1.1
  have hvT : v ∈ Sec4.thetaQuotCentralizer Y' := hv.1.2
  have hve : v * e = e * v := Subgroup.mem_centralizer_singleton_iff.mp (hQ.le hvQ)
  have hvd : v * d = d * v := by
    obtain ⟨k, hk⟩ := hQ.isPGroup ⟨d⁻¹ * (v * d * v⁻¹), Q.mul_mem (Q.inv_mem (hAQ hdA))
      (Q.mul_mem (Q.mul_mem hvQ (hAQ hdA)) (Q.inv_mem hvQ))⟩
    exact commute_of_mem_thetaQuotCentralizer hvT hdY (k := k)
      (by simpa using congrArg Subtype.val hk)
  by_contra hvA
  have hvc : v * c ≠ c * v := by
    intro hvc
    apply hvA
    have hle : A ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [hA', Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hvc.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hve.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hvd.symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hv3 : v ^ 3 = 1 := hZ9 hrank v hv hvc
  have hvo : orderOf v = 3 :=
    orderOf_eq_prime hv3 (fun h1 => hvc (by rw [h1, one_mul, mul_one]))
  have hve' : v ∉ Subgroup.zpowers e := fun hm =>
    hvc (hAc v (Subgroup.zpowers_le.mpr heA hm) c h.mem_A)
  have hez : ∀ z ∈ Subgroup.zpowers e, z ^ 3 = 1 := fun z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hvC : v ∈ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute e v from hve.symm) k)).eq
  obtain ⟨hEcard, hEc, hEe⟩ := card_sup_zpowers_of_disjoint hvC inferInstance hez hvo
    (Sec12.inf_zpowers_eq_bot_of_not_mem hvo hve')
  refine hrank (Subgroup.zpowers e ⊔ Subgroup.zpowers v) (sup_le ?_ ?_) ⟨hEc, hEe⟩ ?_
  · rw [Subgroup.zpowers_le]
    exact ⟨hAQ heA, heT⟩
  · rw [Subgroup.zpowers_le]
    exact hv.1
  · rw [hEcard, Nat.card_zpowers, he3o]

end Data

end Item1117Res7Proof

section Main

open Item1117Res7Proof in
theorem sylow11PGLWATwo_of_res7 (h45 : Sec4.Item4_5) (hZ9 : Step1129PGLNotZ9) :
    Sylow11PGLWATwo := by
  intro G _ _ A c L a R Y d x s r g e Y' h heA hecd hY' hKY' hnf hsc hrs hx9 hPP hP Q hQ hTQ
  exact le_centralizer_of_notZ9 h45 h heA hecd (conj_mul_inv_mem_of_commutator_eq h heA hecd hPP)
    hY' hKY' hP hQ hTQ (hZ9 G A c L a R Y d x s r g e Y' h hsc hrs hx9 heA hecd (Or.inl hPP) hY'
      hKY' hnf hP Q hQ hTQ)

open Item1117Res7Proof in
theorem gap1117NotActXPGL_of_res7 (h45 : Sec4.Item4_5) (hZ9 : Step1129PGLNotZ9) :
    Gap1117NotActXPGL := by
  intro G _ _ A c L a R Y d x s r g e Y' h hsc hrs hx9 hgx hPP heA hecd hcan hY' hKY' hnf hP Q hQ
    hTQ
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have heP : e ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 heA)
  have hxe : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
    have hc : ⁅x, e⁆ ∈ Subgroup.zpowers d := hPP ▸ Subgroup.commutator_mem_commutator hxP heP
    rwa [commutatorElement_def] at hc
  exact le_centralizer_of_notZ9 h45 h heA hecd hxe hY' hKY' hP hQ hTQ
    (hZ9 G A c L a R Y d x s r g e Y' h hsc hrs hx9 heA hecd (Or.inr ⟨hgx, hPP, hcan⟩) hY' hKY'
      hnf hP Q hQ hTQ)

end Main

end CFSG.RankThree.PartTwo.Sec11
