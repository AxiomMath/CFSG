module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5ProofStar
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

structure Pair2127 (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G)
    (d : G) : Prop where
  cfg : Config2119 G A E U c L
  mem_d : d ∈ A ⊓ L
  ne_one_d : d ≠ 1
  type_d : Sec4.InducesTypeOn L d 1
  normal_d : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d
  trans : trivOnQuot A (Subgroup.zpowers d) ≤ wStar A
  unique : ∀ K ∈ thetaComponentsAt 3 c, 3 ∣ Nat.card K → K = L
  l34 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))
  mover : ∃ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 ∧ x * d * x⁻¹ = d ∧
    (∀ y ∈ A, y⁻¹ * (x * y * x⁻¹) ∈ Subgroup.zpowers d) ∧ x * c * x⁻¹ ≠ c

namespace Item2119End5Proof

open Item2119EndProof Item2119End4Proof

variable {G : Type} [Group G] [Finite G]

theorem sec21Pair_conj {A E U K : Subgroup G} {x g : G} (hp : Sec21Pair G A E U x K)
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hEA : E = A) :
    Sec21Pair G A E (U.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (K.map (MulAut.conj g).toMonoidHom) := by
  have hA : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgA
  have hE : E.map (MulAut.conj g).toMonoidHom = E := by rw [hEA, hA]
  have h1 := map_mem_lThreeStarPairs (MulAut.conj g) hp.mem_pair
  rw [hA, hE, MulAut.conj_apply] at h1
  have h2 := map_mem_fourGroups (MulAut.conj g) hp.mem_U
  rw [hE] at h2
  exact { toSec21Std := hp.toSec21Std, mem_E := hp.mem_E, mem_U := h2, mem_pair := h1 }

theorem sec21Pair_inv {A E U K : Subgroup G} {x : G} (hp : Sec21Pair G A E U x K) :
    Sec21Pair G A E U x⁻¹ K := by
  obtain ⟨hx, hx1, hK, hUN, hVN, hUK, hVK⟩ := hp.mem_pair
  have hcent : Subgroup.centralizer ((U : Set G) ∪ {x⁻¹}) =
      Subgroup.centralizer ((U : Set G) ∪ {x}) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h y hy
      rcases hy with hy | rfl
      · exact h y (Or.inl hy)
      · have h1 := h y⁻¹ (Or.inr rfl)
        calc y * g = y * (g * y⁻¹) * y := by group
          _ = y * (y⁻¹ * g) * y := by rw [h1]
          _ = g * y := by group
    · intro h y hy
      rcases hy with hy | rfl
      · exact h y (Or.inl hy)
      · have h1 := h x (Or.inr rfl)
        calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * g) * x⁻¹ := by rw [← h1]
          _ = g * x⁻¹ := by group
  have hV : lThreeV E U x⁻¹ = lThreeV E U x := by rw [lThreeV, lThreeV, hcent]
  have hK' : K ∈ lZeroStarAt A x⁻¹ := by
    rw [lZeroStarAt, thetaComponentsAt_eq_of_zpowers_eq Subgroup.zpowers_inv]
    exact hK
  have hxi : x⁻¹ ∈ E ⊓ Subgroup.centralizer (U : Set G) := Subgroup.inv_mem _ hx
  have hVN' : lThreeV E U x⁻¹ ≤ Subgroup.normalizer (K : Set G) := by rw [hV]; exact hVN
  have hVK' : ⁅K, lThreeV E U x⁻¹⁆ = K := by rw [hV]; exact hVK
  have hmem : (x⁻¹, K) ∈ lThreeStarPairs A E U :=
    ⟨hxi, inv_ne_one.mpr hx1, hK', hUN, hVN', hUK, hVK'⟩
  exact { toSec21Std := hp.toSec21Std, mem_E := hp.mem_E, mem_U := hp.mem_U, mem_pair := hmem }

omit [Finite G] in
theorem exists_conj_eq_mul_pow {A : Subgroup G} {d w x : G} (hd3 : d ^ 3 = 1)
    (hwA : ∀ y ∈ A, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers d) (hxA : x ∈ A)
    (hwx : w * x * w⁻¹ ≠ x) : ∃ k < 3, k ≠ 0 ∧ w * x * w⁻¹ = x * d ^ k := by
  obtain ⟨k, hk, hkd⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA x hxA)
  refine ⟨k, hk, ?_, ?_⟩
  · rintro rfl
    apply hwx
    rw [pow_zero, inv_mul_eq_one] at hkd
    exact hkd.symm
  · rw [← hkd]
    group

theorem sec21Pair_of_coset {A E U K : Subgroup G} {x d w : G} (hp : Sec21Pair G A E U x K)
    (hEA : E = A) (hwN : w ∈ Subgroup.normalizer (A : Set G)) (hd3 : d ^ 3 = 1)
    (hwd : w * d * w⁻¹ = d) (hwA : ∀ y ∈ A, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers d)
    (hxA : x ∈ A) (hwx : w * x * w⁻¹ ≠ x) {j : ℕ} (hj : j < 3) :
    ∃ U' K' : Subgroup G, Sec21Pair G A E U' (x * d ^ j) K' := by
  obtain ⟨k, hk, hk0, hvx⟩ := exists_conj_eq_mul_pow hd3 hwA hxA hwx
  obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hwd hk hk0 hvx j hj
  have h := sec21Pair_conj hp (Subgroup.pow_mem _ hwN m) hEA
  rw [hm] at h
  exact ⟨_, _, h⟩

theorem exists_sec21Pair
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) :
    ∃ U' K : Subgroup G, Sec21Pair G A E U' e K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23' := h23
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have ha1 : a ≠ 1 := hpairs'.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have ha3 : a ^ 3 = 1 := h3 a haA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, -, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c := not_mem_zpowers_symm hc3 hd1 hcd
  have haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := not_mem_sup_of_config2119End hE
  have had : a ∉ Subgroup.zpowers d := fun h => haCD (Subgroup.mem_sup_right h)
  have hda : d ∉ Subgroup.zpowers a := not_mem_zpowers_symm ha3 hd1 had
  have hdc9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 hc3 hd1 hcd
  have haDC : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact haCD
  have hcDA : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a :=
    not_mem_sup_swap (hcomm d hdA c hcA) (hcomm d hdA a haA) hd3 hc3 ha3 hd1 hcd haDC
  have hda9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA a haA) hd3 ha3 hd1 had
  have hwmv : ∀ x ∈ A, x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d → w * x * w⁻¹ ≠ x := by
    intro x hx hxcd hwx
    have hxDC : x ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
      rw [sup_comm]
      exact hxcd
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA hx hdc9 hxDC hwx hwd hwc y hyA)
  have hw'mv : ∀ x ∈ A, x ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d → w' * x * w'⁻¹ ≠ x := by
    intro x hx hxad hw'x
    have hxDA : x ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
      rw [sup_comm]
      exact hxad
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 haA hdA hx hda9 hxDA hw'x hw'd hw'a y hyA)
  have hoff : ∀ e' ∈ A, e' ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d →
      e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d →
      e' ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c →
      ∃ U' K : Subgroup G, Sec21Pair G A E U' e' K := by
    intro e' he' hecd' head' heac'
    obtain ⟨Y, hgen⟩ := exists_gen2125 h211 h2116 h45 h48 h66 hE h23' h24 he' hecd' head' heac'
    obtain ⟨U₁, hU₁, Y', hpY⟩ := hStar G A E U c L d U₀ a X e' Y hgen
    have hpY' : Sec21Pair G A E U₁ e' Y' :=
      { toSec21Std := hpair.toSec21Std
        mem_E := hpair.mem_E
        mem_U := hU₁
        mem_pair := hpY }
    exact ⟨U₁, Y', hpY'⟩
  by_cases hecd : e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm c hcA d hdA) hc3 hd3 hecd
    interval_cases i
    · exfalso
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    · rw [pow_one]
      exact sec21Pair_of_coset hpair hEeq hw'N hd3 hw'd hw'A hcA
        (hw'mv c hcA (by rw [sup_comm]; exact hcDA)) hj
    · have hc2 : c ^ 2 = c⁻¹ := Item21LateProof.sq_eq_inv_of_pow_three hc3
      have hc2A : c ^ 2 ∈ A := Subgroup.pow_mem _ hcA 2
      have hc2mv : w' * c ^ 2 * w'⁻¹ ≠ c ^ 2 := by
        intro h
        apply hw'mv c hcA (by rw [sup_comm]; exact hcDA)
        have h1 : w' * c⁻¹ * w'⁻¹ = c⁻¹ := by rw [← hc2]; exact h
        calc w' * c * w'⁻¹ = (w' * c⁻¹ * w'⁻¹)⁻¹ := by group
          _ = c := by rw [h1, inv_inv]
      obtain ⟨U', K, hp⟩ := sec21Pair_of_coset (x := c ^ 2) (by rw [hc2]; exact sec21Pair_inv hpair)
        hEeq hw'N hd3 hw'd hw'A hc2A hc2mv hj
      exact ⟨U', K, hp⟩
  · by_cases head : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d
    ·
      obtain ⟨i, hi, j, hj, rfl⟩ :=
        Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm a haA d hdA) ha3 hd3 head
      interval_cases i
      · exfalso
        apply hed
        rw [pow_zero, one_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
      · rw [pow_one]
        exact sec21Pair_of_coset hpair' hEeq hwN hd3 hwd hwA haA (hwmv a haA haCD) hj
      · have ha2 : a ^ 2 = a⁻¹ := Item21LateProof.sq_eq_inv_of_pow_three ha3
        have ha2A : a ^ 2 ∈ A := Subgroup.pow_mem _ haA 2
        have ha2mv : w * a ^ 2 * w⁻¹ ≠ a ^ 2 := by
          intro h
          apply hwmv a haA haCD
          have h1 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← ha2]; exact h
          calc w * a * w⁻¹ = (w * a⁻¹ * w⁻¹)⁻¹ := by group
            _ = a := by rw [h1, inv_inv]
        obtain ⟨U', K, hp⟩ := sec21Pair_of_coset (x := a ^ 2)
          (by rw [ha2]; exact sec21Pair_inv hpair') hEeq hwN hd3 hwd hwA ha2A ha2mv hj
        exact ⟨U', K, hp⟩
    · by_cases heac : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c
      ·
        have hBA : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ A :=
          sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hcA)
        have hdB : d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
          rw [sup_comm]
          exact not_mem_sup_swap (hcomm c hcA d hdA) (hcomm c hcA a haA) hc3 hd3 ha3 hc1 hdc
            haCD
        have hedA : e * d ∈ A := A.mul_mem he hdA
        have hdmem : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
        have hdmem' : d ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
        have hecd' : e * d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := fun h =>
          hecd (by simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hdmem))
        have head' : e * d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d := fun h =>
          head (by simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hdmem'))
        have heac' : e * d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := fun h =>
          hdB (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ heac) h)
        obtain ⟨U', K, hp⟩ := hoff (e * d) hedA hecd' head' heac'
        obtain ⟨U'', K', hp'⟩ := sec21Pair_of_coset hp hEeq hwN hd3 hwd hwA hedA
          (hwmv _ hedA hecd') (show 2 < 3 by norm_num)
        refine ⟨U'', K', ?_⟩
        have e1 : e * d * d ^ 2 = e := by rw [mul_assoc, ← pow_succ', hd3, mul_one]
        rwa [e1] at hp'
      · exact hoff e he hecd head heac

theorem exists_mover
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X)
    (h23 : Concl2123 L X c d) {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) :
    ∃ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 ∧ x * d * x⁻¹ = d ∧
      (∀ y ∈ A, y⁻¹ * (x * y * x⁻¹) ∈ Subgroup.zpowers d) ∧ x * e * x⁻¹ ≠ e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have ha1 : a ≠ 1 := hpairs'.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have ha3 : a ^ 3 = 1 := h3 a haA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, hw3, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, hw'3, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 hc3 hd1 hcd
  have haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := not_mem_sup_of_config2119End hE
  have had : a ∉ Subgroup.zpowers d := fun h => haCD (Subgroup.mem_sup_right h)
  have hda9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA a haA) hd3 ha3 hd1 had
  have haDC : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact haCD
  have hcDA : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a :=
    not_mem_sup_swap (hcomm d hdA c hcA) (hcomm d hdA a haA) hd3 hc3 ha3 hd1 hcd haDC
  by_cases hecd : e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  ·
    refine ⟨w', hw'N, hw'3, hw'd, hw'A, ?_⟩
    obtain ⟨i, hi, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm c hcA d hdA) hc3 hd3 hecd
    intro hfix
    have hw'c : w' * c * w'⁻¹ ≠ c := by
      intro hw'c
      obtain ⟨y, hyA, hy⟩ := hw'move
      exact hy (conj_eq_of_fix_basis hcomm h3 h27 haA hdA hcA hda9 hcDA hw'c hw'd hw'a y hyA)
    have hconjpow : ∀ (x : G) (m : ℕ), w' * x ^ m * w'⁻¹ = (w' * x * w'⁻¹) ^ m := fun x m => by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    have hdj : w' * d ^ j * w'⁻¹ = d ^ j := by rw [hconjpow, hw'd]
    have hci : w' * c ^ i * w'⁻¹ = c ^ i := by
      have h1 : w' * (c ^ i * d ^ j) * w'⁻¹ = (w' * c ^ i * w'⁻¹) * (w' * d ^ j * w'⁻¹) := by
        group
      rw [hfix, hdj] at h1
      exact (mul_right_cancel h1).symm
    interval_cases i
    · exfalso
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    · exact hw'c (by simpa using hci)
    · apply hw'c
      have hc4 : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
      calc w' * c * w'⁻¹ = w' * (c ^ 2) ^ 2 * w'⁻¹ := by rw [← hc4]
        _ = (w' * c ^ 2 * w'⁻¹) ^ 2 := hconjpow _ 2
        _ = c := by rw [hci, ← hc4]
  ·
    refine ⟨w, hwN, hw3, hwd, hwA, ?_⟩
    intro hwe
    have heDC : e ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
      rw [sup_comm]
      exact hecd
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA he hdc9 heDC hwe hwd hwc y hyA)

end Item2119End5Proof

open Item2119End5Proof

theorem exists_pair2127
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) {G : Type} [Group G] [Finite G] {A E U L U₀ X : Subgroup G}
    {c d a : G} (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))) {e : G} (he : e ∈ A)
    (hed : e ∉ Subgroup.zpowers d) : ∃ U' : Subgroup G, Pair2127 G A E U' e (Lf e) d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', K, hp⟩ := exists_sec21Pair h211 h2116 h45 h48 h66 hStar hE h23 h24 he hed
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  obtain ⟨hde, hcfgK⟩ := Item2119End4Proof.config2119_of_pair h211 h2115 h218 h2118 h45 h66 hp h27
    hdA hd1 hE.normal_d
  obtain ⟨hdK, -⟩ := Item2119End4Proof.mem_and_type_of_pair h45 h66 hcfgK hdA hd1 hde hE.normal_d
  obtain ⟨hLe, hLe3, hLeU, ⟨eLe⟩, hdLe, hdTLe, -⟩ := hLf e he hed
  have hK : K ∈ thetaComponentsAt 3 e := lZeroStarAt_subset A e hp.mem_pair.2.2.1
  have hK3 : 3 ∣ Nat.card K := by
    have h1 := orderOf_dvd_natCard (⟨d, hdK⟩ : K)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at h1
  have hKe : K = Lf e := hLeU K hK hK3
  subst hKe
  obtain ⟨eL4⟩ := h26
  refine ⟨U', ⟨hcfgK, ⟨hdA, hdLe⟩, hd1, hdTLe, hE.normal_d, ?_, hLeU, ⟨eLe.trans eL4⟩,
    exists_mover h211 h2116 h45 h66 hE h23 he hed⟩⟩
  rw [← h24]
  exact sup_le (starOf_le_wStar A X) (starOf_le_wStar A L)

end CFSG.RankThree.PartTwo.Sec21
