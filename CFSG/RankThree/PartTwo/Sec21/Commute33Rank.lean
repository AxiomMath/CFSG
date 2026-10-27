module

public import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingMinimalOddCoreAction
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Commute33Tools
public import CFSG.RankThree.PartTwo.Sec21.Star22

public section

namespace CFSG.RankThree.PartTwo.Sec21.Commute33Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly (IsElemAbelian)
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_three_of_faithful [Finite G] {s : ℕ} [hs : Fact s.Prime] (hs3 : 3 < s)
    (hloc : localRank s G < 3) {D : Subgroup G} (hDp : IsPGroup s D)
    (hDexp : ∀ x ∈ D, x ^ s = 1)
    (hDcl : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⁅x, y⁆ * z = z * ⁅x, y⁆)
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (hVn : Nat.card V = 2 ^ n) (ι : V →* G) (hιD : ∀ v, ι v ∈ normalizer (D : Set G))
    (hfaith : ∀ v, ι v ∈ centralizer (D : Set G) → v = 1) : n ≤ 3 := by
  set ι' : V →* normalizer (D : Set G) := ι.codRestrict _ hιD with hι'
  let act : MulDistribMulAction V D :=
    MulDistribMulAction.compHom D (D.normalizerMonoidHom.comp ι')
  have hsmul : ∀ (v : V) (d : D), ((v • d : D) : G) = ι v * d * (ι v)⁻¹ := fun v d => rfl
  have hfaithS : FaithfulSMul V D := by
    refine ⟨fun {v₁ v₂} h => ?_⟩
    have hc : ι (v₁⁻¹ * v₂) ∈ centralizer (D : Set G) := by
      rw [mem_centralizer_iff]
      intro d hd
      have h1 := congrArg Subtype.val (h ⟨d, hd⟩)
      rw [hsmul, hsmul] at h1
      rw [map_mul, map_inv]
      calc d * ((ι v₁)⁻¹ * ι v₂) = (ι v₁)⁻¹ * (ι v₁ * d * (ι v₁)⁻¹) * ι v₂ := by group
        _ = (ι v₁)⁻¹ * (ι v₂ * d * (ι v₂)⁻¹) * ι v₂ := by rw [h1]
        _ = (ι v₁)⁻¹ * ι v₂ * d := by group
    have := hfaith _ hc
    rwa [inv_mul_eq_one] at this
  have hexp : Monoid.exponent D ∣ s := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hclass : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ]
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have := hDcl x x.2 y y.2 z z.2
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at this ⊢
    exact this.symm
  have hm : ∀ v : V, v ≠ 1 →
      CFSG.pRank s (CFSG.fixedPointSubgroup (Subgroup.zpowers v) D) ≤ 2 := by
    intro v hv
    set C := CFSG.fixedPointSubgroup (Subgroup.zpowers v) D
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht : orderOf (ι v) = 2 := orderOf_eq_prime (by rw [← map_pow, hV2, map_one])
      (fun h => hv (hfaith v (by rw [h]; exact Subgroup.one_mem _)))
    have hC : ∀ c ∈ C.map D.subtype, c * ι v = ι v * c := by
      rintro _ ⟨c, hc, rfl⟩
      have hfix : v • c = c := hc ⟨v, Subgroup.mem_zpowers v⟩
      have h1 := congrArg Subtype.val hfix
      rw [hsmul] at h1
      change (c : G) * ι v = ι v * c
      calc (c : G) * ι v = ι v * c * (ι v)⁻¹ * ι v := by rw [h1]
        _ = ι v * c := by group
    have h1 := Sec4.Census.pRank_le_localRank_of_centralizes hs.out (by omega) ht hC
    rw [← CFSG.RankThree.PartTwo.pRank_congr_mulEquiv hs.out.one_lt
      (C.equivMapOfInjective D.subtype D.subtype_injective)] at h1
    omega
  have h2x : ∀ x : Additive V, 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow]
    exact (congrArg Additive.ofMul (hV2 (Additive.toMul x))).trans ofMul_one
  have hbound := (@CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound s hs
    (hs.out.odd_of_ne_two (by omega)) D _ _ hDp hexp hclass V _ _
    (AddCommGroup.zmodModule (n := 2) h2x) n 2 hVn act hfaithS hm).1
  omega

theorem sq_eq_one_F4 : ∀ x : Multiplicative (Fin 2 → ZMod 2), x ^ 2 = 1 := by decide

theorem sq_eq_one_V (v : Multiplicative (Fin 2 → ZMod 2) × Multiplicative (Fin 2 → ZMod 2)) :
    v ^ 2 = 1 := Prod.ext (sq_eq_one_F4 _) (sq_eq_one_F4 _)

theorem eq_one_of_pow_two_pow {N : Subgroup G} [Finite G] (hN : Odd (Nat.card N)) {x : G}
    (hx : x ∈ N) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem mul_comm_of_sq_eq_one {S : Subgroup G} (hS : ∀ x ∈ S, x ^ 2 = 1) {x y : G} (hx : x ∈ S)
    (hy : y ∈ S) : x * y = y * x := by
  have hx2 : x * x = 1 := by rw [← sq]; exact hS x hx
  have hy2 : y * y = 1 := by rw [← sq]; exact hS y hy
  have hxy2 : (x * y) * (x * y) = 1 := by rw [← sq]; exact hS _ (S.mul_mem hx hy)
  calc x * y = x * y * ((y * x) * (y * x)) := by rw [← sq, hS _ (S.mul_mem hy hx), mul_one]
    _ = x * (y * y) * x * (y * x) := by group
    _ = y * x := by rw [hy2, mul_one, hx2, one_mul]

theorem centralizes_pCore_of_odd [Finite G]
    (hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s G < 3) {K J EK EJ : Subgroup G}
    [IsSimpleGroup K] [IsSimpleGroup J] (hK : ⁅K, K⁆ = K) (hJ : ⁅J, J⁆ = J)
    (hNs : Group.IsSolvable (⁅K, J⁆ : Subgroup G))
    (hNodd : Odd (Nat.card (⁅K, J⁆ : Subgroup G))) (hEKK : EK ≤ K) (hEJJ : EJ ≤ J)
    (hEK : IsElemAbelian 2 EK) (hEJ : IsElemAbelian 2 EJ) (hEK4 : Nat.card EK = 4)
    (hEJ4 : Nat.card EJ = 4) {s : ℕ} (hs : s.Prime) (hs3 : 3 < s) :
    K ≤ centralizer (inSubgroup (pCore s) (⁅K, J⁆ : Subgroup G) : Set G) ∨
      J ≤ centralizer (inSubgroup (pCore s) (⁅K, J⁆ : Subgroup G) : Set G) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hKQ', hJQ'⟩ := hcon
  have : Fact s.Prime := ⟨hs⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := ⁅K, J⁆ with hNdef
  set Q : Subgroup G := inSubgroup (pCore s) N with hQdef
  set W : Subgroup G := normalizer (Q : Set G) with hWdef
  have hKN : K ≤ normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left K J
  have hJN : J ≤ normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_right K J
  have hKW : K ≤ W := hKN.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s N)
  have hJW : J ≤ W := hJN.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s N)
  have hNW : N ≤ W := SteinbergBY.le_normalizer_inSubgroup_pCore s N
  have hNconj : ∀ g ∈ normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (mem_normalizer_iff.mp hg n).mp hn
  set C : Subgroup G := W ⊓ centralizer (Q : Set G) with hCdef
  have hFK : ∀ e ∈ K, e ≠ 1 → ¬ ∀ k ∈ K, ⁅e, k⁆ ∈ C ⊔ N := fun e he he1 h =>
    hKQ' (le_centralizer_of_commutator_mem hK hKW hNW hKN hNs he he1 h)
  have hFJ : ∀ e ∈ J, e ≠ 1 → ¬ ∀ k ∈ J, ⁅e, k⁆ ∈ C ⊔ N := by
    have hJN' : J ≤ normalizer (N : Set G) := hJN
    exact fun e he he1 h =>
      hJQ' (le_centralizer_of_commutator_mem hJ hJW hNW hJN' hNs he he1 h)
  have hWC : W ≤ normalizer (C : Set G) := normalizer_le_normalizer_inf_centralizer Q
  have hQp : IsPGroup s Q := (pCore_isPGroup (p := s) (G := N)).map N.subtype
  have hQnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hKQ'
    intro k _
    rw [mem_centralizer_iff]
    intro q hq
    have hq1 : q = 1 := congrArg Subtype.val (Subsingleton.elim (⟨q, hq⟩ : Q) 1)
    rw [hq1, one_mul, mul_one]
  obtain ⟨D₀, hD₀c, -, hD₀comm, hD₀exp, hD₀fix⟩ :=
    SectionRank.Ccomm.odd_critical_exponent_subgroup (p := s) (P := Q) (by omega) hQp
  set D : Subgroup G := D₀.map Q.subtype with hDdef
  have hWD : W ≤ normalizer (D : Set G) :=
    SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic Q D₀
  set Y : Subgroup G := N ⊔ EJ with hYdef
  have hEJN : EJ ≤ normalizer (N : Set G) := hEJJ.trans hJN
  have hYset : (Y : Set G) = (N : Set G) * (EJ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N EJ hEJN
  have hmemY : ∀ y, y ∈ Y → ∃ n ∈ N, ∃ j ∈ EJ, n * j = y := fun y hy => by
    rw [← SetLike.mem_coe, hYset] at hy
    exact hy
  have hcommNK : ∀ n ∈ N, ∀ k ∈ K, ⁅n, k⁆ ∈ N := fun n hn k hk => by
    have h1 : k * n⁻¹ * k⁻¹ ∈ N := hNconj k (hKN hk) _ (N.inv_mem hn)
    have e1 : ⁅n, k⁆ = n * (k * n⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [e1]
    exact N.mul_mem hn h1
  have hcommNJ : ∀ n ∈ N, ∀ k ∈ J, ⁅n, k⁆ ∈ N := fun n hn k hk => by
    have h1 : k * n⁻¹ * k⁻¹ ∈ N := hNconj k (hJN hk) _ (N.inv_mem hn)
    have e1 : ⁅n, k⁆ = n * (k * n⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [e1]
    exact N.mul_mem hn h1
  have hYK : ∀ y ∈ Y, ∀ k ∈ K, ⁅y, k⁆ ∈ N := by
    intro y hy k hk
    obtain ⟨n, hn, j, hj, rfl⟩ := hmemY y hy
    have e1 : ⁅n * j, k⁆ = n * ⁅j, k⁆ * n⁻¹ * ⁅n, k⁆ := by
      simp only [commutatorElement_def]
      group
    have hjk : ⁅j, k⁆ ∈ N := by
      have := N.inv_mem (Subgroup.commutator_mem_commutator hk (hEJJ hj))
      rwa [commutatorElement_inv] at this
    rw [e1]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hjk) (N.inv_mem hn)) (hcommNK n hn k hk)
  have hKY : K ≤ normalizer (Y : Set G) := le_normalizer_of_forall_mul_mem fun e he y hy => by
    obtain ⟨n, hn, j, hj, rfl⟩ := hmemY y hy
    have e1 : e * (n * j) * e⁻¹ = (e * n * e⁻¹) * ⁅e, j⁆ * j := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact Subgroup.mul_mem_sup (N.mul_mem (hNconj e (hKN he) n hn)
      (Subgroup.commutator_mem_commutator he (hEJJ hj))) hj
  have hEKY : EK ≤ normalizer (Y : Set G) := hEKK.trans hKY
  let _ : MulDistribMulAction EK Y := PartOne.conjActionOn hEKY
  have hEK2 : IsPGroup 2 EK := IsPGroup.of_card (n := 2) (by rw [hEK4]; norm_num)
  have hEJ2 : IsPGroup 2 EJ := IsPGroup.of_card (n := 2) (by rw [hEJ4]; norm_num)
  have hcardSyl : ¬ 2 ∣ Nat.card (Sylow 2 Y) := by
    have h1 := card_sylow_modEq_one 2 Y
    rintro ⟨c, hc⟩
    rw [Nat.ModEq, hc] at h1
    omega
  obtain ⟨P, hP⟩ := hEK2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 Y) hcardSyl
  set P' : Subgroup G := (P : Subgroup Y).map Y.subtype with hP'def
  have hP'Y : P' ≤ Y := map_subtype_le _
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map Y.subtype
  have hEKP : ∀ e ∈ EK, ∀ p ∈ P', e * p * e⁻¹ ∈ P' := by
    rintro e he _ ⟨p, hp, rfl⟩
    have hfix : (⟨e, he⟩ : EK) • P = P := hP ⟨e, he⟩
    have hmem : (⟨e, he⟩ : EK) • p ∈ (P : Subgroup Y) := by
      rw [← hfix, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul p _ _ hp
    exact ⟨_, hmem, rfl⟩
  have hP'N : ∀ p ∈ P', p ∈ N → p = 1 := fun p hp hpN => by
    obtain ⟨k, hk⟩ := hP'2 ⟨p, hp⟩
    exact eq_one_of_pow_two_pow hNodd hpN (by simpa using congrArg Subtype.val hk)
  have hEKPc : ∀ e ∈ EK, ∀ p ∈ P', e * p = p * e := by
    intro e he p hp
    have h1 : ⁅p, e⁆ ∈ N := hYK p (hP'Y hp) e (hEKK he)
    have h2 : ⁅p, e⁆ ∈ P' := by
      have e1 : ⁅p, e⁆ = p * (e * p⁻¹ * e⁻¹) := by rw [commutatorElement_def]; group
      rw [e1]
      exact P'.mul_mem hp (hEKP e he _ (P'.inv_mem hp))
    have h3 := hP'N _ h2 h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hP'exp : ∀ p ∈ P', p ^ 2 = 1 := by
    intro p hp
    obtain ⟨n, hn, j, hj, hnj⟩ := hmemY p (hP'Y hp)
    have hj2 : j ^ 2 = 1 := hEJ.2 j hj
    have hsq : p ^ 2 ∈ N := by
      rw [← hnj]
      have e1 : (n * j) ^ 2 = n * (j * n * j⁻¹) * j ^ 2 := by rw [sq, sq]; group
      rw [e1, hj2, mul_one]
      exact N.mul_mem hn (hNconj j (hEJN hj) n hn)
    exact hP'N _ (P'.pow_mem hp 2) hsq
  have hP'le : Nat.card P' ≤ 4 := by
    have hdec : ∀ p : P', ∃ j : EJ, (p : G) * (j : G)⁻¹ ∈ N := fun p => by
      obtain ⟨n, hn, j, hj, hnj⟩ := hmemY p (hP'Y p.2)
      exact ⟨⟨j, hj⟩, by rw [← hnj, mul_inv_cancel_right]; exact hn⟩
    choose f hf using hdec
    have hfinj : Function.Injective f := by
      intro p q hpq
      have h1 : (p : G) * (q : G)⁻¹ ∈ N := by
        have := N.mul_mem (hf p) (N.inv_mem (hf q))
        rw [hpq] at this
        simpa [mul_assoc] using this
      have h2 := hP'N _ (P'.mul_mem p.2 (P'.inv_mem q.2)) h1
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    rw [← hEJ4]
    exact Nat.card_le_card_of_injective f hfinj
  have hP'ge : 4 ≤ Nat.card P' := by
    obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow (p := 2) (P := EJ.subgroupOf Y)
      (hEJ2.comap_subtype)
    have hc1 : Nat.card P' = Nat.card (P : Subgroup Y) :=
      Subgroup.card_map_of_injective Y.subtype_injective
    have hc2 : Nat.card (P : Subgroup Y) = Nat.card (S₀ : Subgroup Y) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hc3 : Nat.card (EJ.subgroupOf Y) = 4 := by
      rw [← hEJ4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [hc1, hc2, ← hc3]
    exact Subgroup.card_le_of_le hS₀
  have hP'4 : Nat.card P' = 2 ^ 2 := by omega
  have hEK4' : Nat.card EK = 2 ^ 2 := by rw [hEK4]; norm_num
  obtain ⟨eK⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := EK)
    (fun a b => hEK.1.is_comm.comm a b) (fun a => Subtype.ext (hEK.2 a a.2)) hEK4'
  obtain ⟨eP⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := P')
    (fun a b => Subtype.ext (mul_comm_of_sq_eq_one hP'exp a.2 b.2))
    (fun a => Subtype.ext (hP'exp a a.2)) hP'4
  set ιK : Multiplicative (Fin 2 → ZMod 2) →* G := EK.subtype.comp eK.symm.toMonoidHom
  set ιP : Multiplicative (Fin 2 → ZMod 2) →* G := P'.subtype.comp eP.symm.toMonoidHom
  have hιK : ∀ a, ιK a ∈ EK := fun a => (eK.symm a).2
  have hιP : ∀ b, ιP b ∈ P' := fun b => (eP.symm b).2
  have hιKinj : ∀ a, ιK a = 1 → a = 1 := fun a h => by
    have : eK.symm a = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at this
  have hιPinj : ∀ b, ιP b = 1 → b = 1 := fun b h => by
    have : eP.symm b = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at this
  set ι := ιK.noncommCoprod ιP (fun a b => hEKPc _ (hιK a) _ (hιP b)) with hιdef
  have hιapp : ∀ v, ι v = ιK v.1 * ιP v.2 := fun v => MonoidHom.noncommCoprod_apply _ _ _ v
  have hYW : Y ≤ W := sup_le hNW (hEJJ.trans hJW)
  have hιW : ∀ v, ι v ∈ W := fun v => by
    rw [hιapp]
    exact W.mul_mem (hKW (hEKK (hιK v.1))) (hYW (hP'Y (hιP v.2)))
  have hfaith : ∀ v, ι v ∈ centralizer (D : Set G) → v = 1 := by
    intro v hvD
    set e := ιK v.1
    set p := ιP v.2
    have hv2 : ι v ^ 2 = 1 := by
      rw [← map_pow, sq_eq_one_V v, map_one]
    have hT2 : IsPGroup 2 (Subgroup.zpowers (ι v)) := fun g => ⟨1, by
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv2, one_zpow]⟩
    have hvQ : ι v ∈ centralizer (Q : Set G) :=
      PartOne.le_centralizer_of_centralizes_critical_subgroup hs (by omega)
        (Subgroup.zpowers_le.mpr (hιW v)) hT2 D₀ hD₀fix (Subgroup.zpowers_le.mpr hvD)
        (Subgroup.mem_zpowers _)
    have hvC : ι v ∈ C := ⟨hιW v, hvQ⟩
    have hCconj : ∀ g ∈ W, ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g hg c hc =>
      (mem_normalizer_iff.mp (hWC hg) c).mp hc
    have hcommC : ∀ k ∈ W, ⁅ι v, k⁆ ∈ C := fun k hk => by
      have e1 : ⁅ι v, k⁆ = ι v * (k * (ι v)⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e1]
      exact C.mul_mem hvC (hCconj k hk _ (C.inv_mem hvC))
    have he : ιK v.1 = 1 := by
      by_contra he1
      apply hFK _ (hEKK (hιK v.1)) he1
      intro k hk
      have hpk : ⁅ιP v.2, k⁆ ∈ N := hYK _ (hP'Y (hιP v.2)) k hk
      have e1 : ⁅ιK v.1, k⁆ =
          (ιK v.1 * ⁅ιP v.2, k⁆ * (ιK v.1)⁻¹)⁻¹ * ⁅ιK v.1 * ιP v.2, k⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1, ← hιapp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
          (N.inv_mem (hNconj _ (hKN (hEKK (hιK v.1))) _ hpk)))
        (Subgroup.mem_sup_left (hcommC k (hKW hk)))
    have hp : ιP v.2 = 1 := by
      by_contra hp1
      obtain ⟨n, hn, j, hj, hnj⟩ := hmemY _ (hP'Y (hιP v.2))
      have hj1 : j ≠ 1 := by
        rintro rfl
        rw [mul_one] at hnj
        exact hp1 (hP'N _ (hιP v.2) (hnj ▸ hn))
      apply hFJ j (hEJJ hj) hj1
      intro k hk
      have hpC : ⁅ιP v.2, k⁆ ∈ C := by
        have := hcommC k (hJW hk)
        rwa [hιapp, he, one_mul] at this
      have e1 : ⁅j, k⁆ = (n⁻¹ * ⁅ιP v.2, k⁆ * n) * (n⁻¹ * ⁅n, k⁆⁻¹ * n) := by
        rw [← hnj]
        simp only [commutatorElement_def]
        group
      rw [e1]
      have h1 : n⁻¹ * ⁅ιP v.2, k⁆ * n ∈ C := by
        have := hCconj n⁻¹ (hNW (N.inv_mem hn)) _ hpC
        rwa [inv_inv] at this
      have h2 : n⁻¹ * ⁅n, k⁆⁻¹ * n ∈ N :=
        N.mul_mem (N.mul_mem (N.inv_mem hn) (N.inv_mem (hcommNJ n hn k hk))) hn
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    exact Prod.ext (hιKinj _ he) (hιPinj _ hp)
  have hDp : IsPGroup s D := (hQp.to_subgroup D₀).map Q.subtype
  have hDexp : ∀ x ∈ D, x ^ s = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD₀exp d hd, map_one]
  have hDcl : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩ _ ⟨c, hc, rfl⟩
    have h1 : ⁅a, b⁆ ∈ D₀ ⊓ centralizer (D₀ : Set Q) :=
      hD₀comm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
    have h2 := mem_centralizer_iff.mp h1.2 c hc
    rw [← map_commutatorElement, ← map_mul, ← map_mul, h2]
  have hVn : Nat.card (Multiplicative (Fin 2 → ZMod 2) × Multiplicative (Fin 2 → ZMod 2)) =
      2 ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have h4 := le_three_of_faithful (V := Multiplicative (Fin 2 → ZMod 2) ×
    Multiplicative (Fin 2 → ZMod 2)) hs3 (hloc s hs hs3) hDp hDexp hDcl sq_eq_one_V hVn ι
    (fun v => hWD (hιW v)) hfaith
  omega

end CFSG.RankThree.PartTwo.Sec21.Commute33Steps
