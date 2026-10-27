module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofCore
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofNormal
import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofComm
import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartOne.S10.PlaneLocalRankTwoLocal
import CFSG.RankThree.PartOne.S10.PlaneLocalRankContract

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof

open Item2129Res2Proof
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne.SourceSixThirteen
  (three_lt_localRank_iff_exists_elementary_abelian_normalizer)

variable {G : Type} [Group G] [Finite G] {F H Q Y : Subgroup G} {e d : G}

theorem le_normalizer_K (hL : Loc2129 F H Q Y e d) :
    Y ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  intro y hy
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hy hx'.1) (Y.inv_mem hy),
    hL.conj_mem_centralizer hy hx'.2⟩

theorem exists_sylow_R (hL : Loc2129 F H Q Y e d) :
    ∃ R : Subgroup G, IsSylowOf 3 R (Y ⊓ Subgroup.centralizer (H : Set G)) ∧
      Q ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hQP⟩ := Item2119End5Proof.exists_isSylowOf_ge hL.le_Q
    (Loc2129.isPGroup_of_pow hL.pow_Q)
  have hYK := le_normalizer_K hL
  refine ⟨P ⊓ (Y ⊓ Subgroup.centralizer (H : Set G)),
    hP.inf_of_le_normalizer inf_le_left hYK, ?_⟩
  exact (le_inf (hQP.trans Subgroup.le_normalizer) (hL.le_Q.trans hYK)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem exists_kap_eq_R (hL : Loc2129 F H Q Y e d) {R : Subgroup G}
    (hR : IsSylowOf 3 R (Y ⊓ Subgroup.centralizer (H : Set G))) {h : G} (hh : h ∈ H) :
    ∃ r ∈ R, e⁻¹ * (r * e * r⁻¹) = h := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKY : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Y := inf_le_left
  have hKH : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.centralizer (H : Set G) :=
    inf_le_right
  have hsurj : Function.Surjective (hL.kapHom _ hKY hKH) := by
    intro h
    obtain ⟨x, hxK, hxh⟩ := hL.exists_kap_eq_of_cent h.2
    exact ⟨⟨x, hxK⟩, Subtype.ext (by rw [hL.kapHom_apply]; exact hxh)⟩
  have hidx := Subgroup.index_map_dvd
    (H := R.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))) hsurj
  have hnd : ¬ 3 ∣ (R.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hR).2.2
  have hdvd9 : ((R.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).map
      (hL.kapHom _ hKY hKH)).index ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hL.card_H]
    exact Subgroup.index_dvd_card (G := H) (H := _)
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9
  have hk0 : k = 0 := by
    by_contra hk0
    apply hnd
    rw [hke] at hidx
    exact (dvd_pow_self 3 hk0).trans hidx
  rw [hk0, pow_zero, Subgroup.index_eq_one] at hke
  have hmem : (⟨h, hh⟩ : H) ∈ (R.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).map
      (hL.kapHom _ hKY hKH) := by
    rw [hke]
    exact Subgroup.mem_top _
  obtain ⟨p, hp, hph⟩ := hmem
  refine ⟨p, Subgroup.mem_subgroupOf.mp hp, ?_⟩
  have h2 := congrArg Subtype.val hph
  rw [hL.kapHom_apply] at h2
  exact h2

theorem exists_frattini (hL : Loc2129 F H Q Y e d) {R : Subgroup G}
    (hR : IsSylowOf 3 R (Y ⊓ Subgroup.centralizer (H : Set G))) {m : G} (hm : m ∈ Y) :
    ∃ k ∈ Y ⊓ Subgroup.centralizer (F : Set G), k⁻¹ * m ∈ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYK := le_normalizer_K hL
  have hRK : R ≤ Y ⊓ Subgroup.centralizer (H : Set G) := hR.le
  have hR'K : R.map (MulAut.conj m).toMonoidHom ≤ Y ⊓ Subgroup.centralizer (H : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hYK hm) r).mp (hRK hr)
  have hR'S : IsSylowOf 3 (R.map (MulAut.conj m).toMonoidHom)
      (Y ⊓ Subgroup.centralizer (H : Set G)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hR'K ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hR.card_eq
  obtain ⟨g, hgK, hg⟩ := hR.exists_mem_conj hR'S
  obtain ⟨r, hrR, hrg⟩ := exists_kap_eq_R hL hR (hL.kap_mem hgK.1)
  have hrK := hRK hrR
  have hrinvK : r⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.inv_mem _ hrK
  have hκ : e⁻¹ * (g * r⁻¹ * e * (g * r⁻¹)⁻¹) = 1 := by
    rw [hL.kap_mul hgK.1 hgK.2 hrinvK.1, kap_inv hL hrK, hrg, mul_inv_cancel]
  have hgr : g * r⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.mul_mem _ hgK hrinvK
  refine ⟨g * r⁻¹, ⟨hgr.1, hL.mem_centralizer_F hgr.2 (Loc2129.kap_eq_one_iff.mp hκ)⟩, ?_⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have h1 : m * x * m⁻¹ ∈ R.map (MulAut.conj m).toMonoidHom := ⟨x, hx, rfl⟩
  have h2 := (hg _).mp h1
  have h3 : r * (g⁻¹ * (m * x * m⁻¹) * g) * r⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem hrR h2) (R.inv_mem hrR)
  rw [show (g * r⁻¹)⁻¹ * m * x * ((g * r⁻¹)⁻¹ * m)⁻¹ =
    r * (g⁻¹ * (m * x * m⁻¹) * g) * r⁻¹ by group]
  exact h3

theorem loc2129_inf_normalizer (hL : Loc2129 F H Q Y e d) {R : Subgroup G}
    (hR : IsSylowOf 3 R (Y ⊓ Subgroup.centralizer (H : Set G)))
    (hQR : Q ≤ Subgroup.normalizer (R : Set G)) :
    Loc2129 F H Q (Y ⊓ Subgroup.normalizer (R : Set G)) e d :=
  { comm_F := hL.comm_F
    pow_F := hL.pow_F
    card_F := hL.card_F
    le_H := hL.le_H
    card_H := hL.card_H
    mem_e := hL.mem_e
    not_mem_e := hL.not_mem_e
    mem_d := hL.mem_d
    ne_one_d := hL.ne_one_d
    le_Q := le_inf hL.le_Q hQR
    le_F_Q := hL.le_F_Q
    card_Q := hL.card_Q
    extra_Q := hL.extra_Q
    pow_Q := hL.pow_Q
    conj_d := hL.conj_d
    conj_e_Q := hL.conj_e_Q
    le_normalizer := inf_le_left.trans hL.le_normalizer
    triv := fun y hy => hL.triv y hy.1
    trans := by
      intro v hv w hw hv1 hw1
      obtain ⟨m, hmY, hme, hmvw⟩ := hL.trans v hv w hw hv1 hw1
      obtain ⟨k, hkC, hkm⟩ := exists_frattini hL hR hmY
      have hke : k * e = e * k := (Subgroup.mem_centralizer_iff.mp hkC.2 e hL.mem_e).symm
      have hkw : k * w = w * k :=
        (Subgroup.mem_centralizer_iff.mp hkC.2 w (hL.le_H hw)).symm
      refine ⟨k⁻¹ * m, ⟨Y.mul_mem (Y.inv_mem hkC.1) hmY, hkm⟩, ?_, ?_⟩
      · calc k⁻¹ * m * e = k⁻¹ * (e * m) := by rw [mul_assoc, hme]
          _ = k⁻¹ * (e * k) * k⁻¹ * m := by group
          _ = k⁻¹ * (k * e) * k⁻¹ * m := by rw [hke]
          _ = e * (k⁻¹ * m) := by group
      · calc k⁻¹ * m * v * (k⁻¹ * m)⁻¹ = k⁻¹ * (m * v * m⁻¹) * k := by group
          _ = k⁻¹ * (w * k) := by rw [hmvw, mul_assoc]
          _ = k⁻¹ * (k * w) := by rw [hkw]
          _ = w := by group
    le_F := hL.le_F
    card_le_27 := hL.card_le_27
    card_le_729 := fun X hX3 hXY => hL.card_le_729 X hX3 (hXY.trans inf_le_left)
    exists_t := by
      obtain ⟨t, htY, htH⟩ := hL.exists_t
      obtain ⟨k, hkC, hkt⟩ := exists_frattini hL hR htY
      refine ⟨k⁻¹ * t, ⟨Y.mul_mem (Y.inv_mem hkC.1) htY, hkt⟩, fun h hh => ?_⟩
      have hkh : k * h⁻¹ = h⁻¹ * k :=
        (Subgroup.mem_centralizer_iff.mp hkC.2 h⁻¹ (hL.le_H (H.inv_mem hh))).symm
      calc k⁻¹ * t * h * (k⁻¹ * t)⁻¹ = k⁻¹ * (t * h * t⁻¹) * k := by group
        _ = k⁻¹ * (h⁻¹ * k) := by rw [htH h hh, mul_assoc]
        _ = k⁻¹ * (k * h⁻¹) := by rw [hkh]
        _ = h⁻¹ := by group }

theorem comm_inf_normalizer (hL : Loc2129 F H Q Y e d) {R : Subgroup G}
    (hR : IsSylowOf 3 R (Y ⊓ Subgroup.centralizer (H : Set G))) :
    ∀ x ∈ (Y ⊓ Subgroup.normalizer (R : Set G)) ⊓ Subgroup.centralizer (H : Set G),
      ∀ o ∈ (Y ⊓ Subgroup.normalizer (R : Set G)) ⊓ Subgroup.centralizer (F : Set G),
        (∃ n : ℕ, x ^ 3 ^ n = 1) → Nat.Coprime (orderOf o) 3 → x * o = o * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRK : R ≤ Y ⊓ Subgroup.centralizer (H : Set G) := hR.le
  have hR3 : IsPGroup 3 R := hR.isPGroup
  intro x hx o ho ⟨n, hxn⟩ ho3
  have hxK : x ∈ Y ⊓ Subgroup.centralizer (H : Set G) := ⟨hx.1.1, hx.2⟩
  have hxR : x ∈ R := by
    have hZN : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) :=
      Subgroup.zpowers_le.mpr hx.1.2
    have h3 : IsPGroup 3 (Subgroup.zpowers x ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (Loc2129.isPGroup_zpowers hxn) hR3 hZN
    have heq := hR.eq_of_le le_sup_right (sup_le (Subgroup.zpowers_le.mpr hxK) hRK) h3
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hoY : o ∈ Y := ho.1.1
  have hoH : o ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.centralizer_le (show (H : Set G) ⊆ F from hL.le_H) ho.2
  have hoR : ∀ r ∈ R, o * r = r * o := by
    intro r hr
    have hrK := hRK hr
    have horR : o * r * o⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp ho.1.2 r).mp hr
    have hfR : r⁻¹ * (o * r * o⁻¹) ∈ R := R.mul_mem (R.inv_mem hr) horR
    have hfK := hRK hfR
    have hκ : e⁻¹ * (r⁻¹ * (o * r * o⁻¹) * e * (r⁻¹ * (o * r * o⁻¹))⁻¹) = 1 := by
      have horY : o * r * o⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hoY hrK.1) (Y.inv_mem hoY)
      have hrinvK : r⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.inv_mem _ hrK
      have hκr : e⁻¹ * (r * e * r⁻¹) ∈ H := hL.kap_mem hrK.1
      have hoκ : o * (e⁻¹ * (r * e * r⁻¹)) * o⁻¹ = e⁻¹ * (r * e * r⁻¹) := by
        have h1 := Subgroup.mem_centralizer_iff.mp hoH _ hκr
        rw [← h1]
        group
      rw [hL.kap_mul hrinvK.1 hrinvK.2 horY, hL.kap_conj hrK.1 hrK.2 hoY, hoκ, kap_inv hL hrK,
        inv_mul_cancel]
    have hfC : r⁻¹ * (o * r * o⁻¹) ∈ Subgroup.centralizer (F : Set G) :=
      hL.mem_centralizer_F hfK.2 (Loc2129.kap_eq_one_iff.mp hκ)
    have hfF : r⁻¹ * (o * r * o⁻¹) ∈ F := hL.le_F _ (hR3.to_le (Subgroup.zpowers_le.mpr hfR))
      (Subgroup.zpowers_le.mpr hfC) (Subgroup.mem_zpowers _)
    set f := r⁻¹ * (o * r * o⁻¹) with hf
    have hof : o * f * o⁻¹ = f := by
      have h1 := Subgroup.mem_centralizer_iff.mp ho.2 f hfF
      rw [← h1]
      group
    have hor : o * r * o⁻¹ = r * f := by rw [hf]; group
    have hind : ∀ k : ℕ, o ^ k * r * (o ^ k)⁻¹ = r * f ^ k := by
      intro k
      induction k with
      | zero => group
      | succ k ih =>
        calc o ^ (k + 1) * r * (o ^ (k + 1))⁻¹ = o * (o ^ k * r * (o ^ k)⁻¹) * o⁻¹ := by
              rw [pow_succ']
              group
          _ = o * (r * f ^ k) * o⁻¹ := by rw [ih]
          _ = (o * r * o⁻¹) * (o * f * o⁻¹) ^ k := by rw [conj_pow]; group
          _ = r * f * f ^ k := by rw [hor, hof]
          _ = r * f ^ (k + 1) := by rw [pow_succ']; group
    have hfo : f ^ orderOf o = 1 := by
      have h := hind (orderOf o)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
      exact mul_eq_left.mp h.symm
    have hf1 : f = 1 := by
      have h1 : orderOf f ∣ orderOf o := orderOf_dvd_of_pow_eq_one hfo
      have h2 : orderOf f ∣ 3 := orderOf_dvd_of_pow_eq_one (hL.pow_F f hfF)
      have h3 : orderOf f ∣ Nat.gcd (orderOf o) 3 := Nat.dvd_gcd h1 h2
      rw [ho3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    calc o * r = o * r * o⁻¹ * o := by group
      _ = r * f * o := by rw [hor]
      _ = r * o := by rw [hf1, mul_one]
  exact (hoR x hxR).symm

theorem exists_E81 (hL : Loc2129 F H Q Y e d) :
    ∃ S : Subgroup G, S ≤ Y ∧ CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S = 81 := by
  obtain ⟨R, hR, hQR⟩ := exists_sylow_R hL
  have hL' := loc2129_inf_normalizer hL hR hQR
  obtain ⟨R'', hR''⟩ := hL'.exists_R (comm_inf_normalizer hL hR)
  obtain ⟨S, hSY, -, hSe, hS81, -⟩ := hR''.exists_S hL'
  exact ⟨S, hSY.trans inf_le_left, hSe, hS81⟩

theorem odd_card_centralizer (hL : Loc2129 F H Q Y e d)
    (hrank : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3) :
    Odd (Nat.card (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSY, hSe, hS81⟩ := exists_E81 hL
  have hSC : S ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := by
    intro s hs
    exact Subgroup.mem_normalizer_fintype fun x hx => conj_mem_C hL (hSY hs) hx
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hFC : F ≤ Y ⊓ Subgroup.centralizer (F : Set G) :=
    le_inf hL.le_F_Y fun f hf => Subgroup.mem_centralizer_iff.mpr fun x hx => hL.comm_F x hx f hf
  have hFS : IsSylowOf 3 F (Y ⊓ Subgroup.centralizer (F : Set G)) := by
    obtain ⟨S₃, hS₃, hFS₃⟩ := Item2119End5Proof.exists_isSylowOf_ge hFC hL.isPGroup_F
    have hS₃F : S₃ ≤ F := hL.le_F S₃ hS₃.isPGroup (hS₃.le.trans inf_le_right)
    rwa [le_antisymm hS₃F hFS₃] at hS₃
  have hn : ¬ 3 ∣ Nat.card (Sylow 2 (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)) := by
    obtain ⟨T⟩ := (inferInstance :
      Nonempty (Sylow 2 (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)))
    rw [Sylow.card_eq_index_normalizer T]
    intro h3
    apply (CFSG.ABGLocalTools.isSylowOf_iff.mp hFS).2.2
    refine h3.trans (Subgroup.index_dvd_of_le ?_)
    intro f hf
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hfx : f * x * f⁻¹ = x := by
      have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 (f : G)
        (Subgroup.mem_subgroupOf.mp hf)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]
      group
    rw [hfx]
    exact hx
  have hS3 : IsPGroup 3 S := Loc2129.isPGroup_of_pow hSe.2
  let φ : S →* MulAut (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :=
    (Y ⊓ Subgroup.centralizer (F : Set G)).normalizerMonoidHom.comp (Subgroup.inclusion hSC)
  let _ : MulDistribMulAction S (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :=
    MulDistribMulAction.compHom _ φ
  let _ : MulAction S (Sylow 2 (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)) :=
    Sylow.pointwiseMulAction
  obtain ⟨T, hT⟩ := hS3.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow 2 (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)) hn
  have hTinv : ∀ s : S, ∀ x ∈ (T : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) :
      Subgroup G)), s • x ∈ (T : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) :
      Subgroup G)) := by
    intro s x hx
    have hmem : s • x ∈ ((s • T : Sylow 2 (Y ⊓ Subgroup.centralizer (F : Set G) :
        Subgroup G)) : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨x, hx, rfl⟩
    rwa [hT s] at hmem
  have hST : S ≤ Subgroup.normalizer
      (((T : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)).map
        (Y ⊓ Subgroup.centralizer (F : Set G)).subtype : Subgroup G) : Set G) := by
    intro s hs
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hTinv ⟨s, hs⟩ x hx, rfl⟩
  have hT2 : IsPGroup 2 ((T : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) :
      Subgroup G)).map (Y ⊓ Subgroup.centralizer (F : Set G)).subtype) :=
    T.isPGroup'.map _
  have hTne : (T : Subgroup (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)).map
      (Y ⊓ Subgroup.centralizer (F : Set G)).subtype ≠ ⊥ := by
    intro hbot
    exact Sylow.ne_bot_of_dvd_card T h2
      ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hbot)
  have helem : CFSG.IsElementaryAbelian 3 S :=
    { toIsMulCommutative := hSe.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hSe.2 x x.2) }
  have h4 : 3 < CFSG.Assembly.RankThreeEven.localRank 3 G :=
    (three_lt_localRank_iff_exists_elementary_abelian_normalizer Nat.prime_three).mpr
      ⟨_, hT2, hTne, S, hST, helem, by rw [hS81]; norm_num⟩
  omega

end CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof
