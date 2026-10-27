module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res419Two

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open Equiv

theorem card_center_wreathW_le {H : Type*} [Group H] [Finite H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) : Nat.card (Subgroup.center (wreathW z t)) ≤ 3 := by
  have hz0 : z 0 ∈ wreathW z t := Subgroup.mem_sup_left (z_mem_baseA 0)
  have hsub : (Subgroup.center (wreathW z t)).map (wreathW z t).subtype ≤
      Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, j, hxv⟩ := mem_wreathW hf x.2
    have hct : t * (x : H) = (x : H) * t :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨t, t_mem_wreathW⟩)
    have hcz : z 0 * (x : H) = (x : H) * z 0 :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨z 0, hz0⟩)
    change (x : H) ∈ _
    rw [hxv] at hct hcz ⊢
    have hvz : vecElt z v * z 0 = z 0 * vecElt z v :=
      congrArg Subtype.val ((isElemAbelian_baseA hf).1.is_comm.comm
        ⟨_, vecElt_mem_baseA hf v⟩ ⟨_, z_mem_baseA 0⟩)
    have htj : t ^ (j : ℕ) * z 0 = z 0 * t ^ (j : ℕ) := by
      have h1 : vecElt z v * (t ^ (j : ℕ) * z 0) = vecElt z v * (z 0 * t ^ (j : ℕ)) :=
        calc vecElt z v * (t ^ (j : ℕ) * z 0) = vecElt z v * t ^ (j : ℕ) * z 0 :=
              (mul_assoc _ _ _).symm
          _ = z 0 * (vecElt z v * t ^ (j : ℕ)) := hcz.symm
          _ = z 0 * vecElt z v * t ^ (j : ℕ) := (mul_assoc _ _ _).symm
          _ = vecElt z v * z 0 * t ^ (j : ℕ) := by rw [hvz]
          _ = vecElt z v * (z 0 * t ^ (j : ℕ)) := mul_assoc _ _ _
      exact mul_left_cancel h1
    have hj : j = 0 := by
      by_contra hj
      have hj12 : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by
        have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
        have := j.isLt
        omega
      have hconj : t ^ (j : ℕ) * z 0 * (t ^ (j : ℕ))⁻¹ = z 0 := by
        rw [htj, mul_inv_cancel_right]
      have hne : ∀ i : Fin 3, i ≠ 0 → z i ≠ z 0 := by
        intro i hi heq
        have h := vecElt_injective hf (show vecElt z (Pi.single i 1) = vecElt z (Pi.single 0 1) by
          rw [vecElt_single_one, vecElt_single_one, heq])
        have h' := congrFun h i
        simp only [Pi.single_eq_same, Pi.single_apply, hi, ite_false] at h'
        exact one_ne_zero h'
      rcases hj12 with h1 | h2
      · rw [h1, pow_one, hf.conj0] at hconj
        exact hne 1 (by decide) hconj
      · rw [h2, show t ^ 2 * z 0 * (t ^ 2)⁻¹ = t * (t * z 0 * t⁻¹) * t⁻¹ by
            rw [sq, mul_inv_rev]; simp only [mul_assoc], hf.conj0, hf.conj1] at hconj
        exact hne 2 (by decide) hconj
    subst hj
    simp only [Fin.val_zero, pow_zero, mul_one] at hct ⊢
    obtain ⟨h01, h12⟩ := eq_of_commute hf (j := 1) (by decide)
      (by rw [Fin.val_one, pow_one]; exact hct.symm)
    exact vecElt_mem_zpowers_of_const hf h01 h12
  calc Nat.card (Subgroup.center (wreathW z t))
      = Nat.card ((Subgroup.center (wreathW z t)).map (wreathW z t).subtype) :=
        (Subgroup.card_map_of_injective (wreathW z t).subtype_injective).symm
    _ ≤ Nat.card (Subgroup.zpowers (vecElt z ![1, 1, 1])) := Subgroup.card_le_of_le hsub
    _ ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one ((isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)))

theorem false_of_wreath {H : Type*} [Group H] [Finite H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81)
    (h3 : (Nat.card H).factorization 3 = 4) {K : Subgroup H} (hK : 27 ∣ Nat.card K)
    (hZ : Subgroup.center K = ⊥) {s : H} (hs : orderOf s = 3)
    (hsK : ∀ k ∈ K, s * k = k * s) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := K)
    (by norm_num; exact hK)
  set P : Subgroup H := P₀.map K.subtype with hPdef
  have hPcard : Nat.card P = 27 := by
    rw [hPdef, Subgroup.card_map_of_injective K.subtype_injective, hP₀]
    norm_num
  have hPK : P ≤ K := Subgroup.map_subtype_le P₀
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPcard]; norm_num)
  have hsK' : s ∉ K := by
    intro hs'
    have hmem : (⟨s, hs'⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hsK g g.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    have h1 : s = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hs
    norm_num at hs
  have hint : ∀ y ∈ P, y ∈ Subgroup.zpowers s → y = 1 := by
    intro y hyP hys
    by_contra hy1
    have hyo : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 := by
        rw [← hs]
        exact orderOf_dvd_of_mem_zpowers hys
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h
    have hzs : Subgroup.zpowers y = Subgroup.zpowers s := by
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hys)
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hs]
    have : s ∈ Subgroup.zpowers y := hzs ▸ Subgroup.mem_zpowers s
    exact hsK' (hPK ((Subgroup.zpowers_le.mpr hyP) this))
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer (P : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hhP
      rw [show s * h * s⁻¹ = h by rw [hsK h (hPK hhP), mul_inv_cancel_right]]
      exact hhP
    · intro hhP
      have hk : s * (s * h * s⁻¹) = (s * h * s⁻¹) * s := hsK _ (hPK hhP)
      have heq : s * h * s⁻¹ = h := mul_left_cancel (hk.trans (by group))
      exact heq ▸ hhP
  have hs3 : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  set Q : Subgroup H := P ⊔ Subgroup.zpowers s with hQdef
  have hQ3 : IsPGroup 3 Q := hP3.to_sup_of_normal_left' hs3 hsN
  have hPQ : P ≤ Q := le_sup_left
  have hsQ : s ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hQcard : Nat.card Q = 81 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ3
    have hle := Sec4.Item434AltPerm.card_le_of_isPGroup hQ3
    rw [h3, hk] at hle
    have hk4 : k ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    have hdvd : Nat.card P ∣ Nat.card Q := Subgroup.card_dvd_of_le hPQ
    rw [hPcard, hk, show (27 : ℕ) = 3 ^ 3 by norm_num] at hdvd
    have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hk3' : k ≠ 3 := by
      rintro rfl
      have hPQe : P = Q := Subgroup.eq_of_le_of_card_ge hPQ (by rw [hk, hPcard]; norm_num)
      exact hsK' (hPK (hPQe ▸ hsQ))
    have : k = 4 := by omega
    rw [hk, this]
    norm_num
  have hWsyl : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3 := by
    rw [hW, h3]; norm_num
  obtain ⟨g, hg⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hWsyl hQ3
  have hQW : Q = (wreathW z t).map (MulAut.conj g).toMonoidHom := by
    apply Subgroup.eq_of_le_of_card_ge hg
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hW, hQcard]
  let eQ : wreathW z t ≃* Q :=
    ((wreathW z t).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hQW.symm)
  have hZQ : Nat.card (Subgroup.center Q) ≤ 3 := by
    rw [← Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
    exact card_center_wreathW_le hf
  have hPnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPcard]; norm_num
  have hZnt := hP3.center_nontrivial
  obtain ⟨y, hy1⟩ := exists_ne (1 : Subgroup.center P)
  have hyP : ((y : P) : H) ∈ P := (y : P).2
  have hy1' : ((y : P) : H) ≠ 1 := by
    intro h
    exact hy1 (Subtype.ext (Subtype.ext h))
  have hyc : ∀ p ∈ P, p * ((y : P) : H) = ((y : P) : H) * p := fun p hp =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp y.2 ⟨p, hp⟩)
  have hQs : Q ≤ Subgroup.centralizer ({s} : Set H) := by
    refine sup_le (fun p hp => ?_)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hsK p (hPK hp)).symm
  have hQy : Q ≤ Subgroup.centralizer ({((y : P) : H)} : Set H) := by
    refine sup_le (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hyc p hp)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hsK _ (hPK hyP))
  have hsZ : (⟨s, hsQ⟩ : Q) ∈ Subgroup.center Q :=
    Subgroup.mem_center_iff.mpr fun q =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQs q.2))
  have hyZ : (⟨_, hPQ hyP⟩ : Q) ∈ Subgroup.center Q :=
    Subgroup.mem_center_iff.mpr fun q =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQy q.2))
  have hle : Subgroup.zpowers (⟨s, hsQ⟩ : Q) ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr hsZ
  have hne : Subgroup.zpowers (⟨s, hsQ⟩ : Q) ≠ Subgroup.center Q := by
    intro heq
    have hyz : (⟨_, hPQ hyP⟩ : Q) ∈ Subgroup.zpowers (⟨s, hsQ⟩ : Q) := heq ▸ hyZ
    obtain ⟨k, hk⟩ := hyz
    have hk' : s ^ k = ((y : P) : H) := congrArg Subtype.val hk
    exact hy1' (hint _ hyP ⟨k, hk'⟩)
  have hlt : Nat.card (Subgroup.zpowers (⟨s, hsQ⟩ : Q)) < Nat.card (Subgroup.center Q) := by
    rcases (Subgroup.card_le_of_le hle).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle h.ge) hne
  rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hs] at hlt
  omega

@[expose] def z9 : Fin 3 → Perm (Fin 9) := ![c1 9, c2 9, c3 9]

theorem wreathFacts_perm9 : WreathFacts z9 (tt 9) where
  pow_z := by decide +kernel
  comm_z := by decide +kernel
  inj := by decide +kernel
  pow_t := by decide +kernel
  conj0 := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  t_ne := by decide +kernel

theorem z9_mem : ∀ i, z9 i ∈ alternatingGroup (Fin 9) := by
  intro i
  rw [Equiv.Perm.mem_alternatingGroup]
  revert i
  decide +kernel

theorem tt9_mem : tt 9 ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem wreathFacts_alt9 :
    WreathFacts (fun i => (⟨z9 i, z9_mem i⟩ : alternatingGroup (Fin 9))) ⟨tt 9, tt9_mem⟩ :=
  wreathFacts_perm9.subtype z9_mem tt9_mem

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem factorization_card_alt9 : (Nat.card (alternatingGroup (Fin 9))).factorization 3 = 4 := by
  rw [card_alt9, show (181440 : ℕ) = 3 ^ 4 * 2240 by norm_num,
    factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW_alt9 :
    Nat.card (wreathW (fun i => (⟨z9 i, z9_mem i⟩ : alternatingGroup (Fin 9)))
      ⟨tt 9, tt9_mem⟩) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := card_le_of_isPGroup (isPGroup_wreathW wreathFacts_alt9)
  rw [factorization_card_alt9] at hle
  have := le_card_wreathW wreathFacts_alt9
  norm_num at hle
  omega

theorem isSimpleGroup_projSU_three_three : IsSimpleGroup (projSU 3 3 1) :=
  CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.isSimpleGroup_projSU_three_three

theorem center_eq_bot_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Y :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

theorem center_eq_bot_of_projSU_three_three {X : Type*} [Group X] (e : X ≃* projSU 3 3 1) :
    Subgroup.center X = ⊥ := by
  have := isSimpleGroup_projSU_three_three
  have hZ : Subgroup.center (projSU 3 3 1) = ⊥ := center_eq_bot_of_simple (by
    rw [CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three,
      show (6048 : ℕ) = 2 * 3024 by norm_num]
    exact Nat.not_prime_mul (by norm_num) (by norm_num))
  exact Sec4.Item434SmallTwoIII.center_eq_bot_of_mulEquiv e.symm hZ

noncomputable def subgroupEquivImage {G M : Type*} [Group G] [Group M] {L K : Subgroup G}
    (hKL : K ≤ L) (e : L ≃* M) : K ≃* (K.subgroupOf L).map e.toMonoidHom :=
  (Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    ((K.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)

theorem false_of_wreath_U33 {H : Type*} [Group H] [Finite H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81)
    (h3 : (Nat.card H).factorization 3 = 4) {G : Type*} [Group G] {L K : Subgroup G}
    (hKL : K ≤ L) (e : L ≃* H) (eU : K ≃* projSU 3 3 1) {s : H} (hs : orderOf s = 3)
    (hsK : ∀ k : L, (k : G) ∈ K → s * e k = e k * s) : False := by
  have eK := subgroupEquivImage hKL e
  refine false_of_wreath hf hW h3 (K := (K.subgroupOf L).map e.toMonoidHom) ?_
    (center_eq_bot_of_projSU_three_three (eK.symm.trans eU)) hs ?_
  · rw [← Nat.card_congr eK.toEquiv, Nat.card_congr eU.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · rintro _ ⟨k, hk, rfl⟩
    exact hsK k (Subgroup.mem_subgroupOf.mp hk)

theorem normalizerMonoidHom_ne_one {G : Type*} [Group G] {L : Subgroup G} {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haC : a ∉ Subgroup.centralizer (L : Set G)) :
    L.normalizerMonoidHom ⟨a, haL⟩ ≠ 1 := by
  intro h1
  apply haC
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : G)) h1
  change a * l * a⁻¹ = l at h
  calc l * a = a * l * a⁻¹ * a := by rw [h]
    _ = a * l := by group

theorem normalizerMonoidHom_pow_three {G : Type*} [Group G] {L : Subgroup G} {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) :
    L.normalizerMonoidHom ⟨a, haL⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨a, haL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  rw [this, map_one]

theorem normalizerMonoidHom_apply_eq {G : Type*} [Group G] {L K : Subgroup G} {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) (k : L) (hk : (k : G) ∈ K) :
    L.normalizerMonoidHom ⟨a, haL⟩ k = k := by
  apply Subtype.ext
  change a * (k : G) * a⁻¹ = k
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hK hk).2
  rw [← hc, mul_inv_cancel_right]

theorem a6_of_alt9
    {G : Type} [Group G]
    [Finite G] {L K : Subgroup G} {a : G} (e : L ≃* alternatingGroup (Fin 9))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (haC : a ∉ Subgroup.centralizer (L : Set G))
    (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) (ht : IsType419 K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  have hKL : K ≤ L := fun x hx => (hK hx).1
  rcases card_cases ht with h6 | hU | ⟨h8, -⟩
  · exact h6
  · exfalso
    obtain ⟨eU⟩ := hU
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set φ : MulAut L := L.normalizerMonoidHom ⟨a, haL⟩ with hφ
    have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
      (by norm_num) (by norm_num)
    obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr e φ)
    have hπ3 : π ^ 3 = 1 := by
      apply hbij.1
      rw [map_pow, hπ, ← map_pow, hφ, normalizerMonoidHom_pow_three haL ha3, map_one, map_one]
    have hπ1 : π ≠ 1 := by
      intro h1
      apply normalizerMonoidHom_ne_one haL haC
      have h2 : MulAut.congr e φ = 1 := by rw [← hπ, h1, map_one]
      have h3 : φ = (MulAut.congr e).symm (MulAut.congr e φ) :=
        ((MulAut.congr e).symm_apply_apply φ).symm
      rw [← hφ, h3, h2, map_one]
    have hπo : orderOf π = 3 := orderOf_eq_prime hπ3 hπ1
    have hsign : Equiv.Perm.sign π = 1 := by
      have h := congrArg Equiv.Perm.sign hπ3
      rw [map_pow, map_one] at h
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1
      · exact h1
      · rw [h1] at h
        exact absurd h (by decide)
    refine false_of_wreath_U33 wreathFacts_alt9 card_wreathW_alt9 factorization_card_alt9 hKL e
      eU (s := ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩)
      (by rw [← Subgroup.orderOf_coe]; exact hπo) ?_
    intro k hk
    have hψk : MulAut.congr e φ (e k) = e k := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply, hφ, normalizerMonoidHom_apply_eq haL hK k hk]
    have h1 : (MulAut.conjNormal π) (e k) = e k := by rw [hπ]; exact hψk
    have h2 : π * ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π⁻¹ =
        ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9)) := by
      rw [← MulAut.conjNormal_apply, h1]
    apply Subtype.ext
    change π * ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π
    calc π * ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9))
        = π * ((e k : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π⁻¹ * π := by group
      _ = _ := by rw [h2]
  · exfalso
    have hdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
    rw [Nat.card_congr e.toEquiv, card_alt9] at hdvd
    have := h8.trans hdvd
    norm_num at this

theorem a6_of_sp62
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a : G}
    (e : L ≃* projSp 3 (GaloisField 2 1))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (haC : a ∉ Subgroup.centralizer (L : Set G))
    (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) (ht : IsType419 K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  have hKL : K ≤ L := fun x hx => (hK hx).1
  rcases card_cases ht with h6 | hU | ⟨-, h10 | h17⟩
  · exact h6
  · exfalso
    obtain ⟨eU⟩ := hU
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set f : L ≃* Census.Carrier.Sp6Two.H6 := e.trans Sec4.Item434SmallTwoIII.sp62Equiv with hf
    set φ : MulAut L := L.normalizerMonoidHom ⟨a, haL⟩ with hφ
    have hZ : Subgroup.center Census.Carrier.Sp6Two.H6 = ⊥ :=
      Sec4.Item434SmallTwoIII.center_eq_bot_of_mulEquiv Sec4.Item434SmallTwoIII.sp62Equiv
        Sec8.Item812Res3.isYModel_projSp_three_two.1
    have hinj : Function.Injective
        (MulAut.conj : Census.Carrier.Sp6Two.H6 →* MulAut Census.Carrier.Sp6Two.H6) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [← hZ, Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun φ : MulAut Census.Carrier.Sp6Two.H6 => φ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    obtain ⟨h, hh⟩ := Sec4.Item434SmallTwoIII.mem_range_conj_H6 (MulAut.congr f φ)
    have hh3 : h ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hh, ← map_pow, hφ, normalizerMonoidHom_pow_three haL ha3, map_one, map_one]
    have hh1 : h ≠ 1 := by
      intro h1
      apply normalizerMonoidHom_ne_one haL haC
      have h2 : MulAut.congr f φ = 1 := by rw [← hh, h1, map_one]
      have h3 : φ = (MulAut.congr f).symm (MulAut.congr f φ) :=
        ((MulAut.congr f).symm_apply_apply φ).symm
      rw [← hφ, h3, h2, map_one]
    refine false_of_wreath_U33 Sec4.Item434SmallTwoIII.wreathFacts_zH
      Sec4.Item434SmallTwoIII.card_wreathW_zH Sec4.Item434SmallTwoIII.factorization_card_H6 hKL f
      eU (orderOf_eq_prime hh3 hh1) ?_
    intro k hk
    have hψk : MulAut.congr f φ (f k) = f k := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply, hφ, normalizerMonoidHom_apply_eq haL hK k hk]
    have h1 : MulAut.conj h (f k) = f k := by rw [hh]; exact hψk
    rw [MulAut.conj_apply] at h1
    calc h * f k = h * f k * h⁻¹ * h := by group
      _ = f k * h := by rw [h1]
  · exfalso
    have hdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
    rw [Nat.card_congr (e.trans Sec4.Item434SmallTwoIII.sp62Equiv).toEquiv,
      Census.Carrier.Sp6Two.card_H6] at hdvd
    have := h10.trans hdvd
    norm_num at this
  · exfalso
    have hdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
    rw [Nat.card_congr (e.trans Sec4.Item434SmallTwoIII.sp62Equiv).toEquiv,
      Census.Carrier.Sp6Two.card_H6] at hdvd
    have := h17.trans hdvd
    norm_num at this

theorem a6_of_j3
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} (hKL : K ≤ L)
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J3) ∨
      IsTripleCover ↥L CFSG.Blueprint.NativeSporadic.J3)
    (ht : IsType419 K) : Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  have hcard : Nat.card L = 50232960 ∨ Nat.card L = 3 * 50232960 := by
    rcases hL with hL | ⟨hZ, hQ⟩
    · obtain ⟨e⟩ := hL
      exact Or.inl ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3)
    · obtain ⟨e⟩ := hQ
      right
      rw [← Subgroup.card_mul_index (Subgroup.center L), Subgroup.index_eq_card, hZ,
        Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]
  have hdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
  rcases card_cases ht with h6 | hU | ⟨h8, -⟩
  · exact h6
  · exfalso
    obtain ⟨eU⟩ := hU
    rw [Nat.card_congr eU.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three] at hdvd
    rcases hcard with h | h <;> rw [h] at hdvd <;> norm_num at hdvd
  · exfalso
    have h8' := h8.trans hdvd
    rcases hcard with h | h <;> rw [h] at h8' <;> norm_num at h8'

theorem nonempty_quot_center_J3 {L : Type*} [Group L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J3) ∨
      IsTripleCover L CFSG.Blueprint.NativeSporadic.J3) :
    Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Blueprint.NativeSporadic.J3) := by
  rcases hL with hL | ⟨-, hQ⟩
  · obtain ⟨e⟩ := hL
    have := CFSG.Sporadic.J3.isSimpleGroup_J3
    have hJ : Subgroup.center CFSG.Blueprint.NativeSporadic.J3 = ⊥ :=
      center_eq_bot_of_simple (by
        rw [CFSG.Sporadic.J3.card_J3, show (50232960 : ℕ) = 2 * 25116480 by norm_num]
        exact Nat.not_prime_mul (by norm_num) (by norm_num))
    have hZ : Subgroup.center L = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.J3 := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨x, rfl⟩ := e.surjective w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
      rw [hJ, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      exact e.injective (by rw [hz', map_one])
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩
  · exact hQ

end CFSG.RankThree.PartTwo.Sec4.Res419Two
