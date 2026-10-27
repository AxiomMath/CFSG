module

public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossRankTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QHeis
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4

public section

namespace CFSG.StandardType

section Sylow

open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)


private theorem pairwise_commute_union_singleton {G : Type*} [Group G] {E : Subgroup G} {z : G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hz : z ∈ Subgroup.centralizer (E : Set G)) :
    ((E : Set G) ∪ ({z} : Set G)).Pairwise Commute := by
  intro a ha b hb _
  rcases Set.mem_or_mem_of_mem_union ha with ha | ha
  · rcases Set.mem_or_mem_of_mem_union hb with hb | hb
    · exact hEc a ha b hb
    · rw [Set.mem_singleton_iff.mp hb]
      exact (Subgroup.mem_centralizer_iff.mp hz) a ha
  · rw [Set.mem_singleton_iff.mp ha]
    rcases Set.mem_or_mem_of_mem_union hb with hb | hb
    · exact ((Subgroup.mem_centralizer_iff.mp hz) b hb).symm
    · rw [Set.mem_singleton_iff.mp hb]

private theorem pow_three_eq_one_of_mem_closure {G : Type*} [Group G] {s : Set G}
    (hcomm : s.Pairwise Commute) (h3 : ∀ x ∈ s, x ^ 3 = 1) :
    ∀ x ∈ Subgroup.closure s, x ^ 3 = 1 := by
  have : IsMulCommutative ↥(Subgroup.closure s) := Subgroup.isMulCommutative_closure hcomm
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hc : Commute x y := Subgroup.mul_comm_of_mem_isMulCommutative _ hx hy
      rw [hc.mul_pow 3, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem mem_of_mem_centralizer_of_pow_three {J : Type} [Group J] [Finite J]
    (E : Subgroup J) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9)
    (hrank : ∀ A : Subgroup J, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 3 = 1) →
      Nat.card A ≤ 9)
    {z : J} (hz : z ∈ Subgroup.centralizer (E : Set J)) (hz3 : z ^ 3 = 1) : z ∈ E := by
  by_contra hzE
  let A : Subgroup J := Subgroup.closure ((E : Set J) ∪ ({z} : Set J))
  have hpair := pairwise_commute_union_singleton hEc hz
  have hAab : IsMulCommutative ↥A := Subgroup.isMulCommutative_closure hpair
  have h3union : ∀ x ∈ ((E : Set J) ∪ ({z} : Set J)), x ^ 3 = 1 := by
    intro x hx
    rcases Set.mem_or_mem_of_mem_union hx with hx | hx
    · exact hE3 x hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hz3
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx =>
    pow_three_eq_one_of_mem_closure hpair h3union x hx
  have hcard : Nat.card A ≤ 9 :=
    hrank A (fun a ha b hb => Subgroup.mul_comm_of_mem_isMulCommutative _ ha hb) hA3
  have hEA : E ≤ A := fun e he => Subgroup.subset_closure (Or.inl he)
  have hzA : z ∈ A := Subgroup.subset_closure (Or.inr (Set.mem_singleton z))
  have hlt : E < A := by
    refine lt_of_le_of_ne hEA ?_
    intro hEeqA
    exact hzE (by rw [hEeqA]; exact hzA)
  have h9 : 9 < Nat.card A := by
    rw [← hE9]
    exact Subgroup.card_lt_of_lt hlt
  exact (not_le_of_gt h9) hcard

private theorem sylow_le_centralizer {J : Type} [Group J] [Finite J]
    (E : Subgroup J) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hAut : ∀ g ∈ Subgroup.normalizer (E : Set J), IsPGroup 3 (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (E : Set J))
    (P : Sylow 3 J) (hEP : E ≤ P)
    (hkey : ∀ z ∈ (P : Subgroup J) ⊓ Subgroup.centralizer (E : Set J), z ^ 3 = 1 → z ∈ E) :
    (P : Subgroup J) ≤ Subgroup.centralizer (E : Set J) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q : Subgroup J := (P : Subgroup J) ⊓ Subgroup.centralizer (E : Set J)
  have hQle : Q ≤ P := inf_le_left
  have hEQ : E ≤ Q := fun e he =>
    Subgroup.mem_inf.mpr ⟨hEP he,
      Subgroup.mem_centralizer_iff.mpr fun h hh => hEc h hh e he⟩
  have hQP : Q = P := by
    refine le_antisymm hQle ?_
    by_contra hnot
    have hne : Q.subgroupOf P ≠ ⊤ := by
      intro htop
      apply hnot
      intro p hp
      have h1 : (⟨p, hp⟩ : ↥P) ∈ Q.subgroupOf P := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp h1
    have hQp_lt : Q.subgroupOf P < ⊤ := lt_of_le_of_ne le_top hne
    have : Group.IsNilpotent ↥P := (Sylow.isPGroup' P).isNilpotent
    have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
    have hlt : Q.subgroupOf P < Subgroup.normalizer (Q.subgroupOf P : Set ↥P) :=
      hnc (Q.subgroupOf P) hQp_lt
    obtain ⟨g, hgN, hgQ⟩ := SetLike.exists_of_lt hlt
    have hgNQ : (g : J) ∈ Subgroup.normalizer (Q : Set J) := by
      have hgsub : g ∈ (Subgroup.normalizer (Q : Set J)).subgroupOf (P : Subgroup J) := by
        rw [Subgroup.subgroupOf_normalizer_eq hQle]
        exact hgN
      exact Subgroup.mem_subgroupOf.mp hgsub
    have hconj : ∀ e ∈ E, (g : J) * e * (g : J)⁻¹ ∈ E := by
      intro e he
      have hmem : (g : J) * e * (g : J)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hgNQ e).mp (hEQ he)
      have hcube : ((g : J) * e * (g : J)⁻¹) ^ 3 = 1 := by
        rw [show (g : J) * e * (g : J)⁻¹ = MulAut.conj (g : J) e by
          rw [MulAut.conj_apply]]
        rw [← map_pow, hE3 e he, map_one]
      exact hkey _ hmem hcube
    have hinv : ∀ e ∈ E, (g : J)⁻¹ * e * (g : J) ∈ E := by
      intro e he
      have hgNQinv : (g : J)⁻¹ ∈ Subgroup.normalizer (Q : Set J) :=
        Subgroup.inv_mem _ hgNQ
      have hmem : (g : J)⁻¹ * e * (g : J) ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp hgNQinv e).mp (hEQ he)
      have hcube : ((g : J)⁻¹ * e * (g : J)) ^ 3 = 1 := by
        rw [show (g : J)⁻¹ * e * (g : J) = MulAut.conj (g : J)⁻¹ e by
          rw [MulAut.conj_apply, inv_inv]]
        rw [← map_pow, hE3 e he, map_one]
      exact hkey _ hmem hcube
    have hgNormE : (g : J) ∈ Subgroup.normalizer (E : Set J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · exact hconj e
      · intro he
        have h := hinv ((g : J) * e * (g : J)⁻¹) he
        rwa [show (g : J)⁻¹ * ((g : J) * e * (g : J)⁻¹) * (g : J) = e by group] at h
    have hgP3 : IsPGroup 3 (Subgroup.zpowers (g : J)) :=
      (Sylow.isPGroup' P).to_le (Subgroup.zpowers_le.mpr g.2)
    have hgC : (g : J) ∈ Subgroup.centralizer (E : Set J) := hAut _ hgNormE hgP3
    exact hgQ (Subgroup.mem_subgroupOf.mpr
      (show (g : J) ∈ Q from Subgroup.mem_inf.mpr ⟨g.2, hgC⟩))
  rw [← hQP]
  exact inf_le_right

theorem not_hasNoncommPair_three_of_elemAbelian_nine {J : Type} [Group J] [Finite J]
    (E : Subgroup J) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9)
    (hrank : ∀ A : Subgroup J, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 3 = 1) →
      Nat.card A ≤ 9)
    (hAut : ∀ g ∈ Subgroup.normalizer (E : Set J), IsPGroup 3 (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (E : Set J)) :
    ¬ HasNoncommPair 3 J := by
  rintro ⟨x, y, hx3, hy3, hxy, hH⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hE3g : IsPGroup 3 ↥E := fun e => ⟨1, by
    apply Subtype.ext
    simpa using hE3 (e : J) e.2⟩
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow hE3g
  obtain ⟨P', hHP'⟩ := IsPGroup.exists_le_sylow hH
  have hPre : MulAction.IsPretransitive J (Sylow 3 J) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := J) (α := Sylow 3 J) P' P
  let : MulAction (MulAut J) (Subgroup J) := Subgroup.pointwiseMulAction
  have hP'coe : MulAut.conj g • (P' : Subgroup J) = (P : Subgroup J) := by
    have h := congrArg (fun R : Sylow 3 J => (R : Subgroup J)) hg
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  have hxP' : x ∈ (P' : Subgroup J) := hHP' (Subgroup.subset_closure (by simp))
  have hyP' : y ∈ (P' : Subgroup J) := hHP' (Subgroup.subset_closure (by simp))
  set x' : J := MulAut.conj g x with hx'def
  set y' : J := MulAut.conj g y with hy'def
  have hx'P : x' ∈ (P : Subgroup J) := by
    have h := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P' : Subgroup J) hxP'
    rw [hP'coe] at h
    simpa [MulAut.smul_def, hx'def] using h
  have hy'P : y' ∈ (P : Subgroup J) := by
    have h := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P' : Subgroup J) hyP'
    rw [hP'coe] at h
    simpa [MulAut.smul_def, hy'def] using h
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx'def, ← map_pow, hx3, map_one]
  have hy'3 : y' ^ 3 = 1 := by
    rw [hy'def, ← map_pow, hy3, map_one]
  have hx'y' : x' * y' ≠ y' * x' := by
    intro h
    apply hxy
    have h2 : MulAut.conj g (x * y) = MulAut.conj g (y * x) := by
      simpa only [map_mul, hx'def, hy'def] using h
    exact (MulAut.conj g).injective h2
  have hkey : ∀ z ∈ (P : Subgroup J) ⊓ Subgroup.centralizer (E : Set J), z ^ 3 = 1 → z ∈ E :=
    fun z hz hz3 => mem_of_mem_centralizer_of_pow_three E hEc hE3 hE9 hrank hz.2 hz3
  have hPle : (P : Subgroup J) ≤ Subgroup.centralizer (E : Set J) :=
    sylow_le_centralizer E hEc hE3 hAut P hEP hkey
  have hx'E : x' ∈ E := hkey x' (Subgroup.mem_inf.mpr ⟨hx'P, hPle hx'P⟩) hx'3
  have hy'E : y' ∈ E := hkey y' (Subgroup.mem_inf.mpr ⟨hy'P, hPle hy'P⟩) hy'3
  exact hx'y' (hEc x' hx'E y' hy'E)

end Sylow

section Rank

open CFSG.Assembly TableB
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)


theorem hasNoncommPair_three_of_quotient_center {H : Type} [Group H] [Finite H]
    (hZ : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 → z = 1)
    (h : HasNoncommPair 3 (H ⧸ Subgroup.center H)) : HasNoncommPair 3 H := by
  classical
  obtain ⟨xbar, ybar, hxbar, hybar, hxy, hQbarP⟩ := h
  let Z : Subgroup H := Subgroup.center H
  let q : H →* H ⧸ Z := QuotientGroup.mk' Z
  let Qbar : Subgroup (H ⧸ Z) := Subgroup.closure ({xbar, ybar} : Set (H ⧸ Z))
  let Q : Subgroup H := Qbar.comap q
  have hZleQ : Z ≤ Q := by
    intro z hz
    change q z ∈ Qbar
    rw [show q z = 1 from (QuotientGroup.eq_one_iff (N := Z) z).2 hz]
    exact Qbar.one_mem
  let N : Subgroup Q := Z.subgroupOf Q
  have hNnormal : N.Normal := (inferInstance : Z.Normal).subgroupOf Q
  let : N.Normal := hNnormal
  let f : Q →* Qbar := (q.comp Q.subtype).codRestrict Qbar (fun x => x.2)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z y
    have hxQ : x ∈ Q := by
      change q x ∈ Qbar
      rw [show q x = (y : H ⧸ Z) by simpa [q] using hx]
      exact y.2
    refine ⟨⟨x, hxQ⟩, ?_⟩
    apply Subtype.ext
    change q x = (y : H ⧸ Z)
    exact hx
  have hker : f.ker = N := by
    ext x
    constructor
    · intro hx
      apply Subgroup.mem_subgroupOf.mpr
      apply (QuotientGroup.eq_one_iff (N := Z) (x : H)).mp
      exact congrArg Subtype.val hx
    · intro hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := Z) (x : H)).mpr
        (Subgroup.mem_subgroupOf.mp hx)
  have hNindex : N.index = Nat.card Qbar := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfsurj]
    simp
  have hNcard : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleQ).toEquiv
  have hZ3 : ¬ 3 ∣ Nat.card Z := by
    intro hdvd
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hz3Z : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    have hz3 : (z : H) ^ 3 = 1 := by simpa using congrArg Subtype.val hz3Z
    have hzone : z = 1 := Subtype.ext (hZ (z : H) z.2 hz3)
    rw [hzone] at hzord
    simp at hzord
  obtain ⟨k, hk⟩ := hQbarP.exists_card_eq
  have hNcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hNindex, hk]
    exact Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three hZ3
  obtain ⟨W, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hNcop
  have hWcard : Nat.card W = Nat.card Qbar := by
    rw [← hcomp.symm.index_eq_card, hNindex]
  have hWinfN : W ⊓ N = ⊥ := hcomp.disjoint.symm.eq_bot
  let g : W →* Qbar := f.comp W.subtype
  have hginj : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    rw [eq_bot_iff]
    intro x hx
    have hxN : (x : Q) ∈ N := by
      rw [← hker]
      exact hx
    have hxInf : (x : Q) ∈ W ⊓ N := ⟨x.2, hxN⟩
    rw [hWinfN] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  have hgcard : Nat.card g.range = Nat.card W := by
    have h := Subgroup.card_ker_mul_card_range g
    have hkerbot : g.ker = ⊥ := (MonoidHom.ker_eq_bot_iff g).mpr hginj
    rw [hkerbot] at h
    simpa using h
  have hgrange : g.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hgcard, hWcard]
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : y ∈ g.range := by rw [hgrange]; exact Subgroup.mem_top y
    exact MonoidHom.mem_range.mp hy
  have hxbarQ : xbar ∈ Qbar := Subgroup.subset_closure (by simp)
  have hybarQ : ybar ∈ Qbar := Subgroup.subset_closure (by simp)
  obtain ⟨wx, hwx⟩ := hgsurj ⟨xbar, hxbarQ⟩
  obtain ⟨wy, hwy⟩ := hgsurj ⟨ybar, hybarQ⟩
  let x : H := (wx : Q)
  let y : H := (wy : Q)
  have hqx : q x = xbar := congrArg Subtype.val hwx
  have hqy : q y = ybar := congrArg Subtype.val hwy
  have hx3 : x ^ 3 = 1 := by
    have hwx3 : wx ^ 3 = 1 := by
      apply hginj
      rw [map_pow, hwx, map_one]
      exact Subtype.ext (by simpa using hxbar)
    have h := congrArg (Q.subtype.comp W.subtype) hwx3
    simp only [map_pow, map_one] at h
    simpa [x] using h
  have hy3 : y ^ 3 = 1 := by
    have hwy3 : wy ^ 3 = 1 := by
      apply hginj
      rw [map_pow, hwy, map_one]
      exact Subtype.ext (by simpa using hybar)
    have h := congrArg (Q.subtype.comp W.subtype) hwy3
    simp only [map_pow, map_one] at h
    simpa [y] using h
  have hxyn : x * y ≠ y * x := by
    intro heq
    apply hxy
    have hq := congrArg q heq
    simpa [map_mul, hqx, hqy] using hq
  have hWp : IsPGroup 3 W := IsPGroup.of_injective hQbarP g hginj
  have hWHp : IsPGroup 3 (W.map Q.subtype) := hWp.map Q.subtype
  have hxmem : x ∈ W.map Q.subtype := ⟨(wx : Q), wx.2, rfl⟩
  have hymem : y ∈ W.map Q.subtype := ⟨(wy : Q), wy.2, rfl⟩
  have hclosure : Subgroup.closure ({x, y} : Set H) ≤ W.map Q.subtype := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxmem
    · exact hymem
  exact ⟨x, y, hx3, hy3, hxyn, hWHp.to_le hclosure⟩

theorem card_le_nine_of_elemAbelian_of_smallLabel
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (H ⧸ Subgroup.center H))
    (htag : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hZ : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 → z = 1)
    {A : Subgroup H} (hA : IsElemAbelian 3 A) : Nat.card A ≤ 9 := by
  classical
  let Z : Subgroup H := Subgroup.center H
  let q : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hAZ : A ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haA, haZ⟩ := Subgroup.mem_inf.mp ha
    have h3 : a ^ 3 = 1 := hA.2 a haA
    exact Subgroup.mem_bot.mpr (hZ a haZ h3)
  have hAEcard : Nat.card (A.map q) = Nat.card A := by
    rw [← Subgroup.relIndex_ker A q, QuotientGroup.ker_mk']
    have h := Subgroup.relIndex_mul_card Z A
    rw [show Z ⊓ A = ⊥ by rw [inf_comm, hAZ]] at h
    simpa using h
  have hEa : IsElemAbelian 3 (A.map q) := hA.map q
  have hlt : Nat.card A < 3 ^ 3 := by
    by_contra hge
    have hge' : 27 ≤ Nat.card (A.map q) := by
      rw [hAEcard]
      have : 3 ^ 3 ≤ Nat.card A := by omega
      norm_num at this ⊢
      exact this
    exact (ggSmallThreeRank_not_small_of_elemAbelian hlab hhas hEa hge') htag
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hA)
  rw [hk] at hlt ⊢
  have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
  have hle : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
  simpa using hle

end Rank

section Pair

open CFSG.Assembly TableB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)


private theorem hasNoncommPair_graphFixedD4
    {L : Type} [Field L] [Finite L] (Fr : L ≃+* L)
    (hk3 : 3 ≤ Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr))
    (hk : ¬ 3 ∣ Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr)) :
    HasNoncommPair 3 ↥(graphFixedRootGroup TwistTag.D4 L Fr.toRingHom) := by
  have hk3e : (3 : ℕ∞) ≤ ENat.card (CFSG.LieType.Chevalley.fixSubfield Fr) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hk3
  have hG2 : HasNoncommPair 3
      ↥(adjointGroup Tag.G2 (CFSG.LieType.Chevalley.fixSubfield Fr)) :=
    CFSG.AGLEmbedding.KFactProofs.G2Q.exists_pair_not_dvd_three
      (K := CFSG.LieType.Chevalley.fixSubfield Fr) hk
  have hJ := hG2.map
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 Fr
      hk3e).symm.toMonoidHom (MulEquiv.injective _)
  exact hJ.map (Subgroup.inclusion
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_le Fr))
    (Subgroup.inclusion_injective _)

private theorem factorization_three_eq {n k : ℕ} (hn : n ≠ 0) (h1 : 3 ^ k ∣ n)
    (h2 : ¬ 3 ^ (k + 1) ∣ n) : n.factorization 3 = k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def n Nat.prime_three]
  have := (padicValNat_dvd_iff_le hn).1 h1
  have h' : ¬ k + 1 ≤ padicValNat 3 n := fun h => h2 ((padicValNat_dvd_iff_le hn).2 h)
  omega

private theorem hasNoncommPair_graphFixedD4_two
    {K₈ : Type} [Field K₈] [Finite K₈]
    (σ : K₈ ≃+* K₈) (hK : Nat.card K₈ = 8) (hσ : ∀ c, σ c = c ^ 2) :
    HasNoncommPair 3 ↥(graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K₈ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) (by rw [hK]; norm_num)
  let L := FiniteField.Extension K₈ 2 4
  have hL : Nat.card L = 2 ^ 12 := by
    rw [FiniteField.natCard_extension, hK]
    norm_num
  obtain ⟨σ₀, hσ₀, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num : 1 ≤ 12) hL
  have hpow : ∀ (n : ℕ) (x : L), (σ₀ ^ n) x = x ^ (2 ^ n) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      show σ₀ ((σ₀ ^ n) x) = _
      rw [ih, hσ₀, ← pow_mul, ← pow_succ]
  let Fr : L ≃+* L := σ₀ ^ 4
  have hFr : ∀ x, Fr x = x ^ 16 := fun x => by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact hpow 4 x
  have hc8 : ∀ c : K₈, c ^ 8 = c := fun c => by
    have := Fintype.ofFinite K₈
    have := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hcompat : ∀ c : K₈, Fr.toRingHom (algebraMap K₈ L c) =
      algebraMap K₈ L (σ.toRingHom c) := by
    intro c
    show Fr (algebraMap K₈ L c) = algebraMap K₈ L (σ c)
    rw [hFr, ← map_pow, hσ, show c ^ 16 = (c ^ 8) ^ 2 by ring, hc8]
  have hle := CFSG.LieType.Chevalley.map_baseChangeGL_graphFixedRootGroup_le
    (t := TwistTag.D4) (σ := σ.toRingHom) (Fr := Fr.toRingHom) (ι := algebraMap K₈ L)
    σ.surjective hcompat
  let ψ : ↥(graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom) →*
      ↥(graphFixedRootGroup TwistTag.D4 L Fr.toRingHom) :=
    ((CFSG.LieType.Chevalley.baseChangeGL (τ := TwistTag.D4.tag) (algebraMap K₈ L)).comp
      (graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom).subtype).codRestrict _
      (fun x => hle ⟨x, x.2, rfl⟩)
  have hψ : Function.Injective ψ := fun x y h => Subtype.ext
    (CFSG.LieType.Chevalley.baseChangeGL_injective _ (congrArg Subtype.val h))
  have hfix : Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr) = 2 ^ 4 :=
    CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube (f := 4) (by norm_num)
      (by rw [hL]; norm_num) (fun c => by rw [hFr]; norm_num)
  refine CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.RankTwo.hasNoncommPair_of_injective
    ψ hψ ?_ (hasNoncommPair_graphFixedD4 Fr
      (by rw [hfix]; norm_num) (by rw [hfix]; norm_num))
  have hcC := CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (f := 1) (r := 1)
    le_rfl (Or.inl rfl) (by rw [hK]; norm_num) σ.toRingHom (fun c => by
      show σ c = _
      rw [hσ]
      norm_num)
  have hcL := CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (f := 4) (r := 1)
    (by norm_num) (Or.inl rfl) (by rw [hL]; norm_num) Fr.toRingHom (fun c => by
      show Fr c = _
      rw [hFr]
      norm_num)
  rw [hcC, hcL, factorization_three_eq (k := 4) (by norm_num [CFSG.Open.ordTrialityD4])
      (Nat.dvd_of_mod_eq_zero (by norm_num [CFSG.Open.ordTrialityD4]))
      (fun h => by
        have := Nat.mod_eq_zero_of_dvd h
        norm_num [CFSG.Open.ordTrialityD4] at this),
    factorization_three_eq (k := 4) (by norm_num [CFSG.Open.ordTrialityD4])
      (Nat.dvd_of_mod_eq_zero (by norm_num [CFSG.Open.ordTrialityD4]))
      (fun h => by
        have := Nat.mod_eq_zero_of_dvd h
        norm_num [CFSG.Open.ordTrialityD4] at this)]

private theorem su3_cube_of_mem {m : List ℕ} (hm : m ∈ TableBExcSmallRest.su3Codes) :
    (CFSG.Quasithin.G2U.dec3 m) ^ 3 = 1 := by
  have hc : CFSG.Quasithin.G2U.mul3 (CFSG.Quasithin.G2U.mul3 m m) m =
      CFSG.Quasithin.G2U.id3 := by
    simpa using List.all_eq_true.mp TableBExcSmallRest.su3Codes_cube m hm
  rw [pow_succ, pow_succ, pow_one, ← CFSG.Quasithin.G2U.dec3_mul3,
    ← CFSG.Quasithin.G2U.dec3_mul3, hc, CFSG.Quasithin.G2U.dec3_id3]

private theorem su3X_pow_three :
    (TableBExcSmallRest.su3X : GL (Fin 3) CFSG.Quasithin.G2U.F9) ^ 3 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  rw [show ((TableBExcSmallRest.su3X : GL (Fin 3) CFSG.Quasithin.G2U.F9) :
      Matrix (Fin 3) (Fin 3) CFSG.Quasithin.G2U.F9) =
      CFSG.Quasithin.G2U.dec3 TableBExcSmallRest.su3xc from rfl]
  exact su3_cube_of_mem (by decide)

private theorem su3Y_pow_three :
    (TableBExcSmallRest.su3Y : GL (Fin 3) CFSG.Quasithin.G2U.F9) ^ 3 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  rw [show ((TableBExcSmallRest.su3Y : GL (Fin 3) CFSG.Quasithin.G2U.F9) :
      Matrix (Fin 3) (Fin 3) CFSG.Quasithin.G2U.F9) =
      CFSG.Quasithin.G2U.dec3 TableBExcSmallRest.su3yc from rfl]
  exact su3_cube_of_mem (by decide)

private theorem hasNoncommPair_statedSU33 :
    HasNoncommPair 3 ↥(CFSG.Open.StatedSU 3 3 CFSG.Quasithin.G2U.F9) := by
  refine ⟨⟨TableBExcSmallRest.su3X, TableBExcSmallRest.su3X_mem⟩,
    ⟨TableBExcSmallRest.su3Y, TableBExcSmallRest.su3Y_mem⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact su3X_pow_three
  · apply Subtype.ext
    exact su3Y_pow_three
  · intro h
    exact TableBExcSmallRest.su3X_mul_su3Y_ne (by simpa using congrArg Subtype.val h)
  · exact TableBExcSmallRest.isPGroup_su3P

private theorem hasNoncommPair_commutator_reeFixed_tits
    {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2) :
    HasNoncommPair 3 ↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := K) hK
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem hasNoncommPair_three_of_smallLabel
    {X : Type} [Group X] {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab X)
    (htag : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der) :
    HasNoncommPair 3 X := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag hlab
  rcases htag with ht | ht | ht | ht | ht
  ·
    subst ht
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, hF, hFin, hK, hq⟩ := hhas
    let : Field K := hF
    let : Finite K := hFin
    obtain ⟨e⟩ := hq
    have h3 : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro h
      have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hpair : HasNoncommPair 3 ↥(adjointGroup Tag.G2 K) :=
      CFSG.AGLEmbedding.KFactProofs.G2Q.exists_pair_not_dvd_three (K := K) h3
    exact (hpair.map (TableBExc.recipeEquiv .G2 K).symm.toMonoidHom
      (MulEquiv.injective _)).map e.symm.toMonoidHom e.symm.injective
  ·
    subst ht
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, hF, hFin, hK, hq⟩ := hhas
    let : Field K := hF
    let : Finite K := hFin
    obtain ⟨e⟩ := hq
    have hn : 1 ≤ n := hlab.1
    have hchar : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
    let σ := iterateFrobeniusEquiv K 2 n
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      rw [show σ = iterateFrobeniusEquiv K 2 n from rfl,
        iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    obtain ⟨e₀⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
    refine (HasNoncommPair.map e₀.symm.toMonoidHom (MulEquiv.injective _) ?_).map
      e.symm.toMonoidHom e.symm.injective
    by_cases hn1 : n = 1
    · have hK8 : Nat.card K = 8 := by rw [hK, hn1]; norm_num
      have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c, hn1]; norm_num
      exact hasNoncommPair_graphFixedD4_two σ hK8 hσ2
    · have hfix : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ n :=
        CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube (f := n) (by omega) hK hσ
      have hk3 : 3 ≤ Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) := by
        rw [hfix]
        have hn2 : 2 ≤ n := by omega
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hk : ¬ 3 ∣ Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) := by
        rw [hfix]
        intro h
        have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        omega
      exact hasNoncommPair_graphFixedD4 σ hk3 hk
  ·
    subst ht
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, hF, hFin, hK, hq⟩ := hhas
    let : Field K := hF
    let : Finite K := hFin
    obtain ⟨e⟩ := hq
    have hn3 : 3 ≤ n := hlab.2.2.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    have hchar : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      apply charP_two_of_card (m := 2 * ((n - 1) / 2) + 1)
      rw [hK]
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
    obtain ⟨e₀⟩ := gff_nonempty_centerQuot_equiv_reeGamma (a := (n - 1) / 2) ha hK
    refine (HasNoncommPair.map e₀.symm.toMonoidHom (MulEquiv.injective _)
      (CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.hasNoncommPair_reeGamma
        ((n - 1) / 2) K hK)).map e.symm.toMonoidHom e.symm.injective
  ·
    subst ht
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, hF, hFin, hK, hq⟩ := hhas
    let : Field K := hF
    let : Finite K := hFin
    obtain ⟨e⟩ := hq
    obtain ⟨e₀⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
    exact (HasNoncommPair.map e₀.symm.toMonoidHom (MulEquiv.injective _)
      hasNoncommPair_statedSU33).map e.symm.toMonoidHom e.symm.injective
  ·
    subst ht
    have hn1 : n = 1 := hlab.2.2
    subst hn1
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, hF, hFin, hK, hq⟩ := hhas
    let : Field K := hF
    let : Finite K := hFin
    obtain ⟨e⟩ := hq
    have hk2 : Nat.card K = 2 := by simpa using hK
    have hchar : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
    obtain ⟨e₀⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GField.nonempty_titsQuot_equiv
      (k := K) hk2
    exact (HasNoncommPair.map e₀.symm.toMonoidHom (MulEquiv.injective _)
      (hasNoncommPair_commutator_reeFixed_tits hk2)).map e.symm.toMonoidHom e.symm.injective

end Pair

section Bridge

theorem card_inf_eq_nine_and_centralizes_of_lineJDatum_B2 {G : Type} [Group G] [Finite G]
    {B Bs J : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .B2)
    (hγ : Nat.card (ggGamma J hN).range ≤ 9)
    (hZ : Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) = ⊥) :
    Nat.card ((Bs ⊓ J).subgroupOf J) = 9 ∧
      ∀ g ∈ Subgroup.normalizer (((Bs ⊓ J).subgroupOf J : Subgroup ↥J) : Set ↥J),
        IsPGroup 3 (Subgroup.zpowers g) →
          g ∈ Subgroup.centralizer (((Bs ⊓ J).subgroupOf J : Subgroup ↥J) : Set ↥J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup G := Bs ⊓ J
  let U : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hEle : E ≤ Bs := inf_le_left
  have h9ge : 9 ≤ Nat.card ↥E := by
    change 9 ≤ Nat.card ↥(Bs ⊓ J)
    exact card_inf_ge_nine_of_lineJDatum_B2 hBs hN hD
  have h9le : Nat.card ↥E ≤ 9 := by
    let f : ↥E → (ggGamma J hN).range := fun e =>
      ⟨ggGamma J hN (Subgroup.inclusion hEle e), ⟨_, rfl⟩⟩
    have hinj : Function.Injective f := by
      intro e e' hee'
      have h1 : ggGamma J hN (Subgroup.inclusion hEle e) =
          ggGamma J hN (Subgroup.inclusion hEle e') := congrArg Subtype.val hee'
      have h2 : ggGamma J hN (Subgroup.inclusion hEle (e * e'⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := (ggGamma_eq_one_iff J hN (Subgroup.inclusion hEle (e * e'⁻¹))).mp h2
      have h4 : ((e * e'⁻¹ : ↥E) : G) ∈ Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) :=
        Subgroup.mem_inf.mpr ⟨(e * e'⁻¹).2, by simpa using h3⟩
      rw [hZ, Subgroup.mem_bot] at h4
      exact mul_inv_eq_one.mp (Subtype.ext h4)
    exact (Nat.card_le_card_of_injective f hinj).trans hγ
  have hcardE : Nat.card ↥E = 9 := le_antisymm h9le h9ge
  have hcardE' : Nat.card ((Bs ⊓ J).subgroupOf J) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ J ≤ J)).toEquiv]
    exact hcardE
  refine ⟨hcardE', ?_⟩
  have hUcard : Nat.card ↥(U.subgroupOf Bs) = Nat.card ↥U := by
    change Nat.card { x : ↥Bs // x ∈ (Bs ⊓ Subgroup.centralizer (J : Set G)).subgroupOf Bs } =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ Bs)).toEquiv
  have hker : (ggGamma J hN).ker = U.subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    simp [U, Subgroup.mem_inf]
  have hcount := TableB.card_range_mul_card_ker (ggGamma J hN)
  rw [hker, hUcard] at hcount
  have hBscard : Nat.card ↥Bs ≤ 9 * Nat.card ↥U := by
    rw [← hcount]
    exact Nat.mul_le_mul_right _ hγ
  have hEUdisj : E ⊓ U = ⊥ := by
    rw [show E ⊓ U = Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) by
      ext x
      simp [E, U, Subgroup.mem_inf, and_assoc, and_left_comm]]
    exact hZ
  have : IsMulCommutative ↥Bs := hBs.2.1.1
  let _ : CommGroup ↥Bs := IsMulCommutative.instCommGroup
  have hcomm : ∀ h : ↥E, ∀ k : ↥U, ((h : G) * (k : G) : G) = (k : G) * (h : G) := by
    intro h k
    have hh : (h : G) ∈ Bs := h.2.1
    have hk : (k : G) ∈ Bs := k.2.1
    let h' : ↥Bs := ⟨h, hh⟩
    let k' : ↥Bs := ⟨k, hk⟩
    have hcommBs : h' * k' = k' * h' := mul_comm _ _
    have := congrArg Subtype.val hcommBs
    simpa [h', k'] using this
  have hdisj : Disjoint E U := disjoint_iff_inf_le.mpr (by rw [hEUdisj])
  have hnormal : U ≤ Subgroup.normalizer (E : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have hcommue : (u : G) * e = e * (u : G) := (hcomm ⟨e, he⟩ ⟨u, hu⟩).symm
      have heq : (u : G) * e * (u : G)⁻¹ = e := by
        calc (u : G) * e * (u : G)⁻¹ = e * (u : G) * (u : G)⁻¹ := by rw [hcommue]
          _ = e := by group
      rwa [heq]
    · intro he
      have hcommuy : (u : G) * ((u : G) * e * (u : G)⁻¹) =
          ((u : G) * e * (u : G)⁻¹) * (u : G) :=
        (hcomm ⟨(u : G) * e * (u : G)⁻¹, he⟩ ⟨u, hu⟩).symm
      have heq : e = (u : G) * e * (u : G)⁻¹ := by
        calc e = (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * (u : G) := by group
          _ = (u : G)⁻¹ * (((u : G) * e * (u : G)⁻¹) * (u : G)) := by group
          _ = (u : G)⁻¹ * ((u : G) * ((u : G) * e * (u : G)⁻¹)) := by rw [hcommuy]
          _ = (u : G) * e * (u : G)⁻¹ := by group
      rwa [heq]
  have hsupcard : Nat.card ↥(E ⊔ U) = Nat.card ↥E * Nat.card ↥U :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E U hnormal hdisj
  have hsup_le : E ⊔ U ≤ Bs := sup_le inf_le_left inf_le_left
  have hsup_eq : E ⊔ U = Bs := by
    apply Subgroup.eq_of_le_of_card_ge hsup_le
    rw [hsupcard, hcardE]
    exact hBscard
  intro g hgN hgP
  have hconj_mem : ∀ h : ↥J, h ∈ Subgroup.normalizer ((E.subgroupOf J : Subgroup ↥J) : Set ↥J) →
      ∀ x ∈ Bs, (h : G) * x * (h : G)⁻¹ ∈ Bs := by
    intro h hhN x hx
    have hx_sup : x ∈ E ⊔ U := by rw [hsup_eq]; exact hx
    have hsub : (E ⊔ U).subgroupOf Bs = E.subgroupOf Bs ⊔ U.subgroupOf Bs :=
      Subgroup.subgroupOf_sup (A := E) (A' := U) (B := Bs) hEle inf_le_left
    let xBs : ↥Bs := ⟨x, hx⟩
    have hx_sup' : xBs ∈ E.subgroupOf Bs ⊔ U.subgroupOf Bs := by
      rw [← hsub]
      exact hx_sup
    obtain ⟨e, he, u, hu, hx_eq'⟩ :=
      (Subgroup.mem_sup (s := E.subgroupOf Bs) (t := U.subgroupOf Bs)
        (x := xBs)).mp hx_sup'
    have hxG : x = (e : G) * (u : G) := by
      simpa using (congrArg Subtype.val hx_eq').symm
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have heJ : (e : G) ∈ J := heE.2
    let eJ : ↥J := ⟨e, heJ⟩
    have heJ_mem : eJ ∈ (E.subgroupOf J : Subgroup ↥J) := by
      rw [Subgroup.mem_subgroupOf]
      exact heE
    have hge : h * eJ * h⁻¹ ∈ (E.subgroupOf J : Subgroup ↥J) :=
      (Subgroup.mem_normalizer_iff.mp hhN eJ).mp heJ_mem
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have huC : (u : G) ∈ Subgroup.centralizer (J : Set G) := huU.2
    have hhu : (h : G) * (u : G) * (h : G)⁻¹ = u := by
      have hcommhu : (h : G) * (u : G) = (u : G) * (h : G) :=
        Subgroup.mem_centralizer_iff.mp huC (h : G) h.2
      calc (h : G) * (u : G) * (h : G)⁻¹ = (u : G) * (h : G) * (h : G)⁻¹ := by rw [hcommhu]
        _ = u := by group
    have hge_mem : ((h : G) * (e : G) * (h : G)⁻¹) ∈ E := by
      have hmem : ((h * eJ * h⁻¹ : ↥J) : G) ∈ E := Subgroup.mem_subgroupOf.mp hge
      simpa [eJ] using hmem
    have hmem : ((h : G) * (e : G) * (h : G)⁻¹) * (u : G) ∈ Bs :=
      Subgroup.mul_mem Bs (hEle hge_mem) huU.1
    have hcomm' : (u : G) * (h : G)⁻¹ = (h : G)⁻¹ * (u : G) := by
      have h := congrArg (fun y => (h : G)⁻¹ * y) hhu
      simpa [mul_assoc] using h
    have hxG' : (h : G) * x * (h : G)⁻¹ =
        ((h : G) * (e : G) * (h : G)⁻¹) * (u : G) := by
      rw [hxG]
      calc (h : G) * ((e : G) * (u : G)) * (h : G)⁻¹
          = (h : G) * (e : G) * ((u : G) * (h : G)⁻¹) := by group
        _ = (h : G) * (e : G) * ((h : G)⁻¹ * (u : G)) := by rw [hcomm']
        _ = ((h : G) * (e : G) * (h : G)⁻¹) * (u : G) := by group
    rwa [hxG']
  have hgBsN : (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hconj_mem g hgN b hb
    · intro hb
      have hginvN : g⁻¹ ∈ Subgroup.normalizer ((E.subgroupOf J : Subgroup ↥J) : Set ↥J) :=
        Subgroup.inv_mem _ hgN
      have h := hconj_mem g⁻¹ hginvN (g * b * g⁻¹) hb
      have hb_eq : (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) * (g : G) = b := by group
      simp only [Subgroup.coe_inv, inv_inv] at h
      rwa [hb_eq] at h
  let φ : MulAut ↥Bs := ggConjAut Bs hgBsN
  have hφ_mem : φ ∈ ggAutomizer J Bs :=
    ggConjAut_mem_ggAutomizer (H := J) g.2 hgBsN
  have hφ8 : φ ^ 8 = 1 := by
    have hdiv : orderOf φ ∣ Nat.card (ggAutomizer J Bs) :=
      Subgroup.orderOf_dvd_natCard (ggAutomizer J Bs) hφ_mem
    rw [ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD] at hdiv
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv
  obtain ⟨k, hgk⟩ := hgP ⟨g, Subgroup.mem_zpowers g⟩
  have hgkG : (g : G) ^ (3 ^ k) = 1 := by
    have hgk' : (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) ^ (3 ^ k) = 1 := hgk
    have := congrArg (fun x : ↥(Subgroup.zpowers g) => (x : ↥J)) hgk'
    simpa using congrArg (fun x : ↥J => (x : G)) this
  have hφ3 : φ ^ (3 ^ k) = 1 := by
    ext b
    rw [ggConjAut_pow_apply Bs hgBsN (3 ^ k) b, hgkG]
    simp
  have hcoprime : Nat.Coprime (3 ^ k) 8 := by
    exact Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 8)
  have hdiv1 : orderOf φ ∣ 1 := by
    have hdiv3 : orderOf φ ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hφ3
    have hdiv8 : orderOf φ ∣ 8 := orderOf_dvd_iff_pow_eq_one.mpr hφ8
    have hgcd : Nat.gcd (3 ^ k) 8 = 1 := hcoprime.gcd_eq_one
    have hdiv_gcd : orderOf φ ∣ Nat.gcd (3 ^ k) 8 := Nat.dvd_gcd hdiv3 hdiv8
    rwa [hgcd] at hdiv_gcd
  have hφ_eq_one : φ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv1)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
  let xBs : ↥Bs := ⟨(x : G), hEle hxE⟩
  have hφx : φ xBs = xBs := by rw [hφ_eq_one]; rfl
  have hconj := ggConjAut_apply Bs hgBsN xBs
  rw [hφx] at hconj
  have hconj' : (x : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
    simpa [xBs] using hconj
  have hcommG : (g : G) * (x : G) = (x : G) * (g : G) := by
    have h1 : ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) = (g : G) * (x : G) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    calc (g : G) * (x : G) = ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) := h1.symm
      _ = (x : G) * (g : G) := by rw [← hconj']
  apply Subtype.ext
  exact hcommG.symm

end Bridge

end CFSG.StandardType

end
