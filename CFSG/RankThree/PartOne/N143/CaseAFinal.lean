module

public import CFSG.RankThree.PartOne.N143.CaseADecomp
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.RankThree.PartOne.N143.CaseA
public import CFSG.RankThree.PartOne.N143.CaseASetup
public import CFSG.RankThree.PartOne.N143.CaseAV

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] {A : Subgroup G} {zs : MulAut A}

theorem action_of_pi_eq {k : ℕ} (hk : ∀ a : A, zs a = a ^ k) {z : G}
    (hz : z ∈ Subgroup.normalizer (A : Set G)) (h : A.normalizerMonoidHom ⟨z, hz⟩ = zs) :
    ∀ a ∈ A, z * a * z⁻¹ = a ^ k := by
  intro a ha
  have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h
  have e1 : ((A.normalizerMonoidHom ⟨z, hz⟩ ⟨a, ha⟩ : A) : G) = z * a * z⁻¹ := rfl
  simp only [e1] at h2
  rw [h2, hk ⟨a, ha⟩]
  rfl

theorem isScalarOn_of_pi_eq_pow {k : ℕ} (hk : ∀ a : A, zs a = a ^ k) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (n : ℕ)
    (hyw : A.normalizerMonoidHom ⟨y, hy⟩ = zs ^ n) : ∀ a ∈ A, y * a * y⁻¹ = a ^ (k ^ n) := by
  intro a ha
  have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) hyw
  have e1 : ((A.normalizerMonoidHom ⟨y, hy⟩ ⟨a, ha⟩ : A) : G) = y * a * y⁻¹ := rfl
  simp only [e1] at h2
  rw [h2, pow_apply_of_apply hk n ⟨a, ha⟩]
  rfl

theorem pow_conj_eq_of_pi_pow_eq_one {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) {m : ℕ}
    (h : (A.normalizerMonoidHom ⟨w, hw⟩) ^ m = 1) : ∀ a ∈ A, w ^ m * a * (w ^ m)⁻¹ = a := by
  intro a ha
  have h1 : A.normalizerMonoidHom ((⟨w, hw⟩ : Subgroup.normalizer (A : Set G)) ^ m) = 1 := by
    rw [map_pow]
    exact h
  have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h1
  have e1 : ((A.normalizerMonoidHom ((⟨w, hw⟩ : Subgroup.normalizer (A : Set G)) ^ m) ⟨a, ha⟩ : A) : G) =
      w ^ m * a * (w ^ m)⁻¹ := rfl
  simp only [e1] at h2
  rw [h2]
  rfl

theorem exists_moved_of_pi_ne_one {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (h : A.normalizerMonoidHom ⟨w, hw⟩ ≠ 1) : ∃ a ∈ A, w * a * w⁻¹ ≠ a := by
  by_contra hcon
  push Not at hcon
  apply h
  ext a
  show w * (a : G) * w⁻¹ = (((1 : MulAut A) a : A) : G)
  rw [hcon a a.2]
  rfl

theorem exists_pow_of_mem_zpowers {H : Type} [Group H] {z y : H} (hz : z ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers z) : ∃ n : ℕ, y = z ^ n := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨(i % 3).toNat, ?_⟩
  have h3 : z ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hz
  rw [zpow_eq_zpow_emod i h3, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

end Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}

theorem models_at (hKt1 : JLemmaKt1) (hctx : HessCtx p A c L) (hpair : KF134Pair)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    ∀ J ∈ thetaCompZeroStarE p A,
      StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f := by
  intro J hJ
  obtain ⟨c1, h1⟩ := hgood J hJ
  obtain ⟨f', -, hf', hm'⟩ := h1.model
  have := models_eq_all hKt1 hctx hpair hgood hctx.facts13.inZeroStar hJ hf hm hf' hm'
  subst this
  exact hm'

theorem rank_bound (hKt : JLemmaKt) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (Xs : Subgroup (MulAut A)) (E : Subgroup ↥(Xsub A Xs))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hπ : ∀ e ∈ E, piX Xs e ∈ Subgroup.zpowers zs) : Nat.card E ≤ 27 := by
  classical
  obtain ⟨c1, h1⟩ := hgood L hctx.facts13.inZeroStar
  obtain ⟨k, -, -, hk⟩ := hspec.z_scalar
  have hact : ∀ e ∈ E, ∃ n : ℕ,
      A.normalizerMonoidHom ⟨(e : G), (mem_Xsub.1 e.2).1⟩ = zs ^ n := fun e he =>
    exists_pow_of_mem_zpowers hspec.z_cube (hπ e he)
  have hscalar : ∀ e ∈ E, IsScalarOn A (e : G) := fun e he => by
    obtain ⟨n, hn⟩ := hact e he
    exact ⟨k ^ n, isScalarOn_of_pi_eq_pow hk (mem_Xsub.1 e.2).1 n hn⟩
  have hnormL : ∀ e ∈ E, (e : G) ∈ Subgroup.normalizer (L : Set G) := fun e he =>
    h1.mem_normalizer_of_scalar (mem_Xsub.1 e.2).1 (hscalar e he)
  set R : Subgroup G := E.map (Xsub A Xs).subtype with hR
  have hR3 : IsPGroup 3 R := by
    intro u
    obtain ⟨e, he, hu⟩ := Subgroup.mem_map.1 u.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have : (e : G) ^ 3 = 1 := congrArg Subtype.val (hexp e he)
    show (u : G) ^ (3 ^ 1) = 1
    rw [← hu]
    simpa using this
  have hRle : R ≤ Subgroup.normalizer (L : Set G) ⊓ torusNormalizer A := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨hnormL e he, (mem_Xsub.1 e.2).1⟩
  have hRsc : ∀ u ∈ R, ∃ k : ℕ, ∀ a ∈ Tof A L, u * a * u⁻¹ = a ^ k := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨n, hn⟩ := hact e he
    exact ⟨k ^ n, fun a ha => isScalarOn_of_pi_eq_pow hk (mem_Xsub.1 e.2).1 n hn a (Tof_le A L ha)⟩
  obtain ⟨S, hS1, hS2, -, hRS⟩ := hKt G p A c1 L h1 R hR3 hRle hRsc
  have hpg : IsPGroup 3 ↥E := by
    intro e
    exact ⟨1, Subtype.ext (by simpa using hexp e e.2)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  let f : ↥E →* G := (Xsub A Xs).subtype.comp E.subtype
  have hfinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hm3 : m ≤ evenRank G :=
    PlaneAux.le_evenRank_of_hom_normalizes (p := 3) (A := ↥E) Nat.prime_three (by norm_num)
      (fun a b => Subtype.ext (hcomm a a.2 b b.2)) (fun a => Subtype.ext (by simpa using hexp a a.2)) hm f hfinj
      hS1 hS2 (fun e => hRS ⟨(e : ↥(Xsub A Xs)), e.2, rfl⟩)
  have hev : evenRank G = 3 := hctx.hyp.evenRank_eq
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hev ▸ hm3)
    _ = 27 := by norm_num

theorem caseA_contra (hJ : JFacts) (hpair : KF134Pair) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (hcard : Nat.card (reflectionGroup p A) = 54) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) (h1mod : 2 ^ f % 3 = 1) :
    False := by
  classical
  have hJ' := hJ
  obtain ⟨-, hF, -, hA, hKt, hKt1, -, -⟩ := hJ'
  have hmods := models_at hKt1 hctx hpair hgood hf hm
  obtain ⟨k, hk1, hk3, hk⟩ := hspec.z_scalar
  have hXs : reflectionGroup p A ≤ A.normalizerMonoidHom.range := WeylIso.closure_le_weyl
  obtain ⟨z0, hz0N, hz03, hz0π⟩ := exists_z hJ hctx hgood hspec
  have hz0X : z0 ∈ Xsub A (reflectionGroup p A) :=
    mem_Xsub.2 ⟨hz0N, by rw [hz0π]; exact hspec.P_le hspec.z_mem⟩
  have h9 : 9 ∣ 2 ^ f - 1 := by
    obtain ⟨c1, h1⟩ := hgood L hctx.facts13.inZeroStar
    have hzL : z0 ∈ Subgroup.normalizer (L : Set G) ⊓ torusNormalizer A :=
      ⟨h1.mem_normalizer_of_scalar hz0N ⟨k, action_of_pi_eq hk hz0N hz0π⟩, hz0N⟩
    have h3 : 3 ∣ f := hF G p A c1 L h1 f hf hm z0 hzL hz03 k hk1 hk3
      (fun a ha => action_of_pi_eq hk hz0N hz0π a (Tof_le A L ha))
    exact nine_dvd_two_pow_sub_one h3 h1mod
  have : Nonempty ↥(thetaCompZeroStarE p A) := ⟨⟨L, hctx.facts13.inZeroStar⟩⟩
  refine caseA_false_range (X := ↥(Xsub A (reflectionGroup p A))) (piX (reflectionGroup p A)) ?_
    Ps ?_ hspec.card_P ?_ zs hspec.z_cube hspec.z_ne ⟨z0, hz0X⟩ ?_ ?_
    (ι := ↥(thetaCompZeroStarE p A)) (fun i => Aline A i.1 Ps zs) ?_ ?_
    (fun i => (Vof A i.1).subgroupOf (Xsub A (reflectionGroup p A))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [range_piX _ hXs]
    exact hcard
  · rw [range_piX _ hXs]
    exact hspec.P_le
  · rw [range_piX _ hXs]
    exact hspec.mem_P
  · exact Subtype.ext (by simpa using hz03)
  · rw [piX_eq]
    exact hz0π
  · intro i
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    exact h'.card_Aline hspec
  · intro i
    exact Aline_le_Ps hspec.z_mem
  · intro i v hv
    rw [Subgroup.mem_subgroupOf] at hv
    rw [mem_ker_piX]
    intro a ha
    have hvC : (v : G) ∈ Subgroup.centralizer (A : Set G) := (Vof_le i.1 hv).2
    exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hvC a ha).symm
  · intro i a ha b hb
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    have hE := (hA G p A c' i.1 h' f hf h9 (hmods i.1 i.2)).1.1
    rw [Subgroup.mem_subgroupOf] at ha hb
    have h := hE.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
    have h2 : (a : G) * b = b * a := congrArg Subtype.val h
    exact Subtype.ext h2
  · intro i a ha
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    have hE := (hA G p A c' i.1 h' f hf h9 (hmods i.1 i.2)).1.1
    rw [Subgroup.mem_subgroupOf] at ha
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (Vof A i.1)) ⟨(a : G), ha⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  · intro i
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    have hc := (hA G p A c' i.1 h' f hf h9 (hmods i.1 i.2)).1.2
    have hle : Vof A i.1 ≤ Xsub A (reflectionGroup p A) :=
      (Vof_le i.1).trans (inf_le_right.trans (centralizer_le_Xsub _))
    rw [card_subgroupOf_of_le hle]
    exact hc
  · intro i x hx v hv
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    rw [mem_ker_piX] at hx
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (mul_inv_eq_iff_eq_mul.1 (hx a ha)).symm
    exact conj_mem_Vof (h'.centralizer_A_le_normalizer hxC) (mem_Xsub.1 x.2).1 hv
  · intro i y hy v hv
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) := (mem_Xsub.1 y.2).1
    have hy' : A.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ Aline A i.1 Ps zs := hy
    obtain ⟨w, hwJ, hw, n, hwP, hyw⟩ := Aline_decomp hspec hyN hy'
    have hyJ := h'.mem_normalizer_of_decomp hk hyN hw hwJ n hyw
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact conj_mem_Vof hyJ hyN hv
  · intro i y hy hnz
    obtain ⟨c', h'⟩ := hgood i.1 i.2
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) := (mem_Xsub.1 y.2).1
    have hy' : A.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ Aline A i.1 Ps zs := hy
    obtain ⟨w, hwJ, hw, n, hwP, hyw⟩ := Aline_decomp hspec hyN hy'
    have hyJ := h'.mem_normalizer_of_decomp hk hyN hw hwJ n hyw
    have hπw1 : A.normalizerMonoidHom ⟨w, hw⟩ ≠ 1 := by
      intro h1
      apply hnz
      show A.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ Subgroup.zpowers zs
      rw [hyw, h1, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers zs) n
    have hw3 : (A.normalizerMonoidHom ⟨w, hw⟩) ^ 3 = 1 :=
      (hspec.mem_P _ (hspec.P_le hwP)).1 hwP
    obtain ⟨-, hmove⟩ := hA G p A c' i.1 h' f hf h9 (hmods i.1 i.2)
    obtain ⟨v, hv, hne⟩ := hmove w ⟨hwJ, hw⟩ (pow_conj_eq_of_pi_pow_eq_one hw hw3)
      (exists_moved_of_pi_ne_one hw hπw1) (y : G) ⟨hyJ, hyN⟩ (k ^ n)
      (action_of_decomp hk hyN hw n hyw)
    have hvX : v ∈ Xsub A (reflectionGroup p A) := centralizer_le_Xsub _ (Vof_le i.1 hv).2
    refine ⟨⟨v, hvX⟩, ?_, fun h => hne (congrArg Subtype.val h)⟩
    rw [Subgroup.mem_subgroupOf]
    exact hv
  · intro y hyP hyZ
    obtain ⟨J, hJm, hyJ⟩ := exists_Aline_of_mem hctx hspec hpair hyP hyZ
    exact ⟨⟨J, hJm⟩, hyJ⟩
  · intro x i
    have hxN : (x : G) ∈ Subgroup.normalizer (A : Set G) := (mem_Xsub.1 x.2).1
    refine ⟨⟨conjBy (x : G) i.1, conjBy_mem_thetaCompZeroStarE hctx.hyp.prime hxN i.2⟩, ?_⟩
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact conj_mem_Vof_conjBy hxN hv
  · intro E hcomm hexp hπ
    exact rank_bound hKt hctx hgood hspec _ E hcomm hexp hπ

end CFSG.RankThree.PartOne.N143
