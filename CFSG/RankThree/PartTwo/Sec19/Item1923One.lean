module

public import CFSG.RankThree.PartTwo.Sec19.Item1923O23
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
public import CFSG.RankThree.PartTwo.Sec19.Item1923Inner
public import CFSG.RankThree.PartTwo.Sec19.Item1923KM2

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem barAut_eq_one_iff_of_mem {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    Sec3.Sims321.barAut K ⟨x, hx⟩ = 1 ↔
      ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  constructor
  · intro h1 k hk
    have h2 : ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K) =
        ((⟨x * k * x⁻¹, Sec3.Sims321.conj_mem_of_mem_normalizer K ⟨x, hx⟩ ⟨k, hk⟩⟩ : K) :
          K ⧸ CFSG.pCore 2 K) := by
      have := Sec3.Sims321.barAut_mk K ⟨x, hx⟩ ⟨k, hk⟩
      rw [h1, MulAut.one_apply] at this
      exact this
    set u : K := ⟨x * k * x⁻¹, Sec3.Sims321.conj_mem_of_mem_normalizer K ⟨x, hx⟩ ⟨k, hk⟩⟩
    set v : K := ⟨k, hk⟩
    have h3 : ((u * v⁻¹ : K) : K ⧸ CFSG.pCore 2 K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h2, mul_inv_cancel]
    exact (CFSG.mem_openPCoreOf_iff (H := K) (u * v⁻¹)).mpr ((QuotientGroup.eq_one_iff _).mp h3)
  · intro h
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [Sec3.Sims321.barAut_mk, MulAut.one_apply, ← mul_inv_eq_one, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      refine (CFSG.mem_openPCoreOf_iff (H := K) _).mp ?_
      exact h y y.2

private theorem map_eq_of_forall_map_le {P : Type*} [Group P] {S : Subgroup (MulAut P)}
    {X : Subgroup P} (hX : ∀ φ ∈ S, X.map φ.toMonoidHom ≤ X) :
    ∀ φ ∈ S, X.map φ.toMonoidHom = X := by
  intro φ hφ
  refine le_antisymm (hX φ hφ) fun x hx => ?_
  exact ⟨φ⁻¹ x, hX φ⁻¹ (S.inv_mem hφ) ⟨x, hx, rfl⟩, MulEquiv.apply_symm_apply φ x⟩

private theorem faithful_or_trivial (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M) :
    (∀ b ∈ A ⊓ L, (∃ hb : b ∈ Subgroup.normalizer (K : Set G),
        Sec3.Sims321.barAut K ⟨b, hb⟩ = 1) → b = 1) ∨
      ∀ b ∈ A ⊓ L, ∃ hb : b ∈ Subgroup.normalizer (K : Set G),
        Sec3.Sims321.barAut K ⟨b, hb⟩ = 1 := by
  have hBN : A ⊓ L ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_left.trans (step1923_normalizer_A h hK)
  obtain ⟨hirr, -⟩ := step1923_irreducible h hF hK
  let Bc : Subgroup ↥(A ⊓ L) :=
    MonoidHom.ker ((Sec3.Sims321.barAut K).comp (Subgroup.inclusion hBN))
  have hmem : ∀ x : ↥(A ⊓ L), x ∈ Bc ↔ Sec3.Sims321.barAut K ⟨(x : G), hBN x.2⟩ = 1 :=
    fun x => Iff.rfl
  have hstable : ∀ φ ∈ Sec4.autIn (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G))
      (A ⊓ L), Bc.map φ.toMonoidHom = Bc := by
    apply map_eq_of_forall_map_le
    intro φ hφ
    obtain ⟨w, hwB, hwS, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hwK : w ∈ Subgroup.normalizer (K : Set G) := (Subgroup.mem_inf.mp hwS).2
    have key : ∀ x ∈ Bc, (A ⊓ L).normalizerMonoidHom ⟨w, hwB⟩ x ∈ Bc := by
      intro x hx
      rw [hmem] at hx ⊢
      have e : (⟨(((A ⊓ L).normalizerMonoidHom ⟨w, hwB⟩ x : ↥(A ⊓ L)) : G),
          hBN ((A ⊓ L).normalizerMonoidHom ⟨w, hwB⟩ x).2⟩ :
            ↥(Subgroup.normalizer (K : Set G))) =
          ⟨w, hwK⟩ * ⟨(x : G), hBN x.2⟩ * ⟨w, hwK⟩⁻¹ :=
        Subtype.ext (Sec4.normalizerMonoidHom_apply_coe hwB x)
      rw [e, map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact key x hx
  rcases hirr Bc hstable with hbot | htop
  · left
    intro b hb hb1
    obtain ⟨hbN, h1⟩ := hb1
    have hbc : (⟨b, hb⟩ : ↥(A ⊓ L)) ∈ Bc := (hmem _).mpr h1
    rw [hbot, Subgroup.mem_bot] at hbc
    exact congrArg Subtype.val hbc
  · right
    intro b hb
    exact ⟨hBN hb, (hmem ⟨b, hb⟩).mp ((Subgroup.eq_top_iff' Bc).mp htop ⟨b, hb⟩)⟩

theorem step1923_card_barActionImage (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M)
    (hfaith : ∀ b ∈ A ⊓ L, (∃ hb : b ∈ Subgroup.normalizer (K : Set G),
      Sec3.Sims321.barAut K ⟨b, hb⟩ = 1) → b = 1) :
    CFSG.Assembly.IsElemAbelian 3 (barActionImage K (A ⊓ L)) ∧
      Nat.card (barActionImage K (A ⊓ L)) = 9 := by
  have hBN : A ⊓ L ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_left.trans (step1923_normalizer_A h hK)
  let φ : ↥(A ⊓ L) →* MulAut (K ⧸ CFSG.pCore 2 K) :=
    (Sec3.Sims321.barAut K).comp (Subgroup.inclusion hBN)
  have hrange : barActionImage K (A ⊓ L) = φ.range := by
    ext d
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Subgroup.inclusion hBN b, b.2, rfl⟩
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfaith b b.2 ⟨hBN b.2, hb⟩)
  have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L : Subgroup G) :=
    CFSG.Open.IsElemAbelian.mono h.isE27.1 inf_le_left
  have hcomm := hBe.1
  rw [hrange]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    change (a : MulAut (K ⧸ CFSG.pCore 2 K)) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm' a' b']
  · obtain ⟨y, rfl⟩ := hx
    rw [← map_pow]
    have hy3 : y ^ 3 = 1 := Subtype.ext (hBe.2 y y.2)
    rw [hy3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hF.card

private theorem ncard_conj_eq_two_of_not_le (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) (hK : K ∈ oTwoComponentsIn M)
    (hW : ¬ planeGroup A L c ≤ Subgroup.normalizer (K : Set G)) :
    {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard = 2 := by
  have hle := Sec18.Item185Proof.ncard_conj_le_two h.toSec18Std hK
  obtain ⟨w, hwW, hwK⟩ := Set.not_subset.mp hW
  have hwM : w ∈ M :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (step1923_W_le h hF hwW)).1).2
  have hne : K.map (MulAut.conj w).toMonoidHom ≠ K := fun hEq =>
    hwK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq)
  have hlt : 1 < {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mpr
      ⟨K, K.map (MulAut.conj w).toMonoidHom, ⟨1, M.one_mem, by ext y; simp⟩, ⟨w, hwM, rfl⟩,
        hne.symm⟩
  omega

private theorem outTwoExpTwo_of_relIndex_eq_two (hkf : KFacts1923) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N) (hlist : InK194 (K ⧸ CFSG.pCore 2 K))
    (hidx : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
      (planeGroup A L c) = 2) : OutTwoExpTwo (K ⧸ CFSG.pCore 2 K) := by
  have hW : ¬ planeGroup A L c ≤ Subgroup.normalizer (K : Set G) := by
    intro hle
    have h1 : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
        (planeGroup A L c) = 1 := Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hle)
    omega
  exact hkf.kf1.2.1 _ hlist (step1923_KM2 h hK hkf.h194 hkf.kf2 hkf.kf3a hkf.kfbig
    (ncard_conj_eq_two_of_not_le h hF hK.1 hW))

private theorem barAut_inverts {B : Subgroup G} (e : ↥(Subgroup.normalizer (K : Set G)))
    (he : ∀ b ∈ B, (e : G) * b * (e : G)⁻¹ = b⁻¹) :
    ∀ d ∈ barActionImage K B,
      Sec3.Sims321.barAut K e * d * (Sec3.Sims321.barAut K e)⁻¹ = d⁻¹ := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : e * x * e⁻¹ = x⁻¹ := Subtype.ext (he x hx)
  have key : Sec3.Sims321.barAut K (e * x * e⁻¹) =
      Sec3.Sims321.barAut K e * Sec3.Sims321.barAut K x * (Sec3.Sims321.barAut K e)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← key, hx', map_inv]

private theorem barAut_mem_normalizer_image {B : Subgroup G}
    (e : ↥(Subgroup.normalizer (K : Set G)))
    (heB : (e : G) ∈ Subgroup.normalizer (B : Set G)) :
    Sec3.Sims321.barAut K e ∈
      Subgroup.normalizer ((barActionImage K B : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))) :
        Set (MulAut (K ⧸ CFSG.pCore 2 K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e * x * e⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp heB x).mp hx
  · rintro ⟨x, hx, hxd⟩
    have heB' : (e : G)⁻¹ ∈ Subgroup.normalizer (B : Set G) := Subgroup.inv_mem _ heB
    refine ⟨e⁻¹ * x * e, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp heB' x).mp hx
      rw [inv_inv] at h1
      exact h1
    · rw [map_mul, map_mul, map_inv, hxd]
      group

private theorem le_pRank_of_le_inner {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {D : Subgroup (MulAut X)} (hD : D ≤ inner X)
    (hDe : CFSG.Assembly.IsElemAbelian 3 D) {k : ℕ} (hk : Nat.card D = 3 ^ k) :
    k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : a * g * a⁻¹ = b * g * b⁻¹ := by
        simpa [MulAut.conj_apply] using DFunLike.congr_fun hab g
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [hg]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  let D' : Subgroup X := D.comap (MulAut.conj : X →* MulAut X)
  have hmap : D'.map (MulAut.conj : X →* MulAut X) = D := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hD
  have hDc := hDe.1
  have hD'e : CFSG.Assembly.IsElemAbelian 3 D' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have ha : MulAut.conj (a : X) ∈ D := a.2
      have hb : MulAut.conj (b : X) ∈ D := b.2
      have := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : D) ⟨_, hb⟩)
      simpa [map_mul] using this
    · apply hinj
      rw [map_pow, map_one]
      exact hDe.2 _ hx
  have hcard : Nat.card D' = 3 ^ k := by
    have := Subgroup.card_map_of_injective (K := D') hinj
    rw [hmap, hk] at this
    exact this.symm
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hD'e hcard

private theorem false_of_faithful
    (hkf : KFacts1923) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N)
    (hfaith : ∀ b ∈ A ⊓ L, (∃ hb : b ∈ Subgroup.normalizer (K : Set G),
      Sec3.Sims321.barAut K ⟨b, hb⟩ = 1) → b = 1) : False := by
  classical
  have hKM : K ∈ oTwoComponentsIn M := hK.1
  obtain ⟨hlist, hP⟩ := step1923_list hkf.h194 h hK
  obtain ⟨hDab, hD9⟩ := step1923_card_barActionImage h hF hKM hfaith
  have hab : OutTwoAbelian (K ⧸ CFSG.pCore 2 K) := hkf.kf1.1 _ hlist
  have hexp : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
      (planeGroup A L c) = 2 → OutTwoExpTwo (K ⧸ CFSG.pCore 2 K) :=
    outTwoExpTwo_of_relIndex_eq_two hkf h hF hK hlist
  have hinn := step1923_inner h hF hKM hab hexp
  have hw := step1923_inverting h hF hKM hab hexp
  have hpar : barActionImage K (A ⊓ L) ≤ (starIm K N).map
      (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →* MulAut (K ⧸ CFSG.pCore 2 K)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxB : (x : G) ∈ A ⊓ L := hx
    exact step1923_inner_mem_parab h hP (h.le_N (Subgroup.mem_inf.mp hxB).1) x.2
      (hinn (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hO23 := step1923_O23 h hF hK hP hpar hw
  have hWN : ∀ w ∈ planeGroup A L c,
      w ∈ N ∧ w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    fun w hw => ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (step1923_W_le h hF hw)).1).1,
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).2⟩
  by_cases hnc : IsNoncyclicOutType (K ⧸ CFSG.pCore 2 K)
  · obtain ⟨w, hwN, hwW, hwinv, hwi⟩ := hw
    refine (hkf.kfpar _ hlist).1 hnc (starIm K N) (barActionImage K (A ⊓ L)) hP hpar hDab hD9
      hO23 (Sec3.Sims321.barAut K ⟨w, hwN⟩)
      (step1923_inner_mem_parab h hP (hWN w hwW).1 hwN hwi)
      (barAut_mem_normalizer_image ⟨w, hwN⟩ (hWN w hwW).2) ?_
    exact barAut_inverts ⟨w, hwN⟩ hwinv
  · have hcyc : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (K ⧸ CFSG.pCore 2 K) :=
      hkf.kf1.2.2 _ hlist hnc
    have hnorm : planeGroup A L c ≤ Subgroup.normalizer (K : Set G) := by
      by_contra hW
      rcases step1923_KM2 h hK hkf.h194 hkf.kf2 hkf.kf3a hkf.kfbig
          (ncard_conj_eq_two_of_not_le h hF hKM hW) with hL3 | hT | hS
      · obtain ⟨hr, hZ⟩ := hkf.kf3b _ hL3
        have := le_pRank_of_le_inner hZ hinn hDab (k := 2) (by rw [hD9]; norm_num)
        omega
      · exact hnc (Or.inr (Or.inr (Or.inr hT)))
      · exact hnc (Or.inl ⟨1, le_rfl, Or.inl hS⟩)
    obtain ⟨w, hwN, hwW, hwinv, hwi⟩ := step1923_square_inverting h hF hKM hcyc hnorm
    refine (hkf.kfpar _ hlist).2 hnc (starIm K N) (barActionImage K (A ⊓ L)) hP hpar hDab hD9
      hO23 (Sec3.Sims321.barAut K ⟨w, hwN⟩)
      (step1923_inner_mem_parab h hP (hWN w hwW).1 hwN hwi)
      (barAut_mem_normalizer_image ⟨w, hwN⟩ (hWN w hwW).2) ?_
    have hsq := barAut_inverts (K := K) (B := A ⊓ L) (⟨w, hwN⟩ ^ 2) (fun b hb => by
      simpa [pow_two] using hwinv b hb)
    intro d hd
    have h2 := hsq d hd
    rwa [map_pow] at h2

theorem item1923_one
    (hkf : KFacts1923) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) :
    ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  rcases faithful_or_trivial h hF hK.1 with hfaith | hall
  · exact (false_of_faithful hkf h hF hK hfaith).elim
  · intro b hb k hk
    obtain ⟨hbN, h1⟩ := hall b hb
    exact (barAut_eq_one_iff_of_mem hbN).mp h1 k hk

end CFSG.RankThree.PartTwo.Late
