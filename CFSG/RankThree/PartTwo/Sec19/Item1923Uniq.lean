module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Item1923Rank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Image
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
import CFSG.RankThree.PartTwo.Sec11.Item116R1Alg
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

section Helpers

variable {Y : Type*} [Group Y]

private theorem b8_comm_of_isElemAbelian {p : ℕ} {E : Subgroup Y}
    (hE : CFSG.Open.IsElemAbelian p E) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

private theorem b8_isElemAbelian_of_comm_pow {p : ℕ} {E : Subgroup Y}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hp : ∀ x ∈ E, x ^ p = 1) :
    CFSG.Open.IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => hp x hx⟩

private theorem b8_isElemAbelian_map {Y' : Type*} [Group Y'] {p : ℕ} {E : Subgroup Y}
    (f : Y →* Y') (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine b8_isElemAbelian_of_comm_pow ?_ ?_
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, b8_comm_of_isElemAbelian hE a ha b hb]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 a ha, map_one]

private theorem b8_commute_sup_of_comm {H K : Subgroup Y} {S : Set Y}
    (hH : ∀ x ∈ H, ∀ s ∈ S, x * s = s * x) (hK : ∀ x ∈ K, ∀ s ∈ S, x * s = s * x) :
    ∀ x ∈ H ⊔ K, ∀ s ∈ S, x * s = s * x := by
  have hle : H ⊔ K ≤ Subgroup.centralizer S := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    · exact (hH x hx s hs).symm
    · exact (hK x hx s hs).symm
  intro x hx s hs
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) s hs).symm

private theorem b8_isElemAbelian_sup_of_comm {p : ℕ} {E F : Subgroup Y}
    (hE : CFSG.Open.IsElemAbelian p E) (hF : CFSG.Open.IsElemAbelian p F)
    (hEF : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) : CFSG.Open.IsElemAbelian p (E ⊔ F) := by
  have hEc := b8_comm_of_isElemAbelian hE
  have hFc := b8_comm_of_isElemAbelian hF
  have h1 : ∀ x ∈ E ⊔ F, ∀ s ∈ (E : Set Y), x * s = s * x :=
    b8_commute_sup_of_comm (fun x hx s hs => hEc x hx s hs)
      (fun x hx s hs => (hEF s hs x hx).symm)
  have h2 : ∀ x ∈ E ⊔ F, ∀ s ∈ (F : Set Y), x * s = s * x :=
    b8_commute_sup_of_comm (fun x hx s hs => hEF x hx s hs) (fun x hx s hs => hFc x hx s hs)
  have hcomm : ∀ x ∈ E ⊔ F, ∀ y ∈ E ⊔ F, x * y = y * x := by
    intro x hx y hy
    have hle : E ⊔ F ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine sup_le (fun e he => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
        (fun f hf => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
      · rw [Set.mem_singleton_iff.mp hs]; exact h1 x hx e he
      · rw [Set.mem_singleton_iff.mp hs]; exact h2 x hx f hf
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x (Set.mem_singleton x)
  have hexp : ∀ x ∈ E ⊔ F, x ^ p = 1 := by
    intro x hx0
    have hx : x ∈ Subgroup.closure ((E : Set Y) ∪ (F : Set Y)) := by
      rw [← Subgroup.sup_eq_closure]; exact hx0
    clear hx0
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hE.2 x hx
      · exact hF.2 x hx
    | one => exact one_pow p
    | mul x y hxm hym ihx ihy =>
      have hxS : x ∈ E ⊔ F := by rw [Subgroup.sup_eq_closure]; exact hxm
      have hyS : y ∈ E ⊔ F := by rw [Subgroup.sup_eq_closure]; exact hym
      have hcm : Commute x y := hcomm x hxS y hyS
      rw [hcm.mul_pow p, ihx, ihy, one_mul]
    | inv x _ ihx => rw [inv_pow, ihx, inv_one]
  exact b8_isElemAbelian_of_comm_pow hcomm hexp

private theorem b8_exists_mul_of_mem_sup_of_comm {H K : Subgroup Y}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : Y} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h1, hh1, k1, hk1, rfl⟩ := ihx
    obtain ⟨h2, hh2, k2, hk2, rfl⟩ := ihy
    refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
    have hk : k1 * h2 = h2 * k1 := (hc h2 hh2 k1 hk1).symm
    calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by group
      _ = h1 * (h2 * k1) * k2 := by rw [hk]
      _ = h1 * h2 * (k1 * k2) := by group
  | inv x _ ihx =>
    obtain ⟨h1, hh1, k1, hk1, rfl⟩ := ihx
    refine ⟨h1⁻¹, H.inv_mem hh1, k1⁻¹, K.inv_mem hk1, ?_⟩
    have hk : h1 * k1 = k1 * h1 := hc h1 hh1 k1 hk1
    calc (h1 * k1)⁻¹ = (k1 * h1)⁻¹ := by rw [hk]
      _ = h1⁻¹ * k1⁻¹ := by group

private theorem b8_eq_of_card_nine_of_normal {T : Type*} [Group T] [Finite T]
    (hT : Nat.card T = 72) {E F : Subgroup T} [E.Normal] (hE : Nat.card E = 9)
    (hF : Nat.card F = 9) : E = F := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFp : IsPGroup 3 F := IsPGroup.of_card (n := 2) (by rw [hF]; norm_num)
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  have hES : E ≤ (S : Subgroup T) := hEp.le_sylow_of_normal S
  have hS : Nat.card (S : Subgroup T) = 9 := by
    obtain ⟨k, hk⟩ := (S.isPGroup').exists_card_eq
    have hdvd : Nat.card (S : Subgroup T) ∣ 72 := hT ▸ Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card F ≤ Nat.card (S : Subgroup T) := Subgroup.card_le_of_le hFS
    rw [hF] at hle
    rw [hk] at hdvd hle ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have h27 : 3 ^ 3 ∣ 72 := (pow_dvd_pow 3 hk3).trans hdvd
      norm_num at h27
    interval_cases k
    · exact absurd hle (by norm_num)
    · exact absurd hle (by norm_num)
    · norm_num
  have h1 : F = (S : Subgroup T) :=
    Subgroup.eq_of_le_of_card_ge hFS (le_of_eq (by rw [hS, hF]))
  have h2 : E = (S : Subgroup T) :=
    Subgroup.eq_of_le_of_card_ge hES (le_of_eq (by rw [hS, hE]))
  rw [h1, h2]

private theorem b8_eq_of_card_nine_normal_in [Finite Y] {T E F : Subgroup Y}
    (hT : Nat.card T = 72) (hET : E ≤ T) (hFT : F ≤ T)
    (hEn : ∀ g ∈ T, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hEc : Nat.card E = 9) (hFc : Nat.card F = 9) :
    E = F := by
  haveI : (E.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hEn (g : Y) g.2 n hn
    simpa using this⟩
  have hcardE : Nat.card (E.subgroupOf T) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv, hEc]
  have hcardF : Nat.card (F.subgroupOf T) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv, hFc]
  have hTc : Nat.card T = 72 := hT
  have key := b8_eq_of_card_nine_of_normal (T := T) hTc hcardE hcardF
  ext y
  constructor
  · intro hy
    have hyT : y ∈ T := hET hy
    have : (⟨y, hyT⟩ : T) ∈ F.subgroupOf T := by
      rw [← key]; exact Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_subgroupOf.mp this
  · intro hy
    have hyT : y ∈ T := hFT hy
    have : (⟨y, hyT⟩ : T) ∈ E.subgroupOf T := by
      rw [key]; exact Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_subgroupOf.mp this

private theorem b8_central_three_eq_bot_of_rank_one {Γ : Type*} [Group Γ] [Finite Γ]
    (hperf : commutator Γ = ⊤)
    (hb : ∀ V : Subgroup Γ, CFSG.Open.IsElemAbelian 3 V → Nat.card V ≤ 3)
    (Z : Subgroup Γ) (hZ : Z ≤ Subgroup.center Γ) (hZ3 : IsPGroup 3 Z) : Z = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine central_threeGroup_eq_bot_of_perfect hperf (fun P => ?_) Z hZ hZ3
  apply CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) P.isPGroup'
  unfold CFSG.pRank
  apply csSup_le'
  rintro r ⟨V, hV, hcard⟩
  have hVe : CFSG.Open.IsElemAbelian 3 V := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  have hVm := b8_isElemAbelian_map (P : Subgroup Γ).subtype hVe
  have hcard3 : Nat.card (V.map (P : Subgroup Γ).subtype) ≤ 3 := hb _ hVm
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hcard] at hcard3
  by_contra hr
  push Not at hr
  have h9 : 9 ≤ 3 ^ r := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have := h9.trans hcard3
  norm_num at this

end Helpers

section Core

private abbrev b8_piM (M : Subgroup G) : M →* (M ⧸ CFSG.pCore 2 M) :=
  QuotientGroup.mk' (CFSG.pCore 2 M)

private theorem b8_mem_pCore_subtype_iff {M : Subgroup G} {z : G} (hz : z ∈ M) :
    (⟨z, hz⟩ : M) ∈ CFSG.pCore 2 M ↔ z ∈ CFSG.Open.pCoreOf 2 M := by
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem M.subtype h
  · intro h
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp h
    have : w = ⟨z, hz⟩ := Subtype.ext hwz
    rw [← this]
    exact hw

private theorem b8_exists_pow_two_pow_eq_one {H : Subgroup G} {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 H) : ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨z, hz⟩
  refine ⟨m, ?_⟩
  have hm' := congrArg (fun w : ↥(CFSG.pCore 2 H) => ((w : ↥H) : G)) hm
  simpa using hm'

private theorem b8_eq_one_of_pow_three_of_pCoreOf {H : Subgroup G} {x : G} (h3 : x ^ 3 = 1)
    (hx : x ∈ CFSG.Open.pCoreOf 2 H) : x = 1 := by
  obtain ⟨m, hm⟩ := b8_exists_pow_two_pow_eq_one hx
  have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  have hg : x ^ Nat.gcd 3 (2 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨h3, hm⟩
  rw [hcop, pow_one] at hg
  exact hg

private theorem b8_mk_commute_of_pCoreOf {M : Subgroup G} {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (h : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    b8_piM M ⟨x, hx⟩ * b8_piM M ⟨y, hy⟩ = b8_piM M ⟨y, hy⟩ * b8_piM M ⟨x, hx⟩ := by
  have hu : x * y * x⁻¹ * y⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)
  have hM : (⟨x, hx⟩ : M) * ⟨y, hy⟩ = ⟨x * y * x⁻¹ * y⁻¹, hu⟩ * (⟨y, hy⟩ * ⟨x, hx⟩) :=
    Subtype.ext (by simp [mul_assoc])
  have h1 : b8_piM M ⟨x * y * x⁻¹ * y⁻¹, hu⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((b8_mem_pCore_subtype_iff hu).mpr h)
  calc b8_piM M ⟨x, hx⟩ * b8_piM M ⟨y, hy⟩ = b8_piM M ((⟨x, hx⟩ : M) * ⟨y, hy⟩) := by rw [map_mul]
    _ = b8_piM M (⟨x * y * x⁻¹ * y⁻¹, hu⟩ * (⟨y, hy⟩ * ⟨x, hx⟩)) := by rw [hM]
    _ = b8_piM M ⟨x * y * x⁻¹ * y⁻¹, hu⟩ * b8_piM M (⟨y, hy⟩ * ⟨x, hx⟩) := map_mul _ _ _
    _ = b8_piM M (⟨y, hy⟩ * ⟨x, hx⟩) := by rw [h1, one_mul]
    _ = b8_piM M ⟨y, hy⟩ * b8_piM M ⟨x, hx⟩ := map_mul _ _ _

private theorem b8_barAut_eq_one_of_forall {L : Subgroup G}
    (x : ↥(Subgroup.normalizer (L : Set G)))
    (hx : ∀ y ∈ L, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    Sec3.Sims321.barAut L x = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H y =>
    rw [Sec3.Sims321.barAut_mk, MulAut.one_apply, QuotientGroup.eq]
    have hyi : (y : G)⁻¹ ∈ L := L.inv_mem y.2
    have hconj : (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ L :=
      Sec3.Sims321.conj_mem_of_mem_normalizer L x ⟨(y : G)⁻¹, hyi⟩
    have hzL : (x : G) * (y : G)⁻¹ * (x : G)⁻¹ * (y : G) ∈ L := L.mul_mem hconj y.2
    have hpc := (b8_mem_pCore_subtype_iff hzL).mpr (by simpa using hx (y : G)⁻¹ hyi)
    convert hpc using 1
    apply Subtype.ext
    simp [mul_assoc]

private theorem b8_le_pCoreOf_two_of_subnormal {M K' R : Subgroup G} (hK'M : K' ≤ M)
    (hsn : (K'.subgroupOf M).IsSubnormal) (hRK : R ≤ K')
    (hRn : ∀ g ∈ K', ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR2 : IsPGroup 2 R) :
    R ≤ CFSG.Open.pCoreOf 2 M := by
  intro r hr
  have hrM : r ∈ M := hK'M (hRK hr)
  have hR'W : R.subgroupOf M ≤ K'.subgroupOf M := fun z hz => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hRK hz
  have hR'n : ((R.subgroupOf M).subgroupOf (K'.subgroupOf M)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : M) : G) ∈ R := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
    have hg : ((g : M) : G) ∈ K' := Subgroup.mem_subgroupOf.mp g.2
    have key := hRn ((g : M) : G) hg _ hn'
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using key))
  have hR'2 : IsPGroup 2 (R.subgroupOf M) := hR2.comap_subtype
  have h1 : R.subgroupOf M ≤ CFSG.Open.pCoreOf 2 (K'.subgroupOf M) :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hR'W hR'n hR'2
  have h2 : CFSG.Open.pCoreOf 2 (K'.subgroupOf M) ≤ CFSG.Open.pCore 2 ↥M :=
    pCoreOf_le_pCore_of_isSubnormal 2 hsn
  have h3 : (⟨r, hrM⟩ : M) ∈ CFSG.pCore 2 M := h2 (h1 (Subgroup.mem_subgroupOf.mpr hr))
  exact (b8_mem_pCore_subtype_iff hrM).mp h3

end Core

section Action


private theorem b8_forall_mem_of_barAut_eq_one {L : Subgroup G}
    (x : ↥(Subgroup.normalizer (L : Set G))) (hx : Sec3.Sims321.barAut L x = 1) :
    ∀ y ∈ L, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  intro y hy
  have hyi : y⁻¹ ∈ L := L.inv_mem hy
  have h1 := congrArg
    (fun φ : MulAut (L ⧸ CFSG.pCore 2 L) => φ (QuotientGroup.mk (⟨y⁻¹, hyi⟩ : L))) hx
  simp only [MulAut.one_apply] at h1
  rw [Sec3.Sims321.barAut_mk, QuotientGroup.eq] at h1
  refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
  simp [mul_assoc]

private theorem b8_barAut_eq_one_of_mem_K' (kf6 : KF6) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) {K' : Subgroup G} (hK' : K' ∈ oTwoComponentsIn M)
    (hK'N : K' ≤ N) :
    ∀ x : ↥(Subgroup.normalizer (L : Set G)), (x : G) ∈ K' →
      Sec3.Sims321.barAut L x = 1 := by
  classical
  obtain ⟨e⟩ := h.quotient_iso
  have hK'M : K' ≤ M := le_of_mem_oTwoComponentsIn hK'
  have hNL : ∀ x ∈ N, x ∈ Subgroup.normalizer (L : Set G) := fun x hx => by
    rw [hF.normalizer_eq]; exact hx
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hLM : ¬ L ≤ M := hF.not_le_M
  have hO2 : CFSG.Open.pCoreOf 2 L ≤ M := hF.pCoreOf_le_M
  have hNB : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M := hF.normalizer_le_M
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := hF.card
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := b8_comm_of_isElemAbelian h.isE27.1
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => h.isE27.1.2 x hx
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    IsPGroup.of_card (n := 2) (hB9.trans (by norm_num))
  have hB3L : IsPGroup 3 ((A ⊓ L).subgroupOf L) := hB3.comap_subtype
  set E : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hEdef
  have hEcard : Nat.card E = 9 := by
    have h1 := CFSG.RankThree.PartTwo.Sec20.card_eq_card_map_mul_inf_ker
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ((A ⊓ L).subgroupOf L)
    rw [QuotientGroup.ker_mk', CFSG.RankThree.PartTwo.Sec20.card_inf_eq_one_of_isPGroup hB3L
      CFSG.pCore_isPGroup, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv,
      hB9] at h1
    exact h1.symm
  have hEel : CFSG.Open.IsElemAbelian 3 E := by
    refine b8_isElemAbelian_of_comm_pow ?_ ?_
    · intro x hx y hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hb).1 _
        (Subgroup.mem_subgroupOf.mp hb').1)
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow]
      have h3 : b ^ 3 = 1 := Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hb).1)
      rw [h3, map_one]
  have hTeq : ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Subgroup.normalizer (E : Set (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    h.map_inf_eq_normalizer_of hBL hB9 hNB hLM hO2
  have hTc : Nat.card (Subgroup.normalizer (E : Set (↥L ⧸ CFSG.pCore 2 ↥L))) = 72 :=
    KFacts.L34Max.card_normalizer_of_card_eq_nine e hEcard
  set T : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Subgroup.normalizer (E : Set (↥L ⧸ CFSG.pCore 2 ↥L)) with hTdef
  have hαT : ∀ x : ↥(Subgroup.normalizer (L : Set G)), (x : G) ∈ K' →
      ∀ t ∈ T, Sec3.Sims321.barAut L x t ∈ T := by
    intro x hxK t ht
    rw [← hTeq] at ht ⊢
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ht
    have hy' : (y : G) ∈ L ⊓ M := Subgroup.mem_subgroupOf.mp hy
    have hxM : (x : G) ∈ M := hK'M hxK
    have hconj := Sec3.Sims321.conj_mem_of_mem_normalizer L x y
    have hz : (x : G) * (y : G) * (x : G)⁻¹ ∈ L ⊓ M :=
      ⟨hconj, M.mul_mem (M.mul_mem hxM hy'.2) (M.inv_mem hxM)⟩
    rw [show Sec3.Sims321.barAut L x (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨(x : G) * (y : G) * (x : G)⁻¹, hconj⟩ from
      Sec3.Sims321.barAut_mk L x y]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
  have hTmap : ∀ x : ↥(Subgroup.normalizer (L : Set G)), (x : G) ∈ K' →
      T.map (Sec3.Sims321.barAut L x).toMonoidHom = T := by
    intro x hxK
    have hle : T.map (Sec3.Sims321.barAut L x).toMonoidHom ≤ T := by
      rintro _ ⟨t, ht, rfl⟩
      exact hαT x hxK t ht
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulEquiv.injective _)).symm)
  have hEfix : ∀ x : ↥(Subgroup.normalizer (L : Set G)), (x : G) ∈ K' →
      E.map (Sec3.Sims321.barAut L x).toMonoidHom = E := by
    intro x hxK
    have hnorm : Subgroup.normalizer
        ((E.map (Sec3.Sims321.barAut L x).toMonoidHom : Subgroup _) : Set _) = T := by
      rw [← Subgroup.map_equiv_normalizer_eq E (Sec3.Sims321.barAut L x)]
      exact hTmap x hxK
    have hET : E ≤ T := fun e' he' => Subgroup.le_normalizer he'
    have hE'T : E.map (Sec3.Sims321.barAut L x).toMonoidHom ≤ T := by
      rw [← hnorm]
      exact fun e' he' => Subgroup.le_normalizer he'
    have hEn : ∀ g ∈ T, ∀ e' ∈ E, g * e' * g⁻¹ ∈ E := fun g hg e' he' =>
      (Subgroup.mem_normalizer_iff.mp hg e').mp he'
    have hcardE' : Nat.card (E.map (Sec3.Sims321.barAut L x).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hEcard]
    exact (b8_eq_of_card_nine_normal_in hTc hET hE'T hEn hEcard hcardE').symm
  set H : Subgroup (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    (K'.subgroupOf (Subgroup.normalizer (L : Set G))).map (Sec3.Sims321.barAut L) with hHdef
  have hH_fix : ∀ β ∈ H, E.map β.toMonoidHom = E := by
    intro β hβ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hβ
    exact hEfix x (Subgroup.mem_subgroupOf.mp hx)
  have hsolv : Group.IsSolvable H :=
    kf6 (↥L ⧸ CFSG.pCore 2 ↥L) h.quotient_iso E hEel hEcard H hH_fix
  obtain ⟨hpM, -, -⟩ := (mem_oTwoComponentsIn_iff.mp hK').2
  have hpK : Group.IsPerfect ↥K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'M).toMonoidHom)
      (MulEquiv.surjective _)
  have hK'NL : K' ≤ Subgroup.normalizer (L : Set G) := fun x hx => hNL x (hK'N hx)
  have hpKN : Group.IsPerfect ↥(K'.subgroupOf (Subgroup.normalizer (L : Set G))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'NL).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hHperf : Group.IsPerfect ↥H := by
    rw [hHdef]
    haveI := hpKN
    exact Group.IsPerfect.map (Sec3.Sims321.barAut L)
  have hsub : Subsingleton ↥H := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact (Group.IsPerfect.not_isSolvable ↥H) hsolv
  intro x hxK
  have hmemH : Sec3.Sims321.barAut L x ∈ H :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxK)
  exact congrArg Subtype.val (Subsingleton.elim (⟨_, hmemH⟩ : ↥H) 1)

private theorem b8_comm_mem_of_mem_K' (kf6 : KF6) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) {K' : Subgroup G} (hK' : K' ∈ oTwoComponentsIn M)
    (hK'N : K' ≤ N) :
    ∀ k ∈ K', ∀ y ∈ L, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := by
    rw [hF.normalizer_eq]; exact hK'N hk
  exact b8_forall_mem_of_barAut_eq_one ⟨k, hkN⟩
    (b8_barAut_eq_one_of_mem_K' kf6 h hF hK' hK'N ⟨k, hkN⟩ hk)

end Action

section Main


private theorem b8_conj_mem_pCoreOf {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {r : G} (hr : r ∈ CFSG.Open.pCoreOf 2 L) :
    g * r * g⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hr
  have hσ : L.normalizerMonoidHom ⟨g, hg⟩ z ∈ CFSG.pCore 2 L := by
    have := CFSG.pCore_map_iso 2 (L.normalizerMonoidHom ⟨g, hg⟩)
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hz
  have hval : ((L.normalizerMonoidHom ⟨g, hg⟩ z : L) : G) = g * (z : G) * g⁻¹ := rfl
  change g * (z : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 L
  rw [← hval]
  exact Subgroup.mem_map_of_mem L.subtype hσ

private theorem b8_eq_one_of_central_quotient {L : Subgroup G}
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))
    {y : ↥L ⧸ CFSG.pCore 2 ↥L} (hy : ∀ z : ↥L ⧸ CFSG.pCore 2 ↥L, z * y = y * z) : y = 1 := by
  have hc : e y ∈ Subgroup.center (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨z, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hy z]
  rw [CFSG.RankThree.PartTwo.Sec4.center_projSL_eq_bot, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

private theorem b8_mem_zpowers_of_mul_mem_pCoreOf (kf6 : KF6) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) {K' : Subgroup G} (hK' : K' ∈ oTwoComponentsIn M)
    (hK'N : K' ≤ N) {a k : G} (ha : a ∈ A) (hk : k ∈ K')
    (ho : k⁻¹ * a ∈ CFSG.Open.pCoreOf 2 M) : a ∈ Subgroup.zpowers c := by
  classical
  have hfix := b8_barAut_eq_one_of_mem_K' kf6 h hF hK' hK'N
  obtain ⟨e⟩ := h.quotient_iso
  have hNL : ∀ x ∈ N, x ∈ Subgroup.normalizer (L : Set G) := fun x hx => by
    rw [hF.normalizer_eq]; exact hx
  have hcA : c ∈ A := by rw [hF.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcN : c ∈ N := h.le_N hcA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := b8_comm_of_isElemAbelian h.isE27.1
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => h.isE27.1.2 x hx
  have haS : a ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [← hF.eq_sup]; exact ha
  obtain ⟨g, hg, b, hb, hab⟩ := b8_exists_mul_of_mem_sup_of_comm (H := Subgroup.zpowers c)
    (K := A ⊓ L)
      (fun g hg (b : G) (hb : b ∈ A ⊓ L) =>
        hAc g (Subgroup.zpowers_le.mpr hcA hg) b hb.1)
    haS
  have hbA : b ∈ A := hb.1
  have hbL : b ∈ L := hb.2
  have hgA : g ∈ A := Subgroup.zpowers_le.mpr hcA hg
  have hkN : k ∈ N := hK'N hk
  have haN : a ∈ N := h.le_N ha
  have hgN : g ∈ N := h.le_N hgA
  have hbN : b ∈ N := h.le_N hbA
  have hoN : k⁻¹ * a ∈ N := N.mul_mem (N.inv_mem hkN) haN
  have hcSC : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hF.centralizer_eq]; exact Subgroup.mem_zpowers c
  have hψc : Sec3.Sims321.barAut L ⟨c, hNL c hcN⟩ = 1 :=
    b8_barAut_eq_one_of_forall _ (fun y hy => hcSC.2 y hy)
  have hψg : Sec3.Sims321.barAut L ⟨g, hNL g hgN⟩ = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hx : (⟨g, hNL g hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨c, hNL c hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ i :=
      Subtype.ext (by simp [← hi])
    rw [hx, map_zpow, hψc, one_zpow]
  have hψa : Sec3.Sims321.barAut L ⟨a, hNL a haN⟩ = Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ := by
    have hx : (⟨a, hNL a haN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hNL g hgN⟩ * ⟨b, hNL b hbN⟩ := Subtype.ext (by simp [hab])
    rw [hx, map_mul, hψg, one_mul]
  have hψo : Sec3.Sims321.barAut L ⟨k⁻¹ * a, hNL _ hoN⟩ = Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ := by
    have hx : (⟨k⁻¹ * a, hNL _ hoN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨k, hNL k hkN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨a, hNL a haN⟩ :=
      Subtype.ext (by simp)
    rw [hx, map_mul, map_inv, hfix ⟨k, hNL k hkN⟩ hk, inv_one, one_mul, hψa]
  obtain ⟨m, hm⟩ := b8_exists_pow_two_pow_eq_one ho
  have hpow2 : (⟨k⁻¹ * a, hNL _ hoN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ (2 ^ m) = 1 :=
    Subtype.ext (by simpa using hm)
  have hb2 : Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ ^ (2 ^ m) = 1 := by
    rw [← hψo, ← map_pow, hpow2, map_one]
  have hb3 : Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hNL b hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA3 b hbA)
    rw [this, map_one]
  have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  have hψb : Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ = 1 := by
    have hg1 : Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ ^ Nat.gcd 3 (2 ^ m) = 1 :=
      pow_gcd_eq_one.mpr ⟨hb3, hb2⟩
    rw [hcop, pow_one] at hg1
    exact hg1
  have hcentral : ∀ z : ↥L ⧸ CFSG.pCore 2 ↥L,
      z * QuotientGroup.mk (⟨b, hbL⟩ : L) = QuotientGroup.mk (⟨b, hbL⟩ : L) * z := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      have h1 : Sec3.Sims321.barAut L ⟨b, hNL b hbN⟩ (QuotientGroup.mk y) = QuotientGroup.mk y := by
        rw [hψb, MulAut.one_apply]
      rw [Sec3.Sims321.barAut_mk] at h1
      have h2 : QuotientGroup.mk (⟨b, hbL⟩ : L) * QuotientGroup.mk y *
          (QuotientGroup.mk (⟨b, hbL⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L)⁻¹ = QuotientGroup.mk y := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
  have hb1 : (QuotientGroup.mk (⟨b, hbL⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
    b8_eq_one_of_central_quotient e hcentral
  have hb_pc : b ∈ CFSG.Open.pCoreOf 2 L :=
    (b8_mem_pCore_subtype_iff hbL).mp ((QuotientGroup.eq_one_iff _).mp hb1)
  have hb_one : b = 1 := b8_eq_one_of_pow_three_of_pCoreOf (hA3 b hbA) hb_pc
  rw [hab, hb_one, mul_one]
  exact hg

end Main

theorem item1923_uniqueness
    (kf6 : KF6) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N)
    (h2 : scriptJ M N = {K}) (hcK : c ∈ K) (hAK : A ⊓ K = Subgroup.zpowers c)
    {K' : Subgroup G} (hK' : K' ∈ oTwoComponentsIn M) (h3 : 3 ∣ Nat.card K') : K' = K := by
  classical
  by_contra hne
  have hKK' : K ≠ K' := fun e => hne e.symm
  have hK'M : K' ≤ M := le_of_mem_oTwoComponentsIn hK'
  have hK'N : K' ≤ N := by
    by_contra hnot
    have hmem : K' ∈ scriptJ M N := ⟨hK', hnot⟩
    rw [h2] at hmem
    exact hne (Set.mem_singleton_iff.mp hmem)
  have hKX : K ∈ oTwoComponentsIn M := hK.1
  have hK'NL : K' ≤ Subgroup.normalizer (L : Set G) := by
    rw [hF.normalizer_eq]; exact hK'N
  obtain ⟨hpM, hsn, -⟩ := (mem_oTwoComponentsIn_iff.mp hK').2
  have hcA : c ∈ A := by rw [hF.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcM : c ∈ M := h.le_M hcA
  have hAM : A ≤ M := h.le_M
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := b8_comm_of_isElemAbelian h.isE27.1
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => h.isE27.1.2 x hx
  have hKB : ∀ k ∈ K', ∀ b ∈ A ⊓ L, k * b * k⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    intro k hk b hb
    have hbN : b ∈ Subgroup.normalizer (K' : Set G) :=
      step1923_normalizer_A h hK' hb.1
    have hr1 : k * b * k⁻¹ * b⁻¹ ∈ K' := by
      have := K'.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hbN k⁻¹).mp (K'.inv_mem hk))
      simpa [mul_assoc] using this
    have hr2 : k * b * k⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      b8_comm_mem_of_mem_K' kf6 h hF hK' hK'N k hk b hb.2
    have hR2 : IsPGroup 2 ((K' ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
    exact b8_le_pCoreOf_two_of_subnormal hK'M hsn inf_le_left
      (fun g hg r hr => ⟨K'.mul_mem (K'.mul_mem hg hr.1) (K'.inv_mem hg),
        b8_conj_mem_pCoreOf (hK'NL hg) hr.2⟩) hR2 ⟨hr1, hr2⟩
  have hKc : ∀ k ∈ K', c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun k hk =>
    CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf hKX hK' hKK' hcK hk
  set Ab : Subgroup (M ⧸ CFSG.pCore 2 M) := (A.subgroupOf M).map (b8_piM M) with hAb
  set Xb : Subgroup (M ⧸ CFSG.pCore 2 M) := (K'.subgroupOf M).map (b8_piM M) with hXb
  set cb : M ⧸ CFSG.pCore 2 M := b8_piM M ⟨c, hcM⟩ with hcb
  have hXcb : ∀ x ∈ Xb, x * cb = cb * x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact (b8_mk_commute_of_pCoreOf hcM y.2 (hKc y (Subgroup.mem_subgroupOf.mp hy))).symm
  have hXB : ∀ b (hb : b ∈ A ⊓ L), ∀ x ∈ Xb,
      x * b8_piM M ⟨b, hAM hb.1⟩ = b8_piM M ⟨b, hAM hb.1⟩ * x := by
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact b8_mk_commute_of_pCoreOf y.2 (hAM hb.1) (hKB y (Subgroup.mem_subgroupOf.mp hy) b hb)
  have hXA : ∀ x ∈ Xb, ∀ y ∈ Ab, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have haS : (a : G) ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [← hF.eq_sup]; exact haA
    obtain ⟨g, hg, b, hb, hab⟩ := b8_exists_mul_of_mem_sup_of_comm (H := Subgroup.zpowers c)
      (K := A ⊓ L)
        (fun g hg (b : G) (hb : b ∈ A ⊓ L) =>
          hAc g (Subgroup.zpowers_le.mpr hcA hg) b hb.1)
      haS
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hMeq : a = (⟨c, hcM⟩ : M) ^ i * ⟨b, hAM hb.1⟩ := Subtype.ext (by simp [hab])
    rw [hMeq, map_mul, map_zpow]
    have hc1 : Commute x cb := hXcb x hx
    have hc2 : Commute x (b8_piM M ⟨b, hAM hb.1⟩) := hXB b hb x hx
    exact ((hc1.zpow_right i).mul_right hc2).eq
  have hAb_el : CFSG.Open.IsElemAbelian 3 Ab := by
    refine b8_isElemAbelian_map (b8_piM M) ?_
    refine b8_isElemAbelian_of_comm_pow ?_ ?_
    · intro x hx y hy
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
    · intro x hx
      exact Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hx))
  have hAb_card : Nat.card Ab = 27 := by
    have hA3' : IsPGroup 3 (A.subgroupOf M) :=
      (IsPGroup.of_card (p := 3) (n := 3)
        (by rw [h.isE27.2]; norm_num) : IsPGroup 3 A).comap_subtype
    have h1 := CFSG.RankThree.PartTwo.Sec20.card_eq_card_map_mul_inf_ker (b8_piM M) (A.subgroupOf M)
    rw [QuotientGroup.ker_mk', CFSG.RankThree.PartTwo.Sec20.card_inf_eq_one_of_isPGroup hA3'
      CFSG.pCore_isPGroup, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv,
      h.isE27.2] at h1
    exact h1.symm
  have hAb_X : ∀ y ∈ Ab, y ∈ Xb → y ∈ Subgroup.zpowers cb := by
    intro y hy hyX
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp hyX
    have hrel : (k : M)⁻¹ * a ∈ CFSG.pCore 2 M := QuotientGroup.eq.mp hka
    have hG : ((((k : M)⁻¹ * a : M)) : G) ∈ CFSG.Open.pCoreOf 2 M := Subgroup.mem_map_of_mem _ hrel
    have hG' : (k : G)⁻¹ * (a : G) ∈ CFSG.Open.pCoreOf 2 M := by simpa using hG
    have haZ := b8_mem_zpowers_of_mul_mem_pCoreOf kf6 h hF hK' hK'N
      (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hk) hG'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp haZ
    have hae : a = (⟨c, hcM⟩ : M) ^ i := Subtype.ext (by simp [hi])
    rw [hae, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hbound : ∀ V : Subgroup (M ⧸ CFSG.pCore 2 M), V ≤ Xb → CFSG.Open.IsElemAbelian 3 V →
      V ≤ Subgroup.zpowers cb := by
    intro V hVX hV
    have hVA : CFSG.Open.IsElemAbelian 3 (V ⊔ Ab) :=
      b8_isElemAbelian_sup_of_comm hV hAb_el (fun x hx y hy => hXA x (hVX hx) y hy)
    have hcard : Nat.card ↥(V ⊔ Ab) ≤ 27 := h.card_le_of_isElemAbelian_quotient hVA
    have heq : Ab = V ⊔ Ab :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hAb_card]; exact hcard)
    intro v hv
    have hvAb : v ∈ Ab := by rw [heq]; exact Subgroup.mem_sup_left hv
    exact hAb_X v hvAb (hVX hv)
  have hc3 : c ^ 3 = 1 := by rw [← hF.orderOf_c]; exact pow_orderOf_eq_one c
  have hcb_pow : cb ^ 3 = 1 := by
    rw [hcb, ← map_pow]
    exact congrArg (b8_piM M) (Subtype.ext (by simpa using hc3))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcb_ne : cb ≠ 1 := by
    intro h1
    have hpc : (⟨c, hcM⟩ : M) ∈ CFSG.pCore 2 M := (QuotientGroup.eq_one_iff _).mp h1
    have hc' : c ∈ CFSG.Open.pCoreOf 2 M := (b8_mem_pCore_subtype_iff hcM).mp hpc
    have hc1 : c = 1 := b8_eq_one_of_pow_three_of_pCoreOf hc3 hc'
    have := hF.orderOf_c
    rw [hc1, orderOf_one] at this
    norm_num at this
  have hcb_order : orderOf cb = 3 := orderOf_eq_prime hcb_pow hcb_ne
  have hcb_mem : cb ∈ Xb := by
    obtain ⟨kx, hkx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 h3
    have hkG : (kx : G) ∈ K' := kx.2
    have hkord : orderOf (kx : G) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hkx
    have hkM : (kx : G) ∈ M := hK'M hkG
    have hk3 : (kx : G) ^ 3 = 1 := by rw [← hkord]; exact pow_orderOf_eq_one _
    set rk : M ⧸ CFSG.pCore 2 M := b8_piM M ⟨(kx : G), hkM⟩ with hrk
    have hrkX : rk ∈ Xb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hkG)
    have hrk3 : rk ^ 3 = 1 := by
      rw [hrk, ← map_pow]
      exact congrArg (b8_piM M) (Subtype.ext (by simpa using hk3))
    have hrk1 : rk ≠ 1 := by
      intro h1
      have hpc : (⟨(kx : G), hkM⟩ : M) ∈ CFSG.pCore 2 M := (QuotientGroup.eq_one_iff _).mp h1
      have hkpc : (kx : G) ∈ CFSG.Open.pCoreOf 2 M := (b8_mem_pCore_subtype_iff hkM).mp hpc
      have hk1 : (kx : G) = 1 := b8_eq_one_of_pow_three_of_pCoreOf hk3 hkpc
      rw [hk1, orderOf_one] at hkord
      norm_num at hkord
    have hrkord : orderOf rk = 3 := orderOf_eq_prime hrk3 hrk1
    have hZX : Subgroup.zpowers rk ≤ Xb := Subgroup.zpowers_le.mpr hrkX
    have hZel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers rk) := by
      refine b8_isElemAbelian_of_comm_pow ?_ ?_
      · intro x hx y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow_self rk i j)
      · intro x hx
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hrk3, one_zpow]
    have hZeq : Subgroup.zpowers rk = Subgroup.zpowers cb :=
      Subgroup.eq_of_le_of_card_ge (hbound _ hZX hZel)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hrkord, hcb_order]))
    have hcbZ : cb ∈ Subgroup.zpowers rk := hZeq ▸ Subgroup.mem_zpowers cb
    exact hZX hcbZ
  haveI : Group.IsPerfect ↥(K'.subgroupOf M) := hpM
  have hperfX : Group.IsPerfect ↥Xb := Group.IsPerfect.map (b8_piM M)
  have hcomm_perf : commutator ↥Xb = ⊤ := Group.isPerfect_def.mp hperfX
  have hbΓ : ∀ V : Subgroup ↥Xb, CFSG.Open.IsElemAbelian 3 V → Nat.card V ≤ 3 := by
    intro V hV
    have hVm := b8_isElemAbelian_map Xb.subtype hV
    have hle : V.map Xb.subtype ≤ Subgroup.zpowers cb :=
      hbound _ (Subgroup.map_subtype_le V) hVm
    calc Nat.card ↥V = Nat.card ↥(V.map Xb.subtype) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective Xb)).symm
      _ ≤ Nat.card ↥(Subgroup.zpowers cb) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, hcb_order]
  set g : ↥Xb := ⟨cb, hcb_mem⟩ with hg
  have hgord : orderOf g = 3 := (Subgroup.orderOf_mk cb hcb_mem).trans hcb_order
  have hZc : Subgroup.zpowers g ≤ Subgroup.center ↥Xb := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hXcb y.1 y.2)
  have hZ3 : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgord]; norm_num)
  have hZbot := b8_central_three_eq_bot_of_rank_one hcomm_perf hbΓ (Subgroup.zpowers g) hZc hZ3
  have hgmem : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
  rw [hZbot, Subgroup.mem_bot] at hgmem
  rw [hgmem, orderOf_one] at hgord
  norm_num at hgord

end CFSG.RankThree.PartTwo.Late
