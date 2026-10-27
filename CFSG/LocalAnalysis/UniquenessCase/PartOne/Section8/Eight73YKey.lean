module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.RankThree.PartTwo.Sec16.Kcd166.IOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.GroupTheory.QuasisimplePSolvable
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_of_forall_commutator_mem {L : Subgroup G} {x : G}
    (h : ∀ y ∈ L, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hOle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hmaple : L.map (MulAut.conj x).toMonoidHom ≤ L := by
    rintro z ⟨y, hy, rfl⟩
    change x * y * x⁻¹ ∈ L
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [hxy]
    exact L.mul_mem (hOle (h y hy)) hy
  have hmap : L.map (MulAut.conj x).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hmaple (by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem commutatorElement_mem_pCoreOf_of_commute {P L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) {c u v : G}
    (hc : c ∈ normalizer (L : Set G)) (hu : u ∈ L) (hup : ∃ k : ℕ, u ^ p ^ k = 1)
    (hv : v ∈ centralizerBar P L) (hcomm : c * (u * v) = u * v * c) :
    ⁅c, u⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  let Cstar : Subgroup G := centralizerBar (normalizer (L : Set G)) L
  have hCstar_normal : (Cstar.subgroupOf (normalizer (L : Set G))).Normal :=
    centralizerBar_normal (P := normalizer (L : Set G)) (L := L) le_rfl
  have hCstar_le : Cstar ≤ normalizer (L : Set G) := centralizerBar_le _ _
  have hNnorm : normalizer (L : Set G) ≤ Subgroup.normalizer (Cstar : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCstar_le).mp hCstar_normal
  have hvC : v ∈ Cstar := by
    refine mem_centralizerBar_iff.mpr ⟨?_, ?_⟩
    · exact mem_normalizer_of_forall_commutator_mem
        (fun y hy => (mem_centralizerBar_iff.mp hv).2 y hy)
    · exact fun y hy => (mem_centralizerBar_iff.mp hv).2 y hy
  have hCv : c * v⁻¹ * c⁻¹ ∈ Cstar :=
    (Subgroup.mem_normalizer_iff.mp (hNnorm hc) v⁻¹).1 (Cstar.inv_mem hvC)
  have hprod : v * (c * v⁻¹ * c⁻¹) ∈ Cstar := Cstar.mul_mem hvC hCv
  have huN : u ∈ Subgroup.normalizer (Cstar : Set G) := hNnorm (Subgroup.le_normalizer hu)
  have hwC : u * (v * (c * v⁻¹ * c⁻¹)) * u⁻¹ ∈ Cstar :=
    (Subgroup.mem_normalizer_iff.mp huN (v * (c * v⁻¹ * c⁻¹))).1 hprod
  have hcu : c * u * c⁻¹ = u * v * c * v⁻¹ * c⁻¹ := by
    have h := congrArg (fun t => t * v⁻¹ * c⁻¹) hcomm
    have hL : c * (u * v) * v⁻¹ * c⁻¹ = c * u * c⁻¹ := by group
    rw [hL] at h
    exact h
  have hw_eq : ⁅c, u⁆ = u * (v * (c * v⁻¹ * c⁻¹)) * u⁻¹ := by
    rw [commutatorElement_def, hcu]
    group
  have hwC' : ⁅c, u⁆ ∈ Cstar := by
    rw [hw_eq]
    exact hwC
  have hcuL : c * u * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hc u).1 hu
  have hwL : ⁅c, u⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem hcuL (L.inv_mem hu)
  let wL : ↥L := ⟨⁅c, u⁆, hwL⟩
  have hwbar_center : (QuotientGroup.mk wL : Bar2 L) ∈ center (Bar2 L) := by
    refine CFSG.SectionRank.Ccomm.mk_mem_center_iff.mpr fun y => ?_
    have hmem : ⁅(wL : G), (y : G)⁆ ∈ CFSG.Open.pCoreOf 2 L :=
      (mem_centralizerBar_iff.mp hwC').2 (y : G) y.2
    exact (CFSG.mem_openPCoreOf_iff (⁅wL, y⁆)).mp (by
      simpa [commutatorElement_def] using hmem)
  obtain ⟨k, hk⟩ := hup
  let uL : ↥L := ⟨u, hu⟩
  let cuL : ↥L := ⟨c * u * c⁻¹, hcuL⟩
  have hcu_eq : cuL = wL * uL := by
    apply Subtype.ext
    change c * u * c⁻¹ = ⁅c, u⁆ * u
    rw [commutatorElement_def]
    group
  have hcu_pow : cuL ^ p ^ k = 1 := by
    apply Subtype.ext
    change (c * u * c⁻¹) ^ p ^ k = (1 : G)
    have hconj : (c * u * c⁻¹) ^ p ^ k = c * u ^ p ^ k * c⁻¹ := by
      have h : c * u * c⁻¹ = (MulAut.conj c) u := by simp [MulAut.conj_apply]
      rw [h, ← map_pow]
      simp [MulAut.conj_apply]
    rw [hconj, hk, mul_one, mul_inv_cancel]
  have hu_pow : uL ^ p ^ k = 1 := by
    apply Subtype.ext
    exact hk
  have hcu_bar_pow : (QuotientGroup.mk cuL : Bar2 L) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hcu_pow]
    rfl
  have hu_bar_pow : (QuotientGroup.mk uL : Bar2 L) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hu_pow]
    rfl
  have hcu_bar_eq : (QuotientGroup.mk cuL : Bar2 L) =
      (QuotientGroup.mk wL : Bar2 L) * (QuotientGroup.mk uL : Bar2 L) := by
    rw [hcu_eq]
    rfl
  have hcommw : Commute (QuotientGroup.mk wL : Bar2 L) (QuotientGroup.mk uL : Bar2 L) :=
    (Subgroup.mem_center_iff.mp hwbar_center (QuotientGroup.mk uL : Bar2 L)).symm
  have hwbar_pow : (QuotientGroup.mk wL : Bar2 L) ^ p ^ k = 1 := by
    have h := hcu_bar_pow
    rw [hcu_bar_eq, hcommw.mul_pow, hu_bar_pow, mul_one] at h
    exact h
  have horder : orderOf (QuotientGroup.mk wL : Bar2 L) = 1 :=
    Nat.eq_one_of_dvd_coprimes (((hp.coprime_iff_not_dvd).2 hZ).pow_left k)
      (orderOf_dvd_of_pow_eq_one hwbar_pow)
      (Subgroup.orderOf_dvd_natCard _ hwbar_center)
  have hwN : wL ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff wL).mp (orderOf_eq_one_iff.mp horder)
  exact (CFSG.mem_openPCoreOf_iff wL).mpr hwN

theorem false_of_isPSolvable_inf_centralizer {P L Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLq : CFSG.Open.IsQuasisimple (Bar2 L)) (hpL : p ∣ Nat.card L)
    (hYp : IsPGroup p Y) (hY : Y ≤ centralizerBar P L)
    (hK : CFSG.HallHigman.IsPSolvable p ↥(L ⊓ centralizer (Y : Set G))) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := by
    intro y hy
    exact mem_normalizer_of_forall_commutator_mem
      (fun z hz => (mem_centralizerBar_iff.mp (hY hy)).2 z hz)
  have hO2p : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L
  have hpO2 : ¬ p ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    obtain ⟨n, hn⟩ := hO2p.exists_card_eq
    intro h
    rw [hn] at h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hcop : L = (L ⊓ Subgroup.centralizer (Y : Set G)) ⊔ CFSG.Open.pCoreOf 2 L :=
    CFSG.RankThree.PartTwo.Sec16.Kcd166.eq_inf_centralizer_sup_of_isPGroup
      (p := p) (P := Y) (H := L) (N := CFSG.Open.pCoreOf 2 L) hYp hpO2
      (CFSG.openPCoreOf_le 2 L) hYN
      (fun x hx y hy => by
        have h := (mem_centralizerBar_iff.mp (hY hx)).2 y hy
        simpa [commutatorElement_def] using h)
  let K : Subgroup G := L ⊓ Subgroup.centralizer (Y : Set G)
  let N : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' N
  have hKle : K ≤ L := inf_le_left
  have hKsupN : (K.subgroupOf L) ⊔ N = ⊤ := by
    have h1 : (K.subgroupOf L) ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKle (CFSG.openPCoreOf_le 2 L)]
      rw [hcop.symm]
      exact Subgroup.subgroupOf_self L
    rwa [CFSG.openPCoreOf_subgroupOf 2 L] at h1
  have hNmap : N.map π = ⊥ := by
    refine (Subgroup.map_eq_bot_iff N).mpr ?_
    intro x hx
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hmapK : (K.subgroupOf L).map π = ⊤ := by
    calc (K.subgroupOf L).map π
        = (K.subgroupOf L).map π ⊔ N.map π := by rw [hNmap, sup_bot_eq]
      _ = ((K.subgroupOf L) ⊔ N).map π := by rw [Subgroup.map_sup]
      _ = ⊤ := by
            rw [hKsupN, Subgroup.map_top,
              MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
  let f : ↥K →* Bar2 L := π.comp (Subgroup.inclusion hKle)
  have hf_range : f.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hmapK
  have hKtop : CFSG.HallHigman.IsPSolvable p ↥(⊤ : Subgroup ↥K) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm (show CFSG.HallHigman.IsPSolvable p ↥K from hK)
  have hBarPS : CFSG.HallHigman.IsPSolvable p (Bar2 L) := by
    have hmap := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (p := p) f (N := ⊤) hKtop
    rw [Subgroup.map_top, hf_range] at hmap
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv hmap
  have hO2card : Nat.card (CFSG.Open.pCoreOf 2 L) = Nat.card N := by
    show Nat.card (CFSG.Open.pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L)
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.card_map_of_injective L.subtype_injective
  have hcardL : Nat.card L = Nat.card (Bar2 L) * Nat.card (CFSG.Open.pCoreOf 2 L) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [← hO2card] at h
    exact h
  have hpBar : p ∣ Nat.card (Bar2 L) := by
    have h := hpL
    rw [hcardL] at h
    rcases hp.dvd_mul.mp h with h | h
    · exact h
    · exact absurd h hpO2
  exact CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.not_isPSolvable_of_isQuasisimple
    hLq hpBar hBarPS

theorem normalizer_le_of_forall_maximal {M P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M)
    (h : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ P → ¬ normalizer (Y : Set G) ≤ M →
      (∀ Z : Subgroup G, Y < Z → Z ≤ M → IsPGroup p Z → normalizer (Z : Set G) ≤ M) → False)
    {Y : Subgroup G} (hYM : Y ≤ M) (hYp : IsPGroup p Y) (hY : Y ≠ ⊥) :
    normalizer (Y : Set G) ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hYN
  let S : Set (Subgroup G) :=
    {Z | Z ≠ ⊥ ∧ Z ≤ M ∧ IsPGroup p Z ∧ ¬ normalizer (Z : Set G) ≤ M}
  have hSne : S.Nonempty := ⟨Y, hY, hYM, hYp, hYN⟩
  obtain ⟨Y₀, hY₀S, hY₀max⟩ :=
    Set.exists_max_image S (fun Z => Nat.card Z) (Set.toFinite S) hSne
  obtain ⟨hY₀ne, hY₀M, hY₀p, hY₀N⟩ := hY₀S
  have hY₀sub : IsPGroup p (Y₀.subgroupOf M) := hY₀p.comap_subtype (K := M)
  obtain ⟨Q, hY₀Q⟩ := hY₀sub.exists_le_sylow
  let P₀ : Subgroup G := (Q : Subgroup M).map M.subtype
  have hP₀ : CFSG.ABGLocalTools.IsSylowOf p P₀ M := ⟨Q, rfl⟩
  have hY₀P₀ : Y₀ ≤ P₀ := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hY₀M hy⟩, hY₀Q (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  obtain ⟨k, hkM, hconj⟩ := hP.exists_mem_conj hP₀
  let Y₁ : Subgroup G := Y₀.map (MulAut.conj k⁻¹).toMonoidHom
  have hY₁P : Y₁ ≤ P := by
    rintro y ⟨z, hz, rfl⟩
    have hzP : z ∈ P₀ := hY₀P₀ hz
    have hz' : k⁻¹ * z * k ∈ P := (hconj z).mp hzP
    simpa [MulAut.conj_apply] using hz'
  have hY₁ne : Y₁ ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom :=
      (MulAut.conj k⁻¹).injective
    exact hY₀ne ((Subgroup.map_eq_bot_iff_of_injective Y₀ hinj).mp hbot)
  have hNY₁ : normalizer (Y₁ : Set G) =
      (normalizer (Y₀ : Set G)).map (MulAut.conj k⁻¹).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq Y₀ (MulAut.conj k⁻¹)).symm
  have hY₁N : ¬ normalizer (Y₁ : Set G) ≤ M := by
    intro hle
    apply hY₀N
    intro x hx
    have hconjx : k⁻¹ * x * k ∈ normalizer (Y₁ : Set G) := by
      rw [hNY₁]
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hmem : k⁻¹ * x * k ∈ M := hle hconjx
    have hxeq : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [hxeq]
    exact M.mul_mem (M.mul_mem hkM hmem) (M.inv_mem hkM)
  have hY₁max : ∀ Z : Subgroup G, Y₁ < Z → Z ≤ M → IsPGroup p Z →
      normalizer (Z : Set G) ≤ M := by
    intro Z hlt hZM hZp
    by_contra hZN
    have hZne : Z ≠ ⊥ := by
      intro hZbot
      rw [hZbot] at hlt
      exact (not_lt_of_ge bot_le) hlt
    have hZS : Z ∈ S := ⟨hZne, hZM, hZp, hZN⟩
    have hcardY₁ : Nat.card Y₁ = Nat.card Y₀ := by
      change Nat.card (Y₀.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card Y₀
      exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    have hltcard : Nat.card Y₁ < Nat.card Z := Subgroup.card_lt_of_lt hlt
    have hlecard : Nat.card Z ≤ Nat.card Y₀ := hY₀max Z hZS
    omega
  exact h Y₁ hY₁ne hY₁P hY₁N hY₁max

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
