module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate120
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJTag
import CFSG.LocalAnalysis.StandardType.GGStdPosTableBPos
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJFrame
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJSwap
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJBlock
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin CFSG.SeitzReduction.LinearPilot

private theorem jshape_count {G : Type} [Group G] {L Bs J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 2 ≤ k) (φ : M.Group ≃* ggWeylD k)
    (S : Finset M.Group) (hroot : ∀ t ∈ S, ∃ γ, GGDReflRoot k (φ t) γ)
    (hJ : ∀ t ∈ S, ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer J Bs) :
    ∃ T : Finset (Fin k → ℤ), ↑T ⊆ ggDMemberRoots e φ J ∧ 2 * S.card ≤ T.card := by
  classical
  choose! γ hγ using hroot
  have hinj : ∀ t ∈ S, ∀ t' ∈ S, (γ t' = γ t ∨ γ t' = -γ t) → t = t' := fun t ht t' ht' h =>
    φ.injective ((hγ t ht).unique hk (hγ t' ht') h)
  have hne : ∀ t ∈ S, γ t ≠ -γ t := fun t ht h => by
    have h2 := ggDDot_self_of_mem ((hγ t ht).mem (by omega))
    have h0 : γ t = 0 := funext fun y => by
      have h1 := congrFun h y
      rw [Pi.neg_apply] at h1
      rw [Pi.zero_apply]
      omega
    simp [h0, ggDDot_eq_dotProduct] at h2
  have hi1 : Set.InjOn γ S := fun t ht t' ht' h => hinj t ht t' ht' (Or.inl h.symm)
  have hi2 : Set.InjOn (fun t => -γ t) S := fun t ht t' ht' h =>
    hinj t ht t' ht' (Or.inl (neg_injective h).symm)
  have hd : Disjoint (S.image γ) (S.image fun t => -γ t) := by
    refine Finset.disjoint_left.mpr fun v hv hv' => ?_
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨t', ht', h⟩ := Finset.mem_image.mp hv'
    have htt := hinj t ht t' ht' (Or.inr (by rw [← h, neg_neg]))
    rw [← htt] at h
    exact hne t ht h.symm
  refine ⟨S.image γ ∪ S.image fun t => -γ t, fun v hv => ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with h | h <;>
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    · exact ⟨t, hγ t ht, hJ t ht⟩
    · exact ⟨t, (hγ t ht).neg, hJ t ht⟩
  · rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hi1,
      Finset.card_image_of_injOn hi2, two_mul]

theorem ggDk_jShape
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hB : Bs = B) (hss : GGDNoSameSupp e φ) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hloc : GGKGPosLocalHyp p Bs L t n f ψ)
    (hstd : GGKGPosStdPos (ggU t n f).D ψ Bs) :
    p ∣ Nat.card J ∧ ∃ T : Finset (Fin k → ℤ), ↑T ⊆ ggDMemberRoots e φ J ∧
      (k - 1) * (k - 2) ≤ T.card := by
  classical
  have hTB := ggKGPos_tableBPos_of_stdPos G p Bs L t n f ψ hloc hstd
  obtain ⟨rfl, rfl, hcard⟩ := ggDk_tablePos_tag hKG hcfg hsplit hpres hle3 hk hM φ hφ hss
    hloc.1.2.2.1 hloc.2.1.2.2.1 hTB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨⟨hp, -, hadm, -⟩, ⟨hker, hX, -, hpf⟩, ⟨hBs, -, hC3⟩, -, -⟩ := hloc
  obtain ⟨-, hxB, hx1, hLx, hcyc⟩ := hcfg.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, -, hDcard, hxD, -, hJ, hDJ⟩ := hcfg.1.1.2.2.1
  rw [← hB] at hDJ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (GaloisField 2 f)ˣ, IsPrimitiveRoot ζ p := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : p ∣ Nat.card (GaloisField 2 f)ˣ := by
      rw [Nat.card_units, GaloisField.card 2 f (by have := hadm.2.1; omega)]
      exact hpf
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨y, by simpa [hy] using IsPrimitiveRoot.orderOf y⟩
  have hE : IsElemAbelian p (Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) :=
    TableB.isElemAbelian_mono hBs inf_le_left
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ p :=
    TableB.card_le_of_isCyclic hp.pos (hcyc _ (by rw [← hX]; exact inf_le_right)
      (TableB.isPGroup_of_isElemAbelian hE)) hE.2
  obtain ⟨δ, hδ, hδp, hδC, hfull⟩ :=
    ggDk_exists_diagFrame (F := GaloisField 2 f) hm hker hp hBs hstd hcard hC
  let xb : ↥Bs := ⟨x, hcfg.1.1.2.1.1 hxB⟩
  have hxC : (xb : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hX]
    exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx.1 hl) x (Set.mem_singleton x)).symm
  rw [← hX] at hJ
  obtain ⟨I, hI, hIc⟩ := ggDk_comp_eq_block (F := GaloisField 2 f) (x := xb) hker hp hδ hfull hζ
    hDJ hDcard hxD (fun h => hx1 (congrArg Subtype.val h)) (hδC xb hxC) hJ
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp (show 1 < I.card by omega)
  have hJL : J ≤ L := by
    rw [← hX]
    exact hJ.1.trans inf_le_left
  have hrefl : ∀ a ∈ I, ∀ c ∈ I, a ≠ c → ∃ u : M.Group, (∃ γ, GGDReflRoot (m + 1) (φ u) γ) ∧
      ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer J Bs ∧
      ∀ b : ↥Bs, ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b ↔ δ b a = δ b c := by
    intro a ha c hc hac
    obtain ⟨hN, hr, hfix⟩ :=
      ggDk_swap_refl (F := GaloisField 2 f) hm hker hp hC3 hδ hδp hfull hζ hac
    have hrJ : ggConjAut Bs hN ∈ ggAutomizer J Bs := ggConjAut_mem_ggAutomizer (by
      rw [hI]
      exact Subgroup.mem_map_of_mem ψ (ggPermSL_swap_mem_blockSpecialLinear ha hc)) hN
    obtain ⟨w, i, hwi⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (ggAutomizer_mono Bs hJL hrJ)) hr
    refine ⟨w * M.simple i * w⁻¹, exists_ggDReflRoot_of_conj φ hφ w i, ?_, ?_⟩
    · rw [← hwi]
      exact hrJ
    · rw [← hwi]
      exact hfix
  choose! u hu hJu hfu using hrefl
  obtain ⟨T, hT, hTc⟩ := jshape_count (J := J) (by omega : 2 ≤ m + 1) φ
    (I.offDiag.image fun q => u q.1 q.2)
    (fun v hv => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hq
      exact hu _ h1 _ h2 h3)
    (fun v hv => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hq
      exact hJu _ h1 _ h2 h3)
  have hpJ : p ∣ Nat.card J := by
    rw [hI]
    exact ggDk_prime_dvd_card_block (F := GaloisField 2 f) hm hker hp hζ ha hc hac
  refine ⟨hpJ, T, hT, ?_⟩
  have hfib : I.offDiag.card ≤ 2 * (I.offDiag.image fun q => u q.1 q.2).card := by
    refine Finset.card_le_mul_card_image _ 2 fun v hv => ?_
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ha₀, hc₀, hac₀⟩ := Finset.mem_offDiag.mp hq₀
    refine (Finset.card_le_card (t := {q₀, q₀.swap}) fun q hq => ?_).trans Finset.card_le_two
    obtain ⟨hq, hqv⟩ := Finset.mem_filter.mp hq
    obtain ⟨ha', hc', hac'⟩ := Finset.mem_offDiag.mp hq
    rcases ggDk_pair_eq_of_fix_iff hp hfull hζ hac₀ (a' := q.1) (c' := q.2) fun b => by
        rw [← hfu _ ha₀ _ hc₀ hac₀, ← hfu _ ha' _ hc' hac', hqv] with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Prod.ext_iff, h1, h2]
    · simp [Prod.ext_iff, h1, h2]
  have hoff : (m + 1 - 1) * (m + 1 - 2) ≤ I.offDiag.card := by
    rw [Finset.offDiag_card, ← Nat.mul_sub_one]
    exact Nat.mul_le_mul (by omega) (by omega)
  exact hoff.trans (hfib.trans hTc)

end CFSG.StandardType

end
