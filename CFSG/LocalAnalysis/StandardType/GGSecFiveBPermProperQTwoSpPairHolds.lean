module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpLeafDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoSpSmallBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameOn
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniModelTwoCenter
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoSpPairLift
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFourCharts
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LieType.Universal.Symplectic
import CFSG.Assembly.Subnormal
import CFSG.ClassicalInvolution.WeakCT.SpSpThreeConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.SeitzReduction.SymplecticPilot (spBlock)
open CFSG.ClassicalInvolution.WeakCT (weakCT_symplectic_two_of_three_conj_rotate)

private theorem ne_Bs_of_root {G : Type} [Group G] {p n : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {a a' : Fin n} (haa' : a ≠ a')
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) : B ≠ Bs := by
  intro hBB
  have hmem : ((eta.symm (Pi.mulSingle a (Multiplicative.ofAdd 1)) : ↥Bs) : G) ∈ B := by
    rw [hBB]
    exact (eta.symm (Pi.mulSingle a (Multiplicative.ofAdd 1))).2
  have h := (hroot _).mp hmem
  rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne haa'.symm] at h
  exact one_ne_zero (ofAdd_eq_one.mp h)

private theorem isComponentOf_of_largeEvenPComponent {G : Type} [Group G] {p : ℕ}
    {C K : Subgroup G} {s : ℕ} (hs : 1 ≤ s) (hKp : LargeEvenPComponent p C K)
    (eK : ↥K ≃* StatedSp (s + 2) (GaloisField 2 1)) :
    CFSG.Open.IsComponentOf K C := by
  have hSq : CFSG.Open.IsQuasisimple (StatedSp (s + 2) (GaloisField 2 1)) := by
    have hadm : StatedLieAdmissible .PSp (s + 2) 2 1 := ⟨Nat.prime_two, le_rfl, by omega, by
      intro h
      rw [Prod.mk.injEq] at h
      exact absurd h.1 (by omega)⟩
    have hq := Symplectic.isQuasisimple_of_admissible (s + 2) (GaloisField 2 1) hadm
      (GaloisField.card 2 1 (by omega))
    have := hq.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  exact ⟨hKp.1, isSubnormal_iff_open.mp hKp.2.1, CFSG.Open.IsQuasisimple.of_mulEquiv eK hSq⟩

private theorem exists_perm_last_two {s : ℕ} {a a' : Fin (s + 4)} (haa' : a ≠ a') :
    ∃ e : Equiv.Perm (Fin (s + 4)),
      ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map e.toEmbedding =
        {a, a'} ∧
      ∀ j, j ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ ↔
        ∃ k : Fin (s + 2), e (Fin.castLE (by omega) k) = j := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq
    ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))) {a, a'}
    (by rw [Finset.card_pair (by simp [Fin.ext_iff]), Finset.card_pair haa'])
  refine ⟨e, he, ?_⟩
  intro j
  have hiff : j ∈ ({a, a'} : Finset (Fin (s + 4))) ↔
      j ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
        Finset (Fin (s + 4))).map e.toEmbedding := by
    rw [he]
  rw [Finset.mem_compl, not_congr hiff, Finset.mem_map_equiv]
  constructor
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff] at hj
    have hjlt : (e.symm j).val < s + 2 := by
      have := (e.symm j).isLt
      omega
    refine ⟨Fin.castLT (e.symm j) hjlt, ?_⟩
    change e (Fin.castLE (by omega) (Fin.castLT (e.symm j) hjlt)) = j
    rw [show Fin.castLE (by omega) (Fin.castLT (e.symm j) hjlt) = e.symm j from
      Fin.ext rfl, Equiv.apply_symm_apply]
  · rintro ⟨k, hk⟩
    rw [← hk, Equiv.symm_apply_apply]
    have hklt : (Fin.castLE (by omega : s + 2 ≤ s + 4) k).val < s + 2 := by
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff]
    constructor <;> omega

private theorem qTwoSmallBlock_map_conj_image {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {e τ : Equiv.Perm (Fin n)} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (e * τ * e⁻¹))
    (S T : Set (Fin n)) :
    (ggQTwoSmallBlock Bs eta (e '' S) (e '' T)).map (MulAut.conj g).toMonoidHom =
      ggQTwoSmallBlock Bs eta (e '' (τ '' S)) (e '' (τ '' T)) := by
  have himg : ∀ A : Set (Fin n), (e * τ * e⁻¹) '' (e '' A) = e '' (τ '' A) := by
    intro A
    rw [Set.image_image, Set.image_image]
    congr 1
    ext x
    simp [Equiv.Perm.coe_mul]
  rw [ggQTwoSmallBlock_map_conj hg hτ, himg, himg]

private theorem exists_conjAut_swap_permAut {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {h k : G} (hh : h ∈ Subgroup.normalizer (Bs : Set G))
    (hk : k ∈ Subgroup.normalizer (Bs : Set G))
    {σ : Equiv.Perm (Fin n)}
    (hσ : MulAut.congr eta (ggConjAut Bs hh) = SpCoord.permAut σ)
    {c d : Fin n}
    (hkτ : MulAut.congr eta (ggConjAut Bs hk) =
      SpCoord.permAut (Equiv.swap c d)) :
    ∃ hg : h * k * h⁻¹ ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) =
        SpCoord.permAut (Equiv.swap (σ c) (σ d)) := by
  have hhk : h * k ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hh hk
  have hki : h⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hh
  have hg : h * k * h⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hhk hki
  have hginv : ggConjAut Bs hki = (ggConjAut Bs hh)⁻¹ := by
    ext b
    have hinv_b := inv_apply_of_forall (φ := ggConjAut Bs hh) (h := h)
      (fun b => ggConjAut_apply Bs hh b) b
    rw [ggConjAut_apply, hinv_b]
    simp [inv_inv]
  have hσinv : (SpCoord.permAut (p := p) σ)⁻¹ = SpCoord.permAut σ⁻¹ := by
    have h1 : SpCoord.permAut (p := p) σ * SpCoord.permAut σ⁻¹ = 1 := by
      rw [← SpCoord.permAut_mul', mul_inv_cancel, SpCoord.permAut_one']
    exact eq_inv_of_mul_eq_one_right h1
  refine ⟨hg, ?_⟩
  rw [ggConjAut_mul hhk hki, ggConjAut_mul hh hk, map_mul, map_mul, hσ, hkτ,
    hginv, map_inv, hσ, hσinv, ← SpCoord.permAut_mul', ← SpCoord.permAut_mul']
  congr 1
  exact (Equiv.swap_apply_apply σ c d).symm

private theorem chart_block_comm {G : Type} [Group G] [Finite G] {p s : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {e : Equiv.Perm (Fin (s + 4))} {ι : Fin (s + 2) → Fin (s + 4)}
    {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    (hp2 : p ≠ 2) (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hιe : ∀ k, ι k = e (Fin.castLE (by omega) k))
    (N : Finset (Fin (s + 2))) (hN : 3 ≤ N.card) (hNu : N ≠ Finset.univ) :
    ggBlockComm Bs eta (e '' (Fin.castLE (by omega : s + 2 ≤ s + 4) ''
      (N : Set (Fin (s + 2))))) =
      (spBlock (GaloisField 2 1) N).map κ := by
  have himage : e '' (Fin.castLE (by omega : s + 2 ≤ s + 4) ''
      (N : Set (Fin (s + 2)))) =
      ι '' (N : Set (Fin (s + 2))) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact (hιe x).symm
  rw [himage]
  exact hκ.ggBlockComm_image_eq_map_spBlock_of_or hp2 hBsC hyBs hKc (Or.inr hN)
    (Finset.card_pos.mp (by omega)) hNu

private theorem chart_block_small {G : Type} [Group G] [Finite G] {p s : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {e : Equiv.Perm (Fin (s + 4))} {ι : Fin (s + 2) → Fin (s + 4)}
    {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    (hp2 : p ≠ 2) (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hιe : ∀ k, ι k = e (Fin.castLE (by omega) k))
    (N I : Finset (Fin (s + 2))) (hN : 3 ≤ N.card) (hNu : N ≠ Finset.univ)
    (hIN : I ⊆ N) (hI2 : I.card ≤ 2) :
    ggQTwoSmallBlock Bs eta (e '' (Fin.castLE (by omega : s + 2 ≤ s + 4) ''
        (I : Set (Fin (s + 2)))))
        (e '' (Fin.castLE (by omega : s + 2 ≤ s + 4) '' (N : Set (Fin (s + 2))))) =
      (spBlock (GaloisField 2 1) I).map κ := by
  have himage : ∀ M : Finset (Fin (s + 2)),
      e '' (Fin.castLE (by omega : s + 2 ≤ s + 4) '' (M : Set (Fin (s + 2)))) =
        ι '' (M : Set (Fin (s + 2))) := by
    intro M
    rw [Set.image_image]
    congr 1
    funext x
    exact (hιe x).symm
  rw [himage, himage]
  exact hκ.ggQTwoSmallBlock_eq_map_spBlock_of_three_le hp2 hBsC hyBs hKc hN hNu hIN hI2

private theorem finRotate_finRotate_last_two (s : ℕ) :
    finRotate (s + 4) (finRotate (s + 4) (⟨s + 2, by omega⟩ : Fin (s + 4))) = 0 ∧
      finRotate (s + 4) (finRotate (s + 4) (⟨s + 3, by omega⟩ : Fin (s + 4))) = 1 := by
  have h1 : finRotate (s + 4) (⟨s + 2, by omega⟩ : Fin (s + 4)) = ⟨s + 3, by omega⟩ := by
    apply Fin.ext
    rw [finRotate_apply, Fin.val_add]
    have hone : ((1 : Fin (s + 4)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone]
    have hlt : s + 2 + 1 < s + 4 := by omega
    rw [Nat.mod_eq_of_lt hlt]
  have h2' : (⟨s + 3, by omega⟩ : Fin (s + 4)) + 1 = 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_zero]
    have hone : ((1 : Fin (s + 4)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_self]
  have h2 : finRotate (s + 4) (⟨s + 3, by omega⟩ : Fin (s + 4)) = 0 := by
    rw [finRotate_apply]
    exact h2'
  have h0 : finRotate (s + 4) (0 : Fin (s + 4)) = 1 := by
    simp
  constructor
  · rw [h1, h2]
  · rw [h2, h0]

private theorem rot_double_apply {s : ℕ} {e ρ : Equiv.Perm (Fin (s + 4))}
    (hρ : ρ = e * finRotate (s + 4) * e⁻¹) (x : Fin (s + 4)) :
    e.symm ((ρ * ρ) x) =
      finRotate (s + 4) (finRotate (s + 4) (e.symm x)) := by
  have hx : (ρ * ρ) x =
      e (finRotate (s + 4) (finRotate (s + 4) (e.symm x))) := by
    simp [hρ, Equiv.Perm.coe_mul]
  rw [hx, Equiv.symm_apply_apply]

private theorem rot_double_last_two_notMem {s : ℕ} {y : Fin (s + 4)}
    (hy : y ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4)))) :
    finRotate (s + 4) (finRotate (s + 4) y) ∉
      ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))) := by
  obtain ⟨hrot2, hrot3⟩ := finRotate_finRotate_last_two s
  rcases Finset.mem_insert.mp hy with rfl | hy
  · rw [hrot2]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, not_or]
    omega
  · rw [Finset.mem_singleton.mp hy, hrot3]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_one, not_or]
    omega

private theorem rot_pow_two_notMem {s : ℕ} {a a' : Fin (s + 4)}
    {e ρ : Equiv.Perm (Fin (s + 4))}
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'})
    (hρ : ρ = e * finRotate (s + 4) * e⁻¹) :
    (ρ * ρ) a ∉ ({a, a'} : Finset (Fin (s + 4))) ∧
      (ρ * ρ) a' ∉ ({a, a'} : Finset (Fin (s + 4))) := by
  have hea : e.symm a ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
      Finset (Fin (s + 4))) := by
    rw [← Finset.mem_map_equiv, he]
    simp
  have hea' : e.symm a' ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
      Finset (Fin (s + 4))) := by
    rw [← Finset.mem_map_equiv, he]
    simp
  constructor
  · intro hmem
    rw [← he] at hmem
    rw [Finset.mem_map_equiv, rot_double_apply hρ] at hmem
    exact rot_double_last_two_notMem hea hmem
  · intro hmem
    rw [← he] at hmem
    rw [Finset.mem_map_equiv, rot_double_apply hρ] at hmem
    exact rot_double_last_two_notMem hea' hmem

private theorem rot_compl_union {s : ℕ} {a a' : Fin (s + 4)}
    {e ρ : Equiv.Perm (Fin (s + 4))}
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'})
    (hρ : ρ = e * finRotate (s + 4) * e⁻¹) :
    ({a, a'} : Finset (Fin (s + 4)))ᶜ ∪
        ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ = Finset.univ := by
  obtain ⟨ha_not, ha'_not⟩ := rot_pow_two_notMem he hρ
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  by_cases hx : x ∈ ({a, a'} : Finset (Fin (s + 4)))
  · refine Finset.mem_union.mpr (Or.inr (Finset.mem_compl.mpr ?_))
    intro hxt
    rw [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with h | h
    · rw [h] at hx
      exact ha_not hx
    · rw [h] at hx
      exact ha'_not hx
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_compl.mpr hx))

private theorem rot_symm_pow_two_eq_zero_one {s : ℕ} {a a' : Fin (s + 4)}
    {e ρ : Equiv.Perm (Fin (s + 4))}
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'})
    (hρ : ρ = e * finRotate (s + 4) * e⁻¹) :
    (e.symm ((ρ * ρ) a) = 0 ∨ e.symm ((ρ * ρ) a) = 1) ∧
      (e.symm ((ρ * ρ) a') = 0 ∨ e.symm ((ρ * ρ) a') = 1) := by
  obtain ⟨hrot2, hrot3⟩ := finRotate_finRotate_last_two s
  have hea : e.symm a ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
      Finset (Fin (s + 4))) := by
    rw [← Finset.mem_map_equiv, he]
    simp
  have hea' : e.symm a' ∈ ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
      Finset (Fin (s + 4))) := by
    rw [← Finset.mem_map_equiv, he]
    simp
  constructor
  · rw [rot_double_apply hρ]
    rcases Finset.mem_insert.mp hea with h | h
    · left
      rw [h, hrot2]
    · right
      rw [Finset.mem_singleton.mp h, hrot3]
  · rw [rot_double_apply hρ]
    rcases Finset.mem_insert.mp hea' with h | h
    · left
      rw [h, hrot2]
    · right
      rw [Finset.mem_singleton.mp h, hrot3]

private theorem two_notMem_last_two (s : ℕ) (hs : 1 ≤ s) :
    (⟨2, by omega⟩ : Fin (s + 4)) ∉
      ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

private theorem rot_compl_inter_nonempty {s : ℕ} (hs : 1 ≤ s) {a a' : Fin (s + 4)}
    {e ρ : Equiv.Perm (Fin (s + 4))}
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'})
    (hρ : ρ = e * finRotate (s + 4) * e⁻¹) :
    (({a, a'} : Finset (Fin (s + 4)))ᶜ ∩
      ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ).Nonempty := by
  obtain ⟨hρρa, hρρa'⟩ := rot_symm_pow_two_eq_zero_one he hρ
  refine ⟨e ⟨2, by omega⟩, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · rw [Finset.mem_compl]
    intro hmem
    have hmem' : e ⟨2, by omega⟩ ∈
        ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} :
          Finset (Fin (s + 4))).map e.toEmbedding := by
      rw [he]
      exact hmem
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hmem'
    exact two_notMem_last_two s hs hmem'
  · rw [Finset.mem_compl]
    intro hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have h2 : (⟨2, by omega⟩ : Fin (s + 4)) = e.symm ((ρ * ρ) a) := by
        rw [← h, Equiv.symm_apply_apply]
      rcases hρρa with h0 | h1
      · rw [h0] at h2
        exact absurd h2 (by simp [Fin.ext_iff])
      · rw [h1] at h2
        exact absurd h2 (by simp [Fin.ext_iff])
    · have h2 : (⟨2, by omega⟩ : Fin (s + 4)) = e.symm ((ρ * ρ) a') := by
        rw [← h, Equiv.symm_apply_apply]
      rcases hρρa' with h0 | h1
      · rw [h0] at h2
        exact absurd h2 (by simp [Fin.ext_iff])
      · rw [h1] at h2
        exact absurd h2 (by simp [Fin.ext_iff])

private theorem exists_mem_range_swap_conj {G : Type} [Group G] {p s : ℕ}
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {a a' : Fin (s + 4)} {ρ : Equiv.Perm (Fin (s + 4))}
    {g₁ : G} {Ψ : StatedSp (s + 4) (GaloisField 2 1) →* G}
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn (s + 4) p ({a, a'} : Finset (Fin (s + 4)))ᶜ)
    (hK₂Ψ : K.map (MulAut.conj (g₁ * g₁)).toMonoidHom ≤ Ψ.range)
    (hg₁N : g₁ ∈ Subgroup.normalizer (Bs : Set G))
    (hg₁τ : MulAut.congr eta (ggConjAut Bs hg₁N) = SpCoord.permAut ρ)
    {c d : Fin (s + 4)}
    (hc : c ∈ ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ)
    (hd : d ∈ ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ)
    (hcd : c ≠ d) :
    ∃ g ∈ Ψ.range, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap c d) := by
  let c₀ : Fin (s + 4) := (ρ * ρ)⁻¹ c
  let d₀ : Fin (s + 4) := (ρ * ρ)⁻¹ d
  have hmem₀ : ∀ x ∈ ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ,
      (ρ * ρ)⁻¹ x ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hmem
    apply (Finset.mem_compl.mp hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h
    · exact Or.inl (by rw [← h, Equiv.Perm.inv_def, Equiv.apply_symm_apply])
    · exact Or.inr (by rw [← h, Equiv.Perm.inv_def, Equiv.apply_symm_apply])
  have hc₀ : c₀ ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ := hmem₀ c hc
  have hd₀ : d₀ ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ := hmem₀ d hd
  have hcd₀ : c₀ ≠ d₀ := by
    intro h
    apply hcd
    have h' := congrArg (ρ * ρ) h
    dsimp only [c₀, d₀] at h'
    simpa using h'
  obtain ⟨k, hkK, hkN, hkτ⟩ :=
    exists_mem_conjAut_eq_permAut_swap_of_bBlockOn hAK hc₀ hd₀ hcd₀
  have hg₂N : g₁ * g₁ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hg₁N hg₁N
  have hgN : (g₁ * g₁) * k * (g₁ * g₁)⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₂N hkN) (Subgroup.inv_mem _ hg₂N)
  have hgΨ : (g₁ * g₁) * k * (g₁ * g₁)⁻¹ ∈ Ψ.range := by
    apply hK₂Ψ
    refine Subgroup.mem_map.mpr ⟨k, hkK, ?_⟩
    simpa using MulAut.conj_apply (g := g₁ * g₁) k
  have hg₂τ : MulAut.congr eta (ggConjAut Bs hg₂N) = SpCoord.permAut (ρ * ρ) := by
    rw [ggConjAut_mul hg₁N hg₁N, map_mul, hg₁τ, ← SpCoord.permAut_mul']
  obtain ⟨hg, hgτ⟩ := exists_conjAut_swap_permAut hg₂N hkN hg₂τ hkτ
  have hc' : (ρ * ρ) c₀ = c := by
    dsimp only [c₀]
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hd' : (ρ * ρ) d₀ = d := by
    dsimp only [d₀]
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  refine ⟨(g₁ * g₁) * k * (g₁ * g₁)⁻¹, hgΨ, hg, ?_⟩
  rw [hgτ, hc', hd']

private theorem threeBlock_mem_range {G : Type} [Group G] [Finite G] {p s : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {ι : Fin (s + 2) → Fin (s + 4)} {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    {Ψ : StatedSp (s + 4) (GaloisField 2 1) →* G}
    (hs3 : 3 ≤ s) (hp2 : p ≠ 2)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (hι : Function.Injective ι)
    (hKΨ : K ≤ Ψ.range) :
    ∃ S₀ : Finset (Fin (s + 4)), S₀.card = 3 ∧
      ggBlockComm Bs eta (S₀ : Set (Fin (s + 4))) ≤ Ψ.range := by
  let N₀ : Finset (Fin (s + 2)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hN₀card : N₀.card = 3 := by simp [N₀]
  have hN₀ne : N₀.Nonempty := ⟨⟨0, by omega⟩, by simp [N₀]⟩
  have hN₀u : N₀ ≠ Finset.univ := by
    intro h
    have hcard : N₀.card = s + 2 := by
      rw [h, Finset.card_univ, Fintype.card_fin]
    omega
  refine ⟨N₀.map ⟨ι, hι⟩, ?_, ?_⟩
  · rw [Finset.card_map, hN₀card]
  · rw [Finset.coe_map]
    change ggBlockComm Bs eta (ι '' (N₀ : Set (Fin (s + 2)))) ≤ Ψ.range
    rw [hκ.ggBlockComm_image_eq_map_spBlock_of_or hp2 hBsC hyBs hKc
      (Or.inr (by omega)) hN₀ne hN₀u]
    exact (Subgroup.map_le_range κ (spBlock (GaloisField 2 1) N₀)).trans (by
      rw [hκ.2.2.1]
      exact hKΨ)

private theorem le_of_rotation {G : Type} [Group G] [Finite G] {p s : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F]
    {Bs K L : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {e : Equiv.Perm (Fin (s + 4))} {a a' : Fin (s + 4)}
    {ι : Fin (s + 2) → Fin (s + 4)}
    {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F (s + 4)) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    {Ψ : StatedSp (s + 4) (GaloisField 2 1) →* G} {g₁ : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hs3 : 3 ≤ s)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn (s + 4) p ({a, a'} : Finset (Fin (s + 4)))ᶜ)
    (hKΨ : K ≤ Ψ.range)
    (hK₂Ψ : K.map (MulAut.conj (g₁ * g₁)).toMonoidHom ≤ Ψ.range)
    (hg₁N : g₁ ∈ Subgroup.normalizer (Bs : Set G))
    (hg₁τ : MulAut.congr eta (ggConjAut Bs hg₁N) =
      SpCoord.permAut (e * finRotate (s + 4) * e⁻¹))
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'}) :
    L ≤ Ψ.range := by
  let ρ : Equiv.Perm (Fin (s + 4)) := e * finRotate (s + 4) * e⁻¹
  have hρ : ρ = e * finRotate (s + 4) * e⁻¹ := rfl
  obtain ⟨hIJ, hIJne⟩ := rot_compl_union he hρ, rot_compl_inter_nonempty (by omega) he hρ
  have hswap : ∀ c d : Fin (s + 4), c ≠ d →
      (c ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ ∧
        d ∈ ({a, a'} : Finset (Fin (s + 4)))ᶜ) ∨
      (c ∈ ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ ∧
        d ∈ ({(ρ * ρ) a, (ρ * ρ) a'} : Finset (Fin (s + 4)))ᶜ) →
      ∃ g ∈ Ψ.range, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
        MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap c d) := by
    intro c d hcd hcase
    rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · obtain ⟨g, hgK, hgN, hgτ⟩ :=
        exists_mem_conjAut_eq_permAut_swap_of_bBlockOn hAK hc hd hcd
      exact ⟨g, hKΨ hgK, hgN, hgτ⟩
    · exact exists_mem_range_swap_conj hAK hK₂Ψ hg₁N hg₁τ hc hd hcd
  obtain ⟨S₀, hS₀, hS₀M⟩ := threeBlock_mem_range hs3 hp2 hBsC hyBs hKc hκ hκ.1 hKΨ
  exact hLF.le_of_permLift hUF hp (by omega) hS₀ hS₀M
    (exists_mem_conjAut_eq_permAut_of_swaps hIJ hIJne hswap)

private theorem exists_psi_of_chart {G : Type} [Group G] [Finite G] {p s : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F]
    {Bs K L : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin (s + 4) → Multiplicative (ZMod p))}
    {e : Equiv.Perm (Fin (s + 4))} {a a' : Fin (s + 4)}
    {ι : Fin (s + 2) → Fin (s + 4)}
    {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F (s + 4)) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hs3 : 3 ≤ s)
    (hF2 : Nat.card (GaloisField 2 1) = 2)
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hιe : ∀ k, ι k = e (Fin.castLE (by omega) k))
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn (s + 4) p ({a, a'} : Finset (Fin (s + 4)))ᶜ)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      aPermutationFull (s + 4) p)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (he : ({⟨s + 2, by omega⟩, ⟨s + 3, by omega⟩} : Finset (Fin (s + 4))).map
      e.toEmbedding = {a, a'})
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F) :
    ∃ Ψ : StatedSp (s + 4) (GaloisField 2 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp (s + 4) (GaloisField 2 1)) ∧ Ψ.range = L ⊔ K := by
  let Y : Set (Fin (s + 4)) → Subgroup G := fun S => ggBlockComm Bs eta (e '' S)
  let X : Set (Fin (s + 4)) → Set (Fin (s + 4)) → Subgroup G :=
    fun S T => ggQTwoSmallBlock Bs eta (e '' S) (e '' T)
  have hY : ∀ N : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ →
      Y (Fin.castLE (by omega : s + 2 ≤ s + 4) '' ↑N) = (spBlock (GaloisField 2 1) N).map κ :=
    fun N hN hNu => chart_block_comm hp2 hBsC hyBs hKc hκ hιe N hN hNu
  have hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N →
      I.card ≤ 2 → X (Fin.castLE (by omega : s + 2 ≤ s + 4) '' ↑I)
        (Fin.castLE (by omega : s + 2 ≤ s + 4) '' ↑N) =
        (spBlock (GaloisField 2 1) I).map κ :=
    fun N I hN hNu hIN hI2 =>
      chart_block_small hp2 hBsC hyBs hKc hκ hιe N I hN hNu hIN hI2
  have hlift : ∀ τ : Equiv.Perm (Fin (s + 4)), ∃ g : G,
      ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom = X (τ '' S) (τ '' T) := by
    intro τ
    obtain ⟨g, -, hgN, hgτ⟩ := exists_mem_conjAut_eq_permAut hAut (e * τ * e⁻¹)
    exact ⟨g, fun S T => qTwoSmallBlock_map_conj_image hgN hgτ S T⟩
  obtain ⟨g₁, hg₁L, hg₁N, hg₁τ⟩ :=
    exists_mem_conjAut_eq_permAut hAut (e * finRotate (s + 4) * e⁻¹)
  obtain ⟨Ψ, hΨker, hΨ⟩ := weakCT_symplectic_two_of_three_conj_rotate hs3 hF2 hκ.2.1 hY hX
    hlift (fun S => ggBlockComm_image_map_conj hg₁N hg₁τ S)
      (fun S T => qTwoSmallBlock_map_conj_image hg₁N hg₁τ S T)
  have hK : κ.range = K := hκ.2.2.1
  have hKΨ : K ≤ Ψ.range := by
    rw [hΨ, hK]
    exact le_sup_left.trans le_sup_left
  have hK₂Ψ : K.map (MulAut.conj (g₁ * g₁)).toMonoidHom ≤ Ψ.range := by
    rw [hΨ, hK]
    exact le_sup_right
  have hLΨ := le_of_rotation hp hp2 hs3 hBsC hyBs hKc hκ hAK hKΨ hK₂Ψ hg₁N hg₁τ hLF hUF he
  refine ⟨Ψ, hΨker, le_antisymm ?_ (sup_le hLΨ hKΨ)⟩
  have hconjle : ∀ g ∈ L, K.map (MulAut.conj g).toMonoidHom ≤ L ⊔ K := by
    rintro g hg _ ⟨k, hk, rfl⟩
    change g * k * g⁻¹ ∈ L ⊔ K
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
      (Subgroup.mem_sup_right hk)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hg))
  rw [hΨ, hK]
  exact sup_le (sup_le le_sup_right (hconjle g₁ hg₁L)) (hconjle _ (L.mul_mem hg₁L hg₁L))

theorem ggSecFiveBPermProperQTwoSpPairMpInput_holds :
    GGSecFiveBPermProperQTwoSpPairMpInput := by
  intro hMp G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn7 eta hJoin hAut hNbr hG0 hCell K a a' haa'
    hroot hC hG0K
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlab, hK𝒦, ⟨eK⟩, hAK⟩ := hC
  have hB : B ≠ Bs := ne_Bs_of_root haa' hroot
  have hz : Line63.H5.twoCenter L = ⊥ := hR.1.1.twoCenter_eq_bot_of_B_lt_Bs
    (lt_of_le_of_ne hR.1.1.2.1.1 hB) hR.1.2.2.1.1.le_normalizer
  obtain ⟨-, F, hF, hFin, _, hN, φ, -, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel_of_twoCenter hR (by omega) (fun _ => hz) hlab
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC
    hR.1.1.card_bstar_inf_centralizer_L.le (by omega) eta hAut hN φ hM hdiag 1
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K := hNy.1.2.2.2.2.1
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 4 := ⟨n - 4, by omega⟩
  have hKc := isComponentOf_of_largeEvenPComponent (by omega : 1 ≤ s) hKp
    (eK : ↥K ≃* StatedSp (s + 2) (GaloisField 2 1))
  classical
  have hs3 : 3 ≤ s := by omega
  obtain ⟨e, he, hI⟩ := exists_perm_last_two haa'
  let ι : Fin (s + 2) → Fin (s + 4) := fun k => e (Fin.castLE (by omega) k)
  have hι : Function.Injective ι := e.injective.comp (Fin.castLE_injective _)
  obtain ⟨κ₁, ζ₁, hκ₁⟩ := ggSecFiveBPermSpK_exists_planeChartOn_of_conj hMp hp2 le_rfl
    (by omega : 2 ≤ s + 1) hR.1.1.2.1 (hR.1.2.2.1.2 y K hNy)
    (eK : ↥K ≃* StatedSp (s + 2) (GaloisField 2 1)) eta hι hI hAK
  have hκ : GGSpPlaneFrameOn Bs K eta ι κ₁ ζ₁ := ⟨hι, hκ₁⟩
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega), pow_one]
  exact exists_psi_of_chart hp hp2 hs3 hF2 hκ (fun _ => rfl) hAK hAut hBsC hyBs hKc he
    hLF hM.field

end CFSG.StandardType

end
