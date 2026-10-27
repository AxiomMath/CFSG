module

public import CFSG.RankThree.PartOne.DISTX.PairSym
public import CFSG.RankThree.PartOne.DISTX.Row10Members
public import CFSG.RankThree.PartOne.S13K.Node135
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.S12.Sec126a
public import CFSG.RankThree.PartOne.S12.Sec136Setup

public section

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem node136_of_members (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hSame : KFCommSame)
    (hRow10 : KF123Row 10) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) (hRefl : KF136Refl) (hAt : KF136At) : Node136 := by
  have h135 := node135_rank4
  intro G _ _ p A c L E h hF hF13 hT hEA hrow
  classical
  obtain ⟨hG, hweyl, hcard⟩ := rowTen_data hRow10 h107 h109 h122 h hrow
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have h5 := Sec12Three.five_le h
  obtain ⟨f, hf1, hpf, hmod⟩ := id hrow
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have h3 : p ∣ 3 := by simpa using hpf
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨u, huΓ, hu1, hu2, hucomm, hfix, hinv⟩ := central_involution_data h hF hG hweyl
  have hu : u ∈ torusWeyl E := Sec127.torusImage_le_torusWeyl E L huΓ
  obtain ⟨t₀, ht₀D, ht₀Γ⟩ : ∃ t₀, t₀ ∈ reflectionSet p E ∧ t₀ ∈ torusImage E L := by
    by_contra hne
    have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hxΓ => hne ⟨x, hx, hxΓ⟩
    have h3 := hF.three.1
    rw [hempty, Subgroup.closure_empty] at h3
    apply hu1
    have : u ∈ (⊥ : Subgroup (MulAut E)) := h3 ▸ huΓ
    exact Subgroup.mem_bot.1 this
  have hKt₀ := hAt G p A c L E f h hF hF13 hT hEA hf1 hpf hmod t₀ ht₀D ht₀Γ
  have hK : IsKt p E t₀ (kZero p E t₀) := (isKt_iff_of_nonexceptional hKt₀.1).2 rfl
  have hKL : kZero p E t₀ ≤ L := hF13.kt_le L hF13.inZeroStar t₀ ht₀D ht₀Γ _ hK
  have hodd := h135 G p A c L E h hF hF13 hT hcard t₀ ht₀D _ hK hKL ⟨u, hu⟩ huΓ
    (Subtype.ext hu2) hinv hucomm hfix
  have hnc : (⟨u, hu⟩ : ↥(torusWeyl E)) ∉ Subgroup.center ↥(torusWeyl E) := by
    intro hcen
    apply hF.five
    apply torusNormalizer_le_cNormalizer_of_invariant
    intro w hw b hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
    have hg : conjAut E w hwN ∈ torusWeyl E := ⟨⟨w, hwN⟩, rfl⟩
    have hgu : conjAut E w hwN * u = u * conjAut E w hwN :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨conjAut E w hwN, hg⟩)
    rw [← hfix] at hb ⊢
    obtain ⟨e', he', rfl⟩ := hb
    refine ⟨conjAut E w hwN e', ?_, Equivariance.coe_conjAut hwN e'⟩
    have h2 : u e' = e' := he'
    have h3 : (conjAut E w hwN * u) e' = (u * conjAut E w hwN) e' := by rw [hgu]
    show u (conjAut E w hwN e') = conjAut E w hwN e'
    have h4 : conjAut E w hwN (u e') = u (conjAut E w hwN e') := h3
    rw [← h4, h2]
  have _hEel : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨w, hw, hwH, -, hcomm⟩ := zStar_step hp hp2 u hu hu2 hfix hnc hodd
  obtain ⟨z, hzD, ⟨hcE', hzc⟩, hzL, ⟨h1D, h1L⟩, ⟨h2D, h2L⟩⟩ :=
    pair_both hRefl h hF hF13 hT hEA hrow hG hcard huΓ hu2 hucomm hfix hinv hw hwH hcomm
  obtain ⟨K, _, _, _, ⟨C⟩⟩ := exists_sp6ctx hGA h hF hEA hf1 hpf hmod
  have hKt₂ : KFAt p E f ((conjAut E w hw)⁻¹ * z * conjAut E w hw) :=
    hAt G p A c L E f h hF hF13 hT hEA hf1 hpf hmod _ h2D h2L
  have hKz : KFAt p E f z := by
    have h3 := hKt₂.conj hw
    have h4 : conjAut E w hw * ((conjAut E w hw)⁻¹ * z * conjAut E w hw) *
        (conjAut E w hw)⁻¹ = z := by
      group
    rwa [h4] at h3
  let s : Fin 3 → MulAut E := fun i => C.tSgn 1 (fun j => decide (j = i))
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp C.hp2 C.hpq'
  have hs_mem : ∀ i, s i ∈ reflectionSet p E := fun i => C.S_mem_reflectionSet hF13 i
  have hs_L : ∀ i, s i ∈ torusImage E L := fun i => C.tSgn_mem_torusImage _ _
  have hs_ne : ∀ i j, i ≠ j → s i ≠ s j := fun i j hij => C.S_ne hζ h5 hij
  have hs_comm : ∀ i j, s i * s j = s j * s i := fun i j => C.S_comm i j
  have hKs : ∀ i, KFAt p E f (s i) := fun i => C.kfAt_tSgn_S i
  have hzs : ∀ i, kZero p E z ≤ Subgroup.centralizer (kZero p E (s i) : Set G) := fun i =>
    commute_z_sign hS hRe hSame C hF13 hT hEA hzD (KFAt.toLiftAt hKz) hzc hzL hw h1D h1L h2L i
  have hss : ∀ i j, i ≠ j → kZero p E (s i) ≤ Subgroup.centralizer (kZero p E (s j) : Set G) :=
    fun i j hij => (hSame G p A c L E h hF hF13 hT (Or.inl hEA) (s i) (hs_mem i) (hs_L i) (s j)
      (hs_mem j) (hs_L j) (hs_ne i j hij) (hs_comm i j)).1
  exact no_four_local C.hf2 h.setup.2.2.2.2.1 hKz (hKs 0) (hKs 1) (hKs 2) (hzs 0) (hzs 1) (hzs 2)
    (hss 0 1 (by decide)) (hss 0 2 (by decide)) (hss 1 2 (by decide))

end CFSG.RankThree.PartOne.DISTX
