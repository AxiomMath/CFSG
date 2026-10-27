module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup
import Mathlib.Algebra.Group.Subgroup.Ker

namespace CFSG
end CFSG
open CFSG

/-!
# Quotient index-parity infrastructure for Lemma 2.7

Generic Noether/cardinality helpers used to reduce divisibility-by-four of
subgroup indices to the D-group quotient models: image cardinality, index
decomposition across a surjective homomorphism, odd-kernel two-part
preservation, and the trivial-kernel embedding bound.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-! ## Quotient index-parity infrastructure for the D-group cases -/

/-- Noether's first isomorphism theorem, in cardinal form: for a subgroup
`K` of `G`, `|K| = |K.map f| * |K ⊓ f.ker|`. -/
public theorem card_map_eq_card_mul_card_ker
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (K : Subgroup G) :
    Nat.card (↥K) =
      Nat.card (↥(K.map f)) * Nat.card (↥(K ⊓ f.ker)) := by
  classical
  let kerK : Subgroup (↥K) := (K ⊓ f.ker).subgroupOf K
  have hkerK : kerK = (f.comp K.subtype).ker := by
    ext x
    simp [kerK, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have : kerK.Normal := by
    rw [hkerK]
    infer_instance
  have hrange : (f.comp K.subtype).range = K.map f := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  have h1 : (↥K) ⧸ kerK ≃* (↥K) ⧸ (f.comp K.subtype).ker :=
    QuotientGroup.quotientMulEquivOfEq hkerK
  have h2 : (↥K) ⧸ (f.comp K.subtype).ker ≃* (f.comp K.subtype).range :=
    QuotientGroup.quotientKerEquivRange (f.comp K.subtype)
  have h3 : (f.comp K.subtype).range ≃* K.map f :=
    MulEquiv.subgroupCongr hrange
  have hiso : Nonempty ((↥K) ⧸ kerK ≃* K.map f) :=
    ⟨h1.trans (h2.trans h3)⟩
  have hcard : Nat.card (↥K) =
      Nat.card ((↥K) ⧸ kerK) * Nat.card (↥kerK) := by
    rw [← kerK.index_mul_card, Subgroup.index_eq_card]
  have eKer : kerK ≃* ↥(K ⊓ f.ker) := by
    dsimp [kerK]
    exact Subgroup.subgroupOfEquivOfLe (H := K ⊓ f.ker) (K := K) inf_le_left
  have hcardKer : Nat.card (↥kerK) = Nat.card (↥(K ⊓ f.ker)) :=
    Nat.card_congr eKer.toEquiv
  calc
    Nat.card (↥K) = Nat.card ((↥K) ⧸ kerK) * Nat.card (↥kerK) := hcard
    _ = Nat.card (↥(K.map f)) * Nat.card (↥kerK) := by
      rw [Nat.card_congr hiso.some.toEquiv]
    _ = Nat.card (↥(K.map f)) * Nat.card (↥(K ⊓ f.ker)) := by
      rw [hcardKer]

/-- Index of a subgroup in terms of its image and its intersection with the
kernel of a surjective homomorphism:
`N.index = (N.map f).index * [f.ker : N ⊓ f.ker]`. -/
public theorem index_eq_index_map_mul_index_inf_ker
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) :
    N.index = (N.map f).index *
      ((N ⊓ f.ker).subgroupOf f.ker).index := by
  classical
  let Kidx := ((N ⊓ f.ker).subgroupOf f.ker).index
  have hcardN : Nat.card (↥N) =
      Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker)) :=
    card_map_eq_card_mul_card_ker f N
  have hcardG : Nat.card G = Nat.card H * Nat.card (↥(f.ker)) := by
    have h := (f.ker).index_mul_card
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf] at h
    simpa [Nat.card_eq_fintype_card] using h.symm
  have hprodN : N.index * Nat.card (↥N) = Nat.card G := N.index_mul_card
  have hprodNQ : (N.map f).index * Nat.card (↥(N.map f)) = Nat.card H :=
    (N.map f).index_mul_card
  have eNK : (N ⊓ f.ker).subgroupOf f.ker ≃* ↥(N ⊓ f.ker) :=
    Subgroup.subgroupOfEquivOfLe (H := N ⊓ f.ker) (K := f.ker) inf_le_right
  have hcardNK : Nat.card (↥((N ⊓ f.ker).subgroupOf f.ker)) =
      Nat.card (↥(N ⊓ f.ker)) := Nat.card_congr eNK.toEquiv
  have hprodNK : Kidx * Nat.card (↥(N ⊓ f.ker)) = Nat.card (↥(f.ker)) := by
    calc
      Kidx * Nat.card (↥(N ⊓ f.ker))
          = ((N ⊓ f.ker).subgroupOf f.ker).index *
              Nat.card (↥((N ⊓ f.ker).subgroupOf f.ker)) := by
            rw [hcardNK]
      _ = Nat.card (↥(f.ker)) := ((N ⊓ f.ker).subgroupOf f.ker).index_mul_card
  have hmul : N.index * Nat.card (↥N) =
      ((N.map f).index * Kidx) * Nat.card (↥N) := by
    calc
      N.index * Nat.card (↥N) = Nat.card G := hprodN
      _ = Nat.card H * Nat.card (↥(f.ker)) := hcardG
      _ = (N.map f).index * Nat.card (↥(N.map f)) *
          (Kidx * Nat.card (↥(N ⊓ f.ker))) := by
        rw [hprodNQ, hprodNK]
      _ = ((N.map f).index * Kidx) *
          (Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker))) := by ring
      _ = ((N.map f).index * Kidx) * Nat.card (↥N) := by
        rw [← hcardN]
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N)) hmul

/-- If a normal kernel has odd order, a subgroup of order divisible by four
has image of order divisible by four. -/
public theorem card_dvd_four_of_map_odd_kernel
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G)
    (hkerOdd : Odd (Nat.card (↥(f.ker))))
    (h4 : 4 ∣ Nat.card (↥N)) :
    4 ∣ Nat.card (↥(N.map f)) := by
  classical
  have hcardN : Nat.card (↥N) =
      Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker)) :=
    card_map_eq_card_mul_card_ker f N
  have hNKodd : Odd (Nat.card (↥(N ⊓ f.ker))) := by
    exact Odd.of_dvd_nat hkerOdd (Subgroup.card_dvd_of_le inf_le_right)
  have hcop2 : Nat.Coprime 2 (Nat.card (↥(N ⊓ f.ker))) :=
    Nat.coprime_two_left.mpr hNKodd
  have hcop4 : Nat.Coprime 4 (Nat.card (↥(N ⊓ f.ker))) := by
    simpa using (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2
      (Nat.card (↥(N ⊓ f.ker)))).2 hcop2
  have h4' : 4 ∣ Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker)) := by
    rwa [← hcardN]
  exact hcop4.dvd_of_dvd_mul_left (by simpa [mul_comm] using h4')

/-- Divisibility by four of an index is decided in the quotient by an odd
normal kernel. -/
public theorem index_not_dvd_four_of_quotient_index_not_dvd_four
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G)
    (hkerOdd : Odd (Nat.card (↥(f.ker))))
    (hnot4Q : ¬ 4 ∣ (N.map f).index) :
    ¬ 4 ∣ N.index := by
  classical
  have hidx : N.index = (N.map f).index *
      ((N ⊓ f.ker).subgroupOf f.ker).index :=
    index_eq_index_map_mul_index_inf_ker f hf N
  intro h4N
  have h4N' : 4 ∣ (N.map f).index *
      ((N ⊓ f.ker).subgroupOf f.ker).index := by
    rwa [← hidx]
  have hKidOdd : Odd ((N ⊓ f.ker).subgroupOf f.ker).index := by
    have hmul := ((N ⊓ f.ker).subgroupOf f.ker).index_mul_card
    have hdvd : ((N ⊓ f.ker).subgroupOf f.ker).index ∣
        Nat.card (↥(f.ker)) :=
      ⟨Nat.card (↥((N ⊓ f.ker).subgroupOf f.ker)), hmul.symm⟩
    exact Odd.of_dvd_nat hkerOdd hdvd
  have hcop2 : Nat.Coprime 2 ((N ⊓ f.ker).subgroupOf f.ker).index :=
    Nat.coprime_two_left.mpr hKidOdd
  have hcop4 : Nat.Coprime 4 ((N ⊓ f.ker).subgroupOf f.ker).index := by
    simpa using (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2
      ((N ⊓ f.ker).subgroupOf f.ker).index).2 hcop2
  exact hnot4Q (hcop4.dvd_of_dvd_mul_left (by simpa [mul_comm] using h4N'))

/-- If the image of a subgroup under a homomorphism with odd-order kernel has
odd order, a subgroup of order divisible by four meets the kernel in order
divisible by four. -/
public theorem card_dvd_four_of_inf_ker_odd_image
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G)
    (himgOdd : Odd (Nat.card (↥(N.map f))))
    (h4 : 4 ∣ Nat.card (↥N)) :
    4 ∣ Nat.card (↥(N ⊓ f.ker)) := by
  classical
  have hcardN : Nat.card (↥N) =
      Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker)) :=
    card_map_eq_card_mul_card_ker f N
  have h4' : 4 ∣ Nat.card (↥(N.map f)) * Nat.card (↥(N ⊓ f.ker)) := by
    rwa [← hcardN]
  have hcop2 : Nat.Coprime 2 (Nat.card (↥(N.map f))) :=
    Nat.coprime_two_left.mpr himgOdd
  have hcop4 : Nat.Coprime 4 (Nat.card (↥(N.map f))) := by
    simpa using (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2
      (Nat.card (↥(N.map f)))).2 hcop2
  exact hcop4.dvd_of_dvd_mul_left h4'

/-- If the kernel-side relative index is not divisible by four and the
image-side index is odd, then the ambient index is not divisible by four. -/
public theorem index_not_dvd_four_of_inf_ker_index_not_dvd_four
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G)
    (himgIndexOdd : Odd ((N.map f).index))
    (hnot4K : ¬ 4 ∣ ((N ⊓ f.ker).subgroupOf f.ker).index) :
    ¬ 4 ∣ N.index := by
  classical
  have hidx : N.index = (N.map f).index *
      ((N ⊓ f.ker).subgroupOf f.ker).index :=
    index_eq_index_map_mul_index_inf_ker f hf N
  intro h4N
  have h4N' : 4 ∣ (N.map f).index *
      ((N ⊓ f.ker).subgroupOf f.ker).index := by
    rwa [← hidx]
  have hcop2 : Nat.Coprime 2 ((N.map f).index) :=
    Nat.coprime_two_left.mpr himgIndexOdd
  have hcop4 : Nat.Coprime 4 ((N.map f).index) := by
    simpa using (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2
      ((N.map f).index)).2 hcop2
  exact hnot4K (hcop4.dvd_of_dvd_mul_left h4N')

/-- If a subgroup meets the kernel of a homomorphism trivially, its image has
the same cardinality and is bounded by the codomain. -/
public theorem card_le_of_inf_ker_bot
    {G : Type u} [Group G] [Finite G] {H : Type u} [Group H] [Finite H]
    (f : G →* H) (M : Subgroup G)
    (hbot : M ⊓ f.ker = ⊥) :
    Nat.card (↥M) ≤ Nat.card H := by
  classical
  have hfM : Function.Bijective (f.subgroupMap M) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff]
      rw [Subgroup.ker_subgroupMap M f]
      have hmap : (f.ker.subgroupOf M).map M.subtype = f.ker ⊓ M :=
        Subgroup.subgroupOf_map_subtype (H := f.ker) (K := M)
      have hbot' : (f.ker.subgroupOf M).map M.subtype = ⊥ := by
        rw [hmap]
        simpa [inf_comm] using hbot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := f.ker.subgroupOf M) (f := M.subtype) M.subtype_injective).mp hbot'
    · exact f.subgroupMap_surjective M
  have hcard : Nat.card (↥M) = Nat.card (↥(M.map f)) :=
    Nat.card_congr (Equiv.ofBijective (f.subgroupMap M) hfM)
  calc
    Nat.card (↥M) = Nat.card (↥(M.map f)) := hcard
    _ ≤ Nat.card H := by
      simpa [Subgroup.card_top] using
        Subgroup.card_le_of_le (le_top : M.map f ≤ ⊤)


end

end CFSG.GorensteinWalter
