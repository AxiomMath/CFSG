module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
import CFSG.RankThree.PartTwo.Sec21.Item228Census6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

namespace Item228Census6Proof


theorem nonempty_autIn_g2 {Y : Type} [Group Y] {f : ℕ} (hev : Even f)
    (hY : ChevalleyExceptionalModel Y .G2 2 f) {B : Subgroup Y} (hB : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) : Nonempty (Sec4.autIn ⊤ B ≃* DihedralGroup 6) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    exact (Finite.one_lt_card (α := K)).ne' hK
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have h31 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have h := two_pow_mod_three_of_even hev
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  set φ : Y ≃* adjointGroup .G2 K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot) with hφ
  set T := (torusTorsion K 3).subgroupOf (adjointGroup .G2 K) with hTdef
  have hTmem : ∀ x : adjointGroup .G2 K, x ∈ T ↔ (x : ModGL .G2 K) ∈ torusTorsion K 3 :=
    fun x => Subgroup.mem_subgroupOf
  have hD3 : ∀ x ∈ B.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ^ 3 = 1
    rw [← map_pow, hB.2 x hx, map_one]
  have hDc : ∀ x ∈ B.map φ.toMonoidHom, ∀ y ∈ B.map φ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    have hxy : x * y = y * x := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  obtain ⟨g, hg⟩ :=
    Sec4.Res417Seven.exists_conj_mem_torusTorsion_three h31 (B.map φ.toMonoidHom) hD3 hDc
  have hle : B.map (φ.trans (MulAut.conj g)).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hTmem _).mpr (hg _ ⟨x, hx, rfl⟩)
  have hTcard : Nat.card T = 9 := by
    rw [hTdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusTorsion_le_torusGroup 3 |>.trans
      torusGroup_le_adjointGroup_G2)).toEquiv, natCard_torusTorsion h31]
    norm_num
  have hmap : B.map (φ.trans (MulAut.conj g)).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hTcard, Subgroup.card_map_of_injective (MulEquiv.injective _), hB9])
  obtain ⟨ψ⟩ := Sec4.Res417Six.nonempty_autIn_mulEquiv_of_map_eq _ hmap
  obtain ⟨ψ'⟩ := Sec4.Res417Seven.nonempty_torusImage_torusTorsion_three_mulEquiv h31
  exact ⟨ψ.trans ψ'⟩

end Item228Census6Proof

end CFSG.RankThree.PartTwo.Sec21
