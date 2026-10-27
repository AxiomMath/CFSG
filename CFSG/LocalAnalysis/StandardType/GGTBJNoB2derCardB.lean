module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue2
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LocalAnalysis.GL83PartI.I_7_13
import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_card_B {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    Nat.card B = 81 := by
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hB : IsElemAbelian 3 B := hS.1.1
  have hpre : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hcomp.2.2.1
  have hnormJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hpre
  let φ : ↥B →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hnormJ)
  have hmemker : ∀ b : ↥B, b ∈ φ.ker ↔ (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    exact normalizerMonoidHom_eq_one_iff (Subgroup.inclusion hnormJ b).2
  have hker_eq : φ.ker.map B.subtype = D := by
    rw [hDcent]
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, (hmemker b).mp hb⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (hmemker ⟨g, hgB⟩).mpr hgC, rfl⟩
  have hkercard : Nat.card φ.ker = 3 ^ 2 := by
    rw [← hDcard, ← hker_eq]
    exact (Subgroup.card_map_of_injective (f := B.subtype) (Subgroup.subtype_injective B)).symm
  have hE : IsElemAbelian 3 φ.range := isElemAbelian_range_of_isElemAbelian hB φ
  have hrange : Nat.card φ.range ≤ 3 ^ 2 := by
    obtain ⟨eiso⟩ := ggB2der_label_iso_A6 hJ
    obtain ⟨A', hA'ab, hA'card⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.H248.exists_elemAbelian_mulAut_of_perfect
        hperfJ eiso φ.range hE
    by_contra hle
    rw [not_le] at hle
    have hpg : IsPGroup 3 φ.range := by
      intro g
      exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
    have hpow : 3 ^ 3 ≤ Nat.card φ.range := by
      obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hpg
      rw [hn] at hle ⊢
      have hn3 : 3 ≤ n := by
        by_contra h
        rw [not_le] at h
        interval_cases n <;> norm_num at hle
      exact Nat.pow_le_pow_right (by norm_num) hn3
    have h3 : 3 ^ 3 ≤ Nat.card A' := by rw [hA'card]; exact hpow
    have hpgA : IsPGroup 3 A' := by
      intro g
      exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA'ab.2 g.1 g.2)⟩
    obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
      (p := 3) (n := 3) (by norm_num) hpgA h3
    let D' : Subgroup (MulAut (alternatingGroup (Fin 6))) := H.map A'.subtype
    have hD'card : Nat.card D' = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective (f := A'.subtype) (Subgroup.subtype_injective A'),
        hHcard]
    have hD'comm : IsMulCommutative ↥D' := by
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      show (x : MulAut (alternatingGroup (Fin 6))) * (y : MulAut (alternatingGroup (Fin 6)))
          = (y : MulAut (alternatingGroup (Fin 6))) * (x : MulAut (alternatingGroup (Fin 6)))
      have hxA : (x : MulAut (alternatingGroup (Fin 6))) ∈ A' := by
        obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp x.2
        rw [← ha]; exact a.2
      have hyA : (y : MulAut (alternatingGroup (Fin 6))) ∈ A' := by
        obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp y.2
        rw [← ha]; exact a.2
      haveI : IsMulCommutative ↥A' := hA'ab.1
      exact congrArg Subtype.val
        (mul_comm' (⟨(x : MulAut (alternatingGroup (Fin 6))), hxA⟩ : ↥A')
          ⟨(y : MulAut (alternatingGroup (Fin 6))), hyA⟩)
    have hD'pow : ∀ x ∈ D', x ^ 3 = 1 := by
      intro x hx
      obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp hx
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA'ab.2 a.1 a.2)
      rw [← ha, ← map_pow, ha3, map_one]
    exact (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.no_elemAbelian_cube_mulAut_alternating_six
      (p := 3) (by norm_num) (by norm_num) D') ⟨hD'comm, hD'pow, hD'card⟩
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hcfg
  have hbeta : 3 ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  have hrank : 4 ≤ LargeEvenTwoLocalRank 3 G := hbeta.2.2.2
  have hlower : 81 ≤ Nat.card B := by
    rw [hcardB]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hrank
  have hupper : Nat.card B ≤ 81 := by
    have hcard := Subgroup.card_ker_mul_card_range φ
    calc Nat.card ↥B = Nat.card φ.ker * Nat.card φ.range := hcard.symm
      _ ≤ 3 ^ 2 * 3 ^ 2 := Nat.mul_le_mul (le_of_eq hkercard) hrange
      _ = 81 := by norm_num
  omega

end CFSG.StandardType

end
