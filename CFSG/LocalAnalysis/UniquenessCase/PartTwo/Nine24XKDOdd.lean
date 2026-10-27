module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDDefs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Fin
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import CFSG.CGT.PushingUpLit.SolK.GenFour
import CFSG.GH74.KGroups.PSL2
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Open
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
open CFSG.AGLEmbedding
open CFSG.GH74

private theorem n924x_false_of_section_bound {L : Type} [Group L] [Finite L]
    {X : Subgroup L} {n c : ℕ} (hn : 1 < n) (hL2 : IsL2 (Bar2 X) (2 * n))
    (hc : c < 2 ^ (2 * n))
    (hbound : ∀ (B E : Type) [Group B] [Group E] [Finite B] [Finite E] (ι : B →* L)
      (f : B →* E), Function.Injective ι → Function.Surjective f →
      (∀ x : E, x * x = 1) → Nat.card E ≤ c) : False := by
  classical
  have hn1 : 1 ≤ 2 * n := by omega
  have h2npos : 0 < 2 * n := by omega
  have hGF : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  obtain ⟨eS⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel
    (F := GaloisField 2 (2 * n)) 2 (2 * n) h2npos hGF hL2
  let U : Sylow 2 (PSL2GF 2 (2 * n)) := default
  have hU := CFSG.AGLEmbedding.psl2GF_sylow 2 (2 * n) hn1 U
  let T : Subgroup (Bar2 X) := U.map eS.symm.toMonoidHom
  have hTcard : Nat.card T = 2 ^ (2 * n) := by
    dsimp only [T]
    rw [Subgroup.card_map_of_injective (f := eS.symm.toMonoidHom) eS.symm.injective, hU.2]
  have hTtwo : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    dsimp only [T] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy2 : y ^ 2 = 1 := hU.1.2 y hy
    have := congrArg (fun z => eS.symm z) hy2
    simpa [pow_two] using this
  let B : Subgroup X := T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  let ι : B →* L := X.subtype.comp B.subtype
  have hι : Function.Injective ι := X.subtype_injective.comp B.subtype_injective
  let f : B →* T :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp B.subtype) T
      (fun b => b.2)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) (t : Bar2 X)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈ T
    rw [hx]
    exact t.2
  have hE2 : ∀ x : T, x * x = 1 := fun x => Subtype.ext (hTtwo x.1 x.2)
  have hle : Nat.card T ≤ c := hbound B T ι f hι hf hE2
  have hge : 2 ^ (2 * n) ≤ Nat.card T := by rw [hTcard]
  omega

private theorem n924x_card_le_four_of_section_rank {L : Type} [Group L] [Finite L]
    (hrank : SectionalTwoRankLE L 2) :
    ∀ (B E : Type) [Group B] [Group E] [Finite B] [Finite E] (ι : B →* L) (f : B →* E),
      Function.Injective ι → Function.Surjective f → (∀ x : E, x * x = 1) →
      Nat.card E ≤ 4 := by
  intro B E _ _ _ _ ι f hι hf hE2
  obtain ⟨P⟩ : Nonempty (Sylow 2 B) := inferInstance
  have hEp : IsPGroup 2 E := fun x => ⟨1, by simpa [pow_two] using hE2 x⟩
  have hidx : ((P : Subgroup B).map f).index = 1 := by
    have h1 : ((P : Subgroup B).map f).index ∣ (P : Subgroup B).index :=
      Subgroup.index_map_dvd (H := P.toSubgroup) hf
    obtain ⟨k, hk⟩ := hEp.index ((P : Subgroup B).map f)
    have h2 : ¬ 2 ∣ (P : Subgroup B).index := P.not_dvd_index
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · rfl
    · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h1) h2
  have htop : (P : Subgroup B).map f = ⊤ := Subgroup.index_eq_one.mp hidx
  have hrankP : SectionalTwoRankLE ↥(P : Subgroup B) 2 :=
    SectionalTwoRankLE.of_injective (ι.comp (P : Subgroup B).subtype)
      (hι.comp (P : Subgroup B).subtype_injective) hrank
  have hsurj : Function.Surjective (f.comp (P : Subgroup B).subtype) := by
    intro x
    have hx : x ∈ (P : Subgroup B).map f := htop ▸ Subgroup.mem_top x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨y, hy⟩, hyx⟩
  have hrankE : SectionalTwoRankLE E 2 :=
    SectionalTwoRankLE.of_surjective (f.comp (P : Subgroup B).subtype) hsurj hrankP
  have hcomm : ∀ a b : E, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE2 a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE2 b)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hE2 (a * b))
    rw [mul_inv_rev, ha, hb] at hab
    exact hab.symm
  have hEel : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup E) := by
    refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hcomm a.1 b.1)), ?_⟩
    intro x _
    exact by simpa [pow_two] using hE2 x
  have hcard := SectionalTwoRankLE.card_le_of_elementary hrankE ⊤ hEel
  rw [Subgroup.card_top] at hcard
  simpa using hcard

theorem noL2Section_psl2_odd {L : Type} [Group L] [Finite L] {p f : ℕ} (hp : p ≠ 2)
    (hL : LieModel L .PSL 2 p f) : NoL2Section L := by
  obtain ⟨hAdm, hB⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨K, hKfield, hKfin, hKcard, _⟩ := hB
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hp_prime : p.Prime := hAdm.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hf : 0 < f := Nat.lt_of_lt_of_le Nat.zero_lt_one hAdm.2.1
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := K) p f hf hKcard hL
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp_prime, hp_prime.odd_of_ne_two hp, hAdm.2.1, hKcard⟩
  have hgw := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd
  have hA : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo (PSL2 K) := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PSL2 K)))
    obtain ⟨m, hm, ⟨d⟩⟩ := hgw S
    exact ⟨S, m + 1, by omega, ⟨by simpa using d⟩⟩
  have hrank : SectionalTwoRankLE (PSL2 K) 2 :=
    CFSG.CGT.PushingUpLit.SolK.gen2_of_dihedral_or_semidihedral (Or.inl hA)
  have hrankL : SectionalTwoRankLE L 2 := SectionalTwoRankLE.of_mulEquiv e.symm hrank
  intro X n hn hL2
  refine n924x_false_of_section_bound hn hL2 ?_ (n924x_card_le_four_of_section_rank hrankL)
  calc 4 = 2 ^ 2 := by norm_num
    _ < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem noL2Section_psl3_odd {L : Type} [Group L] [Finite L] {p f : ℕ} (hp : p ≠ 2)
    (hL : LieModel L .PSL 3 p f) : NoL2Section L := by
  obtain ⟨hAdm, hB⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hB
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hp_prime : p.Prime := hAdm.1
  have hKodd : Nat.card K % 2 = 1 := by
    rw [hKcard]
    exact Nat.odd_iff.mp ((hp_prime.odd_of_ne_two hp).pow (n := f))
  have hsec : Sec8 (StatedProj (StatedSL 3 K)) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.sec8_statedSL hKodd
  have hsecL : Sec8 L := Sec8.of_injective e.toMonoidHom e.injective hsec
  intro X n hn hL2
  refine n924x_false_of_section_bound hn hL2 ?_ hsecL
  calc 8 = 2 ^ 3 := by norm_num
    _ < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem noL2Section_psu3_odd {L : Type} [Group L] [Finite L] {p f : ℕ} (hp : p ≠ 2)
    (hL : LieModel L .PSU 3 p f) : NoL2Section L := by
  obtain ⟨hAdm, hB⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hB
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hp_prime : p.Prime := hAdm.1
  have hKodd : Nat.card K % 2 = 1 := by
    rw [hKcard]
    exact Nat.odd_iff.mp (((hp_prime.odd_of_ne_two hp).pow (n := f)).pow)
  have hsec : Sec8 (StatedProj (StatedSU 3 (p ^ f) K)) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.sec8_statedSU (p ^ f) hKodd
  have hsecL : Sec8 L := Sec8.of_injective e.toMonoidHom e.injective hsec
  intro X n hn hL2
  refine n924x_false_of_section_bound hn hL2 ?_ hsecL
  calc 8 = 2 ^ 3 := by norm_num
    _ < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
