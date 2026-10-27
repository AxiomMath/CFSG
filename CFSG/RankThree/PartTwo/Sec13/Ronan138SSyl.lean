module

public import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SP
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step138PZero : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
      E ⊔ F ≤ P →
        P ≤ Subgroup.normalizer (L : Set G) ∧
          P ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers c

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_inf_thetaQuotCentralizer {L P : Subgroup G} {c : G} (hP3 : IsPGroup 3 P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPC : P ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers c) (hc3 : c ^ 3 = 1)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) : Nat.card P ≤ 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hq2 := two_lt_of_mulEquiv hLq hK hq ψ
  set f : P →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hPL)) with hf
  have hker : Nat.card f.ker ≤ 3 := by
    have hle : f.ker.map P.subtype ≤ Subgroup.zpowers c := by
      rintro _ ⟨t, ht, rfl⟩
      refine hPC (Subgroup.mem_inf.mpr ⟨t.2, ?_⟩)
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hPL t, ht, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective P.subtype_injective] at h1
    have h2 : Nat.card (Subgroup.zpowers c) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
    omega
  have hrange : Nat.card f.range ≤ 27 := by
    have h1 := Sec13.Item138Proof.factorization_card_three_eq_two he hiso h9
    have := Sec19.Item19ResProof.finite_mulAut (L ⧸ aschbacherSolvableCore 3 L)
    exact Sec19.Item19ResProof.card_le_of_isPGroup h1
      (Sec19.Item19ResProof.not_nine_dvd_card_outer he hiso (by omega)
        (fun h => h9 (Or.inl h)) (fun h => h9 (Or.inr h)))
      f.range (hP3.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hcard
  rw [hcard]
  calc Nat.card f.range * Nat.card f.ker ≤ 27 * 3 := Nat.mul_le_mul hrange hker
    _ = 81 := by norm_num

theorem item138SylHN_of (hPZ : Step138PZero) : Item138SylHN := by
  intro G _ _ A c L E hH hPGL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF⟩ := item138ExistsN G A c L E hH
  obtain ⟨x, y, -, -, -, -, -, -, h81, -, -⟩ := exists_frame138 hH hF hPGL
  have hH' := hH
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH'
  have hFEL : F ≤ E ⊔ L := hF.1.1
  obtain ⟨p, e, _, he, hiso⟩ := hL3
  have h9 := not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he hiso
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hEc : ∀ a ∈ E, a * c = c * a := fun a ha =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcE⟩)
  have hELc : E ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEc a ha))
      h.le_centralizer
  have hEFH : E ⊔ F ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (sup_le le_sup_left hFEL).trans (hELc.trans (centralizer_le_normalizer_zpowers c))
  have hEF3 : IsPGroup 3 (E ⊔ F : Subgroup G) :=
    IsPGroup.of_card (n := 4) (by rw [h81]; norm_num)
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  obtain ⟨Q, hQ⟩ := (hEF3.comap_subtype (K := H)).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup H).map H.subtype with hPdef
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P H := ⟨Q, rfl⟩
  have hEFP : E ⊔ F ≤ P := fun z hz =>
    ⟨⟨z, hEFH hz⟩, hQ (show (⟨z, _⟩ : H) ∈ (E ⊔ F).subgroupOf H from hz), rfl⟩
  obtain ⟨hPL, hPC⟩ := hPZ G A c L E hH hPGL F hF P hPsyl hEFP
  have hle := card_le_of_inf_thetaQuotCentralizer hPsyl.isPGroup hPL hPC hc3 hLq he hiso h9
  have hge : 81 ≤ Nat.card P := h81 ▸ Subgroup.card_le_of_le hEFP
  have hcard := hPsyl.card_eq
  rw [show Nat.card P = 3 ^ 4 by omega] at hcard
  exact (Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3)) hcard).symm

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
