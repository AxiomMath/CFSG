module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5FVertex
import CFSG.Quasithin.Recognition.Stroth.Str83G5FFpf
import CFSG.GroupTheory.ChiefFactors.OddElement
public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzRep
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzSmall

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem card_chiefMod_additive {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (Additive (Ch3z.chiefMod L N)) = L.relIndex N := by
  rw [Nat.card_congr Additive.toMul]
  have hker : (Ch3z.chiefIota hNL).ker = L.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Ch3z.chiefIota_eq_one_iff hNL x
  have hmain := Subgroup.card_ker_mul_card_range (Ch3z.chiefIota hNL)
  rw [hker, MonoidHom.range_eq_top.mpr (Ch3z.chiefIota_surjective hNL), Subgroup.card_top]
    at hmain
  have hcard : Nat.card ↥(L.subgroupOf N) = Nat.card ↥(L ⊓ N) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.2, x.1.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hcard, mul_comm] at hmain
  rw [← Subgroup.relIndex_mul_card L N] at hmain
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmain

theorem chief_dichotomy (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hQ : Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)))
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) L N) :
    (∀ g ∈ L1 ⊔ S, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ L) ∨
      (L.relIndex N = 2 ^ (4 * (2 * a + 1)) ∧
        ∀ δ ∈ borelOf L1 S, Odd (orderOf δ) → δ ≠ 1 →
          ∀ n ∈ N, δ * n * δ⁻¹ * n⁻¹ ∈ L → n ∈ L) := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨hpCore, -, -, e, he⟩ := sz_vertex (K := K) hK hF hB ha hSz
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hpCore ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ S)
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hQ1H).trans hHL
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hQ1H
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S))
  have hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
    rw [hpCore]
    intro q hq
    have hqH : q ∈ L1 ⊔ S := by
      rw [← hpCore] at hq
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ S) hq
    refine ⟨hqH, hHL hqH, fun n hn => ?_⟩
    have hchief : ∀ X : Subgroup G, L ≤ X → X ≤ N →
        (L1 ⊔ S) ≤ Subgroup.normalizer (X : Set G) → X = L ∨ X = N := by
      intro X hLX hXN hNX
      exact hstep.2.2.2 X ⟨hXN.trans hstep.1.1, fun g hg x hx =>
        (Subgroup.mem_normalizer_iff.mp (hNX hg) x).mp hx⟩ hLX hXN
    exact CFSG.GroupTheory.commutator_mem_of_chief (N := L1 ⊔ S) (P := Q1 L1 L2 S)
      (R₁ := N) (R₂ := L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S))
      (hpCore ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ S))
      (by rw [← hpCore]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ S))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hstep.1.1)
      hstep.2.2.1 hHN hHL hNL hchief q hq n hn
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod L N)) :=
    sectionRep hHL hHN hNL hE hO e
  haveI : Fact ρ.IsIrreducible :=
    ⟨sectionRep_isIrreducible hstep hQ1H hHL hHN hNL hE hO e⟩
  by_cases htriv : ∀ g, ρ g = 1
  ·
    left
    have htriv' : ∀ g, sectionRep hHL hHN hNL hE hO e g = 1 := htriv
    intro g hg n hn
    have hgn : g * n * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hg) n).mp hn
    have h2 := sectionRep_chiefIota (H := L1 ⊔ S) (X := suzukiGroup a K)
      hHL hHN hNL hE hO e ⟨g, hg⟩ ⟨n, hn⟩ hgn
    have hcomm : Additive.ofMul (Ch3z.chiefIota hNL ⟨g * n * g⁻¹, hgn⟩) =
        Additive.ofMul (Ch3z.chiefIota hNL ⟨n, hn⟩) := by
      rw [← h2]
      rw [htriv' (e (QuotientGroup.mk (⟨g, hg⟩ : ↥(L1 ⊔ S)))), Module.End.one_apply]
    have hlt : Ch3z.chiefIota hNL (⟨g * n * g⁻¹, hgn⟩ * (⟨n, hn⟩ : ↥N)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Additive.ofMul.injective hcomm
    have hmem := (Ch3z.chiefIota_eq_one_iff hNL
      (⟨g * n * g⁻¹, hgn⟩ * (⟨n, hn⟩ : ↥N)⁻¹)).mp hlt
    simpa using hmem
  ·
    right
    have hnt : ∃ g, ρ g ≠ 1 := by
      by_contra h
      push Not at h
      exact htriv h
    have hcard := card_chiefMod_additive (L := L) (N := N) hNL
    rcases CFSG.RankThree.GF2n.Tim81.Sec2.isSzNatural_or_le_card (K := K) (a := a) hK ρ hnt
      with hnat | hbig
    · have hnatρ : CFSG.RankThree.GF2n.Tim81.Sec2.IsSzNatural ρ := hnat
      obtain ⟨_, φ, -⟩ := hnat
      have hWK : Nat.card (Additive (Ch3z.chiefMod L N)) = Nat.card (Fin 4 → K) :=
        Nat.card_congr φ.toEquiv
      have hK4 : Nat.card (Fin 4 → K) = 2 ^ (4 * (2 * a + 1)) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, hK,
          ← pow_mul]
        congr 1
        ring
      refine ⟨hcard.symm.trans (hWK.trans hK4), fun δ hδ hodd h1 n hn hδn => ?_⟩
      exact mem_of_commutator_mem_of_isSzNatural hB hHL hHN hNL hE hO e he hnatρ hδ hodd h1 hn hδn
    ·
      exfalso
      have hle : 2 ^ (16 * (2 * a + 1)) ≤ Nat.card (Q1 L1 L2 S) := by
        calc 2 ^ (16 * (2 * a + 1)) ≤ Nat.card (Additive (Ch3z.chiefMod L N)) := hbig
          _ = L.relIndex N := hcard
          _ ≤ Nat.card ↥N :=
              Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card (H := L) (K := N))
          _ ≤ Nat.card (Q1 L1 L2 S) := Subgroup.card_le_of_le hstep.1.1
      exact absurd hle (not_le.mpr hQ)

end CFSG.Quasithin.Stroth.G5F

end
