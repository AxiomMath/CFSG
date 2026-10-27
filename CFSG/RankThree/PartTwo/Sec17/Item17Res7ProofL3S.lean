module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofJ2
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof17Res7

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem le_sup_cQuot_of_l3 (hA : KS17L3AutCent) {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hB9 : Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) = 9) {q : ℕ} [Fact q.Prime] (hq3 : 3 < q)
    (hiso : Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) q 1) (h91 : q % 9 ≠ 1)
    (h98 : q % 9 ≠ 8) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) :=
  Proof17Res6.le_sup_cQuot_of_inner h h142 hLsurj hAnorm hSM
    (center_eq_bot_of_iso le_rfl hq3 hiso)
    (Proof17Res6.actQ_le_range_of h hSM fun _ hQ3 hQN =>
      le_range_of_autCent hA hq3 hiso h91 h98 hB9 hQ3 hQN)

theorem item1717One_of_l3 (hA : KS17L3AutCent) (hT : KS17L3TwoCent) [(kerAO2 A Y₀).Normal]
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hB9 : Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) = 9) {q : ℕ} [Fact q.Prime] (hq3 : 3 < q)
    (hiso : Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) q 1) (h91 : q % 9 ≠ 1)
    (h98 : q % 9 ≠ 8) :
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
        imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set B := Proof17Res6.kimg Y₀ (A ⊓ L) with hB
  set R := Proof17Res6.kimg Y₀ (S ⊓ Y₀) with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hSQ.1.2.2 h.le_normalizer_y0
  refine ⟨le_antisymm (le_sup_cQuot_of_l3 hA h h142 hLsurj hAnorm hSM hB9 hq3 hiso h91 h98)
    (sup_le inf_le_left inf_le_left), ?_⟩
  have hBR : B ≤ Subgroup.normalizer (R : Set _) :=
    Proof17Res6.kimg_le_normalizer_kimg (inf_le_left.trans hAS)
  have hR2 : IsPGroup 2 R := ((hS2.to_le inf_le_left).comap_subtype).map _
  obtain ⟨b, hbB, hb1, hRO⟩ := (hT _ q hq3 hiso h91 h98 B hB9).1 R hR2 hBR
  obtain ⟨a, haAL, rfl⟩ := Proof17Res6.mem_kimg.mp hbB
  set V := CFSG.Open.pCoreOf 2 (Subgroup.centralizer {κ a}) with hV
  have hBC : B ≤ Subgroup.centralizer ({κ a} : Set _) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_card_nine hB9 hx hbB)
  have hBV : B ≤ Subgroup.normalizer (V : Set _) :=
    hBC.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVR : V ≤ R := Proof17Res6.le_kimg_of_le h h142 hLsurj hAnorm hV2 hBV hRO
  have hRV : R = V := le_antisymm hRO hVR
  refine ⟨a, haAL.1, haAL.2, fun ha1 => hb1 ?_, ?_⟩
  · have : a = 1 := Subtype.ext ha1
    rw [this, map_one]
  · rw [Proof17Res6.oTwoCY0_eq_kimg (A := A) haAL.1]
    refine Proof17Res6.imgY0_eq_of_kimg_eq inf_le_right (Subgroup.map_subtype_le _) ?_
    rw [Proof17Res6.kimg_preimage, ← hR, hRV]

end Proof17Res7

end CFSG.RankThree.PartTwo.Sec17
