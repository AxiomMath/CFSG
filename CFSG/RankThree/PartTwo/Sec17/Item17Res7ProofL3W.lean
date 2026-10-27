module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22W
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Quot
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof17Res7

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem exists_w_of_l3 (hA : KS17L3AutCent) (hT : KS17L3TwoCent)
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hLnorm : ∀ t ∈ L, t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      t ∈ Subgroup.normalizer (A : Set G))
    (hB9 : Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) = 9) {q : ℕ} [Fact q.Prime] (hq3 : 3 < q)
    (hiso : Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) q 1) (h91 : q % 9 ≠ 1)
    (h98 : q % 9 ≠ 8) :
    ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLY : L ≤ Y₀ := h.toSec17Std.le_y0
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set B := Proof17Res6.kimg Y₀ (A ⊓ L) with hB
  set R := Proof17Res6.kimg Y₀ (S ⊓ Y₀) with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hBR : B ≤ Subgroup.normalizer (R : Set _) :=
    Proof17Res6.kimg_le_normalizer_kimg (inf_le_left.trans hAS)
  have hR2 : IsPGroup 2 R := ((hS2.to_le inf_le_left).comap_subtype).map _
  have hRmax : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) :=
    ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, hBR⟩, fun X hX hRX =>
      Proof17Res6.le_kimg_of_le h h142 hLsurj hAnorm
        ((isPiSubgroup_piOf_iff Nat.prime_two X).mp hX.2.1) hX.2.2 hRX⟩
  obtain ⟨x, hxB, hxR⟩ := exists_not_mem_normalizer_of_two hA hT hq3 hiso h91 h98 hB9 hRmax
  set κL : ↥L →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ := κ.comp (Subgroup.inclusion hLY) with hκL
  have hκker : IsPGroup 2 κL.ker := by
    rw [hκL, ← MonoidHom.comap_ker, hκ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hLY)
  set BL : Subgroup ↥L := (A ⊓ L).subgroupOf L with hBL
  have hBL3 : IsPGroup 3 BL :=
    ((HeadProof.isE27_of_std h.toSec17Std).isPGroup.to_le inf_le_left).comap_subtype
  have hBLmap : BL.map κL = B := by
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Proof17Res6.mem_kimg.mpr ⟨Subgroup.inclusion hLY b, Subgroup.mem_subgroupOf.mp hb,
        rfl⟩
    · intro hz
      obtain ⟨b, hb, rfl⟩ := Proof17Res6.mem_kimg.mp hz
      exact ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hBc : ∀ u ∈ BL.map κL, ∀ v ∈ BL.map κL, u * v = v * u := by
    rw [hBLmap]
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Proof17Res6.mem_kimg.mp hu
    obtain ⟨b, hb, rfl⟩ := Proof17Res6.mem_kimg.mp hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.toSec17Std.commute_of_mem ha.1 hb.1)
  have hxκ : x ∈ κL.range := by
    obtain ⟨l, hl, hlx⟩ := hLsurj x
    exact ⟨⟨l, hl⟩, hlx⟩
  have hxN : x ∈ Subgroup.normalizer ((BL.map κL : Subgroup _) : Set _) := by
    rw [hBLmap]
    exact hxB
  obtain ⟨y, hyN, hyκ⟩ := Step163Alt.exists_normalizer_lift κL hκker hBL3 hBc hxκ hxN
  have hBLL : BL.map L.subtype = A ⊓ L := by
    rw [hBL, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hwAL : (y : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    have := Subgroup.le_normalizer_map L.subtype ⟨y, hyN, rfl⟩
    rwa [hBLL] at this
  have hwY : (y : G) ∈ Y₀ := hLY y.2
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hLnorm y y.2 hwAL, hwY⟩, hwAL, fun hwS => hxR ?_⟩
  have hwR : κ ⟨y, hwY⟩ ∈ Subgroup.normalizer (R : Set _) :=
    Proof17Res6.mk_mem_normalizer_kimg hwS
  have hκy : κL y = κ ⟨y, hwY⟩ := rfl
  have hu : x⁻¹ * κ ⟨y, hwY⟩ ∈ Subgroup.centralizer (B : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hBLmap] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    have h1 := hyκ b hb
    rw [map_mul, map_mul, map_inv, hκy] at h1
    calc κL b * (x⁻¹ * κ ⟨y, hwY⟩)
        = x⁻¹ * (x * κL b * x⁻¹) * κ ⟨y, hwY⟩ := by group
      _ = x⁻¹ * (κ ⟨y, hwY⟩ * κL b * (κ ⟨y, hwY⟩)⁻¹) * κ ⟨y, hwY⟩ := by rw [h1]
      _ = x⁻¹ * κ ⟨y, hwY⟩ * κL b := by group
  rw [centralizer_eq_of_autCent hA hq3 hiso h91 h98 hB9] at hu
  have hx' : x = κ ⟨y, hwY⟩ * (x⁻¹ * κ ⟨y, hwY⟩)⁻¹ := by group
  rw [hx']
  exact mul_mem hwR (inv_mem (hBR hu))

end Proof17Res7

theorem claim1719WNJOneL3_of_autCent
    (hA : KS17L3AutCent) (hT : KS17L3TwoCent) (h1715 : Item1715)
    (h135 : Item135) (h142 : Concl142S14) (h9 : CardInfNineS17) (h138 : Item138N) :
    Claim1719WNJOneL3 := by
  intro G _ _ A c L Y₀ Y₁ S p P h _ hΩ hL3
  have hs := h.toSec17Std
  obtain ⟨hY, q, hq, hq3, h91, h98, hiso⟩ := Proof17Res7.exists_l3Pic h1715 h135 h138 h hΩ hL3
  have h9' := h9 G A c L Y₀ hs
  exact Proof17Res7.exists_w_of_l3 hA hT h (h142 G A c L hs.toSec14Std)
    (Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY) (Proof17Res6.le_normalizer_of_inf hs h9')
    (fun t ht htE => Proof1721.mem_normalizer_A_of_mem_L hs h9' ht htE)
    (Proof17Res6.card_kimg_inf hs h9') hq3 hiso h91 h98

end CFSG.RankThree.PartTwo.Sec17
