module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL card_mapL mapL_inf_centralizer
  embedOf embedOf_injective perfectResidualEquiv)

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {L : Subgroup G}
  {L' : Subgroup G'} (E : L ≃* L')

theorem nonempty_bar2_derInf8_mapL {A : Subgroup G} (hA : A ≤ L) :
    Nonempty (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G))) ≃*
      Bar2 (F08.DerInf8 (L' ⊓ centralizer (mapL E A : Set G')))) := by
  let φ := perfectResidualEquiv E hA
  exact ⟨QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)⟩

theorem pRank_inf_centralizer_mapL {A : Subgroup G} (hA : A ≤ L) (p : ℕ) :
    Open.pRank p (L' ⊓ centralizer (mapL E A : Set G')) =
      Open.pRank p (L ⊓ centralizer (A : Set G)) := by
  rw [← mapL_inf_centralizer E hA]
  have h1 : Open.pRank p (mapL E (L ⊓ centralizer (A : Set G))) =
      Open.pRank p ((L ⊓ centralizer (A : Set G)).subgroupOf L) :=
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
      (embedOf_injective E) _
  have h2 : Open.pRank p (L ⊓ centralizer (A : Set G)) =
      Open.pRank p ((L ⊓ centralizer (A : Set G)).subgroupOf L) := by
    have h := CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
      L.subtype_injective ((L ⊓ centralizer (A : Set G)).subgroupOf L)
    rwa [map_subgroupOf_eq_of_le (inf_le_left : L ⊓ centralizer (A : Set G) ≤ L)] at h
  exact h1.trans h2.symm

omit [Finite G] [Finite G'] in
private theorem mapL_le_mapL_iff {Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ≤ L) :
    mapL E Z₁ ≤ mapL E Z₂ ↔ Z₁ ≤ Z₂ := by
  rw [mapL, mapL, Subgroup.map_le_map_iff_of_injective (embedOf_injective E)]
  constructor
  · intro h x hx
    exact Subgroup.mem_subgroupOf.mp
      (h (x := ⟨x, h₁ hx⟩) (Subgroup.mem_subgroupOf.mpr hx))
  · intro h x hx
    exact Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

private theorem isU3_or_isL2_bar2_derInf8_mapL_iff {A : Subgroup G} (hA : A ≤ L) {n : ℕ} :
    (IsU3 (Bar2 (F08.DerInf8 (L' ⊓ centralizer (mapL E A : Set G')))) 2 ∨
      IsL2 (Bar2 (F08.DerInf8 (L' ⊓ centralizer (mapL E A : Set G')))) n) ↔
    (IsU3 (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) 2 ∨
      IsL2 (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) n) := by
  obtain ⟨φ⟩ := nonempty_bar2_derInf8_mapL E hA
  constructor
  · rintro (h | h)
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ.symm h)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ.symm h)
  · rintro (h | h)
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ h)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ h)

private theorem isL2_bar2_derInf8_mapL_iff {B : Subgroup G} (hB : B ≤ L) {n : ℕ} :
    IsL2 (Bar2 (F08.DerInf8 (L' ⊓ centralizer (mapL E B : Set G')))) n ↔
      IsL2 (Bar2 (F08.DerInf8 (L ⊓ centralizer (B : Set G)))) n := by
  obtain ⟨φ⟩ := nonempty_bar2_derInf8_mapL E hB
  exact ⟨fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ.symm h,
    fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv φ h⟩

theorem notationA8103_mapL_iff {P A : Subgroup G} (hA : A ≤ L) {p n : ℕ} :
    F08.NotationA8103 L' (mapL E P) p n (mapL E A) ↔ F08.NotationA8103 L P p n A := by
  unfold F08.NotationA8103
  rw [card_mapL E hA, mapL_le_mapL_iff E hA, isU3_or_isL2_bar2_derInf8_mapL_iff E hA,
    pRank_inf_centralizer_mapL E hA p]

theorem notationB8103_mapL_iff {P B : Subgroup G} (hB : B ≤ L) {n : ℕ} :
    F08.NotationB8103 L' (mapL E P) n (mapL E B) ↔ F08.NotationB8103 L P n B := by
  unfold F08.NotationB8103 F08.KOf8103
  rw [card_mapL E hB, mapL_le_mapL_iff E hB, isL2_bar2_derInf8_mapL_iff E hB]

omit [Finite G] [Finite G'] in
theorem mapL_map_conj {B : Subgroup G} (hB : B ≤ L) (x : L) :
    mapL E (B.map (MulAut.conj (x : G)).toMonoidHom) =
      (mapL E B).map (MulAut.conj ((E x : L') : G')).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp hz
    refine ⟨embedOf E ⟨b, hB hb⟩, Subgroup.mem_map_of_mem (embedOf E)
      (Subgroup.mem_subgroupOf.mpr hb), ?_⟩
    change MulAut.conj ((E x : L') : G') (embedOf E ⟨b, hB hb⟩) = embedOf E z
    rw [MulAut.conj_apply]
    have hz' : z = x * ⟨b, hB hb⟩ * x⁻¹ := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hbz.symm
    rw [hz', map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨bL, hbL, hbw⟩ := Subgroup.mem_map.mp hw
    rw [← hbw]
    refine ⟨x * bL * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [Subgroup.mem_map]
      refine ⟨(bL : G), Subgroup.mem_subgroupOf.mp hbL, ?_⟩
      change MulAut.conj (x : G) (bL : G) = ((x * bL * x⁻¹ : L) : G)
      rw [MulAut.conj_apply]
      simp [Subgroup.coe_mul]
    · change embedOf E (x * bL * x⁻¹) =
        MulAut.conj ((E x : L') : G') (embedOf E bL)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      rfl

omit [Finite G] [Finite G'] in
theorem mapL_mapL_symm {A' : Subgroup G'} (hA' : A' ≤ L') : mapL E (mapL E.symm A') = A' := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hza⟩ := Subgroup.mem_map.mp hz
    have hz' : z = E.symm a := Subtype.ext hza.symm
    rw [hz']
    simpa [embedOf] using Subgroup.mem_subgroupOf.mp ha
  · intro y hy
    refine ⟨E.symm ⟨y, hA' hy⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (embedOf E.symm)
        (Subgroup.mem_subgroupOf.mpr hy)
    · simp [embedOf]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
