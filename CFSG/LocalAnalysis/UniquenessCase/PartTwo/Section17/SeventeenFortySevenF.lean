module

public import CFSG.GroupTheory.CommutatorCentralizerInNormal
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3TorusInvolution
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20n
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s17_47_isSylowOf_inf (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L := by
  exact (D.sylowG.of_le le_sup_right le_top).inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer hTL)

theorem s17_47_pCoreOf_le_inf (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) : pCoreOf 2 L ≤ D.T ⊓ L :=
  s16c7_pCoreOf_le_of_isSylowOf (s17_47_isSylowOf_inf D hTL)

theorem s17_47_sylowBar_index (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) : ¬ 2 ∣ (uc22p20iSylowBar D L).index := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (D.T ⊓ L).subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (s17_47_pCoreOf_le_inf D hTL this)
  unfold uc22p20iSylowBar
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 (s17_47_isSylowOf_inf D hTL)).2.2

theorem s17_47_mem_sylowBar_iff (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) (y : ↥L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈ uc22p20iSylowBar D L ↔ (y : G) ∈ D.T ⊓ L := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (z⁻¹ * y : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker, map_mul, map_inv, hzy]
      exact inv_mul_cancel _
    have hmem : (((z⁻¹ * y : ↥L)) : G) ∈ pCoreOf 2 L := ⟨_, hzy', rfl⟩
    have h3 := s17_47_pCoreOf_le_inf D hTL hmem
    have hz' : (z : G) ∈ D.T ⊓ L := Subgroup.mem_subgroupOf.1 hz
    have : (y : G) = (z : G) * (((z⁻¹ * y : ↥L)) : G) := by simp
    rw [this]
    exact (D.T ⊓ L).mul_mem hz' h3
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩

theorem s17_47_ind_sylowBar (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) {t : G} (ht : t ∈ normalizer (L : Set G))
    (htT : t ∈ D.T) (x : Bar2 L) :
    x ∈ uc22p20iSylowBar D L ↔ uc22p20uInd L t ht x ∈ uc22p20iSylowBar D L := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have e : uc22p20uInd L t ht (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht l).1 l.2⟩ := rfl
  rw [e, s17_47_mem_sylowBar_iff D hTL, s17_47_mem_sylowBar_iff D hTL]
  exact Subgroup.mem_normalizer_iff.1 (uc22p20u_T_le_normalizer_inf D hTL htT) (l : G)

theorem s17_47_mk_mem_normalizer_sylowBar (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) {l : ↥L}
    (hl : (l : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l * QuotientGroup.mk' (CFSG.pCore 2 ↥L) y *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l)⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) (l * y * l⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e, s17_47_mem_sylowBar_iff D hTL, s17_47_mem_sylowBar_iff D hTL]
  have := Subgroup.mem_normalizer_iff.1 hl (y : G)
  simpa using this

theorem s17_47_exists_T0_of_borel {D : Data G} {L : Subgroup G} {n r : ℕ}
    (hTL : D.T ≤ normalizer (L : Set G)) (hSL : IsSL3 (Bar2 L) n) (hn : 3 ≤ n)
    (hri : ∀ i : ℕ, n ∣ 2 * i → r ∣ 2 ^ i - 1)
    {E : Subgroup G} (hEL : E ≤ L) (hEN : E ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G))
    (hEexp : ∀ e ∈ E, e ^ r = 1) (hperm : Permutes E D.T) :
    ∃ T₀ : Subgroup G, T₀ ≤ D.T ∧ D.T ≤ normalizer (T₀ : Set G) ∧
      E ≤ normalizer (T₀ : Set G) ∧
        ∀ v ∈ D.T, ∀ w ∈ D.T, v ^ 2 = 1 → w ^ 2 = 1 → v ∉ T₀ → w ∉ T₀ → v * w⁻¹ ∈ T₀ := by
  have hTS : D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    uc22p20u_T_le_normalizer_inf D hTL
  have hcoe : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G) :=
    uc22p20n_coe_sup_of_perm hperm
  refine ⟨commutatorCentralizerIn D.T (D.T ⊓ L) E hTS, commutatorCentralizerIn_le _ _ _ hTS,
    le_normalizer_commutatorCentralizerIn hTS hEN (le_normalizer_sup_inf_of_permutes hEL hTL hcoe),
    le_normalizer_commutatorCentralizerIn_of_le hTS inf_le_left hEN, ?_⟩
  intro v hv w hw hv2 hw2 hvT₀ hwT₀
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let U : Sylow 2 (Bar2 L) :=
    (uc22p20i_sylowBar_isPGroup D).toSylow (s17_47_sylowBar_index D hTL)
  have hUcoe : (U : Subgroup (Bar2 L)) = uc22p20iSylowBar D L :=
    IsPGroup.toSylow_coe (uc22p20i_sylowBar_isPGroup D) (s17_47_sylowBar_index D hTL)
  have hmem : ∀ y : ↥L, π y ∈ (U : Subgroup (Bar2 L)) ↔ (y : G) ∈ D.T ⊓ L := by
    intro y; rw [hUcoe]; exact s17_47_mem_sylowBar_iff D hTL y
  have hbN : ∀ e (he : e ∈ E),
      π ⟨e, hEL he⟩ ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    intro e he; rw [hUcoe]; exact s17_47_mk_mem_normalizer_sylowBar D hTL (hEN he)
  have hbr : ∀ e (he : e ∈ E), (π ⟨e, hEL he⟩) ^ r ∈ (U : Subgroup (Bar2 L)) := by
    intro e he
    have h1 : (⟨e, hEL he⟩ : ↥L) ^ r = 1 := Subtype.ext (by simpa using hEexp e he)
    rw [← map_pow, h1, map_one]
    exact one_mem _
  have hsq : ∀ (u : G) (hu : u ∈ D.T), u ^ 2 = 1 →
      uc22pwIndHom L D.T hTL ⟨u, hu⟩ * uc22pwIndHom L D.T hTL ⟨u, hu⟩ = 1 := by
    intro u hu hu2
    rw [← map_mul, ← map_one (uc22pwIndHom L D.T hTL)]
    congr 1
    exact Subtype.ext (by simpa [pow_two] using hu2)
  have hUinv : ∀ (u : G) (hu : u ∈ D.T) (x : Bar2 L), x ∈ (U : Subgroup (Bar2 L)) ↔
      uc22pwIndHom L D.T hTL ⟨u, hu⟩ x ∈ (U : Subgroup (Bar2 L)) := by
    intro u hu x
    rw [hUcoe]
    exact s17_47_ind_sylowBar D hTL (hTL hu) hu x
  have hact : ∀ (u : G) (hu : u ∈ D.T) (e : G) (he : e ∈ L),
      uc22pwIndHom L D.T hTL ⟨u, hu⟩ (π ⟨e, he⟩) =
        π ⟨u * e * u⁻¹, (Subgroup.mem_normalizer_iff.1 (hTL hu) e).1 he⟩ := fun _ _ _ _ => rfl
  have hne : ∀ (u : G) (hu : u ∈ D.T), u ∉ commutatorCentralizerIn D.T (D.T ⊓ L) E hTS →
      ∃ b ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)),
        b ^ r ∈ (U : Subgroup (Bar2 L)) ∧
          uc22pwIndHom L D.T hTL ⟨u, hu⟩ b * b⁻¹ ∉ (U : Subgroup (Bar2 L)) := by
    intro u hu huT₀
    have hex : ∃ e ∈ E, ⁅u, e⁆ ∉ D.T ⊓ L := by
      by_contra hcon
      refine huT₀ ((mem_commutatorCentralizerIn hTS).2 ⟨hu, fun e he => ?_⟩)
      by_contra h'
      exact hcon ⟨e, he, h'⟩
    obtain ⟨e, he, hce⟩ := hex
    refine ⟨π ⟨e, hEL he⟩, hbN e he, hbr e he, fun hcon => hce ?_⟩
    rw [hact, ← map_inv, ← map_mul, hmem] at hcon
    simpa [commutatorElement_def] using hcon
  have hK := fun (b : Bar2 L) (hb : b ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)))
      (hb' : b ^ r ∈ (U : Subgroup (Bar2 L))) =>
    uc22pwI3_involution_borel_action hSL.1 hn hSL.2 U hri
      (hsq v hv hv2) (hsq w hw hw2) (hUinv v hv) (hUinv w hw) (hne v hv hvT₀) (hne w hw hwT₀)
      hb hb'
  refine mul_inv_mem_commutatorCentralizerIn hTS hv hw hv2 hw2 (fun e he => ?_)
  have h2 := hK _ (hbN e he) (hbr e he)
  rw [hact, hact, ← map_inv, ← map_mul, hmem] at h2
  simpa using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
