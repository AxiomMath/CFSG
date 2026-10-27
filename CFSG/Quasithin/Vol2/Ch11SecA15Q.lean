module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Vol2.Ch11SecA15MS

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem reducedAggregate_le_centralizer (X : Subgroup G) :
    reducedAggregate X ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
  obtain ⟨-, -, hZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  rintro _ ⟨x', hx', rfl⟩
  obtain ⟨-, h2, -⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hZ hx')
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg Subtype.val (h2 k hk)

theorem fsuV_le_centralizer_pCoreOf_LT (h : Hyp11 G T L I n) :
    fsuV T I ≤ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
  (fsuV_le_reducedAggregate h).trans (reducedAggregate_le_centralizer _)

theorem fsuV_le_L (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) : fsuV T I ≤ L := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  rw [← hirr.2.2.2.1, Subgroup.commutator_le]
  intro v hv l hl
  have hvL : v ∈ Subgroup.normalizer (L : Set G) := fsuV_le_normalizer_L h hv
  rw [commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hvL l).mp hl) (L.inv_mem hl)

theorem pCoreOf_msG0_le_pCoreOf_LT (h : Hyp11 G T L I n) :
    pCoreOf 2 (L ⊔ ROf T L V₁) ≤ pCoreOf 2 (L ⊔ T) := by
  have hle : L ⊔ ROf T L V₁ ≤ L ⊔ T := sup_le_sup_left (ROf_le_T h) L
  exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (msG0_le_normalizer h))

theorem fsuV_le_pCoreOf_msG0 (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    fsuV T I ≤ pCoreOf 2 (L ⊔ ROf T L V₁) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((fsuV_le_L h1102 h).trans le_sup_left)
    (sup_le (L_le_normalizer_fsuV h) ((ROf_le_T h).trans (T_le_normalizer_fsuV T I)))
    (isPGroup_fsuV h)

omit [Finite G] in
theorem L_le_normalizer_c134Q :
    L ≤ Subgroup.normalizer (c134Q (L ⊔ ROf T L V₁) L : Set G) := by
  have h1 : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ ROf T L V₁) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  unfold c134Q
  rw [Subgroup.map_commutator, (Subgroup.mem_normalizer_iff_map_conj_eq).mp (h1 hl),
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hl)]

omit [Finite G] in
theorem c134Q_le_pCoreOf_msG0 :
    c134Q (L ⊔ ROf T L V₁) L ≤ pCoreOf 2 (L ⊔ ROf T L V₁) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem fsuV_le_c134Q (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    fsuV T I ≤ c134Q (L ⊔ ROf T L V₁) L := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  rw [← hirr.2.2.2.1]
  exact Subgroup.commutator_mono (fsuV_le_pCoreOf_msG0 h1102 h) le_rfl

theorem fsuV_le_centerOf_c134Q (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    fsuV T I ≤ centerOf (c134Q (L ⊔ ROf T L V₁) L) := by
  refine le_inf (fsuV_le_c134Q h1102 h) ?_
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : q ∈ pCoreOf 2 (L ⊔ T) :=
    pCoreOf_msG0_le_pCoreOf_LT h (c134Q_le_pCoreOf_msG0 hq)
  exact Subgroup.mem_centralizer_iff.mp (fsuV_le_centralizer_pCoreOf_LT h hv) q hq'

theorem pCoreOf_msG0_le_S (h : Hyp11 G T L I n) :
    pCoreOf 2 (L ⊔ ROf T L V₁) ≤ T ⊓ (L ⊔ ROf T L V₁) :=
  CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_inf_msG0 h)

theorem centerOf_S_le_centralizer_c134Q (h : Hyp11 G T L I n) :
    centerOf (T ⊓ (L ⊔ ROf T L V₁)) ≤
      Subgroup.centralizer (c134Q (L ⊔ ROf T L V₁) L : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact Subgroup.mem_centralizer_iff.mp hz.2 q
    (pCoreOf_msG0_le_S h (c134Q_le_pCoreOf_msG0 hq))

theorem centerOf_S_le_pCoreOf_msG0 (h : Hyp11 G T L I n) :
    centerOf (T ⊓ (L ⊔ ROf T L V₁)) ≤ pCoreOf 2 (L ⊔ ROf T L V₁) := by
  intro z hz
  refine charTwo_msG0 h ⟨hz.1.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hz.2 k (pCoreOf_msG0_le_S h hk)

theorem commutator_mem_centerOf_c134Q (h : Hyp11 G T L I n) {z l : G}
    (hz : z ∈ centerOf (T ⊓ (L ⊔ ROf T L V₁))) (hl : l ∈ L) :
    l * z * l⁻¹ * z⁻¹ ∈ centerOf (c134Q (L ⊔ ROf T L V₁) L) := by
  refine ⟨?_, ?_⟩
  · have := Subgroup.commutator_mem_commutator hl (centerOf_S_le_pCoreOf_msG0 h hz)
    rw [Subgroup.commutator_comm, commutatorElement_def] at this
    exact this
  · have hzQ := centerOf_S_le_centralizer_c134Q h hz
    rw [Subgroup.mem_centralizer_iff] at hzQ
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hq' : l⁻¹ * q * l ∈ c134Q (L ⊔ ROf T L V₁) L := by
      have := (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_c134Q (L.inv_mem hl)) q).mp hq
      simpa using this
    have h1 := hzQ q hq
    have h2 := hzQ _ hq'
    calc q * (l * z * l⁻¹ * z⁻¹) = l * ((l⁻¹ * q * l) * z) * l⁻¹ * z⁻¹ := by group
      _ = l * (z * (l⁻¹ * q * l)) * l⁻¹ * z⁻¹ := by rw [h2]
      _ = l * z * l⁻¹ * (q * z⁻¹) := by group
      _ = l * z * l⁻¹ * (z⁻¹ * q) := by
          rw [show q * z⁻¹ = z⁻¹ * q from by
            calc q * z⁻¹ = z⁻¹ * (z * q) * z⁻¹ := by group
              _ = z⁻¹ * (q * z) * z⁻¹ := by rw [h1]
              _ = z⁻¹ * q := by group]
      _ = l * z * l⁻¹ * z⁻¹ * q := by group

theorem commute_pCoreOf_L (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ centerOf (T ⊓ (L ⊔ ROf T L V₁))) {k : G} (hk : k ∈ pCoreOf 2 L) :
    k * z = z * k := by
  have hkS : k ∈ T ⊓ (L ⊔ ROf T L V₁) :=
    ⟨(CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h) hk).1,
      Subgroup.mem_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 L hk)⟩
  exact Subgroup.mem_centralizer_iff.mp hz.2 k hkS

end CFSG.Quasithin.Vol2.Ch11.SecA
