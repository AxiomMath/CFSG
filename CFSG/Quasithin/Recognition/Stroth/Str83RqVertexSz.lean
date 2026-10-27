module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexBase
public import CFSG.RankThree.PartTwo.KFacts.AutOddFixOmega
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {L T : Subgroup G}

theorem commutator_mem_pCoreOf_of_odd_of_sz {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf k))
    (hcent : ∀ x ∈ T, x * x ∈ pCoreOf 2 L → ⁅k, x⁆ ∈ pCoreOf 2 L) :
    ∀ l ∈ L, ⁅k, l⁆ ∈ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := hSz
  let α : MulAut (oTwoQuot ↥L) :=
    CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl ⟨k, hk⟩
  have hαodd : Odd (orderOf α) := by
    refine Odd.of_dvd_nat hodd ?_
    have h := orderOf_map_dvd
      (CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl)
      (⟨k, hk⟩ : ↥(Subgroup.normalizer (L : Set G)))
    simpa [α, Subgroup.orderOf_coe] using h
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  have hfix : ∀ z ∈ (P : Subgroup (oTwoQuot ↥L)), z ^ 2 = 1 → α z = z := by
    intro z hz hz2
    rw [hP] at hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hxx : (x : G) * (x : G) ∈ pCoreOf 2 L := by
      have h1 : ((x ^ 2 : ↥L) : oTwoQuot ↥L) = 1 := by
        simpa using hz2
      have h2 : (x : ↥L) ^ 2 ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
      have h3 := (F1.mem_pCore_iff_coe (x ^ 2 : ↥L)).mp h2
      simpa [Subgroup.coe_pow, pow_two] using h3
    exact (conjModPCore_mk_eq_mk_iff hk x).mpr (hcent (x : G) hxT hxx)
  have hα1 : α = 1 :=
    CFSG.RankThree.PartTwo.KFacts.eq_one_of_odd_of_fix_omega_sz (X := oTwoQuot ↥L)
      (a := a) ha e P α hαodd hfix
  intro l hl
  have hker : k ∈ (CFSG.GroupTheory.conjModPCore 2 L
      (Subgroup.normalizer (L : Set G)) le_rfl).ker.map
        (Subgroup.normalizer (L : Set G)).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩, ?_, rfl⟩
    exact MonoidHom.mem_ker.mpr (by simpa [α] using hα1)
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L
    (Subgroup.normalizer (L : Set G)) le_rfl).mp hker
  simpa [commutatorElement_def] using hcomm.2 l hl

theorem le_sup_pCoreOf_of_sylow_ne_of_sz
    {T' X : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (hne : T ≠ T') (h : ∀ x ∈ T, x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L)
    (h' : ∀ x ∈ T', x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L) :
    L ≤ X ⊔ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := hSz
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  obtain ⟨P', hP'⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT'
  have hneBar : (P : Subgroup (oTwoQuot ↥L)) ≠ (P' : Subgroup (oTwoQuot ↥L)) := by
    intro hEq
    exact hne (map_oTwoQuot_injective_of_isSylowTwoOf hT hT'
      (by simpa only [hP, hP'] using hEq))
  have hPne : P ≠ P' := by
    intro hEq
    exact hneBar (by rw [hEq])
  have hB : fusionBenderBorel (oTwoQuot ↥L) (2 ^ (2 * a + 1)) 2 :=
    fusionBenderBorel_of_mulEquiv_sz (L := oTwoQuot ↥L) ha e
  have hgen : sylowCenter (P : Subgroup (oTwoQuot ↥L)) ⊔
      sylowCenter (P' : Subgroup (oTwoQuot ↥L)) = ⊤ := by
    simpa [sylowCenter] using
      CFSG.LocalAnalysis.WeakClosure81.inf_centralizer_sup_inf_centralizer_eq_top
        (Q := oTwoQuot ↥L) (a := a) ha e hPne
  let Y : Subgroup G := (X ⊔ pCoreOf 2 L) ⊓ L
  have hZl : sylowCenter (P : Subgroup (oTwoQuot ↥L)) ≤ (Y.subgroupOf L).map π := by
    intro z hz
    have hzP : z ∈ (P : Subgroup (oTwoQuot ↥L)) := (mem_sylowCenter.mp hz).1
    have hz2 : z ^ 2 = 1 := (benderBorel_sylowCenter hB P).2.1 z hz
    rw [hP] at hzP
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hzP
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hxx : (x : G) * (x : G) ∈ pCoreOf 2 L := by
      have h1 : ((x ^ 2 : ↥L) : oTwoQuot ↥L) = 1 := by
        simpa using hz2
      have h2 : (x : ↥L) ^ 2 ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
      have h3 := (F1.mem_pCore_iff_coe (x ^ 2 : ↥L)).mp h2
      simpa [Subgroup.coe_pow, pow_two] using h3
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨h (x : G) hxT hxx, x.2⟩
  have hZ'l : sylowCenter (P' : Subgroup (oTwoQuot ↥L)) ≤ (Y.subgroupOf L).map π := by
    intro z hz
    have hzP : z ∈ (P' : Subgroup (oTwoQuot ↥L)) := (mem_sylowCenter.mp hz).1
    have hz2 : z ^ 2 = 1 := (benderBorel_sylowCenter hB P').2.1 z hz
    rw [hP'] at hzP
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hzP
    have hxT : (x : G) ∈ T' := Subgroup.mem_subgroupOf.mp hx
    have hxx : (x : G) * (x : G) ∈ pCoreOf 2 L := by
      have h1 : ((x ^ 2 : ↥L) : oTwoQuot ↥L) = 1 := by
        simpa using hz2
      have h2 : (x : ↥L) ^ 2 ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
      have h3 := (F1.mem_pCore_iff_coe (x ^ 2 : ↥L)).mp h2
      simpa [Subgroup.coe_pow, pow_two] using h3
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨h' (x : G) hxT hxx, x.2⟩
  have hIm : (Y.subgroupOf L).map π = ⊤ := by
    have hsup : sylowCenter (P : Subgroup (oTwoQuot ↥L)) ⊔
        sylowCenter (P' : Subgroup (oTwoQuot ↥L)) ≤ (Y.subgroupOf L).map π :=
      sup_le hZl hZ'l
    exact le_antisymm le_top (hgen ▸ hsup)
  exact (le_sup_pCoreOf_iff_map_subgroupOf_eq_top (L := L) (X := X)).2 hIm

end CFSG.Quasithin.Stroth
