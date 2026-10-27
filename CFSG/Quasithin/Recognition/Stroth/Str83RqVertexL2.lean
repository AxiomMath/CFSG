module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexBase
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.Walter.Bender1970.S2.AutEven

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {L T : Subgroup G}

theorem commutator_mem_pCoreOf_of_odd_of_l2 {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf k))
    (hcent : ∀ x ∈ T, ⁅k, x⁆ ∈ pCoreOf 2 L) : ∀ l ∈ L, ⁅k, l⁆ ∈ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := hL2
  let α : MulAut (oTwoQuot ↥L) :=
    CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl ⟨k, hk⟩
  have hαodd : Odd (orderOf α) := by
    refine Odd.of_dvd_nat hodd ?_
    have h := orderOf_map_dvd
      (CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl)
      (⟨k, hk⟩ : ↥(Subgroup.normalizer (L : Set G)))
    simpa [α, Subgroup.orderOf_coe] using h
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  let β : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    MulAut.congr e α
  have hβodd : Odd (orderOf β) := by
    rw [show orderOf β = orderOf α from (MulAut.congr e).orderOf_eq α]
    exact hαodd
  let S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScoe : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))) =
      (P : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom := rfl
  have hfixS : ∀ y ∈ (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))), β y = y := by
    intro y hy
    rw [hScoe] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hP] at hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hfix : α (QuotientGroup.mk x) = QuotientGroup.mk x :=
      (conjModPCore_mk_eq_mk_iff hk x).mpr (hcent (x : G) hxT)
    simpa [β, MulAut.congr_apply] using congrArg e hfix
  have hβ1 : β = 1 := CFSG.Walter.psl2_even_mulAut_eq_one hf β hβodd S hfixS
  have hα1 : α = 1 := (MulAut.congr e).injective (by simpa [β, map_one] using hβ1)
  intro l hl
  have hker : k ∈ (CFSG.GroupTheory.conjModPCore 2 L
      (Subgroup.normalizer (L : Set G)) le_rfl).ker.map
        (Subgroup.normalizer (L : Set G)).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩, ?_, rfl⟩
    exact MonoidHom.mem_ker.mpr (by simpa [α] using hα1)
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L
    (Subgroup.normalizer (L : Set G)) le_rfl).mp hker
  simpa [commutatorElement_def] using hcomm.2 l hl

theorem le_sup_pCoreOf_of_sylow_ne_of_l2 {T' X : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (hne : T ≠ T') (h : T ≤ X ⊔ pCoreOf 2 L) (h' : T' ≤ X ⊔ pCoreOf 2 L) :
    L ≤ X ⊔ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := hL2
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  obtain ⟨P', hP'⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT'
  have hneBar : (P : Subgroup (oTwoQuot ↥L)) ≠ (P' : Subgroup (oTwoQuot ↥L)) := by
    intro hEq
    exact hne (map_oTwoQuot_injective_of_isSylowTwoOf hT hT'
      (by simpa only [hP, hP'] using hEq))
  let S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  let S' : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScoe : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))) =
      (P : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom := rfl
  have hS'coe : (S' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))) =
      (P' : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom := rfl
  have hSne : S ≠ S' := by
    intro hSS
    apply hneBar
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    calc
      (P : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom = (S : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) := hScoe.symm
      _ = (S' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
            (GaloisField 2 f))) := by rw [hSS]
      _ = (P' : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom := hS'coe
  have htop : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))) ⊔
      (S' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 f))) = ⊤ :=
    CFSG.Quasithin.St84.psl2_sylow_two_sup_eq_top (f := f) (by omega) hSne
  have hbarTop : (P : Subgroup (oTwoQuot ↥L)) ⊔ (P' : Subgroup (oTwoQuot ↥L)) = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective]
    rw [← hScoe, ← hS'coe]
    exact htop
  let Y : Subgroup G := (X ⊔ pCoreOf 2 L) ⊓ L
  have hTY : T ≤ Y := le_inf h hT.1
  have hT'Y : T' ≤ Y := le_inf h' hT'.1
  have hPle : (P : Subgroup (oTwoQuot ↥L)) ≤ (Y.subgroupOf L).map π := by
    rw [hP]
    exact Subgroup.map_mono (Subgroup.comap_mono hTY)
  have hP'le : (P' : Subgroup (oTwoQuot ↥L)) ≤ (Y.subgroupOf L).map π := by
    rw [hP']
    exact Subgroup.map_mono (Subgroup.comap_mono hT'Y)
  have hsupLe : (P : Subgroup (oTwoQuot ↥L)) ⊔ (P' : Subgroup (oTwoQuot ↥L)) ≤
      (Y.subgroupOf L).map π := sup_le hPle hP'le
  have hIm : (Y.subgroupOf L).map π = ⊤ := le_antisymm le_top (hbarTop ▸ hsupLe)
  exact (le_sup_pCoreOf_iff_map_subgroupOf_eq_top (L := L) (X := X)).2 hIm

end CFSG.Quasithin.Stroth
