module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Class
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Cover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Marking
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Setup
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType

theorem stepOne_of_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5) {n : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {z : G} (hzL : z ∈ L) (hzc : ∀ l ∈ L, z * l = l * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    False := by
  have hKd : UnitaryFieldData 2 n K := CFSG.StandardType.TableBU.unitaryFieldData_of_card hK
    (by omega)
  have hcov : LineU.UnitaryCoverAt n 6 K :=
    LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num) (by
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega)
  obtain ⟨φ, hφL, hφs, hφZ, -, hact⟩ := exists_cover_actsAs hKd hcov hL θ hBN hBI
  have hrange : (φ.range : Subgroup G) = L := by
    ext l
    constructor
    · rintro ⟨s, rfl⟩
      exact hφL s
    · intro hl
      obtain ⟨s, hs⟩ := hφs l hl
      exact ⟨s, hs⟩
  have hZ' : ∀ s, (∀ l ∈ φ.range, φ s * l = l * φ s) ↔
      LargeEvenProjMk (unitarySU 2 n K 6) s = 1 := by
    intro s
    rw [← hφZ s]
    constructor
    · intro h l hl
      exact h l (hrange ▸ hl)
    · intro h l hl
      exact h l (hrange ▸ hl)
  have hφinj : Function.Injective φ :=
    injective_of_central_three hKd hpq φ hZ' (hrange ▸ hzL) (fun l hl => hzc l (hrange ▸ hl)) hz1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hcard, hrank⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  refine false_of_injective_cover_class hKd hpq φ hφinj hBs hcard hrank (config_selfCent hcfg)
    (fun S hS' hSp => config_cyclic_sylow hcfg S (hrange ▸ hS') hSp) hxBs hS.2.2.1
    (fun s => ?_) (fun b hb => hact b hb)
  have := Subgroup.mem_centralizer_singleton_iff.mp (hLx (hφL s))
  exact this.symm

end CFSG.StandardType.Line63.H5

end
