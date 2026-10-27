module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

variable {K : Type} [Field K]

@[expose] noncomputable def ggTBJF4RootDiagModel (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin 4 → ZMod p) →* ↥(adjointGroup Tag.F4 K) :=
  (Subgroup.inclusion (torusGroup_le_adjointGroup_F4 (k := K))).comp
    ((rootDiagUnitHom Tag.F4 K).codRestrict (torusGroup Tag.F4 K)
        fun a => F4_rootDiagUnit_mem_torusGroup a) |>.comp (chevTorusExp Tag.F4 ζ hζ)

theorem ggTBJF4RootDiagModel_apply (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (f : Multiplicative (Fin 4 → ZMod p)) :
    ((ggTBJF4RootDiagModel (K := K) p ζ hζ f : ↥(adjointGroup Tag.F4 K)) :
        ModGL Tag.F4 K) = rootDiagUnit Tag.F4 (ggTBJa p ζ f) := by
  rw [ggTBJF4RootDiagModel]
  rfl

theorem ggTBJF4RootDiagModel_injective (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) : Function.Injective (ggTBJF4RootDiagModel (K := K) p ζ hζ) := by
  intro f g hfg
  have h1 := congrArg (fun x : ↥(adjointGroup Tag.F4 K) => (x : ModGL Tag.F4 K)) hfg
  rw [ggTBJF4RootDiagModel_apply, ggTBJF4RootDiagModel_apply] at h1
  have h2 := (F4_bijOn_rootDiagUnit_pow_val (k := K) hζo).2.1 (Set.mem_univ _)
    (Set.mem_univ _) h1
  exact Multiplicative.ofAdd.injective h2

theorem ggTBJF4RootDiagModel_range (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) :
    (ggTBJF4RootDiagModel (K := K) p ζ hζ).range = TableBF4.torusPow K p := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    rw [TableBF4.mem_torusPow]
    have h1 := ggTBJF4RootDiagModel_apply (K := K) p ζ hζ f
    exact ⟨by rw [h1]; exact F4_rootDiagUnit_mem_torusGroup _,
      by
        apply Subtype.ext
        rw [Subgroup.coe_one, Subgroup.coe_pow, h1]
        exact (F4_rootDiagUnit_pow_val_mem (k := K) hζo (Multiplicative.toAdd f)).2⟩
  · intro hx
    rw [TableBF4.mem_torusPow] at hx
    obtain ⟨v, -, hv⟩ := (F4_bijOn_rootDiagUnit_pow_val (k := K) hζo).2.2
      ⟨hx.1, by rw [← Subgroup.coe_pow, hx.2, OneMemClass.coe_one]⟩
    refine ⟨Multiplicative.ofAdd v, Subtype.ext ?_⟩
    rw [ggTBJF4RootDiagModel_apply]
    show rootDiagUnit Tag.F4 (fun i => ζ ^ (v i).val) = ↑x
    exact hv

end CFSG.StandardType

end
