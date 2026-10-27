module

public import CFSG.Quasithin.EmptyFaithful.S153MAR
public import CFSG.Quasithin.EmptyFaithful.S153MSort
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

theorem ffLayer_abstract
    (h51 : AsB51) (hA21 : AsA21SQTKSection)
    {Hg : Type} [Group Hg] [Finite Hg] (hS : SQTKGroup Hg)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : Hg →* MulAut V) (Kg : Subgroup Hg) [Kg.Normal]
    (hq : CFSG.IsQuasisimple (↥Kg ⧸ CFSG.pCore 2 ↥Kg)) (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ Kg) (hnt : ¬ Kg ≤ ρ.ker) (hFF : IsFFModule ρ.range)
    (hK : S153L.KsCover ↥(Kg.map ρ)) :
    FFNatShape (Kg.map ρ) ∧ ffJ ρ.range = Kg.map ρ := by
  obtain ⟨hqL, hLX, hn, h2', hO2⟩ := ar_facts ρ Kg hq hQ h2 hnt
  have hSL : SQTKGroup ↥(Kg.map ρ) := by
    let π : ↥Kg →* ↥(Kg.map ρ) := (ρ.comp Kg.subtype).codRestrict (Kg.map ρ) fun k => ⟨k, k.2, rfl⟩
    have hπ : Function.Surjective π := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hlayer : CFSG.layer ↥(⊤ : Subgroup ↥(Kg.map ρ)) = ⊤ :=
      B5.layer_eq_top_of_quasisimple
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hqL)
    refine hA21 Hg hS Kg ↥(Kg.map ρ) π hπ ⊤ hlayer ?_
    intro x
    have : Subsingleton (↥(Kg.map ρ) ⧸ (⊤ : Subgroup ↥(Kg.map ρ))) :=
      QuotientGroup.subsingleton_quotient_top
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hLJ, hB51⟩ := le_ffJ_of_ffModule hV hLX hn h2' hqL hSL hO2 hFF
  have h1 := (h51 V hV _ _ hB51).1
  have hJX : ffJ ρ.range ≤ ρ.range := B6.ffJ_le _
  have hnJ : ∀ x ∈ ffJ ρ.range, ∀ l ∈ Kg.map ρ, x * l * x⁻¹ ∈ Kg.map ρ :=
    fun x hx l hl => hn x (hJX hx) l hl
  have h2J : ∀ x ∈ ffJ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ Kg.map ρ := fun x hx => h2' x (hJX hx)
  exact ⟨ffNatShape_of_part1 hLJ hnJ h2J h1 hqL hK, eq_of_part1 hLJ hnJ h2J h1 hqL hK⟩

end S153M

end CFSG.Quasithin
