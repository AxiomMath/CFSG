module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevel
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockSup

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_sylow {S P : Subgroup G} (hS : IsSylowTwoOf S P) : pCoreOf 2 P ≤ S := by
  have hsub : S ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    hS.1.trans (localGroup_le_normalizer_pCoreOf 2 P)
  have hsup : IsPGroup 2 ↥(S ⊔ pCoreOf 2 P) :=
    hS.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 P) hsub
  have hle : S ⊔ pCoreOf 2 P ≤ P := sup_le hS.1 (pCoreOf_le 2 P)
  have := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _ hle hsup le_sup_left
  exact le_sup_right.trans this

theorem borel_carrier {L S₀ : Subgroup G} {P : Fin 2 → Subgroup G} (hlie : LieLevel L S₀ P)
    (hS₀ : IsSylowTwoOf S₀ L) :
    IsCarrier (L ⊓ Subgroup.normalizer (S₀ : Set G)) S₀ := by
  have hSB : S₀ ≤ L ⊓ Subgroup.normalizer (S₀ : Set G) := le_inf hS₀.1 Subgroup.le_normalizer
  have hsyl : IsSylowTwoOf S₀ (L ⊓ Subgroup.normalizer (S₀ : Set G)) :=
    isSylowTwoOf_of_le_of_le hS₀ hSB inf_le_left
  have hsyl0 : IsSylowTwoOf S₀ (P 0) :=
    isSylowTwoOf_of_le_of_le hS₀ (hlie.S_le 0) (hlie.le_L 0)
  refine ⟨hSB, hS₀.2.1, inf_le_right, fun x hx k hk => ?_, fun x hx hc => ?_⟩
  · exact mem_of_isSylow_of_normal hsyl inf_le_right hx hk
  · have hx0 : x ∈ P 0 := hlie.norm_le 0 hx
    have hQ := pCoreOf_le_sylow hsyl0
    refine hQ (hlie.charTwo 0 ⟨hx0, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩)
    exact (hc h (hQ hh)).symm

theorem borel_of_solvable {X MZ L S₀ : Subgroup G} {P : Fin 2 → Subgroup G}
    (hlie : LieLevel L S₀ P) (hMZX : MZ ≤ X) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hS₀ : IsSylowTwoOf S₀ L) (hS₀M : S₀ ≤ MZ)
    (h2 : ∀ K : Subgroup G, K ≤ X → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
      MZ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ MZ)
    (hsolv : Group.IsSolvable ↥(MZ ⊓ L)) : IsBorelIn L (MZ ⊓ L) := by
  have hMB : MZ ⊓ L ≤ L ⊓ Subgroup.normalizer (S₀ : Set G) :=
    fun x hx => ⟨hx.2, hlie.solv _ (le_inf hS₀M hS₀.1) inf_le_right hsolv hx⟩
  have hcar := borel_carrier hlie hS₀
  obtain ⟨hch, hodd⟩ := hcar.charTwo_odd
  have hnorm : MZ ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer (S₀ : Set G) : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨l, hl, n, hn, rfl⟩ := frattini hMZX hXL hS₀ hS₀M hm
    refine mul_mem (Subgroup.le_normalizer (hMB hl)) ?_
    exact mem_normalizer_inf (hXL (hMZX hn.1)) (Subgroup.le_normalizer hn.2)
  have hBM := h2 _ (inf_le_left.trans hLX) hodd hnorm hch
  refine ⟨S₀, hS₀, le_antisymm hMB fun x hx => ⟨hBM hx, hx.1⟩⟩

theorem maxParabolic_of_nonsolvable {X MZ L S₀ : Subgroup G} {P : Fin 2 → Subgroup G}
    (hlie : LieLevel L S₀ P) (hMZX : MZ ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hS₀ : IsSylowTwoOf S₀ L) (hS₀M : S₀ ≤ MZ) (hLnot : ¬ L ≤ MZ)
    (h2 : ∀ K : Subgroup G, K ≤ X → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
      MZ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ MZ)
    (hLX : L ≤ X) (hns : ¬ Group.IsSolvable ↥(MZ ⊓ L)) : IsMaxParabolic2 L (MZ ⊓ L) := by
  have hMLne : MZ ⊓ L ≠ L := fun h => hLnot (h ▸ inf_le_left)
  obtain ⟨j, hjk, hΛ⟩ := hlie.nonsolv (MZ ⊓ L) (le_inf hS₀M hS₀.1) inf_le_right hMLne hns
  have hMj : MZ ⊓ L ≤ P j := (hjk j).2 rfl
  have hnormP : MZ ≤ Subgroup.normalizer (P j : Set G) := by
    intro m hm
    obtain ⟨l, hl, n, hn, rfl⟩ := frattini hMZX hXL hS₀ hS₀M hm
    exact mul_mem (Subgroup.le_normalizer (hMj hl))
      (mem_normalizer_of_nonsolvable hlie hMZX hXL hMj hns hn)
  obtain ⟨hch, hodd⟩ := (leviCent_carrier (hlie.charTwo j) (hlie.hall j)).charTwo_odd
  have hKM : leviCent (P j) ≤ MZ :=
    h2 _ ((leviCent_le _).trans ((hlie.le_L j).trans hLX)) hodd
      (hnormP.trans (le_normalizer_leviCent _)) hch
  have hPM : P j ≤ MZ := by
    intro g hg
    obtain ⟨a, ha, c, hc, rfl⟩ := hlie.split j g hg
    exact MZ.mul_mem (hΛ.trans inf_le_left ha) (hKM hc)
  have hEq : MZ ⊓ L = P j := le_antisymm hMj (le_inf hPM (hlie.le_L j))
  rw [hEq]
  refine ⟨⟨hlie.le_L j, S₀, hS₀, hlie.norm_le j⟩, hlie.ne_L j, fun Q hQ hQL hPQ => ?_⟩
  exact (hlie.maxl j Q hPQ hQ.1).resolve_right hQL

theorem main_of_lie {X MZ L S₀ : Subgroup G} {P : Fin 2 → Subgroup G}
    (hlie : LieLevel L S₀ P) (hMZX : MZ ≤ X) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hS₀ : IsSylowTwoOf S₀ L) (hS₀M : S₀ ≤ MZ)
    (hLnot : ¬ L ≤ MZ)
    (h2 : ∀ K : Subgroup G, K ≤ X → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
      MZ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ MZ) :
    IsBorelIn L (MZ ⊓ L) ∨ IsMaxParabolic2 L (MZ ⊓ L) := by
  by_cases hsolv : Group.IsSolvable ↥(MZ ⊓ L)
  · exact Or.inl (borel_of_solvable hlie hMZX hLX hXL hS₀ hS₀M h2 hsolv)
  · exact Or.inr (maxParabolic_of_nonsolvable hlie hMZX hXL hS₀ hS₀M hLnot h2 hLX hsolv)

end CFSG.Quasithin.GoldMLB
