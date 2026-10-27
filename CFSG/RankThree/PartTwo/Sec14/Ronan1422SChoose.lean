module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SRK

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

@[expose] def fam (A : Subgroup G) (c : G) (R K : Subgroup G) : Set (Subgroup G) :=
  {S | S ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ R ≤ S ∧ K ≤ Subgroup.normalizer (S : Set G) ∧
    ∀ u ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ⊓
        Subgroup.normalizer (R : Set G),
      ∃ v ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer (S : Set G),
        ∀ a ∈ A, u * a * u⁻¹ = v * a * v⁻¹}

variable {R : Subgroup G}

theorem Pt.mem_fam_R (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    R ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G)) := by
  obtain ⟨hRL, hR2, hAR, -⟩ := h.R_facts hR
  refine ⟨⟨⟨h.iq R hR2 hAR, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩, le_rfl,
    inf_le_right, fun u hu => ⟨u, hu, fun a _ => rfl⟩⟩

theorem fam_facts {K S : Subgroup G} (hS : S ∈ fam A c R K) :
    IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧ R ≤ S ∧
      K ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨⟨⟨hSQ, -⟩, hSpi⟩, hRS, hKS, -⟩ := hS
  exact ⟨(isPiSubgroup_piOf_iff Nat.prime_two S).mp hSpi, hSQ.1.2.2, hRS, hKS⟩

omit [Finite G] in
theorem mem_normalizer_inf {X Y : Subgroup G} {x : G}
    (hX : x ∈ Subgroup.normalizer (X : Set G)) (hY : x ∈ Subgroup.normalizer (Y : Set G)) :
    x ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) :=
  Late.le_normalizer_inf (Subgroup.zpowers_le.mpr hX) (Subgroup.zpowers_le.mpr hY)
    (Subgroup.mem_zpowers x)

theorem Pt.inf_centralizer_eq (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2))
    {K S : Subgroup G} (hS : S ∈ fam A c R K) :
    S ⊓ Subgroup.centralizer ({c} : Set G) = R := by
  obtain ⟨hRL, -, hAR, hmax⟩ := h.R_facts hR
  obtain ⟨hS2, hAS, hRS, -⟩ := fam_facts hS
  have hAc : A ≤ Subgroup.normalizer (Subgroup.centralizer ({c} : Set G) : Set G) :=
    h.std.toSec13Data.A_le_centralizer.trans Subgroup.le_normalizer
  have hAI : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :
      Set G) := Late.le_normalizer_inf hAS hAc
  have hIL := h.two_le _ inf_le_right hAI (hS2.to_le inf_le_left)
  exact hmax _ hIL (hS2.to_le inf_le_left) hAI (le_inf hRS (hRL.trans h.le_centralizer))

theorem Pt.centralizer_inf_le_normalizer_K (h : Pt A c L)
    (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) {K S : Subgroup G} (hS : S ∈ fam A c R K) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  have hRI := h.inf_centralizer_eq hR hS
  intro x ⟨hxS, hxc⟩
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hRI]
    exact mem_normalizer_inf hxS (Subgroup.le_normalizer hxc)
  exact mem_normalizer_inf (h.cent_le hxc) (mem_normalizer_normalizer hxR)

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
