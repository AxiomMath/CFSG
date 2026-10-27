module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
public import CFSG.Quasithin.H13.NQCatLieOverRank2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.NQCat (SolvOver)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_map_eq_of_solvable {L X : Subgroup G} (hX : Group.IsSolvable ↥X)
    (Q : Sylow 2 ↥L) (hQX : (Q : Subgroup ↥L).map L.subtype ≤ X)
    (hSO : SolvOver (BarInf L) ((Q : Subgroup ↥L).map (piInf L))) {b : G}
    (hbX : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G)) :
    ((Q : Subgroup ↥L).map (piInf L)).map (inducedBarInfAutHom L ⟨b, hbL⟩).toMonoidHom =
      (Q : Subgroup ↥L).map (piInf L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX
  have : Group.IsSolvable ↥(X ⊓ L) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  rw [← uc22s2114_rhoInf_eq]
  let ψ : ↥(X ⊓ L) →* BarInf L := (piInf L).comp (Subgroup.inclusion inf_le_right)
  have hWs : Group.IsSolvable ↥ψ.range := Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hmem : ∀ x : ↥L, (x : G) ∈ X → piInf L x ∈ ψ.range := fun x hx => ⟨⟨x, hx, x.2⟩, rfl⟩
  have hUW : (Q : Subgroup ↥L).map (piInf L) ≤ ψ.range := by
    rintro _ ⟨q, hq, rfl⟩
    exact hmem q (hQX ⟨q, hq, rfl⟩)
  have hWN := hSO _ hUW hWs
  have hPW : ((Q : Subgroup ↥L).map (piInf L)).map (rhoInf L ⟨b, hbL⟩).toMonoidHom ≤
      ψ.range := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    show rhoInf L ⟨b, hbL⟩ (piInf L q) ∈ ψ.range
    rw [rhoInf_mk]
    refine hmem _ ?_
    rw [rhoInf_mk_coe]
    exact (mem_normalizer_iff.1 hbX _).1 (hQX ⟨q, hq, rfl⟩)
  let S : Sylow 2 (BarInf L) :=
    Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L))
  have hP : IsPGroup 2
      ↥(((Q : Subgroup ↥L).map (piInf L)).map (rhoInf L ⟨b, hbL⟩).toMonoidHom) :=
    (Q.isPGroup'.map _).map _
  have hle : ((Q : Subgroup ↥L).map (piInf L)).map (rhoInf L ⟨b, hbL⟩).toMonoidHom ≤
      (Q : Subgroup ↥L).map (piInf L) :=
    calc _ = _ ⊓ normalizer (S : Set (BarInf L)) := (inf_eq_left.2 (hPW.trans hWN)).symm
      _ = _ ⊓ (S : Subgroup (BarInf L)) := hP.inf_normalizer_sylow S
      _ ≤ _ := inf_le_right
  exact CFSG.Quasithin.H13.L32A.C.SkPf.map_eq_of_forall_mem fun u hu =>
    hle (mem_map_of_mem _ hu)

theorem uc22s2114_exists_map_eq_of_permutes {L T B : Subgroup G} (hTL : IsSylowOf 2 (T ⊓ L) L)
    (hT : IsPGroup 2 T) (hBodd : Odd (Nat.card B)) (hBc : IsMulCommutative B)
    (hperm : Permutes B T)
    (hSO : ∀ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ → SolvOver (BarInf L) U) {b : G}
    (hb : b ∈ B) (hbL : b ∈ normalizer (L : Set G)) :
    ∃ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ ∧
      U.map (inducedBarInfAutHom L ⟨b, hbL⟩).toMonoidHom = U := by
  obtain ⟨Q, hQ⟩ := hTL
  refine ⟨(Q : Subgroup ↥L).map (piInf L), isSylowTwoOf_map_piInf L Q,
    uc22s2114_map_eq_of_solvable (uc22p2214_isSolvable_sup hBodd hBc hT hperm) Q ?_
      (hSO _ (isSylowTwoOf_map_piInf L Q)) (le_normalizer (mem_sup_left hb)) hbL⟩
  rw [hQ]
  exact inf_le_left.trans le_sup_right

theorem uc22s2114_exists_map_eq_of_solvOver {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hSO : ∀ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ → SolvOver (BarInf L) U) {b : G}
    (hb : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G)) :
    ∃ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ ∧
      U.map (inducedBarInfAutHom L ⟨b, hbL⟩).toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hB0c, -, -, -, -, -, -, -, hperm, -⟩ := c.hB0
  exact uc22s2114_exists_map_eq_of_permutes (uc22p2214_isSylowOf_inf D.sylowM hL.1)
    (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1
    (uc22p22f_odd_card_B { c with B := c.B0, hB := c.hB0, hle := le_rfl }) hB0c hperm hSO hb hbL

theorem uc22s2114_exists_of_solvOver {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hSO : ∀ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ → SolvOver (BarInf L) U) {b : G}
    (hb : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hbr : b ^ r = 1)
    (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1)
    (hin : ∀ α : MulAut (BarInf L), α ^ r = 1 →
      α ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    ∃ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ ∧
      ∃ y ∈ normalizer (U : Set (BarInf L)), y ≠ 1 ∧ y ^ r = 1 := by
  obtain ⟨U, hU, hαU⟩ := uc22s2114_exists_map_eq_of_solvOver c hL hSO hb hbL
  have hαr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := Subtype.ext (by simpa using hbr)
    rw [this, map_one]
  exact ⟨U, hU, uc22s2114_exists_of_inner (center_barInf_eq_bot hL.2.2) hαU (hin _ hαr) hb1 hαr⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
