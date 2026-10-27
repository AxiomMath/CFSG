module

public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Quasithin.H13.NQCatParabolicSp4
public import CFSG.Quasithin.H13.KGFact22Tor

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.QuasithinUnique

@[expose] def SolvOver (Y : Type) [Group Y] (U : Subgroup Y) : Prop :=
  ∀ X : Subgroup Y, U ≤ X → Group.IsSolvable ↥X → X ≤ normalizer (U : Set Y)

theorem SolvOver.map {Y Y' : Type} [Group Y] [Group Y'] {U : Subgroup Y} (h : SolvOver Y U)
    (e : Y ≃* Y') : SolvOver Y' (U.map e.toMonoidHom) := by
  intro X' hUX' hX'
  have hUX : U ≤ X'.map e.symm.toMonoidHom := by
    rw [← Vol2Native.A312L.map_map_symm e U]
    exact map_mono hUX'
  have hsol : Group.IsSolvable ↥(X'.map e.symm.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := (X'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toMonoidHom)
      (MulEquiv.surjective _)
  have h1 := map_mono (f := e.toMonoidHom) (h _ hUX hsol)
  have h2 := Vol2Native.A312L.map_map_symm e.symm X'
  rw [MulEquiv.symm_symm] at h2
  rwa [h2, map_equiv_normalizer_eq] at h1

theorem exists_conj_map_eq {Y : Type} [Group Y] [Finite Y] {U₀ U : Subgroup Y}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    ∃ g : Y, U₀.map (MulAut.conj g).toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, rfl⟩ := KG22.exists_sylow_of_isSylowTwoOf hU₀
  obtain ⟨P, rfl⟩ := KG22.exists_sylow_of_isSylowTwoOf hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₀ P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  rfl

theorem solvOver_of_sylow {Y₀ Y : Type} [Group Y₀] [Group Y] [Finite Y] {U₀ : Subgroup Y₀}
    (h : SolvOver Y₀ U₀) (hU₀ : IsSylowTwoOf U₀ ⊤) (e : Y₀ ≃* Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : SolvOver Y U := by
  have : Finite Y₀ := Finite.of_equiv _ e.symm.toEquiv
  have hU₁ : IsSylowTwoOf (U₀.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU₀.2.1.map _, ?_⟩
    have h1 := hU₀.2.2
    rw [show (U₀.subgroupOf ⊤).index = U₀.index from relIndex_top_right _] at h1
    rwa [show ((U₀.map e.toMonoidHom).subgroupOf ⊤).index = (U₀.map e.toMonoidHom).index from
      relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, index_map_equiv]
  obtain ⟨g, rfl⟩ := exists_conj_map_eq hU₁ hU
  exact (h.map e).map (MulAut.conj g)

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem exists_finset_card_four_of_card {K : Type} [Finite K] {k : ℕ} (hk : 2 ≤ k)
    (hK : Nat.card K = 2 ^ k) : ∃ s : Finset K, s.card = 4 :=
  exists_finset_card_four (by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem solvOver_projectiveSL (hK4 : ∃ s : Finset K, s.card = 4) :
    SolvOver (projectiveSL 3 K) (projUnitriangular 3 K) := by
  intro X hUX hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := X.comap (LinearFlag.proj 3 K) with hA
  have hUA : unitriangular 3 K ≤ A := fun u hu => hUX (mem_map_of_mem _ hu)
  have hcomm : ∀ a b : ↥((LinearFlag.proj 3 K).subgroupComap X).ker, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K :=
      proj_eq_one_iff.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))
    have hb' : (b : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K :=
      proj_eq_one_iff.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
    obtain ⟨c, -, hc⟩ := ha'
    obtain ⟨d, -, hd⟩ := hb'
    refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
    change ((a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (b : Matrix _ _ K) =
      (b : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K)
    rw [hc, hd]
    exact (Matrix.scalar_commute (d : K) (fun r => Commute.all _ r) _).eq.symm
  have hkS : Group.IsSolvable ↥((LinearFlag.proj 3 K).subgroupComap X).ker :=
    Group.isSolvable_of_comm hcomm
  have hAS : Group.IsSolvable ↥A :=
    Group.isSolvable_of_ker_le_range ((LinearFlag.proj 3 K).subgroupComap X).ker.subtype
      ((LinearFlag.proj 3 K).subgroupComap X) (by rw [range_subtype])
  have hAB := SL3.le_upperTriangular_of_isSolvable hK4 hUA hAS
  rw [normalizer_projUnitriangular 2,
    ← map_comap_eq_self_of_surjective (proj_surjective 3 K) X]
  exact map_mono hAB

theorem solvOver_projSp (hK4 : ∃ s : Finset K, s.card = 4) :
    SolvOver (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))
      (projUnipotent 2 K) := by
  intro X hUX hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUA : unipotent 2 K ≤ X.comap (SymplecticFlag.proj 2 K) := fun u hu =>
    hUX (mem_map_of_mem _ hu)
  have hle : (X.comap (SymplecticFlag.proj 2 K)).map (SymplecticFlag.proj 2 K) ≤ X :=
    map_comap_le _ _
  have h1 :
      Group.IsSolvable ↥((X.comap (SymplecticFlag.proj 2 K)).map (SymplecticFlag.proj 2 K)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hAS : Group.IsSolvable ↥(X.comap (SymplecticFlag.proj 2 K)) :=
    Group.isSolvable_of_surjective (f := ((X.comap (SymplecticFlag.proj 2 K)).equivMapOfInjective
      (SymplecticFlag.proj 2 K) proj_injective_charTwo).symm.toMonoidHom) (MulEquiv.surjective _)
  have hAB := Sp4.le_borelSubgroup_of_isSolvable hK4 hUA hAS
  rw [normalizer_projUnipotent 2 (by norm_num),
    ← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X]
  exact map_mono hAB

@[expose] def LieOvergroupFactRank2Exc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ k : ℕ, 2 ≤ k ∧ (IsG2 2 k S ∨ Is3D4 2 k S ∨ Is2F4 k S)) →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      ∀ X : Subgroup S, P ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (P : Set S)

theorem lieOvergroupFactL3Sp4_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 3 2 k S ∨ IsPSp4 2 k S)) →
      ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
        ∀ X : Subgroup S, P ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (P : Set S) := by
  intro S _ _ _ ⟨k, hk, h⟩ P hP
  rcases h with hL | hSp
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hL
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    have hK4 := exists_finset_card_four_of_card hk hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
      hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact solvOver_of_sylow (solvOver_projectiveSL hK4) hU₀
      ((e.trans (statedSLEquivProjectiveSL 3 K)).symm) hP
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hSp
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    have hK4 := exists_finset_card_four_of_card hk hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
      hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact solvOver_of_sylow (solvOver_projSp hK4) hU₀ e.symm hP

theorem lieOvergroupFactRank2_of (hE : LieOvergroupFactRank2Exc) : LieOvergroupFactRank2 := by
  intro S _ _ hs ⟨k, hk, h⟩ P hP X hPX hX
  rcases h with h | h | h | h | h
  · exact lieOvergroupFactL3Sp4_holds S hs ⟨k, hk, Or.inl h⟩ P hP X hPX hX
  · exact lieOvergroupFactL3Sp4_holds S hs ⟨k, hk, Or.inr h⟩ P hP X hPX hX
  · exact hE S hs ⟨k, hk, Or.inl h⟩ P hP X hPX hX
  · exact hE S hs ⟨k, hk, Or.inr (Or.inl h)⟩ P hP X hPX hX
  · exact hE S hs ⟨k, hk, Or.inr (Or.inr h)⟩ P hP X hPX hX

end CFSG.Quasithin.H13.NQCat
