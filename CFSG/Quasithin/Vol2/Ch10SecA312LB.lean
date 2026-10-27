module

public import CFSG.Quasithin.Vol2.Ch10SecA312LA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312LF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L (exists_finset_card_four isParabolic2_top_map_equiv
  map_map_symm perfectCoreMapEquiv)

noncomputable def modO2MapEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) (Q : Subgroup X) :
    ModO2 (perfectCore Q) ≃* ModO2 (perfectCore (Q.map f)) :=
  A312.modO2Equiv (((perfectCore Q).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_perfectCore f Q)))

theorem transport {G : Type} [Group G] [Finite G] {L P : Subgroup G} {X : Type} [Group X]
    [Finite X] (e : ↥L ≃* X) (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) :
    IsParabolic2 ⊤ ((P.subgroupOf L).map e.toMonoidHom) ∧
      (P.subgroupOf L).map e.toMonoidHom ≠ ⊤ ∧
      IsPSL 2 2 n (ModO2 (perfectCore ((P.subgroupOf L).map e.toMonoidHom))) := by
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hP.1
  have hpar : IsParabolic2 ⊤ (P.subgroupOf L) :=
    (A312.isParabolic2_top_iff L _).2 (by rw [hmap]; exact hP)
  refine ⟨isParabolic2_top_map_equiv e hpar, fun htop => hPL ?_, ?_⟩
  · have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    rw [← hmap, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [← hmap] at hn
    exact IsPSL.of_mulEquiv ((modO2MapEquiv _ L.subtype_injective _).symm.trans
      (modO2MapEquiv _ e.injective _)) hn

section Linear3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K]

theorem leviField_linear3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) {S : Type} [Group S]
    [Finite S] (π : SpecialLinearGroup (Fin 3) K →* S) (hker : π.ker ≤ scalars 3 K)
    (j : Fin 2) : LeviField f ((Q3 K j).map π) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hinj : ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j), π x = π y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  let eN : ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map π)) :=
    perfectCoreMapEquiv π (Q3 K j) hinj
  by_cases h4 : 4 ≤ Nat.card K
  · have hK4 := exists_finset_card_four h4
    have hf2 : 2 ≤ f := by
      by_contra hlt
      rw [hf] at h4
      have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine Or.inr (Or.inl ⟨K, inferInstance, inferInstance, inferInstance, f, hf, dvd_rfl, hf2,
      (blk3 j).comp eN.symm.toMonoidHom, (blk3_surjective hK4 j).comp eN.symm.surjective,
      fun z => ?_⟩)
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
    have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    have : eN.symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact (map_eq_one_iff _ eN.symm.injective).mp this
  · left
    have hK2 : Nat.card K = 2 := by
      have hpos : 1 < Nat.card K := Finite.one_lt_card
      have : Nat.card K ≠ 3 := by
        intro h3
        rw [hf] at h3
        have h2 : 2 ∣ 3 := h3 ▸ dvd_pow_self 2 (by rintro rfl; simp at h3)
        omega
      omega
    have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
      refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
      norm_num
    have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := (blk3_ker_isPGroup hK j).isNilpotent
      infer_instance
    have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
      Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
        (by rw [Subgroup.range_subtype])
    have hbot := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
    rw [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at hbot
    rw [← map_perfectCore, hbot, Subgroup.map_bot]

theorem dvd_of_isPSL3 {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ}
    (hL : IsPSL 3 2 f ↥L) (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) : f ∣ n := by
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  obtain ⟨hQ, hQtop, hn'⟩ := transport (e.trans (statedSLEquivProjectiveSL 3 K)) hP hPL hn
  obtain ⟨Py, hPy⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
    hPy ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Py
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact dvd_of_leviField hT₀ (linear_three_residual_of_cover ⟨f, hcard⟩ (proj 3 K)
    (proj_surjective 3 K) (ker_proj 3 K).le) (leviField_linear3 hcard (proj 3 K)
    (ker_proj 3 K).le) hQ hQtop hn'

theorem dvd_of_isSL3 {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (hL : IsSL3 (2 ^ f) ↥L) (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) : f ∣ n := by
  obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  obtain ⟨hQ, hQtop, hn'⟩ := transport (φ.trans (specialLinearGroupEquivStatedSL 3 K).symm)
    hP hPL hn
  obtain ⟨Py, hPy⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hPy ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Py
  have hres := linear_three_residual_of_cover ⟨f, hcard⟩ (MonoidHom.id _)
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
  rw [Subgroup.map_id] at hres
  exact dvd_of_leviField hT₀ hres
    (leviField_linear3 hcard (MonoidHom.id _) (by rw [MonoidHom.ker_id]; exact bot_le)) hQ hQtop
    hn'

end Linear3

section Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K]

theorem leviField_sp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    LeviField f ((Q2 K j).map (proj 2 K)) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let eN : ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    perfectCoreMapEquiv (proj 2 K) (Q2 K j) fun x _ y _ h => proj_injective_charTwo h
  refine Or.inr (Or.inl ⟨K, inferInstance, inferInstance, inferInstance, f, hf, dvd_rfl, hf2,
    (blkN j).comp eN.symm.toMonoidHom, (blkN_surjective hK4 j).comp eN.symm.surjective,
    fun z => ?_⟩)
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
  have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : eN.symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ eN.symm.injective).mp this

theorem dvd_of_isPSp4 {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ} (hf2 : 2 ≤ f)
    (hL : IsPSp4 2 f ↥L) (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) : f ∣ n := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  obtain ⟨hQ, hQtop, hn'⟩ := transport e hP hPL hn
  obtain ⟨Py, hPy⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hPy ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Py
  exact dvd_of_leviField hU (symplectic_two_residualOvergroupsAt ⟨f, hcard⟩)
    (leviField_sp4 hcard hf2) hQ hQtop hn'

end Sp4

end CFSG.Quasithin.Vol2.Ch10.A312LF
