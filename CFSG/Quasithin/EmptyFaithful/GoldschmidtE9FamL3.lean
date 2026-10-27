module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamTr
public import CFSG.Quasithin.EmptyFaithful.T1521SL3EMain
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Core

public section

namespace CFSG.Quasithin.E9.ThreeLin

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.L3Aut CFSG.Quasithin
  CFSG.QuasithinUnique

section Model

variable {K : Type} [Field K]

theorem x12_mem_unitriangular (t : K) : x12 t ∈ unitriangular 3 K := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · fin_cases i <;> simp

theorem x23_mem_unitriangular (t : K) : x23 t ∈ unitriangular 3 K := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · fin_cases i <;> simp

@[expose] def torusHom : Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun := torus
  map_one' := Bor.torus_one
  map_mul' a b := (Bor.torus_mul a b).symm

theorem eq_one_of_fixes_unitri [Finite K] [CharP K 2] {a : Kˣ} (ha : a ≠ 1)
    (β : MulAut (projectiveSL 3 K)) (hU : ∀ u ∈ projUnitriangular 3 K, β u = u)
    (hT : β (proj 3 K (torus a)) = proj 3 K (torus a)) : β = 1 :=
  Core.eq_one_of_fixes_root_torus ha β
    (fun t => hU _ (Subgroup.mem_map_of_mem (proj 3 K) (x12_mem_unitriangular t)))
    (hU _ (Subgroup.mem_map_of_mem (proj 3 K) (x23_mem_unitriangular 1))) hT

end Model

section Transport

variable {G : Type} [Group G]

theorem exists_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 3 2 n ↥L)
    (hP : IsSylowTwoOf P L) :
    ∃ H : Subgroup G, H ≤ L ⊓ Subgroup.normalizer (P : Set G) ∧ Odd (Nat.card H) ∧
      ∀ H₀ : Subgroup G, H₀ ≤ H → H₀.relIndex H ∣ 3 →
        ∀ v ∈ Subgroup.normalizer (L : Set G), (∀ x ∈ P, v * x = x * v) →
          (∀ h ∈ H₀, v * h = h * v) → ∀ l ∈ L, v * l = l * v := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  let φ : ↥L ≃* projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  obtain ⟨g, hg⟩ := Tr.exists_carries hP φ
    (exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num))
  obtain ⟨c, hc⟩ := Tr.exists_unit_cube_ne_one hn hK
  let ψ : Kˣ →* G := (Tr.liftHom L φ g).comp ((proj 3 K).comp torusHom)
  refine ⟨ψ.range, ?_, ?_, fun H₀ hH₀ hidx => ?_⟩
  · rintro _ ⟨s, rfl⟩
    refine ⟨Tr.liftHom_mem L φ g _, Tr.liftHom_mem_normalizer hP.1 hg ?_⟩
    rw [normalizer_projUnitriangular (n := 3) (K := K) 2]
    exact Subgroup.mem_map_of_mem (proj 3 K) (Bor.torus_mem_upperTriangular s)
  · exact (Tr.odd_card_units (by omega) hK).of_dvd_nat (Subgroup.card_range_dvd ψ)
  · have hcomm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
      rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
      rw [← map_mul, ← map_mul, mul_comm s s']
    have h1 : ψ (c ^ 3) ∈ H₀ := by
      rw [map_pow]
      exact pow_three_mem_of_relIndex_dvd_three hcomm hidx _ ⟨c, rfl⟩
    intro v hvN hvP hvH l hl
    refine Tr.centralizes_of_conjAut_eq_one φ g hvN ?_ l hl
    refine eq_one_of_fixes_unitri hc _ (fun u hu => ?_) ?_
    · exact Tr.conjAut_apply_of_commute φ g hvN (hvP _ (Tr.liftHom_mem_of_mem hg hu))
    · exact Tr.conjAut_apply_of_commute φ g hvN (hvH _ h1)

end Transport

end CFSG.Quasithin.E9.ThreeLin

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem nrmE9_L3_big (h37 : A37ForSQTK) (h38 : A38ForSQTK) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    {n : ℕ} (hn : 3 ≤ n) (hty : IsPSL 3 2 n ↥L) : NrmE9 S L := by
  have hJ : thompsonJ S ≤ innerPart1521 S L :=
    e1L3_of h37 h38 G X S L hStd hc hZ ⟨n, by omega, hty⟩
  obtain ⟨H, hHL, hodd, hH⟩ := ThreeLin.exists_torus hn hty hStd.sylowL
  refine nrmE9_of_inner hJ hHL hodd fun H₀ hH₀ hidx => ?_
  have hEa := hH H₀ hH₀ hidx
  refine ⟨fun v _ hvN hvP hvH l hl => hEa v hvN hvP hvH l hl, fun x hx hxH => ?_⟩
  have hxP : ∀ y ∈ S ⊓ L, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hxL : ∀ l ∈ L, x * l = l * x :=
    hEa x (Subgroup.le_normalizer hx.1.2) hxP hxH
  exact ⟨hx.1.2, Subgroup.mem_centralizer_iff.mpr fun l hl => (hxL l hl).symm⟩

end CFSG.Quasithin.E9
