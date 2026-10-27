module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem isSimpleGroup_of_isType429
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X] (h : IsType429 X) : IsSimpleGroup X := by
  rcases h with ⟨p, e, hp, he, ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩⟩ | hA | hM | hM | hJ
  · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact φ.isSimpleGroup
  · by_cases hq2 : p ^ e = 2
    · exfalso
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq2
      have hs := Sec13.isSolvable_projSU_two
      have hsolv : IsSolvable X :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.not_isSolvable X hsolv
    · haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (n := 3) (p := p) (f := e)
        ⟨Fact.out, he, le_rfl, fun h => hq2 (Prod.mk.inj h).2⟩
      exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := hA
    haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := hM
    haveI : IsSimpleGroup Blueprint.NativeSporadic.M12 :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := hM
    haveI : IsSimpleGroup Blueprint.NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := hJ
    haveI : IsSimpleGroup Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact φ.isSimpleGroup

@[expose] def NoCommNormalPair3 (X : Type*) [Group X] : Prop :=
  ∀ N₁ N₂ : Subgroup X, N₁.Normal → N₂.Normal → (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) →
    ∀ a ∈ N₁, a ≠ 1 → a ^ 3 = 1 → ∀ b ∈ N₂, b ≠ 1 → b ^ 3 = 1 → False

theorem noCommNormalPair3_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoCommNormalPair3 X) : NoCommNormalPair3 Y := by
  intro N₁ N₂ h₁ h₂ hc a ha ha1 ha3 b hb hb1 hb3
  refine h (N₁.comap e.toMonoidHom) (N₂.comap e.toMonoidHom) (h₁.comap _) (h₂.comap _) ?_
    (e.symm a) ?_ ?_ ?_ (e.symm b) ?_ ?_ ?_
  · intro x hx y hy
    apply e.injective
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  · change e (e.symm a) ∈ N₁
    rwa [MulEquiv.apply_symm_apply]
  · intro h1
    apply ha1
    rw [← e.apply_symm_apply a, h1, map_one]
  · rw [← map_pow, ha3, map_one]
  · change e (e.symm b) ∈ N₂
    rwa [MulEquiv.apply_symm_apply]
  · intro h1
    apply hb1
    rw [← e.apply_symm_apply b, h1, map_one]
  · rw [← map_pow, hb3, map_one]

theorem noCommNormalPair3_of_simple {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X)) : NoCommNormalPair3 X := by
  intro N₁ N₂ h₁ h₂ hc a ha ha1 ha3 b hb hb1 hb3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := CFSG.pCore 2 X with hNdef
  haveI hNn : N.Normal := CFSG.pCore_normal
  haveI := hs
  have hM : ∀ M : Subgroup X, M.Normal → ∀ c ∈ M, c ≠ 1 → c ^ 3 = 1 →
      M.map (QuotientGroup.mk' N) = ⊤ := by
    intro M hMn c hc hc1 hc3
    haveI : (M.map (QuotientGroup.mk' N)).Normal :=
      hMn.map _ (QuotientGroup.mk'_surjective N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' N)) with h | h
    · exfalso
      have hmem : QuotientGroup.mk' N c ∈ M.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hc
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hc1 (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hmem hc3)
    · exact h
  have hT₁ := hM N₁ h₁ a ha ha1 ha3
  have hT₂ := hM N₂ h₂ b hb hb1 hb3
  have hcomm : ∀ u w : X ⧸ N, u * w = w * u := by
    intro u w
    have hu : u ∈ N₁.map (QuotientGroup.mk' N) := hT₁ ▸ Subgroup.mem_top u
    have hw : w ∈ N₂.map (QuotientGroup.mk' N) := hT₂ ▸ Subgroup.mem_top w
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    rw [← map_mul, ← map_mul, hc u' hu' w' hw']
  exact Group.IsPerfect.not_isMulCommutative (X ⧸ N) ⟨⟨hcomm⟩⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
