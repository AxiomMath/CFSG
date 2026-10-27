module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open Matrix CFSG.CosetTable
open CFSG.RankThree.LocalRank (aschbacherSolvableCore aschbacherSolvableCore_normal
  solvable_prime_complement_core_characterization)

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

@[expose] noncomputable def toPSL {m : ℕ} (ws : List (List (Fin m × Bool)))
    (g : Fin m → SpecialLinearGroup n K)
    (hrel : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) ∈
      Subgroup.center (SpecialLinearGroup n K)) :
    PG m ws →* ProjectiveSpecialLinearGroup n K :=
  PresentedGroup.toGroup
    (f := fun i => (QuotientGroup.mk (g i) : ProjectiveSpecialLinearGroup n K)) (by
      intro r hr
      have hr' : r ∈ ws.map FreeGroup.mk := hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr'
      have hlift : FreeGroup.lift (fun i => (QuotientGroup.mk (g i) :
          ProjectiveSpecialLinearGroup n K)) =
          (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup n K))).comp
            (FreeGroup.lift g) :=
        FreeGroup.ext_hom _ _ fun i => by simp
      rw [hlift, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hrel w hw)

theorem toPSL_of {m : ℕ} (ws : List (List (Fin m × Bool))) (g : Fin m → SpecialLinearGroup n K)
    (hrel : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) ∈
      Subgroup.center (SpecialLinearGroup n K)) (i : Fin m) :
    toPSL ws g hrel (PresentedGroup.of i) =
      (QuotientGroup.mk (g i) : ProjectiveSpecialLinearGroup n K) :=
  PresentedGroup.toGroup.of _

theorem toPSL_surjective {m : ℕ} (ws : List (List (Fin m × Bool)))
    (g : Fin m → SpecialLinearGroup n K)
    (hrel : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) ∈
      Subgroup.center (SpecialLinearGroup n K))
    (htr : ∀ t : TransvectionStruct n K, t.toSpecialLinearGroup ∈ Subgroup.closure (Set.range g)) :
    Function.Surjective (toPSL ws g hrel) := by
  have htop : Subgroup.closure (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact htr t
  have hle : (Subgroup.closure (Set.range g)).map
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup n K))) ≤
        (toPSL ws g hrel).range := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨PresentedGroup.of i, by rw [toPSL_of]; rfl⟩
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : y ∈ Subgroup.closure (Set.range g) := by
    rw [htop]
    exact Subgroup.mem_top y
  obtain ⟨z, hz⟩ := hle ⟨y, hy, rfl⟩
  exact ⟨z, hz⟩

theorem bijective_toPSL {m : ℕ} (ws : List (List (Fin m × Bool)))
    (g : Fin m → SpecialLinearGroup n K)
    (hrel : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) ∈
      Subgroup.center (SpecialLinearGroup n K))
    (htr : ∀ t : TransvectionStruct n K, t.toSpecialLinearGroup ∈ Subgroup.closure (Set.range g))
    [Finite (PG m ws)]
    (hcard : Nat.card (PG m ws) ≤ Nat.card (ProjectiveSpecialLinearGroup n K)) :
    Function.Bijective (toPSL ws g hrel) :=
  (toPSL_surjective ws g hrel htr).bijective_of_nat_card_le hcard

theorem transvection_natCast {i j : n} (hij : i ≠ j) (k : ℕ) :
    SpecialLinearGroup.transvection hij (k : K) = SpecialLinearGroup.transvection hij 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, SpecialLinearGroup.transvection_add, ih, pow_succ]

end Generic

section Seven

theorem transvection_mem_of_one_mem {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
    (S : Subgroup (SpecialLinearGroup n (ZMod p))) {i j : n} (hij : i ≠ j)
    (h1 : SpecialLinearGroup.transvection hij 1 ∈ S) (c : ZMod p) :
    SpecialLinearGroup.transvection hij c ∈ S := by
  rw [← ZMod.natCast_zmod_val c, transvection_natCast]
  exact S.pow_mem h1 _

theorem card_psl_three_seven :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) = 1876896 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := ZMod 7) (n := 3)
    (by norm_num)
  rw [← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 7)).toEquiv,
    Nat.card_zmod, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num)] at h
  rw [h]
  norm_num

theorem isSimpleGroup_psl_three_seven :
    IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  CFSG.BenderSuzuki.External.huppert_II_6_13 (K := ZMod 7) 3 (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))

@[expose] noncomputable def pslEquivProjSL [Fact (Nat.Prime 7)] :
    ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1) :=
  (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3)
    (GaloisField.equivZmodP 7).toRingEquiv.symm).trans
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSLn 3 (GaloisField 7 1)).symm

theorem nonempty_mulEquiv_psl_of_presented {m : ℕ} (ws : List (List (Fin m × Bool)))
    (g : Fin m → SpecialLinearGroup (Fin 3) (ZMod 7))
    (hrel : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) ∈
      Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7)))
    (htr : ∀ (i j : Fin 3) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij 1 ∈ Subgroup.closure (Set.range g))
    [Finite (PG m ws)] (hcard : Nat.card (PG m ws) ≤ 1876896) :
    Nonempty (PG m ws ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have htr' : ∀ t : TransvectionStruct (Fin 3) (ZMod 7),
      t.toSpecialLinearGroup ∈ Subgroup.closure (Set.range g) := by
    rintro ⟨i, j, hij, c⟩
    rw [TransvectionStruct.toSpecialLinearGroup_mk]
    exact transvection_mem_of_one_mem _ hij (htr i j hij) c
  exact ⟨MulEquiv.ofBijective _ (bijective_toPSL ws g hrel htr'
    (by rw [card_psl_three_seven]; exact hcard))⟩

theorem exists_quot_mulEquiv_projSL_of_presented {G : Type*} [Group G] {m : ℕ}
    (ws : List (List (Fin m × Bool)))
    (hPG : Nonempty (PG m ws ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)))
    (h : Fin m → G) (hh : ∀ w ∈ ws, FreeGroup.lift h (FreeGroup.mk w) = 1) {H : Subgroup G}
    (hH : Subgroup.closure (Set.range h) = H) (hne : H ≠ ⊥) :
    ∃ _ : Fact (Nat.Prime 7), Nonempty (↥H ⧸ aschbacherSolvableCore 3 ↥H ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) := by
  have hf7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨hf7, ?_⟩
  obtain ⟨e⟩ := hPG
  set φ : PG m ws →* G := PresentedGroup.toGroup (f := h) (by
    intro r hr
    have hr' : r ∈ ws.map FreeGroup.mk := hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr'
    exact hh w hw)
  have hrange : φ.range = H := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure, ← hH,
      ← Set.range_comp]
    congr 2
    funext i
    exact PresentedGroup.toGroup.of _
  have := isSimpleGroup_psl_three_seven
  have hntPG : Nontrivial (PG m ws) := e.toEquiv.nontrivial
  have hsimp : IsSimpleGroup (PG m ws) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hker : φ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · exact hk
    · exfalso
      apply hne
      rw [← hrange, eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact (MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)) ▸ Subgroup.one_mem ⊥
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  set eH : PG m ws ≃* ↥H := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hcardH : Nat.card ↥H = 1876896 := by
    rw [← Nat.card_congr eH.toEquiv, Nat.card_congr e.toEquiv, card_psl_three_seven]
  have : Nontrivial ↥H := eH.symm.toEquiv.nontrivial
  have hsH : IsSimpleGroup ↥H :=
    IsSimpleGroup.isSimpleGroup_of_surjective eH.toMonoidHom eH.surjective
  have hθ : aschbacherSolvableCore 3 ↥H = ⊥ := by
    have : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
    obtain ⟨-, -, h3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three
    rcases (aschbacherSolvableCore_normal 3 ↥H).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      rw [ht, Subgroup.card_top, hcardH] at h3
      exact h3 (by norm_num)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans
    ((QuotientGroup.quotientBot).trans (eH.symm.trans (e.trans pslEquivProjSL)))⟩

end Seven

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
