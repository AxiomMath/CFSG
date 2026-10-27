module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Module

theorem ggQ2s08d_coxeter_facts_of_pair {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (h6 : ∀ i j, i ≠ j → M.coxeter i j ≠ 6) (i j : M.Λ) (hij : i ≠ j)
    (hpair : LinearIndependent (ZMod 3) ![M.coroot i, M.coroot j]) :
    (ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j)) ^ M.coxeter i j =
      1 ∧
      ggLin (p := 3) M.model (M.simple i) ≠ ggLin (p := 3) M.model (M.simple j) ∧
      (M.coxeter i j = 2 →
        ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j) =
          ggLin (p := 3) M.model (M.simple j) * ggLin (p := 3) M.model (M.simple i)) ∧
      (M.coxeter i j ≠ 2 →
        ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j) ≠
          ggLin (p := 3) M.model (M.simple j) * ggLin (p := 3) M.model (M.simple i)) := by
  have hα : ∀ k, M.root k (M.coroot k) = (2 : ZMod 3) := fun k => by
    rw [M.pairing k k, M.isCartan.1 k]
    norm_num
  have hlin : ∀ k, ggLin (p := 3) M.model (M.simple k) = reflection (hα k) := fun k =>
    ggLin_eq_reflection M.model (hα k) (M.simple_apply k)
  have hpair' := LinearIndependent.pair_iff.mp hpair
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hlin i, hlin j]
    exact isLiftable_reflection_of_intCartan M.isCartan M.coroot M.root hα M.pairing i j
  ·
    rw [hlin i, hlin j]
    intro heq
    have h := congrArg (fun T : M.V ≃ₗ[ZMod 3] M.V => T (M.coroot i)) heq
    rw [reflection_apply, reflection_apply, hα i] at h
    have h2 : (2 : ZMod 3) • M.coroot i +
        (-(M.root j (M.coroot i))) • M.coroot j = 0 := by
      have h1 := h
      rw [sub_eq_add_neg, sub_eq_add_neg] at h1
      have h' : (2 : ZMod 3) • M.coroot i =
          M.root j (M.coroot i) • M.coroot j :=
        neg_inj.mp (add_left_cancel h1)
      calc (2 : ZMod 3) • M.coroot i + (-(M.root j (M.coroot i))) • M.coroot j
          = M.root j (M.coroot i) • M.coroot j +
              (-(M.root j (M.coroot i))) • M.coroot j :=
              congrArg (fun z => z + (-(M.root j (M.coroot i))) • M.coroot j) h'
        _ = 0 := by
            calc M.root j (M.coroot i) • M.coroot j +
                  (-(M.root j (M.coroot i))) • M.coroot j
                = M.root j (M.coroot i) • M.coroot j +
                    -(M.root j (M.coroot i) • M.coroot j) :=
                    congrArg (fun z => M.root j (M.coroot i) • M.coroot j + z)
                      (neg_smul (M.root j (M.coroot i)) (M.coroot j))
              _ = 0 := add_neg_cancel _
    exact absurd (hpair' 2 (-(M.root j (M.coroot i))) h2).1 (by decide)
  ·
    intro hm
    rw [hlin i, hlin j]
    have hCs : M.cartan i j = 0 ∧ M.cartan j i = 0 := by
      rcases M.isCartan.2 i j hij with ⟨hm2, h1, h2⟩ | ⟨hm3, -, -⟩ | ⟨hm4, -, -, -⟩ |
        ⟨hm6, -, -, -⟩
      · exact ⟨h1, h2⟩
      · rw [hm] at hm3; norm_num at hm3
      · rw [hm] at hm4; norm_num at hm4
      · rw [hm] at hm6; norm_num at hm6
    have hCij : M.root i (M.coroot j) = 0 := by rw [M.pairing i j, hCs.1, Int.cast_zero]
    have hCji : M.root j (M.coroot i) = 0 := by rw [M.pairing j i, hCs.2, Int.cast_zero]
    ext w
    rw [reflection_mul_reflection_apply' (hα i) (hα j) w,
      reflection_mul_reflection_apply' (hα j) (hα i) w, hCij, hCji]
    module
  ·
    intro hm
    rw [hlin i, hlin j]
    have ha : M.root i (M.coroot j) ≠ 0 := by
      rcases M.isCartan.2 i j hij with ⟨hm2, -, -⟩ | ⟨hm3, h1, -⟩ | ⟨hm4, hprod, -, -⟩ |
        ⟨hm6, -, -, -⟩
      · exact absurd hm2 hm
      · rw [M.pairing i j, h1]; decide
      · intro ha0
        have h2 : M.root i (M.coroot j) * M.root j (M.coroot i) = (2 : ZMod 3) := by
          rw [M.pairing i j, M.pairing j i, ← Int.cast_mul, hprod]
          decide
        rw [ha0, zero_mul] at h2
        exact absurd h2 (by decide)
      · exact absurd hm6 (h6 i j hij)
    intro heq
    have h := congrArg (fun T : M.V ≃ₗ[ZMod 3] M.V => T (M.coroot j)) heq
    have hL : (reflection (hα i) * reflection (hα j)) (M.coroot j)
        = -M.coroot j + M.root i (M.coroot j) • M.coroot i := by
      rw [reflection_mul_reflection_apply' (hα i) (hα j) (M.coroot j), hα j]
      module
    have hR : (reflection (hα j) * reflection (hα i)) (M.coroot j)
        = -M.coroot j - M.root i (M.coroot j) • M.coroot i +
            (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j := by
      rw [reflection_mul_reflection_apply' (hα j) (hα i) (M.coroot j), hα j]
      module
    rw [hL, hR] at h
    have hzero : (2 * M.root i (M.coroot j)) • M.coroot i +
        (-(M.root i (M.coroot j) * M.root j (M.coroot i))) • M.coroot j = 0 := by
      have h1 : -M.coroot j + M.root i (M.coroot j) • M.coroot i
          = -M.coroot j + (-(M.root i (M.coroot j) • M.coroot i) +
              (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j) := by
        simpa only [sub_eq_add_neg, add_assoc] using h
      have h2 : M.root i (M.coroot j) • M.coroot i
          = -(M.root i (M.coroot j) • M.coroot i) +
              (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j :=
        add_left_cancel h1
      have h3 : (2 * M.root i (M.coroot j)) • M.coroot i
          = (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j := by
        rw [two_mul, add_smul]
        nth_rewrite 1 [h2]
        abel
      calc (2 * M.root i (M.coroot j)) • M.coroot i +
            (-(M.root i (M.coroot j) * M.root j (M.coroot i))) • M.coroot j
          = (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j +
              (-(M.root i (M.coroot j) * M.root j (M.coroot i))) • M.coroot j :=
                congrArg (fun z => z +
                  (-(M.root i (M.coroot j) * M.root j (M.coroot i))) • M.coroot j) h3
        _ = 0 := by
            calc (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j +
                  (-(M.root i (M.coroot j) * M.root j (M.coroot i))) • M.coroot j
                = (M.root i (M.coroot j) * M.root j (M.coroot i)) • M.coroot j +
                    -((M.root i (M.coroot j) * M.root j (M.coroot i)) •
                      M.coroot j) :=
                      congrArg (fun z =>
                        (M.root i (M.coroot j) * M.root j (M.coroot i)) •
                          M.coroot j + z)
                        (neg_smul (M.root i (M.coroot j) * M.root j (M.coroot i))
                          (M.coroot j))
              _ = 0 := add_neg_cancel _
    have h2a : 2 * M.root i (M.coroot j) = 0 := (hpair' _ _ hzero).1
    exact ha ((mul_eq_zero.mp h2a).resolve_left (by decide))

theorem ggQ2s08d_coxeter_facts {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hind : LinearIndependent (ZMod 3) M.coroot)
    (h6 : ∀ i j, i ≠ j → M.coxeter i j ≠ 6) (i j : M.Λ) (hij : i ≠ j) :
    (ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j)) ^ M.coxeter i j =
      1 ∧
      ggLin (p := 3) M.model (M.simple i) ≠ ggLin (p := 3) M.model (M.simple j) ∧
      (M.coxeter i j = 2 →
        ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j) =
          ggLin (p := 3) M.model (M.simple j) * ggLin (p := 3) M.model (M.simple i)) ∧
      (M.coxeter i j ≠ 2 →
        ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple j) ≠
          ggLin (p := 3) M.model (M.simple j) * ggLin (p := 3) M.model (M.simple i)) := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  refine ggQ2s08d_coxeter_facts_of_pair M h6 i j hij ?_
  have hcomp : (M.coroot ∘ ![i, j]) = ![M.coroot i, M.coroot j] := by
    funext k
    fin_cases k <;> rfl
  have h1 := hind.comp ![i, j] hinj
  rwa [hcomp] at h1

end CFSG.StandardType

end
