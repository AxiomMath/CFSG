module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.RootSystem

private theorem levTwoS3a_exists_ratLinear {τ : Tag} (w : WeylGroup τ) :
    ∃ f : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ), Function.Injective f ∧
      ∀ v : Fin τ.rank → ℤ, f (toRat v) = toRat (weylAction (isFiniteType_cartan τ) w v) := by
  let Mz : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    Matrix.of fun i j => weylAction (isFiniteType_cartan τ) w (Pi.single j 1) i
  let Mz' : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    Matrix.of fun i j => weylAction (isFiniteType_cartan τ) w⁻¹ (Pi.single j 1) i
  let M : Matrix (Fin τ.rank) (Fin τ.rank) ℚ := Mz.map (Int.cast : ℤ → ℚ)
  let M' : Matrix (Fin τ.rank) (Fin τ.rank) ℚ := Mz'.map (Int.cast : ℤ → ℚ)
  have hM'M : M' * M = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, M, M', Mz, Mz', Matrix.map_apply,
      Matrix.of_apply]
    have h2 : (∑ k, (weylAction (isFiniteType_cartan τ) w (Pi.single j 1)) k •
        weylAction (isFiniteType_cartan τ) w⁻¹ (Pi.single k 1)) =
        (Pi.single j 1 : Fin τ.rank → ℤ) := by
      calc _ = weylAction (isFiniteType_cartan τ) w⁻¹
              (∑ k, (weylAction (isFiniteType_cartan τ) w (Pi.single j 1)) k •
                (Pi.single k 1 : Fin τ.rank → ℤ)) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
        _ = weylAction (isFiniteType_cartan τ) w⁻¹
              (weylAction (isFiniteType_cartan τ) w (Pi.single j 1)) := by
              congr 1
              rw [← Finset.univ_sum_single
                (weylAction (isFiniteType_cartan τ) w (Pi.single j 1))]
              exact Finset.sum_congr rfl fun k _ => by
                funext i; simp [Pi.single_apply]
        _ = Pi.single j 1 := weylAction_inv_apply_apply (isFiniteType_cartan τ) w (Pi.single j 1)
    have hcoord := congrFun h2 i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hcoord
    rw [show (∑ x, (weylAction (isFiniteType_cartan τ) w⁻¹ (Pi.single x 1) i : ℚ) *
          (weylAction (isFiniteType_cartan τ) w (Pi.single j 1) x : ℚ)) =
        ((∑ k, (weylAction (isFiniteType_cartan τ) w (Pi.single j 1)) k *
          (weylAction (isFiniteType_cartan τ) w⁻¹ (Pi.single k 1)) i : ℤ) : ℚ) by
      push_cast
      exact Finset.sum_congr rfl fun k _ => by ring]
    rw [hcoord]
    split_ifs <;> norm_num
  refine ⟨M.mulVecLin, ?_, ?_⟩
  · intro x y hxy
    have h := congrArg (fun z => M'.mulVec z) hxy
    simp only [Matrix.mulVecLin_apply] at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
    exact h
  · intro v
    have hv : weylAction (isFiniteType_cartan τ) w v =
        ∑ j, v j • weylAction (isFiniteType_cartan τ) w (Pi.single j 1) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsingle : (Pi.single j (v j) : Fin τ.rank → ℤ) = v j • Pi.single j 1 := by
        funext k; simp [Pi.single_apply]
      rw [hsingle, map_smul]
    funext i
    rw [hv]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Mz, Matrix.map_apply,
      Matrix.of_apply, toRat_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem levTwoS3a_rank_smul {τ : Tag} {p : ℕ} {Φ : Set (Fin τ.rank → ℤ)}
    (w : WeylGroup τ)
    (h : ∃ s : Finset (Fin τ.rank → ℤ), (s : Set (Fin τ.rank → ℤ)) ⊆ Φ ∧
      LinearIndependent ℚ (fun v : s => toRat (v : Fin τ.rank → ℤ)) ∧
      3 ≤ s.card ∧ Fintype.card (Fin τ.rank) ≤ s.card + 2 ∧
      (Fintype.card (Fin τ.rank) ≤ s.card + 1 ∨ (p : ℤ) ∣ (τ.cartan).det)) :
    ∃ s' : Finset (Fin τ.rank → ℤ), (s' : Set (Fin τ.rank → ℤ)) ⊆
        weylAction (isFiniteType_cartan τ) w '' Φ ∧
      LinearIndependent ℚ (fun v : s' => toRat (v : Fin τ.rank → ℤ)) ∧
      3 ≤ s'.card ∧ Fintype.card (Fin τ.rank) ≤ s'.card + 2 ∧
      (Fintype.card (Fin τ.rank) ≤ s'.card + 1 ∨ (p : ℤ) ∣ (τ.cartan).det) := by
  obtain ⟨s, hsub, hind, h3, hcard, hdet⟩ := h
  obtain ⟨f, hfinj, hf⟩ := levTwoS3a_exists_ratLinear w
  have hind' : LinearIndependent ℚ
      (fun v : s => toRat (weylAction (isFiniteType_cartan τ) w (v : Fin τ.rank → ℤ))) := by
    have h := hind.map' f (LinearMap.ker_eq_bot.2 hfinj)
    have hfun : (⇑f ∘ fun v : s => toRat (v : Fin τ.rank → ℤ)) =
        (fun v : s => toRat (weylAction (isFiniteType_cartan τ) w (v : Fin τ.rank → ℤ))) := by
      funext v
      exact hf v
    rwa [hfun] at h
  classical
  let s' : Finset (Fin τ.rank → ℤ) := s.image (weylAction (isFiniteType_cartan τ) w)
  let F : s → s' := fun v =>
    ⟨weylAction (isFiniteType_cartan τ) w v.1, Finset.mem_image_of_mem _ v.2⟩
  let G : s' → s := fun x =>
    ⟨weylAction (isFiniteType_cartan τ) w⁻¹ x.1, by
      obtain ⟨v, hv, hvw⟩ := Finset.mem_image.1 x.2
      rw [← hvw, weylAction_inv_apply_apply]
      exact hv⟩
  have hFG : ∀ x : s', F (G x) = x := fun x =>
    Subtype.ext (weylAction_apply_inv_apply (isFiniteType_cartan τ) w x.1)
  have hGinj : Function.Injective G := fun x y hxy => by
    have := congrArg F hxy
    rwa [hFG x, hFG y] at this
  have hind'' : LinearIndependent ℚ (fun v : s' => toRat (v : Fin τ.rank → ℤ)) := by
    have h := hind'.comp G hGinj
    have hfun : ((fun v : s => toRat (weylAction (isFiniteType_cartan τ) w
          (v : Fin τ.rank → ℤ))) ∘ G) = (fun v : s' => toRat (v : Fin τ.rank → ℤ)) := by
      funext x
      simp only [Function.comp_apply]
      have hx := congrArg Subtype.val (hFG x)
      simp only [F] at hx
      rw [hx]
    rwa [hfun] at h
  have hcard' : s'.card = s.card :=
    Finset.card_image_of_injective s (weylAction_apply_injective (isFiniteType_cartan τ) w)
  refine ⟨s', ?_, hind'', ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(G ⟨x, hx⟩).1, hsub (G ⟨x, hx⟩).2, congrArg Subtype.val (hFG ⟨x, hx⟩)⟩
  · rw [hcard']; exact h3
  · rw [hcard']; exact hcard
  · rw [hcard']; exact hdet
theorem levTwoS3a_levTwoData_smul
    {τ : Tag} {p : ℕ} {c c' : Fin τ.rank → ZMod p} {Φ : Set (Fin τ.rank → ℤ)}
    (hd : LevTwoData (isFiniteType_cartan τ) p c Φ) (w : WeylGroup τ)
    (hc : ∀ β, lam c' (weylAction (isFiniteType_cartan τ) w β) = lam c β) :
    LevTwoData (isFiniteType_cartan τ) p c'
      (weylAction (isFiniteType_cartan τ) w '' Φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    ·
      intro β hβ
      obtain ⟨α, hα, rfl⟩ := hβ
      exact isRt_smul (isFiniteType_cartan τ) (hd.isRt α hα) w
    ·
      intro β hβ
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨-α, hd.neg α hα, by simp⟩
    ·
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [rRefl_smul (isFiniteType_cartan τ) (hd.isRt a' ha') w]
      have hcomp : weylAction (isFiniteType_cartan τ) (w * rRefl (isFiniteType_cartan τ) a' * w⁻¹)
          (weylAction (isFiniteType_cartan τ) w b') =
          weylAction (isFiniteType_cartan τ) w
            (weylAction (isFiniteType_cartan τ) (rRefl (isFiniteType_cartan τ) a') b') := by
        rw [weylAction_mul_apply (isFiniteType_cartan τ) (w * rRefl (isFiniteType_cartan τ) a') w⁻¹,
          weylAction_inv_apply_apply,
          weylAction_mul_apply (isFiniteType_cartan τ) w (rRefl (isFiniteType_cartan τ) a')]
      rw [hcomp]
      exact ⟨_, hd.closed a' ha' b' hb', rfl⟩
    ·
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have key : ∀ x y, (fun a b => b ∈ Φ ∧
          form (isFiniteType_cartan τ) (toRat a) (toRat b) ≠ 0) x y →
          (fun a b => b ∈ weylAction (isFiniteType_cartan τ) w '' Φ ∧
            form (isFiniteType_cartan τ) (toRat a) (toRat b) ≠ 0)
            (weylAction (isFiniteType_cartan τ) w x) (weylAction (isFiniteType_cartan τ) w y) := by
        rintro x y ⟨hy, hf⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rwa [form_weylAction]
      have hmap : ∀ {x y : Fin τ.rank → ℤ},
          Relation.ReflTransGen (fun a b => b ∈ Φ ∧
            form (isFiniteType_cartan τ) (toRat a) (toRat b) ≠ 0) x y →
          Relation.ReflTransGen (fun a b => b ∈ weylAction (isFiniteType_cartan τ) w '' Φ ∧
            form (isFiniteType_cartan τ) (toRat a) (toRat b) ≠ 0)
            (weylAction (isFiniteType_cartan τ) w x) (weylAction (isFiniteType_cartan τ) w y) := by
        intro x y hxy
        induction hxy with
        | refl => exact Relation.ReflTransGen.refl
        | tail hab hbc ih => exact Relation.ReflTransGen.tail ih (key _ _ hbc)
      exact hmap (hd.irred a' ha' b' hb')
    ·
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [form_weylAction, form_weylAction]
      exact hd.oneLen a' ha' b' hb'
  ·
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    rw [hc α]
    exact hd.fix α hα
  ·
    intro β hβr hβ0 hconj
    obtain ⟨α, hα, v, hv⟩ := hconj
    obtain ⟨α', hα', rfl⟩ := hα
    have hkey : weylAction (isFiniteType_cartan τ) (w⁻¹ * v * w) α' =
        weylAction (isFiniteType_cartan τ) w⁻¹ β := by
      rw [weylAction_mul_apply (isFiniteType_cartan τ) (w⁻¹ * v) w,
        weylAction_mul_apply (isFiniteType_cartan τ) w⁻¹ v, hv]
    have hroot : IsRt (isFiniteType_cartan τ) (weylAction (isFiniteType_cartan τ) w⁻¹ β) :=
      isRt_smul (isFiniteType_cartan τ) hβr w⁻¹
    have hlam : lam c (weylAction (isFiniteType_cartan τ) w⁻¹ β) = 0 := by
      have h := hc (weylAction (isFiniteType_cartan τ) w⁻¹ β)
      rw [weylAction_apply_inv_apply (isFiniteType_cartan τ) w β] at h
      rw [hβ0] at h
      exact h.symm
    have hmem : weylAction (isFiniteType_cartan τ) w⁻¹ β ∈ Φ :=
      hd.sat _ hroot hlam ⟨α', hα', w⁻¹ * v * w, hkey⟩
    exact ⟨weylAction (isFiniteType_cartan τ) w⁻¹ β, hmem, weylAction_apply_inv_apply _ w β⟩
  ·
    exact levTwoS3a_rank_smul w hd.rank

end CFSG.StandardType.LevTwo
