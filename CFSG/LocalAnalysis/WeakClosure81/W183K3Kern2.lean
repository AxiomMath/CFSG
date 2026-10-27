module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem w183k3_kern2_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem false_of_two_kernels_quasi (h : Assumption131 G Γ VA i)
    {A L₁ L₂ D F : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hL₁G : L₁ ≤ G) (hL₂G : L₂ ≤ G)
    (hq₁ : CFSG.Open.IsQuasisimple ↥L₁) (hq₂ : CFSG.Open.IsQuasisimple ↥L₂)
    (ho₁ : Odd (Nat.card ↥(Subgroup.center ↥L₁)))
    (ho₂ : Odd (Nat.card ↥(Subgroup.center ↥L₂)))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hAn₁ : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (hAn₂ : ∀ a ∈ A, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂)
    (hD : D = A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hF : F = A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD0 : D ≠ ⊥) (hF0 : F ≠ ⊥) (hDF : D ⊓ F = ⊥) (hrank : mOf A D ≤ i) : False := by
  have hDA : D ≤ A := by rw [hD]; exact inf_le_left
  have hDFA : D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
    rw [hD]; exact inf_le_right
  have hFA : F ≤ A := by rw [hF]; exact inf_le_left
  have hFFA : F ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
    rw [hF]; exact inf_le_right
  obtain ⟨⟨f, hfF⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF0
  have hf1' : f ≠ 1 := fun hh => hf1 (Subtype.ext hh)
  have hncF : ∃ y ∈ F, ∃ x ∈ L₁, x * y ≠ y * x := by
    refine ⟨f, hfF, ?_⟩
    by_contra hcon
    have hcent : f ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      by_contra hne
      exact hcon ⟨l, hl, hne⟩
    have hfD : f ∈ D := by
      rw [hD]
      exact ⟨hFA hfF, hcent⟩
    exact hf1' (by
      have : f ∈ D ⊓ F := ⟨hfD, hfF⟩
      rwa [hDF, Subgroup.mem_bot] at this)
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD0
  have hd1' : d ≠ 1 := fun hh => hd1 (Subtype.ext hh)
  have hncD : ∃ y ∈ D, ∃ x ∈ L₂, x * y ≠ y * x := by
    refine ⟨d, hdD, ?_⟩
    by_contra hcon
    have hcent : d ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      by_contra hne
      exact hcon ⟨l, hl, hne⟩
    have hdF : d ∈ F := by
      rw [hF]
      exact ⟨hDA hdD, hcent⟩
    exact hd1' (by
      have : d ∈ D ⊓ F := ⟨hdD, hdF⟩
      rwa [hDF, Subgroup.mem_bot] at this)
  have hYF : ∀ y ∈ F, ∀ x ∈ L₁, y * x * y⁻¹ ∈ L₁ := fun y hy x hx => hAn₁ y (hFA hy) x hx
  have hYD : ∀ y ∈ D, ∀ x ∈ L₂, y * x * y⁻¹ ∈ L₂ := fun y hy x hx => hAn₂ y (hDA hy) x hx
  have hP₁inv : Invariant L₁ (commSub D) := by
    rw [← commSpace_top_eq_commSub D]
    refine invariant_commSpace ?_ (fun _ _ _ _ => trivial)
    intro l hl g hg
    have hlg : l * g = g * l := (Subgroup.mem_centralizer_iff.mp (hDFA hg)) l hl
    have hlgg : l * g * l⁻¹ = g := by rw [hlg, mul_assoc, mul_inv_cancel, mul_one]
    rw [hlgg]; exact hg
  have hP₁fix : commSub D ≤ fixSub F := by
    have hbot : commSpace F (commSub D) = ⊥ :=
      le_bot_iff.mp (calc commSpace F (commSub D) ≤ commSpace A (commSub A) :=
            commSpace_mono hFA (commSub_mono D A hDA)
        _ = ⊥ := h.quadratic A hA)
    intro u hu g hg
    exact (commSpace_eq_bot_iff.mp hbot) g hg u hu
  have hP₁ : commSub D ≤ fixSub L₁ :=
    w183k3_fixSub_le_of_not_centralizes (L := L₁) (Y := F) hq₁ hYF hncF hP₁inv hP₁fix
  have hP₂inv : Invariant L₂ (commSub F) := by
    rw [← commSpace_top_eq_commSub F]
    refine invariant_commSpace ?_ (fun _ _ _ _ => trivial)
    intro l hl g hg
    have hlg : l * g = g * l := (Subgroup.mem_centralizer_iff.mp (hFFA hg)) l hl
    have hlgg : l * g * l⁻¹ = g := by rw [hlg, mul_assoc, mul_inv_cancel, mul_one]
    rw [hlgg]; exact hg
  have hP₂fix : commSub F ≤ fixSub D := by
    have hbot : commSpace D (commSub F) = ⊥ :=
      le_bot_iff.mp (calc commSpace D (commSub F) ≤ commSpace A (commSub A) :=
            commSpace_mono hDA (commSub_mono F A hFA)
        _ = ⊥ := h.quadratic A hA)
    intro u hu g hg
    exact (commSpace_eq_bot_iff.mp hbot) g hg u hu
  have hP₂ : commSub F ≤ fixSub L₂ :=
    w183k3_fixSub_le_of_not_centralizes (L := L₂) (Y := D) hq₂ hYD hncD hP₂inv hP₂fix
  by_cases hzero : commSpace F (fixSub D) = ⊥
  · have hfixDF : fixSub D ≤ fixSub F := by
      intro u hu g hg
      exact (commSpace_eq_bot_iff.mp hzero) g hg u hu
    have hfixDinv : ∀ l ∈ L₁, ∀ u ∈ fixSub D, l u ∈ fixSub D := by
      intro l hl u hu g hg
      have hgl : g * l = l * g := ((Subgroup.mem_centralizer_iff.mp (hDFA hg)) l hl).symm
      calc g (l u) = (g * l) u := (LinearEquiv.mul_apply g l u).symm
        _ = (l * g) u := by rw [hgl]
        _ = l (g u) := LinearEquiv.mul_apply l g u
        _ = l u := by rw [hu g hg]
    have hfixD_L₁ : fixSub D ≤ fixSub L₁ :=
      w183k3_fixSub_le_of_not_centralizes (L := L₁) (Y := F) hq₁ hYF hncF hfixDinv hfixDF
    have hmul : ∀ l ∈ L₁, ∀ l' ∈ L₁, ∀ v : V, l (l' v - v) = l' v - v := by
      intro l hl l' hl' v
      have hmem : l' v - v ∈ fixSub D := by
        intro g hg
        have hgl : g * l' = l' * g :=
          ((Subgroup.mem_centralizer_iff.mp (hDFA hg)) l' hl').symm
        have hgv : g v - v ∈ commSub D := sub_mem_commSub D hg v
        have hfixP : l' (g v - v) = g v - v := hP₁ hgv l' hl'
        have hkey : g (l' v - v) - (l' v - v) = l' (g v - v) - (g v - v) := by
          rw [map_sub, map_sub]
          rw [show g (l' v) = l' (g v) from by
            rw [← LinearEquiv.mul_apply, hgl, LinearEquiv.mul_apply]]
          abel
        exact sub_eq_zero.mp (by rw [hkey, hfixP, sub_self])
      exact hfixD_L₁ hmem l hl
    obtain ⟨a, ha, b, hb, hab⟩ := quasi_exists_noncomm hq₁
    exact hab (w183_mul_comm_of_comp_eq (N := L₁) hmul a ha b hb)
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
    have hwVA : w ∈ VA A := by
      have h1 : commSpace F (fixSub D) ≤ commSpace A (fixSub D) := commSpace_mono hFA le_rfl
      exact h.cond2 A hA D hDA hrank (h1 hw)
    have hwF : w ∈ commSub F := by
      rw [← commSpace_top_eq_commSub F]
      exact commSpace_mono (le_refl F) le_top hw
    have hL₂norm : L₂ ≤ Subgroup.normalizer (A : Set (LGL 2 V)) := fun l hl =>
      h.stabilizer_le_normalizer hA hwVA hw0 (hL₂G hl) (hP₂ hwF l hl)
    have hKL₂ : A ⊓ L₂ ≤ L₂ := inf_le_right
    have hKn : ∀ y ∈ L₂, ∀ k ∈ A ⊓ L₂, y * k * y⁻¹ ∈ A ⊓ L₂ := by
      intro y hy k hk
      refine ⟨?_, ?_⟩
      · show y * k * y⁻¹ ∈ A
        exact (Subgroup.mem_normalizer_iff.mp (hL₂norm hy) k).mp hk.1
      · show y * k * y⁻¹ ∈ L₂
        exact L₂.mul_mem (L₂.mul_mem hy hk.2) (L₂.inv_mem hy)
    haveI : Finite (LGL 2 V) := w183k3_kern2_finite_lgl
    haveI : Finite ↥L₂ := Subtype.finite
    rcases quasi_normal_dichotomy (L := L₂) (K := A ⊓ L₂) hq₂ hKL₂ hKn with hcent | htop
    · have hAL₂bot : A ⊓ L₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hx2 : x ^ (2 ^ 1) = 1 := by
          simpa using (h.isElemAb A hA).2 x hx.1
        exact quasi_centre_two_pow_eq_one ho₂ (hcent hx) hx2
      have hAcent : ∀ a ∈ A, ∀ l ∈ L₂, a * l = l * a := by
        intro a ha l hl
        have hmem : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L₂ := by
          refine ⟨?_, ?_⟩
          · have hlA : l * a⁻¹ * l⁻¹ ∈ A :=
              (Subgroup.mem_normalizer_iff.mp (hL₂norm hl) a⁻¹).mp (A.inv_mem ha)
            rw [show a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) by group]
            exact A.mul_mem ha hlA
          · exact L₂.mul_mem (hAn₂ a ha l hl) (L₂.inv_mem hl)
        have heq : a * l * a⁻¹ * l⁻¹ = 1 := by
          have hmem0 : a * l * a⁻¹ * l⁻¹ ∈ (⊥ : Subgroup (LGL 2 V)) := by
            rw [← hAL₂bot]; exact hmem
          simpa using hmem0
        calc a * l = (a * l * a⁻¹ * l⁻¹) * (l * a) := by group
          _ = l * a := by rw [heq, one_mul]
      have hDF_le : D ≤ F := by
        intro e he
        rw [hF]
        exact ⟨hDA he, Subgroup.mem_centralizer_iff.mpr fun l hl => (hAcent e (hDA he) l hl).symm⟩
      have hmem : d ∈ D ⊓ F := ⟨hdD, hDF_le hdD⟩
      rw [hDF, Subgroup.mem_bot] at hmem
      exact hd1' hmem
    · have hL₂A : L₂ ≤ A := htop ▸ inf_le_left
      obtain ⟨a, ha, b, hb, hab⟩ := quasi_exists_noncomm hq₂
      exact hab ((h.isElemAb A hA).comm (hL₂A ha) (hL₂A hb))

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
