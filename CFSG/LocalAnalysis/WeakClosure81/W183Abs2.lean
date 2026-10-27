module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs1
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183_mul_comm_of_comp_eq {N : Subgroup (LGL 2 V)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, ∀ v : V, a (b v - v) = b v - v) :
    ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro a ha b hb
  ext v
  have h1 := hN a ha b hb v
  have h2 := hN b hb a ha v
  rw [map_sub] at h1 h2
  show a (b v) = b (a v)
  calc a (b v) = (b v - v) + a v := by rw [← h1]; abel
    _ = (a v - v) + b v := by abel
    _ = b (a v) := by rw [← h2]; abel

theorem w183_fixSub_le_of_simple {L X : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L] (hXL : X ≤ L)
    (hX : X ≠ ⊥) {P : Submodule (ZMod 2) V} (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P)
    (hfix : P ≤ fixSub X) : P ≤ fixSub L := by
  let N : Subgroup ↥L :=
    { carrier := {x | ∀ p ∈ P, (x : LGL 2 V) p = p}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {a b} ha hb p hp => by
        change ((a : LGL 2 V) * (b : LGL 2 V)) p = p
        rw [LinearEquiv.mul_apply, hb p hp, ha p hp]
      inv_mem' := fun {a} ha p hp => by
        change (a : LGL 2 V)⁻¹ p = p
        calc (a : LGL 2 V)⁻¹ p = (a : LGL 2 V)⁻¹ ((a : LGL 2 V) p) := by rw [ha p hp]
          _ = p := by simp }
  have hNnormal : N.Normal := ⟨fun n hn g => by
    intro p hp
    have hgp : (g : LGL 2 V)⁻¹ p ∈ P := hP (g : LGL 2 V)⁻¹ (L.inv_mem g.2) p hp
    have hn' : (n : LGL 2 V) ((g : LGL 2 V)⁻¹ p) = (g : LGL 2 V)⁻¹ p :=
      hn ((g : LGL 2 V)⁻¹ p) hgp
    calc ((g * n * g⁻¹ : ↥L) : LGL 2 V) p
        = (g : LGL 2 V) ((n : LGL 2 V) ((g : LGL 2 V)⁻¹ p)) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
      _ = (g : LGL 2 V) ((g : LGL 2 V)⁻¹ p) := by rw [hn']
      _ = p := LinearEquiv.apply_symm_apply (g : LGL 2 V) p⟩
  haveI := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exfalso
    apply hX
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxN : (⟨x, hXL hx⟩ : ↥L) ∈ N := fun p hp => hfix hp x hx
    rw [hbot, Subgroup.mem_bot] at hxN
    exact congrArg Subtype.val hxN
  · intro p hp l hl
    have hlN : (⟨l, hl⟩ : ↥L) ∈ N := by rw [htop]; trivial
    exact hlN p hp

theorem w183_fixSub_le_of_not_centralizes {L Y : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L]
    (hY : ∀ y ∈ Y, ∀ x ∈ L, y * x * y⁻¹ ∈ L) (hnc : ∃ y ∈ Y, ∃ x ∈ L, x * y ≠ y * x)
    {P : Submodule (ZMod 2) V} (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P) (hfix : P ≤ fixSub Y) :
    P ≤ fixSub L := by
  let S : Set (LGL 2 V) := {c | ∃ y ∈ Y, ∃ x ∈ L, c = x * y * x⁻¹ * y⁻¹}
  have hSL : Subgroup.closure S ≤ L := (Subgroup.closure_le L).mpr <| by
    rintro c ⟨y, hy, x, hx, rfl⟩
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact L.mul_mem hx (hY y hy x⁻¹ (L.inv_mem hx))
  have hXne : Subgroup.closure S ≠ ⊥ := by
    obtain ⟨y, hy, x, hx, hxy⟩ := hnc
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨x * y * x⁻¹ * y⁻¹, Subgroup.subset_closure ⟨y, hy, x, hx, rfl⟩⟩, ?_⟩
    intro h1
    refine hxy ?_
    have h2 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h2, one_mul]
  have hfixX : P ≤ fixSub (Subgroup.closure S) := by
    intro p hp
    change ∀ c ∈ Subgroup.closure S, c p = p
    intro c₀ hc₀
    refine Subgroup.closure_induction (p := fun z _ => z p = p) ?_ ?_ ?_ ?_ hc₀
    · intro c hc
      obtain ⟨y, hy, x, hx, rfl⟩ := hc
      have hyinv : y⁻¹ p = p := hfix hp y⁻¹ (Y.inv_mem hy)
      have hxinvP : x⁻¹ p ∈ P := hP x⁻¹ (L.inv_mem hx) p hp
      have hyx : y (x⁻¹ p) = x⁻¹ p := hfix hxinvP y hy
      calc (x * y * x⁻¹ * y⁻¹) p = x (y (x⁻¹ (y⁻¹ p))) := by
            simp only [LinearEquiv.mul_apply]
        _ = x (y (x⁻¹ p)) := by rw [hyinv]
        _ = x (x⁻¹ p) := by rw [hyx]
        _ = p := LinearEquiv.apply_symm_apply x p
    · rfl
    · intro a b _ _ ha hb
      show a (b p) = p
      rw [hb, ha]
    · intro a _ ha
      show a⁻¹ p = p
      calc a⁻¹ p = a⁻¹ (a p) := by rw [ha]
        _ = p := by simp
  exact w183_fixSub_le_of_simple hSL hXne hP hfixX

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem false_of_two_kernels (h : Assumption131 G Γ VA i)
    {A L₁ L₂ D F : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hL₁G : L₁ ≤ G) (hL₂G : L₂ ≤ G)
    [IsSimpleGroup ↥L₁] [IsSimpleGroup ↥L₂]
    (hnab₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hnab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a)
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
    w183_fixSub_le_of_not_centralizes (L := L₁) (Y := F) hYF hncF hP₁inv hP₁fix
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
    w183_fixSub_le_of_not_centralizes (L := L₂) (Y := D) hYD hncD hP₂inv hP₂fix
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
      w183_fixSub_le_of_not_centralizes (L := L₁) (Y := F) hYF hncF hfixDinv hfixDF
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
    obtain ⟨a, ha, b, hb, hab⟩ := hnab₁
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
    have hNnormal : ((A ⊓ L₂).subgroupOf L₂).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, ?_⟩
      · show (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈ A
        exact (Subgroup.mem_normalizer_iff.mp (hL₂norm g.2) (n : LGL 2 V)).mp hn.1
      · show (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈ L₂
        exact L₂.mul_mem (L₂.mul_mem g.2 hn.2) (L₂.inv_mem g.2)⟩
    haveI := hNnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ L₂).subgroupOf L₂) with hNbot | hNtop
    · have hAL₂bot : A ⊓ L₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxL₂ : x ∈ L₂ := hx.2
        have hmem : (⟨x, hxL₂⟩ : ↥L₂) ∈ (A ⊓ L₂).subgroupOf L₂ := by
          rw [Subgroup.mem_subgroupOf]; exact hx
        rw [hNbot, Subgroup.mem_bot] at hmem
        exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hmem)
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
    · have hL₂A : L₂ ≤ A := by
        intro l hl
        have hmem : (⟨l, hl⟩ : ↥L₂) ∈ (A ⊓ L₂).subgroupOf L₂ := by
          rw [hNtop]; trivial
        rw [Subgroup.mem_subgroupOf] at hmem
        exact hmem.1
      obtain ⟨a, ha, b, hb, hab⟩ := hnab₂
      exact hab ((h.isElemAb A hA).comm (hL₂A ha) (hL₂A hb))

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
