module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus
public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat
public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (σ) in
@[expose] def compatBorel : Subgroup (ModGL t.tag K) :=
  compatTorus σ ⊔ graphFixedPosUnipotent t K σ

theorem compatTorus_le_normalizer :
    compatTorus σ ≤ Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) :=
  (compatTorus_le_graphFixedRootTorus σ).trans
    graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent

theorem mem_compatBorel {b : ModGL t.tag K} :
    b ∈ compatBorel σ ↔ ∃ h ∈ compatTorus σ, ∃ u ∈ graphFixedPosUnipotent t K σ, h * u = b := by
  rw [← SetLike.mem_coe, compatBorel,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ compatTorus_le_normalizer, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem compatTorus_le_compatBorel : compatTorus (t := t) σ ≤ compatBorel σ :=
  le_sup_left

theorem graphFixedPosUnipotent_le_compatBorel : graphFixedPosUnipotent t K σ ≤ compatBorel σ :=
  le_sup_right

theorem compatBorel_le_graphFixedRootBorel : compatBorel σ ≤ graphFixedRootBorel t K σ :=
  sup_le ((compatTorus_le_graphFixedRootTorus σ).trans graphFixedRootTorus_le_graphFixedRootBorel)
    graphFixedPosUnipotent_le_graphFixedRootBorel

theorem orbitH_mem_compatTorus (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) ∈ compatTorus σ := by
  classical
  let s : (b : Fin t.foldedTag.rank) → (orbitField t K σ b)ˣ := Pi.mulSingle a u
  have hsa : s a = u := by simp [s]
  have hsb : ∀ b, b ≠ a → s b = 1 := fun b hb => by simp [s, hb]
  have h := list_prod_orbitH (K := K) (σ := σ) s
  have hone : ∀ b, b ≠ a → (orbitH t K σ b (s b) : ModGL t.tag K) = 1 := fun b hb => by
    rw [hsb b hb, orbitH, mul_inv_cancel]
    rfl
  have hl : ((List.finRange t.foldedTag.rank).map fun b =>
      (orbitH t K σ b (s b) : ModGL t.tag K)).prod = (orbitH t K σ a u : ModGL t.tag K) := by
    have key : ∀ l : List (Fin t.foldedTag.rank), l.Nodup →
        ((l.map fun b => (orbitH t K σ b (s b) : ModGL t.tag K)).prod =
          if a ∈ l then (orbitH t K σ a u : ModGL t.tag K) else 1) := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
        obtain ⟨hb, hl'⟩ := List.nodup_cons.1 hl
        rw [List.map_cons, List.prod_cons, ih hl']
        by_cases hba : b = a
        · subst hba
          simp only [List.mem_cons, true_or, ↓reduceIte, hb, mul_one]
          rw [hsa]
        · rw [hone b hba, one_mul]
          by_cases hal : a ∈ l
          · simp [hal]
          · simp [hal, Ne.symm hba]
    rw [key _ (List.nodup_finRange _), ite_eq_left (List.mem_finRange a)]
  rw [← hl, h]
  refine (mem_compatTorus σ).2 ⟨compatDiag t σ s, fun i => compatDiag_perm s i, ?_⟩
  rw [coe_torusCoordHom, List.ofFn_eq_map]

variable (σ) in
@[expose] def compatCells : Set (ModGL t.tag K) :=
  {x | ∃ w ∈ relWeylTwist t, ∃ b ∈ compatBorel σ, ∃ b' ∈ compatBorel σ,
    b * canonicalRep (coxeterSystem t.tag) K w * b' = x}

theorem one_mem_compatCells : (1 : ModGL t.tag K) ∈ compatCells σ :=
  ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by rw [canonicalRep_one, one_mul, one_mul]⟩

theorem mul_mem_compatCells {b x : ModGL t.tag K} (hb : b ∈ compatBorel σ)
    (hx : x ∈ compatCells σ) : b * x ∈ compatCells σ := by
  obtain ⟨w, hw, b₁, hb₁, b₂, hb₂, rfl⟩ := hx
  exact ⟨w, hw, b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩

theorem mem_compatCells_mul {b x : ModGL t.tag K} (hb : b ∈ compatBorel σ)
    (hx : x ∈ compatCells σ) : x * b ∈ compatCells σ := by
  obtain ⟨w, hw, b₁, hb₁, b₂, hb₂, rfl⟩ := hx
  exact ⟨w, hw, b₁, hb₁, b₂ * b, mul_mem hb₂ hb, by group⟩

theorem canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α)
    (hpos : ∀ α ∈ S, 0 < height (w⁻¹ • α)) {g : ModGL t.tag K}
    (hg : g ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) :
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹ * g * canonicalRep (coxeterSystem t.tag) K w ∈
      graphFixedPosUnipotent t K σ := by
  set n := canonicalRep (coxeterSystem t.tag) K w
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hmap := (canonical_weyl_root_transport t.tag K).1 w ((fun α => w⁻¹ • α) '' S)
    (by rintro _ ⟨α, hα, rfl⟩; exact IsRoot.smul (hS α hα) w⁻¹)
  rw [Set.image_image, Set.image_congr fun α _ => smul_inv_smul w α, Set.image_id'] at hmap
  rw [← hmap] at hgS
  obtain ⟨y, hy, hyg⟩ := hgS
  have hyg' : n * y * n⁻¹ = g := hyg
  have e : n⁻¹ * g * n = y := by rw [← hyg']; group
  rw [e]
  have hyΓ : y ∈ twistedFixedGroup t K σ := by
    rw [← e]
    exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hy, hyΓ⟩
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨IsRoot.smul (hS α hα) w⁻¹, hpos α hα⟩

variable (hσ : Function.Surjective σ)
include hσ

theorem exists_canonicalRep_orbitReflection_mul_compatBorel (a : Fin t.foldedTag.rank)
    {b : ModGL t.tag K} (hb : b ∈ compatBorel σ) :
    ∃ b' ∈ compatBorel σ, ∃ c : orbitField t K σ a,
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b =
        b' * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a c : ModGL t.tag K) := by
  set N := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  obtain ⟨h, hh, u, hu, rfl⟩ := (mem_compatBorel).1 hb
  obtain ⟨v, hv, c, rfl⟩ := exists_mul_orbitX_eq hσ a hu
  have hh' : N * h * N⁻¹ ∈ compatTorus σ :=
    canonicalRep_orbitReflection_conj_mem_compatTorus σ a hh
  have hv' : N * v * N⁻¹ ∈ graphFixedSimpleComplement t K σ a :=
    (Subgroup.mem_normalizer_iff.1
      (canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement (σ := σ) a) v).1 hv
  refine ⟨(N * h * N⁻¹) * (N * v * N⁻¹), mul_mem (compatTorus_le_compatBorel hh')
    (graphFixedPosUnipotent_le_compatBorel (graphFixedSimpleComplement_le a hv')), c, ?_⟩
  group

omit hσ in
theorem canonicalRep_orbitReflection_mul_orbitX_mul_mem (a : Fin t.foldedTag.rank)
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (c : orbitField t K σ a) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w ∈
      compatCells σ := by
  have hlen := length_orbitReflection (t := t) a
  rcases forall_height_pos_or_forall_height_neg (inv_mem hw) a with hpos | hneg
  ·
    obtain ⟨-, hl⟩ := length_orbitReflection_mul_of_pos t hw hpos
    have hN : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * w) =
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          canonicalRep (coxeterSystem t.tag) K w :=
      canonicalRep_mul_of_length_eq (by rw [hl, hlen, add_comm])
    have hx := canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent (σ := σ) hw
      (S := simpleOrbitRoots t a) (fun α hα => (simpleOrbitRoots_pos a α hα).1)
      (by rintro _ ⟨i, hi, rfl⟩; exact hpos i hi) (orbitX_mem t σ a c)
    refine ⟨t.orbitReflection a * w, mul_mem (t.orbitReflection_mem a) hw, 1, one_mem _, _,
      graphFixedPosUnipotent_le_compatBorel hx, ?_⟩
    rw [hN]
    group
  ·
    set w' := t.orbitReflection a * w
    have hw' : w' ∈ relWeylTwist t := mul_mem (t.orbitReflection_mem a) hw
    obtain ⟨-, hl⟩ := length_orbitReflection_mul_of_neg t hw hneg
    have hww : t.orbitReflection a * w' = w := by
      rw [← mul_assoc, t.orbitReflection_mul_self, one_mul]
    have hn : canonicalRep (coxeterSystem t.tag) K w =
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          canonicalRep (coxeterSystem t.tag) K w' := by
      rw [← canonicalRep_mul_of_length_eq (by rw [hww, hlen, ← hl, add_comm]), hww]
    by_cases hc : c = 0
    · subst hc
      refine ⟨w', hw', canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a), compatTorus_le_compatBorel
        (canonicalRep_orbitReflection_sq_mem_compatTorus σ a), 1, one_mem _, ?_⟩
      rw [orbitX_zero, Subgroup.coe_one, mul_one, hn]
      group
    · set u : (orbitField t K σ a)ˣ := Units.mk0 c hc
      have hid := canonicalRep_orbitReflection_mul_orbitX t σ a u
      have hy := canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent (σ := σ) hw
        (S := (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
        (by rintro _ ⟨i, -, rfl⟩; exact isRoot_neg_single _ i)
        (by rintro _ ⟨i, hi, rfl⟩; rw [smul_neg, height_neg]; linarith [hneg i hi])
        (orbitYEquiv t σ a (Multiplicative.ofAdd
          ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a))).2
      rw [coe_orbitYEquiv] at hy
      refine ⟨w, hw, (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) :
          orbitField t K σ a)) : ModGL t.tag K) * (orbitH t K σ a (-u⁻¹) : ModGL t.tag K),
        mul_mem (graphFixedPosUnipotent_le_compatBorel (orbitX_mem_graphFixedPosUnipotent t σ a _))
          (compatTorus_le_compatBorel (orbitH_mem_compatTorus a _)), _,
        graphFixedPosUnipotent_le_compatBorel hy, ?_⟩
      have hcu : (orbitX t K σ a c : ModGL t.tag K) = orbitX t K σ a (u : orbitField t K σ a) :=
        rfl
      rw [hcu, hid]
      group

theorem canonicalRep_orbitReflection_mul_mem_compatCells (a : Fin t.foldedTag.rank)
    {x : ModGL t.tag K} (hx : x ∈ compatCells σ) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * x ∈ compatCells σ := by
  obtain ⟨w, hw, b, hb, b', hb', rfl⟩ := hx
  obtain ⟨b'', hb'', c, hc⟩ := exists_canonicalRep_orbitReflection_mul_compatBorel hσ a hb
  have e : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      (b * canonicalRep (coxeterSystem t.tag) K w * b') =
      b'' * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w) * b' := by
    rw [← mul_assoc, ← mul_assoc, hc]
    group
  rw [e]
  exact mem_compatCells_mul hb' (mul_mem_compatCells hb''
    (canonicalRep_orbitReflection_mul_orbitX_mul_mem a hw c))

omit hσ in
theorem canonicalRep_mem_of_forall {M : Subgroup (ModGL t.tag K)}
    (hM : ∀ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M) :
    ∀ w ∈ relWeylTwist t, canonicalRep (coxeterSystem t.tag) K w ∈ M := by
  suffices h : ∀ n, ∀ w ∈ relWeylTwist t, (coxeterSystem t.tag).length w = n →
      canonicalRep (coxeterSystem t.tag) K w ∈ M from fun w hw => h _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hlen
    by_cases h1 : w = 1
    · rw [h1, canonicalRep_one]
      exact one_mem _
    obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t hw h1
    obtain ⟨-, hl⟩ := length_mul_orbitReflection_of_neg t hw ha
    set v := w * t.orbitReflection a
    have hv : v ∈ relWeylTwist t := mul_mem hw (t.orbitReflection_mem a)
    have hvw : v * t.orbitReflection a = w := by
      rw [mul_assoc, t.orbitReflection_mul_self, mul_one]
    have hrep : canonicalRep (coxeterSystem t.tag) K w =
        canonicalRep (coxeterSystem t.tag) K v *
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) := by
      rw [← canonicalRep_mul_of_length_eq (by rw [hvw, length_orbitReflection a, ← hl]), hvw]
    rw [hrep]
    have hcard : 0 < (t.orbit a).card := Finset.card_pos.2 ⟨_, t.orbitMin_mem a⟩
    exact mul_mem (ih _ (by omega) v hv rfl) (hM a)

theorem mem_compatCells_of_mem_graphFixedRootGroup {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootGroup t K σ) : g ∈ compatCells σ := by
  set S : Set (ModGL t.tag K) := (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) ∪
    Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  have hle : graphFixedRootGroup t K σ ≤ Subgroup.closure S := by
    rw [graphFixedRootGroup_eq_closure σ hσ, Subgroup.closure_le]
    rintro _ ⟨w, hw, a, c, rfl⟩
    have hn := canonicalRep_mem_of_forall (M := Subgroup.closure S)
      (fun a => Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)) w hw
    exact mul_mem (mul_mem hn (Subgroup.subset_closure (Or.inl
      (orbitX_mem_graphFixedPosUnipotent t σ a c)))) (inv_mem hn)
  refine Subgroup.closure_induction_left (p := fun x _ => x ∈ compatCells σ)
    one_mem_compatCells (fun x hx y _ hy => ?_) (fun x hx y _ hy => ?_) (hle hg)
  · rcases hx with hx | ⟨a, rfl⟩
    · exact mul_mem_compatCells (graphFixedPosUnipotent_le_compatBorel hx) hy
    · exact canonicalRep_orbitReflection_mul_mem_compatCells hσ a hy
  · rcases hx with hx | ⟨a, rfl⟩
    · exact mul_mem_compatCells (graphFixedPosUnipotent_le_compatBorel (inv_mem hx)) hy
    · set N := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
      have hN2 : (N * N)⁻¹ ∈ compatBorel σ := inv_mem (compatTorus_le_compatBorel
        (canonicalRep_orbitReflection_sq_mem_compatTorus σ a))
      have e : N⁻¹ * y = N * ((N * N)⁻¹ * y) := by group
      rw [e]
      exact canonicalRep_orbitReflection_mul_mem_compatCells hσ a (mul_mem_compatCells hN2 hy)

theorem graphFixedRootTorus_eq_compatTorus :
    graphFixedRootTorus t K σ = compatTorus σ := by
  refine le_antisymm (fun h hh => ?_) (compatTorus_le_graphFixedRootTorus σ)
  obtain ⟨w, hw, b, hb, b', hb', hbw⟩ :=
    mem_compatCells_of_mem_graphFixedRootGroup hσ (graphFixedRootTorus_le t K σ hh)
  have hw1 : w = 1 := by
    by_contra hne
    have h1 : h ∈ graphFixedRootBruhatCell t K σ 1 :=
      mem_graphFixedRootBruhatCell.2 ⟨h, graphFixedRootTorus_le_graphFixedRootBorel hh, 1,
        one_mem _, by rw [canonicalRep_one, mul_one, mul_one]⟩
    have h2 : h ∈ graphFixedRootBruhatCell t K σ w :=
      mem_graphFixedRootBruhatCell.2 ⟨b, compatBorel_le_graphFixedRootBorel hb, b',
        compatBorel_le_graphFixedRootBorel hb', hbw⟩
    exact Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell (Ne.symm hne)) h1 h2
  subst hw1
  rw [canonicalRep_one, mul_one] at hbw
  obtain ⟨x, hx, u, hu, hxu⟩ := (mem_compatBorel).1 (mul_mem hb hb')
  have hu1 : u ∈ graphFixedRootTorus t K σ ⊓ graphFixedPosUnipotent t K σ := by
    refine Subgroup.mem_inf.2 ⟨?_, hu⟩
    have : u = x⁻¹ * h := by rw [← hbw, ← hxu]; group
    rw [this]
    exact mul_mem (inv_mem (compatTorus_le_graphFixedRootTorus σ hx)) hh
  rw [graphFixedRootTorus_inf_graphFixedPosUnipotent, Subgroup.mem_bot] at hu1
  rw [← hbw, ← hxu, hu1, mul_one]
  exact hx

end CFSG.Timmesfeld.ExceptionalOrders
