module

public import CFSG.LieType.Chevalley.LangG2Tangent
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def cartanWt (τ : Tag) (j : Fin τ.rank) (γ : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, τ.cartan j i * γ i

section Weights

variable {τ : Tag} {F : Type} [Field F]

theorem cast_natAbs_eq [CharP F 2] (a : ℤ) : ((a.natAbs : ℕ) : F) = (a : F) := by
  rcases Int.natAbs_eq a with h | h
  · rw [← Int.cast_natCast]
    exact congrArg (Int.cast : ℤ → F) h.symm
  · have h' : (a : F) = -(((a.natAbs : ℕ) : ℤ) : F) := by
      conv_lhs => rw [h]
      exact Int.cast_neg _
    rw [h', CharTwo.neg_eq, Int.cast_natCast]

theorem cartanWt_single (j i : Fin τ.rank) : cartanWt τ j (Pi.single i 1) = τ.cartan j i := by
  simp [cartanWt, Pi.single_apply]

theorem cartanWt_reflect (i j : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    cartanWt τ j (reflect τ i β) = cartanWt τ j β - cartanWt τ i β * τ.cartan j i := by
  have h : ∀ l, τ.cartan j l * reflect τ i β l = τ.cartan j l * β l -
      cartanWt τ i β * (τ.cartan j l * (Pi.single i 1 : Fin τ.rank → ℤ) l) := by
    intro l
    simp only [reflect, cartanWt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [cartanWt, Finset.sum_congr rfl (fun l _ => h l), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  congr 2
  simp [Pi.single_apply]

variable (τ F) in
@[expose] def hPair (γ : Fin τ.rank → ℤ) : RootModule τ F →ₗ[F] F :=
  ∑ k, ((cartanWt τ k γ : ℤ) : F) • (Finsupp.lapply (R := F) (Sum.inl k) :
    RootModule τ F →ₗ[F] F)

theorem hPair_apply (γ : Fin τ.rank → ℤ) (x : RootModule τ F) :
    hPair τ F γ x = ∑ k, ((cartanWt τ k γ : ℤ) : F) * x (Sum.inl k) := by
  simp [hPair, LinearMap.sum_apply]

theorem hPair_hVec (γ : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    hPair τ F γ (hVec τ F k) = ((cartanWt τ k γ : ℤ) : F) := by
  rw [hPair_apply]
  simp [hVec, Finsupp.single_apply]

theorem hPair_rootVec (γ v : Fin τ.rank → ℤ) : hPair τ F γ (rootVec τ F v) = 0 := by
  by_cases h : IsRoot τ v
  · simp [rootVec, h, hPair_apply]
  · simp [rootVec, h]

variable (τ F) in
@[expose] def hSpan : Submodule F (RootModule τ F) := Submodule.span F (Set.range (hVec τ F))

theorem eq_sum_hVec_of_mem_hSpan {x : RootModule τ F} (hx : x ∈ hSpan τ F) :
    x = ∑ l, x (Sum.inl l) • hVec τ F l := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    simp [hVec, Finsupp.single_apply]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul a x _ hx =>
    simp only [Finsupp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← hx]

structure Good (g : Module.End F (RootModule τ F))
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) : Prop where
  root : ∀ v, IsRoot τ v → IsRoot τ (σ v) ∧ g (rootVec τ F v) = rootVec τ F (σ v)
  hspan : ∀ x ∈ hSpan τ F, g x ∈ hSpan τ F
  pair : ∀ v x, hPair τ F (σ v) (g x) = hPair τ F v x

theorem Good.one : Good (1 : Module.End F (RootModule τ F)) (τ := τ) id :=
  ⟨fun _ hv => ⟨hv, rfl⟩, fun _ hx => hx, fun _ _ => rfl⟩

theorem Good.mul {g g' : Module.End F (RootModule τ F)} {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)}
    (h : Good g σ) (h' : Good g' σ') : Good (g * g') (σ ∘ σ') :=
  ⟨fun v hv => by
    obtain ⟨hr', he'⟩ := h'.root v hv
    obtain ⟨hr, he⟩ := h.root _ hr'
    exact ⟨hr, by rw [Module.End.mul_apply, he', he]; rfl⟩,
   fun x hx => by rw [Module.End.mul_apply]; exact h.hspan _ (h'.hspan x hx),
   fun v x => by rw [Module.End.mul_apply]; exact (h.pair _ _).trans (h'.pair v x)⟩


theorem cartanWt_reflect_self (i : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    cartanWt τ i (reflect τ i β) = - cartanWt τ i β :=
  sum_cartan_mul_reflect τ i β

variable [CharP F 2]

theorem weylElt_one_rootVec {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (i : Fin τ.rank) :
    (weylElt τ F i 1 : Module.End F (RootModule τ F)) (rootVec τ F v) =
      rootVec τ F (reflect τ i v) := by
  rw [weylElt_rootVec i 1 hv]
  have h1 : (-1 : F) = 1 := CharTwo.neg_eq 1
  simp [h1]

theorem weylElt_one_inv (i : Fin τ.rank) : (weylElt τ F i 1)⁻¹ = weylElt τ F i 1 := by
  rw [weylElt_inv]
  congr 1
  exact Units.ext (CharTwo.neg_eq 1)

theorem hPair_weylElt (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) (x : RootModule τ F) :
    hPair τ F (reflect τ i γ) ((weylElt τ F i 1 : Module.End F (RootModule τ F)) x) =
      hPair τ F γ x := by
  have key : (hPair τ F (reflect τ i γ)).comp
      (weylElt τ F i 1 : Module.End F (RootModule τ F)) = hPair τ F γ := by
    refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rcases c with k | v
    · have h1 : (Finsupp.single (Sum.inl k) (1 : F) : RootModule τ F) = hVec τ F k := rfl
      rw [h1, weylElt_hVec, map_sub, map_smul, hPair_hVec, hPair_hVec, hPair_hVec,
        cartanWt_reflect, cartanWt_reflect_self, cast_natAbs_eq]
      push_cast
      ring
    · have h1 : (Finsupp.single (Sum.inr v) (1 : F) : RootModule τ F) = rootVec τ F v.1 :=
        (rootVec_eq_single_of_isRoot' v.2).symm
      rw [h1, weylElt_rootVec i 1 v.2, map_smul, hPair_rootVec, hPair_rootVec, smul_zero]
  exact LinearMap.congr_fun key x

theorem good_weylElt (i : Fin τ.rank) :
    Good ((weylElt τ F i 1 : Module.End F (RootModule τ F))) (reflect τ i) :=
  ⟨fun v hv => ⟨IsRoot.reflect i hv, weylElt_one_rootVec hv i⟩,
   fun x hx => by
    have hle : hSpan τ F ≤ (hSpan τ F).comap (weylElt τ F i 1 : Module.End F (RootModule τ F)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      show (weylElt τ F i 1 : Module.End F (RootModule τ F)) (hVec τ F k) ∈ hSpan τ F
      rw [weylElt_hVec]
      exact sub_mem (Submodule.subset_span ⟨k, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    exact hle hx,
   fun v x => hPair_weylElt i v x⟩

variable (τ F) in
@[expose] def wordWeyl (w : List ℕ) : (Module.End F (RootModule τ F))ˣ :=
  ((w.map fun i => weylElt τ F (τ.idx i) 1).reverse).prod

theorem good_wordWeyl (w : List ℕ) :
    Good ((wordWeyl τ F w : (Module.End F (RootModule τ F))ˣ) : Module.End F (RootModule τ F))
      (fun v => w.foldl (fun v i => reflect τ (τ.idx i) v) v) := by
  induction w with
  | nil => exact Good.one
  | cons i w ih =>
    have h1 : wordWeyl τ F (i :: w) = wordWeyl τ F w * weylElt τ F (τ.idx i) 1 := by
      simp [wordWeyl]
    rw [h1, Units.val_mul]
    exact ih.mul (good_weylElt (τ.idx i))

theorem wordWeyl_inv (w : List ℕ) : (wordWeyl τ F w)⁻¹ = wordWeyl τ F w.reverse := by
  unfold wordWeyl
  rw [List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, List.map_map,
    List.map_reverse, List.reverse_reverse]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  exact weylElt_one_inv _

theorem foldl_reverse_reflect (w : List ℕ) (v : Fin τ.rank → ℤ) :
    w.reverse.foldl (fun v i => reflect τ (τ.idx i) v)
      (w.foldl (fun v i => reflect τ (τ.idx i) v) v) = v := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
    rw [List.foldl_cons, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil, reflect_reflect]

theorem pinnedE_hVec {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (k : Fin τ.rank) :
    pinnedE τ F α (hVec τ F k) = ((cartanWt τ k α : ℤ) : F) • rootVec τ F α := by
  set w := (pinnedData τ α).2.1 with hw
  set j₀ := (pinnedData τ α).1 with hj₀
  have hε : (((pinnedData τ α).2.2 : ℤ) : F) = 1 := by
    rcases pinnedSign_eq τ α with h | h
    · rw [h]; simp
    · rw [h]; simp [CharTwo.neg_eq]
  have hW : pinnedWeyl τ F α = wordWeyl τ F w := rfl
  have hα' : w.foldl (fun v i => reflect τ (τ.idx i) v) (Pi.single j₀ 1) = α :=
    foldl_reflect_pinnedData hα
  have hgW := good_wordWeyl (τ := τ) (F := F) w
  have hgW' := good_wordWeyl (τ := τ) (F := F) w.reverse
  set y : RootModule τ F := ((wordWeyl τ F w.reverse : (Module.End F (RootModule τ F))ˣ) :
    Module.End F (RootModule τ F)) (hVec τ F k) with hy
  have hyspan : y ∈ hSpan τ F := hgW'.hspan _ (Submodule.subset_span ⟨k, rfl⟩)
  have hσ : w.reverse.foldl (fun v i => reflect τ (τ.idx i) v) α = Pi.single j₀ 1 := by
    rw [← hα']
    exact foldl_reverse_reflect w _
  have hypair : hPair τ F (Pi.single j₀ 1) y = ((cartanWt τ k α : ℤ) : F) := by
    have := hgW'.pair α (hVec τ F k)
    rw [hσ] at this
    rw [hy, this, hPair_hVec]
  have hinfE : infE τ F j₀ y = hPair τ F (Pi.single j₀ 1) y • rootVec τ F (Pi.single j₀ 1) := by
    conv_lhs => rw [eq_sum_hVec_of_mem_hSpan hyspan]
    rw [map_sum, hPair_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, infE_hVec, cartanWt_single, cast_natAbs_eq, smul_smul, mul_comm]
  have hWe : ((wordWeyl τ F w : (Module.End F (RootModule τ F))ˣ) :
      Module.End F (RootModule τ F)) (rootVec τ F (Pi.single j₀ 1)) = rootVec τ F α := by
    have := (hgW.root _ (isRoot_single τ j₀)).2
    rw [this, hα']
  rw [pinnedE, LinearMap.smul_apply, hε, one_smul, Module.End.mul_apply, Module.End.mul_apply,
    hW, wordWeyl_inv]
  change ((wordWeyl τ F w : (Module.End F (RootModule τ F))ˣ) : Module.End F (RootModule τ F))
    (infE τ F j₀ y) = _
  rw [hinfE, map_smul, hWe, hypair]

omit [CharP F 2] in
theorem rootVec_apply_inr (α β : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootVec τ F α.1 (Sum.inr β) = if α = β then 1 else 0 := by
  simp [rootVec, α.2, Finsupp.single_apply]

theorem linearIndependent_pinnedE_tangentH_of
    (hodd : ∀ β, IsRoot τ β → ∃ k, ((cartanWt τ k β : ℤ) : F) ≠ 0)
    (hdet : (τ.cartan.map (Int.cast : ℤ → F)).det ≠ 0) :
    LinearIndependent F (Sum.elim (fun α : {α // IsRoot τ α} => pinnedE τ F α.1)
      (tangentH τ F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' := hg
  rw [Fintype.sum_sum_type] at hg'
  simp only [Sum.elim_inl, Sum.elim_inr] at hg'
  have h1 : ∀ k, ∀ β : {α // IsRoot τ α}, g (Sum.inl β) * ((cartanWt τ k β.1 : ℤ) : F) = 0 := by
    intro k β
    have hE : ∀ α : {α // IsRoot τ α}, pinnedE τ F α.1 (hVec τ F k) =
        ((cartanWt τ k α.1 : ℤ) : F) • rootVec τ F α.1 := fun α => pinnedE_hVec α.2 k
    have h := LinearMap.congr_fun hg' (hVec τ F k)
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, tangentH_hVec,
      smul_zero, Finset.sum_const_zero, add_zero, LinearMap.zero_apply, hE] at h
    have h2 := congrArg (fun x : RootModule τ F => x (Sum.inr β)) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      rootVec_apply_inr, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h2
    exact h2
  have hg0 : ∀ β, g (Sum.inl β) = 0 := by
    intro β
    obtain ⟨k, hk⟩ := hodd β.1 β.2
    exact (mul_eq_zero.1 (h1 k β)).resolve_right hk
  simp only [hg0, zero_smul, Finset.sum_const_zero, zero_add] at hg'
  have h3 : ∀ k, ∑ i, g (Sum.inr i) * ((τ.cartan i k : ℤ) : F) = 0 := by
    intro k
    have h := LinearMap.congr_fun hg' (rootVec τ F (Pi.single k 1))
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h
    have h2 := congrArg
      (fun x : RootModule τ F => x (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩)) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tangentH_rootVec i (isRoot_single τ k), Finsupp.smul_apply]
    have h5 : rootVec τ F (Pi.single k 1)
        (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩) = 1 := by
      have := rootVec_apply_inr (τ := τ) (F := F) ⟨Pi.single k 1, isRoot_single τ k⟩
        ⟨Pi.single k 1, isRoot_single τ k⟩
      simpa using this
    rw [h5, smul_eq_mul, mul_one]
    have h6 : (∑ j, τ.cartan i j * (Pi.single k 1 : Fin τ.rank → ℤ) j) = τ.cartan i k :=
      cartanWt_single i k
    rw [h6]
  have h4 : (fun i => g (Sum.inr i)) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext k
    simpa [Matrix.vecMul, dotProduct] using h3 k
  rintro (β | i)
  · exact hg0 β
  · exact congrFun h4 i

end Weights

theorem F4_exists_odd_cartanWt :
    ∀ β ∈ rootFinset Tag.F4, ∃ j : Fin Tag.F4.rank, ¬ (2 : ℤ) ∣ cartanWt Tag.F4 j β := by
  decide +kernel

theorem linearIndependent_pinnedE_tangentH_F4 {F : Type} [Field F] [CharP F 2] :
    LinearIndependent F (Sum.elim (fun α : {α // IsRoot Tag.F4 α} => pinnedE Tag.F4 F α.1)
      (tangentH Tag.F4 F)) := by
  refine linearIndependent_pinnedE_tangentH_of (fun β hβ => ?_) ?_
  · obtain ⟨j, hj⟩ := F4_exists_odd_cartanWt β (mem_rootFinset.2 hβ)
    refine ⟨j, fun h => hj ?_⟩
    have h2 := (CharP.intCast_eq_zero_iff F 2 _).1 h
    exact_mod_cast h2
  · have h := RingHom.map_det (Int.castRingHom F) Tag.F4.cartan
    rw [det_cartan_F4, map_one] at h
    intro h0
    exact one_ne_zero (h.trans h0)

end CFSG.RankThree.PartOne.RF4
