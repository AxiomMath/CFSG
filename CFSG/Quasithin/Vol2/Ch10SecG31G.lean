module

public import CFSG.Quasithin.Vol2.Ch10SecG31F

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

namespace Hyp

variable {Gm : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ₀ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}

theorem conj_mem (hH : Hyp Gm Δ₀ F) {k : W ≃ₗ[ZMod 2] W} (hk : k ∈ Gm) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens Δ₀ F)) : k * g * k⁻¹ ∈ Subgroup.closure (gens Δ₀ F) := by
  have hle : Subgroup.closure (gens Δ₀ F) ≤
      (Subgroup.closure (gens Δ₀ F)).comap (MulAut.conj k).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro t ⟨x, hx, φ, hφ, h, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show k * LinearEquiv.transvection h * k⁻¹ ∈ Subgroup.closure (gens Δ₀ F)
    rw [mul_transvection_mul_inv k h (transvection_comp_apply_eq_zero k h)]
    refine Subgroup.subset_closure ⟨k x, hH.map_mem k hk x hx, _, ?_, _, rfl⟩
    rw [hH.mem_F_map k hk x hx]
    convert hφ using 1
    ext w
    simp
  exact hle hg

theorem sub_mem_span {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ Subgroup.closure (gens Δ₀ F)) (v : W) :
    g v - v ∈ Submodule.span (ZMod 2) Δ₀ := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem t ht =>
    obtain ⟨x, hx, φ, -, h, rfl⟩ := ht
    rw [transvection_apply, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  | one => simp
  | mul a b _ _ ha hb =>
    have : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [this]
    exact Submodule.add_mem _ (ha _) (hb _)
  | inv a _ ha =>
    have : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
      rw [show a (a⁻¹ v) = v from a.apply_symm_apply v]
      abel
    rw [this]
    exact Submodule.neg_mem _ (ha _)

theorem map_mem_span (hH : Hyp Gm Δ₀ F) {k : W ≃ₗ[ZMod 2] W} (hk : k ∈ Gm) {v : W}
    (hv : v ∈ Submodule.span (ZMod 2) Δ₀) : k v ∈ Submodule.span (ZMod 2) Δ₀ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hH.map_mem k hk x hx)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

end Hyp

structure OrbHyp (Gm : Subgroup (W ≃ₗ[ZMod 2] W)) (Δ₀ : Set W)
    (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)) {s : ℕ} (Δ : Fin s → Set W) : Prop where
  hyp : Hyp Gm Δ₀ F
  O2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ Gm → (∀ k ∈ Gm, ∀ n ∈ N, k * n * k⁻¹ ∈ N) →
    (∀ n ∈ N, n ^ 4 = 1) → N = ⊥
  rank : ∀ x ∈ Δ₀, 2 ≤ finrank (ZMod 2) (F x)
  disj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)
  union : ⋃ i, Δ i = Δ₀
  inv : ∀ i, ∀ x ∈ Δ i, ∀ g ∈ Subgroup.closure (gens Δ₀ F), g x ∈ Δ i
  trans : ∀ i, ∀ x ∈ Δ i, ∀ y ∈ Δ i, ∃ g ∈ Subgroup.closure (gens Δ₀ F), g x = y

namespace OrbHyp

variable {Gm : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ₀ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)} {s : ℕ} {Δ : Fin s → Set W}

theorem subset (hO : OrbHyp Gm Δ₀ F Δ) (i : Fin s) : Δ i ⊆ Δ₀ :=
  fun _ hx => hO.union ▸ Set.mem_iUnion_of_mem i hx

theorem closure_le (hO : OrbHyp Gm Δ₀ F Δ) (i : Fin s) :
    Subgroup.closure (gens (Δ i) F) ≤ Subgroup.closure (gens Δ₀ F) :=
  Subgroup.closure_mono (by
    rintro t ⟨x, hx, φ, hφ, h, rfl⟩
    exact ⟨x, hO.subset i hx, φ, hφ, h, rfl⟩)

theorem closure_eq_iSup (hO : OrbHyp Gm Δ₀ F Δ) :
    Subgroup.closure (gens Δ₀ F) = ⨆ i, Subgroup.closure (gens (Δ i) F) := by
  rw [← Subgroup.closure_iUnion]
  congr 1
  ext t
  simp only [gens, Set.mem_iUnion, ← hO.union]
  constructor
  · rintro ⟨x, ⟨i, hx⟩, rest⟩
    exact ⟨i, x, hx, rest⟩
  · rintro ⟨i, x, hx, rest⟩
    exact ⟨x, ⟨i, hx⟩, rest⟩

variable [Finite W]

theorem mem_C_of_ne (hO : OrbHyp Gm Δ₀ F Δ) {i j : Fin s} (hij : i ≠ j) {x y : W}
    (hx : x ∈ Δ i) (hy : y ∈ Δ j) : y ∈ C F x := by
  by_contra hyx
  have hH := hO.hyp
  have hx₀ := hO.subset i hx
  have hy₀ := hO.subset j hy
  obtain ⟨φ, hφ, hφy⟩ := exists_eq_one_of_not_mem_C hyx
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx₀ hy₀ hyx)
  have hφx : φ x = 0 := hH.apply_self x hx₀ φ hφ
  have hψy : ψ y = 0 := hH.apply_self y hy₀ ψ hψ
  have h1 := hO.inv i x hx _ (Subgroup.subset_closure ⟨y, hy₀, ψ, hψ, hψy, rfl⟩)
  have h2 := hO.inv j y hy _ (Subgroup.subset_closure ⟨x, hx₀, φ, hφ, hφx, rfl⟩)
  rw [transvection_apply, hψx, one_smul] at h1
  rw [transvection_apply, hφy, one_smul, add_comm] at h2
  exact Set.disjoint_left.1 (hO.disj i j hij) h1 h2

theorem fix_of_ne (hO : OrbHyp Gm Δ₀ F Δ) {i j : Fin s} (hij : i ≠ j) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens (Δ i) F)) {v : W}
    (hv : v ∈ Submodule.span (ZMod 2) (Δ j)) : g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨x, hx, φ, hφ, h, rfl⟩ := ht
    have hφv : φ v = 0 := by
      have hle : Submodule.span (ZMod 2) (Δ j) ≤ C F x :=
        Submodule.span_le.2 fun y hy => hO.mem_C_of_ne hij hx hy
      exact mem_C.1 (hle hv) φ hφ
    rw [transvection_apply, hφv, zero_smul, add_zero]
  | one => rfl
  | mul a b _ _ ha hb => rw [LinearEquiv.mul_apply, hb, ha]
  | inv a _ ha =>
    show a.symm v = v
    rw [LinearEquiv.symm_apply_eq, ha]

theorem commute_of_ne (hO : OrbHyp Gm Δ₀ F Δ) {i j : Fin s} (hij : i ≠ j)
    {a b : W ≃ₗ[ZMod 2] W} (ha : a ∈ Subgroup.closure (gens (Δ i) F))
    (hb : b ∈ Subgroup.closure (gens (Δ j) F)) : a * b = b * a := by
  have hgen : ∀ t ∈ gens (Δ i) F, ∀ u ∈ gens (Δ j) F, t * u = u * t := by
    rintro t ⟨x, hx, φ, hφ, h, rfl⟩ u ⟨y, hy, ψ, hψ, h', rfl⟩
    exact transvection_commute h h' (mem_C.1 (hO.mem_C_of_ne hij hx hy) φ hφ)
      (mem_C.1 (hO.mem_C_of_ne (Ne.symm hij) hy hx) ψ hψ)
  have h1 : Subgroup.closure (gens (Δ i) F) ≤ Subgroup.centralizer (gens (Δ j) F) :=
    (Subgroup.closure_le _).2 fun t ht => Subgroup.mem_centralizer_iff.2 fun u hu =>
      (hgen t ht u hu).symm
  have h2 : Subgroup.closure (gens (Δ j) F) ≤ Subgroup.centralizer {a} :=
    (Subgroup.closure_le _).2 fun u hu => Subgroup.mem_centralizer_iff.2 fun t ht => by
      rw [Set.mem_singleton_iff.1 ht]
      exact (Subgroup.mem_centralizer_iff.1 (h1 ha) u hu).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hb) a rfl

omit [Finite W] in
theorem map_mem_span_i (hO : OrbHyp Gm Δ₀ F Δ) (i : Fin s) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens Δ₀ F)) {v : W}
    (hv : v ∈ Submodule.span (ZMod 2) (Δ i)) : g v ∈ Submodule.span (ZMod 2) (Δ i) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hO.inv i x hx g hg)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

omit [Finite W] in
theorem eq_one (hO : OrbHyp Gm Δ₀ F Δ) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens Δ₀ F))
    (hfix : ∀ v ∈ Submodule.span (ZMod 2) Δ₀, ∀ h ∈ Subgroup.closure (gens Δ₀ F),
      h (g v - v) = g v - v) : g = 1 := by
  have hH := hO.hyp
  have hG₀m : Subgroup.closure (gens Δ₀ F) ≤ Gm := hH.closure_gens_le subset_rfl
  let N : Subgroup (W ≃ₗ[ZMod 2] W) :=
    { carrier := {n | n ∈ Subgroup.closure (gens Δ₀ F) ∧ ∀ v ∈ Submodule.span (ZMod 2) Δ₀,
        ∀ h ∈ Subgroup.closure (gens Δ₀ F), h (n v - v) = n v - v}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun v hv h hh => ?_⟩
        have e : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [e, map_add, ha' _ (hH.map_mem_span (hG₀m hb) hv) h hh, hb' v hv h hh]
      one_mem' := ⟨Subgroup.one_mem _, fun v _ h _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun v hv h hh => ?_⟩
        have e : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
          rw [show a (a⁻¹ v) = v from a.apply_symm_apply v]
          abel
        rw [e, map_neg, ha' _ (hH.map_mem_span (hG₀m (Subgroup.inv_mem _ ha)) hv) h hh] }
  have hN : N = ⊥ := by
    refine hO.O2 N (fun n hn => hG₀m hn.1) (fun k hk n hn => ⟨hH.conj_mem hk hn.1,
      fun v hv h hh => ?_⟩) (fun n hn => ?_)
    · have hkv : k⁻¹ v ∈ Submodule.span (ZMod 2) Δ₀ := hH.map_mem_span (Gm.inv_mem hk) hv
      have hconj : k⁻¹ * h * k ∈ Subgroup.closure (gens Δ₀ F) := by
        have := hH.conj_mem (Gm.inv_mem hk) hh
        rwa [inv_inv] at this
      have e : (k * n * k⁻¹) v - v = k (n (k⁻¹ v) - k⁻¹ v) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub,
          show k (k⁻¹ v) = v from k.apply_symm_apply v]
      have h1 := hn.2 _ hkv _ hconj
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
      have h2 := congrArg (⇑k) h1
      rw [show k (k⁻¹ (h (k (n (k⁻¹ v) - k⁻¹ v)))) = h (k (n (k⁻¹ v) - k⁻¹ v)) from
        k.apply_symm_apply _] at h2
      rw [e, h2]
    · refine LinearEquiv.ext fun v => ?_
      have ha : n v - v ∈ Submodule.span (ZMod 2) Δ₀ := Hyp.sub_mem_span hn.1 v
      have hb := hn.2 _ ha n hn.1
      have hnv : n v = v + (n v - v) := by abel
      have hna : n (n v - v) = (n v - v) + (n (n v - v) - (n v - v)) := by abel
      set a := n v - v
      set b := n a - a
      have h2 : n (n v) = v + b := by
        rw [hnv, map_add, hnv, hna, add_assoc, ← add_assoc a a b, two_add_self, zero_add]
      have h3 : n (n (n v)) = v + a + b := by rw [h2, map_add, hnv, hb]
      have h4 : n (n (n (n v))) = v := by
        rw [h3, map_add, map_add, hnv, hna, hb, add_assoc v a (a + b), ← add_assoc a a b,
          two_add_self, zero_add, add_assoc, two_add_self, add_zero]
      rw [pow_succ, pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      exact h4
  have hgN : g ∈ N := ⟨hg, hfix⟩
  rw [hN] at hgN
  exact hgN

theorem exists_proj (hO : OrbHyp Gm Δ₀ F Δ) (i : Fin s) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens Δ₀ F)) :
    ∃ g' ∈ Subgroup.closure (gens (Δ i) F), ∀ v ∈ Submodule.span (ZMod 2) (Δ i), g v = g' v := by
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨x, hx, φ, hφ, h, rfl⟩ := ht
    rw [← hO.union, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    by_cases hij : j = i
    · subst hij
      exact ⟨_, Subgroup.subset_closure ⟨x, hj, φ, hφ, h, rfl⟩, fun v _ => rfl⟩
    · exact ⟨1, Subgroup.one_mem _, fun v hv =>
        hO.fix_of_ne hij (Subgroup.subset_closure ⟨x, hj, φ, hφ, h, rfl⟩) hv⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun v _ => rfl⟩
  | mul a b ha₀ hb₀ ha hb =>
    obtain ⟨a', ha', ha⟩ := ha
    obtain ⟨b', hb', hb⟩ := hb
    refine ⟨a' * b', Subgroup.mul_mem _ ha' hb', fun v hv => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha _ (hO.map_mem_span_i i hb₀ hv), hb v hv]
  | inv a ha₀ ha =>
    obtain ⟨a', ha', ha⟩ := ha
    refine ⟨a'⁻¹, Subgroup.inv_mem _ ha', fun v hv => ?_⟩
    have hav : a'.symm v ∈ Submodule.span (ZMod 2) (Δ i) :=
      Hyp.invariant_span a'⁻¹ (Subgroup.inv_mem _ ha') v hv
    show a.symm v = a'.symm v
    rw [LinearEquiv.symm_apply_eq, ha _ hav]
    exact (a'.apply_symm_apply v).symm

theorem core_i (hO : OrbHyp Gm Δ₀ F Δ) (i : Fin s) :
    (∀ v ∈ Submodule.span (ZMod 2) (Δ i), v ≠ 0 → v ∈ Δ i) ∧
    (∀ g : Submodule.span (ZMod 2) (Δ i) ≃ₗ[ZMod 2] Submodule.span (ZMod 2) (Δ i),
      ∃ k ∈ Subgroup.closure (gens (Δ i) F), ∀ v : Submodule.span (ZMod 2) (Δ i), k v = g v) ∧
    (∀ x ∈ Δ i, finrank (ZMod 2) (F x) + 1 =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Δ i))) := by
  refine hO.hyp.core_restrict (hO.subset i)
    (fun g hg x hx => hO.inv i x hx g (hO.closure_le i hg)) (fun x hx y hy => ?_)
    (fun x hx => hO.rank x (hO.subset i hx)) (fun g hg hfix => ?_)
  · obtain ⟨g, hg, hgxy⟩ := hO.trans i x hx y hy
    obtain ⟨g', hg', hgg⟩ := hO.exists_proj i hg
    exact ⟨g', hg', by rw [← hgg x (Submodule.subset_span hx), hgxy]⟩
  · refine hO.eq_one (hO.closure_le i hg) fun v hv h hh => ?_
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rw [← hO.union, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      by_cases hij : j = i
      · subst hij
        obtain ⟨h', hh', hhh⟩ := hO.exists_proj j hh
        rw [hhh _ (Hyp.sub_mem_span hg x), hfix x (Submodule.subset_span hj) h' hh']
      · rw [hO.fix_of_ne (Ne.symm hij) hg (Submodule.subset_span hj), sub_self, map_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, add_sub_add_comm, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ← smul_sub, map_smul, ha]

theorem eq_one_of_fix (hO : OrbHyp Gm Δ₀ F Δ) {i : Fin s} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ Subgroup.closure (gens (Δ i) F))
    (hfix : ∀ v ∈ Submodule.span (ZMod 2) (Δ i), g v = v) : g = 1 := by
  refine hO.eq_one (hO.closure_le i hg) fun v hv h _ => ?_
  have hgv : g v = v := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rw [← hO.union, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      by_cases hij : j = i
      · subst hij
        exact hfix x (Submodule.subset_span hj)
      · exact hO.fix_of_ne (Ne.symm hij) hg (Submodule.subset_span hj)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  rw [hgv, sub_self, map_zero]

theorem iSupIndep_span (hO : OrbHyp Gm Δ₀ F Δ) :
    iSupIndep fun i => Submodule.span (ZMod 2) (Δ i) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro v hv hv'
  by_contra hv0
  have hle : (⨆ j, ⨆ (_ : j ≠ i), Submodule.span (ZMod 2) (Δ j)) ≤
      G11.fixedSpace (Subgroup.closure (gens (Δ i) F)) :=
    iSup₂_le fun j hj w hw g' hg' => hO.fix_of_ne (Ne.symm hj) hg' hw
  have hfixv : ∀ g ∈ Subgroup.closure (gens (Δ i) F), g v = v := hle hv'
  obtain ⟨h1, h2, h3⟩ := hO.core_i i
  have hvΔ := h1 v hv hv0
  have hdim := h3 v hvΔ
  have hr := hO.rank v (hO.subset i hvΔ)
  obtain ⟨u, huV, hu⟩ := exists_mem_notMem_of_finrank_lt
    (U := Submodule.span (ZMod 2) (Δ i)) (S := Submodule.span (ZMod 2) {v})
    (by rw [finrank_span_singleton hv0]; omega)
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  obtain ⟨f, d, hfd, hgu⟩ := exists_transvection_apply_eq
    (a := (⟨v, hv⟩ : Submodule.span (ZMod 2) (Δ i))) (b := ⟨u, huV⟩)
    (fun h => hv0 (congrArg Subtype.val h)) (fun h => hu0 (congrArg Subtype.val h))
  obtain ⟨k, hk, hkg⟩ := h2 (LinearEquiv.transvection hfd)
  have h4 := hkg ⟨v, hv⟩
  rw [hgu, hfixv k hk] at h4
  have h5 : v = u := h4
  exact hu (by rw [← h5]; exact Submodule.mem_span_singleton_self v)

theorem iSupIndep_closure (hO : OrbHyp Gm Δ₀ F Δ) :
    iSupIndep fun i => Subgroup.closure (gens (Δ i) F) := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  refine hO.eq_one_of_fix hg fun v hv => ?_
  have hle : (⨆ j, ⨆ (_ : j ≠ i), Subgroup.closure (gens (Δ j) F)) ≤
      G11.centralizerOn ⊤ (Submodule.span (ZMod 2) (Δ i)) :=
    iSup₂_le fun j hj g' hg' => ⟨Subgroup.mem_top g', fun u hu => hO.fix_of_ne hj hg' hu⟩
  exact (hle hg').2 v hv

end OrbHyp

end CFSG.Quasithin.G31
