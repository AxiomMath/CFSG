module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRootFacts
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs}

private theorem nat_all_iff_r {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h x _
    exact h x.val x.isLt

private theorem tabsOK_rtEq (hT : Chk.tabsOK m T = true) (u t : Root m) :
    Chk.rtEq T (dim m) ((T.rt[u.val]!)[t.val]!) u t 1 = true ∨
      Chk.rtEq T (dim m) ((T.rt[u.val]!)[t.val]!) u t (-1) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  have hrt := nat_all_iff_r.mp (nat_all_iff_r.mp h.2 u.val u.isLt) t.val t.isLt
  exact (Bool.or_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hrt).2

@[expose] def rtR (hT : Chk.tabsOK m T = true) (u t : Root m) : Root m :=
  ⟨(T.rt[u.val]!)[t.val]!, tabsOK_rt_lt hT u t⟩

private theorem reflection_reflection (u : Root m) (v : V m) : reflection m u (reflection m u v) = v :=
  Module.involutive_reflection (root_coroot m u) v

private theorem sum_eps_sub_distrib_r {ι : Type*} [Fintype ι] (a b v : ι → ZMod 3)
    (ε p : ZMod 3) :
    (∑ k, (ε * (a k - p * b k)) * v k) = ε * ((∑ k, a k * v k) - p * ∑ k, b k * v k) := by
  have h1 : (∑ k, (ε * (a k - p * b k)) * v k)
      = ∑ k, (ε * (a k * v k) - (ε * p) * (b k * v k)) :=
    Finset.sum_congr rfl fun k _ => by ring
  have h2 : (∑ k, (ε * (a k * v k) - (ε * p) * (b k * v k)))
      = ∑ k, ε * (a k * v k) - ∑ k, (ε * p) * (b k * v k) :=
    Finset.sum_sub_distrib (s := Finset.univ) _ _
  have h3 : (∑ k, ε * (a k * v k)) = ε * ∑ k, a k * v k :=
    (Finset.mul_sum (s := Finset.univ) (fun k => a k * v k) ε).symm
  have h4 : (∑ k, (ε * p) * (b k * v k)) = (ε * p) * ∑ k, b k * v k :=
    (Finset.mul_sum (s := Finset.univ) (fun k => b k * v k) (ε * p)).symm
  rw [h1, h2, h3, h4]
  ring

private theorem rtEq_spec (hT : Chk.tabsOK m T = true) (u t : Root m) {ε : ℤ}
    (h : Chk.rtEq T (dim m) ((T.rt[u.val]!)[t.val]!) u t ε = true) :
    (∀ v, root m (rtR hT u t) v = (ε : ZMod 3) * root m t (reflection m u v)) ∧
      coroot m (rtR hT u t) = (ε : ZMod 3) • reflection m u (coroot m t) := by
  have hk : ∀ k : Fin (dim m),
      ((F m (rtR hT u t) k : ZMod 3) = (ε : ZMod 3) * ((F m t k : ZMod 3) -
        (pairing m t u : ZMod 3) * (F m u k : ZMod 3))) ∧
      ((H m (rtR hT u t) k : ZMod 3) = (ε : ZMod 3) * ((H m t k : ZMod 3) -
        (pairing m u t : ZMod 3) * (H m u k : ZMod 3))) := by
    intro k
    have hb := (Bool.and_eq_true _ _).mp (nat_all_iff_r.mp h k.val k.isLt)
    rw [beq_iff_eq, beq_iff_eq, RootFacts.int_emod_three_eq_zero_iff,
      RootFacts.int_emod_three_eq_zero_iff] at hb
    rw [← tabsOK_f hT (rtR hT u t) k, ← tabsOK_f hT t k, ← tabsOK_f hT u k,
      ← tabsOK_h hT (rtR hT u t) k, ← tabsOK_h hT t k, ← tabsOK_h hT u k,
      ← tabsOK_pair hT t u, ← tabsOK_pair hT u t]
    obtain ⟨h1, h2⟩ := hb
    push_cast at h1 h2
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  refine ⟨fun v => ?_, ?_⟩
  · rw [root_reflection_apply, root_apply, root_apply, root_apply,
      ← sum_eps_sub_distrib_r (fun k : Fin (dim m) => (F m t k : ZMod 3))
        (fun k => (F m u k : ZMod 3)) v (ε : ZMod 3) (pairing m t u)]
    exact Finset.sum_congr rfl fun k _ => by rw [(hk k).1]
  · funext k
    have h2 := (hk k).2
    change (H m (rtR hT u t) k : ZMod 3) = _
    rw [h2, reflection_apply, pairing_eq]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change _ = (ε : ZMod 3) * ((H m t k : ZMod 3) - (pairing m u t : ZMod 3) * (H m u k : ZMod 3))
    rfl

theorem rtR_spec (hT : Chk.tabsOK m T = true) (u t : Root m) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (∀ v, root m (rtR hT u t) v = (ε : ZMod 3) * root m t (reflection m u v)) ∧
      coroot m (rtR hT u t) = (ε : ZMod 3) • reflection m u (coroot m t) := by
  rcases tabsOK_rtEq hT u t with h | h
  · exact ⟨1, Or.inl rfl, rtEq_spec hT u t h⟩
  · exact ⟨-1, Or.inr rfl, rtEq_spec hT u t h⟩

private theorem sign_sq {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : (ε : ZMod 3) * (ε : ZMod 3) = 1 := by
  rcases hε with rfl | rfl <;> norm_num

private theorem sign_mul {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ε * δ = 1 ∨ ε * δ = -1 := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num

private theorem sign_ne_zero {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : (ε : ZMod 3) ≠ 0 := by
  rcases hε with rfl | rfl <;> decide

private theorem root_rtR_refl (hT : Chk.tabsOK m T = true) {u t : Root m} {ε : ℤ}
    (h : ∀ v, root m (rtR hT u t) v = (ε : ZMod 3) * root m t (reflection m u v)) (w : V m) :
    root m (rtR hT u t) (reflection m u w) = (ε : ZMod 3) * root m t w := by
  rw [h, reflection_reflection]

theorem rtR_injective (hT : Chk.tabsOK m T = true) (u : Root m) :
    Function.Injective (rtR hT u) := by
  intro a b hab
  obtain ⟨εa, hεa, ha, -⟩ := rtR_spec hT u a
  obtain ⟨εb, hεb, hb, -⟩ := rtR_spec hT u b
  refine eq_of_root_eq_sign (sign_mul hεa hεb) fun w => ?_
  have h1 : (εa : ZMod 3) * root m a w = (εb : ZMod 3) * root m b w := by
    rw [← root_rtR_refl hT ha w, hab, root_rtR_refl hT hb w]
  calc root m a w = ((εa : ZMod 3) * (εa : ZMod 3)) * root m a w := by
        rw [sign_sq hεa, one_mul]
    _ = (εa : ZMod 3) * ((εb : ZMod 3) * root m b w) := by rw [mul_assoc, h1]
    _ = ((εa * εb : ℤ) : ZMod 3) * root m b w := by
        rw [Int.cast_mul, mul_assoc]

@[expose] def rtE (hT : Chk.tabsOK m T = true) (u : Root m) : Root m ≃ Root m :=
  Equiv.ofBijective (rtR hT u) (Finite.injective_iff_bijective.mp (rtR_injective hT u))

theorem rtE_apply (hT : Chk.tabsOK m T = true) (u t : Root m) : rtE hT u t = rtR hT u t :=
  rfl

@[expose] def reflCode (hT : Chk.tabsOK m T = true) (u : Root m) :
    Finset (Root m) ≃ Finset (Root m) :=
  (rtE hT u).finsetCongr

theorem reflCode_apply (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    reflCode hT u c = c.map (rtE hT u).toEmbedding :=
  rfl

theorem card_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    (reflCode hT u c).card = c.card := by
  rw [reflCode_apply, Finset.card_map]

theorem vanish_rtR (hT : Chk.tabsOK m T = true) (u : Root m) (U : Submodule (ZMod 3) (V m))
    (t : Root m) :
    Vanish m (U.map (reflection m u : V m →ₗ[ZMod 3] V m)) (rtR hT u t) ↔ Vanish m U t := by
  obtain ⟨ε, hε, h, -⟩ := rtR_spec hT u t
  constructor
  · intro hv x hx
    have hx' : reflection m u x ∈ U.map (reflection m u : V m →ₗ[ZMod 3] V m) :=
      Submodule.mem_map_of_mem hx
    have h0 := hv _ hx'
    rw [root_rtR_refl hT h] at h0
    exact (mul_eq_zero.mp h0).resolve_left (sign_ne_zero hε)
  · intro hv y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change root m (rtR hT u t) (reflection m u x) = 0
    rw [root_rtR_refl hT h, hv x hx, mul_zero]

theorem pairing_rtR_eq_zero_iff (hT : Chk.tabsOK m T = true) (u a b : Root m) :
    pairing m (rtR hT u a) (rtR hT u b) = 0 ↔ pairing m a b = 0 := by
  obtain ⟨εa, hεa, ha, -⟩ := rtR_spec hT u a
  obtain ⟨εb, hεb, -, hb⟩ := rtR_spec hT u b
  rw [pairing_eq_zero_iff, pairing_eq_zero_iff, ← pairing_eq, ← pairing_eq, hb, map_smul,
    root_rtR_refl hT ha, smul_eq_mul, ← mul_assoc]
  constructor
  · intro h0
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (sign_ne_zero hεb) (sign_ne_zero hεa))
  · intro h0
    rw [h0, mul_zero]

theorem adj_rtR_iff (hT : Chk.tabsOK m T = true) (u a b : Root m) :
    Adj m (rtR hT u a) (rtR hT u b) ↔ Adj m a b := by
  unfold Adj
  rw [Ne, Ne, Ne, Ne, pairing_rtR_eq_zero_iff, pairing_rtR_eq_zero_iff]

private theorem isComp_map_aux (e : Root m ≃ Root m) {S S' : Root m → Prop}
    (hS : ∀ t, S' (e t) ↔ S t) (hA : ∀ a b, Adj m (e a) (e b) ↔ Adj m a b)
    {c : Finset (Root m)} (hc : IsComp m S c) : IsComp m S' (c.map e.toEmbedding) := by
  have hS' : ∀ t, S (e.symm t) ↔ S' t := fun t => by rw [← hS (e.symm t), e.apply_symm_apply]
  have hA' : ∀ a b, Adj m (e.symm a) (e.symm b) ↔ Adj m a b := fun a b => by
    rw [← hA (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]
  obtain ⟨hne, hS1, hcl, hmin⟩ := hc
  refine ⟨hne.map, ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_map_equiv] at hi
    exact (hS' i).mp (hS1 _ hi)
  · intro i hi j hj hadj
    rw [Finset.mem_map_equiv] at hi ⊢
    exact hcl _ hi _ ((hS' j).mpr hj) ((hA' i j).mpr hadj)
  · intro T' hT' hTne hTcl
    have hmem : ∀ x, x ∈ T'.map e.symm.toEmbedding ↔ e x ∈ T' := fun x => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
    have key : T'.map e.symm.toEmbedding = c := by
      refine hmin _ (fun x hx => ?_) hTne.map (fun i hi j hj hadj => ?_)
      · have h1 := hT' ((hmem x).mp hx)
        rw [Finset.mem_map_equiv, e.symm_apply_apply] at h1
        exact h1
      · rw [hmem] at hi ⊢
        refine hTcl _ hi _ ?_ ((hA i j).mpr hadj)
        rw [Finset.mem_map_equiv, e.symm_apply_apply]
        exact hj
    ext x
    rw [Finset.mem_map_equiv, ← key, hmem, e.apply_symm_apply]

private theorem isComp_map_iff (e : Root m ≃ Root m) {S S' : Root m → Prop}
    (hS : ∀ t, S' (e t) ↔ S t) (hA : ∀ a b, Adj m (e a) (e b) ↔ Adj m a b)
    (c : Finset (Root m)) : IsComp m S' (c.map e.toEmbedding) ↔ IsComp m S c := by
  refine ⟨fun h => ?_, isComp_map_aux e hS hA⟩
  have hS' : ∀ t, S (e.symm t) ↔ S' t := fun t => by rw [← hS (e.symm t), e.apply_symm_apply]
  have hA' : ∀ a b, Adj m (e.symm a) (e.symm b) ↔ Adj m a b := fun a b => by
    rw [← hA (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]
  have h2 := isComp_map_aux e.symm hS' hA' h
  have hc : (c.map e.toEmbedding).map e.symm.toEmbedding = c := by
    ext x
    simp [Finset.mem_map_equiv]
  rwa [hc] at h2

theorem occurs_reflCode (hT : Chk.tabsOK m T = true) (u : Root m)
    (U : Submodule (ZMod 3) (V m)) (c : Finset (Root m)) :
    occurs m (U.map (reflection m u : V m →ₗ[ZMod 3] V m)) (reflCode hT u c) ↔ occurs m U c :=
  isComp_map_iff (rtE hT u) (fun t => vanish_rtR hT u U t) (fun a b => adj_rtR_iff hT u a b) c

private theorem map_map_reflection (u : Root m) (U : Submodule (ZMod 3) (V m)) :
    (U.map (reflection m u : V m →ₗ[ZMod 3] V m)).map (reflection m u : V m →ₗ[ZMod 3] V m) =
      U := by
  rw [← Submodule.map_comp]
  have h : (reflection m u : V m →ₗ[ZMod 3] V m) ∘ₗ (reflection m u : V m →ₗ[ZMod 3] V m) =
      LinearMap.id := LinearMap.ext fun v => reflection_reflection u v
  rw [h, Submodule.map_id]

private theorem mem_cent_iff' {c : Finset (Root m)} {v : V m} :
    v ∈ cent m c ↔ ∀ i ∈ c, root m i v = 0 := by
  simp [cent, Submodule.mem_iInf]

theorem cent_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    cent m (reflCode hT u c) = (cent m c).map (reflection m u : V m →ₗ[ZMod 3] V m) := by
  ext v
  have hv : v = reflection m u (reflection m u v) := (reflection_reflection u v).symm
  constructor
  · intro h
    rw [hv]
    refine Submodule.mem_map_of_mem (mem_cent_iff'.mpr fun t ht => ?_)
    obtain ⟨ε, hε, hr, -⟩ := rtR_spec hT u t
    have h0 := mem_cent_iff'.mp h (rtR hT u t) (by
      rw [reflCode_apply, Finset.mem_map_equiv]
      change (rtE hT u).symm (rtE hT u t) ∈ c
      rw [Equiv.symm_apply_apply]
      exact ht)
    rw [hr] at h0
    exact (mul_eq_zero.mp h0).resolve_left (sign_ne_zero hε)
  · intro h
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
    refine mem_cent_iff'.mpr fun i hi => ?_
    rw [reflCode_apply, Finset.mem_map_equiv] at hi
    have hi' : rtR hT u ((rtE hT u).symm i) = i := (rtE hT u).apply_symm_apply i
    obtain ⟨ε, hε, hr, -⟩ := rtR_spec hT u ((rtE hT u).symm i)
    rw [← hi']
    change root m (rtR hT u _) (reflection m u y) = 0
    rw [root_rtR_refl hT hr, mem_cent_iff'.mp hy _ hi, mul_zero]

theorem inside_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    inside m (reflCode hT u c) = (inside m c).map (reflection m u : V m →ₗ[ZMod 3] V m) := by
  rw [inside, inside, Submodule.map_span, reflCode_apply, Finset.coe_map]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨ε, -, -, hc⟩ := rtR_spec hT u t
    change coroot m (rtR hT u t) ∈ _
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨coroot m t, ⟨t, ht, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨ε, hε, -, hc⟩ := rtR_spec hT u t
    have hx : (reflection m u : V m →ₗ[ZMod 3] V m) (coroot m t) =
        (ε : ZMod 3) • coroot m (rtR hT u t) := by
      rw [hc, smul_smul, sign_sq hε, one_smul]
      rfl
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rtR hT u t, ⟨t, ht, rfl⟩, rfl⟩)

private theorem reflection_mul_self (u : Root m) : reflection m u * reflection m u = 1 :=
  LinearEquiv.ext fun v => reflection_reflection u v

private theorem reflection_inv (u : Root m) : (reflection m u)⁻¹ = reflection m u :=
  inv_eq_of_mul_eq_one_right (reflection_mul_self u)

theorem weyl_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    weyl m (reflCode hT u c) = (weyl m c).map (MulAut.conj (reflection m u)).toMonoidHom := by
  rw [weyl, weyl, MonoidHom.map_closure, reflCode_apply, Finset.coe_map, Set.image_image,
    Set.image_image]
  congr 1
  refine Set.image_congr fun t _ => ?_
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, reflection_inv]
  exact reflection_rt hT u t

private theorem conj_mem_ker_iff {G A : Type*} [Group G] [CommGroup A] (φ : G →* A) (g y : G) :
    (MulAut.conj g).toMonoidHom y ∈ φ.ker ↔ y ∈ φ.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_mul, map_inv, mul_comm (φ g) (φ y), mul_assoc, mul_inv_cancel, mul_one]

theorem normalizerGroup_reflCode (hT : Chk.tabsOK m T = true) (u : Root m)
    (c : Finset (Root m)) :
    normalizerGroup m (reflCode hT u c) =
      (normalizerGroup m c).map (MulAut.conj (reflection m u)).toMonoidHom := by
  rw [normalizerGroup, normalizerGroup, card_reflCode]
  split_ifs
  · rw [weyl_reflCode]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, ⟨hy, (conj_mem_ker_iff _ _ _).mp hx⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyK⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (conj_mem_ker_iff _ _ _).mpr hyK⟩
  · exact weyl_reflCode hT u c

theorem orthCount_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    orthCount m (reflCode hT u c) = orthCount m c := by
  unfold orthCount
  symm
  refine Finset.card_nbij' (fun p => (rtE hT u p.1, rtE hT u p.2))
    (fun p => ((rtE hT u).symm p.1, (rtE hT u).symm p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp ⊢
    rw [reflCode_apply, Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, rtE_apply, rtE_apply, pairing_rtR_eq_zero_iff]
    exact hp
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp ⊢
    rw [reflCode_apply, Finset.mem_map_equiv, Finset.mem_map_equiv] at hp
    refine ⟨⟨hp.1.1, hp.1.2⟩, ?_⟩
    rw [← pairing_rtR_eq_zero_iff hT u, ← rtE_apply, ← rtE_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact hp.2
  · intro p _
    simp
  · intro p _
    simp

theorem longCount_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m))
    (hm : m.val = 1) : longCount m (reflCode hT u c) = longCount m c := by
  obtain rfl : m = 1 := Fin.ext hm
  have hfix : ∀ t : Root 1, tabFix1.getD (rtR hT u t).val false = tabFix1.getD t.val false := by
    intro t
    obtain ⟨ε, hε, hr, -⟩ := rtR_spec hT u t
    exact tabFix1_eq_of_root hε hr
  unfold longCount
  rw [reflCode_apply, Finset.filter_map, Finset.card_map]
  congr 1
  refine Finset.filter_congr fun t _ => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, rtE_apply, hfix]

theorem label_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    label m (reflCode hT u c) = label m c := by
  have hcard := card_reflCode hT u c
  have horth := orthCount_reflCode hT u c
  obtain ⟨n, hn⟩ := m
  have hlong := longCount_reflCode (m := ⟨n, hn⟩) hT u c
  unfold label
  interval_cases n
  · simp only [hcard]
  · simp only [hcard, hlong rfl]
  all_goals simp only [hcard, horth]

theorem admissible_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) (c : Finset (Root m)) :
    admissible m (reflCode hT u c) ↔ admissible m c := by
  unfold admissible
  rw [label_reflCode]
  constructor
  · rintro ⟨⟨U, hU⟩, hl⟩
    refine ⟨⟨U.map (reflection m u : V m →ₗ[ZMod 3] V m), ?_⟩, hl⟩
    rw [← occurs_reflCode hT u, map_map_reflection]
    exact hU
  · rintro ⟨⟨U, hU⟩, hl⟩
    exact ⟨⟨_, (occurs_reflCode hT u U c).mpr hU⟩, hl⟩

@[expose] def reflFrameAut (hT : Chk.tabsOK m T = true) (u : Root m) : FrameAut (excRaw m) where
  g := reflection m u
  σ := reflCode hT u
  admissible_iff := admissible_reflCode hT u
  occurs_iff := occurs_reflCode hT u
  cent_eq := cent_reflCode hT u
  inside_eq := inside_reflCode hT u
  normalizerGroup_eq := normalizerGroup_reflCode hT u
  label_eq := label_reflCode hT u

theorem reflFrameAut_g (hT : Chk.tabsOK m T = true) (u : Root m) :
    (reflFrameAut hT u).g = reflection m u :=
  rfl

theorem extCasesVx_reflection (hT : Chk.tabsOK m T = true) (u : Root m) {vx : V m}
    (h : ExtCasesVx (excRaw m) vx) : ExtCasesVx (excRaw m) (reflection m u vx) :=
  (reflFrameAut hT u).extCasesVx_map h

end

end CFSG.StandardType.GGQ2Frame.ExcRaw
