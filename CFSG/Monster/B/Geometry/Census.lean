module

public import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

@[expose] def wordWeight (q : ι → ℕ) (ω : List ι) : ℕ := (ω.map q).prod

@[simp] theorem wordWeight_nil (q : ι → ℕ) : wordWeight q [] = 1 := by
  simp [wordWeight]

@[simp] theorem wordWeight_concat (q : ι → ℕ) (ω : List ι) (i : ι) :
    wordWeight q (ω ++ [i]) = wordWeight q ω * q i := by
  simp [wordWeight]

variable (cs) in
@[expose] noncomputable def weylWeight (q : ι → ℕ) (w : W) : ℕ :=
  wordWeight q (cs.exists_isReduced w).choose

@[simp] theorem weylWeight_one (q : ι → ℕ) : weylWeight cs q 1 = 1 := by
  obtain ⟨hred, h⟩ := (cs.exists_isReduced (1 : W)).choose_spec
  have hlen : (cs.exists_isReduced (1 : W)).choose.length = 0 := by
    rw [← hred.eq, ← h, cs.length_one]
  rw [weylWeight, List.length_eq_zero_iff.mp hlen, wordWeight_nil]

section Building

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem dist_eq_simple_of_mem_panel {i : ι} {b d : C} (hd : d ∈ panel cs δ i b) (hne : d ≠ b) :
    δ b d = cs.simple i := by
  rcases (mem_panel_iff hδ).mp hd with h | h
  · exact absurd ((hδ.eq_one_iff b d).mp h).symm hne
  · exact h

omit hδ in
theorem panel_finite_ncard {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    (i : ι) (x : C) : (panel cs δ i x).Finite ∧ (panel cs δ i x).ncard = q i + 1 := by
  have h : (panel cs δ i x).encard = ((q i + 1 : ℕ) : ℕ∞) := by
    rw [hpanel]
    push_cast
    rfl
  exact ⟨Set.finite_of_encard_eq_coe h, by rw [Set.ncard_def, h, ENat.toNat_natCast]⟩

theorem ncard_shell_mul_simple {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    (a : C) {w : W} {i : ι} (hw : cs.length (w * cs.simple i) = cs.length w + 1)
    (hfin : {b | δ a b = w}.Finite) :
    {b | δ a b = w * cs.simple i}.Finite ∧
      {b | δ a b = w * cs.simple i}.ncard = {b | δ a b = w}.ncard * q i := by
  classical
  have hex : ∀ d : ↥{d | δ a d = w * cs.simple i}, ∃ z, δ d.1 z = cs.simple i ∧ δ a z = w := by
    intro d
    have hd : δ a d.1 = w * cs.simple i := d.2
    obtain ⟨z, h1, h2⟩ := hδ.exists_simple a d.1 i
    refine ⟨z, h1, ?_⟩
    rw [h2, hd, mul_assoc, cs.simple_mul_simple_self, mul_one]
  choose φ hφ1 hφ2 using hex
  have hup : ∀ b d : C, δ a b = w → d ∈ panel cs δ i b → d ≠ b → δ a d = w * cs.simple i := by
    intro b d hb hd hne
    rw [← hb]
    exact (hδ.mul_simple a b d i (dist_eq_simple_of_mem_panel hδ hd hne)).2 (by rw [hb]; exact hw)
  have huniq : ∀ b z d : C, δ a b = w → δ a z = w → δ b d = cs.simple i →
      δ z d = cs.simple i → b = z := by
    intro b z d hb hz hbd hzd
    by_contra hne
    have h := (hδ.mul_simple a b z i (dist_eq_simple_of_eq_simple hδ hbd hzd hne)).2
      (by rw [hb]; exact hw)
    rw [hz, hb] at h
    exact cs.simple_ne_one i (left_eq_mul.mp h)
  have hmem : ∀ d : ↥{d | δ a d = w * cs.simple i}, d.1 ∈ panel cs δ i (φ d) \ {φ d} := by
    intro d
    refine ⟨(mem_panel_iff hδ).mpr (Or.inr (hδ.symm_of_eq_simple (hφ1 d))), fun h => ?_⟩
    have h' : d.1 = φ d := h
    have hd : δ a d.1 = w * cs.simple i := d.2
    have h2 := hφ2 d
    rw [← h', hd] at h2
    exact cs.simple_ne_one i (mul_eq_left.mp h2)
  let e : ↥{d | δ a d = w * cs.simple i} ≃
      Σ b : ↥{b | δ a b = w}, ↥(panel cs δ i b.1 \ {b.1}) :=
    { toFun := fun d => ⟨⟨φ d, hφ2 d⟩, d.1, hmem d⟩
      invFun := fun p => ⟨p.2.1, hup p.1.1 p.2.1 p.1.2 p.2.2.1 p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun p => by
        refine Sigma.subtype_ext (Subtype.ext ?_) rfl
        have hd : δ a p.2.1 = w * cs.simple i := hup p.1.1 p.2.1 p.1.2 p.2.2.1 p.2.2.2
        exact (huniq p.1.1 _ p.2.1 p.1.2 (hφ2 ⟨p.2.1, hd⟩)
          (dist_eq_simple_of_mem_panel hδ p.2.2.1 p.2.2.2)
          (hδ.symm_of_eq_simple (hφ1 ⟨p.2.1, hd⟩))).symm }
  have hfib : ∀ b : C, (panel cs δ i b \ {b}).Finite ∧ (panel cs δ i b \ {b}).ncard = q i := by
    intro b
    obtain ⟨hf, hc⟩ := panel_finite_ncard hpanel i b
    exact ⟨hf.sdiff, by rw [Set.ncard_sdiff_singleton_of_mem (self_mem_residue _ b), hc]; rfl⟩
  have : Finite ↥{b | δ a b = w} := hfin.to_subtype
  have : Fintype ↥{b | δ a b = w} := Fintype.ofFinite _
  have : ∀ b : ↥{b | δ a b = w}, Finite ↥(panel cs δ i b.1 \ {b.1}) :=
    fun b => (hfib b.1).1.to_subtype
  have : Finite ↥{d | δ a d = w * cs.simple i} := Finite.of_equiv _ e.symm
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]
  simp only [Nat.card_coe_set_eq, (hfib _).2, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem shell_wordProd {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    (a : C) {ω : List ι} (hω : cs.IsReduced ω) :
    {b | δ a b = cs.wordProd ω}.Finite ∧ {b | δ a b = cs.wordProd ω}.ncard = wordWeight q ω := by
  induction ω using List.reverseRecOn with
  | nil =>
    have h : {b | δ a b = cs.wordProd []} = {a} :=
      Set.ext fun b => by
        rw [Set.mem_ofPred_eq, cs.wordProd_nil, hδ.eq_one_iff, Set.mem_singleton_iff, eq_comm]
    rw [h]
    exact ⟨Set.finite_singleton a, by simp⟩
  | append_singleton ω i ih =>
    obtain ⟨hfin, hcard⟩ := ih (isReduced_of_isReduced_concat hω)
    rw [cs.wordProd_append, cs.wordProd_singleton, wordWeight_concat, ← hcard]
    exact ncard_shell_mul_simple hδ hpanel a (length_mul_simple_of_isReduced_concat hω) hfin

theorem wordWeight_eq_of_wordProd_eq {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) {ω ω' : List ι} (hω : cs.IsReduced ω)
    (hω' : cs.IsReduced ω') (h : cs.wordProd ω = cs.wordProd ω') :
    wordWeight q ω = wordWeight q ω' := by
  obtain ⟨a⟩ := hδ.nonempty
  rw [← (shell_wordProd hδ hpanel a hω).2, ← (shell_wordProd hδ hpanel a hω').2, h]

theorem weylWeight_wordProd {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    {ω : List ι} (hω : cs.IsReduced ω) : weylWeight cs q (cs.wordProd ω) = wordWeight q ω := by
  obtain ⟨h1, h2⟩ := (cs.exists_isReduced (cs.wordProd ω)).choose_spec
  exact wordWeight_eq_of_wordProd_eq hδ hpanel h1 hω h2.symm

theorem shell_finite_ncard {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    (a : C) (w : W) :
    {b | δ a b = w}.Finite ∧ {b | δ a b = w}.ncard = weylWeight cs q w := by
  obtain ⟨hred, hw⟩ := (cs.exists_isReduced w).choose_spec
  have h := shell_wordProd (q := q) hδ hpanel a hred
  rw [← hw] at h
  exact h

theorem encard_shell {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) (a : C)
    (w : W) : {b | δ a b = w}.encard = weylWeight cs q w := by
  obtain ⟨hfin, hcard⟩ := shell_finite_ncard hδ hpanel a w
  rw [← hfin.cast_ncard_eq, hcard]

variable [Finite W]

theorem card_eq_finsum_weylWeight {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) :
    Finite C ∧ Nat.card C = ∑ᶠ w, weylWeight cs q w := by
  obtain ⟨a⟩ := hδ.nonempty
  have : Fintype W := Fintype.ofFinite W
  have : ∀ w : W, Finite {b // δ a b = w} := fun w =>
    (shell_finite_ncard hδ hpanel a w).1.to_subtype
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv (δ a)), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (δ a)), Nat.card_sigma, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun w _ =>
    (Nat.card_coe_set_eq {b | δ a b = w}).trans (shell_finite_ncard hδ hpanel a w).2

theorem ncard_residue_eq_finsum {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) (J : Set ι) (x : C) :
    (residue cs δ J x).ncard = ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w := by
  classical
  have := (card_eq_finsum_weylWeight hδ hpanel).1
  have : Fintype C := Fintype.ofFinite C
  have : Fintype W := Fintype.ofFinite W
  have hres : residue cs δ J x = ↑(Finset.univ.filter fun y => δ x y ∈ cs.parabolic J) := by
    ext y
    simp [mem_residue_iff_mem_parabolic hδ]
  rw [finsum_mem_eq_toFinset_sum, hres, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := δ x) (t := (cs.parabolic J : Set W).toFinset)
      (fun y hy => by simpa using hy)]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : w ∈ cs.parabolic J := by simpa using hw
  rw [← (shell_finite_ncard hδ hpanel x w).2, ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hw', h⟩⟩

theorem ncard_range_residue_mul {q : ι → ℕ} (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1)
    (J : Set ι) :
    (Set.range (residue cs δ J)).ncard * ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w =
      ∑ᶠ w, weylWeight cs q w := by
  classical
  obtain ⟨hC, hcard⟩ := card_eq_finsum_weylWeight hδ hpanel
  have : Fintype C := Fintype.ofFinite C
  rw [← hcard, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := residue cs δ J)
      (t := (Set.range (residue cs δ J)).toFinset) (fun y _ => by simp),
    Set.ncard_eq_toFinset_card', ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun R hR => ?_
  obtain ⟨y, rfl⟩ := Set.mem_toFinset.mp hR
  rw [← ncard_residue_eq_finsum hδ hpanel J y, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact ⟨fun h => residue_eq_of_mem hδ h, fun h => h ▸ self_mem_residue J x⟩

theorem finsum_weylWeight_parabolic_pos {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) (J : Set ι) :
    0 < ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w := by
  have := (card_eq_finsum_weylWeight hδ hpanel).1
  obtain ⟨x⟩ := hδ.nonempty
  rw [← ncard_residue_eq_finsum hδ hpanel J x]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, self_mem_residue J x⟩

theorem ncard_range_residue_eq_div {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) (J : Set ι) :
    (Set.range (residue cs δ J)).ncard =
      (∑ᶠ w, weylWeight cs q w) / ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w := by
  rw [← ncard_range_residue_mul hδ hpanel J,
    Nat.mul_div_cancel _ (finsum_weylWeight_parabolic_pos hδ hpanel J)]

theorem card_eq_card_stabilizer_mul {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) {H : Type*} [Group H] [MulAction H C]
    [MulAction.IsPretransitive H C] (a : C) :
    Nat.card H = Nat.card (MulAction.stabilizer H a) * ∑ᶠ w, weylWeight cs q w := by
  rw [← (card_eq_finsum_weylWeight hδ hpanel).2, ← (MulAction.stabilizer H a).card_mul_index,
    MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]

end Building

theorem weighted_census [Finite W] (hδ : IsWeylDistanceBuilding cs δ) {q : ι → ℕ}
    (hpanel : ∀ i x, (panel cs δ i x).encard = q i + 1) :
    (∀ ω ω' : List ι, cs.IsReduced ω → cs.IsReduced ω' → cs.wordProd ω = cs.wordProd ω' →
      wordWeight q ω = wordWeight q ω') ∧
    (∀ ω : List ι, cs.IsReduced ω → weylWeight cs q (cs.wordProd ω) = wordWeight q ω) ∧
    (∀ (a : C) (w : W), {b | δ a b = w}.encard = weylWeight cs q w) ∧
    (Finite C ∧ Nat.card C = ∑ᶠ w, weylWeight cs q w) ∧
    (∀ (J : Set ι) (x : C),
      (residue cs δ J x).ncard = ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w) ∧
    (∀ J : Set ι,
      (Set.range (residue cs δ J)).ncard * ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w =
        ∑ᶠ w, weylWeight cs q w ∧
      (Set.range (residue cs δ J)).ncard =
        (∑ᶠ w, weylWeight cs q w) / ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w) ∧
    (∀ H : Subgroup (Equiv.Perm C), (∀ x y : C, ∃ h ∈ H, h x = y) →
      Finite H ∧ ∀ a : C,
        Nat.card H = Nat.card (MulAction.stabilizer H a) * ∑ᶠ w, weylWeight cs q w) := by
  refine ⟨fun ω ω' hω hω' h => wordWeight_eq_of_wordProd_eq hδ hpanel hω hω' h,
    fun ω hω => weylWeight_wordProd hδ hpanel hω, encard_shell hδ hpanel,
    card_eq_finsum_weylWeight hδ hpanel, ncard_residue_eq_finsum hδ hpanel,
    fun J => ⟨ncard_range_residue_mul hδ hpanel J, ncard_range_residue_eq_div hδ hpanel J⟩,
    fun H htr => ?_⟩
  have := (card_eq_finsum_weylWeight hδ hpanel).1
  have : MulAction.IsPretransitive H C := ⟨fun x y => by
    obtain ⟨h, hh, rfl⟩ := htr x y
    exact ⟨⟨h, hh⟩, rfl⟩⟩
  exact ⟨inferInstance, card_eq_card_stabilizer_mul hδ hpanel⟩

end CFSG.Monster.B.Geometry
