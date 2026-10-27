module

public import CFSG.Quasithin.Background.B5FinS8Schur

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin

namespace D6

abbrev Ker6 : Subgroup ↥(G6.coreMod 6) :=
  (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)

abbrev Mod6 : Type := ↥(G6.coreMod 6) ⧸ Ker6

@[expose] noncomputable def act6 (σ : Equiv.Perm (Fin 6)) : Mod6 →* Mod6 :=
  (FFModel.symDn_isActionModel 6).modEnd σ

theorem act6_mk (σ : Equiv.Perm (Fin 6)) (m : ↥(G6.coreMod 6)) :
    act6 σ (QuotientGroup.mk m) =
      QuotientGroup.mk (⟨G6.permAct 6 σ m.1, G6.permAct_mem_coreMod σ m.2⟩ : ↥(G6.coreMod 6)) :=
  rfl

@[expose] def ev (i : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1

@[expose] def pv (a b : Fin 6) : Fin 6 → ZMod 2 := ev a + ev b

theorem sum_pv : ∀ a b : Fin 6, ∑ i, pv a b i = 0 := by decide +kernel

@[expose] def pelt (a b : Fin 6) : ↥(G6.coreMod 6) :=
  ⟨Multiplicative.ofAdd (pv a b), (G6.mem_coreMod).2 (sum_pv a b)⟩

@[expose] def pclass (a b : Fin 6) : Mod6 := QuotientGroup.mk (pelt a b)

theorem vec_add_self : ∀ u : Fin 6 → ZMod 2, u + u = 0 := by decide +kernel

theorem mk_eq_mk_iff (x y : ↥(G6.coreMod 6)) :
    (QuotientGroup.mk x : Mod6) = QuotientGroup.mk y ↔
      (Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 = 0 ∨
        Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 = fun _ => 1) := by
  rw [QuotientGroup.eq]
  change x.1⁻¹ * y.1 ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 ↔ _
  rw [Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  have hcore : x.1⁻¹ * y.1 ∈ G6.coreMod 6 := (x⁻¹ * y).2
  have hneg : ∀ u : Fin 6 → ZMod 2, -u = u := by decide +kernel
  have e1 : Multiplicative.toAdd (x.1⁻¹ * y.1) =
      Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 := by
    rw [toAdd_mul, toAdd_inv, hneg]
  constructor
  · rintro ⟨h | h, -⟩
    · left
      rw [← e1, h]
      rfl
    · right
      rw [← e1, h]
      rfl
  · rintro (h | h)
    · exact ⟨Or.inl (Multiplicative.toAdd.injective (by rw [e1, h]; rfl)), hcore⟩
    · exact ⟨Or.inr (Multiplicative.toAdd.injective (by rw [e1, h]; rfl)), hcore⟩

theorem permAct_pv (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    G6.permAct 6 σ (Multiplicative.ofAdd (pv a b)) = Multiplicative.ofAdd (pv (σ a) (σ b)) := by
  apply Multiplicative.toAdd.injective
  funext i
  change pv a b (σ⁻¹ i) = pv (σ a) (σ b) i
  have h1 : (σ⁻¹ i = a) ↔ (i = σ a) := by rw [Equiv.Perm.inv_eq_iff_eq]
  have h2 : (σ⁻¹ i = b) ↔ (i = σ b) := by rw [Equiv.Perm.inv_eq_iff_eq]
  simp only [pv, ev, Pi.add_apply, Pi.single_apply, h1, h2]

theorem act6_pclass (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    act6 σ (pclass a b) = pclass (σ a) (σ b) := by
  rw [pclass, act6_mk, pclass]
  congr 1
  exact Subtype.ext (permAct_pv σ a b)

@[expose] def ca : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def cb : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

theorem ca_cb_apply : ca 0 = 1 ∧ ca 1 = 2 ∧ ca 2 = 0 ∧ ca 3 = 3 ∧ ca 4 = 4 ∧ ca 5 = 5 ∧
    cb 0 = 0 ∧ cb 1 = 1 ∧ cb 2 = 2 ∧ cb 3 = 4 ∧ cb 4 = 5 ∧ cb 5 = 3 := by
  decide

abbrev FixCond (f : Fin 6 → Fin 6) (v : Fin 6 → ZMod 2) : Prop :=
  v + (fun i => v (f i)) = 0 ∨ v + (fun i => v (f i)) = fun _ => 1

theorem cb_inv_apply : ∀ i : Fin 6, cb⁻¹ i = (if i = 4 then 3 else if i = 5 then 4 else
    if i = 3 then 5 else i) := by
  decide +kernel

theorem ca_inv_apply : ∀ i : Fin 6, ca⁻¹ i = (if i = 1 then 0 else if i = 2 then 1 else
    if i = 0 then 2 else i) := by
  decide +kernel

theorem fixed_cb : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    FixCond (fun i => if i = 4 then 3 else if i = 5 then 4 else if i = 3 then 5 else i) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 0 1 ∨ v = pv 0 1 + (fun _ => 1) ∨ v = pv 1 2 ∨
      v = pv 1 2 + (fun _ => 1) ∨ v = pv 0 2 ∨ v = pv 0 2 + (fun _ => 1) := by
  decide +kernel

theorem fixed_ca : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    FixCond (fun i => if i = 1 then 0 else if i = 2 then 1 else if i = 0 then 2 else i) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 3 4 ∨ v = pv 3 4 + (fun _ => 1) ∨ v = pv 4 5 ∨
      v = pv 4 5 + (fun _ => 1) ∨ v = pv 3 5 ∨ v = pv 3 5 + (fun _ => 1) := by
  decide +kernel

theorem exists_pv_sum6 : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    ∃ c₁ c₂ c₃ c₄ c₅ : ZMod 2, v = c₁.val • pv 0 1 + c₂.val • pv 1 2 + c₃.val • pv 3 4 +
      c₄.val • pv 4 5 + c₅.val • (fun _ => 1) := by
  decide +kernel

theorem pclass_ne : pclass 0 1 ≠ 1 ∧ pclass 3 4 ≠ 1 ∧ pclass 1 2 ≠ pclass 0 1 ∧
    pclass 2 0 ≠ pclass 0 1 ∧ pclass 4 5 ≠ pclass 3 4 ∧ pclass 5 3 ≠ pclass 3 4 := by
  have h : ∀ a b c d : Fin 6, ¬ (pv a b + pv c d = 0 ∨ pv a b + pv c d = fun _ => 1) →
      pclass a b ≠ pclass c d := by
    intro a b c d hn he
    exact hn ((mk_eq_mk_iff _ _).1 he)
  have h1 : ∀ a b : Fin 6, ¬ (pv a b + 0 = 0 ∨ pv a b + 0 = fun _ => 1) → pclass a b ≠ 1 := by
    intro a b hn he
    exact hn ((mk_eq_mk_iff (pelt a b) 1).1 he)
  refine ⟨h1 0 1 (by decide), h1 3 4 (by decide), h 1 2 0 1 (by decide), h 2 0 0 1 (by decide),
    h 4 5 3 4 (by decide), h 5 3 3 4 (by decide)⟩

theorem fix_cb_class (q : Mod6) (hq : act6 cb q = q) :
    q = 1 ∨ q = pclass 0 1 ∨ q = pclass 1 2 ∨ q = pclass 2 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  have hfix : FixCond (fun i => if i = 4 then 3 else if i = 5 then 4 else if i = 3 then 5 else i)
      (Multiplicative.toAdd x.1) := by
    rw [act6_mk] at hq
    have h2 := (mk_eq_mk_iff _ _).1 hq
    have h3 : Multiplicative.toAdd (G6.permAct 6 cb x.1) = fun i =>
        Multiplicative.toAdd x.1 (if i = 4 then 3 else if i = 5 then 4 else if i = 3 then 5
          else i) := by
      funext i
      exact congrArg (Multiplicative.toAdd x.1) (cb_inv_apply i)
    have h4 : Multiplicative.toAdd (⟨G6.permAct 6 cb x.1,
        G6.permAct_mem_coreMod cb x.2⟩ : ↥(G6.coreMod 6)).1 = _ := h3
    rw [h4] at h2
    rcases h2 with h2 | h2
    · left
      rw [add_comm]
      exact h2
    · right
      rw [add_comm]
      exact h2
  have hmk : ∀ (w : Fin 6 → ZMod 2) (hw : ∑ i, w i = 0),
      (Multiplicative.toAdd x.1 + w = 0 ∨ Multiplicative.toAdd x.1 + w = fun _ => 1) →
      (QuotientGroup.mk x : Mod6) =
        QuotientGroup.mk (⟨Multiplicative.ofAdd w, (G6.mem_coreMod).2 hw⟩ : ↥(G6.coreMod 6)) :=
    fun w hw h => (mk_eq_mk_iff _ _).2 h
  rcases fixed_cb _ hvsum hfix with h | h | h | h | h | h | h | h
  · left
    refine (hmk 0 (by decide) (Or.inl (by rw [h, add_zero]))).trans rfl
  · left
    refine (hmk 0 (by decide) (Or.inr (by rw [h, add_zero]))).trans rfl
  · right; left
    exact hmk (pv 0 1) (sum_pv 0 1) (Or.inl (by rw [h, vec_add_self]))
  · right; left
    refine hmk (pv 0 1) (sum_pv 0 1) (Or.inr ?_)
    rw [h, add_right_comm, vec_add_self, zero_add]
  · right; right; left
    exact hmk (pv 1 2) (sum_pv 1 2) (Or.inl (by rw [h, vec_add_self]))
  · right; right; left
    refine hmk (pv 1 2) (sum_pv 1 2) (Or.inr ?_)
    rw [h, add_right_comm, vec_add_self, zero_add]
  · right; right; right
    have e : pv 0 2 = pv 2 0 := by decide
    refine hmk (pv 2 0) (sum_pv 2 0) (Or.inl ?_)
    rw [h, e, vec_add_self]
  · right; right; right
    have e : pv 0 2 = pv 2 0 := by decide
    refine hmk (pv 2 0) (sum_pv 2 0) (Or.inr ?_)
    rw [h, e, add_right_comm, vec_add_self, zero_add]

theorem fix_ca_class (q : Mod6) (hq : act6 ca q = q) :
    q = 1 ∨ q = pclass 3 4 ∨ q = pclass 4 5 ∨ q = pclass 5 3 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  have hfix : FixCond (fun i => if i = 1 then 0 else if i = 2 then 1 else if i = 0 then 2 else i)
      (Multiplicative.toAdd x.1) := by
    rw [act6_mk] at hq
    have h2 := (mk_eq_mk_iff _ _).1 hq
    have h3 : Multiplicative.toAdd (G6.permAct 6 ca x.1) = fun i =>
        Multiplicative.toAdd x.1 (if i = 1 then 0 else if i = 2 then 1 else if i = 0 then 2
          else i) := by
      funext i
      exact congrArg (Multiplicative.toAdd x.1) (ca_inv_apply i)
    have h4 : Multiplicative.toAdd (⟨G6.permAct 6 ca x.1,
        G6.permAct_mem_coreMod ca x.2⟩ : ↥(G6.coreMod 6)).1 = _ := h3
    rw [h4] at h2
    rcases h2 with h2 | h2
    · left
      rw [add_comm]
      exact h2
    · right
      rw [add_comm]
      exact h2
  have hmk : ∀ (w : Fin 6 → ZMod 2) (hw : ∑ i, w i = 0),
      (Multiplicative.toAdd x.1 + w = 0 ∨ Multiplicative.toAdd x.1 + w = fun _ => 1) →
      (QuotientGroup.mk x : Mod6) =
        QuotientGroup.mk (⟨Multiplicative.ofAdd w, (G6.mem_coreMod).2 hw⟩ : ↥(G6.coreMod 6)) :=
    fun w hw h => (mk_eq_mk_iff _ _).2 h
  rcases fixed_ca _ hvsum hfix with h | h | h | h | h | h | h | h
  · left
    refine (hmk 0 (by decide) (Or.inl (by rw [h, add_zero]))).trans rfl
  · left
    refine (hmk 0 (by decide) (Or.inr (by rw [h, add_zero]))).trans rfl
  · right; left
    exact hmk (pv 3 4) (sum_pv 3 4) (Or.inl (by rw [h, vec_add_self]))
  · right; left
    refine hmk (pv 3 4) (sum_pv 3 4) (Or.inr ?_)
    rw [h, add_right_comm, vec_add_self, zero_add]
  · right; right; left
    exact hmk (pv 4 5) (sum_pv 4 5) (Or.inl (by rw [h, vec_add_self]))
  · right; right; left
    refine hmk (pv 4 5) (sum_pv 4 5) (Or.inr ?_)
    rw [h, add_right_comm, vec_add_self, zero_add]
  · right; right; right
    have e : pv 3 5 = pv 5 3 := by decide
    refine hmk (pv 5 3) (sum_pv 5 3) (Or.inl ?_)
    rw [h, e, vec_add_self]
  · right; right; right
    have e : pv 3 5 = pv 5 3 := by decide
    refine hmk (pv 5 3) (sum_pv 5 3) (Or.inr ?_)
    rw [h, e, add_right_comm, vec_add_self, zero_add]

@[expose] def oneElt : ↥(G6.coreMod 6) :=
  ⟨G6.allOnes 6, (G6.mem_coreMod).2 (by decide +kernel)⟩

theorem mk_oneElt : (QuotientGroup.mk oneElt : Mod6) = 1 := by
  change (QuotientGroup.mk oneElt : Mod6) = QuotientGroup.mk 1
  rw [mk_eq_mk_iff]
  right
  change (fun _ => (1 : ZMod 2)) + 0 = fun _ => 1
  rw [add_zero]

theorem eq_of_comm_sylow (φ : Mod6 →* Mod6) (hinj : Function.Injective φ)
    (ha : ∀ q, φ (act6 ca q) = act6 ca (φ q)) (hb : ∀ q, φ (act6 cb q) = act6 cb (φ q))
    (h2 : ∀ q, φ (φ q) = q) : ∀ q, φ q = q := by
  obtain ⟨hu1, hw1, h12, h20, h45, h53⟩ := pclass_ne
  obtain ⟨a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5⟩ := ca_cb_apply
  have e1 : act6 ca (pclass 0 1) = pclass 1 2 := by rw [act6_pclass, a0, a1]
  have e2 : act6 ca (pclass 1 2) = pclass 2 0 := by rw [act6_pclass, a1, a2]
  have e3 : act6 ca (pclass 2 0) = pclass 0 1 := by rw [act6_pclass, a2, a0]
  have f1 : act6 cb (pclass 3 4) = pclass 4 5 := by rw [act6_pclass, b3, b4]
  have f2 : act6 cb (pclass 4 5) = pclass 5 3 := by rw [act6_pclass, b4, b5]
  have f3 : act6 cb (pclass 5 3) = pclass 3 4 := by rw [act6_pclass, b5, b3]
  have hu : φ (pclass 0 1) = pclass 0 1 := by
    have hfix : act6 cb (φ (pclass 0 1)) = φ (pclass 0 1) := by
      rw [← hb, act6_pclass, b0, b1]
    rcases fix_cb_class _ hfix with h | h | h | h
    · exact absurd (hinj (h.trans (map_one φ).symm)) hu1
    · exact h
    · exfalso
      have h' : φ (φ (pclass 0 1)) = pclass 2 0 := by rw [h, ← e1, ha, h, e2]
      exact h20 (h'.symm.trans (h2 _))
    · exfalso
      have h' : φ (φ (pclass 0 1)) = pclass 1 2 := by
        rw [h, ← e2, ha, ← e1, ha, h, e3, e1]
      exact h12 (h'.symm.trans (h2 _))
  have hw : φ (pclass 3 4) = pclass 3 4 := by
    have hfix : act6 ca (φ (pclass 3 4)) = φ (pclass 3 4) := by
      rw [← ha, act6_pclass, a3, a4]
    rcases fix_ca_class _ hfix with h | h | h | h
    · exact absurd (hinj (h.trans (map_one φ).symm)) hw1
    · exact h
    · exfalso
      have h' : φ (φ (pclass 3 4)) = pclass 5 3 := by rw [h, ← f1, hb, h, f2]
      exact h53 (h'.symm.trans (h2 _))
    · exfalso
      have h' : φ (φ (pclass 3 4)) = pclass 4 5 := by
        rw [h, ← f2, hb, ← f1, hb, h, f3, f1]
      exact h45 (h'.symm.trans (h2 _))
  have hu2 : φ (pclass 1 2) = pclass 1 2 := by rw [← e1, ha, hu]
  have hw2 : φ (pclass 4 5) = pclass 4 5 := by rw [← f1, hb, hw]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := exists_pv_sum6 _ hvsum
  have hx : x = (pelt 0 1) ^ c₁.val * (pelt 1 2) ^ c₂.val * (pelt 3 4) ^ c₃.val *
      (pelt 4 5) ^ c₄.val * oneElt ^ c₅.val := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, toAdd_mul, toAdd_pow]
    exact hc
  rw [hx]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow]
  rw [mk_oneElt, map_one, one_pow]
  change φ (pclass 0 1) ^ c₁.val * φ (pclass 1 2) ^ c₂.val * φ (pclass 3 4) ^ c₃.val *
      φ (pclass 4 5) ^ c₄.val * 1 = pclass 0 1 ^ c₁.val * pclass 1 2 ^ c₂.val *
      pclass 3 4 ^ c₃.val * pclass 4 5 ^ c₄.val * 1
  rw [hu, hu2, hw, hw2]

end D6

namespace D8

open CFSG.Quasithin.B5FinS8

abbrev ca : Equiv.Perm (Fin 8) := cyc 0 1 2

abbrev cb : Equiv.Perm (Fin 8) := cyc 3 4 5

theorem ca_cb_apply : ca 0 = 1 ∧ ca 1 = 2 ∧ ca 2 = 0 ∧ ca 3 = 3 ∧ ca 4 = 4 ∧ ca 5 = 5 ∧
    ca 6 = 6 ∧ ca 7 = 7 ∧ cb 0 = 0 ∧ cb 1 = 1 ∧ cb 2 = 2 ∧ cb 3 = 4 ∧ cb 4 = 5 ∧ cb 5 = 3 ∧
    cb 6 = 6 ∧ cb 7 = 7 := by
  decide

theorem ca_inv : ∀ i : Fin 8, ca⁻¹ i = inv3 0 1 2 i := by decide +kernel

theorem cb_inv : ∀ i : Fin 8, cb⁻¹ i = inv3 3 4 5 i := by decide +kernel

abbrev NormCond (f : Fin 8 → Fin 8) (v : Fin 8 → ZMod 2) : Prop :=
  v + (fun i => v (f i)) + (fun i => v (f (f i))) = 0 ∨
    v + (fun i => v (f i)) + (fun i => v (f (f i))) = fun _ => 1

theorem fixed_cb_norm : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → FixCond (inv3 3 4 5) v →
    NormCond (inv3 0 1 2) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 0 1 ∨ v = pv 0 1 + (fun _ => 1) ∨ v = pv 1 2 ∨
      v = pv 1 2 + (fun _ => 1) ∨ v = pv 2 0 ∨ v = pv 2 0 + (fun _ => 1) := by
  decide +kernel

theorem fixed_ca_norm : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → FixCond (inv3 0 1 2) v →
    NormCond (inv3 3 4 5) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 3 4 ∨ v = pv 3 4 + (fun _ => 1) ∨ v = pv 4 5 ∨
      v = pv 4 5 + (fun _ => 1) ∨ v = pv 5 3 ∨ v = pv 5 3 + (fun _ => 1) := by
  decide +kernel

@[expose] def tv : Fin 8 → ZMod 2 := pv 0 1 + pv 2 6

theorem fixed_cab : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → FixCond (inv3 0 1 2) v →
    FixCond (inv3 3 4 5) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 6 7 ∨ v = pv 6 7 + (fun _ => 1) ∨ v = tv ∨
      v = tv + (fun _ => 1) ∨ v = pv 6 7 + tv ∨ v = pv 6 7 + tv + (fun _ => 1) := by
  decide +kernel

theorem exists_sum8 : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 →
    ∃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ZMod 2, v = c₁.val • pv 0 1 + c₂.val • pv 1 2 + c₃.val • pv 3 4 +
      c₄.val • pv 4 5 + c₅.val • pv 6 7 + c₆.val • tv + c₇.val • (fun _ => 1) := by
  decide +kernel

theorem toAdd_permAct_cyc {f : Fin 8 → Fin 8} {σ : Equiv.Perm (Fin 8)} (hf : ∀ i, σ⁻¹ i = f i)
    (x : ↥(G6.coreMod 8)) :
    Multiplicative.toAdd (⟨G6.permAct 8 σ x.1, G6.permAct_mem_coreMod σ x.2⟩ :
      ↥(G6.coreMod 8)).1 = fun i => Multiplicative.toAdd x.1 (f i) := by
  funext i
  exact congrArg (Multiplicative.toAdd x.1) (hf i)

theorem mk_eq_pclass {x : ↥(G6.coreMod 8)} {a b : Fin 8}
    (h : Multiplicative.toAdd x.1 = pv a b ∨ Multiplicative.toAdd x.1 = pv a b + fun _ => 1) :
    (QuotientGroup.mk x : Mod8) = pclass a b := by
  rw [pclass, mk_eq_mk_iff]
  rcases h with h | h
  · left
    change Multiplicative.toAdd x.1 + pv a b = 0
    rw [h, vec_add_self]
  · right
    change Multiplicative.toAdd x.1 + pv a b = fun _ => 1
    rw [h, add_right_comm, vec_add_self, zero_add]

theorem mk_eq_one {x : ↥(G6.coreMod 8)}
    (h : Multiplicative.toAdd x.1 = 0 ∨ Multiplicative.toAdd x.1 = fun _ => 1) :
    (QuotientGroup.mk x : Mod8) = 1 := by
  change (QuotientGroup.mk x : Mod8) = QuotientGroup.mk 1
  rw [mk_eq_mk_iff]
  rcases h with h | h
  · left
    change Multiplicative.toAdd x.1 + 0 = 0
    rw [h, add_zero]
  · right
    change Multiplicative.toAdd x.1 + 0 = fun _ => 1
    rw [h, add_zero]

theorem fixCond_of_fixed {f : Fin 8 → Fin 8} {σ : Equiv.Perm (Fin 8)} (hf : ∀ i, σ⁻¹ i = f i)
    (x : ↥(G6.coreMod 8)) (hq : act8 σ (QuotientGroup.mk x) = QuotientGroup.mk x) :
    FixCond f (Multiplicative.toAdd x.1) := by
  rw [act8_mk] at hq
  have h2 := (mk_eq_mk_iff _ _).1 hq
  rw [toAdd_permAct_cyc hf x] at h2
  rcases h2 with h2 | h2
  · left
    rw [add_comm]
    exact h2
  · right
    rw [add_comm]
    exact h2

theorem normCond_of_norm {f : Fin 8 → Fin 8} {σ : Equiv.Perm (Fin 8)} (hf : ∀ i, σ⁻¹ i = f i)
    (x : ↥(G6.coreMod 8))
    (hq : QuotientGroup.mk x * act8 σ (QuotientGroup.mk x) *
      act8 σ (act8 σ (QuotientGroup.mk x)) = (1 : Mod8)) :
    NormCond f (Multiplicative.toAdd x.1) := by
  rw [act8_mk, act8_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hq
  change (QuotientGroup.mk _ : Mod8) = QuotientGroup.mk 1 at hq
  have h2 := (mk_eq_mk_iff _ _).1 hq
  have e : Multiplicative.toAdd ((x * ⟨G6.permAct 8 σ x.1, G6.permAct_mem_coreMod σ x.2⟩ *
      ⟨G6.permAct 8 σ (⟨G6.permAct 8 σ x.1, G6.permAct_mem_coreMod σ x.2⟩ :
        ↥(G6.coreMod 8)).1, G6.permAct_mem_coreMod σ
          (⟨G6.permAct 8 σ x.1, G6.permAct_mem_coreMod σ x.2⟩ : ↥(G6.coreMod 8)).2⟩ :
        ↥(G6.coreMod 8)).1) + Multiplicative.toAdd (1 : ↥(G6.coreMod 8)).1 =
      Multiplicative.toAdd x.1 + (fun i => Multiplicative.toAdd x.1 (f i)) +
        (fun i => Multiplicative.toAdd x.1 (f (f i))) := by
    funext i
    simp only [Subgroup.coe_mul, toAdd_mul, Pi.add_apply, OneMemClass.coe_one, toAdd_one,
      Pi.zero_apply, add_zero]
    rw [G6.permAct_apply, G6.permAct_apply, G6.permAct_apply, hf, hf]
  rw [e] at h2
  exact h2

theorem fix_cb_class (q : Mod8) (hb : act8 cb q = q)
    (hn : q * act8 ca q * act8 ca (act8 ca q) = 1) :
    q = 1 ∨ q = pclass 0 1 ∨ q = pclass 1 2 ∨ q = pclass 2 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  rcases fixed_cb_norm _ hvsum (fixCond_of_fixed cb_inv x hb) (normCond_of_norm ca_inv x hn) with
    h | h | h | h | h | h | h | h
  · exact Or.inl (mk_eq_one (Or.inl h))
  · exact Or.inl (mk_eq_one (Or.inr h))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inl h)))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inl (mk_eq_pclass (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl (mk_eq_pclass (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (mk_eq_pclass (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (mk_eq_pclass (Or.inr h))))

theorem fix_ca_class (q : Mod8) (ha : act8 ca q = q)
    (hn : q * act8 cb q * act8 cb (act8 cb q) = 1) :
    q = 1 ∨ q = pclass 3 4 ∨ q = pclass 4 5 ∨ q = pclass 5 3 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  rcases fixed_ca_norm _ hvsum (fixCond_of_fixed ca_inv x ha) (normCond_of_norm cb_inv x hn) with
    h | h | h | h | h | h | h | h
  · exact Or.inl (mk_eq_one (Or.inl h))
  · exact Or.inl (mk_eq_one (Or.inr h))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inl h)))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inl (mk_eq_pclass (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl (mk_eq_pclass (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (mk_eq_pclass (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (mk_eq_pclass (Or.inr h))))

@[expose] def tclass : Mod8 :=
  QuotientGroup.mk (⟨Multiplicative.ofAdd tv, (G6.mem_coreMod).2 (by decide +kernel)⟩ :
    ↥(G6.coreMod 8))

@[expose] def oneElt : ↥(G6.coreMod 8) :=
  ⟨G6.allOnes 8, (G6.mem_coreMod).2 (by decide +kernel)⟩

theorem mk_oneElt : (QuotientGroup.mk oneElt : Mod8) = 1 := mk_eq_one (Or.inr rfl)

theorem mul_self8 (q : Mod8) : q * q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_mul]
  refine mk_eq_one (Or.inl ?_)
  change Multiplicative.toAdd x.1 + Multiplicative.toAdd x.1 = 0
  exact vec_add_self _

theorem inv8 (q : Mod8) : q⁻¹ = q := inv_eq_of_mul_eq_one_right (mul_self8 q)

theorem mul_comm8 (x y : Mod8) : x * y = y * x := by
  calc x * y = (x * y)⁻¹ := (inv8 _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv8, inv8]

theorem fix_p0 : act8 ca (pclass 6 7) = pclass 6 7 ∧ act8 cb (pclass 6 7) = pclass 6 7 := by
  obtain ⟨-, -, -, -, -, -, a6, a7, -, -, -, -, -, -, b6, b7⟩ := ca_cb_apply
  exact ⟨by rw [act8_pclass, a6, a7], by rw [act8_pclass, b6, b7]⟩

theorem tv_fix : (fun i => tv (inv3 0 1 2 i)) = tv ∧ (fun i => tv (inv3 3 4 5 i)) = tv := by
  decide +kernel

theorem fix_t0 : act8 ca tclass = tclass ∧ act8 cb tclass = tclass := by
  constructor
  · rw [tclass, act8_mk, mk_eq_mk_iff]
    left
    rw [toAdd_permAct_cyc ca_inv]
    change (fun i => tv (inv3 0 1 2 i)) + tv = 0
    rw [tv_fix.1, vec_add_self]
  · rw [tclass, act8_mk, mk_eq_mk_iff]
    left
    rw [toAdd_permAct_cyc cb_inv]
    change (fun i => tv (inv3 3 4 5 i)) + tv = 0
    rw [tv_fix.2, vec_add_self]

theorem rearr (r a b c d : Mod8) :
    r * a * b * 1 * (r * c * d * 1)⁻¹ = (a * c⁻¹) * (b * d⁻¹) := by
  calc r * a * b * 1 * (r * c * d * 1)⁻¹ = r * (a * b * (c * d)⁻¹) * r⁻¹ := by group
    _ = (a * b * (c * d)⁻¹) * r * r⁻¹ := by rw [mul_comm8 r]
    _ = a * b * (d⁻¹ * c⁻¹) := by rw [mul_inv_rev]; group
    _ = a * (b * d⁻¹) * c⁻¹ := by group
    _ = a * c⁻¹ * (b * d⁻¹) := by rw [mul_assoc a, mul_comm8 (b * d⁻¹), ← mul_assoc]

theorem fix_cab_class (q : Mod8) (ha : act8 ca q = q) (hb : act8 cb q = q) :
    q = 1 ∨ q = pclass 6 7 ∨ q = tclass ∨ q = pclass 6 7 * tclass := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  have hpt : pclass 6 7 * tclass = QuotientGroup.mk (⟨Multiplicative.ofAdd (pv 6 7 + tv),
      (G6.mem_coreMod).2 (by decide +kernel)⟩ : ↥(G6.coreMod 8)) := by
    rw [pclass, tclass, ← QuotientGroup.mk_mul]
    rfl
  have hmk : ∀ (w : Fin 8 → ZMod 2) (hw : ∑ i, w i = 0),
      (Multiplicative.toAdd x.1 = w ∨ Multiplicative.toAdd x.1 = w + fun _ => 1) →
      (QuotientGroup.mk x : Mod8) =
        QuotientGroup.mk (⟨Multiplicative.ofAdd w, (G6.mem_coreMod).2 hw⟩ : ↥(G6.coreMod 8)) := by
    intro w hw h
    rw [mk_eq_mk_iff]
    rcases h with h | h
    · left
      change Multiplicative.toAdd x.1 + w = 0
      rw [h, vec_add_self]
    · right
      change Multiplicative.toAdd x.1 + w = fun _ => 1
      rw [h, add_right_comm, vec_add_self, zero_add]
  rcases fixed_cab _ hvsum (fixCond_of_fixed ca_inv x ha) (fixCond_of_fixed cb_inv x hb) with
    h | h | h | h | h | h | h | h
  · exact Or.inl (mk_eq_one (Or.inl h))
  · exact Or.inl (mk_eq_one (Or.inr h))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inl h)))
  · exact Or.inr (Or.inl (mk_eq_pclass (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inl (hmk tv (by decide +kernel) (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl (hmk tv (by decide +kernel) (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (hpt ▸ hmk (pv 6 7 + tv) (by decide +kernel) (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (hpt ▸ hmk (pv 6 7 + tv) (by decide +kernel) (Or.inr h))))

theorem pclass_norm (a b c : Fin 8) (h : pv a b + pv b c + pv c a = 0) :
    pclass a b * pclass b c * pclass c a = 1 := by
  rw [pclass, pclass, pclass, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  refine mk_eq_one (Or.inl ?_)
  exact h

theorem classes_ne : pclass 0 1 ≠ 1 ∧ pclass 3 4 ≠ 1 ∧ pclass 1 2 ≠ pclass 0 1 ∧
    pclass 2 0 ≠ pclass 0 1 ∧ pclass 4 5 ≠ pclass 3 4 ∧ pclass 5 3 ≠ pclass 3 4 ∧
    pclass 6 7 ≠ 1 ∧ tclass ≠ 1 ∧ pclass 6 7 ≠ tclass := by
  have h : ∀ (x y : Fin 8 → ZMod 2) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0),
      ¬ (x + y = 0 ∨ x + y = fun _ => 1) →
      (QuotientGroup.mk (⟨Multiplicative.ofAdd x, (G6.mem_coreMod).2 hx⟩ : ↥(G6.coreMod 8)) :
        Mod8) ≠ QuotientGroup.mk (⟨Multiplicative.ofAdd y, (G6.mem_coreMod).2 hy⟩ :
          ↥(G6.coreMod 8)) := by
    intro x y hx hy hn he
    exact hn ((mk_eq_mk_iff _ _).1 he)
  have hone : (1 : Mod8) = QuotientGroup.mk (⟨Multiplicative.ofAdd 0, (G6.mem_coreMod).2
      (by decide +kernel)⟩ : ↥(G6.coreMod 8)) := rfl
  have h0 : ∑ i, (0 : Fin 8 → ZMod 2) i = 0 := by decide +kernel
  have ht : ∑ i, tv i = 0 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hone]; exact h _ _ (sum_pv 0 1) h0 (by decide +kernel)
  · rw [hone]; exact h _ _ (sum_pv 3 4) h0 (by decide +kernel)
  · exact h _ _ (sum_pv 1 2) (sum_pv 0 1) (by decide +kernel)
  · exact h _ _ (sum_pv 2 0) (sum_pv 0 1) (by decide +kernel)
  · exact h _ _ (sum_pv 4 5) (sum_pv 3 4) (by decide +kernel)
  · exact h _ _ (sum_pv 5 3) (sum_pv 3 4) (by decide +kernel)
  · rw [hone]; exact h _ _ (sum_pv 6 7) h0 (by decide +kernel)
  · rw [hone]; exact h _ _ ht h0 (by decide +kernel)
  · exact h _ _ (sum_pv 6 7) ht (by decide +kernel)

theorem exists_comm_values (φ : Mod8 →* Mod8) (hinj : Function.Injective φ)
    (ha : ∀ q, φ (act8 ca q) = act8 ca (φ q)) (hb : ∀ q, φ (act8 cb q) = act8 cb (φ q))
    (h2 : ∀ q, φ (φ q) = q) : ∃ x : Mod8, ∀ q, φ q * q⁻¹ = 1 ∨ φ q * q⁻¹ = x := by
  let inst : CommGroup Mod8 := { (inferInstance : Group Mod8) with mul_comm := mul_comm8 }
  obtain ⟨hu1, hw1, h12, h20, h45, h53, hp1, ht1, hpt⟩ := classes_ne
  obtain ⟨a0, a1, a2, a3, a4, a5, -, -, b0, b1, b2, b3, b4, b5, -, -⟩ := ca_cb_apply
  have e1 : act8 ca (pclass 0 1) = pclass 1 2 := by rw [act8_pclass, a0, a1]
  have e2 : act8 ca (pclass 1 2) = pclass 2 0 := by rw [act8_pclass, a1, a2]
  have e3 : act8 ca (pclass 2 0) = pclass 0 1 := by rw [act8_pclass, a2, a0]
  have f1 : act8 cb (pclass 3 4) = pclass 4 5 := by rw [act8_pclass, b3, b4]
  have f2 : act8 cb (pclass 4 5) = pclass 5 3 := by rw [act8_pclass, b4, b5]
  have f3 : act8 cb (pclass 5 3) = pclass 3 4 := by rw [act8_pclass, b5, b3]
  have hu : φ (pclass 0 1) = pclass 0 1 := by
    have hfix : act8 cb (φ (pclass 0 1)) = φ (pclass 0 1) := by
      rw [← hb, act8_pclass, b0, b1]
    have hn : φ (pclass 0 1) * act8 ca (φ (pclass 0 1)) * act8 ca (act8 ca (φ (pclass 0 1))) =
        1 := by
      rw [← ha, ← ha, ← map_mul, ← map_mul, e1, e2, pclass_norm 0 1 2 (by decide +kernel),
        map_one]
    rcases fix_cb_class _ hfix hn with h | h | h | h
    · exact absurd (hinj (h.trans (map_one φ).symm)) hu1
    · exact h
    · exfalso
      have h' : φ (φ (pclass 0 1)) = pclass 2 0 := by rw [h, ← e1, ha, h, e2]
      exact h20 (h'.symm.trans (h2 _))
    · exfalso
      have h' : φ (φ (pclass 0 1)) = pclass 1 2 := by
        rw [h, ← e2, ha, ← e1, ha, h, e3, e1]
      exact h12 (h'.symm.trans (h2 _))
  have hw : φ (pclass 3 4) = pclass 3 4 := by
    have hfix : act8 ca (φ (pclass 3 4)) = φ (pclass 3 4) := by
      rw [← ha, act8_pclass, a3, a4]
    have hn : φ (pclass 3 4) * act8 cb (φ (pclass 3 4)) * act8 cb (act8 cb (φ (pclass 3 4))) =
        1 := by
      rw [← hb, ← hb, ← map_mul, ← map_mul, f1, f2, pclass_norm 3 4 5 (by decide +kernel),
        map_one]
    rcases fix_ca_class _ hfix hn with h | h | h | h
    · exact absurd (hinj (h.trans (map_one φ).symm)) hw1
    · exact h
    · exfalso
      have h' : φ (φ (pclass 3 4)) = pclass 5 3 := by rw [h, ← f1, hb, h, f2]
      exact h53 (h'.symm.trans (h2 _))
    · exfalso
      have h' : φ (φ (pclass 3 4)) = pclass 4 5 := by
        rw [h, ← f2, hb, ← f1, hb, h, f3, f1]
      exact h45 (h'.symm.trans (h2 _))
  have hu2 : φ (pclass 1 2) = pclass 1 2 := by rw [← e1, ha, hu]
  have hw2 : φ (pclass 4 5) = pclass 4 5 := by rw [← f1, hb, hw]
  have hφB : ∀ q, act8 ca q = q → act8 cb q = q → act8 ca (φ q) = φ q ∧ act8 cb (φ q) = φ q :=
    fun q hqa hqb => ⟨by rw [← ha, hqa], by rw [← hb, hqb]⟩
  set p0 := pclass 6 7 with hp0
  set t0 := tclass with ht0
  have hφp := hφB p0 fix_p0.1 fix_p0.2
  have hφt := hφB t0 fix_t0.1 fix_t0.2
  set A := φ p0 * p0⁻¹ with hA
  set B := φ t0 * t0⁻¹ with hB
  have hAB : A = 1 ∨ B = 1 ∨ A = B := by
    rcases fix_cab_class _ hφp.1 hφp.2 with h | h | h | h
    · exact absurd (hinj (h.trans (map_one φ).symm)) hp1
    · left; rw [hA, h, mul_inv_cancel]
    · rcases fix_cab_class _ hφt.1 hφt.2 with k | k | k | k
      · exact absurd (hinj (k.trans (map_one φ).symm)) ht1
      · right; right
        rw [hA, hB, h, k, inv8, inv8]
        exact mul_comm8 _ _
      · right; left; rw [hB, k, mul_inv_cancel]
      · exfalso
        have h' : φ (φ p0) = p0 * t0 := by rw [h, k]
        apply ht1
        have h3 : p0 * t0 = p0 := h'.symm.trans (h2 _)
        calc t0 = p0⁻¹ * (p0 * t0) := by group
          _ = 1 := by rw [h3, inv_mul_cancel]
    · rcases fix_cab_class _ hφt.1 hφt.2 with k | k | k | k
      · exact absurd (hinj (k.trans (map_one φ).symm)) ht1
      · exfalso
        have h' : φ (φ t0) = p0 * t0 := by rw [k, h]
        apply hp1
        have h3 : p0 * t0 = t0 := h'.symm.trans (h2 _)
        calc p0 = (p0 * t0) * t0⁻¹ := by group
          _ = 1 := by rw [h3, mul_inv_cancel]
      · right; left; rw [hB, k, mul_inv_cancel]
      · exfalso
        exact hpt (hinj (h.trans k.symm))
  have hval : ∀ q, ∃ c₅ c₆ : ℕ, φ q * q⁻¹ = A ^ c₅ * B ^ c₆ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
    obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, hc⟩ := exists_sum8 _ hvsum
    have hx : x = (pelt 0 1) ^ c₁.val * (pelt 1 2) ^ c₂.val * (pelt 3 4) ^ c₃.val *
        (pelt 4 5) ^ c₄.val * (pelt 6 7) ^ c₅.val *
        (⟨Multiplicative.ofAdd tv, (G6.mem_coreMod).2 (by decide +kernel)⟩ :
          ↥(G6.coreMod 8)) ^ c₆.val * oneElt ^ c₇.val := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, toAdd_mul, toAdd_pow]
      exact hc
    refine ⟨c₅.val, c₆.val, ?_⟩
    rw [hx]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow]
    rw [mk_oneElt, map_one, one_pow]
    change φ (pclass 0 1) ^ c₁.val * φ (pclass 1 2) ^ c₂.val * φ (pclass 3 4) ^ c₃.val *
        φ (pclass 4 5) ^ c₄.val * φ p0 ^ c₅.val * φ t0 ^ c₆.val * 1 *
        (pclass 0 1 ^ c₁.val * pclass 1 2 ^ c₂.val * pclass 3 4 ^ c₃.val *
          pclass 4 5 ^ c₄.val * p0 ^ c₅.val * t0 ^ c₆.val * 1)⁻¹ = A ^ c₅.val * B ^ c₆.val
    rw [hu, hu2, hw, hw2, rearr, hA, hB, mul_pow, mul_pow, inv_pow, inv_pow]
  have hpow : ∀ (y : Mod8) (c : ℕ), y ^ c = 1 ∨ y ^ c = y := by
    intro y c
    induction c with
    | zero => left; rw [pow_zero]
    | succ c ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h, mul_self8]
  rcases hAB with h | h | h
  · refine ⟨B, fun q => ?_⟩
    obtain ⟨c₅, c₆, hq⟩ := hval q
    rw [hq, h, one_pow, one_mul]
    exact hpow B c₆
  · refine ⟨A, fun q => ?_⟩
    obtain ⟨c₅, c₆, hq⟩ := hval q
    rw [hq, h, one_pow, mul_one]
    exact hpow A c₅
  · refine ⟨A, fun q => ?_⟩
    obtain ⟨c₅, c₆, hq⟩ := hval q
    rw [hq, ← h, ← pow_add]
    exact hpow A (c₅ + c₆)

end D8

end CFSG.Quasithin.H13.A6
