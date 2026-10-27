module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.C41Pf.AltN

open CFSG.QuasithinUnique Equiv Equiv.Perm
open scoped commutatorElement

section Fix2

variable {n : ℕ}

@[expose] def fix2 (a b : Fin n) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {g | (g : Perm (Fin n)) a = a ∧ (g : Perm (Fin n)) b = b}
  mul_mem' := by
    rintro g h ⟨hga, hgb⟩ ⟨hha, hhb⟩
    refine ⟨?_, ?_⟩
    · show (g : Perm (Fin n)) ((h : Perm (Fin n)) a) = a
      rw [hha, hga]
    · show (g : Perm (Fin n)) ((h : Perm (Fin n)) b) = b
      rw [hhb, hgb]
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := by
    rintro g ⟨hga, hgb⟩
    refine ⟨?_, ?_⟩
    · show (g : Perm (Fin n))⁻¹ a = a
      rw [Perm.inv_eq_iff_eq, hga]
    · show (g : Perm (Fin n))⁻¹ b = b
      rw [Perm.inv_eq_iff_eq, hgb]

theorem mem_fix2 {a b : Fin n} {g : alternatingGroup (Fin n)} :
    g ∈ fix2 a b ↔ (g : Perm (Fin n)) a = a ∧ (g : Perm (Fin n)) b = b :=
  Iff.rfl

abbrev Cpl (a b : Fin n) : Type := {i : Fin n // i ≠ a ∧ i ≠ b}

theorem card_cpl {a b : Fin n} (hab : a ≠ b) : Fintype.card (Cpl a b) = n - 2 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin n => i ≠ a ∧ i ≠ b) = Finset.univ \ {a, b} := by
    ext i
    simp [not_or]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hab]

@[expose] noncomputable def cplEquiv {a b : Fin n} (hab : a ≠ b) : Fin (n - 2) ≃ Cpl a b :=
  (Fintype.equivFinOfCardEq (card_cpl hab)).symm

theorem cpl_iff {a b : Fin n} {g : Perm (Fin n)} (ha : g a = a) (hb : g b = b) (i : Fin n) :
    (g i ≠ a ∧ g i ≠ b) ↔ (i ≠ a ∧ i ≠ b) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (h ▸ ha), fun h => h2 (h ▸ hb)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (g.injective (h.trans ha.symm)), fun h => h2 (g.injective (h.trans hb.symm))⟩

variable {a b : Fin n} (hab : a ≠ b)

@[expose] noncomputable def resPerm (g : ↥(fix2 a b)) : Perm (Fin (n - 2)) :=
  (cplEquiv hab).symm.permCongr (((g : alternatingGroup (Fin n)) : Perm (Fin n)).subtypePerm
    (cpl_iff g.2.1 g.2.2))

theorem resPerm_apply (g : ↥(fix2 a b)) (i : Fin (n - 2)) :
    ((cplEquiv hab (resPerm hab g i) : Cpl a b) : Fin n) =
      ((g : alternatingGroup (Fin n)) : Perm (Fin n)) (cplEquiv hab i) := by
  simp [resPerm, Equiv.permCongr_apply]

theorem resPerm_inv_apply (g : ↥(fix2 a b)) (i : Fin (n - 2)) :
    ((cplEquiv hab ((resPerm hab g)⁻¹ i) : Cpl a b) : Fin n) =
      ((g : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ (cplEquiv hab i) := by
  rw [Perm.eq_inv_iff_eq, ← resPerm_apply]
  simp

@[expose] noncomputable def emb (i : Fin (n - 2)) : Fin n := (cplEquiv hab i : Fin n)

theorem emb_injective : Function.Injective (emb hab) := fun _ _ h =>
  (cplEquiv hab).injective (Subtype.ext h)

theorem emb_ne (i : Fin (n - 2)) : emb hab i ≠ a ∧ emb hab i ≠ b := (cplEquiv hab i).2

theorem emb_resPerm (g : ↥(fix2 a b)) (i : Fin (n - 2)) :
    emb hab (resPerm hab g i) = ((g : alternatingGroup (Fin n)) : Perm (Fin n)) (emb hab i) :=
  resPerm_apply hab g i

theorem emb_resPerm_inv (g : ↥(fix2 a b)) (i : Fin (n - 2)) :
    emb hab ((resPerm hab g)⁻¹ i) = ((g : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ (emb hab i) :=
  resPerm_inv_apply hab g i

theorem resPerm_mul (g h : ↥(fix2 a b)) : resPerm hab (g * h) = resPerm hab g * resPerm hab h := by
  ext i
  apply congrArg Fin.val
  apply emb_injective hab
  rw [Perm.mul_apply, emb_resPerm, emb_resPerm, emb_resPerm]
  rfl

theorem sign_resPerm (g : ↥(fix2 a b)) : sign (resPerm hab g) = 1 := by
  rw [resPerm, sign_permCongr, sign_subtypePerm _ _ fun x hx =>
    ⟨fun h => hx (by rw [h]; exact g.2.1), fun h => hx (by rw [h]; exact g.2.2)⟩]
  exact (g : alternatingGroup (Fin n)).2

theorem resPerm_one : resPerm hab (1 : ↥(fix2 a b)) = 1 := by
  ext i
  apply congrArg Fin.val
  apply emb_injective hab
  rw [emb_resPerm]
  rfl

@[expose] noncomputable def resHom : ↥(fix2 a b) →* alternatingGroup (Fin (n - 2)) where
  toFun g := ⟨resPerm hab g, by rw [mem_alternatingGroup, sign_resPerm]⟩
  map_one' := Subtype.ext (resPerm_one hab)
  map_mul' g h := Subtype.ext (resPerm_mul hab g h)

theorem coe_resHom (g : ↥(fix2 a b)) :
    ((resHom hab g : alternatingGroup (Fin (n - 2))) : Perm (Fin (n - 2))) = resPerm hab g := rfl

theorem resHom_injective : Function.Injective (resHom hab) := by
  intro g h hgh
  have hp : resPerm hab g = resPerm hab h := congrArg Subtype.val hgh
  apply Subtype.ext
  apply Subtype.ext
  ext x
  apply congrArg Fin.val
  by_cases hxa : x = a
  · rw [hxa, g.2.1, h.2.1]
  by_cases hxb : x = b
  · rw [hxb, g.2.2, h.2.2]
  obtain ⟨i, hi⟩ := (cplEquiv hab).surjective ⟨x, hxa, hxb⟩
  have hx : x = emb hab i := by rw [emb, hi]
  rw [hx, ← emb_resPerm, ← emb_resPerm, hp]

theorem resHom_surjective : Function.Surjective (resHom hab) := by
  intro τ
  set f : Perm (Cpl a b) := (cplEquiv hab).permCongr (τ : Perm (Fin (n - 2))) with hf
  have hfa : ofSubtype f a = a := ofSubtype_apply_of_not_mem f (by simp)
  have hfb : ofSubtype f b = b := ofSubtype_apply_of_not_mem f (by simp)
  have hsign : ofSubtype f ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, sign_ofSubtype, hf, sign_permCongr]
    exact τ.2
  refine ⟨⟨⟨ofSubtype f, hsign⟩, hfa, hfb⟩, ?_⟩
  apply Subtype.ext
  ext i
  apply congrArg Fin.val
  apply emb_injective hab
  rw [coe_resHom, emb_resPerm]
  show ofSubtype f (emb hab i) = emb hab ((τ : Perm (Fin (n - 2))) i)
  rw [ofSubtype_apply_of_mem f (emb_ne hab i)]
  simp [hf, emb, Equiv.permCongr_apply]

@[expose] noncomputable def resEquiv : ↥(fix2 a b) ≃* alternatingGroup (Fin (n - 2)) :=
  MulEquiv.ofBijective (resHom hab) ⟨resHom_injective hab, resHom_surjective hab⟩

include hab in
theorem isSimpleGroup_fix2 (hn : 7 ≤ n) : IsSimpleGroup ↥(fix2 a b) := by
  have : IsSimpleGroup (alternatingGroup (Fin (n - 2))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact (resEquiv hab).isSimpleGroup

theorem comm_swap_of_mem_fix2 {g : alternatingGroup (Fin n)} (hg : g ∈ fix2 a b) :
    (g : Perm (Fin n)) * swap a b = swap a b * g := by
  rw [mul_swap_eq_swap_mul, hg.1, hg.2]

omit hab in
theorem fix_or_swap (hab : a ≠ b) {g : Perm (Fin n)} (hg : g * swap a b = swap a b * g) :
    (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  have h1 : g b = swap a b (g a) := by
    have := congrArg (fun f : Perm (Fin n) => f a) hg
    simpa [Perm.mul_apply] using this
  by_cases ha : g a = a
  · left
    rw [ha, swap_apply_left] at h1
    exact ⟨ha, h1⟩
  by_cases hb : g a = b
  · right
    rw [hb, swap_apply_right] at h1
    exact ⟨hb, h1⟩
  exfalso
  rw [swap_apply_of_ne_of_ne ha hb] at h1
  exact hab (g.injective h1).symm

include hab in
theorem le_fix2_of_perfect {X : Subgroup (alternatingGroup (Fin n))}
    (hX : ∀ x ∈ X, (x : Perm (Fin n)) * swap a b = swap a b * x) (hperf : ⁅X, X⁆ = X) :
    X ≤ fix2 a b := by
  rw [← hperf, Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_fix2]
  have key : ∀ g : Perm (Fin n), g * swap a b = swap a b * g →
      (g a = a ∧ g b = b ∧ g⁻¹ a = a ∧ g⁻¹ b = b) ∨
        (g a = b ∧ g b = a ∧ g⁻¹ a = b ∧ g⁻¹ b = a) := by
    intro g hg
    rcases fix_or_swap hab hg with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, hb, by rw [Perm.inv_eq_iff_eq, ha], by rw [Perm.inv_eq_iff_eq, hb]⟩
    · exact Or.inr ⟨ha, hb, by rw [Perm.inv_eq_iff_eq, hb], by rw [Perm.inv_eq_iff_eq, ha]⟩
  have e : ((⁅x, y⁆ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      (x : Perm (Fin n)) * y * (x : Perm (Fin n))⁻¹ * (y : Perm (Fin n))⁻¹ := rfl
  rw [e]
  rcases key _ (hX x hx) with ⟨h1, h2, h5, h6⟩ | ⟨h1, h2, h5, h6⟩ <;>
    rcases key _ (hX y hy) with ⟨h3, h4, h7, h8⟩ | ⟨h3, h4, h7, h8⟩ <;>
    simp only [Perm.mul_apply, h1, h2, h3, h4, h5, h6, h7, h8, and_self]

end Fix2

section Heart

variable (m : ℕ)

@[expose] def pwHom (σ : Perm (Fin m)) : ↥(evenWeight m) →+ ↥(evenWeight m) where
  toFun := permWeight m σ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permWeight_apply (σ : Perm (Fin m)) (x : ↥(evenWeight m)) (i : Fin m) :
    (permWeight m σ x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i) := rfl

theorem permWeight_mem_constWeight (σ : Perm (Fin m)) {x : ↥(evenWeight m)}
    (hx : x ∈ constWeight m) : permWeight m σ x ∈ constWeight m := fun _ _ => hx _ _

@[expose] def hAct (σ : Perm (Fin m)) : AltHeart m →+ AltHeart m :=
  QuotientAddGroup.map _ _ (pwHom m σ) fun _ hx => permWeight_mem_constWeight m σ hx

theorem hAct_mk (σ : Perm (Fin m)) (x : ↥(evenWeight m)) :
    hAct m σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (permWeight m σ x) := rfl

variable {m}

theorem hAct_eq_of_blockType {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin m)} {β : ↥(blockU L) →* Multiplicative (AltHeart m)}
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight m), (QuotientAddGroup.mk x : AltHeart m) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight m (α ℓ : Perm (Fin m)) x) : AltHeart m) =
          Multiplicative.toAdd (β v))
    (ℓ : ↥L) (u v : ↥(blockU L)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (β v) = hAct m (α ℓ : Perm (Fin m)) (Multiplicative.toAdd (β u)) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
  rw [← hx, hAct_mk]
  exact (hβe ℓ u v h x hx).symm

theorem heart_add_self (y : AltHeart m) : y + y = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 := Subtype.ext (funext fun i => CharTwo.add_self_eq_zero _)
  rw [this]
  rfl

theorem heart_add_comm (y z : AltHeart m) : y + z = z + y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
  congr 1
  exact Subtype.ext (funext fun i => show (x : Fin m → ZMod 2) i + (x' : Fin m → ZMod 2) i =
    (x' : Fin m → ZMod 2) i + (x : Fin m → ZMod 2) i from add_comm _ _)

@[expose] def pairVec (i j : Fin m) : ↥(evenWeight m) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Pi.add_apply,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true]
    decide⟩

theorem pairVec_apply (i j k : Fin m) :
    ((pairVec i j : ↥(evenWeight m)) : Fin m → ZMod 2) k =
      (Pi.single i 1 : Fin m → ZMod 2) k + (Pi.single j 1 : Fin m → ZMod 2) k :=
  rfl

theorem permWeight_pairVec (σ : Perm (Fin m)) (i j : Fin m) :
    permWeight m σ (pairVec i j) = pairVec (σ i) (σ j) := by
  apply Subtype.ext
  funext k
  rw [permWeight_apply, pairVec_apply, pairVec_apply]
  simp only [Pi.single_apply, Perm.inv_eq_iff_eq]

theorem pairVec_sub (i j k : Fin m) : pairVec i j - pairVec i k = pairVec j k := by
  apply Subtype.ext
  funext l
  show ((pairVec i j : ↥(evenWeight m)) : Fin m → ZMod 2) l -
    ((pairVec i k : ↥(evenWeight m)) : Fin m → ZMod 2) l =
      ((pairVec j k : ↥(evenWeight m)) : Fin m → ZMod 2) l
  rw [pairVec_apply, pairVec_apply, pairVec_apply]
  generalize (Pi.single i 1 : Fin m → ZMod 2) l = A
  generalize (Pi.single j 1 : Fin m → ZMod 2) l = B
  generalize (Pi.single k 1 : Fin m → ZMod 2) l = C
  revert A B C
  decide

theorem exists_ne_two (hm : 3 ≤ m) (i j : Fin m) : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
  by_contra h
  push Not at h
  have hk : ∀ k : Fin m, k.val = i.val ∨ k.val = j.val := by
    intro k
    by_cases hki : k = i
    · exact Or.inl (congrArg Fin.val hki)
    · exact Or.inr (congrArg Fin.val (h k hki))
  have h0 := hk ⟨0, by omega⟩
  have h1 := hk ⟨1, by omega⟩
  have h2 := hk ⟨2, by omega⟩
  simp only at h0 h1 h2
  omega

theorem mk_pairVec_ne_zero (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    (QuotientAddGroup.mk (pairVec i j) : AltHeart m) ≠ 0 := by
  rw [Ne, QuotientAddGroup.eq_zero_iff]
  intro hc
  obtain ⟨k, hki, hkj⟩ := exists_ne_two hm i j
  have := hc i k
  rw [pairVec_apply, pairVec_apply] at this
  simp [hij, hki, hkj] at this

theorem alt_two_transitive (hm : 4 ≤ m) {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ τ : Perm (Fin m), τ ∈ alternatingGroup (Fin m) ∧ τ a = c ∧ τ b = d := by
  have h4 := alternatingGroup.isMultiplyPretransitive (Fin m)
  have hc : Nat.card (Fin m) - 2 = m - 2 := by simp
  rw [hc] at h4
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin m)) (Fin m) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := m - 2) (by omega)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  let x : Fin 2 ↪ Fin m := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin m := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin m)) x y
  refine ⟨g, g.2, ?_, ?_⟩
  · exact congrArg (fun e : Fin 2 ↪ Fin m => e 0) hg
  · exact congrArg (fun e : Fin 2 ↪ Fin m => e 1) hg

private theorem zmod2_cases (u v w : ZMod 2) (h : u ≠ v) :
    (w = u ∧ u + w = 0 ∧ v + u = 1 ∧ w + v = 1) ∨ (w = v ∧ u + w = 1 ∧ v + u = 1 ∧ w + v = 0) := by
  revert u v w; decide

theorem exists_pairVec_add (x : ↥(evenWeight m)) {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hx : (x : Fin m → ZMod 2) i ≠ (x : Fin m → ZMod 2) j) :
    ∃ a b : Fin m, a ≠ b ∧ x + permWeight m (swap i j * swap j k) x = pairVec a b := by
  have hσ : ∀ p, (swap i j * swap j k)⁻¹ p = swap j k (swap i j p) := by
    intro p
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply]
  have hval : ∀ p, ((x + permWeight m (swap i j * swap j k) x : ↥(evenWeight m)) :
      Fin m → ZMod 2) p = (x : Fin m → ZMod 2) p +
        (x : Fin m → ZMod 2) (swap j k (swap i j p)) := by
    intro p
    show (x : Fin m → ZMod 2) p + (x : Fin m → ZMod 2) ((swap i j * swap j k)⁻¹ p) = _
    rw [hσ]
  have hi : swap j k (swap i j i) = k := by rw [swap_apply_left, swap_apply_left]
  have hj : swap j k (swap i j j) = i := by
    rw [swap_apply_right, swap_apply_of_ne_of_ne hij hik]
  have hk : swap j k (swap i j k) = j := by
    rw [swap_apply_of_ne_of_ne hik.symm hjk.symm, swap_apply_right]
  have ho : ∀ p, p ≠ i → p ≠ j → p ≠ k → swap j k (swap i j p) = p := by
    intro p hpi hpj hpk
    rw [swap_apply_of_ne_of_ne hpi hpj, swap_apply_of_ne_of_ne hpj hpk]
  rcases zmod2_cases ((x : Fin m → ZMod 2) i) ((x : Fin m → ZMod 2) j)
    ((x : Fin m → ZMod 2) k) hx with ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
  · refine ⟨j, k, hjk, Subtype.ext (funext fun p => ?_)⟩
    rw [hval, pairVec_apply]
    by_cases hpi : p = i
    · subst hpi; rw [hi, h1]; simp [hij, hik]
    by_cases hpj : p = j
    · subst hpj; rw [hj, h2]; simp [hjk]
    by_cases hpk : p = k
    · subst hpk; rw [hk, h3]; simp [hjk.symm]
    rw [ho p hpi hpj hpk, CharTwo.add_self_eq_zero]
    simp [hpj, hpk]
  · refine ⟨i, j, hij, Subtype.ext (funext fun p => ?_)⟩
    rw [hval, pairVec_apply]
    by_cases hpi : p = i
    · subst hpi; rw [hi, h1]; simp [hij]
    by_cases hpj : p = j
    · subst hpj; rw [hj, h2]; simp [hij.symm]
    by_cases hpk : p = k
    · subst hpk; rw [hk, h3]; simp [hik.symm, hjk.symm]
    rw [ho p hpi hpj hpk, CharTwo.add_self_eq_zero]
    simp [hpi, hpj]

theorem eq_top_of_pairVec_mem (Y : AddSubgroup ↥(evenWeight m))
    (h : ∀ a b, a ≠ b → pairVec a b ∈ Y) : Y = ⊤ := by
  suffices key : ∀ k, ∀ x : ↥(evenWeight m),
      (Finset.univ.filter fun p => (x : Fin m → ZMod 2) p ≠ 0).card = k → x ∈ Y from
    eq_top_iff.mpr fun x _ => key _ x rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      exact Y.zero_mem
    obtain ⟨i, hi⟩ : ∃ i, (x : Fin m → ZMod 2) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (Subtype.ext (funext hcon))
    have hsum : ∑ p, (x : Fin m → ZMod 2) p = 0 := by
      have := x.2
      simpa [evenWeight] using this
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ (x : Fin m → ZMod 2) j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hs : ∑ p, (x : Fin m → ZMod 2) p = (x : Fin m → ZMod 2) i :=
        Finset.sum_eq_single i (fun p _ hp => hcon p hp) (by simp)
      exact hi (hs ▸ hsum)
    have hone : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by decide
    have hxi := hone _ hi
    have hxj := hone _ hj
    set x' := x + pairVec i j with hx'def
    have hx' : x = x' + pairVec i j := by
      rw [hx'def, add_assoc, ← two_nsmul]
      have : (2 : ℕ) • pairVec i j = 0 := by
        apply Subtype.ext
        funext p
        show (2 : ℕ) • ((pairVec i j : ↥(evenWeight m)) : Fin m → ZMod 2) p = 0
        rw [two_nsmul, CharTwo.add_self_eq_zero]
      rw [this, add_zero]
    have hval : ∀ p, (x' : Fin m → ZMod 2) p =
        (x : Fin m → ZMod 2) p + (Pi.single i 1 : Fin m → ZMod 2) p +
          (Pi.single j 1 : Fin m → ZMod 2) p := by
      intro p
      show (x : Fin m → ZMod 2) p + ((Pi.single i 1 : Fin m → ZMod 2) p +
        (Pi.single j 1 : Fin m → ZMod 2) p) = _
      rw [add_assoc]
    have hsub : (Finset.univ.filter fun p => (x' : Fin m → ZMod 2) p ≠ 0) ⊂
        (Finset.univ.filter fun p => (x : Fin m → ZMod 2) p ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, by simp [hi], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        rw [hval, hxi]
        simp [hji.symm]
        decide
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro hp0
        apply hp
        rw [hval, hp0]
        by_cases hpi : p = i
        · subst hpi
          exact absurd hp0 hi
        by_cases hpj : p = j
        · subst hpj
          exact absurd hp0 hj
        simp [hpi, hpj]
    have hlt := Finset.card_lt_card hsub
    rw [hx] at hlt
    rw [hx']
    exact Y.add_mem (ih _ hlt x' rfl) (h i j hji.symm)

theorem heart_irreducible (hm : 4 ≤ m) (Y : AddSubgroup (AltHeart m))
    (hY : ∀ σ ∈ alternatingGroup (Fin m), ∀ y ∈ Y, hAct m σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hyY⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hbot
  have hy0' : y ≠ 0 := fun h => hy0 (Subtype.ext h)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hnc : x ∉ constWeight m := fun h => hy0' (by
    rw [QuotientAddGroup.eq_zero_iff]
    exact h)
  obtain ⟨i, j, hij⟩ : ∃ i j, (x : Fin m → ZMod 2) i ≠ (x : Fin m → ZMod 2) j := by
    by_contra hcon
    push Not at hcon
    exact hnc hcon
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨k, hki, hkj⟩ := exists_ne_two (by omega) i j
  have hσ : swap i j * swap j k ∈ alternatingGroup (Fin m) := by
    rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hne, Perm.sign_swap (Ne.symm hkj)]
    decide
  obtain ⟨a, b, hab, he⟩ := exists_pairVec_add x hne hki.symm hkj.symm hij
  have hpair : (QuotientAddGroup.mk (pairVec a b) : AltHeart m) ∈ Y := by
    have := Y.add_mem hyY (hY _ hσ _ hyY)
    rw [hAct_mk, ← QuotientAddGroup.mk_add, he] at this
    exact this
  have hall : ∀ c d, c ≠ d → (QuotientAddGroup.mk (pairVec c d) : AltHeart m) ∈ Y := by
    intro c d hcd
    obtain ⟨τ, hτ, hτa, hτb⟩ := alt_two_transitive hm hab hcd
    have := hY τ hτ _ hpair
    rwa [hAct_mk, permWeight_pairVec, hτa, hτb] at this
  have hY' := eq_top_of_pairVec_mem (Y.comap (QuotientAddGroup.mk' (constWeight m)))
    (fun c d hcd => hall c d hcd)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have : w ∈ Y.comap (QuotientAddGroup.mk' (constWeight m)) := hY' ▸ AddSubgroup.mem_top w
  exact this

@[expose] def pairSub (y : AltHeart m) : AddSubgroup (AltHeart m) where
  carrier := {z | z = 0 ∨ z = y}
  add_mem' := by
    rintro _ _ (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add _)
    · exact Or.inr (add_zero _)
    · exact Or.inl (heart_add_self _)
  zero_mem' := Or.inl rfl
  neg_mem' := by
    rintro _ (rfl | rfl)
    · exact Or.inl neg_zero
    · exact Or.inr (neg_eq_iff_add_eq_zero.mpr (heart_add_self _))

theorem not_isPGroup_two_alt (hm : 3 ≤ m) : ¬ IsPGroup 2 (alternatingGroup (Fin m)) := by
  intro h
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  have h02 : (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp
  have h12 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp
  have hc := Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  obtain ⟨k, hk⟩ := h ⟨_, hc.mem_alternatingGroup⟩
  have hk' := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk'
  have h3 := orderOf_dvd_of_pow_eq_one hk'
  rw [hc.orderOf] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem heart_fixed_eq_zero (hm : 4 ≤ m) (y : AltHeart m)
    (hy : ∀ σ ∈ alternatingGroup (Fin m), hAct m σ y = y) : y = 0 := by
  have hinv : ∀ σ ∈ alternatingGroup (Fin m), ∀ z ∈ pairSub y, hAct m σ z ∈ pairSub y := by
    rintro σ hσ _ (rfl | rfl)
    · exact Or.inl (map_zero _)
    · exact Or.inr (hy σ hσ)
  rcases heart_irreducible hm (pairSub y) hinv with h | h
  · have : y ∈ pairSub y := Or.inr rfl
    rw [h] at this
    exact this
  · exfalso
    have h0 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
    have h1 : (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp
    have h2 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp
    have hp1 : (QuotientAddGroup.mk (pairVec ⟨0, by omega⟩ ⟨1, by omega⟩) : AltHeart m) ∈
        pairSub y := h ▸ AddSubgroup.mem_top _
    have hp2 : (QuotientAddGroup.mk (pairVec ⟨0, by omega⟩ ⟨2, by omega⟩) : AltHeart m) ∈
        pairSub y := h ▸ AddSubgroup.mem_top _
    rcases hp1 with hp1 | hp1
    · exact mk_pairVec_ne_zero (by omega) h0 hp1
    rcases hp2 with hp2 | hp2
    · exact mk_pairVec_ne_zero (by omega) h1 hp2
    have h3 : (QuotientAddGroup.mk (pairVec (⟨1, by omega⟩ : Fin m) ⟨2, by omega⟩) :
        AltHeart m) = 0 := by
      rw [← pairVec_sub, QuotientAddGroup.mk_sub, hp1, hp2, sub_self]
    exact mk_pairVec_ne_zero (by omega) h2 h3

end Heart

section Res

variable {n : ℕ} {a b : Fin n} (hab : a ≠ b) (i0 : Fin (n - 2))

theorem exists_fix2_apply (hn : 6 ≤ n) {i j k l : Fin (n - 2)} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ g ∈ fix2 a b, (g : Perm (Fin n)) (emb hab i) = emb hab k ∧
      (g : Perm (Fin n)) (emb hab j) = emb hab l := by
  obtain ⟨τ, hτ, hτi, hτj⟩ := alt_two_transitive (m := n - 2) (by omega) hij hkl
  obtain ⟨g, hg⟩ := resHom_surjective hab ⟨τ, hτ⟩
  have hgτ : resPerm hab g = τ := congrArg Subtype.val hg
  refine ⟨g, g.2, ?_, ?_⟩
  · rw [← emb_resPerm, hgτ, hτi]
  · rw [← emb_resPerm, hgτ, hτj]

theorem sum_emb (x : Fin n → ZMod 2) : ∑ i, x (emb hab i) + x a + x b = ∑ j, x j := by
  have h1 : ∑ i, x (emb hab i) = ∑ c : Cpl a b, x c :=
    Equiv.sum_comp (cplEquiv hab) (fun c : Cpl a b => x c)
  have h2 : ∑ c : Cpl a b, x c = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ a ∧ j ≠ b), x j :=
    (Finset.sum_subtype _ (by simp) x).symm
  have h3 : (Finset.univ.filter fun j : Fin n => ¬(j ≠ a ∧ j ≠ b)) = {a, b} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  rw [h1, h2, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j ≠ a ∧ j ≠ b),
    h3, Finset.sum_pair hab, add_assoc]

@[expose] noncomputable def resVec (x : Fin n → ZMod 2) : Fin (n - 2) → ZMod 2 :=
  fun i => x (emb hab i) + (x a + x b) * (Pi.single i0 1 : Fin (n - 2) → ZMod 2) i

theorem resVec_mem (x : ↥(evenWeight n)) : resVec hab i0 x ∈ evenWeight (n - 2) := by
  have hx : ∑ j, (x : Fin n → ZMod 2) j = 0 := by
    have := x.2
    simpa [evenWeight] using this
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, resVec]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_pi_single']
  simp only [Finset.mem_univ, ite_true, mul_one]
  rw [← add_assoc, sum_emb, hx]

@[expose] noncomputable def resEven : ↥(evenWeight n) →+ ↥(evenWeight (n - 2)) where
  toFun x := ⟨resVec hab i0 x, resVec_mem hab i0 x⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp [resVec]
  map_add' x y := by
    apply Subtype.ext
    funext i
    show resVec hab i0 ((x + y : ↥(evenWeight n)) : Fin n → ZMod 2) i =
      resVec hab i0 x i + resVec hab i0 y i
    simp only [resVec, AddSubgroup.coe_add, Pi.add_apply]
    ring

theorem resEven_apply (x : ↥(evenWeight n)) (i : Fin (n - 2)) :
    ((resEven hab i0 x : ↥(evenWeight (n - 2))) : Fin (n - 2) → ZMod 2) i =
      resVec hab i0 x i := rfl

theorem resEven_mem_constWeight {x : ↥(evenWeight n)} (hx : x ∈ constWeight n) :
    resEven hab i0 x ∈ constWeight (n - 2) := by
  intro i j
  rw [resEven_apply, resEven_apply]
  have h0 : (x : Fin n → ZMod 2) a + (x : Fin n → ZMod 2) b = 0 := by
    rw [hx b a]
    exact CharTwo.add_self_eq_zero _
  simp only [resVec, h0, zero_mul, add_zero]
  exact hx _ _

@[expose] noncomputable def resHeart : AltHeart n →+ AltHeart (n - 2) :=
  QuotientAddGroup.map _ _ (resEven hab i0) fun _ hx => resEven_mem_constWeight hab i0 hx

theorem resHeart_mk (x : ↥(evenWeight n)) :
    resHeart hab i0 (QuotientAddGroup.mk x) = QuotientAddGroup.mk (resEven hab i0 x) := rfl

omit hab in
@[expose] def dSub (a b : Fin n) : AddSubgroup ↥(evenWeight n) where
  carrier := {x | (x : Fin n → ZMod 2) a = 0 ∧ (x : Fin n → ZMod 2) b = 0}
  add_mem' := by
    rintro x y ⟨hxa, hxb⟩ ⟨hya, hyb⟩
    exact ⟨by simp [hxa, hya], by simp [hxb, hyb]⟩
  zero_mem' := ⟨rfl, rfl⟩
  neg_mem' := by
    rintro x ⟨hxa, hxb⟩
    exact ⟨by simp [hxa], by simp [hxb]⟩

omit hab in
@[expose] def dHeart (a b : Fin n) : AddSubgroup (AltHeart n) :=
  (dSub a b).map (QuotientAddGroup.mk' (constWeight n))

omit hab in
instance dHeart_normal (a b : Fin n) : (dHeart a b).Normal :=
  ⟨fun y hy g => by rwa [heart_add_comm g y, add_neg_cancel_right]⟩

theorem resVec_of_mem_dSub {x : ↥(evenWeight n)} (hx : x ∈ dSub a b) (i : Fin (n - 2)) :
    resVec hab i0 x i = (x : Fin n → ZMod 2) (emb hab i) := by
  simp [resVec, hx.1, hx.2]

omit hab in
theorem permWeight_mem_dSub {g : alternatingGroup (Fin n)} (hg : g ∈ fix2 a b)
    {x : ↥(evenWeight n)} (hx : x ∈ dSub a b) : permWeight n (g : Perm (Fin n)) x ∈ dSub a b := by
  have ha : (g : Perm (Fin n))⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hg.1]
  have hb : (g : Perm (Fin n))⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hg.2]
  exact ⟨by rw [permWeight_apply, ha]; exact hx.1, by rw [permWeight_apply, hb]; exact hx.2⟩

theorem resHeart_hAct (g : ↥(fix2 a b)) {x : ↥(evenWeight n)} (hx : x ∈ dSub a b) :
    resHeart hab i0 (hAct n ((g : alternatingGroup (Fin n)) : Perm (Fin n))
      (QuotientAddGroup.mk x)) =
      hAct (n - 2) (resPerm hab g) (resHeart hab i0 (QuotientAddGroup.mk x)) := by
  rw [hAct_mk, resHeart_mk, resHeart_mk, hAct_mk]
  congr 1
  apply Subtype.ext
  funext i
  rw [resEven_apply, permWeight_apply, resEven_apply,
    resVec_of_mem_dSub hab i0 (permWeight_mem_dSub g.2 hx), resVec_of_mem_dSub hab i0 hx,
    permWeight_apply, emb_resPerm_inv]

omit hab in
theorem sub_hAct_mem_dHeart {g : alternatingGroup (Fin n)} (hg : g ∈ fix2 a b)
    (y : AltHeart n) : y - hAct n (g : Perm (Fin n)) y ∈ dHeart a b := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have ha : (g : Perm (Fin n))⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hg.1]
  have hb : (g : Perm (Fin n))⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hg.2]
  refine ⟨x - permWeight n (g : Perm (Fin n)) x, ⟨?_, ?_⟩, rfl⟩
  · show (x : Fin n → ZMod 2) a - (permWeight n (g : Perm (Fin n)) x : Fin n → ZMod 2) a = 0
    rw [permWeight_apply, ha, sub_self]
  · show (x : Fin n → ZMod 2) b - (permWeight n (g : Perm (Fin n)) x : Fin n → ZMod 2) b = 0
    rw [permWeight_apply, hb, sub_self]

theorem permWeight_eq_of_resHeart_eq_zero {x : ↥(evenWeight n)} (hx : x ∈ dSub a b)
    (h0 : resHeart hab i0 (QuotientAddGroup.mk x) = 0) {g : alternatingGroup (Fin n)}
    (hg : g ∈ fix2 a b) : permWeight n (g : Perm (Fin n)) x = x := by
  rw [resHeart_mk, QuotientAddGroup.eq_zero_iff] at h0
  have hc : ∀ i j : Fin (n - 2), (x : Fin n → ZMod 2) (emb hab i) =
      (x : Fin n → ZMod 2) (emb hab j) := by
    intro i j
    have := h0 i j
    rwa [resEven_apply, resEven_apply, resVec_of_mem_dSub hab i0 hx,
      resVec_of_mem_dSub hab i0 hx] at this
  have ha : (g : Perm (Fin n))⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hg.1]
  have hb : (g : Perm (Fin n))⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hg.2]
  apply Subtype.ext
  funext k
  rw [permWeight_apply]
  by_cases hka : k = a
  · rw [hka, ha]
  by_cases hkb : k = b
  · rw [hkb, hb]
  have hk' : (g : Perm (Fin n))⁻¹ k ≠ a ∧ (g : Perm (Fin n))⁻¹ k ≠ b :=
    (cpl_iff ha hb k).mpr ⟨hka, hkb⟩
  obtain ⟨i, hi⟩ := (cplEquiv hab).surjective ⟨k, hka, hkb⟩
  obtain ⟨j, hj⟩ := (cplEquiv hab).surjective ⟨_, hk'⟩
  have hi' : emb hab i = k := by rw [emb, hi]
  have hj' : emb hab j = (g : Perm (Fin n))⁻¹ k := by rw [emb, hj]
  rw [← hj', hc j i, hi']

theorem emb_pairVec (i j : Fin (n - 2)) :
    resEven hab i0 (pairVec (emb hab i) (emb hab j)) = pairVec i j := by
  have hd : pairVec (emb hab i) (emb hab j) ∈ dSub a b := by
    obtain ⟨hia, hib⟩ := emb_ne hab i
    obtain ⟨hja, hjb⟩ := emb_ne hab j
    refine ⟨?_, ?_⟩ <;> rw [pairVec_apply] <;>
      simp [Ne.symm hia, Ne.symm hib, Ne.symm hja, Ne.symm hjb]
  apply Subtype.ext
  funext k
  rw [resEven_apply, resVec_of_mem_dSub hab i0 hd, pairVec_apply, pairVec_apply]
  simp only [Pi.single_apply, (emb_injective hab).eq_iff]

end Res

end CFSG.Quasithin.C41Pf.AltN
