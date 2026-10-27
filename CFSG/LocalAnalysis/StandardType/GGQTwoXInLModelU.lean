module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAugDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def q3u_pi (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr (finRotate n)).trans (finSuccEquiv n).symm)

private lemma q3u_pi_zero (n : ℕ) : q3u_pi n 0 = 0 := by
  have h : (finSuccEquiv n) (0 : Fin (n + 1)) = none := finSuccEquiv_zero
  simp only [q3u_pi, Equiv.trans_apply, Equiv.optionCongr_apply, h, Option.map_none]
  rw [← h]
  exact Equiv.symm_apply_apply _ _

private lemma q3u_pi_succ (n : ℕ) (j : Fin n) :
    q3u_pi n j.succ = (finRotate n j).succ := by
  have h : (finSuccEquiv n) (j.succ) = some j := (finSuccEquiv_eq_some).mpr rfl
  simp only [q3u_pi, Equiv.trans_apply, Equiv.optionCongr_apply, h, Option.map_some]
  rw [Equiv.symm_apply_eq]
  exact ((finSuccEquiv_eq_some).mpr rfl).symm

private lemma q3u_pi_last (n : ℕ) (hn : 2 ≤ n) : q3u_pi n (Fin.last n) = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have hj : j.succ = (Fin.last n : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last, j]
    omega
  have hpi : q3u_pi n (Fin.last n) = (finRotate n j).succ := by
    rw [← hj, q3u_pi_succ n j]
  have hj0 : j ≠ 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_zero, j] at hv
    omega
  have hr : finRotate n j = 0 := by
    rw [finRotate_apply j]
    apply Fin.ext
    have h1 : ((1 : Fin n)).val = 1 := by
      rw [show ((1 : Fin n)).val = 1 % n from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hjv : j.val = n - 1 := rfl
    rw [Fin.val_add, h1, Fin.val_zero, hjv, Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  rw [hpi, hr]
  apply Fin.ext
  simp

private lemma q3u_pi_injective (n : ℕ) : Function.Injective (q3u_pi n) := (q3u_pi n).injective

private lemma q3u_one_val {m : ℕ} [NeZero m] (hm : 1 < m) : ((1 : Fin m)).val = 1 := by
  rw [show ((1 : Fin m)).val = 1 % m from rfl]
  exact Nat.mod_eq_of_lt hm

private lemma q3u_mem_iff (n : ℕ) (f : Fin (n + 1) → ZMod 3) :
    f ∈ GGQTwoXInLAug n ↔ ∑ i, f i = 0 := by
  simp [GGQTwoXInLAug]

private noncomputable def q3u_single {n : ℕ} (a : Fin (n + 1)) (c : ZMod 3) :
    Fin (n + 1) → ZMod 3 :=
  fun m => if m = a then c else 0

private lemma q3u_single_apply {n : ℕ} (a m : Fin (n + 1)) (c : ZMod 3) :
    q3u_single a c m = (if m = a then c else 0 : ZMod 3) := rfl

private lemma q3u_sum_single {n : ℕ} (a : Fin (n + 1)) (c : ZMod 3) :
    ∑ i, q3u_single a c i = c := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [q3u_single_apply, if_pos rfl]
  · intro b _ hb
    rw [q3u_single_apply, if_neg hb]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private noncomputable def q3u_coroot (n : ℕ) (k : Fin n) : ↥(GGQTwoXInLAug n) :=
  ⟨q3u_single (q3u_pi n k.castSucc) (1 : ZMod 3) -
      q3u_single (q3u_pi n k.succ) 1, by
    rw [q3u_mem_iff]
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, q3u_sum_single, q3u_sum_single, sub_self]⟩

private noncomputable def q3u_root (n : ℕ) (k : Fin n) :
    Module.Dual (ZMod 3) ↥(GGQTwoXInLAug n) where
  toFun w := (w : Fin (n + 1) → ZMod 3) (q3u_pi n k.castSucc) -
    (w : Fin (n + 1) → ZMod 3) (q3u_pi n k.succ)
  map_add' a b := by
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c a := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma q3u_root_apply (n : ℕ) (k : Fin n) (w : ↥(GGQTwoXInLAug n)) :
    q3u_root n k w = (w : Fin (n + 1) → ZMod 3) (q3u_pi n k.castSucc) -
      (w : Fin (n + 1) → ZMod 3) (q3u_pi n k.succ) := rfl

private lemma q3u_coroot_apply (n : ℕ) (k : Fin n) (m : Fin (n + 1)) :
    (q3u_coroot n k : Fin (n + 1) → ZMod 3) m =
      (if m = q3u_pi n k.castSucc then (1 : ZMod 3) else 0) -
        (if m = q3u_pi n k.succ then 1 else 0) := by
  simp only [q3u_coroot, Pi.sub_apply, q3u_single_apply]

private lemma q3u_cartan_A (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j =
      if i = j then (2 : ℤ) else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private lemma q3u_castSucc_eq_succ_iff {n : ℕ} (i j : Fin n) :
    (i.castSucc = j.succ) ↔ j.val + 1 = i.val := by
  constructor <;> intro h
  · have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  · apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

private lemma q3u_succ_eq_castSucc_iff {n : ℕ} (i j : Fin n) :
    (i.succ = j.castSucc) ↔ i.val + 1 = j.val := by
  constructor <;> intro h
  · have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  · apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

private lemma q3u_pairing (n : ℕ) (i j : Fin n) :
    q3u_root n i (q3u_coroot n j) = (CartanMatrix.A n i j : ZMod 3) := by
  rw [q3u_cartan_A, q3u_root_apply]
  simp only [q3u_coroot_apply, Pi.sub_apply]
  simp only [Function.Injective.eq_iff (q3u_pi_injective n)]
  simp only [Fin.castSucc_inj, Fin.succ_inj, q3u_castSucc_eq_succ_iff, q3u_succ_eq_castSucc_iff]
  split_ifs <;> (first | omega | (exfalso; omega) | norm_num)

private noncomputable def q3u_permFun (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : ↥(GGQTwoXInLAug n)) : ↥(GGQTwoXInLAug n) :=
  ⟨fun i => (v : Fin (n + 1) → ZMod 3) (σ.symm i), by
    rw [q3u_mem_iff]
    rw [Equiv.sum_comp]
    exact (q3u_mem_iff n (v : Fin (n + 1) → ZMod 3)).mp v.property⟩

private lemma q3u_permFun_apply (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)) :
    (q3u_permFun n σ v : Fin (n + 1) → ZMod 3) i =
      (v : Fin (n + 1) → ZMod 3) (σ.symm i) := rfl

private noncomputable def q3u_permLE (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    ↥(GGQTwoXInLAug n) ≃ₗ[ZMod 3] ↥(GGQTwoXInLAug n) where
  toFun := q3u_permFun n σ
  map_add' a b := by
    apply Subtype.ext; funext i
    simp only [q3u_permFun_apply, Submodule.coe_add, Pi.add_apply]
  map_smul' c a := by
    apply Subtype.ext; funext i
    simp only [q3u_permFun_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
  invFun := q3u_permFun n σ.symm
  left_inv v := by
    apply Subtype.ext; funext i
    simp only [q3u_permFun_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv v := by
    apply Subtype.ext; funext i
    simp only [q3u_permFun_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

private lemma q3u_permLE_apply (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)) :
    (q3u_permLE n σ v : Fin (n + 1) → ZMod 3) i =
      (v : Fin (n + 1) → ZMod 3) (σ.symm i) := rfl

private noncomputable def q3u_permHom (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* (↥(GGQTwoXInLAug n) ≃ₗ[ZMod 3] ↥(GGQTwoXInLAug n)) where
  toFun := q3u_permLE n
  map_one' := by
    apply LinearEquiv.ext; intro v; apply Subtype.ext; funext i
    rw [q3u_permLE_apply]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext; intro v; apply Subtype.ext; funext i
    simp only [q3u_permLE_apply, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.trans_apply,
      LinearEquiv.mul_apply]

private lemma q3u_permLE_swap_apply (n : ℕ) (a b : Fin (n + 1))
    (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)) :
    (q3u_permLE n (Equiv.swap a b) v : Fin (n + 1) → ZMod 3) i =
      (v : Fin (n + 1) → ZMod 3) (Equiv.swap a b i) := by
  rw [q3u_permLE_apply, Equiv.symm_swap]

private lemma q3u_coord (n : ℕ) (k : Fin n) (v : ↥(GGQTwoXInLAug n)) :
    q3u_permLE n (Equiv.swap (q3u_pi n k.castSucc) (q3u_pi n k.succ)) v =
      v - q3u_root n k v • q3u_coroot n k := by
  apply Subtype.ext; funext i
  rw [q3u_permLE_swap_apply, Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply,
    q3u_coroot_apply, q3u_root_apply, smul_eq_mul]
  rcases eq_or_ne i (q3u_pi n k.castSucc) with h | h
  · subst h
    rw [Equiv.swap_apply_left]
    have hne : q3u_pi n k.castSucc ≠ q3u_pi n k.succ :=
      fun hh => (Fin.castSucc_lt_succ (i := k)).ne (q3u_pi_injective n hh)
    rw [if_pos rfl, if_neg hne]
    ring
  · rcases eq_or_ne i (q3u_pi n k.succ) with h2 | h2
    · subst h2
      have hne : q3u_pi n k.succ ≠ q3u_pi n k.castSucc :=
        fun hh => (Fin.castSucc_lt_succ (i := k)).ne (q3u_pi_injective n hh.symm)
      rw [Equiv.swap_apply_right, if_neg hne, if_pos rfl]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne h h2, if_neg h, if_neg h2]
      ring

private noncomputable def q3u_permCongrHom {α β : Type*} (e : α ≃ β) :
    Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := e.permCongr_refl
  map_mul' := e.permCongr_mul

private lemma q3u_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  apply Equiv.Perm.ext
  intro x
  rw [Equiv.permCongr_apply]
  by_cases h : x = e a
  · subst h; rw [Equiv.symm_apply_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases h2 : x = e b
    · subst h2; rw [Equiv.symm_apply_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · have hsa : e.symm x ≠ a := fun hh => h (by rw [← hh, Equiv.apply_symm_apply])
      have hsb : e.symm x ≠ b := fun hh => h2 (by rw [← hh, Equiv.apply_symm_apply])
      rw [Equiv.swap_apply_of_ne_of_ne hsa hsb, Equiv.swap_apply_of_ne_of_ne h h2,
        Equiv.apply_symm_apply]

private lemma q3u_chain_closure {m : ℕ} {α : Type*} [DecidableEq α]
    (c : Fin (m + 1) → α) (hc : Function.Injective c) (z : α)
    (hz : ∀ x, x ∈ Set.range c ↔ x ≠ z) :
    Subgroup.closure (Set.range fun j : Fin m => Equiv.swap (c j.castSucc) (c j.succ)) =
      MulAction.stabilizer (Equiv.Perm α) z := by
  classical
  let p : α → Prop := fun x => x ≠ z
  haveI : DecidablePred p := fun x => inferInstance
  let e : Fin (m + 1) ≃ Subtype p :=
    Equiv.ofBijective (fun j => (⟨c j, (hz (c j)).mp (Set.mem_range_self j)⟩ : Subtype p)) (by
      constructor
      · intro a b hab
        exact hc (congrArg Subtype.val hab)
      · intro x
        obtain ⟨j, hj⟩ := (hz x.1).mpr x.2
        exact ⟨j, Subtype.ext hj⟩)
  let Φ : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm α :=
    (Equiv.Perm.ofSubtype (p := p)).comp (q3u_permCongrHom e)
  have hgen : Subgroup.closure (Set.range fun j : Fin m => Equiv.swap j.castSucc j.succ) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ m)
  have hmap : Subgroup.map Φ ⊤ =
      Subgroup.closure (Set.range fun j : Fin m => Equiv.swap (c j.castSucc) (c j.succ)) := by
    rw [← hgen, MonoidHom.map_closure]
    congr 1
    ext T; constructor
    · rintro ⟨g, ⟨j, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      change Equiv.swap (c j.castSucc) (c j.succ) =
        Equiv.Perm.ofSubtype (e.permCongr (Equiv.swap j.castSucc j.succ))
      rw [q3u_permCongr_swap, Equiv.Perm.ofSubtype_swap_eq]
      rfl
    · rintro ⟨j, rfl⟩
      refine ⟨Equiv.swap j.castSucc j.succ, ⟨j, rfl⟩, ?_⟩
      change Equiv.Perm.ofSubtype (e.permCongr (Equiv.swap j.castSucc j.succ)) =
        Equiv.swap (c j.castSucc) (c j.succ)
      rw [q3u_permCongr_swap, Equiv.Perm.ofSubtype_swap_eq]
      rfl
  have hrange : Subgroup.map Φ ⊤ = MulAction.stabilizer (Equiv.Perm α) z := by
    apply le_antisymm
    · rintro f ⟨g, -, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [p])
    · intro f hf
      rw [MulAction.mem_stabilizer_iff] at hf
      have hfix : ∀ a, ¬ p a → f a = a := by
        intro a ha
        have haz : a = z := by simpa [p] using ha
        rw [haz]
        simpa using hf
      have hfz : f z = z := by simpa using hf
      have hg : ∀ x, p (f x) ↔ p x := by
        intro x
        simp only [p]
        constructor
        · intro hfx hx
          exact hfx (by rw [hx]; exact hfz)
        · intro hx hfx
          exact hx (f.injective (by rw [hfx, hfz]))
      refine Subgroup.mem_map.mpr ⟨e.symm.permCongr (f.subtypePerm hg), trivial, ?_⟩
      change Equiv.Perm.ofSubtype (e.permCongr (e.symm.permCongr (f.subtypePerm hg))) = f
      have hcancel : e.permCongr (e.symm.permCongr (f.subtypePerm hg)) = f.subtypePerm hg := by
        ext x; simp [Equiv.permCongr_apply]
      rw [hcancel]
      ext a
      by_cases ha : p a
      · rw [Equiv.Perm.ofSubtype_apply_of_mem _ ha]; rfl
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ ha, hfix a ha]
  rw [← hmap, hrange]

private lemma q3u_mem_ggFixedSubmodule_closure {E V : Type*} [Group E] [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive E ≃+ V) (S : Set (MulAut E)) (w : V) :
    w ∈ ggFixedSubmodule (p := 3) ι (Subgroup.closure S) ↔
      ∀ φ ∈ S, ggLin (p := 3) ι φ w = w := by
  rw [mem_ggFixedSubmodule_iff]
  constructor
  · intro h φ hφ; exact h φ (Subgroup.subset_closure hφ)
  · intro h φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem y hy => exact h y hy
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, LinearEquiv.mul_apply, hb, ha]
    | inv a _ ha =>
        have h2 : (ggLin (p := 3) ι a).symm w = w := by
          have h3 := congrArg (fun x => (ggLin (p := 3) ι a).symm x) ha
          simpa using h3.symm
        rw [map_inv]
        exact h2

private lemma q3u_fixed_iff_span (n : ℕ) (hn3 : 3 ∣ n) (z : Fin (n + 1))
    (v0 : ↥(GGQTwoXInLAug n))
    (hv0 : (v0 : Fin (n + 1) → ZMod 3) = fun i => if i = z then 0 else -1)
    (w0 : Fin (n + 1)) (hw0 : w0 ≠ z) (w : ↥(GGQTwoXInLAug n)) :
    (∀ σ : Equiv.Perm (Fin (n + 1)), σ z = z → q3u_permLE n σ w = w) ↔
      w ∈ Submodule.span (ZMod 3) ({v0} : Set (↥(GGQTwoXInLAug n))) := by
  have hn3' : (n : ZMod 3) = 0 := by
    obtain ⟨k, hk⟩ := hn3
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  constructor
  · intro hw
    have hconst : ∀ j : Fin (n + 1), j ≠ z → (w : Fin (n + 1) → ZMod 3) j =
        (w : Fin (n + 1) → ZMod 3) w0 := by
      intro j hj
      have hswap : Equiv.swap j w0 z = z :=
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hw0)
      have h := hw (Equiv.swap j w0) hswap
      have h' := congrArg (fun x : ↥(GGQTwoXInLAug n) => (x : Fin (n + 1) → ZMod 3) j) h
      simp only [q3u_permLE_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h'
      exact h'.symm
    have hwz : (w : Fin (n + 1) → ZMod 3) z = 0 := by
      have hsum : ∑ i, (w : Fin (n + 1) → ZMod 3) i = 0 := (q3u_mem_iff n _).mp w.property
      have hsplit : ∑ i, (w : Fin (n + 1) → ZMod 3) i =
          (w : Fin (n + 1) → ZMod 3) z + (n : ZMod 3) * (w : Fin (n + 1) → ZMod 3) w0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
        congr 1
        rw [Finset.sum_congr rfl (fun i hi => hconst i (Finset.mem_erase.mp hi).1)]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ z),
          Finset.card_univ, Fintype.card_fin]
        simp
      rw [hsplit, hn3', zero_mul, add_zero] at hsum
      exact hsum
    have hw_eq : w = (-(w : Fin (n + 1) → ZMod 3) w0) • v0 := by
      apply Subtype.ext; funext i
      have hv0i : (v0 : Fin (n + 1) → ZMod 3) i = (if i = z then 0 else -1 : ZMod 3) := by
        simpa using congrFun hv0 i
      rw [Submodule.coe_smul, Pi.smul_apply, hv0i, smul_eq_mul]
      by_cases hi : i = z
      · subst hi
        rw [if_pos rfl, mul_zero, hwz]
      · have hc := hconst i hi
        rw [if_neg hi, hc]
        ring
    rw [hw_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v0)
  · intro hw σ hσ
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    apply Subtype.ext; funext i
    have hv0i : (v0 : Fin (n + 1) → ZMod 3) (σ.symm i) =
        (if σ.symm i = z then 0 else -1 : ZMod 3) := by
      simpa using congrFun hv0 (σ.symm i)
    have hv0i' : (v0 : Fin (n + 1) → ZMod 3) i = (if i = z then 0 else -1 : ZMod 3) := by
      simpa using congrFun hv0 i
    simp only [q3u_permLE_apply, Submodule.coe_smul, Pi.smul_apply, hv0i, hv0i']
    have hsz : σ.symm z = z := (Equiv.symm_apply_eq σ).mpr hσ.symm
    by_cases hi : i = z
    · subst hi
      rw [if_pos hsz, if_pos rfl]
    · have hsi : σ.symm i ≠ z := by
        intro hh; apply hi; rw [← hσ, ← hh, Equiv.apply_symm_apply]
      rw [if_neg hsi, if_neg hi]

private noncomputable def q3u_fixSub (n : ℕ) (w : ↥(GGQTwoXInLAug n)) :
    Subgroup (Equiv.Perm (Fin (n + 1))) where
  carrier := {τ | q3u_permLE n τ w = w}
  one_mem' := by
    show (q3u_permLE n 1) w = w
    change (q3u_permHom n 1) w = w
    rw [map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    show (q3u_permLE n (a * b)) w = w
    change (q3u_permHom n (a * b)) w = w
    rw [map_mul, LinearEquiv.mul_apply]
    change (q3u_permLE n a) ((q3u_permLE n b) w) = w
    rw [show (q3u_permLE n b) w = w from hb, show (q3u_permLE n a) w = w from ha]
  inv_mem' := by
    intro a ha
    show (q3u_permLE n a⁻¹) w = w
    change (q3u_permHom n a⁻¹) w = w
    have h2 : (q3u_permLE n a).symm w = w := by
      have h3 := congrArg (fun z => (q3u_permLE n a).symm z) ha
      simpa using h3.symm
    rw [map_inv]
    exact h2

theorem ggQTwoXInL_model_unitary {G : Type} [Group G] (n : ℕ) (hn3 : 3 ∣ n) (hn6 : 6 ≤ n)
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (ι : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n))
    (hL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧
        ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
          ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
            (v : Fin (n + 1) → ZMod 3) (σ i)})
    (hK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 1 = 1 ∧
        ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
          ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
            (v : Fin (n + 1) → ZMod 3) (σ i)})
    (hxv : ((ι (Additive.ofMul ⟨x, hx⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
      fun i => if i = 0 then 0 else -1)
    (hyv : ((ι (Additive.ofMul ⟨y, hy⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
      fun i => if i = 1 then 0 else -1) :
    Nonempty (GGQTwoModel 3 Bs x y D L J K) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let a : Fin n := 0
  let b : Fin n := ⟨n - 1, by omega⟩
  let s : Fin n → Equiv.Perm (Fin (n + 1)) :=
    fun k => Equiv.swap (q3u_pi n k.castSucc) (q3u_pi n k.succ)
  have hb0 : (0 : Fin n) ≠ b := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_zero, b] at hv
    omega
  have hab : a ≠ b := by
    intro hh; exact hb0 (by rw [← hh])
  have h : (n - 1) + 1 = n := Nat.sub_add_cancel hn1
  let cL : Fin ((n - 1) + 1) → Fin (n + 1) := fun j => q3u_pi n ⟨j.val + 1, by omega⟩
  let cK : Fin ((n - 1) + 1) → Fin (n + 1) := fun j => q3u_pi n ⟨j.val, by omega⟩
  have hcL : Function.Injective cL := by
    intro i j hij
    change q3u_pi n ⟨i.val + 1, by omega⟩ = q3u_pi n ⟨j.val + 1, by omega⟩ at hij
    have h' := q3u_pi_injective n hij
    have hv := congrArg Fin.val h'
    simp only at hv
    apply Fin.ext
    omega
  have hcK : Function.Injective cK := by
    intro i j hij
    change q3u_pi n ⟨i.val, by omega⟩ = q3u_pi n ⟨j.val, by omega⟩ at hij
    have h' := q3u_pi_injective n hij
    have hv := congrArg Fin.val h'
    simp only at hv
    apply Fin.ext
    omega
  have hzL : ∀ x : Fin (n + 1), x ∈ Set.range cL ↔ x ≠ 0 := by
    intro x; constructor
    · rintro ⟨j, rfl⟩ hx
      have h' : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) :=
        q3u_pi_injective n (hx.trans (q3u_pi_zero n).symm)
      have hv := congrArg Fin.val h'
      simp only [Fin.val_zero] at hv
      omega
    · intro hx
      let y : Fin (n + 1) := (q3u_pi n).symm x
      have hy : y ≠ 0 := by
        intro h0
        apply hx
        rw [← Equiv.apply_symm_apply (q3u_pi n) x]
        change q3u_pi n y = 0
        rw [h0, q3u_pi_zero]
      have hyv : 1 ≤ y.val := by
        have := y.isLt
        have hne : y.val ≠ 0 := fun hh => hy (Fin.ext (by simpa using hh))
        omega
      refine ⟨⟨y.val - 1, by omega⟩, ?_⟩
      show q3u_pi n (⟨y.val - 1 + 1, by omega⟩ : Fin (n + 1)) = x
      rw [show (⟨y.val - 1 + 1, by omega⟩ : Fin (n + 1)) = y from by
        apply Fin.ext; simp only; omega]
      exact Equiv.apply_symm_apply (q3u_pi n) x
  have hzK : ∀ x : Fin (n + 1), x ∈ Set.range cK ↔ x ≠ 1 := by
    intro x; constructor
    · rintro ⟨j, rfl⟩ hx
      have h' : (⟨j.val, by omega⟩ : Fin (n + 1)) = Fin.last n :=
        q3u_pi_injective n (hx.trans (q3u_pi_last n hn2).symm)
      have hv := congrArg Fin.val h'
      simp only [Fin.val_last] at hv
      have hjlt : j.val < n := by omega
      exact (Nat.ne_of_lt hjlt) hv
    · intro hx
      let y : Fin (n + 1) := (q3u_pi n).symm x
      have hy : y ≠ Fin.last n := by
        intro h0
        apply hx
        rw [← Equiv.apply_symm_apply (q3u_pi n) x]
        change q3u_pi n y = 1
        rw [h0, q3u_pi_last n hn2]
      have hyv : y.val < n := by
        have := y.isLt
        have hne : y.val ≠ n := by
          intro hh
          apply hy
          apply Fin.ext
          simpa only [Fin.val_last] using hh
        omega
      refine ⟨⟨y.val, by omega⟩, ?_⟩
      show q3u_pi n (⟨y.val, by omega⟩ : Fin (n + 1)) = x
      rw [show (⟨y.val, by omega⟩ : Fin (n + 1)) = y from Fin.ext rfl]
      exact Equiv.apply_symm_apply (q3u_pi n) x
  have hfixL : ∀ k : Fin n, k ≠ 0 → s k 0 = 0 := by
    intro k hk
    have h1 : q3u_pi n k.castSucc ≠ 0 := by
      intro hh
      have h' : k.castSucc = (0 : Fin (n + 1)) := q3u_pi_injective n (by rw [hh, q3u_pi_zero])
      exact hk (Fin.castSucc_injective n h')
    have h2 : q3u_pi n k.succ ≠ 0 := by
      intro hh
      have h' : k.succ = (0 : Fin (n + 1)) := q3u_pi_injective n (by rw [hh, q3u_pi_zero])
      exact Fin.succ_ne_zero k h'
    simp only [s]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2)
  have hfixK : ∀ k : Fin n, k ≠ b → s k 1 = 1 := by
    intro k hk
    have hpilast : q3u_pi n (Fin.last n) = 1 := q3u_pi_last n hn2
    have h1 : q3u_pi n k.castSucc ≠ 1 := by
      intro hh
      have h' : k.castSucc = Fin.last n := q3u_pi_injective n (by rw [hh, hpilast])
      have hv := congrArg Fin.val h'
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      exact (Nat.ne_of_lt k.isLt) hv
    have h2 : q3u_pi n k.succ ≠ 1 := by
      intro hh
      have h' : k.succ = Fin.last n := q3u_pi_injective n (by rw [hh, hpilast])
      have hv := congrArg Fin.val h'
      simp only [Fin.val_succ, Fin.val_last] at hv
      apply hk
      apply Fin.ext
      simp only [b]
      exact Nat.eq_sub_of_add_eq hv
    simp only [s]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2)
  have hstabL : Subgroup.closure (s '' {k : Fin n | k ≠ 0}) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (0 : Fin (n + 1)) := by
    have hset : s '' {k : Fin n | k ≠ 0} =
        Set.range (fun j : Fin (n - 1) => Equiv.swap (cL j.castSucc) (cL j.succ)) := by
      ext T; constructor
      · rintro ⟨k, hk, rfl⟩
        have hk0 : k.val ≠ 0 := fun hh => hk (Fin.ext (by simpa using hh))
        refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
        simp only [s, cL]
        congr 1 <;>
          (apply congrArg (q3u_pi n); apply Fin.ext;
            simp only [Fin.val_castSucc, Fin.val_succ]; omega)
      · rintro ⟨j, rfl⟩
        refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
        · intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_zero] at hv
          omega
        · simp only [s, cL]
          congr 1 <;>
            (apply congrArg (q3u_pi n); apply Fin.ext;
              simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    rw [hset]
    exact q3u_chain_closure cL hcL 0 hzL
  have hstabK : Subgroup.closure (s '' {k : Fin n | k ≠ b}) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (1 : Fin (n + 1)) := by
    have hset : s '' {k : Fin n | k ≠ b} =
        Set.range (fun j : Fin (n - 1) => Equiv.swap (cK j.castSucc) (cK j.succ)) := by
      ext T; constructor
      · rintro ⟨k, hk, rfl⟩
        have hkv : k.val < n - 1 := by
          have := k.isLt
          have hne : k.val ≠ n - 1 := fun hh => hk (Fin.ext (by simpa [b] using hh))
          omega
        refine ⟨⟨k.val, hkv⟩, ?_⟩
        simp only [s, cK]
        congr 1 <;>
          (apply congrArg (q3u_pi n); apply Fin.ext;
            simp only [Fin.val_castSucc, Fin.val_succ]; omega)
      · rintro ⟨j, rfl⟩
        refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
        · intro hh
          have hv := congrArg Fin.val hh
          simp only [b, Fin.val_last] at hv
          omega
        · simp only [s, cK]
          congr 1 <;>
            (apply congrArg (q3u_pi n); apply Fin.ext;
              simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    rw [hset]
    exact q3u_chain_closure cK hcK 1 hzK
  have hLset : {T : ↥(GGQTwoXInLAug n) ≃ₗ[ZMod 3] ↥(GGQTwoXInLAug n) |
      ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧
        ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
          ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
            (v : Fin (n + 1) → ZMod 3) (σ i)} =
      q3u_permHom n '' {σ : Equiv.Perm (Fin (n + 1)) | σ 0 = 0} := by
    ext T; constructor
    · rintro ⟨σ, hσ, hT⟩
      refine ⟨σ.symm, (Equiv.symm_apply_eq σ).mpr hσ.symm, ?_⟩
      ext v i
      change (q3u_permLE n σ.symm v : Fin (n + 1) → ZMod 3) i =
        (T v : Fin (n + 1) → ZMod 3) i
      rw [hT v i, q3u_permLE_apply, Equiv.symm_symm]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨τ.symm, (Equiv.symm_apply_eq τ).mpr hτ.symm, fun v i => ?_⟩
      change (q3u_permLE n τ v : Fin (n + 1) → ZMod 3) i =
        (v : Fin (n + 1) → ZMod 3) (τ.symm i)
      rw [q3u_permLE_apply]
  have hKset : {T : ↥(GGQTwoXInLAug n) ≃ₗ[ZMod 3] ↥(GGQTwoXInLAug n) |
      ∃ σ : Equiv.Perm (Fin (n + 1)), σ 1 = 1 ∧
        ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
          ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
            (v : Fin (n + 1) → ZMod 3) (σ i)} =
      q3u_permHom n '' {σ : Equiv.Perm (Fin (n + 1)) | σ 1 = 1} := by
    ext T; constructor
    · rintro ⟨σ, hσ, hT⟩
      refine ⟨σ.symm, (Equiv.symm_apply_eq σ).mpr hσ.symm, ?_⟩
      ext v i
      change (q3u_permLE n σ.symm v : Fin (n + 1) → ZMod 3) i =
        (T v : Fin (n + 1) → ZMod 3) i
      rw [hT v i, q3u_permLE_apply, Equiv.symm_symm]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨τ.symm, (Equiv.symm_apply_eq τ).mpr hτ.symm, fun v i => ?_⟩
      change (q3u_permLE n τ v : Fin (n + 1) → ZMod 3) i =
        (v : Fin (n + 1) → ZMod 3) (τ.symm i)
      rw [q3u_permLE_apply]
  have hXclsL : Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | σ 0 = 0} =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (0 : Fin (n + 1)) := by
    have hset : {σ : Equiv.Perm (Fin (n + 1)) | σ 0 = 0} =
        (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (0 : Fin (n + 1)) : Set _) := by
      ext σ; simp [MulAction.mem_stabilizer_iff]
    rw [hset, Subgroup.closure_eq]
  have hXclsK : Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | σ 1 = 1} =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (1 : Fin (n + 1)) := by
    have hset : {σ : Equiv.Perm (Fin (n + 1)) | σ 1 = 1} =
        (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (1 : Fin (n + 1)) : Set _) := by
      ext σ; simp [MulAction.mem_stabilizer_iff]
    rw [hset, Subgroup.closure_eq]
  have hmemL : ∀ k : Fin n, k ≠ 0 → q3u_permLE n (s k) ∈
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) := by
    intro k hk
    rw [hL, hLset]
    exact Subgroup.subset_closure ⟨s k, hfixL k hk, rfl⟩
  have hmemK : ∀ k : Fin n, k ≠ b → q3u_permLE n (s k) ∈
      (ggAutomizer K Bs).map (ggLin (p := 3) ι) := by
    intro k hk
    rw [hK, hKset]
    exact Subgroup.subset_closure ⟨s k, hfixK k hk, rfl⟩
  let simple : Fin n → MulAut ↥Bs := fun k =>
    if hk : k = 0 then
      Classical.choose (Subgroup.mem_map.mp (hmemK k (by rw [hk]; exact hb0)))
    else
      Classical.choose (Subgroup.mem_map.mp (hmemL k hk))
  have simple_spec : ∀ k : Fin n, ggLin (p := 3) ι (simple k) = q3u_permLE n (s k) := by
    intro k
    by_cases hk : k = 0
    · simp only [simple, dif_pos hk]
      exact (Classical.choose_spec (Subgroup.mem_map.mp (hmemK k (by rw [hk]; exact hb0)))).2
    · simp only [simple, dif_neg hk]
      exact (Classical.choose_spec (Subgroup.mem_map.mp (hmemL k hk))).2
  have himgL : ggLin (p := 3) ι '' (simple '' {k : Fin n | k ≠ 0}) =
      q3u_permHom n '' (s '' {k : Fin n | k ≠ 0}) := by
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [simple_spec k]
    rfl
  have autL : ggAutomizer L Bs = Subgroup.closure (simple '' {k : Fin n | k ≠ 0}) := by
    apply Subgroup.map_injective (ggLin_injective (p := 3) ι)
    have e1 : Subgroup.map (ggLin (p := 3) ι) (ggAutomizer L Bs) =
        Subgroup.map (q3u_permHom n)
          (Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | σ 0 = 0}) := by
      rw [hL, hLset, ← MonoidHom.map_closure]
    have e2 : Subgroup.map (ggLin (p := 3) ι)
        (Subgroup.closure (simple '' {k : Fin n | k ≠ 0})) =
        Subgroup.map (q3u_permHom n) (Subgroup.closure (s '' {k : Fin n | k ≠ 0})) := by
      rw [MonoidHom.map_closure, himgL, ← MonoidHom.map_closure]
    rw [e1, e2, hXclsL, hstabL]
  have himgK : ggLin (p := 3) ι '' (simple '' {k : Fin n | k ≠ b}) =
      q3u_permHom n '' (s '' {k : Fin n | k ≠ b}) := by
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [simple_spec k]
    rfl
  have autK : ggAutomizer K Bs = Subgroup.closure (simple '' {k : Fin n | k ≠ b}) := by
    apply Subgroup.map_injective (ggLin_injective (p := 3) ι)
    have e1 : Subgroup.map (ggLin (p := 3) ι) (ggAutomizer K Bs) =
        Subgroup.map (q3u_permHom n)
          (Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | σ 1 = 1}) := by
      rw [hK, hKset, ← MonoidHom.map_closure]
    have e2 : Subgroup.map (ggLin (p := 3) ι)
        (Subgroup.closure (simple '' {k : Fin n | k ≠ b})) =
        Subgroup.map (q3u_permHom n) (Subgroup.closure (s '' {k : Fin n | k ≠ b})) := by
      rw [MonoidHom.map_closure, himgK, ← MonoidHom.map_closure]
    rw [e1, e2, hXclsK, hstabK]
  have fixedx : ggFixedSubmodule (p := 3) ι (ggAutomizer L Bs) =
      Submodule.span (ZMod 3) {ι (Additive.ofMul ⟨x, hx⟩)} := by
    rw [autL]
    apply SetLike.ext
    intro w
    have hiff : w ∈ ggFixedSubmodule (p := 3) ι
        (Subgroup.closure (simple '' {k : Fin n | k ≠ 0})) ↔
        (∀ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 → q3u_permLE n σ w = w) := by
      rw [q3u_mem_ggFixedSubmodule_closure]
      constructor
      · intro hw σ hσ
        have hgen : s '' {k : Fin n | k ≠ 0} ⊆ q3u_fixSub n w := by
          rintro τ ⟨k, hk, rfl⟩
          have hh := hw (simple k) ⟨k, hk, rfl⟩
          rwa [simple_spec k] at hh
        have hσ' : σ ∈ Subgroup.closure (s '' {k : Fin n | k ≠ 0}) := by
          rw [hstabL]; exact hσ
        have hσ'' : σ ∈ Subgroup.closure (s '' {k : Fin n | k ≠ 0}) := by
          rw [hstabL]; exact hσ
        have hfix : q3u_permLE n σ w = w :=
          Subgroup.closure_induction (p := fun τ _ => q3u_permLE n τ w = w)
            (fun y hy => hgen hy)
            (q3u_fixSub n w).one_mem
            (fun x y _ _ hx hy => (q3u_fixSub n w).mul_mem hx hy)
            (fun x _ hx => (q3u_fixSub n w).inv_mem hx)
            hσ''
        exact hfix
      · intro hw φ hφ
        obtain ⟨k, hk, rfl⟩ := hφ
        rw [simple_spec k]
        exact hw (s k) (hfixL k hk)
    rw [hiff]
    exact q3u_fixed_iff_span n hn3 0 (ι (Additive.ofMul ⟨x, hx⟩)) hxv 1 (by
      intro hh
      have hv := congrArg Fin.val hh
      rw [q3u_one_val (by omega : 1 < n + 1), Fin.val_zero] at hv
      omega) w
  have fixedy : ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) =
      Submodule.span (ZMod 3) {ι (Additive.ofMul ⟨y, hy⟩)} := by
    rw [autK]
    apply SetLike.ext
    intro w
    have hiff : w ∈ ggFixedSubmodule (p := 3) ι
        (Subgroup.closure (simple '' {k : Fin n | k ≠ b})) ↔
        (∀ σ : Equiv.Perm (Fin (n + 1)), σ 1 = 1 → q3u_permLE n σ w = w) := by
      rw [q3u_mem_ggFixedSubmodule_closure]
      constructor
      · intro hw σ hσ
        have hgen : s '' {k : Fin n | k ≠ b} ⊆ q3u_fixSub n w := by
          rintro τ ⟨k, hk, rfl⟩
          have hh := hw (simple k) ⟨k, hk, rfl⟩
          rwa [simple_spec k] at hh
        have hσ' : σ ∈ Subgroup.closure (s '' {k : Fin n | k ≠ b}) := by
          rw [hstabK]; exact hσ
        have hσ'' : σ ∈ Subgroup.closure (s '' {k : Fin n | k ≠ b}) := by
          rw [hstabK]; exact hσ
        have hfix : q3u_permLE n σ w = w :=
          Subgroup.closure_induction (p := fun τ _ => q3u_permLE n τ w = w)
            (fun y hy => hgen hy)
            (q3u_fixSub n w).one_mem
            (fun x y _ _ hx hy => (q3u_fixSub n w).mul_mem hx hy)
            (fun x _ hx => (q3u_fixSub n w).inv_mem hx)
            hσ''
        exact hfix
      · intro hw φ hφ
        obtain ⟨k, hk, rfl⟩ := hφ
        rw [simple_spec k]
        exact hw (s k) (hfixK k hk)
    rw [hiff]
    exact q3u_fixed_iff_span n hn3 1 (ι (Additive.ofMul ⟨y, hy⟩)) hyv 0 (by
      intro hh
      have hv := congrArg Fin.val hh
      rw [Fin.val_zero, q3u_one_val (by omega : 1 < n + 1)] at hv
      omega) w
  refine ⟨GGQTwoModel.mk (p := 3) (Bs := Bs) (x := x) (y := y) (D := D) (L := L) (J := J)
    (K := K) (ι := Fin n) (coxeter := CoxeterMatrix.A n) (cartan := CartanMatrix.A n)
    (V := ↥(GGQTwoXInLAug n)) (model := ι) (hx := hx) (hy := hy) (simple := simple)
    (coroot := q3u_coroot n) (root := q3u_root n) (a := a) (b := b) (a_ne_b := hab)
    (a_leaf := ?_) (isWeyl := ?_) (isCartan := ggIntCartan_A n)
    (pairing := fun i j => q3u_pairing n i j)
    (simple_apply := fun i w => by rw [simple_spec i]; exact q3u_coord n i w)
    (automizer_L := autL) (automizer_K := autK)
    (fixed_x := fixedx) (fixed_y := fixedy)⟩
  · have h01 : (0 : Fin n) ≠ 1 := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [Fin.val_zero, q3u_one_val hn2] at hv
      omega
    have ha0 : a = (0 : Fin n) := rfl
    have h10 : (1 : Fin n) ≠ a := by rw [ha0]; exact h01.symm
    refine ⟨1, ⟨h10, ?_⟩, ?_⟩
    · rw [q3u_cartan_A]
      simp only [a]
      rw [if_neg h01, if_pos (Or.inl (by rw [Fin.val_zero, q3u_one_val hn2]))]
      norm_num
    · intro c hc
      obtain ⟨hc0, hcA⟩ := hc
      rw [q3u_cartan_A] at hcA
      simp only [a] at hc0 hcA
      by_cases hc1 : (0 : Fin n) = c
      · exact absurd hc1.symm hc0
      · rw [if_neg hc1] at hcA
        by_cases hc2 : (0 : Fin n).val + 1 = c.val ∨ c.val + 1 = (0 : Fin n).val
        · rw [if_pos hc2] at hcA
          have hcv : c.val = 1 := by
            rcases hc2 with hh | hh
            · simpa using hh.symm
            · exact absurd (by simpa using hh) (Nat.succ_ne_zero c.val)
          apply Fin.ext
          rw [q3u_one_val hn2]
          exact hcv
        · rw [if_neg hc2] at hcA
          exact absurd rfl hcA
  · refine Or.inl ⟨n, Equiv.refl _, hn1, Or.inl ?_⟩
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl

end CFSG.StandardType

end
