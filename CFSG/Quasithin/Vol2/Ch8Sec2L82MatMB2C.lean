module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2G
public import CFSG.Quasithin.Background.HCocBase

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H13.L828T

@[expose] def Field4Data (C : Type) [Ring C] : Prop :=
  (2 : C) = 0 ∧ (∃ A : C, A * A + A + 1 = 0) ∧ Nat.card C ≤ 4

@[expose] def Matrix2Data (C : Type) [Ring C] : Prop :=
  (2 : C) = 0 ∧ (∃ e : Fin 2 → Fin 2 → C,
    (∀ i j k l, e i j * e k l = if j = k then e i l else 0) ∧ e 0 0 + e 1 1 = 1) ∧
    Nat.card C ≤ 16

@[expose] def matUnits (e00 e01 e10 e11 : List ℕ) : Fin 2 → Fin 2 → List ℕ := fun i j =>
  if i = 0 then (if j = 0 then e00 else e01) else (if j = 0 then e10 else e11)

theorem exists_field4_of_data {C : Type} [Ring C] [Finite C] [Nontrivial C] (h : Field4Data C) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧ Nonempty (C ≃+* K) := by
  obtain ⟨h2, ⟨A, hA⟩, hcard⟩ := h
  exact ring_iso_field4 h2 A hA hcard

theorem exists_matrix2_of_data {C : Type} [Ring C] [Finite C] [Nontrivial C] (h : Matrix2Data C) :
    Nonempty (C ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  obtain ⟨h2, ⟨e, he, hsum⟩, hcard⟩ := h
  exact ring_iso_matrix2 h2 e he hsum hcard

namespace MB2C

structure QCoords (Q : Type*) [AddCommGroup Q] (d : ℕ) where
  vm : ℕ → Q
  vm_xor : ∀ a b, vm (a ^^^ b) = vm a + vm b
  vm_mod : ∀ a, vm (a % 2 ^ d) = vm a
  vm_inj : ∀ a b, a < 2 ^ d → b < 2 ^ d → vm a = vm b → a = b
  vm_surj : ∀ q, ∃ m < 2 ^ d, vm m = q

namespace QCoords

variable {Q : Type*} [AddCommGroup Q] {d : ℕ} (c : QCoords Q d)

theorem vm_zero : c.vm 0 = 0 := by
  have h := c.vm_xor 0 0
  rw [Nat.xor_self] at h
  exact left_eq_add.1 h

theorem vm_eq_iff {a b : ℕ} : c.vm a = c.vm b ↔ a % 2 ^ d = b % 2 ^ d := by
  constructor
  · intro h
    exact c.vm_inj _ _ (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.mod_lt _ (Nat.two_pow_pos d))
      (by rw [c.vm_mod, c.vm_mod]; exact h)
  · intro h
    rw [← c.vm_mod a, ← c.vm_mod b, h]

theorem vm_add_self (a : ℕ) : c.vm a + c.vm a = 0 := by
  rw [← c.vm_xor, Nat.xor_self, c.vm_zero]

include c in
theorem finite : Finite Q :=
  Finite.of_surjective (fun m : Fin (2 ^ d) => c.vm m) fun q => by
    obtain ⟨m, hm, hmq⟩ := c.vm_surj q
    exact ⟨⟨m, hm⟩, hmq⟩

noncomputable def dec (q : Q) : ℕ := Classical.choose (c.vm_surj q)

theorem dec_lt (q : Q) : c.dec q < 2 ^ d := (Classical.choose_spec (c.vm_surj q)).1

theorem vm_dec (q : Q) : c.vm (c.dec q) = q := (Classical.choose_spec (c.vm_surj q)).2

theorem dec_vm (m : ℕ) : c.dec (c.vm m) = m % 2 ^ d :=
  c.vm_inj _ _ (c.dec_lt _) (Nat.mod_lt _ (Nat.two_pow_pos d))
    (by rw [c.vm_dec, c.vm_mod])

theorem dec_add (q q' : Q) : c.dec (q + q') = c.dec q ^^^ c.dec q' :=
  c.vm_inj _ _ (c.dec_lt _) (Nat.xor_lt_two_pow (c.dec_lt q) (c.dec_lt q'))
    (by rw [c.vm_dec, c.vm_xor, c.vm_dec, c.vm_dec])

@[expose] def Rep (φ : AddMonoid.End Q) (f : ℕ → ℕ) : Prop := ∀ m, φ (c.vm m) = c.vm (f m)

variable {c}

theorem Rep.mul {φ ψ : AddMonoid.End Q} {f g : ℕ → ℕ} (hφ : c.Rep φ f) (hψ : c.Rep ψ g) :
    c.Rep (φ * ψ) (f ∘ g) := fun m => by
  show φ (ψ (c.vm m)) = c.vm (f (g m))
  rw [hψ, hφ]

theorem Rep.add {φ ψ : AddMonoid.End Q} {f g : ℕ → ℕ} (hφ : c.Rep φ f) (hψ : c.Rep ψ g) :
    c.Rep (φ + ψ) (fun m => f m ^^^ g m) := fun m => by
  show φ (c.vm m) + ψ (c.vm m) = c.vm (f m ^^^ g m)
  rw [hφ, hψ, c.vm_xor]

theorem Rep.one : c.Rep (1 : AddMonoid.End Q) id := fun m => by
  rw [AddMonoid.End.one_apply]
  rfl

theorem Rep.zero : c.Rep (0 : AddMonoid.End Q) (fun _ => 0) := fun m => by
  rw [AddMonoid.End.zero_apply]
  exact c.vm_zero.symm

theorem Rep.ext {φ ψ : AddMonoid.End Q} {f g : ℕ → ℕ} (hφ : c.Rep φ f) (hψ : c.Rep ψ g)
    (h : ∀ m < 2 ^ d, f m % 2 ^ d = g m % 2 ^ d) : φ = ψ := by
  refine AddMonoid.End.ext _ fun x => ?_
  obtain ⟨m, hm, rfl⟩ := c.vm_surj x
  rw [hφ, hψ, c.vm_eq_iff]
  exact h m hm

theorem Rep.eq_iff {φ ψ : AddMonoid.End Q} {f g : ℕ → ℕ} (hφ : c.Rep φ f) (hψ : c.Rep ψ g) :
    φ = ψ ↔ ∀ m, f m % 2 ^ d = g m % 2 ^ d := by
  constructor
  · rintro rfl m
    exact c.vm_eq_iff.1 ((hφ m).symm.trans (hψ m))
  · exact fun h => Rep.ext hφ hψ fun m _ => h m

variable (c)

theorem exists_end (f : ℕ → ℕ) (hf : XorLin f) (hmod : ∀ m, f (m % 2 ^ d) = f m) :
    ∃ φ : AddMonoid.End Q, c.Rep φ f := by
  refine ⟨AddMonoidHom.mk' (fun q => c.vm (f (c.dec q))) fun q q' => ?_, fun m => ?_⟩
  · simp only [c.dec_add]
    rw [hf (c.dec q) (c.dec q'), c.vm_xor]
  · show c.vm (f (c.dec (c.vm m))) = c.vm (f m)
    rw [c.dec_vm, hmod]

noncomputable def mat (φ : AddMonoid.End Q) (m : ℕ) : ℕ := c.dec (φ (c.vm m))

theorem rep_mat (φ : AddMonoid.End Q) : c.Rep φ (c.mat φ) := fun m => (c.vm_dec _).symm

theorem mat_lt (φ : AddMonoid.End Q) (m : ℕ) : c.mat φ m < 2 ^ d := c.dec_lt _

theorem xorLin_mat (φ : AddMonoid.End Q) : XorLin (c.mat φ) := fun a b => by
  show c.dec (φ (c.vm (a ^^^ b))) = c.dec (φ (c.vm a)) ^^^ c.dec (φ (c.vm b))
  rw [c.vm_xor, map_add, c.dec_add]

theorem mat_mod (φ : AddMonoid.End Q) (m : ℕ) : c.mat φ (m % 2 ^ d) = c.mat φ m := by
  unfold mat
  rw [c.vm_mod]

theorem mat_eq_of_rep {φ : AddMonoid.End Q} {f : ℕ → ℕ} (h : c.Rep φ f) (m : ℕ) :
    c.mat φ m = f m % 2 ^ d := by
  unfold mat
  rw [h m, c.dec_vm]

end QCoords

@[expose] def algAct (Ms : List (List ℕ)) : List (ℕ × List ℕ) → List ℕ → ℕ
  | [], _ => 0
  | (t, w) :: W, xs => wAct Ms w (xs.getD t 0) ^^^ algAct Ms W xs

theorem wAct_comm {Ms : List (List ℕ)} {f : ℕ → ℕ} (hf : XorLin f)
    (h : ∀ i < Ms.length, ∀ m, f (actM (Ms.getD i []) m) = actM (Ms.getD i []) (f m)) :
    ∀ (w : List ℕ) (m : ℕ), f (wAct Ms w m) = wAct Ms w (f m)
  | [], m => rfl
  | i :: w, m => by
    show f (actM (Ms.getD i []) (wAct Ms w m)) = actM (Ms.getD i []) (wAct Ms w (f m))
    by_cases hi : i < Ms.length
    · rw [h i hi, wAct_comm hf h w m]
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hf.map_zero

theorem algAct_map {Ms : List (List ℕ)} {f : ℕ → ℕ} (hf : XorLin f)
    (h : ∀ i < Ms.length, ∀ m, f (actM (Ms.getD i []) m) = actM (Ms.getD i []) (f m)) :
    ∀ (W : List (ℕ × List ℕ)) (xs : List ℕ), f (algAct Ms W xs) = algAct Ms W (xs.map f)
  | [], xs => hf.map_zero
  | (t, w) :: W, xs => by
    rw [algAct, algAct, hf, wAct_comm hf h w, algAct_map hf h W xs]
    have e : (xs.map f).getD t 0 = f (xs.getD t 0) := by
      have := List.getD_map (l := xs) (n := t) (d := 0) f
      rwa [hf.map_zero] at this
    rw [e]

@[expose] def phiCols (Ms : List (List ℕ)) (W : List (List (ℕ × List ℕ))) (d : ℕ)
    (xs : List ℕ) : List ℕ :=
  (List.range d).map fun j => algAct Ms (W.getD j []) xs

@[expose] def tuples (d : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | r + 1 => (tuples d r).flatMap fun xs => (List.range (2 ^ d)).map fun x => x :: xs

theorem mem_tuples_of (d : ℕ) : ∀ (r : ℕ) (xs : List ℕ), xs.length = r →
    (∀ x ∈ xs, x < 2 ^ d) → xs ∈ tuples d r
  | 0, xs, hl, _ => by
    rw [List.length_eq_zero_iff.1 hl]
    simp [tuples]
  | r + 1, [], hl, _ => by simp at hl
  | r + 1, x :: xs, hl, hlt => by
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨xs, mem_tuples_of d r xs (by simpa using hl)
      fun y hy => hlt y (List.mem_cons_of_mem x hy), x, hlt x List.mem_cons_self, rfl⟩

@[expose] def commCheck (Ms : List (List ℕ)) (W : List (List (ℕ × List ℕ))) (d : ℕ)
    (xs : List ℕ) : Bool :=
  decide (∀ i, i < Ms.length → ∀ j, j < d →
    actM (Ms.getD i []) (actM (phiCols Ms W d xs) (2 ^ j)) =
      actM (phiCols Ms W d xs) (actM (Ms.getD i []) (2 ^ j)))

theorem mem_commutant_closure_iff {W : Type*} [CommGroup W] {B U : Subgroup W}
    (S : Set (MulAut W)) (hB : ∀ g ∈ Subgroup.closure S, ∀ b ∈ B, g b ∈ B)
    (hU : ∀ g ∈ Subgroup.closure S, ∀ u ∈ U, g u ∈ U) {φ : AddMonoid.End (QMod B U)} :
    φ ∈ commutant B U (Subgroup.closure S : Set (MulAut W)) ↔
      ∀ g ∈ S, ∀ γ : AddMonoid.End (QMod B U), Induces γ ⇑g → γ * φ = φ * γ := by
  constructor
  · intro h g hg γ hγ
    exact mem_commutant_iff.1 h γ ⟨g, Subgroup.subset_closure hg, hγ⟩
  · intro h
    rw [mem_commutant_iff]
    rintro γ ⟨g, hg, hγ⟩
    have key : ∀ x ∈ Subgroup.closure S, ∀ γ : AddMonoid.End (QMod B U), Induces γ ⇑x →
        γ * φ = φ * γ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact fun γ hγ => h x hx γ hγ
      | one =>
        intro γ hγ
        have h1 : γ = 1 :=
          Induces.ext_of hγ (induces_one B U) (fun b _ => by simp)
        rw [h1, one_mul, mul_one]
      | mul x y hx hy ihx ihy =>
        intro γ hγ
        obtain ⟨γx, hγx⟩ := exists_induces (B := B) (U := U) ⇑x
          (fun a _ b _ => map_mul x a b) (hB x hx) (hU x hx)
        obtain ⟨γy, hγy⟩ := exists_induces (B := B) (U := U) ⇑y
          (fun a _ b _ => map_mul y a b) (hB y hy) (hU y hy)
        have h1 : γ = γx * γy :=
          Induces.ext_of hγ (Induces.mul hγy hγx) (fun b _ => by simp [MulAut.mul_apply])
        rw [h1, mul_assoc, ihy γy hγy, ← mul_assoc, ihx γx hγx, mul_assoc]
      | inv x hx ih =>
        intro γ hγ
        obtain ⟨γx, hγx⟩ := exists_induces (B := B) (U := U) ⇑x
          (fun a _ b _ => map_mul x a b) (hB x hx) (hU x hx)
        have h1 : γ * γx = 1 :=
          Induces.ext_of (Induces.mul hγx hγ) (induces_one B U) (fun b _ => by simp)
        have h2 : γx * γ = 1 :=
          Induces.ext_of (Induces.mul hγ hγx) (induces_one B U) (fun b _ => by simp)
        calc γ * φ = γ * φ * (γx * γ) := by rw [h2, mul_one]
          _ = γ * (φ * γx) * γ := by simp only [mul_assoc]
          _ = γ * (γx * φ) * γ := by rw [← ih γx hγx]
          _ = (γ * γx) * φ * γ := by simp only [mul_assoc]
          _ = φ * γ := by rw [h1, one_mul]
    exact key g hg γ hγ

section OfMasks

variable {V : Type*} [CommGroup V] {n d : ℕ}

theorem maskCoords_vm_inv (mc : MaskCoords V n) (x : ℕ) : (mc.vm x)⁻¹ = mc.vm x := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← mc.vm_xor, Nat.xor_self, mc.vm_zero]

structure MaskCoordsData (mc : MaskCoords V n) (B U : Subgroup V) (d : ℕ)
    (LB LU LC : List ℕ) : Prop where
  mem_B : ∀ v, v ∈ B ↔ ∃ m ∈ combos LB, mc.vm m = v
  mem_U : ∀ v, v ∈ U ↔ ∃ m ∈ combos LU, mc.vm m = v
  lt_B : ∀ a ∈ LB, a < 2 ^ n
  lt_U : ∀ a ∈ LU, a < 2 ^ n
  mem_C : ∀ a ∈ LC, a ∈ combos LB
  len_C : LC.length = d
  inj : ∀ m, m < 2 ^ d → actM LC m ∈ combos LU → m = 0
  surj : ∀ b ∈ LB, ∃ m, m < 2 ^ d ∧ (b ^^^ actM LC m) ∈ combos LU

theorem MaskCoordsData.std {LB LU LC : List ℕ} (lt_B : ∀ a ∈ LB, a < 2 ^ n)
    (lt_U : ∀ a ∈ LU, a < 2 ^ n) (mem_C : ∀ a ∈ LC, a ∈ combos LB) (len_C : LC.length = d)
    (inj : ∀ m, m < 2 ^ d → actM LC m ∈ combos LU → m = 0)
    (surj : ∀ b ∈ LB, ∃ m, m < 2 ^ d ∧ (b ^^^ actM LC m) ∈ combos LU) :
    MaskCoordsData (MaskCoords.std n) (maskSub n LB) (maskSub n LU) d LB LU LC :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, lt_B, lt_U, mem_C, len_C, inj, surj⟩

namespace MaskCoordsData

variable {mc : MaskCoords V n} {B U : Subgroup V} {LB LU LC : List ℕ}
  (h : MaskCoordsData mc B U d LB LU LC)

include h

theorem lt_C : ∀ a ∈ LC, a < 2 ^ n := fun a ha => combos_lt h.lt_B a (h.mem_C a ha)

theorem actM_lt_C (m : ℕ) : actM LC m < 2 ^ n := actM_lt h.lt_C m

theorem vm_mem_U_iff {x : ℕ} (hx : x < 2 ^ n) : mc.vm x ∈ U ↔ x ∈ combos LU := by
  rw [h.mem_U]
  constructor
  · rintro ⟨m, hm, e⟩
    rwa [← mc.vm_inj m x (combos_lt h.lt_U m hm) hx e]
  · exact fun hx' => ⟨x, hx', rfl⟩

@[expose] def lift (m : ℕ) : ↥B :=
  ⟨mc.vm (actM LC m), (h.mem_B _).2 ⟨_, actM_mem_combos h.mem_C m, rfl⟩⟩

theorem lift_xor (a b : ℕ) : h.lift (a ^^^ b) = h.lift a * h.lift b :=
  Subtype.ext (by
    show mc.vm (actM LC (a ^^^ b)) = mc.vm (actM LC a) * mc.vm (actM LC b)
    rw [actM_xor LC a b, mc.vm_xor])

theorem lift_mod (a : ℕ) : h.lift (a % 2 ^ d) = h.lift a := by
  have e : actM LC (a % 2 ^ d) = actM LC a := by
    have := actM_mod LC a
    rwa [h.len_C] at this
  exact Subtype.ext (congrArg mc.vm e)

noncomputable def coords : QCoords (QMod B U) d where
  vm m := QMod.mk _ _ (h.lift m)
  vm_xor a b := by rw [h.lift_xor, QMod.mk_add]
  vm_mod a := by rw [h.lift_mod]
  vm_inj a b ha hb hab := by
    rw [QMod.mk_eq_mk_iff] at hab
    have h1 : mc.vm (actM LC (a ^^^ b)) ∈ U := by
      have e : (↑(h.lift a) : V) * (↑(h.lift b))⁻¹ = mc.vm (actM LC (a ^^^ b)) := by
        show mc.vm (actM LC a) * (mc.vm (actM LC b))⁻¹ = _
        rw [maskCoords_vm_inv mc, ← mc.vm_xor, actM_xor LC a b]
      rwa [e] at hab
    have h2 : actM LC (a ^^^ b) ∈ combos LU :=
      (h.vm_mem_U_iff (h.actM_lt_C _)).1 h1
    exact eq_of_xor_eq_zero (h.inj _ (Nat.xor_lt_two_pow ha hb) h2)
  vm_surj q := by
    obtain ⟨b, rfl⟩ := QMod.mk_surjective _ _ q
    obtain ⟨x, hx, hxb⟩ := (h.mem_B _).1 b.2
    have hT : ∀ y ∈ combos LB, ∃ m, m < 2 ^ d ∧ (y ^^^ actM LC m) ∈ combos LU := by
      refine mem_of_combos (fun y => ∃ m, m < 2 ^ d ∧ (y ^^^ actM LC m) ∈ combos LU) ?_ ?_ LB
        h.surj
      · refine ⟨0, Nat.two_pow_pos d, ?_⟩
        show (0 ^^^ actM LC 0) ∈ combos LU
        rw [(actM_xor LC).map_zero, Nat.xor_self]
        exact zero_mem_combos LU
      · rintro a b ⟨m, hm, hmem⟩ ⟨m', hm', hmem'⟩
        refine ⟨m ^^^ m', Nat.xor_lt_two_pow hm hm', ?_⟩
        have e : a ^^^ b ^^^ actM LC (m ^^^ m') = (a ^^^ actM LC m) ^^^ (b ^^^ actM LC m') := by
          rw [actM_xor LC m m']
          ac_rfl
        rw [e]
        exact xor_mem_combos LU hmem hmem'
    obtain ⟨m, hm, hmem⟩ := hT x hx
    refine ⟨m, hm, ?_⟩
    show QMod.mk _ _ (h.lift m) = QMod.mk _ _ b
    rw [QMod.mk_eq_mk_iff, ← hxb, maskCoords_vm_inv mc]
    show mc.vm (actM LC m) * mc.vm x ∈ U
    rw [← mc.vm_xor, Nat.xor_comm]
    exact (h.mem_U _).2 ⟨_, hmem, rfl⟩

theorem rep_of_induces {g : MulAut V} {cols M : List ℕ}
    (hg : ∀ m, g (mc.vm m) = mc.vm (actM cols m)) (hM : M.length = d)
    (hcheck : ∀ j < d, (actM cols (actM LC (2 ^ j)) ^^^ actM LC (actM M (2 ^ j))) ∈ combos LU)
    {γ : AddMonoid.End (QMod B U)} (hγ : Induces γ ⇑g) :
    h.coords.Rep γ (actM M) := by
  intro m
  show γ (QMod.mk _ _ (h.lift m)) = QMod.mk _ _ (h.lift (actM M m))
  obtain ⟨b', hb', hγb⟩ := hγ (h.lift m)
  rw [hγb, QMod.mk_eq_mk_iff]
  have hF : XorLin (fun m => actM cols (actM LC m) ^^^ actM LC (actM M m)) := by
    intro a b
    show actM cols (actM LC (a ^^^ b)) ^^^ actM LC (actM M (a ^^^ b)) =
      (actM cols (actM LC a) ^^^ actM LC (actM M a)) ^^^
        (actM cols (actM LC b) ^^^ actM LC (actM M b))
    rw [actM_xor LC a b, actM_xor cols, actM_xor M a b, actM_xor LC]
    ac_rfl
  have key : (actM cols (actM LC m) ^^^ actM LC (actM M m)) ∈ combos LU := by
    have e1 : actM LC (m % 2 ^ d) = actM LC m := by
      have := actM_mod LC m
      rwa [h.len_C] at this
    have e2 : actM M (m % 2 ^ d) = actM M m := by
      have := actM_mod M m
      rwa [hM] at this
    have := mem_combos_of_xorLin hF hcheck (m % 2 ^ d) (Nat.mod_lt _ (Nat.two_pow_pos d))
    simpa only [e1, e2] using this
  rw [hb']
  show g (mc.vm (actM LC m)) * (mc.vm (actM LC (actM M m)))⁻¹ ∈ _
  rw [hg, maskCoords_vm_inv mc, ← mc.vm_xor]
  exact (h.mem_U _).2 ⟨_, key, rfl⟩

end MaskCoordsData

end OfMasks

section Model

variable {V : Type*} [CommGroup V]

@[expose] def genGroup (gens : List (MulAut V)) : Subgroup (MulAut V) :=
  Subgroup.closure {g | g ∈ gens}

theorem genGroup_two (a b : MulAut V) :
    genGroup [a, b] = Subgroup.closure ({a, b} : Set (MulAut V)) := by
  unfold genGroup
  congr 1
  ext g
  simp

theorem hgens_two {n : ℕ} {mc : MaskCoords V n} {a b : MulAut V} {ca cb : List ℕ}
    (ha : ∀ m, a (mc.vm m) = mc.vm (actM ca m)) (hb : ∀ m, b (mc.vm m) = mc.vm (actM cb m)) :
    ∀ i < [a, b].length, ∀ m,
      [a, b].getD i 1 (mc.vm m) = mc.vm (actM ([ca, cb].getD i []) m) := by
  intro i hi m
  have hi2 : i < 2 := hi
  interval_cases i
  · exact ha m
  · exact hb m

theorem getD_mem_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem gen_mem_genGroup (gens : List (MulAut V)) {i : ℕ} (hi : i < gens.length) :
    gens.getD i 1 ∈ genGroup gens :=
  Subgroup.subset_closure (getD_mem_of_lt 1 hi)

structure MB2Model (d : ℕ) (B U : Subgroup V) (gens : List (MulAut V)) where
  c : QCoords (QMod B U) d
  Ms : List (List ℕ)
  len : Ms.length = gens.length
  len_M : ∀ M ∈ Ms, M.length = d
  lt : ∀ M ∈ Ms, ∀ x ∈ M, x < 2 ^ d
  rep : ∀ i < gens.length, ∀ γ : AddMonoid.End (QMod B U), Induces γ ⇑(gens.getD i 1) →
    c.Rep γ (actM (Ms.getD i []))
  inv_B : ∀ g ∈ genGroup gens, ∀ b ∈ B, g b ∈ B
  inv_U : ∀ g ∈ genGroup gens, ∀ u ∈ U, g u ∈ U

@[expose] noncomputable def MB2Model.ofMasks {n d : ℕ} {mc : MaskCoords V n} {B U : Subgroup V}
    {LB LU LC : List ℕ} (hc : MaskCoordsData mc B U d LB LU LC) (gens : List (MulAut V))
    (cols Ms : List (List ℕ))
    (hgens : ∀ i < gens.length, ∀ m, gens.getD i 1 (mc.vm m) = mc.vm (actM (cols.getD i []) m))
    (hlen : Ms.length = gens.length) (hlen_M : ∀ M ∈ Ms, M.length = d)
    (hlt : ∀ M ∈ Ms, ∀ x ∈ M, x < 2 ^ d)
    (hcheck : ∀ i < gens.length, ∀ j < d,
      (actM (cols.getD i []) (actM LC (2 ^ j)) ^^^ actM LC (actM (Ms.getD i []) (2 ^ j))) ∈
        combos LU)
    (hB : ∀ g ∈ genGroup gens, ∀ b ∈ B, g b ∈ B)
    (hU : ∀ g ∈ genGroup gens, ∀ u ∈ U, g u ∈ U) : MB2Model d B U gens where
  c := hc.coords
  Ms := Ms
  len := hlen
  len_M := hlen_M
  lt := hlt
  rep i hi γ hγ := hc.rep_of_induces (hgens i hi)
    (hlen_M _ (getD_mem_of_lt [] (by rw [hlen]; exact hi))) (hcheck i hi) hγ
  inv_B := hB
  inv_U := hU

namespace MB2Model

variable {d : ℕ} {B U : Subgroup V} {gens : List (MulAut V)} (M : MB2Model d B U gens)

include M

theorem col_mem {i : ℕ} (hi : i < gens.length) : M.Ms.getD i [] ∈ M.Ms :=
  getD_mem_of_lt [] (by rw [M.len]; exact hi)

theorem col_lt {i : ℕ} (hi : i < gens.length) : ∀ x ∈ M.Ms.getD i [], x < 2 ^ d :=
  M.lt _ (M.col_mem hi)

theorem col_len {i : ℕ} (hi : i < gens.length) : (M.Ms.getD i []).length = d :=
  M.len_M _ (M.col_mem hi)

theorem exists_induces_gen {i : ℕ} (hi : i < gens.length) :
    ∃ γ : AddMonoid.End (QMod B U), Induces γ ⇑(gens.getD i 1) :=
  exists_induces ⇑(gens.getD i 1) (fun a _ b _ => map_mul _ a b)
    (M.inv_B _ (gen_mem_genGroup gens hi)) (M.inv_U _ (gen_mem_genGroup gens hi))

theorem mem_commutant_iff {φ : AddMonoid.End (QMod B U)} :
    φ ∈ commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)) ↔
      ∀ i < gens.length, ∀ m < 2 ^ d,
        actM (M.Ms.getD i []) (M.c.mat φ m) = M.c.mat φ (actM (M.Ms.getD i []) m) := by
  unfold genGroup
  rw [mem_commutant_closure_iff {g | g ∈ gens} M.inv_B M.inv_U]
  constructor
  · intro h i hi m hm
    obtain ⟨γ, hγ⟩ := M.exists_induces_gen hi
    have h1 := h _ (getD_mem_of_lt 1 hi) γ hγ
    have h2 := ((QCoords.Rep.eq_iff ((M.rep i hi γ hγ).mul (M.c.rep_mat φ))
      ((M.c.rep_mat φ).mul (M.rep i hi γ hγ))).1 h1) m
    have h3 : actM (M.Ms.getD i []) (M.c.mat φ m) < 2 ^ d := actM_lt (M.col_lt hi) _
    have h4 : M.c.mat φ (actM (M.Ms.getD i []) m) < 2 ^ d := M.c.mat_lt _ _
    exact (Nat.mod_eq_of_lt h3).symm.trans (h2.trans (Nat.mod_eq_of_lt h4))
  · intro h g hg γ hγ
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 hg
    have hg' : g = gens.getD i 1 := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hgi.symm
    subst hg'
    refine (QCoords.Rep.eq_iff ((M.rep i hi γ hγ).mul (M.c.rep_mat φ))
      ((M.c.rep_mat φ).mul (M.rep i hi γ hγ))).2 fun m => ?_
    have e1 : actM (M.Ms.getD i []) (m % 2 ^ d) = actM (M.Ms.getD i []) m := by
      have := actM_mod (M.Ms.getD i []) m
      rwa [M.col_len hi] at this
    have h5 := h i hi (m % 2 ^ d) (Nat.mod_lt _ (Nat.two_pow_pos d))
    rw [M.c.mat_mod, e1] at h5
    exact congrArg (· % 2 ^ d) h5

theorem mat_comm_all {φ : AddMonoid.End (QMod B U)}
    (hφ : φ ∈ commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)))
    {i : ℕ} (hi : i < gens.length) (m : ℕ) :
    M.c.mat φ (actM (M.Ms.getD i []) m) = actM (M.Ms.getD i []) (M.c.mat φ m) := by
  have e1 : actM (M.Ms.getD i []) (m % 2 ^ d) = actM (M.Ms.getD i []) m := by
    have := actM_mod (M.Ms.getD i []) m
    rwa [M.col_len hi] at this
  have h5 := M.mem_commutant_iff.1 hφ i hi (m % 2 ^ d) (Nat.mod_lt _ (Nat.two_pow_pos d))
  rw [M.c.mat_mod, e1] at h5
  exact h5.symm

theorem exists_mem_commutant {MA : List ℕ} (hMA : MA.length = d) (hlt : ∀ x ∈ MA, x < 2 ^ d)
    (hcomm : ∀ i < gens.length, ∀ m < 2 ^ d,
      actM (M.Ms.getD i []) (actM MA m) = actM MA (actM (M.Ms.getD i []) m)) :
    ∃ φ ∈ commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)),
      M.c.Rep φ (actM MA) := by
  obtain ⟨φ, hφ⟩ := M.c.exists_end (actM MA) (actM_xor MA) (fun m => by
    have := actM_mod MA m
    rwa [hMA] at this)
  refine ⟨φ, M.mem_commutant_iff.2 fun i hi m hm => ?_, hφ⟩
  have e1 : ∀ x, M.c.mat φ x = actM MA x := fun x => by
    rw [M.c.mat_eq_of_rep hφ, Nat.mod_eq_of_lt (actM_lt hlt x)]
  rw [e1, e1]
  exact hcomm i hi m hm

theorem mat_eq_phiCols {φ : AddMonoid.End (QMod B U)}
    (hφ : φ ∈ commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)))
    (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j) :
    ∀ m < 2 ^ d, M.c.mat φ m = actM (phiCols M.Ms W d (bs.map (M.c.mat φ))) m := by
  intro m hm
  have hf := M.c.xorLin_mat φ
  have h1 : matOf d (M.c.mat φ) = phiCols M.Ms W d (bs.map (M.c.mat φ)) := by
    unfold matOf phiCols
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < d := List.mem_range.1 hj
    rw [← hW j hj', algAct_map hf
      (fun i hi m' => M.mat_comm_all hφ (by rw [← M.len]; exact hi) m') _ bs]
  rw [← h1, actM_matOf hf d m hm]

theorem commCheck_of_mem {φ : AddMonoid.End (QMod B U)}
    (hφ : φ ∈ commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)))
    (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j) :
    commCheck M.Ms W d (bs.map (M.c.mat φ)) = true := by
  unfold commCheck
  rw [decide_eq_true_eq]
  intro i hi j hj
  have hi' : i < gens.length := by rw [← M.len]; exact hi
  have hP := M.mat_eq_phiCols hφ bs W hW
  have h2j : 2 ^ j < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) hj
  have h3 : actM (M.Ms.getD i []) (2 ^ j) < 2 ^ d := actM_lt (M.col_lt hi') _
  calc actM (M.Ms.getD i []) (actM (phiCols M.Ms W d (bs.map (M.c.mat φ))) (2 ^ j))
      = actM (M.Ms.getD i []) (M.c.mat φ (2 ^ j)) := by rw [← hP _ h2j]
    _ = M.c.mat φ (actM (M.Ms.getD i []) (2 ^ j)) := (M.mat_comm_all hφ hi' _).symm
    _ = actM (phiCols M.Ms W d (bs.map (M.c.mat φ))) (actM (M.Ms.getD i []) (2 ^ j)) := hP _ h3

theorem card_le (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j) {N : ℕ}
    (hN : ((tuples d bs.length).filter (commCheck M.Ms W d)).length ≤ N) :
    Nat.card ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) ≤ N := by
  set L := (tuples d bs.length).filter (commCheck M.Ms W d) with hL
  have hmem : ∀ φ : ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))),
      bs.map (M.c.mat φ.1) ∈ L := by
    intro φ
    rw [hL, List.mem_filter]
    refine ⟨mem_tuples_of d _ _ (by simp) ?_, M.commCheck_of_mem φ.2 bs W hW⟩
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact M.c.mat_lt _ _
  let f : ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) →
      Fin L.length := fun φ =>
    ⟨L.idxOf (bs.map (M.c.mat φ.1)), List.idxOf_lt_length_of_mem (hmem φ)⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    have h1 : bs.map (M.c.mat φ.1) = bs.map (M.c.mat ψ.1) :=
      (List.idxOf_inj (hmem φ)).1 (Fin.mk.inj h)
    refine Subtype.ext ?_
    refine QCoords.Rep.ext (M.c.rep_mat φ.1) (M.c.rep_mat ψ.1) fun m hm => ?_
    rw [M.mat_eq_phiCols φ.2 bs W hW m hm, M.mat_eq_phiCols ψ.2 bs W hW m hm, h1]
  calc Nat.card ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)))
      ≤ Nat.card (Fin L.length) := Nat.card_le_card_of_injective f hf
    _ = L.length := Nat.card_fin _
    _ ≤ N := hN

end MB2Model

end Model

section Data

variable {V : Type} [CommGroup V] {d : ℕ} {B U : Subgroup V} {gens : List (MulAut V)}
  (M : MB2Model d B U gens)

include M

theorem MB2Model.two_eq_zero :
    (2 : ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)))) = 0 := by
  apply Subtype.ext
  refine QCoords.Rep.ext (c := M.c) (f := fun m => m ^^^ m) (g := fun _ => 0) ?_ QCoords.Rep.zero
    (fun m _ => by simp)
  intro m
  show (2 : AddMonoid.End (QMod B U)) (M.c.vm m) = M.c.vm (m ^^^ m)
  rw [AddMonoid.End.ofNat_apply, two_nsmul, M.c.vm_add_self, Nat.xor_self, M.c.vm_zero]

theorem MB2Model.finite_commutant :
    Finite ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) := by
  haveI := M.c.finite
  haveI : Finite (AddMonoid.End (QMod B U)) :=
    Finite.of_injective (fun φ : AddMonoid.End (QMod B U) => (⇑φ : QMod B U → QMod B U))
      DFunLike.coe_injective
  infer_instance

theorem MB2Model.nontrivial_commutant (hd : 0 < d) :
    Nontrivial ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) := by
  have hne : M.c.vm 1 ≠ 0 := by
    rw [← M.c.vm_zero, Ne, M.c.vm_eq_iff, Nat.zero_mod, Nat.mod_eq_of_lt]
    · exact one_ne_zero
    · exact Nat.one_lt_two_pow hd.ne'
  haveI : Nontrivial (AddMonoid.End (QMod B U)) :=
    ⟨⟨1, 0, fun h1 => hne (by
      simpa using congrArg (fun φ : AddMonoid.End (QMod B U) => φ (M.c.vm 1)) h1)⟩⟩
  infer_instance

theorem MB2Model.field4Data {MA : List ℕ} (hMA : MA.length = d) (hlt : ∀ x ∈ MA, x < 2 ^ d)
    (hcomm : ∀ i < gens.length, ∀ m < 2 ^ d,
      actM (M.Ms.getD i []) (actM MA m) = actM MA (actM (M.Ms.getD i []) m))
    (hroot : ∀ m < 2 ^ d, actM MA (actM MA m) ^^^ actM MA m ^^^ m = 0)
    (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j)
    (hN : ((tuples d bs.length).filter (commCheck M.Ms W d)).length ≤ 4) :
    Field4Data ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) := by
  refine ⟨M.two_eq_zero, ?_, M.card_le bs W hW hN⟩
  obtain ⟨φ, hφ, hrep⟩ := M.exists_mem_commutant hMA hlt hcomm
  refine ⟨⟨φ, hφ⟩, Subtype.ext ?_⟩
  show φ * φ + φ + 1 = 0
  have h1 := ((hrep.mul hrep).add hrep).add (QCoords.Rep.one (c := M.c))
  refine QCoords.Rep.ext h1 QCoords.Rep.zero fun m hm => ?_
  show (actM MA (actM MA m) ^^^ actM MA m ^^^ m) % 2 ^ d = 0 % 2 ^ d
  rw [hroot m hm]

theorem MB2Model.matrix2Data (E : Fin 2 → Fin 2 → List ℕ) (hlen : ∀ i j, (E i j).length = d)
    (hlt : ∀ i j, ∀ x ∈ E i j, x < 2 ^ d)
    (hcomm : ∀ i j, ∀ k < gens.length, ∀ m < 2 ^ d,
      actM (M.Ms.getD k []) (actM (E i j) m) = actM (E i j) (actM (M.Ms.getD k []) m))
    (hmul : ∀ i j k l, ∀ m < 2 ^ d,
      actM (E i j) (actM (E k l) m) = if j = k then actM (E i l) m else 0)
    (hsum : ∀ m < 2 ^ d, actM (E 0 0) m ^^^ actM (E 1 1) m = m)
    (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j)
    (hN : ((tuples d bs.length).filter (commCheck M.Ms W d)).length ≤ 16) :
    Matrix2Data ↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) := by
  refine ⟨M.two_eq_zero, ?_, M.card_le bs W hW hN⟩
  have hex : ∀ ij : Fin 2 × Fin 2, ∃ φ ∈ commutant B U
      ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V)), M.c.Rep φ (actM (E ij.1 ij.2)) :=
    fun ij => M.exists_mem_commutant (hlen _ _) (hlt _ _) (hcomm _ _)
  choose φ hφ hrep using hex
  refine ⟨fun i j => ⟨φ (i, j), hφ (i, j)⟩, ?_, ?_⟩
  · intro i j k l
    by_cases h : j = k
    · rw [if_pos h]
      refine Subtype.ext ?_
      show φ (i, j) * φ (k, l) = φ (i, l)
      refine QCoords.Rep.ext ((hrep (i, j)).mul (hrep (k, l))) (hrep (i, l)) fun m hm => ?_
      show actM (E i j) (actM (E k l) m) % 2 ^ d = actM (E i l) m % 2 ^ d
      rw [hmul i j k l m hm, if_pos h]
    · rw [if_neg h]
      refine Subtype.ext ?_
      show φ (i, j) * φ (k, l) = 0
      refine QCoords.Rep.ext ((hrep (i, j)).mul (hrep (k, l))) QCoords.Rep.zero fun m hm => ?_
      show actM (E i j) (actM (E k l) m) % 2 ^ d = 0 % 2 ^ d
      rw [hmul i j k l m hm, if_neg h]
  · refine Subtype.ext ?_
    show φ (0, 0) + φ (1, 1) = 1
    refine QCoords.Rep.ext ((hrep (0, 0)).add (hrep (1, 1))) QCoords.Rep.one fun m hm => ?_
    show (actM (E 0 0) m ^^^ actM (E 1 1) m) % 2 ^ d = m % 2 ^ d
    rw [hsum m hm]

theorem MB2Model.exists_field2 (hd : 0 < d) (bs : List ℕ) (W : List (List (ℕ × List ℕ)))
    (hW : ∀ j < d, algAct M.Ms (W.getD j []) bs = 2 ^ j)
    (hN : ((tuples d bs.length).filter (commCheck M.Ms W d)).length ≤ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (↥(commutant B U ((genGroup gens : Subgroup (MulAut V)) : Set (MulAut V))) ≃+*
        K) := by
  haveI := M.nontrivial_commutant hd
  haveI := M.finite_commutant
  exact ring_iso_zmod2 (M.card_le bs W hW hN)

end Data

end MB2C

end CFSG.Quasithin.H13.Mat
