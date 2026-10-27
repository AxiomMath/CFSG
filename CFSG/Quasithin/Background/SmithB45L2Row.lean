module

public import CFSG.Quasithin.Background.SmithB45L2Herm
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

section Card

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem card_frob_fixed {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s)) :
    Nat.card {x : F // x ^ (2 ^ s) = x} = 2 ^ s := by
  classical
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_le_of_frob_fixed hs _ (fun u hu => (Finset.mem_filter.mp hu).2)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
    have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
    have hfrF : Module.finrank (ZMod 2) F = 2 * s := by
      have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
      rw [Nat.card_eq_fintype_card, hF, Nat.card_zmod] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
      (K := GaloisField 2 s) (L := F)
      (by rw [GaloisField.finrank 2 (by omega), hfrF]; exact Dvd.intro_left 2 rfl)
    have hGF : Nat.card (GaloisField 2 s) = 2 ^ s := GaloisField.card 2 s (by omega)
    have : Fintype (GaloisField 2 s) := Fintype.ofFinite _
    have hfix : ∀ y : GaloisField 2 s, (ι y) ^ (2 ^ s) = ι y := by
      intro y
      rw [← map_pow, ← hGF, ← Fintype.card_eq_nat_card, FiniteField.pow_card]
    calc 2 ^ s = Nat.card (GaloisField 2 s) := hGF.symm
      _ ≤ _ := Nat.card_le_card_of_injective (fun y => ⟨ι y, hfix y⟩)
        (fun y y' h => ι.injective (congrArg Subtype.val h))

omit [CharP F 2] in
theorem frob_frob {s : ℕ} (hF : Fintype.card F = 2 ^ (2 * s)) (x : F) :
    (x ^ (2 ^ s)) ^ (2 ^ s) = x := by
  rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]

theorem card_hermA {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s)) :
    Nat.card ↥(hermA s F) = 2 ^ (4 * s) := by
  apply le_antisymm
  · let f : ↥(hermA s F) → {x : F // x ^ (2 ^ s) = x} × F × {x : F // x ^ (2 ^ s) = x} :=
      fun X => (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, by
          have := hermA_00 (a := s) X
          rwa [sig_apply] at this⟩,
        (X : Matrix (Fin 2) (Fin 2) F) 1 0, ⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, by
          have := hermA_11 (a := s) X
          rwa [sig_apply] at this⟩)
    have hf : Function.Injective f := by
      intro X Y h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h00, h10, h11⟩ := h
      refine hermA_ext h00 ?_ h11
      have e1 := hermA_10 (a := s) X
      have e2 := hermA_10 (a := s) Y
      rw [sig_apply] at e1 e2
      exact frob_pow_injective s (e1.symm.trans (h10.trans e2))
    have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_prod, card_frob_fixed hs hF,
      show Nat.card F = 2 ^ (2 * s) by rw [Nat.card_eq_fintype_card, hF]] at h
    calc _ ≤ _ := h
      _ = 2 ^ (4 * s) := by ring
  · have h := card_le_card_hermA (F := F) s (frob_frob hF)
    rw [card_frob_fixed hs hF, show Nat.card F = 2 ^ (2 * s) by
      rw [Nat.card_eq_fintype_card, hF]] at h
    calc 2 ^ (4 * s) = (2 ^ s) ^ 2 * 2 ^ (2 * s) := by ring
      _ ≤ _ := h

end Card

section Root

variable {F : Type} [Field F]

@[expose] def rootSub (T : AddSubgroup F) : Subgroup (SL2 F) where
  carrier := {g | ∃ t ∈ T, g = uMat t}
  mul_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t + t', T.add_mem ht ht', uMat_mul t t'⟩
  one_mem' := ⟨0, T.zero_mem, uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨-t, T.neg_mem ht, ?_⟩
    rw [inv_eq_iff_mul_eq_one, uMat_mul, add_neg_cancel, uMat_zero]

theorem mem_rootSub {T : AddSubgroup F} {g : SL2 F} : g ∈ rootSub T ↔ ∃ t ∈ T, g = uMat t :=
  Iff.rfl

theorem uMat_injective : Function.Injective (uMat : F → SL2 F) := by
  intro t t' h
  have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uMat_coe] using this

theorem card_rootSub (T : AddSubgroup F) : Nat.card (rootSub T) = Nat.card T := by
  refine (Nat.card_congr (Equiv.ofBijective (fun t : T => (⟨uMat t, t, t.2, rfl⟩ : rootSub T))
    ⟨fun t t' h => Subtype.ext (uMat_injective (congrArg Subtype.val h)), ?_⟩)).symm
  rintro ⟨_, t, ht, rfl⟩
  exact ⟨⟨t, ht⟩, rfl⟩

@[expose] def frobFixSub [CharP F 2] (s : ℕ) : AddSubgroup F where
  carrier := {x | x ^ (2 ^ s) = x}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [add_pow_char_pow, hx, hy]
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [neg_pow, hx]
    rcases Nat.even_or_odd (2 ^ s) with h | h
    · rw [h.neg_one_pow, one_mul, CharTwo.neg_eq]
    · rw [h.neg_one_pow]
      ring

end Root

section Transport

variable {V : Type} [CommGroup V] {F : Type} [Field F] {L : Subgroup (MulAut V)}

@[expose] def imL (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F)) : Subgroup (MulAut V) :=
  (R.map θ.symm.toMonoidHom).map L.subtype

theorem mem_imL (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F)) {a : MulAut V} :
    a ∈ imL θ R ↔ ∃ g ∈ R, a = ((θ.symm g : ↥L) : MulAut V) := by
  constructor
  · rintro ⟨l, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨θ.symm g, ⟨g, hg, rfl⟩, rfl⟩

theorem imL_le (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F)) : imL θ R ≤ L := by
  rintro _ ⟨l, -, rfl⟩
  exact l.2

theorem card_imL (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F)) : Nat.card (imL θ R) = Nat.card R := by
  rw [imL, Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective θ.symm.injective]

theorem isElemAbelian2_imL (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F))
    (hc : ∀ g ∈ R, ∀ h ∈ R, g * h = h * g) (h2 : ∀ g ∈ R, g ^ 2 = 1) :
    IsElemAbelian2 (imL θ R) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := (mem_imL θ R).mp ha
    obtain ⟨h, hh, rfl⟩ := (mem_imL θ R).mp hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc g hg h hh]
  · obtain ⟨g, hg, rfl⟩ := (mem_imL θ R).mp ha
    rw [← Subgroup.coe_pow, ← map_pow, h2 g hg, map_one, Subgroup.coe_one]

theorem rootSub_comm (T : AddSubgroup F) : ∀ g ∈ rootSub T, ∀ h ∈ rootSub T, g * h = h * g := by
  rintro _ ⟨t, -, rfl⟩ _ ⟨t', -, rfl⟩
  rw [uMat_mul, uMat_mul, add_comm]

theorem rootSub_sq [CharP F 2] (T : AddSubgroup F) : ∀ g ∈ rootSub T, g ^ 2 = 1 := by
  rintro _ ⟨t, -, rfl⟩
  rw [sq, uMat_mul, CharTwo.add_self_eq_zero, uMat_zero]

end Transport

theorem rAV_le_three_halves {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (h : IsA2 X A)
    (hc : Nat.card V ^ 2 ≤ Nat.card A ^ 3 * Nat.card (fixV A) ^ 2) :
    rAV A ≤ ((3 / 2 : ℚ)) := by
  rw [B1.card_eq_index_mul A, B1.index_eq_two_pow hV, B1.card_elemAbelian h.2.2] at hc
  have hpos : 0 < Nat.card (fixV A) ^ 2 := pow_pos (B1.card_fixV_pos A) 2
  have hc' : 2 ^ (2 * rkIdx (fixV A)) ≤ 2 ^ (3 * rk A) := by
    rw [mul_pow, ← pow_mul, ← pow_mul] at hc
    rw [mul_comm 2, mul_comm 3]
    exact Nat.le_of_mul_le_mul_right hc hpos
  have h2 : 2 * rkIdx (fixV A) ≤ 3 * rk A := (Nat.pow_le_pow_iff_right (by norm_num)).mp hc'
  have hr : (0 : ℚ) < rk A := by exact_mod_cast h.rk_pos
  have h3 : (2 : ℚ) * rkIdx (fixV A) ≤ 3 * rk A := by exact_mod_cast h2
  unfold rAV
  rw [div_le_iff₀ hr]
  linarith

section Orth

variable {V : Type} [CommGroup V] [Finite V] {F : Type} [Field F] [Fintype F] [CharP F 2]
  {s : ℕ} {L : Subgroup (MulAut V)}

omit [Finite V] in
theorem act_imL_herm (hF : Fintype.card F = 2 ^ (2 * s)) (θ : ↥L ≃* SL2 F)
    (β : V ≃* Multiplicative ↥(hermA s F))
    (hβ : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (β ((l : MulAut V) v)) =
      hermAct s (sig_sig hF) (θ l) (Multiplicative.toAdd (β v)))
    (g : SL2 F) (v : V) :
    Multiplicative.toAdd (β (((θ.symm g : ↥L) : MulAut V) v)) =
      hermAct s (sig_sig hF) g (Multiplicative.toAdd (β v)) := by
  rw [hβ, MulEquiv.apply_symm_apply]

omit [Finite V] in
theorem card_fixV_imL_herm (hF : Fintype.card F = 2 ^ (2 * s)) (θ : ↥L ≃* SL2 F)
    (β : V ≃* Multiplicative ↥(hermA s F))
    (hβ : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (β ((l : MulAut V) v)) =
      hermAct s (sig_sig hF) (θ l) (Multiplicative.toAdd (β v)))
    (R : Subgroup (SL2 F)) :
    Nat.card (fixV (imL θ R)) =
      Nat.card {X : ↥(hermA s F) // ∀ g ∈ R, hermAct s (sig_sig hF) g X = X} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (β.toEquiv.trans Multiplicative.toAdd) fun v => ?_)
  show (∀ a ∈ imL θ R, a v = v) ↔ ∀ g ∈ R, hermAct s (sig_sig hF) g (Multiplicative.toAdd (β v)) =
    Multiplicative.toAdd (β v)
  constructor
  · intro h g hg
    rw [← act_imL_herm hF θ β hβ, h _ ((mem_imL θ R).mpr ⟨g, hg, rfl⟩)]
  · intro h a ha
    obtain ⟨g, hg, rfl⟩ := (mem_imL θ R).mp ha
    apply β.injective
    apply Multiplicative.toAdd.injective
    rw [act_imL_herm hF θ β hβ, h g hg]

theorem hermAct_uMat_fixed (hF : Fintype.card F = 2 ^ (2 * s)) {t : F} (ht : t ^ (2 ^ s) = t)
    (X : ↥(hermA s F)) (h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (h01 : ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ (2 ^ s) = (X : Matrix (Fin 2) (Fin 2) F) 0 1) :
    hermAct s (sig_sig hF) (uMat t) X = X := by
  have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = (X : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    rw [hermA_10, sig_apply, h01]
  refine hermA_ext ?_ ?_ ?_
  · rw [hermAct_uMat_00, sig_apply, ht, h11, h10, mul_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · rw [hermAct_uMat_01, h11, mul_zero, add_zero]
  · rw [hermAct_uMat_11]

theorem hermAct_uMat_fixed_E11 (hF : Fintype.card F = 2 ^ (2 * s)) (t : F)
    (X : ↥(hermA s F)) (h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (h01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) :
    hermAct s (sig_sig hF) (uMat t) X = X := by
  have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hermA_10, h01, map_zero]
  refine hermA_ext ?_ ?_ ?_
  · rw [hermAct_uMat_00, h11, h10, h01]
    ring
  · rw [hermAct_uMat_01, h11, mul_zero, add_zero]
  · rw [hermAct_uMat_11]

@[expose] def hermMk (hF : Fintype.card F = 2 ^ (2 * s)) (a : F) (ha : a ^ (2 ^ s) = a) (b : F)
    (d : F) (hd : d ^ (2 ^ s) = d) : ↥(hermA s F) :=
  ⟨!![a, b; b ^ (2 ^ s), d], mem_hermA_of fun i j => by
    fin_cases i <;> fin_cases j <;> simp [sig_apply, ha, hd, frob_frob hF]⟩

theorem hermMk_coe (hF : Fintype.card F = 2 ^ (2 * s)) (a : F) (ha : a ^ (2 ^ s) = a) (b : F)
    (d : F) (hd : d ^ (2 ^ s) = d) :
    ((hermMk hF a ha b d hd : ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) =
      !![a, b; b ^ (2 ^ s), d] := rfl

omit [Finite V] [Fintype F] [CharP F 2] in
theorem commSub_imL_le (θ : ↥L ≃* SL2 F) (R : Subgroup (SL2 F)) (W W' : Subgroup V)
    (h : ∀ g ∈ R, ∀ v ∈ W, ((θ.symm g : ↥L) : MulAut V) v * v⁻¹ ∈ W') :
    commSub W (imL θ R) ≤ W' := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨g, hg, rfl⟩ := (mem_imL θ R).mp hx
  exact h g hg w hw

omit [Finite V] in
theorem toAdd_comm_herm (hF : Fintype.card F = 2 ^ (2 * s)) (θ : ↥L ≃* SL2 F)
    (β : V ≃* Multiplicative ↥(hermA s F))
    (hβ : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (β ((l : MulAut V) v)) =
      hermAct s (sig_sig hF) (θ l) (Multiplicative.toAdd (β v)))
    (g : SL2 F) (v : V) :
    Multiplicative.toAdd (β (((θ.symm g : ↥L) : MulAut V) v * v⁻¹)) =
      hermAct s (sig_sig hF) g (Multiplicative.toAdd (β v)) - Multiplicative.toAdd (β v) := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, act_imL_herm hF θ β hβ, sub_eq_add_neg]

@[expose] def pullH (β : V ≃* Multiplicative ↥(hermA s F)) (H : AddSubgroup ↥(hermA s F)) :
    Subgroup V :=
  (AddSubgroup.toSubgroup H).comap β.toMonoidHom

@[expose] def herm11 (s : ℕ) (F : Type) [Field F] [CharP F 2] : AddSubgroup ↥(hermA s F) where
  carrier := {X | (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, Matrix.add_apply] at hX hY ⊢
    rw [hX, hY, add_zero]
  zero_mem' := by simp
  neg_mem' := fun {X} hX => by
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_neg, Matrix.neg_apply] at hX ⊢
    rw [hX, neg_zero]

@[expose] def herm1101 (s : ℕ) (F : Type) [Field F] [CharP F 2] : AddSubgroup ↥(hermA s F) where
  carrier := {X | (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧ (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, Matrix.add_apply] at hX hY ⊢
    rw [hX.1, hY.1, hX.2, hY.2, add_zero]
    exact ⟨rfl, rfl⟩
  zero_mem' := by simp
  neg_mem' := fun {X} hX => by
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_neg, Matrix.neg_apply] at hX ⊢
    rw [hX.1, hX.2, neg_zero]
    exact ⟨rfl, rfl⟩

omit [Finite V] in
theorem orth_realizes (hF : Fintype.card F = 2 ^ (2 * s)) (θ : ↥L ≃* SL2 F)
    (β : V ≃* Multiplicative ↥(hermA s F))
    (hβ : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (β ((l : MulAut V) v)) =
      hermAct s (sig_sig hF) (θ l) (Multiplicative.toAdd (β v))) :
    BinaryOrthogonalFour L ⊤ ⊥ s := by
  have hcard : Nat.card F = 2 ^ (2 * s) := by rw [Nat.card_eq_fintype_card, hF]
  refine ⟨F, inferInstance, inferInstance, inferInstance, hcard, ?_⟩
  set e := specialLinearGroupEquivStatedSL 2 F
  let π : ↥(StatedSL 2 F) →* ↥L := θ.symm.toMonoidHom.comp e.symm.toMonoidHom
  have hπ : Function.Surjective π := θ.symm.surjective.comp e.symm.surjective
  let β' : V ≃* ↥(hermSub s (Fin 2) F) :=
    { toFun := fun v => ⟨Multiplicative.ofAdd ((Multiplicative.toAdd (β v) : ↥(hermA s F)) :
          Matrix (Fin 2) (Fin 2) F), (Multiplicative.toAdd (β v)).2⟩
      invFun := fun X => β.symm (Multiplicative.ofAdd
        ⟨Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F)), X.2⟩)
      left_inv := fun v => by simp
      right_inv := fun X => by simp
      map_mul' := fun v w => by
        apply Subtype.ext
        simp }
  refine ⟨π, B42L2.realizesVia_of_secEquiv
    (FFModel.twistTensor_isActionModel s (StatedSL 2 F) hcard) rfl π hπ β'
    fun (γ : ↥(StatedSL 2 F)) v => ?_⟩
  have hcoe : ((e.symm γ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← specialLinearGroupEquivStatedSL_coe 2 F (e.symm γ), MulEquiv.apply_symm_apply]
  show Multiplicative.ofAdd ((Multiplicative.toAdd (β (((θ.symm (e.symm γ) : ↥L) : MulAut V) v)) :
      ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) = Multiplicative.ofAdd
      (((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((Multiplicative.toAdd (β v) : ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) *
        (frobPow s ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ)
  rw [act_imL_herm hF θ β hβ, hermAct_coe, hcoe]

theorem orth_row (hV : ∀ v : V, v ^ 2 = 1) (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s))
    {G : Subgroup (MulAut V)} (hLG : L ≤ G) (θ : ↥L ≃* SL2 F)
    (β : V ≃* Multiplicative ↥(hermA s F))
    (hβ : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (β ((l : MulAut V) v)) =
      hermAct s (sig_sig hF) (θ l) (Multiplicative.toAdd (β v))) :
    BinaryOrthogonalFour L ⊤ ⊥ s ∧ qOf G ≤ ((2 : ℚ) : WithTop ℚ) ∧
      qhatOf G ≤ ((3 / 2 : ℚ) : WithTop ℚ) := by
  classical
  have hVcard : Nat.card V = 2 ^ (4 * s) := by
    rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_hermA hs hF]
  have hKcard : Nat.card ↥(frobFixSub (F := F) s) = 2 ^ s := card_frob_fixed hs hF
  have hpos : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
  refine ⟨orth_realizes hF θ β hβ, ?_, ?_⟩
  ·
    set R := rootSub (frobFixSub (F := F) s) with hR
    set A := imL θ R with hA
    have hAcard : Nat.card A = 2 ^ s := by rw [hA, card_imL, card_rootSub, hKcard]
    have hA1 : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hAcard
      omega
    have hA2 : IsA2 G A :=
      ⟨(imL_le θ R).trans hLG, hA1, isElemAbelian2_imL θ R (rootSub_comm _) (rootSub_sq _)⟩
    have hC : 2 ^ (2 * s) ≤ Nat.card (fixV A) := by
      rw [hA, card_fixV_imL_herm hF θ β hβ]
      let f : ↥(frobFixSub (F := F) s) × ↥(frobFixSub (F := F) s) →
          {X : ↥(hermA s F) // ∀ g ∈ R, hermAct s (sig_sig hF) g X = X} := fun p =>
        ⟨hermMk hF p.1 p.1.2 p.2 0 (by simp), by
          rintro _ ⟨t, ht, rfl⟩
          exact hermAct_uMat_fixed hF ht _ rfl p.2.2⟩
      have hf : Function.Injective f := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ h
        have h1 := congrArg (fun X : {X : ↥(hermA s F) //
          ∀ g ∈ R, hermAct s (sig_sig hF) g X = X} => (X.1 : Matrix (Fin 2) (Fin 2) F)) h
        have h00 := congrFun (congrFun h1 0) 0
        have h01 := congrFun (congrFun h1 0) 1
        simp only [f] at h00 h01
        simp only [Prod.mk.injEq]
        exact ⟨Subtype.ext h00, Subtype.ext h01⟩
      have h := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod, hKcard] at h
      calc 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by ring
        _ ≤ _ := h
    have hquad : IsQuadratic A := by
      unfold IsQuadratic
      rw [commV_eq_commSub]
      refine commSub_imL_le θ R ⊤ (fixV A) fun g hg v _ => ?_
      obtain ⟨t, ht, rfl⟩ := hg
      intro y hy
      obtain ⟨g', hg', rfl⟩ := (mem_imL θ R).mp hy
      obtain ⟨t', ht', rfl⟩ := hg'
      apply β.injective
      apply Multiplicative.toAdd.injective
      rw [act_imL_herm hF θ β hβ]
      refine hermAct_uMat_fixed hF ht' _ ?_ ?_
      · rw [toAdd_comm_herm hF θ β hβ, AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_11,
          sub_self]
      · rw [toAdd_comm_herm hF θ β hβ, AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_01,
          add_sub_cancel_left, mul_pow, ht]
        have h11 := hermA_11 (a := s) (Multiplicative.toAdd (β v))
        rw [sig_apply] at h11
        rw [h11]
    rw [qOf_le_iff]
    refine ⟨A, hA2, hquad, (rAV_le_two_iff hV hA2).mpr ?_⟩
    rw [hVcard, hAcard]
    calc 2 ^ (4 * s) = (2 ^ s) ^ 2 * 2 ^ (2 * s) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hC
  ·
    set U := rootSub (⊤ : AddSubgroup F) with hU
    set A := imL θ U with hA
    have hAcard : Nat.card A = 2 ^ (2 * s) := by
      rw [hA, card_imL, card_rootSub, Nat.card_congr (AddSubgroup.topEquiv (G := F)).toEquiv,
        Nat.card_eq_fintype_card, hF]
    have hA1 : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hAcard
      have : 1 < 2 ^ (2 * s) := Nat.one_lt_two_pow (by omega)
      omega
    have hA2 : IsA2 G A :=
      ⟨(imL_le θ U).trans hLG, hA1, isElemAbelian2_imL θ U (rootSub_comm _) (rootSub_sq _)⟩
    have hC : 2 ^ s ≤ Nat.card (fixV A) := by
      rw [hA, card_fixV_imL_herm hF θ β hβ]
      let f : ↥(frobFixSub (F := F) s) →
          {X : ↥(hermA s F) // ∀ g ∈ U, hermAct s (sig_sig hF) g X = X} := fun a =>
        ⟨hermMk hF a a.2 0 0 (by simp), by
          rintro _ ⟨t, -, rfl⟩
          exact hermAct_uMat_fixed_E11 hF t _ rfl rfl⟩
      have hf : Function.Injective f := by
        intro a a' h
        have h1 := congrArg (fun X : {X : ↥(hermA s F) //
          ∀ g ∈ U, hermAct s (sig_sig hF) g X = X} => (X.1 : Matrix (Fin 2) (Fin 2) F)) h
        have h00 := congrFun (congrFun h1 0) 0
        simp only [f] at h00
        exact Subtype.ext h00
      have h := Nat.card_le_card_of_injective f hf
      rwa [hKcard] at h
    have hcubic : commSeries A 3 = ⊥ := by
      have h1 : commSub ⊤ A ≤ pullH β (herm11 s F) :=
        commSub_imL_le θ U ⊤ _ fun g hg v _ => by
          obtain ⟨t, -, rfl⟩ := hg
          show ((Multiplicative.toAdd (β _) : ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
          rw [toAdd_comm_herm hF θ β hβ, AddSubgroup.coe_sub, Matrix.sub_apply,
            hermAct_uMat_11, sub_self]
      have h2 : commSub (pullH β (herm11 s F)) A ≤ pullH β (herm1101 s F) :=
        commSub_imL_le θ U _ _ fun g hg v hv => by
          obtain ⟨t, -, rfl⟩ := hg
          have hv' : ((Multiplicative.toAdd (β v) : ↥(hermA s F)) :
              Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := hv
          show ((Multiplicative.toAdd (β (((θ.symm (uMat t) : ↥L) : MulAut V) v * v⁻¹)) :
              ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
            ((Multiplicative.toAdd (β (((θ.symm (uMat t) : ↥L) : MulAut V) v * v⁻¹)) :
              ↥(hermA s F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
          refine ⟨?_, ?_⟩
          · rw [toAdd_comm_herm hF θ β hβ, AddSubgroup.coe_sub, Matrix.sub_apply,
              hermAct_uMat_11, sub_self]
          · rw [toAdd_comm_herm hF θ β hβ, AddSubgroup.coe_sub, Matrix.sub_apply,
              hermAct_uMat_01, hv', mul_zero, add_zero, sub_self]
      have h3 : commSub (pullH β (herm1101 s F)) A = ⊥ := by
        rw [commSub_eq_bot_iff]
        intro v hv y hy
        obtain ⟨g, hg, rfl⟩ := (mem_imL θ U).mp hy
        obtain ⟨t, -, rfl⟩ := hg
        apply β.injective
        apply Multiplicative.toAdd.injective
        rw [act_imL_herm hF θ β hβ]
        exact hermAct_uMat_fixed_E11 hF t _ hv.1 hv.2
      show commSub (commSub (commSub ⊤ A) A) A = ⊥
      refine eq_bot_iff.mpr (le_trans (commSub_mono (commSub_mono h1 le_rfl) le_rfl) ?_)
      rw [← h3]
      exact commSub_mono h2 le_rfl
    refine kq_le_iff.mpr ⟨A, hA2, hcubic, rAV_le_three_halves hV hA2 ?_⟩
    rw [hVcard, hAcard]
    calc (2 ^ (4 * s)) ^ 2 = (2 ^ (2 * s)) ^ 3 * (2 ^ s) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hC 2)

end Orth

section Natural

variable {V : Type} [CommGroup V] [Finite V] {F : Type} [Field F] [Fintype F] [CharP F 2]
  {L : Subgroup (MulAut V)}

omit [Fintype F] [CharP F 2] in
theorem uMat_mulVec (t : F) (x : Fin 2 → F) :
    ((uMat t : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec x 0 = x 0 + t * x 1 ∧
      ((uMat t : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec x 1 = x 1 := by
  rw [mulVec_two_zero, mulVec_two_one, uMat_coe]
  simp

theorem natural_qhat_le_one (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {G : Subgroup (MulAut V)} (hLG : L ≤ G) (θ : ↥L ≃* SL2 F)
    (e : V ≃* Multiplicative (Fin 2 → F))
    (he : ∀ (l : ↥L) (v : V), Multiplicative.toAdd (e ((l : MulAut V) v)) =
      (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (e v))) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  classical
  refine (qhatOf_le_qOf G).trans ?_
  have hact : ∀ (g : SL2 F) (v : V), Multiplicative.toAdd (e (((θ.symm g : ↥L) : MulAut V) v)) =
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (e v)) := fun g v => by
    rw [he, MulEquiv.apply_symm_apply]
  have hFcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := by
    rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_fin,
      hFcard, sq]
  set U := rootSub (⊤ : AddSubgroup F) with hU
  set A := imL θ U with hA
  have hAcard : Nat.card A = 2 ^ n := by
    rw [hA, card_imL, card_rootSub, Nat.card_congr (AddSubgroup.topEquiv (G := F)).toEquiv,
      hFcard]
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  have hA2 : IsA2 G A :=
    ⟨(imL_le θ U).trans hLG, hA1, isElemAbelian2_imL θ U (rootSub_comm _) (rootSub_sq _)⟩
  have hfix : ∀ v : V, Multiplicative.toAdd (e v) 1 = 0 → v ∈ fixV A := by
    intro v hv y hy
    obtain ⟨g, hg, rfl⟩ := (mem_imL θ U).mp hy
    obtain ⟨t, -, rfl⟩ := hg
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hact]
    funext i
    obtain ⟨h0, h1⟩ := uMat_mulVec t (Multiplicative.toAdd (e v))
    fin_cases i
    · rw [Fin.zero_eta, h0, hv, mul_zero, add_zero]
    · exact h1
  have hC : 2 ^ n ≤ Nat.card (fixV A) := by
    let f : F → fixV A := fun a => ⟨e.symm (Multiplicative.ofAdd ![a, 0]), hfix _ (by simp)⟩
    have hf : Function.Injective f := by
      intro a a' h
      have h1 := congrArg (fun v : fixV A => Multiplicative.toAdd (e v.1) 0) h
      simpa [f] using h1
    have h := Nat.card_le_card_of_injective f hf
    rwa [hFcard] at h
  have hquad : IsQuadratic A := by
    unfold IsQuadratic
    rw [commV_eq_commSub, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, -, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_imL θ U).mp hx
    obtain ⟨t, -, rfl⟩ := hg
    refine hfix _ ?_
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hact, Pi.add_apply, Pi.neg_apply,
      (uMat_mulVec t (Multiplicative.toAdd (e v))).2, add_neg_cancel]
  rw [qOf_le_iff]
  refine ⟨A, hA2, hquad, (rAV_le_one_iff hV hA2).mpr ?_⟩
  rw [hVcard, hAcard]
  exact Nat.mul_le_mul_left _ hC

end Natural

end CFSG.Quasithin.B45L2
