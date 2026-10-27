module

public import CFSG.Quasithin.Background.SmithB45Alt7Res
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
  CFSG.QuasithinUnique.Setup.Offender

@[expose] def proj (k : Fin 7) : Vec 28 →ₗ[ZMod 2] Vec 4 where
  toFun u := fun m => u ⟨4 * k.val + m.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem proj_toVec (k : Fin 7) (X : ℕ) : proj k (toVec 28 X) = toVec 4 (X >>> (4 * k.val)) := by
  funext m
  change toVec 28 X ⟨4 * k.val + m.val, _⟩ = toVec 4 (X >>> (4 * k.val)) m
  rw [toVec_apply, toVec_apply, Nat.testBit_shiftRight]

theorem shift_bits : ∀ Y < 16, ∀ a k : Fin 7, ∀ m : Fin 4,
    ((Y <<< (4 * a.val)) >>> (4 * k.val)).testBit m.val = (decide (k = a) && Y.testBit m.val) := by
  decide +kernel

theorem toVec_shift_self {Y : ℕ} (hY : Y < 16) (a : Fin 7) :
    toVec 4 ((Y <<< (4 * a.val)) >>> (4 * a.val)) = toVec 4 Y := by
  funext m
  rw [toVec_apply, shift_bits Y hY a a m]
  simp [toVec_apply]

theorem toVec_shift_ne {Y : ℕ} (hY : Y < 16) {a k : Fin 7} (h : k ≠ a) :
    toVec 4 ((Y <<< (4 * a.val)) >>> (4 * k.val)) = 0 := by
  funext m
  rw [toVec_apply, shift_bits Y hY a k m]
  simp [h]

theorem one_shift_split : ∀ j : Fin 28,
    1 <<< j.val = (1 <<< (j.val % 4)) <<< (4 * (j.val / 4)) := by
  decide +kernel

section Ind

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

@[expose] noncomputable def phiI (ψ : Vec 4 →ₗ[ZMod 2] Additive V) :
    Vec 28 →ₗ[ZMod 2] Additive V :=
  ∑ k : Fin 7, ((rho7 ι (tk k) : Additive V ≃ₗ[ZMod 2] Additive V) :
    Additive V →ₗ[ZMod 2] Additive V).comp (ψ.comp (proj k))

theorem phiI_shift (ψ : Vec 4 →ₗ[ZMod 2] Additive V) {Y : ℕ} (hY : Y < 16) (a : Fin 7) :
    phiI ι ψ (toVec 28 (Y <<< (4 * a.val))) = rho7 ι (tk a) (ψ (toVec 4 Y)) := by
  unfold phiI
  rw [LinearMap.sum_apply, Finset.sum_eq_single a]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [proj_toVec, toVec_shift_self hY]
  · intro k _ hk
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [proj_toVec, toVec_shift_ne hY hk, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem phiI_single (ψ : Vec 4 →ₗ[ZMod 2] Additive V) (j : Fin 28) :
    phiI ι ψ (Pi.single j 1) = rho7 ι (tk ⟨j.val / 4, by omega⟩)
      (ψ (Pi.single ⟨j.val % 4, by omega⟩ 1)) := by
  have h1 : (Pi.single j 1 : Vec 28) = toVec 28 ((1 <<< (j.val % 4)) <<< (4 * (j.val / 4))) := by
    rw [← one_shift_split, toVec_one_shiftLeft 28 j.val j.isLt]
  have hlt : 1 <<< (j.val % 4) < 16 := by
    have : j.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Nat.one_shiftLeft]
    calc 2 ^ (j.val % 4) < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) this
      _ = 16 := by norm_num
  rw [h1, phiI_shift ι ψ hlt ⟨j.val / 4, by omega⟩]
  congr 2
  exact toVec_one_shiftLeft 4 _ _

theorem indCols_getD (c b : Bool) (j : Fin 28) :
    (indCols c b).getD j.val 0 =
      wapp 4 (blkOf (rB c)) (cosW b (j.val / 4)) (1 <<< (j.val % 4)) <<<
        (4 * g7N b (j.val / 4)) := by
  unfold indCols
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt]
  rfl

theorem dim_rB (c : Bool) : eNs.getD (rB c + 1) 0 - eNs.getD (rB c) 0 = 4 := by
  cases c <;> decide

theorem blkOf_rB_lt (c : Bool) : ∀ b, ∀ j < 4, (blkOf (rB c) b).getD j 0 < 2 ^ 4 := by
  intro b j hj
  unfold blkOf
  rw [dim_rB]
  exact blkCols_lt _ _ 4 j hj

theorem phiI_gen {c : Bool} {ψ : Vec 4 →ₗ[ZMod 2] Additive V}
    (hψ : ∀ b s, ψ (lin 4 (blkOf (rB c) b) s) = sigma6 ι (gen b) (ψ s)) (b : Bool)
    (u : Vec 28) :
    phiI ι ψ (lin 28 (indCols c b) u) = rho7 ι (gen7 b) (phiI ι ψ u) := by
  have key : (phiI ι ψ).comp (lin 28 (indCols c b)) =
      ((rho7 ι (gen7 b) : Additive V ≃ₗ[ZMod 2] Additive V) :
        Additive V →ₗ[ZMod 2] Additive V).comp (phiI ι ψ) := by
    apply linearMap_ext_basis (d := 28)
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    set k : Fin 7 := ⟨j.val / 4, by omega⟩ with hk
    set m : Fin 4 := ⟨j.val % 4, by omega⟩ with hm
    rw [lin_single, indCols_getD, phiI_single]
    have hg : g7N b (j.val / 4) = ((gen7 b : Perm (Fin 7)) k).val := (gen7_apply_val b k).symm
    have hY : wapp 4 (blkOf (rB c)) (cosW b (j.val / 4)) (1 <<< (j.val % 4)) < 16 := by
      have := wapp_lt (d := 4) (cols := blkOf (rB c)) (blkOf_rB_lt c) (cosW b (j.val / 4))
        (v := 1 <<< (j.val % 4)) (one_shiftLeft_lt (by omega))
      simpa using this
    rw [hg, phiI_shift ι ψ hY, toVec_wapp, toVec_one_shiftLeft 4 _ (by omega)]
    rw [wmap_intertwine (fun b' => lin 4 (blkOf (rB c) b'))
      (fun b' => ((sigma6 ι (gen b') : Additive V ≃ₗ[ZMod 2] Additive V) :
        Additive V →ₗ[ZMod 2] Additive V)) ψ (fun b' s => hψ b' s), ← σ_evalG]
    rw [sigma6_apply, ← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
    have h1 : gen7 b * tk k = tk ((gen7 b : Perm (Fin 7)) k) * j6 (evalG (cosW b k.val)) :=
      Subtype.ext (coset_rel b k)
    rw [h1]
  exact LinearMap.congr_fun key u

end Ind

theorem baseOK_facts (c : Bool) :
    (∀ i : Fin 28, papply 28 (indB c) ((indT c).getD i.val 0) = 1 <<< i.val) ∧
    (∀ b : Bool, ∀ j : Fin 28, papply 28 (indB c) ((indM c b).getD j.val 0) =
      papply 28 (indCols c b) ((indB c).getD j.val 0)) := by
  have h : baseOK c = true := by
    cases c
    · exact baseOK_false
    · exact baseOK_true
  unfold baseOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i => h1 i i.isLt, fun b j => ?_⟩
  cases b
  · exact h2 j j.isLt
  · exact h3 j j.isLt

theorem lin_indB_indT (c : Bool) (u : Vec 28) : lin 28 (indB c) (lin 28 (indT c) u) = u := by
  have : (lin 28 (indB c)).comp (lin 28 (indT c)) = LinearMap.id := by
    apply linearMap_ext_basis
    intro i
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [lin_single, ← toVec_papply, (baseOK_facts c).1 i, toVec_one_shiftLeft 28 i.val i.isLt]
  exact LinearMap.congr_fun this u

theorem lin_indB_indM (c b : Bool) (u : Vec 28) :
    lin 28 (indB c) (lin 28 (indM c b) u) = lin 28 (indCols c b) (lin 28 (indB c) u) := by
  have : (lin 28 (indB c)).comp (lin 28 (indM c b)) =
      (lin 28 (indCols c b)).comp (lin 28 (indB c)) := by
    apply linearMap_ext_basis
    intro j
    simp only [LinearMap.comp_apply]
    rw [lin_single, lin_single, ← toVec_papply, ← toVec_papply, (baseOK_facts c).2 b j]
  exact LinearMap.congr_fun this u

theorem flag_facts (c : Bool) :
    (indNs c).getD 0 0 = 0 ∧ (indNs c).getD (indSteps c) 0 = 28 ∧
      (∀ i < indSteps c, (indNs c).getD i 0 < (indNs c).getD (i + 1) 0) ∧
      (∀ i ≤ indSteps c, ∀ j < (indNs c).getD i 0,
        (indM c false).getD j 0 < 2 ^ (indNs c).getD i 0 ∧
          (indM c true).getD j 0 < 2 ^ (indNs c).getD i 0) := by
  have h : flagOK c = true := by
    cases c
    · exact flagOK_false
    · exact flagOK_true
  unfold flagOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
    at h
  obtain ⟨⟨⟨⟨-, h0⟩, hN⟩, hmono⟩, hfl⟩ := h
  exact ⟨h0, hN, hmono, fun i hi j hj => hfl i (by omega) j hj⟩

theorem blocks_irred (c : Bool) : ∀ i < indSteps c,
    IrredPair (fun b => lin ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (indBlk c i b)) := by
  intro i hi
  have h : blocksOK c = true := by
    cases c
    · exact blocksOK_false
    · exact blocksOK_true
  unfold blocksOK at h
  rw [List.all_eq_true] at h
  have hi' := h i (List.mem_range.2 hi)
  unfold nortonAt at hi'
  cases c
  · exact nortonOK_sound hi'
  · exact nortonOK_sound hi'

theorem exists_block_of_quot (c : Bool) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (gW : Bool → (W →ₗ[ZMod 2] W)) (hW : IrredPair gW)
    (hWne : (⊤ : Submodule (ZMod 2) W) ≠ ⊥) (φ : Vec 28 →ₗ[ZMod 2] W)
    (hφ : Function.Surjective φ) (hφeq : ∀ b u, φ (lin 28 (indCols c b) u) = gW b (φ u)) :
    ∃ i < indSteps c, ∃ Ψ : Vec ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) ≃ₗ[ZMod 2] W,
      ∀ b s, Ψ (lin _ (indBlk c i b) s) = gW b (Ψ s) := by
  obtain ⟨hns0, hnsN, hmono, hfl⟩ := flag_facts c
  have hsurj : Function.Surjective (φ.comp (lin 28 (indB c))) := by
    rw [LinearMap.coe_comp]
    exact hφ.comp fun u => ⟨lin 28 (indT c) u, lin_indB_indT c u⟩
  have hφeq' : ∀ b u, (φ.comp (lin 28 (indB c))) (lin 28 (indM c b) u) =
      gW b ((φ.comp (lin 28 (indB c))) u) := by
    intro b u
    simp only [LinearMap.comp_apply]
    rw [lin_indB_indM, hφeq]
  have hinv : ∀ i ≤ indSteps c, ∀ b, ∀ w ∈ Fl 28 ((indNs c).getD i 0),
      lin 28 (indM c b) w ∈ Fl 28 ((indNs c).getD i 0) := by
    intro i hi b w hw
    apply lin_mem_Fl _ hw
    intro j hj
    have := hfl i hi j hj
    cases b
    · exact this.1
    · exact this.2
  have hwin : ∀ i < indSteps c,
      (indNs c).getD i 0 + ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) ≤ 28 := by
    intro i hi
    have h1 := hmono i hi
    have h2 : (indNs c).getD (i + 1) 0 ≤ (indNs c).getD (indSteps c) 0 :=
      ns_mono (ns := fun i => (indNs c).getD i 0) (nSteps := indSteps c) hmono (i + 1)
        (indSteps c) (by omega) le_rfl
    omega
  have hirr : ∀ i < indSteps c, IrredPair (fun b => blockMap 28 ((indNs c).getD i 0)
      ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (lin 28 (indM c b))) := by
    intro i hi
    have : (fun b => blockMap 28 ((indNs c).getD i 0)
        ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (lin 28 (indM c b))) =
        fun b => lin ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (indBlk c i b) := by
      funext b
      exact blockMap_lin (hwin i hi) (indM c b)
    rw [this]
    exact blocks_irred c i hi
  obtain ⟨i, hi, Ψ, hΨ⟩ := chain_jh (N := 28) (fun i => (indNs c).getD i 0) (indSteps c) hns0
    hnsN hmono (fun b => lin 28 (indM c b)) hinv hirr gW hW hWne
    (φ.comp (lin 28 (indB c))) hsurj hφeq'
  refine ⟨i, hi, Ψ, fun b s => ?_⟩
  have := hΨ b s
  rw [blockMap_lin (hwin i hi)] at this
  exact this

section Main

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)] [Finite V]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

omit [Finite V] in
theorem card_eq_of_equiv {d : ℕ} (Ψ : Vec d ≃ₗ[ZMod 2] Additive V) : Nat.card V = 2 ^ d := by
  have h1 : Nat.card (Vec d) = Nat.card (Additive V) := Nat.card_congr Ψ.toEquiv
  have h2 : Nat.card (Additive V) = Nat.card V := rfl
  rw [← h2, ← h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin]

theorem exists_four_block
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hcard : Nat.card V ≤ 2 ^ 12) (c : Bool) {ψ : Vec 4 →ₗ[ZMod 2] Additive V}
    (hψi : Function.Injective ψ)
    (hψ : ∀ b s, ψ (lin 4 (blkOf (rB c) b) s) = sigma6 ι (gen b) (ψ s)) :
    ∃ i < 2, ∃ Ψ : Vec 4 ≃ₗ[ZMod 2] Additive V,
      ∀ b s, Ψ (lin 4 (indBlk true i b) s) = rho7 ι (gen7 b) (Ψ s) := by
  have hne : ψ (Pi.single 0 1) ≠ 0 := by
    intro h
    have h1 : (Pi.single 0 1 : Vec 4) = 0 := hψi (h.trans (map_zero ψ).symm)
    have h2 := congrFun h1 0
    simp at h2
  have hWne : (⊤ : Submodule (ZMod 2) (Additive V)) ≠ ⊥ := by
    intro h
    apply hne
    have : ψ (Pi.single 0 1) ∈ (⊤ : Submodule (ZMod 2) (Additive V)) := trivial
    rw [h, Submodule.mem_bot] at this
    exact this
  have hsurj : Function.Surjective (phiI ι ψ) := by
    have hU := irred_gen7 ι hirr (LinearMap.range (phiI ι ψ)) (by
      rintro b _ ⟨u, rfl⟩
      exact ⟨lin 28 (indCols c b) u, phiI_gen ι hψ b u⟩)
    rcases hU with h | h
    · exfalso
      apply hne
      have hmem : phiI ι ψ (Pi.single 0 1) ∈ LinearMap.range (phiI ι ψ) := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot, phiI_single] at hmem
      exact (rho7 ι _).injective (hmem.trans (map_zero _).symm)
    · exact LinearMap.range_eq_top.mp h
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_of_quot c _ (irred_gen7 ι hirr) hWne (phiI ι ψ) hsurj
    (phiI_gen ι hψ)
  have hc := card_eq_of_equiv Ψ
  cases c
  · exfalso
    have hi2 : i < 2 := hi
    interval_cases i
    · have h14 : (indNs false).getD (0 + 1) 0 - (indNs false).getD 0 0 = 14 := by decide
      rw [h14] at hc
      rw [hc] at hcard
      norm_num at hcard
    · have h14 : (indNs false).getD (1 + 1) 0 - (indNs false).getD 1 0 = 14 := by decide
      rw [h14] at hc
      rw [hc] at hcard
      norm_num at hcard
  · have hi3 : i < 3 := hi
    interval_cases i
    · exact ⟨0, by norm_num, Ψ, hΨ⟩
    · exact ⟨1, by norm_num, Ψ, hΨ⟩
    · exfalso
      have h20 : (indNs true).getD (2 + 1) 0 - (indNs true).getD 2 0 = 20 := by decide
      rw [h20] at hc
      rw [hc] at hcard
      norm_num at hcard

end Main

end CFSG.Quasithin.B45Alt7
