module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOrbit
public import CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.L34Bin

open CFSG.Fischer CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv matRepTwist)
open scoped MatrixGroups Matrix

theorem card_F4 : Fintype.card F4 = 2 ^ 2 := by
  rw [F4.card]
  norm_num

abbrev phi2 : ZMod 2 →+* F4 := ZMod.castHom (dvd_refl 2) F4

abbrev baseF {G : Type} [Group G] {n : ℕ} (ρ₀ : G →* Matrix (Fin n) (Fin n) (ZMod 2)) :
    G →* Matrix (Fin n) (Fin n) F4 :=
  matMap phi2 ρ₀

abbrev dimT (a b : Fin 2 → Bool) : ℕ := 3 ^ cntS a b * 8 ^ cntH a b

theorem omega_ne_zero : (⟨2⟩ : F4) ≠ 0 := fun h => absurd (congrArg F4.code h) (by decide)

@[expose] def omegaU : F4ˣ := Units.mk0 ⟨2⟩ omega_ne_zero

@[expose] noncomputable def zSL : SL(3, F4) := dT omegaU omegaU

theorem omegaU_coe : (omegaU : F4) = ⟨2⟩ := rfl

theorem omega_pow_eq_one_iff (k : ℕ) : (omegaU : F4) ^ k = 1 ↔ k % 3 = 0 := by
  have h3 : (omegaU : F4) ^ 3 = 1 := by
    rw [omegaU_coe, pow_succ, pow_two]
    exact congrArg F4.mk (by decide)
  have h1 : (omegaU : F4) ^ 1 ≠ 1 := by
    rw [omegaU_coe, pow_one]
    exact fun h => absurd (congrArg F4.code h) (by decide)
  have h2 : (omegaU : F4) ^ 2 ≠ 1 := by
    rw [omegaU_coe, pow_two]
    exact fun h => absurd (congrArg F4.code h) (by decide)
  have hk : (omegaU : F4) ^ k = (omegaU : F4) ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hk]
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 3)
  · simp
  · simpa using h1
  · simpa using h2

@[expose] def digits5 : List ((Fin 2 → Bool) × (Fin 2 → Bool)) :=
  [(![true, true], ![false, false]), (![false, false], ![true, true]),
    (![true, false], ![true, false]), (![false, true], ![false, true]),
    (![true, true], ![true, true])]

theorem dimT_digits5 {d : (Fin 2 → Bool) × (Fin 2 → Bool)} (hd : d ∈ digits5) :
    (dimT d.1 d.2 = 9 ∧
      (d = (![true, true], ![false, false]) ∨ d = (![false, false], ![true, true]))) ∨
    (dimT d.1 d.2 = 8 ∧ (d = (![true, false], ![true, false]) ∨
      d = (![false, true], ![false, true]))) ∨
    (dimT d.1 d.2 = 64 ∧ d = (![true, true], ![true, true])) := by
  simp only [digits5, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide

theorem dimT_shiftBits (a b : Fin 2 → Bool) : dimT (shiftBits 2 a) (shiftBits 2 b) = dimT a b := by
  have h : ∀ a b : Fin 2 → Bool, cntS (shiftBits 2 a) (shiftBits 2 b) = cntS a b ∧
      cntH (shiftBits 2 a) (shiftBits 2 b) = cntH a b := by decide
  rw [dimT, dimT, (h a b).1, (h a b).2]

theorem finrank_tensorRep (a b : Fin 2 → Bool) :
    Module.finrank F4 (TIdx 2 a b → F4) = dimT a b :=
  ((tensorRep_absolutely_irreducible_and_distinct F4 card_F4 (by norm_num)).1 a b).2

theorem mem_digits_of_center {a b : Fin 2 → Bool}
    (h : (tensorRep (F := F4) F4 a b zSL).mulVec (hw F4 a b) = hw F4 a b) :
    (a = ![false, false] ∧ b = ![false, false]) ∨ (a, b) ∈ digits5 := by
  rw [zSL, tensorRep_dT_hw] at h
  have h1 : (algebraMap F4 F4 (omegaU : F4) ^ (mBits a + mBits b) *
      algebraMap F4 F4 (omegaU : F4) ^ mBits b) • hw F4 a b = (1 : F4) • hw F4 a b := by
    rw [h, one_smul]
  have h2 := smul_left_injective F4 (hw_ne_zero F4 a b) h1
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h2
  rw [← pow_add, omega_pow_eq_one_iff] at h2
  clear h h1
  revert h2
  revert a b
  decide

variable {n : ℕ}

theorem pow_four_F4 (x : F4) : x ^ 2 ^ 2 = x := by
  rw [← card_F4]
  exact FiniteField.pow_card x

theorem exists_pair (ρ₀ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∃ (a b : Fin 2 → Bool) (Y Y' : Subrepresentation (matRep (baseF ρ₀))),
      Y.toRepresentation.IsIrreducible ∧ Y'.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv Y.toRepresentation
        (matRep (tensorRep (F := F4) F4 a b))) ∧
      Nonempty (Representation.Equiv Y'.toRepresentation
        (matRep (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) ∧
      Y.toSubmodule ⊔ Y'.toSubmodule = ⊤ := by
  classical
  set PF := baseF ρ₀ with hPF
  have hτ : ∀ j : ℕ, matMap (frobPowEquiv F4 j : F4 →+* F4) PF = PF := by
    intro j
    rw [hPF, baseF, ← CFSG.QuasithinUnique.Setup.X7a.matMap_comp_ringHom]
    congr 1
    exact RingHom.ext_zmod _ _
  let Ψ : ∀ j : ℕ, TwistEquiv (frobPowEquiv F4 j) (matRep PF) (matRep PF) := fun j =>
    { e := (matRepTwist (frobPowEquiv F4 j) PF).e
      comm := fun g v => by
        have hent : ∀ i' j', (frobPowEquiv F4 j) (PF g i' j') = PF g i' j' := fun i' j' =>
          congrFun (congrFun (congrArg (fun R => R g) (hτ j)) i') j'
        funext i
        show frobPowEquiv F4 j ((PF g).mulVec v i) =
          (PF g).mulVec (fun i' => frobPowEquiv F4 j (v i')) i
        simp [Matrix.mulVec, dotProduct, map_sum, hent] }
  have hΨ : ∀ (j : ℕ) (w : Fin n → F4) (i : Fin n), (Ψ j).e w i = w i ^ 2 ^ j := fun j w i =>
    frobPowEquiv_apply j (w i)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨W, hW⟩ := exists_atom_subrep (matRep PF)
  have hWirr := isIrreducible_of_atom (matRep PF) W hW
  obtain ⟨a, b, ⟨eW⟩⟩ := exists_T3_equiv F4 card_F4 (by norm_num) W.toRepresentation hWirr
  let Wj : ℕ → Subrepresentation (matRep PF) := fun j => (Ψ j).mapSub W
  have hWj : ∀ j, (Wj j).toRepresentation.IsIrreducible := fun j =>
    ((Ψ j).sub W).isIrreducible hWirr
  have heq : ∀ j : ℕ, Nonempty (Representation.Equiv (Wj j).toRepresentation
      (matRep (tensorRep (F := F4) F4 ((shiftBits 2)^[j] a) ((shiftBits 2)^[j] b)))) := by
    intro j
    have h1 := ((Ψ j).sub W).nonempty_equiv_iff
      (matRepTwist (frobPowEquiv F4 j) (tensorRep (F := F4) F4 a b))
    have h2 : Nonempty (Representation.Equiv (Wj j).toRepresentation
        (matRep (matMap (frobPowEquiv F4 j : F4 →+* F4)
          (tensorRep (F := F4) F4 a b)))) := h1.mpr ⟨eW.symm⟩
    rw [matMap_frobPowEquiv_tensorRep] at h2
    obtain ⟨P', Q', hM⟩ := tensorRep_comp_frobPow F4 card_F4 j a b
    exact ⟨h2.some.trans hM.equiv.some⟩
  have hW2 : (Wj 2).toSubmodule = (Wj 0).toSubmodule := by
    have hΨ2 : ∀ w, (Ψ 2).e w = (Ψ 0).e w := fun w => by
      funext i
      rw [hΨ, hΨ, pow_four_F4, pow_zero, pow_one]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hΨ2 w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, hΨ2 w⟩
  let M : Submodule F4 (Fin n → F4) := (Wj 0).toSubmodule ⊔ (Wj 1).toSubmodule
  have hG : ∀ g, ∀ v ∈ M, ((ρ₀ g).map phi2).mulVec v ∈ M := by
    intro g v hv
    have hle0 : (Wj 0).toSubmodule ≤ M.comap (Matrix.toLin' ((ρ₀ g).map phi2)) :=
      fun w hw => Submodule.mem_sup_left ((Wj 0).apply_mem_toSubmodule g hw)
    have hle1 : (Wj 1).toSubmodule ≤ M.comap (Matrix.toLin' ((ρ₀ g).map phi2)) :=
      fun w hw => Submodule.mem_sup_right ((Wj 1).apply_mem_toSubmodule g hw)
    exact (sup_le hle0 hle1) hv
  have hΦ : ∀ v ∈ M, (fun i => v i ^ 2) ∈ M := by
    intro v hv
    refine Submodule.mem_sup.mpr ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨fun i => y i ^ 2, ?_, fun i => x i ^ 2, ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := hy
      have h1 : (fun i => ((Ψ 1).e w) i ^ 2) = (Ψ 2).e w := by
        funext i
        rw [hΨ, hΨ, ← pow_mul]
        norm_num
      show (fun i => ((Ψ 1).e w) i ^ 2) ∈ (Wj 0).toSubmodule
      rw [h1, ← hW2]
      exact Submodule.mem_map_of_mem hw
    · obtain ⟨w, hw, rfl⟩ := hx
      have h1 : (fun i => ((Ψ 0).e w) i ^ 2) = (Ψ 1).e w := by
        funext i
        rw [hΨ, hΨ, pow_zero, pow_one, pow_one]
      show (fun i => ((Ψ 0).e w) i ^ 2) ∈ (Wj 1).toSubmodule
      rw [h1]
      exact Submodule.mem_map_of_mem hw
    · funext i
      simp [CharTwo.add_sq, add_comm]
  have hWne : W.toSubmodule ≠ ⊥ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have hMne : M ≠ ⊥ := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hmem : (Ψ 0).e w ∈ M := Submodule.mem_sup_left (Submodule.mem_map_of_mem hwW)
    have hne : (Ψ 0).e w ≠ 0 := fun h => hw0 ((Ψ 0).e.injective (by rw [h, map_zero]))
    exact fun h => hne ((Submodule.mem_bot F4).mp (h ▸ hmem))
  refine ⟨a, b, Wj 0, Wj 1, hWj 0, hWj 1, heq 0, heq 1,
    descent card_F4 ρ₀ hirr M hG hΦ hMne⟩

theorem inf_eq_bot_or_le {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {Y : Subrepresentation ρ} (hY : Y.toRepresentation.IsIrreducible)
    (Z : Subrepresentation ρ) : Y.toSubmodule ⊓ Z.toSubmodule = ⊥ ∨ Y ≤ Z := by
  let S : Subrepresentation Y.toRepresentation :=
    ⟨Z.toSubmodule.comap Y.toSubmodule.subtype, fun g v hv => Z.apply_mem_toSubmodule g hv⟩
  rcases hY.eq_bot_or_eq_top S with h | h
  · left
    rw [eq_bot_iff]
    rintro v ⟨hvY, hvZ⟩
    have hv : (⟨v, hvY⟩ : Y.toSubmodule) ∈ S.toSubmodule := hvZ
    rw [h] at hv
    have := (Submodule.mem_bot k).mp hv
    exact (Submodule.mem_bot k).mpr (congrArg Subtype.val this)
  · right
    intro v hvY
    have hv : (⟨v, hvY⟩ : Y.toSubmodule) ∈ S.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact hv

theorem finrank_eq_of_pair {ρ₀ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2)}
    {a b : Fin 2 → Bool} {Y Y' : Subrepresentation (matRep (baseF ρ₀))}
    (hY : Y.toRepresentation.IsIrreducible)
    (eY : Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F4) F4 a b)))
    (eY' : Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b))))
    (htop : Y.toSubmodule ⊔ Y'.toSubmodule = ⊤) :
    n = dimT a b ∨ n = 2 * dimT a b := by
  have h1 : Module.finrank F4 Y.toSubmodule = dimT a b := by
    rw [eY.toLinearEquiv.finrank_eq, finrank_tensorRep]
  have h2 : Module.finrank F4 Y'.toSubmodule = dimT a b := by
    rw [eY'.toLinearEquiv.finrank_eq, finrank_tensorRep, dimT_shiftBits]
  have hn : Module.finrank F4 ↥(Y.toSubmodule ⊔ Y'.toSubmodule) = n := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y.toSubmodule Y'.toSubmodule
  rcases inf_eq_bot_or_le hY Y' with h | h
  · right
    rw [h, finrank_bot, add_zero, hn, h1, h2] at hsum
    omega
  · left
    have hle : Y.toSubmodule ≤ Y'.toSubmodule := h
    rw [sup_eq_right.mpr hle] at hn
    rw [← hn, h2]

theorem exists_pair_digit (ρ₀ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hZ : ρ₀ zSL = 1) (hnt : ∃ g, ρ₀ g ≠ 1) :
    ∃ (a b : Fin 2 → Bool) (Y Y' : Subrepresentation (matRep (baseF ρ₀))),
      Y.toRepresentation.IsIrreducible ∧ Y'.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv Y.toRepresentation
        (matRep (tensorRep (F := F4) F4 a b))) ∧
      Nonempty (Representation.Equiv Y'.toRepresentation
        (matRep (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) ∧
      Y.toSubmodule ⊔ Y'.toSubmodule = ⊤ ∧ (a, b) ∈ digits5 ∧
      (n = dimT a b ∨ n = 2 * dimT a b) := by
  classical
  obtain ⟨a, b, Y, Y', hY, hY', ⟨eY⟩, ⟨eY'⟩, htop⟩ := exists_pair ρ₀ hn hirr
  refine ⟨a, b, Y, Y', hY, hY', ⟨eY⟩, ⟨eY'⟩, htop, ?_, finrank_eq_of_pair hY eY eY' htop⟩
  have hZY : ∀ y : Y.toSubmodule, Y.toRepresentation zSL y = y := by
    intro y
    apply Subtype.ext
    show (matRep (baseF ρ₀) zSL) (y : Fin n → F4) = y
    rw [matRep_apply, matMap_apply, hZ, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hZT : (tensorRep (F := F4) F4 a b zSL).mulVec (hw F4 a b) = hw F4 a b := by
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ eY.toIntertwiningMap zSL
      (eY.symm (hw F4 a b))
    have h2 : eY.toIntertwiningMap (eY.symm (hw F4 a b)) = hw F4 a b :=
      Representation.Equiv.apply_symm_apply eY _
    rw [hZY, h2] at h1
    rw [← matRep_apply]
    exact h1.symm
  rcases mem_digits_of_center hZT with ⟨rfl, rfl⟩ | h
  · exfalso
    obtain ⟨g, hg⟩ := hnt
    have htriv : ∀ (Z : Subrepresentation (matRep (baseF ρ₀))),
        Representation.Equiv Z.toRepresentation
          (matRep (tensorRep (F := F4) F4 (zeros 2) (zeros 2))) →
        ∀ v ∈ Z.toSubmodule, (baseF ρ₀ g).mulVec v = v := by
      intro Z e v hv
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g ⟨v, hv⟩
      rw [matRep_apply, tensorRep_zeros_apply, Matrix.one_mulVec] at h1
      have h2 : Z.toRepresentation g ⟨v, hv⟩ = ⟨v, hv⟩ := by
        apply e.toLinearEquiv.injective
        exact h1
      exact congrArg Subtype.val h2
    have h0 : (![false, false] : Fin 2 → Bool) = zeros 2 := by decide
    have hs : shiftBits 2 (zeros 2) = zeros 2 := by decide
    rw [h0] at eY eY'
    rw [hs] at eY'
    have hall : ∀ v ∈ Y.toSubmodule ⊔ Y'.toSubmodule, (baseF ρ₀ g).mulVec v = v := by
      intro v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
      rw [Matrix.mulVec_add, htriv Y eY x hx, htriv Y' eY' y hy]
    apply hg
    have hmat : baseF ρ₀ g = 1 := by
      ext i j
      have h1 := hall (Pi.single j 1) (by rw [htop]; exact Submodule.mem_top)
      have h2 := congrFun h1 i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using h2
    apply Matrix.map_injective phi2.injective
    show (ρ₀ g).map phi2 = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map phi2
    rw [Matrix.map_one _ (map_zero _) (map_one _), ← matMap_apply]
    exact hmat
  · exact h

end CFSG.Quasithin.L34Bin
