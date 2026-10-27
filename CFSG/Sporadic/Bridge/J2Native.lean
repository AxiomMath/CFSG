module

public import CFSG.Sporadic.Bridge.J2NativeData
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.J2

open CFSG.Blueprint.NativeSporadic Matrix

set_option maxRecDepth 100000 in
theorem decode_seed₁ : decode 5 14 1 J2Seed1 = toM mA := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem decode_seed₂ : decode 5 14 1 J2Seed2 = toM mB := by
  decide +kernel

theorem wfM_seeds : wfM mA = true ∧ wfM mB = true ∧ wfM mB2 = true := by
  decide +kernel

theorem wfM_images : wfM mAl = true ∧ wfM mAli = true ∧ wfM mBe = true ∧ wfM mBei = true := by
  decide +kernel

theorem mulL_seeds : mulL mA mA = idL ∧ mulL mB mB2 = idL ∧ mulL mB2 mB = idL := by
  decide +kernel

theorem mulL_images : mulL mAl mAli = idL ∧ mulL mAli mAl = idL ∧ mulL mBe mBei = idL ∧
    mulL mBei mBe = idL := by
  decide +kernel

@[expose] noncomputable def uA : GL (Fin 14) (ZMod 5) :=
  unitL mA mA wfM_seeds.1 wfM_seeds.1 mulL_seeds.1 mulL_seeds.1

@[expose] noncomputable def uB : GL (Fin 14) (ZMod 5) :=
  unitL mB mB2 wfM_seeds.2.1 wfM_seeds.2.2 mulL_seeds.2.1 mulL_seeds.2.2

@[expose] noncomputable def uAl : GL (Fin 14) (ZMod 5) :=
  unitL mAl mAli wfM_images.1 wfM_images.2.1 mulL_images.1 mulL_images.2.1

@[expose] noncomputable def uBe : GL (Fin 14) (ZMod 5) :=
  unitL mBe mBei wfM_images.2.2.1 wfM_images.2.2.2 mulL_images.2.2.1 mulL_images.2.2.2

noncomputable abbrev seedGroup : Subgroup (GL (Fin 14) (ZMod 5)) :=
  Subgroup.closure {uA, uB}

theorem seedMonoid_eq : seedMonoid 5 14 1 J2Seed1 J2Seed2 =
    Submonoid.closure {(uA : Matrix (Fin 14) (Fin 14) (ZMod 5)), (uB : Matrix _ _ _)} := by
  unfold seedMonoid
  rw [decode_seed₁, decode_seed₂]
  rfl

noncomputable def nativeEquiv : Blueprint.NativeSporadic.J2 ≃* seedGroup := by
  change (seedMonoid 5 14 1 J2Seed1 J2Seed2)ˣ ≃* _
  rw [seedMonoid_eq]
  exact unitSeedEquiv uA uB

@[expose] def natX (i : ℕ) : List (List ℕ) := cond (Nat.beq i 0) mA mB

@[expose] def natXi (i : ℕ) : List (List ℕ) := cond (Nat.beq i 0) mA mB2

@[expose] noncomputable def natU (i : ℕ) : GL (Fin 14) (ZMod 5) := cond (Nat.beq i 0) uA uB

@[expose] def presX (i : ℕ) : List (List ℕ) := cond (Nat.beq i 0) mAl mBe

@[expose] def presXi (i : ℕ) : List (List ℕ) := cond (Nat.beq i 0) mAli mBei

@[expose] noncomputable def presU (i : ℕ) : GL (Fin 14) (ZMod 5) := cond (Nat.beq i 0) uAl uBe

theorem natX_wf (i : ℕ) : wfM (natX i) = true := by
  unfold natX; cases Nat.beq i 0
  · exact wfM_seeds.2.1
  · exact wfM_seeds.1

theorem natXi_wf (i : ℕ) : wfM (natXi i) = true := by
  unfold natXi; cases Nat.beq i 0
  · exact wfM_seeds.2.2
  · exact wfM_seeds.1

theorem natU_val (i : ℕ) : (natU i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (natX i) := by
  unfold natU natX; cases Nat.beq i 0 <;> rfl

theorem natU_inv (i : ℕ) :
    (((natU i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (natXi i) := by
  unfold natU natXi; cases Nat.beq i 0 <;> rfl

theorem natU_mem (i : ℕ) : natU i ∈ seedGroup := by
  unfold natU; cases Nat.beq i 0
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem presX_wf (i : ℕ) : wfM (presX i) = true := by
  unfold presX; cases Nat.beq i 0
  · exact wfM_images.2.2.1
  · exact wfM_images.1

theorem presXi_wf (i : ℕ) : wfM (presXi i) = true := by
  unfold presXi; cases Nat.beq i 0
  · exact wfM_images.2.2.2
  · exact wfM_images.2.1

theorem presU_val (i : ℕ) : (presU i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (presX i) := by
  unfold presU presX; cases Nat.beq i 0 <;> rfl

theorem presU_inv (i : ℕ) :
    (((presU i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (presXi i) := by
  unfold presU presXi; cases Nat.beq i 0 <;> rfl

theorem val_natWord {w : List (ℕ × Bool)} {Z : List (List ℕ)} (h : lwordL natX natXi w idL = Z) :
    ((Bridge.wordProd natU w : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM Z :=
  val_wordProd_of_lwordL natX_wf natXi_wf natU_val natU_inv h

theorem val_presWord {w : List (ℕ × Bool)} {Z : List (List ℕ)}
    (h : lwordL presX presXi w idL = Z) :
    ((Bridge.wordProd presU w : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM Z :=
  val_wordProd_of_lwordL presX_wf presXi_wf presU_val presU_inv h

theorem natWord_mem (w : List (ℕ × Bool)) : Bridge.wordProd natU w ∈ seedGroup :=
  Bridge.wordProd_mem natU_mem w

theorem lwordL_wAl : lwordL natX natXi wAl idL = mAl := by
  decide +kernel

theorem lwordL_wBe : lwordL natX natXi wBe idL = mBe := by
  decide +kernel

theorem uAl_eq : uAl = Bridge.wordProd natU wAl := Units.ext (val_natWord lwordL_wAl).symm

theorem uBe_eq : uBe = Bridge.wordProd natU wBe := Units.ext (val_natWord lwordL_wBe).symm

theorem presU_mem (i : ℕ) : presU i ∈ seedGroup := by
  unfold presU; cases Nat.beq i 0
  · rw [uBe_eq]; exact natWord_mem _
  · rw [uAl_eq]; exact natWord_mem _

theorem lwordL_wA : lwordL presX presXi wA idL = mA := by
  decide +kernel

theorem lwordL_wB : lwordL presX presXi wB idL = mB := by
  decide +kernel

theorem uA_eq : uA = Bridge.wordProd presU wA := Units.ext (val_presWord lwordL_wA).symm

theorem uB_eq : uB = Bridge.wordProd presU wB := Units.ext (val_presWord lwordL_wB).symm

@[expose] def r₁L : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, false), (1, false)]

@[expose] def r₂L : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false),
    (1, false)]

@[expose] def wL : List (ℕ × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (1, false), (1, false), (0, true), (0, true),
    (0, true), (1, false)]

@[expose] def r₃L : List (ℕ × Bool) :=
  wL ++ wL ++ wL ++ [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]

theorem lwordL_relators : lwordL presX presXi r₁L idL = idL ∧
    lwordL presX presXi r₂L idL = idL ∧ lwordL presX presXi r₃L idL = idL := by
  decide +kernel

theorem presU_relator : ∀ v ∈ [r₁L, r₂L, r₃L], Bridge.wordProd presU v = 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl)
  · exact wordProd_eq_one_of_lwordL presX_wf presXi_wf presU_val presU_inv lwordL_relators.1
  · exact wordProd_eq_one_of_lwordL presX_wf presXi_wf presU_val presU_inv lwordL_relators.2.1
  · exact wordProd_eq_one_of_lwordL presX_wf presXi_wf presU_val presU_inv lwordL_relators.2.2

theorem length_dvd_card_seedGroup {Xs : List (List (List ℕ))} {ws : List (List (ℕ × Bool))}
    {O : List (List ℕ)} {par lab : List ℕ}
    (hws : ∀ j < Xs.length, lwordL natX natXi (ws.getD j []) idL = Xs.getD j [])
    (h : orbitOK Xs O par lab = true) : O.length ∣ Nat.card seedGroup := by
  have hdvd := length_dvd_card_of_orbitOK (fun j => Bridge.wordProd natU (ws.getD j []))
    (fun j hj => val_natWord (hws j hj)) h
  refine dvd_trans hdvd (Subgroup.card_dvd_of_le ?_)
  rw [Subgroup.closure_le]
  rintro _ ⟨j, _, rfl⟩
  exact natWord_mem _

theorem orbit₂_ok : orbitOK [mP2a, mP2b, mP2c] orbit2 par2 lab2 = true := by
  decide +kernel

theorem orbit₃_ok : orbitOK [mP3a, mP3b] orbit3 par3 lab3 = true := by
  decide +kernel

theorem orbit₅_ok : orbitOK [mP5a, mP5b] orbit5 par5 lab5 = true := by
  decide +kernel

theorem orbit₇_ok : orbitOK [mAl] orbit7 par7 lab7 = true := by
  decide +kernel

theorem lwordL_sylow : lwordL natX natXi wP2a idL = mP2a ∧ lwordL natX natXi wP2b idL = mP2b ∧
    lwordL natX natXi wP2c idL = mP2c ∧ lwordL natX natXi wP3a idL = mP3a ∧
    lwordL natX natXi wP3b idL = mP3b ∧ lwordL natX natXi wP5a idL = mP5a ∧
    lwordL natX natXi wP5b idL = mP5b := by
  decide +kernel

theorem dvd_card_seedGroup₂ : 128 ∣ Nat.card seedGroup := by
  have h := length_dvd_card_seedGroup (ws := [wP2a, wP2b, wP2c]) (fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    obtain ⟨h₁, h₂, h₃, -⟩ := lwordL_sylow
    interval_cases j
    · exact h₁
    · exact h₂
    · exact h₃) orbit₂_ok
  rwa [show orbit2.length = 128 by decide +kernel] at h

theorem dvd_card_seedGroup₃ : 27 ∣ Nat.card seedGroup := by
  have h := length_dvd_card_seedGroup (ws := [wP3a, wP3b]) (fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    obtain ⟨-, -, -, h₁, h₂, -⟩ := lwordL_sylow
    interval_cases j
    · exact h₁
    · exact h₂) orbit₃_ok
  rwa [show orbit3.length = 27 by decide +kernel] at h

theorem dvd_card_seedGroup₅ : 25 ∣ Nat.card seedGroup := by
  have h := length_dvd_card_seedGroup (ws := [wP5a, wP5b]) (fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    obtain ⟨-, -, -, -, -, h₁, h₂⟩ := lwordL_sylow
    interval_cases j
    · exact h₁
    · exact h₂) orbit₅_ok
  rwa [show orbit5.length = 25 by decide +kernel] at h

theorem dvd_card_seedGroup₇ : 7 ∣ Nat.card seedGroup := by
  have h := length_dvd_card_seedGroup (ws := [wAl]) (fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j
    exact lwordL_wAl) orbit₇_ok
  rwa [show orbit7.length = 7 by decide +kernel] at h

theorem le_card_seedGroup : 604800 ≤ Nat.card seedGroup := by
  have h₁ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 128 27)
    dvd_card_seedGroup₂ dvd_card_seedGroup₃
  have h₂ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (128 * 27) 25) h₁
    dvd_card_seedGroup₅
  have h₃ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (128 * 27 * 25) 7) h₂
    dvd_card_seedGroup₇
  exact Nat.le_of_dvd Nat.card_pos h₃

end CFSG.Sporadic.Bridge.J2
