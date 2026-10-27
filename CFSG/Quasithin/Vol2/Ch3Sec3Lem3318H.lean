module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318F

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_single_mem {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (S : Subgroup (Multiplicative (ι → κ → ZMod 2)))
    (h : ∀ i j, Multiplicative.ofAdd (Pi.single i (Pi.single j (1 : ZMod 2))) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∏ i, ∏ j, Multiplicative.ofAdd
      (Pi.single i (Pi.single j (Multiplicative.toAdd x i j))) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_prod, toAdd_ofAdd]
    funext i' j'
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single i']
    · rw [Finset.sum_eq_single j']
      · simp
      · intro j _ hj
        simp [hj.symm]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      simp [hi.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hx]
  refine S.prod_mem fun i _ => S.prod_mem fun j _ => ?_
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd x i j) with h0 | h1
  · rw [h0, Pi.single_zero, Pi.single_zero, ofAdd_zero]
    exact S.one_mem
  · rw [h1]
    exact h i j

@[expose] def ext3 (n k : ℕ) :
    Multiplicative (Fin k → Fin 3 → ZMod 2) →* (Fin k → Multiplicative (Fin n → ZMod 2)) where
  toFun x i := Multiplicative.ofAdd fun a =>
    if h : (a : ℕ) < 3 then Multiplicative.toAdd x i ⟨a, h⟩ else 0
  map_one' := by
    funext i
    apply Multiplicative.toAdd.injective
    funext a
    simp
  map_mul' x y := by
    funext i
    apply Multiplicative.toAdd.injective
    funext a
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, Pi.mul_apply]
    split_ifs <;> simp

theorem ext3_apply (n k : ℕ) (x : Multiplicative (Fin k → Fin 3 → ZMod 2)) (i : Fin k)
    (a : Fin n) : Multiplicative.toAdd (ext3 n k x i) a =
      if h : (a : ℕ) < 3 then Multiplicative.toAdd x i ⟨a, h⟩ else 0 := rfl

theorem ext3_injective (n k : ℕ) (hn : 3 ≤ n) : Function.Injective (ext3 n k) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  funext i a
  have := congrArg (fun c : Fin k → Multiplicative (Fin n → ZMod 2) =>
    Multiplicative.toAdd (c i) (⟨a, by omega⟩ : Fin n)) hxy
  simp only [ext3_apply] at this
  split_ifs at this with h
  · exact this
  · exact absurd a.isLt h

theorem ext3_apply_of_le (n k : ℕ) (x : Multiplicative (Fin k → Fin 3 → ZMod 2)) (i : Fin k)
    {a : Fin n} (ha : 3 ≤ (a : ℕ)) : Multiplicative.toAdd (ext3 n k x i) a = 0 := by
  rw [ext3_apply]
  split_ifs with h
  · omega
  · rfl

theorem exists_ext3 {n k : ℕ} (hn : 3 ≤ n) {c : Fin k → Multiplicative (Fin n → ZMod 2)}
    (hc : ∀ i (a : Fin n), 3 ≤ (a : ℕ) → Multiplicative.toAdd (c i) a = 0) :
    ∃ x, ext3 n k x = c := by
  refine ⟨Multiplicative.ofAdd fun i (a : Fin 3) =>
    Multiplicative.toAdd (c i) ⟨a, by omega⟩, ?_⟩
  funext i
  apply Multiplicative.toAdd.injective
  funext a
  rw [ext3_apply]
  split_ifs with ha
  · rfl
  · exact (hc i a (by omega)).symm

@[expose] noncomputable def W₃ {L T : Subgroup G} {n k : ℕ}
    (Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)) : Subgroup G :=
  ((vPlus L T).subtype.comp (Φ.comp (ext3 n k))).range

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem card_W₃ (hD : Data G T M L D n k α Φ) : Nat.card (W₃ Φ) = 8 ^ k := by
  have hinj : Function.Injective ((vPlus L T).subtype.comp (Φ.comp (ext3 n k))) :=
    (vPlus L T).subtype_injective.comp (hD.inj.comp (ext3_injective n k (by have := hD.n4; omega)))
  rw [W₃, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun, Nat.card_zmod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem W₃_le_commV (hD : Data G T M L D n k α Φ) : W₃ Φ ≤ ⁅vPlus L T, L⁆ := by
  rintro _ ⟨x, rfl⟩
  exact hD.mem_commV _

theorem commV_le (hD : Data G T M L D n k α Φ) : ⁅vPlus L T, L⁆ ≤ L := by
  have hred := Hyp331.vPlus_reduced hD.hyp.toSetup331
  have hVT : vPlus L T ≤ T :=
    (hred.1.trans inf_le_left).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf)
  exact Ch3Sec3.commutator_le_right_of_le_normalizer (hVT.trans hD.TL)

theorem mem_pCoreOf_of_mem (hD : Data G T M L D n k α Φ) {x : G} (hxL : x ∈ L)
    (hxV : x ∈ vPlus L T) : x ∈ pCoreOf 2 L := by
  have hab := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
  have hxC : x ∈ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hab.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxV⟩)
  have h1 : α ⟨x, hxL⟩ = 1 := (hD.ker_iff ⟨x, hxL⟩).mpr hxC
  have h2 : (⟨x, hxL⟩ : ↥L) ∈ α.ker := h1
  rw [hD.ker] at h2
  exact (Lem3328.mem_pCore_iff _).mp h2

theorem W₃_le_pCoreOf (hD : Data G T M L D n k α Φ) : W₃ Φ ≤ pCoreOf 2 L := by
  rintro _ ⟨x, rfl⟩
  exact hD.mem_pCoreOf_of_mem (hD.commV_le (hD.mem_commV _)) (Φ _).2

theorem le_normalizer_Y (hD : Data G T M L D n k α Φ) (I : Set ℕ) :
    T ≤ Subgroup.normalizer (liftCore α (flagStabilizer n (ZMod 2) I) : Set G) := fun _ ht =>
  L3316.mem_normalizer_perfectCore (hD.le_normalizer_liftPre I ht)

theorem pCoreOf_le_pCoreOf (hD : Data G T M L D n k α Φ) {Y : Subgroup G} (hYL : Y ≤ L) :
    pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (Y ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right)
    ((sup_le_sup_right hYL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem vPlus_le_pCoreOf (hD : Data G T M L D n k α Φ) {Y : Subgroup G} (hYL : Y ≤ L) :
    vPlus L T ≤ pCoreOf 2 (Y ⊔ T) :=
  ((Hyp331.vPlus_reduced hD.hyp.toSetup331).1.trans inf_le_left).trans
    (hD.pCoreOf_le_pCoreOf hYL)

theorem ext3_single {n k : ℕ} (hn : 3 ≤ n) (i : Fin k) (a : Fin 3) :
    ext3 n k (Multiplicative.ofAdd (Pi.single i (Pi.single a 1))) =
      Pi.mulSingle i (Multiplicative.ofAdd (Pi.single (⟨a, by omega⟩ : Fin n) 1)) := by
  funext j
  apply Multiplicative.toAdd.injective
  funext b
  rw [ext3_apply]
  by_cases hji : j = i
  · subst hji
    rw [Pi.mulSingle_eq_same, toAdd_ofAdd]
    split_ifs with hb
    · simp only [toAdd_ofAdd, Pi.single_eq_same]
      by_cases hab : (⟨b, hb⟩ : Fin 3) = a
      · subst hab
        simp
      · have : b ≠ ⟨a, by omega⟩ := fun e => hab (Fin.ext (by
          have := congrArg Fin.val e
          simpa using this))
        rw [Pi.single_eq_of_ne hab, Pi.single_eq_of_ne this]
    · have : b ≠ ⟨a, by omega⟩ := fun e => hb (by
        have := congrArg Fin.val e
        simp only at this
        rw [this]
        exact a.isLt)
      rw [toAdd_ofAdd, Pi.single_eq_of_ne this]
  · rw [Pi.mulSingle_eq_of_ne hji, toAdd_one]
    split_ifs
    · simp [Pi.single_eq_of_ne hji]
    · rfl

theorem W₃_le_commutator (hD : Data G T M L D n k α Φ) :
    W₃ Φ ≤ ⁅vPlus L T, liftCore α (flagStabilizer n (ZMod 2) {3})⁆ := by
  classical
  have hn := hD.n4
  set Y := liftCore α (flagStabilizer n (ZMod 2) {3}) with hY
  set S := (⁅vPlus L T, Y⁆).comap ((vPlus L T).subtype.comp (Φ.comp (ext3 n k))) with hS
  suffices hS' : S = ⊤ by
    rintro _ ⟨x, rfl⟩
    have : x ∈ S := hS' ▸ Subgroup.mem_top x
    exact this
  refine eq_top_of_single_mem S fun i a => ?_
  show ((Φ (ext3 n k (Multiplicative.ofAdd (Pi.single i (Pi.single a 1))))) : G) ∈ ⁅vPlus L T, Y⁆
  rw [ext3_single (by omega)]
  obtain ⟨b, hba⟩ : ∃ b : Fin 3, b ≠ a := ⟨a + 1, by
    intro h
    have := congrArg (fun x : Fin 3 => (x : ℕ)) h
    fin_cases a <;> simp_all⟩
  set a' : Fin n := ⟨a, by omega⟩ with ha'
  set b' : Fin n := ⟨b, by omega⟩ with hb'
  have hab' : a' ≠ b' := fun e => hba (Fin.ext (by
    have := congrArg Fin.val e
    simpa [ha', hb'] using this.symm))
  have h3 : 0 + 3 ≤ n := by omega
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hmem : SpecialLinearGroup.transvection hab' (1 : ZMod 2) ∈
      perfectCore (flagStabilizer n (ZMod 2) {3}) := by
    rw [transvection_eq_liftT h3 a.isLt b.isLt hab']
    exact Ln2.liftT_mem_perfectCore h3 le_rfl hno _
  obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
  set c : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single b' 1)) with hc
  set ca : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single a' 1)) with hca
  have hconj : (y : G) * (Φ c : G) * y⁻¹ = (Φ c : G) * (Φ ca : G) := by
    have h1 := hD.equiv ⟨y, liftCore_le α _ hyY⟩ c
    rw [hye] at h1
    rw [h1, ← Subgroup.coe_mul, ← map_mul]
    congr 2
    rw [hc, vecAct_mulSingle, hca, ← Pi.mulSingle_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    have := SpecialLinearGroup.transvection_smul_single_snd hab' (1 : ZMod 2)
    rw [Matrix.SpecialLinearGroup.smul_def, one_smul] at this
    exact this
  have hcomm : ⁅y, (Φ c : G)⁆ = (Φ ca : G) := by
    rw [commutatorElement_def, hconj]
    have hab := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
    have := congrArg Subtype.val (hab.1.is_comm.comm (Φ c) (Φ ca))
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group
  rw [← hcomm, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hyY (Φ c).2

theorem W₃_le_Q (hD : Data G T M L D n k α Φ) :
    W₃ Φ ≤ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})) :=
  hD.W₃_le_commutator.trans (Subgroup.commutator_mono (hD.vPlus_le_pCoreOf (liftCore_le α _))
    le_rfl)

theorem Q_le_pCoreOf (hD : Data G T M L D n k α Φ) :
    c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3})) ≤
      pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {3})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := liftCore α (flagStabilizer n (ZMod 2) {3}) with hY
  have hYN : Y ⊔ T ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (hD.le_normalizer_Y {3})
  have hQY : c134Q (Y ⊔ T) Y ≤ Y :=
    Ch3Sec3.commutator_le_right_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hYN)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQY
    (le_sup_left.trans (MSY.le_normalizer_c134Q (hD.le_normalizer_Y {3})))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le MSY.c134Q_le_pCoreOf)

theorem entry_of_ker (hD : Data G T M L D n k α Φ)
    {ψ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψe : ∀ y : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blkAt 0 3 (by have := hD.n4; omega)
          ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)))
    {x : ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))} (hx : ψ x = 1) {i j : Fin n}
    (hij : ¬ ((i : ℕ) < 3 ∧ 3 ≤ (j : ℕ))) :
    ((α ⟨x, liftCore_le α _ x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) i j = if i = j then 1 else 0 := by
  have hn := hD.n4
  have hP := mem_perfectCore_of_mem_liftCore hD.surj x.2
  by_cases hi : (i : ℕ) < 3
  · have hj : (j : ℕ) < 3 := by omega
    have h1 := congrFun (congrFun (hψe x) ⟨i, hi⟩) ⟨j, hj⟩
    rw [hx, Matrix.SpecialLinearGroup.coe_one, blkAt_apply] at h1
    have hi' : (⟨0 + (i : ℕ), by omega⟩ : Fin n) = i := Fin.ext (by simp)
    have hj' : (⟨0 + (j : ℕ), by omega⟩ : Fin n) = j := Fin.ext (by simp)
    simp only [hi', hj'] at h1
    rw [← h1, Matrix.one_apply]
    by_cases hij' : i = j
    · subst hij'
      simp
    · have : (⟨i, hi⟩ : Fin 3) ≠ ⟨j, hj⟩ := fun e => hij' (Fin.ext (by
        have := congrArg Fin.val e
        simpa using this))
      simp [this, hij']
  · by_cases hj : (j : ℕ) < 3
    · rw [bl_eq_zero (perfectCore_le _ hP) (by omega) hj]
      have : i ≠ j := fun e => by subst e; omega
      simp [this]
    · exact br_eq_ite (Nat.card_zmod 2) hn hD.n5 hP (by omega) (by omega)

theorem mulVec_eq_of_ker (hD : Data G T M L D n k α Φ)
    {ψ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψe : ∀ y : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blkAt 0 3 (by have := hD.n4; omega)
          ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)))
    {x : ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))} (hx : ψ x = 1) {v : Fin n → ZMod 2}
    (hv : ∀ j : Fin n, 3 ≤ (j : ℕ) → v j = 0) :
    ((α ⟨x, liftCore_le α _ x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v := by
  funext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single r]
  · rw [hD.entry_of_ker hψe hx (by omega), ite_eq_left rfl, one_mul]
  · intro t _ htr
    by_cases ht : 3 ≤ (t : ℕ)
    · rw [hv t ht, mul_zero]
    · rw [hD.entry_of_ker hψe hx (by omega), ite_eq_right (Ne.symm htr), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem W₃_le_centerOf (hD : Data G T M L D n k α Φ) :
    W₃ Φ ≤ centerOf (c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) := by
  obtain ⟨ψ, -, hψk, hψe⟩ := hD.exists_levi_three
  refine le_inf hD.W₃_le_Q ?_
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqP := hD.Q_le_pCoreOf hq
  have hqY : q ∈ liftCore α (flagStabilizer n (ZMod 2) {3}) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hqP
  have hψq : ψ ⟨q, hqY⟩ = 1 := by
    have : (⟨q, hqY⟩ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))) ∈ ψ.ker := by
      rw [hψk]
      exact (Lem3328.mem_pCore_iff _).mpr hqP
    exact this
  have h1 : (q : G) * (Φ (ext3 n k x) : G) * q⁻¹ = (Φ (ext3 n k x) : G) := by
    refine (hD.comm_iff ⟨q, liftCore_le α _ hqY⟩ (ext3 n k x)).mpr fun i => ?_
    exact hD.mulVec_eq_of_ker hψe hψq fun j hj => ext3_apply_of_le n k x i hj
  show q * (Φ (ext3 n k x) : G) = (Φ (ext3 n k x) : G) * q
  calc q * (Φ (ext3 n k x) : G) = q * (Φ (ext3 n k x) : G) * q⁻¹ * q := by group
    _ = (Φ (ext3 n k x) : G) * q := by rw [h1]

theorem exists_rad (hD : Data G T M L D n k α Φ)
    {ψ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψk : ψ.ker = CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {3})))
    (hψe : ∀ y : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blkAt 0 3 (by have := hD.n4; omega)
          ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)))
    {c b : Fin n} (hc : (c : ℕ) < 3) (hb : 3 ≤ (b : ℕ)) (hcb : c ≠ b) :
    ∃ (x : G) (hx : x ∈ liftCore α (flagStabilizer n (ZMod 2) {3})),
      x ∈ pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) ∧
      α ⟨x, liftCore_le α _ hx⟩ = SpecialLinearGroup.transvection hcb (1 : ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxe⟩ := exists_mem_liftCore hD.surj
    (transvection_mem_perfectCore_three (K := ZMod 2) hc hb hcb)
  refine ⟨x, hx, ?_, hxe⟩
  have hψx : ψ ⟨x, hx⟩ = 1 := by
    apply Subtype.ext
    rw [hψe, hxe, Matrix.SpecialLinearGroup.coe_one, SpecialLinearGroup.transvection_coe]
    ext i j
    rw [blkAt_apply, Matrix.add_apply, Matrix.single_apply]
    have : ¬ (c = (⟨0 + (i : ℕ), by have := i.isLt; have := hD.n4; omega⟩ : Fin n) ∧
        b = ⟨0 + (j : ℕ), by have := j.isLt; have := hD.n4; omega⟩) := by
      rintro ⟨-, e⟩
      have := congrArg Fin.val e
      simp only at this
      have := j.isLt
      omega
    rw [ite_eq_right this, add_zero, Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.mk.injEq, Nat.zero_add, Fin.val_inj]
  have hxP : x ∈ pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {3})) := by
    have : (⟨x, hx⟩ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))) ∈ ψ.ker := hψx
    rw [hψk] at this
    exact (Lem3328.mem_pCore_iff _).mp this
  exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
    le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (hD.le_normalizer_Y {3}))) hxP

theorem card_inf_mul (hD : Data G T M L D n k α Φ) :
    Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3})) ⊓ pCoreOf 2 L) * 8 ^ (n - 3) =
      Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3}))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hD.n4
  have hn5 := hD.n5
  obtain ⟨ψ, -, hψk, hψe⟩ := hD.exists_levi_three
  have hQL : ∀ q ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})),
      q ∈ liftCore α (flagStabilizer n (ZMod 2) {3}) := fun q hq =>
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hD.Q_le_pCoreOf hq)
  have hψq : ∀ (q : G) (hq : q ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))), ψ ⟨q, hQL q hq⟩ = 1 := by
    intro q hq
    have : (⟨q, hQL q hq⟩ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))) ∈ ψ.ker := by
      rw [hψk]
      exact (Lem3328.mem_pCore_iff _).mpr (hD.Q_le_pCoreOf hq)
    exact this
  let A : ∀ q : G, q ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})) → Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun q hq => ((α ⟨q, liftCore_le α _ (hQL q hq)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))
  have hA : ∀ (q : G) (hq) (i j : Fin n), ¬ ((i : ℕ) < 3 ∧ 3 ≤ (j : ℕ)) →
      A q hq i j = if i = j then 1 else 0 := fun q hq i j hij =>
    hD.entry_of_ker hψe (hψq q hq) hij
  let μ : ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) →*
      Multiplicative (Fin 3 → Fin (n - 3) → ZMod 2) :=
    { toFun := fun q => Multiplicative.ofAdd fun a b =>
        A q q.2 ⟨a, by omega⟩ ⟨3 + b, by omega⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext a b
        simp only [toAdd_ofAdd, toAdd_one, Pi.zero_apply, A, OneMemClass.coe_one]
        rw [show (⟨1, liftCore_le α _ (hQL 1 (Subgroup.one_mem _))⟩ : ↥L) = 1 from rfl, map_one,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
        rw [ite_eq_right]
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
      map_mul' := fun q q' => by
        apply Multiplicative.toAdd.injective
        funext a b
        simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
        show A (q * q' : G) (q * q').2 ⟨a, _⟩ ⟨3 + b, _⟩ = A q q.2 ⟨a, _⟩ ⟨3 + b, _⟩ +
          A q' q'.2 ⟨a, _⟩ ⟨3 + b, _⟩
        have hmul : A (q * q' : G) (q * q').2 = A q q.2 * A q' q'.2 := by
          simp only [A]
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
          rfl
        rw [hmul, Matrix.mul_apply]
        rw [Finset.sum_eq_add (⟨a, by omega⟩ : Fin n) ⟨3 + b, by omega⟩]
        · rw [hA q q.2 _ _ (by simp), ite_eq_left rfl, one_mul,
            hA q' q'.2 ⟨3 + b, by omega⟩ ⟨3 + b, by omega⟩ (by simp), ite_eq_left rfl, mul_one,
            add_comm]
        · intro h
          have := congrArg Fin.val h
          simp only at this
          omega
        · intro t _ ht
          by_cases ht3 : (t : ℕ) < 3
          · rw [hA q q.2 ⟨a, by omega⟩ t (by omega), ite_eq_right (Ne.symm ht.1), zero_mul]
          · rw [hA q' q'.2 t ⟨3 + b, by omega⟩ (by omega), ite_eq_right ht.2, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro h
          exact absurd (Finset.mem_univ _) h }
  have hker : μ.ker = (pCoreOf 2 L).subgroupOf
      (c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3}))) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have h1 : A q q.2 = 1 := by
        ext i j
        rw [Matrix.one_apply]
        by_cases hij : (i : ℕ) < 3 ∧ 3 ≤ (j : ℕ)
        · have := congrFun (congrFun (congrArg Multiplicative.toAdd hq) ⟨i, hij.1⟩)
            ⟨(j : ℕ) - 3, by omega⟩
          simp only [μ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one,
            Pi.zero_apply] at this
          have hj : (⟨3 + ((j : ℕ) - 3), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
          rw [hj] at this
          rw [this, ite_eq_right]
          intro e
          rw [e] at hij
          omega
        · exact hA q q.2 i j hij
      have h2 : α ⟨q, liftCore_le α _ (hQL q q.2)⟩ = 1 := Subtype.ext h1
      have h3 : (⟨(q : G), liftCore_le α _ (hQL q q.2)⟩ : ↥L) ∈ α.ker := h2
      rw [hD.ker] at h3
      exact (Lem3328.mem_pCore_iff _).mp h3
    · intro hq
      have h1 : (⟨(q : G), liftCore_le α _ (hQL q q.2)⟩ : ↥L) ∈ α.ker := by
        rw [hD.ker]
        exact (Lem3328.mem_pCore_iff _).mpr hq
      have h2 : A q q.2 = 1 := congrArg Subtype.val (show α _ = 1 from h1)
      apply Multiplicative.toAdd.injective
      funext a b
      simp only [μ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Pi.zero_apply]
      rw [h2, Matrix.one_apply, ite_eq_right]
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
  have hrange : μ.range = ⊤ := by
    refine eq_top_of_single_mem _ fun a b => ?_
    obtain ⟨c, hca⟩ : ∃ c : Fin 3, c ≠ a := ⟨a + 1, by
      intro h
      have := congrArg (fun x : Fin 3 => (x : ℕ)) h
      fin_cases a <;> simp_all⟩
    set a' : Fin n := ⟨a, by omega⟩ with ha'
    set c' : Fin n := ⟨c, by omega⟩ with hc'
    set b' : Fin n := ⟨3 + b, by omega⟩ with hb'
    have hac : a' ≠ c' := fun e => hca (Fin.ext (by
      have := congrArg Fin.val e
      simpa [ha', hc'] using this.symm))
    have hcb : c' ≠ b' := fun e => by
      have := congrArg Fin.val e
      simp [hc', hb'] at this
      omega
    have hab : a' ≠ b' := fun e => by
      have := congrArg Fin.val e
      simp [ha', hb'] at this
      omega
    obtain ⟨x, hxY, hxO, hxe⟩ := hD.exists_rad hψk hψe (c := c') (b := b') c.isLt
      (by simp [hb']) hcb
    have h3 : 0 + 3 ≤ n := by omega
    have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      omega
    have hmem : SpecialLinearGroup.transvection hac (1 : ZMod 2) ∈
        perfectCore (flagStabilizer n (ZMod 2) {3}) := by
      rw [transvection_eq_liftT h3 a.isLt c.isLt hac]
      exact Ln2.liftT_mem_perfectCore h3 le_rfl hno _
    obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
    have hq : ⁅y, x⁆ ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3})) := by
      rw [c134Q, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hyY hxO
    refine ⟨⟨_, hq⟩, ?_⟩
    have hαq : α ⟨⁅y, x⁆, liftCore_le α _ (hQL _ hq)⟩ =
        SpecialLinearGroup.transvection hab (1 : ZMod 2) := by
      have : (⟨⁅y, x⁆, liftCore_le α _ (hQL _ hq)⟩ : ↥L) =
          ⁅(⟨y, liftCore_le α _ hyY⟩ : ↥L), ⟨x, liftCore_le α _ hxY⟩⁆ := rfl
      rw [this, map_commutatorElement, hye, hxe,
        Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab, mul_one]
    apply Multiplicative.toAdd.injective
    funext a₀ b₀
    simp only [μ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, A]
    rw [hαq, SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, ite_eq_right (fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega), zero_add]
    by_cases ha₀ : a₀ = a
    · subst ha₀
      by_cases hb₀ : b₀ = b
      · subst hb₀
        simp [ha', hb']
      · have : ¬ ((⟨3 + b, by omega⟩ : Fin n) = ⟨3 + b₀, by omega⟩) := fun e => hb₀ (Fin.ext (by
          have := congrArg Fin.val e
          simp only at this
          omega))
        simp [ha', hb', this, Pi.single_eq_of_ne hb₀]
    · have : ¬ (a' = (⟨a₀, by omega⟩ : Fin n)) := fun e => ha₀ (Fin.ext (by
        have := congrArg Fin.val e
        simpa [ha'] using this.symm))
      simp [this, Pi.single_eq_of_ne ha₀]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup μ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv, hrange,
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fun, Nat.card_zmod, hker] at h1
  have h2 : Nat.card ↥((pCoreOf 2 L).subgroupOf
      (c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3})))) =
      Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
        (liftCore α (flagStabilizer n (ZMod 2) {3})) ⊓ pCoreOf 2 L) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h2] at h1
  rw [h1]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [mul_comm]
  congr 1
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

end Data

end CFSG.Quasithin.H13.L3318
