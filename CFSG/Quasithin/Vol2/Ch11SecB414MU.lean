module

public import CFSG.Quasithin.Vol2.Ch11SecB414MT

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix

variable {F : Type} [Field F]

theorem exists_SL2_map {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ C : SpecialLinearGroup (Fin 2) F, (C : Matrix (Fin 2) (Fin 2) F) *ᵥ v = w := by
  obtain ⟨A, hA⟩ := exists_SL2_e0 hv
  obtain ⟨B, hB⟩ := exists_SL2_e0 hw
  refine ⟨B * A⁻¹, ?_⟩
  rw [coe_mul2, ← Matrix.mulVec_mulVec, ← hA, inv_mulVec_mulVec, hB]

theorem eq_zero_of_forall_SL2 {u : Fin 2 → F}
    (h : ∀ C : SpecialLinearGroup (Fin 2) F, (C : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u) :
    u = 0 := by
  let C : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have h1 := congrFun (h (unip 1)) 0
  have h2 := congrFun (h C) 1
  simp [unip, C, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  funext i
  fin_cases i
  · exact h2
  · exact h1

variable {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F}
  (m : Model Γ V Z F k α)

@[expose] def Model.img (J : Subgroup G) : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | ∃ j : ↥V, (j : G) ∈ J ∧ Multiplicative.toAdd (m.β j) = M}
  zero_mem' := ⟨1, J.one_mem, by rw [map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, J.mul_mem ha hb, by rw [map_mul, toAdd_mul]⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, J.inv_mem ha, by rw [map_inv, toAdd_inv]⟩

theorem Model.toAdd_conj {γ : ↥Γ} {A : SpecialLinearGroup (Fin 3) F}
    (hA : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) = α γ) {v : G} (hv : v ∈ V)
    (hmem : (γ : G) * v * (γ : G)⁻¹ ∈ V) :
    Multiplicative.toAdd (m.β ⟨_, hmem⟩) =
      cnj (A : Matrix (Fin 3) (Fin 3) F) (Multiplicative.toAdd (m.β ⟨v, hv⟩)) := by
  rw [m.act γ ⟨v, hv⟩ ⟨_, hmem⟩ rfl _ hA, twAdj_toGL]

section Normal

variable (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ}
  (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
include m hLΓ hXΓ hL hX

theorem Model.twistedFixed_of (κ : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F))
    (hinj : ∀ M, twAdj k (dgHom ν) M = M → κ M = 0 → M = 0)
    (hex : ∃ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 ∧ twAdj k (dgHom ν) M = M ∧ M ≠ 0)
    (hequiv : ∀ (C : SpecialLinearGroup (Fin 2) F) (M : Matrix (Fin 3) (Fin 3) F),
      twAdj k (dgHom ν) M = M →
        κ (cnj (blkC (C : Matrix (Fin 2) (Fin 2) F)) M) = (C : Matrix (Fin 2) (Fin 2) F) *ᵥ κ M) :
    TwistedFixed V Z L X (α.ker.map Γ.subtype) := by
  have hblk : ∀ C : SpecialLinearGroup (Fin 2) F, ∃ l : G, ∃ hl : l ∈ L,
      IsCentMod X (α.ker.map Γ.subtype) l ∧ ∃ A : SpecialLinearGroup (Fin 3) F,
        (A : Matrix (Fin 3) (Fin 3) F) = blkC (C : Matrix (Fin 2) (Fin 2) F) ∧
        ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) = α ⟨l, hLΓ hl⟩ := by
    intro C
    let A : SpecialLinearGroup (Fin 3) F := ⟨blkC (C : Matrix (Fin 2) (Fin 2) F), by
      rw [det_blkC]; exact C.prop⟩
    obtain ⟨l, hl, hc, hlA⟩ := exists_isCentMod_of_block hLΓ hXΓ hL hX (A := A) (isBlock_blkC _)
    exact ⟨l, hl, hc, A, rfl, hlA.symm⟩
  have hfix : ∀ v (hv : v ∈ V), IsFixedMod X Z v ↔
      twAdj k (dgHom ν) (Multiplicative.toAdd (m.β ⟨v, hv⟩)) =
        Multiplicative.toAdd (m.β ⟨v, hv⟩) := fun v hv => m.isFixedMod_iff hXΓ hX hv
  have hmemV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (m.normV (hLΓ hl)) v).mp hv
  refine ⟨?_, fun J hZJ hJ hJl => ?_, fun v hv hvfix hcomm => ?_⟩
  · obtain ⟨M, htr, hM, hM0⟩ := hex
    obtain ⟨v, hv⟩ := m.onto M htr
    refine ⟨v, v.2, (hfix v v.2).mpr (by rw [hv]; exact hM), fun hz => hM0 ?_⟩
    rw [← hv]
    exact (m.toAdd_eq_zero v).mpr hz
  · by_cases hJZ : J ≤ Z
    · exact Or.inl (le_antisymm hJZ hZJ)
    right
    obtain ⟨j, hjJ, hjZ⟩ := Set.not_subset.mp hJZ
    obtain ⟨hjV, hjfix⟩ := hJ j hjJ
    have hjf := (hfix j hjV).mp hjfix
    have hκj : κ (Multiplicative.toAdd (m.β ⟨j, hjV⟩)) ≠ 0 := fun h0 =>
      hjZ ((m.toAdd_eq_zero ⟨j, hjV⟩).mp (hinj _ hjf h0))
    intro v hv hvfix
    have hvf := (hfix v hv).mp hvfix
    by_cases hκv : κ (Multiplicative.toAdd (m.β ⟨v, hv⟩)) = 0
    · exact hZJ ((m.toAdd_eq_zero ⟨v, hv⟩).mp (hinj _ hvf hκv))
    obtain ⟨C, hC⟩ := exists_SL2_map hκj hκv
    obtain ⟨l, hl, hc, A, hA, hlA⟩ := hblk C
    have hj'J : l * j * l⁻¹ ∈ J := hJl l hl hc j hjJ
    have hj'V := hmemV l hl j hjV
    have hj'f := (hfix _ hj'V).mp (hJ _ hj'J).2
    have e := m.toAdd_conj (γ := ⟨l, hLΓ hl⟩) hlA hjV hj'V
    rw [hA] at e
    have hd : Multiplicative.toAdd (m.β ⟨_, hj'V⟩) - Multiplicative.toAdd (m.β ⟨v, hv⟩) = 0 := by
      refine hinj _ ?_ ?_
      · rw [twAdj_sub, hj'f, hvf]
      · rw [map_sub, e, hequiv C _ hjf, hC, sub_self]
    have hmem : v * (l * j * l⁻¹)⁻¹ ∈ V := V.mul_mem hv (V.inv_mem hj'V)
    have hvj : v * (l * j * l⁻¹)⁻¹ ∈ Z := by
      refine (m.toAdd_eq_zero ⟨_, hmem⟩).mp ?_
      have e2 : (⟨_, hmem⟩ : ↥V) = ⟨v, hv⟩ * (⟨_, hj'V⟩ : ↥V)⁻¹ := rfl
      rw [e2, map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, ← neg_sub, hd, neg_zero]
    have := J.mul_mem (hZJ hvj) hj'J
    rwa [inv_mul_cancel_right] at this
  · have hvf := (hfix v hv).mp hvfix
    refine (m.toAdd_eq_zero ⟨v, hv⟩).mp (hinj _ hvf (eq_zero_of_forall_SL2 fun C => ?_))
    obtain ⟨l, hl, hc, A, hA, hlA⟩ := hblk C
    have h1 := (m.comm_mem_iff hlA hv).mp (hcomm l hl hc)
    rw [twAdj_toGL, hA] at h1
    rw [← hequiv C _ hvf, h1]

end Normal

theorem facE_zero (i j : Fin 3) :
    facE 0 i j % 3 ≠ 0 ↔ (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> decide

theorem facE_one (i j : Fin 3) : facE 1 i j % 3 ≠ 0 ↔ ¬ (i ≠ 0 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> decide

theorem facE_two (i j : Fin 3) : facE 2 i j % 3 ≠ 0 ↔ ¬ (i = 0 ∧ j ≠ 0) := by
  fin_cases i <;> fin_cases j <;> decide

section Fixed

variable [CharP F 2] (hF : Nat.card F = 4) (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ)
  (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ} (hν : ν ≠ 1)
  (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
include hF hLΓ hXΓ hL hν hX

omit m in
theorem Model.untwistedFixed (m : Model Γ V Z F 0 α) :
    UntwistedFixed V Z L X (α.ker.map Γ.subtype) := by
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  have hfix : ∀ v (hv : v ∈ V), IsFixedMod X Z v ↔
      ∀ i j, facE 0 i j % 3 ≠ 0 → Multiplicative.toAdd (m.β ⟨v, hv⟩) i j = 0 :=
    fun v hv => (m.isFixedMod_iff hXΓ hX hv).trans (fixed_iff hF hν 0 _)
  have hmemV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (m.normV (hLΓ hl)) v).mp hv
  refine ⟨fun J hZJ hJ hJl => ?_, ?_⟩
  · have hS : ∀ M ∈ m.img J, IsBlock M ∧ M.trace = 0 := by
      rintro _ ⟨j, hj, rfl⟩
      have hf := (hfix j j.2).mp (hJ j hj).2
      exact ⟨⟨hf 0 1 (by decide), hf 0 2 (by decide), hf 1 0 (by decide), hf 2 0 (by decide)⟩,
        m.sl j⟩
    have hcnj : ∀ A : Matrix (Fin 3) (Fin 3) F, IsBlock A → A.det = 1 →
        ∀ M ∈ m.img J, cnj A M ∈ m.img J := by
      rintro A hA hdet _ ⟨j, hj, rfl⟩
      obtain ⟨l, hl, hc, hlA⟩ := exists_isCentMod_of_block hLΓ hXΓ hL hX (A := ⟨A, hdet⟩) hA
      have hmem := hmemV l hl j j.2
      exact ⟨⟨_, hmem⟩, hJl l hl hc j hj, m.toAdd_conj hlA.symm j.2 hmem⟩
    obtain ⟨j₀, hj₀J, hj₀Z⟩ := Set.not_subset.mp (not_le_of_gt hZJ)
    have hj₀V := (hJ j₀ hj₀J).1
    have hM0 : Multiplicative.toAdd (m.β ⟨j₀, hj₀V⟩) ≠ 0 := fun h =>
      hj₀Z ((m.toAdd_eq_zero _).mp h)
    obtain ⟨x, hx0, hxS⟩ := exists_hatI ν.ne_zero hν1 (m.img J) hS hcnj ⟨⟨j₀, hj₀V⟩, hj₀J, rfl⟩ hM0
    obtain ⟨j, hjJ, hj⟩ := hxS
    refine ⟨j, hjJ, fun hz => hx0 ?_, fun l hl hc => ?_⟩
    · have h0 := (m.toAdd_eq_zero j).mpr hz
      rw [hj] at h0
      simpa using congrFun (congrFun h0 1) 1
    · obtain ⟨A, hA, hlA⟩ := exists_block_of_isCentMod hLΓ hL hν hX hl hc
      refine (m.comm_mem_iff hlA j.2).mpr ?_
      rw [twAdj_toGL]
      show cnj _ (Multiplicative.toAdd (m.β j)) = Multiplicative.toAdd (m.β j)
      rw [hj, show cnj (A : Matrix (Fin 3) (Fin 3) F) (x • hatI F) =
          x • cnj (A : Matrix (Fin 3) (Fin 3) F) (hatI F) by
        simp only [cnj, Matrix.mul_smul, Matrix.smul_mul], cnj_hatI hA A.prop]
  · let A : SpecialLinearGroup (Fin 3) F := ⟨aU F, det_aU⟩
    obtain ⟨l, hl, hc, hlA⟩ := exists_isCentMod_of_block hLΓ hXΓ hL hX (A := A) isBlock_aU
    obtain ⟨v, hv⟩ := m.onto !![0, 0, 0; 0, 0, 0; 0, 1, 0] (by simp [Matrix.trace_fin_three])
    refine ⟨l, hl, hc, v, v.2, (hfix v v.2).mpr fun i j hij => ?_, fun h => ?_⟩
    · show Multiplicative.toAdd (m.β v) i j = 0
      rw [hv]
      rw [facE_zero] at hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · have h2 := (m.comm_mem_iff hlA.symm v.2).mp h
      rw [twAdj_toGL] at h2
      have e := congrFun (congrFun h2 1) 1
      change cnj (aU F) (Multiplicative.toAdd (m.β v)) 1 1 = Multiplicative.toAdd (m.β v) 1 1 at e
      rw [hv] at e
      simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three] at e
      simp [adjugate_fin_three] at e

include m in
theorem Model.twistedFixed (hk3 : k < 3) (hk0 : k ≠ 0) :
    TwistedFixed V Z L X (α.ker.map Γ.subtype) := by
  have hC2 : ∀ C : SpecialLinearGroup (Fin 2) F,
      (C : Matrix (Fin 2) (Fin 2) F) 1 1 * (C : Matrix (Fin 2) (Fin 2) F) 0 0 -
        -(C : Matrix (Fin 2) (Fin 2) F) 1 0 * -(C : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 ^ 2 :=
    fun C => by
      have hC : (C : Matrix (Fin 2) (Fin 2) F).det = 1 := C.prop
      rw [Matrix.det_fin_two] at hC
      linear_combination hC
  interval_cases k
  · exact absurd rfl hk0
  · have hsh : ∀ M, twAdj 1 (dgHom ν) M = M ↔ ∀ i j : Fin 3, ¬ (i ≠ 0 ∧ j = 0) → M i j = 0 :=
      fun M => (fixed_iff hF hν 1 M).trans (by simp only [facE_one])
    refine m.twistedFixed_of hLΓ hXΓ hL hX kmHom (fun M hM h0 => ?_)
      ⟨!![0, 0, 0; 1, 0, 0; 0, 0, 0], by simp [Matrix.trace_fin_three], (hsh _).mpr ?_, ?_⟩
      (fun C M _ => ?_)
    · have hf := (hsh M).mp hM
      have h20 : M 2 0 = 0 := by simpa [kmHom_apply, km] using congrFun h0 0
      have h10 : M 1 0 = 0 := by simpa [kmHom_apply, km] using congrFun h0 1
      ext i j
      by_cases hij : i ≠ 0 ∧ j = 0
      · obtain ⟨hi, rfl⟩ := hij
        fin_cases i
        · exact absurd rfl hi
        · simpa using h10
        · simpa using h20
      · simpa using hf i j hij
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro h
      simpa using congrFun (congrFun h 1) 0
    · rw [kmHom_apply, kmHom_apply, km_cnj rfl rfl (hC2 C), rhoA_blkC]
  · have hsh : ∀ M, twAdj 2 (dgHom ν) M = M ↔ ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0 :=
      fun M => (fixed_iff hF hν 2 M).trans (by simp only [facE_two])
    refine m.twistedFixed_of hLΓ hXΓ hL hX kpHom (fun M hM h0 => ?_)
      ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], by simp [Matrix.trace_fin_three], (hsh _).mpr ?_, ?_⟩
      (fun C M hM => ?_)
    · have hf := (hsh M).mp hM
      have h01 : M 0 1 = 0 := by simpa [kpHom_apply, kp] using congrFun h0 0
      have h02 : M 0 2 = 0 := by simpa [kpHom_apply, kp] using congrFun h0 1
      ext i j
      by_cases hij : i = 0 ∧ j ≠ 0
      · obtain ⟨rfl, hj⟩ := hij
        fin_cases j
        · exact absurd rfl hj
        · simpa using h01
        · simpa using h02
      · simpa using hf i j hij
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro h
      simpa using congrFun (congrFun h 0) 1
    · rw [kpHom_apply, kpHom_apply, kp_cnj ((hsh M).mp hM), rhoA_blkC]

end Fixed

end CFSG.Quasithin.H13.Ch4.B414.M
