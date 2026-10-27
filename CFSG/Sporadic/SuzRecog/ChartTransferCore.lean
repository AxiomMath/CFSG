module

public import CFSG.Sporadic.SuzRecog.RigidL2
public import CFSG.Sporadic.SuzRecog.ChartTransferTests
public import Certificates.Certificate15111
public import CFSG.Sporadic.SuzRecog.Rigid
public import CFSG.LargeExtraspecial.S3Eight
public import CFSG.Sporadic.Co1Patterson.AmalgamKey
public import CFSG.Sporadic.Co1Patterson.SettingOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.RigidL2

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson
  CFSG.LargeExtraspecial CFSG.Open

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

theorem chartSwap_check : chartSwapOK = true :=
  Certificates.certificate15111

section TrivMod

variable {Γ : Type*} [Group Γ]

@[expose] def trivMod (K : Subgroup Γ) : Subgroup Γ where
  carrier := {g | (∀ k, k ∈ K ↔ g * k * g⁻¹ ∈ K) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ coreOf K}
  one_mem' := ⟨fun k => by simp, fun k _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨fun k => by rw [h₂, h₁]; group, fun k hk => ?_⟩
    have e : g₁ * g₂ * k * (g₁ * g₂)⁻¹ * k⁻¹ =
        g₁ * (g₂ * k * g₂⁻¹ * k⁻¹) * g₁⁻¹ * (g₁ * k * g₁⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem ((isoOn_conj g₁ h₁).map_mem_coreOf (h₂' k hk)) (h₁' k hk)
  inv_mem' := by
    rintro g ⟨h, h'⟩
    have hinv : ∀ k, k ∈ K ↔ g⁻¹ * k * g⁻¹⁻¹ ∈ K := fun k => by
      rw [h (g⁻¹ * k * g⁻¹⁻¹)]
      group
    refine ⟨hinv, fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K := by simpa using (hinv k).1 hk
    have := inv_mem (h' _ hk')
    rw [show (g * (g⁻¹ * k * g) * g⁻¹ * (g⁻¹ * k * g)⁻¹)⁻¹ = g⁻¹ * k * g⁻¹⁻¹ * k⁻¹ by group]
      at this
    exact this

theorem mem_trivMod {K : Subgroup Γ} {g : Γ} :
    g ∈ trivMod K ↔ (∀ k, k ∈ K ↔ g * k * g⁻¹ ∈ K) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ coreOf K :=
  Iff.rfl

theorem mem_coreOf_of_pgroup {K P : Subgroup Γ} (hP : IsPGroup 2 P)
    (hnorm : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) {x : Γ} (hxK : x ∈ K) (hxP : x ∈ P) :
    x ∈ coreOf K := by
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 K := by
    refine le_sSup ⟨⟨fun n hn k => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hn ⊢
      simpa using hnorm k.1 k.2 n.1 hn
    · exact hP.comap_of_injective K.subtype K.subtype_injective
  exact ⟨⟨x, hxK⟩, hle (by rw [mem_subgroupOf]; exact hxP), rfl⟩

structure QData (z : Γ) (Q : Subgroup Γ) : Prop where
  le : Q ≤ C[z]
  conj_mem : ∀ c ∈ C[z], ∀ q ∈ Q, c * q * c⁻¹ ∈ Q
  isPGroup : IsPGroup 2 Q
  comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z

theorem QData.le_trivMod {z : Γ} {Q : Subgroup Γ} (hQ : QData z Q) {v : Γ} (hv : v ∈ Q) :
    Q ≤ trivMod (C[z] ⊓ C[v]) := by
  intro x hx
  have hxz : x * z * x⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (hQ.le hx), mul_inv_cancel_right]
  have hvz : z * v = v * z := (mem_centralizer_singleton_iff.1 (hQ.le hv)).symm
  have hK : ∀ k, k ∈ C[z] ⊓ C[v] ↔ x * k * x⁻¹ ∈ C[z] ⊓ C[v] := by
    rcases hQ.comm x hx v hv with h | h
    · have hxv : x * v * x⁻¹ = v := by
        calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
          _ = v := by rw [h, one_mul]
      exact conj_mem_inf_iff_of hxz hxv (fun _ => Iff.rfl)
    · have hxv : x * v * x⁻¹ = z * v := by
        calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
          _ = z * v := by rw [h]
      exact conj_mem_inf_iff_of hxz hxv (mem_inf_mul_right_iff hvz)
  refine ⟨hK, fun k hk => ?_⟩
  refine mem_coreOf_of_pgroup hQ.isPGroup (fun c hc y hy => hQ.conj_mem c (mem_inf.1 hc).1 y hy)
    ?_ ?_
  · exact mul_mem ((hK k).1 hk) (inv_mem hk)
  · have := mul_mem hx (hQ.conj_mem k (mem_inf.1 hk).1 x⁻¹ (inv_mem hx))
    simpa [mul_assoc] using this

theorem QData.conj {z : Γ} {Q : Subgroup Γ} (hQ : QData z Q) (c : Γ) :
    QData (c * z * c⁻¹) (Q.map (MulAut.conj c).toMonoidHom) where
  le := by
    rintro _ ⟨q, hq, rfl⟩
    exact (mem_cent_conj_iff c q z).1 (hQ.le hq)
  conj_mem := by
    rintro d hd _ ⟨q, hq, rfl⟩
    have hd' : c⁻¹ * d * c ∈ C[z] := by
      have h := (mem_cent_conj_iff c⁻¹ d (c * z * c⁻¹)).1 hd
      rwa [show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group, inv_inv] at h
    refine ⟨(c⁻¹ * d * c) * q * (c⁻¹ * d * c)⁻¹, hQ.conj_mem _ hd' q hq, ?_⟩
    change c * ((c⁻¹ * d * c) * q * (c⁻¹ * d * c)⁻¹) * c⁻¹ = d * (c * q * c⁻¹) * d⁻¹
    group
  isPGroup := hQ.isPGroup.map _
  comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change c * x * c⁻¹ * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ = 1 ∨
      c * x * c⁻¹ * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ = c * z * c⁻¹
    have e : c * x * c⁻¹ * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ =
        c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by group
    rw [e]
    rcases hQ.comm x hx y hy with h | h
    · left
      rw [h]
      group
    · right
      rw [h]

theorem qData_setting {G : Type*} [Group G] (S : Setting G) : QData S.z S.QG where
  le := S.QG_le_M
  conj_mem := fun _ hc _ hq => S.conj_mem_QG hc hq
  isPGroup := S.isPGroup_QG
  comm := fun x hx y hy => by
    have h1 : x * y ∈ S.QG := mul_mem hx hy
    have h2 : x * y * x⁻¹ ∈ S.QG := mul_mem h1 (inv_mem hx)
    rw [← S.cl_eq_zero_iff (mul_mem h2 (inv_mem hy)), S.cl_mul h2 (inv_mem hy), S.cl_mul h1
      (inv_mem hx), S.cl_mul hx hy, S.cl_inv hx, S.cl_inv hy,
      show S.cl x + S.cl y + S.cl x + S.cl y = (S.cl x + S.cl x) + (S.cl y + S.cl y) by abel,
      ZModModule.add_self, ZModModule.add_self, add_zero]

end TrivMod

theorem exists_setting_swap {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 3)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) {W : G} (hWQ : W ∈ S.QG)
    (hW2 : orderOf W = 2) (hWz : W ≠ S.z) :
    ∃ g : G, g * S.z * g⁻¹ = W ∧ g * W * g⁻¹ = S.z ∧
      ∀ k ∈ C[S.z] ⊓ C[W], g * k * g⁻¹ * k⁻¹ ∈ coreOf (C[S.z] ⊓ C[W]) := by
  have h5 : 5 ≤ Module.finrank (ZMod 2) S.Qt := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
    norm_num
  obtain ⟨g, hg, hne⟩ := hNWC
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (isConj_of_mem_QG_of_omega S h5 hΩ hg hne hWQ hW2)
  obtain ⟨u, hu, hu1, hu2⟩ := S.exists_swap hg₀ hWQ hWz
  have hT : QData W (S.Qa g₀) := by
    have h := (qData_setting S).conj g₀
    rw [hg₀, ← Setting.Qa_eq_map] at h
    exact h
  have hzQ : S.z ∈ S.Qa g₀ := S.z_mem_Qa_of_mem_QG hg₀ hWQ hWz
  have hle : S.QG ⊔ S.Qa g₀ ≤ trivMod (C[S.z] ⊓ C[W]) := by
    refine sup_le ((qData_setting S).le_trivMod hWQ) ?_
    have h := hT.le_trivMod hzQ
    rwa [inf_comm] at h
  exact ⟨u, hu1, hu2, (mem_trivMod.1 (hle hu)).2⟩

@[expose] noncomputable def bWord (w : List ℕ) : Equiv.Perm (Fin 1782) :=
  (w.map fun k => if k = 0 then suzB0 else suzB1).prod

theorem bWord_mem_suzM : ∀ w : List ℕ, bWord w ∈ suzM
  | [] => one_mem _
  | k :: w => by
    rw [bWord, List.map_cons, List.prod_cons]
    refine mul_mem ?_ (bWord_mem_suzM w)
    split_ifs
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem rep_bWord :
    ∀ w : List ℕ, Rep 1782 (bWordTab w) (bWord w)
  | [] => by
    have e1 : bWordTab [] = idA 1782 := by rw [bWordTab, List.foldr_nil]
    have e2 : bWord [] = 1 := by rw [bWord, List.map_nil, List.prod_nil]
    rw [e1, e2]
    exact rep_idA
  | k :: w => by
    have h := rep_bWord w
    have hk : Rep 1782 (bLetterTab k) (if k = 0 then suzB0 else suzB1) := by
      unfold bLetterTab
      split_ifs with h1 h2 h2
      · exact rep_b0
      · exact absurd (beq_iff_eq.1 h1) h2
      · exact absurd (beq_iff_eq.2 h2) h1
      · exact rep_b1
    have e : bWord (k :: w) = (if k = 0 then suzB0 else suzB1) * bWord w := by
      rw [bWord, List.map_cons, List.prod_cons, ← bWord]
    have e3 : bWordTab (k :: w) = compA 1782 (bLetterTab k) (bWordTab w) := by
      rw [bWordTab, List.foldr_cons, ← bWordTab]
    rw [e, e3]
    exact rep_compA hk h

section Q1


@[expose] noncomputable def q1M : Subgroup ↥suzM := coord_qVec.Q.comap suzM.subtype

theorem mem_q1M {x : ↥suzM} : x ∈ q1M ↔ (x : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := Iff.rfl

theorem qData_q1M : QData t1' q1M where
  le := fun x hx => mem_centralizer_singleton_iff.2 (comm_t1' (Q_le_invE (mem_q1M.1 hx)))
  conj_mem := fun c hc q hq => by
    have hcE : (c : Equiv.Perm (Fin 1782)) ∈ invE 1 :=
      mem_invE_iff.2 (mem_centralizer_singleton_iff.1 hc)
    have hN := (mem_inf.1 (invE_le hcE)).1
    show (c : Equiv.Perm (Fin 1782)) * q * (c : Equiv.Perm (Fin 1782))⁻¹ ∈ coord_qVec.Q
    exact (mem_normalizer_iff.1 hN _).1 (mem_q1M.1 hq)
  isPGroup := coord_qVec.isPGroup_Q.comap_of_injective suzM.subtype suzM.subtype_injective
  comm := fun x hx y hy => by
    have h := coord_qVec.commutator_mem_zpowers (mem_q1M.1 hx) (mem_q1M.1 hy)
    rw [commutatorElement_def, mem_zpowers_t1_iff] at h
    rcases h with h | h
    · left
      apply Subtype.ext
      simpa using h
    · right
      apply Subtype.ext
      rw [coe_t1']
      simpa using h

theorem wq_mem_q1M : wq ∈ q1M := mem_q1M.2 w0P_mem

theorem wq_mem_cent : wq ∈ C[t1'] := qData_q1M.le wq_mem_q1M

@[expose] noncomputable def x2M : ↥suzM := ⟨qVec 2, invE_le_suzM (qVec_mem_invE 2)⟩

theorem x2M_mem : x2M ∈ q1M := mem_q1M.2 (coord_qVec.q_mem (v := 2) (by norm_num))

theorem x2M_conj_wq : x2M * wq * x2M⁻¹ = t1' * wq := by
  apply Subtype.ext
  have h := coord_qVec.commutator_eq (v := 2) (w := 1) (by norm_num) (by norm_num) 0 0
  rw [show (gammaBit 2 1 + gammaBit 1 2) % 2 = 1 by decide, pow_one] at h
  simp only [pow_zero, mul_one] at h
  change qVec 2 * qVec 1 * (qVec 2)⁻¹ = suzInv 1 * qVec 1
  rw [← h]
  group

end Q1

section Model


@[expose] noncomputable def g0M : ↥suzM := ⟨bWord chartWord, bWord_mem_suzM _⟩

theorem chartSwap_parts :
    bWord chartWord * suzInv 1 = qVec 1 * bWord chartWord ∧
      suzInv 1 * bWord chartWord = bWord chartWord * qVec 1 := by
  have h := chartSwap_check
  rw [chartSwapOK, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  have hg := rep_bWord chartWord
  refine ⟨eq_of_eqA (rep_compA hg rep_tTab) (rep_compA rep_w0P hg) h1,
    eq_of_eqA (rep_compA rep_tTab hg) (rep_compA hg rep_w0P) h2⟩

theorem g0M_conj_t1 : g0M * t1' * g0M⁻¹ = wq := by
  apply Subtype.ext
  change bWord chartWord * suzInv 1 * (bWord chartWord)⁻¹ = qVec 1
  rw [chartSwap_parts.1, mul_inv_cancel_right]

theorem g0M_conj_wq : g0M * wq * g0M⁻¹ = t1' := by
  apply Subtype.ext
  change bWord chartWord * qVec 1 * (bWord chartWord)⁻¹ = suzInv 1
  rw [← chartSwap_parts.2, mul_inv_cancel_right]

theorem exists_model_swap :
    ∃ s : ↥suzM, s * t1' * s⁻¹ = wq ∧ s * wq * s⁻¹ = t1' ∧
      ∀ k ∈ C[t1'] ⊓ C[wq], s⁻¹ * k * s * k⁻¹ ∈ coreOf (C[t1'] ⊓ C[wq]) := by
  have hQw : QData wq (q1M.map (MulAut.conj g0M).toMonoidHom) := by
    have h := qData_q1M.conj g0M
    rwa [g0M_conj_t1] at h
  set y := g0M * x2M * g0M⁻¹ with hy
  have hyQ : y ∈ q1M.map (MulAut.conj g0M).toMonoidHom := ⟨x2M, x2M_mem, rfl⟩
  have ht1Q : t1' ∈ q1M.map (MulAut.conj g0M).toMonoidHom := by
    refine ⟨wq, wq_mem_q1M, ?_⟩
    change g0M * wq * g0M⁻¹ = t1'
    exact g0M_conj_wq
  have hx := qData_q1M.le_trivMod wq_mem_q1M x2M_mem
  have hy' : y ∈ trivMod (C[t1'] ⊓ C[wq]) := by
    have h := hQw.le_trivMod ht1Q hyQ
    rwa [inf_comm] at h
  have hxt : x2M * t1' * x2M⁻¹ = t1' := by
    rw [mem_centralizer_singleton_iff.1 (qData_q1M.le x2M_mem), mul_inv_cancel_right]
  have hxw := x2M_conj_wq
  have hyw : y * wq * y⁻¹ = wq := by
    rw [mem_centralizer_singleton_iff.1 (hQw.le hyQ), mul_inv_cancel_right]
  have hyt : y * t1' * y⁻¹ = wq * t1' := by
    have e : y * t1' * y⁻¹ = g0M * (x2M * (g0M⁻¹ * t1' * g0M) * x2M⁻¹) * g0M⁻¹ := by
      rw [hy]
      group
    have e2 : g0M⁻¹ * t1' * g0M = wq := by
      rw [← g0M_conj_wq]
      group
    rw [e, e2, hxw, show g0M * (t1' * wq) * g0M⁻¹ = (g0M * t1' * g0M⁻¹) * (g0M * wq * g0M⁻¹) by
      group, g0M_conj_t1, g0M_conj_wq]
  have hwt : wq * t1' = t1' * wq := (mem_centralizer_singleton_iff.1 wq_mem_cent)
  have ht2 : t1' * t1' = 1 := Subtype.ext (suzInv_sq (by norm_num))
  refine ⟨x2M * y * x2M, ?_, ?_, fun k hk => ?_⟩
  · calc x2M * y * x2M * t1' * (x2M * y * x2M)⁻¹
        = x2M * (y * (x2M * t1' * x2M⁻¹) * y⁻¹) * x2M⁻¹ := by group
      _ = x2M * (wq * t1') * x2M⁻¹ := by rw [hxt, hyt]
      _ = (x2M * wq * x2M⁻¹) * (x2M * t1' * x2M⁻¹) := by group
      _ = t1' * wq * t1' := by rw [hxw, hxt]
      _ = wq := by rw [← hwt, mul_assoc, ht2, mul_one]
  · calc x2M * y * x2M * wq * (x2M * y * x2M)⁻¹
        = x2M * (y * (x2M * wq * x2M⁻¹) * y⁻¹) * x2M⁻¹ := by group
      _ = x2M * ((y * t1' * y⁻¹) * (y * wq * y⁻¹)) * x2M⁻¹ := by rw [hxw]; group
      _ = x2M * (wq * t1' * wq) * x2M⁻¹ := by rw [hyt, hyw]
      _ = x2M * t1' * x2M⁻¹ := by
        have hw2 : wq * wq = 1 := Subtype.ext (by
          change qVec 1 * qVec 1 = 1
          have h := coord_qVec.mul_self_eq (v := 1) (by norm_num) 0
          rwa [pow_zero, mul_one, show qMinusBit 1 = 0 by decide, pow_zero] at h)
        rw [hwt, mul_assoc t1' wq wq, hw2, mul_one]
      _ = t1' := hxt
  · have hs : x2M * y * x2M ∈ trivMod (C[t1'] ⊓ C[wq]) := mul_mem (mul_mem hx hy') hx
    have h := (mem_trivMod.1 (inv_mem hs)).2 k hk
    rwa [inv_inv] at h

@[expose] noncomputable def centT1Equiv : ↥(C[t1'] : Subgroup ↥suzM) ≃* ↥(invE 1) where
  toFun x := ⟨(x : ↥suzM), mem_invE_iff.2 (mem_centralizer_singleton_iff.1 x.2)⟩
  invFun y := ⟨⟨y, invE_le_suzM y.2⟩, mem_centralizer_singleton_iff.2 (comm_t1' y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem chartTransfer_wq {G : Type} [Group G] [Finite G]
    (S : Setting G) (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* invE 1) :
    ∃ ζ : centM (qVec 1) →* G, ∀ x (hx : x ∈ invE 1) (hxw : x ∈ centM (qVec 1)),
      ζ ⟨x, hxw⟩ = (σ.symm ⟨x, hx⟩ : G) := by
  set e : ↥(C[t1'] : Subgroup ↥suzM) ≃* ↥(C[S.z] : Subgroup G) := centT1Equiv.trans σ.symm
  set A : ↥suzM → G := extFun e with hAdef
  have hA : IsoOn A C[t1'] C[S.z] := isoOn_extFun e
  have hAval : ∀ x (hx : x ∈ C[t1']), A x = (σ.symm (centT1Equiv ⟨x, hx⟩) : G) :=
    fun x hx => extFun_of_mem e hx
  have htC : t1' ∈ C[t1'] := mem_centralizer_singleton_iff.2 rfl
  have hzc : t1C ∈ center ↥(invE 1) := mem_center_iff.2 fun g => (t1C_comm g).symm
  have hz1 : t1C ≠ 1 := fun h => suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)
  have hσz : σ.symm t1C = S.zM := by
    rw [← map_zM_eq S σ hzc hz1, MulEquiv.symm_apply_apply]
  have hAa : A t1' = S.z := by
    rw [hAval _ htC]
    have e1 : centT1Equiv ⟨t1', htC⟩ = t1C := rfl
    rw [e1, hσz]
    rfl
  have hW : A wq = (σ.symm w0C : G) := by
    rw [hAval _ wq_mem_cent]
    rfl
  have hWQ : A wq ∈ S.QG := by
    let q1C : Subgroup ↥(invE 1) := coord_qVec.Q.comap (invE 1).subtype
    have hN : q1C.Normal := ⟨fun n hn c => by
      have hN := (mem_inf.1 (invE_le c.2)).1
      exact (mem_normalizer_iff.1 hN _).1 hn⟩
    have hP : IsPGroup 2 q1C :=
      coord_qVec.isPGroup_Q.comap_of_injective (invE 1).subtype (invE 1).subtype_injective
    have hle := S.le_of_normal (q1C.map σ.symm.toMonoidHom) (hN.map _ σ.symm.surjective)
      (hP.map _)
    rw [hW]
    exact ⟨σ.symm w0C, hle ⟨w0C, w0P_mem, rfl⟩, rfl⟩
  have hw01 : w0C ≠ 1 := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 0 (by norm_num) (by
      simp only [pow_zero, mul_one, coord_qVec.q_zero]
      exact congrArg Subtype.val h)
    omega
  have hw0t : w0C ≠ t1C := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 1 (by norm_num) (by
      simp only [pow_zero, mul_one, pow_one, coord_qVec.q_zero, one_mul]
      exact congrArg Subtype.val h)
    omega
  have hW2 : orderOf (A wq) = 2 := by
    rw [hW, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact w0C_mul_self) hw01
  have hWz : A wq ≠ S.z := by
    rw [hW]
    intro h
    apply hw0t
    apply σ.symm.injective
    rw [hσz]
    exact Subtype.ext h
  obtain ⟨s, hs1, hs2, hsO⟩ := exists_model_swap
  obtain ⟨g, hg1, hg2, hgO⟩ := exists_setting_swap S hw hΩ hNWC hWQ hW2 hWz
  obtain ⟨Z, hZ, hagree, -⟩ :=
    exists_isoOn_agree hA hAa wq_mem_cent rfl hs1 hs2 hg1 hg2 hsO hgO autInnerModAt_t1_wq
  have hmem : ∀ x : centM (qVec 1), (⟨x, x.2.2⟩ : ↥suzM) ∈ C[wq] := fun x =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1))
  let ζ : centM (qVec 1) →* G :=
    { toFun := fun x => Z ⟨x, x.2.2⟩
      map_one' := hZ.map_one
      map_mul' := fun x y => hZ.map_mul _ (hmem x) _ (hmem y) }
  refine ⟨ζ, fun x hx hxw => ?_⟩
  have hxt : (⟨x, hxw.2⟩ : ↥suzM) ∈ C[t1'] := mem_centralizer_singleton_iff.2 (comm_t1' hx)
  change Z ⟨x, hxw.2⟩ = _
  rw [hagree _ (mem_inf.2 ⟨hxt, hmem ⟨x, hxw⟩⟩), hAval _ hxt]
  rfl

theorem chartTransfer_conj {G : Type} [Group G] [Finite G]
    (S : Setting G) (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* invE 1)
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ invE 1) :
    ∃ ζ : centM (c * qVec 1 * c⁻¹) →* G, ∀ x (hx : x ∈ invE 1)
      (hxw : x ∈ centM (c * qVec 1 * c⁻¹)), ζ ⟨x, hxw⟩ = (σ.symm ⟨x, hx⟩ : G) := by
  obtain ⟨ζ, hζ⟩ := chartTransfer_wq S hw hΩ hNWC σ
  have hcM : c ∈ suzM := invE_le_suzM hc
  have hmem : ∀ x : centM (c * qVec 1 * c⁻¹), c⁻¹ * (x : Equiv.Perm (Fin 1782)) * c ∈
      centM (qVec 1) := fun x => by
    refine mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hcM) x.2.2) hcM⟩
    have h := (mem_cent_conj_iff c⁻¹ _ (c * qVec 1 * c⁻¹)).1 x.2.1
    rwa [show c⁻¹ * (c * qVec 1 * c⁻¹) * c⁻¹⁻¹ = qVec 1 by group, inv_inv] at h
  let φ : centM (c * qVec 1 * c⁻¹) →* centM (qVec 1) :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change c⁻¹ * ((x : Equiv.Perm (Fin 1782)) * y) * c =
          c⁻¹ * (x : Equiv.Perm (Fin 1782)) * c * (c⁻¹ * y * c)
        group) }
  refine ⟨(MulAut.conj (σ.symm ⟨c, hc⟩ : G)).toMonoidHom.comp (ζ.comp φ), fun x hx hxw => ?_⟩
  have hxE : c⁻¹ * x * c ∈ invE 1 := mul_mem (mul_mem (inv_mem hc) hx) hc
  have h1 := hζ _ hxE (hmem ⟨x, hxw⟩)
  have h2 : (⟨c⁻¹ * x * c, hxE⟩ : ↥(invE 1)) = (⟨c, hc⟩ : ↥(invE 1))⁻¹ * ⟨x, hx⟩ * ⟨c, hc⟩ :=
    rfl
  rw [h2, map_mul, map_mul, map_inv] at h1
  change (σ.symm ⟨c, hc⟩ : G) * ζ ⟨_, hmem ⟨x, hxw⟩⟩ * (σ.symm ⟨c, hc⟩ : G)⁻¹ = _
  rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Model

end CFSG.Sporadic.SuzRecog.RigidL2
