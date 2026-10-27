module

public import CFSG.Sporadic.Co1Patterson.AmalgamRigidCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Monster.GMS CFSG.Open
  CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1Patterson.TwistNative
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (bNat ind)

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Generic

variable {G H : Type*} [Group G] [Group H]

theorem eq_on_of_eq_on_two {K : Subgroup G} {q p k₀ y₀ : G} {F F' : G → H}
    (hF : ∀ x ∈ K, ∀ y ∈ K, F (x * y) = F x * F y)
    (hF' : ∀ x ∈ K, ∀ y ∈ K, F' (x * y) = F' x * F' y)
    (hqq : q * q = 1) (hpp : p * p = 1) (hqp : q * p = p * q)
    (hW : ∀ x ∈ K, x * q * x⁻¹ = q ∨ x * q * x⁻¹ = p ∨ x * q * x⁻¹ = q * p)
    (hk₀ : k₀ ∈ K) (hk₀q : k₀ * q * k₀⁻¹ = p) (hk₀p : k₀ * p * k₀⁻¹ = q * p)
    (hy₀ : y₀ ∈ K) (hy₀q : y₀ * q * y₀⁻¹ = q) (hy₀p : y₀ * p * y₀⁻¹ = q * p)
    (h1 : ∀ x ∈ K, x * q = q * x → F x = F' x) (h2 : ∀ x ∈ K, x * p = p * x → F x = F' x) :
    ∀ x ∈ K, F x = F' x := by
  have hcomm : ∀ x : G, x * q * x⁻¹ = q → x * q = q * x := fun x hx => by
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [hx]
  have hcommp : ∀ x : G, x * p * x⁻¹ = p → x * p = p * x := fun x hx => by
    calc x * p = x * p * x⁻¹ * x := by group
      _ = p * x := by rw [hx]
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  have hk₀qp : k₀ * (q * p) * k₀⁻¹ = q := by
    calc k₀ * (q * p) * k₀⁻¹ = (k₀ * q * k₀⁻¹) * (k₀ * p * k₀⁻¹) := by group
      _ = p * (q * p) := by rw [hk₀q, hk₀p]
      _ = q * (p * p) := by rw [← mul_assoc, ← hqp, mul_assoc]
      _ = q := by rw [hpp, mul_one]
  have hk₀i : k₀⁻¹ * q * k₀ = q * p := by
    calc k₀⁻¹ * q * k₀ = k₀⁻¹ * (k₀ * (q * p) * k₀⁻¹) * k₀ := by rw [hk₀qp]
      _ = q * p := by group
  have hz₂ : k₀ * y₀ * k₀⁻¹ * p = p * (k₀ * y₀ * k₀⁻¹) := by
    refine hcommp _ ?_
    calc k₀ * y₀ * k₀⁻¹ * p * (k₀ * y₀ * k₀⁻¹)⁻¹ = k₀ * (y₀ * (k₀⁻¹ * p * k₀) * y₀⁻¹) * k₀⁻¹ := by
          group
      _ = k₀ * (y₀ * q * y₀⁻¹) * k₀⁻¹ := by
          rw [show k₀⁻¹ * p * k₀ = q by rw [← hk₀q]; group]
      _ = p := by rw [hy₀q, hk₀q]
  have hz₂K : k₀ * y₀ * k₀⁻¹ ∈ K := mul_mem (mul_mem hk₀ hy₀) (inv_mem hk₀)
  have hhq : y₀ * (k₀ * y₀ * k₀⁻¹) * q * (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹ = p := by
    calc y₀ * (k₀ * y₀ * k₀⁻¹) * q * (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹ =
          y₀ * (k₀ * (y₀ * (k₀⁻¹ * q * k₀) * y₀⁻¹) * k₀⁻¹) * y₀⁻¹ := by group
      _ = y₀ * (k₀ * (y₀ * (q * p) * y₀⁻¹) * k₀⁻¹) * y₀⁻¹ := by rw [hk₀i]
      _ = y₀ * (k₀ * ((y₀ * q * y₀⁻¹) * (y₀ * p * y₀⁻¹)) * k₀⁻¹) * y₀⁻¹ := by group
      _ = y₀ * (k₀ * (q * (q * p)) * k₀⁻¹) * y₀⁻¹ := by rw [hy₀q, hy₀p]
      _ = y₀ * (k₀ * p * k₀⁻¹) * y₀⁻¹ := by
          rw [show q * (q * p) = p by rw [← mul_assoc, hqq, one_mul]]
      _ = y₀ * (q * p) * y₀⁻¹ := by rw [hk₀p]
      _ = (y₀ * q * y₀⁻¹) * (y₀ * p * y₀⁻¹) := by group
      _ = q * (q * p) := by rw [hy₀q, hy₀p]
      _ = p := by rw [← mul_assoc, hqq, one_mul]
  set m := (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹ * k₀ with hm
  have hmK : m ∈ K := mul_mem (inv_mem (mul_mem hy₀ hz₂K)) hk₀
  have hmq : m * q = q * m := by
    refine hcomm m ?_
    calc m * q * m⁻¹ = (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹ * (k₀ * q * k₀⁻¹) *
          (y₀ * (k₀ * y₀ * k₀⁻¹)) := by rw [hm]; group
      _ = (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹ *
          (y₀ * (k₀ * y₀ * k₀⁻¹) * q * (y₀ * (k₀ * y₀ * k₀⁻¹))⁻¹) *
          (y₀ * (k₀ * y₀ * k₀⁻¹)) := by rw [hk₀q, hhq]
      _ = q := by group
  have hy₀q' : y₀ * q = q * y₀ := hcomm y₀ hy₀q
  have hk : k₀ = y₀ * (k₀ * y₀ * k₀⁻¹) * m := by rw [hm]; group
  have hFk : F k₀ = F' k₀ := by
    rw [hk, hF _ (mul_mem hy₀ hz₂K) _ hmK, hF _ hy₀ _ hz₂K, hF' _ (mul_mem hy₀ hz₂K) _ hmK,
      hF' _ hy₀ _ hz₂K, h1 y₀ hy₀ hy₀q', h2 _ hz₂K hz₂, h1 m hmK hmq]
  have hinv : ∀ {f : G → H}, (∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x * f y) → ∀ x ∈ K,
      f x⁻¹ = (f x)⁻¹ := fun {f} hf x hx => by
    have h0 := hf 1 K.one_mem 1 K.one_mem
    rw [one_mul] at h0
    have h1' : f 1 = 1 := mul_eq_left.mp h0.symm
    have h := hf x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, h1'] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  intro x hx
  rcases hW x hx with h | h | h
  · exact h1 x hx (hcomm x h)
  ·
    have hx' : k₀⁻¹ * x * q = q * (k₀⁻¹ * x) := by
      refine hcomm _ ?_
      calc k₀⁻¹ * x * q * (k₀⁻¹ * x)⁻¹ = k₀⁻¹ * (x * q * x⁻¹) * k₀ := by group
        _ = q := by rw [h, ← hk₀q]; group
    have e : x = k₀ * (k₀⁻¹ * x) := by group
    rw [e, hF _ hk₀ _ (mul_mem (inv_mem hk₀) hx), hF' _ hk₀ _ (mul_mem (inv_mem hk₀) hx), hFk,
      h1 _ (mul_mem (inv_mem hk₀) hx) hx']
  ·
    have hx' : k₀ * x * q = q * (k₀ * x) := by
      refine hcomm _ ?_
      calc k₀ * x * q * (k₀ * x)⁻¹ = k₀ * (x * q * x⁻¹) * k₀⁻¹ := by group
        _ = q := by rw [h, hk₀qp]
    have e : x = k₀⁻¹ * (k₀ * x) := by group
    rw [e, hF _ (inv_mem hk₀) _ (mul_mem hk₀ hx), hF' _ (inv_mem hk₀) _ (mul_mem hk₀ hx),
      hinv hF k₀ hk₀, hinv hF' k₀ hk₀, hFk, h1 _ (mul_mem hk₀ hx) hx']

end Generic

local notation "qN" => ((wT 2 : Vt) : NativeSporadic.Co1)

local notation "pN" => ((wT 0 : Vt) : NativeSporadic.Co1)

@[expose] noncomputable def yZero : NativeSporadic.Co1 := gElt y0Idx

theorem nrep_qN : NRep qRows qN := nrep_wT 2

theorem nrep_pN : NRep pRows pN := nrep_wT 0

theorem kZero_conj_p : kZero * pN * kZero⁻¹ = qN * pN := by
  obtain ⟨-, h, -⟩ := edgeElemOK_parts
  have hk := nrep_gEl (dagOK_parts dagOK_true).1 (gensKe.getD 4 0)
  have hki := nrep_gElInv dagOK_true (amalgamCheck_parts.2.1) (amalgamCheck_parts.2.2.1)
  exact NRep.unique ((hk.mul nrep_pN).mul hki) (by rw [h]; exact nrep_qN.mul nrep_pN)

theorem yZero_mem : yZero ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] := by
  obtain ⟨-, -, -, hcent, -⟩ := triCheck_parts
  exact mem_of_centOK hcent (fun l hl => nrep_gensArr dagOK_true _ hl)
    (nrep_repV (show 1 < 10 by norm_num)) 2 (by rw [gensArr_size]; decide)

theorem yZero_conj : yZero * qN * yZero⁻¹ = qN ∧ yZero * pN * yZero⁻¹ = qN * pN := by
  obtain ⟨⟨h1, h2⟩, -, hq, hp, -⟩ := edgeElemOK_parts
  have hy := nrep_gEl (dagOK_parts dagOK_true).1 y0Idx
  have hyi := nrep_gElInv dagOK_true h1 h2
  exact ⟨NRep.unique ((hy.mul nrep_qN).mul hyi) (by rw [hq]; exact nrep_qN),
    NRep.unique ((hy.mul nrep_pN).mul hyi) (by rw [hp]; exact nrep_qN.mul nrep_pN)⟩

theorem qN_mul_pN : qN * pN = pN * qN := by
  have hq : typeSystemC.φ (yprodH 217 * typeSystemC.z) = 1 := by
    rw [map_mul, phi_yprodH, typeSystemC.φ_z, one_mul]
  have h := (typeSystemC.comm_eq_one_iff _ _ hq (phi_yprodH 9)).2 (by
    rw [vec_yprodH_mul_z, vec_yprodH]
    show QuadraticMap.polar q₀ (bv 217) (bv 9) = 0
    rw [polar_q₀_bv]
    rfl)
  have hC : yprodH 217 * typeSystemC.z * yprodH 9 = yprodH 9 * (yprodH 217 * typeSystemC.z) := by
    calc yprodH 217 * typeSystemC.z * yprodH 9 =
        yprodH 217 * typeSystemC.z * yprodH 9 * (yprodH 217 * typeSystemC.z)⁻¹ * (yprodH 9)⁻¹ *
          (yprodH 9 * (yprodH 217 * typeSystemC.z)) := by group
      _ = yprodH 9 * (yprodH 217 * typeSystemC.z) := by rw [h, one_mul]
  have h' := congrArg Subtype.val hC
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
  rw [coe_q_eq, coe_p_eq]
  exact h'

theorem qN_mem_qOf_vE : qN ∈ qOf (vE : NativeSporadic.Co1) := by
  refine mem_qOf_symm₂ pattersonCo1Hyp_native vE.2 (wT 2).2 (fun h => ?_) (vE_mem_qOf_wT 2)
  have h2 := wT_mem_qOf_aNC 2
  rw [← h] at h2
  exact vE_not_mem_qOf_aNC h2

theorem qOf_inter_cases {y : NativeSporadic.Co1} (hya : y ∈ qOf aNC)
    (hye : y ∈ qOf (vE : NativeSporadic.Co1)) : y = 1 ∨ y = qN ∨ y = pN ∨ y = qN * pN := by
  have hyQ : y ∈ twoAQNC := by rw [← qOf_aNC]; exact hya
  have hyC : y ∈ C[aNC] := qOf_le_centralizer _ hya
  set yC : centralizer ({aNC} : Set NativeSporadic.Co1) := ⟨y, hyC⟩ with hyCdef
  have hφ : typeSystemC.φ yC = 1 :=
    (Setting.phiV₀_eq_one_iff nativeSetting coordIso nativeOmega yC).2
      (mem_QG_of_centEmb (by rw [centEmb_apply]; exact hyQ))
  obtain ⟨Y, hY, hYv, hYmem⟩ : ∃ Y : Native.Rows, NRep Y y ∧
      CFSG.Sporadic.Co1.InvNative.validRows Y = true ∧
      (Y = yprodRow (enc (typeSystemC.vec yC)) ∨
        Y = Native.mul (yprodRow (enc (typeSystemC.vec yC))) iotaARows) := by
    have hv := TwistNative.dagOK_parts.2.2.2.1 _ (enc_lt (typeSystemC.vec yC))
    rcases eq_yprodH_of_phi hφ with h1 | h1
    · refine ⟨_, ?_, hv, Or.inl rfl⟩
      have e : y = ((yprodH (enc (typeSystemC.vec yC)) :
          centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) :=
        congrArg Subtype.val h1
      rw [e]
      exact nrep_yprodH _
    · refine ⟨_, ?_, valid_mul hv TwistNative.dagOK_parts.2.1, Or.inr rfl⟩
      have e : y = ((yprodH (enc (typeSystemC.vec yC)) * typeSystemC.z :
          centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) :=
        congrArg Subtype.val h1
      rw [e, Subgroup.coe_mul, coe_z]
      exact (nrep_yprodH _).mul nrep_aNC
  have hxe : gElt (repJ 1) * aNC * (gElt (repJ 1))⁻¹ = (vE : NativeSporadic.Co1) := by
    have := coe_smul_eq (repV_eq_smul 1).symm
    rw [coe_vA] at this
    exact this
  have hconj : (gElt (repJ 1))⁻¹ * y * gElt (repJ 1) ∈ twoAQNC := by
    rw [← qOf_aNC]
    refine (mem_qOf_conj (gElt (repJ 1)) aNC y).1 ?_
    rw [hxe]
    exact hye
  have hR := ((nrep_repXi dagOK_true (show 1 < 10 by norm_num)).mul hY).mul
    (nrep_repX dagOK_true 1)
  have hRv : CFSG.Sporadic.Co1.InvNative.validRows
      (Native.mul (Native.mul (repXi 1) Y) (repX 1)) = true :=
    valid_mul (valid_mul ((dagOK_parts dagOK_true).2 _ (repJ_mem (show 1 < 10 by
      norm_num)).1 (repJ_mem (show 1 < 10 by norm_num)).2).2.1 hYv)
      ((dagOK_parts dagOK_true).2 _ (repJ_mem (show 1 < 10 by norm_num)).1
        (repJ_mem (show 1 < 10 by norm_num)).2).1
  have hcont := (mem_twoAQNC_iff_contains hR hRv).1 hconj
  have hq := edgeRigidCheck_parts.1
  unfold qaeOK at hq
  simp only [List.all_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hq
  have hYc : Y = Native.one ∨ Y = qRows ∨ Y = pRows ∨ Y = Native.mul qRows pRows := by
    obtain ⟨h1, h2⟩ := hq _ (enc_lt (typeSystemC.vec yC))
    rcases hYmem with rfl | rfl
    · rcases h1 with ((((h | h) | h) | h) | h)
      · rw [hcont] at h; exact absurd h (by decide)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases h2 with ((((h | h) | h) | h) | h)
      · rw [hcont] at h; exact absurd h (by decide)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  rcases hYc with h | h | h | h
  · rw [h] at hY
    exact Or.inl (NRep.unique hY NRep.one')
  · rw [h] at hY
    exact Or.inr (Or.inl (NRep.unique hY nrep_qN))
  · rw [h] at hY
    exact Or.inr (Or.inr (Or.inl (NRep.unique hY nrep_pN)))
  · rw [h] at hY
    exact Or.inr (Or.inr (Or.inr (NRep.unique hY (nrep_qN.mul nrep_pN))))

theorem yprodH_comm_qN_pN {c : ℕ} (hc : c ∈ uBasis) :
    (yprodH c : NativeSporadic.Co1) * qN = qN * yprodH c ∧
      (yprodH c : NativeSporadic.Co1) * pN = pN * yprodH c := by
  have hq : typeSystemC.φ (yprodH 217 * typeSystemC.z) = 1 := by
    rw [map_mul, phi_yprodH, typeSystemC.φ_z, one_mul]
  have hb : bNat c 217 = false ∧ bNat c 9 = false := by
    simp only [uBasis, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have comm : ∀ u v : centralizer ({aNC} : Set NativeSporadic.Co1),
      u * v * u⁻¹ * v⁻¹ = 1 → u * v = v * u := fun u v h => by
    calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
      _ = v * u := by rw [h, one_mul]
  have h1 := comm _ _ ((typeSystemC.comm_eq_one_iff _ _ (phi_yprodH c) hq).2 (by
    rw [vec_yprodH, vec_yprodH_mul_z]
    show QuadraticMap.polar q₀ (bv c) (bv 217) = 0
    rw [polar_q₀_bv, hb.1]
    rfl))
  have h2 := comm _ _ ((typeSystemC.comm_eq_one_iff _ _ (phi_yprodH c) (phi_yprodH 9)).2 (by
    rw [vec_yprodH, vec_yprodH]
    show QuadraticMap.polar q₀ (bv c) (bv 9) = 0
    rw [polar_q₀_bv, hb.2]
    rfl))
  have e1 := congrArg Subtype.val h1
  have e2 := congrArg Subtype.val h2
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at e1 e2
  rw [coe_q_eq, coe_p_eq]
  exact ⟨e1, e2⟩

theorem autRigidAt_native : AutRigidAt aNC (vE : NativeSporadic.Co1) qN := by
  intro ψ hψ
  obtain ⟨F, hFdef⟩ : ∃ F : NativeSporadic.Co1 → NativeSporadic.Co1, F = extFun ψ := ⟨_, rfl⟩
  have hF : IsoOn F (C[aNC] ⊓ C[(vE : NativeSporadic.Co1)])
      (C[aNC] ⊓ C[(vE : NativeSporadic.Co1)]) := by
    rw [hFdef]
    exact isoOn_extFun ψ
  have hFval : ∀ x (hx : x ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)]),
      F x = (ψ ⟨x, hx⟩ : NativeSporadic.Co1) := fun x hx => by rw [hFdef, extFun_of_mem ψ hx]
  have hF1 : ∀ x ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)], x * qN = qN * x → F x = x :=
    fun x hx hxq => by
      rw [hFval x hx, hψ ⟨x, hx⟩ (mem_centralizer_singleton_iff.2 hxq)]
  have hqq : qN * qN = 1 := vt_mul_self (wT 2)
  have hpp : pN * pN = 1 := vt_mul_self (wT 0)
  have hW : ∀ x ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)],
      x * qN * x⁻¹ = qN ∨ x * qN * x⁻¹ = pN ∨ x * qN * x⁻¹ = qN * pN := by
    intro x hx
    have hconj : ∀ w : NativeSporadic.Co1, x * w * x⁻¹ = w → qN ∈ qOf w →
        x * qN * x⁻¹ ∈ qOf w := fun w hw hq => by
      have := (mem_qOf_conj x w (x * qN * x⁻¹)).2
        (by rw [show x⁻¹ * (x * qN * x⁻¹) * x = qN by group]; exact hq)
      rwa [hw] at this
    have hxa : x * aNC * x⁻¹ = aNC := by
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hx).1]; group
    have hxe : x * vE * x⁻¹ = vE := by
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2]; group
    rcases qOf_inter_cases (hconj _ hxa (wT_mem_qOf_aNC 2)) (hconj _ hxe qN_mem_qOf_vE) with
      h | h | h | h
    · exfalso
      have : qN = 1 := by
        calc qN = x⁻¹ * (x * qN * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      have h2 := orderOf_vt (wT 2)
      rw [this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hk₀ := kZero_mem
  have hFk : F kZero ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] := hF.map_mem _ hk₀
  have hdK : F kZero * kZero⁻¹ ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] :=
    mul_mem hFk (inv_mem hk₀)
  have hFK₂ : ∀ x ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)], x * pN = pN * x →
      F x = (F kZero * kZero⁻¹) * x * (F kZero * kZero⁻¹)⁻¹ := by
    intro x hx hxp
    have hy : kZero⁻¹ * x * kZero ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] :=
      mul_mem (mul_mem (inv_mem hk₀) hx) hk₀
    have hyq : kZero⁻¹ * x * kZero * qN = qN * (kZero⁻¹ * x * kZero) := by
      have hp : pN = kZero * qN * kZero⁻¹ := kZero_conj.symm
      calc kZero⁻¹ * x * kZero * qN = kZero⁻¹ * (x * (kZero * qN * kZero⁻¹)) * kZero := by group
        _ = kZero⁻¹ * ((kZero * qN * kZero⁻¹) * x) * kZero := by rw [← hp, hxp]
        _ = qN * (kZero⁻¹ * x * kZero) := by group
    have e : x = kZero * (kZero⁻¹ * x * kZero) * kZero⁻¹ := by group
    rw [e, hF.map_conj hk₀ hy, hF1 _ hy hyq]
    group
  have hdc : ∀ c ∈ uBasis, (F kZero * kZero⁻¹) * (yprodH c : NativeSporadic.Co1) =
      (yprodH c : NativeSporadic.Co1) * (F kZero * kZero⁻¹) := by
    intro c hc
    obtain ⟨hq', hp'⟩ := yprodH_comm_qN_pN hc
    have hyK : (yprodH c : NativeSporadic.Co1) ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] := by
      refine mem_inf.2 ⟨(yprodH c).2, mem_centralizer_singleton_iff.2 ?_⟩
      have := congrArg Subtype.val (yprodH_comm_eC hc)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eC] at this
      exact this
    have e := (hF1 _ hyK hq').symm.trans (hFK₂ _ hyK hp')
    calc (F kZero * kZero⁻¹) * (yprodH c : NativeSporadic.Co1) =
        (F kZero * kZero⁻¹) * (yprodH c : NativeSporadic.Co1) * (F kZero * kZero⁻¹)⁻¹ *
          (F kZero * kZero⁻¹) := by group
      _ = (yprodH c : NativeSporadic.Co1) * (F kZero * kZero⁻¹) := by rw [← e]
  obtain ⟨hy₀q, hy₀p⟩ := yZero_conj
  have hext := fun (F' : NativeSporadic.Co1 → NativeSporadic.Co1)
      (hF' : ∀ x ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)],
        ∀ y ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)], F' (x * y) = F' x * F' y) =>
    eq_on_of_eq_on_two (F := F) (F' := F') hF.map_mul hF' hqq hpp qN_mul_pN hW hk₀ kZero_conj
      kZero_conj_p yZero_mem hy₀q hy₀p
  rcases cent_cases hdK hdc with h1 | h1
  · left
    have hall := hext id (fun _ _ _ _ => rfl) (fun x hx hxq => hF1 x hx hxq)
      (fun x hx hxp => by
        rw [hFK₂ x hx hxp, h1 x (mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxp⟩)]
        rfl)
    intro g
    apply Subtype.ext
    rw [← hFval g g.2]
    exact hall g g.2
  · right
    have hall := hext (fun x => qN * x * qN⁻¹) (fun _ _ _ _ => by group)
      (fun x hx hxq => by
        show F x = qN * x * qN⁻¹
        rw [hF1 x hx hxq, ← hxq]
        group)
      (fun x hx hxp => by
        show F x = qN * x * qN⁻¹
        rw [hFK₂ x hx hxp, h1 x (mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxp⟩)])
    intro g
    rw [← hFval g g.2]
    exact hall g g.2

end CFSG.Sporadic.Co1Patterson
