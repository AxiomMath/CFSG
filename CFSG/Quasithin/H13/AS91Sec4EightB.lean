module

public import CFSG.Quasithin.H13.AS91Sec4EightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

namespace Two

@[expose] def kapQ (u : ℕ) : Array ℕ :=
  ((List.range 7).map fun j =>
    if j = 0 then 1 else 2 ^ j + if polarB (w1Basis.getD (j - 1) 0) u then 1 else 0).toArray

theorem kapQ_size (u : ℕ) : (kapQ u).size = 7 := by simp [kapQ]

theorem kapQ_getElem (u : ℕ) {j : ℕ} (hj : j < 7) :
    (kapQ u)[j]! =
      if j = 0 then 1 else 2 ^ j + if polarB (w1Basis.getD (j - 1) 0) u then 1 else 0 := by
  rw [getElem!_pos _ j (by rw [kapQ_size]; exact hj)]
  simp [kapQ]

theorem kapQ_q0c : kapQ q0c = t7el := by decide

theorem two_pow_xor_one : ∀ j < 7, j ≠ 0 → 2 ^ j ^^^ 1 = 2 ^ j + 1 := by decide

theorem i7List_lt : ∀ c ∈ i7List, c < 128 := by decide

end Two

theorem polar_vecOf_eq_one_iff (a b : ℕ) :
    QuadraticMap.polar q0 (vecOf a) (vecOf b) = 1 ↔ Two.polarB a b = true := by
  rw [polar_vecOf]
  unfold Two.polarB
  cases q0b (a ^^^ b) <;> cases q0b a <;> cases q0b b <;> decide

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section KapQ

theorem kap_toMb_QG {q : G} (hq : q ∈ h.setting.QG) :
    D.kap (D.toMb ⟨q, D.QG_le_N hq⟩ : MulAut ↥D.E) = Two.kapQ (D.wc q) := by
  apply Array.ext
  · rw [kap_size, Two.kapQ_size]
  · intro j h1 h2
    have hj : j < 7 := by rwa [kap_size] at h1
    rw [← getElem!_pos (D.kap _) j h1, ← getElem!_pos (Two.kapQ _) j h2, D.kap_getElem _ hj,
      Two.kapQ_getElem _ hj]
    change D.crd (q * D.bE j * q⁻¹) = _
    have hqz : q * z * q⁻¹ = z := by
      have := h.setting.z_comm_QG hq
      rw [h.setting_z] at this
      rw [this, mul_inv_cancel_right]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, bE, if_pos rfl, hqz, D.crd_z]
    rw [if_neg hj0]
    set w := Two.w1Basis.getD (j - 1) 0 with hw
    have hb : D.bE j = D.rep w := by rw [bE, if_neg hj0]
    have hpolar : QuadraticMap.polar h.setting.q (h.setting.cl q) (h.setting.cl (D.rep w)) =
        QuadraticMap.polar q0 (vecOf w) (vecOf (D.wc q)) := by
      rw [D.polar_ψV, QuadraticMap.polar_comm, D.ψV_cl_rep, wc, vecOf_codeOf]
    have hcb := D.crd_bE hj
    rw [hb] at hcb
    split_ifs with hp
    · have h1' : QuadraticMap.polar h.setting.q (h.setting.cl q) (h.setting.cl (D.rep w)) = 1 := by
        rw [hpolar]
        exact (polar_vecOf_eq_one_iff w (D.wc q)).mpr hp
      rw [hb, conj_eq_mul_z_of_polar h.setting hq (D.rep_mem _) h1', h.setting_z,
        D.crd_mul (hb ▸ D.bE_mem_E1 j) D.z_mem_E1, hcb, D.crd_z]
      exact Two.two_pow_xor_one j hj hj0
    · have h0 : QuadraticMap.polar h.setting.q (h.setting.cl q) (h.setting.cl (D.rep w)) = 0 := by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (QuadraticMap.polar h.setting.q
          (h.setting.cl q) (h.setting.cl (D.rep w))) with h' | h'
        · exact h'
        · rw [hpolar] at h'
          exact absurd ((polar_vecOf_eq_one_iff w (D.wc q)).mp h') hp
      have hc := (h.setting.polar_cl_eq_zero_iff hq (D.rep_mem _)).mp h0
      rw [hb, hc, mul_inv_cancel_right, hcb, add_zero]

theorem tb_mem_Mz : D.tb ∈ D.Mz := by
  refine D.mem_Mz.mpr (Subtype.ext ?_)
  change D.q0e * z * D.q0e⁻¹ = z
  have := h.setting.z_comm_QG D.q0e_mem_QG
  rw [h.setting_z] at this
  rw [this, mul_inv_cancel_right]

theorem tb_mem_C3 : D.tb ∈ D.C3 := ⟨D.tb_mem_Mz, mem_centralizer_singleton_iff.mpr rfl⟩

theorem kap_tb : D.kap (D.tb : MulAut ↥D.E) = Two.t7el := by
  rw [tb, D.kap_toMb_QG D.q0e_mem_QG, D.wc_q0, Two.kapQ_q0c]

end KapQ

section B

@[expose] noncomputable def Bb : Subgroup ↥D.Mb where
  carrier := {φ | φ ∈ D.Cb ∧ ∀ x ∈ D.Iset, (φ : MulAut ↥D.E) x = x}
  mul_mem' {φ ψ} hφ hψ := ⟨mul_mem hφ.1 hψ.1, fun x hx => by
    change (φ : MulAut ↥D.E) ((ψ : MulAut ↥D.E) x) = x
    rw [hψ.2 x hx, hφ.2 x hx]⟩
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' {φ} hφ := ⟨inv_mem hφ.1, fun x hx => by
    calc ((φ⁻¹ : ↥D.Mb) : MulAut ↥D.E) x
        = ((φ⁻¹ : ↥D.Mb) : MulAut ↥D.E) ((φ : MulAut ↥D.E) x) := by rw [hφ.2 x hx]
      _ = x := by
        change ((φ⁻¹ * φ : ↥D.Mb) : MulAut ↥D.E) x = x
        rw [inv_mul_cancel]
        rfl⟩

theorem Bb_le_Cb : D.Bb ≤ D.Cb := fun _ hφ => hφ.1

theorem conj_mem_Bb {c : ↥D.Mb} (hc : c ∈ D.Cb) {b : ↥D.Mb} (hb : b ∈ D.Bb) :
    c * b * c⁻¹ ∈ D.Bb := by
  refine ⟨mul_mem (mul_mem hc hb.1) (inv_mem hc), fun x hx => ?_⟩
  have hx' := D.apply_mem_Iset (inv_mem hc) hx
  change (c : MulAut ↥D.E) ((b : MulAut ↥D.E) (((c⁻¹ : ↥D.Mb) : MulAut ↥D.E) x)) = x
  rw [hb.2 _ hx']
  change ((c * c⁻¹ : ↥D.Mb) : MulAut ↥D.E) x = x
  rw [mul_inv_cancel]
  rfl

theorem inv_apply_apply (φ : ↥D.Mb) (x : ↥D.E) :
    ((φ⁻¹ : ↥D.Mb) : MulAut ↥D.E) ((φ : MulAut ↥D.E) x) = x := by
  change ((φ⁻¹ * φ : ↥D.Mb) : MulAut ↥D.E) x = x
  rw [inv_mul_cancel]
  rfl

end B

section BFacts

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem eq_of_kap_eq {φ ψ : ↥D.Mb} (hφ : φ ∈ D.Mz) (hψ : ψ ∈ D.Mz)
    (hk : D.kap (φ : MulAut ↥D.E) = D.kap (ψ : MulAut ↥D.E)) : φ = ψ := by
  have hφ' := D.presE1_of_mem_Mz hOut hTw hφ
  have hψ' := D.presE1_of_mem_Mz hOut hTw hψ
  refine D.eq_of_agree_E1 hOut hTw hHat fun x hx => Subtype.ext ?_
  exact D.crd_injective (hφ' x hx) (hψ' x hx) (by rw [D.crd_apply hφ' hx, D.crd_apply hψ' hx, hk])

theorem Bb_le_C3 : D.Bb ≤ D.C3 := fun φ hφ =>
  ⟨D.mem_Mz.mpr (hφ.2 _ (D.zE_mem_Iset hOut hTw hHat)), hφ.1⟩

theorem omE_mem_Iset {v : ℕ} (hv : v ∈ Two.i7List) : D.omE v ∈ D.Iset := by
  refine (D.mem_Iset_iff hOut hTw hHat _).mpr ⟨D.elt7_mem_E1 v, ?_⟩
  change D.crd (D.elt7 v) ∈ Two.i7List
  rw [D.crd_elt7 (Two.i7List_lt v hv)]
  exact hv

theorem mem_Bb_iff {φ : ↥D.Mb} (hφ : φ ∈ D.C3) :
    φ ∈ D.Bb ↔ ∀ v ∈ Two.i7List, Two.app7 (D.kap (φ : MulAut ↥D.E)) v = v := by
  have hp := D.presE1_of_mem_Mz hOut hTw hφ.1
  constructor
  · intro hB v hv
    have h1 := hB.2 _ (D.omE_mem_Iset hOut hTw hHat hv)
    have h2 := D.crd_apply hp (x := D.omE v) (D.elt7_mem_E1 v)
    rw [h1] at h2
    change D.crd (D.elt7 v) = Two.app7 _ (D.crd (D.elt7 v)) at h2
    rw [D.crd_elt7 (Two.i7List_lt v hv)] at h2
    exact h2.symm
  · intro hfix
    refine ⟨hφ.2, fun x hx => ?_⟩
    obtain ⟨hxE1, hxc⟩ := (D.mem_Iset_iff hOut hTw hHat x).mp hx
    apply Subtype.ext
    apply D.crd_injective (hp x hxE1) hxE1
    rw [D.crd_apply hp hxE1, hfix _ hxc]

theorem kap_mem_b7List {φ : ↥D.Mb} (hφ : φ ∈ D.Bb) :
    D.kap (φ : MulAut ↥D.E) ∈ Two.b7List () := by
  have hC := D.Bb_le_C3 hOut hTw hHat hφ
  refine List.mem_filter.mpr ⟨D.kap_mem_c3List hOut hTw hHat hC, ?_⟩
  exact List.all_eq_true.mpr fun v hv =>
    beq_iff_eq.mpr ((D.mem_Bb_iff hOut hTw hHat hC).mp hφ v hv)

theorem exists_of_mem_b7List {X : Array ℕ} (hX : X ∈ Two.b7List ()) :
    ∃ φ ∈ D.Bb, D.kap (φ : MulAut ↥D.E) = X := by
  obtain ⟨hX3, hXf⟩ := List.mem_filter.mp hX
  obtain ⟨φ, hφ, rfl⟩ := D.exists_of_mem_c3List hOut hTw hHat hX3
  refine ⟨φ, (D.mem_Bb_iff hOut hTw hHat hφ).mpr fun v hv => ?_, rfl⟩
  exact beq_iff_eq.mp (List.all_eq_true.mp hXf v hv)

theorem tb_mem_Bb : D.tb ∈ D.Bb := by
  refine (D.mem_Bb_iff hOut hTw hHat D.tb_mem_C3).mpr fun v hv => ?_
  have h1 := (List.mem_filter.mp Two.c3OK48_spec.2.2.2.1).2
  rw [D.kap_tb]
  exact beq_iff_eq.mp (List.all_eq_true.mp h1 v hv)

theorem Bb_comm {φ ψ : ↥D.Mb} (hφ : φ ∈ D.Bb) (hψ : ψ ∈ D.Bb) : φ * ψ = ψ * φ := by
  have hφz := (D.Bb_le_C3 hOut hTw hHat hφ).1
  have hψz := (D.Bb_le_C3 hOut hTw hHat hψ).1
  have hp := D.presE1_of_mem_Mz hOut hTw hφz
  have hq := D.presE1_of_mem_Mz hOut hTw hψz
  refine D.eq_of_kap_eq hOut hTw hHat (mul_mem hφz hψz) (mul_mem hψz hφz) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, D.kap_mul hp hq, D.kap_mul hq hp]
  exact Two.c3OK48_spec.2.2.2.2.1 _ (D.kap_mem_b7List hOut hTw hHat hφ) _
    (D.kap_mem_b7List hOut hTw hHat hψ)

theorem Bb_mul_self {φ : ↥D.Mb} (hφ : φ ∈ D.Bb) : φ * φ = 1 := by
  have hφz := (D.Bb_le_C3 hOut hTw hHat hφ).1
  have hp := D.presE1_of_mem_Mz hOut hTw hφz
  refine D.eq_of_kap_eq hOut hTw hHat (mul_mem hφz hφz) (one_mem _) ?_
  rw [Subgroup.coe_mul, D.kap_mul hp hp,
    Two.c3OK48_spec.2.2.2.2.2.1 _ (D.kap_mem_b7List hOut hTw hHat hφ), Subgroup.coe_one, D.kap_one]

theorem card_Bb : Nat.card D.Bb = 16 := by
  let f : ↥D.Bb → ↥(Two.b7List ()).toFinset := fun φ =>
    ⟨D.kap ((φ : ↥D.Mb) : MulAut ↥D.E), List.mem_toFinset.mpr (D.kap_mem_b7List hOut hTw hHat φ.2)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun φ ψ h1 => Subtype.ext (D.eq_of_kap_eq hOut hTw hHat
      (D.Bb_le_C3 hOut hTw hHat φ.2).1 (D.Bb_le_C3 hOut hTw hHat ψ.2).1
      (congrArg Subtype.val h1)), fun X => ?_⟩
    obtain ⟨φ, hφ, hX⟩ := D.exists_of_mem_b7List hOut hTw hHat (List.mem_toFinset.mp X.2)
    exact ⟨⟨φ, hφ⟩, Subtype.ext hX⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.card_toFinset, Two.c3OK48_spec.2.2.1]

theorem mem_Bb_of_mem_C3 {φ : ↥D.Mb} (hφ : φ ∈ D.C3) (hc : ∀ b ∈ D.Bb, φ * b = b * φ) :
    φ ∈ D.Bb := by
  have hp := D.presE1_of_mem_Mz hOut hTw hφ.1
  have hX : D.kap (φ : MulAut ↥D.E) ∈ Two.b7List () := by
    refine Two.c3OK48_spec.2.2.2.2.2.2 _ (D.kap_mem_c3List hOut hTw hHat hφ) fun b hb => ?_
    obtain ⟨β, hβ, rfl⟩ := D.exists_of_mem_b7List hOut hTw hHat hb
    have hq := D.presE1_of_mem_Mz hOut hTw (D.Bb_le_C3 hOut hTw hHat hβ).1
    rw [← D.kap_mul hp hq, ← D.kap_mul hq hp, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc β hβ]
  obtain ⟨φ', hφ', hk⟩ := D.exists_of_mem_b7List hOut hTw hHat hX
  rwa [← D.eq_of_kap_eq hOut hTw hHat (D.Bb_le_C3 hOut hTw hHat hφ').1 hφ.1 hk]

theorem apply_omE {φ : ↥D.Mb} (hφ : φ ∈ D.C3) {c d : ℕ} (hc : c < 128)
    (hd : Two.app7 (D.kap (φ : MulAut ↥D.E)) c = d) (hd' : d < 128) :
    (φ : MulAut ↥D.E) (D.omE c) = D.omE d := by
  have hp := D.presE1_of_mem_Mz hOut hTw hφ.1
  apply Subtype.ext
  apply D.crd_injective (hp _ (D.elt7_mem_E1 c)) (D.elt7_mem_E1 d)
  rw [D.crd_apply hp (D.elt7_mem_E1 c)]
  change Two.app7 _ (D.crd (D.elt7 c)) = D.crd (D.elt7 d)
  rw [D.crd_elt7 hc, D.crd_elt7 hd', hd]

theorem exists_C3_apply {c c' : ℕ} (hc : c ∈ Two.omList) (hc' : c' ∈ Two.omList) :
    ∃ x ∈ D.C3, (x : MulAut ↥D.E) (D.omE c) = D.omE c' := by
  obtain ⟨-, -, -, -, -, -, -, hi8, -⟩ := Two.iOK48_spec
  obtain ⟨X, hX, hX2⟩ := hi8 c hc
  obtain ⟨X', hX', hX2'⟩ := hi8 c' hc'
  obtain ⟨φ, hφ, rfl⟩ := D.exists_of_mem_c3List hOut hTw hHat hX
  obtain ⟨φ', hφ', rfl⟩ := D.exists_of_mem_c3List hOut hTw hHat hX'
  have h1 := D.apply_omE hOut hTw hHat hφ (by norm_num) hX2 (Two.omList_lt c hc)
  have h2 := D.apply_omE hOut hTw hHat hφ' (by norm_num) hX2' (Two.omList_lt c' hc')
  refine ⟨φ' * φ⁻¹, mul_mem hφ' (inv_mem hφ), ?_⟩
  change (φ' : MulAut ↥D.E) (((φ⁻¹ : ↥D.Mb) : MulAut ↥D.E) (D.omE c)) = D.omE c'
  rw [← h1, D.inv_apply_apply, h2]

end BFacts

section Cent

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem not_powers_of_C3 (s : ↥D.Mb)
    (hconj : ∀ {x : ↥D.Mb}, x ∈ D.C3 → ∃ a : ℤ, x * s * x⁻¹ = s ^ a) {i : ℤ}
    (hω : D.omE 2 = (((s ^ i : ↥D.Mb)) : MulAut ↥D.E) D.zE) : False := by
  have happ : ∀ {x : ↥D.Mb}, x ∈ D.C3 → ∀ {a : ℤ}, x * s * x⁻¹ = s ^ a →
      ∀ j : ℤ, (x : MulAut ↥D.E) (((s ^ j : ↥D.Mb) : MulAut ↥D.E) D.zE) =
        (((s ^ (a * j) : ↥D.Mb)) : MulAut ↥D.E) D.zE := by
    intro x hx a ha j
    have e1 : x * s ^ j = s ^ (a * j) * x := by
      rw [zpow_mul, ← ha, conj_zpow, inv_mul_cancel_right]
    have hxz := D.mem_Mz.mp hx.1
    calc (x : MulAut ↥D.E) (((s ^ j : ↥D.Mb) : MulAut ↥D.E) D.zE)
        = (((x * s ^ j : ↥D.Mb)) : MulAut ↥D.E) D.zE := rfl
      _ = (((s ^ (a * j) * x : ↥D.Mb)) : MulAut ↥D.E) D.zE := by rw [e1]
      _ = _ := by
        change (((s ^ (a * j) : ↥D.Mb)) : MulAut ↥D.E) ((x : MulAut ↥D.E) D.zE) = _
        rw [hxz]
  obtain ⟨-, -, -, -, -, -, -, -, hw1, hw2, hw3, -⟩ := Two.iOK48_spec
  obtain ⟨φ₁, hφ₁, hk₁⟩ := D.exists_of_mem_c3List hOut hTw hHat hw1
  obtain ⟨φ₂, hφ₂, hk₂⟩ := D.exists_of_mem_c3List hOut hTw hHat hw2
  obtain ⟨a, ha⟩ := hconj hφ₁
  obtain ⟨b, hb⟩ := hconj hφ₂
  have e1 : (φ₁ : MulAut ↥D.E) ((φ₂ : MulAut ↥D.E) (D.omE 2)) =
      (φ₂ : MulAut ↥D.E) ((φ₁ : MulAut ↥D.E) (D.omE 2)) := by
    rw [hω, happ hφ₂ hb i, happ hφ₁ ha (b * i), happ hφ₁ ha i, happ hφ₂ hb (a * i),
      show a * (b * i) = b * (a * i) by ring]
  have hp₁ := D.presE1_of_mem_Mz hOut hTw hφ₁.1
  have hp₂ := D.presE1_of_mem_Mz hOut hTw hφ₂.1
  have h2E : ((D.omE 2 : ↥D.E) : G) ∈ D.E1 := D.elt7_mem_E1 2
  have hc2 : D.crd ((D.omE 2 : ↥D.E) : G) = 2 := D.crd_elt7 (c := 2) (by norm_num)
  have c1 : D.crd (((φ₁ : MulAut ↥D.E) ((φ₂ : MulAut ↥D.E) (D.omE 2)) : ↥D.E) : G) =
      Two.app7 (D.kap (φ₁ : MulAut ↥D.E)) (Two.app7 (D.kap (φ₂ : MulAut ↥D.E)) 2) := by
    rw [D.crd_apply hp₁ (hp₂ (D.omE 2) h2E), D.crd_apply hp₂ h2E, hc2]
  have c2 : D.crd (((φ₂ : MulAut ↥D.E) ((φ₁ : MulAut ↥D.E) (D.omE 2)) : ↥D.E) : G) =
      Two.app7 (D.kap (φ₂ : MulAut ↥D.E)) (Two.app7 (D.kap (φ₁ : MulAut ↥D.E)) 2) := by
    rw [D.crd_apply hp₂ (hp₁ (D.omE 2) h2E), D.crd_apply hp₁ h2E, hc2]
  rw [← hk₁, ← hk₂] at hw3
  rw [e1] at c1
  exact hw3 (c1.symm.trans c2)

theorem mem_Bb_of_centralizes {φ : ↥D.Mb} (hφ : φ ∈ D.Cb) (hcent : ∀ b ∈ D.Bb, φ * b = b * φ) :
    φ ∈ D.Bb := by
  by_cases hz : φ ∈ D.Mz
  · exact D.mem_Bb_of_mem_C3 hOut hTw hHat ⟨hz, hφ⟩ hcent
  exfalso
  obtain ⟨g₁, hg₁⟩ := D.exists_g₁ hOut hTw
  obtain ⟨s₀, hs₀⟩ := D.exists_s₀ hOut hTw
  set K : Subgroup ↥D.Mb := D.Cb ⊓ centralizer (D.Bb : Set ↥D.Mb) with hK
  have hmemK : ∀ {k : ↥D.Mb}, k ∈ D.Cb → (∀ b ∈ D.Bb, k * b = b * k) → k ∈ K :=
    fun hk hkb => ⟨hk, mem_centralizer_iff.mpr fun b hb => (hkb b hb).symm⟩
  have hKc : ∀ {k : ↥D.Mb}, k ∈ K → ∀ b ∈ D.Bb, k * b = b * k :=
    fun hk b hb => (mem_centralizer_iff.mp hk.2 b hb).symm
  have hBK : D.Bb ≤ K := fun b hb =>
    hmemK hb.1 fun b' hb' => D.Bb_comm hOut hTw hHat hb hb'
  have hnorm : ∀ {c : ↥D.Mb}, c ∈ D.Cb → ∀ {k : ↥D.Mb}, k ∈ K → c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    refine hmemK (mul_mem (mul_mem hc hk.1) (inv_mem hc)) fun b hb => ?_
    have hb' : c⁻¹ * b * c⁻¹⁻¹ ∈ D.Bb := D.conj_mem_Bb (inv_mem hc) hb
    rw [inv_inv] at hb'
    have h1 := hKc hk _ hb'
    calc c * k * c⁻¹ * b = c * (k * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * b * c) * k) * c⁻¹ := by rw [h1]
      _ = b * (c * k * c⁻¹) := by group
  have hOmC := D.orbit_eq hOut hTw hHat hg₁ hs₀
  have hΩ7 := D.ncard_orbit hOut hTw hHat hg₁ hs₀
  have hmemΩ : ∀ {k : ↥D.Mb}, k ∈ D.Cb →
      (k : MulAut ↥D.E) D.zE ∈ MulAction.orbit ↥D.Cb D.zE := fun hk => ⟨⟨_, hk⟩, rfl⟩
  have homE : ∀ {c : ℕ}, c ∈ Two.omList → D.omE c ∈ MulAction.orbit ↥D.Cb D.zE := by
    intro c hc
    rw [hOmC]
    refine ⟨c, ?_, rfl⟩
    rw [Finset.mem_coe, List.mem_toFinset]
    exact List.mem_cons_of_mem _ hc
  have horbK : MulAction.orbit ↥K D.zE = MulAction.orbit ↥D.Cb D.zE := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨k, rfl⟩
      exact hmemΩ k.2.1
    · have hsub : MulAction.orbit ↥D.Cb D.zE ⊆ MulAction.orbit ↥K D.zE := by
        intro y hy
        rw [hOmC] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        rw [Finset.mem_coe, List.mem_toFinset, List.mem_cons] at hc
        rcases hc with rfl | hc
        · rw [D.omE_one]
          exact MulAction.mem_orbit_self _
        have hφΩ := hmemΩ hφ
        rw [hOmC] at hφΩ
        obtain ⟨c₁, hc₁, he₁⟩ := hφΩ
        rw [Finset.mem_coe, List.mem_toFinset, List.mem_cons] at hc₁
        rcases hc₁ with rfl | hc₁
        · exact absurd (D.mem_Mz.mpr (he₁.symm.trans D.omE_one)) hz
        obtain ⟨x, hx, hxc⟩ := D.exists_C3_apply hOut hTw hHat hc₁ hc
        refine ⟨⟨x * φ * x⁻¹, hnorm hx.2 (hmemK hφ hcent)⟩, ?_⟩
        have hxz : ((x⁻¹ : ↥D.Mb) : MulAut ↥D.E) D.zE = D.zE := by
          conv_lhs => rw [← D.mem_Mz.mp hx.1]
          exact D.inv_apply_apply x _
        change (x : MulAut ↥D.E) ((φ : MulAut ↥D.E) (((x⁻¹ : ↥D.Mb) : MulAut ↥D.E) D.zE)) = _
        rw [hxz, ← he₁, hxc]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hstab : ∀ k ∈ K, (k : MulAut ↥D.E) D.zE = D.zE ↔ k ∈ D.Bb := by
    intro k hk
    constructor
    · intro hkz
      exact D.mem_Bb_of_mem_C3 hOut hTw hHat ⟨D.mem_Mz.mpr hkz, hk.1⟩ (hKc hk)
    · intro hkB
      exact D.mem_Mz.mp (D.Bb_le_C3 hOut hTw hHat hkB).1
  have hcardK : Nat.card ↥K = 112 := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥K D.zE)
    rw [MulAction.index_stabilizer, horbK, hΩ7] at h1
    have h2 : Nat.card (MulAction.stabilizer ↥K D.zE) = 16 := by
      rw [← D.card_Bb hOut hTw hHat]
      exact Nat.card_congr
        { toFun := fun k => ⟨k.1.1, (hstab k.1.1 k.1.2).mp k.2⟩
          invFun := fun b => ⟨⟨b.1, hBK b.2⟩, (hstab b.1 (hBK b.2)).mpr b.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h2] at h1
    omega
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨s, hs7⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 7 (by rw [hcardK]; norm_num)
  have hs' : orderOf (s : ↥D.Mb) = 7 := by rw [Subgroup.orderOf_coe, hs7]
  have hsK : (s : ↥D.Mb) ∈ K := s.2
  have hspow : (s : ↥D.Mb) ^ 7 = 1 := by
    rw [← hs']
    exact pow_orderOf_eq_one _
  have hsz : ((s : ↥D.Mb) : MulAut ↥D.E) D.zE ≠ D.zE := by
    intro h1
    have h2 := D.Bb_mul_self hOut hTw hHat ((hstab _ hsK).mp h1)
    have h3 : orderOf (s : ↥D.Mb) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hs'] at h3
    norm_num at h3
  have hzs : MulAction.orbit ↥(zpowers (s : ↥D.Mb)) D.zE = MulAction.orbit ↥D.Cb D.zE := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨g, rfl⟩
      exact hmemΩ ((zpowers_le (H := D.Cb)).mpr hsK.1 g.2)
    · rw [hΩ7]
      have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(zpowers (s : ↥D.Mb)) D.zE)
      rw [MulAction.index_stabilizer, Nat.card_zpowers, hs'] at h1
      have h2 : Nat.card (MulAction.stabilizer ↥(zpowers (s : ↥D.Mb)) D.zE) ∣ 7 :=
        ⟨_, h1.symm⟩
      rcases (Nat.dvd_prime (by norm_num)).mp h2 with h3 | h3
      · rw [h3, one_mul] at h1
        omega
      · exfalso
        have htop := Subgroup.eq_top_of_card_eq
          (MulAction.stabilizer ↥(zpowers (s : ↥D.Mb)) D.zE) (by rw [h3, Nat.card_zpowers, hs'])
        have hmem : (⟨(s : ↥D.Mb), mem_zpowers _⟩ : ↥(zpowers (s : ↥D.Mb))) ∈
            MulAction.stabilizer ↥(zpowers (s : ↥D.Mb)) D.zE := by
          rw [htop]
          trivial
        exact hsz hmem
  have hN : zpowers (s : ↥D.Mb) ≤ normalizer (D.Bb : Set ↥D.Mb) := by
    rw [zpowers_le]
    exact mem_normalizer_fintype fun b hb => D.conj_mem_Bb hsK.1 hb
  have hsup : K ≤ D.Bb ⊔ zpowers (s : ↥D.Mb) := by
    have hle : D.Bb ⊔ zpowers (s : ↥D.Mb) ≤ K := sup_le hBK ((zpowers_le).mpr hsK)
    have h1 := card_sup_mul_card_inf_of_le_normalizer hN
    have hinf : Nat.card ↥(zpowers (s : ↥D.Mb) ⊓ D.Bb) = 1 := by
      have h7 : Nat.card ↥(zpowers (s : ↥D.Mb) ⊓ D.Bb) ∣ 7 := by
        rw [← hs', ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h16 : Nat.card ↥(zpowers (s : ↥D.Mb) ⊓ D.Bb) ∣ 16 := by
        rw [← D.card_Bb hOut hTw hHat]
        exact Subgroup.card_dvd_of_le inf_le_right
      exact Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h7 h16)
    rw [hinf, mul_one, Nat.card_zpowers, hs', D.card_Bb hOut hTw hHat, sup_comm] at h1
    rw [Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hcardK])]
  have hconj : ∀ {x : ↥D.Mb}, x ∈ D.C3 → ∃ a : ℤ, x * (s : ↥D.Mb) * x⁻¹ = (s : ↥D.Mb) ^ a := by
    intro x hx
    obtain ⟨n, hn, y, hy, hny⟩ := exists_mul_of_mem_sup hN (hsup (hnorm hx.2 hsK))
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨a, ?_⟩
    have hcomm : Commute n ((s : ↥D.Mb) ^ a) :=
      (Commute.symm (show Commute (s : ↥D.Mb) n from hKc hsK n hn)).zpow_right a
    have h7 : (x * (s : ↥D.Mb) * x⁻¹) ^ 7 = 1 := by rw [conj_pow, hspow, mul_one, mul_inv_cancel]
    have hn2 : n ^ 2 = 1 := by
      rw [pow_two]
      exact D.Bb_mul_self hOut hTw hHat hn
    have hn7 : n ^ 7 = n := by
      rw [show 7 = 2 * 3 + 1 from rfl, pow_succ, pow_mul, hn2, one_pow, one_mul]
    have hsa7 : ((s : ↥D.Mb) ^ a) ^ 7 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hspow, one_zpow]
    rw [← hny, hcomm.mul_pow, hn7, hsa7, mul_one] at h7
    rw [← hny, h7, one_mul]
  have h2Ω := homE (show (2 : ℕ) ∈ Two.omList by decide)
  rw [← hzs] at h2Ω
  obtain ⟨g, hg⟩ := h2Ω
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
  refine D.not_powers_of_C3 hOut hTw hHat (s : ↥D.Mb) hconj (i := i) ?_
  rw [← hg, hi]
  rfl

end Cent

end Data41

end CFSG.Quasithin.H13.AS91
