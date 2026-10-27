module

public import CFSG.RankThree.GF2n.Tim78S48Defs
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Tim78S4Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem comm_mul_right {y x z : G} (hy : y ∈ Q) (hx : x ∈ Q) (hz : z ∈ Q) :
    ⁅y, x * z⁆ = ⁅y, x⁆ * ⁅y, z⁆ := by
  have h1 : ⁅y, z⁆ ∈ B := H.commutator_mem hy hz
  have h2 : x * ⁅y, z⁆ = ⁅y, z⁆ * x := (H.center_Q h1 hx).symm
  have h3 : ⁅y, x * z⁆ = ⁅y, x⁆ * (x * ⁅y, z⁆ * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h3, h2]
  group

theorem comm_mul_left {y x z : G} (hy : y ∈ Q) (hx : x ∈ Q) (hz : z ∈ Q) :
    ⁅x * z, y⁆ = ⁅x, y⁆ * ⁅z, y⁆ := by
  have h1 : ⁅x, y⁆ ∈ B := H.commutator_mem hx hy
  have h2 : ⁅z, y⁆ ∈ B := H.commutator_mem hz hy
  have h3 : ⁅x * z, y⁆ = x * ⁅z, y⁆ * x⁻¹ * ⁅x, y⁆ := by
    simp only [commutatorElement_def]; group
  have h4 : x * ⁅z, y⁆ = ⁅z, y⁆ * x := (H.center_Q h2 hx).symm
  have h5 : ⁅x, y⁆ * ⁅z, y⁆ = ⁅z, y⁆ * ⁅x, y⁆ := H.B_comm h1 h2
  rw [h3, h4, h5]
  group

end Certified

end Hyp4

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G} {C L : Subgroup G}
  (E : EndgameData M B Q P T g C L)
include E

theorem C_le_L : C ≤ L := by rw [E.hL]; exact le_sup_left

theorem Bg_le_L : conjSubgroup g B ≤ L := by rw [E.hL]; exact le_sup_right

theorem B_le_L : B ≤ L := E.B_le_C.trans E.C_le_L

theorem comm_L {a b : G} (ha : a ∈ L) (hb : b ∈ L) : a * b = b * a :=
  comm_of_isElemAbelian E.L_elem ha hb

theorem comm_C {a b : G} (ha : a ∈ C) (hb : b ∈ C) : a * b = b * a :=
  comm_of_isElemAbelian E.C_elem ha hb

theorem sq_C {c : G} (hc : c ∈ C) : c * c = 1 := IsElemAbelian.mul_self_eq_one E.C_elem hc

theorem C_le_P : C ≤ P := fun c hc => ((E.hC c).mp hc).1

variable (H : Hyp4 M B Q P T)
include H

theorem C_le_Q : C ≤ Q := E.C_le_P.trans H.P_le_Q

theorem Bg_ne_B : conjSubgroup g B ≠ B := by
  intro h
  apply H.B_ne_bot
  have := E.Bg_inf
  rw [h, inf_eq_left.mpr H.B_le_Q] at this
  exact this

section Form

variable {b' : G}

omit E H in
theorem u_conj {x : G} (hxb' : x * b' = b' * x) (y : G) :
    ⁅b', x * y * x⁻¹⁆ = x * ⁅b', y⁆ * x⁻¹ := by
  have hb : x * b' * x⁻¹ = b' := by rw [hxb']; group
  calc ⁅b', x * y * x⁻¹⁆ = ⁅x * b' * x⁻¹, x * y * x⁻¹⁆ := by rw [hb]
    _ = x * ⁅b', y⁆ * x⁻¹ := by simp only [commutatorElement_def]; group

omit H in
theorem u_mem (hb' : b' ∈ conjSubgroup g B) {y : G} (hy : y ∈ Q) : ⁅b', y⁆ ∈ C := by
  have h := C.inv_mem (E.Q_comm y hy b' (E.Bg_le_L hb'))
  rwa [commutatorElement_inv] at h

theorem D_mem (hb' : b' ∈ conjSubgroup g B) {y y' : G} (hy : y ∈ Q) (hy' : y' ∈ Q) :
    ⁅y, ⁅b', y'⁆⁆ ∈ B :=
  H.commutator_mem hy (E.C_le_Q H (E.u_mem hb' hy'))

theorem D_mul_left (hb' : b' ∈ conjSubgroup g B) {y y₂ y' : G} (hy : y ∈ Q) (hy₂ : y₂ ∈ Q)
    (hy' : y' ∈ Q) : ⁅y * y₂, ⁅b', y'⁆⁆ = ⁅y, ⁅b', y'⁆⁆ * ⁅y₂, ⁅b', y'⁆⁆ :=
  H.comm_mul_left (E.C_le_Q H (E.u_mem hb' hy')) hy hy₂

theorem D_mul_right (hb' : b' ∈ conjSubgroup g B) {y y' y₂' : G} (hy : y ∈ Q) (hy' : y' ∈ Q)
    (hy₂' : y₂' ∈ Q) : ⁅y, ⁅b', y' * y₂'⁆⁆ = ⁅y, ⁅b', y'⁆⁆ * ⁅y, ⁅b', y₂'⁆⁆ := by
  have hu := E.C_le_Q H (E.u_mem hb' hy')
  have hu₂ := E.C_le_Q H (E.u_mem hb' hy₂')
  have hβ : ⁅y', ⁅b', y₂'⁆⁆ ∈ B := E.D_mem H hb' hy' hy₂'
  have hβQ : ⁅y', ⁅b', y₂'⁆⁆ ∈ Q := H.B_le_Q hβ
  have h1 : ⁅y, ⁅y', ⁅b', y₂'⁆⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.center_Q hβ hy).symm
  rw [show ⁅b', y' * y₂'⁆ = ⁅b', y'⁆ * (⁅y', ⁅b', y₂'⁆⁆ * ⁅b', y₂'⁆) by
    simp only [commutatorElement_def]; group,
    H.comm_mul_right hy hu (Q.mul_mem hβQ hu₂), H.comm_mul_right hy hβQ hu₂, h1, one_mul]

theorem D_self (hb' : b' ∈ conjSubgroup g B) {y : G} (hy : y ∈ Q) : ⁅y, ⁅b', y⁆⁆ = 1 := by
  have hs : y * y ∈ B := by have := H.sq_mem hy; rwa [pow_two] at this
  have hsb : (y * y) * b' = b' * (y * y) := E.comm_L (E.B_le_L hs) (E.Bg_le_L hb')
  have hu : ⁅b', y⁆ * ⁅b', y⁆ = 1 := E.sq_C (E.u_mem hb' hy)
  have h2 : (y * y) * b'⁻¹ * (y * y)⁻¹ = b'⁻¹ := by
    have : (y * y) * b'⁻¹ = b'⁻¹ * (y * y) := by
      have := congrArg (fun z => b'⁻¹ * z * b'⁻¹) hsb
      simpa [mul_assoc] using this.symm
    rw [this]; group
  have key : y * ⁅b', y⁆ * y⁻¹ = ⁅b', y⁆ := by
    have e : y * ⁅b', y⁆ * y⁻¹ = (y * b' * y⁻¹) * ((y * y) * b'⁻¹ * (y * y)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, h2]
    have hinv : ⁅b', y⁆⁻¹ = ⁅b', y⁆ := inv_eq_of_mul_eq_one_right hu
    rw [← hinv]
    simp only [commutatorElement_def]; group
  calc ⁅y, ⁅b', y⁆⁆ = (y * ⁅b', y⁆ * y⁻¹) * ⁅b', y⁆⁻¹ := rfl
    _ = 1 := by rw [key]; exact mul_inv_cancel _

theorem exists_comm_eq (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) {β : G} (hβ : β ∈ B) :
    ∃ t ∈ T, ⁅b', t⁆ = β := by
  classical
  have hTB : ∀ t ∈ T, ⁅b', t⁆ ∈ B := fun t ht => E.T_comm t ht b' (E.Bg_le_L hb')
  let τ : T →* B :=
    { toFun := fun t => ⟨⁅b', (t : G)⁆, hTB t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun t t' => by
        refine Subtype.ext ?_
        have hc : (t : G) * ⁅b', (t' : G)⁆ = ⁅b', (t' : G)⁆ * (t : G) :=
          (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P t.2) _
            (H.B_le_P (hTB t' t'.2))).symm
        show ⁅b', (t : G) * (t' : G)⁆ = ⁅b', (t : G)⁆ * ⁅b', (t' : G)⁆
        rw [show ⁅b', (t : G) * (t' : G)⁆ =
          ⁅b', (t : G)⁆ * ((t : G) * ⁅b', (t' : G)⁆ * (t : G)⁻¹) by
            simp only [commutatorElement_def]; group, hc]
        group }
  have hker : τ.ker = (T ⊓ Subgroup.centralizer (L : Set G)).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : ⁅b', (t : G)⁆ = 1 := congrArg Subtype.val h
      refine ⟨t.2, ?_⟩
      have hbt : (t : G) * b' = b' * (t : G) :=
        (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      have hMg : (t : G) ∈ conjSubgroup g M :=
        H.centralizer_le_conj hb' hb'1 (Subgroup.mem_centralizer_singleton_iff.mpr hbt)
      have hnorm : (t : G) ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
        rw [H.normalizer_conj_eq g]; exact hMg
      have hBg : ∀ z ∈ conjSubgroup g B, z * (t : G) = (t : G) * z := by
        intro z hz
        have h2 : ⁅z, (t : G)⁆ ∈ conjSubgroup g B := by
          have e : ⁅z, (t : G)⁆ = z * ((t : G) * z⁻¹ * (t : G)⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (conjSubgroup g B).mul_mem hz
            ((Subgroup.mem_normalizer_iff.mp hnorm z⁻¹).mp ((conjSubgroup g B).inv_mem hz))
        have h3 : ⁅z, (t : G)⁆ ∈ B := E.T_comm t t.2 z (E.Bg_le_L hz)
        have h4 : ⁅z, (t : G)⁆ ∈ B ⊓ conjSubgroup g B := ⟨h3, h2⟩
        rw [inf_conjSubgroup_eq_bot_of_isTI H.ti (E.Bg_ne_B H), Subgroup.mem_bot] at h4
        exact commutatorElement_eq_one_iff_mul_comm.mp h4
      have hCt : ∀ c ∈ C, c * (t : G) = (t : G) * c := fun c hc =>
        Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P t.2) c (E.C_le_P hc)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      rw [E.hL] at hl
      obtain ⟨c, hc, z, hz, rfl⟩ := exists_mul_of_mem_sup
        (le_normalizer_of_comm fun x hx y hy => (E.C_cent y hy x hx).symm) hl
      calc c * z * (t : G) = c * (z * (t : G)) := by group
        _ = c * ((t : G) * z) := by rw [hBg z hz]
        _ = (c * (t : G)) * z := by group
        _ = ((t : G) * c) * z := by rw [hCt c hc]
        _ = (t : G) * (c * z) := by group
    · rintro ⟨-, h⟩
      refine Subtype.ext ?_
      have := Subgroup.mem_centralizer_iff.mp h b' (E.Bg_le_L hb')
      exact commutatorElement_eq_one_iff_mul_comm.mpr this
  have hrange : τ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.index_ker τ
    rw [hker] at h1
    have h2 : ((T ⊓ Subgroup.centralizer (L : Set G)).subgroupOf T).index = Nat.card B := E.T_rel
    rw [h2] at h1
    exact h1.symm
  have hmem : (⟨β, hβ⟩ : B) ∈ τ.range := by rw [hrange]; trivial
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

theorem mem_C_of_comm_mem_B (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) {p : G} (hp : p ∈ P)
    (h : ⁅b', p⁆ ∈ B) : p ∈ C := by
  obtain ⟨t, ht, htp⟩ := E.exists_comm_eq H hb' hb'1 h
  set y := p⁻¹ * t with hy
  have hyQ : y ∈ Q := Q.mul_mem (Q.inv_mem (H.P_le_Q hp)) (H.T_le_Q ht)
  have e1 : t * b'⁻¹ * t⁻¹ = b'⁻¹ * ⁅b', t⁆ := by simp only [commutatorElement_def]; group
  have e2 : p * b'⁻¹ * p⁻¹ = b'⁻¹ * ⁅b', p⁆ := by simp only [commutatorElement_def]; group
  have hyb : y * b'⁻¹ * y⁻¹ = b'⁻¹ := by
    calc y * b'⁻¹ * y⁻¹ = p⁻¹ * (t * b'⁻¹ * t⁻¹) * p := by simp only [hy]; group
      _ = p⁻¹ * (p * b'⁻¹ * p⁻¹) * p := by rw [e1, htp, ← e2]
      _ = b'⁻¹ := by group
  have hcomm : y * b' = b' * y := by
    have h3 : y * b' * y⁻¹ = b' := by
      have := congrArg (fun z => z⁻¹) hyb
      simpa [mul_assoc] using this
    calc y * b' = (y * b' * y⁻¹) * y := by group
      _ = b' * y := by rw [h3]
  have hMg : y ∈ conjSubgroup g M :=
    H.centralizer_le_conj hb' hb'1 (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hnorm : y ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
    rw [H.normalizer_conj_eq g]; exact hMg
  have hycent : ∀ z ∈ conjSubgroup g B, y * z = z * y := by
    intro z hz
    have h1 : ⁅z, y⁆ ∈ conjSubgroup g B := by
      have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup g B).mul_mem hz
        ((Subgroup.mem_normalizer_iff.mp hnorm z⁻¹).mp ((conjSubgroup g B).inv_mem hz))
    have h2 : ⁅z, y⁆ ∈ C := by
      have := C.inv_mem (E.Q_comm y hyQ z (E.Bg_le_L hz))
      rwa [commutatorElement_inv] at this
    have h4 : ⁅z, y⁆ ∈ C ⊓ conjSubgroup g B := ⟨h2, h1⟩
    rw [E.C_inf, Subgroup.mem_bot] at h4
    exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm
  rw [E.hC]
  refine ⟨hp, fun z hz => ?_⟩
  have hpz : ⁅p, z⁆ = ⁅t, z⁆ := by
    have hpt : p = t * y⁻¹ := by simp only [hy]; group
    have hyz : y⁻¹ * z * y = z := by
      have := hycent z hz
      calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
        _ = y⁻¹ * (y * z) := by rw [this]
        _ = z := by group
    calc ⁅p, z⁆ = p * z * p⁻¹ * z⁻¹ := rfl
      _ = t * (y⁻¹ * z * y) * t⁻¹ * z⁻¹ := by rw [hpt]; group
      _ = ⁅t, z⁆ := by rw [hyz]; rfl
  rw [hpz]
  have := B.inv_mem (E.T_comm t ht z (E.Bg_le_L hz))
  rwa [commutatorElement_inv] at this

omit H in
theorem u_mul_C_right (hb' : b' ∈ conjSubgroup g B) {y c : G} (hc : c ∈ C) :
    ⁅b', y * c⁆ = ⁅b', y⁆ := by
  have hbc : ⁅b', c⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (E.C_cent c hc b' hb').symm
  rw [show ⁅b', y * c⁆ = ⁅b', y⁆ * (⁅y, ⁅b', c⁆⁆ * ⁅b', c⁆) by
    simp only [commutatorElement_def]; group, hbc]
  simp

theorem D_mul_C_left (hb' : b' ∈ conjSubgroup g B) {y c y' : G} (hy : y ∈ Q) (hc : c ∈ C)
    (hy' : y' ∈ Q) : ⁅y * c, ⁅b', y'⁆⁆ = ⁅y, ⁅b', y'⁆⁆ := by
  rw [E.D_mul_left H hb' hy (E.C_le_Q H hc) hy']
  have : ⁅c, ⁅b', y'⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (E.comm_C hc (E.u_mem hb' hy'))
  rw [this, mul_one]

omit H in
theorem D_mul_C_right (hb' : b' ∈ conjSubgroup g B) {y y' c : G} (hc : c ∈ C) :
    ⁅y, ⁅b', y' * c⁆⁆ = ⁅y, ⁅b', y'⁆⁆ := by
  rw [E.u_mul_C_right hb' hc]

end Form

end EndgameData

end CFSG.RankThree.GF2n.Tim78
