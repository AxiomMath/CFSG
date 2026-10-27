module

public import CFSG.Timmesfeld.Transvection.ModelSUTransvLe
import CFSG.RankThree.GF2n.Tim79aSUGenCriterion
public import CFSG.Timmesfeld.Transvection.ModelSUTheta

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open Matrix CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Field

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def transvGroup (σ : F ≃+* F) (n : ℕ) (v : Fin n → F) : Subgroup (SU σ n) :=
  Subgroup.closure {x | ∃ c, c + σ c = 0 ∧ suMat σ n x = uTrans σ v c}

theorem isUTransGroup_transvGroup (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F}
    (hv : uForm σ v v = 0) : IsUTransGroup σ v (transvGroup σ n v) := by
  obtain ⟨X, hX⟩ := exists_isUTransGroup hσ hv
  have hXe : transvGroup σ n v = X := by
    refine le_antisymm ((Subgroup.closure_le X).2 fun x hx => (hX.1 x).2 hx) fun x hx => ?_
    exact Subgroup.subset_closure ((hX.1 x).1 hx)
  rw [hXe]
  exact hX

theorem transvGroup_eq (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} (hv : uForm σ v v = 0)
    {X : Subgroup (SU σ n)} (hX : IsUTransGroup σ v X) : transvGroup σ n v = X :=
  (isUTransGroup_transvGroup hσ hv).eq hX

theorem transvGroup_smul (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} (hv : uForm σ v v = 0)
    {l : F} (hl : l ≠ 0) : transvGroup σ n (l • v) = transvGroup σ n v := by
  have hlv : uForm σ (l • v) (l • v) = 0 := by
    rw [uForm_smul_left, uForm_smul_right, hv, mul_zero, mul_zero]
  exact (transvGroup_eq hσ hv
    (IsUTransGroup.of_smul hσ hl (isUTransGroup_transvGroup hσ hlv))).symm

theorem conjSub_transvGroup (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} (hv : uForm σ v v = 0)
    (g : SU σ n) : conjSub (transvGroup σ n v) g = transvGroup σ n (suMat σ n g *ᵥ v) := by
  have hgv : uForm σ (suMat σ n g *ᵥ v) (suMat σ n g *ᵥ v) = 0 := by rw [uForm_mulVec, hv]
  exact ((isUTransGroup_transvGroup hσ hv).conjSub g).eq (isUTransGroup_transvGroup hσ hgv)

variable [CharP F 2]

theorem mul_self_eq_one_of_mem_transvGroup (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F}
    (hv : uForm σ v v = 0) {x : SU σ n} (hx : x ∈ transvGroup σ n v) : x * x = 1 := by
  obtain ⟨c, -, hxc⟩ := ((isUTransGroup_transvGroup hσ hv).1 x).1 hx
  apply suMat_injective σ
  rw [map_mul, hxc, uTrans_mul_uTrans σ hv, CharTwo.add_self_eq_zero, uTrans_zero, map_one]

theorem isPGroup_transvGroup (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} (hv : uForm σ v v = 0) :
    IsPGroup 2 (transvGroup σ n v) := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, sq]
  exact Subtype.ext (mul_self_eq_one_of_mem_transvGroup hσ hv x.2)

theorem exists_ne_zero_of_mem_transvGroup (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F}
    (hv : uForm σ v v = 0) {x : SU σ n} (hx : x ∈ transvGroup σ n v) (hx1 : x ≠ 1) :
    ∃ c : F, c ≠ 0 ∧ c + σ c = 0 ∧ ∀ u, suMat σ n x *ᵥ u = u + (c * uForm σ v u) • v := by
  obtain ⟨c, hc, hxc⟩ := ((isUTransGroup_transvGroup hσ hv).1 x).1 hx
  refine ⟨c, fun h0 => hx1 ?_, hc, fun u => by rw [hxc, uTrans_mulVec]⟩
  apply suMat_injective σ
  rw [hxc, h0, uTrans_zero, map_one]

theorem exists_mem_transvGroup_ne_one (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F}
    (hv : uForm σ v v = 0) (hv0 : v ≠ 0) : ∃ x ∈ transvGroup σ n v, x ≠ 1 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hT := isUTransGroup_transvGroup hσ hv
  obtain ⟨x, hx⟩ := hT.2 1 h1
  refine ⟨x, (hT.1 x).2 ⟨1, h1, hx⟩, fun hx1 => ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (uRow_ne_zero σ hv0)
  have h := congrFun (congrFun hx i) j
  rw [hx1, map_one, uTrans, Matrix.add_apply, Matrix.smul_apply, uNil, vecMulVec_apply,
    one_smul, left_eq_add] at h
  exact mul_ne_zero hi hj h

theorem exists_mem_sup_conjSub_eq (hσ : ∀ c, σ (σ c) = c) {a z : Fin n → F}
    (haa : uForm σ a a = 0) (hzz : uForm σ z z = 0) (haz : uForm σ a z = 1)
    {Ta Tz : Subgroup (SU σ n)} (hTa : IsUTransGroup σ a Ta) (hTz : IsUTransGroup σ z Tz) :
    ∃ w ∈ Ta ⊔ Tz, conjSub Ta w = Tz := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  obtain ⟨x, hx⟩ := hTa.2 1 h1
  obtain ⟨y, hy⟩ := hTz.2 1 h1
  have hxT : x ∈ Ta := (hTa.1 x).2 ⟨1, h1, hx⟩
  have hyT : y ∈ Tz := (hTz.1 y).2 ⟨1, h1, hy⟩
  have hza : uForm σ z a = 1 := uForm_swap_eq_one hσ haz
  have haa2 : a + a = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, CharTwo.add_self_eq_zero]
  have e1 : uTrans σ a 1 *ᵥ a = a := by
    rw [uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
  have e2 : uTrans σ z 1 *ᵥ a = a + z := by
    rw [uTrans_mulVec, hza, mul_one, one_smul]
  have e3 : uTrans σ a 1 *ᵥ (a + z) = z := by
    rw [uTrans_mulVec, uForm_add_right, haa, haz, zero_add, mul_one, one_smul, add_comm a z,
      add_assoc, haa2, add_zero]
  refine ⟨x * y * x, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hxT)
    (Subgroup.mem_sup_right hyT)) (Subgroup.mem_sup_left hxT), ?_⟩
  have hmv : suMat σ n (x * y * x) *ᵥ a = z := by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, e1, e2, e3]
  have h := hTa.conjSub (x * y * x)
  rw [hmv] at h
  exact h.eq hTz

end Field

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem eq_top_of_uTransLe_outer (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    {L : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (h0 : UTransLe L (Pi.single 0 1)) (hlast : UTransLe L (Pi.single (Fin.last (m + 1)) 1))
    (hP : ∀ v : Fin (m + 2) → F, uForm (unitaryInvolution F 2 f) v v = 0 →
      uForm (unitaryInvolution F 2 f) (Pi.single 0 1) v = 0 → UTransLe L v) : L = ⊤ := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨l, hl⟩ := exists_add_unitaryInvolution_eq hF (a := 1) (map_one _)
  set a : Fin (m + 2) → F := Pi.single 0 1 with hadef
  set d : Fin (m + 2) → F := Pi.single (Fin.last (m + 1)) 1 with hddef
  set i₁ : Fin (m + 2) := ⟨1, by omega⟩ with hi₁
  set w₀ : Fin (m + 2) → F := Pi.single i₁ 1 with hw₀def
  have h0l : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have hl0 : Fin.last (m + 1) ≠ Fin.rev (Fin.last (m + 1)) := by
    rw [Fin.rev_last]
    intro h
    have := congrArg Fin.val h
    simp at this
  have hi₁r : i₁ ≠ Fin.rev i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁, Fin.val_rev] at this
    omega
  have haa : uForm (unitaryInvolution F 2 f) a a = 0 := uForm_single_self h0l
  have hdd : uForm (unitaryInvolution F 2 f) d d = 0 := uForm_single_self hl0
  have had : uForm (unitaryInvolution F 2 f) a d = 1 := by
    rw [hadef, hddef, uForm_single_left, Fin.rev_zero, Pi.single_eq_same]
  have ha_x : ∀ x : Fin (m + 2) → F, uForm (unitaryInvolution F 2 f) a x = x (Fin.last (m + 1)) :=
    fun x => by rw [hadef, uForm_single_left, Fin.rev_zero]
  have hd_x : ∀ x : Fin (m + 2) → F, uForm (unitaryInvolution F 2 f) d x = x 0 :=
    fun x => by rw [hddef, uForm_single_left, Fin.rev_last]
  have hi₁0 : i₁ ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁] at this
  have hi₁l : i₁ ≠ Fin.last (m + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁] at this
    omega
  have hw₀ : w₀ ∈ perpPair (unitaryInvolution F 2 f) a d :=
    ⟨by rw [ha_x, hw₀def, Pi.single_eq_of_ne hi₁l.symm],
      by rw [hd_x, hw₀def, Pi.single_eq_of_ne hi₁0.symm]⟩
  have hw₀0 : w₀ ≠ 0 := single_one_ne_zero i₁
  have hw₀w₀ : uForm (unitaryInvolution F 2 f) w₀ w₀ = 0 := uForm_single_self hi₁r
  have haw : uForm (unitaryInvolution F 2 f) a w₀ = 0 := hw₀.1
  have hwa : uForm (unitaryInvolution F 2 f) w₀ a = 0 := uForm_eq_zero_comm hσ hw₀.1
  have hsum_iso : ∀ c : F, uForm (unitaryInvolution F 2 f) (a + c • w₀) (a + c • w₀) = 0 := by
    intro c
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hw₀w₀,
      haw, hwa, mul_zero, add_zero]
  have hsum_perp : ∀ c : F, uForm (unitaryInvolution F 2 f) a (a + c • w₀) = 0 := by
    intro c
    rw [uForm_add_right, uForm_smul_right, haa, haw, mul_zero, add_zero]
  have hLw : UTransLe L w₀ := hP w₀ hw₀w₀ haw
  have hL1 : UTransLe L (a + (1 : F) • w₀) := hP _ (hsum_iso 1) (hsum_perp 1)
  have hLl : UTransLe L (a + l • w₀) := hP _ (hsum_iso l) (hsum_perp l)
  refine eq_top_of_uTransLe_pair hF (by omega) haa hdd had hw₀ hw₀0 hw₀w₀ h0 hlast
    (fun v hv hvv => hP v hvv hv.1) ?_
  intro ν
  obtain ⟨c₂, hc₂def⟩ : ∃ c : F, c = ν + unitaryInvolution F 2 f ν := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁def⟩ : ∃ c : F, c = ν + c₂ * l := ⟨_, rfl⟩
  have hσc₂ : unitaryInvolution F 2 f c₂ = c₂ := by rw [hc₂def, map_add, hσ, add_comm]
  have hc₂ : c₂ + unitaryInvolution F 2 f c₂ = 0 := by
    rw [hσc₂]; exact CharTwo.add_self_eq_zero c₂
  have hc₁ : c₁ + unitaryInvolution F 2 f c₁ = 0 := by
    rw [hc₁def, map_add, map_mul, hσc₂]
    grind
  obtain ⟨z₁, hz₁L, hz₁⟩ := exists_mem_eichler_of_uTransLe hσ haa hw₀w₀ haw h0 hLw hL1 hc₁
  obtain ⟨z₂, hz₂L, hz₂⟩ := exists_mem_eichler_of_uTransLe hσ haa hw₀w₀ haw h0 hLw hLl hc₂
  obtain ⟨hz₁R, hz₁v⟩ := eichler_mem_uRad_radVec hσ haa hdd had hw₀ hz₁
  obtain ⟨hz₂R, hz₂v⟩ := eichler_mem_uRad_radVec hσ haa hdd had hw₀ hz₂
  refine ⟨z₁ * z₂, L.mul_mem hz₁L hz₂L, (uRad _ _).mul_mem hz₁R hz₂R, ?_⟩
  rw [radVec_mul_of_mem_uRad hσ haa hdd had hz₁R hz₂R, hz₁v, hz₂v, ← add_smul]
  congr 1
  rw [hc₁def]
  grind

end Finite

end CFSG.RankThree.GF2n.Tim81.TIModule
