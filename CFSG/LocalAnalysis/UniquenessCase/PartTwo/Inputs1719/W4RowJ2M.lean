module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLiftEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ2Pack
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLiftGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Quasithin.B45Exc.HSRu CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

namespace W4Row

private theorem j2_orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

private theorem j2_ep2Line_mem {x₁ x₂ : Equiv.Perm (Fin 315)} (hx₁ : x₁ ∈ j2P)
    (hx₂ : x₂ ∈ j2P) : ∀ i, ep2Line x₁ x₂ i ∈ j2P
  | 0 => hx₂
  | i + 1 => j2P.mul_mem hx₁ (j2P.pow_mem hx₂ i)

private theorem j2_map_ep2Line {W : Type} [CommGroup W] {ψ : ↥j2P →* MulAut W}
    (P₁ P₂ : ↥j2P) : ∀ i, ψ (ep2Line P₁ P₂ i) = ep2Line (ψ P₁) (ψ P₂) i := by
  intro n
  cases n with
  | zero => rfl
  | succ i => simp only [ep2Line, map_mul, map_pow]

private theorem j2_ep2Line_coe (P₁ P₂ : ↥j2P) :
    ∀ i, ((ep2Line P₁ P₂ i : ↥j2P) : Equiv.Perm (Fin 315)) =
      ep2Line (P₁ : Equiv.Perm (Fin 315)) (P₂ : Equiv.Perm (Fin 315)) i := by
  intro n
  cases n with
  | zero => rfl
  | succ i => simp only [ep2Line, Subgroup.coe_mul, Subgroup.coe_pow]

private theorem j2_ep2Line_pow_five {G : Type*} [Group G] {a b : G}
    (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hab : a * b = b * a) :
    ∀ i, ep2Line a b i ^ 5 = 1 := by
  intro n
  cases n with
  | zero => simpa [ep2Line] using hb
  | succ i =>
    have hbi : (b ^ i) ^ 5 = 1 := by
      rw [show (b ^ i) ^ 5 = b ^ (i * 5) from (pow_mul b i 5).symm]
      rw [show i * 5 = 5 * i by ring, pow_mul, hb, one_pow]
    have hc : (a * b ^ i) ^ 5 = a ^ 5 * (b ^ i) ^ 5 :=
      (show Commute a b from hab).pow_right i |>.mul_pow 5
    rw [ep2Line, hc, ha, hbi, mul_one]

private theorem j2_zpowers_pow_two_of_pow_five {G : Type*} [Group G] {g : G}
    (h : g ^ 5 = 1) : Subgroup.zpowers (g ^ 2) = Subgroup.zpowers g := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2
  · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    refine ⟨3, ?_⟩
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    calc (g ^ 2) ^ 3 = g ^ (2 * 3) := (pow_mul g 2 3).symm
      _ = g ^ 5 * g := by rw [show 2 * 3 = 5 + 1 by norm_num, pow_succ]
      _ = g := by rw [h, one_mul]

private theorem j2_line_index_eq {W : Type} [CommGroup W] {ψ : ↥j2P →* MulAut W}
    {x₁ x₂ : Equiv.Perm (Fin 315)} (hx₁ : x₁ ∈ j2P) (hx₂ : x₂ ∈ j2P)
    (hline : ∀ i, ψ (ep2Line (⟨x₁, hx₁⟩ : ↥j2P) (⟨x₂, hx₂⟩ : ↥j2P) i) =
      ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) i)
    (ha : (ψ ⟨x₁, hx₁⟩) ^ 5 = 1) (hb : (ψ ⟨x₂, hx₂⟩) ^ 5 = 1)
    (hab : ψ ⟨x₁, hx₁⟩ * ψ ⟨x₂, hx₂⟩ = ψ ⟨x₂, hx₂⟩ * ψ ⟨x₁, hx₁⟩)
    {m : Equiv.Perm (Fin 315)} (hm : m ∈ j2P) {i j e : ℕ}
    (he : e = 1 ∨ e = 2)
    (hme : m * ep2Line x₁ x₂ i * m⁻¹ = ep2Line x₁ x₂ j ^ e) :
    (fixV (zpowers (ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) j))).index =
      (fixV (zpowers (ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) i))).index := by
  have hmi := j2_ep2Line_mem hx₁ hx₂ i
  have hmj := j2_ep2Line_mem hx₁ hx₂ j
  have hidx := index_fixV_hom_conj ψ (⟨ep2Line x₁ x₂ i, hmi⟩ : ↥j2P)
    (⟨ep2Line x₁ x₂ j ^ e, j2P.pow_mem hmj e⟩ : ↥j2P) hm (by simpa using hme)
  have hPi : ψ (⟨ep2Line x₁ x₂ i, hmi⟩ : ↥j2P) =
      ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) i := by
    rw [show (⟨ep2Line x₁ x₂ i, hmi⟩ : ↥j2P) =
      ep2Line (⟨x₁, hx₁⟩ : ↥j2P) (⟨x₂, hx₂⟩ : ↥j2P) i from
        Subtype.ext (by rw [j2_ep2Line_coe])]
    exact hline i
  have hPj : ψ (⟨ep2Line x₁ x₂ j ^ e, j2P.pow_mem hmj e⟩ : ↥j2P) =
      (ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) j) ^ e := by
    rw [show (⟨ep2Line x₁ x₂ j ^ e, j2P.pow_mem hmj e⟩ : ↥j2P) =
      (ep2Line (⟨x₁, hx₁⟩ : ↥j2P) (⟨x₂, hx₂⟩ : ↥j2P) j) ^ e from
        Subtype.ext (by rw [Subgroup.coe_pow, j2_ep2Line_coe])]
    rw [map_pow, hline j]
  rw [hPi, hPj] at hidx
  rcases he with rfl | rfl
  · simpa using hidx
  · have h5 : (ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) j) ^ 5 = 1 :=
      j2_ep2Line_pow_five ha hb hab j
    rw [j2_zpowers_pow_two_of_pow_five h5] at hidx
    simpa using hidx

private theorem j2_e25_index {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {ψ : ↥j2P →* MulAut W} (hψ : Function.Injective ψ)
    {x₁ x₂ : Equiv.Perm (Fin 315)} (hx₁ : x₁ ∈ j2P) (hx₂ : x₂ ∈ j2P)
    (h51 : x₁ ^ 5 = 1) (h52 : x₂ ^ 5 = 1) (hne : x₁ ≠ 1) (hcomm : x₁ * x₂ = x₂ * x₁)
    (hba : ∀ j < 5, x₂ ≠ x₁ ^ j)
    (hpart : ∀ i ≤ 5, ∃ j ≤ 5, ∃ k ≤ 5, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        m * ep2Line x₁ x₂ i * m⁻¹ = ep2Line x₁ x₂ j ^ e) ∧
      (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        m * ep2Line x₁ x₂ i * m⁻¹ = ep2Line x₁ x₂ k ^ e)) :
    (∀ i ≤ 5, 2 ^ 8 ≤
      (fixV (zpowers (ep2Line (ψ ⟨x₁, hx₁⟩) (ψ ⟨x₂, hx₂⟩) i))).index) ∧
    2 ^ 12 ≤ (fixV (zpowers (ψ ⟨x₁, hx₁⟩) ⊔ zpowers (ψ ⟨x₂, hx₂⟩))).index := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P₁ : ↥j2P := ⟨x₁, hx₁⟩
  let P₂ : ↥j2P := ⟨x₂, hx₂⟩
  have ha : (ψ P₁) ^ 5 = 1 := by
    rw [← map_pow, show P₁ ^ 5 = 1 from Subtype.ext (by simpa using h51), map_one]
  have hb : (ψ P₂) ^ 5 = 1 := by
    rw [← map_pow, show P₂ ^ 5 = 1 from Subtype.ext (by simpa using h52), map_one]
  have ha1 : ψ P₁ ≠ 1 := fun h =>
    hne (congrArg Subtype.val (hψ (h.trans (map_one ψ).symm)))
  have hab : ψ P₁ * ψ P₂ = ψ P₂ * ψ P₁ := by
    rw [← map_mul, ← map_mul, show P₁ * P₂ = P₂ * P₁ from Subtype.ext hcomm]
  have hba' : ∀ j < 5, ψ P₂ ≠ (ψ P₁) ^ j := fun j hj h =>
    hba j hj (by simpa using congrArg Subtype.val (hψ (h.trans (map_pow ψ P₁ j).symm)))
  have hline := j2_map_ep2Line (W := W) (ψ := ψ) P₁ P₂
  have hpart' : ∀ i ≤ 5, ∃ j ≤ 5, ∃ k ≤ 5, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (fixV (zpowers (ep2Line (ψ P₁) (ψ P₂) j))).index =
        (fixV (zpowers (ep2Line (ψ P₁) (ψ P₂) i))).index ∧
      (fixV (zpowers (ep2Line (ψ P₁) (ψ P₂) k))).index =
        (fixV (zpowers (ep2Line (ψ P₁) (ψ P₂) i))).index := by
    intro i hi
    obtain ⟨j, hj, k, hk, hji, hki, hjk,
      ⟨m, hm, e, he, hme⟩, ⟨m', hm', e', he', hm'e⟩⟩ := hpart i hi
    exact ⟨j, hj, k, hk, hji, hki, hjk,
      j2_line_index_eq (W := W) hx₁ hx₂ hline ha hb hab hm he hme,
      j2_line_index_eq (W := W) hx₁ hx₂ hline ha hb hab hm' he' hm'e⟩
  have h := two_pow_le_index_of_ep2_partners (W := W) (p := 5) (a := ψ P₁) (b := ψ P₂)
    hW (by norm_num) ha hb ha1 hab hba' hpart'
  rw [j2_orderOf_two_zmod_five] at h
  refine ⟨fun i hi => ?_, ?_⟩
  · simpa [P₁, P₂] using h.1 i hi
  · simpa [P₁, P₂] using h.2

private theorem j2_inner_case {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (ψL : Lift L Y j2R j2P)
    {x₁ : Equiv.Perm (Fin 315)} (hx₁ : x₁ ∈ j2P) (h51 : x₁ ^ 5 = 1)
    (hP₁ : 2 ^ 8 ≤ (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩))).index)
    (ht : t ∈ Y) (ht2 : t * t = 1)
    (hinv : ∀ s ∈ [tp 315 (j2CentTbl 17), tp 315 (j2CentTbl 31)], ∃ h ∈ j2P,
      s * (h * x₁ * h⁻¹) * s⁻¹ = (h * x₁ * h⁻¹)⁻¹)
    {g : Equiv.Perm (Fin 315)} (hg : g ∈ j2P) {ρ : ClassRow}
    (hrep : ρ.rep = j2CentTbl 17 ∨ ρ.rep = j2CentTbl 31)
    (hgρ : (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 315)) =
      g * tp 315 ρ.rep * g⁻¹) :
    2 ^ 8 ≤ (fixV (zpowers t)).index ^ 2 := by
  have hrow : tp 315 ρ.rep ∈ [tp 315 (j2CentTbl 17), tp 315 (j2CentTbl 31)] := by
    rcases hrep with h | h <;> rw [h] <;> simp
  obtain ⟨h, hh, hhinv⟩ := hinv (tp 315 ρ.rep) hrow
  let c : ↥j2P := ⟨g * h, j2P.mul_mem hg hh⟩
  let p : ↥j2P := c * ⟨x₁, hx₁⟩ * c⁻¹
  have hp_coe : (p : Equiv.Perm (Fin 315)) = g * (h * x₁ * h⁻¹) * g⁻¹ := by
    simp only [p, c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hconj : (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 315)) *
      (p : Equiv.Perm (Fin 315)) *
      (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 315))⁻¹ =
      (p : Equiv.Perm (Fin 315))⁻¹ := by
    rw [hgρ, hp_coe]
    calc (g * tp 315 ρ.rep * g⁻¹) * (g * (h * x₁ * h⁻¹) * g⁻¹) *
          (g * tp 315 ρ.rep * g⁻¹)⁻¹
        = g * (tp 315 ρ.rep * (h * x₁ * h⁻¹) * (tp 315 ρ.rep)⁻¹) * g⁻¹ := by
          group
      _ = g * (h * x₁ * h⁻¹)⁻¹ * g⁻¹ := by rw [hhinv]
      _ = (g * (h * x₁ * h⁻¹) * g⁻¹)⁻¹ := by group
  have htp : t * psiOfLift ψL p * t⁻¹ = (psiOfLift ψL p)⁻¹ :=
    conj_psiOfLift_eq_inv j2P_le_R ψL ht hconj
  have hp5 : (psiOfLift ψL p) ^ 5 = 1 := by
    have hp : p ^ 5 = 1 := by
      have hPP : p = c * ⟨x₁, hx₁⟩ * c⁻¹ := rfl
      rw [hPP, conj_pow, show (⟨x₁, hx₁⟩ : ↥j2P) ^ 5 = 1 from Subtype.ext (by simpa using h51)]
      group
    rw [← map_pow, hp, map_one]
  have hzidx : (fixV (zpowers (psiOfLift ψL p))).index =
      (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩))).index := by
    change (fixV (zpowers (psiOfLift ψL (c * ⟨x₁, hx₁⟩ * c⁻¹)))).index = _
    rw [map_mul, map_mul, map_inv]
    rw [index_fixV_conj (psiOfLift ψL c) (psiOfLift ψL ⟨x₁, hx₁⟩)]
  have hsq := index_fixV_le_sq_of_inverts (W := W) (p := 5) (by norm_num) hp5 ht2 htp
  calc 2 ^ 8 ≤ (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩))).index := hP₁
    _ = (fixV (zpowers (psiOfLift ψL p))).index := hzidx.symm
    _ ≤ (fixV (zpowers t)).index ^ 2 := hsq

private theorem j2_outer_case {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (ψL : Lift L Y j2R j2P)
    {x₁ x₂ : Equiv.Perm (Fin 315)} (hx₁ : x₁ ∈ j2P) (hx₂ : x₂ ∈ j2P)
    (hX : 2 ^ 12 ≤ (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩) ⊔
      zpowers (psiOfLift ψL ⟨x₂, hx₂⟩))).index)
    (hsupL : zpowers (psiOfLift ψL ⟨x₁, hx₁⟩) ⊔
      zpowers (psiOfLift ψL ⟨x₂, hx₂⟩) ≤ L)
    (ht : t ∈ Y)
    (hgen : GenSet j2P 3 {tp 315 (j2CentTbl 9)})
    {g : Equiv.Perm (Fin 315)} (hg : g ∈ j2P) {ρ : ClassRow}
    (hrep : ρ.rep = j2CentTbl 9)
    (hgρ : (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 315)) =
      g * tp 315 ρ.rep * g⁻¹) :
    2 ^ 8 ≤ (fixV (zpowers t)).index ^ 2 := by
  have hgenr : GenSet j2P 3 {tp 315 ρ.rep} := by
    rw [hrep]
    exact hgen
  have htransfer : GenSet j2P 3
      {((ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : ↥j2R) :
        Equiv.Perm (Fin 315))} := by
    refine GenSet.transfer (s := g⁻¹) ?_ ?_ ?_ hgenr
    · intro p hp
      simpa [mul_assoc] using j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hp) hg
    · intro p hp
      simpa [mul_assoc] using j2P.mul_mem (j2P.mul_mem hg hp) (j2P.inv_mem hg)
    · intro t' ht'
      rw [Set.mem_singleton_iff] at ht'
      rw [ht', inv_inv, ← hgρ]
      exact Subgroup.subset_closure (by simp)
  have hLidx := index_fixV_le_pow_of_genSet ψL ht htransfer
  have hanti : (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩) ⊔
      zpowers (psiOfLift ψL ⟨x₂, hx₂⟩))).index ≤ (fixV L).index :=
    Subgroup.index_antitone (CFSG.QuasithinUnique.Setup.X1.fixV_anti hsupL)
  have hbig : 2 ^ 12 ≤ (fixV (zpowers t)).index ^ 3 :=
    hX.trans (hanti.trans hLidx)
  have hn : 16 ≤ (fixV (zpowers t)).index := by
    refine (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).1 ?_
    calc (16 : ℕ) ^ 3 = 4096 := by norm_num
      _ = 2 ^ 12 := by norm_num
      _ ≤ (fixV (zpowers t)).index ^ 3 := hbig
  calc 2 ^ 8 = 16 ^ 2 := by norm_num
    _ ≤ (fixV (zpowers t)).index ^ 2 := Nat.pow_le_pow_left hn 2

private theorem j2_inv_index_sq
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J2)
    (hZ : Subgroup.center ↥L = ⊥) {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    2 ^ 8 ≤ (fixV (zpowers t)).index ^ 2 := by
  obtain ⟨Φ, hΦ⟩ := j2_aut_model
  let ψL : Lift L Y j2R j2P :=
    liftOfFstar hLY hF hperf hY e₀ hZ j2P_le_R Φ j2EquivC hΦ
  obtain ⟨x₁, hx₁, x₂, hx₂, h51, h52, hne, hcomm, hba, hpart, hinv, hgen⟩ :=
    j2_e25_package
  have he25 := j2_e25_index (W := W) (ψ := psiOfLift ψL) hW (psiOfLift_injective ψL)
    hx₁ hx₂ h51 h52 hne hcomm hba hpart
  have hP₁ : 2 ^ 8 ≤ (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩))).index := by
    simpa [ep2Line] using he25.1 1 (by norm_num)
  have hX : 2 ^ 12 ≤ (fixV (zpowers (psiOfLift ψL ⟨x₁, hx₁⟩) ⊔
      zpowers (psiOfLift ψL ⟨x₂, hx₂⟩))).index := he25.2
  have hsupL : zpowers (psiOfLift ψL ⟨x₁, hx₁⟩) ⊔
      zpowers (psiOfLift ψL ⟨x₂, hx₂⟩) ≤ L :=
    sup_le (Subgroup.zpowers_le.2 (psiOfLift_mem ψL ⟨x₁, hx₁⟩))
      (Subgroup.zpowers_le.2 (psiOfLift_mem ψL ⟨x₂, hx₂⟩))
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  let t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right ht⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa [t'] using ht2)
  let r : ↥j2R := ψL.hom t'
  have hr2 : (r : Equiv.Perm (Fin 315)) ^ 2 = 1 := by
    have h : r * r = 1 := by
      change ψL.hom t' * ψL.hom t' = 1
      rw [← map_mul, ht'2, map_one]
    rw [sq]
    exact congrArg (fun x : ↥j2R => (x : Equiv.Perm (Fin 315))) h
  have hr1 : (r : Equiv.Perm (Fin 315)) ≠ 1 := by
    intro h
    have h1 : ψL.hom t' = 1 := Subtype.ext h
    have h2 : t' = 1 := ψL.inj (by rw [h1, map_one])
    have h3 : t = 1 := by
      simpa [t'] using congrArg (fun x : ↥(L ⊔ Y) => (x : MulAut W)) h2
    rw [h3, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hro : orderOf (r : Equiv.Perm (Fin 315)) = 2 := orderOf_eq_prime hr2 hr1
  obtain ⟨ρ, hρ, g, hg, hgρ⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.1
      (r : Equiv.Perm (Fin 315)) r.2 hro
  have hgρ' : (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 315)) =
      g * tp 315 ρ.rep * g⁻¹ := by simpa [r, t'] using hgρ
  rcases rows_cases ρ hρ with hrep | hrep | hrep
  · exact j2_outer_case ψL hx₁ hx₂ hX hsupL ht hgen hg hrep hgρ'
  · exact j2_inner_case ψL hx₁ h51 hP₁ ht ht2 hinv hg (Or.inl hrep) hgρ'
  · exact j2_inner_case ψL hx₁ h51 hP₁ ht ht2 hinv hg (Or.inr hrep) hgρ'

end W4Row

theorem w4Thm11_1RowM_J2_holds :
    W4Thm11_1RowM .J2 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hZ : Subgroup.center ↥L = ⊥ :=
    W4Row.center_eq_bot_of_o2Trivial_of_cover hq.1 hO2 e₀ j2_cover
  have hcard : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  obtain ⟨t₀, ht₀, ht₀o⟩ := W4Row.exists_orderOf_eq_two_of_cq e₀ (by rw [hcard]; norm_num)
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  show tableM .J2 ≤ E3.mParam Y
  rw [show tableM .J2 = 4 from rfl]
  exact W4Row.le_mParam_of_index_sq hW' ⟨t₀, hLY ht₀, ht₀o⟩ fun t ht hto =>
    W4Row.j2_inv_index_sq hW' hLY hF hq.1 hY e₀ hZ ht hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
