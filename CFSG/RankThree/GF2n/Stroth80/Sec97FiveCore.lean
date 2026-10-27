module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FivePoint
public import CFSG.RankThree.GF2n.Stroth80.CarterSec97K5
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
import CFSG.GroupTheory.ClassTwoCommutator
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Schur

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

private theorem T_le_Wt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T) :
    T ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
  hK5.t_le_sum.trans (sup_le (HS6.Vt_le_Wt h34 hc hs.toSec5) inf_le_left)

private theorem comm_mem_ulineX (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {T : Subgroup G}
    (hK5 : Sec97K5 M Q Z B hc t T) (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y))
    {x : G} (hxX : x ∈ X) {τ : G} (hτT : τ ∈ T) :
    ⁅x, τ⁆ ∈ Uline Z B X := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, -, -, -, hcomm⟩, -, hcommV⟩ := hsplit0
  have hTQ : T ≤ Q := (T_le_Wt h34 hc hs hK5).trans inf_le_left
  have hτQ : τ ∈ Q := hTQ hτT
  have hτW : τ ∈ Wt Q (Vt M (LB M Q B) B Z t) := T_le_Wt h34 hc hs hK5 hτT
  have hxM : x ∈ M := hc.Rt_le_M t (hXR hxX)
  refine mem_ulineX_of_fix h34 h311a hc hs hsplit h4 (hcommV x hxX τ hτW) fun y hy => ?_
  obtain ⟨hyL, hyY⟩ := Subgroup.mem_inf.mp hy
  have hxyQ : ⁅x, y⁆ ∈ Q := hcomm x hxX y hyY
  have hyτZ : ⁅y, τ⁆ ∈ Z := (mem_CQtGrp.mp (hTC hτT)).2 y (Subgroup.mem_inf.mpr ⟨hyL, hyY⟩)
  exact CFSG.GroupTheory.commutatorElement_commutatorElement_mem_of_classTwo
    (fun z hz => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hc.hyp.toHyp79.V_central hz hq).symm)
    (Subgroup.commutator_le.mpr fun a ha b hb => hc.hyp.toHyp79.comm_mem_V ha hb)
    (hc.hyp.Q_normal.2 hxM) (hc.hyp.Z_normal.2 hxM) hxyQ hτQ hyτZ

private theorem X_le_normalizer_sup (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {T : Subgroup G}
    (hK5 : Sec97K5 M Q Z B hc t T) (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y)) :
    X ≤ Subgroup.normalizer ((Uline Z B X ⊔ T : Subgroup G) : Set G) := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit0
  have hXM : X ≤ M := hXR.trans (hc.Rt_le_M t)
  intro x hx
  have hWx : conjSubgroup x (Uline Z B X) = Uline Z B X := conj_Uline hc hXM hx
  have hTx : conjSubgroup x T ≤ Uline Z B X ⊔ T := by
    intro u hu
    rw [mem_conjSubgroup] at hu
    have hcomm : ⁅x, x⁻¹ * u * x⁆ ∈ Uline Z B X :=
      comm_mem_ulineX h34 h311a hc hs hsplit h4 hK5 hTC hx hu
    have e : u = ⁅x, x⁻¹ * u * x⁆ * (x⁻¹ * u * x) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem_sup hcomm hu
  have hle : conjSubgroup x (Uline Z B X ⊔ T) ≤ Uline Z B X ⊔ T := by
    rw [conjSubgroup_sup', hWx]
    exact sup_le le_sup_left hTx
  exact conjSubgroup_eq_self_iff.mp
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]))

private theorem card_uline_sup (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T)
    {m : G} (hm : m ∈ M) (hpt : T = conjSubgroup m B ⊔ Z) :
    Nat.card ↥(Uline Z B X ⊔ T) = Nat.card Z ^ 4 := by
  have hdata := ulineX_data h34 h311a hc hs hsplit
  have hWcard : Nat.card ↥(Uline Z B X) = Nat.card Z ^ 3 := hdata.1
  have hWV : Uline Z B X ≤ Vt M (LB M Q B) B Z t := hdata.2.2.2
  have hTcard : Nat.card T = Nat.card Z ^ 2 := by
    rw [hpt]
    exact card_conj_sup_Z hc hm
  have hinf : Uline Z B X ⊓ T = Z := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxW, hxT⟩ := Subgroup.mem_inf.mp hx
      exact hK5.inf_V_le (Subgroup.mem_inf.mpr ⟨hxT, hWV hxW⟩)
    · intro z hz
      exact Subgroup.mem_inf.mpr ⟨Z_le_Uline Z B X hz, hpt ▸ Subgroup.mem_sup_right hz⟩
  have hTN : T ≤ Subgroup.normalizer (Uline Z B X : Set G) := by
    have hTW := T_le_Wt h34 hc hs hK5
    have hcent : T ≤ Subgroup.centralizer (Uline Z B X : Set G) := by
      intro τ hτ
      exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hTW hτ)).2 w (hWV hw)
    exact hcent.trans (Subgroup.centralizer_le_normalizer (Uline Z B X : Set G))
  have hprod := card_sup_mul_card_inf_of_le_normalizer (L := Uline Z B X) (E := T) hTN
  rw [hinf, hWcard, hTcard] at hprod
  have hq : 0 < Nat.card Z := Nat.card_pos
  have h' : Nat.card ↥(Uline Z B X ⊔ T) * Nat.card Z = Nat.card Z ^ 4 * Nat.card Z := by
    rw [hprod]
    ring
  exact Nat.eq_of_mul_eq_mul_right hq h'

private theorem commutator_mul_right_mem_Z (hc : Ctx M Q Z B) {n u τ : G}
    (hnM : n ∈ M) (huQ : u ∈ Q) (hτQ : τ ∈ Q) (hnu : ⁅n, u⁆ ∈ Z) :
    ⁅n, u * τ⁆ * ⁅n, τ⁆⁻¹ ∈ Z := by
  have hnτQ : ⁅n, τ⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hnM) τ).mp hτQ) (Q.inv_mem hτQ)
  have h2 : u * ⁅n, τ⁆ * u⁻¹ * ⁅n, τ⁆⁻¹ ∈ Z :=
    hc.hyp.toHyp79.comm_mem_V huQ hnτQ
  have h1 : ⁅n, u * τ⁆ = ⁅n, u⁆ * (u * ⁅n, τ⁆ * u⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
  rw [h1]
  have h := Z.mul_mem hnu h2
  simpa only [mul_assoc] using h

private def commutatorPreimage (hc : Ctx M Q Z B) (V : Subgroup G) (hVQ : V ≤ Q) {t : G}
    {τ : G} (hZQ : Z ≤ Subgroup.centralizer (Q : Set G))
    (hτV : ∀ n ∈ hc.CN t, ⁅n, τ⁆ ∈ V)
    (hcen : ∀ n ∈ hc.CN t, ∀ v ∈ V, ⁅n, v⁆ ∈ Z) : Subgroup G where
  carrier := {v : G | ∃ n ∈ hc.CN t, v * ⁅n, τ⁆⁻¹ ∈ Z}
  one_mem' := ⟨1, (hc.CN t).one_mem, by simp⟩
  mul_mem' := by
    rintro v₁ v₂ ⟨n₁, hn₁, h₁⟩ ⟨n₂, hn₂, h₂⟩
    set z₁ := v₁ * ⁅n₁, τ⁆⁻¹ with hz₁
    set z₂ := v₂ * ⁅n₂, τ⁆⁻¹ with hz₂
    have hz₁Z : z₁ ∈ Z := h₁
    have hz₂Z : z₂ ∈ Z := h₂
    have hv₁ : v₁ = z₁ * ⁅n₁, τ⁆ := by rw [hz₁]; group
    have hv₂ : v₂ = z₂ * ⁅n₂, τ⁆ := by rw [hz₂]; group
    have ha₁Q : ⁅n₁, τ⁆ ∈ Q := hVQ (hτV n₁ hn₁)
    have hswap : ⁅n₁, τ⁆ * z₂ = z₂ * ⁅n₁, τ⁆ :=
      Subgroup.mem_centralizer_iff.mp (hZQ hz₂Z) ⁅n₁, τ⁆ ha₁Q
    have hmulZ : ⁅n₂ * n₁, τ⁆ * (⁅n₁, τ⁆ * ⁅n₂, τ⁆)⁻¹ ∈ Z := by
      have hcen' : n₂ * ⁅n₁, τ⁆ * n₂⁻¹ * ⁅n₁, τ⁆⁻¹ ∈ Z :=
        (hcen n₂ hn₂) ⁅n₁, τ⁆ (hτV n₁ hn₁)
      have e : ⁅n₂ * n₁, τ⁆ = (n₂ * ⁅n₁, τ⁆ * n₂⁻¹) * ⁅n₂, τ⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
      rw [e]
      have h : ((n₂ * ⁅n₁, τ⁆ * n₂⁻¹) * ⁅n₂, τ⁆) * (⁅n₁, τ⁆ * ⁅n₂, τ⁆)⁻¹ =
          n₂ * ⁅n₁, τ⁆ * n₂⁻¹ * ⁅n₁, τ⁆⁻¹ := by group
      rw [h]
      exact hcen'
    have hcommZ : ⁅n₁, τ⁆ * ⁅n₂, τ⁆ * ⁅n₂ * n₁, τ⁆⁻¹ ∈ Z := by
      have h := Z.inv_mem hmulZ
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
    refine ⟨n₂ * n₁, (hc.CN t).mul_mem hn₂ hn₁, ?_⟩
    have heq : (v₁ * v₂) * ⁅n₂ * n₁, τ⁆⁻¹ =
        (z₁ * z₂) * (⁅n₁, τ⁆ * ⁅n₂, τ⁆ * ⁅n₂ * n₁, τ⁆⁻¹) := by
      rw [hv₁, hv₂]
      calc (z₁ * ⁅n₁, τ⁆) * (z₂ * ⁅n₂, τ⁆) * ⁅n₂ * n₁, τ⁆⁻¹
          = z₁ * (⁅n₁, τ⁆ * z₂) * ⁅n₂, τ⁆ * ⁅n₂ * n₁, τ⁆⁻¹ := by group
        _ = z₁ * (z₂ * ⁅n₁, τ⁆) * ⁅n₂, τ⁆ * ⁅n₂ * n₁, τ⁆⁻¹ := by rw [hswap]
        _ = (z₁ * z₂) * (⁅n₁, τ⁆ * ⁅n₂, τ⁆ * ⁅n₂ * n₁, τ⁆⁻¹) := by group
    rw [heq]
    exact Z.mul_mem (Z.mul_mem hz₁Z hz₂Z) hcommZ
  inv_mem' := by
    rintro v ⟨n, hn, h⟩
    set a := ⁅n, τ⁆ with ha
    set z := v * a⁻¹ with hz
    have hzZ : z ∈ Z := h
    have haQ : a ∈ Q := hVQ (hτV n hn)
    have hv : v = z * a := by rw [hz]; group
    have hswap : a * z⁻¹ = z⁻¹ * a :=
      Subgroup.mem_centralizer_iff.mp (hZQ (Z.inv_mem hzZ)) a haQ
    have hva : v⁻¹ * a = z⁻¹ := by
      rw [hv, mul_inv_rev, mul_assoc, ← hswap]
      group
    have ha2 : a⁻¹ * a⁻¹ ∈ Z := by
      have h2 : a ^ 2 ∈ Z := hc.hyp.toHyp79.sq_mem_V haQ
      have e : a⁻¹ * a⁻¹ = (a ^ 2)⁻¹ := by group
      rw [e]
      exact Z.inv_mem h2
    refine ⟨n, hn, ?_⟩
    have heq : v⁻¹ * a⁻¹ = (v⁻¹ * a) * (a⁻¹ * a⁻¹) := by group
    rw [heq, hva]
    exact Z.mul_mem (Z.inv_mem hzZ) ha2

private theorem commutatorPreimage_le_uline (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T)
    (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y)) {τ : G} (hτT : τ ∈ T) {A : Subgroup G}
    (hA : ∀ v, v ∈ A ↔ ∃ g ∈ hc.CN t, v * ⁅g, τ⁆⁻¹ ∈ Z) :
    A ≤ Uline Z B X := by
  intro v hv
  obtain ⟨g, hg, hvg⟩ := (hA v).mp hv
  have hNX : hc.CN t ≤ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  set z := v * ⁅g, τ⁆⁻¹ with hz
  have hzZ : z ∈ Z := hvg
  have hvz : v = z * ⁅g, τ⁆ := by rw [hz]; group
  rw [hvz]
  exact (Uline Z B X).mul_mem (Z_le_Uline Z B X hzZ)
    (comm_mem_ulineX h34 h311a hc hs hsplit h4 hK5 hTC (hNX hg) hτT)

private theorem conj_commutatorPreimage (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T) {τ : G}
    (hτT : τ ∈ T) (hτQ : τ ∈ Q) {A : Subgroup G}
    (hA : ∀ v, v ∈ A ↔ ∃ g ∈ hc.CN t, v * ⁅g, τ⁆⁻¹ ∈ Z) :
    ∀ x ∈ X, conjSubgroup x A = A := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, hcommV⟩ := hsplit0
  have hNX : hc.CN t ≤ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hτW : τ ∈ Wt Q (Vt M (LB M Q B) B Z t) := T_le_Wt h34 hc hs hK5 hτT
  intro x hx
  have hxM : x ∈ M := hc.Rt_le_M t (hXR hx)
  have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
  have hsub : conjSubgroup x A ≤ A := by
    intro v hv
    rw [mem_conjSubgroup] at hv
    obtain ⟨g, hg, hga⟩ := (hA _).mp hv
    have hgN : x * g * x⁻¹ ∈ hc.CN t := Ctx.CN_conj_mem hc hs.mem hxR hg
    refine (hA _).mpr ⟨x * g * x⁻¹, hgN, ?_⟩
    have hconj1 : x * (x⁻¹ * v * x) * x⁻¹ * (x * ⁅g, τ⁆ * x⁻¹)⁻¹ ∈ Z := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM)
        ((x⁻¹ * v * x) * ⁅g, τ⁆⁻¹)).mp hga
      have he : x * (x⁻¹ * v * x) * x⁻¹ * (x * ⁅g, τ⁆ * x⁻¹)⁻¹ =
          x * ((x⁻¹ * v * x) * ⁅g, τ⁆⁻¹) * x⁻¹ := by group
      rwa [he]
    have e1 : x * ⁅g, τ⁆ * x⁻¹ = ⁅x * g * x⁻¹, x * τ * x⁻¹⁆ :=
      conjugate_commutatorElement g τ x
    have e2 : x * τ * x⁻¹ = ⁅x, τ⁆ * τ := by
      rw [commutatorElement_def]
      group
    have hxτV : ⁅x, τ⁆ ∈ Vt M (LB M Q B) B Z t := hcommV x hx τ hτW
    have hxτQ : ⁅x, τ⁆ ∈ Q := hc.Vt_le_Q t hxτV
    have hgM : x * g * x⁻¹ ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hgN).1
    have hZ : ⁅x * g * x⁻¹, ⁅x, τ⁆⁆ ∈ Z :=
      (Ctx.mem_CN.mp hgN).2 ⁅x, τ⁆ hxτV
    have hconj2 : x * ⁅g, τ⁆ * x⁻¹ * ⁅x * g * x⁻¹, τ⁆⁻¹ ∈ Z := by
      have h := commutator_mul_right_mem_Z hc hgM hxτQ hτQ hZ
      rwa [← e2, ← e1] at h
    have hcomb : (x * (x⁻¹ * v * x) * x⁻¹) * ⁅x * g * x⁻¹, τ⁆⁻¹ ∈ Z := by
      have h := Z.mul_mem hconj1 hconj2
      have he : (x * (x⁻¹ * v * x) * x⁻¹) * (x * ⁅g, τ⁆ * x⁻¹)⁻¹ *
          ((x * ⁅g, τ⁆ * x⁻¹) * ⁅x * g * x⁻¹, τ⁆⁻¹) =
          (x * (x⁻¹ * v * x) * x⁻¹) * ⁅x * g * x⁻¹, τ⁆⁻¹ := by group
      rwa [he] at h
    have hv' : v = x * (x⁻¹ * v * x) * x⁻¹ := by group
    rwa [hv']
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [card_conjSubgroup])

private theorem commutatorPreimage_ne_Z (hc : Ctx M Q Z B) {t : G} {T : Subgroup G}
    (hK5 : Sec97K5 M Q Z B hc t T) {τ : G} (hτT : τ ∈ T) (hτZ : τ ∉ Z) {A : Subgroup G}
    (hA : ∀ v, v ∈ A ↔ ∃ g ∈ hc.CN t, v * ⁅g, τ⁆⁻¹ ∈ Z) :
    A ≠ Z := by
  intro hAZ
  apply hτZ
  have hcen : ∀ l ∈ LB M Q B ⊓ hc.CN t, ⁅l, τ⁆ ∈ Z := by
    intro l hl
    have h1 : ⁅l, τ⁆ * ⁅l, τ⁆⁻¹ ∈ Z := by
      rw [mul_inv_cancel]
      exact Z.one_mem
    have hlA : ⁅l, τ⁆ ∈ A := (hA _).mpr ⟨l, hl.2, h1⟩
    rwa [hAZ] at hlA
  exact hK5.inf_V_le (Subgroup.mem_inf.mpr ⟨hτT, hK5.cen_le τ hτT hcen⟩)

private theorem exists_mem_CN_comm_inv_mem_Z (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T)
    (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y)) {τ : G} (hτT : τ ∈ T) (hτZ : τ ∉ Z) {w : G}
    (hwW : w ∈ Uline Z B X) :
    ∃ g ∈ hc.CN t, w * ⁅g, τ⁆⁻¹ ∈ Z := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, hcommV⟩ := hsplit0
  have hNX : hc.CN t ≤ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hτQ : τ ∈ Q := ((T_le_Wt h34 hc hs hK5).trans inf_le_left) hτT
  have hτW : τ ∈ Wt Q (Vt M (LB M Q B) B Z t) := T_le_Wt h34 hc hs hK5 hτT
  have hZQ : Z ≤ Subgroup.centralizer (Q : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun q hq => (hc.hyp.toHyp79.V_central hz hq).symm
  let A : Subgroup G := commutatorPreimage hc (Vt M (LB M Q B) B Z t) hVQ hZQ
    (fun g hg => hcommV g (hNX hg) τ hτW) (fun g hg v hv => (Ctx.mem_CN.mp hg).2 v hv)
  have hA : ∀ v, v ∈ A ↔ ∃ g ∈ hc.CN t, v * ⁅g, τ⁆⁻¹ ∈ Z := fun v => Iff.rfl
  have hAW : A ≤ Uline Z B X :=
    commutatorPreimage_le_uline h34 h311a hc hs hsplit h4 hK5 hTC hτT hA
  have hAX : ∀ x ∈ X, conjSubgroup x A = A :=
    conj_commutatorPreimage h34 h311a hc hs hsplit hK5 hτT hτQ hA
  have hAZ : A ≠ Z := commutatorPreimage_ne_Z hc hK5 hτT hτZ hA
  have hArep : A = Uline Z B X := by
    rcases (ulineX_data h34 h311a hc hs hsplit).2.1.2.2.2 A
      (fun z hz => (hA z).mpr ⟨1, (hc.CN t).one_mem, by simpa using hz⟩) hAW hAX with h | h
    · exact absurd h hAZ
    · exact h
  change w ∈ A
  rw [hArep]
  exact hwW

private theorem exists_point_of_mem_sup (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    {T : Subgroup G} (hK5 : Sec97K5 M Q Z B hc t T)
    (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y)) {m : G} (hm : m ∈ M)
    (hmY : conjSubgroup m Y = Y) (hpt : T = conjSubgroup m B ⊔ Z) {u : G}
    (hu : u ∈ Uline Z B X ⊔ T) :
    ∃ h ∈ M, conjSubgroup h Y = Y ∧ conjSubgroup h B ≤ Uline Z B X ⊔ T ∧
      u ∈ (conjSubgroup h B ⊔ Z : Subgroup G) := by
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, -, hXY, -, hcomm⟩, -, hcommV⟩ := hsplit0
  have hNX : hc.CN t ≤ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hTW : T ≤ Wt Q (Vt M (LB M Q B) B Z t) := T_le_Wt h34 hc hs hK5
  have hWV : Uline Z B X ≤ Vt M (LB M Q B) B Z t :=
    (ulineX_data h34 h311a hc hs hsplit).2.2.2
  have hWT : Uline Z B X ≤ Subgroup.centralizer (T : Set G) := by
    intro w hw
    exact Subgroup.mem_centralizer_iff.mpr fun τ hτ =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hTW hτ)).2 w (hWV hw)).symm
  have hWN : Uline Z B X ≤ Subgroup.normalizer (T : Set G) :=
    hWT.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  obtain ⟨w, hwW, τ, hτT, hwτ⟩ := exists_mul_of_mem_sup_of_le_normalizer hWN hu
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le (X := Y) (Y := X) hQY fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this
  have hYX' : Y ≤ Subgroup.normalizer (X : Set G) :=
    normalizer_of_commutator_le hQX hcomm
  have hRtY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hXY]
    exact sup_le hXY' Subgroup.le_normalizer
  by_cases hτZ : τ ∈ Z
  · have huW : u ∈ Uline Z B X := by
      rw [← hwτ]
      exact (Uline Z B X).mul_mem hwW (Z_le_Uline Z B X hτZ)
    obtain ⟨x, hxX, hux⟩ := (ulineX_data h34 h311a hc hs hsplit).2.2.1 u huW
    have hxN := X_le_normalizer_sup h34 h311a hc hs hsplit h4 hK5 hTC hxX
    have hBx : conjSubgroup x B ≤ Uline Z B X ⊔ T := by
      have h1 : conjSubgroup x B ≤ conjSubgroup x (Uline Z B X ⊔ T) :=
        Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom)
          ((B_le_Uline Z B X).trans le_sup_left)
      rwa [conjSubgroup_eq_self_iff.mpr hxN] at h1
    exact ⟨x, hc.Rt_le_M t (hXR hxX), conjSubgroup_eq_self_iff.mpr (hXY' hxX), hBx, hux⟩
  · obtain ⟨g, hg, hzg⟩ := exists_mem_CN_comm_inv_mem_Z h34 h311a hc hs hsplit h4 hK5 hTC
      hτT hτZ hwW
    have hgM : g ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hg).1
    have hgR : g ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hg).1
    have hgX : g ∈ X := hNX hg
    have hgN := X_le_normalizer_sup h34 h311a hc hs hsplit h4 hK5 hTC hgX
    refine ⟨g * m, M.mul_mem hgM hm, ?_, ?_, ?_⟩
    · rw [conjSubgroup_mul, hmY]
      exact conjSubgroup_eq_self_iff.mpr (hRtY hgR)
    · have hBm : conjSubgroup m B ≤ T := hpt ▸ le_sup_left
      have h1 : conjSubgroup g (conjSubgroup m B) ≤ conjSubgroup g T :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hBm
      have h2 : conjSubgroup g T ≤ conjSubgroup g (Uline Z B X ⊔ T) :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) le_sup_right
      rw [conjSubgroup_eq_self_iff.mpr hgN] at h2
      rw [conjSubgroup_mul]
      exact h1.trans h2
    · have hτB : τ ∈ conjSubgroup m B ⊔ Z := hpt ▸ hτT
      have hgτ : g * τ * g⁻¹ ∈ conjSubgroup (g * m) B ⊔ Z := by
        have hmem : g * τ * g⁻¹ ∈ conjSubgroup g (conjSubgroup m B ⊔ Z) := by
          rw [mem_conjSubgroup]
          have e : g⁻¹ * (g * τ * g⁻¹) * g = τ := by group
          rwa [e]
        rw [conjSubgroup_sup', ← conjSubgroup_mul] at hmem
        rwa [hc.conj_Z_eq hgM] at hmem
      have hu_eq : u = (w * ⁅g, τ⁆⁻¹) * (g * τ * g⁻¹) := by
        rw [← hwτ]
        calc w * τ = (w * ⁅g, τ⁆⁻¹) * (⁅g, τ⁆ * τ) := by group
          _ = (w * ⁅g, τ⁆⁻¹) * (g * τ * g⁻¹) := by
            rw [commutatorElement_def]
            group
      rw [hu_eq]
      exact (conjSubgroup (g * m) B ⊔ Z).mul_mem (Subgroup.mem_sup_right hzg) hgτ

theorem fiveCore_of_line (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {T : Subgroup G}
    (hK5 : Sec97K5 M Q Z B hc t T) (hTC : T ≤ CQtGrp hc (LB M Q B ⊓ Y)) {m : G}
    (hm : m ∈ M) (hmY : conjSubgroup m Y = Y) (hpt : T = conjSubgroup m B ⊔ Z) :
    FiveCore M Q Z B Y := by
  classical
  have hWV : Uline Z B X ≤ Vt M (LB M Q B) B Z t :=
    (ulineX_data h34 h311a hc hs hsplit).2.2.2
  have hBmQ : conjSubgroup m B ≤ Q := by
    rw [← hc.conj_Q_eq hm]
    exact Subgroup.map_mono hc.le
  have hTQ : T ≤ Q := by
    rw [hpt]
    exact sup_le hBmQ hc.Z_le_Q
  refine ⟨Uline Z B X ⊔ T, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Z_le_Uline Z B X).trans le_sup_left
  · exact (B_le_Uline Z B X).trans le_sup_left
  · exact sup_le (hWV.trans (hc.Vt_le_Q t)) hTQ
  · rw [card_uline_sup h34 h311a hc hs hsplit hK5 hm hpt]
  · intro u hu _
    exact exists_point_of_mem_sup h34 h311a hc hs hsplit h4 hK5 hTC hm hmY hpt hu

end HS9

end CFSG.RankThree.GF2n.Stroth80
