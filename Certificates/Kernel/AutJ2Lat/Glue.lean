module

public import Certificates.Kernel.AutJ2Lat.Checks
public import Certificates.Kernel.J2Dc.IdxG
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2LatInputs
public import CFSG.Certificates.Kernel.S151IdxGAct
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.AutJ2Lat

open CFSG.KC.LQT.PW CFSG.KC.LQT.BW.Pf CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.IdxG
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.ComponentClassification.J2Cover CFSG.Quasithin.F112R.AJ2L
open CFSG.KD.J2Dc (wW G ga gb)

@[expose] def PI (σ : Equiv.Perm (Fin 315)) (f : ℕ → ℕ) : Prop :=
  ∀ p (hp : p < 315), (σ ⟨p, hp⟩ : ℕ) = f p

theorem pi_ext {σ τ : Equiv.Perm (Fin 315)} {f : ℕ → ℕ} (h1 : PI σ f) (h2 : PI τ f) : σ = τ :=
  Equiv.ext fun x => Fin.ext ((h1 x.1 x.2).trans (h2 x.1 x.2).symm)

theorem imgW_mulW {c d p : ℕ} (hp : p < 315) :
    imgW 9 (mulW 315 9 c d) p = imgW 9 c (imgW 9 d p) := by
  rw [mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hp]

theorem pi_mul {σ τ : Equiv.Perm (Fin 315)} {c d : ℕ} (h1 : PI σ (imgW 9 c))
    (h2 : PI τ (imgW 9 d)) : PI (σ * τ) (imgW 9 (mulW 315 9 c d)) := by
  intro p hp
  rw [imgW_mulW hp, Equiv.Perm.mul_apply, ← h2 p hp]
  exact h1 _ (τ ⟨p, hp⟩).2

theorem pi_one : PI 1 (imgW 9 (oneW 315 9)) := fun p hp => by
  rw [oneW, imgW_ofFnW (fun j hj => lt_trans hj (by norm_num)) hp]
  rfl

theorem evalElt_app {Γ : Type} [Group Γ] (els : Array Γ) (u v : List ℕ) :
    evalElt els (u ++ v) = evalElt els u * evalElt els v := by
  simp [evalElt, List.map_append, List.prod_append]

private def piWordProp {Γ : Type} [Group Γ] (ρ : Γ →* Equiv.Perm (Fin 315)) (els : Array Γ)
    (cs : List ℕ) (w : List ℕ) : Prop :=
  PI (ρ (evalElt els w)) (imgW 9 (w.foldr (fun l acc => mulW 315 9 (cs.getD l 0) acc)
    (oneW 315 9)))

private theorem pi_word_nil {Γ : Type} [Group Γ] (ρ : Γ →* Equiv.Perm (Fin 315))
    (els : Array Γ) (cs : List ℕ) : piWordProp ρ els cs [] := by
  change PI (ρ (evalElt els [])) (imgW 9 (([] : List ℕ).foldr
    (fun l acc => mulW 315 9 (cs.getD l 0) acc) (oneW 315 9)))
  rw [evalElt_nil, map_one]
  exact pi_one

private theorem pi_word_cons {Γ : Type} [Group Γ] (ρ : Γ →* Equiv.Perm (Fin 315))
    (els : Array Γ) (cs : List ℕ)
    (h : ∀ l < els.size, PI (ρ (els.getD l 1)) (imgW 9 (cs.getD l 0)))
    (l : ℕ) (w : List ℕ) (hl : l < els.size) (ih : piWordProp ρ els cs w) :
    piWordProp ρ els cs (l :: w) := by
  change PI (ρ (evalElt els (l :: w))) (imgW 9 ((l :: w).foldr
    (fun l acc => mulW 315 9 (cs.getD l 0) acc) (oneW 315 9)))
  rw [evalElt_cons, map_mul, List.foldr_cons]
  exact pi_mul (h l hl) ih

private theorem list_rec_mem {α : Type} (P : List α → Prop) (good : α → Prop)
    (h0 : P []) (hs : ∀ a w, good a → P w → P (a :: w)) :
    ∀ w, (∀ a ∈ w, good a) → P w := by
  intro w
  induction w with
  | nil =>
    intro _
    exact h0
  | cons a w ih =>
    intro hw
    exact hs a w (hw a List.mem_cons_self)
      (ih fun x hx => hw x (List.mem_cons_of_mem _ hx))

private theorem pi_word_aux {Γ : Type} [Group Γ] (ρ : Γ →* Equiv.Perm (Fin 315))
    (els : Array Γ) (cs : List ℕ)
    (h : ∀ l < els.size, PI (ρ (els.getD l 1)) (imgW 9 (cs.getD l 0))) :
    ∀ w : List ℕ, (∀ l ∈ w, l < els.size) → piWordProp ρ els cs w := by
  exact list_rec_mem (P := piWordProp ρ els cs) (good := fun l => l < els.size)
    (pi_word_nil ρ els cs) (pi_word_cons ρ els cs h)

theorem pi_word {Γ : Type} [Group Γ] (ρ : Γ →* Equiv.Perm (Fin 315)) (els : Array Γ)
    (cs : List ℕ) (h : ∀ l < els.size, PI (ρ (els.getD l 1)) (imgW 9 (cs.getD l 0))) :
    ∀ w : List ℕ, (∀ l ∈ w, l < els.size) →
      PI (ρ (evalElt els w)) (imgW 9 (w.foldr (fun l acc => mulW 315 9 (cs.getD l 0) acc)
        (oneW 315 9))) := by
  exact pi_word_aux ρ els cs h

theorem pi_of_rep {t : Array ℕ} {σ : Equiv.Perm (Fin 315)} (hr : CFSG.Monster.B.Co2.Rep 315 t σ)
    {c : ℕ} (h : (t.toList == imgs c) = true) : PI σ (imgW 9 c) := by
  intro p hp
  have e := beq_iff_eq.1 h
  have hs : p < t.size := by
    have hl := congrArg List.length e
    simp only [imgs, List.length_map, List.length_range, Array.length_toList] at hl
    omega
  rw [← hr.apply hp, getElem!_pos t p hs]
  have h2 : t.toList[p]? = some (imgW 9 c p) := by
    rw [e]
    simp [imgs, hp]
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem hs] at h2
  exact Option.some_inj.1 h2

theorem good_of_pi {g : R} {f : ℕ → ℕ} (h : PI (g : Equiv.Perm (Fin 315)) f) :
    Good 315 (tab 315 g).toArray f := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  have e : (tab 315 g).toArray.getD p 0 = act 315 g p := img_tab g p
  have e2 : act 315 g p = f p := (act_eq g ⟨p, hp⟩).trans (h p hp)
  exact ⟨e.trans e2, e2 ▸ act_lt g hp⟩

theorem pi_of_goodJ {g : G} {f : ℕ → ℕ}
    (h : Good 315 (tab 315 g).toArray f) : PI (actionHom g) f := fun p hp => by
  rw [← (h.2 p hp).1]
  exact ((img_tab g p).trans (act_eq g ⟨p, hp⟩)).symm

@[expose] noncomputable def φ : G →* R :=
  MonoidHom.codRestrict actionHom R fun g =>
    P_le_R (actionHom_range ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩)

theorem φ_val (g : G) : (φ g : Equiv.Perm (Fin 315)) = actionHom g := rfl

theorem φ_injective : Function.Injective φ := by
  intro g h e
  have e' : actionHom g = actionHom h := by rw [← φ_val, ← φ_val, e]
  exact actionHom_injective e'

theorem ab_parts : ((autStrong.getD 0 #[]).toList == imgs AC) = true ∧
    ((autStrong.getD 1 #[]).toList == imgs BC) = true := by
  have h := ab_ok
  rw [abOK.eq_1, Bool.and_eq_true] at h
  exact h

theorem x_parts : (outerArr.toList == imgs K.UC) = true ∧ (K.XC == mulW 315 9 K.UC AC) = true := by
  have h := x_ok
  rw [xOK.eq_1, Bool.and_eq_true] at h
  exact h

theorem piA : PI permA (imgW 9 AC) :=
  pi_of_rep rep_permA (by rw [Array.getElem!_eq_getD]; exact ab_parts.1)

theorem piB : PI permB (imgW 9 BC) :=
  pi_of_rep rep_permB (by rw [Array.getElem!_eq_getD]; exact ab_parts.2)

theorem piX : PI (xR : Equiv.Perm (Fin 315)) (imgW 9 K.XC) := by
  rw [eq_of_beq x_parts.2]
  exact pi_mul (pi_of_rep rep_permU x_parts.1) piA

theorem piY : PI (yR : Equiv.Perm (Fin 315)) (imgW 9 BC) := piB

theorem piS {i : ℕ} (hi : i < 3) :
    PI (sgen i hi : Equiv.Perm (Fin 315)) (imgW 9 (K.SC.getD i 0)) := by
  have hr := rep_permOfArr_of_chainOK sylowChain_ok (j := i) (by
    have : sylowStrong.size = 5 := rfl
    omega)
  refine pi_of_rep hr ?_
  rw [Array.getElem!_eq_getD]
  exact List.all_eq_true.1 s_ok i (List.mem_range.2 hi)

theorem φ_ga : φ ga = ⟨permA, P_le_R (Subgroup.subset_closure (Set.mem_insert _ _))⟩ :=
  Subtype.ext (by rw [φ_val]; exact actionHom_a)

theorem φ_gb : φ gb = yR := Subtype.ext (by rw [φ_val]; exact actionHom_b)

theorem piJ_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    PI (actionHom (wordElt ga gb w)) (imgW 9 (wW w)) :=
  pi_word actionHom #[ga, gb] J2Dc.J.tc (fun l hl => by
    obtain rfl | rfl : l = 0 ∨ l = 1 := by simp at hl; omega
    · change PI (actionHom ga) (imgW 9 AC)
      rw [actionHom_a]
      exact piA
    · change PI (actionHom gb) (imgW 9 BC)
      rw [actionHom_b]
      exact piB) w (by simpa using hw)

theorem piR_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    PI ((wordElt xR yR w : R) : Equiv.Perm (Fin 315)) (imgW 9 (wXY w)) :=
  pi_word R.subtype #[xR, yR] [K.XC, BC] (fun l hl => by
    obtain rfl | rfl : l = 0 ∨ l = 1 := by simp at hl; omega
    · exact piX
    · exact piY) w (by simpa using hw)

theorem wordElt_WA : wordElt xR yR WA = φ ga := by
  apply Subtype.ext
  refine pi_ext (piR_word (w := WA) (by decide)) ?_
  rw [eq_of_beq wa_ok, φ_val, actionHom_a]
  exact piA

theorem wordElt_trW : ∀ v : List ℕ, (∀ l ∈ v, l < 2) →
    wordElt xR yR (trW v) = φ (wordElt ga gb v)
  | [], _ => by
    change evalElt #[xR, yR] [] = φ (evalElt #[ga, gb] [])
    rw [evalElt_nil, evalElt_nil, map_one]
  | l :: v, hv => by
    have ih := wordElt_trW v fun x hx => hv x (List.mem_cons_of_mem _ hx)
    change evalElt #[xR, yR] ((bif Nat.beq l 0 then WA else [1]) ++ trW v) =
      φ (evalElt #[ga, gb] (l :: v))
    rw [evalElt_app, evalElt_cons, map_mul]
    change _ * wordElt xR yR (trW v) = _
    rw [ih]
    congr 1
    obtain rfl | rfl : l = 0 ∨ l = 1 := by have := hv l List.mem_cons_self; omega
    · exact wordElt_WA
    · change evalElt #[xR, yR] [1] = φ gb
      rw [evalElt_cons, evalElt_nil, mul_one, φ_gb]
      rfl

theorem cw_lt : (K.cw.all (Nat.blt · 2) && K.ciw.all (Nat.blt · 2)) = true := by quickRfl

theorem tw_lt : (K.tw.all fun w => w.all (Nat.blt · 3)) = true := by quickRfl

theorem lt_of_all {w : List ℕ} {m : ℕ} (h : w.all (Nat.blt · m) = true) : ∀ l ∈ w, l < m :=
  fun l hl => by simpa using List.all_eq_true.1 h l hl

@[expose] noncomputable def cJ : G := wordElt ga gb K.cw

theorem c_parts : (wW K.cw == K.CC) = true ∧ (wW K.ciw == K.CI) = true ∧
    (mulW 315 9 K.CC K.CI == oneW 315 9) = true := by
  have h := c_ok
  rw [cOK.eq_1, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem piC : PI (actionHom cJ) (imgW 9 K.CC) := by
  rw [← eq_of_beq c_parts.1]
  exact piJ_word (lt_of_all (Bool.and_eq_true _ _ ▸ cw_lt).1)

theorem ciw_eq : wordElt ga gb K.ciw = cJ⁻¹ := by
  have hci : PI (actionHom (wordElt ga gb K.ciw)) (imgW 9 K.CI) := by
    rw [← eq_of_beq c_parts.2.1]
    exact piJ_word (lt_of_all (Bool.and_eq_true _ _ ▸ cw_lt).2)
  have h1 : actionHom (cJ * wordElt ga gb K.ciw) = actionHom 1 := by
    rw [map_mul, map_one]
    refine pi_ext (pi_mul piC hci) ?_
    rw [eq_of_beq c_parts.2.2]
    exact pi_one
  exact eq_inv_of_mul_eq_one_right (actionHom_injective h1)

theorem pi_conj {g : G} {d : ℕ} (h : PI (actionHom g) (imgW 9 d)) :
    PI (φ (cJ * g * cJ⁻¹) : Equiv.Perm (Fin 315)) (imgW 9 (mulW 315 9 K.CC (mulW 315 9 d K.CI))) := by
  rw [φ_val, map_mul, map_mul, mul_assoc]
  refine pi_mul piC (pi_mul h ?_)
  rw [← ciw_eq, ← eq_of_beq c_parts.2.1]
  exact piJ_word (lt_of_all (Bool.and_eq_true _ _ ▸ cw_lt).2)

end CFSG.KD.AutJ2Lat

end
