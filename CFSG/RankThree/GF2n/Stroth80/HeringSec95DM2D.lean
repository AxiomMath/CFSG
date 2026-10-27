module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM2C
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DCW
public import CFSG.RankThree.GF2n.Stroth80.CarterSec97Good

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def borelSL (K : Type) [Field K] : Subgroup SL(2, K) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, zero_mul,
      zero_add, hy, mul_zero]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hx]

theorem comm_LB_XB (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {g b : G}
    (hg : g ∈ LB M Q B)
    (hb : b ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) :
    ⁅g, b⁆ ∈ Vt M (LB M Q B) B Z t :=
  comm_LB_X95 hc inf_le_left (fun v hv y hy => Subgroup.mem_centralizer_iff.mp hy.2 v hv)
    (sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt) hg (hc.Rt_normalizes_Vt ht (le_Rt _ ht hg)) hb

theorem comm_LB_mem_Wt' (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {l x : G}
    (hl : l ∈ LB M Q B) (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    ⁅l, x⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have h1 := sec9_conj_mem_Wt hc ht (le_Rt _ ht hl) hx
  rw [commutatorElement_def]
  exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem h1 ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hx)

theorem comm_comm_LB_Wt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {l₁ l₂ x : G}
    (h₁ : l₁ ∈ LB M Q B) (h₂ : l₂ ∈ LB M Q B) (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    ⁅l₂, ⁅l₁, x⁆⁆ ∈ Vt M (LB M Q B) B Z t :=
  comm_LB_XB hc ht h₂ (le_sup_left (a := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))
    ⟨comm_LB_Wt_mem_QB hc (hc.B_le_Vt ht) h₁ hx, comm_LB_mem_Wt' hc ht h₁ hx⟩)

theorem conj_XB_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) :
    conjSubgroup r ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  rw [show conjSubgroup r ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      conjSubgroup r (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        conjSubgroup r (Vt M (LB M Q B) B Z t) from Subgroup.map_sup _ _ _,
    QB_conj, conjSubgroup_inf, sec9_conj_Wt_eq hc ht hrR, sec9_conj_Vt_eq hc ht hrR]

section Setup

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

theorem pi_mem_img_sup {XA XB : Subgroup G} (hA : XA ≤ Q) (hB : XB ≤ Q) {z : G}
    (hz : z ∈ XA ⊔ XB) : M₀.π z ∈ M₀.img XA ⊔ M₀.img XB := by
  let T : Subgroup G :=
    { carrier := {z | z ∈ Q ∧ M₀.π z ∈ M₀.img XA ⊔ M₀.img XB}
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [M₀.π_mul a ha.1 b hb.1]
        exact add_mem ha.2 hb.2⟩
      one_mem' := ⟨Q.one_mem, by
        rw [M₀.pi_one]
        exact zero_mem _⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
        rw [M₀.pi_inv ha.1]
        exact neg_mem ha.2⟩ }
  have hXA : XA ≤ T := fun z hz => ⟨hA hz, AddSubgroup.mem_sup_left (M₀.pi_mem_img hz (hA hz))⟩
  have hXB : XB ≤ T := fun z hz => ⟨hB hz, AddSubgroup.mem_sup_right (M₀.pi_mem_img hz (hB hz))⟩
  exact (sup_le hXA hXB hz).2

namespace SetupW

variable (S : SetupW hc t M₀ φ)

include S in
theorem pi_comm {l x : G} (hl : l ∈ H0 M Z) (hx : x ∈ Q) :
    M₀.π ⁅l, x⁆ = actM φ l (M₀.π x) - M₀.π x := by
  have hlM : l ∈ M := hl.1
  have h1 : l * x * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hx
  rw [commutatorElement_def, M₀.π_mul _ h1 _ (Q.inv_mem hx), S.pi_conj hl hx, M₀.pi_inv hx]
  abel

theorem rhoV_LB_eq [CharP K 2] {l : G} (hl : l ∈ LB M Q B) :
    ∃ s s' : K, rhoV S.vd l = (M1.uSL s, M1.uSL s') := by
  obtain ⟨s, s', h1, h2⟩ := S.rhoV_LB_unip hl
  exact ⟨s, s', Prod.ext (Subtype.ext h1) (Subtype.ext h2)⟩

theorem Act_rhoV {l : G} (hl : l ∈ Rt M (LB M Q B) t) :
    S.Act (rhoV S.vd l) = S.ActR ⟨l, hl⟩ := by
  rw [rhoV_of_mem S.vd hl]
  exact S.Act_rho ⟨l, hl⟩

theorem ActR_mkW_eq_iff {l : ↥(Rt M (LB M Q B) t)} {w : S.Wsub} :
    S.ActR l (S.mkW w) = S.mkW w ↔ actM φ (l : G) (w : M₀.E) - w ∈ S.Vsub := by
  show S.mkW (S.actWsub l w) = S.mkW w ↔ _
  rw [mkW_eq_iff]
  rfl

theorem actM_siegel {l₁ l₂ : G} (h₁ : l₁ ∈ LB M Q B) (h₂ : l₂ ∈ LB M Q B) {w : M₀.E}
    (hw : w ∈ S.Wsub) :
    actM φ l₂ (actM φ l₁ w - w) - (actM φ l₁ w - w) ∈ S.Vsub := by
  obtain ⟨x, hxW, hxQ, rfl⟩ := S.mem_Wsub.mp hw
  have hH₁ : l₁ ∈ H0 M Z := hc.Rt_le_H0 t (le_Rt (M := M) (LB M Q B) S.ht h₁)
  have hH₂ : l₂ ∈ H0 M Z := hc.Rt_le_H0 t (le_Rt (M := M) (LB M Q B) S.ht h₂)
  have hyQ : ⁅l₁, x⁆ ∈ Q := (comm_LB_mem_Wt' hc S.ht h₁ hxW).1
  rw [← S.pi_comm hH₁ hxQ, ← S.pi_comm hH₂ hyQ]
  exact M₀.pi_mem_img (comm_comm_LB_Wt hc S.ht h₁ h₂ hxW) (hc.Vt_le_Q t
    (comm_comm_LB_Wt hc S.ht h₁ h₂ hxW))

@[expose] def Xfix : Submodule K S.Wq where
  carrier := {w | ∀ a a' : K, S.Act (M1.uSL a, M1.uSL a') w = w}
  add_mem' := fun {x y} hx hy a a' => by rw [map_add, hx a a', hy a a']
  zero_mem' := fun a a' => map_zero _
  smul_mem' := fun c x hx a a' => by rw [map_smul, hx a a']

theorem mem_Xfix_iff_LB [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    (x : S.Wq) : x ∈ S.Xfix ↔
      ∀ (l : G) (hl : l ∈ LB M Q B), S.ActR ⟨l, le_Rt (M := M) (LB M Q B) S.ht hl⟩ x = x := by
  constructor
  · intro hx l hl
    obtain ⟨s, s', hρ⟩ := S.rhoV_LB_eq hl
    have h := hx s s'
    rw [← hρ, S.Act_rhoV (le_Rt (M := M) (LB M Q B) S.ht hl)] at h
    exact h
  · intro hx a a'
    obtain ⟨l, hl, h1, h2⟩ := S.rhoV_LB_surj h34 hs a a'
    have hρ : rhoV S.vd l = (M1.uSL a, M1.uSL a') := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    rw [← hρ, S.Act_rhoV (le_Rt (M := M) (LB M Q B) S.ht hl)]
    exact hx l hl

theorem act_sub_mem_Xfix [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    (a a' : K) (x : S.Wq) : S.Act (M1.uSL a, M1.uSL a') x - x ∈ S.Xfix := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨l₁, hl₁, h1, h2⟩ := S.rhoV_LB_surj h34 hs a a'
  have hρ : rhoV S.vd l₁ = (M1.uSL a, M1.uSL a') := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hl₁R := le_Rt (M := M) (LB M Q B) S.ht hl₁
  refine (S.mem_Xfix_iff_LB h34 hs _).mpr fun l₂ hl₂ => ?_
  rw [← hρ, S.Act_rhoV hl₁R]
  have key : S.ActR ⟨l₁, hl₁R⟩ (S.mkW w) - S.mkW w = S.mkW (S.actWsub ⟨l₁, hl₁R⟩ w - w) := by
    rw [map_sub]
    rfl
  rw [key, ActR_mkW_eq_iff]
  exact S.actM_siegel hl₁ hl₂ w.2

include S in
theorem comm_mem_Q {g z : G} (hg : g ∈ M) (hz : z ∈ Q) : ⁅g, z⁆ ∈ Q := by
  have h1 : g * z * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) z).mp hz
  rw [commutatorElement_def]
  exact Q.mul_mem h1 (Q.inv_mem hz)

theorem mkW_mem_Xfix_iff [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    (hwlb : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ g ∈ LB M Q B, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) →
        w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
    (w : S.Wsub) :
    S.mkW w ∈ S.Xfix ↔ (w : M₀.E) ∈
      M₀.img ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) := by
  rw [S.mem_Xfix_iff_LB h34 hs]
  constructor
  · intro hfix
    obtain ⟨x, hxW, hxQ, hxw⟩ := S.mem_Wsub.mp w.2
    have hall : ∀ g ∈ LB M Q B, ⁅g, x⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro g hg
      have hgR := le_Rt (M := M) (LB M Q B) S.ht hg
      have hH : g ∈ H0 M Z := hc.Rt_le_H0 t hgR
      have h1 := (S.ActR_mkW_eq_iff).mp (hfix g hg)
      have hgQ : ⁅g, x⁆ ∈ Q := (comm_LB_mem_Wt' hc S.ht hg hxW).1
      rw [← hxw] at h1
      have h2 : actM φ g (M₀.π x) - M₀.π x ∈ S.Vsub := h1
      rw [← S.pi_comm hH hxQ] at h2
      exact (M₀.mem_img_iff sec39_Z_le_Vt hgQ).mp h2
    have hxX := hwlb x hxW hall
    rw [← hxw]
    exact M₀.pi_mem_img hxX hxQ
  · rintro ⟨z, hz, hzQ, hzw⟩ l hl
    have hlR := le_Rt (M := M) (LB M Q B) S.ht hl
    have hH : l ∈ H0 M Z := hc.Rt_le_H0 t hlR
    rw [ActR_mkW_eq_iff]
    show actM φ l (w : M₀.E) - w ∈ S.Vsub
    rw [← hzw, ← S.pi_comm hH hzQ]
    exact M₀.pi_mem_img (comm_LB_XB hc S.ht hl hz) (hc.Vt_le_Q t (comm_LB_XB hc S.ht hl hz))

theorem rho_opposite_aux [CharP K 2] {r : G} (hr : Sec7A hc t r)
    (pr : SL(2, K) × SL(2, K) →* SL(2, K))
    (hu : ∀ s s' : K, pr (M1.uSL s, M1.uSL s') ∈ borelSL K)
    (hl : pr (M1.lSL 1, M1.lSL 1) ∉ borelSL K) :
    pr (S.vd.ρ ⟨r, hr.mem⟩) ∉ borelSL K := by
  intro hg
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  let Hs : Subgroup ↥(Rt M (LB M Q B) t) := (borelSL K).comap (pr.comp S.vd.ρ)
  have hLBmem : ∀ l ∈ LB M Q B, pr (rhoV S.vd l) ∈ borelSL K := by
    intro l hl
    obtain ⟨s, s', h⟩ := S.rhoV_LB_eq hl
    rw [h]
    exact hu s s'
  have hLB : LB M Q B ≤ Hs.map (Rt M (LB M Q B) t).subtype := by
    intro l hl
    have hlR := le_Rt (M := M) (LB M Q B) S.ht hl
    refine ⟨⟨l, hlR⟩, ?_, rfl⟩
    show pr (S.vd.ρ ⟨l, hlR⟩) ∈ borelSL K
    rw [← rhoV_of_mem S.vd hlR]
    exact hLBmem l hl
  have hLAR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hr.gen ▸ le_sup_right
  have hLA : LB M Q (conjSubgroup r B) ≤ Hs.map (Rt M (LB M Q B) t).subtype := by
    intro l' hl'
    have hl'R := hLAR hl'
    refine ⟨⟨l', hl'R⟩, ?_, rfl⟩
    have hl'' : l' ∈ conjSubgroup r (LB M Q B) := by
      rw [← LB_conjSubgroup M Q B (fun m hm => hc.conj_Q_eq hm) hrM]
      exact hl'
    have hl0 : r⁻¹ * l' * r ∈ LB M Q B := mem_conjSubgroup.mp hl''
    have hl0R := le_Rt (M := M) (LB M Q B) S.ht hl0
    have hρ : rhoV S.vd l' = rhoV S.vd r * rhoV S.vd (r⁻¹ * l' * r) * (rhoV S.vd r)⁻¹ := by
      calc rhoV S.vd l' = rhoV S.vd (r * (r⁻¹ * l' * r) * r⁻¹) := by
            rw [show r * (r⁻¹ * l' * r) * r⁻¹ = l' by group]
        _ = _ := by
            rw [rhoV_mul S.vd ((Rt M (LB M Q B) t).mul_mem hr.mem hl0R)
              ((Rt M (LB M Q B) t).inv_mem hr.mem), rhoV_mul S.vd hr.mem hl0R,
              rhoV_inv S.vd hr.mem]
    show pr (S.vd.ρ ⟨l', hl'R⟩) ∈ borelSL K
    rw [← rhoV_of_mem S.vd hl'R, hρ, map_mul, map_mul, map_inv, rhoV_of_mem S.vd hr.mem]
    exact (borelSL K).mul_mem ((borelSL K).mul_mem hg (hLBmem _ hl0)) ((borelSL K).inv_mem hg)
  have hle : Rt M (LB M Q B) t ≤ Hs.map (Rt M (LB M Q B) t).subtype :=
    calc Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B) := hr.gen
      _ ≤ _ := sup_le hLB hLA
  obtain ⟨x, hx⟩ := S.vd.ρ_surj (M1.lSL 1, M1.lSL 1)
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [hyx'] at hy
  have h1 : pr (S.vd.ρ x) ∈ borelSL K := hy
  rw [hx] at h1
  exact hl h1

theorem rho_opposite [CharP K 2] {r : G} (hr : Sec7A hc t r) :
    ((S.vd.ρ ⟨r, hr.mem⟩).1 : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      ((S.vd.ρ ⟨r, hr.mem⟩).2 : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  have hlK : M1.lSL (1 : K) ∉ borelSL K := by
    intro h'
    have h'' : ((M1.lSL (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := h'
    simp [M1.lSL, M1.lMat] at h''
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact S.rho_opposite_aux hr (MonoidHom.fst _ _) (fun s s' => rfl) (fun h' => hlK h') h
  · exact S.rho_opposite_aux hr (MonoidHom.snd _ _) (fun s s' => rfl) (fun h' => hlK h') h

include S in
theorem actM_img_XB {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {XA XB : Subgroup G}
    (hconj : conjSubgroup r XB = XA) (hXBQ : XB ≤ Q) {u : M₀.E} (hu : u ∈ M₀.img XB) :
    actM φ r u ∈ M₀.img XA := by
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hrH := hc.Rt_le_H0 t hrR
  obtain ⟨z, hz, hzQ, rfl⟩ := hu
  rw [← S.pi_conj hrH hzQ]
  have hzA : r * z * r⁻¹ ∈ XA := by
    rw [← hconj]
    exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using hz)
  exact M₀.pi_mem_img hzA
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) z).mp hzQ)

include S in
theorem exists_actM_img_XA {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {XA XB : Subgroup G}
    (hconj : conjSubgroup r XB = XA) (hXBQ : XB ≤ Q) {u' : M₀.E} (hu' : u' ∈ M₀.img XA) :
    ∃ u ∈ M₀.img XB, u' = actM φ r u := by
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hrH := hc.Rt_le_H0 t hrR
  obtain ⟨z', hz', hz'Q, rfl⟩ := hu'
  have hzB : r⁻¹ * z' * r ∈ XB := by
    rw [← hconj] at hz'
    exact mem_conjSubgroup.mp hz'
  have hzQ : r⁻¹ * z' * r ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hrM)) z').mp hz'Q
    rwa [inv_inv] at h
  refine ⟨M₀.π (r⁻¹ * z' * r), M₀.pi_mem_img hzB hzQ, ?_⟩
  rw [← S.pi_conj hrH hzQ]
  congr 1
  group

theorem isCompl_Xfix [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    {r : G} (hr : Sec7A hc t r) {V W XA XB : Subgroup G}
    (hV : V = Vt M (LB M Q B) B Z t) (hW : W = Wt Q V)
    (hXA : XA = (QB (conjSubgroup r B) ⊓ W) ⊔ V) (hXB : XB = (QB B ⊓ W) ⊔ V)
    (hdir : IsDirectSumSec W V XA XB)
    (hwlb : ∀ w ∈ W, (∀ g ∈ LB M Q B, ⁅g, w⁆ ∈ V) → w ∈ XB) :
    IsCompl S.Xfix
      (S.Xfix.map ((S.Act (S.vd.ρ ⟨r, hr.mem⟩) : S.Wq ≃ₗ[K] S.Wq) : S.Wq →ₗ[K] S.Wq)) := by
  obtain ⟨hVXA, hXAW, hVXB, hXBW, hsup, hinf⟩ := hdir
  have hrR := hr.mem
  have hconj : conjSubgroup r XB = XA := by
    rw [hXA, hXB, hW, hV]
    exact conj_XB_eq hc S.ht hrR
  have hWQ : W ≤ Q := by
    rw [hW]
    exact inf_le_left
  have hXAQ : XA ≤ Q := hXAW.trans hWQ
  have hXBQ : XB ≤ Q := hXBW.trans hWQ
  have hZV : Z ≤ V := by
    rw [hV]
    exact sec39_Z_le_Vt
  have hZXB : Z ≤ XB := hZV.trans hVXB
  have hVs : ∀ z, z ∈ M₀.img V ↔ z ∈ S.Vsub := fun z => by
    rw [S.mem_Vsub, hV]
  have hWs : ∀ z, z ∈ M₀.img W ↔ z ∈ S.Wsub := fun z => by
    rw [S.mem_Wsub, hW, hV]
  have hwlb' : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ g ∈ LB M Q B, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) →
        w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
    subst hV hW hXB
    exact hwlb
  have hXBiff : ∀ w : S.Wsub, S.mkW w ∈ S.Xfix ↔ (w : M₀.E) ∈ M₀.img XB := by
    intro w
    rw [S.mkW_mem_Xfix_iff h34 hs hwlb' w, hXB, hW, hV]
  have hfmk : ∀ u : S.Wsub,
      (S.Act (S.vd.ρ ⟨r, hr.mem⟩) : S.Wq ≃ₗ[K] S.Wq) (S.mkW u) = S.mkW (S.actWsub ⟨r, hrR⟩ u) :=
    fun u => S.Act_rho_mk ⟨r, hrR⟩ u
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx'
    obtain ⟨u, rfl⟩ := S.mkW_surjective y
    have hu := (hXBiff u).mp hy
    have hfu : ((S.Act (S.vd.ρ ⟨r, hr.mem⟩) : S.Wq ≃ₗ[K] S.Wq) : S.Wq →ₗ[K] S.Wq) (S.mkW u) =
        S.mkW (S.actWsub ⟨r, hrR⟩ u) := hfmk u
    rw [hfu] at hx ⊢
    have hv := (hXBiff _).mp hx
    have hA : actM φ r (u : M₀.E) ∈ M₀.img XA := S.actM_img_XB hrR hconj hXBQ hu
    obtain ⟨z, hz, hzQ, hzπ⟩ := hA
    have hzXB : z ∈ XB := by
      refine (M₀.mem_img_iff hZXB hzQ).mp ?_
      rw [hzπ]
      exact hv
    have hzV : z ∈ V := by
      have : z ∈ XA ⊓ XB := ⟨hz, hzXB⟩
      rwa [hinf] at this
    refine S.mkW_eq_zero_iff.mpr ?_
    show actM φ (r : G) (u : M₀.E) ∈ S.Vsub
    rw [← hzπ]
    exact (hVs _).mp (M₀.pi_mem_img hzV hzQ)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨w, rfl⟩ := S.mkW_surjective x
    obtain ⟨z, hzW, hzQ, hzw⟩ := S.mem_Wsub.mp w.2
    have hz' : z ∈ XA ⊔ XB := by
      rw [hsup, hW, hV]
      exact hzW
    have hpz := pi_mem_img_sup (M₀ := M₀) hXAQ hXBQ hz'
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hpz
    obtain ⟨u, hu, hau⟩ := S.exists_actM_img_XA hrR hconj hXBQ ha
    have huW : u ∈ S.Wsub := (hWs u).mp (M₀.img_mono hXBW hu)
    have hbW : b ∈ S.Wsub := (hWs b).mp (M₀.img_mono hXBW hb)
    have hsum : S.mkW w = S.mkW ⟨b, hbW⟩ +
        ((S.Act (S.vd.ρ ⟨r, hr.mem⟩) : S.Wq ≃ₗ[K] S.Wq) : S.Wq →ₗ[K] S.Wq)
          (S.mkW ⟨u, huW⟩) := by
      have hfu : ((S.Act (S.vd.ρ ⟨r, hr.mem⟩) : S.Wq ≃ₗ[K] S.Wq) : S.Wq →ₗ[K] S.Wq)
          (S.mkW ⟨u, huW⟩) = S.mkW (S.actWsub ⟨r, hrR⟩ ⟨u, huW⟩) := hfmk ⟨u, huW⟩
      rw [hfu, ← map_add]
      congr 1
      apply Subtype.ext
      show (w : M₀.E) = b + actM φ r u
      rw [← hzw, ← hab, hau, add_comm]
    rw [hsum]
    exact Submodule.add_mem_sup ((hXBiff _).mpr hb)
      (Submodule.mem_map.mpr ⟨S.mkW ⟨u, huW⟩, (hXBiff _).mpr hu, hfmk ⟨u, huW⟩ ▸ rfl⟩)

theorem eq_zero_of_fix_Gamma
    (hwr : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ g ∈ Rt M (LB M Q B) t, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) →
        w ∈ Vt M (LB M Q B) B Z t)
    (x : S.Wq) (hx : ∀ γ, S.Act γ x = x) : x = 0 := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨z, hzW, hzQ, hzw⟩ := S.mem_Wsub.mp w.2
  rw [mkW_eq_zero_iff]
  have hzV : z ∈ Vt M (LB M Q B) B Z t := by
    refine hwr z hzW fun g hg => ?_
    have hgH := hc.Rt_le_H0 t hg
    have h0 := hx (S.vd.ρ ⟨g, hg⟩)
    rw [S.Act_rho] at h0
    have h1 := (S.ActR_mkW_eq_iff).mp h0
    rw [← hzw] at h1
    have h2 : actM φ g (M₀.π z) - M₀.π z ∈ S.Vsub := h1
    rw [← S.pi_comm hgH hzQ] at h2
    exact (M₀.mem_img_iff sec39_Z_le_Vt (S.comm_mem_Q (hc.Rt_le_M t hg) hzQ)).mp h2
  rw [← hzw]
  exact M₀.pi_mem_img hzV (hc.Vt_le_Q t hzV)

end SetupW

end Setup

end HS9

end CFSG.RankThree.GF2n.Stroth80
