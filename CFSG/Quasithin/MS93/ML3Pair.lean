module

public import CFSG.Quasithin.MS93.ML3Sec

public section

namespace CFSG.Quasithin.MS93.ML3

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped commutatorElement

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem conj_comm (g x w : 𝔾) : ⁅g * x * g⁻¹, w⁆ = g * ⁅x, g⁻¹ * w * g⁆ * g⁻¹ := by
  rw [conj_commutatorElement]
  congr 1
  group

theorem conj_mem_centralizer_of {V : Subgroup 𝔾} {g d : 𝔾} (hV : ∀ v ∈ V, g⁻¹ * v * g ∈ V)
    (hd : d ∈ Subgroup.centralizer (V : Set 𝔾)) :
    g * d * g⁻¹ ∈ Subgroup.centralizer (V : Set 𝔾) := by
  rw [Subgroup.mem_centralizer_iff] at hd ⊢
  intro v hv
  have h := hd _ (hV v hv)
  calc v * (g * d * g⁻¹) = g * (g⁻¹ * v * g * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * d * g⁻¹ * v := by group

theorem smul_eq_zero_of_smul_eq {v : Fin 3 → F} (hv : v ∉ pt0) {a b : F}
    (h : a • v = b • (![1, 0, 0] + v)) : a • v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h0 h1 h2
  have hab : a = b := by
    rw [mem_pt0, not_and_or] at hv
    rcases hv with hv1 | hv2
    · exact mul_right_cancel₀ hv1 (by simpa using h1)
    · exact mul_right_cancel₀ hv2 (by simpa using h2)
  subst hab
  have ha : a = 0 := by
    have : a * v 0 = a * (1 + v 0) := by simpa using h0
    linear_combination -this
  rw [ha, zero_smul]

structure Setup17 (L Z W U K X : Subgroup 𝔾)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (dual : Bool) where
  NZ : NatSec L Z ⊥ α dual
  NU : NatSec L U K α false
  surj : Function.Surjective α
  LW : L ≤ Subgroup.normalizer (W : Set 𝔾)
  ZU : ⁅Z, U⁆ = ⊥
  ZW : ⁅Z, W⁆ = ⊥
  UW : ⁅U, W⁆ ≤ Z
  XU : X ≤ U
  gen : U = Subgroup.closure {u | ∃ l : ↥L, ∃ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ = u}
  stab : ∀ l : ↥L, toSL3 α l ∈ ptStab → ∀ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ ∈ X
  levi : ∀ l : ↥L, toSL3 α l ∈ ptLevi → ∀ x ∈ X, x⁻¹ * ((l : 𝔾) * x * (l : 𝔾)⁻¹) ∈ K
  ne : ⁅X, W⁆ ≠ ⊥
  card : Nat.card ↥⁅X, W⁆ ≤ Nat.card F ^ 2

namespace Setup17

variable {L Z W U K X : Subgroup 𝔾} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
  {dual : Bool} (S : Setup17 L Z W U K X α dual)
include S

theorem comm_mem {u w : 𝔾} (hu : u ∈ U) (hw : w ∈ W) : ⁅u, w⁆ ∈ Z :=
  S.UW (Subgroup.commutator_mem_commutator hu hw)

theorem conj_mem_W (l : ↥L) {w : 𝔾} (hw : w ∈ W) : (l : 𝔾) * w * (l : 𝔾)⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp (S.LW l.2) w).mp hw

theorem inv_conj_mem_W (l : ↥L) {w : 𝔾} (hw : w ∈ W) : (l : 𝔾)⁻¹ * w * (l : 𝔾) ∈ W := by
  have := S.conj_mem_W l⁻¹ hw
  rwa [Subgroup.coe_inv, inv_inv] at this

theorem XW_le : ⁅X, W⁆ ≤ Z :=
  (Subgroup.commutator_mono S.XU le_rfl).trans S.UW

theorem exists_conj {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ l : ↥L, ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v := by
  obtain ⟨g, hg⟩ := exists_mulVec_e0_eq hv
  obtain ⟨l, rfl⟩ := toSL3_surjective S.surj g
  exact ⟨l, hg⟩

theorem conj_mem_XW (l : ↥L) (hl : toSL3 α l ∈ (ptStab : Subgroup (SL3 F))) {z : 𝔾}
    (hz : z ∈ ⁅X, W⁆) : (l : 𝔾) * z * (l : 𝔾)⁻¹ ∈ ⁅X, W⁆ :=
  conj_mem_commutator (fun x hx => S.stab l hl x hx) (fun _ hw => S.conj_mem_W l hw) hz

theorem coordU_mem_pt0 {x : 𝔾} (hx : x ∈ X) : S.NU.coord x ∈ pt0 := by
  have h : S.NU.coord x ∈ fixN (ptLevi : Subgroup (SL3 F)) := by
    intro g hg
    obtain ⟨l, rfl⟩ := toSL3_surjective S.surj g
    have hxU := S.XU hx
    have h0 := (S.NU.coord_eq_zero_iff (U.mul_mem (U.inv_mem hxU) (S.NU.conj_mem l hxU))).mpr
      (S.levi l hg x hx)
    rw [S.NU.coord_mul (U.inv_mem hxU) (S.NU.conj_mem l hxU), S.NU.coord_inv hxU,
      S.NU.coord_conj l hxU, natAct_false, neg_add_eq_zero] at h0
    exact h0.symm
  rwa [ptLevi, fixN_ptLevi] at h

theorem decomp_mem [CharP F 2] {x : 𝔾} (hx : x ∈ X) (l l' : ↥L)
    (hl' : ((toSL3 α l' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      ![1, 0, 0] + ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) :
    (x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹))⁻¹ * ((l : 𝔾) * x * (l : 𝔾)⁻¹) ∈ K := by
  have hxU := S.XU hx
  apply S.NU.inv_mul_mem_of_coord_eq (U.mul_mem hxU (S.NU.conj_mem l' hxU))
    (S.NU.conj_mem l hxU)
  have hx0 := eq_smul_e0_of_mem_pt0 (S.coordU_mem_pt0 hx)
  rw [S.NU.coord_mul hxU (S.NU.conj_mem l' hxU), S.NU.coord_conj l' hxU, S.NU.coord_conj l hxU,
    natAct_false, natAct_false, hx0, Matrix.mulVec_smul, Matrix.mulVec_smul, hl', smul_add,
    ← add_assoc, ← two_smul F, CharTwo.two_eq_zero, zero_smul, zero_add]

end Setup17

section Natural

variable {L Z W U K X : Subgroup 𝔾} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

namespace Setup17

theorem img_XW_ne_top [Finite F] {dual : Bool} (S : Setup17 L Z W U K X α dual)
    (h : ∀ y, y ∈ S.NZ.img ⁅X, W⁆) : False := by
  have hZle : Z ≤ ⁅X, W⁆ := fun z hz => by
    obtain ⟨z', hz'H, hz'Z, hz'⟩ := S.NZ.mem_img.mp (h (S.NZ.coord z))
    rw [← S.NZ.eq_of_coord_eq hz'Z hz hz']
    exact hz'H
  have hcard := S.card
  rw [le_antisymm S.XW_le hZle, S.NZ.card_eq] at hcard
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have := Nat.pow_lt_pow_right hq (show 2 < 3 by norm_num)
  omega

theorem coordZ_comm_pt0 [Finite F] (S : Setup17 L Z W U K X α false) {x w : 𝔾} (hx : x ∈ X)
    (hw : w ∈ W) : S.NZ.coord ⁅x, w⁆ ∈ pt0 := by
  have hT : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ∀ y ∈ S.NZ.img ⁅X, W⁆,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S.NZ.img ⁅X, W⁆ := by
    rintro g hg _ hy
    obtain ⟨z, hzH, hzZ, rfl⟩ := S.NZ.mem_img.mp hy
    obtain ⟨l, rfl⟩ := toSL3_surjective S.surj g
    exact S.NZ.mem_img.mpr ⟨_, S.conj_mem_XW l (ptLevi_le_ptStab hg) hzH, S.NZ.conj_mem l hzZ,
      S.NZ.coord_conj l hzZ⟩
  rcases ptLevi_invariant_cases _ hT with h | h
  · exact h _ (S.NZ.mem_img.mpr
      ⟨⁅x, w⁆, Subgroup.commutator_mem_commutator hx hw, S.comm_mem (S.XU hx) hw, rfl⟩)
  · exact (S.img_XW_ne_top h).elim

theorem coordZ_comm_conj [Finite F] (S : Setup17 L Z W U K X α false) (l : ↥L) {x w : 𝔾}
    (hx : x ∈ X) (hw : w ∈ W) : ∃ a : F, S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ =
      a • (((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := by
  have hw' := S.inv_conj_mem_W l hw
  have hc := S.comm_mem (S.XU hx) hw'
  obtain ⟨a, ha⟩ : ∃ a : F, S.NZ.coord ⁅x, (l : 𝔾)⁻¹ * w * (l : 𝔾)⁆ = a • ![1, 0, 0] :=
    ⟨_, eq_smul_e0_of_mem_pt0 (S.coordZ_comm_pt0 hx hw')⟩
  refine ⟨a, ?_⟩
  rw [conj_comm, S.NZ.coord_conj l hc, ha, natAct_false, Matrix.mulVec_smul]

end Setup17

end Natural

section PartOne

variable {L Z W U C X : Subgroup 𝔾} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

namespace Setup17

variable (S : Setup17 L Z W U C X α false) (hZC : Z ≤ C) (hCL : ⁅C, L⁆ ≤ Z)
include S hZC hCL

theorem conj_comm_of_mem_C (l : ↥L) {c w : 𝔾} (hc : c ∈ C) (hw : w ∈ W) :
    (l : 𝔾) * ⁅c, w⁆ * (l : 𝔾)⁻¹ = ⁅c, (l : 𝔾) * w * (l : 𝔾)⁻¹⁆ := by
  have hz : ⁅(l : 𝔾), c⁆ ∈ Z := by
    rw [← commutatorElement_inv]
    exact Z.inv_mem (hCL (Subgroup.commutator_mem_commutator hc l.2))
  have hlc : (l : 𝔾) * c * (l : 𝔾)⁻¹ = ⁅(l : 𝔾), c⁆ * c := by
    rw [commutatorElement_def]
    group
  have hw' := S.conj_mem_W l hw
  rw [conj_commutatorElement, hlc,
    comm_mul_left S.ZU S.UW (S.NU.le (hZC hz)) (S.NU.le hc) hw',
    commutatorElement_eq_one_iff_mul_comm.mpr (commute_of_commutator_eq_bot S.ZW hz hw'),
    mul_one]

theorem comm_eq_one_of_mem_C {c : 𝔾} (hc : c ∈ C) (T : AddSubgroup (Fin 3 → F))
    {y₀ : Fin 3 → F} (hy₀ : y₀ ∉ T) (hT : ∀ w ∈ W, S.NZ.coord ⁅c, w⁆ ∈ T) {w : 𝔾}
    (hw : w ∈ W) : ⁅c, w⁆ = 1 := by
  by_contra h1
  have hHL : ∀ l : ↥L, ∀ h ∈ Subgroup.closure {z | ∃ w ∈ W, ⁅c, w⁆ = z},
      (l : 𝔾) * h * (l : 𝔾)⁻¹ ∈ Subgroup.closure {z | ∃ w ∈ W, ⁅c, w⁆ = z} := fun l h hh => by
    refine conj_mem_closure (fun s hs => ?_) hh
    obtain ⟨w', hw', rfl⟩ := hs
    rw [S.conj_comm_of_mem_C hZC hCL l hc hw']
    exact Subgroup.subset_closure ⟨_, S.conj_mem_W l hw', rfl⟩
  have hcU := S.NU.le hc
  have hle := S.NZ.le_of_invariant S.surj hHL (Subgroup.subset_closure ⟨w, hw, rfl⟩)
    (S.comm_mem hcU hw) h1
  have hHT : Subgroup.closure {z | ∃ w ∈ W, ⁅c, w⁆ = z} ≤ S.NZ.pre T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w', hw', rfl⟩
    exact S.NZ.mem_pre.mpr ⟨S.comm_mem hcU hw', hT w' hw'⟩
  obtain ⟨z, hz, hzy⟩ := S.NZ.exists_coord_eq y₀
  have := (S.NZ.mem_pre.mp (hHT (hle hz))).2
  rw [hzy] at this
  exact hy₀ this

theorem comm_eq_one_of_centralizer [CharP F 2] [Finite F] {w : 𝔾} (hw : w ∈ W)
    (hwX : ∀ x ∈ X, ⁅x, w⁆ = 1) {u : 𝔾} (hu : u ∈ U) : ⁅u, w⁆ = 1 := by
  have key : ∀ (l : ↥L) (x : 𝔾), x ∈ X → ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ = 1 := by
    intro l x hx
    obtain ⟨v, hv⟩ : ∃ v, ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v :=
      ⟨_, rfl⟩
    by_cases hv0 : v ∈ pt0
    · exact hwX _ (S.stab l (mem_ptStab_iff_mulVec_e0.mpr (hv ▸ hv0)) x hx)
    have hne : ![1, 0, 0] + v ≠ 0 := by
      intro h
      apply hv0
      rw [mem_pt0]
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      exact ⟨by simpa using h1, by simpa using h2⟩
    obtain ⟨l', hl'⟩ := S.exists_conj hne
    have hxU := S.XU hx
    have hx'U : (l' : 𝔾) * x * (l' : 𝔾)⁻¹ ∈ U := S.NU.conj_mem l' hxU
    have hxvU : (l : 𝔾) * x * (l : 𝔾)⁻¹ ∈ U := S.NU.conj_mem l hxU
    have hxx'U : x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹) ∈ U := U.mul_mem hxU hx'U
    have hcC := S.decomp_mem hx l l' (by rw [hl', hv])
    have hcU := S.NU.le hcC
    have hsplit : ∀ w' ∈ W, ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w'⁆ =
        ⁅(x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹))⁻¹ * ((l : 𝔾) * x * (l : 𝔾)⁻¹), w'⁆ *
          (⁅(l' : 𝔾) * x * (l' : 𝔾)⁻¹, w'⁆ * ⁅x, w'⁆) := fun w' hw' => by
      conv_lhs => rw [← mul_inv_cancel_left (x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹))
        ((l : 𝔾) * x * (l : 𝔾)⁻¹)]
      rw [comm_mul_left S.ZU S.UW hxx'U hcU hw', comm_mul_left S.ZU S.UW hxU hx'U hw']
    let T : AddSubgroup (Fin 3 → F) :=
      { carrier := {y | y 1 * v 2 = y 2 * v 1}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, Pi.add_apply] at ha hb ⊢
          rw [add_mul, add_mul, ha, hb]
        neg_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq, Pi.neg_apply] at ha ⊢
          rw [neg_mul, neg_mul, ha] }
    have hT : ∀ w' ∈ W, S.NZ.coord ⁅(x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹))⁻¹ *
        ((l : 𝔾) * x * (l : 𝔾)⁻¹), w'⁆ ∈ T := by
      intro w' hw'
      have hm1 := S.comm_mem hxvU hw'
      have hm2 := S.comm_mem hx'U hw'
      have hm3 := S.comm_mem hxU hw'
      have hcw := hsplit w' hw'
      rw [← mul_inv_eq_iff_eq_mul] at hcw
      rw [← hcw, S.NZ.coord_mul hm1 (Z.inv_mem (Z.mul_mem hm2 hm3)),
        S.NZ.coord_inv (Z.mul_mem hm2 hm3), S.NZ.coord_mul hm2 hm3]
      obtain ⟨a, ha⟩ := S.coordZ_comm_conj l hx hw'
      obtain ⟨b, hb⟩ := S.coordZ_comm_conj l' hx hw'
      obtain ⟨d, hd⟩ : ∃ d : F, S.NZ.coord ⁅x, w'⁆ = d • ![1, 0, 0] :=
        ⟨_, eq_smul_e0_of_mem_pt0 (S.coordZ_comm_pt0 hx hw')⟩
      rw [ha, hb, hd, hl', hv]
      show _ * v 2 = _ * v 1
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      simp
      ring
    have hy₀ : ∃ y₀, y₀ ∉ T := by
      rw [mem_pt0, not_and_or] at hv0
      rcases hv0 with h1 | h2
      · refine ⟨![0, 0, 1], fun h => h1 ?_⟩
        have h' : (![0, 0, 1] : Fin 3 → F) 1 * v 2 = (![0, 0, 1] : Fin 3 → F) 2 * v 1 := h
        simp at h'
        exact h'.symm
      · refine ⟨![0, 1, 0], fun h => h2 ?_⟩
        have h' : (![0, 1, 0] : Fin 3 → F) 1 * v 2 = (![0, 1, 0] : Fin 3 → F) 2 * v 1 := h
        simpa using h'
    obtain ⟨y₀, hy₀⟩ := hy₀
    have hc1 := S.comm_eq_one_of_mem_C hZC hCL hcC T hy₀ hT hw
    have h1 : ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ = ⁅(l' : 𝔾) * x * (l' : 𝔾)⁻¹, w⁆ := by
      rw [hsplit w hw, hc1, hwX x hx, one_mul, mul_one]
    obtain ⟨a, ha⟩ := S.coordZ_comm_conj l hx hw
    obtain ⟨b, hb⟩ := S.coordZ_comm_conj l' hx hw
    rw [hv] at ha
    rw [hl'] at hb
    have hab : a • v = b • (![1, 0, 0] + v) := by rw [← ha, ← hb, h1]
    apply S.NZ.eq_one_of_coord_eq_zero (S.comm_mem hxvU hw)
    rw [ha]
    exact smul_eq_zero_of_smul_eq hv0 hab
  exact comm_mem_of_closure S.ZU S.UW S.gen hw (H := ⊥)
    (by rintro _ ⟨l, x, hx, rfl⟩; rw [Subgroup.mem_bot]; exact key l x hx) hu

theorem comm_levi_comm_eq_one [Finite F] {x : 𝔾} (hx : x ∈ X) (l : ↥L)
    (hl : toSL3 α l ∈ (ptLevi : Subgroup (SL3 F))) {w : 𝔾} (hw : w ∈ W) :
    ⁅⁅x, (l : 𝔾)⁆, w⁆ = 1 := by
  have hcX : ⁅x, (l : 𝔾)⁆ ∈ X := by
    have he : ⁅x, (l : 𝔾)⁆ = x * ((l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact X.mul_mem hx (S.stab l (ptLevi_le_ptStab hl) _ (X.inv_mem hx))
  have hcC : ⁅x, (l : 𝔾)⁆ ∈ C := by
    have h := S.levi l hl x⁻¹ (X.inv_mem hx)
    have he : ⁅x, (l : 𝔾)⁆ = x⁻¹⁻¹ * ((l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact h
  refine S.comm_eq_one_of_mem_C hZC hCL hcC (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup
    (y₀ := ![0, 1, 0]) ?_ (fun w' hw' => S.coordZ_comm_pt0 hcX hw') hw
  rw [Submodule.mem_toAddSubgroup, mem_pt0]
  simp

theorem comm_comm_levi_eq_one [Finite F] (l : ↥L) (hl : toSL3 α l ∈ (ptLevi : Subgroup (SL3 F)))
    {w x : 𝔾} (hw : w ∈ W) (hx : x ∈ X) : ⁅⁅(l : 𝔾), w⁆, x⁆ = 1 := by
  set L₀ : Subgroup 𝔾 := ((ptLevi : Subgroup (SL3 F)).comap (toSL3 α)).map L.subtype with hL₀
  have hmemL₀ : ∀ h ∈ L₀, ∃ l' : ↥L, toSL3 α l' ∈ (ptLevi : Subgroup (SL3 F)) ∧ (l' : 𝔾) = h := by
    rintro _ ⟨l', hl', rfl⟩
    exact ⟨l', hl', rfl⟩
  have h1 : ⁅⁅W, X⁆, L₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro w' hw' x' hx'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨l', hl', rfl⟩ := hmemL₀ h hh
    have hc := S.comm_mem (S.XU hx') hw'
    have hz : ⁅w', x'⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem hc
    have hz0 : S.NZ.coord ⁅w', x'⁆ ∈ pt0 := by
      rw [← commutatorElement_inv, S.NZ.coord_inv hc]
      exact neg_mem (S.coordZ_comm_pt0 hx' hw')
    have heq : (l' : 𝔾) * ⁅w', x'⁆ * (l' : 𝔾)⁻¹ = ⁅w', x'⁆ := by
      apply S.NZ.eq_of_coord_eq (S.NZ.conj_mem l' hz) hz
      rw [S.NZ.coord_conj l' hz, natAct_false, mulVec_of_mem_ptLevi hl' hz0]
    calc (l' : 𝔾) * ⁅w', x'⁆ = (l' : 𝔾) * ⁅w', x'⁆ * (l' : 𝔾)⁻¹ * l' := by group
      _ = ⁅w', x'⁆ * l' := by rw [heq]
  have h2 : ⁅⁅X, L₀⁆, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro x' hx' h hh
    obtain ⟨l', hl', rfl⟩ := hmemL₀ h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    have := S.comm_levi_comm_eq_one hZC hCL hx' l' hl' hw'
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hmem : ⁅⁅(l : 𝔾), w⁆, x⁆ ∈ ⁅⁅L₀, W⁆, X⁆ :=
    Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator ⟨l, hl, rfl⟩ hw) hx
  rwa [h3, Subgroup.mem_bot] at hmem

omit hZC hCL in
theorem conj_mem_centralizer (l : ↥L) {d : 𝔾} (hd : d ∈ Subgroup.centralizer (U : Set 𝔾)) :
    (l : 𝔾) * d * (l : 𝔾)⁻¹ ∈ Subgroup.centralizer (U : Set 𝔾) :=
  conj_mem_centralizer_of (fun u hu => by
    have := S.NU.conj_mem l⁻¹ hu
    rwa [Subgroup.coe_inv, inv_inv] at this) hd

theorem comm_L_mem_centralizer [CharP F 2] [Finite F] (l : ↥L) {w : 𝔾} (hw : w ∈ W) :
    ⁅(l : 𝔾), w⁆ ∈ Subgroup.centralizer (U : Set 𝔾) := by
  let P : Subgroup ↥L :=
    { carrier := {k | ∀ w ∈ W, ⁅((k : ↥L) : 𝔾), w⁆ ∈ Subgroup.centralizer (U : Set 𝔾)}
      one_mem' := fun w _ => by
        rw [OneMemClass.coe_one, commutatorElement_one_left]
        exact Subgroup.one_mem _
      mul_mem' := fun {k k'} hk hk' w hw => by
        have he : ⁅((k * k' : ↥L) : 𝔾), w⁆ =
            (k : 𝔾) * ⁅(k' : 𝔾), w⁆ * (k : 𝔾)⁻¹ * ⁅(k : 𝔾), w⁆ := by
          rw [Subgroup.coe_mul, commutatorElement_def, commutatorElement_def,
            commutatorElement_def]
          group
        rw [he]
        exact Subgroup.mul_mem _ (S.conj_mem_centralizer k (hk' w hw)) (hk w hw)
      inv_mem' := fun {k} hk w hw => by
        have he : ⁅((k⁻¹ : ↥L) : 𝔾), w⁆ = ⁅(k : 𝔾), (k : 𝔾)⁻¹ * w * (k : 𝔾)⁆⁻¹ := by
          rw [Subgroup.coe_inv, commutatorElement_def, commutatorElement_def]
          group
        rw [he]
        exact Subgroup.inv_mem _ (hk _ (S.inv_conj_mem_W k hw)) }
  have hPn : P.Normal := ⟨fun k hk m w hw => by
    have he : ⁅((m * k * m⁻¹ : ↥L) : 𝔾), w⁆ =
        (m : 𝔾) * ⁅(k : 𝔾), (m : 𝔾)⁻¹ * w * (m : 𝔾)⁆ * (m : 𝔾)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def,
        commutatorElement_def]
      group
    rw [he]
    exact S.conj_mem_centralizer m (hk _ (S.inv_conj_mem_W m hw))⟩
  have hlevi : ∀ k : ↥L, toSL3 α k ∈ (ptLevi : Subgroup (SL3 F)) → k ∈ P := by
    intro k hk w hw
    have hdW : ⁅(k : 𝔾), w⁆ ∈ W := by
      rw [commutatorElement_def]
      exact W.mul_mem (S.conj_mem_W k hw) (W.inv_mem hw)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := S.comm_eq_one_of_centralizer hZC hCL hdW (fun x hx => by
      rw [← commutatorElement_inv, S.comm_comm_levi_eq_one hZC hCL k hk hw hx, inv_one]) hu
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have htop : P.map (toSL3 α) = ⊤ := by
    apply eq_top_of_ptLevi_le (hPn.map _ (toSL3_surjective S.surj))
    intro g hg
    obtain ⟨k, rfl⟩ := toSL3_surjective S.surj g
    exact ⟨k, hlevi k hg, rfl⟩
  have hl : l ∈ P := by
    obtain ⟨k, hk, hkl⟩ : toSL3 α l ∈ P.map (toSL3 α) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hker : k⁻¹ * l ∈ P := hlevi _ (by
      rw [map_mul, map_inv, hkl, inv_mul_cancel]
      exact Subgroup.one_mem _)
    have := P.mul_mem hk hker
    rwa [mul_inv_cancel_left] at this
  exact hl w hw

theorem comm_C_W_eq_one [CharP F 2] [Finite F] {c w : 𝔾} (hc : c ∈ C) (hw : w ∈ W) :
    ⁅c, w⁆ = 1 := by
  have hcU := S.NU.le hc
  have hz := S.comm_mem hcU hw
  apply S.NZ.eq_one_of_coord_eq_zero hz
  apply eq_zero_of_fixed
  intro g
  obtain ⟨l, rfl⟩ := toSL3_surjective S.surj g
  have hd := S.comm_L_mem_centralizer hZC hCL l hw
  have hdW : ⁅(l : 𝔾), w⁆ ∈ W := by
    rw [commutatorElement_def]
    exact W.mul_mem (S.conj_mem_W l hw) (W.inv_mem hw)
  have hconj : (l : 𝔾) * ⁅c, w⁆ * (l : 𝔾)⁻¹ = ⁅c, w⁆ := by
    rw [S.conj_comm_of_mem_C hZC hCL l hc hw]
    have he : (l : 𝔾) * w * (l : 𝔾)⁻¹ = ⁅(l : 𝔾), w⁆ * w := by
      rw [commutatorElement_def]
      group
    rw [he, comm_mul_right S.ZW S.UW hcU hdW hw,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hd c hcU),
      one_mul]
  rw [← natAct_false, ← S.NZ.coord_conj l hz, hconj]

theorem conclusions [CharP F 2] [Finite F] :
    ⁅C, W⁆ = ⊥ ∧ ⁅⁅W, L⁆, U⁆ = ⊥ ∧ U ⊓ Subgroup.centralizer (W : Set 𝔾) = C ∧
      W ⊓ Subgroup.centralizer (X : Set 𝔾) = W ⊓ Subgroup.centralizer (U : Set 𝔾) ∧
      ∀ w ∈ W, w ∉ Subgroup.centralizer (U : Set 𝔾) → ⁅U, Subgroup.zpowers w⁆ = Z := by
  have hCW : ∀ c ∈ C, c ∈ Subgroup.centralizer (W : Set 𝔾) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (commutatorElement_eq_one_iff_mul_comm.mp (S.comm_C_W_eq_one hZC hCL hc hw)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hCW
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro w hw l hl
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (S.comm_L_mem_centralizer hZC hCL ⟨l, hl⟩ hw)
  · refine le_antisymm (fun u hu => ?_) (fun c hc => ⟨S.NU.le hc, hCW c hc⟩)
    by_contra huC
    have hHL : ∀ l : ↥L, ∀ h ∈ U ⊓ Subgroup.centralizer (W : Set 𝔾),
        (l : 𝔾) * h * (l : 𝔾)⁻¹ ∈ U ⊓ Subgroup.centralizer (W : Set 𝔾) := fun l h hh =>
      ⟨S.NU.conj_mem l hh.1, conj_mem_centralizer_of (fun w hw => by
        have := S.conj_mem_W l⁻¹ hw
        rwa [Subgroup.coe_inv, inv_inv] at this) hh.2⟩
    apply S.ne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    obtain ⟨u', hu', -, hu'x⟩ := S.NU.exists_inv_mul_mem_of_invariant S.surj hHL hu hu.1 huC
      (S.XU hx)
    have he : x = u' * (u'⁻¹ * x) := by group
    rw [he]
    exact Subgroup.mul_mem _ hu'.2 (hCW _ hu'x)
  · refine le_antisymm (fun w hw => Subgroup.mem_inf.mpr ⟨hw.1, ?_⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le S.XU))
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := S.comm_eq_one_of_centralizer hZC hCL hw.1 (fun x hx =>
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hw.2 x hx)) hu
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  · intro w hw hwU
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu h hh
      exact S.comm_mem hu (Subgroup.zpowers_le.mpr hw hh)
    · obtain ⟨u₀, hu₀, hne⟩ : ∃ u ∈ U, ⁅u, w⁆ ≠ 1 := by
        by_contra h
        push Not at h
        apply hwU
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact commutatorElement_eq_one_iff_mul_comm.mp (h u hu)
      have hHL : ∀ l : ↥L, ∀ h ∈ Subgroup.closure {z | ∃ u ∈ U, ⁅u, w⁆ = z},
          (l : 𝔾) * h * (l : 𝔾)⁻¹ ∈ Subgroup.closure {z | ∃ u ∈ U, ⁅u, w⁆ = z} := by
        intro l h hh
        refine conj_mem_closure (fun s hs => ?_) hh
        obtain ⟨u, hu, rfl⟩ := hs
        have hd := S.comm_L_mem_centralizer hZC hCL l hw
        have hdW : ⁅(l : 𝔾), w⁆ ∈ W := by
          rw [commutatorElement_def]
          exact W.mul_mem (S.conj_mem_W l hw) (W.inv_mem hw)
        have hu' := S.NU.conj_mem l hu
        have he : (l : 𝔾) * w * (l : 𝔾)⁻¹ = ⁅(l : 𝔾), w⁆ * w := by
          rw [commutatorElement_def]
          group
        rw [conj_commutatorElement, he, comm_mul_right S.ZW S.UW hu' hdW hw,
          commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hd _ hu'),
          one_mul]
        exact Subgroup.subset_closure ⟨_, hu', rfl⟩
      refine (S.NZ.le_of_invariant S.surj hHL (Subgroup.subset_closure ⟨u₀, hu₀, rfl⟩)
        (S.comm_mem hu₀ hw) hne).trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers w)

end Setup17

end PartOne

end CFSG.Quasithin.MS93.ML3

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique ML3

theorem ms17i_holds : MS17i := by
  intro 𝔾 _ F _ _ n hF L Z W U C X α hα hZ hU hZC hCL hLW hZU hZW hUW hXU hgen hstab hlevi hne
    hcard
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hF'
  let S : Setup17 L Z W U C X α false :=
    { NZ := NatSec.ofIsSum hZ
      NU := NatSec.ofIsSum hU
      surj := hα
      LW := hLW
      ZU := hZU
      ZW := hZW
      UW := hUW
      XU := hXU
      gen := hgen
      stab := hstab
      levi := hlevi
      ne := hne
      card := hcard }
  exact S.conclusions hZC hCL

end CFSG.Quasithin.MS93
