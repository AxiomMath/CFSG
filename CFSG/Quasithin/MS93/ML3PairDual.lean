module

public import CFSG.Quasithin.MS93.ML3Pair

public section

namespace CFSG.Quasithin.MS93.ML3

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem dotProduct_e0 (y : Fin 3 → F) : y ⬝ᵥ ![1, 0, 0] = y 0 := by
  simp [dotProduct, Fin.sum_univ_three]

theorem dualMat_mulVec_of_mem_qPt {g : SL3 F} (hg : g ∈ (qPt : Subgroup (SL3 F)))
    {y : Fin 3 → F} (hy : y 0 = 0) : dualMat g *ᵥ y = y := by
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∀ y : Fin 3 → F, y 0 = 0 → dualMat g *ᵥ y = y}
      one_mem' := fun y _ => by
        show dualMat 1 *ᵥ y = y
        rw [dualMat_one, Matrix.one_mulVec]
      mul_mem' := fun {a b} ha hb y hy => by
        show dualMat (a * b) *ᵥ y = y
        rw [dualMat_mul, ← Matrix.mulVec_mulVec, hb y hy, ha y hy]
      inv_mem' := fun {a} ha y hy => by
        show dualMat a⁻¹ *ᵥ y = y
        conv_lhs => rw [← ha y hy]
        rw [Matrix.mulVec_mulVec, ← dualMat_mul, inv_mul_cancel, dualMat_one,
          Matrix.one_mulVec] }
  have hroot : ∀ j : Fin 3, j ≠ 0 → rootGroup 0 j ≤ P := by
    rintro j hj _ ⟨c, rfl⟩ y hy
    rw [dualMat_rootElt_mulVec hj.symm, hy, mul_zero, Pi.single_zero, add_zero]
  have hle : (qPt : Subgroup (SL3 F)) ≤ P :=
    sup_le (hroot 1 (by decide)) (hroot 2 (by decide))
  exact hle hg y hy

theorem exists_eq_smul_rot (φ : (Fin 3 → F) → Fin 3 → F)
    (hadd : ∀ y y', φ (y + y') = φ y + φ y') (h0 : ∀ c : F, φ (c • ![1, 0, 0]) = 0)
    (h1 : ∀ v : Fin 3 → F, v ∉ pt0 → ∀ b : F, φ (b • v) 0 = 0 ∧ φ (b • v) ⬝ᵥ v = 0) :
    ∃ t : F, ∀ y, φ y = ![0, -(t * y 2), t * y 1] := by
  have hφ0 : φ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have he1 : (![0, 1, 0] : Fin 3 → F) ∉ pt0 := by
    rw [mem_pt0]
    simp
  have he2 : (![0, 0, 1] : Fin 3 → F) ∉ pt0 := by
    rw [mem_pt0]
    simp
  have hA : ∀ a : F, φ (a • ![0, 1, 0]) = ![0, 0, φ (a • ![0, 1, 0]) 2] := by
    intro a
    obtain ⟨h0', h1'⟩ := h1 _ he1 a
    have h1'' : φ (a • ![0, 1, 0]) 1 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using h1'
    funext k
    fin_cases k
    · exact h0'
    · exact h1''
    · rfl
  have hB : ∀ b : F, φ (b • ![0, 0, 1]) = ![0, φ (b • ![0, 0, 1]) 1, 0] := by
    intro b
    obtain ⟨h0', h1'⟩ := h1 _ he2 b
    have h2'' : φ (b • ![0, 0, 1]) 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using h1'
    funext k
    fin_cases k
    · exact h0'
    · rfl
    · exact h2''
  set σ : F → F := fun a => φ (a • ![0, 1, 0]) 2 with hσ
  set τ : F → F := fun b => φ (b • ![0, 0, 1]) 1 with hτ
  have hsplit : ∀ a b : F, φ ![0, a, b] = ![0, τ b, σ a] := by
    intro a b
    have he : (![0, a, b] : Fin 3 → F) = a • ![0, 1, 0] + b • ![0, 0, 1] := by
      funext k
      fin_cases k <;> simp
    rw [he, hadd, hA, hB]
    funext k
    fin_cases k <;> simp [σ, τ]
  have hC : ∀ a b : F, τ b * a + σ a * b = 0 := by
    intro a b
    by_cases hab : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hab
      ring
    have hv : (![0, a, b] : Fin 3 → F) ∉ pt0 := by
      rw [mem_pt0]
      simpa using hab
    have h := (h1 _ hv 1).2
    rw [one_smul, hsplit] at h
    simpa [dotProduct, Fin.sum_univ_three] using h
  refine ⟨σ 1, fun y => ?_⟩
  have hσa : ∀ a, σ a = σ 1 * a := fun a => by
    have h1a := hC a 1
    have h11 := hC 1 1
    linear_combination h1a - a * h11
  have hτb : ∀ b, τ b = -(σ 1 * b) := fun b => by
    have h := hC 1 b
    linear_combination h
  have hy : y = y 0 • ![1, 0, 0] + ![0, y 1, y 2] := by
    funext k
    fin_cases k <;> simp
  rw [hy, hadd, h0, zero_add, hsplit, hσa, hτb]
  funext k
  fin_cases k <;> simp

variable {𝔾 : Type} [Group 𝔾] {L Z W U K X : Subgroup 𝔾}
  {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

namespace Setup17

theorem coordZ_comm_hyp0 [Finite F] (S : Setup17 L Z W U K X α true) {x w : 𝔾} (hx : x ∈ X)
    (hw : w ∈ W) : S.NZ.coord ⁅x, w⁆ 0 = 0 := by
  have hT : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ y ∈ S.NZ.img ⁅X, W⁆,
      dualMat g *ᵥ y ∈ S.NZ.img ⁅X, W⁆ := by
    rintro g hg _ hy
    obtain ⟨z, hzH, hzZ, rfl⟩ := S.NZ.mem_img.mp hy
    obtain ⟨l, rfl⟩ := toSL3_surjective S.surj g
    exact S.NZ.mem_img.mpr ⟨_, S.conj_mem_XW l hg hzH, S.NZ.conj_mem l hzZ,
      S.NZ.coord_conj l hzZ⟩
  rcases ptStab_dual_invariant_cases _ hT with h | h
  · exact h _ (S.NZ.mem_img.mpr
      ⟨⁅x, w⁆, Subgroup.commutator_mem_commutator hx hw, S.comm_mem (S.XU hx) hw, rfl⟩)
  · exact (S.img_XW_ne_top h).elim

theorem coordZ_comm_conj_dual [Finite F] (S : Setup17 L Z W U K X α true) (l : ↥L) {x w : 𝔾}
    (hx : x ∈ X) (hw : w ∈ W) : S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ ⬝ᵥ
      (((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) = 0 := by
  have hw' := S.inv_conj_mem_W l hw
  have hc := S.comm_mem (S.XU hx) hw'
  rw [conj_comm, S.NZ.coord_conj l hc, natAct_true, dualMat_mulVec_dotProduct, dotProduct_e0]
  exact S.coordZ_comm_hyp0 hx hw'

end Setup17

namespace Setup17

variable (S : Setup17 L Z W U (U ⊓ Subgroup.centralizer (W : Set 𝔾)) X α true)
include S

theorem exists_coordU_eq_smul (b : F) : ∃ x ∈ X, S.NU.coord x = b • ![1, 0, 0] := by
  obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x ∈ X, S.NU.coord x ≠ 0 := by
    by_contra h
    push Not at h
    apply S.ne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact ((S.NU.coord_eq_zero_iff (S.XU hx)).mp (h x hx)).2
  obtain ⟨a, ha⟩ : ∃ a : F, S.NU.coord x₀ = a • ![1, 0, 0] :=
    ⟨_, eq_smul_e0_of_mem_pt0 (S.coordU_mem_pt0 hx₀)⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hx₀0 ha
  by_cases hb : b = 0
  · exact ⟨1, X.one_mem, by rw [S.NU.coord_one, hb, zero_smul]⟩
  have ht : b / a ≠ 0 := div_ne_zero hb ha0
  obtain ⟨l, hl⟩ := toSL3_surjective S.surj (diagPt (b / a) ht)
  refine ⟨_, S.stab l (hl ▸ diagPt_mem_ptStab _ ht) x₀ hx₀, ?_⟩
  rw [S.NU.coord_conj l (S.XU hx₀), natAct_false, hl, ha, Matrix.mulVec_smul, diagPt_mulVec]
  funext k
  fin_cases k <;> simp
  field_simp

variable {w : 𝔾} (hw : w ∈ W) (hwX : ∀ x ∈ X, ⁅x, w⁆ = 1)
include hw hwX

omit hwX in
theorem coordZ_comm_eq_of_coordU_eq {u u' : 𝔾} (hu : u ∈ U) (hu' : u' ∈ U)
    (h : S.NU.coord u = S.NU.coord u') : S.NZ.coord ⁅u, w⁆ = S.NZ.coord ⁅u', w⁆ := by
  have hc := S.NU.inv_mul_mem_of_coord_eq hu' hu h.symm
  have hc1 : ⁅u'⁻¹ * u, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have he : u = u' * (u'⁻¹ * u) := by group
  rw [he, comm_mul_left S.ZU S.UW hu' hc.1 hw, hc1, one_mul]

theorem coordZ_comm_mem_perp [CharP F 2] [Finite F] {v : Fin 3 → F} (hv : v ∉ pt0) {b : F}
    {u : 𝔾} (hu : u ∈ U) (hub : S.NU.coord u = b • v) :
    S.NZ.coord ⁅u, w⁆ 0 = 0 ∧ S.NZ.coord ⁅u, w⁆ ⬝ᵥ v = 0 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (Submodule.zero_mem _)
  have hne : ![1, 0, 0] + v ≠ 0 := by
    intro h
    apply hv
    rw [mem_pt0]
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  obtain ⟨l, hl⟩ := S.exists_conj hv0
  obtain ⟨l', hl'⟩ := S.exists_conj hne
  obtain ⟨x, hx, hxb⟩ := S.exists_coordU_eq_smul b
  have hxU := S.XU hx
  have hx'U : (l' : 𝔾) * x * (l' : 𝔾)⁻¹ ∈ U := S.NU.conj_mem l' hxU
  have hxvU : (l : 𝔾) * x * (l : 𝔾)⁻¹ ∈ U := S.NU.conj_mem l hxU
  have hxv : S.NU.coord ((l : 𝔾) * x * (l : 𝔾)⁻¹) = b • v := by
    rw [S.NU.coord_conj l hxU, natAct_false, hxb, Matrix.mulVec_smul, hl]
  have h1 : S.NZ.coord ⁅u, w⁆ = S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ :=
    S.coordZ_comm_eq_of_coordU_eq hw hu hxvU (by rw [hub, hxv])
  have hdec := S.decomp_mem hx l l' (by rw [hl', hl])
  have hdec' : S.NU.coord (x * ((l' : 𝔾) * x * (l' : 𝔾)⁻¹)) =
      S.NU.coord ((l : 𝔾) * x * (l : 𝔾)⁻¹) := by
    have h0 := (S.NU.coord_eq_zero_iff (U.mul_mem (U.inv_mem (U.mul_mem hxU hx'U)) hxvU)).mpr
      hdec
    rw [S.NU.coord_mul (U.inv_mem (U.mul_mem hxU hx'U)) hxvU,
      S.NU.coord_inv (U.mul_mem hxU hx'U), neg_add_eq_zero] at h0
    exact h0
  have h2 : S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ =
      S.NZ.coord ⁅(l' : 𝔾) * x * (l' : 𝔾)⁻¹, w⁆ := by
    rw [← S.coordZ_comm_eq_of_coordU_eq hw (U.mul_mem hxU hx'U) hxvU hdec',
      comm_mul_left S.ZU S.UW hxU hx'U hw, hwX x hx, mul_one]
  have hpv := S.coordZ_comm_conj_dual l hx hw
  have hpe := S.coordZ_comm_conj_dual l' hx hw
  rw [hl] at hpv
  rw [hl'] at hpe
  rw [h1]
  refine ⟨?_, hpv⟩
  rw [← dotProduct_e0 (S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆)]
  have hsum : S.NZ.coord ⁅(l : 𝔾) * x * (l : 𝔾)⁻¹, w⁆ ⬝ᵥ (![1, 0, 0] + v) = 0 := by
    rw [h2]
    exact hpe
  rw [dotProduct_add, hpv, add_zero] at hsum
  exact hsum

theorem exists_coordZ_comm_eq [CharP F 2] [Finite F] :
    ∃ t : F, ∀ u ∈ U, S.NZ.coord ⁅u, w⁆ =
      ![0, -(t * S.NU.coord u 2), t * S.NU.coord u 1] := by
  choose s hsU hs using S.NU.exists_coord_eq
  have hf : ∀ u ∈ U, S.NZ.coord ⁅u, w⁆ = S.NZ.coord ⁅s (S.NU.coord u), w⁆ := fun u hu =>
    S.coordZ_comm_eq_of_coordU_eq hw hu (hsU _) (hs _).symm
  obtain ⟨t, ht⟩ := exists_eq_smul_rot (fun y => S.NZ.coord ⁅s y, w⁆)
    (fun y y' => by
      have hm := U.mul_mem (hsU y) (hsU y')
      rw [S.coordZ_comm_eq_of_coordU_eq hw (hsU (y + y')) hm
        (by rw [hs, S.NU.coord_mul (hsU y) (hsU y'), hs, hs]),
        comm_mul_left S.ZU S.UW (hsU y) (hsU y') hw,
        S.NZ.coord_mul (S.comm_mem (hsU y') hw) (S.comm_mem (hsU y) hw), add_comm])
    (fun c => by
      obtain ⟨x, hx, hxc⟩ := S.exists_coordU_eq_smul c
      rw [S.coordZ_comm_eq_of_coordU_eq hw (hsU _) (S.XU hx) (by rw [hs, hxc]), hwX x hx,
        S.NZ.coord_one])
    (fun v hv b => S.coordZ_comm_mem_perp hw hwX hv (hsU _) (hs _))
  exact ⟨t, fun u hu => by rw [hf u hu, ht]⟩

end Setup17

namespace Setup17

variable (S : Setup17 L Z W U (U ⊓ Subgroup.centralizer (W : Set 𝔾)) X α true)
include S

theorem mem_centralizer_qPtPre_iff {z : 𝔾} (hz : z ∈ Z) :
    z ∈ Subgroup.centralizer (qPtPre L α : Set 𝔾) ↔ S.NZ.coord z 0 = 0 := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := toSL3_surjective S.surj (rootElt 0 1 1)
    have hq : (l : 𝔾) ∈ qPtPre L α := ⟨l, by
      show toSL3 α l ∈ (qPt : Subgroup (SL3 F))
      rw [hl]
      exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 1), rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp h _ hq
    have heq : (l : 𝔾) * z * (l : 𝔾)⁻¹ = z := by
      rw [hc, mul_inv_cancel_right]
    have h1 := S.NZ.coord_conj l hz
    rw [heq, natAct_true, hl, dualMat_rootElt_mulVec (by decide)] at h1
    have h2 := congrFun h1 1
    simpa using h2
  · intro h0
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have heq : (l : 𝔾) * z * (l : 𝔾)⁻¹ = z := by
      apply S.NZ.eq_of_coord_eq (S.NZ.conj_mem l hz) hz
      rw [S.NZ.coord_conj l hz, natAct_true]
      exact dualMat_mulVec_of_mem_qPt hl h0
    calc ((l : ↥L) : 𝔾) * z = (l : 𝔾) * z * (l : 𝔾)⁻¹ * l := by group
      _ = z * l := by rw [heq]

theorem conclusion [CharP F 2] [Finite F] {w : 𝔾} (hw : w ∈ W)
    (hwX : w ∈ Subgroup.centralizer (X : Set 𝔾))
    (hwU : w ∉ Subgroup.centralizer (U : Set 𝔾)) :
    ⁅U, Subgroup.zpowers w⁆ = Z ⊓ Subgroup.centralizer (qPtPre L α : Set 𝔾) := by
  have hX : ∀ w' ∈ Subgroup.zpowers w, ∀ x ∈ X, ⁅x, w'⁆ = 1 := fun w' hw' x hx =>
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hwX hw') x hx)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu w' hw'
    have hw'W : w' ∈ W := Subgroup.zpowers_le.mpr hw hw'
    have hz := S.comm_mem hu hw'W
    refine ⟨hz, (S.mem_centralizer_qPtPre_iff hz).mpr ?_⟩
    obtain ⟨t, ht⟩ := S.exists_coordZ_comm_eq hw'W (hX w' hw')
    rw [ht u hu]
    rfl
  · rintro z ⟨hz, hzQ⟩
    have hz0 := (S.mem_centralizer_qPtPre_iff hz).mp hzQ
    obtain ⟨t, ht⟩ := S.exists_coordZ_comm_eq hw (hX w (Subgroup.mem_zpowers w))
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hwU
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h := S.NZ.eq_one_of_coord_eq_zero (S.comm_mem hu hw) (by
        rw [ht u hu]
        funext k
        fin_cases k <;> simp)
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    obtain ⟨u, hu, huc⟩ := S.NU.exists_coord_eq
      ![0, S.NZ.coord z 2 / t, -(S.NZ.coord z 1 / t)]
    have heq : ⁅u, w⁆ = z := by
      apply S.NZ.eq_of_coord_eq (S.comm_mem hu hw) hz
      rw [ht u hu, huc]
      funext k
      fin_cases k
      · simpa using hz0.symm
      · simp [mul_div_cancel₀ _ ht0]
      · simp [mul_div_cancel₀ _ ht0]
    rw [← heq]
    exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers w)

end Setup17

end CFSG.Quasithin.MS93.ML3

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique ML3

theorem ms17ii_holds :
    ∀ (𝔾 : Type) [Group 𝔾] (F : Type) [Field F] [Fintype F] (n : ℕ), Fintype.card F = 2 ^ n →
    ∀ (L Z W U X : Subgroup 𝔾) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Function.Surjective α →
      IsSumOfNaturalModulesVia L Z ⊥ α true 1 →
      IsSumOfNaturalModulesVia L U (U ⊓ Subgroup.centralizer (W : Set 𝔾)) α false 1 →
      L ≤ Subgroup.normalizer (W : Set 𝔾) →
      ⁅Z, U⁆ = ⊥ → ⁅Z, W⁆ = ⊥ → ⁅U, W⁆ ≤ Z →
      X ≤ U → U = Subgroup.closure {u | ∃ l : ↥L, ∃ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ = u} →
      (∀ l : ↥L, toSL3 α l ∈ ptStab → ∀ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ ∈ X) →
      (∀ l : ↥L, toSL3 α l ∈ ptLevi → ∀ x ∈ X,
        x⁻¹ * ((l : 𝔾) * x * (l : 𝔾)⁻¹) ∈ U ⊓ Subgroup.centralizer (W : Set 𝔾)) →
      ⁅X, W⁆ ≠ ⊥ → Nat.card ↥⁅X, W⁆ ≤ Nat.card F ^ 2 →
      ∀ w ∈ W, w ∈ Subgroup.centralizer (X : Set 𝔾) → w ∉ Subgroup.centralizer (U : Set 𝔾) →
        ⁅U, Subgroup.zpowers w⁆ = Z ⊓ Subgroup.centralizer (qPtPre L α : Set 𝔾) := by
  intro 𝔾 _ F _ _ n hF L Z W U X α hα hZ hU hLW hZU hZW hUW hXU hgen hstab hlevi hne hcard w hw
    hwX hwU
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hF'
  let S : Setup17 L Z W U (U ⊓ Subgroup.centralizer (W : Set 𝔾)) X α true :=
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
  exact S.conclusion hw hwX hwU

end CFSG.Quasithin.MS93
