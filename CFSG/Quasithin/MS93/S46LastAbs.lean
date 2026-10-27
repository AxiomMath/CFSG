module

public import CFSG.Quasithin.MS93.S46Struct
public import CFSG.Quasithin.MS93.S4AFAbs
public import CFSG.Quasithin.MS93.S4AFSec
public import CFSG.Quasithin.MS93.ML3Rec

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.ML3 CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

section Lin

variable {F : Type} [Field F]

theorem exists_dualMat_mulVec_e0_eq {c : Fin 3 → F} (hc : c ≠ 0) :
    ∃ g : SL3 F, dualMat g *ᵥ ![1, 0, 0] = c := by
  obtain ⟨h, hh⟩ := exists_mulVec_e0_eq hc
  refine ⟨transposeInv h, ?_⟩
  rw [← coe_transposeInv, transposeInv_transposeInv, hh]

theorem dualMat_inv_mul (g : SL3 F) : dualMat g⁻¹ * dualMat g = 1 := by
  rw [← dualMat_mul, inv_mul_cancel, dualMat_one]

theorem dualMat_rootElt_mulVec_e0 {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 0) (c : F) :
    dualMat (rootElt i j c) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  rw [dualMat_rootElt_mulVec hij]
  have : (![1, 0, 0] : Fin 3 → F) i = 0 := by
    fin_cases i
    · exact absurd rfl hi
    all_goals rfl
  rw [this, mul_zero, Pi.single_zero, add_zero]

theorem rootElt_mulVec_eq_add_single {i j : Fin 3} (hij : i ≠ j) (c : F) (u : Fin 3 → F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u + Pi.single i (c * u j) := by
  rw [coe_rootElt hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem dualMat_conj_mulVec {g₀ s : SL3 F} {c : Fin 3 → F} (hg₀ : dualMat g₀ *ᵥ ![1, 0, 0] = c)
    (hs : dualMat s *ᵥ ![1, 0, 0] = ![1, 0, 0]) : dualMat (g₀ * s * g₀⁻¹) *ᵥ c = c := by
  rw [dualMat_mul, dualMat_mul, ← hg₀, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, dualMat_inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec, hs]

theorem eq_zero_of_forall_dualStab {c u : Fin 3 → F} (hc : c ≠ 0)
    (hu : ∀ g : SL3 F, dualMat g *ᵥ c = c → ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u) :
    u = 0 := by
  obtain ⟨g₀, hg₀⟩ := exists_dualMat_mulVec_e0_eq hc
  set u' := ((g₀⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u with hu'
  have hfix : ∀ s : SL3 F, dualMat s *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u' = u' := by
    intro s hs
    have h1 := hu _ (dualMat_conj_mulVec hg₀ hs)
    calc ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u'
        = ((g₀⁻¹ * (g₀ * s * g₀⁻¹) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
          rw [hu', Matrix.mulVec_mulVec, ← coe_mul_SL3,
            show s * g₀⁻¹ = g₀⁻¹ * (g₀ * s * g₀⁻¹) by group]
      _ = u' := by rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, h1]
  have hj : ∀ i j : Fin 3, i ≠ j → i ≠ 0 → u' j = 0 := by
    intro i j hij hi
    have h := hfix (rootElt i j 1) (dualMat_rootElt_mulVec_e0 hij hi 1)
    rw [rootElt_mulVec_eq_add_single hij, add_eq_left, one_mul] at h
    have := congrFun h i
    simpa using this
  have hu0 : u' = 0 := by
    funext k
    fin_cases k
    · exact hj 1 0 (by decide) (by decide)
    · exact hj 2 1 (by decide) (by decide)
    · exact hj 1 2 (by decide) (by decide)
  have : u = ((g₀ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u' := by
    rw [hu', Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3,
      Matrix.one_mulVec]
  rw [this, hu0, Matrix.mulVec_zero]

theorem eq_top_of_forall_dualStab {c : Fin 3 → F} (hc : c ≠ 0) (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ g : SL3 F, dualMat g *ᵥ c = c → ∀ w : Fin 3 → F, dualMat g *ᵥ w - w ∈ S) :
    S = ⊤ := by
  obtain ⟨g₀, hg₀⟩ := exists_dualMat_mulVec_e0_eq hc
  have h0 : ∀ s : SL3 F, dualMat s *ᵥ ![1, 0, 0] = ![1, 0, 0] → ∀ w : Fin 3 → F,
      dualMat g₀ *ᵥ (dualMat s *ᵥ w - w) ∈ S := by
    intro s hs w
    have h := hS _ (dualMat_conj_mulVec hg₀ hs) (dualMat g₀ *ᵥ w)
    have e : dualMat (g₀ * s * g₀⁻¹) *ᵥ (dualMat g₀ *ᵥ w) - dualMat g₀ *ᵥ w =
        dualMat g₀ *ᵥ (dualMat s *ᵥ w - w) := by
      rw [dualMat_mul, dualMat_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        dualMat_inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    rwa [e] at h
  have hsingle : ∀ (i j : Fin 3), i ≠ j → i ≠ 0 → ∀ a : F, dualMat g₀ *ᵥ Pi.single j a ∈ S := by
    intro i j hij hi a
    have h := h0 (rootElt i j (-1)) (dualMat_rootElt_mulVec_e0 hij hi _) (Pi.single i a)
    rwa [dualMat_rootElt_mulVec hij, add_sub_cancel_left, Pi.single_eq_same, neg_neg,
      one_mul] at h
  rw [eq_top_iff]
  intro y _
  set y' := dualMat g₀⁻¹ *ᵥ y with hy'
  have hy : y = dualMat g₀ *ᵥ y' := by
    rw [hy', Matrix.mulVec_mulVec, ← dualMat_mul, mul_inv_cancel, dualMat_one,
      Matrix.one_mulVec]
  have hdec : y' = Pi.single 0 (y' 0) + Pi.single 1 (y' 1) + Pi.single 2 (y' 2) := by
    funext k
    fin_cases k <;> simp
  rw [hy, hdec, Matrix.mulVec_add, Matrix.mulVec_add]
  exact S.add_mem (S.add_mem (hsingle 1 0 (by decide) (by decide) _)
    (hsingle 2 1 (by decide) (by decide) _)) (hsingle 1 2 (by decide) (by decide) _)

end Lin

section Grp

variable {𝔾 : Type} [Group 𝔾]

theorem exists_mul_eq_of_mem_sup_of_conj {A B : Subgroup 𝔾}
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    {x : 𝔾} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    refine ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hBA b₁ hb₁ a₂ ha₂), b₁ * b₂,
      B.mul_mem hb₁ hb₂, by group⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hBA _ (B.inv_mem hb) _ (A.inv_mem ha), b⁻¹, B.inv_mem hb,
      by group⟩

theorem commutatorElement_mul_left_conj (g g' w : 𝔾) :
    ⁅g * g', w⁆ = g * ⁅g', w⁆ * g⁻¹ * ⁅g, w⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right_conj (q l l' : 𝔾) :
    ⁅q, l * l'⁆ = ⁅q, l⁆ * (l * ⁅q, l'⁆ * l⁻¹) := by
  simp only [commutatorElement_def]
  group

def commInSub (K W N : Subgroup 𝔾) (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) : Subgroup 𝔾 where
  carrier := {g | g ∈ K ∧ ∀ w ∈ W, ⁅g, w⁆ ∈ N}
  one_mem' := ⟨K.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun w hw => by
    rw [commutatorElement_mul_left_conj]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hg.1) _).mp (hg'.2 w hw)) (hg.2 w hw)⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun w hw => by
    have h := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hg.1)) _).mp
      (N.inv_mem (hg.2 w hw))
    have e : ⁅g⁻¹, w⁆ = g⁻¹ * ⁅g, w⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h⟩

theorem commutator_sup_le_of_le_normalizer {K A B W N : Subgroup 𝔾}
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾))
    (hAK : A ≤ K) (hBK : B ≤ K) (hA : ⁅A, W⁆ ≤ N) (hB : ⁅B, W⁆ ≤ N) : ⁅A ⊔ B, W⁆ ≤ N := by
  have hle : A ⊔ B ≤ commInSub K W N hKN := sup_le
    (fun a ha => ⟨hAK ha, fun w hw => hA (Subgroup.commutator_mem_commutator ha hw)⟩)
    (fun b hb => ⟨hBK hb, fun w hw => hB (Subgroup.commutator_mem_commutator hb hw)⟩)
  rw [Subgroup.commutator_le]
  intro g hg w hw
  exact (hle hg).2 w hw

theorem comm_mem_of_perfect {Lt A B : Subgroup 𝔾} (hperf : ⁅Lt, Lt⁆ = Lt) (hAB : A ≤ B)
    (hAn : ∀ l ∈ Lt, ∀ a ∈ A, l * a * l⁻¹ ∈ A) (hBB : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ A)
    (hBL : ∀ b ∈ B, ∀ l ∈ Lt, l * b * l⁻¹ * b⁻¹ ∈ A) {x : 𝔾} (hx : ∀ l ∈ Lt, ⁅x, l⁆ ∈ B)
    {l : 𝔾} (hl : l ∈ Lt) : ⁅x, l⁆ ∈ A := by
  let P : Subgroup 𝔾 :=
    { carrier := {l | l ∈ Lt ∧ ⁅x, l⁆ ∈ A}
      one_mem' := ⟨Lt.one_mem, by rw [commutatorElement_one_right]; exact A.one_mem⟩
      mul_mem' := fun {l l'} hl hl' => ⟨Lt.mul_mem hl.1 hl'.1, by
        rw [commutatorElement_mul_right_conj]
        exact A.mul_mem hl.2 (hAn l hl.1 _ hl'.2)⟩
      inv_mem' := fun {l} hl => ⟨Lt.inv_mem hl.1, by
        have e : ⁅x, l⁻¹⁆ = l⁻¹ * ⁅x, l⁆⁻¹ * l⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hAn _ (Lt.inv_mem hl.1) _ (A.inv_mem hl.2)⟩ }
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have h := hBB b hb a (hAB ha)
    have e : b * a * b⁻¹ = ⁅b, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem h ha
  have hN : (A.subgroupOf B).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hBA g g.2 n hn⟩
  have hcomm : ∀ p p' : ↥B ⧸ A.subgroupOf B, p * p' = p' * p := by
    intro p p'
    induction p using QuotientGroup.induction_on with
    | H a =>
      induction p' using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have e : (((a * b)⁻¹ * (b * a) : ↥B) : 𝔾) = ⁅(b : 𝔾)⁻¹, (a : 𝔾)⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact hBB _ (B.inv_mem b.2) _ (B.inv_mem a.2)
  let f : ↥Lt →* ↥B ⧸ A.subgroupOf B :=
    { toFun := fun l => QuotientGroup.mk ⟨⁅x, (l : 𝔾)⁆, hx l l.2⟩
      map_one' := by
        rw [← QuotientGroup.mk_one, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp
      map_mul' := fun l l' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : (((⟨⁅x, ((l * l' : ↥Lt) : 𝔾)⁆, hx _ (l * l').2⟩ : ↥B)⁻¹ *
            (⟨⁅x, (l : 𝔾)⁆, hx l l.2⟩ * ⟨⁅x, (l' : 𝔾)⁆, hx l' l'.2⟩) : ↥B) : 𝔾) =
            (l : 𝔾) * ⁅x, (l' : 𝔾)⁆⁻¹ * (l : 𝔾)⁻¹ * (⁅x, (l' : 𝔾)⁆⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact hBL _ (B.inv_mem (hx l' l'.2)) l l.2 }
  have key : ∀ l₁ ∈ Lt, ∀ l₂ ∈ Lt, ⁅x, ⁅l₁, l₂⁆⁆ ∈ A := by
    intro l₁ h₁ l₂ h₂
    have h1 : f ⁅(⟨l₁, h₁⟩ : ↥Lt), ⟨l₂, h₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have h2 : (f ⁅(⟨l₁, h₁⟩ : ↥Lt), ⟨l₂, h₂⟩⁆ : ↥B ⧸ A.subgroupOf B) =
        QuotientGroup.mk ⟨⁅x, ⁅l₁, l₂⁆⁆, hx _ (by
          have := Subgroup.commutator_mem_commutator h₁ h₂
          rwa [hperf] at this)⟩ := by
      rfl
    rw [h2, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hle : ⁅Lt, Lt⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro l₁ h₁ l₂ h₂
    have hm := Subgroup.commutator_mem_commutator h₁ h₂
    rw [hperf] at hm
    exact ⟨hm, key l₁ h₁ l₂ h₂⟩
  rw [hperf] at hle
  exact (hle hl).2

end Grp

section Abs

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

structure LastHyp (K Q Lt U Z0 Z V : Subgroup 𝔾) (ψ : ↥K →* ↥(StatedSL 3 F)) : Prop where
  fin : Finite ↥K
  surj : Function.Surjective ψ
  nat : IsSumOfNaturalModulesVia K U ⊥ ψ false 1
  ker : ∀ k : ↥K, toSL3 ψ k = 1 ↔ (k : 𝔾) ∈ Q
  qK : Q ≤ K
  ltK : Lt ≤ K
  ltN : K ≤ Subgroup.normalizer (Lt : Set 𝔾)
  sup : K ≤ Lt ⊔ Q
  perf : ⁅Lt, Lt⁆ = Lt
  zN : K ≤ Subgroup.normalizer (Z : Set 𝔾)
  zEq : Z = U ⊔ Z0
  z0c : Z0 ≤ Subgroup.centralizer (K : Set 𝔾)
  zq : Z ≤ Subgroup.centralizer (Q : Set 𝔾)
  z2 : ∀ z ∈ Z, z ^ 2 = 1
  vq : V ≤ Q
  vN : K ≤ Subgroup.normalizer (V : Set 𝔾)
  zv : Z ≤ V
  vv : ⁅V, V⁆ ≤ Z
  vqc : ⁅V, Q⁆ ≤ Z
  vne : ⁅V, V⁆ ≠ ⊥
  bl : ⁅centerOf V, Lt⁆ ≤ Z
  ql : ⁅Q, Lt⁆ ≤ V

namespace LastHyp

variable {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ)
include h

theorem uZ : U ≤ Z := h.zEq ▸ le_sup_left

theorem vK : V ≤ K := h.vq.trans h.qK

theorem zK : Z ≤ K := h.zv.trans h.vK

theorem uK : U ≤ K := h.uZ.trans h.zK

theorem comm_z_q {z x : 𝔾} (hz : z ∈ Z) (hx : x ∈ Q) : z * x = x * z :=
  (Subgroup.mem_centralizer_iff.mp (h.zq hz) x hx).symm

theorem commutator_z_eq_bot {W : Subgroup 𝔾} (hW : W ≤ Q) : ⁅Z, W⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h.zq.trans (Subgroup.centralizer_le hW)

theorem comm_z0_k {b g : 𝔾} (hb : b ∈ Z0) (hg : g ∈ K) : g * b = b * g :=
  Subgroup.mem_centralizer_iff.mp (h.z0c hb) g hg

theorem conj_mem_u {u : 𝔾} (hu : u ∈ U) {k : 𝔾} (hk : k ∈ K) : k * u * k⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp (h.nat.1 hk) u).mp hu

theorem conj_mul_inv_mem_u {z : 𝔾} (hz : z ∈ Z) {k : 𝔾} (hk : k ∈ K) :
    k * z * k⁻¹ * z⁻¹ ∈ U := by
  have hz' := hz
  rw [h.zEq] at hz'
  obtain ⟨u, hu, z0, hz0, rfl⟩ := exists_mul_eq_of_mem_sup_of_conj (fun b hb a ha => by
    rw [← h.comm_z0_k hb (h.uK ha), mul_inv_cancel_right]
    exact ha) hz'
  have hk0 : z0 * k⁻¹ = k⁻¹ * z0 := (h.comm_z0_k hz0 (K.inv_mem hk)).symm
  have e : k * (u * z0) * k⁻¹ * (u * z0)⁻¹ = k * u * k⁻¹ * u⁻¹ := by
    calc k * (u * z0) * k⁻¹ * (u * z0)⁻¹ = k * u * (z0 * k⁻¹) * z0⁻¹ * u⁻¹ := by group
      _ = k * u * k⁻¹ * u⁻¹ := by rw [hk0]; group
  rw [e]
  exact U.mul_mem (h.conj_mem_u hu hk) (U.inv_mem hu)

theorem exists_lt_toSL3_eq (g : SL3 F) : ∃ l : ↥K, (l : 𝔾) ∈ Lt ∧ toSL3 ψ l = g := by
  have htop : Lt.subgroupOf K ⊔ Q.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.ltK h.qK, eq_top_iff]
    intro k _
    exact Subgroup.mem_subgroupOf.mpr (h.sup k.2)
  have hQ : (Q.subgroupOf K).map (toSL3 ψ) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_bot).mpr ((h.ker k).mpr (Subgroup.mem_subgroupOf.mp hk))
  have hmap := congrArg (Subgroup.map (toSL3 ψ)) htop
  rw [Subgroup.map_sup, hQ, sup_bot_eq, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (toSL3_surjective h.surj)] at hmap
  have hg : g ∈ (Lt.subgroupOf K).map (toSL3 ψ) := by rw [hmap]; trivial
  obtain ⟨l, hl, rfl⟩ := hg
  exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩

end LastHyp

namespace LastLayer

variable [Fintype F] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  {W : Subgroup 𝔾}

theorem wQ (h : LastHyp K Q Lt U Z0 Z V ψ) (hW : LastLayer K Q U Z V ψ W) : W ≤ Q :=
  hW.le.trans h.vq

theorem zW (hW : LastLayer K Q U Z V ψ W) : Z ≤ W := hW.dual.2.1

theorem commutator_le_z (h : LastHyp K Q Lt U Z0 Z V ψ) (hW : LastLayer K Q U Z V ψ W) :
    ⁅W, W⁆ ≤ Z :=
  (Subgroup.commutator_mono hW.le hW.le).trans h.vv

variable [CharP F 2] (h : LastHyp K Q Lt U Z0 Z V ψ) (hW : LastLayer K Q U Z V ψ W)
include h hW

theorem sq_eq_one {x : 𝔾} (hx : x ∈ W) : x ^ 2 = 1 := by
  classical
  set N := NatSec.ofIsSum hW.dual with hN
  set NU := NatSec.ofIsSum h.nat with hNU
  have hcomm : ∀ z ∈ Z, ∀ y ∈ W, z * y = y * z := fun z hz y hy =>
    h.comm_z_q hz (hW.wQ h hy)
  have hsqZ : ∀ y ∈ W, y * y ∈ Z := by
    intro y hy
    rw [← N.coord_eq_zero_iff (W.mul_mem hy hy), N.coord_mul hy hy]
    exact CharTwo.add_self_eq_zero _
  have hsq_eq : ∀ y ∈ W, ∀ y' ∈ W, y⁻¹ * y' ∈ Z → y' * y' = y * y := by
    intro y hy y' hy' hz
    set z := y⁻¹ * y' with hzdef
    have hy'e : y' = y * z := by rw [hzdef, mul_inv_cancel_left]
    rw [hy'e]
    have hzy : z * y = y * z := hcomm z hz y hy
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [hzy]
      _ = y * y * (z * z) := by group
      _ = y * y := by rw [← sq z, h.z2 z hz, mul_one]
  have hfix_sq : ∀ y ∈ W, ∀ k : ↥K, dualMat (toSL3 ψ k) *ᵥ N.coord y = N.coord y →
      (k : 𝔾) * (y * y) * (k : 𝔾)⁻¹ = y * y := by
    intro y hy k hk
    have hky : N.coord ((k : 𝔾) * y * (k : 𝔾)⁻¹) = N.coord y := by
      rw [N.coord_conj k hy, natAct_true]
      exact hk
    have h1 := hsq_eq y hy _ (N.conj_mem k hy) (N.inv_mul_mem_of_coord_eq hy (N.conj_mem k hy)
      hky.symm)
    calc (k : 𝔾) * (y * y) * (k : 𝔾)⁻¹ =
        (k : 𝔾) * y * (k : 𝔾)⁻¹ * ((k : 𝔾) * y * (k : 𝔾)⁻¹) := by group
      _ = y * y := h1
  have hsqZ0 : ∀ y ∈ W, y ∉ Z → y * y ∈ Z0 := by
    intro y hy hyZ
    have hyy := hsqZ y hy
    rw [h.zEq] at hyy
    obtain ⟨u, hu, z0, hz0, huz⟩ := exists_mul_eq_of_mem_sup_of_conj (fun b hb a ha => by
      rw [← h.comm_z0_k hb (h.uK ha), mul_inv_cancel_right]
      exact ha) hyy
    have hc : N.coord y ≠ 0 := by rwa [Ne, N.coord_eq_zero_iff hy]
    have hufix : ∀ g : SL3 F, dualMat g *ᵥ N.coord y = N.coord y →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ NU.coord u = NU.coord u := by
      intro g hg
      obtain ⟨k, rfl⟩ := toSL3_surjective h.surj g
      have h1 := hfix_sq y hy k hg
      rw [← huz] at h1
      have hk0 : (k : 𝔾) * z0 * (k : 𝔾)⁻¹ = z0 := by
        rw [h.comm_z0_k hz0 k.2, mul_inv_cancel_right]
      have h2 : (k : 𝔾) * u * (k : 𝔾)⁻¹ = u := by
        have e : (k : 𝔾) * (u * z0) * (k : 𝔾)⁻¹ = (k : 𝔾) * u * (k : 𝔾)⁻¹ *
            ((k : 𝔾) * z0 * (k : 𝔾)⁻¹) := by group
        rw [e, hk0] at h1
        exact mul_right_cancel h1
      rw [← natAct_false, ← NU.coord_conj k hu, h2]
    have hu1 : u = 1 := NU.eq_one_of_coord_eq_zero hu (eq_zero_of_forall_dualStab hc hufix)
    rw [← huz, hu1, one_mul]
    exact hz0
  have hconst : ∀ y ∈ W, ∀ y' ∈ W, y ∉ Z → y' ∉ Z → y * y = y' * y' := by
    intro y hy y' hy' hyZ hy'Z
    have hc : N.coord y ≠ 0 := by rwa [Ne, N.coord_eq_zero_iff hy]
    have hc' : N.coord y' ≠ 0 := by rwa [Ne, N.coord_eq_zero_iff hy']
    obtain ⟨g₁, hg₁⟩ := exists_dualMat_mulVec_e0_eq hc
    obtain ⟨g₂, hg₂⟩ := exists_dualMat_mulVec_e0_eq hc'
    obtain ⟨k, hk⟩ := toSL3_surjective h.surj (g₂ * g₁⁻¹)
    have hky : N.coord ((k : 𝔾) * y * (k : 𝔾)⁻¹) = N.coord y' := by
      rw [N.coord_conj k hy, natAct_true, hk, dualMat_mul, ← Matrix.mulVec_mulVec, ← hg₁,
        show dualMat g₁⁻¹ *ᵥ (dualMat g₁ *ᵥ ![1, 0, 0]) = ![1, 0, 0] by
          rw [Matrix.mulVec_mulVec, dualMat_inv_mul, Matrix.one_mulVec], hg₂]
    have h1 := hsq_eq y' hy' _ (N.conj_mem k hy) (N.inv_mul_mem_of_coord_eq hy'
      (N.conj_mem k hy) hky.symm)
    have h2 : (k : 𝔾) * y * (k : 𝔾)⁻¹ * ((k : 𝔾) * y * (k : 𝔾)⁻¹) = y * y := by
      have e : (k : 𝔾) * y * (k : 𝔾)⁻¹ * ((k : 𝔾) * y * (k : 𝔾)⁻¹) =
          (k : 𝔾) * (y * y) * (k : 𝔾)⁻¹ := by group
      rw [e, h.comm_z0_k (hsqZ0 y hy hyZ) k.2, mul_inv_cancel_right]
    rw [← h2, h1]
  have hpol : ∀ y ∈ W, ∀ y' ∈ W, (y * y') * (y * y') = ⁅y', y⁆ * (y * y) * (y' * y') := by
    intro y hy y' hy'
    have hc := hcomm _ (hW.commutator_le_z h (Subgroup.commutator_mem_commutator hy' hy)) y hy
    have e : y' * y = ⁅y', y⁆ * y * y' := by
      simp only [commutatorElement_def]
      group
    calc (y * y') * (y * y') = y * (y' * y) * y' := by group
      _ = y * (⁅y', y⁆ * y * y') * y' := by rw [e]
      _ = (y * ⁅y', y⁆) * y * y' * y' := by group
      _ = (⁅y', y⁆ * y) * y * y' * y' := by rw [hc]
      _ = ⁅y', y⁆ * (y * y) * (y' * y') := by group
  obtain ⟨x₀, hx₀, hc₀⟩ := N.exists_coord_eq ![1, 0, 0]
  obtain ⟨x₁, hx₁, hc₁⟩ := N.exists_coord_eq ![0, 1, 0]
  obtain ⟨x₂, hx₂, hc₂⟩ := N.exists_coord_eq ![0, 0, 1]
  have hnot : ∀ y ∈ W, N.coord y ≠ 0 → y ∉ Z := fun y hy hc hyZ =>
    hc ((N.coord_eq_zero_iff hy).mpr hyZ)
  have hn₀ : x₀ ∉ Z := hnot x₀ hx₀ (by rw [hc₀]; simp)
  have hn₁ : x₁ ∉ Z := hnot x₁ hx₁ (by rw [hc₁]; simp)
  have hn₂ : x₂ ∉ Z := hnot x₂ hx₂ (by rw [hc₂]; simp)
  have hn₀₁ : x₀ * x₁ ∉ Z := hnot _ (W.mul_mem hx₀ hx₁) (by
    rw [N.coord_mul hx₀ hx₁, hc₀, hc₁]
    intro h0
    have := congrFun h0 0
    simp at this)
  have hn₀₂ : x₀ * x₂ ∉ Z := hnot _ (W.mul_mem hx₀ hx₂) (by
    rw [N.coord_mul hx₀ hx₂, hc₀, hc₂]
    intro h0
    have := congrFun h0 0
    simp at this)
  have hn₁₂ : x₁ * x₂ ∉ Z := hnot _ (W.mul_mem hx₁ hx₂) (by
    rw [N.coord_mul hx₁ hx₂, hc₁, hc₂]
    intro h0
    have := congrFun h0 1
    simp at this)
  have hn₀₁₂ : x₀ * x₁ * x₂ ∉ Z := hnot _ (W.mul_mem (W.mul_mem hx₀ hx₁) hx₂) (by
    rw [N.coord_mul (W.mul_mem hx₀ hx₁) hx₂, N.coord_mul hx₀ hx₁, hc₀, hc₁, hc₂]
    intro h0
    have := congrFun h0 0
    simp at this)
  set s := x₀ * x₀ with hs
  have hsq : ∀ y ∈ W, y ∉ Z → y * y = s := fun y hy hyZ => hconst y hy x₀ hx₀ hyZ hn₀
  have hcs : ∀ y ∈ W, y ∉ Z → y * x₂ ∉ Z → ⁅x₂, y⁆ = s⁻¹ := by
    intro y hy hyZ hyxZ
    have h1 := hpol y hy x₂ hx₂
    rw [hsq _ (W.mul_mem hy hx₂) hyxZ, hsq y hy hyZ, hsq x₂ hx₂ hn₂] at h1
    have : ⁅x₂, y⁆ = s * s⁻¹ * s⁻¹ := by
      rw [show s * s⁻¹ * s⁻¹ = (⁅x₂, y⁆ * s * s) * s⁻¹ * s⁻¹ by rw [← h1]]
      group
    rw [this, mul_inv_cancel, one_mul]
  have e₀ := hcs x₀ hx₀ hn₀ hn₀₂
  have e₁ := hcs x₁ hx₁ hn₁ hn₁₂
  have e₀₁ := hcs (x₀ * x₁) (W.mul_mem hx₀ hx₁) hn₀₁ hn₀₁₂
  have hbil := ML3.comm_mul_right (h.commutator_z_eq_bot (hW.wQ h)) (hW.commutator_le_z h)
    hx₂ hx₀ hx₁
  rw [e₀₁, e₀, e₁] at hbil
  have hs1 : s = 1 := by
    have : s⁻¹ = 1 := by
      have := congrArg (· * s) hbil
      simpa using this
    simpa using this
  rw [sq]
  by_cases hxZ : x ∈ Z
  · rw [← sq]
    exact h.z2 x hxZ
  · rw [hsq x hx hxZ, hs1]

theorem commutator_eq_bot : ⁅W, W⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hW.sq_eq_one h hx
  have h2 := hW.sq_eq_one h hy
  have h3 := hW.sq_eq_one h (W.mul_mem hy hx)
  rw [sq] at h1 h2 h3
  rw [eq_inv_of_mul_eq_one_left h3, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right h1,
    inv_eq_of_mul_eq_one_right h2]

end LastLayer

namespace LastLayer

variable [Fintype F] [CharP F 2] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ) {W W' : Subgroup 𝔾} (hW : LastLayer K Q U Z V ψ W)
  (hW' : LastLayer K Q U Z V ψ W')
include h hW hW'

omit [CharP F 2] in
theorem commutator_le_u : ⁅W, W'⁆ ≤ U := by
  classical
  set N := NatSec.ofIsSum hW.dual with hN
  set N' := NatSec.ofIsSum hW'.dual with hN'
  have hWW' : ⁅W, W'⁆ ≤ Z := (Subgroup.commutator_mono hW.le hW'.le).trans h.vv
  have hZW' : ⁅Z, W'⁆ = ⊥ := h.commutator_z_eq_bot (hW'.wQ h)
  rw [Subgroup.commutator_le]
  intro v hv w hw
  by_cases hvZ : v ∈ Z
  · have : ⁅v, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.comm_z_q hvZ (hW'.wQ h hw)
    rw [this]
    exact U.one_mem
  have hc : N.coord v ≠ 0 := by rwa [Ne, N.coord_eq_zero_iff hv]
  have hinv : ∀ w ∈ W', ⁅v, w⁻¹⁆ = ⁅v, w⁆⁻¹ := by
    intro w hw
    have h1 := ML3.comm_mul_right hZW' hWW' hv hw (W'.inv_mem hw)
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  let P : Subgroup 𝔾 :=
    { carrier := {w | w ∈ W' ∧ ⁅v, w⁆ ∈ U}
      one_mem' := ⟨W'.one_mem, by rw [commutatorElement_one_right]; exact U.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨W'.mul_mem ha.1 hb.1, by
        rw [ML3.comm_mul_right hZW' hWW' hv ha.1 hb.1]
        exact U.mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨W'.inv_mem ha.1, by
        rw [hinv a ha.1]
        exact U.inv_mem ha.2⟩ }
  have hZP : ∀ z ∈ Z, z ∈ P := by
    intro z hz
    refine ⟨hW'.zW hz, ?_⟩
    have : ⁅v, z⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (h.comm_z_q hz (hW.wQ h hv)).symm
    rw [this]
    exact U.one_mem
  have himg : N'.img P = ⊤ := by
    refine eq_top_of_forall_dualStab hc _ fun g hg y => ?_
    obtain ⟨k, rfl⟩ := toSL3_surjective h.surj g
    obtain ⟨w, hw, rfl⟩ := N'.exists_coord_eq y
    have hkw := N'.conj_mem k hw
    refine (N'.mem_img).mpr ⟨(k : 𝔾) * w * (k : 𝔾)⁻¹ * w⁻¹,
      ⟨W'.mul_mem hkw (W'.inv_mem hw), ?_⟩, W'.mul_mem hkw (W'.inv_mem hw), ?_⟩
    ·
      have hkv : N.coord ((k : 𝔾) * v * (k : 𝔾)⁻¹) = N.coord v := by
        rw [N.coord_conj k hv, natAct_true]
        exact hg
      set z := v⁻¹ * ((k : 𝔾) * v * (k : 𝔾)⁻¹) with hzdef
      have hz : z ∈ Z := N.inv_mul_mem_of_coord_eq hv (N.conj_mem k hv) hkv.symm
      have hkve : (k : 𝔾) * v * (k : 𝔾)⁻¹ = v * z := by rw [hzdef, mul_inv_cancel_left]
      have hzw : z * ((k : 𝔾) * w * (k : 𝔾)⁻¹) = ((k : 𝔾) * w * (k : 𝔾)⁻¹) * z :=
        h.comm_z_q hz (hW'.wQ h hkw)
      have hzv : z * v = v * z := h.comm_z_q hz (hW.wQ h hv)
      have e1 : ⁅v, (k : 𝔾) * w * (k : 𝔾)⁻¹⁆ = (k : 𝔾) * ⁅v, w⁆ * (k : 𝔾)⁻¹ := by
        rw [ML3.conj_commutatorElement, hkve]
        simp only [commutatorElement_def]
        calc v * ((k : 𝔾) * w * (k : 𝔾)⁻¹) * v⁻¹ * ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹
            = v * (z * ((k : 𝔾) * w * (k : 𝔾)⁻¹)) * z⁻¹ * v⁻¹ *
                ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹ := by rw [hzw]; group
          _ = v * z * ((k : 𝔾) * w * (k : 𝔾)⁻¹) * (v * z)⁻¹ *
                ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹ := by group
      rw [ML3.comm_mul_right hZW' hWW' hv hkw (W'.inv_mem hw), hinv w hw, e1]
      exact h.conj_mul_inv_mem_u (hWW' (Subgroup.commutator_mem_commutator hv hw)) k.2
    · rw [N'.coord_mul hkw (W'.inv_mem hw), N'.coord_conj k hw, N'.coord_inv hw, natAct_true,
        sub_eq_add_neg]
  have hwc : N'.coord w ∈ N'.img P := by rw [himg]; trivial
  obtain ⟨p, hpP, hpW, hpc⟩ := (N'.mem_img).mp hwc
  have hpw : p⁻¹ * w ∈ Z := N'.inv_mul_mem_of_coord_eq hpW hw hpc
  have hwP : w ∈ P := by
    have := P.mul_mem hpP (hZP _ hpw)
    rwa [mul_inv_cancel_left] at this
  exact hwP.2

end LastLayer

namespace LastLayer

variable [Fintype F] [CharP F 2] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ) {W : Subgroup 𝔾} (hW : LastLayer K Q U Z V ψ W)
include h hW

omit [CharP F 2] in
theorem commutator_vv_le_u {V₀ V₁ : Subgroup 𝔾} (hV₀K : V₀ ≤ K) (hV₁K : V₁ ≤ K)
    (hsup : V ≤ V₀ ⊔ V₁ ⊔ centerOf V) (h₀ : ⁅V₀, W⁆ ≤ U) (h₁ : ⁅V₁, W⁆ ≤ U) : ⁅V, W⁆ ≤ U := by
  have hZV : ⁅centerOf V, W⁆ ≤ U := by
    have : ⁅centerOf V, W⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right.trans (Subgroup.centralizer_le hW.le)
    rw [this]
    exact bot_le
  have hcK : centerOf V ≤ K := inf_le_left.trans h.vK
  refine (Subgroup.commutator_mono hsup le_rfl).trans ?_
  exact commutator_sup_le_of_le_normalizer h.nat.1 (sup_le hV₀K hV₁K) hcK
    (commutator_sup_le_of_le_normalizer h.nat.1 hV₀K hV₁K h₀ h₁) hZV

omit [CharP F 2] in
theorem commutator_q_le_u (hVW : ⁅V, W⁆ ≤ U) : ⁅W, Q⁆ ≤ U := by
  classical
  set N := NatSec.ofIsSum hW.dual with hN
  have hWQ : ⁅W, Q⁆ ≤ Z := (Subgroup.commutator_mono hW.le le_rfl).trans h.vqc
  have hZW : ⁅Z, W⁆ = ⊥ := h.commutator_z_eq_bot (hW.wQ h)
  have hZQ : ⁅Z, Q⁆ = ⊥ := h.commutator_z_eq_bot le_rfl
  have hWV : ⁅W, V⁆ ≤ U := by rw [Subgroup.commutator_comm]; exact hVW
  rw [Subgroup.commutator_le]
  intro w hw q hq
  let P : Subgroup 𝔾 :=
    { carrier := {w | w ∈ W ∧ ⁅w, q⁆ ∈ U}
      one_mem' := ⟨W.one_mem, by rw [commutatorElement_one_left]; exact U.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, by
        rw [ML3.comm_mul_left hZW hWQ ha.1 hb.1 hq]
        exact U.mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by
        rw [ML3.comm_inv_left hZW hWQ ha.1 hq]
        exact U.inv_mem ha.2⟩ }
  have hZP : ∀ z ∈ Z, z ∈ P := by
    intro z hz
    refine ⟨hW.zW hz, ?_⟩
    have : ⁅z, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.comm_z_q hz hq
    rw [this]
    exact U.one_mem
  have hkey : ∀ l : ↥K, (l : 𝔾) ∈ Lt → ∀ w ∈ W, (l : 𝔾) * w * (l : 𝔾)⁻¹ * w⁻¹ ∈ P := by
    intro l hl w hw
    have hlw : (l : 𝔾) * w * (l : 𝔾)⁻¹ ∈ W := N.conj_mem l hw
    refine ⟨W.mul_mem hlw (W.inv_mem hw), ?_⟩
    set y := ⁅q⁻¹, (l : 𝔾)⁆ with hy
    have hyV : y ∈ V := h.ql (Subgroup.commutator_mem_commutator (Q.inv_mem hq) hl)
    have hlq : (l : 𝔾) * q * (l : 𝔾)⁻¹ = q * y := by
      rw [hy]
      simp only [commutatorElement_def]
      group
    have e1 : (l : 𝔾) * ⁅w, q⁆ * (l : 𝔾)⁻¹ = ⁅(l : 𝔾) * w * (l : 𝔾)⁻¹, q⁆ *
        ⁅(l : 𝔾) * w * (l : 𝔾)⁻¹, y⁆ := by
      rw [ML3.conj_commutatorElement, hlq,
        ML3.comm_mul_right hZQ hWQ hlw hq (h.vq hyV)]
    have hc : ⁅(l : 𝔾) * w * (l : 𝔾)⁻¹, y⁆ ∈ U :=
      hWV (Subgroup.commutator_mem_commutator hlw hyV)
    have hwq : ⁅w, q⁆ ∈ Z := hWQ (Subgroup.commutator_mem_commutator hw hq)
    have hlwq : (l : 𝔾) * ⁅w, q⁆ * (l : 𝔾)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (h.zN l.2) _).mp hwq
    rw [ML3.comm_mul_left hZW hWQ hlw (W.inv_mem hw) hq, ML3.comm_inv_left hZW hWQ hw hq]
    have e2 : ⁅(l : 𝔾) * w * (l : 𝔾)⁻¹, q⁆ =
        (l : 𝔾) * ⁅w, q⁆ * (l : 𝔾)⁻¹ * ⁅(l : 𝔾) * w * (l : 𝔾)⁻¹, y⁆⁻¹ := by
      rw [e1, mul_inv_cancel_right]
    rw [e2]
    have hcomm : ⁅w, q⁆⁻¹ * ((l : 𝔾) * ⁅w, q⁆ * (l : 𝔾)⁻¹) =
        (l : 𝔾) * ⁅w, q⁆ * (l : 𝔾)⁻¹ * ⁅w, q⁆⁻¹ :=
      h.comm_z_q (Z.inv_mem hwq) (h.vq (h.zv hlwq))
    rw [← mul_assoc, hcomm]
    exact U.mul_mem (h.conj_mul_inv_mem_u hwq l.2) (U.inv_mem hc)
  have himg : N.img P = ⊤ := by
    refine eq_top_of_forall_dualStab (c := ![1, 0, 0]) (by
      intro h0
      have := congrFun h0 0
      simp at this) _ fun g _ y => ?_
    obtain ⟨l, hl, rfl⟩ := h.exists_lt_toSL3_eq g
    obtain ⟨w, hw, rfl⟩ := N.exists_coord_eq y
    refine (N.mem_img).mpr ⟨_, hkey l hl w hw, W.mul_mem (N.conj_mem l hw) (W.inv_mem hw), ?_⟩
    rw [N.coord_mul (N.conj_mem l hw) (W.inv_mem hw), N.coord_conj l hw, N.coord_inv hw,
      natAct_true, sub_eq_add_neg]
  have hwc : N.coord w ∈ N.img P := by rw [himg]; trivial
  obtain ⟨p, hpP, hpW, hpc⟩ := (N.mem_img).mp hwc
  have hpw : p⁻¹ * w ∈ Z := N.inv_mul_mem_of_coord_eq hpW hw hpc
  have hwP : w ∈ P := by
    have := P.mul_mem hpP (hZP _ hpw)
    rwa [mul_inv_cancel_left] at this
  exact hwP.2

end LastLayer

namespace LastLayer

variable [Fintype F] [CharP F 2] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ) {W : Subgroup 𝔾} (hW : LastLayer K Q U Z V ψ W)
include h hW

omit [CharP F 2] in
theorem commutator_lt_le : ⁅W, Lt⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw l hl
  have hlw : l * w⁻¹ * l⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hW.dual.1 (h.ltK hl)) _).mp (W.inv_mem hw)
  have e : ⁅w, l⁆ = w * (l * w⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact W.mul_mem hw hlw

omit [CharP F 2] in
theorem conj_mem_commutator_lt {x : 𝔾} (hx : x ∈ ⁅W, Lt⁆) {k : 𝔾} (hk : k ∈ K) :
    k * x * k⁻¹ ∈ ⁅W, Lt⁆ :=
  ML3.conj_mem_commutator (fun a ha => (Subgroup.mem_normalizer_iff.mp (hW.dual.1 hk) a).mp ha)
    (fun b hb => (Subgroup.mem_normalizer_iff.mp (h.ltN hk) b).mp hb) hx

omit [CharP F 2] in
theorem exists_commutator_not_mem :
    ∃ x ∈ ⁅W, Lt⁆, x ∈ W ∧ x ∉ Z := by
  classical
  set N := NatSec.ofIsSum hW.dual with hN
  obtain ⟨w, hw, hwc⟩ := N.exists_coord_eq ![1, 0, 0]
  obtain ⟨l, hl, hlg⟩ := h.exists_lt_toSL3_eq (rootElt 0 1 (1 : F))
  have hlw : (l : 𝔾) * w⁻¹ * (l : 𝔾)⁻¹ ∈ W := N.conj_mem l (W.inv_mem hw)
  refine ⟨⁅w, (l : 𝔾)⁆, Subgroup.commutator_mem_commutator hw hl,
    hW.commutator_lt_le h (Subgroup.commutator_mem_commutator hw hl), fun hZ => ?_⟩
  have e : ⁅w, (l : 𝔾)⁆ = w * ((l : 𝔾) * w⁻¹ * (l : 𝔾)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h0 := (N.coord_eq_zero_iff (W.mul_mem hw hlw)).mpr (e ▸ hZ)
  rw [N.coord_mul hw hlw, N.coord_conj l (W.inv_mem hw), N.coord_inv hw, natAct_true, hlg,
    hwc, Matrix.mulVec_neg, dualMat_rootElt_mulVec (by decide)] at h0
  have := congrFun h0 1
  simp [Matrix.vecHead, Matrix.vecTail] at this

theorem inf_z_le_u (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hWQ : ⁅W, Q⁆ ≤ U) : ⁅W, Lt⁆ ⊓ Z ≤ U := by
  classical
  obtain ⟨A, hAK, hA2, hAc, hqA, hcomm⟩ := hW.off
  have hUW : U ≤ W := h.uZ.trans hW.zW
  have hab := hW.commutator_eq_bot h
  have : Finite ↥K := h.fin
  have hWfin : Finite ↥W := Finite.of_injective _ (Subgroup.inclusion_injective
    (hW.le.trans h.vK))
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := S4A.F.exists_quotient_conj (K := K) (V := W) (Z := U)
    hW.dual.1 hUW h.nat.1 (fun v hv w hw => by
      have : ⁅v, w⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hv hw
        rwa [hab, Subgroup.mem_bot] at this
      rw [this]
      exact U.one_mem)
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    have : v ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hW.sq_eq_one h v.2)
    rw [this, map_one]
  have hQ : (toSL3 ψ).ker = Q.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact h.ker k
  have hA2' : ∀ a ∈ A.subgroupOf K, toSL3 ψ a ^ 2 = 1 := by
    intro a ha
    rw [← map_pow, (h.ker _)]
    rw [Subgroup.coe_pow]
    exact hA2 _ (Subgroup.mem_subgroupOf.mp ha)
  have hAc' : ∀ a ∈ A.subgroupOf K, ∀ b ∈ A.subgroupOf K,
      toSL3 ψ a * toSL3 ψ b = toSL3 ψ b * toSL3 ψ a := by
    intro a ha b hb
    have h1 : toSL3 ψ ⁅a, b⁆ = 1 := by
      rw [h.ker]
      have := hAc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
      simpa [commutatorElement_def] using this
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hqA' : Nat.card F ≤ Nat.card ((A.subgroupOf K).map (toSL3 ψ)) := by
    rw [← Subgroup.relIndex_ker, hQ, Subgroup.relIndex_subgroupOf hAK, Nat.card_eq_fintype_card]
    exact hqA
  have hcomm' : Nat.card (commV ((A.subgroupOf K).map ρ)) ≤ Nat.card F := by
    rw [← S4A.F.card_pre hπk hUW hπs, S4A.F.pre_commV hρ hπk hUW hπs hAK,
      Nat.card_eq_fintype_card]
    exact hcomm
  have hXQ : commV ((Q.subgroupOf K).map ρ) = ⊥ := by
    have hpre := S4A.F.pre_commV hρ hπk hUW hπs h.qK
    rw [sup_eq_right.mpr hWQ] at hpre
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hπs x
    have hv : (v : 𝔾) ∈ S4A.F.pre π (commV ((Q.subgroupOf K).map ρ)) :=
      S4A.F.mem_pre.mpr ⟨v.2, hx⟩
    rw [hpre] at hv
    rw [Subgroup.mem_bot]
    exact (hπk v).mpr hv
  have hKpre : S4A.F.pre π (commV ρ.range) = ⁅W, K⁆ ⊔ U := by
    have := S4A.F.pre_commV hρ hπk hUW hπs (le_refl K)
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  have hnt : ¬ commV ρ.range ≤ commV ((Q.subgroupOf K).map ρ) := by
    rw [hXQ]
    intro hle
    obtain ⟨x, hxL, hxW, hxZ⟩ := hW.exists_commutator_not_mem h
    have hx : x ∈ S4A.F.pre π (commV ρ.range) := by
      rw [hKpre]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mono le_rfl h.ltK hxL)
    obtain ⟨hxW', hxP⟩ := S4A.F.mem_pre.mp hx
    have h1 := (Subgroup.mem_bot).mp (hle hxP)
    exact hxZ (h.uZ ((hπk _).mp h1))
  obtain ⟨-, -, -, -, -, F', iF', fF', -, τ, β, hτs, -, hβk, hβe⟩ :=
    S4A.F.natSplit_quot h14 hSQ hsq hF hX2 (toSL3 ψ) (toSL3_surjective h.surj) hQ ρ hA2'
      hAc' hqA' hcomm' hnt
  have hcf : ∀ x : X, x ∈ commV ρ.range → (∀ k : ↥K, ρ k x = x) → x = 1 := by
    intro x hxP hxF
    set p : ↥(commV ρ.range) := ⟨x, hxP⟩ with hp
    have hfix : ∀ g : SL3 F', ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ
        Multiplicative.toAdd (β p) = Multiplicative.toAdd (β p) := by
      intro g
      obtain ⟨k, rfl⟩ := hτs g
      have h1 := hβe k p
      have h2 : S4A.F.resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) k p = p :=
        Subtype.ext (hxF k)
      rw [h2] at h1
      have := congrArg Multiplicative.toAdd h1
      rw [toAdd_ofAdd] at this
      exact this.symm
    have h0 : Multiplicative.toAdd (β p) = 0 := by
      funext j
      obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
      have := congrFun (hfix (rootElt i j 1)) i
      rw [rootElt_mulVec_eq_add_single hij] at this
      simpa using this
    have h1 : β p = 1 := by
      rw [← ofAdd_toAdd (β p), h0, ofAdd_zero]
    have := (hβk p).mp h1
    rw [hXQ, Subgroup.mem_bot] at this
    exact this
  intro x ⟨hxL, hxZ⟩
  have hxW : x ∈ W := hW.commutator_lt_le h hxL
  have hxP : π ⟨x, hxW⟩ ∈ commV ρ.range := by
    have hx : x ∈ S4A.F.pre π (commV ρ.range) := by
      rw [hKpre]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mono le_rfl h.ltK hxL)
    obtain ⟨hxW', hxP⟩ := S4A.F.mem_pre.mp hx
    exact hxP
  have hxF : ∀ k : ↥K, ρ k (π ⟨x, hxW⟩) = π ⟨x, hxW⟩ := by
    intro k
    rw [hρ k, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπk]
    have h1 := h.conj_mul_inv_mem_u hxZ k.2
    simpa [coe_conjOn_apply] using h1
  have h1 := hcf _ hxP hxF
  exact (hπk ⟨x, hxW⟩).mp h1

end LastLayer

namespace LastLayer

variable [Fintype F] [CharP F 2] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ) {W : Subgroup 𝔾} (hW : LastLayer K Q U Z V ψ W)
include h hW

omit [CharP F 2] in
theorem exists_commutator_inv_mul_mem {v : 𝔾} (hv : v ∈ W) :
    ∃ w ∈ ⁅W, Lt⁆, w⁻¹ * v ∈ Z := by
  classical
  set N := NatSec.ofIsSum hW.dual with hN
  obtain ⟨x, hxL, hxW, hxZ⟩ := hW.exists_commutator_not_mem h
  obtain ⟨w, hwL, -, hwv⟩ := N.exists_inv_mul_mem_of_invariant h.surj
    (fun l y hy => hW.conj_mem_commutator_lt h hy l.2) hxL hxW hxZ hv
  exact ⟨w, hwL, hwv⟩

omit [CharP F 2] in
theorem u_le_commutator : U ≤ ⁅W, Lt⁆ := by
  classical
  set NU := NatSec.ofIsSum h.nat with hNU
  obtain ⟨u, hu, huc⟩ := NU.exists_coord_eq ![1, 0, 0]
  obtain ⟨l, hl, hlg⟩ := h.exists_lt_toSL3_eq (rootElt 1 0 (1 : F))
  have hlu : (l : 𝔾) * u⁻¹ * (l : 𝔾)⁻¹ ∈ U := h.conj_mem_u (U.inv_mem hu) l.2
  have hcU : ⁅u, (l : 𝔾)⁆ ∈ U := by
    have e : ⁅u, (l : 𝔾)⁆ = u * ((l : 𝔾) * u⁻¹ * (l : 𝔾)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact U.mul_mem hu hlu
  have hc1 : ⁅u, (l : 𝔾)⁆ ≠ 1 := by
    intro h1
    have e : ⁅u, (l : 𝔾)⁆ = u * ((l : 𝔾) * u⁻¹ * (l : 𝔾)⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h0'' : NU.coord (u * ((l : 𝔾) * u⁻¹ * (l : 𝔾)⁻¹)) = 0 := by rw [← e, h1, NU.coord_one]
    rw [NU.coord_mul hu hlu, NU.coord_conj l (U.inv_mem hu), NU.coord_inv hu, natAct_false,
      hlg, huc, Matrix.mulVec_neg, rootElt_mulVec_eq_add_single (by decide)] at h0''
    have := congrFun h0'' 1
    simp [Matrix.vecHead, Matrix.vecTail] at this
  have hle := NU.le_of_invariant h.surj (H := ⁅U, Lt⁆)
    (fun l y hy => ML3.conj_mem_commutator (fun a ha => h.conj_mem_u ha l.2)
      (fun b hb => (Subgroup.mem_normalizer_iff.mp (h.ltN l.2) b).mp hb) hy)
    (Subgroup.commutator_mem_commutator hu hl) hcU hc1
  exact hle.trans (Subgroup.commutator_mono (h.uZ.trans hW.zW) le_rfl)

omit [CharP F 2] in
theorem isSum_commutator (hsplit : ⁅W, Lt⁆ ⊓ Z ≤ U) :
    IsSumOfNaturalModulesVia K ⁅W, Lt⁆ U ψ true 1 := by
  obtain ⟨hKW, hZW, β, hβs, hβk, hβe⟩ := hW.dual
  have hle : ⁅W, Lt⁆ ≤ W := hW.commutator_lt_le h
  refine ⟨fun k hk => Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨fun hx => hW.conj_mem_commutator_lt h hx hk, fun hx => ?_⟩, hW.u_le_commutator h,
    β.comp (Subgroup.inclusion hle), ?_, ?_, ?_⟩
  · have := hW.conj_mem_commutator_lt h hx (K.inv_mem hk)
    simpa [mul_assoc] using this
  · intro y
    obtain ⟨v, rfl⟩ := hβs y
    obtain ⟨w, hwL, hwv⟩ := hW.exists_commutator_inv_mul_mem h v.2
    refine ⟨⟨w, hwL⟩, ?_⟩
    have h1 : β (⟨w, hle hwL⟩⁻¹ * v) = 1 := by
      rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
      exact hwv
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact hsplit ⟨x.2, hx⟩
    · intro hx
      exact h.uZ hx
  · intro a u v huv i
    exact hβe a (Subgroup.inclusion hle u) (Subgroup.inclusion hle v) huv i

end LastLayer

section Final

variable [Fintype F] [CharP F 2] {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem conj_mem_sup_of_conj_mem {K A B : Subgroup 𝔾} (hB : B ≤ K)
    (hA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hBn : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    {k : 𝔾} (hk : k ∈ K) {x : 𝔾} (hx : x ∈ A ⊔ B) : k * x * k⁻¹ ∈ A ⊔ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_eq_of_mem_sup_of_conj (fun b hb a ha => hA b (hB hb) a ha) hx
  have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (hA k hk a ha) (hBn k hk b hb)

theorem last_struct (h : LastHyp K Q Lt U Z0 Z V ψ) {V₀ V₁ : Subgroup 𝔾}
    (h₀ : LastLayer K Q U Z V ψ V₀) (h₁ : LastLayer K Q U Z V ψ V₁) (hinf : V₀ ⊓ V₁ = Z)
    (hsup : V ≤ V₀ ⊔ V₁ ⊔ centerOf V) (h14 : MS14AS) (hSQ : SQTKQuot)
    (hsq : SQTKGroup (SL3 F)) {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    centerOf ⁅Q, Lt⁆ = U ∧ ⁅V₀, Lt⁆ ≤ ⁅Q, Lt⁆ ∧ ⁅V₁, Lt⁆ ≤ ⁅Q, Lt⁆ ∧
      ⁅V₀, Lt⁆ ⊓ ⁅V₁, Lt⁆ = U ∧ ⁅V₀, Lt⁆ ⊔ ⁅V₁, Lt⁆ = ⁅Q, Lt⁆ ∧
      IsSumOfNaturalModulesVia K ⁅V₀, Lt⁆ U ψ true 1 ∧
      IsSumOfNaturalModulesVia K ⁅V₁, Lt⁆ U ψ true 1 := by
  have hV₀K : V₀ ≤ K := h₀.le.trans h.vK
  have hV₁K : V₁ ≤ K := h₁.le.trans h.vK
  have hcK : centerOf V ≤ K := inf_le_left.trans h.vK
  have hab₀ := h₀.commutator_eq_bot h
  have hab₁ := h₁.commutator_eq_bot h
  have h01 : ⁅V₀, V₁⁆ ≤ U := LastLayer.commutator_le_u h h₀ h₁
  have h10 : ⁅V₁, V₀⁆ ≤ U := LastLayer.commutator_le_u h h₁ h₀
  have hV0 : ⁅V, V₀⁆ ≤ U :=
    h₀.commutator_vv_le_u h hV₀K hV₁K hsup (by rw [hab₀]; exact bot_le) h10
  have hV1 : ⁅V, V₁⁆ ≤ U :=
    h₁.commutator_vv_le_u h hV₀K hV₁K hsup h01 (by rw [hab₁]; exact bot_le)
  have hs0 := h₀.inf_z_le_u h h14 hSQ hsq hF (h₀.commutator_q_le_u h hV0)
  have hs1 := h₁.inf_z_le_u h h14 hSQ hsq hF (h₁.commutator_q_le_u h hV1)
  have hd0 := h₀.isSum_commutator h hs0
  have hd1 := h₁.isSum_commutator h hs1
  set W₀ := ⁅V₀, Lt⁆ with hW₀
  set W₁ := ⁅V₁, Lt⁆ with hW₁
  have hW₀Q : W₀ ≤ ⁅Q, Lt⁆ := Subgroup.commutator_mono (h₀.wQ h) le_rfl
  have hW₁Q : W₁ ≤ ⁅Q, Lt⁆ := Subgroup.commutator_mono (h₁.wQ h) le_rfl
  have hU0 : U ≤ W₀ := h₀.u_le_commutator h
  have hW₀V : W₀ ≤ V := (h₀.commutator_lt_le h).trans h₀.le
  have hW₁V : W₁ ≤ V := (h₁.commutator_lt_le h).trans h₁.le
  have hinfW : W₀ ⊓ W₁ = U := by
    apply le_antisymm
    · intro x hx
      have hxZ : x ∈ Z := hinf ▸ ⟨h₀.commutator_lt_le h hx.1, h₁.commutator_lt_le h hx.2⟩
      exact hs0 ⟨hx.1, hxZ⟩
    · exact le_inf hU0 (h₁.u_le_commutator h)
  have hW₀n : ∀ k ∈ K, ∀ a ∈ W₀, k * a * k⁻¹ ∈ W₀ := fun k hk a ha =>
    h₀.conj_mem_commutator_lt h ha hk
  have hW₁n : ∀ k ∈ K, ∀ a ∈ W₁, k * a * k⁻¹ ∈ W₁ := fun k hk a ha =>
    h₁.conj_mem_commutator_lt h ha hk
  have hW₁K : W₁ ≤ K := hW₁V.trans h.vK
  have hPn : ∀ k ∈ K, ∀ x ∈ W₀ ⊔ W₁, k * x * k⁻¹ ∈ W₀ ⊔ W₁ := fun k hk x hx =>
    conj_mem_sup_of_conj_mem hW₁K hW₀n hW₁n hk hx
  have hPN : K ≤ Subgroup.normalizer ((W₀ ⊔ W₁ : Subgroup 𝔾) : Set 𝔾) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hPn k hk x, fun hx => ?_⟩
    have := hPn k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hUN : K ≤ Subgroup.normalizer (U : Set 𝔾) := h.nat.1
  have hZab : ∀ b ∈ Z, ∀ b' ∈ Z, ⁅b, b'⁆ ∈ U := by
    intro b hb b' hb'
    have : ⁅b, b'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.comm_z_q hb (h.vq (h.zv hb'))
    rw [this]
    exact U.one_mem
  have hcL : ⁅centerOf V, Lt⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro b hb l hl
    exact comm_mem_of_perfect h.perf h.uZ (fun l hl a ha => h.conj_mem_u ha (h.ltK hl)) hZab
      (fun b hb l hl => h.conj_mul_inv_mem_u hb (h.ltK hl))
      (fun l hl => h.bl (Subgroup.commutator_mem_commutator hb hl)) hl
  have hVL : ⁅V, Lt⁆ ≤ W₀ ⊔ W₁ := by
    refine (Subgroup.commutator_mono hsup le_rfl).trans ?_
    exact commutator_sup_le_of_le_normalizer hPN (sup_le hV₀K hV₁K) hcK
      (commutator_sup_le_of_le_normalizer hPN hV₀K hV₁K le_sup_left le_sup_right)
      (hcL.trans (hU0.trans le_sup_left))
  have hZVc : ∀ W' : Subgroup 𝔾, W' ≤ V → ⁅centerOf V, W'⁆ = ⊥ := by
    intro W' hW'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right.trans (Subgroup.centralizer_le hW')
  have hVV : ⁅V, V⁆ ≤ U := by
    refine (Subgroup.commutator_mono hsup le_rfl).trans ?_
    refine commutator_sup_le_of_le_normalizer hUN (sup_le hV₀K hV₁K) hcK
      (commutator_sup_le_of_le_normalizer hUN hV₀K hV₁K ?_ ?_) (by rw [hZVc V le_rfl]; exact bot_le)
    · rw [Subgroup.commutator_comm]; exact hV0
    · rw [Subgroup.commutator_comm]; exact hV1
  have hQL : ⁅Q, Lt⁆ ≤ W₀ ⊔ W₁ := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    refine comm_mem_of_perfect h.perf (sup_le hW₀V hW₁V)
      (fun l hl a ha => hPn l (h.ltK hl) a ha)
      (fun b hb b' hb' => hU0.trans le_sup_left (hVV (Subgroup.commutator_mem_commutator hb hb')))
      (fun b hb l hl => ?_) (fun l hl => h.ql (Subgroup.commutator_mem_commutator hq hl)) hl
    have e : l * b * l⁻¹ * b⁻¹ = ⁅b, l⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (W₀ ⊔ W₁).inv_mem (hVL (Subgroup.commutator_mem_commutator hb hl))
  have hsupW : W₀ ⊔ W₁ = ⁅Q, Lt⁆ := le_antisymm (sup_le hW₀Q hW₁Q) hQL
  have hne : ¬ ⁅W₀, W₁⁆ = ⊥ := by
    intro hbot
    have hcomm01 : ⁅V₀, V₁⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v₀ hv₀ v₁ hv₁
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      obtain ⟨w₀, hw₀, hz₀⟩ := h₀.exists_commutator_inv_mul_mem h hv₀
      obtain ⟨w₁, hw₁, hz₁⟩ := h₁.exists_commutator_inv_mul_mem h hv₁
      have e₀ : v₀ = w₀ * (w₀⁻¹ * v₀) := by group
      have e₁ : v₁ = w₁ * (w₁⁻¹ * v₁) := by group
      have hww : w₀ * w₁ = w₁ * w₀ := ML3.commute_of_commutator_eq_bot hbot hw₀ hw₁
      have hc1 := h.comm_z_q hz₀ (h.vq (hW₁V hw₁))
      have hc2 := h.comm_z_q hz₀ (h.vq (h.zv hz₁))
      have hc3 := h.comm_z_q hz₁ (h.vq (hW₀V hw₀))
      rw [e₀, e₁]
      calc w₀ * (w₀⁻¹ * v₀) * (w₁ * (w₁⁻¹ * v₁))
          = w₀ * ((w₀⁻¹ * v₀) * w₁) * (w₁⁻¹ * v₁) := by group
        _ = w₀ * (w₁ * (w₀⁻¹ * v₀)) * (w₁⁻¹ * v₁) := by rw [hc1]
        _ = (w₀ * w₁) * ((w₀⁻¹ * v₀) * (w₁⁻¹ * v₁)) := by group
        _ = (w₁ * w₀) * ((w₁⁻¹ * v₁) * (w₀⁻¹ * v₀)) := by rw [hww, hc2]
        _ = w₁ * (w₀ * (w₁⁻¹ * v₁)) * (w₀⁻¹ * v₀) := by group
        _ = w₁ * ((w₁⁻¹ * v₁) * w₀) * (w₀⁻¹ * v₀) := by rw [hc3]
        _ = w₁ * (w₁⁻¹ * v₁) * (w₀ * (w₀⁻¹ * v₀)) := by group
    have hbotN : K ≤ Subgroup.normalizer ((⊥ : Subgroup 𝔾) : Set 𝔾) := by
      intro k _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    have hVi : ∀ W' : Subgroup 𝔾, W' ≤ V → ⁅V₀, W'⁆ ≤ ⊥ → ⁅V₁, W'⁆ ≤ ⊥ → ⁅V, W'⁆ ≤ ⊥ := by
      intro W' hW' h0 h1
      refine (Subgroup.commutator_mono hsup le_rfl).trans ?_
      exact commutator_sup_le_of_le_normalizer hbotN (sup_le hV₀K hV₁K) hcK
        (commutator_sup_le_of_le_normalizer hbotN hV₀K hV₁K h0 h1) (hZVc W' hW').le
    have hVV0 : ⁅V, V₀⁆ ≤ ⊥ := hVi V₀ h₀.le hab₀.le (by rw [Subgroup.commutator_comm,
      hcomm01])
    have hVV1 : ⁅V, V₁⁆ ≤ ⊥ := hVi V₁ h₁.le hcomm01.le hab₁.le
    have hVVb : ⁅V, V⁆ ≤ ⊥ := hVi V le_rfl (by rw [Subgroup.commutator_comm]; exact hVV0)
      (by rw [Subgroup.commutator_comm]; exact hVV1)
    exact h.vne (le_bot_iff.mp hVVb)
  have hC : ∀ {X Y : Subgroup 𝔾}, IsSumOfNaturalModulesVia K X U ψ true 1 → Y ≤ Q →
      (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) → ¬ ⁅X, Y⁆ = ⊥ →
      X ⊓ Subgroup.centralizer (Y : Set 𝔾) ≤ U := by
    intro X Y hX hYQ hYn hXY
    by_contra hnle
    obtain ⟨c, ⟨hcX, hcY⟩, hcU⟩ := Set.not_subset.mp hnle
    set NX := NatSec.ofIsSum hX with hNX
    have hinv : ∀ l : ↥K, ∀ y ∈ X ⊓ Subgroup.centralizer (Y : Set 𝔾),
        (l : 𝔾) * y * (l : 𝔾)⁻¹ ∈ X ⊓ Subgroup.centralizer (Y : Set 𝔾) := by
      intro l y hy
      refine ⟨NX.conj_mem l hy.1, ?_⟩
      show (l : 𝔾) * y * (l : 𝔾)⁻¹ ∈ Subgroup.centralizer (Y : Set 𝔾)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ (hYn _ (K.inv_mem l.2) z hz)
      calc z * ((l : 𝔾) * y * (l : 𝔾)⁻¹)
          = (l : 𝔾) * (((l : 𝔾)⁻¹ * z * (l : 𝔾)⁻¹⁻¹) * y) * (l : 𝔾)⁻¹ := by group
        _ = (l : 𝔾) * (y * ((l : 𝔾)⁻¹ * z * (l : 𝔾)⁻¹⁻¹)) * (l : 𝔾)⁻¹ := by rw [h1]
        _ = (l : 𝔾) * y * (l : 𝔾)⁻¹ * z := by group
    have hall : X ≤ Subgroup.centralizer (Y : Set 𝔾) := by
      intro x hx
      obtain ⟨w, hw, -, hwx⟩ := NX.exists_inv_mul_mem_of_invariant h.surj hinv
        ⟨hcX, hcY⟩ hcX hcU hx
      have hu : w⁻¹ * x ∈ Subgroup.centralizer (Y : Set 𝔾) :=
        (h.uZ.trans (h.zq.trans (Subgroup.centralizer_le hYQ))) hwx
      have := (Subgroup.centralizer (Y : Set 𝔾)).mul_mem hw.2 hu
      rwa [mul_inv_cancel_left] at this
    exact hXY ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hall)
  have hC₀ : W₀ ⊓ Subgroup.centralizer (W₁ : Set 𝔾) ≤ U :=
    hC hd0 (hW₁V.trans h.vq) hW₁n hne
  have hC₁ : W₁ ⊓ Subgroup.centralizer (W₀ : Set 𝔾) ≤ U :=
    hC hd1 (hW₀V.trans h.vq) hW₀n (by rw [Subgroup.commutator_comm]; exact hne)
  have hcen : centerOf ⁅Q, Lt⁆ = U := by
    apply le_antisymm
    · rintro x ⟨hxP, hxc⟩
      rw [← hsupW] at hxP hxc
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_conj
        (fun b hb a ha => hW₀n b (hW₁K hb) a ha) hxP
      have hc0 : ∀ y ∈ W₀, ∀ y' ∈ W₀, y * y' = y' * y := fun y hy y' hy' =>
        ML3.commute_of_commutator_eq_bot hab₀ (h₀.commutator_lt_le h hy)
          (h₀.commutator_lt_le h hy')
      have hc1 : ∀ y ∈ W₁, ∀ y' ∈ W₁, y * y' = y' * y := fun y hy y' hy' =>
        ML3.commute_of_commutator_eq_bot hab₁ (h₁.commutator_lt_le h hy)
          (h₁.commutator_lt_le h hy')
      have hbW : b ∈ Subgroup.centralizer (W₀ : Set 𝔾) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 := Subgroup.mem_centralizer_iff.mp hxc w (Subgroup.mem_sup_left hw)
        have h2 := hc0 a ha w hw
        have h3 : a * (w * b) = a * (b * w) := by
          calc a * (w * b) = (a * w) * b := by group
            _ = (w * a) * b := by rw [h2]
            _ = w * (a * b) := by group
            _ = (a * b) * w := h1
            _ = a * (b * w) := by group
        exact mul_left_cancel h3
      have haW : a ∈ Subgroup.centralizer (W₁ : Set 𝔾) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 := Subgroup.mem_centralizer_iff.mp hxc w (Subgroup.mem_sup_right hw)
        have h2 := hc1 b hb w hw
        have h3 : (w * a) * b = (a * w) * b := by
          calc (w * a) * b = w * (a * b) := by group
            _ = (a * b) * w := h1
            _ = a * (b * w) := by group
            _ = a * (w * b) := by rw [h2]
            _ = (a * w) * b := by group
        exact mul_right_cancel h3
      exact U.mul_mem (hC₀ ⟨ha, haW⟩) (hC₁ ⟨hb, hbW⟩)
    · exact le_inf (hU0.trans hW₀Q) ((h.uZ.trans h.zq).trans
        (Subgroup.centralizer_le (h.ql.trans h.vq)))
  exact ⟨hcen, hW₀Q, hW₁Q, hinfW, hsupW, hd0, hd1⟩

end Final

end Abs

end CFSG.Quasithin.MS93.S46
