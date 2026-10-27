module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NatPoint
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)
open CFSG.Quasithin.Vol2.Ch11.G2Q8 (U0 InF isPGroup_U0 g2X_mem_U0 g2Y_mem_U0 g2A_mem_U0
  g2Act_g2X_e0 g2Act_g2Y_e12 g2Act_g2A_uSL fixed_U0 inF_q6_iff not_two_dvd_index_U0
  finite_cayleyGroup g2Act_mul_apply' g2Act_tv tv eu ev)
open scoped Matrix

namespace A6L76Oi

section Levi

variable {F : Type} [Field F]

@[expose] def leviTLMat (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem det_leviTLMat (B : Matrix (Fin 2) (Fin 2) F) : (leviTLMat B).det = B.det := by
  rw [leviTLMat, Matrix.det_fin_three, Matrix.det_fin_two]
  simp

theorem leviTLMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    leviTLMat (A * B) = leviTLMat A * leviTLMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviTLMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem leviTLMat_one : leviTLMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviTLMat]

@[expose] def leviTL : Matrix.SpecialLinearGroup (Fin 2) F →* SL3 F where
  toFun B := ⟨leviTLMat (B : Matrix (Fin 2) (Fin 2) F), by rw [det_leviTLMat, B.2]⟩
  map_one' := Subtype.ext (by
    show leviTLMat ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, leviTLMat_one])
  map_mul' A B := Subtype.ext (by
    show leviTLMat ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      leviTLMat (A : Matrix (Fin 2) (Fin 2) F) * leviTLMat (B : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, leviTLMat_mul])

theorem leviTL_coe (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((leviTL B : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      leviTLMat (B : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] def leviCay : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(cayleyGroup F) :=
  g2A.comp leviTL

theorem leviCay_apply (B : Matrix.SpecialLinearGroup (Fin 2) F) : leviCay B = g2A (leviTL B) :=
  rfl

end Levi

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def cayHom : ↥(cayleyGroup F) →* MulAut (Multiplicative (Ix3 → F)) where
  toFun g :=
    { toFun := fun w => Multiplicative.ofAdd (g2Act g (Multiplicative.toAdd w))
      invFun := fun w => Multiplicative.ofAdd (g2Act g⁻¹ (Multiplicative.toAdd w))
      left_inv := fun w => by
        show Multiplicative.ofAdd (g2Act g⁻¹ (g2Act g (Multiplicative.toAdd w))) = w
        rw [← g2Act_mul_apply', inv_mul_cancel, map_one]
        rfl
      right_inv := fun w => by
        show Multiplicative.ofAdd (g2Act g (g2Act g⁻¹ (Multiplicative.toAdd w))) = w
        rw [← g2Act_mul_apply', mul_inv_cancel, map_one]
        rfl
      map_mul' := fun w w' => by
        show Multiplicative.ofAdd (g2Act g (Multiplicative.toAdd w + Multiplicative.toAdd w')) =
          Multiplicative.ofAdd (g2Act g (Multiplicative.toAdd w)) *
            Multiplicative.ofAdd (g2Act g (Multiplicative.toAdd w'))
        rw [map_add, ofAdd_add] }
  map_one' := MulEquiv.ext fun w => by
    show Multiplicative.ofAdd (g2Act 1 (Multiplicative.toAdd w)) = w
    rw [map_one]
    rfl
  map_mul' g h := MulEquiv.ext fun w => by
    show Multiplicative.ofAdd (g2Act (g * h) (Multiplicative.toAdd w)) =
      Multiplicative.ofAdd (g2Act g (g2Act h (Multiplicative.toAdd w)))
    rw [g2Act_mul_apply']

theorem cayHom_apply (g : ↥(cayleyGroup F)) (w : Multiplicative (Ix3 → F)) :
    Multiplicative.toAdd (cayHom g w) = g2Act g (Multiplicative.toAdd w) := rfl

theorem disp_y1 (t : F) (v : Ix3 → F) :
    g2Act (g2Y ![0, t, 0]) v - v =
      q6 (t * v (.inr 2)) 0 (t * v (.inr 0)) 0 (t * (t * v (.inl 1))) 0 := by
  rw [g2Act_g2Y_e12]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem disp_e12 (c : F) (v : Ix3 → F) :
    g2Act (g2A (uSL 0 0 c)) v - v = q6 0 (c * v (.inl 2)) 0 0 0 (c * v (.inr 1)) := by
  rw [g2Act_g2A_uSL]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem disp_x0 (α : F) (v : Ix3 → F) :
    g2Act (g2X ![α, 0, 0]) v - v =
      q6 (α * α * v (.inr 0)) 0 0 0 (α * v (.inl 2)) (α * v (.inl 1)) := by
  rw [g2Act_g2X_e0]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem U0_comm [Finite F] (hq : 2 < Nat.card F) {w v : Ix3 → F} (hw : InF 1 w)
    (hv : ∀ u ∈ U0 F, g2Act u v - v = 0 ∨ g2Act u v - v = w) : InF 1 v := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
      by_cases h : c = 0
      · simp [h]
      · simp [hcon c h]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  have hoff : ∀ u ∈ U0 F, ∀ k, 1 ≤ Vol2.Ch11.G2Q8.ht k → (g2Act u v - v) k = 0 := by
    intro u hu k hk
    rcases hv u hu with h | h <;> rw [h]
    · rfl
    · exact hw k hk
  have hv0 : v (.inr 0) = 0 := by
    have h := hoff _ (g2Y_mem_U0 1 0) (.inl 2) (by decide)
    rw [disp_y1] at h
    simpa [q6] using h
  have hu2 : v (.inl 2) = 0 := by
    have h := hoff _ (g2A_mem_U0 0 0 1) (.inl 1) (by decide)
    rw [disp_e12] at h
    simpa [q6] using h
  have hv1 : v (.inr 1) = 0 := by
    have h := hoff _ (g2A_mem_U0 0 0 1) (.inr 2) (by decide)
    rw [disp_e12] at h
    simpa [q6] using h
  have hu1 : v (.inl 1) = 0 := by
    have h := hoff _ (g2X_mem_U0 1) (.inr 2) (by decide)
    rw [disp_x0] at h
    simpa [q6] using h
  have hv2 : v (.inr 2) = 0 := by
    have key : ∀ t : F, t * v (.inr 2) = 0 ∨ t * v (.inr 2) = w (.inl 0) := by
      intro t
      rcases hv _ (g2Y_mem_U0 t 0) with h | h
      · left
        have e := congrFun h (.inl 0)
        rw [disp_y1] at e
        simpa [q6] using e
      · right
        have e := congrFun h (.inl 0)
        rw [disp_y1] at e
        simpa [q6] using e
    by_contra h0
    rcases key 1 with h1 | h1
    · exact h0 (by simpa using h1)
    · rcases key c with h2 | h2
      · exact mul_ne_zero hc0 h0 h2
      · apply hc1
        have : c * v (.inr 2) = 1 * v (.inr 2) := h2.trans h1.symm
        exact mul_right_cancel₀ h0 this
  conv => rw [q6_eta v]
  rw [inF_q6_iff]
  exact ⟨by omega, fun _ => hu1, fun _ => hu2, fun _ => hv0, fun _ => hv1, fun _ => hv2⟩

theorem cayHom_fixed {m : Multiplicative (Ix3 → F)} (h : ∀ g, cayHom g m = m) : m = 1 := by
  have h1 : InF 1 (Multiplicative.toAdd m) :=
    fixed_U0 fun u _ => congrArg Multiplicative.toAdd (h u)
  have h2 := congrArg Multiplicative.toAdd (h (g2A (tv 1 0 (by decide) 1)))
  rw [cayHom_apply, g2Act_tv] at h2
  have h3 : Multiplicative.toAdd m (.inl 0) = 0 := by
    have e := congrFun h2 (.inl 1)
    simpa [eu, ev, Pi.single_apply] using e
  apply Multiplicative.toAdd.injective
  rw [toAdd_one, q6_eta (Multiplicative.toAdd m), h3, h1 (.inl 1) (by decide),
    h1 (.inl 2) (by decide), h1 (.inr 0) (by decide), h1 (.inr 1) (by decide),
    h1 (.inr 2) (by decide), q6_zero]

theorem leviCay_fix (B : Matrix.SpecialLinearGroup (Fin 2) F) {x : Ix3 → F} (hx : InF 1 x) :
    g2Act (leviCay B) x = x := by
  have e : x = q6 (x (.inl 0)) 0 0 0 0 0 := by
    conv_lhs => rw [q6_eta x]
    rw [hx (.inl 1) (by decide), hx (.inl 2) (by decide), hx (.inr 0) (by decide),
      hx (.inr 1) (by decide), hx (.inr 2) (by decide)]
  rw [e, leviCay_apply, g2Act_g2A, leviTL_coe]
  simp [leviTLMat]

theorem leviCay_injective : Function.Injective (leviCay (F := F)) := by
  intro A B h
  have h1 : ∀ w, g2Act (leviCay A) w = g2Act (leviCay B) w := fun w => by rw [h]
  have e1 := h1 (q6 0 1 0 0 0 0)
  have e2 := h1 (q6 0 0 1 0 0 0)
  rw [leviCay_apply, leviCay_apply, g2Act_g2A, g2Act_g2A, leviTL_coe, leviTL_coe] at e1 e2
  obtain ⟨-, a1, a2, -, -, -⟩ := q6_inj e1
  obtain ⟨-, b1, b2, -, -, -⟩ := q6_inj e2
  simp [leviTLMat] at a1 a2 b1 b2
  ext i j
  fin_cases i <;> fin_cases j
  · exact a1
  · exact b1
  · exact a2
  · exact b2

theorem exists_conj_U0 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {P : Subgroup ↥(cayleyGroup F)} (hP : IsPGroup 2 ↥P) (hodd : ¬ 2 ∣ P.index) :
    ∃ g : ↥(cayleyGroup F), ∀ x ∈ U0 F, g⁻¹ * x * g ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := F)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(cayleyGroup F)) (hP.toSylow hodd)
    (isPGroup_U0.toSylow (not_two_dvd_index_U0 hF hn))
  refine ⟨g, fun x hx => ?_⟩
  rw [← IsPGroup.toSylow_coe isPGroup_U0 (not_two_dvd_index_U0 hF hn), ← hg,
    Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe] at hx
  exact hx

@[expose] noncomputable def toCay : ↥(quasithinG2 F) ≃* ↥(cayleyGroup F) :=
  MulEquiv.subgroupCongr CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup

theorem zornRealizes_clean {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(quasithinG2 F) →* ↥Y}
    (h : (FFModel.zornQ (quasithinG2 F)).RealizesVia Y U Z π) :
    Function.Surjective π ∧ (∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U) ∧
      ∃ β : ↥U →* Multiplicative (Ix3 → F), Function.Surjective β ∧
        (∀ u, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥(quasithinG2 F)) (u : ↥U) (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
          β ⟨_, hu⟩ = cayHom (toCay γ) (β u) := by
  obtain ⟨hs, -, -, hU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let LM := CFSG.Quasithin.Vol2.KGNat.linModelZorn (quasithinG2 F)
    (le_of_eq CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup)
  refine ⟨hs, hU, LM.e.toMonoidHom.comp β, LM.e.surjective.comp hβs, fun u => ?_,
    fun γ u hu => ?_⟩
  · show LM.e (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hact := hsec γ m m.2
    have h1 := hβe γ u m hu hact hm.symm
    show LM.e (β ⟨_, hu⟩) = cayHom (toCay γ) (LM.e (β u))
    refine (congrArg LM.e h1).trans ?_
    apply Multiplicative.toAdd.injective
    rw [LM.e_act γ m hact, ← hm, cayHom_apply]
    rfl

end A6L76Oi

end CFSG.Quasithin.H13.A6
