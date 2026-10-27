module

public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open Polynomial Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS

section Decomp

variable {V : Type*} [AddCommGroup V]

theorem exists_decomp (s : Finset (AddSubgroup V)) :
    ∀ v ∈ s.sup id, ∃ f : AddSubgroup V → V, (∀ W ∈ s, f W ∈ W) ∧ ∑ W ∈ s, f W = v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    refine ⟨fun _ => 0, fun W hW => absurd hW (Finset.notMem_empty _), ?_⟩
    simp only [Finset.sum_empty]
    exact ((by simpa using hv : v = 0)).symm
  | insert W s hW ih =>
    intro v hv
    rw [Finset.sup_insert] at hv
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hv
    obtain ⟨f', hf'1, hf'2⟩ := ih z hz
    refine ⟨Function.update f' W y, fun W' hW' => ?_, ?_⟩
    · by_cases h : W' = W
      · subst h; simpa using hy
      · rw [Function.update_of_ne h]
        exact hf'1 W' ((Finset.mem_insert.mp hW').resolve_left h)
    · rw [Finset.sum_insert hW, Function.update_self]
      congr 1
      rw [← hf'2]
      refine Finset.sum_congr rfl fun W' hW' => ?_
      have : W' ≠ W := fun h => hW (h ▸ hW')
      rw [Function.update_of_ne this]

theorem eq_zero_of_sum_eq_zero {s : Finset (AddSubgroup V)} (hs : s.SupIndep id)
    {f : AddSubgroup V → V} (hf : ∀ W ∈ s, f W ∈ W) (hsum : ∑ W ∈ s, f W = 0) :
    ∀ W ∈ s, f W = 0 := by
  classical
  intro W₀ hW₀
  have h1 : f W₀ = -∑ W ∈ s.erase W₀, f W := by
    rw [← Finset.add_sum_erase s f hW₀] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  have h2 : f W₀ ∈ (s.erase W₀).sup id := by
    rw [h1]
    refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun W hW => ?_)
    exact (Finset.le_sup (f := id) hW) (hf W (Finset.mem_of_mem_erase hW))
  have hdisj := hs (Finset.erase_subset W₀ s) hW₀ (Finset.notMem_erase W₀ s)
  have : f W₀ ∈ W₀ ⊓ (s.erase W₀).sup id := ⟨hf W₀ hW₀, h2⟩
  rw [(disjoint_iff.mp hdisj : W₀ ⊓ (s.erase W₀).sup id = ⊥), AddSubgroup.mem_bot] at this
  exact this

end Decomp


section ModuleLevel

open CFSG.Timmesfeld.ARS.NaturalModule

variable {K V : Type*} [Field K] [CharP K 2] [PerfectRing K 2] [AddCommGroup V] [Finite V]
  [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]

theorem pow_mulVec_line (x : SpecialLinearGroup (Fin 2) K)
    (hx10 : (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (i : ℕ) (t : K) :
    ((x ^ i : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![t, 0] =
      ![((x : Matrix (Fin 2) (Fin 2) K) 0 0) ^ i * t, 0] := by
  induction i generalizing t with
  | zero => ext j; fin_cases j <;> simp
  | succ i ih =>
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_pow, ih]
    ext j
    fin_cases j
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pow_succ]
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx10]

theorem evalAct_eq_zero
    (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {L : AddSubgroup V} (hL : ∀ w ∈ L, ∀ a ∈ upperUnipotent K, a • w = w)
    (hgen : ∀ U : AddSubgroup V, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      L ≤ U → U = ⊤)
    (x : SpecialLinearGroup (Fin 2) K) (hx10 : (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (p : ℕ[X]) (hp : p.eval₂ (Nat.castRingHom K) ((x : Matrix (Fin 2) (Fin 2) K) 0 0) = 0)
    (v : V) (hv : ∀ a ∈ upperUnipotent K, a • v = v) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i • v) = 0 := by
  classical
  obtain ⟨s, hind, hsup, hs⟩ := exists_supIndep_natural hfix hquad hL hgen
  obtain ⟨f, hf1, hf2⟩ := exists_decomp s v (by rw [hsup]; exact AddSubgroup.mem_top v)
  have hfixed : ∀ a ∈ upperUnipotent K, ∀ W ∈ s, a • f W = f W := by
    intro a ha
    have hsum : ∑ W ∈ s, (a • f W - f W) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hf2, hv a ha, sub_self]
    have hmem : ∀ W ∈ s, (fun W => a • f W - f W) W ∈ W := by
      intro W hW
      obtain ⟨hinv, -⟩ := hs W hW
      exact W.sub_mem (hinv a (f W) (hf1 W hW)) (hf1 W hW)
    intro W hW
    exact sub_eq_zero.mp (eq_zero_of_sum_eq_zero hind hmem hsum W hW)
  have hzero : ∀ W ∈ s, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i • f W) = 0 := by
    intro W hW
    obtain ⟨-, -, -, θ, hθinj, hθrange, hθ⟩ := hs W hW
    have hfW : f W ∈ θ.range := by rw [hθrange]; exact hf1 W hW
    obtain ⟨u, hu⟩ := hfW
    have hu1 : u 1 = 0 := by
      have h1 : upperElt K 1 • θ u = θ u := by
        rw [hu]
        exact hfixed _ ((mem_upperUnipotent_iff K).mpr ⟨1, rfl⟩) W hW
      rw [← hθ] at h1
      have h3 := hθinj h1
      have h4 := congrFun h3 0
      rw [upperElt_mulVec] at h4
      simp only [one_mul, Matrix.cons_val_zero] at h4
      have : u 0 + u 1 = u 0 := h4
      exact add_eq_left.mp this
    have hu' : u = ![u 0, 0] := by
      ext j; fin_cases j
      · rfl
      · simpa using hu1
    set b : K := (x : Matrix (Fin 2) (Fin 2) K) 0 0 with hb
    set w : ℕ → (Fin 2 → K) := fun i => ![b ^ i * u 0, 0] with hw
    have hxi : ∀ i : ℕ, x ^ i • θ u = θ (w i) := by
      intro i
      show x ^ i • θ u = θ ![b ^ i * u 0, 0]
      rw [← pow_mulVec_line x hx10 i (u 0), ← hu', ← hθ]
    have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i • θ u) =
        θ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • w i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hxi, map_nsmul]
    have hfirst : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (b ^ i * u 0) = 0 := by
      have : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (b ^ i * u 0) =
          (p.eval₂ (Nat.castRingHom K) b) * u 0 := by
        rw [Polynomial.eval₂_eq_sum_range, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [nsmul_eq_mul, mul_assoc]
      rw [this, hp, zero_mul]
    have hvec : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • w i = 0 := by
      ext j
      fin_cases j
      · simpa [hw, Finset.sum_apply] using hfirst
      · simp [hw, Finset.sum_apply]
    rw [← hu, hsum, hvec, map_zero]
  have hlin : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i • v) =
      ∑ W ∈ s, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i • f W) := by
    rw [← hf2]
    simp only [Finset.smul_sum]
    exact Finset.sum_comm
  rw [hlin]
  exact Finset.sum_eq_zero hzero

end ModuleLevel


open scoped commutatorElement

section Quotient

variable {Γ : Type*} [Group Γ] {K : Type*} [Field K]

private structure ModData (φ : Γ →* SpecialLinearGroup (Fin 2) K) (C Lγ : Subgroup Γ) : Prop where
  surj : Function.Surjective φ
  le : Lγ ≤ C
  cn : ∀ z : Γ, ∀ c ∈ C, z * c * z⁻¹ ∈ C
  ln : ∀ z : Γ, ∀ l ∈ Lγ, z * l * z⁻¹ ∈ Lγ
  comm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ Lγ
  ker : ∀ z : Γ, φ z = 1 → ∀ c ∈ C, ⁅z, c⁆ ∈ Lγ

variable {φ : Γ →* SpecialLinearGroup (Fin 2) K} {C Lγ : Subgroup Γ}

private theorem ModData.normal (h : ModData φ C Lγ) : (Lγ.subgroupOf C).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.ln g n hn

private def Qmod (_h : ModData φ C Lγ) : Type _ := Additive (↥C ⧸ Lγ.subgroupOf C)

private noncomputable instance (h : ModData φ C Lγ) : AddCommGroup (Qmod h) :=
  letI : (Lγ.subgroupOf C).Normal := h.normal
  letI : CommGroup (↥C ⧸ Lγ.subgroupOf C) :=
    { (inferInstance : Group (↥C ⧸ Lγ.subgroupOf C)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := h.comm (b⁻¹ : ↥C) (b⁻¹).2 (a⁻¹ : ↥C) (a⁻¹).2
        convert this using 1
        simp [commutatorElement_def, mul_assoc] }
  inferInstanceAs (AddCommGroup (Additive (↥C ⧸ Lγ.subgroupOf C)))

private instance [Finite Γ] (h : ModData φ C Lγ) : Finite (Qmod h) :=
  inferInstanceAs (Finite (Additive (↥C ⧸ Lγ.subgroupOf C)))

private def Qmod.mk (h : ModData φ C Lγ) (c : ↥C) : Qmod h :=
  Additive.ofMul (QuotientGroup.mk c : ↥C ⧸ Lγ.subgroupOf C)


private theorem Qmod.mk_mul (h : ModData φ C Lγ) (a b : ↥C) :
    Qmod.mk h (a * b) = Qmod.mk h a + Qmod.mk h b := rfl

private theorem Qmod.mk_one (h : ModData φ C Lγ) : Qmod.mk h 1 = 0 := rfl

private theorem Qmod.mk_surjective (h : ModData φ C Lγ) :
    Function.Surjective (Qmod.mk h) := fun v =>
  let ⟨c, hc⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  ⟨c, by simp only [Qmod.mk, hc]; rfl⟩

private theorem Qmod.mk_eq_mk_iff (h : ModData φ C Lγ) (a b : ↥C) :
    Qmod.mk h a = Qmod.mk h b ↔ (a : Γ)⁻¹ * b ∈ Lγ := by
  letI : (Lγ.subgroupOf C).Normal := h.normal
  have e : Qmod.mk h a = Qmod.mk h b ↔
      (QuotientGroup.mk a : ↥C ⧸ Lγ.subgroupOf C) = QuotientGroup.mk b :=
    ⟨fun hab => Additive.ofMul.injective hab, fun hab => congrArg Additive.ofMul hab⟩
  rw [e, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

private theorem Qmod.mk_eq_zero_iff (h : ModData φ C Lγ) (c : ↥C) :
    Qmod.mk h c = 0 ↔ (c : Γ) ∈ Lγ := by
  rw [← Qmod.mk_one h, Qmod.mk_eq_mk_iff]
  simp

private def cjC (h : ModData φ C Lγ) (z : Γ) : ↥C →* ↥C where
  toFun c := ⟨z * c * z⁻¹, h.cn z c c.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

private noncomputable def actM [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z : Γ) :
    (↥C ⧸ Lγ.subgroupOf C) →* (↥C ⧸ Lγ.subgroupOf C) :=
  QuotientGroup.map _ _ (cjC h z) (fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    simpa [cjC] using h.ln z n hn)

private theorem actM_mk [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    actM h z (QuotientGroup.mk c) = QuotientGroup.mk (cjC h z c) := rfl

private theorem actM_mul [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z z' : Γ)
    (x : ↥C ⧸ Lγ.subgroupOf C) : actM h (z * z') x = actM h z (actM h z' x) := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk, actM_mk, actM_mk]
  congr 1
  ext
  simp [cjC, mul_assoc]

private theorem actM_one [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ)
    (x : ↥C ⧸ Lγ.subgroupOf C) :
    actM h 1 x = x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk]
  congr 1
  ext
  simp [cjC]

private theorem actM_eq [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) {z z' : Γ} (hz : φ z = φ z')
    (x : ↥C ⧸ Lγ.subgroupOf C) : actM h z x = actM h z' x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk, actM_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hw : φ (z⁻¹ * z') = 1 := by rw [map_mul, map_inv, hz, inv_mul_cancel]
  have h1 := h.ker (z⁻¹ * z') hw ((c : Γ)⁻¹) (inv_mem c.2)
  have h2 := h.ln z _ (inv_mem h1)
  convert h2 using 1
  simp only [cjC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
    commutatorElement_def]
  group

private noncomputable def Qmod.smul' (h : ModData φ C Lγ) (g : SpecialLinearGroup (Fin 2) K)
    (v : Qmod h) : Qmod h :=
  letI : (Lγ.subgroupOf C).Normal := h.normal
  Additive.ofMul (actM h (Classical.choose (h.surj g)) (Additive.toMul v))

private noncomputable instance (h : ModData φ C Lγ) :
    DistribMulAction (SpecialLinearGroup (Fin 2) K) (Qmod h) where
  smul := Qmod.smul' h
  one_smul v := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h (Classical.choose (h.surj 1)) (Additive.toMul v)) = v
    rw [actM_eq h (z' := 1) (by rw [Classical.choose_spec (h.surj 1), map_one]), actM_one]
    rfl
  mul_smul g₁ g₂ v := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h (Classical.choose (h.surj (g₁ * g₂))) (Additive.toMul v)) =
      Additive.ofMul (actM h (Classical.choose (h.surj g₁))
        (actM h (Classical.choose (h.surj g₂)) (Additive.toMul v)))
    rw [actM_eq h (z' := Classical.choose (h.surj g₁) * Classical.choose (h.surj g₂)) (by
      rw [map_mul, Classical.choose_spec (h.surj g₁), Classical.choose_spec (h.surj g₂),
        Classical.choose_spec (h.surj (g₁ * g₂))]), actM_mul]
  smul_zero g := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h _ (Additive.toMul (0 : Qmod h))) = 0
    rw [show Additive.toMul (0 : Qmod h) = 1 from rfl, map_one]
    rfl
  smul_add g v w := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h _ (Additive.toMul (v + w))) = _
    rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from rfl, map_mul]
    rfl

private theorem Qmod.smul_mk (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    φ z • Qmod.mk h c = Qmod.mk h (cjC h z c) := by
  letI : (Lγ.subgroupOf C).Normal := h.normal
  show Additive.ofMul (actM h (Classical.choose (h.surj (φ z))) (QuotientGroup.mk c)) = _
  rw [actM_eq h (z' := z) (Classical.choose_spec (h.surj (φ z))), actM_mk]
  rfl

private theorem Qmod.mk_inv (h : ModData φ C Lγ) (a : ↥C) : Qmod.mk h a⁻¹ = - Qmod.mk h a := by
  have := Qmod.mk_mul h a a⁻¹
  rw [mul_inv_cancel, Qmod.mk_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

private theorem Qmod.mk_cjC_eq_iff (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    Qmod.mk h (cjC h z c) = Qmod.mk h c ↔ ⁅z, (c : Γ)⁆ ∈ Lγ := by
  have e : ((cjC h z c * c⁻¹ : ↥C) : Γ) = ⁅z, (c : Γ)⁆ := by
    simp [cjC, commutatorElement_def]
  rw [← e, ← Qmod.mk_eq_zero_iff h, Qmod.mk_mul, Qmod.mk_inv, add_neg_eq_zero]

end Quotient

section GT1

variable {Γ : Type*} [Group Γ] [Finite Γ] {K : Type} [Field K] [Finite K] [CharP K 2]
  [PerfectRing K 2]

theorem gt1_abs
    (φ : Γ →* SpecialLinearGroup (Fin 2) K) (hφ : Function.Surjective φ)
    (C Lγ C₁ : Subgroup Γ) (hLC₁ : Lγ ≤ C₁) (hC₁C : C₁ ≤ C)
    (hCn : ∀ z : Γ, ∀ c ∈ C, z * c * z⁻¹ ∈ C) (hLn : ∀ z : Γ, ∀ l ∈ Lγ, z * l * z⁻¹ ∈ Lγ)
    (hcomm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ Lγ)
    (hker : ∀ z : Γ, φ z = 1 → ∀ c ∈ C, ⁅z, c⁆ ∈ Lγ)
    (hfix : ∀ c ∈ C, (∀ z : Γ, ⁅z, c⁆ ∈ Lγ) → c ∈ Lγ)
    (hquad : ∀ x x' : Γ, φ x ∈ upperUnipotent K → φ x' ∈ upperUnipotent K →
      ∀ c ∈ C, ⁅x', ⁅x, c⁆⁆ ∈ Lγ)
    (hL : ∀ c ∈ C₁, ∀ x : Γ, φ x ∈ upperUnipotent K → ⁅x, c⁆ ∈ Lγ)
    (hgen : ∀ S : Subgroup Γ, Lγ ≤ S → S ≤ C → (∀ z : Γ, ∀ s ∈ S, z * s * z⁻¹ ∈ S) →
      C₁ ≤ S → S = C)
    (z : Γ) (hz10 : (φ z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (p : ℕ[X])
    (hp : p.eval₂ (Nat.castRingHom K) ((φ z : Matrix (Fin 2) (Fin 2) K) 0 0) = 0)
    {c : Γ} (hc : c ∈ C₁) :
    (((List.range (p.natDegree + 1)).map fun i => (z ^ i * c * (z ^ i)⁻¹) ^ p.coeff i).prod) ∈
      Lγ := by
  classical
  have hd : ModData φ C Lγ := ⟨hφ, hLC₁.trans hC₁C, hCn, hLn, hcomm, hker⟩
  let Lt : AddSubgroup (Qmod hd) :=
    { carrier := {v | ∃ c : ↥C, (c : Γ) ∈ C₁ ∧ Qmod.mk hd c = v}
      zero_mem' := ⟨1, C₁.one_mem, Qmod.mk_one hd⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, C₁.mul_mem ha hb, Qmod.mk_mul hd a b⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, C₁.inv_mem ha, Qmod.mk_inv hd a⟩ }
  have hfix' : ∀ v : Qmod hd, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    rw [Qmod.mk_eq_zero_iff]
    refine hfix c c.2 (fun z => ?_)
    exact (Qmod.mk_cjC_eq_iff hd z c).mp (by rw [← Qmod.smul_mk]; exact hv (φ z))
  have hquad' : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : Qmod hd,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨x', rfl⟩ := hφ a'
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    have e : φ x • Qmod.mk hd c - Qmod.mk hd c = Qmod.mk hd (cjC hd x c * c⁻¹) := by
      rw [Qmod.smul_mk, Qmod.mk_mul, Qmod.mk_inv, sub_eq_add_neg]
    rw [e, Qmod.smul_mk]
    refine (Qmod.mk_cjC_eq_iff hd x' (cjC hd x c * c⁻¹)).mpr ?_
    have := hquad x x' ha ha' c c.2
    simpa [cjC, commutatorElement_def, mul_assoc] using this
  have hL' : ∀ w ∈ Lt, ∀ a ∈ upperUnipotent K, a • w = w := by
    rintro _ ⟨c, hc, rfl⟩ a ha
    obtain ⟨x, rfl⟩ := hφ a
    rw [Qmod.smul_mk]
    exact (Qmod.mk_cjC_eq_iff hd x c).mpr (hL c hc x ha)
  have hgen' : ∀ U : AddSubgroup (Qmod hd),
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → Lt ≤ U → U = ⊤ := by
    intro U hU hLU
    let S : Subgroup Γ :=
      { carrier := {z | ∃ hz : z ∈ C, Qmod.mk hd ⟨z, hz⟩ ∈ U}
        one_mem' := ⟨C.one_mem, by
          have e : (⟨1, C.one_mem⟩ : ↥C) = 1 := rfl
          rw [e, Qmod.mk_one hd]
          exact U.zero_mem⟩
        mul_mem' := by
          rintro a b ⟨ha, haU⟩ ⟨hb, hbU⟩
          exact ⟨C.mul_mem ha hb, by
            have := U.add_mem haU hbU
            rwa [← Qmod.mk_mul hd ⟨a, ha⟩ ⟨b, hb⟩] at this⟩
        inv_mem' := by
          rintro a ⟨ha, haU⟩
          exact ⟨C.inv_mem ha, by
            have := U.neg_mem haU
            rwa [← Qmod.mk_inv hd ⟨a, ha⟩] at this⟩ }
    have hS : S = C := by
      refine hgen S (fun l hl => ⟨hd.le hl, ?_⟩) (fun z hz => hz.1) (fun z s hs => ?_)
        (fun c hc => ⟨hC₁C hc, hLU ⟨⟨c, hC₁C hc⟩, hc, rfl⟩⟩)
      · have : Qmod.mk hd ⟨l, hd.le hl⟩ = 0 := (Qmod.mk_eq_zero_iff hd _).mpr hl
        rw [this]
        exact U.zero_mem
      · obtain ⟨hsC, hsU⟩ := hs
        refine ⟨hCn z s hsC, ?_⟩
        have := hU (φ z) _ hsU
        rwa [Qmod.smul_mk] at this
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    have hc : (c : Γ) ∈ S := by
      rw [hS]
      exact c.2
    obtain ⟨hcC, hcU⟩ := hc
    exact hcU
  have hcC : c ∈ C := hC₁C hc
  set v₀ : Qmod hd := Qmod.mk hd ⟨c, hcC⟩ with hv₀
  have hv : ∀ a ∈ upperUnipotent K, a • v₀ = v₀ := by
    intro a ha
    obtain ⟨x, rfl⟩ := hφ a
    rw [hv₀, Qmod.smul_mk]
    exact (Qmod.mk_cjC_eq_iff hd x ⟨c, hcC⟩).mpr (hL c hc x ha)
  have key := evalAct_eq_zero hfix' hquad' hL' hgen' (φ z) hz10 p hp v₀ hv
  let cj : ℕ → ↥C := fun i => cjC hd (z ^ i) ⟨c, hcC⟩
  have hcjmk : ∀ i, (φ z) ^ i • v₀ = Qmod.mk hd (cj i) := by
    intro i
    rw [← map_pow, hv₀, Qmod.smul_mk]
  have hmkpow : ∀ (a : ↥C) (k : ℕ), Qmod.mk hd (a ^ k) = k • Qmod.mk hd a := by
    intro a k
    induction k with
    | zero => simp [Qmod.mk_one]
    | succ k ih => rw [pow_succ, Qmod.mk_mul, ih, succ_nsmul]
  have hlist : ∀ n : ℕ, Qmod.mk hd (((List.range n).map fun i => cj i ^ p.coeff i).prod) =
      ∑ i ∈ Finset.range n, p.coeff i • Qmod.mk hd (cj i) := by
    intro n
    induction n with
    | zero => simp [Qmod.mk_one]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, Qmod.mk_mul, ih,
        Finset.sum_range_succ]
      simp [hmkpow]
  have hmk0 : Qmod.mk hd (((List.range (p.natDegree + 1)).map fun i => cj i ^ p.coeff i).prod) =
      0 := by
    rw [hlist]
    simpa [hcjmk] using key
  have hmem := (Qmod.mk_eq_zero_iff hd _).mp hmk0
  have hcoe : ((((List.range (p.natDegree + 1)).map fun i => cj i ^ p.coeff i).prod : ↥C) : Γ) =
      ((List.range (p.natDegree + 1)).map fun i => (z ^ i * c * (z ^ i)⁻¹) ^ p.coeff i).prod := by
    rw [show ((((List.range (p.natDegree + 1)).map fun i => cj i ^ p.coeff i).prod : ↥C) : Γ) =
      C.subtype (((List.range (p.natDegree + 1)).map fun i => cj i ^ p.coeff i).prod) from rfl,
      map_list_prod, List.map_map]
    congr 1
  rw [← hcoe]
  exact hmem

end GT1

end CFSG.RankThree.GF2n.Stroth80.FieldModel
