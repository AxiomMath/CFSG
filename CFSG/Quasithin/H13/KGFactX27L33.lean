module

public import CFSG.Quasithin.H13.KGFactX27Inv
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelCard
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelLevi
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OConjSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical

public section

namespace CFSG.Quasithin.H13.KGX27

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.NQCore CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Core

variable {X : Type*} [Group X]

@[expose] def coreIn (B G₀ : Subgroup X) : Subgroup X where
  carrier := {x | ∀ h ∈ G₀, h⁻¹ * x * h ∈ B}
  mul_mem' := by
    intro a b ha hb h hh
    have := B.mul_mem (ha h hh) (hb h hh)
    rwa [show h⁻¹ * a * h * (h⁻¹ * b * h) = h⁻¹ * (a * b) * h by group] at this
  one_mem' := fun h _ => by rw [mul_one, inv_mul_cancel]; exact B.one_mem
  inv_mem' := by
    intro a ha h hh
    have := B.inv_mem (ha h hh)
    rwa [show (h⁻¹ * a * h)⁻¹ = h⁻¹ * a⁻¹ * h by group] at this

theorem mem_coreIn {B G₀ : Subgroup X} {x : X} : x ∈ coreIn B G₀ ↔ ∀ h ∈ G₀, h⁻¹ * x * h ∈ B :=
  Iff.rfl

theorem coreIn_le (B G₀ : Subgroup X) : coreIn B G₀ ≤ B := fun x hx => by
  simpa using hx 1 G₀.one_mem

theorem le_coreIn {B G₀ R : Subgroup X} (hRB : R ≤ B) (hR : ∀ h ∈ G₀, ∀ r ∈ R, h⁻¹ * r * h ∈ R) :
    R ≤ coreIn B G₀ := fun r hr h hh => hRB (hR h hh r hr)

theorem map_coreIn_le (α : X ≃* X) {B G₀ : Subgroup X} (hB : B.map α.toMonoidHom = B)
    (hG : G₀.map α.toMonoidHom = G₀) : (coreIn B G₀).map α.toMonoidHom ≤ coreIn B G₀ := by
  rintro _ ⟨x, hx, rfl⟩ h hh
  have hh' : α.symm h ∈ G₀ := by
    rw [← hG] at hh
    obtain ⟨y, hy, rfl⟩ := hh
    simpa using hy
  have h1 : h⁻¹ * α x * h = α ((α.symm h)⁻¹ * x * α.symm h) := by simp
  change h⁻¹ * α x * h ∈ B
  rw [h1, ← hB]
  exact ⟨_, hx _ hh', rfl⟩

theorem map_coreIn (α : X ≃* X) {B G₀ : Subgroup X} (hB : B.map α.toMonoidHom = B)
    (hG : G₀.map α.toMonoidHom = G₀) : (coreIn B G₀).map α.toMonoidHom = coreIn B G₀ := by
  have hB' : B.map α.symm.toMonoidHom = B := by
    conv_lhs => rw [← hB]
    exact CFSG.Quasithin.F134.LieOdd.map_symm_map α B
  have hG' : G₀.map α.symm.toMonoidHom = G₀ := by
    conv_lhs => rw [← hG]
    exact CFSG.Quasithin.F134.LieOdd.map_symm_map α G₀
  refine le_antisymm (map_coreIn_le α hB hG) ?_
  have h := Subgroup.map_mono (f := α.toMonoidHom) (map_coreIn_le α.symm hB' hG')
  rwa [CFSG.Quasithin.F134.LieOdd.map_map_symm] at h

end Core

section Radical

variable {K : Type} [Field K] {n : ℕ}

theorem coe_mul_coe_inv (g : SpecialLinearGroup (Fin n) K) :
    (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

theorem coe_inv_mul_coe' (g : SpecialLinearGroup (Fin n) K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

@[expose] def radicalOf (W : Submodule K (Fin n → K)) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W) ∧
    ∀ v ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    have hgh : ((g * h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) := rfl
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [hgh, ← mulVec_mulVec]
      have := W.add_mem (hg1 ((h : Matrix (Fin n) (Fin n) K) *ᵥ v)) (hh1 v)
      rwa [sub_add_sub_cancel] at this
    · rw [hgh, ← mulVec_mulVec, hh2 v hv, hg2 v hv]
  one_mem' := by
    have h1 : ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := rfl
    refine ⟨fun v => ?_, fun v _ => ?_⟩
    · rw [h1, one_mulVec, sub_self]
      exact W.zero_mem
    · rw [h1, one_mulVec]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
      intro v
      rw [mulVec_mulVec, coe_mul_coe_inv, one_mulVec]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := W.neg_mem (hg1 (((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v))
      rwa [hinv v, neg_sub] at this
    · calc ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
          = ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hg2 v hv]
        _ = v := by rw [mulVec_mulVec, coe_inv_mul_coe', one_mulVec]

theorem mem_radicalOf {W : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ radicalOf W ↔ (∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W) ∧
      ∀ v ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  Iff.rfl

theorem conj_mem_radicalOf {W : Submodule K (Fin n → K)} {s r : SpecialLinearGroup (Fin n) K}
    (hs : s ∈ stabilizer W) (hr : r ∈ radicalOf W) : s * r * s⁻¹ ∈ radicalOf W := by
  have hmap : ∀ {t : SpecialLinearGroup (Fin n) K}, t ∈ stabilizer W → ∀ w ∈ W,
      (t : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro t ht w hw
    rw [← mem_stabilizer.1 ht]
    exact ⟨w, hw, rfl⟩
  have hs' := (stabilizer W).inv_mem hs
  obtain ⟨hr1, hr2⟩ := hr
  have hssi : ∀ v, (s : Matrix (Fin n) (Fin n) K) *ᵥ
      (((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, coe_mul_coe_inv, one_mulVec]
  have hcoe : ((s * r * s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (s : Matrix (Fin n) (Fin n) K) * (r : Matrix (Fin n) (Fin n) K) *
        ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have h := hmap hs _ (hr1 (((s⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v))
    rw [mulVec_sub, hssi, mulVec_mulVec] at h
    rwa [hcoe, ← mulVec_mulVec]
  · rw [hcoe, ← mulVec_mulVec, ← mulVec_mulVec, hr2 _ (hmap hs' v hv), hssi]

theorem radicalOf_flagSpace_le (i : ℕ) : radicalOf (flagSpace n K i) ≤ unitriangular n K := by
  classical
  rintro g ⟨hg1, hg2⟩
  have hcol : ∀ a b : Fin n, (g : Matrix (Fin n) (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1) a := by
    intro a b
    rw [mulVec_single]
    simp
  have key : ∀ a b : Fin n, i ≤ (a : ℕ) ∨ (b : ℕ) < i →
      (g : Matrix (Fin n) (Fin n) K) a b = if a = b then 1 else 0 := by
    intro a b hab
    by_cases hb : (b : ℕ) < i
    · have hmem : (Pi.single b (1 : K) : Fin n → K) ∈ flagSpace n K i := by
        rw [mem_flagSpace]
        intro j hj
        have : j ≠ b := by
          intro hjb
          rw [hjb] at hj
          omega
        simp [this]
      rw [hcol, hg2 _ hmem]
      by_cases hab' : a = b
      · subst hab'
        simp
      · simp [hab']
    · have ha : i ≤ (a : ℕ) := hab.resolve_right hb
      have h := mem_flagSpace.1 (hg1 (Pi.single b 1)) a ha
      rw [Pi.sub_apply, ← hcol, sub_eq_zero] at h
      rw [h]
      by_cases hab' : a = b
      · subst hab'
        simp
      · simp [hab']
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have hab : i ≤ (a : ℕ) ∨ (b : ℕ) < i := by
      have := Fin.lt_def.1 hba
      omega
    rw [key a b hab]
    simp [(ne_of_lt hba).symm]
  · have haa : i ≤ (a : ℕ) ∨ (a : ℕ) < i := by omega
    rw [key a a haa]
    simp

end Radical

section L33

@[expose] def radTwo {K : Type} [Field K] (a b : K) : SL(3, K) :=
  ⟨!![1, 0, a; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def radOne {K : Type} [Field K] (a b : K) : SL(3, K) :=
  ⟨!![1, a, b; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem radTwo_mem {K : Type} [Field K] (a b : K) : radTwo a b ∈ radicalOf (flagSpace 3 K 2) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp [radTwo, dotProduct, Fin.sum_univ_three]
  · have h2 := (mem_flagSpace.1 hv) 2 (by simp)
    ext j
    fin_cases j <;> simp [radTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]

theorem radOne_mem {K : Type} [Field K] (a b : K) : radOne a b ∈ radicalOf (flagSpace 3 K 1) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · simp at hj
    · simp [radOne, dotProduct, Fin.sum_univ_three]
    · simp [radOne, dotProduct, Fin.sum_univ_three]
  · have h1 := (mem_flagSpace.1 hv) 1 (by simp)
    have h2 := (mem_flagSpace.1 hv) 2 (by simp)
    ext j
    fin_cases j <;> simp [radOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem card_radicalOf_two {K : Type} [Field K] [Finite K] :
    Nat.card K ^ 2 ≤ Nat.card (radicalOf (flagSpace 3 K 2)) := by
  have hinj : Function.Injective fun ab : K × K =>
      (⟨radTwo ab.1 ab.2, radTwo_mem ab.1 ab.2⟩ : radicalOf (flagSpace 3 K 2)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := congrArg (fun g : radicalOf (flagSpace 3 K 2) =>
      ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2) h
    have h2 := congrArg (fun g : radicalOf (flagSpace 3 K 2) =>
      ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 2) h
    simp only [radTwo] at h1 h2
    simp at h1 h2
    rw [h1, h2]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, ← sq] at this

theorem card_radicalOf_one {K : Type} [Field K] [Finite K] :
    Nat.card K ^ 2 ≤ Nat.card (radicalOf (flagSpace 3 K 1)) := by
  have hinj : Function.Injective fun ab : K × K =>
      (⟨radOne ab.1 ab.2, radOne_mem ab.1 ab.2⟩ : radicalOf (flagSpace 3 K 1)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := congrArg (fun g : radicalOf (flagSpace 3 K 1) =>
      ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1) h
    have h2 := congrArg (fun g : radicalOf (flagSpace 3 K 1) =>
      ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp only [radOne] at h1 h2
    simp at h1 h2
    rw [h1, h2]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, ← sq] at this

theorem transvection_mem_unitriangular {K : Type} [Field K] {i j : Fin 3} (hij : i < j) (c : K) :
    SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ unitriangular 3 K := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe]
    simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply_ne (ne_of_lt hba).symm,
      zero_add]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      subst h1 h2
      exact absurd (hij.trans hba) (lt_irrefl _)
    · rfl
  · rw [SpecialLinearGroup.transvection_coe]
    simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply_eq]
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) (ne_of_lt hij)
    · rw [add_zero]

theorem transvection_notMem_unitriangular {K : Type} [Field K] {i j : Fin 3} (hij : j < i)
    {c : K} (hc : c ≠ 0) : SpecialLinearGroup.transvection (ne_of_lt hij).symm c ∉
      unitriangular 3 K := by
  intro h
  have h1 := h.1 i j hij
  rw [SpecialLinearGroup.transvection_coe] at h1
  simp [(ne_of_lt hij).symm] at h1
  exact hc h1

theorem reflection_one_moves {K : Type} [Field K] :
    ¬ ∀ x ∈ unitriangular 3 K, reflection 3 K 1 (by norm_num) (by norm_num) * x *
      (reflection 3 K 1 (by norm_num) (by norm_num))⁻¹ ∈ unitriangular 3 K := by
  intro h
  have h1 := h _ (transvection_mem_unitriangular (show (0 : Fin 3) < 1 by decide) (-1))
  rw [L3Odd.reflection_one_conj] at h1
  exact transvection_notMem_unitriangular (show (0 : Fin 3) < 1 by decide) one_ne_zero h1

theorem reflection_two_moves {K : Type} [Field K] :
    ¬ ∀ x ∈ unitriangular 3 K, reflection 3 K 2 (by norm_num) (by norm_num) * x *
      (reflection 3 K 2 (by norm_num) (by norm_num))⁻¹ ∈ unitriangular 3 K := by
  intro h
  have h1 := h _ (transvection_mem_unitriangular (show (1 : Fin 3) < 2 by decide) (-1))
  rw [L3Odd.reflection_two_conj] at h1
  exact transvection_notMem_unitriangular (show (1 : Fin 3) < 2 by decide) one_ne_zero h1

theorem x27Inv_S3 : X27Inv SL(3, ZMod 3) := by
  classical
  intro P U hP hexp hU hidx hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (ZMod 3) = 3 := by simp
  have hG : Nat.card SL(3, ZMod 3) = 5616 := by
    rw [L3Odd.card_SL_three, hK]
    norm_num
  have hU16 : Nat.card U = 16 := by
    have := CFSG.QuasithinUnique.A5.G3.card_eq_of_odd_index hU hidx
      (show Nat.card SL(3, ZMod 3) = 2 ^ 4 * 351 by rw [hG]; norm_num) (by decide)
    rw [this]
    norm_num
  have hU0 : Nat.card (unitriangular 3 (ZMod 3)) = 27 := by
    rw [card_unitriangular, hK]
    norm_num
  have hPp : IsPGroup 3 P := IsPGroup.of_card (show Nat.card P = 3 ^ 3 by rw [hP]; norm_num)
  have hU0p : IsPGroup 3 (unitriangular 3 (ZMod 3)) :=
    IsPGroup.of_card (show Nat.card (unitriangular 3 (ZMod 3)) = 3 ^ 3 by rw [hU0]; norm_num)
  have hidx3 : ∀ {Q : Subgroup SL(3, ZMod 3)}, Nat.card Q = 27 → ¬ 3 ∣ Q.index := by
    intro Q hQ h3
    have h := Q.card_mul_index
    rw [hQ, hG] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, ZMod 3) (hPp.toSylow (hidx3 hP))
    (hU0p.toSylow (hidx3 hU0))
  have hg' := congrArg (fun Q : Sylow 3 SL(3, ZMod 3) => (Q : Subgroup SL(3, ZMod 3))) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow, Subgroup.pointwise_smul_def] at hg'
  set φ : SL(3, ZMod 3) ≃* SL(3, ZMod 3) := MulAut.conj g with hφdef
  have hφP : P.map φ.toMonoidHom = unitriangular 3 (ZMod 3) := hg'
  apply exists_invariant_of_map' φ
  rw [hφP]
  set U₀ := unitriangular 3 (ZMod 3) with hU₀def
  set G₀ : Subgroup SL(3, ZMod 3) := U₀ ⊔ U.map φ.toMonoidHom with hG₀def
  have hG₀ : Nat.card G₀ = 432 := by
    rw [hG₀def, ← hφP, ← Subgroup.map_sup, Subgroup.card_map_of_injective φ.injective, hcard,
      hU16]
  have hUG : U₀ ≤ G₀ := le_sup_left
  refine ⟨coreIn U₀ G₀, coreIn_le U₀ G₀, ?_, fun α hαP hαU =>
    map_coreIn α hαP (by rw [hG₀def, Subgroup.map_sup, hαP, hαU])⟩
  have hcuts : G₀ ≤ flagStabilizer 3 (ZMod 3) (borelOvergroupCuts G₀) :=
    CFSG.QuasithinUnique.Setup.X7a.le_flagStabilizer_borelOvergroupCuts G₀ hUG
  have hupper : ∀ r ∈ G₀, (¬ ∀ x ∈ U₀, r * x * r⁻¹ ∈ U₀) → Nat.card (coreIn U₀ G₀) ≤ 9 := by
    intro r hr hmove
    have hle : coreIn U₀ G₀ ≤ U₀ := coreIn_le U₀ G₀
    have hne : Nat.card (coreIn U₀ G₀) ≠ 27 := by
      intro h27
      apply hmove
      intro x hx
      have heq : coreIn U₀ G₀ = U₀ := Subgroup.eq_of_le_of_card_ge hle (by rw [h27, hU0])
      rw [← heq] at hx
      have := hx r⁻¹ (G₀.inv_mem hr)
      rwa [inv_inv] at this
    have hdvd : Nat.card (coreIn U₀ G₀) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hU0]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases k <;> simp_all
  have hlower : ∀ i : ℕ, G₀ ≤ stabilizer (flagSpace 3 (ZMod 3) i) →
      9 ≤ Nat.card (radicalOf (flagSpace 3 (ZMod 3) i)) → 9 ≤ Nat.card (coreIn U₀ G₀) := by
    intro i hst h9
    have hRle : radicalOf (flagSpace 3 (ZMod 3) i) ≤ coreIn U₀ G₀ := by
      refine le_coreIn (radicalOf_flagSpace_le i) fun h hh r hr => ?_
      have := conj_mem_radicalOf ((stabilizer _).inv_mem (hst hh)) hr
      rwa [inv_inv] at this
    exact h9.trans (Subgroup.card_le_of_le hRle)
  have h9two : 9 ≤ Nat.card (radicalOf (flagSpace 3 (ZMod 3) 2)) := by
    have := card_radicalOf_two (K := ZMod 3)
    rwa [hK] at this
  have h9one : 9 ≤ Nat.card (radicalOf (flagSpace 3 (ZMod 3) 1)) := by
    have := card_radicalOf_one (K := ZMod 3)
    rwa [hK] at this
  by_cases h1 : reflection 3 (ZMod 3) 1 (by norm_num) (by norm_num) ∈ G₀ <;>
    by_cases h2 : reflection 3 (ZMod 3) 2 (by norm_num) (by norm_num) ∈ G₀
  ·
    exfalso
    have hempty : borelOvergroupCuts G₀ = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hi, hin, hnot⟩
      interval_cases i
      · exact hnot h1
      · exact hnot h2
    have htop :=
      CFSG.QuasithinUnique.Setup.X7a.eq_top_of_borelOvergroupCuts_eq_empty G₀ hUG hempty
    rw [htop, Subgroup.card_top, hG] at hG₀
    norm_num at hG₀
  ·
    have h2c : (2 : ℕ) ∈ borelOvergroupCuts G₀ := ⟨by norm_num, by norm_num, h2⟩
    have hst : G₀ ≤ stabilizer (flagSpace 3 (ZMod 3) 2) := fun x hx =>
      mem_flagStabilizer.1 (hcuts hx) 2 h2c
    have := hlower 2 hst h9two
    have := hupper _ h1 reflection_one_moves
    omega
  ·
    have h1c : (1 : ℕ) ∈ borelOvergroupCuts G₀ := ⟨le_rfl, by norm_num, h1⟩
    have hst : G₀ ≤ stabilizer (flagSpace 3 (ZMod 3) 1) := fun x hx =>
      mem_flagStabilizer.1 (hcuts hx) 1 h1c
    have := hlower 1 hst h9one
    have := hupper _ h2 reflection_two_moves
    omega
  ·
    exfalso
    have h1c : (1 : ℕ) ∈ borelOvergroupCuts G₀ := ⟨le_rfl, by norm_num, h1⟩
    have h2c : (2 : ℕ) ∈ borelOvergroupCuts G₀ := ⟨by norm_num, by norm_num, h2⟩
    have hB : G₀ ≤ upperTriangular 3 (ZMod 3) := fun x hx =>
      CFSG.LieType.SteinbergBR.mem_upperTriangular_of_map_flagSpace
        (mem_stabilizer.1 (mem_flagStabilizer.1 (hcuts hx) 1 h1c))
        (mem_stabilizer.1 (mem_flagStabilizer.1 (hcuts hx) 2 h2c))
    have h := (Subgroup.card_dvd_of_le hB).trans (L3Odd.card_upperTriangular_dvd (K := ZMod 3))
    rw [hG₀, hK] at h
    norm_num at h

end L33

theorem x27Psl3Three :
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 3 1 := by
  refine noX27ConfigQ_of_noCover
    (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h)
    (noX27Simple_of_x27Inv fun X _ hX => ?_) fun X _ _ hX h3 hmod => ?_
  · obtain ⟨e⟩ := CFSG.QuasithinUnique.Unc25K1.psl33_equiv hX
    exact X27Inv.of_mulEquiv (e.trans CFSG.QuasithinUnique.Unc25K1.psl33EquivS3) x27Inv_S3
  · have : Group.IsPerfect X := hX.1
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmod
    have hF' : Nat.card F = 3 := by rw [hF, pow_one]
    obtain ⟨h3F, -⟩ := CFSG.QuasithinUnique.Ch1.triple_cover_linear (p := 3) (f := 1) h3 hF e
      fun E _ _ π hπ hC hodd => by
        obtain ⟨⟨s, hs, -⟩, -⟩ :=
          CFSG.SectionRank.OddCover.prime_classical_three_central_odd_extension_splitting
            Nat.prime_three (by norm_num) (Or.inl ⟨rfl, hF', rfl⟩) π hπ hC hodd
        exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    rw [hF'] at h3F
    norm_num at h3F

end CFSG.Quasithin.H13.KGX27
