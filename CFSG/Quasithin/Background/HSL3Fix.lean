module

public import CFSG.Quasithin.Background.HSL3One

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank SL3Pair
open scoped Matrix

theorem eq_of_card_four {α : Type*} [Finite α] (hα : Nat.card α = 4) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : α) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  by_contra h
  push Not at h
  obtain ⟨hxa, hxb, hxc, hxd⟩ := h
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have hdc := hcd.symm
  have hax := hxa.symm
  have hbx := hxb.symm
  have hcx := hxc.symm
  have hdx := hxd.symm
  have hinj : Function.Injective (![a, b, c, d, x] : Fin 5 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have := Nat.card_le_card_of_injective _ hinj
  rw [hα, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

section Defs

variable {K : Type} [Field K]

abbrev zvec (c : Fin 3 → K) : PairMod K := (Multiplicative.ofAdd c, Multiplicative.ofAdd 0)

@[expose] def wSub (c : Fin 3 → K) : Subgroup (PairMod K) where
  carrier := {x | c ⬝ᵥ Multiplicative.toAdd x.2 = 0}
  mul_mem' := fun {a b} ha hb => by
    have ha' : c ⬝ᵥ Multiplicative.toAdd a.2 = 0 := ha
    have hb' : c ⬝ᵥ Multiplicative.toAdd b.2 = 0 := hb
    change c ⬝ᵥ Multiplicative.toAdd (a.2 * b.2) = 0
    rw [toAdd_mul, dotProduct_add, ha', hb', add_zero]
  one_mem' := by
    change c ⬝ᵥ Multiplicative.toAdd (1 : StdMod (Fin 3) K) = 0
    rw [toAdd_one, dotProduct_zero]
  inv_mem' := fun {a} ha => by
    have ha' : c ⬝ᵥ Multiplicative.toAdd a.2 = 0 := ha
    change c ⬝ᵥ Multiplicative.toAdd (a.2)⁻¹ = 0
    rw [toAdd_inv, dotProduct_neg, ha', neg_zero]

theorem mem_wSub {c : Fin 3 → K} {x : PairMod K} :
    x ∈ wSub c ↔ c ⬝ᵥ Multiplicative.toAdd x.2 = 0 := Iff.rfl

@[expose] def ySub (c : Fin 3 → K) : Subgroup (PairMod K) := wSub c ⊓ V₂ K

theorem mem_ySub {c : Fin 3 → K} {x : PairMod K} :
    x ∈ ySub c ↔ c ⬝ᵥ Multiplicative.toAdd x.2 = 0 ∧ x.1 = 1 := by
  rw [ySub, Subgroup.mem_inf, mem_wSub, mem_V₂]

theorem wSub_le_sup (c : Fin 3 → K) : wSub c ≤ V₁ K ⊔ ySub c := by
  intro x hx
  refine Subgroup.mem_sup.mpr ⟨(x.1, 1), mem_V₁.mpr rfl, (1, x.2), mem_ySub.mpr ⟨hx, rfl⟩, ?_⟩
  simp

theorem zvec_mem_V₁ (c : Fin 3 → K) : zvec c ∈ V₁ K := mem_V₁.mpr rfl

theorem zvec_ne_one {c : Fin 3 → K} (hc : c ≠ 0) : zvec c ≠ 1 := fun h =>
  hc (by simpa [zvec] using congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) h)

end Defs

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_card (hK : Nat.card K = 2) (κ : K) : κ = 0 ∨ κ = 1 := by
  by_contra hc
  push Not at hc
  have hinj : Function.Injective (![0, 1, κ] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm, zero_ne_one]
  have := Nat.card_le_card_of_injective _ hinj
  rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem exists_dot_eq_one (hK : Nat.card K = 2) {f : Fin 3 → K} (hf : f ≠ 0) :
    ∃ u : Fin 3 → K, f ⬝ᵥ u = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  refine ⟨Pi.single i 1, ?_⟩
  rw [dotProduct_single, mul_one]
  exact (eq_zero_or_eq_one_of_card hK (f i)).resolve_left hi


variable [CharP K 2]

theorem trv_mul_self {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) :
    (1 + Matrix.vecMulVec u ψ) * (1 + Matrix.vecMulVec u ψ) = (1 : Matrix (Fin 3) (Fin 3) K) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  have key : ψ ⬝ᵥ (v + (ψ ⬝ᵥ v) • u) = ψ ⬝ᵥ v := by
    rw [dotProduct_add, dotProduct_smul, h, smul_zero, add_zero]
  rw [← Matrix.mulVec_mulVec, one_add_vecMulVec_mulVec, one_add_vecMulVec_mulVec, key,
    Matrix.one_mulVec, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def trvGL {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) : GL (Fin 3) K :=
  ⟨1 + Matrix.vecMulVec u ψ, 1 + Matrix.vecMulVec u ψ, trv_mul_self h, trv_mul_self h⟩

theorem coe_trvGL {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) :
    ((trvGL h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec u ψ := rfl

theorem coe_trvGL_inv {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) :
    (((trvGL h)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec u ψ := rfl

theorem trvGL_mem {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) : trvGL h ∈ StatedSL 3 K := by
  rw [mem_statedSL_iff]
  apply eq_one_of_mul_self_eq_one
  rw [← Matrix.det_mul, coe_trvGL, trv_mul_self h, Matrix.det_one]

theorem coe_dualGL_trvGL {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) :
    ((dualGL (trvGL h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec ψ u := by
  rw [coe_dualGL, coe_trvGL_inv, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

theorem pairHom_trvGL_apply {u ψ : Fin 3 → K} (h : ψ ⬝ᵥ u = 0) (x : PairMod K) :
    pairHom (trvGL h) x = (Multiplicative.ofAdd (Multiplicative.toAdd x.1 +
        (ψ ⬝ᵥ Multiplicative.toAdd x.1) • u),
      Multiplicative.ofAdd (Multiplicative.toAdd x.2 + (u ⬝ᵥ Multiplicative.toAdd x.2) • ψ)) := by
  rw [pairHom_apply, pairAut_apply]
  refine Prod.ext ?_ ?_
  · change Multiplicative.ofAdd
      (((trvGL h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.1) = _
    rw [coe_trvGL, one_add_vecMulVec_mulVec]
  · change Multiplicative.ofAdd (((dualGL (trvGL h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.2) = _
    rw [coe_dualGL_trvGL, one_add_vecMulVec_mulVec]

theorem ofAdd_pair_mul_inv (v f v' f' : Fin 3 → K) :
    ((Multiplicative.ofAdd v, Multiplicative.ofAdd f) : PairMod K) *
        (Multiplicative.ofAdd v', Multiplicative.ofAdd f')⁻¹ =
      (Multiplicative.ofAdd (v - v'), Multiplicative.ofAdd (f - f')) := by
  refine Prod.ext ?_ ?_ <;> apply Multiplicative.toAdd.injective <;>
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, toAdd_mul, toAdd_inv,
      toAdd_ofAdd] <;> abel

@[expose] def IsCenterType (E : Subgroup (MulAut (PairMod K))) (c : Fin 3 → K) : Prop :=
  ∀ x ∈ E, ∃ φ : Fin 3 → K, ∃ hφ : φ ⬝ᵥ c = 0, x = pairHom (trvGL hφ)

theorem trv_fix_zvec {c φ : Fin 3 → K} (hφ : φ ⬝ᵥ c = 0) :
    pairHom (trvGL hφ) (zvec c) = zvec c := by
  rw [pairHom_trvGL_apply]
  refine Prod.ext ?_ ?_ <;> simp [zvec, hφ]

theorem fixV_le_wSub {E : Subgroup (MulAut (PairMod K))} {c : Fin 3 → K}
    (hE : IsCenterType E c) {X : Subgroup (MulAut (PairMod K))} (hXE : X ≤ E) (hX : X ≠ ⊥) :
    fixV X ≤ wSub c := by
  obtain ⟨x, hxX, hx1⟩ := (Subgroup.bot_or_exists_ne_one X).resolve_left hX
  obtain ⟨φ, hφ, hxe⟩ := hE x (hXE hxX)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hx1
    rw [hxe]
    have : trvGL hφ = 1 :=
      Units.ext (by rw [coe_trvGL, Matrix.vecMulVec_zero, add_zero, Units.val_one])
    rw [this, map_one]
  intro w hw
  have h := (mem_fixV.mp hw) x hxX
  rw [hxe, pairHom_trvGL_apply] at h
  have h2 := congrArg (fun y : PairMod K => Multiplicative.toAdd y.2) h
  simp only [toAdd_ofAdd, add_eq_left, smul_eq_zero] at h2
  rw [mem_wSub]
  exact h2.resolve_right hφ0

theorem comm_wSub (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))} {c : Fin 3 → K}
    (hE : IsCenterType E c) {x : MulAut (PairMod K)} (hx : x ∈ E) {w : PairMod K}
    (hw : w ∈ wSub c) : x w * w⁻¹ = 1 ∨ x w * w⁻¹ = zvec c := by
  obtain ⟨φ, hφ, rfl⟩ := hE x hx
  rw [mem_wSub] at hw
  rw [pairHom_trvGL_apply, hw, zero_smul, add_zero]
  rcases eq_zero_or_eq_one_of_card hK (φ ⬝ᵥ Multiplicative.toAdd w.1) with h0 | h1
  · left
    rw [h0, zero_smul, add_zero]
    refine Prod.ext ?_ ?_ <;> apply Multiplicative.toAdd.injective <;>
      simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, toAdd_mul, toAdd_inv,
        toAdd_ofAdd, Prod.fst_one, Prod.snd_one, toAdd_one] <;> abel
  · right
    rw [h1, one_smul]
    refine Prod.ext ?_ ?_ <;> apply Multiplicative.toAdd.injective <;>
      simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, toAdd_mul, toAdd_inv,
        toAdd_ofAdd, zvec] <;> abel

theorem cross_dot_self (c u : Fin 3 → K) : (c ⨯₃ u) ⬝ᵥ u = 0 := by
  rw [dotProduct_comm]
  exact dot_cross_self c u

theorem cross_dot_left (c u : Fin 3 → K) : (c ⨯₃ u) ⬝ᵥ c = 0 := by
  rw [dotProduct_comm]
  exact dot_self_cross c u

theorem trv_cross_fix (c u : Fin 3 → K) :
    pairHom (trvGL (cross_dot_self c u)) (zvec c) = zvec c := by
  rw [pairHom_trvGL_apply]
  refine Prod.ext ?_ ?_ <;> simp [zvec, cross_dot_left]

theorem eq_V₁_of_inv (hK : Nat.card K = 2) {c : Fin 3 → K} (hc : c ≠ 0)
    {J : Subgroup (PairMod K)} (hJ : J ≤ V₁ K) (hzJ : zvec c ∈ J)
    (hJz : ¬ J ≤ Subgroup.zpowers (zvec c))
    (hinv : ∀ γ ∈ StatedSL 3 K, pairHom γ (zvec c) = zvec c → ∀ x ∈ J, pairHom γ x ∈ J) :
    J = V₁ K := by
  obtain ⟨x, hxJ, hxz⟩ : ∃ x ∈ J, x ∉ Subgroup.zpowers (zvec c) := by
    by_contra h
    push Not at h
    exact hJz h
  have hx2 : x.2 = 1 := mem_V₁.mp (hJ hxJ)
  obtain ⟨v, hxe⟩ : ∃ v : Fin 3 → K,
      x = (Multiplicative.ofAdd v, Multiplicative.ofAdd 0) :=
    ⟨Multiplicative.toAdd x.1, Prod.ext rfl hx2⟩
  subst hxe
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hxz (Subgroup.one_mem _)
  have hvc : v ≠ c := by
    rintro rfl
    exact hxz (Subgroup.mem_zpowers _)
  have hlin : LinearIndependent K ![c, v] := by
    rw [LinearIndependent.pair_iff' hc]
    intro a ha
    rcases eq_zero_or_eq_one_of_card hK a with h | h
    · rw [h, zero_smul] at ha
      exact hv0 ha.symm
    · rw [h, one_smul] at ha
      exact hvc ha.symm
  have hf0 : c ⨯₃ v ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hlin
  have hJ1 : ∀ u : Fin 3 → K, (c ⨯₃ v) ⬝ᵥ u = 1 →
      ((Multiplicative.ofAdd u, Multiplicative.ofAdd 0) : PairMod K) ∈ J := by
    intro u hu
    have hψv : (c ⨯₃ u) ⬝ᵥ v = 1 := by
      have e1 : (c ⨯₃ u) ⬝ᵥ v = -((c ⨯₃ v) ⬝ᵥ u) := by
        rw [dotProduct_comm, triple_product_permutation, ← cross_anticomm, dotProduct_neg,
          dotProduct_comm (c ⨯₃ v), triple_product_permutation u c v]
      rw [e1, hu, CharTwo.neg_eq]
    have h1 := hinv _ (trvGL_mem (cross_dot_self c u)) (trv_cross_fix c u) _ hxJ
    rw [pairHom_trvGL_apply] at h1
    simp only [toAdd_ofAdd, hψv, one_smul, dotProduct_zero, zero_smul, add_zero] at h1
    have h2 := J.mul_mem h1 (J.inv_mem hxJ)
    rw [ofAdd_pair_mul_inv, add_sub_cancel_left, sub_self] at h2
    exact h2
  obtain ⟨u₀, hu₀⟩ := exists_dot_eq_one hK hf0
  apply le_antisymm hJ
  intro y hy
  have hy2 : y.2 = 1 := mem_V₁.mp hy
  obtain ⟨w, hye⟩ : ∃ w : Fin 3 → K,
      y = (Multiplicative.ofAdd w, Multiplicative.ofAdd 0) :=
    ⟨Multiplicative.toAdd y.1, Prod.ext rfl hy2⟩
  subst hye
  rcases eq_zero_or_eq_one_of_card hK ((c ⨯₃ v) ⬝ᵥ w) with h0 | h1
  · have h3 := hJ1 (u₀ + w) (by rw [dotProduct_add, hu₀, h0, add_zero])
    have h4 := J.mul_mem h3 (J.inv_mem (hJ1 u₀ hu₀))
    rw [ofAdd_pair_mul_inv, add_sub_cancel_left, sub_self] at h4
    exact h4
  · exact hJ1 w h1

theorem eq_ySub_of_inv (hK : Nat.card K = 2) {c : Fin 3 → K} (hc : c ≠ 0)
    {J : Subgroup (PairMod K)} (hJ : J ≤ ySub c) (hJ0 : J ≠ ⊥)
    (hinv : ∀ γ ∈ StatedSL 3 K, pairHom γ (zvec c) = zvec c → ∀ x ∈ J, pairHom γ x ∈ J) :
    J = ySub c := by
  obtain ⟨x, hxJ, hx1⟩ := (Subgroup.bot_or_exists_ne_one J).resolve_left hJ0
  obtain ⟨hxc, hx1'⟩ := mem_ySub.mp (hJ hxJ)
  obtain ⟨f, hxe⟩ : ∃ f : Fin 3 → K,
      x = (Multiplicative.ofAdd 0, Multiplicative.ofAdd f) :=
    ⟨Multiplicative.toAdd x.2, Prod.ext hx1' rfl⟩
  subst hxe
  simp only [toAdd_ofAdd] at hxc
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hx1 rfl
  obtain ⟨u, hu⟩ := exists_dot_eq_one hK hf0
  have hu' : u ⬝ᵥ f = 1 := by
    rw [dotProduct_comm]
    exact hu
  have hgJ : ((Multiplicative.ofAdd 0, Multiplicative.ofAdd (c ⨯₃ u)) : PairMod K) ∈ J := by
    have h1 := hinv _ (trvGL_mem (cross_dot_self c u)) (trv_cross_fix c u) _ hxJ
    rw [pairHom_trvGL_apply] at h1
    simp only [toAdd_ofAdd, dotProduct_zero, zero_smul, add_zero, hu', one_smul] at h1
    have h2 := J.mul_mem h1 (J.inv_mem hxJ)
    rw [ofAdd_pair_mul_inv, sub_self, add_sub_cancel_left] at h2
    exact h2
  have hlin : LinearIndependent K ![c, u] := by
    rw [LinearIndependent.pair_iff' hc]
    intro a ha
    have h3 : u ⬝ᵥ f = a * (c ⬝ᵥ f) := by rw [← ha, smul_dotProduct, smul_eq_mul]
    rw [hu', hxc, mul_zero] at h3
    exact one_ne_zero h3
  have hg0 : c ⨯₃ u ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hlin
  have hgf : c ⨯₃ u ≠ f := by
    intro h
    have h3 := cross_dot_self c u
    rw [h, dotProduct_comm, hu'] at h3
    exact one_ne_zero h3
  have hneg : ∀ a : Fin 3 → K, -a = a := fun a => funext fun i => CharTwo.neg_eq (a i)
  have hfg0 : f + c ⨯₃ u ≠ 0 := by
    intro h
    apply hgf
    rw [add_eq_zero_iff_eq_neg, hneg] at h
    exact h.symm
  have hfgf : f + c ⨯₃ u ≠ f := fun h => hg0 (by simpa using h)
  have hfgg : f + c ⨯₃ u ≠ c ⨯₃ u := fun h => hf0 (by simpa using h)
  have hfgJ : ((Multiplicative.ofAdd 0, Multiplicative.ofAdd (f + c ⨯₃ u)) : PairMod K) ∈ J := by
    have h2 := J.mul_mem hgJ (J.inv_mem hxJ)
    rw [ofAdd_pair_mul_inv, sub_self, sub_eq_add_neg, hneg, add_comm] at h2
    exact h2
  have hcard : Nat.card {k : Fin 3 → K // c ⬝ᵥ k = 0} = 4 := by
    rw [card_orth hc, hK]
    norm_num
  have hgc : c ⬝ᵥ (c ⨯₃ u) = 0 := dot_self_cross c u
  have hfgc : c ⬝ᵥ (f + c ⨯₃ u) = 0 := by rw [dotProduct_add, hxc, hgc, add_zero]
  apply le_antisymm hJ
  intro y hy
  obtain ⟨hyc, hy1⟩ := mem_ySub.mp hy
  obtain ⟨k, hye⟩ : ∃ k : Fin 3 → K,
      y = (Multiplicative.ofAdd 0, Multiplicative.ofAdd k) :=
    ⟨Multiplicative.toAdd y.2, Prod.ext hy1 rfl⟩
  subst hye
  simp only [toAdd_ofAdd] at hyc
  have hval : ∀ {a b : Fin 3 → K} {ha : c ⬝ᵥ a = 0} {hb : c ⬝ᵥ b = 0}, a ≠ b →
      (⟨a, ha⟩ : {k : Fin 3 → K // c ⬝ᵥ k = 0}) ≠ ⟨b, hb⟩ := fun hab h =>
    hab (congrArg Subtype.val h)
  rcases eq_of_card_four hcard (a := ⟨0, dotProduct_zero c⟩) (b := ⟨f, hxc⟩)
      (c := ⟨c ⨯₃ u, hgc⟩) (d := ⟨f + c ⨯₃ u, hfgc⟩) (hval hf0.symm) (hval hg0.symm)
      (hval hfg0.symm) (hval hgf.symm) (hval hfgf.symm) (hval hfgg.symm) ⟨k, hyc⟩ with
    h | h | h | h <;> obtain rfl := Subtype.mk.inj h
  · exact J.one_mem
  · exact hxJ
  · exact hgJ
  · exact hfgJ

theorem mem_pairSL_of_fix (hK : Nat.card K = 2) {c : Fin 3 → K} (hc : c ≠ 0)
    {p : MulAut (PairMod K)} (hpN : p ∈ pairNorm K) (hpz : p (zvec c) = zvec c) :
    p ∈ pairSL K ∧ (∀ x ∈ V₁ K, p x ∈ V₁ K) ∧ ∀ x ∈ ySub c, p x ∈ ySub c := by
  have hpS : p ∈ pairSub K := by
    rcases mem_pairSub_or hpN with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := mem_pairSub_iff.mp h
      have hp : p = swapAut K * pairAut a b := by
        rw [← hab, ← mul_assoc, swapAut_mul_self, one_mul]
      have h1 := hpz
      rw [hp, MulAut.mul_apply, pairAut_apply, swapAut_apply] at h1
      have h2 := congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) h1
      simp only [zvec, ofAdd_zero, map_one, toAdd_one, toAdd_ofAdd] at h2
      exact hc h2.symm
  have hpSL := mem_pairSL_of_mem_pairSub hK hpN hpS
  obtain ⟨γ, hγ, rfl⟩ := hpSL
  have hγc : (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ c = c :=
    congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) hpz
  have hγinv : ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ c = c := by
    conv_lhs => rw [← hγc]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨⟨γ, hγ, rfl⟩, fun x hx => isInv_V₁ _ ⟨γ, hγ, rfl⟩ x hx, fun x hx => ?_⟩
  obtain ⟨hxc, hx1⟩ := mem_ySub.mp hx
  rw [mem_ySub]
  constructor
  · change c ⬝ᵥ (((dualGL γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Multiplicative.toAdd x.2) = 0
    rw [coe_dualGL, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hγinv, hxc]
  · change matAut γ x.1 = 1
    rw [hx1, map_one]

theorem isoMod_of_inf_eq_bot {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    {V₁ V₂ : Subgroup V} (hinf : V₁ ⊓ V₂ = ⊥) (hsup : V₁ ⊔ V₂ = ⊤) (h₁ : Pair.IsInv L V₁)
    (h₂ : Pair.IsInv L V₂) (hI₁ : Pair.IsIrr L V₁) (hI₂ : Pair.IsIrr L V₂) {W : Subgroup V}
    (hW : Pair.IsInv L W) (hW0 : W ≠ ⊥) (h1 : W ⊓ V₁ = ⊥) (h2 : W ⊓ V₂ = ⊥) :
    Pair.IsoMod L V₁ V₂ := by
  have hinf' : V₂ ⊓ V₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hsup' : V₂ ⊔ V₁ = ⊤ := by rw [sup_comm]; exact hsup
  obtain ⟨e₁, he₁⟩ := Pair.exists_iso_of_proj hinf hsup h₁ h₂ hI₁ hW hW0 h2
  obtain ⟨e₂, he₂⟩ := Pair.exists_iso_of_proj hinf' hsup' h₂ h₁ hI₂ hW hW0 h1
  refine ⟨e₁.symm.trans e₂, fun l hl v hv => ?_⟩
  set w := e₁.symm v with hw
  have hlw : l w ∈ W := hW l hl w w.2
  have h3 : e₁.symm ⟨l v, hv⟩ = ⟨l w, hlw⟩ := by
    apply e₁.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [he₁]
    change (l v : V) = Pair.proj hinf hsup (l (w : V))
    rw [Pair.proj_equivariant hinf hsup h₁ h₂ hl, ← he₁, hw, MulEquiv.apply_symm_apply]
  simp only [MulEquiv.trans_apply, h3]
  rw [he₂, he₂]
  exact Pair.proj_equivariant hinf' hsup' h₂ h₁ hl _

theorem isInv_eq {J : Subgroup (PairMod K)} (hJ : Pair.IsInv (pairSL K) J) :
    J = ⊥ ∨ J = V₁ K ∨ J = V₂ K ∨ J = ⊤ := by
  have hinv1 : Pair.IsInv (pairSL K) (J ⊓ V₁ K) := fun l hl w hw =>
    ⟨hJ l hl w hw.1, isInv_V₁ l hl w hw.2⟩
  have hinv2 : Pair.IsInv (pairSL K) (J ⊓ V₂ K) := fun l hl w hw =>
    ⟨hJ l hl w hw.1, isInv_V₂ l hl w hw.2⟩
  have hsub1 : J ⊓ V₁ K = V₁ K → V₁ K ≤ J := fun h => h ▸ inf_le_left
  have hsub2 : J ⊓ V₂ K = V₂ K → V₂ K ≤ J := fun h => h ▸ inf_le_left
  rcases isIrr_V₁.2 _ inf_le_right hinv1 with h1 | h1 <;>
    rcases isIrr_V₂.2 _ inf_le_right hinv2 with h2 | h2
  ·
    by_contra hne
    exact not_isoMod (K := K) (isoMod_of_inf_eq_bot V₁_inf_V₂ V₁_sup_V₂ isInv_V₁ isInv_V₂
      isIrr_V₁ isIrr_V₂ hJ (fun h => hne (Or.inl h)) h1 h2)
  ·
    right; right; left
    refine le_antisymm (fun x hx => ?_) (hsub2 h2)
    have hx2 : ((1, x.2) : PairMod K) ∈ J := hsub2 h2 (mem_V₂.mpr rfl)
    have hx1 : ((x.1, 1) : PairMod K) ∈ J ⊓ V₁ K := by
      refine ⟨?_, mem_V₁.mpr rfl⟩
      have h := J.mul_mem hx (J.inv_mem hx2)
      have heq : x * ((1, x.2) : PairMod K)⁻¹ = (x.1, 1) := Prod.ext (by simp) (by simp)
      rwa [heq] at h
    rw [h1, Subgroup.mem_bot] at hx1
    rw [mem_V₂]
    exact congrArg Prod.fst hx1
  ·
    right; left
    refine le_antisymm (fun x hx => ?_) (hsub1 h1)
    have hx1 : ((x.1, 1) : PairMod K) ∈ J := hsub1 h1 (mem_V₁.mpr rfl)
    have hx2 : ((1, x.2) : PairMod K) ∈ J ⊓ V₂ K := by
      refine ⟨?_, mem_V₂.mpr rfl⟩
      have h := J.mul_mem (J.inv_mem hx1) hx
      have heq : ((x.1, 1) : PairMod K)⁻¹ * x = (1, x.2) := Prod.ext (by simp) (by simp)
      rwa [heq] at h
    rw [h2, Subgroup.mem_bot] at hx2
    rw [mem_V₁]
    exact congrArg Prod.snd hx2
  ·
    right; right; right
    rw [eq_top_iff, ← V₁_sup_V₂]
    exact sup_le (hsub1 h1) (hsub2 h2)

end SL3One

end H

end CFSG.Quasithin
