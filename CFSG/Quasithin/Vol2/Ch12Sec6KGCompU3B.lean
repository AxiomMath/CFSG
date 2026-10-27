module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3A
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

@[expose] noncomputable def hypHf (x y : HypIndex 1 1 → K) : K :=
  hrow h.bar (hypGram 1 1 K) x ⬝ᵥ y

theorem hypGram_herm : ((hypGram 1 1 K).map h.bar)ᵀ = hypGram 1 1 K := by
  rw [hypGram_map, hypGram_transpose]

theorem bar_hypHf (x y : HypIndex 1 1 → K) : h.bar (hypHf h x y) = hypHf h y x := by
  have hx : (h.bar ∘ fun i => h.bar (x i)) = x := funext fun i => h.bar_bar (x i)
  have h1 : (h.bar ∘ ((fun i => h.bar (x i)) ᵥ* hypGram 1 1 K)) = x ᵥ* hypGram 1 1 K := by
    funext i
    rw [Function.comp_apply, RingHom.map_vecMul, hx, hypGram_map]
  simp only [hypHf, hrow]
  rw [RingHom.map_dotProduct, h1, ← dotProduct_mulVec, dotProduct_comm, ← vecMul_transpose,
    hypGram_transpose]
  rfl

theorem hypHf_add_right (x y z : HypIndex 1 1 → K) :
    hypHf h x (y + z) = hypHf h x y + hypHf h x z := dotProduct_add _ _ _

theorem hypHf_smul_right (x y : HypIndex 1 1 → K) (c : K) :
    hypHf h x (c • y) = c * hypHf h x y := dotProduct_smul _ _ _

theorem hypHf_add_left (x y z : HypIndex 1 1 → K) :
    hypHf h (x + y) z = hypHf h x z + hypHf h y z := by
  have : (fun i => h.bar ((x + y) i)) = (fun i => h.bar (x i)) + fun i => h.bar (y i) := by
    funext i
    simp
  simp only [hypHf, hrow]
  rw [this, add_vecMul, add_dotProduct]

theorem hypHf_smul_left (x y : HypIndex 1 1 → K) (c : K) :
    hypHf h (c • x) y = h.bar c * hypHf h x y := by
  rw [hypHf, hrow_smul, smul_dotProduct, smul_eq_mul]
  rfl

theorem hypHf_sub_right (x y z : HypIndex 1 1 → K) :
    hypHf h x (y - z) = hypHf h x y - hypHf h x z := dotProduct_sub _ _ _

theorem bar_hypHf_self (x : HypIndex 1 1 → K) : h.bar (hypHf h x x) = hypHf h x x :=
  bar_hypHf h x x

theorem exists_isotropic {S : Submodule K (HypIndex 1 1 → K)}
    {w₁ w₂ : HypIndex 1 1 → K} (hw₁ : w₁ ∈ S) (hw₂ : w₂ ∈ S)
    (hli : ∀ a b : K, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0) :
    ∃ e ∈ S, e ≠ 0 ∧ hypHf h e e = 0 := by
  have hw₁0 : w₁ ≠ 0 := fun h0 => by
    have := (hli 1 0 (by rw [h0, smul_zero, zero_smul, add_zero])).1
    exact one_ne_zero this
  by_cases ha : hypHf h w₁ w₁ = 0
  · exact ⟨w₁, hw₁, hw₁0, ha⟩
  set c := hypHf h w₁ w₂ / hypHf h w₁ w₁ with hc
  set w₂' := w₂ - c • w₁ with hw₂'
  have hw₂'S : w₂' ∈ S := S.sub_mem hw₂ (S.smul_mem _ hw₁)
  have hw₂'0 : w₂' ≠ 0 := fun h0 => by
    have := (hli (-c) 1 (by rw [neg_smul, one_smul, ← h0, hw₂']; abel)).2
    exact one_ne_zero this
  have horth : hypHf h w₁ w₂' = 0 := by
    rw [hw₂', hypHf_sub_right, hypHf_smul_right, hc, div_mul_cancel₀ _ ha, sub_self]
  have horth' : hypHf h w₂' w₁ = 0 := by
    rw [← bar_hypHf, horth, map_zero]
  by_cases hd : hypHf h w₂' w₂' = 0
  · exact ⟨w₂', hw₂'S, hw₂'0, hd⟩
  have hr : h.bar (-hypHf h w₂' w₂' / hypHf h w₁ w₁) = -hypHf h w₂' w₂' / hypHf h w₁ w₁ := by
    rw [map_div₀, map_neg, bar_hypHf_self, bar_hypHf_self]
  obtain ⟨α, hα⟩ := h.normHom_surjective ⟨_, (h.mem_fixedField).mpr hr⟩
  have hα' : α * h.bar α = -hypHf h w₂' w₂' / hypHf h w₁ w₁ := congrArg Subtype.val hα
  refine ⟨α • w₁ + w₂', S.add_mem (S.smul_mem _ hw₁) hw₂'S, fun h0 => ?_, ?_⟩
  · have := (hli (α - c) 1 (by rw [← h0, hw₂', sub_smul, one_smul]; abel)).2
    exact one_ne_zero this
  · rw [hypHf_add_left, hypHf_add_right, hypHf_add_right, hypHf_smul_left, hypHf_smul_left,
      hypHf_smul_right, hypHf_smul_right, horth, horth']
    calc h.bar α * (α * hypHf h w₁ w₁) + h.bar α * 0 + (α * 0 + hypHf h w₂' w₂') =
        (α * h.bar α) * hypHf h w₁ w₁ + hypHf h w₂' w₂' := by ring
      _ = 0 := by rw [hα', div_mul_cancel₀ _ ha, neg_add_cancel]

theorem hypHf_isometry {T T' : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hT : (T.map h.bar)ᵀ * hypGram 1 1 K * T = hypGram 1 1 K) (hTT : T * T' = 1)
    (x y : HypIndex 1 1 → K) : hypHf h (T *ᵥ x) (T *ᵥ y) = hypHf h x y := by
  rw [hypHf, hypHf, ← hrow_mul_inv hT hTT, ← dotProduct_mulVec, mulVec_mulVec,
    mul_eq_one_comm.mp hTT, one_mulVec]

theorem eq_zero_of_hypHf_eq_zero {x : HypIndex 1 1 → K} (hx : ∀ y, hypHf h x y = 0) : x = 0 := by
  have hrow0 : hrow h.bar (hypGram 1 1 K) x = 0 := by
    funext i
    have := hx (Pi.single i 1)
    rwa [hypHf, dotProduct_single_one] at this
  have hbar0 : (fun i => h.bar (x i)) = 0 := by
    have h1 : (fun i => h.bar (x i)) ᵥ* (hypGram 1 1 K * hypGram 1 1 K) = 0 := by
      rw [← vecMul_vecMul]
      exact (congrArg (· ᵥ* hypGram 1 1 K) hrow0).trans (zero_vecMul _)
    rwa [hypGram_mul_self, vecMul_one] at h1
  funext i
  have := congrFun hbar0 i
  simpa using this

theorem eichler_sub_one_cube {e e₀ : HypIndex 1 1 → K} {b : K}
    (hee : hrow h.bar (hypGram 1 1 K) e ⬝ᵥ e = 0) (he₀e : hrow h.bar (hypGram 1 1 K) e₀ ⬝ᵥ e = 0)
    (hee₀ : hrow h.bar (hypGram 1 1 K) e ⬝ᵥ e₀ = 0) :
    (eichler h.bar (hypGram 1 1 K) e e₀ b - 1) * (eichler h.bar (hypGram 1 1 K) e e₀ b - 1) *
      (eichler h.bar (hypGram 1 1 K) e e₀ b - 1) = 0 := by
  set G := hypGram 1 1 K
  set E₁ := vecMulVec e (hrow h.bar G e₀) with hE₁
  set E₂ := vecMulVec e₀ (hrow h.bar G e) with hE₂
  set E₃ := vecMulVec e (hrow h.bar G e) with hE₃
  have h11 : E₁ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, he₀e, zero_smul, vecMulVec_zero]
  have h12 : E₁ * E₂ = (hrow h.bar G e₀ ⬝ᵥ e₀) • E₃ := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have h13 : E₁ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, he₀e, zero_smul, vecMulVec_zero]
  have h21 : E₂ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h22 : E₂ * E₂ = 0 := by rw [vecMulVec_mul_vecMulVec, hee₀, zero_smul, vecMulVec_zero]
  have h23 : E₂ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h31 : E₃ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h32 : E₃ * E₂ = 0 := by rw [vecMulVec_mul_vecMulVec, hee₀, zero_smul, vecMulVec_zero]
  have h33 : E₃ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have hN : eichler h.bar G e e₀ b - 1 = E₁ - E₂ + b • E₃ := by
    rw [eichler]
    abel
  rw [hN]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, h11, h12,
    h13, h21, h22, h23, h31, h32, h33, smul_zero, sub_zero, zero_sub, add_zero, neg_zero, sub_self]

theorem exists_eichler (hp2 : p ≠ 2) {T T' : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hT : (T.map h.bar)ᵀ * hypGram 1 1 K * T = hypGram 1 1 K) (hTT : T * T' = 1)
    (hT2 : T * T = 1) (hdet : T.det = 1) (hT1 : T ≠ 1) :
    ∃ u u' : Matrix (HypIndex 1 1) (HypIndex 1 1) K, u * u' = 1 ∧ u' * u = 1 ∧
      (u.map h.bar)ᵀ * hypGram 1 1 K * u = hypGram 1 1 K ∧ u ^ p = 1 ∧
      (∀ c : K, u ≠ c • 1) ∧ T * u * T' = u' := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have : (p : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    have := Nat.le_of_dvd (by norm_num) this
    have := h.prime.two_le
    omega
  set f : Module.End K (HypIndex 1 1 → K) := Matrix.toLin' T with hf
  have hfT : ∀ v, f v = T *ᵥ v := fun v => Matrix.toLin'_apply T v
  have hinv : Function.Involutive f := fun v => by rw [hfT, hfT, mulVec_mulVec, hT2, one_mulVec]
  have hdim : Module.finrank K (HypIndex 1 1 → K) = 3 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hdetf : LinearMap.det f = 1 := by rw [hf, LinearMap.det_toLin', hdet]
  have hne : f ≠ LinearMap.id := fun h1 => hT1 (by
    have := congrArg LinearMap.toMatrix' h1
    rwa [hf, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this)
  obtain ⟨hm, hpl⟩ :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_finrank_three h2 f hinv hdim hdetf hne
  set Vm := CFSG.Wreathed.OddLinearThreeCentralizerCore.minusSpace f with hVm
  set Vp := CFSG.Wreathed.OddLinearThreeCentralizerCore.plusSpace f with hVp
  have hmemm : ∀ v, v ∈ Vm ↔ T *ᵥ v = -v := fun v => by
    rw [hVm, CFSG.Wreathed.OddLinearThreeCentralizerCore.minusSpace,
      Module.End.mem_eigenspace_iff, hfT, neg_one_smul]
  have hmemp : ∀ v, v ∈ Vp ↔ T *ᵥ v = v := fun v => by
    rw [hVp, CFSG.Wreathed.OddLinearThreeCentralizerCore.plusSpace,
      Module.End.mem_eigenspace_iff, hfT, one_smul]
  let bm := Module.finBasisOfFinrankEq K Vm hm
  have hli : ∀ a b : K, a • ((bm 0 : Vm) : HypIndex 1 1 → K) + b • ((bm 1 : Vm) : _) = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have hab' : a • bm 0 + b • bm 1 = 0 := Subtype.ext (by simpa using hab)
    have hl := Fintype.linearIndependent_iff.mp bm.linearIndependent ![a, b]
      (by simpa [Fin.sum_univ_two] using hab')
    exact ⟨hl 0, hl 1⟩
  obtain ⟨e, heVm, he0, hee⟩ := exists_isotropic h (bm 0).2 (bm 1).2 hli
  obtain ⟨e₀', he₀'0, hspan⟩ := finrank_eq_one_iff'.mp hpl
  set e₀ : HypIndex 1 1 → K := e₀'.1 with he₀def
  have he₀0 : e₀ ≠ 0 := fun h0 => he₀'0 (Subtype.ext h0)
  have hTe : T *ᵥ e = -e := (hmemm e).mp heVm
  have hTe₀ : T *ᵥ e₀ = e₀ := (hmemp e₀).mp e₀'.2
  have horth : ∀ v w, T *ᵥ v = v → T *ᵥ w = -w → hypHf h v w = 0 := by
    intro v w hv hw
    have h1 := hypHf_isometry h hT hTT v w
    rw [hv, hw, show -w = (-1 : K) • w by rw [neg_one_smul], hypHf_smul_right] at h1
    have : (2 : K) * hypHf h v w = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have he₀e : hypHf h e₀ e = 0 := horth e₀ e hTe₀ hTe
  have hee₀ : hypHf h e e₀ = 0 := by rw [← bar_hypHf, he₀e, map_zero]
  set n₀ := hypHf h e₀ e₀ with hn₀
  have hn₀0 : n₀ ≠ 0 := by
    intro h0
    apply he₀0
    apply eq_zero_of_hypHf_eq_zero h
    intro y
    have hy : y ∈ Vm ⊔ Vp :=
      (CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_spaces_isCompl h2 f hinv).sup_eq_top ▸
        Submodule.mem_top
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc⟩ := hspan ⟨y₂, hy₂⟩
    have hy₂' : y₂ = c • e₀ := (congrArg Subtype.val hc).symm
    rw [hypHf_add_right, horth e₀ y₁ hTe₀ ((hmemm y₁).mp hy₁), hy₂', hypHf_smul_right, ← hn₀, h0,
      mul_zero, add_zero]
  set b : K := -n₀ / 2 with hb
  have hbb : h.bar b = b := by
    rw [hb, map_div₀, map_neg, hn₀, bar_hypHf_self, map_ofNat]
  have hb0 : b + b + n₀ = 0 := by
    rw [hb]
    field_simp
    ring
  set u := eichler h.bar (hypGram 1 1 K) e e₀ b with hu
  set u' := eichler h.bar (hypGram 1 1 K) (-e) e₀ b with hu'
  have huu : u * u' = 1 := eichler_mul_eichler_neg hee he₀e hee₀ hb0
  have hu'u : u' * u = 1 := mul_eq_one_comm.mp huu
  refine ⟨u, u', huu, hu'u, ?_, ?_, ?_, eichler_conj hT hTT hTe hTe₀ b⟩
  · have h1 := adjoint_eichler (bar := h.bar) h.bar_bar (hypGram_herm h) e e₀ b
    rw [hbb] at h1
    rw [h1, mul_assoc, hu'u, mul_one]
  · have h1 := pow_char_of_cube (K := K) (p := p) hp2
      (eichler_sub_one_cube h (b := b) hee he₀e hee₀)
    rwa [add_sub_cancel] at h1
  · intro c hc
    have h1 : u *ᵥ e₀ = e₀ + n₀ • e := by
      rw [hu, eichler, add_mulVec, sub_mulVec, add_mulVec, one_mulVec, smul_mulVec,
        vecMulVec_mulVec, vecMulVec_mulVec, vecMulVec_mulVec]
      change e₀ + MulOpposite.op (hypHf h e₀ e₀) • e - MulOpposite.op (hypHf h e e₀) • e₀ +
        b • MulOpposite.op (hypHf h e e₀) • e = e₀ + n₀ • e
      rw [hee₀, ← hn₀]
      simp
    rw [hc, smul_mulVec, one_mulVec] at h1
    have hm1 : n₀ • e ∈ Vm := Vm.smul_mem _ heVm
    have hp1 : n₀ • e ∈ Vp := by
      have : n₀ • e = (c - 1) • e₀ := by
        rw [sub_smul, one_smul, h1]
        abel
      rw [this]
      exact Vp.smul_mem _ e₀'.2
    have hdisj := (CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_spaces_isCompl h2 f
      hinv).disjoint
    have h0 : n₀ • e = 0 := (Submodule.disjoint_def.mp hdisj) _ hm1 hp1
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact hn₀0 h0
    · exact he0 h0

end CFSG.Quasithin.H13.S126C
