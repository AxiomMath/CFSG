module

public import CFSG.Quasithin.Background.HSL3Fix
public import CFSG.Quasithin.Background.HNPrime
public import CFSG.Quasithin.Background.E3Nprime

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SL3Pair
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def rho : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (PairMod K) :=
  pairHom.comp ((StatedSL 3 K).subtype.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)

theorem rho_apply_fst (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : PairMod K) :
    Multiplicative.toAdd (rho g x).1 = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.1 :=
  rfl

theorem rho_apply_snd (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : PairMod K) :
    Multiplicative.toAdd (rho g x).2 =
      ((dualGL (specialLinearGroupEquivStatedSL 3 K g : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.2 :=
  rfl

theorem rho_injective : Function.Injective (rho (K := K)) := by
  intro g h hgh
  apply Subtype.ext
  ext i j
  have h1 := congrArg (fun φ : MulAut (PairMod K) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1), 1)).1 i) hgh
  simpa [rho_apply_fst, Matrix.mulVec_single] using h1

theorem range_rho : (rho (K := K)).range = pairSL K := by
  rw [pairSL, rho, MonoidHom.range_comp, MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.range_eq_top.mpr (specialLinearGroupEquivStatedSL 3 K).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem rho_mem_pairSL (g : Matrix.SpecialLinearGroup (Fin 3) K) : rho g ∈ pairSL K := by
  rw [← range_rho]
  exact ⟨g, rfl⟩

theorem exists_rho_of_mem {x : MulAut (PairMod K)} (hx : x ∈ pairSL K) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, rho g = x := by
  rw [← range_rho] at hx
  exact hx

section Two

variable [Finite K]

theorem eq_zero_or_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_contra hc
  push Not at hc
  have hinj : Function.Injective (![0, 1, c] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm, zero_ne_one]
  have := Nat.card_le_card_of_injective _ hinj
  rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

variable [CharP K 2]

theorem mem_pairSL_of_odd (hK : Nat.card K = 2) {y : MulAut (PairMod K)} (hyN : y ∈ pairNorm K)
    {p : ℕ} (hp : Odd p) (hyp : y ^ p = 1) : y ∈ pairSL K :=
  mem_pairSL_of_mem_pairSub hK hyN (mem_pairSub_of_odd hyN hp hyp)

omit [CharP K 2] in
theorem mem_pairSub_of_map_V₁ {x : MulAut (PairMod K)} (hx : x ∈ pairNorm K)
    (h1 : (V₁ K).map x.toMonoidHom = V₁ K) : x ∈ pairSub K := by
  obtain ⟨x₁, x₂, rfl, -, -⟩ := exists_pairAut hx h1
  exact pairAut_mem_pairSub x₁ x₂

omit [CharP K 2] in
theorem map_V₁_eq_V₂ {x : MulAut (PairMod K)} (hx : x ∈ pairNorm K) (hxs : x ∉ pairSub K) :
    (V₁ K).map x.toMonoidHom = V₂ K :=
  (map_V₁_eq_or hx).resolve_left fun h => hxs (mem_pairSub_of_map_V₁ hx h)

theorem isPGroup_upperTriangular (hK : Nat.card K = 2) :
    IsPGroup 2 (LinearFlag.upperTriangular 3 K) := by
  rintro ⟨g, hg⟩
  refine ⟨2, ?_⟩
  have hlow := LinearFlag.mem_upperTriangular.mp hg
  have h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hlow 1 0 (by decide)
  have h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hlow 2 0 (by decide)
  have h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hlow 2 1 (by decide)
  have hdet := g.2
  rw [Matrix.det_fin_three, h10, h20, h21] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  have hd : ∀ i : Fin 3, (g : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
    have h0 := eq_zero_or_one hK ((g : Matrix (Fin 3) (Fin 3) K) 0 0)
    have h1 := eq_zero_or_one hK ((g : Matrix (Fin 3) (Fin 3) K) 1 1)
    have h2 := eq_zero_or_one hK ((g : Matrix (Fin 3) (Fin 3) K) 2 2)
    intro i
    fin_cases i
    · rcases h0 with h | h
      · rw [h] at hdet; simp at hdet
      · exact h
    · rcases h1 with h | h
      · rw [h] at hdet; simp at hdet
      · exact h
    · rcases h2 with h | h
      · rw [h] at hdet; simp at hdet
      · exact h
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  apply Subtype.ext
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) K) ^ 2 ^ 2 = 1
  rw [Matrix.eta_fin_three (g : Matrix (Fin 3) (Fin 3) K), h10, h20, h21, hd 0, hd 1, hd 2]
  set a := (g : Matrix (Fin 3) (Fin 3) K) 0 1
  set b := (g : Matrix (Fin 3) (Fin 3) K) 0 2
  set c := (g : Matrix (Fin 3) (Fin 3) K) 1 2
  have e : (!![1, a, b; 0, 1, c; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) ^ 2 ^ 2 =
      !![1, 4 * a, 4 * b + 6 * (a * c); 0, 1, 4 * c; 0, 0, 1] := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [e]
  have h4 : (4 : K) = 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num, h2K, zero_mul]
  have h6 : (6 : K) = 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num, h2K, zero_mul]
  rw [h4, h6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP K 2] in
theorem exists_swap_mem_sylow {X : Subgroup (MulAut (PairMod K))}
    (hX2 : X ≤ pairNorm K) (hX3 : ∃ x ∈ X, x ∉ pairSub K) {S : Subgroup (MulAut (PairMod K))}
    (hS : IsSylowIn 2 S X) : ∃ s ∈ S, s ∉ pairSub K := by
  by_contra h
  push Not at h
  obtain ⟨x, hxX, hx⟩ := hX3
  set X₀ := X ⊓ pairSub K with hX₀
  have hidx : (X₀.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hxX⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hX₀, Subgroup.mem_inf]
    by_cases hb : (b : MulAut (PairMod K)) ∈ pairSub K
    · refine Or.inr ⟨⟨b.2, hb⟩, fun hbx => hx ?_⟩
      have := (pairSub K).mul_mem ((pairSub K).inv_mem hb) hbx.2
      simpa using this
    · refine Or.inl ⟨⟨X.mul_mem b.2 hxX, ?_⟩, fun hb' => hb hb'.2⟩
      have := inv_mul_mem_pairSub (Subgroup.inv_mem _ (hX2 b.2)) (hX2 hxX)
        (fun h' => hb (by simpa using (pairSub K).inv_mem h')) hx
      simpa using this
  have hSX₀ : S ≤ X₀ := fun y hy => ⟨hS.le hy, h y hy⟩
  have hrel := Subgroup.relIndex_mul_relIndex S X₀ X hSX₀ inf_le_left
  apply hS.not_dvd_relIndex
  rw [← hrel]
  have h2 : X₀.relIndex X = 2 := hidx
  rw [h2]
  exact dvd_mul_left 2 _

end Two

section Fix

@[expose] def fix₁ (Q : Subgroup (MulAut (PairMod K))) : Subgroup (PairMod K) := V₁ K ⊓ fixV Q

@[expose] def fix₂ (Q : Subgroup (MulAut (PairMod K))) : Subgroup (PairMod K) := V₂ K ⊓ fixV Q

theorem mem_fix₂_of_mem_fix₁ {Q : Subgroup (MulAut (PairMod K))} {s : MulAut (PairMod K)}
    (hsN : s ∈ Subgroup.normalizer (Q : Set (MulAut (PairMod K))))
    (hsV : (V₁ K).map s.toMonoidHom = V₂ K) {x : PairMod K} (hx : x ∈ fix₁ Q) : s x ∈ fix₂ Q := by
  refine ⟨hsV ▸ ⟨x, hx.1, rfl⟩, fun q hq => ?_⟩
  have hq' : s⁻¹ * q * s ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) q).mp hq
    simpa using this
  have h1 := hx.2 _ hq'
  calc q (s x) = s ((s⁻¹ * q * s) x) := by simp [MulAut.mul_apply]
    _ = s x := by rw [h1]

theorem fix₁_eq_bot_iff {Q : Subgroup (MulAut (PairMod K))} {s : MulAut (PairMod K)}
    (hsN : s ∈ Subgroup.normalizer (Q : Set (MulAut (PairMod K))))
    (hsV : (V₁ K).map s.toMonoidHom = V₂ K) : fix₁ Q = ⊥ ↔ fix₂ Q = ⊥ := by
  have hsV' : (V₂ K).map s⁻¹.toMonoidHom = V₁ K := by
    have hid : s⁻¹.toMonoidHom.comp s.toMonoidHom = MonoidHom.id (PairMod K) :=
      MonoidHom.ext fun v => by simp
    rw [← hsV, Subgroup.map_map, hid, Subgroup.map_id]
  constructor
  · intro h1
    rw [eq_bot_iff]
    intro y hy
    have : s⁻¹ y ∈ fix₁ Q := by
      refine ⟨hsV' ▸ ⟨y, hy.1, rfl⟩, fun q hq => ?_⟩
      have hq' : s * q * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hsN q).mp hq
      have h1 := hy.2 _ hq'
      calc q (s⁻¹ y) = s⁻¹ ((s * q * s⁻¹) y) := by simp [MulAut.mul_apply]
        _ = s⁻¹ y := by rw [h1]
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg s this
  · intro h2
    rw [eq_bot_iff]
    intro x hx
    have := mem_fix₂_of_mem_fix₁ hsN hsV hx
    rw [h2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact s.injective (this.trans (map_one s).symm)

theorem rho_fix_snd_iff (g : Matrix.SpecialLinearGroup (Fin 3) K) (w : Fin 3 → K) :
    rho g ((1 : StdMod (Fin 3) K), Multiplicative.ofAdd w) = (1, Multiplicative.ofAdd w) ↔
      (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w := by
  set A : GL (Fin 3) K := (specialLinearGroupEquivStatedSL 3 K g : GL (Fin 3) K)
  have hA : (A : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) := rfl
  have hinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsnd : ∀ x : PairMod K, Multiplicative.toAdd (rho g x).2 =
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ Multiplicative.toAdd x.2 :=
    fun x => rho_apply_snd g x
  constructor
  · intro h
    have h2 := congrArg (fun x : PairMod K => Multiplicative.toAdd x.2) h
    simp only [hsnd, toAdd_ofAdd] at h2
    calc (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w
        = (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
            (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w) := by rw [h2]
      _ = w := by rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hA, hinv,
          Matrix.transpose_one, Matrix.one_mulVec]
  · intro h
    apply Prod.ext
    · show (rho g (1, Multiplicative.ofAdd w)).1 = (1 : StdMod (Fin 3) K)
      apply Multiplicative.toAdd.injective
      rw [rho_apply_fst]
      simp
    · apply Multiplicative.toAdd.injective
      rw [hsnd]
      simp only [toAdd_ofAdd]
      calc ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w
          = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
              ((g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w) := by rw [h]
        _ = w := by rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hA, hinv',
            Matrix.transpose_one, Matrix.one_mulVec]

theorem rho_fix_fst_iff (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K) :
    rho g (Multiplicative.ofAdd v, (1 : StdMod (Fin 3) K)) = (Multiplicative.ofAdd v, 1) ↔
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  constructor
  · intro h
    have h1 := congrArg (fun x : PairMod K => Multiplicative.toAdd x.1) h
    simpa [rho_apply_fst] using h1
  · intro h
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      rw [rho_apply_fst]
      simpa using h
    · apply Multiplicative.toAdd.injective
      rw [rho_apply_snd]
      simp

end Fix

section Seven

abbrev NZ (K : Type) [Field K] : Type := {v : Fin 3 → K // v ≠ 0}

theorem mulVec_ne_zero (g : Matrix.SpecialLinearGroup (Fin 3) K) {v : Fin 3 → K} (hv : v ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc v = (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ v := by rw [h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

@[expose] noncomputable def nzAct (g : Matrix.SpecialLinearGroup (Fin 3) K) : Function.End (NZ K) :=
  fun v => ⟨(g : Matrix (Fin 3) (Fin 3) K) *ᵥ v.1, mulVec_ne_zero g v.2⟩

theorem nzAct_val (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : NZ K) :
    (nzAct g v).1 = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v.1 := rfl

theorem nzAct_pow (g : Matrix.SpecialLinearGroup (Fin 3) K) (n : ℕ) :
    nzAct g ^ n = nzAct (g ^ n) := by
  induction n with
  | zero =>
    funext v
    apply Subtype.ext
    rw [pow_zero, pow_zero, nzAct_val, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  | succ n ih =>
    funext v
    apply Subtype.ext
    rw [pow_succ', ih, pow_succ', nzAct_val, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec]
    rfl

theorem eq_one_of_nzAct {g : Matrix.SpecialLinearGroup (Fin 3) K} (h : ∀ v : NZ K, nzAct g v = v) :
    g = 1 := by
  apply Subtype.ext
  ext i j
  have hj : (Pi.single j (1 : K) : Fin 3 → K) ≠ 0 := by
    intro h0
    have := congrFun h0 j
    simp at this
  have h1 := congrFun (congrArg Subtype.val (h ⟨Pi.single j 1, hj⟩)) i
  rw [nzAct_val] at h1
  have h1' : ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1) i =
      (Pi.single j (1 : K) : Fin 3 → K) i := h1
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) i j = (Pi.single j (1 : K) : Fin 3 → K) i := by
    rw [← h1']
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Matrix.SpecialLinearGroup.coe_one, h2, Matrix.one_apply]
  simp [Pi.single_apply]

variable [Finite K]

theorem card_NZ (hK : Nat.card K = 2) : Nat.card (NZ K) = 7 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fun, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, hK, Fintype.card_subtype_eq]
  norm_num

theorem card_fix_modEq {g : Matrix.SpecialLinearGroup (Fin 3) K} {p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = 2) (hg : g ^ p = 1) :
    Nat.card (Function.fixedPoints (nzAct g)) ≡ 7 [MOD p] := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hf : nzAct g ^ p ^ 1 = 1 := by
    rw [pow_one, nzAct_pow, hg]
    funext v
    apply Subtype.ext
    rw [nzAct_val, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, card_NZ hK] at h
  exact h.symm

theorem false_of_commute (hK : Nat.card K = 2) {γ ζ : Matrix.SpecialLinearGroup (Fin 3) K}
    (hγ : orderOf γ = 7) (hζ : orderOf ζ = 3) (hc : γ * ζ = ζ * γ) : False := by
  classical
  have : Fintype (NZ K) := Fintype.ofFinite _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hγ7 : γ ^ 7 = 1 := by rw [← hγ, pow_orderOf_eq_one]
  have hζ3 : ζ ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hnofix : ∀ v : NZ K, nzAct γ v ≠ v := by
    intro v hv
    have hmod := card_fix_modEq hK hγ7
    have hle : Nat.card (Function.fixedPoints (nzAct γ)) ≤ 7 :=
      (card_NZ hK) ▸ Finite.card_subtype_le _
    have hpos : 0 < Nat.card (Function.fixedPoints (nzAct γ)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨v, hv⟩⟩, inferInstance⟩
    have h7 : Nat.card (Function.fixedPoints (nzAct γ)) = 7 := by
      unfold Nat.ModEq at hmod
      omega
    have hall : ∀ w : NZ K, nzAct γ w = w := by
      intro w
      by_contra hw
      have hlt := Finite.card_subtype_lt (p := fun u => Function.IsFixedPt (nzAct γ) u)
        (x := w) hw
      change Nat.card (Function.fixedPoints (nzAct γ)) < Nat.card (NZ K) at hlt
      rw [h7, card_NZ hK] at hlt
      exact lt_irrefl 7 hlt
    have h1 := eq_one_of_nzAct hall
    rw [h1, orderOf_one] at hγ
    norm_num at hγ
  set F := Function.fixedPoints (nzAct ζ) with hFdef
  have hmodζ := card_fix_modEq hK hζ3
  have hF1 : 1 ≤ Nat.card F := by
    unfold Nat.ModEq at hmodζ
    rw [← hFdef] at hmodζ
    omega
  have hγF : ∀ v : NZ K, v ∈ F → nzAct γ v ∈ F := by
    intro v hv
    change nzAct ζ (nzAct γ v) = nzAct γ v
    have e : nzAct ζ (nzAct γ v) = nzAct (ζ * γ) v := by
      apply Subtype.ext
      rw [nzAct_val, nzAct_val, nzAct_val, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mulVec_mulVec]
    rw [e, ← hc]
    apply Subtype.ext
    rw [nzAct_val, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← nzAct_val,
      show nzAct ζ v = v from hv, nzAct_val]
  let σ : Function.End F := fun v => ⟨nzAct γ v, hγF v v.2⟩
  have hσ : σ ^ 7 ^ 1 = 1 := by
    have hpow : ∀ (n : ℕ) (v : F), ((σ ^ n) v : NZ K) = (nzAct γ ^ n) v := by
      intro n
      induction n with
      | zero => intro v; rfl
      | succ n ih =>
        intro v
        rw [pow_succ', pow_succ']
        change nzAct γ ((σ ^ n) v : NZ K) = nzAct γ ((nzAct γ ^ n) v)
        rw [ih]
    funext v
    apply Subtype.ext
    rw [pow_one, hpow, nzAct_pow, hγ7]
    apply Subtype.ext
    rw [nzAct_val, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  have hmodF := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hσ
  have hfix0 : Nat.card (Function.fixedPoints σ) = 0 := by
    have : IsEmpty (Function.fixedPoints σ) :=
      ⟨fun ⟨v, hv⟩ => hnofix v (congrArg Subtype.val hv)⟩
    exact Nat.card_of_isEmpty
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hfix0] at hmodF
  have hFle : Nat.card F ≤ 7 := (card_NZ hK) ▸ Finite.card_subtype_le _
  have hF7 : Nat.card F = 7 := by
    unfold Nat.ModEq at hmodF
    omega
  have hall : ∀ w : NZ K, nzAct ζ w = w := by
    intro w
    by_contra hw
    have hlt := Finite.card_subtype_lt (p := fun u => Function.IsFixedPt (nzAct ζ) u) (x := w) hw
    change Nat.card F < Nat.card (NZ K) at hlt
    rw [hF7, card_NZ hK] at hlt
    exact lt_irrefl 7 hlt
  have h1 := eq_one_of_nzAct hall
  rw [h1, orderOf_one] at hζ
  norm_num at hζ

end Seven

section Flag

@[expose] noncomputable def slT (i j : Fin 3) (h : i ≠ j) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j h 1⟩

theorem coe_slT (i j : Fin 3) (h : i ≠ j) :
    ((slT i j h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection i j 1 := rfl

theorem mulVec_single_apply (M : Matrix (Fin 3) (Fin 3) K) (j k : Fin 3) :
    (M *ᵥ Pi.single j 1) k = M k j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem eq_zero_of_transvection_fix {i j : Fin 3} {v : Fin 3 → K}
    (hv : Matrix.transvection i j (1 : K) *ᵥ v = v) : v j = 0 := by
  have h1 := congrFun hv i
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec] at h1
  simpa using h1

theorem mulVec_single_mem_flagSpace {g : Matrix.SpecialLinearGroup (Fin 3) K} {i : ℕ}
    (hg : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K i)) {j : Fin 3} (hj : (j : ℕ) < i) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1 ∈ LinearFlag.flagSpace 3 K i := by
  have hmem : (Pi.single j (1 : K) : Fin 3 → K) ∈ LinearFlag.flagSpace 3 K i :=
    Submodule.subset_span ⟨j, hj, rfl⟩
  rw [← LinearFlag.mem_stabilizer.mp hg]
  exact ⟨_, hmem, rfl⟩

theorem entry_eq_zero_of_stab {g : Matrix.SpecialLinearGroup (Fin 3) K} {i : ℕ}
    (hg : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K i)) {j k : Fin 3}
    (hj : (j : ℕ) < i) (hk : i ≤ (k : ℕ)) : (g : Matrix (Fin 3) (Fin 3) K) k j = 0 := by
  have h := LinearFlag.mem_flagSpace.mp (mulVec_single_mem_flagSpace hg hj) k hk
  rwa [mulVec_single_apply] at h

theorem refl1_mulVec_one (v : Fin 3 → K) :
    (LinearFlag.reflectionMatrix 3 K 1 *ᵥ v) 1 = v 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, LinearFlag.reflectionMatrix]

theorem refl2_transpose_mulVec_one (w : Fin 3 → K) :
    ((LinearFlag.reflectionMatrix 3 K 2)ᵀ *ᵥ w) 1 = w 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, LinearFlag.reflectionMatrix,
    Matrix.transpose_apply]

variable [Finite K]

theorem mulVec_e0_of_stab (hK : Nat.card K = 2) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1)) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have h10 := entry_eq_zero_of_stab hg (j := 0) (k := 1) (by decide) (by decide)
  have h20 := entry_eq_zero_of_stab hg (j := 0) (k := 2) (by decide) (by decide)
  have hdet := g.2
  rw [Matrix.det_fin_three, h10, h20] at hdet
  have h00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    rcases eq_zero_or_one hK ((g : Matrix (Fin 3) (Fin 3) K) 0 0) with h | h
    · rw [h] at hdet; simp at hdet
    · exact h
  funext k
  rw [mulVec_single_apply]
  fin_cases k
  · simpa using h00
  · simpa using h10
  · simpa using h20

theorem transpose_mulVec_e2_of_stab (hK : Nat.card K = 2) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2)) :
    (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
  have h20 := entry_eq_zero_of_stab hg (j := 0) (k := 2) (by decide) (by decide)
  have h21 := entry_eq_zero_of_stab hg (j := 1) (k := 2) (by decide) (by decide)
  have hdet := g.2
  rw [Matrix.det_fin_three, h20, h21] at hdet
  have h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rcases eq_zero_or_one hK ((g : Matrix (Fin 3) (Fin 3) K) 2 2) with h | h
    · rw [h] at hdet; simp at hdet
    · exact h
  funext k
  rw [mulVec_single_apply, Matrix.transpose_apply]
  fin_cases k
  · simpa using h20
  · simpa using h21
  · simpa using h22

variable [CharP K 2]

theorem eq_bot_of_flag (hK : Nat.card K = 2) {Q B : Subgroup (MulAut (PairMod K))}
    (hQL : Q ≤ pairSL K) (hUQ : (LinearFlag.upperTriangular 3 K).map rho ≤ Q) (hBQ : B ≤ Q)
    (hBodd : Odd (Nat.card B)) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    {s : MulAut (PairMod K)} (hsN : s ∈ Subgroup.normalizer (Q : Set (MulAut (PairMod K))))
    (hsV : (V₁ K).map s.toMonoidHom = V₂ K) (h21 : Q = pairSL K → 21 ∣ Nat.card B) :
    B = ⊥ := by
  classical
  set Q' := Q.comap rho with hQ'
  have hUQ' : LinearFlag.upperTriangular 3 K ≤ Q' := fun u hu => hUQ ⟨u, hu, rfl⟩
  obtain ⟨hQI, -⟩ := LinearFlag.borel_overgroups Q' hUQ'
  set I := LinearFlag.borelOvergroupCuts Q' with hI
  have hstab : ∀ i ∈ I, ∀ g ∈ Q', g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K i) := by
    intro i hi g hg
    rw [hQI] at hg
    exact LinearFlag.mem_flagStabilizer.mp hg i hi
  have hrefl : ∀ i (hi : 1 ≤ i) (hin : i < 3), i ∉ I →
      LinearFlag.reflection 3 K i hi hin ∈ Q' := by
    intro i hi hin hiI
    by_contra h
    exact hiI ⟨hi, hin, h⟩
  have hQrho : ∀ q ∈ Q, ∃ g ∈ Q', rho g = q := by
    intro q hq
    obtain ⟨g, hg⟩ := exists_rho_of_mem (hQL hq)
    exact ⟨g, show rho g ∈ Q by rw [hg]; exact hq, hg⟩
  have hfix := fix₁_eq_bot_iff hsN hsV
  have ht01 : slT 0 1 (by decide) ∈ Q' := hUQ' (by
    rw [LinearFlag.mem_upperTriangular]
    intro a b hab
    rw [coe_slT, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hab),
      Matrix.single_apply]
    simp only [zero_add]
    split_ifs with h
    · exfalso; obtain ⟨rfl, rfl⟩ := h; exact absurd hab (by decide)
    · rfl)
  have ht12 : slT 1 2 (by decide) ∈ Q' := hUQ' (by
    rw [LinearFlag.mem_upperTriangular]
    intro a b hab
    rw [coe_slT, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hab),
      Matrix.single_apply]
    simp only [zero_add]
    split_ifs with h
    · exfalso; obtain ⟨rfl, rfl⟩ := h; exact absurd hab (by decide)
    · rfl)
  have hfix1 : 1 ∉ I → fix₁ Q = ⊥ := by
    intro h1
    rw [eq_bot_iff]
    rintro ⟨x₁, x₂⟩ ⟨hxV, hxQ⟩
    have hx2 : x₂ = 1 := (mem_V₁.mp hxV)
    subst hx2
    set v := Multiplicative.toAdd x₁ with hv
    have hx₁ : x₁ = Multiplicative.ofAdd v := rfl
    rw [hx₁] at hxQ ⊢
    have hfixg : ∀ g ∈ Q', (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun g hg =>
      (rho_fix_fst_iff g v).mp (hxQ (rho g) hg)
    have hv1 : v 1 = 0 := eq_zero_of_transvection_fix (hfixg _ ht01)
    have hv2 : v 2 = 0 := eq_zero_of_transvection_fix (hfixg _ ht12)
    have hv0 : v 0 = 0 := by
      have h := congrFun (hfixg _ (hrefl 1 le_rfl (by norm_num) h1)) 1
      rw [LinearFlag.coe_reflection, refl1_mulVec_one, hv1] at h
      exact h
    rw [Subgroup.mem_bot]
    have hv0' : v = 0 := by
      funext k
      fin_cases k
      · exact hv0
      · exact hv1
      · exact hv2
    rw [hv0']
    rfl
  have hfix2 : 2 ∉ I → fix₂ Q = ⊥ := by
    intro h2
    rw [eq_bot_iff]
    rintro ⟨x₁, x₂⟩ ⟨hxV, hxQ⟩
    have hx1 : x₁ = 1 := (mem_V₂.mp hxV)
    subst hx1
    set w := Multiplicative.toAdd x₂ with hw
    have hx₂ : x₂ = Multiplicative.ofAdd w := rfl
    rw [hx₂] at hxQ ⊢
    have hfixg : ∀ g ∈ Q', (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w := fun g hg =>
      (rho_fix_snd_iff g w).mp (hxQ (rho g) hg)
    have hw0 : w 0 = 0 := by
      have h := hfixg _ ht01
      rw [coe_slT, transvection_transpose'] at h
      exact eq_zero_of_transvection_fix h
    have hw1 : w 1 = 0 := by
      have h := hfixg _ ht12
      rw [coe_slT, transvection_transpose'] at h
      exact eq_zero_of_transvection_fix h
    have hw2 : w 2 = 0 := by
      have h := congrFun (hfixg _ (hrefl 2 (by norm_num) (by norm_num) h2)) 1
      rw [LinearFlag.coe_reflection, refl2_transpose_mulVec_one, hw1] at h
      exact h
    rw [Subgroup.mem_bot]
    have hw0' : w = 0 := by
      funext k
      fin_cases k
      · exact hw0
      · exact hw1
      · exact hw2
    rw [hw0']
    rfl
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  ·
    have hQU : Q ≤ (LinearFlag.upperTriangular 3 K).map rho := by
      intro q hq
      obtain ⟨g, hg, rfl⟩ := hQrho q hq
      refine ⟨g, ?_, rfl⟩
      show g ∈ LinearFlag.upperTriangular 3 K
      rw [LinearFlag.mem_upperTriangular]
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
      · exact entry_eq_zero_of_stab (hstab 1 h1 g hg) (by decide) (by decide)
      · exact entry_eq_zero_of_stab (hstab 1 h1 g hg) (by decide) (by decide)
      · exact entry_eq_zero_of_stab (hstab 2 h2 g hg) (by decide) (by decide)
    have hp : IsPGroup 2 B :=
      (((isPGroup_upperTriangular hK).map rho).to_le (hBQ.trans hQU))
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exfalso
      rw [hk] at hBodd
      exact (Nat.not_even_iff_odd.mpr hBodd) ((Nat.even_pow' hkpos.ne').mpr even_two)
  ·
    exfalso
    apply ((Subgroup.ne_bot_iff_exists_ne_one).mpr ?_) (hfix.mpr (hfix2 h2))
    refine ⟨⟨(Multiplicative.ofAdd (Pi.single 0 1), 1), ⟨mem_V₁.mpr rfl, fun q hq => ?_⟩⟩, ?_⟩
    · obtain ⟨g, hg, rfl⟩ := hQrho q hq
      exact (rho_fix_fst_iff g _).mpr (mulVec_e0_of_stab hK (hstab 1 h1 g hg))
    · intro h
      have := congrArg (fun x : ↥(fix₁ Q) => Multiplicative.toAdd (x : PairMod K).1 0) h
      simp at this
  ·
    exfalso
    apply ((Subgroup.ne_bot_iff_exists_ne_one).mpr ?_) (hfix.mp (hfix1 h1))
    refine ⟨⟨(1, Multiplicative.ofAdd (Pi.single 2 1)), ⟨mem_V₂.mpr rfl, fun q hq => ?_⟩⟩, ?_⟩
    · obtain ⟨g, hg, rfl⟩ := hQrho q hq
      exact (rho_fix_snd_iff g _).mpr (transpose_mulVec_e2_of_stab hK (hstab 2 h2 g hg))
    · intro h
      have := congrArg (fun x : ↥(fix₂ Q) => Multiplicative.toAdd (x : PairMod K).2 2) h
      simp at this
  ·
    have hIe : I = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      obtain ⟨hi1, hi3, -⟩ := id hi
      interval_cases i
      · exact h1 hi
      · exact h2 hi
    have hQtop : Q' = ⊤ := by rw [hQI, hIe, LinearFlag.flagStabilizer_empty]
    have hQeq : Q = pairSL K := by
      refine le_antisymm hQL fun x hx => ?_
      obtain ⟨g, rfl⟩ := exists_rho_of_mem hx
      have : g ∈ Q' := hQtop ▸ Subgroup.mem_top g
      exact this
    have h21' := h21 hQeq
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7
      ((show (7 : ℕ) ∣ 21 by norm_num).trans h21')
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3
      ((show (3 : ℕ) ∣ 21 by norm_num).trans h21')
    obtain ⟨γ, hγ⟩ := exists_rho_of_mem (hQL (hBQ y.2))
    obtain ⟨ζ, hζ⟩ := exists_rho_of_mem (hQL (hBQ z.2))
    have hγo : orderOf γ = 7 := by
      rw [← orderOf_injective rho rho_injective γ, hγ, Subgroup.orderOf_coe, hy]
    have hζo : orderOf ζ = 3 := by
      rw [← orderOf_injective rho rho_injective ζ, hζ, Subgroup.orderOf_coe, hz]
    have hcomm : γ * ζ = ζ * γ := by
      apply rho_injective
      rw [map_mul, map_mul, hγ, hζ]
      exact hBab _ y.2 _ z.2
    exact (false_of_commute hK hγo hζo hcomm).elim

end Flag

section Permute

variable {G : Type*} [Group G]

theorem coe_sup_of_permute {H L : Subgroup G} (h : (H : Set G) * L = L * H) :
    ((H ⊔ L : Subgroup G) : Set G) = (H : Set G) * L := by
  let P : Subgroup G :=
    { carrier := (H : Set G) * L
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        have hkh : k₁ * h₂ ∈ (L : Set G) * H := ⟨k₁, hk₁, h₂, hh₂, rfl⟩
        rw [← h] at hkh
        obtain ⟨h₃, hh₃, k₃, hk₃, he⟩ := hkh
        have he' : h₃ * k₃ = k₁ * h₂ := he
        refine ⟨h₁ * h₃, H.mul_mem hh₁ hh₃, k₃ * k₂, L.mul_mem hk₃ hk₂, ?_⟩
        calc h₁ * h₃ * (k₃ * k₂) = h₁ * (h₃ * k₃) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [he']
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, L.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩
        have hkh : k₁⁻¹ * h₁⁻¹ ∈ (L : Set G) * H := ⟨k₁⁻¹, L.inv_mem hk₁, h₁⁻¹, H.inv_mem hh₁, rfl⟩
        rw [← h] at hkh
        simpa [_root_.mul_inv_rev] using hkh }
  apply le_antisymm
  · have : H ⊔ L ≤ P := sup_le (fun x hx => ⟨x, hx, 1, L.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
    exact this
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem card_sup_of_permute {H L : Subgroup G} (h : (H : Set G) * L = L * H) (hinf : H ⊓ L = ⊥) :
    Nat.card ↥(H ⊔ L) = Nat.card H * Nat.card L := by
  have hsup := coe_sup_of_permute h
  let f : ↥H × ↥L → ↥(H ⊔ L) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have e : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have hmem : (q.1 : G)⁻¹ * p.1 ∈ H ⊓ L := by
        refine ⟨H.mul_mem (H.inv_mem q.1.2) p.1.2, ?_⟩
        have : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
        rw [this]
        exact L.mul_mem q.2.2 (L.inv_mem p.2.2)
      rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h1 : p.1 = q.1 := Subtype.ext hmem.symm
      have h2 : p.2 = q.2 := by
        apply Subtype.ext
        rw [h1] at e
        exact mul_left_cancel e
      exact Prod.ext h1 h2
    · have hx : (x : G) ∈ ((H ⊔ L : Subgroup G) : Set G) := x.2
      rw [hsup] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

end Permute

section NPrime

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_SL_two (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card, hK]
  norm_num

omit [CharP K 2] in
theorem card_pairSL (hK : Nat.card K = 2) : Nat.card (pairSL K) = 168 := by
  rw [← range_rho, ← card_SL_two hK]
  exact (Nat.card_congr (MonoidHom.ofInjective rho_injective).toEquiv).symm

theorem eq_bot_of_permutes (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K) (hX3 : ∃ x ∈ X, x ∉ pairSub K)
    {B S : Subgroup (MulAut (PairMod K))} (hBX : B ≤ X)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (PairMod K))) * S = S * B) : B = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hBL : B ≤ pairSL K := by
    intro b hb
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
    exact mem_pairSL_of_odd hK (hX2 (hBX hb)) hodd (pow_orderOf_eq_one b)
  obtain ⟨s, hsS, hs⟩ := exists_swap_mem_sylow hX2 hX3 hS
  have hsX : s ∈ X := hS.le hsS
  have hsV := map_V₁_eq_V₂ (hX2 hsX) hs
  set P := B ⊔ S with hPdef
  set Q := P ⊓ pairSL K with hQdef
  have hsP : s ∈ P := le_sup_right (a := B) hsS
  have hnormP : P ≤ Subgroup.normalizer (P : Set (MulAut (PairMod K))) := Subgroup.le_normalizer
  have hsN : s ∈ Subgroup.normalizer (Q : Set (MulAut (PairMod K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hQdef, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hnormP hsP) y,
      Subgroup.mem_normalizer_iff.mp (hX2 hsX) y]
  have hBQ : B ≤ Q := le_inf le_sup_left hBL
  have hLnX : ((pairSL K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ pairSL K).comap rho with hU'def
  have hU'map : U'.map rho = S ⊓ pairSL K :=
    Subgroup.map_comap_eq_self (by rw [range_rho]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map rho = pairSL K := by
    rw [← MonoidHom.range_eq_map, range_rho]
  have hU' : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective rho_injective, hU'map, htopmap]
    exact hU
  let U'syl : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) K) :=
    hU'.isPGroup.toSylow (by
      have := hU'.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨P₀, hP₀⟩ := (isPGroup_upperTriangular hK).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) K) U'syl P₀
  have hconjU : ∀ u ∈ LinearFlag.upperTriangular 3 K, g⁻¹ * u * g ∈ U' := by
    intro u hu
    have h1 : u ∈ ((g • U'syl : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) K)) :
        Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) := hg ▸ hP₀ hu
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : (MulAut.conj g)⁻¹ • u = g⁻¹ * u * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [h2] at h1
    exact h1
  set c := rho g with hc
  set Q₀ := Q.map (MulAut.conj c).toMonoidHom with hQ₀
  have hcL : c ∈ pairSL K := rho_mem_pairSL g
  have hQL : Q ≤ pairSL K := inf_le_right
  have hmemQ₀ : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q₀ := fun q hq => ⟨q, hq, rfl⟩
  have hQ₀L : Q₀ ≤ pairSL K := by
    rintro _ ⟨q, hq, rfl⟩
    exact (pairSL K).mul_mem ((pairSL K).mul_mem hcL (hQL hq)) ((pairSL K).inv_mem hcL)
  have hconj_mem : ∀ {y : MulAut (PairMod K)}, y ∈ Q₀ ↔ c⁻¹ * y * c ∈ Q := by
    intro y
    rw [hQ₀, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hUQ₀ : (LinearFlag.upperTriangular 3 K).map rho ≤ Q₀ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hconj_mem]
    have h1 : rho (g⁻¹ * u * g) ∈ S ⊓ pairSL K := hconjU u hu
    have h2 : rho (g⁻¹ * u * g) ∈ Q := ⟨le_sup_right (a := B) h1.1, h1.2⟩
    have e : c⁻¹ * rho u * c = rho (g⁻¹ * u * g) := by
      rw [hc, map_mul, map_mul, map_inv]
    rw [e]
    exact h2
  set B₀ := B.map (MulAut.conj c).toMonoidHom with hB₀
  have hB₀Q₀ : B₀ ≤ Q₀ := Subgroup.map_mono hBQ
  have hB₀card : Nat.card B₀ = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hB₀ab : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha b hb]
  set s₀ := c * s * c⁻¹ with hs₀
  have hs₀N : s₀ ∈ Subgroup.normalizer (Q₀ : Set (MulAut (PairMod K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hconj_mem, hconj_mem, Subgroup.mem_normalizer_iff.mp hsN (c⁻¹ * y * c)]
    have e : c⁻¹ * (s₀ * y * s₀⁻¹) * c = s * (c⁻¹ * y * c) * s⁻¹ := by
      rw [hs₀]; group
    rw [e]
  have hcV₁ : ∀ x : MulAut (PairMod K), x ∈ pairSL K → (V₁ K).map x.toMonoidHom = V₁ K := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := hx
    rw [pairHom_apply]
    exact map_V₁_pairAut _ _
  have hcV₂ : ∀ x : MulAut (PairMod K), x ∈ pairSL K → (V₂ K).map x.toMonoidHom = V₂ K :=
    fun x hx => map_V₂_eq (Subgroup.le_normalizer hx) (hcV₁ x hx)
  have hcomp : ∀ y z : MulAut (PairMod K), (y * z).toMonoidHom = y.toMonoidHom.comp z.toMonoidHom :=
    fun _ _ => rfl
  have hs₀V : (V₁ K).map s₀.toMonoidHom = V₂ K := by
    rw [hs₀, hcomp, hcomp, ← Subgroup.map_map, ← Subgroup.map_map,
      hcV₁ _ ((pairSL K).inv_mem hcL), hsV, hcV₂ _ hcL]
  have h21 : Q₀ = pairSL K → 21 ∣ Nat.card B₀ := by
    intro hQ₀eq
    rw [hB₀card]
    have hQeq : Q = pairSL K := by
      refine le_antisymm hQL fun x hx => ?_
      have h1 : c * x * c⁻¹ ∈ Q₀ := by
        rw [hQ₀eq]
        exact (pairSL K).mul_mem ((pairSL K).mul_mem hcL hx) ((pairSL K).inv_mem hcL)
      rw [hconj_mem] at h1
      simpa [mul_assoc] using h1
    have hLP : pairSL K ≤ P := hQeq ▸ inf_le_left
    obtain ⟨k, hk⟩ := hS.isPGroup.exists_card_eq
    have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
    have hcardP := card_sup_of_permute hBS (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have h168 : 168 ∣ Nat.card P := by
      rw [← card_pairSL hK]
      exact Subgroup.card_dvd_of_le hLP
    rw [hcardP, hk] at h168
    have h21' : (21 : ℕ) ∣ Nat.card B * 2 ^ k := (by norm_num : (21 : ℕ) ∣ 168).trans h168
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 21 2)).dvd_of_dvd_mul_right h21'
  have hB₀bot := eq_bot_of_flag hK hQ₀L hUQ₀ hB₀Q₀ (hB₀card ▸ hBodd) hB₀ab hs₀N hs₀V h21
  rw [eq_bot_iff]
  intro b hb
  have h1 : c * b * c⁻¹ ∈ B₀ := ⟨b, hb, rfl⟩
  rw [hB₀bot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc b = c⁻¹ * (c * b * c⁻¹) * c := by group
    _ = 1 := by rw [h1]; group

theorem nPrime_eq_one (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K) (hX3 : ∃ x ∈ X, x ∉ pairSub K) :
    E3.nPrime X = 1 := by
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  refine le_antisymm ?_ (E3.one_le_nPrime X)
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, -, hYc, hBab, hBodd, hS, hBS⟩
    have hB := eq_bot_of_permutes hK hX1 hX2 hX3 hBX hBab hBodd hS hBS
    have hY : Y = ⊥ := le_bot_iff.mp (hB ▸ hYB)
    rw [hY, Subgroup.card_bot] at hYc
    by_contra hc
    push Not at hc
    have h4 : 2 ^ 2 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
    omega

end NPrime

theorem H4_SL3One_nPrime {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) (hφM : φ ∈ M) :
    E3.nPrime M = 1 := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have h1 : pairSL K ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  have hX3 : ∃ x ∈ M.map (congrHom e), x ∉ pairSub K := by
    refine ⟨congrHom e φ, ⟨φ, hφM, rfl⟩, fun hx => ?_⟩
    obtain ⟨π, hπ⟩ := hreal'
    have hinv₁ : Pair.IsInv H V₁ := fun l hl w hw => hπ.2.2.2.1 ⟨l, hl⟩ w hw
    have hmodel : Pair.IsInv (pairSL K) (V₁.map e.toMonoidHom) := by
      intro l hl
      rw [← he] at hl
      obtain ⟨h, hh, rfl⟩ := hl
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨h w, hinv₁ h hh w hw, by simp⟩
    have hmap : (V₁.map φ.toMonoidHom).map e.toMonoidHom =
        (V₁.map e.toMonoidHom).map (congrHom e φ).toMonoidHom := by
      have hcomm : e.toMonoidHom.comp φ.toMonoidHom =
          (congrHom e φ).toMonoidHom.comp e.toMonoidHom :=
        MonoidHom.ext fun v => by
          show e (φ v) = congrHom e φ (e v)
          rw [congrHom_apply, MulEquiv.symm_apply_apply]
      rw [Subgroup.map_map, Subgroup.map_map, hcomm]
    have hinfe : (V₁.map e.toMonoidHom) ⊓ (V₁.map φ.toMonoidHom).map e.toMonoidHom = ⊥ := by
      rw [← Subgroup.map_inf V₁ (V₁.map φ.toMonoidHom) e.toMonoidHom e.injective, hinf,
        Subgroup.map_bot]
    have hxN : congrHom e φ ∈ pairNorm K := h2 ⟨φ, hφM, rfl⟩
    obtain ⟨a, b, hab⟩ := mem_pairSub_iff.mp hx
    have hx1 : (SL3Pair.V₁ K).map (congrHom e φ).toMonoidHom = SL3Pair.V₁ K := by
      rw [hab]; exact map_V₁_pairAut a b
    have hx2 := map_V₂_eq hxN hx1
    have hne : V₁.map e.toMonoidHom ≠ ⊥ := by
      intro h
      have hV₁ : V₁ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective V₁ e.injective).mp h
      have htop : (⊤ : Subgroup V) = ⊥ := by
        rw [← hsup, hV₁, Subgroup.map_bot, sup_bot_eq]
      have hc := congrArg (fun J : Subgroup V => Nat.card J) htop
      simp only [Subgroup.card_top, Subgroup.card_bot] at hc
      have hcardV : Nat.card V = 2 ^ 6 := (Nat.card_congr e.toEquiv).trans (card_pairMod_two hK2)
      rw [hcardV] at hc
      norm_num at hc
    rcases isInv_eq hmodel with h | h | h | h
    · exact hne h
    · rw [hmap, h, hx1, inf_idem] at hinfe
      exact isIrr_V₁.1 hinfe
    · rw [hmap, h, hx2, inf_idem] at hinfe
      exact isIrr_V₂.1 hinfe
    · rw [hmap, h, Subgroup.map_top_of_surjective _ (congrHom e φ).surjective, inf_idem] at hinfe
      exact isIrr_V₁.1 (le_bot_iff.mp (hinfe ▸ (le_top : SL3Pair.V₁ K ≤ ⊤)))
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq_one hK2 h1 h2 hX3


end SL3One

end H

end CFSG.Quasithin
