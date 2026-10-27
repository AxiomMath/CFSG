module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G}

private lemma zmod_two_mul : ∀ c : ZMod 3, (2 : ZMod 3) * c = -c := by
  decide +kernel

private lemma zmod_neg_one_mul : ∀ c : ZMod 3, (-1 : ZMod 3) * c = -c := by
  decide +kernel

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma zmod_add_neg_mul_one : ∀ a : ZMod 3, a + (-a) * 1 = 0 := by
  decide +kernel

private lemma zmod_add_smul_cancel : ∀ a t d : ZMod 3, (a + (-t) * d) + t * d = a := by
  decide +kernel

private lemma zmod_mul_neg_one : ∀ k : ZMod 3, k * -1 = -k := by
  decide +kernel

private lemma zmod_smul_natCast_val : ∀ a x : ZMod 3, a • x = (a.val : ℕ) • x := by
  decide +kernel

private lemma reflNorm_mul : ∀ v : Vec6, norm6 v = 1 → reflNorm v * reflNorm v = 1 := by
  decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma bil6_add_left (u₁ u₂ w : Vec6) :
    bil6 (u₁ + u₂) w = bil6 u₁ w + bil6 u₂ w := by
  simp only [bil6, add_dotProduct]

private lemma bil6_smul_left (a : ZMod 3) (u w : Vec6) :
    bil6 (a • u) w = a * bil6 u w := by
  simp only [bil6, smul_dotProduct, smul_eq_mul]

private lemma bil6_smul_right (b : ZMod 3) (u w : Vec6) :
    bil6 u (b • w) = b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma neg_eq_neg_one_smul (w : Vec6) : -w = (-1 : ZMod 3) • w := by
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [zmod_neg_one_mul]

private lemma bil6_neg_right (u w : Vec6) : bil6 u (-w) = -bil6 u w := by
  rw [neg_eq_neg_one_smul w, bil6_smul_right, zmod_neg_one_mul]

private lemma bil6_smul_smul (a b : ZMod 3) (u w : Vec6) :
    bil6 (a • u) (b • w) = a * b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private lemma ne_zero_of_norm {v : Vec6} (hv : norm6 v = 1) : v ≠ 0 := by
  intro h0
  rw [h0] at hv
  have h0' : norm6 (0 : Vec6) = 0 := by decide +kernel
  rw [h0'] at hv
  exact one_ne_zero hv.symm

private lemma fixed_eq_ker (v : Vec6) (hv : norm6 v = 1) :
    Fintype.card {u : Vec6 // (reflNorm v).mulVec u = u}
      = Fintype.card {u : Vec6 // bil6 u v = 0} := by
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  show (reflNorm v).mulVec u = u ↔ bil6 u v = 0
  rw [reflNorm_mulVec]
  constructor
  · intro h
    have h' : u + bil6 u v • v = u + 0 := by rw [add_zero]; exact h
    have hcv : bil6 u v • v = 0 := add_left_cancel h'
    exact (smul_eq_zero.mp hcv).resolve_right (ne_zero_of_norm hv)
  · intro h
    rw [h, zero_smul, add_zero]

private lemma card_ker (v : Vec6) (hv : norm6 v = 1) :
    Fintype.card {u : Vec6 // bil6 u v = 0} = 243 := by
  have hvv : bil6 v v = 1 := hv
  have hbij : Function.Bijective
      (fun p : {u : Vec6 // bil6 u v = 0} × ZMod 3 => (p.1 : Vec6) + p.2 • v) := by
    constructor
    · rintro ⟨⟨u₁, hu₁⟩, t₁⟩ ⟨⟨u₂, hu₂⟩, t₂⟩ h
      have hb := congrArg (fun w : Vec6 => bil6 w v) h
      simp only [bil6_add_left, bil6_smul_left] at hb
      rw [hu₁, hu₂, hvv, mul_one, mul_one, zero_add, zero_add] at hb
      subst hb
      have h2 : u₁ = u₂ := add_right_cancel h
      subst h2
      exact Prod.ext (Subtype.ext rfl) rfl
    · intro w
      refine ⟨(⟨w + (-(bil6 w v)) • v, ?_⟩, bil6 w v), ?_⟩
      · rw [bil6_add_left, bil6_smul_left, hvv]
        exact zmod_add_neg_mul_one (bil6 w v)
      · show (w + (-(bil6 w v)) • v) + bil6 w v • v = w
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact zmod_add_smul_cancel (w i) (bil6 w v) (v i)
  have hcard := Fintype.card_congr
    (Equiv.ofBijective (fun p : {u : Vec6 // bil6 u v = 0} × ZMod 3 =>
      (p.1 : Vec6) + p.2 • v) hbij)
  rw [Fintype.card_prod, ZMod.card 3] at hcard
  have hV : Fintype.card Vec6 = 729 := by decide +kernel
  rw [hV] at hcard
  omega

private lemma reflNorm_fixed_card (v : Vec6) (hv : norm6 v = 1) :
    Fintype.card {u : Vec6 // (reflNorm v).mulVec u = u} = 243 := by
  rw [fixed_eq_ker v hv]
  exact card_ker v hv

private lemma zmod_one_add_sq : ∀ k : ZMod 3, (1 + k) ^ 2 = 1 → k = 0 ∨ k = 1 := by
  decide +kernel

private lemma zmod_add_eq_self : ∀ a k : ZMod 3, a + k = a → k = 0 := by
  decide +kernel

private lemma zmod_neg_add_neg : ∀ a k : ZMod 3, -a + -k = a → k = a := by
  decide +kernel

private lemma ActsAs_injective {ι : Additive ↥Bs ≃+ Vec6} {φ ψ : MulAut ↥Bs} {g : Mat6}
    (h₁ : ActsAs ι φ g) (h₂ : ActsAs ι ψ g) : φ = ψ := by
  refine MulEquiv.ext fun b => ?_
  first
    | (apply Additive.ofMul.injective; apply ι.injective; rw [h₁ b, h₂ b])
    | (apply ι.injective; rw [h₁ b, h₂ b])

private lemma card_fixed_actsAs {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs} {g : Mat6}
    (h : ActsAs ι φ g) :
    Nat.card {b : ↥Bs // φ b = b} = Nat.card {u : Vec6 // g.mulVec u = u} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) fun b => ?_)
  show φ b = b ↔ g.mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b)
  exact ⟨fun hb => (h b).symm.trans (congrArg (fun x => ι (Additive.ofMul x)) hb),
    fun hb => Additive.ofMul.injective (ι.injective ((h b).trans hb))⟩

private lemma natCard_bs {ι : Additive ↥Bs ≃+ Vec6} : Nat.card ↥Bs = 729 := by
  rw [Nat.card_congr (Additive.ofMul.trans ι.toEquiv), Nat.card_eq_fintype_card]
  decide +kernel

private lemma isometry_bil6 {T : Mat6} (hiso : T.transpose * gram6 * T = gram6) (u w : Vec6) :
    bil6 (T.mulVec u) (T.mulVec w) = bil6 u w := by
  simp only [bil6]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.mul_assoc, hiso, ← Matrix.dotProduct_mulVec]

theorem actsAs_reflNorm {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs} {v : Vec6}
    (hv : norm6 v = 1) (h : ActsAs ι φ (reflNorm v)) :
    GGIsReflection 3 φ ∧ GGReflCentre φ (Additive.toMul (ι.symm v)) := by
  have hφsq : φ ^ 2 = 1 := by
    have h_one : ActsAs ι (1 : MulAut ↥Bs) (reflNorm v * reflNorm v) := by
      rw [reflNorm_mul v hv]
      exact ActsAs.one ι
    have hsq : φ * φ = 1 := ActsAs_injective (h.mul h) h_one
    simpa [pow_two] using hsq
  refine ⟨⟨hφsq, ?_⟩, ?_⟩
  · have hfixed := card_fixed_actsAs h
    have h243 : Nat.card {u : Vec6 // (reflNorm v).mulVec u = u} = 243 := by
      rw [Nat.card_eq_fintype_card]
      exact reflNorm_fixed_card v hv
    rw [hfixed, h243, natCard_bs (ι := ι)] <;> norm_num
  · intro b
    have hcv : ι (Additive.ofMul (Additive.toMul (ι.symm v))) = v := by
      rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    have hdiff : ι (Additive.ofMul (φ b * b⁻¹)) = bil6 (ι (Additive.ofMul b)) v • v := by
      rw [ofMul_mul, map_add, ofMul_inv, map_neg, h b, reflNorm_mulVec]
      abel
    have hcast : bil6 (ι (Additive.ofMul b)) v • v
        = ((bil6 (ι (Additive.ofMul b)) v).val) • v := by
      funext i
      change bil6 (ι (Additive.ofMul b)) v • v i
        = ((bil6 (ι (Additive.ofMul b)) v).val) • v i
      exact zmod_smul_natCast_val (bil6 (ι (Additive.ofMul b)) v) (v i)
    obtain ⟨k, hk⟩ : ∃ k : ℕ,
        φ b * b⁻¹ = (Additive.toMul (ι.symm v)) ^ k := by
      refine ⟨(bil6 (ι (Additive.ofMul b)) v).val, ?_⟩
      apply Additive.ofMul.injective
      apply ι.injective
      rw [ofMul_pow, map_nsmul, hcv, hdiff, hcast] <;> rfl
    rw [hk]
    exact Subgroup.npow_mem_zpowers _ _

theorem actsAs_eq_reflNorm {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs} {T : Mat6}
    (hT : ActsAs ι φ T) (hiso : T.transpose * gram6 * T = gram6) {c : ↥Bs}
    (hc : norm6 (ι (Additive.ofMul c)) = 1) (hr : GGIsReflection 3 φ)
    (hcentre : GGReflCentre φ c) : T = reflNorm (ι (Additive.ofMul c)) := by
  set v : Vec6 := ι (Additive.ofMul c) with hvdef
  have hv : norm6 v = 1 := hc
  have hvv : bil6 v v = 1 := hv
  have hcv : ι (Additive.ofMul c) = v := hvdef.symm
  have hiso' : ∀ u w : Vec6, bil6 (T.mulVec u) (T.mulVec w) = bil6 u w :=
    fun u w => isometry_bil6 hiso u w
  have key : ∀ u : Vec6, ∃ k : ZMod 3, T.mulVec u = u + k • v := by
    intro u
    set b : ↥Bs := Additive.toMul (ι.symm u) with hbdef
    have hb : ι (Additive.ofMul b) = u := by
      rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcentre b)
    have h4 : ι (Additive.ofMul (φ b * b⁻¹)) = T.mulVec u - u := by
      rw [ofMul_mul, map_add, ofMul_inv, map_neg, hT b, hb]
      abel
    have h3 : ι (Additive.ofMul (c ^ n)) = n • v := by
      rw [ofMul_zpow, map_zsmul, hcv] <;> rfl
    have hsub : T.mulVec u - u = n • v := by
      rw [← h4, ← hn, h3] <;> rfl
    have h5 : T.mulVec u = u + n • v := by
      have h := congrArg (fun x : Vec6 => x + u) hsub
      rw [sub_add_cancel] at h
      rw [add_comm] at h
      exact h
    have hcast : n • v = (n : ZMod 3) • v := by
      funext i
      change n • v i = (n : ZMod 3) • v i
      rw [zsmul_eq_mul, smul_eq_mul]
    refine ⟨(n : ZMod 3), ?_⟩
    rw [h5, hcast]
  obtain ⟨k₀, hk₀⟩ := key v
  have hk₀' : T.mulVec v = (1 + k₀) • v := by
    rw [hk₀, add_smul, one_smul] <;> rfl
  have hk₀sq : (1 + k₀) ^ 2 = 1 := by
    have h1 := hiso' v v
    rw [hk₀', bil6_smul_smul, hvv, mul_one] at h1
    simpa [pow_two] using h1
  rcases zmod_one_add_sq k₀ hk₀sq with hk0 | hk1
  ·
    exfalso
    have hTv : T.mulVec v = v := by
      rw [hk₀', hk0]
      simp
    have hfix : ∀ u : Vec6, T.mulVec u = u := by
      intro u
      obtain ⟨ku, hku⟩ := key u
      have h1 := hiso' u v
      rw [hku, hTv, bil6_add_left, bil6_smul_left, hvv, mul_one] at h1
      have hku0 : ku = 0 := zmod_add_eq_self (bil6 u v) ku h1
      rw [hku, hku0, zero_smul, add_zero] <;> rfl
    have hfixφ : ∀ b : ↥Bs, φ b = b := by
      intro b
      have hb := hT b
      rw [hfix (ι (Additive.ofMul b))] at hb
      exact Additive.ofMul.injective (ι.injective hb)
    have hcardeq : Nat.card {b : ↥Bs // φ b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hfixφ)
    have hthis := hr.2
    rw [hcardeq, natCard_bs (ι := ι)] at hthis
    omega
  ·
    have hTv : T.mulVec v = -v := by
      rw [hk₀', hk1]
      show (2 : ZMod 3) • v = -v
      funext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      rw [zmod_two_mul]
    have hku_eq : ∀ u : Vec6, T.mulVec u = u + bil6 u v • v := by
      intro u
      obtain ⟨ku, hku⟩ := key u
      have h1 := hiso' u v
      rw [hku, hTv, bil6_add_left, bil6_smul_left, bil6_neg_right u v, bil6_neg_right v v,
        hvv, zmod_mul_neg_one] at h1
      have hku' : ku = bil6 u v := zmod_neg_add_neg (bil6 u v) ku h1
      rw [hku, hku'] <;> rfl
    have hfun : T.mulVec = (reflNorm v).mulVec := by
      funext u
      rw [hku_eq u, reflNorm_mulVec u v] <;> rfl
    exact Matrix.mulVec_injective hfun

end E6Dep

end CFSG.StandardType

end
