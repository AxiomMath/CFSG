module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishPair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement Matrix

namespace Om10

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_Wt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hom : OmegaPlusNat hc t 5) (hn : n = 18) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ 16 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hVU, hWQ1⟩ := stroth310Chi_of_34 h34 G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  have hUt : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc t) * Nat.card ↥(Ut Q Z t) := by
    haveI : (Z.subgroupOf (Ut Q Z t)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q (hc.LB_le_M ht) hv)))
    exact card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut ht) (fun x hx => hx.1)
      (le_sup_right : Z ≤ Ut Q Z t)
  rw [← hWQ1, ← hVU] at hUt
  have hv := card_Vt_orthogonal hc (m := 5) (by norm_num) (Or.inl hom)
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  rw [hQc, hn, hv] at hUt
  rw [hv]
  have hpos : 0 < Nat.card ↥Z * Nat.card ↥Z ^ (2 * 5) := by
    have : 0 < Nat.card ↥Z := Nat.card_pos
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← hUt]
  ring

omit [Finite G] in
theorem pair_facts_of_mem {Q V A A' : Subgroup G} {x a : G} (hZQ : ∀ q ∈ Q, ∀ q' ∈ Q, ⁅q, q'⁆ ∈ V)
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hx2 : x ^ 2 ∈ Q)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hVA : V ≤ A) (hA'W : A' ≤ Wt Q V)
    (hinf : A ⊓ A' = V) (hsw : conjSubgroup x A = A') (haA : a ∈ A) (haW : a ∈ Wt Q V)
    (haV : a ∉ V) :
    ⁅x, a⁆ ∉ V ∧ a * (x * a * x⁻¹) ∈ fixSec Q V x ∧ a * (x * a * x⁻¹) ∉ V := by
  have hxa : x * a * x⁻¹ ∈ A' := by
    rw [← hsw, mem_conjSubgroup]
    have e : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [e]
    exact haA
  have hback : x * a * x⁻¹ ∈ A → False := by
    intro h
    have hV : x * a * x⁻¹ ∈ V := by
      rw [← hinf]
      exact ⟨h, hxa⟩
    apply haV
    have := (Subgroup.mem_normalizer_iff.mp hxV a).mpr hV
    exact this
  have haQ : a ∈ Q := haW.1
  have hbQ : x * a * x⁻¹ ∈ Q := hxQ a haQ
  refine ⟨fun hc => hback ?_, ⟨(Wt Q V).mul_mem haW (hA'W hxa), ?_⟩, fun hy => hback ?_⟩
  · have e : x * a * x⁻¹ = ⁅x, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem (hVA hc) haA
  · have hx2a : ⁅x ^ 2, a⁆ ∈ V := hZQ _ hx2 _ haQ
    have hba : ⁅x * a * x⁻¹, a⁆ ∈ V := hZQ _ hbQ _ haQ
    have e : ⁅x, a * (x * a * x⁻¹)⁆ =
        ((x * a * x⁻¹) * ⁅x ^ 2, a⁆ * (x * a * x⁻¹)⁻¹) * ⁅x * a * x⁻¹, a⁆ := by
      simp only [commutatorElement_def, pow_two]
      group
    rw [e]
    refine V.mul_mem ?_ hba
    have hbW : x * a * x⁻¹ ∈ Wt Q V := hA'W hxa
    rw [mul_comm_of_mem_Wt hbW hx2a, mul_inv_cancel_right]
    exact hx2a
  · have e : x * a * x⁻¹ = a⁻¹ * (a * (x * a * x⁻¹)) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem haA) (hVA hy)

theorem pair_facts (hPair : Step71VanishPairStatement) (h52b : Stroth52bStatement)
    (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hno : ¬ Conc71abcd hc n t) (hom : OmegaPlusNat hc t 5) (hn : n = 18) {x : G}
    (hx : ConjMod M Q t x) (hxt : ⁅x, t⁆ ∈ Q) (hmov : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) :
    (∃ a ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, a⁆ ∉ Vt M (LB M Q B) B Z t) ∧
      ∃ y ∈ fixSec Q (Vt M (LB M Q B) B Z t) x, y ∉ Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxM : x ∈ M := hx.1
  obtain ⟨-, hx2⟩ := conjMod_facts hc ht hx
  obtain ⟨h, hh, r, hr, hplane, hpair⟩ := hPair G M Q Z B hc n t hs hno x hx hxt hmov
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hd := opp_of_frame h52b hc hs hh hr hplane
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxQn : x ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hxM
  have hxWn : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), x * w * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun w hw => conj_mem_Wt hxQn hxVn hw
  have hxWn' : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x⁻¹ * w * x ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun w hw => by
    have := conj_mem_Wt (Subgroup.inv_mem _ hxQn) (Subgroup.inv_mem _ hxVn) hw
    simpa using this
  have hxVc : ∀ y ∈ Vt M (LB M Q B) B Z t, x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp hxVn y).mp hy
  have hxVc' : ∀ y ∈ Vt M (LB M Q B) B Z t, x⁻¹ * y * x ∈ Vt M (LB M Q B) B Z t :=
    fun y hy => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxVn) y).mp hy
      simpa using this
  have hpair' : conjSubgroup (x * h) B ⊔ Z = conjSubgroup (r * h) B ⊔ Z := by
    rw [conjSubgroup_mul, conjSubgroup_mul]
    exact hpair
  have hxL : conjSubgroup x (conjSubgroup h (LB M Q B)) = conjSubgroup (r * h) (LB M Q B) := by
    rw [← conjSubgroup_mul]
    exact hc.conj_LB_eq_of_conj_BZ (M.mul_mem hxM hhM) (M.mul_mem hrM hhM) hpair'
  have hsw := conjSubgroup_eq_of_isOppDecomp hd hxL hxWn hxWn' hxVc hxVc'
  obtain ⟨hVA, hAW, -, hA'W, hsup, hinf, -⟩ := hd
  have hAV : (QB (conjSubgroup h B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t ≠
      Vt M (LB M Q B) B Z t := by
    intro hAV
    have hA'V : (QB (conjSubgroup r (conjSubgroup h B)) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t = Vt M (LB M Q B) B Z t := by
      rw [← hsw, hAV]
      exact conjSubgroup_eq_self_iff.mpr hxVn
    rw [hAV, hA'V, sup_idem] at hsup
    have hcW := card_Wt h34 hc hs hom hn
    rw [← hsup] at hcW
    have hq : 1 < Nat.card Z ^ 16 := by
      have : 4 ≤ Nat.card Z := hc.hyp.q4
      exact Nat.one_lt_pow (by norm_num) (by omega)
    have hV0 : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
    nlinarith
  obtain ⟨a, haA, haV⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hVA (Ne.symm hAV))
  have hZQ : ∀ q ∈ Q, ∀ q' ∈ Q, ⁅q, q'⁆ ∈ Vt M (LB M Q B) B Z t := fun q hq q' hq' =>
    sec39_Z_le_Vt (CFSG.RankThree.GF2n.Smith81.comm_mem_Z hc.hyp hq hq')
  have hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hxQn q).mp hq
  obtain ⟨h1, h2, h3⟩ := pair_facts_of_mem hZQ hxQ hx2 hxVn hVA hA'W hinf hsw haA (hAW haA) haV
  exact ⟨⟨a, hAW haA, h1⟩, ⟨_, h2, h3⟩⟩

section Coord

variable {t : G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K} [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)}

theorem comm_mem_CN (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B)
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) (F : (ι → K) →ₗ[K] (ι → K))
    (hF : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      F (secVec ψ k) = secVec ψ k')
    (hFF : ∀ w, F (F w) = w) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hcomm : ∀ w, F ((φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ w) = (φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ F w) :
    ⁅x, r⁆ ∈ hc.CN t := by
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hxM hxt)) y).mp hy
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxVn v).mp hv
  have hxV' : ∀ v ∈ Vt M (LB M Q B) B Z t, x⁻¹ * v * x ∈ Vt M (LB M Q B) B Z t := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxVn) v).mp hv
    simpa using this
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hFinv : ∀ k : ↥(Vt M (LB M Q B) B Z t),
      secVec ψ ⟨x⁻¹ * k * x, hxV' k k.2⟩ = F (secVec ψ k) := by
    intro k
    have h1 := hF ⟨x⁻¹ * k * x, hxV' k k.2⟩ k (by simp [mul_assoc])
    rw [← h1, hFF]
  have hrinv : r⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hr
  have hφinv : ∀ w, (φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ ((φ ⟨r⁻¹, hrinv⟩ : Matrix ι ι K) *ᵥ w) = w := by
    intro w
    have e : (⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) * ⟨r⁻¹, hrinv⟩ = 1 := Subtype.ext (mul_inv_cancel r)
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, ← map_mul, e, map_one,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Ctx.mem_CN]
  refine ⟨?_, fun v hv => ?_⟩
  · have e : ⁅x, r⁆ = (x * r * x⁻¹) * r⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem (hxR r hr) hrinv
  ·
    set k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨r⁻¹ * v * r, by
      have := hVR r⁻¹ hrinv v hv
      simpa using this⟩ with hk₁
    set k₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x⁻¹ * k₁ * x, hxV' k₁ k₁.2⟩ with hk₂
    set k₃ : ↥(Vt M (LB M Q B) B Z t) := ⟨r * k₂ * r⁻¹, hVR r hr k₂ k₂.2⟩ with hk₃
    set k₄ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k₃ * x⁻¹, hxV k₃ k₃.2⟩ with hk₄
    have e1 : secVec ψ k₁ = (φ ⟨r⁻¹, hrinv⟩ : Matrix ι ι K) *ᵥ secVec ψ ⟨v, hv⟩ :=
      hψ ⟨r⁻¹, hrinv⟩ ⟨v, hv⟩ k₁ (by simp [hk₁])
    have e2 : secVec ψ k₂ = F (secVec ψ k₁) := hFinv k₁
    have e3 : secVec ψ k₃ = (φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ secVec ψ k₂ :=
      hψ ⟨r, hr⟩ k₂ k₃ rfl
    have e4 : secVec ψ k₄ = F (secVec ψ k₃) := (hF k₃ k₄ rfl).symm
    have hk4v : secVec ψ k₄ = secVec ψ ⟨v, hv⟩ := by
      rw [e4, e3, e2, e1, hcomm, hFF, hφinv]
    have h := (secVec_eq_iff ψ k₄ ⟨v, hv⟩).mp hk4v
    have e : ⁅⁅x, r⁆, v⁆ = (k₄ : G) * v⁻¹ := by
      simp only [hk₄, hk₃, hk₂, hk₁, commutatorElement_def]
      group
    rw [e]
    exact h

theorem conj_BZ_eq (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B)
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) (F : (ι → K) →ₗ[K] (ι → K))
    (hF : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      F (secVec ψ k) = secVec ψ k')
    {Q' : QuadraticForm K (ι → K)} {a : ι → K} (hFa : ∀ v, F v = v + polar Q' v a • a)
    {u : ι → K} (hBu : ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → ∃ c : K, secVec ψ b = c • u)
    {h : G} (hh : h ∈ Rt M (LB M Q B) t)
    (hpol : polar Q' ((φ ⟨h, hh⟩ : Matrix ι ι K) *ᵥ u) a = 0) :
    conjSubgroup (x * h) B ⊔ Z = conjSubgroup h B ⊔ Z := by
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxVn v).mp hv
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hle : conjSubgroup (x * h) B ⊔ Z ≤ conjSubgroup h B ⊔ Z := by
    refine sup_le (fun y hy => ?_) le_sup_right
    have hb : (x * h)⁻¹ * y * (x * h) ∈ B := mem_conjSubgroup.mp hy
    set b := (x * h)⁻¹ * y * (x * h) with hbdef
    have hbV : b ∈ Vt M (LB M Q B) B Z t := hBV hb
    set k : ↥(Vt M (LB M Q B) B Z t) := ⟨h * b * h⁻¹, hVR h hh b hbV⟩ with hk
    have hyk : y = x * k * x⁻¹ := by
      simp only [hk, hbdef]
      group
    have hyV : y ∈ Vt M (LB M Q B) B Z t := by rw [hyk]; exact hxV k k.2
    obtain ⟨c, hc'⟩ := hBu ⟨b, hbV⟩ hb
    have hvk : secVec ψ k = c • ((φ ⟨h, hh⟩ : Matrix ι ι K) *ᵥ u) := by
      have e1 : secVec ψ k = (φ ⟨h, hh⟩ : Matrix ι ι K) *ᵥ secVec ψ ⟨b, hbV⟩ :=
        hψ ⟨h, hh⟩ ⟨b, hbV⟩ k rfl
      rw [e1, hc', Matrix.mulVec_smul]
    have hvy : secVec ψ ⟨y, hyV⟩ = secVec ψ k := by
      rw [← hF k ⟨y, hyV⟩ hyk, hFa, hvk, polar_smul_left_eq, hpol, mul_zero, zero_smul, add_zero]
    have hkB : (k : G) ∈ conjSubgroup h B ⊔ Z := by
      refine Subgroup.mem_sup_left (mem_conjSubgroup.mpr ?_)
      have e : h⁻¹ * (h * b * h⁻¹) * h = b := by group
      rw [hk]
      simpa [e] using hb
    exact mem_of_secVec_eq (le_sup_right : Z ≤ conjSubgroup h B ⊔ Z) ψ (w := k)
      (y := ⟨y, hyV⟩) hkB hvy.symm
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  have e : conjSubgroup (x * h) B ⊔ Z = conjSubgroup x (conjSubgroup h B ⊔ Z) := by
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_mul, hc.conj_Z_eq hxM]
  rw [e, card_conjSubgroup]

end Coord

end Om10

end CFSG.RankThree.GF2n.Stroth80
