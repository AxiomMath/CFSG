module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Cent

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
open scoped Pointwise

section NoTrivial

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [Finite Q] [MulDistribMulAction A Q]

omit [Finite Q] in
private theorem toSubmod_eq_top_of_iSup {ι : Type*} {S : ι → Subgroup Q}
    (hS : ∀ i, XMod.IsInv A (S i)) (htop : (⨆ i, S i) = ⊤) :
    (⨆ i, XMod.toSubmod (hS i)) = ⊤ := by
  rw [← XMod.toSubmod_iSup hS, eq_top_iff]
  intro p _
  show Additive.toMul p ∈ ⨆ i, S i
  rw [htop]
  trivial

private theorem exists_isIrr_le' {B : Subgroup Q} (hB : XMod.IsInv A B) (hne : B ≠ ⊥) :
    ∃ S ≤ B, XMod.IsIrr A S := by
  classical
  obtain ⟨S, ⟨hSB, hSinv, hSne⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup Q))
    {J : Subgroup Q | J ≤ B ∧ XMod.IsInv A J ∧ J ≠ ⊥} ⟨B, le_rfl, hB, hne⟩
  refine ⟨S, hSB, hSinv, bot_lt_iff_ne_bot.2 hSne, fun J hJ _ hJS => ?_⟩
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · right
    by_contra hne'
    exact hmin J ⟨hJS.trans hSB, hJ, hJ0⟩ (lt_of_le_of_ne hJS hne')

theorem commOf_eq_of_le_iSup {ι : Type*} {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr A (S i))
    (hSc : ∀ i, XMod.commOf A (S i) = S i) (htop : (⨆ i, S i) = ⊤) {R : Subgroup Q}
    (hR : XMod.IsInv A R) : XMod.commOf A R = R := by
  classical
  have hinv : ∀ i, XMod.IsInv A (S i) := fun i => (hS i).1
  have : IsSemisimpleModule ↥(XMod.opRing A Q) (Additive Q) := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun i => XMod.toSubmod (hinv i)) (fun i => ?_) (toSubmod_eq_top_of_iSup hinv htop)
    have := (XMod.isIrr_iff (hinv i)).1 (hS i)
    infer_instance
  set C := XMod.commOf A R with hCdef
  have hC : XMod.IsInv A C := XMod.isInv_commOf R
  have hCR : C ≤ R := XMod.commOf_le_of_isInv hR
  obtain ⟨D₀, hD₀⟩ := exists_isCompl (XMod.toSubmod hC)
  set D := D₀ ⊓ XMod.toSubmod hR with hDdef
  have hCD : XMod.toSubmod hC ⊓ D = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ inf_le_left).trans hD₀.inf_eq_bot.le)
  have hCDR : XMod.toSubmod hC ⊔ D = XMod.toSubmod hR := by
    rw [hDdef, ← sup_inf_assoc_of_le D₀ (XMod.toSubmod_le_iff.2 hCR), hD₀.sup_eq_top, top_inf_eq]
  set Dg := XMod.ofSubmod D with hDg
  have hDginv : XMod.IsInv A Dg := XMod.isInv_ofSubmod D
  have hDgR : Dg ≤ R := fun q hq => (inf_le_right : D ≤ XMod.toSubmod hR) hq
  have hDgfix : Dg ≤ XMod.fixed A ⊤ := by
    intro d hd
    refine ⟨trivial, fun a => ?_⟩
    have h1 : (a • d) * d⁻¹ ∈ C := XMod.mem_commOf_of_mem a (hDgR hd)
    have h2 : (a • d) * d⁻¹ ∈ Dg := Dg.mul_mem (hDginv a d hd) (Dg.inv_mem hd)
    have h3 : Additive.ofMul ((a • d) * d⁻¹) ∈ XMod.toSubmod hC ⊓ D := ⟨h1, h2⟩
    rw [hCD, Submodule.mem_bot] at h3
    have h4 : (a • d) * d⁻¹ = 1 := h3
    exact mul_inv_eq_one.1 h4
  have hDgbot : Dg = ⊥ := by
    by_contra hne
    obtain ⟨J, hJD, hJ⟩ := exists_isIrr_le' hDginv hne
    obtain ⟨i, hi⟩ := exists_iso_of_le_iSup hS hJ (htop ▸ le_top)
    have h1 : XMod.commOf A J = J := XMod.commOf_eq_of_iso (hS i) hJ hi (hSc i)
    have h2 : XMod.commOf A J = ⊥ := XMod.commOf_eq_bot_iff.2 (hJD.trans hDgfix)
    exact hJ.2.1.ne (h2.symm.trans h1)
  have hD : D = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have : Additive.toMul p ∈ Dg := hp
    rw [hDgbot, Subgroup.mem_bot] at this
    exact (Submodule.mem_bot _).2 this
  rw [hD, sup_bot_eq] at hCDR
  exact XMod.toSubmod_injective hCDR

omit [Finite Q] in
private theorem commOf_eq_of_surj {A' : Type*} [Group A'] [MulDistribMulAction A' Q]
    (φ : A' → A) (hφ : Function.Surjective φ) (hact : ∀ (a : A') (q : Q), a • q = φ a • q)
    (R : Subgroup Q) : XMod.commOf A' R = XMod.commOf A R := by
  unfold XMod.commOf
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨φ a, l, hl, by rw [hact]⟩
  · rintro ⟨a, l, hl, rfl⟩
    obtain ⟨a', rfl⟩ := hφ a
    exact ⟨a', l, hl, by rw [hact]⟩

theorem commOf_eq_of_iSup_smul {Γ : Type*} [Group Γ] [MulDistribMulAction Γ Q] {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V)
    (hVc : XMod.commOf ↥Λ V = V) (hgen : (⨆ g : Γ, g • V) = ⊤) {R : Subgroup Q}
    (hR : XMod.IsInv ↥Λ R) : XMod.commOf ↥Λ R = R := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have hnorm : ∀ g : Γ, g ∈ Subgroup.normalizer (Λ : Set Γ) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hΛ g h hh, fun hh => ?_⟩
    have := hΛ g⁻¹ _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  refine commOf_eq_of_le_iSup (S := fun g : Γ => g • V) (fun g => isIrr_smul hN g hV)
    (fun g => ?_) hgen hR
  have h1 := smul_modComm (V := Q) (hnorm g) V
  change g • XMod.commOf ↥Λ V = XMod.commOf ↥Λ (g • V) at h1
  rw [← h1, hVc]

end NoTrivial

section Numerics

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem fixed_anti {A B : Subgroup Γ} (hBA : B ≤ A) :
    XMod.fixed ↥A (⊤ : Subgroup Q) ≤ XMod.fixed ↥B ⊤ :=
  fun _ hq => ⟨trivial, fun b => hq.2 ⟨b, hBA b.2⟩⟩

theorem nB_eq_add_of_le [Finite Q] {A B : Subgroup Γ} (hBA : B ≤ A) (S : Subgroup Q) :
    nB A S = nB B S + nB A (S ⊓ XMod.fixed ↥B ⊤) := by
  unfold nB
  set FA := XMod.fixed ↥A (⊤ : Subgroup Q) with hFA
  set FB := XMod.fixed ↥B (⊤ : Subgroup Q) with hFB
  have h1 : S ⊓ FB ⊓ FA = S ⊓ FA := by
    rw [inf_assoc, inf_eq_right.2 (fixed_anti hBA)]
  rw [h1]
  have h2 : rk ↥(S ⊓ FA) ≤ rk ↥(S ⊓ FB) := rk_mono (inf_le_inf_left _ (fixed_anti hBA))
  have h3 : rk ↥(S ⊓ FB) ≤ rk ↥S := rk_mono inf_le_left
  omega

theorem nB_le_of_le [Finite Q] {A B : Subgroup Γ} (hBA : B ≤ A) (S : Subgroup Q) :
    nB B S ≤ nB A S := by
  rw [nB_eq_add_of_le hBA S]
  exact Nat.le_add_right _ _

theorem mem_fixed_zpowers_iff {b : Γ} {q : Q} :
    q ∈ XMod.fixed ↥(Subgroup.zpowers b) (⊤ : Subgroup Q) ↔ b • q = q := by
  constructor
  · intro h
    exact h.2 ⟨b, Subgroup.mem_zpowers b⟩
  · intro h
    refine ⟨trivial, fun g => ?_⟩
    have hle : Subgroup.zpowers b ≤ MulAction.stabilizer Γ q :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
    exact MulAction.mem_stabilizer_iff.1 (hle g.2)

theorem rk_le_two_mul_rk_fixed [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {b : Γ} (hb : b ^ 2 = 1)
    {R : Subgroup Q} (hRb : ∀ r ∈ R, b • r ∈ R) :
    rk ↥R ≤ 2 * rk ↥(R ⊓ XMod.fixed ↥(Subgroup.zpowers b) ⊤) := by
  set F := R ⊓ XMod.fixed ↥(Subgroup.zpowers b) (⊤ : Subgroup Q) with hF
  let f : Q →* Q := MonoidHom.mk' (fun q => (b • q) * q⁻¹) (fun x y => by
    simp only [smul_mul', mul_inv_rev]
    ac_rfl)
  have hf : ∀ q, f q = (b • q) * q⁻¹ := fun _ => rfl
  have hinv : ∀ q : Q, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_left (by rw [← pow_two, hQ])
  have hker : R ⊓ f.ker = F := by
    ext q
    simp only [hF, Subgroup.mem_inf, MonoidHom.mem_ker, hf, mul_inv_eq_one,
      mem_fixed_zpowers_iff]
  have hmap : R.map f ≤ F := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨R.mul_mem (hRb r hr) (R.inv_mem hr), mem_fixed_zpowers_iff.2 ?_⟩
    rw [hf, smul_mul', smul_inv', smul_smul, ← pow_two, hb, one_smul, hinv (b • r), hinv r,
      mul_comm]
  have h1 := B1More.card_map_mul_card_inf_ker R f
  have h2 : rk ↥(R.map f) + rk ↥(R ⊓ f.ker) = rk ↥R := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  rw [hker] at h2
  have h3 : rk ↥(R.map f) ≤ rk ↥F := rk_mono hmap
  omega

theorem two_mul_rk_inf_fixed_eq [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {x a : Γ} (ha2 : a ^ 2 = 1)
    (hax : a * x * a⁻¹ = x⁻¹) {R : Subgroup Q} (hRx : ∀ r ∈ R, x • r ∈ R)
    (hRa : ∀ r ∈ R, a • r ∈ R) (hfix : ∀ r ∈ R, x • r = r → r = 1) :
    2 * rk ↥(R ⊓ XMod.fixed ↥(Subgroup.zpowers a) ⊤) = rk ↥R := by
  have hainv : a⁻¹ = a := inv_eq_iff_mul_eq_one.2 (by rw [← pow_two, ha2])
  have hb2 : (a * x) ^ 2 = 1 := by
    rw [pow_two, show a * x * (a * x) = a * x * a⁻¹ * x by rw [hainv]; group, hax,
      inv_mul_cancel]
  have hRb : ∀ r ∈ R, (a * x) • r ∈ R := fun r hr => by
    rw [mul_smul]
    exact hRa _ (hRx r hr)
  set Fa := R ⊓ XMod.fixed ↥(Subgroup.zpowers a) (⊤ : Subgroup Q) with hFa
  set Fb := R ⊓ XMod.fixed ↥(Subgroup.zpowers (a * x)) (⊤ : Subgroup Q) with hFb
  have h1 : rk ↥R ≤ 2 * rk ↥Fa := rk_le_two_mul_rk_fixed hQ ha2 hRa
  have h2 : rk ↥R ≤ 2 * rk ↥Fb := rk_le_two_mul_rk_fixed hQ hb2 hRb
  have hdisj : Fa ⊓ Fb = ⊥ := by
    rw [eq_bot_iff]
    intro r hr'
    have hr : r ∈ R := hr'.1.1
    have hra : a • r = r := mem_fixed_zpowers_iff.1 hr'.1.2
    have hrb : (a * x) • r = r := mem_fixed_zpowers_iff.1 hr'.2.2
    rw [mul_smul] at hrb
    have h3 : x • r = r := by
      have := congrArg (fun q => a⁻¹ • q) hrb
      simp only [inv_smul_smul] at this
      rw [this, hainv, hra]
    exact (Subgroup.mem_bot).2 (hfix r hr h3)
  have h4 := rk_sup_add_rk_inf Fa Fb
  rw [hdisj, rk_bot] at h4
  have h5 : rk ↥(Fa ⊔ Fb) ≤ rk ↥R := rk_mono (sup_le inf_le_left inf_le_left)
  omega

theorem two_mul_nB_zpowers_eq [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {x a : Γ} (ha2 : a ^ 2 = 1)
    (hax : a * x * a⁻¹ = x⁻¹) {R : Subgroup Q} (hRx : ∀ r ∈ R, x • r ∈ R)
    (hRa : ∀ r ∈ R, a • r ∈ R) (hfix : ∀ r ∈ R, x • r = r → r = 1) :
    2 * nB (Subgroup.zpowers a) R = rk ↥R := by
  have h := two_mul_rk_inf_fixed_eq hQ ha2 hax hRx hRa hfix
  unfold nB
  omega

theorem eq_one_of_mem_commOf_of_fix (hQ : ∀ q : Q, q ^ 2 = 1) {y : Γ} (hy3 : y ^ 3 = 1)
    {S : Subgroup Q} {r : Q} (hr : r ∈ XMod.commOf ↥(Subgroup.zpowers y) S) (hyr : y • r = r) :
    r = 1 := by
  let f : Q →* Q := MonoidHom.mk' (fun q => q * (y • q) * (y ^ 2 • q)) (fun a b => by
    simp only [smul_mul']
    ac_rfl)
  have hf : ∀ q, f q = q * (y • q) * (y ^ 2 • q) := fun _ => rfl
  have hfix : ∀ q, y • f q = f q := by
    intro q
    have h3 : y • y ^ 2 • q = q := by rw [smul_smul, ← pow_succ', hy3, one_smul]
    have h2 : y • y • q = y ^ 2 • q := by rw [smul_smul, ← pow_two]
    rw [hf, smul_mul', smul_mul', h2, h3]
    ac_rfl
  have hker : XMod.commOf ↥(Subgroup.zpowers y) S ≤ f.ker := by
    rw [XMod.commOf_le_iff]
    intro g s _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    have hgf : ∀ q : Q, (g : Γ) • f q = f q := by
      intro q
      have hle : Subgroup.zpowers y ≤ MulAction.stabilizer Γ (f q) :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 (hfix q))
      exact MulAction.mem_stabilizer_iff.1 (hle g.2)
    have hgy : Commute (g : Γ) y := by rw [← hn]; exact (Commute.self_zpow y n).symm
    have hc1 : ∀ q : Q, y • (g : Γ) • q = (g : Γ) • y • q := fun q => by
      rw [smul_smul, smul_smul, hgy.eq]
    have hc2 : ∀ q : Q, y ^ 2 • (g : Γ) • q = (g : Γ) • y ^ 2 • q := fun q => by
      rw [smul_smul, smul_smul, (hgy.pow_right 2).eq]
    have hcomm : ∀ q : Q, f ((g : Γ) • q) = (g : Γ) • f q := by
      intro q
      rw [hf, hf, hc1, hc2, smul_mul', smul_mul']
    show f (((g : Γ) • s) * s⁻¹) = 1
    rw [map_mul, map_inv, hcomm, hgf, mul_inv_cancel]
  have h1 : f r = 1 := hker hr
  rw [hf, hyr, show y ^ 2 • r = r by rw [pow_two, mul_smul, hyr, hyr]] at h1
  have h2 : r * r = 1 := by rw [← pow_two, hQ]
  rw [h2, one_mul] at h1
  exact h1

end Numerics

section Thompson

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private def resAutOf (R : Subgroup Q) (g : Γ) (hg : ∀ r ∈ R, g • r ∈ R)
    (hg' : ∀ r ∈ R, g⁻¹ • r ∈ R) : MulAut ↥R where
  toFun r := ⟨g • (r : Q), hg r r.2⟩
  invFun r := ⟨g⁻¹ • (r : Q), hg' r r.2⟩
  left_inv r := Subtype.ext (inv_smul_smul g (r : Q))
  right_inv r := Subtype.ext (smul_inv_smul g (r : Q))
  map_mul' r s := Subtype.ext (smul_mul' g (r : Q) s)

theorem fix_of_fix_fixed [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {E : Subgroup Γ}
    (hE : IsPGroup 2 E) {y : Γ} {k : ℕ} (hk : Odd k) (hyk : y ^ k = 1)
    (hyE : ∀ e ∈ E, y * e = e * y) {R : Subgroup Q} (hRE : ∀ e ∈ E, ∀ r ∈ R, e • r ∈ R)
    (hRy : ∀ r ∈ R, y • r ∈ R) (hy : ∀ r ∈ R, (∀ e ∈ E, e • r = r) → y • r = r) :
    ∀ r ∈ R, y • r = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk1 : 1 ≤ k := hk.pos
  have hRyn : ∀ n : ℕ, ∀ r ∈ R, y ^ n • r ∈ R := by
    intro n
    induction n with
    | zero => intro r hr; rwa [pow_zero, one_smul]
    | succ n ih => intro r hr; rw [pow_succ, mul_smul]; exact ih _ (hRy r hr)
  have hyinv : y⁻¹ = y ^ (k - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hk1, hyk]
  have hRy' : ∀ r ∈ R, y⁻¹ • r ∈ R := fun r hr => by rw [hyinv]; exact hRyn _ r hr
  let yR : MulAut ↥R := resAutOf R y hRy hRy'
  let β : ↥E →* MulAut ↥R :=
    { toFun := fun e => resAutOf R (e : Γ) (hRE e e.2) (hRE _ (E.inv_mem e.2))
      map_one' := MulEquiv.ext fun r => Subtype.ext (one_smul Γ (r : Q))
      map_mul' := fun e e' => MulEquiv.ext fun r => Subtype.ext (mul_smul (e : Γ) e' (r : Q)) }
  have hβ : ∀ (e : ↥E) (r : ↥R), ((β e r : ↥R) : Q) = (e : Γ) • (r : Q) := fun _ _ => rfl
  have hyRpow : ∀ (n : ℕ) (r : ↥R), (((yR ^ n) r : ↥R) : Q) = y ^ n • (r : Q) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hyRk : yR ^ k = 1 := MulEquiv.ext fun r => Subtype.ext (by rw [hyRpow, hyk, one_smul]; rfl)
  set A : Subgroup (MulAut ↥R) := Subgroup.zpowers yR with hA
  set B : Subgroup (MulAut ↥R) := β.range with hB
  have hR2 : IsPGroup 2 ↥R :=
    (isPGroup_two_of_sq_eq_one hQ).to_subgroup R
  have hA2 : ¬ 2 ∣ Nat.card ↥A := by
    rw [hA, Nat.card_zpowers]
    intro h2
    have h3 : orderOf yR ∣ k := orderOf_dvd_of_pow_eq_one hyRk
    exact (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 (h2.trans h3))
  have hB2 : IsPGroup 2 ↥B := hE.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hcomm1 : ∀ e : ↥E, yR * β e = β e * yR := by
    intro e
    refine MulEquiv.ext fun r => Subtype.ext ?_
    change y • (e : Γ) • (r : Q) = (e : Γ) • y • (r : Q)
    rw [smul_smul, smul_smul, hyE e e.2]
  have key := CFSG.GroupTheory.thompson_A_times_B (p := 2) hR2 hA2 hB2 A.subtype B.subtype
    (fun a b => by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨e, he⟩ := b.2
      change (a : MulAut ↥R) * b = b * a
      rw [← hn, ← he]
      exact ((Commute.zpow_left (hcomm1 e) n)).eq)
    (fun a r hr => by
      have hrE : ∀ e ∈ E, e • (r : Q) = r := fun e he => by
        have := hr ⟨β ⟨e, he⟩, ⟨e, he⟩, rfl⟩
        exact congrArg Subtype.val this
      have hyr : yR r = r := Subtype.ext (hy r r.2 hrE)
      have hle : A ≤ MulAction.stabilizer (MulAut ↥R) r :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hyr)
      exact MulAction.mem_stabilizer_iff.1 (hle a.2))
  intro r hr
  have h1 := key ⟨yR, Subgroup.mem_zpowers yR⟩
  have h2 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : Q)) h1
  exact h2

omit [MulDistribMulAction Γ Q] in
theorem eq_one_of_fix_fixV {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {E : Subgroup (MulAut W)} (hE : IsPGroup 2 E) {y : MulAut W} {k : ℕ} (hk : Odd k)
    (hyk : y ^ k = 1) (hyE : ∀ e ∈ E, y * e = e * y) (hy : ∀ w ∈ fixV E, y w = w) : y = 1 := by
  have h := fix_of_fix_fixed hW hE hk hyk hyE (R := ⊤) (fun _ _ _ _ => trivial)
    (fun _ _ => trivial) (fun w _ hw => hy w fun e he => hw e he)
  exact MulEquiv.ext fun w => h w trivial

end Thompson

section Quotient

variable {W : Type} [CommGroup W] [Finite W] {M N : Subgroup (MulAut W)}

theorem commOf_eq_of_d3Std {T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M L T L V)
    (R : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) :
    letI := qAct hD.hyp.Mp_normal
    XMod.IsInv ↥(L.subgroupOf M) R → XMod.commOf ↥(L.subgroupOf M) R = R := by
  let _i := qAct hD.hyp.Mp_normal
  intro hR
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  let φ : ↥(L.subgroupOf M) → ↥L := fun l => ⟨((l : ↥M) : MulAut W), l.2⟩
  have hφ : Function.Surjective φ := fun a => ⟨⟨⟨(a : MulAut W), hLM a.2⟩, a.2⟩, rfl⟩
  have hact : ∀ (l : ↥(L.subgroupOf M)) (x : W ⧸ modFix L (⊤ : Subgroup W)),
      l • x = φ l • x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hVc : XMod.commOf ↥(L.subgroupOf M) (tilde L ⊤ V) = tilde L ⊤ V := by
    rw [commOf_eq_of_surj φ hφ hact]
    exact (isIrr_tilde hD.hyp.irr).2
  exact commOf_eq_of_iSup_smul (d391_Λ_normal hD) (isIrr_tildeQ hD) hVc (iSup_smul_tildeQ hD) hR

variable (hNM : M ≤ Subgroup.normalizer (N : Set (MulAut W)))

omit [Finite W] in
include hNM in
theorem map_fixV_eq_fixed {E : Subgroup (MulAut W)} (hEM : E ≤ M)
    (hEN : ∀ e ∈ E, ∀ x ∈ N, e * x = x * e)
    (hT0 : letI := qAct hNM; ∀ R : Subgroup (W ⧸ modFix N (⊤ : Subgroup W)),
      XMod.IsInv ↥(N.subgroupOf M) R → XMod.commOf ↥(N.subgroupOf M) R = R) :
    letI := qAct hNM
    (fixV E).map (QuotientGroup.mk' (modFix N (⊤ : Subgroup W))) =
      XMod.fixed ↥(E.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix N (⊤ : Subgroup W))) := by
  let _i := qAct hNM
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨trivial, fun e => ?_⟩
    have he : ((e : ↥M) : MulAut W) ∈ E := Subgroup.mem_subgroupOf.1 e.2
    change (QuotientGroup.mk (((e : ↥M) : MulAut W) w) : W ⧸ modFix N (⊤ : Subgroup W)) =
      QuotientGroup.mk w
    rw [hw _ he]
  · set F := XMod.fixed ↥(E.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix N (⊤ : Subgroup W)))
      with hF
    have hFinv : XMod.IsInv ↥(N.subgroupOf M) F := by
      intro n q hq
      refine ⟨trivial, fun e => ?_⟩
      have hc : (e : ↥M) * (n : ↥M) = (n : ↥M) * (e : ↥M) :=
        Subtype.ext (hEN _ (Subgroup.mem_subgroupOf.1 e.2) _ (Subgroup.mem_subgroupOf.1 n.2))
      have h1 : (e : ↥M) • q = q := hq.2 e
      change (e : ↥M) • (n : ↥M) • q = (n : ↥M) • q
      rw [smul_smul, hc, mul_smul, h1]
    rw [← hT0 F hFinv, XMod.commOf_le_iff]
    intro n q hq
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (modFix N (⊤ : Subgroup W)) q
    refine ⟨((n : ↥M) : MulAut W) w * w⁻¹, fun e he => ?_, rfl⟩
    have h1 : (QuotientGroup.mk (e w) : W ⧸ modFix N (⊤ : Subgroup W)) = QuotientGroup.mk w :=
      hq.2 ⟨⟨e, hEM he⟩, he⟩
    rw [QuotientGroup.eq, modFix_top_eq] at h1
    have hn : ((n : ↥M) : MulAut W) ∈ N := Subgroup.mem_subgroupOf.1 n.2
    set z := (e w)⁻¹ * w with hz
    have hzn : ((n : ↥M) : MulAut W) z = z := h1 _ hn
    have hew : e w = w * z⁻¹ := by rw [hz]; group
    rw [map_mul, map_inv, ← MulAut.mul_apply, hEN e he _ hn, MulAut.mul_apply, hew, map_mul,
      map_inv, hzn, mul_inv_rev, inv_inv]
    simp [mul_assoc]

include hNM in
theorem eq_one_of_fix_fixed (hW : ∀ w : W, w ^ 2 = 1) (hNcomm : commV N = ⊤)
    {E : Subgroup (MulAut W)} (hEM : E ≤ M) (hE : IsPGroup 2 E) {y : MulAut W} (hyM : y ∈ M)
    (hyN : ∀ x ∈ N, y * x = x * y) {k : ℕ} (hk : Odd k) (hyk : y ^ k = 1)
    (hyE : ∀ e ∈ E, y * e = e * y)
    (hy : letI := qAct hNM; ∀ q ∈ XMod.fixed ↥(E.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix N (⊤ : Subgroup W))), (⟨y, hyM⟩ : ↥M) • q = q) :
    y = 1 := by
  let _i := qAct hNM
  have hQ : ∀ q : W ⧸ modFix N (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hW w, QuotientGroup.mk_one]
  have hE' : IsPGroup 2 ↥(E.subgroupOf M) := A4.isPGroup_subgroupOf_of_le hEM hE
  have hyk' : (⟨y, hyM⟩ : ↥M) ^ k = 1 := Subtype.ext (by simpa using hyk)
  have hyE' : ∀ e ∈ E.subgroupOf M, (⟨y, hyM⟩ : ↥M) * e = e * ⟨y, hyM⟩ :=
    fun e he => Subtype.ext (hyE _ (Subgroup.mem_subgroupOf.1 he))
  have hall := fix_of_fix_fixed hQ hE' hk hyk' hyE' (R := ⊤) (fun _ _ _ _ => trivial)
    (fun _ _ => trivial) (fun q _ hq => hy q ⟨trivial, fun e => hq e e.2⟩)
  refine eq_one_of_fix_quot hNcomm hyN fun w => ?_
  have h1 : (QuotientGroup.mk (y w) : W ⧸ modFix N (⊤ : Subgroup W)) = QuotientGroup.mk w :=
    hall (QuotientGroup.mk w) trivial
  rw [QuotientGroup.eq, modFix_top_eq] at h1
  have h2 := (fixV N).inv_mem h1
  rwa [mul_inv_rev, inv_inv, mul_comm] at h2

theorem nB_map_le {Q : Type*} [CommGroup Q] [Finite Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (A : Subgroup (MulAut W))
    (U : Subgroup W) :
    nB (A.subgroupOf M) (U.map π) ≤ rk ↥U - rk ↥(U ⊓ fixV A) := by
  unfold nB
  set F := XMod.fixed ↥(A.subgroupOf M) (⊤ : Subgroup Q) with hF
  have himg : (U ⊓ fixV A).map π ≤ U.map π ⊓ F := by
    rintro _ ⟨w, ⟨hwU, hwA⟩, rfl⟩
    refine ⟨⟨w, hwU, rfl⟩, trivial, fun a => ?_⟩
    change (a : ↥M) • π w = π w
    rw [hπM]
    congr 1
    exact hwA _ (Subgroup.mem_subgroupOf.1 a.2)
  have h1 := B1More.card_map_mul_card_inf_ker U π
  have h2 := B1More.card_map_mul_card_inf_ker (U ⊓ fixV A) π
  have h1' : rk ↥(U.map π) + rk ↥(U ⊓ π.ker) = rk ↥U := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  have h2' : rk ↥((U ⊓ fixV A).map π) + rk ↥(U ⊓ fixV A ⊓ π.ker) = rk ↥(U ⊓ fixV A) := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h2]
  have h3 : rk ↥((U ⊓ fixV A).map π) ≤ rk ↥(U.map π ⊓ F) := rk_mono himg
  have h4 : rk ↥(U.map π ⊓ F) ≤ rk ↥(U.map π) := rk_mono inf_le_left
  have h5 : rk ↥(U ⊓ fixV A ⊓ π.ker) ≤ rk ↥(U ⊓ π.ker) :=
    rk_mono (inf_le_inf_right _ inf_le_left)
  omega

theorem rk_fixV_sub_lt (hW : ∀ w : W, w ^ 2 = 1) {X A B₁ : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar X) (hB₁A : B₁ ≤ A) (hB₁ : B₁ ≠ ⊥) (hUA : ¬ fixV B₁ ≤ fixV A) :
    rk ↥(fixV B₁) - rk ↥(fixV A) < 2 * (rk ↥A - rk ↥B₁) := by
  have hA' := hA
  obtain ⟨r, hr, hr2, ⟨⟨hA2, -⟩, -⟩, -⟩ := hA'
  set U := fixV B₁ with hUdef
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA2.2.2.1
  have hcommute : ∀ a ∈ A, ∀ b ∈ B₁, ∀ u : W, b (a u) = a (b u) := by
    intro a ha b hb u
    rw [← MulAut.mul_apply, hAc b (hB₁A hb) a ha, MulAut.mul_apply]
  have hU : A ≤ stabSub U := by
    intro a ha u
    constructor
    · intro hau b hb
      have h1 := hcommute a⁻¹ (A.inv_mem ha) b hb (a u)
      rw [hau b hb] at h1
      simpa using h1
    · intro hu b hb
      rw [hcommute a ha b hb u, hu b hb]
  have hUA' : commSub U A ≠ ⊥ := fun h => hUA (commSub_eq_bot_iff.1 h)
  have hcentLe : B₁ ≤ A ⊓ centSub U := fun b hb => ⟨hB₁A hb, fun u hu => hu b hb⟩
  obtain ⟨-, h7⟩ := D2_7 hW hr hA hU hUA'
  rcases h7 with ⟨ε, hε, ⟨⟨hIsA2, hrat⟩, -⟩⟩ | ⟨hfaith, -⟩
  ·
    have hfixA : U ⊓ fixV A = fixV A := inf_eq_right.2 fun w hw b hb => hw b (hB₁A hb)
    have hidx : rkIdx (fixV (autSub A U)) = rk ↥U - rk ↥(fixV A) := by
      have h1 := rk_add_rkIdx (fixV (autSub A U))
      have h2 := rk_fixV_autSub hU
      rw [hfixA] at h2
      omega
    have hrkaut : rk ↥(autSub A U) + rk ↥(A ⊓ centSub U) = rk ↥A := by
      have h1 := card_autSub_mul hU
      unfold rk
      rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
    have hrkB : rk ↥B₁ ≤ rk ↥(A ⊓ centSub U) := rk_mono hcentLe
    have hpos : 0 < rk ↥(autSub A U) := by
      have h2 : IsPGroup 2 ↥(autSub A U) := fun g =>
        ⟨1, Subtype.ext (by simpa using hIsA2.2.2.2 g g.2)⟩
      rcases Nat.eq_zero_or_pos (rk ↥(autSub A U)) with h0 | h0
      · exact absurd ((rk_eq_zero_iff_of_isPGroup h2).1 h0) hIsA2.2.1
      · exact h0
    have hlt : (rkIdx (fixV (autSub A U)) : ℚ) < 2 * (rk ↥(autSub A U) : ℚ) := by
      have hposq : (0 : ℚ) < (rk ↥(autSub A U) : ℚ) := by exact_mod_cast hpos
      have h1 : rAV (autSub A U) < 2 := lt_of_le_of_lt hrat (by linarith)
      unfold rAV at h1
      rwa [div_lt_iff₀ hposq] at h1
    have hlt' : rkIdx (fixV (autSub A U)) < 2 * rk ↥(autSub A U) := by exact_mod_cast hlt
    omega
  · exfalso
    apply hB₁
    rw [eq_bot_iff, ← hfaith]
    exact hcentLe

include hNM in
theorem nB_map_fixV_lt (hW : ∀ w : W, w ^ 2 = 1) {X A B₁ : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar X) (hB₁A : B₁ ≤ A) (hB₁ : B₁ ≠ ⊥) (hUA : ¬ fixV B₁ ≤ fixV A) :
    letI := qAct hNM
    nB (A.subgroupOf M) ((fixV B₁).map (QuotientGroup.mk' (modFix N (⊤ : Subgroup W)))) <
      2 * (rk ↥A - rk ↥B₁) := by
  let _i := qAct hNM
  have h1 := nB_map_le (M := M) (QuotientGroup.mk' (modFix N (⊤ : Subgroup W)))
    (fun _ _ => rfl) A (fixV B₁)
  have h2 := rk_fixV_sub_lt hW hA hB₁A hB₁ hUA
  have hfixA : fixV B₁ ⊓ fixV A = fixV A := inf_eq_right.2 fun w hw b hb => hw b (hB₁A hb)
  rw [hfixA] at h1
  omega

include hNM in
theorem nB_fixed_lt (hW : ∀ w : W, w ^ 2 = 1) {X A B₁ : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar X) (hB₁A : B₁ ≤ A) (hB₁ : B₁ ≠ ⊥) (hUA : ¬ fixV B₁ ≤ fixV A)
    (hB₁M : B₁ ≤ M) (hB₁N : ∀ b ∈ B₁, ∀ x ∈ N, b * x = x * b)
    (hT0 : letI := qAct hNM; ∀ R : Subgroup (W ⧸ modFix N (⊤ : Subgroup W)),
      XMod.IsInv ↥(N.subgroupOf M) R → XMod.commOf ↥(N.subgroupOf M) R = R) :
    letI := qAct hNM
    nB (A.subgroupOf M) (XMod.fixed ↥(B₁.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix N (⊤ : Subgroup W)))) < 2 * (rk ↥A - rk ↥B₁) := by
  let _i := qAct hNM
  rw [← map_fixV_eq_fixed hNM hB₁M hB₁N hT0]
  exact nB_map_fixV_lt hNM hW hA hB₁A hB₁ hUA

end Quotient

end CFSG.Quasithin.SmithD39Two
