module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUAct
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISULevi
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUAut
public import CFSG.LocalAnalysis.StandardType.SUCenterOdd

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.Open CFSG.StandardType CFSG.StandardType.RCKC1

variable {k : ℕ}

private noncomputable abbrev rckSUb_mk (k : ℕ) :
    SUG k →* SUG k ⧸ Subgroup.center (SUG k) :=
  QuotientGroup.mk' (Subgroup.center (SUG k))

private lemma rckSUb_add_self (a : ZMod 2) : a + a = 0 := by
  rw [CharTwo.add_self_eq_zero]

private lemma rckSUb_suR_sq (hk : 4 ≤ k) : suR hk ^ 2 = 1 := by
  rw [suR, sq, suZ_add]
  have hv : (![0, 1, 0, 0] : Fin 4 → ZMod 2) + ![0, 1, 0, 0] = 0 := by
    funext i
    fin_cases i <;> decide +kernel
  rw [hv, suZ_zero]

private lemma rckSUb_suZ_inv (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    (suZ hk v)⁻¹ = suZ hk v := by
  have h2 : suZ hk v * suZ hk v = 1 := by
    rw [suZ_add]
    have hv : v + v = 0 := by
      funext i
      exact rckSUb_add_self (v i)
    rw [hv, suZ_zero]
  exact inv_eq_of_mul_eq_one_right h2

private lemma rckSUb_center_eq_one_of_sq_eq_one (hk : 4 ≤ k) {x : SUG k}
    (hx : x ∈ Subgroup.center (SUG k)) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_center_SU SUσ hx
  have hdvd2 : orderOf x ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hx2
  have hcop : Nat.Coprime 2 (orderOf x) := hodd.coprime_two_right.symm
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop.symm (dvd_refl _) hdvd2)

private lemma rckSUb_suZ_eq_zero_of_mem_center (hk : 4 ≤ k) (v : Fin 4 → ZMod 2)
    (hv : suZ hk v ∈ Subgroup.center (SUG k)) : v = 0 := by
  have hsq : suZ hk v ^ 2 = 1 := by
    rw [sq, suZ_add]
    have hv2 : v + v = 0 := by
      funext i
      exact rckSUb_add_self (v i)
    rw [hv2, suZ_zero]
  have h1 : suZ hk v = 1 := rckSUb_center_eq_one_of_sq_eq_one hk hv hsq
  exact suZ_injective hk (by rw [h1, suZ_zero])

private lemma rckSUb_mk_suZ_injective (hk : 4 ≤ k) {v w : Fin 4 → ZMod 2}
    (h : rckSUb_mk k (suZ hk v) = rckSUb_mk k (suZ hk w)) : v = w := by
  have hmem : suZ hk v * (suZ hk w)⁻¹ ∈ Subgroup.center (SUG k) := by
    have h1 : rckSUb_mk k (suZ hk v * (suZ hk w)⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center (SUG k)) _).mp h1
  have heq : suZ hk v * (suZ hk w)⁻¹ = suZ hk (v + w) := by
    rw [rckSUb_suZ_inv hk w, suZ_add]
  have hsum : v + w = 0 := rckSUb_suZ_eq_zero_of_mem_center hk (v + w) (heq ▸ hmem)
  funext i
  have hi : v i + w i = 0 := by
    have := congrFun hsum i
    simpa using this
  exact (by decide +kernel : ∀ a b : ZMod 2, a + b = 0 → a = b) (v i) (w i) hi

private lemma rckSUb_mk_mem_zpowers_of_suZ_mem (hk : 4 ≤ k) {w : Fin 4 → ZMod 2}
    (h : suZ hk w ∈ Subgroup.zpowers (suR hk)) :
    rckSUb_mk k (suZ hk w) ∈ Subgroup.zpowers (rckSUb_mk k (suR hk)) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [← map_zpow, hn]

private lemma rckSUb_mulVec_inv_mulVec (g : GL (Fin 4) (ZMod 2)) (u : Fin 4 → ZMod 2) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) = u := by
  rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
    GeneralLinearGroup.coe_one, Matrix.one_mulVec]

private lemma rckSUb_mulAut_inv_apply {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    γ (γ⁻¹ x) = x := by
  rw [← MulAut.mul_apply, mul_inv_cancel]
  rfl

private abbrev rckSUb_Rep (hk : 4 ≤ k) (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k)))
    (ψ : GL (Fin 4) (ZMod 2)) : Prop :=
  ∀ u : Fin 4 → ZMod 2,
    φ (rckSUb_mk k (suZ hk u)) =
      rckSUb_mk k (suZ hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u))

private lemma rckSUb_Rep_unique (hk : 4 ≤ k)
    {φ : MulAut (SUG k ⧸ Subgroup.center (SUG k))} {ψ₁ ψ₂ : GL (Fin 4) (ZMod 2)}
    (h₁ : rckSUb_Rep hk φ ψ₁) (h₂ : rckSUb_Rep hk φ ψ₂) : ψ₁ = ψ₂ := by
  apply Units.ext
  ext i j
  have hcol : ∀ u : Fin 4 → ZMod 2,
      (ψ₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u =
      (ψ₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u := by
    intro u
    exact rckSUb_mk_suZ_injective hk (by rw [← h₁ u, ← h₂ u])
  have hsingle := congrFun (hcol (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using hsingle

private lemma rckSUb_rep_exists (hk : 4 ≤ k)
    (Y : Subgroup (MulAut (SUG k ⧸ Subgroup.center (SUG k))))
    (hfix : ∀ φ ∈ Y, φ (rckSUb_mk k (suR hk)) = rckSUb_mk k (suR hk)) :
    ∀ φ : MulAut (SUG k ⧸ Subgroup.center (SUG k)), φ ∈ Y →
      ∃ ψ : GL (Fin 4) (ZMod 2),
        rckSUb_Rep hk φ ψ ∧
        (∀ v : Fin 4 → ZMod 2,
          s5q ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v) ∧
        (ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R := by
  intro φ hφ
  obtain ⟨τ, B, hB, hrep⟩ := rckSU_aut hk φ
  have hr : (B : Matrix (Fin k) (Fin k) SUF) *
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
        ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
    obtain ⟨g', hg'mat, hg'φ⟩ := hrep (suR hk)
    have hmk : rckSUb_mk k g' = rckSUb_mk k (suR hk) := by
      have hφg : φ (rckSUb_mk k (suR hk)) = rckSUb_mk k g' := hg'φ
      rw [← hφg]
      exact hfix φ hφ
    have hz : g' * (suR hk)⁻¹ ∈ Subgroup.center (SUG k) := by
      have h1 : rckSUb_mk k (g' * (suR hk)⁻¹) = 1 := by
        rw [map_mul, map_inv, hmk, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center (SUG k)) _).mp h1
    have hMM : ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
        ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ = 1 := by
      rw [← Matrix.map_mul]
      have hr2 : ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
          ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) = 1 := by
        rw [← GeneralLinearGroup.coe_mul, ← Subgroup.coe_mul, ← sq, rckSUb_suR_sq hk,
          Subgroup.coe_one, Units.val_one]
      rw [hr2]
      ext i j
      simp [Matrix.map_apply, Matrix.one_apply]
    have hg'sq : g' ^ 2 = 1 := by
      rw [sq]
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, hg'mat]
      have hBB : (B : Matrix (Fin k) (Fin k) SUF) *
          ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) = 1 := by
        rw [← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one]
      have hB'B : ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
          (B : Matrix (Fin k) (Fin k) SUF) = 1 := by
        rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
      have hstep : ((B : Matrix (Fin k) (Fin k) SUF) *
            ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
              ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) *
          ((B : Matrix (Fin k) (Fin k) SUF) *
            ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
              ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) =
          (B : Matrix (Fin k) (Fin k) SUF) *
            (((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
              ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ) *
            ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
        rw [show
          ((B : Matrix (Fin k) (Fin k) SUF) *
              ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
                ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) *
            ((B : Matrix (Fin k) (Fin k) SUF) *
              ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
                ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) =
          (B : Matrix (Fin k) (Fin k) SUF) *
              ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
            (((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
              (B : Matrix (Fin k) (Fin k) SUF)) *
              ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
            ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) by
          simp only [Matrix.mul_assoc]]
        rw [hB'B, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [hstep, hMM, Matrix.mul_one, hBB]
    have hcomm : Commute (g' * (suR hk)⁻¹) (suR hk) :=
      (Subgroup.mem_center_iff.mp hz (suR hk)).symm
    have hg'z : g' = (g' * (suR hk)⁻¹) * suR hk := by group
    have h1 : g' ^ 2 = ((g' * (suR hk)⁻¹) * suR hk) ^ 2 :=
      congrArg (fun t => t ^ 2) hg'z
    have h1b : ((g' * (suR hk)⁻¹) * suR hk) ^ 2 =
        (g' * (suR hk)⁻¹) ^ 2 * (suR hk) ^ 2 := hcomm.mul_pow 2
    have h1c : (g' * (suR hk)⁻¹) ^ 2 * (suR hk) ^ 2 = (g' * (suR hk)⁻¹) ^ 2 :=
      (congrArg (fun t => (g' * (suR hk)⁻¹) ^ 2 * t) (rckSUb_suR_sq hk)).trans (mul_one _)
    have hzsq : (g' * (suR hk)⁻¹) ^ 2 = 1 :=
      ((h1.trans h1b).trans h1c).symm.trans hg'sq
    have hz1 : g' * (suR hk)⁻¹ = 1 := rckSUb_center_eq_one_of_sq_eq_one hk hz hzsq
    have hg'eq : g' = suR hk := mul_inv_eq_one.mp hz1
    rw [← hg'mat, hg'eq]
  obtain ⟨ψ, hψq, hψR, hψrefl, hψcorner⟩ := rckSU_act hk τ B hB hr
  refine ⟨ψ, fun u => ?_, hψq, hψR⟩
  obtain ⟨g', hg'mat, hg'φ⟩ := hrep (suZ hk u)
  have hg'su : g' = suZ hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) := by
    apply Subtype.ext
    apply Units.ext
    rw [hg'mat]
    rw [show (((suZ hk u : SUG k) : GL (Fin k) SUF) :
        Matrix (Fin k) (Fin k) SUF) = suCorner hk u from suZ_val hk u]
    rw [hψcorner]
    exact (suZ_val hk _).symm
  have hφg : φ (rckSUb_mk k (suZ hk u)) = rckSUb_mk k g' := hg'φ
  rw [hφg, hg'su]

private lemma rckSUb_conj_rep (hk : 4 ≤ k) (c : SUG k) (g : GL (Fin 4) (ZMod 2))
    (hcZ : ∀ u : Fin 4 → ZMod 2,
      c * suZ hk u * c⁻¹ = suZ hk ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u))
    (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) (ψ : GL (Fin 4) (ZMod 2))
    (hrep : rckSUb_Rep hk φ ψ) :
    rckSUb_Rep hk
      (MulAut.conj (rckSUb_mk k c) * φ * (MulAut.conj (rckSUb_mk k c))⁻¹)
      (g * ψ * g⁻¹) := by
  intro u
  have hγapply : ∀ w : Fin 4 → ZMod 2,
      MulAut.conj (rckSUb_mk k c) (rckSUb_mk k (suZ hk w)) =
        rckSUb_mk k (suZ hk ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w)) := by
    intro w
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hcZ w]
  let w : Fin 4 → ZMod 2 :=
    ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u
  have hgw : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w = u :=
    rckSUb_mulVec_inv_mulVec g u
  have hγinv : (MulAut.conj (rckSUb_mk k c))⁻¹ (rckSUb_mk k (suZ hk u)) =
      rckSUb_mk k (suZ hk w) := by
    apply (MulAut.conj (rckSUb_mk k c)).injective
    rw [rckSUb_mulAut_inv_apply, hγapply w, hgw]
  have hvec : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (((ψ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w) =
      (((g * ψ * g⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) := by
    dsimp only [w]
    simp only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  calc (MulAut.conj (rckSUb_mk k c) * φ * (MulAut.conj (rckSUb_mk k c))⁻¹)
        (rckSUb_mk k (suZ hk u))
      = MulAut.conj (rckSUb_mk k c)
          (φ ((MulAut.conj (rckSUb_mk k c))⁻¹ (rckSUb_mk k (suZ hk u)))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = MulAut.conj (rckSUb_mk k c) (φ (rckSUb_mk k (suZ hk w))) := by rw [hγinv]
    _ = MulAut.conj (rckSUb_mk k c)
          (rckSUb_mk k (suZ hk
            (((ψ : GL (Fin 4) (ZMod 2)) :
              Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w))) := by rw [hrep w]
    _ = rckSUb_mk k (suZ hk
          ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
            (((ψ : GL (Fin 4) (ZMod 2)) :
              Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w))) := by rw [hγapply]
    _ = rckSUb_mk k (suZ hk
          (((g * ψ * g⁻¹ : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u)) := by rw [hvec]

theorem rckSU_K1Data (hk : 4 ≤ k) :
    RCKK1Data (QuotientGroup.mk (suR hk) : SUG k ⧸ Subgroup.center (SUG k))
      ((suV hk).map (QuotientGroup.mk' (Subgroup.center (SUG k)))) := by
  let rb : SUG k ⧸ Subgroup.center (SUG k) := rckSUb_mk k (suR hk)
  let Vb : Subgroup (SUG k ⧸ Subgroup.center (SUG k)) := (suV hk).map (rckSUb_mk k)
  change RCKK1Data rb Vb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨suR hk, suR_mem_suV hk, rfl⟩
  · intro h
    have hmem : suR hk ∈ Subgroup.center (SUG k) :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center (SUG k)) (suR hk)).mp h
    exact suR_ne_one hk (rckSUb_center_eq_one_of_sq_eq_one hk hmem (rckSUb_suR_sq hk))
  · exact (isElemAbelian_suV hk).map (rckSUb_mk k)
  · have hinj : Function.Injective (fun x : ↥(suV hk) => rckSUb_mk k (x : SUG k)) := by
      intro x y hxy
      change rckSUb_mk k (x : SUG k) = rckSUb_mk k (y : SUG k) at hxy
      have hmem : (x : SUG k) * (y : SUG k)⁻¹ ∈ Subgroup.center (SUG k) := by
        have h1 : rckSUb_mk k ((x : SUG k) * (y : SUG k)⁻¹) = 1 := by
          rw [map_mul, map_inv, hxy, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff (N := Subgroup.center (SUG k)) _).mp h1
      have hsq : ((x : SUG k) * (y : SUG k)⁻¹) ^ 2 = 1 :=
        (isElemAbelian_suV hk).2 ((x : SUG k) * (y : SUG k)⁻¹)
          (Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ y.2))
      have h1 : (x : SUG k) * (y : SUG k)⁻¹ = 1 :=
        rckSUb_center_eq_one_of_sq_eq_one hk hmem hsq
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    have hinj_sub : Function.Injective (fun x : ↥(suV hk) =>
        (⟨rckSUb_mk k (x : SUG k), Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((suV hk).map (rckSUb_mk k)))) := by
      intro x y hxy
      exact hinj (Subtype.ext_iff.mp hxy)
    rw [← card_suV hk]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(suV hk) =>
        (⟨rckSUb_mk k (x : SUG k), Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((suV hk).map (rckSUb_mk k)))) ⟨hinj_sub, ?_⟩)).symm
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro v hv hv1
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    have hv'1 : v' ≠ 1 := by
      intro h
      exact hv1 (by rw [h, map_one])
    obtain ⟨j, hj⟩ := suV_conj hk v' hv' hv'1
    refine ⟨rckSUb_mk k j, ?_⟩
    rw [hj, map_mul, map_mul, map_inv]
  · intro Y hY2 hfix hnorm v hv φ hφ
    obtain ⟨c₁, c₂, hc₁r, hc₂r, hc₁Z, hc₂Z⟩ := rckSU_levi hk
    have rep_exists := rckSUb_rep_exists hk Y hfix
    have rep_exists' : ∀ φ : ↥Y, ∃ ψ : GL (Fin 4) (ZMod 2),
        rckSUb_Rep hk (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) ψ ∧
        (∀ v : Fin 4 → ZMod 2,
          s5q ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v) ∧
        (ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R :=
      fun φ => rep_exists φ.1 φ.2
    let Ψ : ↥Y →* GL (Fin 4) (ZMod 2) :=
      { toFun := fun φ => Classical.choose (rep_exists' φ)
        map_one' := by
          apply rckSUb_Rep_unique hk
            (φ := ((1 : ↥Y) : MulAut (SUG k ⧸ Subgroup.center (SUG k))))
          · exact (Classical.choose_spec (rep_exists' 1)).1
          · intro u
            simp
        map_mul' := fun φ φ' => by
          apply rckSUb_Rep_unique hk
            (φ := ((φ * φ' : ↥Y) : MulAut (SUG k ⧸ Subgroup.center (SUG k))))
          · exact (Classical.choose_spec (rep_exists' (φ * φ'))).1
          · intro u
            rw [Subgroup.coe_mul, MulAut.mul_apply]
            rw [(Classical.choose_spec (rep_exists' φ')).1 u,
              (Classical.choose_spec (rep_exists' φ)).1
                (((Classical.choose (rep_exists' φ') : GL (Fin 4) (ZMod 2)) :
                  Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u)]
            rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] }
    let Y' : Subgroup (GL (Fin 4) (ZMod 2)) := Ψ.range
    have hY'p : IsPGroup 2 Y' := by
      have htop : IsPGroup 2 (⊤ : Subgroup ↥Y) := by
        have h := IsPGroup.comap_of_injective hY2 Y.subtype (Subgroup.subtype_injective Y)
        rwa [Subgroup.comap_subtype, Subgroup.subgroupOf_self] at h
      change IsPGroup 2 Ψ.range
      rw [MonoidHom.range_eq_map]
      exact IsPGroup.map htop Ψ
    have hY'q : ∀ y ∈ Y', ∀ u : Fin 4 → ZMod 2,
        s5q ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) = s5q u := by
      intro y hy u
      change y ∈ Ψ.range at hy
      obtain ⟨φ, rfl⟩ := MonoidHom.mem_range.mp hy
      exact (Classical.choose_spec (rep_exists' φ)).2.1 u
    have hY'R : ∀ y ∈ Y', (y : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R := by
      intro y hy
      change y ∈ Ψ.range at hy
      obtain ⟨φ, rfl⟩ := MonoidHom.mem_range.mp hy
      exact (Classical.choose_spec (rep_exists' φ)).2.2
    have conj_rep := rckSUb_conj_rep hk
    have normalizer_step : ∀ (c : SUG k) (g : GL (Fin 4) (ZMod 2)),
        c * suR hk = suR hk * c →
        (∀ u : Fin 4 → ZMod 2,
          c * suZ hk u * c⁻¹ = suZ hk ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u)) →
        g ∈ Subgroup.normalizer (Y' : Set (GL (Fin 4) (ZMod 2))) := by
      intro c g hcr hcZ
      have hmkc : rckSUb_mk k c * rb = rb * rckSUb_mk k c := by
        change rckSUb_mk k c * rckSUb_mk k (suR hk) =
          rckSUb_mk k (suR hk) * rckSUb_mk k c
        rw [← map_mul, ← map_mul, hcr]
      have hnormc : MulAut.conj (rckSUb_mk k c) ∈
          Subgroup.normalizer (Y : Set (MulAut (SUG k ⧸ Subgroup.center (SUG k)))) :=
        hnorm (rckSUb_mk k c) hmkc
      have hmkc_inv : (rckSUb_mk k c)⁻¹ * rb = rb * (rckSUb_mk k c)⁻¹ :=
        Commute.inv_left hmkc
      have hnormc_inv : MulAut.conj ((rckSUb_mk k c)⁻¹) ∈
          Subgroup.normalizer (Y : Set (MulAut (SUG k ⧸ Subgroup.center (SUG k)))) :=
        hnorm ((rckSUb_mk k c)⁻¹) hmkc_inv
      have hcZ_inv : ∀ u : Fin 4 → ZMod 2,
          c⁻¹ * suZ hk u * c = suZ hk
            (((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) := by
        intro u
        have hw : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
            (((g⁻¹ : GL (Fin 4) (ZMod 2)) :
              Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u) = u :=
          rckSUb_mulVec_inv_mulVec g u
        have h := hcZ (((g⁻¹ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u)
        rw [hw] at h
        rw [← h]
        group
      refine Subgroup.mem_set_normalizer_iff.mpr (fun y => ⟨?_, ?_⟩)
      · intro hy
        change y ∈ Ψ.range at hy
        obtain ⟨φ, rfl⟩ := MonoidHom.mem_range.mp hy
        have hmem : MulAut.conj (rckSUb_mk k c) *
            (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) *
              (MulAut.conj (rckSUb_mk k c))⁻¹ ∈ Y :=
          (Subgroup.mem_set_normalizer_iff.mp hnormc
            (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k)))).mp φ.2
        let φ₁ : ↥Y := ⟨_, hmem⟩
        have hRep : rckSUb_Rep hk ((φ₁ : ↥Y) :
            MulAut (SUG k ⧸ Subgroup.center (SUG k))) (g * Ψ φ * g⁻¹) :=
          conj_rep c g hcZ (φ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) (Ψ φ)
            (Classical.choose_spec (rep_exists' φ)).1
        have hEq : Ψ φ₁ = g * Ψ φ * g⁻¹ :=
          rckSUb_Rep_unique hk (Classical.choose_spec (rep_exists' φ₁)).1 hRep
        exact ⟨φ₁, hEq⟩
      · intro hy
        change g * y * g⁻¹ ∈ Ψ.range at hy
        obtain ⟨φ₂, hφ₂⟩ := MonoidHom.mem_range.mp hy
        have hmem : MulAut.conj ((rckSUb_mk k c)⁻¹) *
            (φ₂ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) *
              (MulAut.conj ((rckSUb_mk k c)⁻¹))⁻¹ ∈ Y :=
          (Subgroup.mem_set_normalizer_iff.mp hnormc_inv
            (φ₂ : MulAut (SUG k ⧸ Subgroup.center (SUG k)))).mp φ₂.2
        let φ₂' : ↥Y := ⟨_, hmem⟩
        have hRep : rckSUb_Rep hk ((φ₂' : ↥Y) :
            MulAut (SUG k ⧸ Subgroup.center (SUG k))) (g⁻¹ * Ψ φ₂ * (g⁻¹)⁻¹) :=
          conj_rep c⁻¹ g⁻¹ hcZ_inv (φ₂ : MulAut (SUG k ⧸ Subgroup.center (SUG k))) (Ψ φ₂)
            (Classical.choose_spec (rep_exists' φ₂)).1
        have hEq : Ψ φ₂' = g⁻¹ * Ψ φ₂ * (g⁻¹)⁻¹ :=
          rckSUb_Rep_unique hk (Classical.choose_spec (rep_exists' φ₂')).1 hRep
        refine ⟨φ₂', ?_⟩
        rw [hEq, hφ₂]
        group
    have hH1 : s5h1 ∈ Subgroup.normalizer (Y' : Set (GL (Fin 4) (ZMod 2))) :=
      normalizer_step c₁ s5h1 hc₁r hc₁Z
    have hH2 : s5h2 ∈ Subgroup.normalizer (Y' : Set (GL (Fin 4) (ZMod 2))) :=
      normalizer_step c₂ s5h2 hc₂r hc₂Z
    have hs5 := rckSU_s5 Y' hY'p hY'q hY'R hH1 hH2
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    have hv'Z : v' ∈ suZ0 hk := suV_le_suZ0 hk hv'
    have hv'Z' : v' ∈ (MonoidHom.mk' (fun u : Multiplicative (Fin 4 → ZMod 2) =>
        suZ hk u.toAdd) (fun u w => (suZ_add hk u.toAdd w.toAdd).symm)).range := hv'Z
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hv'Z'
    let u' : Fin 4 → ZMod 2 := u.toAdd
    have hu' : suZ hk u' = v' := hu
    let φY : ↥Y := ⟨φ, hφ⟩
    rw [← hu']
    rw [show φ (rckSUb_mk k (suZ hk u')) =
        rckSUb_mk k (suZ hk
          (((Ψ φY : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u')) from
      (Classical.choose_spec (rep_exists' φY)).1 u']
    rw [← map_inv, ← map_mul, rckSUb_suZ_inv hk u', suZ_add]
    refine rckSUb_mk_mem_zpowers_of_suZ_mem hk ?_
    have hψ : Ψ φY = 1 ∨ Ψ φY = s5tau := hs5 (Ψ φY) ⟨φY, rfl⟩
    rcases hψ with hψ1 | hψtau
    · rw [hψ1, GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      have hu'2 : u' + u' = 0 := by
        funext i
        exact rckSUb_add_self (u' i)
      rw [hu'2, suZ_zero]
      exact Subgroup.one_mem _
    · rw [hψtau]
      change suZ hk (((s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u') + u') ∈
        Subgroup.zpowers (suR hk)
      have hvec : (s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u' + u' =
          ![0, u' 2, 0, 0] :=
        (by decide +kernel : ∀ u : Fin 4 → ZMod 2,
          (s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u + u = ![0, u 2, 0, 0]) u'
      rw [hvec]
      rcases (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) (u' 2) with h2 | h2
      · rw [h2]
        have hv0 : (![0, 0, 0, 0] : Fin 4 → ZMod 2) = 0 := by decide +kernel
        rw [hv0, suZ_zero]
        exact Subgroup.one_mem _
      · rw [h2]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]; rfl⟩

end CFSG.StandardType.RCKK1IIISU
