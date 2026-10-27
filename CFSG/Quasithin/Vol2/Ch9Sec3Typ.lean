module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3Conj

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem mem_r0_of_form (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) {s : G} (hs : s ∈ T) {A B : GL (Fin 2) K}
    (hform : bar e ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ = Om4.lr A B) :
    s ∈ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hu3 : ∀ x : K, x ≠ 0 → x ^ 3 = 1 := fun x hx => by
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hK4] at h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.hyp.fsu.sylow.1) ⟨s, hs⟩
  have hk' : orderOf s = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ with hy
  have hy1 : bar e y ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk', pow_orderOf_eq_one]
      rfl
    rw [this, map_one]
  rw [hform, Om4.lr_pow] at hy1
  obtain ⟨c, hc0, hA, hB⟩ := Om4.exists_smul_of_lr_eq_one hy1
  have hdetA : (A : Matrix (Fin 2) (Fin 2) K).det ^ 2 ^ k = c ^ 2 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hA, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin]
  have hdetB : (B : Matrix (Fin 2) (Fin 2) K).det ^ 2 ^ k = c⁻¹ ^ 2 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hB, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin]
  set δA := (A : Matrix (Fin 2) (Fin 2) K).det with hδA
  set δB := (B : Matrix (Fin 2) (Fin 2) K).det with hδB
  have hδA0 : δA ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  have hδB0 : δB ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit |>.ne_zero
  have hδ : δA * δB = 1 := by
    have h1 : (δA * δB) ^ 2 ^ k = 1 := by
      rw [mul_pow, hdetA, hdetB, ← mul_pow, mul_inv_cancel₀ hc0, one_pow]
    have h3 := hu3 _ (mul_ne_zero hδA0 hδB0)
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h1, h3⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  set ν := δA ^ 2 with hν
  set μ := δB ^ 2 with hμ
  have hν2 : ν ^ 2 = δA := by
    rw [hν, ← pow_mul]
    calc δA ^ (2 * 2) = δA ^ 3 * δA := by ring
      _ = δA := by rw [hu3 δA hδA0, one_mul]
  have hμ2 : μ ^ 2 = δB := by
    rw [hμ, ← pow_mul]
    calc δB ^ (2 * 2) = δB ^ 3 * δB := by ring
      _ = δB := by rw [hu3 δB hδB0, one_mul]
  have hν0 : ν ≠ 0 := pow_ne_zero 2 hδA0
  have hμ0 : μ ≠ 0 := pow_ne_zero 2 hδB0
  have hνμ : ν * μ = 1 := by rw [hν, hμ, ← mul_pow, hδ, one_pow]
  let A' : SpecialLinearGroup (Fin 2) K := ⟨ν⁻¹ • (A : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hν2, inv_mul_cancel₀ hδA0]⟩
  let B' : SpecialLinearGroup (Fin 2) K := ⟨μ⁻¹ • (B : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hμ2, inv_mul_cancel₀ hδB0]⟩
  have hρ : Om4.rho (A', B') = Om4.lr A B := by
    refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
    rw [toAdd_rho, Om4.toAdd_lr]
    show (ν⁻¹ • (A : Matrix (Fin 2) (Fin 2) K)) * Multiplicative.toAdd X *
      (μ⁻¹ • (B : Matrix (Fin 2) (Fin 2) K))ᵀ = _
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      ← mul_inv, mul_comm μ ν, hνμ, inv_one, one_smul]
  obtain ⟨u, hu⟩ := hc.surj (A', B')
  have hbar : bar e y = bar e (Subgroup.inclusion S.L0_le_normalizer_V u) := by
    rw [hc.bar_L0, hu, hρ, ← hform]
  have hsu : s * (u : G)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have h1 : bar e (y * (Subgroup.inclusion S.L0_le_normalizer_V u)⁻¹) = 1 := by
      rw [map_mul, map_inv, hbar, mul_inv_cancel]
    exact mem_centralizer_of_bar e _ h1
  have hsuQ : s * (u : G)⁻¹ ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    S.sup_inf_centralizer_le h37c h38c ⟨(fsuL0 T L ⊔ T).mul_mem (Subgroup.mem_sup_right hs)
      ((fsuL0 T L ⊔ T).inv_mem (Subgroup.mem_sup_left u.2)), hsu⟩
  have huT : (u : G) ∈ T := by
    have e1 : (u : G) = (s * (u : G)⁻¹)⁻¹ * s := by group
    rw [e1]
    exact T.mul_mem (T.inv_mem hsuQ.1) hs
  have e2 : s = (s * (u : G)⁻¹) * u := by group
  rw [e2]
  exact mul_mem (Subgroup.mem_sup_right hsuQ) (Subgroup.mem_sup_left ⟨huT, u.2⟩)

variable {D : Subgroup G}

theorem mem_r0_of_comm (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) {s : G} (hs : s ∈ T)
    (hsB : ∀ b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
      s * b * s⁻¹ * b⁻¹ ∈ T ⊓ fsuL0 T L)
    (hsD : ∀ d ∈ D, s * d * s⁻¹ * d⁻¹ ∈ (T ⊓ fsuL0 T L) ⊔ (D ⊓ Subgroup.centralizer
      ((fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) :
        Set G))) :
    s ∈ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set B := D ⊓ Subgroup.centralizer (V₁ : Set G) with hB
  set P₀ := T ⊓ fsuL0 T L with hP₀
  have hDP : ∀ x ∈ D, ∀ y ∈ D, x * y⁻¹ ∈ P₀ → x = y := by
    intro x hx y hy hxy
    have hmem : x * y⁻¹ ∈ D := D.mul_mem hx (D.inv_mem hy)
    have hodd : Odd (orderOf (x * y⁻¹)) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hmem)
    have h1 := eq_one_of_odd_of_mem (S.hyp.fsu.sylow.1.to_le inf_le_left) hxy hodd
    exact mul_inv_eq_one.mp h1
  have hBP : B ≤ Subgroup.normalizer (P₀ : Set G) := inf_le_left.trans (hD.1.trans inf_le_right)
  have hset : ((P₀ ⊔ B : Subgroup G) : Set G) = (P₀ : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P₀ B hBP
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : Nat.card Kˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hK4]
  obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut hs
  obtain ⟨d₁, hd₁D, hd₁L, hψd₁⟩ := exists_mem_of_diag hdiag ω ω
  have key : ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L, ψ ⟨d', hd'L⟩ =
      (diagOf (Units.map τ.toMonoidHom ω), diagOf (Units.map τ.toMonoidHom ω)) ∧
      s * d₁ * s⁻¹ * d'⁻¹ ∈ T := by
    rcases hform with hf | hf
    · exact hc.conj_diag_ns h37c h38c hdiag hs hA hB' hf hd₁L hψd₁
    · exact hc.conj_diag_swap h37c h38c hdiag hs hA hB' hf hd₁L hψd₁
  obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ := key
  have hconjL : ∀ x ∈ fsuL0 T L, ∀ y ∈ fsuL0 T L, s * x * s⁻¹ * y⁻¹ ∈ fsuL0 T L :=
    fun x hx y hy => (fsuL0 T L).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 hs) x).mp hx)
      ((fsuL0 T L).inv_mem hy)
  have hr₁ : s * d₁ * s⁻¹ * d'⁻¹ ∈ P₀ := ⟨hmem, hconjL d₁ hd₁L d' hd'L⟩
  have hr₂ := hsD d₁ hd₁D
  rw [← SetLike.mem_coe, hset] at hr₂
  obtain ⟨r, hr, b, hb, hrb⟩ := hr₂
  have hrb' : r * b = s * d₁ * s⁻¹ * d₁⁻¹ := hrb
  have hd'eq : d' = b * d₁ := by
    refine hDP d' hd'D (b * d₁) (D.mul_mem hb.1 hd₁D) ?_
    have e : d' * (b * d₁)⁻¹ = (s * d₁ * s⁻¹ * d'⁻¹)⁻¹ * r := by
      have e1 : s * d₁ * s⁻¹ = r * b * d₁ := by rw [hrb']; group
      calc d' * (b * d₁)⁻¹ = (s * d₁ * s⁻¹ * d'⁻¹)⁻¹ * (s * d₁ * s⁻¹) * (b * d₁)⁻¹ := by group
        _ = (s * d₁ * s⁻¹ * d'⁻¹)⁻¹ * (r * b * d₁) * (b * d₁)⁻¹ := by rw [e1]
        _ = (s * d₁ * s⁻¹ * d'⁻¹)⁻¹ * r := by group
    rw [e]
    exact P₀.mul_mem (P₀.inv_mem hr₁) hr
  obtain ⟨a, a', haa⟩ := exists_diag_of_mem hdiag hb.1 (hDL hb.1)
  have hprod : a * a' = 1 := (hc.mem_centralizer_V1_iff_diag ⟨b, hDL hb.1⟩ a a' haa).mp hb.2
  have hψbd : ψ ⟨b * d₁, (fsuL0 T L).mul_mem (hDL hb.1) hd₁L⟩ =
      (diagOf (a * ω), diagOf (a' * ω)) := by
    have e : (⟨b * d₁, (fsuL0 T L).mul_mem (hDL hb.1) hd₁L⟩ : ↥(fsuL0 T L)) =
        ⟨b, hDL hb.1⟩ * ⟨d₁, hd₁L⟩ := rfl
    rw [e, map_mul, haa, hψd₁]
    simp only [Prod.mk_mul_mk, ← diagHom_apply, ← map_mul]
  have hψd'' : ψ ⟨d', hd'L⟩ = ψ ⟨b * d₁, (fsuL0 T L).mul_mem (hDL hb.1) hd₁L⟩ := by
    congr 1
    exact Subtype.ext hd'eq
  rw [hψd', hψbd] at hψd''
  have hfst : Units.map τ.toMonoidHom ω = a * ω := by
    have h1 := congrArg (fun p => ((p.1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0) hψd''
    simp only [coe_diagOf] at h1
    exact Units.ext (by simpa using h1)
  have hsnd : Units.map τ.toMonoidHom ω = a' * ω := by
    have h1 := congrArg (fun p => ((p.2 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0) hψd''
    simp only [coe_diagOf] at h1
    exact Units.ext (by simpa using h1)
  have haa1 : a = a' := mul_right_cancel (hfst.symm.trans hsnd)
  have ha1 : a = 1 := by
    have h3 := pow_three_eq_one_of_card_four hK4 a
    rw [← haa1] at hprod
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, hprod, inv_one, one_mul]
  have hτω : Units.map τ.toMonoidHom ω = ω := by rw [hfst, ha1, one_mul]
  have hτ : τ = 1 := by
    ext x
    rw [RingAut.one_apply]
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_of_prime_card hU hω (g' := Units.mk0 x hx))
      have h1 : Units.map τ.toMonoidHom (Units.mk0 x hx) = Units.mk0 x hx := by
        rw [← hm, map_zpow, hτω]
      have h2 := congrArg Units.val h1
      rwa [Units.coe_map, Units.val_mk0] at h2
  subst hτ
  rcases hform with hf | hf
  · rw [Om4.frM_one, mul_one] at hf
    exact hc.mem_r0_of_form h37c h38c h2 hs hf
  exfalso
  obtain ⟨d₂, hd₂D, hd₂L, hψd₂⟩ := exists_mem_of_diag hdiag ω ω⁻¹
  have hd₂B : d₂ ∈ B := ⟨hd₂D, (hc.mem_centralizer_V1_iff_diag ⟨d₂, hd₂L⟩ ω ω⁻¹ hψd₂).mpr
    (mul_inv_cancel ω)⟩
  obtain ⟨d₃, hd₃D, hd₃L, hψd₃, hmem₃⟩ :=
    hc.conj_diag_swap h37c h38c hdiag hs hA hB' hf hd₂L hψd₂
  have hr₃ : s * d₂ * s⁻¹ * d₃⁻¹ ∈ P₀ := ⟨hmem₃, hconjL d₂ hd₂L d₃ hd₃L⟩
  have hr₄ := hsB d₂ hd₂B
  have hd₃eq : d₃ = d₂ := by
    refine hDP d₃ hd₃D d₂ hd₂D ?_
    have e : d₃ * d₂⁻¹ = (s * d₂ * s⁻¹ * d₃⁻¹)⁻¹ * (s * d₂ * s⁻¹ * d₂⁻¹) := by group
    rw [e]
    exact P₀.mul_mem (P₀.inv_mem hr₃) hr₄
  have hψ := congrArg (fun x : G => x) hd₃eq
  have h5 : ψ ⟨d₃, hd₃L⟩ = ψ ⟨d₂, hd₂L⟩ := by
    congr 1
    exact Subtype.ext hd₃eq
  rw [hψd₃, hψd₂] at h5
  have h6 := congrArg (fun p => ((p.1 : SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) 0 0) h5
  simp only [coe_diagOf] at h6
  have h7 : ω⁻¹ = ω := Units.ext (by simpa using h6)
  apply hω
  have h3 := pow_three_eq_one_of_card_four hK4 ω
  calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
    _ = ω ^ 3 * (ω * ω⁻¹)⁻¹ := by rw [h7]
    _ = 1 := by rw [h3, mul_inv_cancel, inv_one, one_mul]

theorem pCoreOf_le_r0 (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) {X : Subgroup G}
    (hTX : T ≤ X) (hDX : D ≤ X) :
    pCoreOf 2 X ≤ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le
    (CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTX)
  have hXO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  intro s hsO
  have hs : s ∈ T := hOT hsO
  have hcomm : ∀ d ∈ D, s * d * s⁻¹ * d⁻¹ ∈ T ⊓ fsuL0 T L := by
    intro d hd
    have h1 : d * s⁻¹ * d⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (hXO (hDX hd)) _).mp (inv_mem hsO)
    have e : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
    refine ⟨hOT (by rw [e]; exact mul_mem hsO h1), (fsuL0 T L).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 hs) d).mp (hDL hd))
      ((fsuL0 T L).inv_mem (hDL hd))⟩
  exact hc.mem_r0_of_comm h37c h38c h2 hD hdiag hs (fun b hb => hcomm b hb.1)
    (fun d hd => Subgroup.mem_sup_left (hcomm d hd))

theorem inf_le_r0 (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) {Kc : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (Kc : Set G)) (hDK : D ≤ Subgroup.normalizer (Kc : Set G))
    (hKV : Kc ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hBTK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T ⊓ Kc : Subgroup G) : Set G)) :
    T ⊓ Kc ≤ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set B := D ⊓ Subgroup.centralizer (V₁ : Set G) with hB
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hN₀eq : N₀ = P₀ ⊔ D :=
    le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD)
      (sup_le S.isSylowTwoOf_T_inf_L0_normalizer.1 hD.1)
  have hDN : D ≤ Subgroup.normalizer (P₀ : Set G) := hD.1.trans inf_le_right
  have hset2 : (N₀ : Set G) = (P₀ : Set G) * (D : Set G) := by
    rw [hN₀eq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P₀ D hDN
  have hTN := T_le_normalizer_N0 (T := T) (L := L)
  rintro s ⟨hs, hsK⟩
  have hconjL : ∀ d ∈ D, s * d * s⁻¹ * d⁻¹ ∈ fsuL0 T L := fun d hd => (fsuL0 T L).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 hs) d).mp (hDL hd))
    ((fsuL0 T L).inv_mem (hDL hd))
  have hsB : ∀ b ∈ B, s * b * s⁻¹ * b⁻¹ ∈ P₀ := by
    intro b hb
    have h1 : b * s⁻¹ * b⁻¹ ∈ T ⊓ Kc :=
      (Subgroup.mem_normalizer_iff.mp (hBTK hb) _).mp (inv_mem ⟨hs, hsK⟩)
    have e : s * b * s⁻¹ * b⁻¹ = s * (b * s⁻¹ * b⁻¹) := by group
    exact ⟨by rw [e]; exact T.mul_mem hs h1.1, hconjL b hb.1⟩
  have hsD : ∀ d ∈ D, s * d * s⁻¹ * d⁻¹ ∈ P₀ ⊔ B := by
    intro d hd
    have hN : s * d * s⁻¹ * d⁻¹ ∈ (N₀ : Set G) :=
      N₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTN hs) d).mp (hD.1 hd))
        (N₀.inv_mem (hD.1 hd))
    have hK : s * d * s⁻¹ * d⁻¹ ∈ Kc := by
      have h1 : d * s⁻¹ * d⁻¹ ∈ Kc :=
        (Subgroup.mem_normalizer_iff.mp (hDK hd) _).mp (Kc.inv_mem hsK)
      have e : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
      rw [e]
      exact Kc.mul_mem hsK h1
    rw [hset2] at hN
    obtain ⟨r, hr, d'', hd'', hrd⟩ := hN
    have hrd' : r * d'' = s * d * s⁻¹ * d⁻¹ := hrd
    have hd''K : d'' ∈ Kc := by
      have hle : Subgroup.zpowers d'' ≤ P₀ ⊔ Kc := by
        rw [Subgroup.zpowers_le]
        have e : d'' = r⁻¹ * (s * d * s⁻¹ * d⁻¹) := by rw [← hrd']; group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_left (inv_mem hr)) (Subgroup.mem_sup_right hK)
      have hodd : Odd (Nat.card (Subgroup.zpowers d'')) := by
        rw [Nat.card_zpowers]
        exact hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hd'')
      have h2 := Vol2.Ch10.SecB.C11AmS.le_of_odd hle hodd
        (B6.isTwoQuotient_of_sup_eq (S.hyp.fsu.sylow.1.to_le inf_le_left)
          (sup_le (inf_le_left.trans hTK) Subgroup.le_normalizer) rfl)
      exact h2 (Subgroup.mem_zpowers d'')
    have hd''B : d'' ∈ B := ⟨hd'', hKV hd''K⟩
    rw [← hrd']
    exact mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hd''B)
  exact hc.mem_r0_of_comm h37c h38c h2 hD hdiag hs hsB hsD

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
