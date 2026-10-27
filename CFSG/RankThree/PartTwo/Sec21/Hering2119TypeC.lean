module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119AutTorus
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)

section Model

variable {F : Type} [Field F]

theorem range_pglEmb_eq (q : ℕ) :
    (pglEmb (F := F)).range = projImage (Sec4.slPi true 3 q F) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨s, rfl⟩ := proj_surjective 3 F z
    exact ⟨Matrix.SpecialLinearGroup.toGL s, (Sec4.mem_slPi_true q).mpr s.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' := (Sec4.mem_slPi_true q).mp hy
    let s0 : Matrix.SpecialLinearGroup (Fin 3) F := ⟨(y : Matrix (Fin 3) (Fin 3) F), hy'⟩
    refine ⟨proj 3 F s0, ?_⟩
    rw [pglEmb_proj]
    congr 1
    exact Units.ext rfl

end Model


section Extract

variable {G : Type} [Group G] [Finite G]

theorem exists_typeC_model {A K : Subgroup G} (hC : Sec4.IsTypeCOn A K) {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar K ≃* projSL 3 (GaloisField 2 n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Φ : lBar K ≃* projectiveSL 3 F)
      (g : GL (Fin 3) F) (τ : Fˣ), Nat.card F = 2 ^ n ∧ τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      (∀ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (K : Set G)),
        ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z,
          Φ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, haN⟩) z) =
            conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) ∧
      (∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ (a : G) (_ : a ∈ A)
        (haN : a ∈ Subgroup.normalizer (K : Set G)), ∀ z,
          Φ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, haN⟩) z) =
            conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) := by
  obtain ⟨π, p', f, F, instF, hPi, hmod, e, D, hD, hconj, hconj'⟩ := hC
  have hFin : Finite F := hPi.finite
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    (by omega) hmod hcard
    (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have hFcard : Nat.card F = 2 ^ f := by simpa [Sec4.piCard] using hPi.card
  obtain ⟨g, -, hdiag, hsurj⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  have hτ₀0 : τ₀ ≠ 0 := by
    rintro rfl
    norm_num at hτ₀
  set Ξ : projectiveSL 3 F ≃* projImage (Sec4.slPi true 3 (2 ^ f) F) :=
    (MonoidHom.ofInjective pglEmb_injective).trans
      (MulEquiv.subgroupCongr (range_pglEmb_eq _)) with hΞ
  set Φ : lBar K ≃* projectiveSL 3 F := e.trans Ξ.symm with hΦ
  have hΦe : ∀ z, pglEmb (Φ z) = (e z : ProjGenLinGroup (Fin 3) F) := by
    intro z
    have h1 := congrArg Subtype.val (Ξ.apply_symm_apply (e z))
    have h2 : ((Ξ (Φ z) : projImage (Sec4.slPi true 3 (2 ^ f) F)) :
        ProjGenLinGroup (Fin 3) F) = pglEmb (Φ z) := rfl
    rw [← h2]
    exact h1
  have hkey : ∀ (τ : MulAut (lBar K)) (y : GL (Fin 3) F),
      (∀ z, (e (τ z) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) F) * (ProjGenLinGroup.mk y)⁻¹) →
      ∀ z, Φ (τ z) = conjAut 3 F y (Φ z) := by
    intro τ y h z
    apply pglEmb_injective
    rw [hΦe, pglEmb_conjAut, hΦe, h z]
  have hframe : ∀ (y : GL (Fin 3) F) (l s t : Fˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t →
      conjAut 3 F y = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) := by
    intro y l s t hy
    have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = _ := by rw [hy]
    rw [hy', map_mul, map_mul, map_mul, conjAut_scalar, one_mul, map_mul, map_mul]
  have hτu0 : τ₀ ≠ 0 := hτ₀0
  refine ⟨F, instF, hFin, Φ, g, Units.mk0 τ₀ hτ₀0, hFcard, ?_, ?_, ?_, ?_⟩
  · exact Units.ext (by simpa using hτ₀)
  · intro h
    exact hτ₀1 (by simpa using congrArg Units.val h)
  · intro a haA haN
    have hτ : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, haN⟩) ∈ Sec4.autThetaQuot A K :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, haA, rfl⟩
    obtain ⟨y, hyD, hy⟩ := hconj _ hτ
    obtain ⟨l, s, t, hs, ht, hyst⟩ := hdiag y hyD
    refine ⟨s, t, (mem_rootsOfUnity 3 s).mp hs, (mem_rootsOfUnity 3 t).mp ht, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]
  · intro s t hs ht
    obtain ⟨y, hyD, l, hyst⟩ := hsurj s ((mem_rootsOfUnity 3 s).mpr hs) t
      ((mem_rootsOfUnity 3 t).mpr ht)
    obtain ⟨τ, hτ, hy⟩ := hconj' y hyD
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    refine ⟨a, haA, haN, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]


theorem diagUnits_pow {F : Type} [Field F] (a b c : Fˣ) (k : ℕ) :
    (diagUnits a b c : GL (Fin 3) F) ^ k = diagUnits (a ^ k) (b ^ k) (c ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    apply Units.ext
    rw [coe_diagUnits, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  | succ k ih => rw [pow_succ, ih, Sec4.diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem T_apply_of_commute {K : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ K) (hax : a * x = x * a) :
    Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, ha⟩) ((⟨x, hx⟩ : K) : lBar K) =
      ((⟨x, hx⟩ : K) : lBar K) := by
  rw [Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  rw [Sec4.normalizerMonoidHom_apply_coe, hax]
  group

theorem exists_exp_of_centralizes {A K : Subgroup G} (hC : Sec4.IsTypeCOn A K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar K ≃* projSL 3 (GaloisField 2 n)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpn : p ∣ 2 ^ n - 1) {P : Subgroup G} (hPK : P ≤ K) (hPcard : Nat.card P = p ^ 2)
    (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hPθ : ∀ (x : G) (hx : x ∈ P), ((⟨x, hPK hx⟩ : K) : lBar K) = 1 → x = 1)
    (hPA : ∀ x ∈ P, ∀ a ∈ A, a * x = x * a) {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgP : ∀ x ∈ P, g * x = x * g) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ x ∈ A, g * x * g⁻¹ * (x ^ e)⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
  obtain ⟨F, instF, hFin, Φ, gf, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
    exists_typeC_model hC hn eL
  set T : Subgroup.normalizer (K : Set G) →* MulAut (lBar K) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hT
  set φ : P →* lBar K := (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp
    (Subgroup.inclusion hPK) with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have := hPθ x.1 x.2 hx
    rw [this]
    rfl
  set Pq : Subgroup (lBar K) := φ.range with hPq
  have hPqcard : Nat.card Pq = p ^ 2 := by
    rw [hPq, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, hPcard]
  have hPqexp : ∀ z ∈ Pq, z ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hPexp x.1 x.2)
    rw [this, map_one]
  have hTP : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)), (∀ x ∈ P, a * x = x * a) →
      ∀ z ∈ Pq, T ⟨a, ha⟩ z = z := by
    rintro a ha hax _ ⟨x, rfl⟩
    exact T_apply_of_commute ha (hPK x.2) (hax x.1 x.2)
  have hcomm : ∀ z ∈ Pq, conjAut 3 F (gf * diagUnits 1 τ (τ ^ 2) * gf⁻¹) (Φ z) = Φ z := by
    intro z hz
    obtain ⟨a, haA, haN, ha⟩ := hpart2 τ (τ ^ 2) hτ3
      (by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow])
    have h1 : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, haN⟩) z = z :=
      hTP a haN (fun x hx => hPA x hx a haA) z hz
    rw [← ha z, h1]
  have hpF : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpn
  have hβ : ∀ z ∈ Pq, T ⟨g, hgK⟩ z = z := hTP g hgK hgP
  obtain ⟨e, he, hconj⟩ := conj_of_fix_transport hp hp3 hpF τ hτ3 hτ1 Φ gf Pq hPqcard hPqexp
    hcomm (T ⟨g, hgK⟩) hβ
  refine ⟨e, he, fun x hx => ?_⟩
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAK hx
  have hgxA : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA x).mp hx
  have hgxN : g * x * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := hAK hgxA
  have hxeN : x ^ e ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hxN e
  obtain ⟨s, t, hs, ht, hst⟩ := hpart1 x hx hxN
  have hcx : MulAut.congr Φ (T ⟨x, hxN⟩) = conjAut 3 F (gf * diagUnits 1 s t * gf⁻¹) := by
    ext w
    rw [MulAut.congr_apply]
    have := hst (Φ.symm w)
    rw [Φ.apply_symm_apply] at this
    exact this
  have h1 := hconj s t hs ht
  have hTgx : T ⟨g * x * g⁻¹, hgxN⟩ = T ⟨g, hgK⟩ * T ⟨x, hxN⟩ * (T ⟨g, hgK⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hTxe : T ⟨x ^ e, hxeN⟩ = (T ⟨x, hxN⟩) ^ e := by
    rw [← map_pow]
    rfl
  have hA1 : MulAut.congr Φ (T ⟨g * x * g⁻¹, hgxN⟩) =
      conjAut 3 F (gf * diagUnits 1 (s ^ e) (t ^ e) * gf⁻¹) := by
    rw [hTgx, map_mul, map_mul, map_inv, hcx, ← h1]
  have hA2 : MulAut.congr Φ (T ⟨x ^ e, hxeN⟩) =
      conjAut 3 F (gf * diagUnits 1 (s ^ e) (t ^ e) * gf⁻¹) := by
    rw [hTxe, map_pow, hcx, ← map_pow, conj_pow, diagUnits_pow, one_pow]
  have hTeq : T ⟨g * x * g⁻¹, hgxN⟩ = T ⟨x ^ e, hxeN⟩ :=
    (MulAut.congr Φ).injective (hA1.trans hA2.symm)
  refine ⟨⟨g * x * g⁻¹ * (x ^ e)⁻¹, Subgroup.mul_mem _ hgxN (Subgroup.inv_mem _ hxeN)⟩, ?_, rfl⟩
  show T _ = 1
  have : (⟨g * x * g⁻¹ * (x ^ e)⁻¹, Subgroup.mul_mem _ hgxN (Subgroup.inv_mem _ hxeN)⟩ :
      Subgroup.normalizer (K : Set G)) = ⟨g * x * g⁻¹, hgxN⟩ * ⟨x ^ e, hxeN⟩⁻¹ := rfl
  rw [this, map_mul, map_inv, hTeq, mul_inv_cancel]

end Extract

end CFSG.RankThree.PartTwo.Sec21.Hering2119
