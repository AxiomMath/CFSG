module

public import CFSG.Quasithin.Background.Harris.KFact2d.Lin2
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelL3
public import CFSG.Quasithin.Background.Harris.KFact2d.ClassTransport
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.AschTight.S19KLinFL
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3
open scoped MatrixGroups Matrix


variable {p : ℕ} [Fact p.Prime]

theorem scL_eq_scalar (a : (ZMod p)ˣ) : scL p a = Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  apply Units.ext
  simp [coe_scL, Matrix.GeneralLinearGroup.coe_scalar]

theorem exists_scL_of_central {A : GL (Fin 2) (ZMod p)} (h : ∀ B : GL (Fin 2) (ZMod p), B * A = A * B) :
    ∃ a : (ZMod p)ˣ, A = scL p a := by
  have : A ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := Subgroup.mem_center_iff.mpr h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at this
  obtain ⟨a, rfl⟩ := this
  exact ⟨a, (scL_eq_scalar a).symm⟩

theorem exists_scL_of_mem_center {U : Subgroup (PSL3 p)} (hp2 : p ≠ 2) (hU : SpecialSylowL p U)
    {b : PSL3 p} (hb1 : b ∈ Subgroup.centralizer (E2P.zOf U : Set (PSL3 p)))
    (hb2 : b ∈ Subgroup.centralizer ((Subgroup.centralizer (E2P.zOf U : Set (PSL3 p)) : Subgroup (PSL3 p)) : Set (PSL3 p))) :
    ∃ a : (ZMod p)ˣ, b = rhoL p (scL p a) := by
  have hC : Subgroup.centralizer (E2P.zOf U : Set (PSL3 p)) = leviC p :=
    centralizer_zOf_eq_leviC hp2 hU.1 hU.2.1
  rw [hC] at hb1 hb2
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hb1
  obtain ⟨a, ha⟩ := exists_scL_of_central (A := A) fun B => by
    have := Subgroup.mem_centralizer_iff.mp hb2 (rhoL p B) ⟨_, ⟨B, rfl⟩, rfl⟩
    exact commute_of_piL_commute this
  exact ⟨a, by rw [← ha]; rfl⟩


theorem g_blockzero {g : Matrix (Fin 3) (Fin 3) (ZMod p)} (hp2 : p ≠ 2)
    (h : g * ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  rw [coe_zt] at h
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply] at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by linear_combination e02 : (2 : ZMod p) * g 0 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination e12 : (2 : ZMod p) * g 1 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -e20 : (2 : ZMod p) * g 2 0 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -e21 : (2 : ZMod p) * g 2 1 = 0)).resolve_left h2

theorem comm_levi_scL {g : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (h02 : g 0 2 = 0) (h12 : g 1 2 = 0) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) (a : (ZMod p)ˣ) :
    g * ((leviHom p (scL p a) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((leviHom p (scL p a) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviHom, coe_scL, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, h02, h12, h20, h21] <;> ring

theorem transpose_leviHom_scL (a : (ZMod p)ˣ) :
    ((leviHom p (scL p a) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ =
      ((leviHom p (scL p a) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviHom, coe_scL, Matrix.scalar_apply, Matrix.diagonal_apply]


theorem linClass_zmod
    (hp2 : p ≠ 2) (hp5 : 5 ≤ p) :
    CFSG.ClassicalInvolution.RouteD.Gaps.LinearAutClassification (ZMod p) 3 := by
  have : Fintype (GaloisField p 1) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p 1) = Fintype.card (ZMod p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card p 1 one_ne_zero,
      pow_one, Nat.card_zmod]
  exact linAutClass_of_ringEquiv (FiniteField.ringEquivOfCardEq hc)
    (CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2
      (by rw [pow_one]; exact hp5) (le_refl 3))

theorem zc_mem_zOf {U : Subgroup (PSL3 p)} (hp2 : p ≠ 2) (hU : SpecialSylowL p U) :
    zc p ∈ E2P.zOf U := by
  obtain ⟨-, hUB, c, d, hQ, hc, hd⟩ := hU
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  · rw [zc_eq_sq hp2 hQ]
    exact U.mul_mem hc hc
  · exact (zc_comm_levi (hUB hu)).symm


theorem f3_core_lin
    (hp4 : p % 4 = 3) (hp5 : 5 ≤ p) {U : Subgroup (PSL3 p)}
    (hU : SpecialSylowL p U) (α : MulAut (PSL3 p)) (hαα : α * α = 1)
    (hno : ∀ y : PSL3 p, α ≠ MulAut.conj y) (hfix : ∀ w ∈ E2P.zOf U, α w = w) (a : (ZMod p)ˣ) :
    α (rhoL p (scL p a)) = (rhoL p (scL p a))⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have hcl := linClass_zmod (p := p) hp2 hp5
  obtain ⟨α', g, φ, ε, hα, hform⟩ := hcl (PSL3 p) (piL p) piL_surjective
    (by rw [ker_piL]) α
  have hφ : ∀ x, φ x = x := by
    intro x
    have := RingHom.ext_zmod (φ : ZMod p →+* ZMod p) (RingHom.id _)
    exact congrArg (fun f : ZMod p →+* ZMod p => f x) this
  have hform' : ∀ x : SL(3, ZMod p), ((α' x : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.twist ε x *
        ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    intro x
    rw [hform x]
    have : φ.mapMatrix (if ε then ((x⁻¹ : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ
        else (x : Matrix (Fin 3) (Fin 3) (ZMod p))) = (if ε then ((x⁻¹ : SL(3, ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ else (x : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
      ext i j
      simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply, hφ]
    rw [this]
    rfl
  have hαa : ∀ x, piL p (α' x) = α (piL p x) := fun x => hα x
  have hfixz : α (zc p) = zc p := hfix _ (zc_mem_zOf hp2 hU)
  have hk : (zt p)⁻¹ * α' (zt p) ∈ Subgroup.center SL(3, ZMod p) := by
    rw [← ker_piL]
    show piL p ((zt p)⁻¹ * α' (zt p)) = 1
    rw [map_mul, map_inv, hαa]
    change (piL p (zt p))⁻¹ * α (zc p) = 1
    rw [hfixz]
    exact inv_mul_cancel _
  obtain ⟨c, hc3, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have hmat : ((α' (zt p) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * Matrix.scalar (Fin 3) c := by
    have h1 : ((α' (zt p) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (((zt p)⁻¹ * α' (zt p) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h1, hc]
  have hztt : ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    rw [coe_zt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hztz : (zt p : SL(3, ZMod p)) * zt p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_zt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hzinv : (zt p : SL(3, ZMod p))⁻¹ = zt p := inv_eq_of_mul_eq_one_right hztz
  have htwz : CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.twist ε (zt p) =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    cases ε
    · rfl
    · show (((zt p : SL(3, ZMod p))⁻¹ : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ = _
      rw [hzinv, hztt]
  have hconj : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * Matrix.scalar (Fin 3) c := by
    have h1 := hform' (zt p)
    rw [htwz, hmat] at h1
    exact h1.symm
  have htr : c = 1 := by
    have h1 := congrArg Matrix.trace hconj
    rw [Matrix.trace_units_conj] at h1
    simp [coe_zt, Matrix.trace_fin_three, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply] at h1
    exact h1.symm
  have hcomm : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    rw [htr, map_one, mul_one] at hconj
    have h1 := congrArg (fun M => M * (g : Matrix (Fin 3) (Fin 3) (ZMod p))) hconj
    simp only [mul_assoc, Units.inv_mul, mul_one] at h1
    exact h1
  obtain ⟨h02, h12, h20, h21⟩ := g_blockzero hp2 hcomm
  cases ε with
  | false =>
    exfalso
    obtain ⟨y, hy⟩ := CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.lin_inner (piL p)
      piL_surjective (by rw [ker_piL]) hα hform' hαα
    exact hno y hy
  | true =>
    have hxinv : (leviHom p (scL p a))⁻¹ = leviHom p (scL p a⁻¹) := by
      rw [← map_inv, ← map_inv]
    have hM := comm_levi_scL h02 h12 h20 h21 a⁻¹
    have hT := transpose_leviHom_scL a⁻¹
    have hx : ((α' (leviHom p (scL p a)) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        (((leviHom p (scL p a))⁻¹ : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      rw [hform']
      show (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (((leviHom p (scL p a))⁻¹ : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * _ = _
      rw [hxinv, hT, hM, mul_assoc, Units.mul_inv, mul_one]
    have hx' : α' (leviHom p (scL p a)) = (leviHom p (scL p a))⁻¹ := Subtype.ext hx
    calc α (rhoL p (scL p a)) = α (piL p (leviHom p (scL p a))) := rfl
      _ = piL p (α' (leviHom p (scL p a))) := (hα _).symm
      _ = piL p ((leviHom p (scL p a))⁻¹) := by rw [hx']
      _ = (piL p (leviHom p (scL p a)))⁻¹ := map_inv _ _


theorem f3At_special
    (hp4 : p % 4 = 3) {U : Subgroup (PSL3 p)}
    (hU : SpecialSylowL p U) : F3At (PSL3 p) U := by
  have hp2 : p ≠ 2 := by omega
  intro α hαα hno hfix b ⟨hb1, hb2⟩ hodd
  obtain ⟨a, rfl⟩ := exists_scL_of_mem_center hp2 hU hb1 hb2
  by_cases hp5 : 5 ≤ p
  · exact f3_core_lin hp4 hp5 hU α hαα hno hfix a
  · have hp3 : p = 3 := by
      have := (Fact.out : p.Prime).two_le
      omega
    have ha2 : a ^ 2 = 1 := by
      have := ZMod.units_pow_card_sub_one_eq_one p a
      rwa [show p - 1 = 2 by omega] at this
    have hb2' : rhoL p (scL p a) ^ 2 = 1 := by
      rw [rhoL_scL_pow, ha2, map_one, map_one]
    have hord : orderOf (rhoL p (scL p a)) ∣ 2 := orderOf_dvd_of_pow_eq_one hb2'
    have h1 : orderOf (rhoL p (scL p a)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have hb1' : rhoL p (scL p a) = 1 := orderOf_eq_one_iff.mp h1
    rw [hb1']
    simp

theorem f3_psl
    {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hp4 : p % 4 = 3) (hK : IsPSL 3 p 1 ↥K) (hS : IsSylowTwoOf S K) (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {u : X} (huu : u * u = 1) (huK : u ∉ K)
    (huz : u ∈ Subgroup.centralizer (E2P.zOf S : Set X)) :
    ∀ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), Odd (orderOf b) →
      u * b * u⁻¹ = b⁻¹ := by
  obtain ⟨e, U₀, hU₀, hmap⟩ := exists_equiv_special (p := p) (by omega) hK hS
  have h := f3At_special hp4 hU₀
  rw [← hmap] at h
  exact f3_of_model hKn hC hS.1 (F3At.of_map e _ h) huu huK huz

end CFSG.Quasithin.Background.Harris.KFact2d
