module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce
public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std
public import CFSG.RankThree.PartTwo.Sec21.Hering2119TypeC
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)
open CFSG.RankThree.PartTwo.Sec21.Hering2119

theorem exists_typeC_model_sub {X : Type} [Group X] [Finite X] {Ē : Subgroup (MulAut X)}
    (hC : IsTypeCSub X Ē) {n : ℕ} (hn : 1 ≤ n) (eL : X ≃* projSL 3 (GaloisField 2 n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Φ : X ≃* projectiveSL 3 F)
      (g : GL (Fin 3) F) (τ : Fˣ), Nat.card F = 2 ^ n ∧ τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      (∀ σ ∈ Ē, ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z,
          Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) ∧
      (∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ σ ∈ Ē, ∀ z,
          Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) := by
  obtain ⟨π, p', f, F, instF, hPi, hmod, e, D, hD, hconj, hconj'⟩ := hC
  have hFin : Finite F := hPi.finite
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    hn hmod hcard
    (Sec19.Step1917EqProof.card_kStar hn (Or.inr ⟨eL⟩))
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
  set Φ : X ≃* projectiveSL 3 F := e.trans Ξ.symm with hΦ
  have hΦe : ∀ z, pglEmb (Φ z) = (e z : ProjGenLinGroup (Fin 3) F) := by
    intro z
    have h1 := congrArg Subtype.val (Ξ.apply_symm_apply (e z))
    have h2 : ((Ξ (Φ z) : projImage (Sec4.slPi true 3 (2 ^ f) F)) :
        ProjGenLinGroup (Fin 3) F) = pglEmb (Φ z) := rfl
    rw [← h2]
    exact h1
  have hkey : ∀ (τ : MulAut X) (y : GL (Fin 3) F),
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
    rw [hy', map_mul, map_mul, map_mul, LinearFlag.conjAut_scalar, one_mul, map_mul, map_mul]
  refine ⟨F, instF, hFin, Φ, g, Units.mk0 τ₀ hτ₀0, hFcard, ?_, ?_, ?_, ?_⟩
  · exact Units.ext (by simpa using hτ₀)
  · intro h
    exact hτ₀1 (by simpa using congrArg Units.val h)
  · intro σ hσ
    obtain ⟨y, hyD, hy⟩ := hconj σ hσ
    obtain ⟨l, s, t, hs, ht, hyst⟩ := hdiag y hyD
    refine ⟨s, t, (mem_rootsOfUnity 3 s).mp hs, (mem_rootsOfUnity 3 t).mp ht, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]
  · intro s t hs ht
    obtain ⟨y, hyD, l, hyst⟩ := hsurj s ((mem_rootsOfUnity 3 s).mpr hs) t
      ((mem_rootsOfUnity 3 t).mpr ht)
    obtain ⟨τ, hτ, hy⟩ := hconj' y hyD
    refine ⟨τ, hτ, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]

theorem eInvFour_of_model {X : Type} [Group X] [Finite X] {Ē : Subgroup (MulAut X)}
    {F : Type} [Field F] [Finite F] [CharP F 2] (Φ : X →* projectiveSL 3 F)
    (hΦ : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card Φ.ker)) (g : GL (Fin 3) F) {τ : Fˣ} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hpart1 : ∀ σ ∈ Ē, ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z,
      Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z))
    (hpart2 : ∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ σ ∈ Ē, ∀ z,
      Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) :
    EInvFour X Ē := by
  obtain ⟨W₀, hW0ab, hW04, hW0inv, w₀, hw₀, hw₀ne⟩ := exists_std_four hτ3 hτ1
  set cg : MulAut (projectiveSL 3 F) := conjAut 3 F g with hcg
  have hconjc : ∀ (d : GL (Fin 3) F) (w : projectiveSL 3 F),
      conjAut 3 F (g * d * g⁻¹) (cg w) = cg (conjAut 3 F d w) := by
    intro d w
    rw [map_mul, map_mul, map_inv]
    simp [MulAut.mul_apply, hcg]
  set W : Subgroup (projectiveSL 3 F) := W₀.map cg.toMonoidHom with hW
  have hmemW : ∀ x, x ∈ W ↔ ∃ w ∈ W₀, cg w = x := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hWab : IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.map hW0ab _
  have hW4 : Nat.card W = 4 := by
    rw [hW, Subgroup.card_map_of_injective
      (show Function.Injective cg.toMonoidHom from cg.injective), hW04]
  obtain ⟨S, hSmem, hSel, hS4, hSsurj⟩ := exists_lift_four hΦ hker hodd hWab hW4
  have hSinv : ∀ σ ∈ Ē, ∀ x ∈ S, σ x ∈ S := by
    intro σ hσ x hx
    rw [hSmem] at hx ⊢
    obtain ⟨s, t, hs, ht, hst⟩ := hpart1 σ hσ
    refine ⟨?_, ?_⟩
    · rw [hst]
      obtain ⟨w, hw, hwx⟩ := (hmemW _).mp hx.1
      refine (hmemW _).mpr ⟨conjAut 3 F (diagUnits 1 s t) w, hW0inv s t hs ht w hw, ?_⟩
      rw [← hwx, hconjc]
    · rw [← map_pow, hx.2, map_one]
  refine ⟨S, hSel, hS4, hSinv, ?_⟩
  obtain ⟨σ, hσ, hσΦ⟩ := hpart2 τ 1 hτ3 (one_pow 3)
  obtain ⟨x, hxS, hxw⟩ := hSsurj (cg w₀) ((hmemW _).mpr ⟨w₀, hw₀, rfl⟩)
  refine ⟨σ, hσ, x, hxS, fun h => hw₀ne ?_⟩
  have h1 := congrArg Φ h
  rw [hσΦ, hxw, hconjc] at h1
  exact cg.injective h1

theorem eInvFour_of_typeC {X : Type} [Group X] [Finite X] {Ē : Subgroup (MulAut X)} {n : ℕ}
    (hn : 0 < n) (eL : X ≃* projSL 3 (GaloisField 2 n)) (hC : IsTypeCSub X Ē) :
    EInvFour X Ē := by
  obtain ⟨F, hF, hFin, Φ, g, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
    exists_typeC_model_sub hC hn eL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  refine eInvFour_of_model Φ.toMonoidHom Φ.surjective ?_ ?_ g hτ3 hτ1 hpart1 hpart2
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr Φ.injective]
    exact bot_le
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr Φ.injective, Subgroup.card_bot]
    exact odd_one

theorem toGL_injective_aux {K : Type} [Field K] {a b : Matrix.SpecialLinearGroup (Fin 3) K}
    (h : Matrix.SpecialLinearGroup.toGL a = Matrix.SpecialLinearGroup.toGL b) : a = b := by
  have h' := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h'
  exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun h' i) j)

theorem exists_typeCSL_model_sub {X : Type} [Group X] [Finite X] {Ē : Subgroup (MulAut X)}
    (hC : IsTypeCSubSL X Ē) {n : ℕ} (hn : 2 ≤ n) (eL : X ≃* SL3 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Φ : X →* projectiveSL 3 F),
      Function.Surjective Φ ∧ Φ.ker ≤ Subgroup.center X ∧ Odd (Nat.card Φ.ker) ∧
      ∃ (g : GL (Fin 3) F) (τ : Fˣ), Nat.card F = 2 ^ n ∧ τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      (∀ σ ∈ Ē, ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z,
          Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) ∧
      (∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ σ ∈ Ē, ∀ z,
          Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) := by
  obtain ⟨π, p', f, K, instK, hPi, hmod, e, D, hD, hconj, hconj'⟩ := hC
  have hFin : Finite K := hPi.finite
  have hcard : Nat.card (Sec4.slPi π 3 (p' ^ f) K) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr eL.toEquiv,
      Sec19.Step1911Proof.card_SL3 (by omega), pow_mul]
    ring
  obtain ⟨hπ, hKcard⟩ := Sec19.Step1911EndProof.card_slPi_eq hPi hmod hn hcard
  subst hπ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  obtain ⟨g, -, hdiag, hsurj⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  have hτ₀0 : τ₀ ≠ 0 := by
    rintro rfl
    norm_num at hτ₀
  set Ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    e.trans (Sec4.slPiTrueEquiv (p' ^ f) K) with hΨ
  set Φ : X →* projectiveSL 3 K := (proj 3 K).comp Ψ.toMonoidHom with hΦ
  have hΦx : ∀ x, Φ x = proj 3 K (Ψ x) := fun x => rfl
  have hkey : ∀ (τ : MulAut X) (y : GL (Fin 3) K),
      (∀ z, ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹) →
      ∀ z, Φ (τ z) = conjAut 3 K y (Φ z) := by
    intro τ y h z
    have hΨτ : Ψ (τ z) = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        3 K y (Ψ z) := by
      apply toGL_injective_aux
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
        hΨ, MulEquiv.trans_apply, MulEquiv.trans_apply, Sec4.toGL_slPiTrueEquiv,
        Sec4.toGL_slPiTrueEquiv, h z]
    rw [hΦx, hΦx, hΨτ, conjAut_proj]
  have hframe : ∀ (y : GL (Fin 3) K) (l s t : Kˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t →
      conjAut 3 K y = conjAut 3 K (g * diagUnits 1 s t * g⁻¹) := by
    intro y l s t hy
    have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = _ := by rw [hy]
    rw [hy', map_mul, map_mul, map_mul, LinearFlag.conjAut_scalar, one_mul, map_mul, map_mul]
  have hkerΨ : ∀ x : X, x ∈ Φ.ker → Ψ x ∈ scalars 3 K := fun x hx =>
    LinearFlag.proj_eq_one_iff.mp hx
  have hker_center : Φ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro z
    have hc : Ψ x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [← scalars_eq_center]
      exact hkerΨ x hx
    apply Ψ.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hc (Ψ z))
  have hker3 : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hkerΨ x hx
    apply Ψ.injective
    rw [map_pow, map_one]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h1 : ((Ψ x ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Matrix.scalar (Fin 3) (c : K)) ^ 3 := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hxc]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, hc]
    simp
  have hodd : Odd (Nat.card Φ.ker) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2 : 2 ∣ Nat.card Φ.ker := even_iff_two_dvd.mp hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hx3 : x ^ 3 = 1 := Subtype.ext (hker3 x x.2)
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at h3
    omega
  have hsurjΦ : Function.Surjective Φ := (LinearFlag.proj_surjective 3 K).comp Ψ.surjective
  refine ⟨K, instK, hFin, Φ, hsurjΦ, hker_center, hodd, g, Units.mk0 τ₀ hτ₀0, hKcard, ?_, ?_,
    ?_, ?_⟩
  · exact Units.ext (by simpa using hτ₀)
  · intro h
    exact hτ₀1 (by simpa using congrArg Units.val h)
  · intro σ hσ
    obtain ⟨y, hyD, hy⟩ := hconj σ hσ
    obtain ⟨l, s, t, hs, ht, hyst⟩ := hdiag y hyD
    refine ⟨s, t, (mem_rootsOfUnity 3 s).mp hs, (mem_rootsOfUnity 3 t).mp ht, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]
  · intro s t hs ht
    obtain ⟨y, hyD, l, hyst⟩ := hsurj s ((mem_rootsOfUnity 3 s).mpr hs) t
      ((mem_rootsOfUnity 3 t).mpr ht)
    obtain ⟨τ, hτ, hy⟩ := hconj' y hyD
    refine ⟨τ, hτ, fun z => ?_⟩
    rw [hkey _ y hy z, hframe y l s t hyst]

theorem eInvFour_of_typeCSL {X : Type} [Group X] [Finite X] {Ē : Subgroup (MulAut X)} {n : ℕ}
    (hn : 2 ≤ n) (eL : X ≃* SL3 n) (hC : IsTypeCSubSL X Ē) : EInvFour X Ē := by
  obtain ⟨F, hF, hFin, Φ, hΦ, hker, hodd, g, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
    exists_typeCSL_model_sub hC hn eL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  exact eInvFour_of_model Φ hΦ hker hodd g hτ3 hτ1 hpart1 hpart2

end CFSG.RankThree.PartTwo.Sec21.Hering214
