module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5Torus
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4
open Matrix

private noncomputable def s16c11_case5_scalHom (K : Type) [Field K] :
    Kˣ →* MulAut (VM K) where
  toFun c := lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
  map_one' := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (1 : Kˣ)) 1 = 1
    rw [map_one, lr_one]
  map_mul' c d := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (c * d)) 1 =
      lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1 *
        lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
    rw [map_mul, lr_mul, mul_one]

private theorem s16c11_case5_scal_eq_range (K : Type) [Field K] :
    s16c11C5Scal K = (s16c11_case5_scalHom K).range := by
  rw [s16c11C5Scal]
  have h : {x : MulAut (VM K) | ∃ c : Kˣ,
      x = lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1} =
      Set.range (s16c11_case5_scalHom K) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range, s16c11_case5_scalHom]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  rw [h, ← MonoidHom.coe_range, Subgroup.closure_eq]

private theorem s16c11_case5_scalHom_injective (K : Type) [Field K] :
    Function.Injective (s16c11_case5_scalHom K) := by
  intro c d h
  have h1 : Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) =
      Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) :=
    congrArg (fun ψ : MulAut (VM K) =>
      Multiplicative.toAdd (ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K)))) h
  simp only [toAdd_lr, toAdd_ofAdd, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
    Units.coe_map] at h1
  exact Units.ext (Matrix.scalar_inj.mp h1)

private theorem s16c11_case5_card_scal (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) : Nat.card ↥(s16c11C5Scal K) = 3 := by
  rw [s16c11_case5_scal_eq_range]
  have hcard : Nat.card ↥((s16c11_case5_scalHom K).range) = Nat.card Kˣ := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (s16c11_case5_scalHom_injective K), Subgroup.card_top]
  rw [hcard, Nat.card_units, hK]

private theorem s16c11_case5_scal_le_centralizer_rho (K : Type) [Field K] :
    s16c11C5Scal K ≤
      Subgroup.centralizer ((rho (K := K)).range : Set (MulAut (VM K))) := by
  rw [s16c11C5Scal, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ ⟨γ, rfl⟩
  rw [rho_apply, lr_mul, lr_mul, mul_one, one_mul]
  have hcomm : Matrix.SpecialLinearGroup.toGL γ.1 *
      Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c =
      Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c *
        Matrix.SpecialLinearGroup.toGL γ.1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map]
    exact (Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _)
      ((Matrix.SpecialLinearGroup.toGL γ.1 : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)).eq.symm
  rw [hcomm]

theorem s16c11_case5_core {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {Y : Subgroup (MulAut (VM K))} (hRY : (rho (K := K)).range ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))))
    (hZY : s16c11C5Scal K ≤ Y) {𝒮 : Set (Subgroup (MulAut (VM K)))}
    (h𝒮 : ∀ A ∈ 𝒮, A = ⊥ ∨ A ∈ E3.aSet 2 Y) (h2 : IsPGroup 2 ↥(⨆ A ∈ 𝒮, A))
    (hc : (⨆ A ∈ 𝒮, A) ≤ Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K)))) :
    ∃ P : Subgroup (MulAut (VM K)), P ≤ Y ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P ∧
      P ≤ Subgroup.normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut (VM K))) :
        Set (MulAut (VM K))) := by
  classical
  haveI : Finite (MulAut (VM K)) := inferInstance
  set R : Subgroup (MulAut (VM K)) := (rho (K := K)).range with hR
  set Z : Subgroup (MulAut (VM K)) := s16c11C5Scal K with hZ
  set N1 : Subgroup (MulAut (VM K)) :=
    Subgroup.normalizer (R : Set (MulAut (VM K))) ⊓
      Subgroup.centralizer (Z : Set (MulAut (VM K))) with hN1
  set W0 : Subgroup (MulAut (VM K)) := ⨆ A ∈ 𝒮, A with hW0
  have hW0Y : W0 ≤ Y := by
    rw [hW0]
    refine iSup_le fun A => iSup_le fun hAin => ?_
    rcases h𝒮 A hAin with hb | hA
    · rw [hb]; exact bot_le
    · exact hA.1
  have hW0N1 : W0 ≤ N1 := by
    rw [hN1]
    exact le_inf (hW0Y.trans hYN) hc
  have hW0sub2 : IsPGroup 2 ↥(W0.subgroupOf N1) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hW0N1).symm
  obtain ⟨Q, hW0Q⟩ := IsPGroup.exists_le_sylow (p := 2) hW0sub2
  set S : Subgroup (MulAut (VM K)) := (Q : Subgroup (↥N1)).map N1.subtype with hS
  have hSN1 : S ≤ N1 := by
    rw [hS]
    exact Subgroup.map_subtype_le (Q : Subgroup (↥N1))
  have hS2 : IsPGroup 2 ↥S := by
    rw [hS]
    exact Q.isPGroup'.map N1.subtype
  have hSsub : S.subgroupOf N1 = (Q : Subgroup (↥N1)) := by
    rw [hS]
    simpa only [Subgroup.comap_subtype] using
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N1)
        (Q : Subgroup (↥N1))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥N1 := inferInstance
  have hSodd : ¬ 2 ∣ S.relIndex N1 := by
    change ¬ 2 ∣ (S.subgroupOf N1).index
    rw [hSsub]
    exact Q.not_dvd_index
  have hW0S : W0 ≤ S := by
    rw [hS]
    have h := Subgroup.map_mono (f := N1.subtype) hW0Q
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW0N1] at h
  have hSN1' : S ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) ⊓
      Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))) := by
    rw [hN1, hR, hZ] at hSN1
    exact hSN1
  have hSodd' : ¬ 2 ∣ S.relIndex (Subgroup.normalizer ((rho (K := K)).range :
      Set (MulAut (VM K))) ⊓
      Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K)))) := by
    rw [hN1, hR, hZ] at hSodd
    exact hSodd
  obtain ⟨D, hDR₀, hDcard, hDinf, hDnorm⟩ := s16c11_case5_torus hK hSN1' hS2 hSodd'
  have hDR : D ≤ R := by rw [hR]; exact hDR₀
  have hDinfZ : Z ⊓ D = ⊥ := by rw [inf_comm]; exact hDinf
  have hDnormW0 : D ≤ Subgroup.normalizer (W0 : Set (MulAut (VM K))) := by
    have hle : D ≤ ⨅ A : 𝒮, Subgroup.normalizer ((A : Subgroup (MulAut (VM K))) :
        Set (MulAut (VM K))) := by
      rw [le_iInf_iff]
      intro A
      rcases h𝒮 A A.2 with hb | hA
      · rw [hb, Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
        exact le_top
      · have hAleW0 : (A : Subgroup (MulAut (VM K))) ≤ W0 := by
          rw [hW0]
          exact (le_iSup (fun _ : (A : Subgroup (MulAut (VM K))) ∈ 𝒮 =>
            (A : Subgroup (MulAut (VM K)))) A.2).trans
            (le_iSup (fun B => ⨆ (_ : B ∈ 𝒮), B) (A : Subgroup (MulAut (VM K))))
        have hAinS : (A : Subgroup (MulAut (VM K))) ∈ E3.aSet 2 S := by
          rw [E3.aSet] at hA ⊢
          exact ⟨hAleW0.trans hW0S, hA.2.1, hA.2.2.1, hA.2.2.2⟩
        exact hDnorm _ hAinS
    have hjoin : W0 = ⨆ A : 𝒮, (A : Subgroup (MulAut (VM K))) := by
      rw [hW0]
      exact (iSup_subtype'' 𝒮 (fun A : Subgroup (MulAut (VM K)) => A)).symm
    rw [hjoin]
    exact hle.trans (Subgroup.iInf_normalizer_le_normalizer_iSup
      (fun A : 𝒮 => (A : Subgroup (MulAut (VM K)))))
  have hZcR : Z ≤ Subgroup.centralizer (R : Set (MulAut (VM K))) := by
    rw [hZ, hR]
    exact s16c11_case5_scal_le_centralizer_rho K
  have hDcZ : D ≤ Subgroup.centralizer (Z : Set (MulAut (VM K))) :=
    hDR.trans (Subgroup.le_centralizer_iff.mp hZcR)
  have hZcD : Z ≤ Subgroup.centralizer (D : Set (MulAut (VM K))) :=
    Subgroup.le_centralizer_iff.mpr hDcZ
  have hcomm : ∀ x ∈ Z, ∀ y ∈ D, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hZcD hx) y hy).symm
  have hZcard : Nat.card ↥Z = 3 := by
    rw [hZ]; exact s16c11_case5_card_scal K hK
  have hPcard : Nat.card ↥(Z ⊔ D) = 9 := by
    have h := CFSG.card_sup_eq_mul_of_commute Z D hcomm hDinfZ
    rw [hZcard, hDcard] at h
    norm_num at h
    exact h
  have hexp : Monoid.exponent ↥(Z ⊔ D) ∣ 3 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    change (x : MulAut (VM K)) ^ 3 = 1
    have hx : (x : MulAut (VM K)) ∈ Z ⊔ D := x.2
    rw [CFSG.mem_sup_of_commute hcomm] at hx
    obtain ⟨z, hz, d, hd, hzd⟩ := hx
    have hz3 : z ^ 3 = 1 := by
      have h : orderOf (⟨z, hz⟩ : ↥Z) ∣ 3 := by
        rw [← hZcard]; exact orderOf_dvd_natCard _
      have h' := (orderOf_dvd_iff_pow_eq_one.mp h)
      simpa using h'
    have hd3 : d ^ 3 = 1 := by
      have h : orderOf (⟨d, hd⟩ : ↥D) ∣ 3 := by
        rw [← hDcard]; exact orderOf_dvd_natCard _
      have h' := (orderOf_dvd_iff_pow_eq_one.mp h)
      simpa using h'
    rw [show (x : MulAut (VM K)) = z * d from hzd.symm]
    rw [(hcomm z hz d hd).mul_pow 3, hz3, hd3, mul_one]
  have hP3 : IsPGroup 3 ↥(Z ⊔ D) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  have hPnotcyc : ¬ IsCyclic ↥(Z ⊔ D) := by
    intro hcyc
    have hcard_exp : Monoid.exponent ↥(Z ⊔ D) = 9 := by
      rw [IsCyclic.exponent_eq_card, hPcard]
    have hdvd : (9 : ℕ) ∣ 3 := by
      rw [← hcard_exp]; exact hexp
    exact absurd hdvd (by norm_num)
  have hZnormW0 : Z ≤ Subgroup.normalizer (W0 : Set (MulAut (VM K))) :=
    (Subgroup.le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨Z ⊔ D, sup_le hZY (hDR.trans hRY), hP3, hPnotcyc, sup_le hZnormW0 hDnormW0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
