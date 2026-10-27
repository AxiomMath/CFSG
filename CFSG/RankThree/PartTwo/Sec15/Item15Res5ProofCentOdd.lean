module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
public import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofHess
public import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofBlock
import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofL3Two
import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res5

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] {m : ℕ} {π : Bool}

open Sec11.KS11LieProof in
theorem not_two_dvd_card_of_model (hK : PiField π 2 m K) (hq : ModThree π (2 ^ m))
    (hq2 : 2 < 2 ^ m) (α : MulAut (projImage (slPi π 3 (2 ^ m) K))) (hα3 : α ^ 3 = 1)
    (R : Subgroup (projImage (slPi π 3 (2 ^ m) K))) (hRfix : ∀ r ∈ R, α r = r)
    (hRnorm : ∀ x, α x = x → ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hRsolv : Group.IsSolvable R)
    (hR3 : ¬ 3 ∣ Nat.card R) : ¬ 2 ∣ Nat.card R := by
  have := hK.finite
  have hm := hK.one_le
  have hπ : π = false → UnitaryFieldData 2 m K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (2 ^ m) := fun h => by subst h; exact hq
  have : Group.IsPerfect (projImage (slPi π 3 (2 ^ m) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hnorm : ∀ x : projImage (slPi π 3 (2 ^ m) K), α x = x →
      x ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (2 ^ m) K))) := fun x hx =>
    Subgroup.mem_normalizer_fintype (fun r hr => hRnorm x hx r hr)
  have hHess : ∀ h ∈ glPi π 3 (2 ^ m) K,
      (∀ x : projImage (slPi π 3 (2 ^ m) K),
        ((x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * diagTau hτ * h⁻¹) ∨
          (x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * cycThree * h⁻¹)) →
            α x = x) → ¬ 2 ∣ Nat.card R := by
    intro h hh hfix
    obtain ⟨a, b, hav, hbv, hE, hE9, hcent⟩ := hessian_pair hK hq hτ hτ1 hh
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
        α.toMonoidHom.eqLocus (MonoidHom.id (projImage (slPi π 3 (2 ^ m) K))) :=
      sup_le (Subgroup.zpowers_le.mpr (hfix a (Or.inl hav)))
        (Subgroup.zpowers_le.mpr (hfix b (Or.inr hbv)))
    exact not_two_dvd_card_of_hessian hE hE9 hcent (fun e he => hnorm e (hle he)) hR3
  rcases aut_pgl_or_field hK hq2 α hα3 with ⟨y₀, hy₀H, hy₀⟩ | ⟨f₀, hf, σ, hσ, g, hg, hα⟩
  · by_cases hy₀Z : y₀ ∈ zPi π 3 (2 ^ m) K
    ·
      have hy₀s : y₀ ∈ StatedScalars (Fin 3) K := by
        rw [zPi_eq hπ hq' hτ hτ1] at hy₀Z
        exact hy₀Z.2
      have hα1 : ∀ x : projImage (slPi π 3 (2 ^ m) K), α x = x := fun x => by
        apply Subtype.ext
        rw [hy₀, mk_eq_one_iff_mem_statedScalars.mpr hy₀s, one_mul, inv_one, mul_one]
      exact hHess 1 (one_mem _) (fun x _ => hα1 x)
    have hα3m : ∀ x : projImage (slPi π 3 (2 ^ m) K), α (α (α x)) = x := by
      intro x
      have h := congrArg (fun β : MulAut (projImage (slPi π 3 (2 ^ m) K)) => β x) hα3
      simpa [pow_succ, MulAut.mul_apply] using h
    have hy₀3s : y₀ ^ 3 ∈ StatedScalars (Fin 3) K := by
      refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
      rw [← mk_eq_one_iff_mem_statedScalars]
      have h1 := congrArg (fun x : projImage (slPi π 3 (2 ^ m) K) =>
        (x : ProjGenLinGroup (Fin 3) K)) (hα3m (projOf _ ⟨s, hs⟩))
      rw [hy₀, hy₀, hy₀, coe_projOf] at h1
      simp only [map_mul, map_inv, map_pow]
      have h2 : ProjGenLinGroup.mk y₀ ^ 3 * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk y₀ ^ 3)⁻¹ = ProjGenLinGroup.mk s := by
        calc ProjGenLinGroup.mk y₀ ^ 3 * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀ ^ 3)⁻¹ =
            ProjGenLinGroup.mk y₀ * (ProjGenLinGroup.mk y₀ * (ProjGenLinGroup.mk y₀ *
              ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀)⁻¹) * (ProjGenLinGroup.mk y₀)⁻¹) *
                (ProjGenLinGroup.mk y₀)⁻¹ := by rw [pow_three]; group
          _ = ProjGenLinGroup.mk s := h1
      rw [h2, mul_inv_cancel]
    have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (2 ^ m) K := by
      rw [zPi_eq hπ hq' hτ hτ1]
      exact ⟨pow_mem hy₀H 3, hy₀3s⟩
    obtain ⟨y, ⟨z, hz, rfl⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hy₀H hy₀Z hy₀3
    have hzs : z ∈ StatedScalars (Fin 3) K := by
      rw [zPi_eq hπ hq' hτ hτ1] at hz
      exact hz.2
    have hfix : ∀ x : projImage (slPi π 3 (2 ^ m) K), α x = x →
        ∃ s ∈ centMod (slPi π 3 (2 ^ m) K) (y₀ * z),
          (x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s := by
      intro x hx
      obtain ⟨⟨s, hs⟩, rfl⟩ := projOf_surjective _ x
      have h1 := congrArg (fun x : projImage (slPi π 3 (2 ^ m) K) =>
        (x : ProjGenLinGroup (Fin 3) K)) hx
      rw [hy₀, coe_projOf] at h1
      have h2 : y₀ * s * y₀⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
        rw [← mk_eq_one_iff_mem_statedScalars]
        simp only [map_mul, map_inv]
        rw [h1, mul_inv_cancel]
      refine ⟨s, mem_centMod_iff_scalar.mpr ⟨hs, (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹, inv_mem h2, ?_⟩,
        coe_projOf _ _⟩
      have hc1 := commute_of_mem_statedScalars hzs s⁻¹
      calc s * (y₀ * z) * s⁻¹ = s * y₀ * (z * s⁻¹) := by group
        _ = s * y₀ * (s⁻¹ * z) := by rw [hc1]
        _ = (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹ * (y₀ * z) := by group
    have hRle : R.map (projImage (slPi π 3 (2 ^ m) K)).subtype ≤
        (centMod (slPi π 3 (2 ^ m) K) (y₀ * z)).map ProjGenLinGroup.mk := by
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨s, hs, hrs⟩ := hfix r (hRfix r hr)
      exact ⟨s, hs, hrs.symm⟩
    have hodd : ¬ 2 ∣ Nat.card (centMod (slPi π 3 (2 ^ m) K) (y₀ * z)) →
        ¬ 2 ∣ Nat.card R := fun hc h2 => by
      apply hc
      have hcard : Nat.card (R.map (projImage (slPi π 3 (2 ^ m) K)).subtype) = Nat.card R :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [← hcard] at h2
      exact h2.trans ((Subgroup.card_dvd_of_le hRle).trans (Subgroup.card_map_dvd _ _))
    rcases hcases with ⟨-, ⟨eT⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, hcent⟩ | ⟨-, -, -, -, hcard, -⟩
    ·
      apply hodd
      apply not_two_dvd_card_centMod hK
      rw [Nat.card_congr eT.toEquiv, Nat.card_prod]
      have hc : Nat.card (Multiplicative (ZMod (qSubPi π (2 ^ m)))) = qSubPi π (2 ^ m) := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rw [hc]
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h' | h' <;>
        exact not_two_dvd_qSubPi hm h'
    ·
      have hy : y₀ * z = g * diagE e * g⁻¹ := eq_conj_of_inv_conj hD
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      have he1 : e ≠ 1 := by
        intro h1
        rw [h1, Units.val_one] at he
        rcases he with he | he
        · exact hτ1 he.symm
        · apply hτ1
          calc τ = τ ^ 3 / τ ^ 2 := by field_simp
            _ = 1 := by rw [hτ, ← he, div_one]
      refine not_two_dvd_card_of_block hK hq hq2 hg R ?_ ?_ hRsolv
      · intro r hr
        obtain ⟨s, hsC, hrs⟩ := hfix r (hRfix r hr)
        rw [hcent, hy, ← map_conj_centralizer hπ hg, centralizer_diagE_eq hK he1] at hsC
        obtain ⟨s', ⟨B, hB, rfl⟩, rfl⟩ := hsC
        exact ⟨B, hB, hrs⟩
      · intro B r hr
        refine hRnorm _ ?_ r hr
        apply Subtype.ext
        rw [hy₀, coe_blockProj]
        have hmk : ProjGenLinGroup.mk y₀ = ProjGenLinGroup.mk (g * diagE e * g⁻¹) := by
          rw [← hy, map_mul, mk_eq_one_iff_mem_statedScalars.mpr hzs, mul_one]
        rw [hmk, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        have hc := blockHom_commute e (B : GL (Fin 2) K)
        calc g * diagE e * g⁻¹ * (g * blockHom (B : GL (Fin 2) K) * g⁻¹) *
              (g * diagE e * g⁻¹)⁻¹ =
            g * (diagE e * blockHom (B : GL (Fin 2) K)) * (diagE e)⁻¹ * g⁻¹ := by group
          _ = g * (blockHom (B : GL (Fin 2) K) * diagE e) * (diagE e)⁻¹ * g⁻¹ := by rw [hc]
          _ = g * blockHom (B : GL (Fin 2) K) * g⁻¹ := by group
    ·
      apply hodd
      apply not_two_dvd_card_centMod hK
      rw [hcard]
      exact not_two_dvd_qSubPi_div hm
  ·
    obtain ⟨φ₀, hφ₀, hφ₀3⟩ := exists_frob hK hf
    have hψ : σ = φ₀ ∨ σ = φ₀ ^ 2 := eq_or_eq_sq_of_pow hφ₀ hσ
    have hΨ3 := frobGL_three' hφ₀3 hψ
    have hTmem : ∀ s ∈ slPi π 3 (2 ^ m) K, g * frobGL σ s * g⁻¹ ∈ slPi π 3 (2 ^ m) K :=
      fun s hs => conj_mem_slPi hπ hg (frobGL_mem_slPi hK σ hs)
    have hαs : ∀ s (hs : s ∈ slPi π 3 (2 ^ m) K),
        α (projOf _ ⟨s, hs⟩) = projOf _ ⟨g * frobGL σ s * g⁻¹, hTmem s hs⟩ :=
      fun s hs => Subtype.ext (by rw [hα, coe_projOf])
    set N := g * frobGL σ g * frobGL σ (frobGL σ g) with hN
    have hW : ∀ A, g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) * g⁻¹ =
        N * A * N⁻¹ := by
      intro A
      rw [hN]
      simp only [map_mul, map_inv, hΨ3]
      group
    have hmod : ∀ A ∈ slPi π 3 (2 ^ m) K, N * A * N⁻¹ * A⁻¹ ∈ StatedScalars (Fin 3) K := by
      intro A hA
      have h1 := congrArg (fun β : MulAut (projImage (slPi π 3 (2 ^ m) K)) =>
        ((β (projOf _ ⟨A, hA⟩) : projImage (slPi π 3 (2 ^ m) K)) :
        ProjGenLinGroup (Fin 3) K)) hα3
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1
      rw [hαs, hαs, hαs] at h1
      have h2 : ProjGenLinGroup.mk (g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) *
          g⁻¹) = ProjGenLinGroup.mk A := h1
      rw [hW] at h2
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h2, mul_inv_cancel]
    have hNc := commute_of_comm_mod_scalars hmod
    have hσ3' : ∀ A ∈ slPi π 3 (2 ^ m) K,
        g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
      intro A hA
      rw [hW, hNc A hA, mul_inv_cancel_right]
    obtain ⟨h, hh, hconj⟩ := exists_conj_frobGL hK hq hf hφ₀ hφ₀3 hψ hg hσ3'
    have hr : piCard π (2 ^ f₀) % 3 = 1 := piCard_mod_three (by rw [← hf]; exact hq)
    have hστ : σ τ = τ := by
      rcases hσ with h1 | h1
      · rw [h1]
        exact pow_eq_self_of_mod_three hτ hr
      · rw [h1]
        refine pow_eq_self_of_mod_three hτ ?_
        rw [Nat.pow_mod, hr]
    refine hHess h hh fun x hx => ?_
    have hfixA : ∀ M : GL (Fin 3) K, frobGL σ M = M →
        ∀ hM : h * M * h⁻¹ ∈ slPi π 3 (2 ^ m) K,
          (x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * M * h⁻¹) → α x = x := by
      intro M hMσ hM hxM
      have hxe : x = projOf _ ⟨_, hM⟩ := Subtype.ext (by rw [coe_projOf, hxM])
      rw [hxe]
      apply Subtype.ext
      rw [hα, hconj _ hM, coe_projOf]
      congr 1
      rw [show h⁻¹ * (h * M * h⁻¹) * h = M by group, hMσ]
    rcases hx with hx | hx
    · exact hfixA _ (Sec4.frobGL_diagTau hτ hστ)
        (conj_mem_slPi hπ hh (diagTau_mem_slPi hπ hq' hτ)) hx
    · exact hfixA _ (frobGL_cycThree σ) (conj_mem_slPi hπ hh (cycThree_mem_slPi hπ)) hx

theorem not_isPerfect_of_two_pow_eq_two {X : Type} [Group X] [Finite X] (hm : 1 ≤ m)
    (hiso : Sec4.IsoLThreePi X 2 m) (h2 : 2 ^ m = 2) : ¬ Group.IsPerfect X := by
  intro hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨hX72, hS9, -, hSn, -⟩ := Sec17.Proof17Res2.u32_structure hm hiso h2 S
  have hQ : Nat.card (X ⧸ (S : Subgroup X)) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S : Subgroup X)
    rw [hX72, hS9] at h
    omega
  have : Group.IsPerfect (X ⧸ (S : Subgroup X)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (S : Subgroup X))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2grp : IsPGroup 2 (X ⧸ (S : Subgroup X)) :=
    IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  have : Group.IsNilpotent (X ⧸ (S : Subgroup X)) := h2grp.isNilpotent
  have hsolv : Group.IsSolvable (X ⧸ (S : Subgroup X)) := inferInstance
  have : Nontrivial (X ⧸ (S : Subgroup X)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    norm_num
  exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hsolv

end Proof15Res5

open Proof15Res5
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks1513CentOdd : KS1513CentOdd := by
  intro X _ _ m hm hiso hperf σ hσ3 R hRfix hRnorm hRsolv hR3
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hm hiso
  have hq2 : 2 < 2 ^ m := by
    by_contra hle
    have h1 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact not_isPerfect_of_two_pow_eq_two hm hiso (by omega) hperf
  set α : MulAut (projImage (slPi π 3 (2 ^ m) K)) := MulAut.congr φ σ with hαdef
  have hαv : ∀ x, α x = φ (σ (φ.symm x)) := fun x => rfl
  have hα3 : α ^ 3 = 1 := by
    ext x : 1
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hαv,
      MulEquiv.symm_apply_apply, hσ3, MulEquiv.apply_symm_apply]
  set R' := R.map φ.toMonoidHom with hR'
  have hcard : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective φ.injective
  rw [← hcard]
  refine not_two_dvd_card_of_model hK hq hq2 α hα3 R' ?_ ?_ ?_ (by rwa [hcard])
  · rintro _ ⟨r, hr, rfl⟩
    rw [hαv]
    simp [hRfix r hr]
  · intro x hx r' hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : σ y = y := by
      apply φ.injective
      rw [← hx, hαv, MulEquiv.symm_apply_apply]
    refine ⟨y * r * y⁻¹, hRnorm y hy r hr, ?_⟩
    simp
  · have : Group.IsSolvable R := hRsolv
    exact Group.isSolvable_of_surjective (f := (φ.toMonoidHom.subgroupMap R))
      (MonoidHom.subgroupMap_surjective _ _)

theorem step1513EvenTrans_of_named
    (h142 : Sec14.Item142R)
    (hbot : Sec14.Item145BotS14) : Step1513EvenTrans :=
  step1513EvenTrans_of_kfact h142 hbot ks1513CentOdd

end CFSG.RankThree.PartTwo.Sec15
