module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailDFour
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentre

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionPSLComp

private theorem tp_ker_proj_slEquiv {m : ℕ} {F : Type} [Field F] :
    ((LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) F)).comp
      (InnerDiagA.slEquiv m F).toMonoidHom).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  ext u
  rw [MonoidHom.mem_ker]
  show (QuotientGroup.mk (InnerDiagA.slEquiv m F u) :
      LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) F)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, largeEvenScalars_def,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hmat : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        Matrix.scalar (Fin (m + 1)) (c : F) := by
      rw [← InnerDiagA.coe_slEquiv, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmat]
    exact (Matrix.scalar_commute (c : F) (fun r => Commute.all _ r) _).eq.symm
  · intro hu
    obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by simp)] at hr
      exact zero_ne_one hr
    exact ⟨Units.mk0 r hr0, Units.ext (by
      rw [Matrix.GeneralLinearGroup.coe_scalar, InnerDiagA.coe_slEquiv]
      exact hru)⟩

private theorem tp_mulAut_conj_shift {R : Type} [Group R] (δ : MulAut R) (x : R) :
    δ * MulAut.conj x * δ⁻¹ = MulAut.conj (δ x) := by
  ext r
  simp [MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv]

private theorem tp_ker_mulAut_conj {R : Type} [Group R] :
    (MulAut.conj : R →* MulAut R).ker = Subgroup.center R := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 := DFunLike.congr_fun h g
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * x = (x * g * x⁻¹) * x := by rw [h1]
      _ = x * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply]
    calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [h g]
      _ = g := by group

private theorem tp_map_fixed_eq {R : Type} [Group R] (δ : MulAut R)
    (hZ : Subgroup.center R = ⊥) :
    (ggAutFixedSubgroup δ).map (MulAut.conj : R →* MulAut R) =
      (MulAut.conj : R →* MulAut R).range ⊓
        Subgroup.centralizer (Subgroup.zpowers δ : Set (MulAut R)) := by
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [tp_ker_mulAut_conj, hZ])
  ext k
  constructor
  · intro hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [ggCentralizer_zpowers_eq δ]
    change MulAut.conj x ∈ Subgroup.centralizer ({δ} : Set (MulAut R))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hx' : δ x = x := hx
    calc δ * MulAut.conj x = MulAut.conj (δ x) * δ := by
          rw [← tp_mulAut_conj_shift δ x]; group
      _ = MulAut.conj x * δ := by rw [hx']
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [ggCentralizer_zpowers_eq δ] at hx
    change MulAut.conj x ∈ Subgroup.centralizer ({δ} : Set (MulAut R)) at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hcomm : δ * MulAut.conj x = MulAut.conj x * δ := hx δ (Set.mem_singleton δ)
    have h2 : MulAut.conj (δ x) = MulAut.conj x := by
      rw [← tp_mulAut_conj_shift δ x, hcomm]
      group
    exact hinj h2

theorem ggTorsion_psl_components {m n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) F)) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {δ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) F))} (hδp : δ ^ p = 1)
    (hδ : δ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) F)) Set.univ)
    {J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) F))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    ∃ (d : ℕ) (D : Type) (_ : Field D) (_ : Finite D), 2 ≤ d ∧ CharP D 2 ∧
      Nat.card F ≤ Nat.card D ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
        Matrix.SpecialLinearGroup (Fin d) D ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rwa [← Nat.card_eq_fintype_card]
  let H := LargeEvenSLGroup (Fin (m + 1)) F
  let R := LargeEvenProj H
  let e : Matrix.SpecialLinearGroup (Fin (m + 1)) F ≃* ↥H := InnerDiagA.slEquiv m F
  let π : ↥H →* R := LargeEvenProjMk H
  let q : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* R := π.comp e.toMonoidHom
  let ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp q
  haveI : Finite R := inferInstance
  haveI : Finite (MulAut R) := inferInstance
  have hq_surj : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  have hψrange : ψ.range = (MulAut.conj : R →* MulAut R).range := by
    rw [show ψ = (MulAut.conj : R →* MulAut R).comp q from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hq_surj, Subgroup.map_top]
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    intro u hu
    have hu1 : ψ u = 1 := MonoidHom.mem_ker.mp hu
    have hqcenter : q u ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun hu1 g
      rw [show ψ u = MulAut.conj (q u) from rfl, MulAut.conj_apply, MulAut.one_apply] at h
      calc g * q u = (q u * g * (q u)⁻¹) * q u := by rw [h]
        _ = q u * g := by group
    have hq1 : q u = 1 := by
      have hmem : q u ∈ (⊥ : Subgroup R) := by rwa [← hZ]
      simpa using hmem
    have hkerq : q.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
      tp_ker_proj_slEquiv
    have hmem : u ∈ q.ker := MonoidHom.mem_ker.mpr hq1
    rw [hkerq] at hmem
    exact hmem
  obtain ⟨A, -, hA⟩ := hδ
  have hstar : ∀ u, δ (q u) = q (InnerDiagA.conjSL A u) := by
    intro u
    have hrel : ((e (InnerDiagA.conjSL A u) : ↥H) : GL (Fin (m + 1)) F) =
        A * (e u) * A⁻¹ := by
      rw [show e (InnerDiagA.conjSL A u) = MulAut.conjNormal A (e u) from
        InnerDiagA.slEquiv_conjSL A u, MulAut.conjNormal_apply]
    exact hA (e u) (e (InnerDiagA.conjSL A u)) hrel
  have hδA : (δ, A) ∈ LinFusion.ggInducedPairs ψ := by
    rw [LinFusion.mem_ggInducedPairs]
    intro u
    rw [show ψ u = MulAut.conj (q u) from rfl,
      show ψ (InnerDiagA.conjSL A u) = MulAut.conj (q (InnerDiagA.conjSL A u)) from rfl,
      tp_mulAut_conj_shift δ (q u), hstar u]
  have hE : IsPGroup p (Subgroup.zpowers δ) := ggIsPGroup_zpowers_of_pow_eq_one hδp
  have hEA : ∀ x ∈ Subgroup.zpowers δ, ∃ B, (x, B) ∈ LinFusion.ggInducedPairs ψ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h := (LinFusion.ggInducedPairs ψ).zpow_mem hδA k
    have hpow : ((δ, A) : MulAut R × GL (Fin (m + 1)) F) ^ k = (δ ^ k, A ^ k) := rfl
    exact ⟨A ^ k, hpow ▸ h⟩
  let K : Subgroup (MulAut R) := J.map (MulAut.conj : R →* MulAut R)
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [tp_ker_mulAut_conj, hZ])
  let eJK : ↥J ≃* ↥K := Subgroup.equivMapOfInjective J (MulAut.conj : R →* MulAut R) hinj
  have hK : IsComponentOf K (ψ.range ⊓
      Subgroup.centralizer (Subgroup.zpowers δ : Set (MulAut R))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [Subgroup.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [hψrange]
        exact ⟨j, rfl⟩
      · rw [ggCentralizer_zpowers_eq δ]
        change MulAut.conj j ∈ Subgroup.centralizer ({δ} : Set (MulAut R))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfix : δ j = j := hJ.1 hj
        have hcomm : δ * MulAut.conj j = MulAut.conj j * δ := by
          calc δ * MulAut.conj j = MulAut.conj (δ j) * δ := by
                rw [← tp_mulAut_conj_shift δ j]; group
            _ = MulAut.conj j * δ := by rw [hfix]
        exact hcomm.symm
    · have hm := hJ.2.1.map (MulAut.conj : R →* MulAut R)
      rw [tp_map_fixed_eq δ hZ, ← hψrange] at hm
      exact hm
    · exact (CFSG.Assembly.IsQuasisimple.congr eJK).mp hJ.2.2
  obtain ⟨d, D, hDfield, hDfin, hd, hD2, hFD, ⟨eKD⟩⟩ :=
    ggAKFT_exists_psl_of_isComponentOf_sl (F := F) hker hp hp2 hE hEA hK
  have hkerJK : eJK.toMonoidHom.ker ≤ Subgroup.center ↥J := by
    rw [MonoidHom.ker_eq_bot eJK.toMonoidHom eJK.injective]
    exact bot_le
  obtain ⟨eJKq⟩ := ggCenterQuotEquiv_of_surjective (P := ↥J) (Q := ↥K)
    ⟨hJ.2.2.1⟩ eJK.toMonoidHom eJK.surjective hkerJK
  exact ⟨d, D, hDfield, hDfin, hd, hD2, hFD, ⟨eJKq.trans eKD⟩⟩

end TorsionPSLComp

end CFSG.StandardType
