module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGK1DBlocks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv)

theorem ggK1Dd_dvd_of_zpowers {L G : Type*} [Group L] [Finite L] [Group G] [Finite G]
    {ψ : L →* G} (hinj : Function.Injective ψ) {p : ℕ} {t : L}
    (ht : IsPGroup p (Subgroup.zpowers t))
    (hcore : ∀ A : Subgroup L, IsPGroup p A → ∃ (β : Type) (S : β → Subgroup L),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S ∧ ∀ c, p ∣ Nat.card (S c))
    {K : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K (ψ.range ⊓ Subgroup.centralizer ({ψ t} : Set G))) :
    p ∣ Nat.card K := by
  have hker : ψ.ker ≤ Subgroup.center L := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]; exact bot_le
  set A : Subgroup L := Subgroup.zpowers t with hA
  have hcentA : Subgroup.centralizer (A : Set L) = Subgroup.centralizer ({t} : Set L) := by
    rw [hA, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hH : ψ.range ⊓ Subgroup.centralizer ({ψ t} : Set G) =
      (Subgroup.centralizer (A : Set L)).map ψ := by
    apply le_antisymm
    · rintro _ ⟨⟨u, rfl⟩, hu⟩
      refine ⟨u, ?_, rfl⟩
      rw [hcentA]
      change u ∈ Subgroup.centralizer ({t} : Set L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ψ u ∈ Subgroup.centralizer ({ψ t} : Set G) at hu
      have hcomm : ψ u * ψ t = ψ t * ψ u :=
        Subgroup.mem_centralizer_singleton_iff.mp hu
      have h1 : ψ (u * t * u⁻¹) = ψ t := by
        rw [map_mul, map_mul, map_inv, hcomm]; group
      have h2 : u * t * u⁻¹ = t := hinj h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, ?_⟩
      change ψ u ∈ Subgroup.centralizer ({ψ t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_iff.mp hu t (by rw [hA]; exact Subgroup.mem_zpowers t)
      rw [← map_mul, ← map_mul, h]
  obtain ⟨β, S, hS, hdvd⟩ := hcore A ht
  rw [hH] at hK
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (Subgroup.commutator_le_self _) hS hK
  rw [Subgroup.card_map_of_injective hinj]
  exact hdvd c

theorem ggK1Dd_core_family {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card K ^ 2 - 1)
    {A : Subgroup (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ : Subgroup (V ≃ₗ[K] V))}
    (hAp : IsPGroup p A) :
    ∃ (β : Type) (S : β → Subgroup (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ : Subgroup (V ≃ₗ[K] V))),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set _)) S ∧
        ∀ c, p ∣ Nat.card (S c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup (V ≃ₗ[K] V) := TauCeti.QuadraticMap.orthogonalGroup Q
  let L : Subgroup (V ≃ₗ[K] V) := ⁅O, O⁆
  have hLO : L ≤ O := Subgroup.commutator_le_self O
  have hAO : A.map L.subtype ≤ O := by
    rintro _ ⟨a, ha, rfl⟩
    exact hLO a.2
  have hAp' : IsPGroup p (A.map L.subtype) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
    exact IsPGroup.iff_card.mpr ⟨k, by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hk]⟩
  obtain ⟨β, S, hS, hdvd⟩ := LayerPDiv.exists_subCoreFamily_orthCent_pDiv hQ hAO
    (LayerCores.odd_card_of_isPGroup hp hp2 hAp') hp hp2 hpF
  have hSinf := hS.inf_of_commutator_le (N := ⁅O, O⁆)
    (Subgroup.commutator_mono inf_le_right inf_le_right)
  have hle : (Subgroup.centralizer ((A.map L.subtype) : Set (V ≃ₗ[K] V)) ⊓ O) ⊓ ⁅O, O⁆ ≤
      L.subtype.range := by
    rw [Subgroup.range_subtype]; exact inf_le_right
  have hcent : ((Subgroup.centralizer ((A.map L.subtype) : Set (V ≃ₗ[K] V)) ⊓ O) ⊓ ⁅O, O⁆).comap
      L.subtype = Subgroup.centralizer (A : Set L) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨⟨hx, -⟩, -⟩ a ha
      exact Subgroup.subtype_injective L (by
        rw [map_mul, map_mul]
        exact hx (L.subtype a) ⟨a, ha, rfl⟩)
    · intro hx
      exact ⟨⟨fun y hy => by
        obtain ⟨a, ha, rfl⟩ := hy
        rw [← map_mul, ← map_mul]
        exact congrArg L.subtype (hx a ha), hLO x.2⟩, x.2⟩
  refine ⟨β, fun c => (S c).comap L.subtype, ?_, ?_⟩
  · rw [← hcent]
    exact hSinf.comap L.subtype L.subtype_injective hle
  · intro c
    rw [LayerPDiv.card_comap_of_le_range L.subtype_injective ((hSinf.1 c).trans hle)]
    exact hdvd c

theorem ggK1D_core_dvd_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1) :
    GGK1Dvd p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  classical
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hpF : p ∣ Nat.card K ^ 2 - 1 := LayerPDiv.dvd_sq_sub_one (by rw [hK]; exact hdvd)
  let Qf : QuadraticForm K (Fin r ⊕ Fin r → K) := TableBOrth.qPlusForm K r
  let O : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
    TauCeti.QuadraticMap.orthogonalGroup Qf
  let L : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) := ⁅O, O⁆
  have hscal : (LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K r)) = ⊥ := by
    by_cases hr : 1 ≤ r
    · exact TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) hr
    · have hr0 : r = 0 := by omega
      subst hr0
      exact Subsingleton.elim _ _
  have hcomap : LargeEvenOmega (LargeEvenQPlus K r) =
      Subgroup.comap (toLinEquiv (Fin r ⊕ Fin r) K).toMonoidHom L :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := Qf) (Q₀ := LargeEvenQPlus K r) (by rw [TableBOrth.coe_qPlusForm])
  have hmap : (LargeEvenOmega (LargeEvenQPlus K r)).map
      (toLinEquiv (Fin r ⊕ Fin r) K).toMonoidHom = L := by
    rw [hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective L
  let e : LargeEvenOmega (LargeEvenQPlus K r) ≃* L :=
    (MulEquiv.subgroupMap (toLinEquiv (Fin r ⊕ Fin r) K)
      (LargeEvenOmega (LargeEvenQPlus K r))).trans (MulEquiv.subgroupCongr hmap)
  let Ψ : L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)) :=
    e.symm.trans (TableBOrth.projMkEquiv hscal)
  have hΨt : Ψ.toMonoidHom (e x) =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x := by
    change Ψ (e x) = _
    change TableBOrth.projMkEquiv hscal (e.symm (e x)) = _
    rw [MulEquiv.symm_apply_apply]
    exact TableBOrth.projMkEquiv_apply hscal x
  have ht : IsPGroup p (Subgroup.zpowers (e x)) :=
    ggIsPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  intro J hJ
  have hfix : ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) =
      Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x} :
        Set (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))) := by
    ext g
    rw [mem_ggFixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  refine ggK1Dd_dvd_of_zpowers (ψ := Ψ.toMonoidHom) Ψ.injective ht (fun A hA => ?_) ?_
  · exact ggK1Dd_core_family (Q := Qf) (TableBOrth.nondegenerate_qPlusForm (K := K) r)
      hp hp2 hpF hA
  · have hrange : Ψ.toMonoidHom.range = ⊤ := MulEquiv.range_eq_top Ψ
    rw [hrange, top_inf_eq, hΨt, ← hfix]
    exact hJ

theorem ggK1D_core_dvd_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1) :
    GGK1Dvd p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  classical
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hpF : p ∣ Nat.card K ^ 2 - 1 := LayerPDiv.dvd_sq_sub_one (by rw [hK]; exact hdvd)
  let Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K) :=
    TableBOrth.qMinusForm K (r - 1) b c
  let O : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (r - 1) → K)) := TauCeti.QuadraticMap.orthogonalGroup Qf
  let L : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (r - 1) → K)) := ⁅O, O⁆
  have hscal : (LargeEvenScalars (LargeEvenMinusIdx (r - 1)) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := r - 1) b c
  have hcomap : LargeEvenOmega (LargeEvenQMinus (r - 1) b c) =
      Subgroup.comap (toLinEquiv (LargeEvenMinusIdx (r - 1)) K).toMonoidHom L :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := Qf) (Q₀ := LargeEvenQMinus (r - 1) b c) (by rw [TableBOrth.coe_qMinusForm])
  have hmap : (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)).map
      (toLinEquiv (LargeEvenMinusIdx (r - 1)) K).toMonoidHom = L := by
    rw [hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective L
  let e : LargeEvenOmega (LargeEvenQMinus (r - 1) b c) ≃* L :=
    (MulEquiv.subgroupMap (toLinEquiv (LargeEvenMinusIdx (r - 1)) K)
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))).trans (MulEquiv.subgroupCongr hmap)
  let Ψ : L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) :=
    e.symm.trans (TableBOrth.projMkEquiv hscal)
  have hΨt : Ψ.toMonoidHom (e x) =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x := by
    change Ψ (e x) = _
    change TableBOrth.projMkEquiv hscal (e.symm (e x)) = _
    rw [MulEquiv.symm_apply_apply]
    exact TableBOrth.projMkEquiv_apply hscal x
  have ht : IsPGroup p (Subgroup.zpowers (e x)) :=
    ggIsPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  intro J hJ
  have hfix : ggFixSub (MulAut.conj
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) =
      Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x} :
          Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
    ext g
    rw [mem_ggFixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  refine ggK1Dd_dvd_of_zpowers (ψ := Ψ.toMonoidHom) Ψ.injective ht (fun A hA => ?_) ?_
  · exact ggK1Dd_core_family (Q := Qf) (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr)
      hp hp2 hpF hA
  · have hrange : Ψ.toMonoidHom.range = ⊤ := MulEquiv.range_eq_top Ψ
    rw [hrange, top_inf_eq, hΨt, ← hfix]
    exact hJ

end CFSG.StandardType

end
