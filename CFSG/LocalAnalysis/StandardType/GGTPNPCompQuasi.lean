module

public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.ComponentClassification.CatalogueBCentralQuotient
open CFSG.ComponentClassification.CatalogueBAlternating

private theorem tpq_quasisimple_of_assembly {G : Type*} [Group G]
    (h : CFSG.Assembly.IsQuasisimple G) : CFSG.IsQuasisimple G :=
  ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr h

private theorem tpq_center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hH, Subgroup.mem_bot] at hzH
  exact e.injective (by rw [hzH, map_one])

private theorem tpq_conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut G => f y) hx
    rw [MulAut.one_apply, MulAut.conj_apply] at h
    have h' : x * y = y * x := by
      have := congrArg (fun t => t * x) h
      simpa [mul_assoc] using this
    exact h'.symm
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hxc

private theorem tpq_centerQuotAut_conj {X : Type*} [Group X] (g : X) :
    centerQuotAut X (MulAut.conj g) =
      MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X) := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [centerQuotAut_mk, MulAut.conj_apply]

theorem tpq_ggInducedAut_conj {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (g : X) :
    ggInducedAut θ (MulAut.conj g) =
      MulAut.conj (θ (QuotientGroup.mk g : X ⧸ Subgroup.center X)) := by
  change MulAut.congr θ (centerQuotAut X (MulAut.conj g)) = _
  rw [tpq_centerQuotAut_conj, CFSG.mulAut_congr_conj]

private theorem tpq_mulAut_congr_apply_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (f : MulAut A) (a : A) : (MulAut.congr e f) (e a) = e (f a) := by
  simp [MulAut.congr_apply]

private theorem tpq_conjAut_mul {G : Type*} [Group G] (c : MulAut G) (g : G) :
    c⁻¹ * MulAut.conj g * c = MulAut.conj (c⁻¹ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hcx : c⁻¹ (c x) = x := by simp
  rw [hcx]

private noncomputable def tpq_innQuotEquiv {X : Type*} [Group X]
    (hZ : Subgroup.center X = ⊥) :
    (MulAut.conj : X →* MulAut X).range ⧸
        Subgroup.center ((MulAut.conj : X →* MulAut X).range) ≃* X :=
  let ρ : X ≃* ↥(MulAut.conj : X →* MulAut X).range :=
    MonoidHom.ofInjective (tpq_conj_injective hZ)
  let hZG : Subgroup.center ↥(MulAut.conj : X →* MulAut X).range = ⊥ :=
    tpq_center_eq_bot_of_mulEquiv ρ.symm hZ
  (QuotientGroup.quotientMulEquivOfEq hZG).trans (QuotientGroup.quotientBot.trans ρ.symm)

private noncomputable def tpq_innIso {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {R : Type} [Group R] (θ : X ≃* R) :
    (MulAut.conj : X →* MulAut X).range ⧸
        Subgroup.center ((MulAut.conj : X →* MulAut X).range) ≃* R :=
  (tpq_innQuotEquiv hZ).trans θ

private theorem tpq_marking_transport_aux {L : Type*} [Group L] {R : Type} [Group R]
    (hZLb : Subgroup.center (L ⧸ Subgroup.center L) = ⊥)
    (θ : L ⧸ Subgroup.center L ≃* R) (E : Subgroup (MulAut L)) (y : MulAut L)
    {I : Set (MulAut R)} (hind : GGInducedInn E θ I) (hyE : y ∈ E) :
    ∀ a ∈ Subgroup.zpowers (centerQuotAut L y), ∃ φ ∈ I,
      LargeEvenInduces (tpq_innIso hZLb θ)
        (fun l l' : (MulAut.conj : L ⧸ Subgroup.center L →* MulAut (L ⧸ Subgroup.center L)).range =>
          (l' : MulAut (L ⧸ Subgroup.center L)) = a⁻¹ * l * a) φ := by
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨ggInducedAut θ ((y ^ k)⁻¹), hind ((y ^ k)⁻¹) (E.inv_mem (E.zpow_mem hyE k)), ?_⟩
  rintro l l' hrel
  let ρ : (L ⧸ Subgroup.center L) ≃*
      ↥(MulAut.conj : L ⧸ Subgroup.center L →* MulAut (L ⧸ Subgroup.center L)).range :=
    MonoidHom.ofInjective (tpq_conj_injective hZLb)
  have hρ : ∀ g : L ⧸ Subgroup.center L, (ρ g : MulAut (L ⧸ Subgroup.center L)) =
      MulAut.conj g := fun g => MonoidHom.ofInjective_apply _
  have hθl : tpq_innIso hZLb θ (QuotientGroup.mk l) = θ (ρ.symm l) := rfl
  have hθl' : tpq_innIso hZLb θ (QuotientGroup.mk l') = θ (ρ.symm l') := rfl
  have hg : (l : MulAut (L ⧸ Subgroup.center L)) = MulAut.conj (ρ.symm l) := by
    rw [← hρ (ρ.symm l), MulEquiv.apply_symm_apply]
  have hg' : (l' : MulAut (L ⧸ Subgroup.center L)) = MulAut.conj (ρ.symm l') := by
    rw [← hρ (ρ.symm l'), MulEquiv.apply_symm_apply]
  let c : MulAut (L ⧸ Subgroup.center L) := (centerQuotAut L y) ^ k
  have hrel' : MulAut.conj (ρ.symm l') = MulAut.conj (c⁻¹ (ρ.symm l)) := by
    have h1 : MulAut.conj (ρ.symm l') = c⁻¹ * l * c := by
      rw [← hg', hrel]
    have h2 : c⁻¹ * l * c = MulAut.conj (c⁻¹ (ρ.symm l)) := by
      rw [hg]
      exact tpq_conjAut_mul c (ρ.symm l)
    rw [h1, h2]
  have hg'' : ρ.symm l' = c⁻¹ (ρ.symm l) :=
    tpq_conj_injective hZLb hrel'
  have hφ : ggInducedAut θ ((y ^ k)⁻¹) = MulAut.congr θ c⁻¹ := by
    change MulAut.congr θ (centerQuotAut L ((y ^ k)⁻¹)) = _
    rw [map_inv, map_zpow]
  rw [hθl, hθl', hφ, tpq_mulAut_congr_apply_apply, hg'']

private theorem tpq_conj_commute_iff {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥)
    (a : MulAut G) (d : G) : a * MulAut.conj d = MulAut.conj d * a ↔ a d = d := by
  have hconj : a * MulAut.conj d * a⁻¹ = MulAut.conj (a d) := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have hax : a (a⁻¹ x) = x := by simp
    rw [hax]
  constructor
  · intro h
    have h2 : MulAut.conj (a d) = MulAut.conj d := by rw [← hconj, h]; group
    exact tpq_conj_injective hZ h2
  · intro h
    have h2 : MulAut.conj (a d) = MulAut.conj d := by rw [h]
    have h3 : a * MulAut.conj d * a⁻¹ = MulAut.conj d := by rw [hconj, h2]
    calc a * MulAut.conj d = a * MulAut.conj d * a⁻¹ * a := by group
      _ = MulAut.conj d * a := by rw [h3]

private theorem tpq_fixed_map {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (y : MulAut X) :
    (fixedSubgroup y).map
        (MonoidHom.ofInjective (tpq_conj_injective hZ)).toMonoidHom =
      (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup (MulAut X)) : Set (MulAut X)) ⊓
        (MulAut.conj : X →* MulAut X).range).subgroupOf
        (MulAut.conj : X →* MulAut X).range := by
  let ρ := MonoidHom.ofInjective (tpq_conj_injective hZ)
  have hρ : ∀ g : X, (ρ g : MulAut X) = MulAut.conj g := fun g => MonoidHom.ofInjective_apply _
  have hcent : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup (MulAut X)) : Set (MulAut X)) =
      Subgroup.centralizer ({y} : Set (MulAut X)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hfix : y (d : X) = (d : X) := hd
    refine ⟨?_, (ρ d).2⟩
    rw [hcent]
    change (ρ d : MulAut X) ∈ Subgroup.centralizer ({y} : Set (MulAut X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (ρ d : MulAut X) * y = y * (ρ d : MulAut X)
    rw [hρ d]
    exact ((tpq_conj_commute_iff hZ y (d : X)).mpr hfix).symm
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨hc, hg⟩ := hx
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hg
    refine ⟨d, ?_, ?_⟩
    · show y d = d
      rw [hcent] at hc
      change (x : MulAut X) ∈ Subgroup.centralizer ({y} : Set (MulAut X)) at hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [← hd] at hc
      exact (tpq_conj_commute_iff hZ y d).mp hc.symm
    · apply Subtype.ext
      change (ρ d : MulAut X) = (x : MulAut X)
      rw [hρ d]
      exact hd

private noncomputable def tpq_fixedIso {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (y : MulAut X) :
    ↥(fixedSubgroup y) ≃*
      ↥(Subgroup.centralizer ((Subgroup.zpowers y : Subgroup (MulAut X)) : Set (MulAut X)) ⊓
        (MulAut.conj : X →* MulAut X).range) :=
  (Subgroup.equivMapOfInjective (fixedSubgroup y)
      (MonoidHom.ofInjective (tpq_conj_injective hZ)).toMonoidHom
      (MonoidHom.ofInjective (tpq_conj_injective hZ)).injective).trans
    ((MulEquiv.subgroupCongr (tpq_fixed_map hZ y)).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right))

private theorem tpq_quotient_pcomp_quasisimple {L : Type} [Group L] [Finite L] {p : ℕ}
    (hS1 : GGStructSOne) (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut L)) (y : MulAut L) (hyE : y ∈ E) (hord : orderOf y = p)
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I))
    (C : Subgroup (fixedSubgroup (centerQuotAut L y)))
    (hC : CFSG.IsPComponent p C) : CFSG.IsQuasisimple ↥C := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmarkKeep : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I) := hmark
  obtain ⟨hperfL, lab0, hΛ0, hraw⟩ := hmark
  obtain ⟨R, hRgrp, I, F, hsimp, hna, θ, hind⟩ := largeEvenRawDatum_exists hraw
  haveI : Group.IsPerfect L := ⟨hperfL⟩
  have hZLb : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot L
  haveI : Group.IsPerfect (L ⧸ Subgroup.center L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  let G₀ : Subgroup (MulAut (L ⧸ Subgroup.center L)) := (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
  let ρ : (L ⧸ Subgroup.center L) ≃* ↥G₀ := MonoidHom.ofInjective (tpq_conj_injective hZLb)
  haveI : IsSimpleGroup R := hsimp
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := θ.isSimpleGroup
  have hG0simple : IsSimpleGroup ↥G₀ := ρ.symm.isSimpleGroup
  let ψ : MulAut (L ⧸ Subgroup.center L) := centerQuotAut L y
  let A : Subgroup (MulAut (L ⧸ Subgroup.center L)) := Subgroup.zpowers ψ
  have hyp : y ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one y
  have hψpow : ψ ^ p = 1 := by
    change (centerQuotAut L y) ^ p = 1
    rw [← map_pow, hyp, map_one]
  have hAel : IsElemAbelian p A := CFSG.Open.isElemAbelian_zpowers hψpow
  have hAN : A ≤ Subgroup.normalizer (G₀ : Set (MulAut (L ⧸ Subgroup.center L))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hg
      exact MonoidHom.mem_range.mpr ⟨a d, by
        have := tpq_conjAut_mul a⁻¹ d
        exact this.symm⟩
    · intro hg
      obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hg
      refine MonoidHom.mem_range.mpr ⟨a⁻¹ d, ?_⟩
      calc MulAut.conj (a⁻¹ d) = a⁻¹ * MulAut.conj d * a := (tpq_conjAut_mul a d).symm
        _ = a⁻¹ * (a * g * a⁻¹) * a := by rw [hd]
        _ = g := by group
  have hperfG0 : commutator ↥G₀ = ⊤ := by
    haveI : Group.IsPerfect ↥G₀ :=
      Group.IsPerfect.ofSurjective (f := ρ.toMonoidHom) (fun x => ρ.surjective x)
    exact Group.IsPerfect.commutator_eq_top
  have hmarkG0 : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ'' => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ'' (fun l l' : ↥G₀ => (l' : MulAut (L ⧸ Subgroup.center L)) = a⁻¹ * l * a) φ) :=
    ggLargeEvenMarking_of_centerQuot_equiv' hperfG0 (tpq_innQuotEquiv hZLb).symm
      (fun lab R' _ I' F' θ' hθ' => tpq_marking_transport_aux hZLb θ' E y hθ' hyE) hmarkKeep
  let Φ : ↥(fixedSubgroup ψ) ≃*
      ↥(Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓
        G₀) := tpq_fixedIso hZLb ψ
  have hmap := (ComponentClassification.CatalogueBAlternating.pComponent_equiv_iff p Φ C).mpr hC
  let C' : Subgroup (MulAut (L ⧸ Subgroup.center L)) :=
    (C.map Φ.toMonoidHom).map
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓
        G₀).subtype
  have hC'sub : C'.subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓ G₀) =
      C.map Φ.toMonoidHom := by
    change (((C.map Φ.toMonoidHom).map
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓ G₀).subtype).comap
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓ G₀).subtype) = C.map Φ.toMonoidHom
    exact Subgroup.comap_map_eq_self_of_injective
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓ G₀).subtype_injective
      (C.map Φ.toMonoidHom)
  have hC' : LargeEvenPComponent p
      (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓ G₀)
      C' := by
    rw [ggLargeEvenPComponent_iff]
    exact ⟨Subgroup.map_subtype_le _, by rw [hC'sub]; exact hmap⟩
  have hC'q : CFSG.IsQuasisimple ↥C' :=
    tpq_quasisimple_of_assembly (hS1 (MulAut (L ⧸ Subgroup.center L)) p G₀ A hp hp2 hG0simple hAel hAN hmarkG0 C' hC').1
  have hmapq : CFSG.IsQuasisimple ↥(C.map Φ.toMonoidHom) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (C.map Φ.toMonoidHom)
        (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓
          G₀).subtype
        (Subgroup.centralizer ((Subgroup.zpowers ψ : Subgroup (MulAut (L ⧸ Subgroup.center L))) : Set (MulAut (L ⧸ Subgroup.center L))) ⊓
          G₀).subtype_injective) hC'q
  have hker : Φ.toMonoidHom.ker ≤ Subgroup.center ↥(fixedSubgroup ψ) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ.toMonoidHom).mpr Φ.injective]
    exact bot_le
  exact (ComponentClassification.CatalogueBCentralQuotient.pComponent_quasisimple_iff Φ.toMonoidHom hker p C hC).mpr hmapq

private theorem tpq_quotient_pcomp_quasisimple_all {L : Type} [Group L] [Finite L] {p : ℕ}
    (hS1 : GGStructSOne) (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut L)) (y : MulAut L) (hyE : y ∈ E) (hord : orderOf y = p)
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I))
    (ψ : MulAut (L ⧸ Subgroup.center L)) (hψ : ψ = centerQuotAut L y) :
    ∀ C : Subgroup (fixedSubgroup ψ), CFSG.IsPComponent p C → CFSG.IsQuasisimple ↥C := by
  subst hψ
  exact fun C hC => tpq_quotient_pcomp_quasisimple hS1 hp hp2 E y hyE hord hmark C hC

theorem ggPCompCentQuasisimple_holds :
    GGPCompCentQuasisimple fun _ => True := by
  intro p hp hp2 L _ _ E y lab hΛ hP hlab hy hord hmark S hS
  haveI : Fact p.Prime := ⟨hp⟩
  let Z : Subgroup L := Subgroup.center L
  have hcentral : Z ≤ Subgroup.center L := le_rfl
  have hinv : Z.map y.toMonoidHom = Z := by
    change (Subgroup.center L).map (MulEquiv.toMonoidHom y) = Subgroup.center L
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance y
  let ψ : MulAut (L ⧸ Z) := onQuotient Z y hinv
  have hψ : ψ = centerQuotAut L y := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change (onQuotient Z y hinv) (QuotientGroup.mk' Z x) =
      (centerQuotAut L y) (QuotientGroup.mk' Z x)
    rw [onQuotient_mk]
    exact (centerQuotAut_mk y x).symm
  have hSle : S ≤ fixedSubgroup y := hS.1
  have hSpc : CFSG.IsPComponent p (S.subgroupOf (fixedSubgroup y)) :=
    ((ggLargeEvenPComponent_iff p (ggAutFixedSubgroup y) S).1 hS).2
  let f := fixedImageProjection Z y hinv
  have hf_surj : Function.Surjective f := fixedImageProjection_surjective Z y hinv
  have hf_central : f.ker ≤ Subgroup.center ↥(fixedSubgroup y) :=
    fixedImageProjection_kernel_central Z y hinv hcentral
  let N : Subgroup ↥(fixedSubgroup ψ) := fixedImage Z y hinv
  have hNnorm : N.Normal := fixedImage_normal Z y hinv hcentral
  let M : Subgroup ↥N := (S.subgroupOf (fixedSubgroup y)).map f
  have hM : CFSG.IsPComponent p M :=
    ComponentClassification.CatalogueBCentralQuotient.pComponent_map p f hf_surj hf_central
      (S.subgroupOf (fixedSubgroup y)) hSpc
  haveI : N.Normal := hNnorm
  have hMpcN : CFSG.IsPComponent p M := hM
  have hMpcD : CFSG.IsPComponent p (M.map N.subtype) :=
    ComponentClassification.CatalogueBAlternating.pComponent_of_normal_subgroup p N M hM
  have hMqD : CFSG.IsQuasisimple ↥(M.map N.subtype) :=
    tpq_quotient_pcomp_quasisimple_all ggStructSOne_holds hp hp2 E y hy hord hmark ψ hψ
      (M.map N.subtype) hMpcD
  have hMq : CFSG.IsQuasisimple ↥M := by
    haveI : N.Normal := hNnorm
    exact CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective M N.subtype N.subtype_injective) hMqD
  have hSsub_q : CFSG.IsQuasisimple ↥(S.subgroupOf (fixedSubgroup y)) :=
    (ComponentClassification.CatalogueBCentralQuotient.pComponent_quasisimple_iff f hf_central p
      (S.subgroupOf (fixedSubgroup y)) hSpc).mpr hMq
  exact CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSle).symm hSsub_q

end CFSG.StandardType

end
