module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

private theorem sSup_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (S : Set (Subgroup G)) :
    (sSup S).map f = sSup ((fun K : Subgroup G => K.map f) '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨K, hK, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨K, hK, rfl⟩
    exact Subgroup.map_mono (le_sSup hK)

theorem aschbacherSolvableCore_eq_solvableRadical (h3 : ¬ 3 ∣ Nat.card H) :
    aschbacherSolvableCore 3 H = CFSG.solvableRadical H := by
  set R := CFSG.solvableRadical H with hR
  have hR3 : Nat.Coprime 3 (Nat.card R) := by
    refine (Nat.prime_three.coprime_iff_not_dvd).mpr ?_
    intro hdvd
    exact h3 (hdvd.trans (Subgroup.card_subgroup_dvd_card R))
  have htop : pPrimeCore 3 R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine le_sSup (show ⊤ ∈ {K : Subgroup R | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}
      from ⟨inferInstance, by simpa using hR3⟩) trivial
  rw [aschbacherSolvableCore, inSubgroup, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem normal_sSup_thetaComponents : (sSup (thetaComponents 3 H)).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  have hstep : ∀ g : H,
      (sSup (thetaComponents 3 H)).map (MulAut.conj g).toMonoidHom ≤
        sSup (thetaComponents 3 H) := by
    intro g
    rw [sSup_map]
    refine sSup_le ?_
    rintro _ ⟨L, hL, rfl⟩
    exact le_sSup (map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj g) hL)
  intro g
  refine le_antisymm (hstep g) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hstep g⁻¹)
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id H := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_one,
      one_mul, mul_one, MonoidHom.id_apply]
    group
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  exact h

instance sSup_thetaComponents_normal : (sSup (thetaComponents 3 H)).Normal :=
  normal_sSup_thetaComponents

theorem commutator_mulAut_le_conj_range_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (h : commutator (MulAut A) ≤ (MulAut.conj : A →* MulAut A).range) :
    commutator (MulAut B) ≤ (MulAut.conj : B →* MulAut B).range := by
  have hmap : (commutator (MulAut A)).map (MulAut.congr e).toMonoidHom =
      commutator (MulAut B) := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective, commutator_def]
  have hrange : ((MulAut.conj : A →* MulAut A).range).map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : B →* MulAut B).range := by
    ext f
    constructor
    · rintro ⟨-, ⟨a, rfl⟩, rfl⟩
      refine ⟨e a, ?_⟩
      ext b
      simp [MulAut.congr_apply, MulAut.conj_apply]
    · rintro ⟨b, rfl⟩
      refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
      ext b
      simp [MulAut.congr_apply, MulAut.conj_apply]
  calc commutator (MulAut B) =
        (commutator (MulAut A)).map (MulAut.congr e).toMonoidHom := hmap.symm
    _ ≤ ((MulAut.conj : A →* MulAut A).range).map (MulAut.congr e).toMonoidHom :=
        Subgroup.map_mono h
    _ = (MulAut.conj : B →* MulAut B).range := hrange

private theorem card_componentIndex_le_two {K : Type*} [Group K] [Finite K]
    (htwo : ∀ J₁ : Subgroup K, IsComponent J₁ → ∀ J₂ : Subgroup K, IsComponent J₂ →
      ∀ J₃ : Subgroup K, IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) :
    Nat.card (CFSG.LocalCores.ComponentIndex K) ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := CFSG.LocalCores.ComponentIndex K) (by
      have h' : 2 < Fintype.card (CFSG.LocalCores.ComponentIndex K) := by simpa using h
      have h3 : 3 ≤ Fintype.card (CFSG.LocalCores.ComponentIndex K) := by omega
      simpa using h3)
  have h012 := htwo (f 0).1 (f 0).2 (f 1).1 (f 1).2 (f 2).1 (f 2).2
  have h01 : f 0 ≠ f 1 := f.injective.ne (by decide)
  have h02 : f 0 ≠ f 2 := f.injective.ne (by decide)
  have h12 : f 1 ≠ f 2 := f.injective.ne (by decide)
  rcases h012 with h | h | h
  · exact h01 (Subtype.ext h)
  · exact h02 (Subtype.ext h)
  · exact h12 (Subtype.ext h)

private noncomputable instance componentIndexMulAction {K : Type*} [Group K] :
    MulAction (ConjAct K) (CFSG.LocalCores.ComponentIndex K) where
  smul g J :=
    ⟨J.1.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom,
      CFSG.LocalCores.isComponent_map_mulEquiv _ J.2⟩
  one_smul J := by
    apply Subtype.ext
    show J.1.map (MulAut.conj (ConjAct.ofConjAct (1 : ConjAct K))).toMonoidHom = J.1
    have h1 : (MulAut.conj (ConjAct.ofConjAct (1 : ConjAct K))).toMonoidHom =
        MonoidHom.id K := by
      ext x
      simp [MulAut.conj_apply]
    rw [h1, Subgroup.map_id]
  mul_smul g h J := by
    apply Subtype.ext
    show J.1.map (MulAut.conj (ConjAct.ofConjAct (g * h))).toMonoidHom =
      (J.1.map (MulAut.conj (ConjAct.ofConjAct h)).toMonoidHom).map
        (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

private theorem commutator_le_componentNormalizers {K : Type*} [Group K] [Finite K]
    (htwo : ∀ J₁ : Subgroup K, IsComponent J₁ → ∀ J₂ : Subgroup K, IsComponent J₂ →
      ∀ J₃ : Subgroup K, IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) :
    commutator K ≤ ⨅ J : CFSG.LocalCores.ComponentIndex K,
      Subgroup.normalizer (J.1 : Set K) := by
  have hcard := card_componentIndex_le_two htwo
  haveI : IsMulCommutative (Equiv.Perm (CFSG.LocalCores.ComponentIndex K)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  have hker : commutator (ConjAct K) ≤
      (MulAction.toPermHom (ConjAct K) (CFSG.LocalCores.ComponentIndex K)).ker :=
    Abelianization.commutator_subset_ker _
  intro x hx
  rw [Subgroup.mem_iInf]
  intro J
  have hx' : ConjAct.toConjAct x ∈ commutator (ConjAct K) := by
    have hmap : (commutator K).map
        (MulEquiv.toMonoidHom (ConjAct.toConjAct : K ≃* ConjAct K)) =
        commutator (ConjAct K) := by
      rw [map_commutator_eq]
      rw [MonoidHom.range_eq_top_of_surjective _
        (MulEquiv.surjective (ConjAct.toConjAct : K ≃* ConjAct K))]
      exact (commutator_def (ConjAct K)).symm
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hfix := hker hx'
  rw [MonoidHom.mem_ker] at hfix
  have hact : (ConjAct.toConjAct x) • J = J := by
    have h := congrArg (fun e : Equiv.Perm (CFSG.LocalCores.ComponentIndex K) => e J) hfix
    simpa [MulAction.toPermHom_apply] using h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hact' : J.1.map (MulAut.conj (ConjAct.ofConjAct (ConjAct.toConjAct x))).toMonoidHom =
      J.1 := congrArg Subtype.val hact
  simpa using hact'

private theorem exists_mem_layer_mul_mem_centralizer_of {K : Type*} [Group K] [Finite K]
    (h : K)
    (hinner : ∀ J : Subgroup K, IsComponent J → ∃ k ∈ J, ∀ y ∈ J,
      h * y * h⁻¹ = k * y * k⁻¹) :
    ∃ e ∈ CFSG.layer K, e⁻¹ * h ∈ Subgroup.centralizer (CFSG.layer K : Set K) := by
  classical
  choose k hkK hk using hinner
  set x : ∀ J : CFSG.LocalCores.ComponentIndex K, J.1 :=
    fun J => ⟨k J.1 J.2, hkK J.1 J.2⟩ with hx
  set e := CFSG.LocalCores.layerMul K x with he
  have heE : e ∈ CFSG.layer K := by
    rw [← CFSG.LocalCores.layerMul_range]
    exact ⟨x, rfl⟩
  refine ⟨e, heE, ?_⟩
  have hK : ∀ (J : CFSG.LocalCores.ComponentIndex K) (y : K), y ∈ J.1 →
      y * (e⁻¹ * h) = (e⁻¹ * h) * y := by
    intro J y hy
    have hu : Commute y (CFSG.LocalCores.layerMul K (Function.update x J 1)) :=
      CFSG.LocalCores.commute_layerMul_update x J hy
    have hdecomp := CFSG.LocalCores.layerMul_eq_mul_update x J
    set u := CFSG.LocalCores.layerMul K (Function.update x J 1) with hudef
    have hxJ : ((x J : J.1) : K) = k J.1 J.2 := rfl
    rw [hxJ] at hdecomp
    have hkey : h * y * h⁻¹ = k J.1 J.2 * y * (k J.1 J.2)⁻¹ := hk J.1 J.2 y hy
    have hu' : y * u⁻¹ = u⁻¹ * y := hu.inv_right.eq
    calc y * (e⁻¹ * h) = y * u⁻¹ * (k J.1 J.2)⁻¹ * h := by rw [he, hdecomp]; group
      _ = u⁻¹ * y * (k J.1 J.2)⁻¹ * h := by rw [hu']
      _ = (k J.1 J.2 * u)⁻¹ * (k J.1 J.2 * y * (k J.1 J.2)⁻¹) * h := by group
      _ = (k J.1 J.2 * u)⁻¹ * (h * y * h⁻¹) * h := by rw [hkey]
      _ = (e⁻¹ * h) * y := by rw [he, hdecomp]; group
  have hle : CFSG.layer K ≤ Subgroup.centralizer ({e⁻¹ * h} : Set K) :=
    sSup_le fun J hJ y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hK ⟨J, hJ⟩ y hy)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

private theorem exists_inner_on_component {K : Type*} [Group K] {x y : K}
    (hx : ∀ J : Subgroup K, IsComponent J → x ∈ Subgroup.normalizer (J : Set K))
    (hy : ∀ J : Subgroup K, IsComponent J → y ∈ Subgroup.normalizer (J : Set K))
    (hout : ∀ J : Subgroup K, IsComponent J →
      commutator (MulAut J) ≤ (MulAut.conj : J →* MulAut J).range) :
    ∀ J : Subgroup K, IsComponent J → ∃ k ∈ J, ∀ z ∈ J,
      ⁅x, y⁆ * z * ⁅x, y⁆⁻¹ = k * z * k⁻¹ := by
  intro J hJ
  have hxJ : x ∈ Subgroup.normalizer (J : Set K) := hx J hJ
  have hyJ : y ∈ Subgroup.normalizer (J : Set K) := hy J hJ
  let α : MulAut J := J.normalizerMonoidHom ⟨x, hxJ⟩
  let β : MulAut J := J.normalizerMonoidHom ⟨y, hyJ⟩
  have hmem : ⁅α, β⁆ ∈ commutator (MulAut J) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨k, hk⟩ := hout J hJ hmem
  refine ⟨(k : K), k.2, fun z hz => ?_⟩
  let zJ : J := ⟨z, hz⟩
  have hα : ∀ w : J, ((α w : J) : K) = x * (w : K) * x⁻¹ := by
    intro w
    simpa [α] using Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨x, hxJ⟩ w
  have hβ : ∀ w : J, ((β w : J) : K) = y * (w : K) * y⁻¹ := by
    intro w
    simpa [β] using Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨y, hyJ⟩ w
  have hαinv : ∀ w : J, (((α⁻¹) w : J) : K) = x⁻¹ * (w : K) * x := by
    intro w
    simpa [α] using Subgroup.normalizerMonoidHom_apply_symm_apply_coe J ⟨x, hxJ⟩ w
  have hβinv : ∀ w : J, (((β⁻¹) w : J) : K) = y⁻¹ * (w : K) * y := by
    intro w
    simpa [β] using Subgroup.normalizerMonoidHom_apply_symm_apply_coe J ⟨y, hyJ⟩ w
  have hconj : ((⁅α, β⁆ zJ : J) : K) = ⁅x, y⁆ * z * ⁅x, y⁆⁻¹ := by
    simp only [commutatorElement_def, MulAut.mul_apply, hα, hβ, hαinv, hβinv, zJ]
    group
  have hkz : ((⁅α, β⁆ zJ : J) : K) = (k : K) * z * (k : K)⁻¹ := by
    have h1 : (⁅α, β⁆) zJ = k * zJ * k⁻¹ := by
      rw [← hk]
      simp [MulAut.conj_apply]
    calc ((⁅α, β⁆ zJ : J) : K) = ((k * zJ * k⁻¹ : J) : K) := congrArg Subtype.val h1
      _ = (k : K) * z * (k : K)⁻¹ := by simp [zJ]
  calc ⁅x, y⁆ * z * ⁅x, y⁆⁻¹ = ((⁅α, β⁆ zJ : J) : K) := hconj.symm
    _ = (k : K) * z * (k : K)⁻¹ := hkz

private theorem le_layer_of_isPerfect {K : Type*} [Group K] [Finite K]
    (hrad : CFSG.solvableRadical K = ⊥)
    (htwo : ∀ J₁ : Subgroup K, IsComponent J₁ → ∀ J₂ : Subgroup K, IsComponent J₂ →
      ∀ J₃ : Subgroup K, IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)
    (hout : ∀ J : Subgroup K, IsComponent J →
      commutator (MulAut J) ≤ (MulAut.conj : J →* MulAut J).range)
    {P : Subgroup K} (hP : Group.IsPerfect P) : P ≤ CFSG.layer K := by
  let K₀ : Subgroup K := ⨅ J : CFSG.LocalCores.ComponentIndex K,
    Subgroup.normalizer (J.1 : Set K)
  have hK' : commutator K ≤ K₀ := commutator_le_componentNormalizers htwo
  have hK0comm : ⁅K₀, K₀⁆ ≤ CFSG.layer K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hinner := exists_inner_on_component (K := K) (x := x) (y := y)
      (fun J hJ => by simpa [K₀] using Subgroup.mem_iInf.mp hx ⟨J, hJ⟩)
      (fun J hJ => by simpa [K₀] using Subgroup.mem_iInf.mp hy ⟨J, hJ⟩) hout
    obtain ⟨e, heE, heC⟩ := exists_mem_layer_mul_mem_centralizer_of ⁅x, y⁆ hinner
    have hcent := CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot
      (G := K) hrad
    have h1 : e⁻¹ * ⁅x, y⁆ = 1 := by
      have h := heC
      rw [hcent, Subgroup.mem_bot] at h
      exact h
    have h2 : ⁅x, y⁆ = e := by
      calc ⁅x, y⁆ = e * (e⁻¹ * ⁅x, y⁆) := by group
        _ = e * 1 := by rw [h1]
        _ = e := mul_one e
    rw [h2]
    exact heE
  have hK'' : ⁅(commutator K : Subgroup K), (commutator K : Subgroup K)⁆ ≤ CFSG.layer K :=
    (Subgroup.commutator_mono hK' hK').trans hK0comm
  have hder : derivedSeries K 2 ≤ CFSG.layer K := by
    rw [derivedSeries_succ, derivedSeries_one]
    exact hK''
  haveI hchar : (CFSG.layer K).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hnorm : (CFSG.layer K).Normal := inferInstance
  have hQ : Group.IsSolvable (K ⧸ CFSG.layer K) := by
    have hmap := map_derivedSeries_eq (f := QuotientGroup.mk' (CFSG.layer K))
      (QuotientGroup.mk'_surjective _) 2
    refine ⟨⟨2, ?_⟩⟩
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hder
  haveI : Group.IsSolvable (K ⧸ CFSG.layer K) := hQ
  intro p hp
  haveI : Group.IsPerfect P := hP
  have hmap : P.map (QuotientGroup.mk' (CFSG.layer K)) = ⊥ := by
    by_contra hne
    haveI : Nontrivial (P.map (QuotientGroup.mk' (CFSG.layer K))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect (P.map (QuotientGroup.mk' (CFSG.layer K))) :=
      Group.IsPerfect.ofSurjective
        (f := (QuotientGroup.mk' (CFSG.layer K)).subgroupMap P)
        ((QuotientGroup.mk' (CFSG.layer K)).subgroupMap_surjective P)
    haveI : Group.IsSolvable (P.map (QuotientGroup.mk' (CFSG.layer K))) := inferInstance
    exact Group.IsPerfect.not_isSolvable (P.map (QuotientGroup.mk' (CFSG.layer K)))
      inferInstance
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  exact hmap hp

private theorem le_left_of_isPerfect_le_sup {E θ : Subgroup H} [E.Normal] [θ.Normal]
    (hθ : Group.IsSolvable θ) {P : Subgroup H} (hP : Group.IsPerfect P)
    (hPle : P ≤ E ⊔ θ) : P ≤ E := by
  let L : Subgroup H := E ⊔ θ
  let M : Subgroup L := E.subgroupOf L
  haveI : M.Normal := inferInstance
  haveI : Group.IsSolvable θ := hθ
  have hθle : θ ≤ L := by simpa [L] using le_sup_right
  let q : θ →* L ⧸ M := (QuotientGroup.mk' M).comp (Subgroup.inclusion hθle)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨x, hxL⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := E) (t := θ)).mp (show x ∈ E ⊔ θ from hxL)
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [q, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (inferInstance : E.Normal).conj_mem' a ha b
  have hLsol : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hq
  haveI : Group.IsPerfect P := hP
  have hPsub_perf : Group.IsPerfect (P.subgroupOf L) :=
    Group.IsPerfect.ofSurjective
      (f := ((Subgroup.subgroupOfEquivOfLe (show P ≤ L from hPle)).symm).toMonoidHom)
      (MulEquiv.surjective _)
  have hPR : CFSG.perfectResidual (↥L) ≤ E.subgroupOf L := by
    have hLsol' : Group.IsSolvable (L ⧸ E.subgroupOf L) := by simpa [M] using hLsol
    obtain ⟨r, hr⟩ :=
      (CFSG.isSolvable_quotient_iff_exists_derivedSeries_le (E.subgroupOf L)).mp hLsol'
    exact (iInf_le _ r).trans hr
  have hPsub : P.subgroupOf L ≤ CFSG.perfectResidual (↥L) :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
      (P.subgroupOf L) hPsub_perf
  have hsub : P.subgroupOf L ≤ E.subgroupOf L := hPsub.trans hPR
  have hmap := Subgroup.map_mono (f := L.subtype) hsub
  rwa [Subgroup.map_subgroupOf_eq_of_le (show P ≤ L from hPle),
    Subgroup.map_subgroupOf_eq_of_le (show E ≤ L from le_sup_left)] at hmap

theorem le_sSup_thetaComponents_of_isPerfect (h3 : ¬ 3 ∣ Nat.card H)
    (hout : ∀ L ∈ thetaComponents 3 H,
      commutator (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≤
        (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range)
    (htwo : ∀ L₁ ∈ thetaComponents 3 H, ∀ L₂ ∈ thetaComponents 3 H,
      ∀ L₃ ∈ thetaComponents 3 H, L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃)
    {P : Subgroup H} (hP : Group.IsPerfect P) : P ≤ sSup (thetaComponents 3 H) := by
  classical
  set θ := aschbacherSolvableCore 3 H with hθ
  set E := sSup (thetaComponents 3 H) with hE
  set K := H ⧸ θ with hK
  let π : H →* K := QuotientGroup.mk' θ
  have hθsol : θ = CFSG.solvableRadical H := aschbacherSolvableCore_eq_solvableRadical h3
  have hKrad : CFSG.solvableRadical K = ⊥ := by
    let e : K ≃* (H ⧸ CFSG.solvableRadical H) :=
      QuotientGroup.quotientMulEquivOfEq hθsol
    have hmap : (CFSG.solvableRadical K).map e.toMonoidHom = ⊥ := by
      rw [CFSG.SignalizerFunctorTheorem.McBride.solvableRadical_map_mulEquiv,
        CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient]
    rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_eq_bot e.toMonoidHom e.injective] at hmap
    exact le_bot_iff.mp hmap
  haveI : Finite K := inferInstance
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have htwoK : ∀ J₁ : Subgroup K, IsComponent J₁ → ∀ J₂ : Subgroup K, IsComponent J₂ →
      ∀ J₃ : Subgroup K, IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃ := by
    intro J₁ hJ₁ J₂ hJ₂ J₃ hJ₃
    obtain ⟨L₁, hL₁, hJ₁'⟩ := hbij.2.2 hJ₁
    obtain ⟨L₂, hL₂, hJ₂'⟩ := hbij.2.2 hJ₂
    obtain ⟨L₃, hL₃, hJ₃'⟩ := hbij.2.2 hJ₃
    rcases htwo L₁ hL₁ L₂ hL₂ L₃ hL₃ with h | h | h
    · exact Or.inl (by rw [← hJ₁', ← hJ₂', h])
    · exact Or.inr (Or.inl (by rw [← hJ₁', ← hJ₃', h]))
    · exact Or.inr (Or.inr (by rw [← hJ₂', ← hJ₃', h]))
  have houtK : ∀ J : Subgroup K, IsComponent J →
      commutator (MulAut J) ≤ (MulAut.conj : J →* MulAut J).range := by
    intro J hJ
    obtain ⟨L, hL, hLJ⟩ := hbij.2.2 hJ
    obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map (H := H) Nat.prime_three hL.2.1
    let e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* J :=
      η.trans (MulEquiv.subgroupCongr hLJ)
    exact commutator_mulAut_le_conj_range_of_mulEquiv e (hout L hL)
  haveI : Group.IsPerfect P := hP
  have hPbar : Group.IsPerfect (P.map π) :=
    Group.IsPerfect.ofSurjective (f := π.subgroupMap P) (π.subgroupMap_surjective P)
  have hPbar_le : P.map π ≤ CFSG.layer K :=
    le_layer_of_isPerfect hKrad htwoK houtK hPbar
  have hset : (fun L : Subgroup H => L.map π) '' thetaComponents 3 H = {J | IsComponent J} := by
    ext J
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact hbij.1 hL
    · intro hJ
      obtain ⟨L, hL, hLJ⟩ := hbij.2.2 hJ
      exact ⟨L, hL, hLJ⟩
  have hE_map : E.map π = CFSG.layer K := by
    rw [hE, sSup_map, hset, ← CFSG.layer.eq_sSup]
  have hP_le_sup : P ≤ E ⊔ θ := by
    have hle : P.map π ≤ E.map π := by
      rw [hE_map]
      exact hPbar_le
    have h := (Subgroup.map_le_map_iff (f := π)).mp hle
    rwa [QuotientGroup.ker_mk'] at h
  haveI hEnorm : E.Normal := normal_sSup_thetaComponents
  have hθsolvable : Group.IsSolvable θ := by
    rw [hθsol]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  exact le_left_of_isPerfect_le_sup (E := E) (θ := θ) hθsolvable hP hP_le_sup

theorem le_sSup_thetaComponentsIn_of_isPerfect {G : Type} [Group G] [Finite G]
    {X : Subgroup G} (h3 : ¬ 3 ∣ Nat.card X)
    (hout : ∀ L ∈ thetaComponents 3 ↥X,
      commutator (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≤
        (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range)
    (htwo : ∀ L₁ ∈ thetaComponents 3 ↥X, ∀ L₂ ∈ thetaComponents 3 ↥X,
      ∀ L₃ ∈ thetaComponents 3 ↥X, L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Group.IsPerfect P) :
    P ≤ sSup (thetaComponentsIn X) := by
  haveI : Group.IsPerfect P := hP
  let PX : Subgroup X := P.subgroupOf X
  have hPX_perf : Group.IsPerfect PX :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hle : PX ≤ sSup (thetaComponents 3 X) :=
    le_sSup_thetaComponents_of_isPerfect (H := X) h3 hout htwo hPX_perf
  have hmap := Subgroup.map_mono (f := X.subtype) hle
  rw [sSup_map] at hmap
  rwa [Subgroup.map_subgroupOf_eq_of_le hPX] at hmap

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
