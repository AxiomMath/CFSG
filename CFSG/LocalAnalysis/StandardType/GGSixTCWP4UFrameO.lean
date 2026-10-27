module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open

private lemma commutator_mul_aux' {G : Type*} [Group G] {n x y : G}
    (hzx : (n * y * n⁻¹ * y⁻¹) * x = x * (n * y * n⁻¹ * y⁻¹)) :
    n * (x * y) * n⁻¹ * (x * y)⁻¹ = (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) := by
  have h : (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) * x
      = n * (x * y) * n⁻¹ * (x * y)⁻¹ * x := by
    calc (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) * x
        = (n * x * n⁻¹ * x⁻¹) * ((n * y * n⁻¹ * y⁻¹) * x) := by group
      _ = (n * x * n⁻¹ * x⁻¹) * (x * (n * y * n⁻¹ * y⁻¹)) := by rw [hzx]
      _ = n * x * n⁻¹ * (n * y * n⁻¹ * y⁻¹) := by group
      _ = n * (x * y) * n⁻¹ * (x * y)⁻¹ * x := by group
  exact (mul_right_cancel h).symm

theorem commute_of_central_commutator' {G : Type*} [Group G] {J Z : Subgroup G}
    (hJ : commutator ↥J = ⊤) (hZJ : ∀ z ∈ Z, ∀ j ∈ J, z * j = j * z)
    (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) {n : G}
    (hn : ∀ j ∈ J, n * j * n⁻¹ * j⁻¹ ∈ Z) : ∀ j ∈ J, n * j = j * n := by
  let f : ↥J → ↥Z := fun j => ⟨n * (j : G) * n⁻¹ * (j : G)⁻¹, hn (j : G) j.2⟩
  have hmul : ∀ a b : ↥J, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    exact commutator_mul_aux' (x := (a : G)) (y := (b : G))
      (hZJ _ (hn (b : G) b.2) (a : G) a.2)
  let cmap : ↥J →* ↥Z := MonoidHom.mk' f hmul
  have hker : commutator ↥J ≤ cmap.ker := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hZZ _ (cmap g₁).2 _ (cmap g₂).2)
  intro j hj
  have htop : (⟨j, hj⟩ : ↥J) ∈ commutator ↥J := by
    rw [hJ]
    exact Subgroup.mem_top _
  have hone : cmap ⟨j, hj⟩ = 1 := hker htop
  have h1 : n * j * n⁻¹ * j⁻¹ = 1 := congrArg Subtype.val hone
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

section Frame

variable {X Y : Type*} [Group X] [Group Y]

structure GGTCUFrameO (G₀ B : Subgroup X) (Y : Type*) [Group Y] where
  Θ : (↥G₀ ⧸ Subgroup.center ↥G₀) →* Y
  Θinj : Function.Injective Θ
  ν : ↥B →* Y
  νinj : Function.Injective ν
  act : ∀ (b : ↥B) (y y' : ↥G₀), (y' : X) = (b : X) * (y : X) * (b : X)⁻¹ →
    Θ (QuotientGroup.mk y') = ν b * Θ (QuotientGroup.mk y) * (ν b)⁻¹

namespace GGTCUFrameO

variable {G₀ B : Subgroup X} (fr : GGTCUFrameO G₀ B Y)

@[expose] def BimgO : Subgroup Y := fr.ν.range

@[expose] def DimgO (D : Subgroup X) : Subgroup Y := (D.subgroupOf B).map fr.ν

@[expose] def JimgO (J : Subgroup X) : Subgroup Y :=
  ((J.subgroupOf G₀).map (QuotientGroup.mk' (Subgroup.center ↥G₀))).map fr.Θ

theorem card_BimgO : Nat.card fr.BimgO = Nat.card B :=
  (Nat.card_congr (MonoidHom.ofInjective fr.νinj).toEquiv).symm

theorem DimgO_le_BimgO {D : Subgroup X} : fr.DimgO D ≤ fr.BimgO := by
  rintro _ ⟨d, _, rfl⟩
  exact ⟨d, rfl⟩

theorem card_DimgO {D : Subgroup X} (hDB : D ≤ B) : Nat.card (fr.DimgO D) = Nat.card D := by
  rw [DimgO, Subgroup.card_map_of_injective fr.νinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv

theorem isElemAbelian_BimgO {p : ℕ} (hBel : IsElemAbelian p B) : IsElemAbelian p fr.BimgO := by
  have h1 : IsElemAbelian p (B.subgroupOf B) := hBel.subgroupOf B
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := h1.map fr.ν
  rwa [Subgroup.map_top] at h2

theorem nonempty_equiv_JimgO {J : Subgroup X} (hJG : J ≤ G₀) (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(fr.JimgO J) ⧸ Subgroup.center ↥(fr.JimgO J)) := by
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJq.1
  have hperf0 : Group.IsPerfect ↥(J.subgroupOf G₀) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).symm.surjective
  obtain ⟨q2⟩ := centerQuot_equiv_map_central (Z := Subgroup.center ↥G₀) le_rfl hperf0
  exact ⟨(centerQuotMulEquivOfEquiv (Subgroup.subgroupOfEquivOfLe hJG).symm).trans
    (q2.trans (centerQuotMulEquivOfEquiv (Subgroup.equivMapOfInjective _ fr.Θ fr.Θinj)))⟩

@[expose] noncomputable def mapConjO (g : Y) : GGTCUFrameO G₀ B Y where
  Θ := (MulAut.conj g).toMonoidHom.comp fr.Θ
  Θinj := (MulAut.conj g).injective.comp fr.Θinj
  ν := (MulAut.conj g).toMonoidHom.comp fr.ν
  νinj := (MulAut.conj g).injective.comp fr.νinj
  act b y y' h := by
    have := fr.act b y y' h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this]
    group

theorem mem_conj_of_normalizer (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) (b : ↥B) (y : ↥G₀) :
    (b : X) * (y : X) * (b : X)⁻¹ ∈ G₀ :=
  (Subgroup.mem_set_normalizer_iff.mp (hBN b.2) (y : X)).mp y.2

theorem isComponentOf_JimgO {D J : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) (hDB : D ≤ B) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    IsComponentOf (fr.JimgO J)
      (fr.Θ.range ⊓ Subgroup.centralizer ((fr.DimgO D : Subgroup Y) : Set Y)) := by
  classical
  set T : Subgroup (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    Subgroup.comap fr.Θ (Subgroup.centralizer ((fr.DimgO D : Subgroup Y) : Set Y)) with hT
  set C : Subgroup ↥G₀ := (G₀ ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G₀ with hC
  have h1 : IsComponentOf (J.subgroupOf G₀) C := isComponentOf_subgroupOf_of_le hJ hJG
  have hCT : C.map (QuotientGroup.mk' (Subgroup.center ↥G₀)) ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD : (y : X) ∈ Subgroup.centralizer (D : Set X) := (Subgroup.mem_inf.1 hy).2
    rw [hT, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hd' : (d : X) ∈ D := Subgroup.mem_subgroupOf.1 hd
    have hdy : (d : X) * (y : X) = (y : X) * (d : X) := Subgroup.mem_centralizer_iff.1 hyD _ hd'
    have h := fr.act d y y (by rw [hdy, mul_inv_cancel_right])
    rw [QuotientGroup.mk'_apply]
    rw [eq_mul_inv_iff_mul_eq] at h
    exact h.symm
  have hN : ((C.map (QuotientGroup.mk' (Subgroup.center ↥G₀))).subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCT]
    rintro h k ⟨y, hy, rfl⟩ hk
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective k
    refine Subgroup.mem_map.mpr ⟨z * y * z⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hyD : (y : X) ∈ Subgroup.centralizer (D : Set X) := (Subgroup.mem_inf.1 hy).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(z * y * z⁻¹ : ↥G₀).2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    have hzT := Subgroup.mem_comap.1 hk
    rw [Subgroup.mem_centralizer_iff] at hzT
    set d : ↥B := ⟨h', hDB hh'⟩ with hd
    have hdy : (d : X) * (y : X) = (y : X) * (d : X) := Subgroup.mem_centralizer_iff.1 hyD _ hh'
    have hcomm : fr.ν d * fr.Θ (QuotientGroup.mk z) = fr.Θ (QuotientGroup.mk z) * fr.ν d :=
      hzT (fr.ν d) ⟨d, Subgroup.mem_subgroupOf.2 hh', rfl⟩
    set zd : ↥G₀ := ⟨(d : X) * (z : X) * (d : X)⁻¹, mem_conj_of_normalizer hBN d z⟩ with hzd
    have hact := fr.act d z zd rfl
    have hΘ : fr.Θ (QuotientGroup.mk zd) = fr.Θ (QuotientGroup.mk z) := by
      rw [hact, hcomm, mul_inv_cancel_right]
    have hmk : (QuotientGroup.mk zd : ↥G₀ ⧸ Subgroup.center ↥G₀) = QuotientGroup.mk z :=
      fr.Θinj hΘ
    have hc : z⁻¹ * zd ∈ Subgroup.center ↥G₀ := QuotientGroup.eq.1 hmk.symm
    have hzdc : zd = z * (z⁻¹ * zd) := by group
    have hcy : (z⁻¹ * zd) * y = y * (z⁻¹ * zd) := (Subgroup.mem_center_iff.1 hc y).symm
    have hcyX : ((z⁻¹ * zd : ↥G₀) : X) * (y : X) = (y : X) * ((z⁻¹ * zd : ↥G₀) : X) :=
      congrArg Subtype.val hcy
    have e1 : (d : X) * ((z : X) * (y : X) * (z : X)⁻¹) * (d : X)⁻¹ =
        (zd : X) * (y : X) * (zd : X)⁻¹ := by
      have hyd : (d : X) * (y : X) * (d : X)⁻¹ = (y : X) := by rw [hdy, mul_inv_cancel_right]
      calc (d : X) * ((z : X) * (y : X) * (z : X)⁻¹) * (d : X)⁻¹
          = ((d : X) * (z : X) * (d : X)⁻¹) * ((d : X) * (y : X) * (d : X)⁻¹) *
              ((d : X) * (z : X) * (d : X)⁻¹)⁻¹ := by group
        _ = (zd : X) * (y : X) * (zd : X)⁻¹ := by rw [hyd]
    have e2 : (zd : X) * (y : X) * (zd : X)⁻¹ = (z : X) * (y : X) * (z : X)⁻¹ := by
      have h2 : (zd : X) = (z : X) * ((z⁻¹ * zd : ↥G₀) : X) := congrArg Subtype.val hzdc
      rw [h2]
      calc (z : X) * ((z⁻¹ * zd : ↥G₀) : X) * (y : X) *
            ((z : X) * ((z⁻¹ * zd : ↥G₀) : X))⁻¹
          = (z : X) * (((z⁻¹ * zd : ↥G₀) : X) * (y : X) * ((z⁻¹ * zd : ↥G₀) : X)⁻¹) *
              (z : X)⁻¹ := by group
        _ = (z : X) * (y : X) * (z : X)⁻¹ := by rw [hcyX]; group
    have e3 : (d : X) * ((z : X) * (y : X) * (z : X)⁻¹) * (d : X)⁻¹ =
        (z : X) * (y : X) * (z : X)⁻¹ := e1.trans e2
    show (h' : X) * ((z : X) * (y : X) * (z : X)⁻¹) = ((z : X) * (y : X) * (z : X)⁻¹) * h'
    exact mul_inv_eq_iff_eq_mul.1 e3
  have h2 := isComponentOf_map_central (Z := Subgroup.center ↥G₀) le_rfl hCT hN h1
  have h3 := isComponentOf_map_injective fr.Θ fr.Θinj h2
  rw [hT, Subgroup.map_comap_eq] at h3
  exact h3

theorem le_DimgO_of_commute {D J : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) (hJG : J ≤ G₀) (hJ : commutator ↥J = ⊤)
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D) :
    fr.BimgO ⊓ Subgroup.centralizer ((fr.JimgO J : Subgroup Y) : Set Y) ≤ fr.DimgO D := by
  rintro _ ⟨⟨b, rfl⟩, hC⟩
  have hZ : ∀ j ∈ J, (b : X) * j * (b : X)⁻¹ * j⁻¹ ∈
      (Subgroup.center ↥G₀).map G₀.subtype := by
    intro j hj
    set jG : ↥G₀ := ⟨j, hJG hj⟩ with hjG
    set j' : ↥G₀ := ⟨(b : X) * (jG : X) * (b : X)⁻¹, mem_conj_of_normalizer hBN b jG⟩ with hj'
    have hact := fr.act b jG j' rfl
    have hmem : fr.Θ (QuotientGroup.mk jG) ∈ fr.JimgO J :=
      ⟨_, ⟨jG, Subgroup.mem_subgroupOf.2 hj, rfl⟩, rfl⟩
    have hcomm : fr.Θ (QuotientGroup.mk jG) * fr.ν b = fr.ν b * fr.Θ (QuotientGroup.mk jG) :=
      Subgroup.mem_centralizer_iff.1 hC _ hmem
    have hΘ : fr.Θ (QuotientGroup.mk j') = fr.Θ (QuotientGroup.mk jG) := by
      rw [hact, ← hcomm, mul_inv_cancel_right]
    have hmk : (QuotientGroup.mk j' : ↥G₀ ⧸ Subgroup.center ↥G₀) = QuotientGroup.mk jG :=
      fr.Θinj hΘ
    have hc : jG⁻¹ * j' ∈ Subgroup.center ↥G₀ := QuotientGroup.eq.1 hmk.symm
    refine ⟨jG⁻¹ * j', hc, ?_⟩
    have hcX : (jG : X) * ((jG⁻¹ * j' : ↥G₀) : X) = ((jG⁻¹ * j' : ↥G₀) : X) * (jG : X) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc jG)
    have h1 : ((jG⁻¹ * j' : ↥G₀) : X) * (jG : X) = (j' : X) := by
      rw [← hcX]
      show (jG : X) * ((jG : X)⁻¹ * (j' : X)) = (j' : X)
      group
    show ((jG⁻¹ * j' : ↥G₀) : X) = (b : X) * j * (b : X)⁻¹ * j⁻¹
    calc ((jG⁻¹ * j' : ↥G₀) : X) = (j' : X) * (jG : X)⁻¹ := eq_mul_inv_of_mul_eq h1
      _ = (b : X) * j * (b : X)⁻¹ * j⁻¹ := rfl
  have hZJ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype, ∀ j ∈ J, z * j = j * z := by
    rintro _ ⟨c, hc, rfl⟩ j hj
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨j, hJG hj⟩)).symm
  have hZZ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype,
      ∀ z' ∈ (Subgroup.center ↥G₀).map G₀.subtype, z * z' = z' * z := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc c')).symm
  have hcomm := commute_of_central_commutator' hJ hZJ hZZ hZ
  have hbJ : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hcomm j hj).symm
  have hbD : (b : X) ∈ D := by
    rw [← hcent]
    exact Subgroup.mem_inf.2 ⟨b.2, hbJ⟩
  exact ⟨b, Subgroup.mem_subgroupOf.2 hbD, rfl⟩

end GGTCUFrameO

end Frame

section Conclusion

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem exists_torus_uframeO
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B : Subgroup X} [Finite B] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S : LangSetup τ (AlgebraicClosure K) 5)
    (fr : GGTCUFrameO G₀ B (ModGL τ (AlgebraicClosure K))) (hΘ : fr.Θ.range = S.Γ)
    (hνM : ∀ b, fr.ν b ∈ S.D.model) (hBel : IsElemAbelian p B)
    (htor : UToralAt τ p (Nat.card B)) :
    ∃ S₁ : LangSetup τ (AlgebraicClosure K) 5, S₁.D.q = S.D.q ∧
      ∃ fr₁ : GGTCUFrameO G₀ B (ModGL τ (AlgebraicClosure K)),
        fr₁.Θ.range = S₁.Γ ∧ fr₁.BimgO ≤ S₁.D.torus := by
  classical
  have : Finite fr.BimgO := Finite.of_equiv _ (MonoidHom.ofInjective fr.νinj).toEquiv
  have hBmodel : fr.BimgO ≤ S.D.model := by
    rintro _ ⟨b, rfl⟩
    exact hνM b
  have hBadj : fr.BimgO ≤ adjointGroup τ (AlgebraicClosure K) := hBmodel.trans inf_le_left
  have hBimgel : IsElemAbelian p fr.BimgO := fr.isElemAbelian_BimgO hBel
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨g, hg, hgx⟩ := htor K fr.BimgO hBadj hBimgel fr.card_BimgO
  obtain ⟨g₁, hg₁, S₁, -, hq₁, hstep, -, htorus, -, -⟩ :=
    ggTCInputG3Toral_holds τ (AlgebraicClosure K) 5 S hτ p hp hp2 fr.BimgO hBmodel hBimgel
      ⟨g, hg, hgx⟩
  have hΓ := gamma_eq_map_of_step S S₁ hg₁ hstep
  refine ⟨S₁, hq₁, fr.mapConjO g₁⁻¹, ?_, ?_⟩
  · change (((MulAut.conj g₁⁻¹).toMonoidHom).comp fr.Θ).range = S₁.Γ
    rw [MonoidHom.range_comp, hΘ, hΓ]
  · rintro _ ⟨b, rfl⟩
    have h := htorus _ ⟨b, rfl⟩
    change ((MulAut.conj g₁⁻¹).toMonoidHom.comp fr.ν) b ∈ S₁.D.torus
    simpa [MulAut.conj_apply] using h

theorem uframeO_conclude
    {τ : Tag} (hField : UFieldInput τ)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S₁ : LangSetup τ (AlgebraicClosure K) 5)
    (hq : S₁.D.q = 2 ^ f) (fr₁ : GGTCUFrameO G₀ B (ModGL τ (AlgebraicClosure K)))
    (hΘ : fr₁.Θ.range = S₁.Γ) (hBT : fr₁.BimgO ≤ S₁.D.torus)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hBel : IsElemAbelian p B) (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (S₁.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BimgO := fr₁.isElemAbelian_BimgO hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BimgO := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.νinj).toEquiv
  have hD₁B : fr₁.DimgO D ≤ fr₁.BimgO := fr₁.DimgO_le_BimgO
  have hpar : ∀ u : fr₁.DimgO D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DimgO D => rootDiagUnit τ (a u)) =
      ((fr₁.DimgO D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DimgO D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JimgO J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DimgO D => rootDiagUnit τ (a u))) := by
    rw [hrange, ← hΘ]
    exact fr₁.isComponentOf_JimgO hBN hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DimgO D) a haT hap (fr₁.JimgO J) hcomp
  rw [hq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JimgO hJG hJ.2.2).some hfield hF
  have hC := fr₁.le_DimgO_of_commute hBN hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BimgO (fr₁.DimgO D) (fr₁.JimgO J) hBT hBel₁.2 hD₁B a i
    hspan hC
  refine ⟨componentRoots (famCharHom a) i, isRootComponent_componentRoots i, ?_, ?_,
    two_mul_finrank_le_of_orbit S₁ a haT i h2⟩
  · obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
      (fun γ hγ => rho_mem_kernelRoots_famChar S₁ a haT hγ) S₁.frob.iform_eq i
    have hij : i ≠ j := by
      rintro rfl
      exact image_ne_of_two_le_componentOrbitLength h2 hj
    intro γ hγ δ hδ
    rw [hj] at hδ
    refine ⟨iform_eq_zero_of_mem_componentRoots' hij hγ hδ, ?_⟩
    obtain ⟨hγk, hγi⟩ := hγ
    obtain ⟨hδk, hδi⟩ := hδ
    have := not_isRoot_of_mk_ne (χ := famCharHom a) (α := ⟨γ, hγk⟩) (β := ⟨δ, hδk⟩)
      (by rw [hγi, hδi]; exact hij) one_pos one_pos
    simpa using this
  · calc Nat.card B = Nat.card fr₁.BimgO := fr₁.card_BimgO.symm
      _ ≤ Nat.card (fr₁.DimgO D) *
          p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
      _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
        rw [fr₁.card_DimgO hDB, hDcard, pow_add]

theorem uframeO_main
    {τ : Tag} (hField : UFieldInput τ)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hex : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup τ (AlgebraicClosure K) 5), S.D.q = 2 ^ f ∧
        ∃ fr : GGTCUFrameO G₀ B (ModGL τ (AlgebraicClosure K)),
          fr.Θ.range = S.Γ ∧ ∀ b, fr.ν b ∈ S.D.model)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt τ p (Nat.card B)) :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧ (∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  obtain ⟨K, instF, instFin, instChar, S, hq, fr, hΘ, hνM⟩ := hex
  obtain ⟨S₁, hq₁, fr₁, hΘ₁, hBT⟩ :=
    exists_torus_uframeO hτ hp hp2 S fr hΘ hνM hBel htor
  obtain ⟨Ψ, hΨ, horth, hcard, h2r⟩ :=
    uframeO_conclude hField hp hp2 S₁ (hq₁.trans hq) fr₁ hΘ₁ hBT hBN hBel hDB hDcard hJG hJ
      hcent hF
  exact ⟨Ψ, S₁.ρ, hΨ, S₁.frob.isRoot_iff, S₁.frob.iform_eq, horth, hcard, h2r⟩

end Conclusion

end CFSG.StandardType.TableCRes
