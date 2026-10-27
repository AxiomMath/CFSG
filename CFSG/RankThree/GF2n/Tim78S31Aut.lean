module

public import CFSG.RankThree.GF2n.BenderFixInner
public import CFSG.RankThree.GF2n.Tim78S31Steps

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G]

@[expose] def conjRestrict (X : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) :
    ↥X ≃* ↥X where
  toFun z := ⟨y * z * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy z).mp z.2⟩
  invFun z := ⟨y⁻¹ * z * y, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) z).mp z.2
    rwa [inv_inv] at this⟩
  left_inv z := Subtype.ext (by simp only; group)
  right_inv z := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

variable [Finite G]

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include P hCen hU

theorem exists_inner {y x : G} (hy2 : y * y = 1) (hyV : conjSubgroup y U = V)
    (hx : x ∈ U ⊔ V)
    (hyC : ∀ c ∈ conjSubgroup x U, y * c * y⁻¹ * c⁻¹ ∈
      PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    ∃ c ∈ conjSubgroup x U, ∀ z ∈ U ⊔ V,
      (c * z * c⁻¹)⁻¹ * (y * z * y⁻¹) ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
  classical
  have D := P.qdata hCen hU
  have hN := D.normal_Q
  have QP := D.quotPair
  have hNe := P.N_eq hCen hU
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyX : y ∈ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := by
    have := mem_normalizer_sup_of_swap hy2 U
    rwa [hyV] at this
  have hyN : ∀ n ∈ nrm U V ⊔ nrm V U, y * n * y⁻¹ ∈ nrm U V ⊔ nrm V U := by
    intro n hn
    rw [hNe] at hn ⊢
    exact P.conj_N_of_swap hCen hU hy2 hyV hn
  set φ := conjRestrict (U ⊔ V) hyX with hφ
  have hφa : ∀ z : ↥(U ⊔ V), (φ z : G) = y * z * y⁻¹ := fun z => rfl
  have hφN : ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)).map (φ : ↥(U ⊔ V) →* ↥(U ⊔ V)) =
      (nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
      rw [Subgroup.mem_subgroupOf]
      exact hyN _ hw
    · intro hz
      refine ⟨φ.symm z, ?_, φ.apply_symm_apply z⟩
      rw [Subgroup.mem_subgroupOf] at hz
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have e : ((φ.symm z : ↥(U ⊔ V)) : G) = y * z * y⁻¹ := by
        show y⁻¹ * (z : G) * y = _
        rw [hyinv]
      rw [e]
      exact hyN _ hz
  set σ : MulAut (↥(U ⊔ V) ⧸ (nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)) :=
    QuotientGroup.congr _ _ φ hφN with hσ
  have hσmk : ∀ z : ↥(U ⊔ V),
      σ (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)) z) =
        QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)) (φ z) :=
    fun z => QuotientGroup.congr_mk' _ _ _ _ z
  have hφφ : ∀ z : ↥(U ⊔ V), φ (φ z) = z := fun z => Subtype.ext (by
    rw [hφa, hφa, hyinv]
    calc y * (y * (z : G) * y) * y = (y * y) * z * (y * y) := by group
      _ = z := by rw [hy2, one_mul, mul_one])
  have hσ2 : ∀ k, σ (σ k) = k := by
    intro k
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ k
    rw [hσmk, hσmk, hφφ]
  set T := ((conjSubgroup x U).subgroupOf (U ⊔ V)).map
    (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V))) with hTdef
  have hTc : T = conjSubgroup (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V))
      ⟨x, hx⟩) ((U.subgroupOf (U ⊔ V)).map
        (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)))) :=
    (QData.conj_image (B₀ := U) (B₁ := V) (A₀ := U) (A₁ := V) ⟨x, hx⟩ U).symm
  have hTs : StrongWC T := by
    rw [hTc]
    exact GF2n.StrongWC.conj QP.strongWC _
  have hT1 : T ≠ ⊥ := by
    rw [hTc]
    intro h
    apply QP.ne_bot
    have := card_conjSubgroup (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V))
      ⟨x, hx⟩) ((U.subgroupOf (U ⊔ V)).map
        (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V))))
    rw [h, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq _ this.symm
  have hfix : ∀ t ∈ T, σ t = t := by
    rintro _ ⟨c, hc, rfl⟩
    rw [hσmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, hNe]
    have hc' : (c : G) ∈ conjSubgroup x U := Subgroup.mem_subgroupOf.mp hc
    have h1 := P.conj_mem_N hCen hU ((U ⊔ V).inv_mem c.2)
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).inv_mem (hyC _ hc'))
    rw [inv_inv] at h1
    have e : (((φ c)⁻¹ * c : ↥(U ⊔ V)) : G) =
        (c : G)⁻¹ * (y * c * y⁻¹ * (c : G)⁻¹)⁻¹ * c := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφa]
      group
    rw [e]
    exact h1
  have hinner : ∃ t ∈ T, ∀ k, σ k = t * k * t⁻¹ := by
    obtain ⟨-, hmod⟩ := QP.models hCen hU
    rcases hmod with ⟨f, hf, -, ⟨e⟩⟩ | ⟨a, ha, -, ⟨e⟩⟩ | ⟨m, hm, -, -, ⟨e⟩⟩
    · exact exists_conj_of_fix_linear (.linear f hf e) hTs hT1 σ hfix
    · exact exists_conj_of_fix_suzuki (.suzuki a ha (e.trans (MulEquiv.subgroupCongr
        (szModel_eq_open_sz a).symm))) hTs hT1 σ hσ2 hfix
    · refine exists_conj_of_fix_dihedral hm e (isPGroup_of_strongWC hTs) hT1
        (isPGroup_of_strongWC QP.strongWC) QP.ne_bot σ hσ2 hfix ?_
      have hVle : (V.subgroupOf (U ⊔ V)).map
          (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V))) ≤
          ((U.subgroupOf (U ⊔ V)).map
            (QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)))).map
              σ.toMonoidHom := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨QuotientGroup.mk' _ (φ v), ⟨φ v, ?_, rfl⟩, ?_⟩
        · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hφa]
          have hv' : (v : G) ∈ conjSubgroup y U := by
            rw [hyV]
            exact Subgroup.mem_subgroupOf.mp hv
          rw [mem_conjSubgroup, hyinv] at hv'
          rw [hyinv]
          exact hv'
        · show σ (QuotientGroup.mk' _ (φ v)) = _
          rw [hσmk, hφφ]
      rw [eq_top_iff, ← QP.sup]
      exact sup_le_sup_left hVle _
  obtain ⟨_, ⟨c, hc, rfl⟩, hσt⟩ := hinner
  refine ⟨c, Subgroup.mem_subgroupOf.mp hc, fun z hz => ?_⟩
  have h2 : QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)) (c * ⟨z, hz⟩ * c⁻¹) =
      QuotientGroup.mk' ((nrm U V ⊔ nrm V U).subgroupOf (U ⊔ V)) (φ ⟨z, hz⟩) := by
    rw [← hσmk, hσt, map_mul, map_mul, map_inv]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, hNe] at h2
  exact h2

theorem commute_of_trivial_mod {x y : G} (hx : x ∈ U ⊔ V) (hne : conjSubgroup x U ≠ U)
    (hy : ∀ z ∈ U ⊔ V, y * z * y⁻¹ * z⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hyN : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V,
      y * n * y⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U))
    {n : G} (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) : y * n * y⁻¹ = n := by
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V with hNdef
  have hCc := Tim78.comm_conj P.setup.comm x
  have hyn : y * n * y⁻¹ ∈ N := by
    rw [show y * n * y⁻¹ = (y * n * y⁻¹ * n⁻¹) * n by group]
    exact N.mul_mem (hy n ((sup_le_sup (PartTwo.omegaOneSub_le U)
      (PartTwo.omegaOneSub_le V)) hn)) hn
  have hxn : x * n * x⁻¹ ∈ N := P.conj_mem_N hCen hU hx hn
  have hmx := hy x hx
  have hw : x * (y * n * y⁻¹) * x⁻¹ ∈ N := P.conj_mem_N hCen hU hx hyn
  have hc := P.comm_N hCen hU hmx hw
  have e : y * (x * n * x⁻¹) * y⁻¹ * (x * n * x⁻¹)⁻¹ = x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ := by
    calc y * (x * n * x⁻¹) * y⁻¹ * (x * n * x⁻¹)⁻¹
        = (y * x * y⁻¹ * x⁻¹) * (x * (y * n * y⁻¹) * x⁻¹) * (y * x * y⁻¹ * x⁻¹)⁻¹ *
            (x * n⁻¹ * x⁻¹) := by group
      _ = (x * (y * n * y⁻¹) * x⁻¹) * (y * x * y⁻¹ * x⁻¹) * (y * x * y⁻¹ * x⁻¹)⁻¹ *
            (x * n⁻¹ * x⁻¹) := by rw [hc]
      _ = x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ := by group
  have h1 := hyN _ hxn
  rw [e, omegaOneSub_conj P.setup.comm, mem_conjSubgroup,
    show x⁻¹ * (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹) * x = y * n * y⁻¹ * n⁻¹ by group] at h1
  have h2 := PartTwo.omegaOneSub_le _ (hyN n hn)
  have hUC : U ⊓ conjSubgroup x U = ⊥ := inf_conjSubgroup_eq_bot_of_isTI P.setup.ti hne
  have h3 : y * n * y⁻¹ * n⁻¹ ∈ U ⊓ conjSubgroup x U :=
    Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ h1, h2⟩
  rw [hUC, Subgroup.mem_bot] at h3
  calc y * n * y⁻¹ = (y * n * y⁻¹ * n⁻¹) * n := by group
    _ = n := by rw [h3, one_mul]

theorem conj_eq_of_trivial_mod {x y : G} (hx : x ∈ U ⊔ V)
    (hy : ∀ z ∈ U ⊔ V, y * z * y⁻¹ * z⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hyN : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V, y * n * y⁻¹ = n) :
    conjSubgroup y (conjSubgroup x U) = conjSubgroup x U := by
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V with hNdef
  have hCc := Tim78.comm_conj P.setup.comm x
  refine P.eq_of_le_sup_of_cent hCen hU ⟨y * x, (conjSubgroup_mul _ _ _).symm⟩ hx
    (fun m hm hmc => ?_) (fun d hd => ?_)
  ·
    have hym : y⁻¹ * m * y = m := by
      have := hyN m hm
      calc y⁻¹ * m * y = y⁻¹ * (y * m * y⁻¹) * y := by rw [this]
        _ = m := by group
    have hmC : m ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
      refine P.centN_conj hCen hU hx hm fun e he => ?_
      have hde : y * e * y⁻¹ ∈ conjSubgroup y (conjSubgroup x U) := by
        rw [mem_conjSubgroup, show y⁻¹ * (y * e * y⁻¹) * y = e by group]
        exact he
      have h1 := hmc _ hde
      have hym' : y * m * y⁻¹ = m := hyN m hm
      calc e * m = y⁻¹ * ((y * e * y⁻¹) * (y * m * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * e * y⁻¹) * m) * y := by rw [hym']
        _ = y⁻¹ * (m * (y * e * y⁻¹)) * y := by rw [h1]
        _ = (y⁻¹ * m * y) * e := by group
        _ = m * e := by rw [hym]
    rw [omegaOneSub_conj hCc, mem_conjSubgroup, hym]
    exact hmC
  ·
    have hd' := mem_conjSubgroup.mp hd
    have hdX : y⁻¹ * d * y ∈ U ⊔ V := by
      rw [show y⁻¹ * d * y = x * (x⁻¹ * (y⁻¹ * d * y) * x) * x⁻¹ by group]
      exact (U ⊔ V).mul_mem ((U ⊔ V).mul_mem hx (Subgroup.mem_sup_left
        (mem_conjSubgroup.mp hd'))) ((U ⊔ V).inv_mem hx)
    have h1 := hy _ hdX
    rw [show d = (y * (y⁻¹ * d * y) * y⁻¹ * (y⁻¹ * d * y)⁻¹) * (y⁻¹ * d * y) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hd')

end NCPair

end CFSG.RankThree.GF2n.Tim78
