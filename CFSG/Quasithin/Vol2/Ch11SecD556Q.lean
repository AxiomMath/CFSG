module

public import CFSG.Quasithin.Vol2.Ch11SecD556H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_component {G₁ Y : Subgroup G} (hYG : Y ≤ G₁)
    (hYN : G₁ ≤ Subgroup.normalizer (Y : Set G)) {Q : Type} [Group Q]
    (θ : ↥Y →* Q) (hθ : ∀ y : ↥Y, θ y = 1 ↔ (y : G) ∈ pCoreOf 2 G₁) {I' : Subgroup ↥Y}
    (hI' : I' ∈ cComp (⊤ : Subgroup ↥Y)) (hq : CFSG.IsQuasisimple ↥(I'.map θ)) :
    CFSG.IsQuasisimple (↥(I'.map Y.subtype) ⧸ CFSG.pCore 2 ↥(I'.map Y.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := I'.map Y.subtype with hIdef
  have hIc : I ∈ cComp Y := map_subtype_mem_cComp hI'
  have hYG' : IsSubnormal Y G₁ := IsSubnormal.step hYG
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYG).mpr hYN) (IsSubnormal.refl G₁)
  have key : ∀ {A B : Subgroup G}, IsSubnormal A B → IsSubnormal B G₁ → IsSubnormal A G₁ := by
    intro A B hAB
    induction hAB with
    | refl => exact id
    | step hle hN _ ih => exact fun hB => IsSubnormal.step hle hN (ih hB)
  have hIG : IsSubnormal I G₁ := key hIc.2.2.1 hYG'
  have hOI : pCoreOf 2 I ≤ pCoreOf 2 G₁ := A4.pCoreOf_le_of_subnormal 2 hIG
  have hmemI : ∀ x : ↥I, (x : G) ∈ Y := fun x => by
    obtain ⟨y, -, hy⟩ := x.2
    rw [← hy]
    exact y.2
  let ψ : ↥I →* ↥(I'.map θ) :=
    { toFun := fun x => ⟨θ ⟨x, hmemI x⟩, by
        obtain ⟨y, hy, hyx⟩ := x.2
        refine ⟨y, hy, ?_⟩
        congr 1
        exact Subtype.ext hyx⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun x y => Subtype.ext (map_mul θ ⟨x, hmemI x⟩ ⟨y, hmemI y⟩) }
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, y, hy, rfl⟩
    refine ⟨⟨y, y, hy, rfl⟩, ?_⟩
    ext
    rfl
  have hker : ψ.ker = CFSG.pCore 2 ↥I := by
    apply le_antisymm
    · have hn : (ψ.ker).Normal := MonoidHom.normal_ker ψ
      refine le_sSup ⟨hn, fun x => ?_⟩
      have hx : ((x : ↥I) : G) ∈ pCoreOf 2 G₁ := by
        have h1 : ψ x = 1 := x.2
        have h2 : θ ⟨x, hmemI x⟩ = 1 := by
          have := congrArg Subtype.val h1
          simpa [ψ] using this
        exact (hθ _).mp h2
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁) ⟨_, hx⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    · intro x hx
      have hxO : ((x : ↥I) : G) ∈ pCoreOf 2 G₁ :=
        hOI ⟨x, by exact hx, rfl⟩
      show ψ x = 1
      apply Subtype.ext
      show θ ⟨x, hmemI x⟩ = 1
      exact (hθ _).mpr hxO
  have e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(I'.map θ) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  refine CFSG.LocalCores.isQuasisimple_of_surjective hq e.symm.toMonoidHom e.symm.surjective ?_
  intro z hz
  have h1 : e.symm z = 1 := hz
  have h2 : z = 1 := by simpa using congrArg e h1
  rw [h2]
  exact Subgroup.one_mem _

theorem commutator_le_pCoreOf_of_components {G₁ Y P X : Subgroup G}
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ G₁ → IsElemAbelian p E →
      ∀ r, Nat.card E = p ^ r → r ≤ 2)
    (hYG : Y ≤ G₁) (hYN : G₁ ≤ Subgroup.normalizer (Y : Set G))
    (hXG : X ≤ G₁) (hXodd : Odd (Nat.card X))
    (hPG : P ≤ G₁) (hP2 : IsPGroup 2 P) (hPX : ⁅P, X⁆ = P)
    (hΦ : (frattini ↥P).map P.subtype ≤ pCoreOf 2 G₁)
    (hPL : ∀ I ∈ cComp Y, CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) → ⁅P, I⁆ ≤ pCoreOf 2 G₁) :
    ⁅P, Y⁆ ≤ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ g : ↥G₁, π g = 1 ↔ (g : G) ∈ pCoreOf 2 G₁ := fun g => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf,
      Subgroup.mem_subgroupOf]
  have hO2 := pCore_two_quotient_eq_bot ↥G₁
  have hY'n : (Y.subgroupOf G₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYG).mpr hYN
  set Ŷ := (Y.subgroupOf G₁).map π with hŶdef
  have hŶn : Ŷ.Normal := hY'n.map π hπs
  have hO2Y : CFSG.pCore 2 ↥Ŷ = ⊥ := by
    have hc : (CFSG.pCore 2 ↥Ŷ).Characteristic := pCore_characteristic' 2 ↥Ŷ
    have hle := (CFSG.LieType.BorelTits.le_pCore 2 (normal_map_of_characteristic hŶn hc)
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥Ŷ)).map Ŷ.subtype)).trans_eq
        (SecA.open_pCore_eq 2 _)
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Ŷ.subtype_injective] at hle
    exact hle
  set Ph := (P.subgroupOf G₁).map π with hPhdef
  set Xh := (X.subgroupOf G₁).map π with hXhdef
  have hXhodd : Odd (Nat.card Xh) := by
    have h1 : Nat.card Xh ∣ Nat.card ↥(X.subgroupOf G₁) := Subgroup.card_map_dvd _ π
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv] at h1
    exact Odd.of_dvd_nat hXodd h1
  have hPh2 : IsPGroup 2 Ph := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm).map π
  have hPhX : ⁅Ph, Xh⁆ = Ph := by
    rw [hPhdef, hXhdef, ← Subgroup.map_commutator, commutator_subgroupOf hPG hXG, hPX]
  have hΦ' : frattiniIn Ph = ⊥ :=
    C2Nine.frattiniIn_eq_bot_of_isElemAbelian (isElemAbelian_map_of_frattini hP2 hΦ)
  have hA := a126_one (H := ⊤) (X := Xh) (V := Ph) le_top (opResidual_eq_self_of_odd hXhodd)
    le_top hPh2 hPhX (fun p hp hp2 => csSup_le' fun r hr => by
      obtain ⟨E, -, hE, hEc⟩ := hr
      exact le_two_of_elemAbelian_quotient hp hp2 (hrank p hp hp2) hE hEc) hΦ'
  have hFle : (CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype ≤
      fusionOddCoreOf (⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)) := by
    have hNn := normal_map_of_characteristic hŶn
      (CFSG.fittingSubgroup_characteristic (G := ↥Ŷ))
    have hNnil : Group.IsNilpotent ↥((CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype) :=
      Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ Ŷ.subtype_injective)
    have hNodd := odd_card_of_isNilpotent_of_normal hO2 hNn hNnil
    intro z hz
    refine ⟨⟨z, trivial⟩, ?_, rfl⟩
    refine le_sSup (s := {M : Subgroup ↥(⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)) |
      M.Normal ∧ Odd (Nat.card M)})
      (a := ((CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype).subgroupOf ⊤) ⟨hNn.subgroupOf _, ?_⟩ hz
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv]
    exact hNodd
  rw [Subgroup.commutator_le]
  intro p hp y hy
  have hpPh : π ⟨p, hPG hp⟩ ∈ Ph := ⟨⟨p, hPG hp⟩, hp, rfl⟩
  let φ : MulAut ↥Ŷ := MulAut.conjNormal (π ⟨p, hPG hp⟩)
  have hφ_apply : ∀ z : ↥Ŷ, ((φ z : ↥Ŷ) : ↥G₁ ⧸ CFSG.pCore 2 ↥G₁) =
      π ⟨p, hPG hp⟩ * z * (π ⟨p, hPG hp⟩)⁻¹ := fun z => MulAut.conjNormal_apply _ _
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hφk : φ ^ 2 ^ k = 1 := by
    have h1 : (π ⟨p, hPG hp⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨p, hPG hp⟩ : ↥G₁) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    change (MulAut.conjNormal (π ⟨p, hPG hp⟩)) ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hcomm : ∀ z ∈ fusionOddCoreOf (⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)),
      π ⟨p, hPG hp⟩ * z * (π ⟨p, hPG hp⟩)⁻¹ = z := fun z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp (hA hpPh) z hz).symm, mul_inv_cancel_right]
  have hfixF : CFSG.fittingSubgroup ↥Ŷ ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) :=
    fun z hz => by
      show φ z = z
      exact Subtype.ext ((hφ_apply z).trans (hcomm _ (hFle ⟨z, hz, rfl⟩)))
  have hfixE : CFSG.layer ↥Ŷ ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) := by
    let θ : ↥Y →* ↥Ŷ := (π.comp (Subgroup.inclusion hYG)).codRestrict Ŷ
      (fun y => ⟨Subgroup.inclusion hYG y, y.2, rfl⟩)
    have hθ : Function.Surjective θ := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hθ1 : ∀ y : ↥Y, θ y = 1 ↔ (y : G) ∈ pCoreOf 2 G₁ := fun y =>
      Subtype.ext_iff.trans (hker (Subgroup.inclusion hYG y))
    have hθk : Group.IsSolvable θ.ker := by
      have hp : IsPGroup 2 θ.ker := fun x => by
        have hx : ((x : ↥Y) : G) ∈ pCoreOf 2 G₁ := (hθ1 x).mp x.2
        obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁) ⟨_, hx⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      have : Group.IsNilpotent θ.ker := hp.isNilpotent
      infer_instance
    simp only [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    have hKc : K ∈ cComp (⊤ : Subgroup ↥Ŷ) := mem_cComp_top_of_isComponent hK
    obtain ⟨I', hI', rfl⟩ := (cComp_map_bijOn θ hθ hθk).surjOn hKc
    have hq := isQuasisimple_of_component hYG hYN θ hθ1 hI' hK.1
    have hPI := hPL _ (map_subtype_mem_cComp hI') hq
    rintro _ ⟨w, hw, rfl⟩
    show φ (θ w) = θ w
    refine Subtype.ext ((hφ_apply (θ w)).trans ?_)
    have hc : p * w * p⁻¹ * (w : G)⁻¹ ∈ pCoreOf 2 G₁ := by
      have := Subgroup.commutator_le.mp hPI p hp w ⟨w, hw, rfl⟩
      rwa [commutatorElement_def] at this
    have h1 : π (⟨p, hPG hp⟩ * ⟨w, hYG w.2⟩ * (⟨p, hPG hp⟩ : ↥G₁)⁻¹ * (⟨w, hYG w.2⟩ : ↥G₁)⁻¹) = 1 :=
      (hker _).mpr hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hfix : ∀ z ∈ CFSG.generalizedFitting ↥Ŷ, φ z = z := fun z hz =>
    (sup_le hfixF hfixE : CFSG.generalizedFitting ↥Ŷ ≤ _) hz
  have hφ1 := mulAut_eq_one_of_fixes_generalizedFitting hO2Y φ hφk hfix
  have hyŶ : π ⟨y, hYG hy⟩ ∈ Ŷ := ⟨⟨y, hYG hy⟩, hy, rfl⟩
  have h2 : π ⟨p, hPG hp⟩ * π ⟨y, hYG hy⟩ * (π ⟨p, hPG hp⟩)⁻¹ = π ⟨y, hYG hy⟩ := by
    rw [← hφ_apply ⟨_, hyŶ⟩, hφ1]
    rfl
  have h3 : π (⟨p, hPG hp⟩ * ⟨y, hYG hy⟩ * (⟨p, hPG hp⟩ : ↥G₁)⁻¹ *
      (⟨y, hYG hy⟩ : ↥G₁)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2, mul_inv_cancel]
  rw [commutatorElement_def]
  exact (hker _).mp h3

end CFSG.Quasithin.Vol2.Ch11.SecD
