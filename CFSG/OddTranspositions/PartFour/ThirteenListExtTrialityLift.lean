module

public import CFSG.OddTranspositions.PartFour.ThirteenList
public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityDefs
public import CFSG.Timmesfeld.Bridge.Asc72YCount

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

section SevenNine

variable {Y Y' : Type} [Group Y] [Group Y'] {D : Set Y} {D' : Set Y'}

theorem isReflModel_of_mulEquiv {p m : ℕ} {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
    (h : IsReflModel p m f Y D) (φ : Y' ≃* Y) (hD : ∀ d ∈ D', φ d ∈ D) :
    IsReflModel p m f Y' D' := by
  obtain ⟨e, he⟩ := h
  exact ⟨φ.trans e, fun d hd => he _ (hD d hd)⟩

theorem isReflQuotModel_of_mulEquiv {p m : ℕ}
    {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
    (h : IsReflQuotModel p m f Y D) (φ : Y' ≃* Y) (hD : ∀ d ∈ D', φ d ∈ D) :
    IsReflQuotModel p m f Y' D' := by
  obtain ⟨e, he⟩ := h
  exact ⟨φ.trans e, fun d hd => he _ (hD d hd)⟩

theorem isSevenNineGroup_of_mulEquiv (h : IsSevenNineGroup Y D) (φ : Y' ≃* Y)
    (hD : ∀ d ∈ D', φ d ∈ D) : IsSevenNineGroup Y' D' := by
  rcases h with ⟨f, hs, hnd, hw, hM⟩ | ⟨f, hs, hnd, hM | hM⟩
  · exact Or.inl ⟨f, hs, hnd, hw, isReflModel_of_mulEquiv hM φ hD⟩
  · exact Or.inr ⟨f, hs, hnd, Or.inl (isReflModel_of_mulEquiv hM φ hD)⟩
  · exact Or.inr ⟨f, hs, hnd, Or.inr (isReflQuotModel_of_mulEquiv hM φ hD)⟩

end SevenNine

theorem oddTranspListAlt_of_sevenNine_le {X : Type} [Group X] {s : X} {Y₀ : Subgroup X}
    (hs : s ∈ Y₀) (h : ∃ L : Subgroup ↥Y₀, ⟨s, hs⟩ ∈ L ∧
      IsSevenNineGroup ↥L {x : ↥L | (x : ↥Y₀) ∈ Subgroup.zpowers ⟨s, hs⟩ ∧ x ≠ 1}) :
    OddTranspListAlt X s := by
  obtain ⟨L, hsL, h79⟩ := h
  set φ : ↥(L.map Y₀.subtype) ≃* ↥L :=
    (L.equivMapOfInjective Y₀.subtype Y₀.subtype_injective).symm
  have hφ : ∀ x : ↥(L.map Y₀.subtype), (((φ x : ↥L) : ↥Y₀) : X) = (x : X) := by
    intro x
    have h' := Subgroup.coe_equivMapOfInjective_apply L Y₀.subtype Y₀.subtype_injective (φ x)
    rw [show L.equivMapOfInjective Y₀.subtype Y₀.subtype_injective (φ x) = x from
      MulEquiv.apply_symm_apply _ x] at h'
    exact h'.symm
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨L.map Y₀.subtype, ⟨⟨s, hs⟩, hsL, rfl⟩,
    isSevenNineGroup_of_mulEquiv h79 φ fun d hd => ⟨?_, ?_⟩⟩)))
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd.1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hφ d]
    exact hk
  · intro h1
    exact hd.2 (φ.injective (h1.trans φ.map_one.symm))

variable {X : Type} [Group X]

@[expose] def extLift (M : Subgroup (X ⧸ Subgroup.center X)) (s : X) : Subgroup X :=
  Subgroup.closure
    {x : X | ∃ m ∈ M.comap (QuotientGroup.mk' (Subgroup.center X)), x = m * s * m⁻¹}

theorem mem_extLift_self (M : Subgroup (X ⧸ Subgroup.center X)) (s : X) : s ∈ extLift M s :=
  Subgroup.subset_closure ⟨1, M.one_mem, by group⟩

theorem image_extLift_gens (M : Subgroup (X ⧸ Subgroup.center X)) (s : X) :
    (QuotientGroup.mk' (Subgroup.center X)) ''
        {x : X | ∃ m ∈ M.comap (QuotientGroup.mk' (Subgroup.center X)), x = m * s * m⁻¹} =
      Subtype.val '' Asc72.conjSet M (QuotientGroup.mk s) := by
  ext k
  constructor
  · rintro ⟨x, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨⟨QuotientGroup.mk' (Subgroup.center X) (m * s * m⁻¹), ?_⟩, ⟨_, hm, ?_⟩, rfl⟩
    · rw [map_mul, map_mul, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hm))
    · simp only [map_mul, map_inv]
      rfl
  · rintro ⟨k, ⟨m, hm, hk⟩, rfl⟩
    obtain ⟨m', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) m
    refine ⟨m' * s * m'⁻¹, ⟨m', hm, rfl⟩, ?_⟩
    rw [hk, map_mul, map_mul, map_inv]
    rfl

theorem map_extLift {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    (extLift M s).map (QuotientGroup.mk' (Subgroup.center X)) =
      M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X) := by
  rw [extLift, MonoidHom.map_closure, image_extLift_gens]
  have h := congrArg (Subgroup.map (M ⊔ Subgroup.zpowers
    (QuotientGroup.mk s : X ⧸ Subgroup.center X)).subtype) hgen
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

@[expose] noncomputable def extLiftHom {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    ↥(extLift M s) →* ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) :=
  ((QuotientGroup.mk' (Subgroup.center X)).comp (extLift M s).subtype).codRestrict _ fun y => by
    rw [← map_extLift hgen]
    exact ⟨y, y.2, rfl⟩

theorem extLiftHom_apply {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) (y : ↥(extLift M s)) :
    (extLiftHom hgen y : X ⧸ Subgroup.center X) = QuotientGroup.mk (y : X) :=
  rfl

theorem extLiftHom_surjective {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    Function.Surjective (extLiftHom hgen) := by
  rintro ⟨k, hk⟩
  rw [← map_extLift hgen] at hk
  obtain ⟨y, hy, rfl⟩ := hk
  exact ⟨⟨y, hy⟩, rfl⟩

theorem ker_extLiftHom {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    (extLiftHom hgen).ker = (Subgroup.center X).comap (extLift M s).subtype := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype, ← QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem center_extLift_eq_comap {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    Subgroup.center ↥(extLift M s) = (Subgroup.center X).comap (extLift M s).subtype := by
  apply le_antisymm
  · intro z hz
    rw [← ker_extLiftHom hgen, MonoidHom.mem_ker]
    have hmem : (extLiftHom hgen z : X ⧸ Subgroup.center X) ∈
        Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hmY : m ∈ M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X) :=
        Subgroup.mem_sup_left hm
      obtain ⟨y, hy⟩ := extLiftHom_surjective hgen ⟨m, hmY⟩
      have hc := Subgroup.mem_center_iff.mp hz y
      have h' := congrArg (fun w => (extLiftHom hgen w : X ⧸ Subgroup.center X)) hc
      simp only [map_mul, Subgroup.coe_mul, hy] at h'
      exact h'
    rw [hcent, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro z hz
    rw [Subgroup.mem_comap] at hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (y : X))

theorem ker_extLiftHom_eq_center {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    (extLiftHom hgen).ker = Subgroup.center ↥(extLift M s) :=
  (ker_extLiftHom hgen).trans (center_extLift_eq_comap hcent hgen).symm

@[expose] noncomputable def extLiftEquiv {M : Subgroup (X ⧸ Subgroup.center X)} {s : X}
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    ↥(extLift M s) ⧸ Subgroup.center ↥(extLift M s) ≃*
      ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_extLiftHom_eq_center hcent hgen).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (extLiftHom_surjective hgen))

section Hyps

variable [Finite X] {s : X} {M : Subgroup (X ⧸ Subgroup.center X)}

omit [Finite X] in
theorem isOddTransp_extLift (hodd : Asc72.IsOddTransp {x : X | IsConj s x}) :
    Asc72.IsOddTransp {y : ↥(extLift M s) | IsConj ⟨s, mem_extLift_self M s⟩ y} := by
  refine ⟨fun d hd => ?_, fun d hd e he => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hodd.1 _ (MonoidHom.map_isConj (extLift M s).subtype hd)
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hodd.2 _ (MonoidHom.map_isConj (extLift M s).subtype hd) _
      (MonoidHom.map_isConj (extLift M s).subtype he)

omit [Finite X] in
theorem normalClosure_extLift (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤) :
    Subgroup.normalClosure ({⟨s, mem_extLift_self M s⟩} : Set ↥(extLift M s)) = ⊤ := by
  set N := Subgroup.normalClosure ({⟨s, mem_extLift_self M s⟩} : Set ↥(extLift M s))
  have hle : extLift M s ≤ N.map (extLift M s).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨m, hm, rfl⟩
    have hmY : QuotientGroup.mk' (Subgroup.center X) m ∈
        M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X) :=
      Subgroup.mem_sup_left hm
    obtain ⟨y, hy⟩ := extLiftHom_surjective hgen ⟨_, hmY⟩
    have hyz : (y : X)⁻¹ * m ∈ Subgroup.center X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h' := congrArg Subtype.val hy
      rw [extLiftHom_apply] at h'
      rw [h']
      exact inv_mul_cancel _
    have he : m * s * m⁻¹ = (y : X) * s * (y : X)⁻¹ := by
      set z := (y : X)⁻¹ * m with hz
      have hm' : m = (y : X) * z := by rw [hz]; group
      have hzs : z * s = s * z := (Subgroup.mem_center_iff.mp hyz s).symm
      rw [hm', mul_inv_rev, mul_assoc (y : X) z s, hzs]
      group
    refine ⟨y * ⟨s, mem_extLift_self M s⟩ * y⁻¹, ?_, ?_⟩
    · exact (Subgroup.normalClosure_normal).conj_mem _
        (Subgroup.subset_normalClosure (Set.mem_singleton _)) y
    · rw [he]
      rfl
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hle y.2
  rw [show y = z from Subtype.ext hzy.symm]
  exact hz

theorem eq_bot_of_isPGroup_le_center_extLift (hO2 : CFSG.pCore 2 X = ⊥)
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤)
    {K : Subgroup ↥(extLift M s)} (hK : IsPGroup 2 K) (hKZ : K ≤ Subgroup.center ↥(extLift M s)) :
    K = ⊥ := by
  rw [center_extLift_eq_comap hcent hgen] at hKZ
  have hodd : Odd (Nat.card K) :=
    Odd.of_dvd_nat (CentralQuot.odd_card_center hO2)
      ((Subgroup.card_dvd_of_le hKZ).trans
        (Subgroup.card_comap_dvd_of_injective _ _ (extLift M s).subtype_injective))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
  rcases n with _ | n
  · exact Subgroup.card_eq_one.mp (by rw [hn, pow_zero])
  · rw [hn, pow_succ] at hodd
    exact absurd (Nat.odd_mul.mp hodd).2 (by decide)

theorem pCore_extLift (hO2 : CFSG.pCore 2 X = ⊥)
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤)
    (hO2Y : CFSG.pCore 2 ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) =
      ⊥) :
    CFSG.pCore 2 ↥(extLift M s) = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun K hK => le_bot_iff.mpr ?_)
  obtain ⟨hKn, hK2⟩ := hK
  have hmap : K.map (extLiftHom hgen) ≤ CFSG.pCore 2
      ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) :=
    le_sSup ⟨hKn.map _ (extLiftHom_surjective hgen), hK2.map _⟩
  rw [hO2Y, le_bot_iff, Subgroup.map_eq_bot_iff, ker_extLiftHom_eq_center hcent hgen] at hmap
  exact eq_bot_of_isPGroup_le_center_extLift hO2 hcent hgen hK2 hmap

theorem fusionOddCore_extLift (hO2 : CFSG.pCore 2 X = ⊥)
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : Subgroup.closure (Asc72.conjSet M (QuotientGroup.mk s)) = ⊤)
    (hOY : fusionOddCore ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) =
      ⊥) :
    fusionOddCore ↥(extLift M s) = Subgroup.center ↥(extLift M s) := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hNodd⟩ := hN
    have hmap : N.map (extLiftHom hgen) ≤ fusionOddCore
        ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X)) :=
      le_sSup ⟨hNn.map _ (extLiftHom_surjective hgen),
        Odd.of_dvd_nat hNodd (Subgroup.card_map_dvd _ _)⟩
    rw [hOY, le_bot_iff, Subgroup.map_eq_bot_iff, ker_extLiftHom_eq_center hcent hgen] at hmap
    exact hmap
  · refine le_sSup ⟨inferInstance, ?_⟩
    rw [center_extLift_eq_comap hcent hgen]
    exact Odd.of_dvd_nat (CentralQuot.odd_card_center hO2)
      (Subgroup.card_comap_dvd_of_injective _ _ (extLift M s).subtype_injective)

end Hyps

section List

variable [Finite X] {s : X} {M : Subgroup (X ⧸ Subgroup.center X)} [M.Normal]

theorem extLiftData_extLift (hord : orderOf s = 2)
    (hodd : Asc72.IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hO2 : CFSG.pCore 2 X = ⊥) (hOZ : fusionOddCore X ≤ Subgroup.center X)
    (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hcls : Asc72.IsOddTranspClass (Asc72.conjSet M (QuotientGroup.mk s))) :
    ExtLiftData (X ⧸ Subgroup.center X) (QuotientGroup.mk s) M ↥(extLift M s)
      ⟨s, mem_extLift_self M s⟩ := by
  have hS := setup_quotient_center hodd hncl hO2
  have hrad := eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ
  obtain ⟨-, -, -, hO2Y, hOY, -, -⟩ :=
    sup_zpowers_hyps hS hrad hM hMs hcent (IsConj.refl _) hcls
  have hgen := hcls.2.2
  refine ⟨?_, isOddTransp_extLift hodd, normalClosure_extLift hgen,
    pCore_extLift hO2 hcent hgen hO2Y, fusionOddCore_extLift hO2 hcent hgen hOY,
    ⟨extLiftEquiv hcent hgen, rfl⟩⟩
  rw [Subgroup.orderOf_mk]
  exact hord

theorem oddTranspListAlt_extLift (hD : OddTranspositionListInputClsDerivedEq)
    (hord : orderOf s = 2)
    (hodd : Asc72.IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hO2 : CFSG.pCore 2 X = ⊥) (hOZ : fusionOddCore X ≤ Subgroup.center X)
    (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hcent : Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥)
    (hcls : Asc72.IsOddTranspClass (Asc72.conjSet M (QuotientGroup.mk s))) :
    OddTranspListAlt ↥(extLift M s) ⟨s, mem_extLift_self M s⟩ := by
  have hS := setup_quotient_center hodd hncl hO2
  have hrad := eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ
  obtain ⟨-, -, -, -, -, -, hder⟩ :=
    sup_zpowers_hyps hS hrad hM hMs hcent (IsConj.refl _) hcls
  have hL := extLiftData_extLift hord hodd hncl hO2 hOZ hM hMs hcent hcls
  set e := extLiftEquiv hcent hcls.2.2
  refine hD _ _ hL.order hL.oddT hL.gen hL.pCore hL.oddCore.le ?_
  rw [← map_derivedSeries_eq (f := e.symm.toMonoidHom) e.symm.surjective 1,
    ← map_derivedSeries_eq (f := e.symm.toMonoidHom) e.symm.surjective 2, hder]

end List

end CFSG.OddTranspositions.PartFour
