module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape2
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedPointwise

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open CFSG.LieType.Ree CFSG.Blueprint
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_part1_core
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∃ P : Subgroup G, P ≤ str83X L1 L2 S ∧
      (str83X L1 L2 S ⊓ Subgroup.centralizer
        (CFSG.conjugate (str83X L1 L2 S) d.w : Set G)) = P ∧
      (∀ ⦃t : G⦄, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w → t ∉ Q1 L1 L2 S →
        str83X L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) = P) ∧
      (∀ ⦃t : G⦄, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w → t ∉ Q1 L1 L2 S →
        P = str83X1 L1 L2 S ⊔ ⁅str83X L1 L2 S, Subgroup.zpowers t⁆) ∧
      S ≤ Subgroup.normalizer (P : Set G) := by
  classical
  have hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83X1 L1 L2 S) (str83X L1 L2 S) :=
    str83G4_isChiefStep_x1_x hfr d hX hB
  have hnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83X1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) :=
    str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB
  let H : Subgroup G := L1 ⊔ S
  let X : Subgroup G := str83X L1 L2 S
  let X1 : Subgroup G := str83X1 L1 L2 S
  let W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w
  let K := GaloisField 2 (2 * a + 1)
  let q : ℕ := 2 ^ (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ1H : Q1 L1 L2 S ≤ H := hQ1S.trans le_sup_right
  have hSH : S ≤ H := le_sup_right
  have hWleS : W ≤ S := str83G4_conjugate_x_le_s hfr d hX
  have hWleH : W ≤ H := hWleS.trans hSH
  have hXleH : X ≤ H := (str83X_le_q1 hfr).trans hQ1S |>.trans le_sup_right
  have hWabel : IsElemAbelian 2 W := str83G4_isElemAbelian_conjugate_x d hX
  have hX1leX : X1 ≤ X := str83G4_x1_le_x L1 L2 S
  have hZ1X1 : Z1 L1 L2 S ≤ X1 := str83G4_z1_le_x1 hfr
  have hX1H : X1 ≤ H := hX1leX.trans hXleH
  have hHL : H ≤ Subgroup.normalizer (X1 : Set G) := by
    exact le_of_eq (rfl : H = L1 ⊔ S) |>.trans (D14.le_normalizer_of_isNormalIn
      (str83G4_x1_normal hfr))
  have hHN : H ≤ Subgroup.normalizer (X : Set G) := str83G4_sup_le_normalizer_x hfr
  obtain ⟨hHL', hHN', hNL', hE, hO, e, he, hnt⟩ :=
    str83G4_exists_sectionSetup hfr hstep hZ1X1 hnc
  letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod X1 X)) :=
    sectionRep hHL' hHN' hNL' hE hO e
  have hCmem : ∀ s : G, s ∈ W ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S :=
    str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB
  have hquad : ⁅⁅X, W⁆, W⁆ = ⊥ := by
    simpa [X, W] using str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX
  have hnat : IsSzNatural ρ :=
    sectionRep_isSzNatural_of_quadratic hfr hCmem hquad hstep hHL' hHN' hNL' hE hO e he hnt
  obtain ⟨c, φ, hφ⟩ := hnat
  let R : Submodule (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := fixedSub ρ (suzukiZ0 a K)
  have hRcard : Nat.card ↥R = q ^ 2 := by
    have h' : Nat.card ↥R = Nat.card K ^ 2 :=
      natCard_fixedSub_suzukiZ0 hK ρ ⟨c, φ, hφ⟩
    rw [h', hK]
  let Cbar : Subgroup (Ch3z.chiefMod X1 X) :=
    (AddSubgroup.toSubgroup' (R.toAddSubgroup) : Subgroup (Ch3z.chiefMod X1 X))
  let P0 : Subgroup ↥X := Cbar.comap (Ch3z.chiefIota hNL')
  let P : Subgroup G := P0.map X.subtype
  have hPleX : P ≤ X := Subgroup.map_subtype_le P0
  have hmemP : ∀ {x : G} (hx : x ∈ X), x ∈ P ↔
      Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hx⟩) ∈ R := by
    intro x hx
    have h1 : x ∈ P ↔ (⟨x, hx⟩ : ↥X) ∈ P0 := by
      constructor
      · intro hxP
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
        have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
        simpa [hyx'] using hy
      · intro hxP
        exact Subgroup.mem_map_of_mem X.subtype hxP
    have h2 : (⟨x, hx⟩ : ↥X) ∈ P0 ↔ Ch3z.chiefIota hNL' ⟨x, hx⟩ ∈ Cbar :=
      Iff.rfl
    have h3 : Ch3z.chiefIota hNL' ⟨x, hx⟩ ∈ Cbar ↔
        Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hx⟩) ∈ R := by
      change Ch3z.chiefIota hNL' ⟨x, hx⟩ ∈
        (AddSubgroup.toSubgroup' R.toAddSubgroup : Subgroup (Ch3z.chiefMod X1 X)) ↔ _
      exact AddSubgroup.mem_toSubgroup' R.toAddSubgroup _
    exact h1.trans (h2.trans h3)
  have hPrel : P.relIndex X = q ^ 2 := by
    have h1 : P.relIndex X = P0.relIndex ⊤ := by
      have h := Subgroup.relIndex_map_map_of_injective (f := X.subtype) P0 ⊤
      simpa [Subgroup.map_top, Subgroup.range_subtype] using h
    have h2 : P0.relIndex ⊤ = Cbar.relIndex ⊤ := by
      change (Cbar.comap (Ch3z.chiefIota hNL')).relIndex ⊤ = Cbar.relIndex ⊤
      rw [Subgroup.relIndex_comap Cbar (Ch3z.chiefIota hNL') ⊤, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (Ch3z.chiefIota_surjective hNL')]
    have hcard : Nat.card ↥Cbar = Nat.card ↥R :=
      Nat.card_congr
        { toFun := fun b => ⟨Additive.ofMul b.1,
            (AddSubgroup.mem_toSubgroup' R.toAddSubgroup b.1).mp b.2⟩
          invFun := fun r => ⟨Additive.toMul r.1,
            (AddSubgroup.mem_toSubgroup' R.toAddSubgroup (Additive.toMul r.1)).mpr (by
              simpa using r.2)⟩
          left_inv := fun b => Subtype.ext rfl
          right_inv := fun r => Subtype.ext rfl }
    have hcardC : Nat.card ↥Cbar = q ^ 2 := by
      rw [hcard]
      exact hRcard
    have hcardM : Nat.card (Ch3z.chiefMod X1 X) = q ^ 4 := by
      have h1 : Nat.card (Ch3z.chiefMod X1 X) =
          Nat.card (Additive (Ch3z.chiefMod X1 X)) :=
        (Nat.card_congr (Additive.toMul : Additive (Ch3z.chiefMod X1 X) ≃
          (Ch3z.chiefMod X1 X))).symm
      rw [h1, Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_fin, hK]
    have hcardMul : Nat.card ↥Cbar * Cbar.index = q ^ 2 * q ^ 2 := by
      calc Nat.card ↥Cbar * Cbar.index = Nat.card (Ch3z.chiefMod X1 X) :=
            Subgroup.card_mul_index Cbar
        _ = q ^ 4 := hcardM
        _ = q ^ 2 * q ^ 2 := by ring
    have hidx : Cbar.index = q ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q ^ 2)
      simpa [hcardC] using hcardMul
    have h3 : Cbar.relIndex ⊤ = Nat.card ↥R := by
      rw [Subgroup.relIndex_top_right, hidx, hRcard]
    rw [h1, h2, h3, hRcard]
  have hzdata : ∀ ⦃t : G⦄ (ht : t ∈ W), t ∉ Q1 L1 L2 S →
      ∃ z : ↥(suzukiGroup a K), z ∈ suzukiZ0 a K ∧ z ≠ 1 ∧
        z = e (QuotientGroup.mk ⟨t, hWleH ht⟩) := by
    intro t ht htQ
    have htS : t ∈ S := hWleS ht
    have htH : t ∈ H := hWleH ht
    have ht2 : t * t = 1 := by
      have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
      simpa [pow_two] using h
    have htSbar : QuotientGroup.mk' (pCore 2 ↥H) ⟨t, htH⟩ ∈ szSbar L1 L2 S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htS)
    let z : ↥(suzukiGroup a K) := e (QuotientGroup.mk ⟨t, htH⟩)
    have hzU : z ∈ suzukiU a K := by
      have hmem : z ∈ (szSbar L1 L2 S).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom htSbar
      rwa [he] at hmem
    have hzsq : z ^ 2 = 1 := by
      have h2 : (QuotientGroup.mk ⟨t, htH⟩ : oTwoQuot ↥H) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow]
        apply (QuotientGroup.eq_one_iff _).mpr
        have ht2H : (⟨t, htH⟩ : ↥H) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [pow_two] using ht2
        rw [ht2H]
        exact (pCore 2 ↥H).one_mem
      calc z ^ 2 = e ((QuotientGroup.mk ⟨t, htH⟩ : oTwoQuot ↥H) ^ 2) := by
            rw [map_pow]
        _ = 1 := by rw [h2, map_one]
    have hzZ0 : z ∈ suzukiZ0 a K := (mem_suzukiZ0_iff_sq_eq_one hK).2 ⟨hzU, hzsq⟩
    have hz1 : z ≠ 1 := by
      intro hz
      apply htQ
      have hq1 : (QuotientGroup.mk ⟨t, htH⟩ : oTwoQuot ↥H) = 1 :=
        e.injective (by simpa [z] using hz)
      have hmem : (⟨t, htH⟩ : ↥H) ∈ pCore 2 ↥H :=
        (QuotientGroup.eq_one_iff _).mp hq1
      rw [← str83G4_pCoreOf_sup_left hfr]
      exact (F1.mem_pCore_iff_coe _).mp hmem
    exact ⟨z, hzZ0, hz1, rfl⟩
  have hcentEq : ∀ ⦃t : G⦄, t ∈ W → t ∉ Q1 L1 L2 S →
      X ⊓ Subgroup.centralizer ({t} : Set G) = P := by
    intro t ht htQ
    obtain ⟨z, hzZ0, hz1, hzeq⟩ := hzdata ht htQ
    have htH : t ∈ H := hWleH ht
    have hrange : LinearMap.range (ρ z - 1) = R :=
      range_sub_one_eq_fixedSub_suzukiZ0 hK ρ ⟨c, φ, hφ⟩ hzZ0 hz1
    have hle : X ⊓ Subgroup.centralizer ({t} : Set G) ≤ P := by
      intro x hx
      have hxX : x ∈ X := hx.1
      have hxC : x ∈ Subgroup.centralizer ({t} : Set G) := hx.2
      have hcomm : t * x = x * t :=
        Subgroup.mem_centralizer_iff.mp hxC t (by simp)
      have hyeq : t * x * t⁻¹ = x := by
        rw [hcomm]
        group
      have hyX : t * x * t⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hHN htH) x).mp hxX
      have hsec := sectionRep_chiefIota hHL' hHN' hNL' hE hO e
        ⟨t, htH⟩ ⟨x, hxX⟩ hyX
      rw [show (⟨t * x * t⁻¹, hyX⟩ : ↥X) = ⟨x, hxX⟩ from Subtype.ext hyeq] at hsec
      have hvfix : ρ z (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) =
          Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩) := by
        rw [hzeq]
        simpa [ρ] using hsec
      have hfix : Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩) ∈
          fixedSub ρ (Subgroup.zpowers z) :=
        (mem_fixedSub_zpowers ρ z _).2 hvfix
      rw [fixedSub_zpowers_eq_fixedSub_suzukiZ0 hK ρ ⟨c, φ, hφ⟩ hzZ0 hz1] at hfix
      exact (hmemP hxX).mpr hfix
    have hrelC : (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex X = q ^ 2 := by
      rw [Subgroup.inf_relIndex_left]
      have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
          Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [← hcent]
      exact str83G4_relIndex_centralizer_x hfr d hX ht htQ
    have hmul := Subgroup.relIndex_mul_relIndex
      (X ⊓ Subgroup.centralizer ({t} : Set G)) P X hle hPleX
    have hqpos : 0 < q ^ 2 := by positivity
    have hone : (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex P = 1 := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      rw [one_mul]
      calc (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex P * q ^ 2
          = (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex P * P.relIndex X := by
              rw [hPrel]
        _ = (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex X := hmul
        _ = q ^ 2 := hrelC
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)
  have ht_ex : ∃ t : G, t ∈ W ∧ t ∉ Q1 L1 L2 S := by
    by_contra h
    apply hB
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  obtain ⟨t, ht, htQ⟩ := ht_ex
  have hWgen : W = Subgroup.closure ((W : Set G) \ (Q1 L1 L2 S : Set G)) := by
    refine le_antisymm ?_ ((Subgroup.closure_le W).mpr fun x hx => hx.1)
    intro w hw
    by_cases hwQ : w ∈ Q1 L1 L2 S
    · have h1W : w * t ∈ W := W.mul_mem hw ht
      have h1Q : w * t ∉ Q1 L1 L2 S := by
        intro h
        apply htQ
        have e : t = w⁻¹ * (w * t) := by group
        rw [e]
        exact (Q1 L1 L2 S).mul_mem ((Q1 L1 L2 S).inv_mem hwQ) h
      have h2W : t⁻¹ ∈ W := W.inv_mem ht
      have h2Q : t⁻¹ ∉ Q1 L1 L2 S := by
        intro h
        exact htQ (by simpa using (Q1 L1 L2 S).inv_mem h)
      rw [show w = (w * t) * t⁻¹ by group]
      exact (Subgroup.closure ((W : Set G) \ (Q1 L1 L2 S : Set G))).mul_mem
        (Subgroup.subset_closure (show w * t ∈ (W : Set G) \ (Q1 L1 L2 S : Set G) from
          ⟨h1W, h1Q⟩))
        (Subgroup.subset_closure (show t⁻¹ ∈ (W : Set G) \ (Q1 L1 L2 S : Set G) from
          ⟨h2W, h2Q⟩))
    · exact Subgroup.subset_closure ⟨hw, hwQ⟩
  have hPleCW : P ≤ Subgroup.centralizer (W : Set G) := by
    have hset : P ≤ Subgroup.centralizer ((W : Set G) \ (Q1 L1 L2 S : Set G)) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      rintro x ⟨hxW, hxQ⟩
      have hPleCx : P ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← hcentEq hxW hxQ]
        exact inf_le_right
      exact Subgroup.mem_centralizer_iff.mp (hPleCx hp) x (by simp)
    rw [hWgen, Subgroup.centralizer_closure]
    exact hset
  have hCW_eq : X ⊓ Subgroup.centralizer (W : Set G) = P := by
    refine le_antisymm ?_ (le_inf hPleX hPleCW)
    calc X ⊓ Subgroup.centralizer (W : Set G)
        ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
          refine inf_le_inf_left _ ?_
          intro y hy
          rw [Subgroup.mem_centralizer_iff] at hy ⊢
          intro z hz
          have hzt : z = t := by simpa using hz
          rw [hzt]
          exact hy t ht
      _ = P := hcentEq ht htQ
  have hU_NZ0 : suzukiU a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
    have hcent := (suzuki_unipotent_structure (a := a) (K := K) hK).2.2.2.2.2.1
    intro u hu
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      change u * z * u⁻¹ ∈ suzukiZ0 a K
      have h : u * z * u⁻¹ = z := by
        calc u * z * u⁻¹ = z * u * u⁻¹ := by rw [← hcent z hz u hu]
          _ = z := by group
      rw [h]
      exact hz
    · intro z hz
      refine ⟨u⁻¹ * z * u, ?_, ?_⟩
      · have h := hcent z hz u⁻¹ ((suzukiU a K).inv_mem hu)
        have hzu : u⁻¹ * z * u = z := by
          rw [← h]
          simp [mul_assoc]
        rw [hzu]
        exact hz
      · simp [MulAut.conj_apply, mul_assoc]
  have hconj_all : ∀ g ∈ S, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hxP
    have hgH : g ∈ H := hSH hg
    have hgU : e (QuotientGroup.mk ⟨g, hgH⟩) ∈ suzukiU a K := by
      have hgSbar : QuotientGroup.mk' (pCore 2 ↥H) ⟨g, hgH⟩ ∈ szSbar L1 L2 S :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)
      have hmem : e (QuotientGroup.mk ⟨g, hgH⟩) ∈ (szSbar L1 L2 S).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hgSbar
      rwa [he] at hmem
    have hgN : e (QuotientGroup.mk ⟨g, hgH⟩) ∈
        Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := hU_NZ0 hgU
    have hgNmap : Subgroup.map (MulAut.conj (e (QuotientGroup.mk ⟨g, hgH⟩))).toMonoidHom
        (suzukiZ0 a K) = suzukiZ0 a K := by
      have h := hgN
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    have hfixg : R = R.map (ρ (e (QuotientGroup.mk ⟨g, hgH⟩))) := by
      have h := fixedSub_map_conj ρ (e (QuotientGroup.mk ⟨g, hgH⟩)) (suzukiZ0 a K)
      rw [hgNmap] at h
      exact h
    have hxX : x ∈ X := hPleX hxP
    have hyX : g * x * g⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHN hgH) x).mp hxX
    have hvxR : Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩) ∈ R :=
      (hmemP hxX).mp hxP
    have hsec := sectionRep_chiefIota hHL' hHN' hNL' hE hO e
      ⟨g, hgH⟩ ⟨x, hxX⟩ hyX
    have hmapmem : ρ (e (QuotientGroup.mk ⟨g, hgH⟩))
        (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) ∈
        R.map (ρ (e (QuotientGroup.mk ⟨g, hgH⟩))) :=
      Submodule.mem_map_of_mem hvxR
    rw [← hfixg] at hmapmem
    apply (hmemP hyX).mpr
    rw [← hsec]
    exact hmapmem
  have hnormP : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxP
      exact hconj_all s hs x hxP
    · intro hxP
      have h := hconj_all s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) hxP
      simpa [mul_assoc] using h
  have hP_eq_sup_all : ∀ ⦃t : G⦄, t ∈ W → t ∉ Q1 L1 L2 S →
      P = X1 ⊔ ⁅X, Subgroup.zpowers t⁆ := by
    intro t ht htQ
    obtain ⟨z, hzZ0, hz1, hzeq⟩ := hzdata ht htQ
    have hrangeZ : LinearMap.range (ρ z - 1) = R :=
      range_sub_one_eq_fixedSub_suzukiZ0 hK ρ ⟨c, φ, hφ⟩ hzZ0 hz1
    have hgen_mem : ∀ ⦃x : G⦄, x ∈ X → ⁅x, t⁆ ∈ P := by
      intro x hxX
      have htH : t ∈ H := hWleH ht
      have hyX : t * x * t⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hHN htH) x).mp hxX
      have htx : t * x⁻¹ * t⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hHN htH) x⁻¹).mp (X.inv_mem hxX)
      have hcommX : ⁅x, t⁆ ∈ X := by
        have e : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact X.mul_mem hxX htx
      have hsec := sectionRep_chiefIota hHL' hHN' hNL' hE hO e
        ⟨t, htH⟩ ⟨x, hxX⟩ hyX
      have hvy : ρ z (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) =
          Additive.ofMul (Ch3z.chiefIota hNL' ⟨t * x * t⁻¹, hyX⟩) := by
        rw [hzeq]
        simpa [ρ] using hsec
      have hcomm_iota : Additive.ofMul (Ch3z.chiefIota hNL' ⟨⁅x, t⁆, hcommX⟩) =
          -(ρ z (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) -
            Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) := by
        have hd_eq : (⟨⁅x, t⁆, hcommX⟩ : ↥X) =
            ⟨x, hxX⟩ * ⟨t * x * t⁻¹, hyX⟩⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        calc Additive.ofMul (Ch3z.chiefIota hNL' ⟨⁅x, t⁆, hcommX⟩)
            = Additive.ofMul (Ch3z.chiefIota hNL' (⟨x, hxX⟩ *
                ⟨t * x * t⁻¹, hyX⟩⁻¹)) := by rw [hd_eq]
          _ = Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩) -
                Additive.ofMul (Ch3z.chiefIota hNL' ⟨t * x * t⁻¹, hyX⟩) := by
              apply Additive.toMul.injective
              simp [sub_eq_add_neg]
          _ = Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩) -
                ρ z (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) := by rw [hvy]
          _ = -(ρ z (Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) -
                Additive.ofMul (Ch3z.chiefIota hNL' ⟨x, hxX⟩)) := by abel
      have hmemR : Additive.ofMul (Ch3z.chiefIota hNL' ⟨⁅x, t⁆, hcommX⟩) ∈ R := by
        rw [hcomm_iota]
        refine R.neg_mem ?_
        rw [← hrangeZ]
        exact LinearMap.mem_range.mpr ⟨_, rfl⟩
      exact (hmemP hcommX).mpr hmemR
    have hX1P : X1 ≤ P := by
      intro x hx
      have hxX : x ∈ X := hX1leX hx
      apply (hmemP hxX).mpr
      have hxker : Ch3z.chiefIota hNL' ⟨x, hxX⟩ = 1 :=
        (Ch3z.chiefIota_eq_one_iff hNL' _).mpr hx
      rw [hxker]
      exact R.zero_mem
    have htNP : t ∈ Subgroup.normalizer (P : Set G) := hnormP (hWleS ht)
    have hDP : ⁅X, Subgroup.zpowers t⁆ ≤ P := by
      refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem htNP ?_
      intro x hx
      exact hgen_mem hx
    have hsup_le : X1 ⊔ ⁅X, Subgroup.zpowers t⁆ ≤ P := sup_le hX1P hDP
    have hP_le_sup : P ≤ X1 ⊔ ⁅X, Subgroup.zpowers t⁆ := by
      intro p hp
      have hpX : p ∈ X := hPleX hp
      have hvpR : Additive.ofMul (Ch3z.chiefIota hNL' ⟨p, hpX⟩) ∈ R :=
        (hmemP hpX).mp hp
      rw [← hrangeZ] at hvpR
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hvpR
      obtain ⟨x, hx_iota⟩ :=
        Ch3z.chiefIota_surjective hNL' (Additive.toMul u)
      have hxX : (x : G) ∈ X := x.2
      have hxu : Additive.ofMul (Ch3z.chiefIota hNL' x) = u := by
        apply Additive.toMul.injective
        simpa using hx_iota
      have hyX : t * (x : G) * t⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hHN (hWleH ht)) (x : G)).mp hxX
      have hsec := sectionRep_chiefIota hHL' hHN' hNL' hE hO e
        ⟨t, hWleH ht⟩ x hyX
      have hvy : ρ z u = Additive.ofMul
          (Ch3z.chiefIota hNL' ⟨t * (x : G) * t⁻¹, hyX⟩) := by
        rw [← hxu, hzeq]
        simpa [ρ] using hsec
      have htx : t * (x : G)⁻¹ * t⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hHN (hWleH ht)) (x : G)⁻¹).mp
          (X.inv_mem hxX)
      have hcommX : ⁅(x : G), t⁆ ∈ X := by
        have e : ⁅(x : G), t⁆ = (x : G) * (t * (x : G)⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact X.mul_mem hxX htx
      have hcomm_iota : Additive.ofMul
          (Ch3z.chiefIota hNL' ⟨⁅(x : G), t⁆, hcommX⟩) =
          -(ρ z u - u) := by
        have hd_eq : (⟨⁅(x : G), t⁆, hcommX⟩ : ↥X) =
            x * ⟨t * (x : G) * t⁻¹, hyX⟩⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        calc Additive.ofMul (Ch3z.chiefIota hNL' ⟨⁅(x : G), t⁆, hcommX⟩)
            = Additive.ofMul (Ch3z.chiefIota hNL' (x *
                ⟨t * (x : G) * t⁻¹, hyX⟩⁻¹)) := by rw [hd_eq]
          _ = Additive.ofMul (Ch3z.chiefIota hNL' x) -
                Additive.ofMul (Ch3z.chiefIota hNL'
                  ⟨t * (x : G) * t⁻¹, hyX⟩) := by
              apply Additive.toMul.injective
              simp [sub_eq_add_neg]
          _ = Additive.ofMul (Ch3z.chiefIota hNL' x) - ρ z u := by rw [hvy]
          _ = -(ρ z u - u) := by rw [hxu]; abel
      let dX : ↥X := ⟨⁅(x : G), t⁆, hcommX⟩
      have hdD : (dX : G) ∈ ⁅X, Subgroup.zpowers t⁆ := by
        exact Subgroup.commutator_mem_commutator hxX (Subgroup.mem_zpowers t)
      have hd_inv : Ch3z.chiefIota hNL' dX =
          (Ch3z.chiefIota hNL' ⟨p, hpX⟩)⁻¹ := by
        have hd_eq : Additive.ofMul (Ch3z.chiefIota hNL' dX⁻¹) =
            Additive.ofMul (Ch3z.chiefIota hNL' ⟨p, hpX⟩) := by
          rw [map_inv, ofMul_inv]
          change -Additive.ofMul (Ch3z.chiefIota hNL' dX) =
            Additive.ofMul (Ch3z.chiefIota hNL' ⟨p, hpX⟩)
          rw [show Additive.ofMul (Ch3z.chiefIota hNL' dX) = -(ρ z u - u) from
            hcomm_iota]
          rw [neg_neg]
          simpa using hu
        have h' := hd_eq
        apply Additive.toMul.injective at h'
        rw [map_inv] at h'
        calc Ch3z.chiefIota hNL' dX = ((Ch3z.chiefIota hNL' dX)⁻¹)⁻¹ :=
              (inv_inv _).symm
          _ = (Ch3z.chiefIota hNL' ⟨p, hpX⟩)⁻¹ := by rw [h']
      have hpdX : p * (dX : G) ∈ X := X.mul_mem hpX dX.2
      have hpdX1 : p * (dX : G) ∈ X1 := by
        refine (Ch3z.chiefIota_eq_one_iff hNL'
          ⟨p * (dX : G), hpdX⟩).mp ?_
        have hprod : (⟨p * (dX : G), hpdX⟩ : ↥X) = ⟨p, hpX⟩ * dX :=
          Subtype.ext rfl
        rw [hprod, map_mul, hd_inv, mul_inv_cancel]
      have hp_eq : p = (p * (dX : G)) * (dX : G)⁻¹ := by group
      rw [hp_eq]
      exact (X1 ⊔ ⁅X, Subgroup.zpowers t⁆).mul_mem
        (Subgroup.mem_sup_left hpdX1)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hdD))
    exact le_antisymm hP_le_sup hsup_le
  exact ⟨P, hPleX, hCW_eq, hcentEq, hP_eq_sup_all, hnormP⟩

theorem str83G4_x_inf_centralizer_eq_of_mem
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w) (htQ : t ∉ Q1 L1 L2 S) :
    str83X L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) =
      str83X L1 L2 S ⊓
        Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) := by
  obtain ⟨P, -, hCW, hcent, -, -⟩ := str83G4_part1_core hfr d hX hB
  rw [hcent ht htQ, hCW]

theorem str83G4_x_inf_centralizer_eq_x1_sup
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w) (htQ : t ∉ Q1 L1 L2 S) :
    str83X L1 L2 S ⊓
        Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X1 L1 L2 S ⊔ ⁅str83X L1 L2 S, Subgroup.zpowers t⁆ := by
  obtain ⟨P, -, hCW, -, hPsup, -⟩ := str83G4_part1_core hfr d hX hB
  rw [hCW, hPsup ht htQ]

theorem str83G4_conjugate_conjugate_x_eq
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) d.w = str83X L1 L2 S := by
  rw [CFSG.conjugate_conjugate]
  apply CFSG.conjugate_eq_self_of_mem_normalizer
  have hw2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  exact le_normalizer_str83X L1 L2 S
    ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) (hQ2S hw2)))

theorem str83G4_conjugate_z2_eq
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    CFSG.conjugate (Z2 L1 L2 S) d.w = Z2 L1 L2 S := by
  apply CFSG.conjugate_eq_self_of_mem_normalizer
  have hwP2 : d.w ∈ P2 L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
  exact SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hwP2

theorem str83G4_commutator_x_inf_conjugate_x_q2_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ⁅str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      Q2 L1 L2 S⁆ ≤ Z2 L1 L2 S := by
  classical
  let I : Subgroup G := str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w
  let A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
    exact (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  have hZ2w : CFSG.conjugate (Z2 L1 L2 S) d.w = Z2 L1 L2 S :=
    str83G4_conjugate_z2_eq hfr d
  have hIeq : CFSG.conjugate I d.w = I := by
    have hXw : CFSG.conjugate (str83X L1 L2 S) d.w =
        CFSG.conjugate (str83X L1 L2 S) d.w := rfl
    have hWw : CFSG.conjugate
        (CFSG.conjugate (str83X L1 L2 S) d.w) d.w = str83X L1 L2 S :=
      str83G4_conjugate_conjugate_x_eq hfr d
    rw [show I = str83X L1 L2 S ⊓
        CFSG.conjugate (str83X L1 L2 S) d.w from rfl, CFSG.conjugate,
      Subgroup.map_inf _ _ _ (MulAut.conj d.w⁻¹).injective]
    rw [show Subgroup.map (MulAut.conj d.w⁻¹).toMonoidHom (str83X L1 L2 S) =
        CFSG.conjugate (str83X L1 L2 S) d.w from rfl]
    rw [show Subgroup.map (MulAut.conj d.w⁻¹).toMonoidHom
        (CFSG.conjugate (str83X L1 L2 S) d.w) = str83X L1 L2 S from hWw]
    exact inf_comm _ _
  have hI_le_X : I ≤ str83X L1 L2 S := inf_le_left
  have hIA0Z1 : ⁅I, A0⁆ ≤ Z1 L1 L2 S := by
    refine (Subgroup.commutator_mono hI_le_X inf_le_left).trans ?_
    exact str83G4_commutator_x_q1_le hfr
  have hIA0 : ⁅I, A0⁆ ≤ Z2 L1 L2 S := hIA0Z1.trans hZ1Z2
  have hIA0w : ⁅I, CFSG.conjugate A0 d.w⁆ ≤ Z2 L1 L2 S := by
    have hconjcomm : CFSG.conjugate ⁅I, A0⁆ d.w = ⁅I, CFSG.conjugate A0 d.w⁆ := by
      simp only [CFSG.conjugate, Subgroup.map_commutator]
      rw [show Subgroup.map (MulAut.conj d.w⁻¹).toMonoidHom I = I from hIeq]
    have h' : CFSG.conjugate ⁅I, A0⁆ d.w ≤ CFSG.conjugate (Z1 L1 L2 S) d.w :=
      Subgroup.map_mono hIA0Z1
    have hZ1w : CFSG.conjugate (Z1 L1 L2 S) d.w ≤ Z2 L1 L2 S := by
      calc CFSG.conjugate (Z1 L1 L2 S) d.w ≤ CFSG.conjugate (Z2 L1 L2 S) d.w :=
            Subgroup.map_mono hZ1Z2
        _ = Z2 L1 L2 S := hZ2w
    rw [hconjcomm] at h'
    exact h'.trans hZ1w
  have hQ2NZ2 : Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (Subgroup.le_normalizer (H := Q2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hA0NZ2 : A0 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (inf_le_right : A0 ≤ Q2 L1 L2 S).trans hQ2NZ2
  have hA0wNZ2 : CFSG.conjugate A0 d.w ≤
      Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    have hA0wQ2 : CFSG.conjugate A0 d.w ≤ Q2 L1 L2 S := by
      calc CFSG.conjugate A0 d.w ≤ CFSG.conjugate (Q2 L1 L2 S) d.w :=
            Subgroup.map_mono inf_le_right
        _ = Q2 L1 L2 S := str83G4_conjugate_q2_eq d
    exact hA0wQ2.trans hQ2NZ2
  have hcomm := CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
    (Y := I) (A := A0) (B := CFSG.conjugate A0 d.w) (N := Z2 L1 L2 S)
    hA0NZ2 hA0wNZ2 hIA0 hIA0w
  have hq2 := str83G4_q2_eq_a0_sup_conjugate_a0 hfr d hX hB
  rw [hq2]
  exact hcomm

end CFSG.Quasithin.Stroth

end
