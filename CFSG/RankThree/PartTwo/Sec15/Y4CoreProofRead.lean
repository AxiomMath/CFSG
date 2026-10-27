module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Read148 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G) : Prop :=
  ∃ U V : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y),
    (U = ⊥ ∨ IsComponent U ∧ oPrimeResidual 3 ↥U = ⊤) ∧
    (V = ⊥ ∨ IsComponent V ∧ oPrimeResidual 3 ↥V = ⊤) ∧
    ((deltaZero A LB Y).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) ≤ U ⊔ V

@[expose] noncomputable def Read148R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY A, Read148 A (lB A) Y

namespace Y4Core

section Quot

variable {H : Type} [Group H] [Finite H]

theorem not_three_dvd_card_subgroupOf_pPrimeCore (L : Subgroup H) :
    ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 H).subgroupOf L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := CFSG.pPrimeCore 3 H with hR
  have hdvd : Nat.card (R.subgroupOf L) ∣ Nat.card R := by
    let f : R.subgroupOf L →* R :=
      { toFun := fun x => ⟨((x : ↥L) : H), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective f fun x y hxy => ?_
    have h := congrArg (fun z : R => (z : H)) hxy
    exact Subtype.ext (Subtype.ext h)
  exact fun h3 => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := H)) (h3.trans hdvd)

theorem subgroupOf_pPrimeCore_le_theta {L : Subgroup H} (hL : L ∈ thetaComponents 3 H)
    (hLR : ¬ L ≤ CFSG.pPrimeCore 3 H) :
    (CFSG.pPrimeCore 3 H).subgroupOf L ≤ aschbacherSolvableCore 3 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set R := CFSG.pPrimeCore 3 H with hR
  set N := R.subgroupOf L with hN
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hNn : N.Normal := Subgroup.normal_subgroupOf
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_subgroupOf_pPrimeCore L
  have hq : IsQuasisimple (↥L ⧸ θ) := hL.2.2
  have hNb : (N.map (QuotientGroup.mk' θ)).Normal := hNn.map _ (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNb with htop | hcen
  · exfalso
    have hsup : N ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hL3 : ¬ 3 ∣ Nat.card ↥L := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
        have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
        rw [Subgroup.mem_sup_of_normal_left] at hx
        obtain ⟨n, hn, t, ht, rfl⟩ := hx
        refine ⟨⟨t, ht⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply]
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      have h1 : Nat.card (↥L ⧸ N) ∣ Nat.card θ := Subgroup.card_dvd_of_surjective hsurj
      have h2 : Nat.card ↥L = Nat.card (↥L ⧸ N) * Nat.card N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      intro h3
      rw [h2] at h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · exact hθ.2.2.1 (h.trans h1)
      · exact hN3 h
    exact hLR (Sec4.le_pPrimeCore_of_isSubnormal hL.2.1 hL3)
  · have hKs : Group.IsSolvable ((Subgroup.center (↥L ⧸ θ)).comap (QuotientGroup.mk' θ)) :=
      isSolvable_comap_center θ hθ.1
    have hNK : N ≤ (Subgroup.center (↥L ⧸ θ)).comap (QuotientGroup.mk' θ) := fun x hx =>
      hcen (Subgroup.mem_map_of_mem _ hx)
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNK)
    exact hθ.2.2.2.1 N hNn hNs hN3

theorem theta_le_subgroupOf_pPrimeCore {L : Subgroup H} (hL : L ∈ thetaComponents 3 H) :
    aschbacherSolvableCore 3 ↥L ≤ (CFSG.pPrimeCore 3 H).subgroupOf L := by
  have hθH := solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have := hθH.2.1
  have hle : aschbacherSolvableCore 3 H ≤ CFSG.pPrimeCore 3 H :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθH.2.2.1⟩
  have h := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL.2.1
  intro x hx
  have hx' : (x : H) ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨x, hx, rfl⟩
  rw [h] at hx'
  exact Subgroup.mem_subgroupOf.mpr (hle hx'.2)

theorem subgroupOf_pPrimeCore_eq_theta {L : Subgroup H} (hL : L ∈ thetaComponents 3 H)
    (hLR : ¬ L ≤ CFSG.pPrimeCore 3 H) :
    (CFSG.pPrimeCore 3 H).subgroupOf L = aschbacherSolvableCore 3 ↥L :=
  le_antisymm (subgroupOf_pPrimeCore_le_theta hL hLR) (theta_le_subgroupOf_pPrimeCore hL)

omit [Finite H] in
theorem ker_mk'_comp_subtype (L : Subgroup H) :
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp L.subtype).ker =
      (CFSG.pPrimeCore 3 H).subgroupOf L := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem isComponent_map_mk' {L : Subgroup H} (hL : L ∈ thetaComponents 3 H)
    (hLR : ¬ L ≤ CFSG.pPrimeCore 3 H) :
    IsComponent (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H))) := by
  set f := (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp L.subtype with hf
  have hker : f.ker = aschbacherSolvableCore 3 ↥L :=
    (ker_mk'_comp_subtype L).trans (subgroupOf_pPrimeCore_eq_theta hL hLR)
  have hrange : f.range = L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H))) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hL.2.2,
    hL.2.1.map (QuotientGroup.mk'_surjective _)⟩

theorem eq_oPrimeResidualOf_of_map {L : Subgroup H} (hL : L ∈ thetaComponents 3 H)
    (hLR : ¬ L ≤ CFSG.pPrimeCore 3 H)
    (h3 : oPrimeResidual 3 ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H))) = ⊤) :
    L = oPrimeResidualOf 3 L := by
  set f := (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp L.subtype with hf
  have hθs : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hker : Group.IsSolvable ↥f.ker := by
    rw [ker_mk'_comp_subtype]
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (subgroupOf_pPrimeCore_le_theta hL hLR))
  have hrange : f.range = L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  refine Sec17.Proof171Steps.eq_oPrimeResidualOf_of_hom hL.1 f hker ?_
  rw [hrange]
  exact h3

end Quot

theorem eq_or_eq_of_le_sup {Q : Type*} [Group Q] [Finite Q] {C U V : Subgroup Q}
    (hC : IsComponent C) (hU : U = ⊥ ∨ IsComponent U) (hV : V = ⊥ ∨ IsComponent V)
    (hle : C ≤ U ⊔ V) : C = U ∨ C = V := by
  have hCU : C = U ∨ ⁅C, U⁆ = ⊥ := by
    rcases hU with rfl | hU
    · exact Or.inr (Subgroup.commutator_bot_right C)
    · exact CFSG.LocalCores.distinct_components_commute hC hU
  have hCV : C = V ∨ ⁅C, V⁆ = ⊥ := by
    rcases hV with rfl | hV
    · exact Or.inr (Subgroup.commutator_bot_right C)
    · exact CFSG.LocalCores.distinct_components_commute hC hV
  rcases hCU with h | hCU
  · exact Or.inl h
  rcases hCV with h | hCV
  · exact Or.inr h
  exfalso
  have hcent : C ≤ Subgroup.centralizer ((U ⊔ V : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCU))
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCV))
  obtain ⟨-, -, a, b, hab⟩ := hC.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hba : (b : Q) * a = a * b :=
    Subgroup.mem_centralizer_iff.mp (hcent a.2) b (hle b.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hba.symm

omit [Finite G] in
theorem oPrimeResidualOf_map_subtype {Y : Subgroup G} (L : Subgroup ↥Y) :
    oPrimeResidualOf 3 (L.map Y.subtype) = (oPrimeResidualOf 3 L).map Y.subtype := by
  rw [Sec14.oPrimeResidualOf_eq_closure, Sec14.oPrimeResidualOf_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, k, hk⟩
    exact ⟨y, ⟨hy, k, Subtype.ext (by simpa using hk)⟩, rfl⟩
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by simpa using congrArg Subtype.val hk⟩

theorem oPrimeResidualOf_le_deltaZero {A : Subgroup G} (hA : Late.IsE27 A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYΔ : Y = delta A (lB A) Y) :
    oPrimeResidualOf 3 Y ≤ deltaZero A (lB A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, -, h3⟩ := rank3II_14_5_lB hA hbot hAY
  set D := deltaZero A (lB A) Y with hDdef
  set C := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC
  have hCD : C ≤ Subgroup.normalizer (D : Set G) := by
    refine inf_le_right.trans ?_
    rw [hYΔ]
    exact h3
  have hC3 : Nat.Coprime 3 (Nat.card C) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  rw [Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  have hyY : y ∈ D ⊔ C := by
    rw [← h1, ← hYΔ]
    exact hy
  exact mem_of_mem_sup_of_pow_eq_one hCD hC3 hyY hk

omit [Finite G] in
theorem ne_bot_of_isComponent {Q : Type*} [Group Q] {C : Subgroup Q} (hC : IsComponent C) :
    C ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot C).mp (CFSG.LocalCores.isQuasisimple_nontrivial hC.1)

theorem y4CoreReadR_of_read148R (hSz : KFacts.KPSz)
    (hbot : Item145BotS14) (hR : Read148R) : Y4CoreReadR := by
  intro G _ _ A c L h Y hY hYΔ
  have hbot' := hbot G A c L h.toSec14Std
  obtain ⟨U, V, hU, hV, hD⟩ := hR G A c L h Y hY
  have hY4 : SectionFourHyp ↥Y := h.toTheoremFourHyp.sectionFourHyp hY.1
  set R := CFSG.pPrimeCore 3 ↥Y with hRdef
  set π := QuotientGroup.mk' R with hπ
  have hRmap : R.map Y.subtype = pPrimeCoreOf 3 Y := rfl
  have hlift : ∀ W : Subgroup (↥Y ⧸ R), (W = ⊥ ∨ IsComponent W ∧ oPrimeResidual 3 ↥W = ⊤) →
      ∃ J : Subgroup G, (J = ⊥ ∨ J ∈ comp3In Y) ∧ (J.subgroupOf Y).map π = W := by
    rintro W (rfl | ⟨hW, hW3⟩)
    · refine ⟨⊥, Or.inl rfl, ?_⟩
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    · obtain ⟨L', hL', hL'W⟩ := Sec4.exists_mem_thetaComponents_map_eq hSz hY4.kGroup
        (Sec4.localRank_theta_quotient_le hY4) hW
      have hL'W' : L'.map π = W := hL'W
      have hL'R : ¬ L' ≤ R := by
        intro hle
        apply ne_bot_of_isComponent hW
        rw [← hL'W', Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
        exact hle
      have hL'3 : L' = oPrimeResidualOf 3 L' :=
        eq_oPrimeResidualOf_of_map hL' hL'R (by rw [hL'W']; exact hW3)
      refine ⟨L'.map Y.subtype, Or.inr ⟨⟨L', hL', rfl⟩, ?_⟩, ?_⟩
      · rw [oPrimeResidualOf_map_subtype, ← hL'3]
      · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
        exact hL'W'
  obtain ⟨J₁, hJ₁, hJ₁U⟩ := hlift U hU
  obtain ⟨J₂, hJ₂, hJ₂V⟩ := hlift V hV
  have hJ₁Y : J₁ ≤ Y := by
    rcases hJ₁ with rfl | hJ
    · exact bot_le
    · exact le_of_mem_comp3In hJ
  have hJ₂Y : J₂ ≤ Y := by
    rcases hJ₂ with rfl | hJ
    · exact bot_le
    · exact le_of_mem_comp3In hJ
  have hcomp : ∀ J ∈ comp3In Y, IsComponent ((J.subgroupOf Y).map π) ∧
      (J.subgroupOf Y).map π ≤ U ⊔ V := by
    intro J hJ
    obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ.1
    have hJR : ¬ J.subgroupOf Y ≤ R := fun hle => not_le_pPrimeCoreOf hJ (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hJY]
      exact Subgroup.map_mono hle)
    refine ⟨isComponent_map_mk' hJ' hJR, le_trans (Subgroup.map_mono ?_) hD⟩
    refine Subgroup.subgroupOf_mono Y ?_
    calc J = oPrimeResidualOf 3 J := hJ.2
      _ ≤ oPrimeResidualOf 3 Y := oPrimeResidualOf_mono 3 hJY
      _ ≤ deltaZero A (lB A) Y :=
        oPrimeResidualOf_le_deltaZero h.toSec14Std.isE27 hbot' hY.2 hYΔ
  have huniq : ∀ J ∈ comp3In Y, ∀ J' ∈ comp3In Y,
      (J.subgroupOf Y).map π ≤ (J'.subgroupOf Y).map π → J = J' := by
    intro J hJ J' hJ' hle
    have hJY := le_of_mem_comp3In hJ
    have hJ'Y := le_of_mem_comp3In hJ'
    have h1 : J.subgroupOf Y ≤ J'.subgroupOf Y ⊔ R := by
      have := Subgroup.map_le_iff_le_comap.mp hle
      rwa [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at this
    have h2 : J ≤ J' ⊔ pPrimeCoreOf 3 Y := by
      have := Subgroup.map_mono (f := Y.subtype) h1
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJY,
        Subgroup.map_subgroupOf_eq_of_le hJ'Y, hRmap] at this
    have h3 : J ≤ J' := by
      rw [hJ.2, Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
      rintro y ⟨hy, k, hk⟩
      exact mem_of_mem_sup_of_pow_eq_one (pPrimeCoreOf_le_normalizer hJ')
        (coprime_card_pPrimeCoreOf 3 Y) (h2 (hJ.2 ▸ hy)) hk
    exact Sec6.eq_of_mem_thetaComponentsIn_of_le hJ.1 hJ'.1
      (isPerfect_of_mem_thetaComponentsIn hJ.1) (ne_bot hJ) le_rfl h3
  refine ⟨⟨J₁, J₂, fun J hJ => ?_⟩, ?_⟩
  · obtain ⟨hJc, hJle⟩ := hcomp J hJ
    rcases eq_or_eq_of_le_sup hJc (hU.imp_right (·.1)) (hV.imp_right (·.1)) hJle with h | h
    · left
      rcases hJ₁ with rfl | hJ₁c
      · exfalso
        rw [Subgroup.bot_subgroupOf, Subgroup.map_bot] at hJ₁U
        exact ne_bot_of_isComponent hJc (h.trans hJ₁U.symm)
      · exact huniq J hJ J₁ hJ₁c (h.trans hJ₁U.symm).le
    · right
      rcases hJ₂ with rfl | hJ₂c
      · exfalso
        rw [Subgroup.bot_subgroupOf, Subgroup.map_bot] at hJ₂V
        exact ne_bot_of_isComponent hJc (h.trans hJ₂V.symm)
      · exact huniq J hJ J₂ hJ₂c (h.trans hJ₂V.symm).le
  · intro d hd
    have hdY : d ∈ Y := deltaZero_le Y hd
    have hdD : π ⟨d, hdY⟩ ∈ U ⊔ V :=
      hD ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    rw [← hJ₁U, ← hJ₂V, ← Subgroup.map_sup] at hdD
    have hd' : (⟨d, hdY⟩ : ↥Y) ∈ (J₁.subgroupOf Y ⊔ J₂.subgroupOf Y) ⊔ R := by
      have h := Subgroup.comap_map_eq π (J₁.subgroupOf Y ⊔ J₂.subgroupOf Y)
      rw [hπ, QuotientGroup.ker_mk'] at h
      rw [← h]
      exact hdD
    have hmem : d ∈ ((J₁.subgroupOf Y ⊔ J₂.subgroupOf Y) ⊔ R).map Y.subtype :=
      ⟨⟨d, hdY⟩, hd', rfl⟩
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ₁Y,
      Subgroup.map_subgroupOf_eq_of_le hJ₂Y, hRmap] at hmem
    have hJ₁S : J₁ ≤ sSup (comp3In Y) := by
      rcases hJ₁ with rfl | hJ
      · exact bot_le
      · exact le_sSup hJ
    have hJ₂S : J₂ ≤ sSup (comp3In Y) := by
      rcases hJ₂ with rfl | hJ
      · exact bot_le
      · exact le_sSup hJ
    exact (sup_le_sup_right (sup_le hJ₁S hJ₂S) _) hmem

end Y4Core

end CFSG.RankThree.PartTwo.Sec15
