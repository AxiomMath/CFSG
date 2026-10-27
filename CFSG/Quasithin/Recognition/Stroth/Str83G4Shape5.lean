module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape4
public import CFSG.Quasithin.Recognition.Stroth.Str83G4VNatCard
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedPointwise

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.GH74.Uniqueness.Bender
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

private theorem mem_fixedSub_sectionRep_iff
    {L1 L2 S : Subgroup G} {a : ℕ} {H X X1 : Subgroup G}
    {e : oTwoQuot ↥H ≃* suzukiGroup a (GaloisField 2 (2 * a + 1))}
    (hSH : S ≤ H)
    (hHL : H ≤ Subgroup.normalizer (X1 : Set G))
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hNL : X ≤ Subgroup.normalizer (X1 : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod X1 X))
    (hO : pCoreOf 2 H ≤ centralizerMod X1 H X)
    (he : ((S.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
      suzukiU a (GaloisField 2 (2 * a + 1)))
    {x : G} (hx : x ∈ X) :
    letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
    Additive.ofMul (Ch3z.chiefIota hNL ⟨x, hx⟩) ∈
      fixedSub
        (sectionRep hHL hHN hNL hE hO e) (suzukiU a (GaloisField 2 (2 * a + 1))) ↔
      x ∈ centralizerMod X1 X S := by
  letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
  constructor
  · intro hfix
    refine ⟨hx, hNL hx, ?_⟩
    intro s hs
    have hsH : s ∈ H := hSH hs
    let sH : ↥H := ⟨s, hsH⟩
    have hg : e (QuotientGroup.mk sH) ∈ suzukiU a (GaloisField 2 (2 * a + 1)) := by
      rw [← he]
      exact Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H))
          (Subgroup.mem_subgroupOf.mpr hs))
    have h1 := (mem_fixedSub.mp hfix) _ hg
    have hxn : s * x * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hHN hsH) x).mp hx
    have h2 := sectionRep_chiefIota hHL hHN hNL hE hO e sH ⟨x, hx⟩ hxn
    rw [h2] at h1
    have h3 : Ch3z.chiefIota hNL ⟨s * x * s⁻¹, hxn⟩ = Ch3z.chiefIota hNL ⟨x, hx⟩ :=
      Additive.ofMul.injective h1
    have h4 : Ch3z.chiefIota hNL (⟨s * x * s⁻¹, hxn⟩ * ⟨x, hx⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h3, mul_inv_cancel]
    have hmem := (Ch3z.chiefIota_eq_one_iff hNL _).mp h4
    have hinv := X1.inv_mem hmem
    simpa [mul_assoc] using hinv
  · intro hxC
    rw [mem_fixedSub]
    intro g hg
    rw [← he] at hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨sH, hsS, rfl⟩ := Subgroup.mem_map.mp hq
    have hs : (sH : G) ∈ S := Subgroup.mem_subgroupOf.mp hsS
    have hxn : (sH : G) * x * (sH : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHN sH.2) x).mp hx
    have h2 := sectionRep_chiefIota hHL hHN hNL hE hO e sH ⟨x, hx⟩ hxn
    change sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk sH))
      (Additive.ofMul (Ch3z.chiefIota hNL ⟨x, hx⟩)) = _
    rw [h2]
    apply congrArg Additive.ofMul
    have hmem : x * (sH : G) * x⁻¹ * (sH : G)⁻¹ ∈ X1 := hxC.2.2 (sH : G) hs
    have hmem' : (sH : G) * x * (sH : G)⁻¹ * x⁻¹ ∈ X1 := by
      have := X1.inv_mem hmem
      simpa [mul_assoc] using this
    have h4 : Ch3z.chiefIota hNL (⟨(sH : G) * x * (sH : G)⁻¹, hxn⟩ * ⟨x, hx⟩⁻¹) = 1 :=
      (Ch3z.chiefIota_eq_one_iff hNL _).mpr hmem'
    rw [map_mul, map_inv] at h4
    exact mul_inv_eq_one.mp h4

private theorem card_le_mul_card_of_sectionRep
    {H X X1 Z Z1 : Subgroup G} {a : ℕ}
    (hHL : H ≤ Subgroup.normalizer (X1 : Set G))
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hNL : X ≤ Subgroup.normalizer (X1 : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod X1 X))
    (hO : pCoreOf 2 H ≤ centralizerMod X1 H X)
    (e : oTwoQuot ↥H ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (f : ↥Z →* Ch3z.chiefMod X1 X)
    (hZ1Z : Z1 ≤ Z)
    (hker : f.ker = Z1.subgroupOf Z)
    (hfix : ∀ z : ↥Z,
      letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
      Additive.ofMul (f z) ∈
        fixedSub
          (sectionRep hHL hHN hNL hE hO e) (suzukiU a (GaloisField 2 (2 * a + 1))))
    (hnat : letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
      IsSzNatural (sectionRep hHL hHN hNL hE hO e)) :
    Nat.card Z ≤ Nat.card Z1 * Nat.card (GaloisField 2 (2 * a + 1)) := by
  letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE
  letI : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hfixcard : Nat.card (fixedSub
      (sectionRep hHL hHN hNL hE hO e) (suzukiU a (GaloisField 2 (2 * a + 1)))) =
      Nat.card (GaloisField 2 (2 * a + 1)) :=
    natCard_fixedSub_suzukiU hK (sectionRep hHL hHN hNL hE hO e) hnat
  have hrange_le : Nat.card f.range ≤ Nat.card (GaloisField 2 (2 * a + 1)) := by
    rw [← hfixcard]
    refine Nat.card_le_card_of_injective
      (fun x : f.range => (⟨Additive.ofMul (x : Ch3z.chiefMod X1 X), ?_⟩ :
        fixedSub
          (sectionRep hHL hHN hNL hE hO e) (suzukiU a (GaloisField 2 (2 * a + 1))))) ?_
    · obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp x.2
      rw [← hz]
      exact hfix z
    · intro x y hxy
      have h2 : Additive.ofMul (x : Ch3z.chiefMod X1 X) =
          Additive.ofMul (y : Ch3z.chiefMod X1 X) :=
        congrArg (fun w : ↥(fixedSub
          (sectionRep hHL hHN hNL hE hO e)
          (suzukiU a (GaloisField 2 (2 * a + 1)))) =>
          (w : Additive (Ch3z.chiefMod X1 X))) hxy
      have h1 : (x : Ch3z.chiefMod X1 X) = (y : Ch3z.chiefMod X1 X) :=
        Additive.ofMul.injective h2
      exact Subtype.ext h1
  have hquot : Nat.card (↥Z ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hsub : Nat.card ↥(Z1.subgroupOf Z) = Nat.card Z1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1Z).toEquiv
  calc
    Nat.card Z = Nat.card (↥Z ⧸ f.ker) * Nat.card ↥f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card f.range * Nat.card ↥(Z1.subgroupOf Z) := by rw [hquot, hker]
    _ = Nat.card f.range * Nat.card Z1 := by rw [hsub]
    _ ≤ Nat.card (GaloisField 2 (2 * a + 1)) * Nat.card Z1 :=
      Nat.mul_le_mul_right _ hrange_le
    _ = Nat.card Z1 * Nat.card (GaloisField 2 (2 * a + 1)) := Nat.mul_comm _ _

private theorem str83G4_card_z2_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    Nat.card (Z2 L1 L2 S) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
  classical
  have hstep := str83G4_isChiefStep_x1_x hfr d hX hB
  obtain ⟨hHL, hHN, hNL, hE, hO, e, he, hnt⟩ :=
    str83G4_exists_sectionSetup hfr hstep (str83G4_z1_le_x1 hfr)
      (str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB)
  have hnat := sectionRep_isSzNatural_of_quadratic hfr
    (str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB)
    (str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX)
    hstep hHL hHN hNL hE hO e he hnt
  let f : ↥(Z2 L1 L2 S) →* Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S) :=
    (Ch3z.chiefIota hNL).comp (Subgroup.inclusion (z2_le_str83X L1 L2 S))
  have hker : f.ker = (Z1 L1 L2 S).subgroupOf (Z2 L1 L2 S) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      have h1 : Ch3z.chiefIota hNL
          (⟨(z : G), z2_le_str83X L1 L2 S z.2⟩ : ↥(str83X L1 L2 S)) = 1 := by
        change Ch3z.chiefIota hNL (Subgroup.inclusion (z2_le_str83X L1 L2 S) z) = 1
        exact hz
      have h2 : (z : G) ∈ str83X1 L1 L2 S := (Ch3z.chiefIota_eq_one_iff hNL _).mp h1
      have h3 : (z : G) ∈ Z2 L1 L2 S ⊓ str83X1 L1 L2 S := ⟨z.2, h2⟩
      rwa [str83G4_z2_inf_x1 hfr d hX hB] at h3
    · intro hz
      have h1 : (z : G) ∈ str83X1 L1 L2 S := str83G4_z1_le_x1 hfr hz
      exact (Ch3z.chiefIota_eq_one_iff hNL _).mpr h1
  have hfix : ∀ z : ↥(Z2 L1 L2 S),
      letI : CommGroup (Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S)) :=
        l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod (str83X1 L1 L2 S)
        (str83X L1 L2 S))) := l2ChiefSectionModule hE
      Additive.ofMul (f z) ∈
        fixedSub
          (sectionRep hHL hHN hNL hE hO e) (suzukiU a (GaloisField 2 (2 * a + 1))) := by
    intro z
    have hCz : (z : G) ∈ centralizerMod (str83X1 L1 L2 S) (str83X L1 L2 S) S := by
      refine mem_centralizerMod.mpr ⟨z2_le_str83X L1 L2 S z.2,
        hNL (z2_le_str83X L1 L2 S z.2), ?_⟩
      intro s hs
      have h1 : ⁅(z : G), s⁆ ∈ ⁅Z2 L1 L2 S, S⁆ :=
        Subgroup.commutator_mem_commutator z.2 hs
      rw [str83G4_commutator_z2_s hfr] at h1
      exact str83G4_z1_le_x1 hfr h1
    exact (mem_fixedSub_sectionRep_iff (L1 := L1) (L2 := L2) (S := S)
      (H := L1 ⊔ S) (X := str83X L1 L2 S) (X1 := str83X1 L1 L2 S) le_sup_right
      hHL hHN hNL hE hO he (z2_le_str83X L1 L2 S z.2)).2 hCz
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    obtain ⟨hF, hBfr, ha, hSz, hL2, hZI⟩ := hfr
    exact (str83_caseI_basics hF hBfr ha hSz hL2 hZI).2.1
  have hbound := card_le_mul_card_of_sectionRep (H := L1 ⊔ S) (X := str83X L1 L2 S)
    (X1 := str83X1 L1 L2 S) (Z := Z2 L1 L2 S) (Z1 := Z1 L1 L2 S) (a := a)
    hHL hHN hNL hE hO e f hZ1Z2 hker hfix hnat
  have hZ1card : Nat.card (Z1 L1 L2 S) = 2 ^ (2 * a + 1) :=
    str83G4Z1Card_holds G L1 L2 S a hfr
  have hKcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  calc
    Nat.card (Z2 L1 L2 S) ≤
        Nat.card (Z1 L1 L2 S) * Nat.card (GaloisField 2 (2 * a + 1)) := hbound
    _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [hZ1card, hKcard]; ring

theorem str83G4_card_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    Nat.card (Z2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨V, hVZ, -, hVnat⟩ := str83G4_exists_natural_bottom hfr
  have hVcard : Nat.card V = (2 ^ (2 * a + 1)) ^ 2 := hVnat.natCard_eq
  refine le_antisymm (str83G4_card_z2_le hfr d hX hB) ?_
  rw [← hVcard]
  exact Subgroup.card_le_of_le hVZ

theorem str83G4_eq_z2_of_vNat
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {V : Subgroup G} (hVZ : V ≤ Z2 L1 L2 S) (hV : Str83G4VNat L1 L2 S V a) :
    V = Z2 L1 L2 S := by
  have hVcard : Nat.card V = (2 ^ (2 * a + 1)) ^ 2 := hV.natCard_eq
  have hZcard : Nat.card (Z2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 :=
    str83G4_card_z2 hfr d hX hB
  refine Subgroup.eq_of_le_of_card_ge hVZ ?_
  simp [hZcard, hVcard]

theorem str83G4_isChiefStep_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) := by
  obtain ⟨V, hVZ, hstep, hVnat⟩ := str83G4_exists_natural_bottom hfr
  have hVeq : V = Z2 L1 L2 S := str83G4_eq_z2_of_vNat hfr d hX hB hVZ hVnat
  simpa [hVeq] using hstep

end CFSG.Quasithin.Stroth

end
