module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleConj
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleTransport
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoProp

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem q1s_commutator_eq_one_of_mem_q2 {L1 L2 S : Subgroup G} {s x : G}
    (hsQ : s ∈ Q2 L1 L2 S) (hxZ : x ∈ Z2 L1 L2 S) :
    x * s * x⁻¹ * s⁻¹ = 1 := by
  have hcs : s ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hsQ
  have h1 : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hcs) x hxZ
  calc x * s * x⁻¹ * s⁻¹ = (s * x) * x⁻¹ * s⁻¹ := by rw [h1]
    _ = 1 := by group

private theorem q1s_mem_image_and_ne_one
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S)
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    {s : G} (hsS : s ∈ S) (hsH : s ∈ u3H L1 L2 S) (hsQ : s ∉ Q2 L1 L2 S) :
    e (QuotientGroup.mk ⟨s, hsH⟩) ∈
        (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom ∧
      e (QuotientGroup.mk ⟨s, hsH⟩) ≠ 1 := by
  have haA : e (QuotientGroup.mk ⟨s, hsH⟩) ∈
      (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)))
        (Subgroup.mem_subgroupOf.mpr hsS))
  refine ⟨haA, ?_⟩
  intro h
  apply hsQ
  have hmk1 : (QuotientGroup.mk ⟨s, hsH⟩ : oTwoQuot ↥(u3H L1 L2 S)) = 1 := by
    apply e.injective
    rw [map_one]
    exact h
  have hmem : (⟨s, hsH⟩ : ↥(u3H L1 L2 S)) ∈ pCore 2 ↥(u3H L1 L2 S) :=
    (QuotientGroup.eq_one_iff _).mp hmk1
  have := (F1.mem_pCore_iff_coe (⟨s, hsH⟩ : ↥(u3H L1 L2 S))).mp hmem
  rwa [str86_pCoreOf_u3H hF.toW] at this

private theorem q1s_fixedSub_zpowers_eq
    {L1 L2 S : Subgroup G} {m : ℕ} {W : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ {a : SL(2, GaloisField 2 m)}
      (ha : a ∈ (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) (ha1 : a ≠ 1),
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e) (Subgroup.zpowers a) =
        fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
          ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hnat' : IsNaturalModule ρ := hnat
  let A : Subgroup (SL(2, GaloisField 2 m)) := (imageOTwoQuot H S).map e.toMonoidHom
  have hApr := str86_imageS_props hF hSB hm hL2 e
  have hA2 : ∀ a ∈ A, a * a = 1 := hApr.1
  have hAeqF : Nat.card A = Nat.card (GaloisField 2 m) := by
    rw [hApr.2]
    exact (GaloisField.card 2 m (by omega)).symm
  exact fun {a} ha ha1 => IsNaturalModule.fixedSub_zpowers_eq hnat' hA2 hAeqF ha ha1

private theorem q1s_mem_z1_of_mem_w_fixed
    {L1 L2 S : Subgroup G} {m : ℕ} {W : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    {s y : G} (hsS : s ∈ S) (hsQ : s ∉ Q2 L1 L2 S) (hyW : y ∈ W)
    (hyfix : s * y * s⁻¹ = y) : y ∈ Z1 L1 L2 S := by
  classical
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hm hL2
  have hsH : s ∈ H := hSleH hsS
  let a : SL(2, GaloisField 2 m) := e (QuotientGroup.mk ⟨s, hsH⟩)
  obtain ⟨haA, ha1⟩ := q1s_mem_image_and_ne_one hF e hsS hsH hsQ
  let P : Subgroup ↥H := Subgroup.zpowers ⟨s, hsH⟩
  have hPsub : (P.map H.subtype : Subgroup G) = Subgroup.zpowers s := by
    rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers]
    rfl
  have hPy : y ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hPsub] at hh
    have hcomm_s : Commute s y := by
      rw [Commute]
      calc s * y = (s * y * s⁻¹) * s := by group
        _ = y * s := by rw [hyfix]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hcomm_s.zpow_left j).eq
  have hPimg : (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
      Subgroup.zpowers a := by
    rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    rfl
  have hfixmem : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) :=
    (mem_fixSub_chiefMod_bot_iff hstepW hUH hE e P ⟨y, hyW⟩).mpr (by
      change (⟨y, hyW⟩ : ↥W).1 ∈ Subgroup.centralizer
        ((P.map H.subtype : Subgroup G) : Set G)
      simpa [hPsub] using hPy)
  rw [hPimg, q1s_fixedSub_zpowers_eq hF hSB hm hL2 hstepW hE e hnat haA ha1] at hfixmem
  have hycent : y ∈ Subgroup.centralizer (S : Set G) :=
    (str86_mem_fixedSub_image_iff hstepW hE e hSleH ⟨y, hyW⟩).mp hfixmem
  have hmem : y ∈ W ⊓ Subgroup.centralizer (S : Set G) := ⟨hyW, hycent⟩
  rwa [hWS] at hmem

theorem str86_natural_commutator_mem_z1 {L1 L2 S : Subgroup G}
    {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) :
    ∀ s ∈ S, ∀ x ∈ Z2 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Z1 L1 L2 S := by
  classical
  have hSleH : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  intro s hsS x hxZ
  by_cases hsQ : s ∈ Q2 L1 L2 S
  · rw [q1s_commutator_eq_one_of_mem_q2 hsQ hxZ]
    exact (Z1 L1 L2 S).one_mem
  · have hsH : s ∈ u3H L1 L2 S := hSleH hsS
    let y : G := s * x * s⁻¹ * x⁻¹
    have hyW : y ∈ W := str86_commutator_mem_w hcomm hsH hxZ
    have hyfix : s * y * s⁻¹ = y :=
      str86_commutator_fixed_of_sq hF.toW hSB hm hL2 hsS hxZ
    have hyZ1 : y ∈ Z1 L1 L2 S :=
      q1s_mem_z1_of_mem_w_fixed hF hSB hm hL2 hstepW hE e hnat hWS hsS hsQ hyW hyfix
    have hinv : x * s * x⁻¹ * s⁻¹ = y⁻¹ := by
      change x * s * x⁻¹ * s⁻¹ = (s * x * s⁻¹ * x⁻¹)⁻¹
      group
    rw [hinv]
    exact (Z1 L1 L2 S).inv_mem hyZ1

private theorem q2s_commutator_le_z1
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    {x : G} (hxS : x ∈ S) :
    ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ ≤ Z1 L1 L2 S := by
  rw [Subgroup.commutator_le]
  intro z hz s hs
  exact str86_natural_commutator_mem_z1 hF hSB hm hL2 hstepW hcomm hE e hnat hWS
    s (Subgroup.zpowers_le.mpr hxS hs) z hz

private theorem q2s_mem_image_and_ne_one
    {L1 L2 S : Subgroup G} {m : ℕ} (hF : F112Hyp L1 L2 S)
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    {x : G} (hxH : x ∈ u3H L1 L2 S) (hxS : x ∈ S) (hxQ : x ∉ Q2 L1 L2 S) :
    e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S))) ∈
        (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom ∧
      e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S))) ≠ 1 ∧
      (imageOTwoQuot (u3H L1 L2 S) (Subgroup.zpowers x)).map e.toMonoidHom =
        Subgroup.zpowers (e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S)))) := by
  classical
  have haA : e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S))) ∈
      (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)))
        (Subgroup.mem_subgroupOf.mpr hxS))
  have ha1 : e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S))) ≠ 1 := by
    intro h
    apply hxQ
    have hmk1 : (QuotientGroup.mk ⟨x, hxH⟩ : oTwoQuot ↥(u3H L1 L2 S)) = 1 := by
      apply e.injective
      rw [map_one]
      exact h
    have hmem : (⟨x, hxH⟩ : ↥(u3H L1 L2 S)) ∈ pCore 2 ↥(u3H L1 L2 S) :=
      (QuotientGroup.eq_one_iff _).mp hmk1
    have := (F1.mem_pCore_iff_coe (⟨x, hxH⟩ : ↥(u3H L1 L2 S))).mp hmem
    rwa [str86_pCoreOf_u3H hF.toW] at this
  have hPsub : (Subgroup.zpowers x).subgroupOf (u3H L1 L2 S) =
      Subgroup.zpowers (⟨x, hxH⟩ : ↥(u3H L1 L2 S)) := by
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  have hImg : (imageOTwoQuot (u3H L1 L2 S) (Subgroup.zpowers x)).map e.toMonoidHom =
      Subgroup.zpowers (e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(u3H L1 L2 S)))) := by
    rw [imageOTwoQuot, hPsub, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  exact ⟨haA, ha1, hImg⟩

private theorem q2s_card_centralizer_inf_W
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {x : G} (hxS : x ∈ S) (hxQ : x ∉ Q2 L1 L2 S) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ W) = 2 ^ m := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hnat' : IsNaturalModule ρ := hnat
  let A : Subgroup (SL(2, GaloisField 2 m)) := (imageOTwoQuot H S).map e.toMonoidHom
  have hApr := str86_imageS_props hF hSB hm hL2 e
  have hA2 : ∀ a ∈ A, a * a = 1 := hApr.1
  have hAeqF : Nat.card A = Nat.card (GaloisField 2 m) := by
    rw [hApr.2]
    exact (GaloisField.card 2 m (by omega)).symm
  have hfixedA : Nat.card ↥(fixedSub ρ A) = 2 ^ m := by
    rw [IsNaturalModule.natCard_fixedSub hnat' hA2 hAeqF]
    exact GaloisField.card 2 m (by omega)
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hm hL2
  have hxH : x ∈ H := hSleH hxS
  have hD : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  obtain ⟨haA, ha1, hImg⟩ := q2s_mem_image_and_ne_one hF e hxH hxS hxQ
  have hH2 := str86_card_fixedSub_image (L1 := L1) (L2 := L2) (S := S)
    (D := Subgroup.zpowers x) (m := m) (W := W) hstepW hE e hD
  have hCcard : Nat.card ↥(W ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) = 2 ^ m := by
    rw [← hH2, hImg, IsNaturalModule.fixedSub_zpowers_eq hnat' hA2 hAeqF haA ha1]
    exact hfixedA
  have hcentzp : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [inf_comm, ← hcentzp]
  exact hCcard

private theorem q2s_card_W {L1 L2 S W : Subgroup G} {m : ℕ}
    (hm : 2 ≤ m)
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    Nat.card ↥W = (2 ^ m) ^ 2 := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  obtain ⟨φ, -⟩ := hnat
  calc Nat.card ↥W = Nat.card ↥(Ch3z.chiefMod ⊥ W) :=
        Nat.card_congr (chiefModBotMulEquiv W).toEquiv
    _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
        (Nat.card_congr Additive.ofMul).symm
    _ = Nat.card (Fin 2 → GaloisField 2 m) := Nat.card_congr φ.toEquiv
    _ = Nat.card (GaloisField 2 m) * Nat.card (GaloisField 2 m) := by
        rw [Nat.card_fun, Nat.card_fin, pow_two]
    _ = (2 ^ m) ^ 2 := by
        rw [GaloisField.card 2 m (by omega), pow_two]

private theorem q2s_relIndex_centralizer_W {W : Subgroup G} {m : ℕ} {x : G}
    (hCW : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ W) = 2 ^ m)
    (hWcard : Nat.card ↥W = (2 ^ m) ^ 2) :
    (Subgroup.centralizer ({x} : Set G)).relIndex W = 2 ^ m := by
  have hmul := Subgroup.relIndex_mul_card
    (H := Subgroup.centralizer ({x} : Set G)) (K := W)
  rw [hCW, hWcard, pow_two] at hmul
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) m) hmul

private theorem q2s_card_range_commutator_le {L1 L2 S : Subgroup G} {x : G} :
    Nat.card (Set.range fun z : ↥(Z2 L1 L2 S) =>
        (z : G) * x * (z : G)⁻¹ * x⁻¹) ≤
      Nat.card ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ := by
  refine Nat.card_le_card_of_injective
    (fun y : Set.range (fun z : ↥(Z2 L1 L2 S) =>
        (z : G) * x * (z : G)⁻¹ * x⁻¹) =>
      (⟨y.1, ?_⟩ : ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆)) ?_
  · obtain ⟨z, hz⟩ := y.2
    rw [← hz]
    exact Subgroup.commutator_mem_commutator z.2 (Subgroup.mem_zpowers x)
  · intro y₁ y₂ h
    apply Subtype.ext
    exact congrArg (fun p : ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ => (p : G)) h

private theorem q2s_card_commutator_ge {L1 L2 S : Subgroup G} {W : Subgroup G} {m : ℕ}
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) {x : G} (hxS : x ∈ S)
    (hrelW : (Subgroup.centralizer ({x} : Set G)).relIndex W = 2 ^ m) :
    2 ^ m ≤ Nat.card ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ := by
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hZ2comm : ∀ a ∈ Z2 L1 L2 S, ∀ b ∈ Z2 L1 L2 S, a * b = b * a := by
    intro a ha b hb
    have h := (isMulCommutative_iff.mp hZ2ea.1) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hWZ2 : W ≤ Z2 L1 L2 S := by
    rw [← hcomm]
    rw [Subgroup.commutator_le]
    intro z hz h hh
    have h1 : h * z⁻¹ * h⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (str86_z2_normal_u3H L1 L2 S hh) z⁻¹).mp
        ((Z2 L1 L2 S).inv_mem hz)
    rw [commutatorElement_def]
    simpa [mul_assoc] using (Z2 L1 L2 S).mul_mem hz h1
  have hneZ : (Subgroup.centralizer ({x} : Set G)).relIndex (Z2 L1 L2 S) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card
      (H := Subgroup.centralizer ({x} : Set G)) (K := Z2 L1 L2 S)
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hxNorm : x ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S) hxS
  have hrange_card : Nat.card (Set.range fun z : ↥(Z2 L1 L2 S) =>
        (z : G) * x * (z : G)⁻¹ * x⁻¹) =
      (Subgroup.centralizer ({x} : Set G)).relIndex (Z2 L1 L2 S) :=
    CFSG.Quasithin.H13.A7.card_range_commutator_eq_relIndex hZ2comm hxNorm
  calc 2 ^ m = (Subgroup.centralizer ({x} : Set G)).relIndex W := hrelW.symm
    _ ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (Z2 L1 L2 S) :=
        Subgroup.relIndex_le_of_le_right hWZ2 hneZ
    _ = Nat.card (Set.range fun z : ↥(Z2 L1 L2 S) =>
          (z : G) * x * (z : G)⁻¹ * x⁻¹) := hrange_card.symm
    _ ≤ Nat.card ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ :=
        q2s_card_range_commutator_le (x := x)

theorem str86_natural_commutator_zpowers_eq
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ m) :
    ∀ x ∈ S, x ∉ Q2 L1 L2 S → ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ = Z1 L1 L2 S := by
  classical
  intro x hxS hxQ
  have hle : ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ ≤ Z1 L1 L2 S :=
    q2s_commutator_le_z1 hF hSB hm hL2 hstepW hcomm hE e hnat hWS hxS
  have hCW : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ W) = 2 ^ m :=
    q2s_card_centralizer_inf_W hF hSB hm hL2 hstepW hE e hnat hxS hxQ
  have hWcard : Nat.card ↥W = (2 ^ m) ^ 2 := q2s_card_W hm hstepW hE e hnat
  have hrelW : (Subgroup.centralizer ({x} : Set G)).relIndex W = 2 ^ m :=
    q2s_relIndex_centralizer_W hCW hWcard
  have hcard_comm : 2 ^ m ≤ Nat.card ↥⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ :=
    q2s_card_commutator_ge hcomm hxS hrelW
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZ1]
  exact hcard_comm

private theorem n1_conj_smul_iInf_eq {P B W : Subgroup G} (hBP : B ≤ P) {b : G}
    (hb : b ∈ B) :
    MulAut.conj b • (⨅ (h : G) (_ : h ∈ P), MulAut.conj h • W) =
      ⨅ (h : G) (_ : h ∈ P), MulAut.conj h • W := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply, Subgroup.mem_iInf]
  constructor
  · intro hy h hh
    have hk : b⁻¹ * h ∈ P := P.mul_mem (P.inv_mem (hBP hb)) hh
    have hmem := hy (b⁻¹ * h) hk
    have heq : (b⁻¹ * h)⁻¹ * (b⁻¹ * y * b) * (b⁻¹ * h) = h⁻¹ * y * h := by group
    rwa [heq] at hmem
  · intro hy h hh
    have hmem := hy (b * h) (P.mul_mem (hBP hb) hh)
    have heq : (b * h)⁻¹ * y * (b * h) = h⁻¹ * (b⁻¹ * y * b) * h := by group
    rwa [heq] at hmem

private theorem n1s_bigB_normalizer_W {L1 L2 S W : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) :
    bigB L1 L2 S ≤ Subgroup.normalizer (W : Set G) := by
  have hBZ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
    exact hBP2.trans ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)))
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 hF.1.symm
    rwa [bigB_comm L1 L2 S] at h
  have hBQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hBH : bigB L1 L2 S ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) :=
    D14.le_normalizer_sup hBL2 hBQ2
  have h := D14.le_normalizer_commutator hBZ2 hBH
  rwa [hcomm] at h

private theorem n1s_q2_centralizer_W {L1 L2 S W : Subgroup G}
    (hWZ2 : W ≤ Z2 L1 L2 S) :
    Q2 L1 L2 S ≤ Subgroup.centralizer (W : Set G) :=
  (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)).trans
    (Subgroup.centralizer_le hWZ2)

private theorem n1s_z1_le_iInf {L1 L2 S W : Subgroup G}
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) :
    Z1 L1 L2 S ≤ ⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W := by
  have hP1Z1 : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hZW : Z1 L1 L2 S ≤ W := hWS.symm ▸ inf_le_left
  intro z hz
  refine Subgroup.mem_iInf.mpr fun h => Subgroup.mem_iInf.mpr fun hh => ?_
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]
  exact hZW (by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hP1Z1 ((P1 L1 L2 S).inv_mem hh)) z).mp hz)

private theorem n1s_iInf_le_W {L1 L2 S W : Subgroup G} :
    (⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W) ≤ W := by
  intro x hx
  have h1 : x ∈ MulAut.conj (1 : G) • W :=
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx 1)) ((P1 L1 L2 S).one_mem)
  simpa using h1

private theorem n1s_bigB_invariant_iInf {L1 L2 S W : Subgroup G} :
    bigB L1 L2 S ≤ Subgroup.normalizer
      (((⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W) : Subgroup G) : Set G) := by
  let W'' : Subgroup G := ⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W
  change bigB L1 L2 S ≤ Subgroup.normalizer (W'' : Set G)
  intro b hb
  have hfix : MulAut.conj b⁻¹ • W'' = W'' :=
    n1_conj_smul_iInf_eq (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      ((bigB L1 L2 S).inv_mem hb)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ MulAut.conj b⁻¹ • W'' := by rw [hfix]; exact hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx'
  · intro hx
    have hx' : (MulAut.conj b⁻¹)⁻¹ • x ∈ W'' := by
      simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx
    have hx'' : x ∈ MulAut.conj b⁻¹ • W'' := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rwa [hfix] at hx''

private theorem n1s_P1_le_normalizer_of_iInf_eq {L1 L2 S W : Subgroup G}
    (hWeq : ((⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W) : Subgroup G) = W) :
    P1 L1 L2 S ≤ Subgroup.normalizer (W : Set G) := by
  have hWi (k : G) (hk : k ∈ P1 L1 L2 S) :
      (⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W) ≤
        MulAut.conj k • W := by
    intro x hx
    exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx k)) hk
  intro h hh
  have hfix : MulAut.conj h • W = W := by
    apply le_antisymm
    · have hle : W ≤ MulAut.conj h⁻¹ • W := by
        have h := hWi h⁻¹ ((P1 L1 L2 S).inv_mem hh)
        rwa [hWeq] at h
      calc MulAut.conj h • W
          ≤ MulAut.conj h • (MulAut.conj h⁻¹ • W) :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hle
        _ = W := by rw [← mul_smul]; simp
    · have h := hWi h hh
      rwa [hWeq] at h
  have hfixinv : MulAut.conj h⁻¹ • W = W := by
    calc MulAut.conj h⁻¹ • W = MulAut.conj h⁻¹ • (MulAut.conj h • W) := by
          rw [hfix]
      _ = W := by rw [← mul_smul]; simp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ MulAut.conj h⁻¹ • W := by rw [hfixinv]; exact hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx'
  · intro hx
    have hx' : (MulAut.conj h⁻¹)⁻¹ • x ∈ W := by
      simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx
    have hx'' : x ∈ MulAut.conj h⁻¹ • W := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rwa [hfixinv] at hx''

private theorem n1s_false_of_iInf_eq_W {L1 L2 S W : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hBW : bigB L1 L2 S ≤ Subgroup.normalizer (W : Set G))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S)
    (hWeq : ((⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W) : Subgroup G) = W) :
    False := by
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
    n1s_P1_le_normalizer_of_iInf_eq hWeq
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (W : Set G) := by
    refine sup_le ?_ hBW
    exact (l2_le_u3H L1 L2 S).trans (D14.le_normalizer_of_isNormalIn hstepW.1)
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (W : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1N hP2N
  have hP2G : P2 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact le_sup_right
  have hWle : W ≤ L1 ⊔ L2 ⊔ S :=
    hWZ2.trans ((A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      ((pCoreOf_le 2 (P2 L1 L2 S)).trans hP2G))
  have hW2 : IsPGroup 2 W :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le
      (hWZ2.trans (A4.omegaOneCenterOf_le (Q2 L1 L2 S)))
  have hWbot : W ≤ ⊥ := by
    have h := le_pCoreOf_of_le_normalizer 2 hWle hG0N hW2
    rwa [hF.1.o2] at h
  exact hstepW.2.2.1.ne' (le_bot_iff.mp hWbot)

theorem str86_natural_inf_conj_eq
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) :
    ∀ g ∈ P1 L1 L2 S, g ∉ bigB L1 L2 S → W ⊓ (MulAut.conj g • W) = Z1 L1 L2 S := by
  classical
  intro g hgP hgB
  have hBW : bigB L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
    n1s_bigB_normalizer_W hF hcomm
  have hQ2W : Q2 L1 L2 S ≤ Subgroup.centralizer (W : Set G) :=
    n1s_q2_centralizer_W hWZ2
  have hR3 := str86_conj_inf_conj_eq_iInf (X := W) (g := (1 : G)) (y := g)
    hF hSB hk hFc hU3 hm hL2 hBW hQ2W (one_mem _) hgP (by simpa using hgB)
  set W'' : Subgroup G :=
    ⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • W with hW''def
  have hR3' : W ⊓ (MulAut.conj g • W) = W'' := by
    simpa [hW''def] using hR3
  have hZi : Z1 L1 L2 S ≤ W'' := by
    rw [hW''def]
    exact n1s_z1_le_iInf hWS
  have hWiW : W'' ≤ W := by
    rw [hW''def]
    exact n1s_iInf_le_W
  have hBW'' : bigB L1 L2 S ≤ Subgroup.normalizer (W'' : Set G) := by
    rw [hW''def]
    exact n1s_bigB_invariant_iInf
  by_cases hWZ : W'' = Z1 L1 L2 S
  · rw [hR3', hWZ]
  ·
    have hWeq : W'' = W :=
      str86_natural_eq_of_bigB_invariant hF hSB hm hL2 hstepW hE e hnat hWS
        hWiW hBW'' hZi hWZ
    exfalso
    exact n1s_false_of_iInf_eq_W hF hBW hstepW hWZ2
      (by rw [← hW''def]; exact hWeq)

end CFSG.Quasithin.Stroth

end
