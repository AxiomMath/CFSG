module

public import CFSG.Quasithin.Background.OddIndexAveraging
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleFrame
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixedPointwise
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelTransport
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem p7_inf_centralizer_le_centralizerMod {A : Subgroup G} {t : G} :
    A ⊓ Subgroup.centralizer ({t} : Set G) ≤
      centralizerMod (⊥ : Subgroup G) A (Subgroup.zpowers t) := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [mem_centralizerMod]
  refine ⟨hx.1, ?_, ?_⟩
  · rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  · intro u hu
    rw [Subgroup.mem_zpowers_iff] at hu
    obtain ⟨k, rfl⟩ := hu
    rw [Subgroup.mem_bot]
    have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    change ⁅x, t ^ k⁆ = 1
    exact commutatorElement_eq_one_iff_commute.mpr (hxt.zpow_right k)

private theorem p7_relIndex_inf_le {W Z C : Subgroup G} (hWZ : W ≤ Z) :
    (W ⊓ C).relIndex W ≤ C.relIndex Z := by
  have hsub : (Z ⊓ C).subgroupOf W = (W ⊓ C).subgroupOf W := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h.2⟩, fun h => ⟨hWZ x.2, h.2⟩⟩
  have hZeq : (Z ⊓ C).relIndex W = (W ⊓ C).relIndex W := by
    rw [Subgroup.relIndex, Subgroup.relIndex, hsub]
  rw [← hZeq, ← Subgroup.inf_relIndex_right C Z,
    show C ⊓ Z = Z ⊓ C from inf_comm C Z]
  exact Subgroup.relIndex_le_of_le_right hWZ Subgroup.index_ne_zero_of_finite

private theorem p7s_disp_le_relIndex {L1 L2 S D : Subgroup G}
    {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S) :
    2 ^ m ≤ (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W := by
  classical
  have hUH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hDleH : D ≤ u3H L1 L2 S := hDS.trans (str86_s_le_u3H hF.toW hSB hm hL2)
  obtain ⟨t, htD, _⟩ : ∃ t, t ∈ D ∧ t ∉ Q2 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact hDQ (fun x hx => hcon x hx)
  have htS : t ∈ S := hDS htD
  have htH : t ∈ u3H L1 L2 S := hDleH htD
  have ht2 : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H hF.toW]
    exact str86_sq_mem_q2 hF.toW hSB hm hL2 htS
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rwa [str86_pCoreOf_u3H hF.toW]
  have hL2H : IsL2Quot m (oTwoQuot ↥(u3H L1 L2 S)) := str86_isL2Quot_u3H hF.toW hL2
  have hdisp := l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := m) hm hL2H
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)) hUH hstepW hncW htH ht2 htO
  have hdisp' : 2 ^ m ≤ (W ⊓ Subgroup.centralizer ({t} : Set G)).relIndex W := by
    refine hdisp.trans ?_
    exact Subgroup.relIndex_le_of_le_left (p7_inf_centralizer_le_centralizerMod (A := W))
      Subgroup.index_ne_zero_of_finite
  refine hdisp'.trans ?_
  exact Subgroup.relIndex_le_of_le_left
    (inf_le_inf_left W (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htD)))
    Subgroup.index_ne_zero_of_finite

private theorem p7s_card_Dbar_bounds {L1 L2 S D : Subgroup G}
    {k m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W) (hWZ2 : W ≤ Z2 L1 L2 S)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S)
    (hD : (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex D) :
    2 ^ k ≤ Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ∧
      (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W ≤
        Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ^ 2 := by
  classical
  have hm : 2 ≤ m := by omega
  have hDleH : D ≤ u3H L1 L2 S := hDS.trans (str86_s_le_u3H hF.toW hSB hm hL2)
  have hDbar_card : Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) =
      (Q2 L1 L2 S).relIndex D := by
    rw [Subgroup.card_map_of_injective e.injective,
      str86_card_imageOTwoQuot_u3H hF hDleH]
  have hdispW : 2 ^ m ≤ (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W :=
    p7s_disp_le_relIndex hF hSB hm hL2 hstepW hncW hE e hDS hDQ
  have hDZ : (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W ≤
      (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) := p7_relIndex_inf_le hWZ2
  have hchain : 2 ^ m ≤
      2 ^ k * Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
    calc 2 ^ m ≤ (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W := hdispW
      _ ≤ (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) := hDZ
      _ ≤ 2 ^ k * (Q2 L1 L2 S).relIndex D := hD
      _ = 2 ^ k * Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
          rw [hDbar_card]
  have hkbar : 2 ^ k ≤ Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
    have hle : 2 ^ k * 2 ^ k ≤
        2 ^ k * Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
      calc 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hkm
        _ ≤ 2 ^ k * Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := hchain
    exact Nat.le_of_mul_le_mul_left hle (by positivity)
  refine ⟨hkbar, ?_⟩
  calc (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W
      ≤ 2 ^ k * (Q2 L1 L2 S).relIndex D := hDZ.trans hD
    _ = 2 ^ k * Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
        rw [hDbar_card]
    _ ≤ Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) *
        Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) :=
        Nat.mul_le_mul hkbar le_rfl
    _ = Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ^ 2 :=
        (pow_two _).symm

private theorem p7s_Dbar_props {L1 L2 S D : Subgroup G}
    {m k : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hk : 2 ≤ k)
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hDS : D ≤ S)
    (hkbar : 2 ^ k ≤ Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom)) :
    (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom ≠ ⊥ ∧
      ∀ a ∈ (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom, a * a = 1 := by
  classical
  have hDbar_le : (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom ≤
      (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :=
    Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hDS))
  have hA2 := (str86_imageS_props hF hSB hm hL2 e).1
  have hgt : 1 < Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) := by
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  exact ⟨(Subgroup.one_lt_card_iff_ne_bot _).mp hgt, fun a ha => hA2 a (hDbar_le ha)⟩

private theorem p7s_hoff {L1 L2 S D : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hDS : D ≤ S)
    (hdisp_le : (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W ≤
      Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ^ 2) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Nat.card (Additive (Ch3z.chiefMod ⊥ W)) ≤
      Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ^ 2 *
        Nat.card {w : Additive (Ch3z.chiefMod ⊥ W) //
          ∀ a ∈ (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom,
            l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e a w = w} := by
  classical
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let Dbar : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom
  let rho := l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
  change Nat.card (Additive (Ch3z.chiefMod ⊥ W)) ≤
    Nat.card Dbar ^ 2 * Nat.card {w : Additive (Ch3z.chiefMod ⊥ W) //
      ∀ a ∈ Dbar, rho a w = w}
  have hDleH : D ≤ u3H L1 L2 S := hDS.trans (str86_s_le_u3H hF.toW hSB hm hL2)
  have hWcard : Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
    calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
          Nat.card_congr (chiefModBotMulEquiv W).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
          Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)
  have hH2 := str86_card_fixedSub_image (L1 := L1) (L2 := L2) (S := S) (D := D)
    (m := m) (W := W) hstepW hE e hDleH
  have hfix : Nat.card {w : Additive (Ch3z.chiefMod ⊥ W) // ∀ a ∈ Dbar, rho a w = w} =
      Nat.card ↥(fixedSub rho Dbar) := rfl
  rw [hfix, hH2]
  calc Nat.card (Additive (Ch3z.chiefMod ⊥ W))
      = Nat.card W := hWcard.symm
    _ = (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W *
          Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) := by
        rw [← Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (D : Set G))
            (K := W), inf_eq_left.mpr inf_le_left]
    _ ≤ Nat.card Dbar ^ 2 * Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) :=
        Nat.mul_le_mul_right _ hdisp_le

theorem str86_chief_natural_or_orth {L1 L2 S : Subgroup G}
    {k m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W) (hWZ2 : W ≤ Z2 L1 L2 S)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {D : Subgroup G} (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S)
    (hD : (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex D) :
    (letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE;
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE;
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) ∨
    ∃ (l : ℕ) (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)), m = 2 * l ∧
      (letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE;
        letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE;
        IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) := by
  classical
  have hm : 2 ≤ m := by omega
  have hn1 : 1 ≤ m := by omega
  have hFcard : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 m (by omega)
  let Dbar : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let rho := l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
  have hρirr : rho.IsIrreducible :=
    l2ChiefSectionRep_irreducible hstepW (q2_le_u3H L1 L2 S) hE e
  haveI : Fact rho.IsIrreducible := ⟨hρirr⟩
  have hnt : ∃ g, rho g ≠ 1 :=
    l2ChiefSectionRep_nontrivial hstepW (q2_le_u3H L1 L2 S) hE e hncW
  have hbounds :=
    p7s_card_Dbar_bounds hF hSB hk hL2 hkm hstepW hncW hWZ2 hE e hDS hDQ hD
  have hprops :=
    p7s_Dbar_props hF hSB hm hL2 hk e hDS (by simpa [Dbar] using hbounds.1)
  have hDbar_ne : Dbar ≠ ⊥ := by simpa [Dbar] using hprops.1
  have hA2 : ∀ a ∈ Dbar, a * a = 1 := by simpa [Dbar] using hprops.2
  have hoff : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) ≤
      Nat.card Dbar ^ 2 * Nat.card {w : Additive (Ch3z.chiefMod ⊥ W) //
        ∀ a ∈ Dbar, rho a w = w} := by
    simpa [Dbar, rho] using p7s_hoff hF hSB hm hL2 hstepW hE e hDS
      (by simpa [Dbar] using hbounds.2)
  obtain ⟨hEnd, hdim⟩ | ⟨l, hml, hEnd, hdim⟩ :=
    CFSG.Quasithin.B45L2.inner_class (n := m) (F := GaloisField 2 m)
      (W := Additive (Ch3z.chiefMod ⊥ W)) hn1 hFcard rho hnt Dbar hDbar_ne hA2 hoff
  · exact Or.inl (isNaturalModule_of_dvd (n := m) (d := m) hn1 hFcard rho hnt
      hEnd hdim dvd_rfl)
  · have hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l) := by
      rw [hFcard, hml]
    exact Or.inr ⟨l, hl, hml, orth_iso (s := l) (by omega) hl rho hnt hEnd hdim⟩

private theorem p8_commutator_le_z2 (L1 L2 S : Subgroup G) :
    ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤ Z2 L1 L2 S := by
  rw [Subgroup.commutator_le]
  intro z hz h hh
  have hnh : h * z⁻¹ * h⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (str86_z2_normal_u3H L1 L2 S hh) z⁻¹).mp
      ((Z2 L1 L2 S).inv_mem hz)
  rw [commutatorElement_def]
  simpa [mul_assoc] using (Z2 L1 L2 S).mul_mem hz hnh

private theorem p8_centralizerMod_le {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    centralizerMod ⊥ (Z2 L1 L2 S) S ≤ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  have hcase := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hZ2H : Z2 L1 L2 S ⊓
      Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) = ⊥ := hcase.2.2.1
  have hSleH : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  have hSylH : IsSylowTwoOf S (u3H L1 L2 S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSleH
      (u3H_le_p2 L1 L2 S)
  have hodd : Odd (S.relIndex (u3H L1 L2 S)) :=
    Nat.not_even_iff_odd.1 fun he =>
      CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hSylH (even_iff_two_dvd.mp he)
  refine mem_of_centralizerMod_odd (P := u3H L1 L2 S) (T := S) (Q := Z2 L1 L2 S)
    (Z := ⊥) (N := ⁅Z2 L1 L2 S, u3H L1 L2 S⁆) hSleH hodd bot_le
    (p8_commutator_le_z2 L1 L2 S) ?_ ?_ (str86_z2_normal_u3H L1 L2 S) ?_ ?_ ?_ ?_
  · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  · exact CFSG.Quasithin.D14.le_normalizer_commutator
      (str86_z2_normal_u3H L1 L2 S) Subgroup.le_normalizer
  · intro x hx y hy
    rw [Subgroup.mem_bot]
    calc x * y * x⁻¹ * y⁻¹ = y * x * x⁻¹ * y⁻¹ := by
          rw [A4.mul_comm_of_mem_omegaOneCenterOf hx hy]
      _ = 1 := by group
  · intro x hx
    rw [Subgroup.mem_bot]
    simpa [pow_two] using A4.sq_eq_one_of_mem_omegaOneCenterOf hx
  · intro p hp x hx
    rw [Subgroup.commutator_comm (Z2 L1 L2 S) (u3H L1 L2 S)]
    simpa only [commutatorElement_def] using Subgroup.commutator_mem_commutator hp hx
  · intro x hxZ2 hx
    have hxH : x ∈ Z2 L1 L2 S ⊓
        Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := by
      refine ⟨hxZ2, ?_⟩
      change x ∈ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h := hx p hp
      rw [Subgroup.mem_bot] at h
      have hp1 : p * x * p⁻¹ = x := by
        calc p * x * p⁻¹ = (p * x * p⁻¹ * x⁻¹) * x := by group
          _ = 1 * x := by rw [h]
          _ = x := by group
      calc p * x = (p * x * p⁻¹) * p := by group
        _ = x * p := by rw [hp1]
    rwa [hZ2H] at hxH

theorem str86_z1_le_commutator {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≤ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ∧
      ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := by
  classical
  have hNQ := p8_commutator_le_z2 L1 L2 S
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  have hcase := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hZ2CS : Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S :=
    hcase.2.2.2.2
  have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer (S : Set G) := by
    rw [← hZ2CS]
    exact inf_le_right
  have hmain := p8_centralizerMod_le hF hSB hk hFc hU3 hB2 hm hL2 hZI
  have hle : Z1 L1 L2 S ≤ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ := by
    intro x hx
    have hx' : x ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) := by
      rw [hZ2CS]
      exact hx
    refine hmain ?_
    rw [mem_centralizerMod]
    refine ⟨hx'.1, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
      exact Subgroup.mem_top x
    · intro u hu
      rw [Subgroup.mem_bot]
      have hux : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hx'.2) u hu
      rw [← hux]
      group
  refine ⟨hle, le_antisymm ?_ ?_⟩
  · intro x hx
    have hx' : x ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) :=
      ⟨hNQ hx.1, hx.2⟩
    rwa [hZ2CS] at hx'
  · intro x hx
    exact ⟨hle hx, hZ1C hx⟩

theorem str86_card_z1_of_natural {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) :
    Nat.card (Z1 L1 L2 S) = 2 ^ m := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  have hSleH : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  obtain ⟨hA2, hAcard⟩ := str86_imageS_props hF hSB hm hL2 e
  have h2 := str86_card_fixedSub_image (L1 := L1) (L2 := L2) (S := S) (W := W) (D := S)
    (m := m) hstepW hE e hSleH
  have hGF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hAcard' : Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) =
      Nat.card (GaloisField 2 m) := by rw [hAcard, hGF]
  have hfixed : Nat.card ↥(fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
      ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom)) = 2 ^ m := by
    rw [IsNaturalModule.natCard_fixedSub hnat hA2 hAcard', hGF]
  rw [show Nat.card (Z1 L1 L2 S) =
    Nat.card ↥(W ⊓ Subgroup.centralizer (S : Set G)) by rw [hWS]]
  rw [← h2]
  exact hfixed

theorem str86_card_z1_of_orth {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) :
    Nat.card (Z1 L1 L2 S) = 2 ^ l := by
  classical
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom
  have hSleH : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  obtain ⟨hA2, hAcard⟩ := str86_imageS_props hF hSB hm hL2 e
  have h2 := str86_card_fixedSub_image (L1 := L1) (L2 := L2) (S := S) (W := W) (D := S)
    (m := m) hstepW hE e hSleH
  have hAcard2 : Nat.card ↥A = 2 ^ (2 * l) := by rw [hAcard, hml]
  have hfixed : Nat.card ↥(fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
      A) = 2 ^ l := IsOrthModule.card_fixedSub hl horth A hA2 hAcard2
  rw [show Nat.card (Z1 L1 L2 S) =
    Nat.card ↥(W ⊓ Subgroup.centralizer (S : Set G)) by rw [hWS]]
  rw [← h2]
  exact hfixed

end CFSG.Quasithin.Stroth

end
