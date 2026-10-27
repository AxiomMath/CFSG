module

public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleGroup
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelBasic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_card_imageOTwoQuot_u3H {L1 L2 S D : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hD : D ≤ u3H L1 L2 S) :
    Nat.card ↥(imageOTwoQuot (u3H L1 L2 S) D) = (Q2 L1 L2 S).relIndex D := by
  classical
  let H := u3H L1 L2 S
  have hsub : CFSG.Open.pCore 2 ↥H = (Q2 L1 L2 S).subgroupOf H := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 H, str86_pCoreOf_u3H hF.toW]
  simp only [imageOTwoQuot]
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hsub,
    Subgroup.relIndex_subgroupOf hD]

theorem str86_imageS_props {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) :
    (∀ a ∈ (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom, a * a = 1) ∧
      Nat.card ↥((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) = 2 ^ m := by
  classical
  let H := u3H L1 L2 S
  have hSH : S ≤ H := str86_s_le_u3H hF.toW hSB hm hL2
  have hsq : ∀ a ∈ (imageOTwoQuot H S).map e.toMonoidHom, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have hxmem : (s * s : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
      rw [F1.mem_pCore_iff_coe, str86_pCoreOf_u3H hF.toW]
      simpa using str86_sq_mem_q2 hF.toW hSB hm hL2 (Subgroup.mem_subgroupOf.mp hs)
    have hmk : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) (s * s : ↥H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxmem
    have harg : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) s *
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) s =
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) (s * s) :=
      (map_mul (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) s s).symm
    rw [← map_mul e.toMonoidHom, harg, hmk, map_one]
  refine ⟨hsq, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective,
    str86_card_imageOTwoQuot_u3H hF hSH, str86_relIndex_q2_s hF.toW hSB hm hL2]

theorem str86_card_fixedSub_image {L1 L2 S D : Subgroup G} {m : ℕ} {W : Subgroup G}
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) (hD : D ≤ u3H L1 L2 S) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Nat.card ↥(fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom)) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) := by
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let P : Subgroup ↥H := D.subgroupOf H
  have hPsub : (P.map H.subtype : Subgroup G) = D := by
    rw [show P = D.subgroupOf H from rfl, Subgroup.map_subgroupOf_eq_of_le hD]
  have hmain := fixSub_chiefMod_bot_card (H := H) (U := Q2 L1 L2 S) (W := W)
    hstepW hUH hE e P
  have hmain' : Nat.card ↥(CFSG.RankThree.FFModules.fixSub
        (l2ChiefSectionRep hstepW hUH hE e)
        ((P.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map e.toMonoidHom)) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [← hPsub]
    exact hmain
  change Nat.card ↥(fixedSub (l2ChiefSectionRep hstepW hUH hE e)
      (((D.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        e.toMonoidHom)) =
    Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G))
  exact hmain'

theorem str86_mem_fixedSub_image_iff {L1 L2 S D : Subgroup G} {m : ℕ} {W : Subgroup G}
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) (hD : D ≤ u3H L1 L2 S)
    (w : ↥W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Additive.ofMul (chiefModBotMulEquiv W w) ∈
        fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
          ((imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom) ↔
      (w : G) ∈ Subgroup.centralizer (D : Set G) := by
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let P : Subgroup ↥H := D.subgroupOf H
  have hPsub : (P.map H.subtype : Subgroup G) = D := by
    rw [show P = D.subgroupOf H from rfl, Subgroup.map_subgroupOf_eq_of_le hD]
  have hmain := mem_fixSub_chiefMod_bot_iff (H := H) (U := Q2 L1 L2 S) (W := W)
    hstepW hUH hE e P w
  rw [hPsub] at hmain
  change Additive.ofMul (chiefModBotMulEquiv W w) ∈
      fixedSub (l2ChiefSectionRep hstepW hUH hE e)
        (((D.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
          e.toMonoidHom) ↔
      (w : G) ∈ Subgroup.centralizer (D : Set G)
  exact hmain

private theorem h3s_memS {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    ∀ x : ↥(u3H L1 L2 S),
      QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)) x ∈
        imageOTwoQuot (u3H L1 L2 S) S → (x : G) ∈ S := by
  classical
  let H := u3H L1 L2 S
  let N := pCore 2 ↥H
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hOX : pCoreOf 2 H ≤ S := by
    rw [show pCoreOf 2 H = Q2 L1 L2 S from str86_pCoreOf_u3H hF.toW]
    exact hQ2S
  have hcomap : (imageOTwoQuot H S).comap (QuotientGroup.mk' N) = S.subgroupOf H :=
    imageOTwoQuot_comap (H := H) (X := S) hOX
  intro x hx
  have hx' : x ∈ (imageOTwoQuot H S).comap (QuotientGroup.mk' N) := hx
  rw [hcomap] at hx'
  exact Subgroup.mem_subgroupOf.mp hx'

private theorem h3s_preimage_mem_normalizer
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) {n : SL(2, GaloisField 2 m)}
    (hn : n ∈ Subgroup.normalizer
      (((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :
        Subgroup (SL(2, GaloisField 2 m))) : Set (SL(2, GaloisField 2 m))))
    (h : ↥(u3H L1 L2 S))
    (hq : e (QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)) h) = n) :
    (h : G) ∈ Subgroup.normalizer (S : Set G) := by
  classical
  let H := u3H L1 L2 S
  let N := pCore 2 ↥H
  have hH : S ≤ H := str86_s_le_u3H hF.toW hSB hm hL2
  have memS := h3s_memS (L1 := L1) (L2 := L2) (S := S) hF
  apply Subgroup.mem_normalizer_fintype
  intro s hs
  let sH : ↥H := ⟨s, hH hs⟩
  let xH : ↥H := ⟨(h : G) * s * (h : G)⁻¹,
    H.mul_mem (H.mul_mem h.2 (hH hs)) (H.inv_mem h.2)⟩
  have hmks : QuotientGroup.mk' N sH ∈ imageOTwoQuot H S := by
    rw [imageOTwoQuot]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N)
      (Subgroup.mem_subgroupOf.mpr hs)
  have hmapS : e (QuotientGroup.mk' N sH) ∈
      (imageOTwoQuot H S).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hmks
  have hnx : n * e (QuotientGroup.mk' N sH) * n⁻¹ ∈
      (imageOTwoQuot H S).map e.toMonoidHom :=
    (Subgroup.mem_normalizer_iff.mp hn (e (QuotientGroup.mk' N sH))).mp hmapS
  have hmul : QuotientGroup.mk' N xH =
      QuotientGroup.mk' N h * QuotientGroup.mk' N sH * (QuotientGroup.mk' N h)⁻¹ := by
    change QuotientGroup.mk' N (h * sH * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have heq : e (QuotientGroup.mk' N xH) = n * e (QuotientGroup.mk' N sH) * n⁻¹ := by
    rw [hmul, map_mul, map_mul, map_inv, hq]
  have hb : e (QuotientGroup.mk' N xH) ∈
      (imageOTwoQuot H S).map e.toMonoidHom := by
    rw [heq]
    exact hnx
  exact memS xH ((Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hb)

private theorem h3s_bigB_eq {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    bigB L1 L2 S =
      P2 L1 L2 S ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
  calc bigB L1 L2 S = bigB L2 L1 S := (bigB_comm L1 L2 S).symm
    _ = (L2 ⊔ bigB L2 L1 S) ⊓
          Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
        F1.bigB_eq_parabolic_inf (Hyp111R.of_hyp111 rankOneListedFacts hF.1).symm
    _ = P2 L1 L2 S ⊓
          Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
        rw [bigB_comm L1 L2 S]

theorem str86_exists_bigB_lift {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) {n : SL(2, GaloisField 2 m)}
    (hn : n ∈ Subgroup.normalizer
      (((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom : Subgroup (SL(2, GaloisField 2 m))) :
        Set (SL(2, GaloisField 2 m)))) :
    ∃ h : ↥(u3H L1 L2 S), (h : G) ∈ bigB L1 L2 S ∧ e (QuotientGroup.mk h) = n := by
  classical
  let H := u3H L1 L2 S
  let N := pCore 2 ↥H
  obtain ⟨q, hq⟩ := e.surjective n
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hnormal : (h : G) ∈ Subgroup.normalizer (S : Set G) :=
    h3s_preimage_mem_normalizer hF hSB hm hL2 e hn h hq
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [← bigB_comm L1 L2 S]
    exact bigB_le_normalizer_of_hyp111 hF.1.symm
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hBL2
  have hP2 : (h : G) ∈ P2 L1 L2 S := u3H_le_p2 L1 L2 S h.2
  have hNinf : (h : G) ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hnormal, hP2N hP2⟩)
  have hBeq : bigB L1 L2 S =
      P2 L1 L2 S ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    h3s_bigB_eq hF
  refine ⟨h, ?_, ?_⟩
  · rw [hBeq]
    exact Subgroup.mem_inf.mpr ⟨hP2, hNinf⟩
  · simpa only [QuotientGroup.mk'_apply] using hq

private theorem h4_conj_mem_conjClosure {Z H : Subgroup G} {c : G}
    (hcH : c ∈ Subgroup.normalizer (H : Set G))
    (hcZ : c ∈ Subgroup.normalizer (Z : Set G)) {x : G}
    (hx : x ∈ conjClosure Z H) : c * x * c⁻¹ ∈ conjClosure Z H := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, z, hz, rfl⟩ := hx
    have hh' : c * h * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hcH h).mp hh
    have hz' : c * z * c⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hcZ z).mp hz
    rw [show c * (h * z * h⁻¹) * c⁻¹ =
      (c * h * c⁻¹) * (c * z * c⁻¹) * (c * h * c⁻¹)⁻¹ by group]
    exact mem_conjClosure hh' hz'
  | one => simpa using (conjClosure Z H).one_mem
  | mul x y _ _ ihx ihy =>
    rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) by group]
    exact (conjClosure Z H).mul_mem ihx ihy
  | inv x _ ih =>
    rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ by group]
    exact (conjClosure Z H).inv_mem ih

private theorem h4_bigB_le_normalizer_conjClosure {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    bigB L1 L2 S ≤
      Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) := by
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  intro b hb
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    simpa using h4_conj_mem_conjClosure (Subgroup.inv_mem _ (hBL hb))
      (Subgroup.inv_mem _ (hBZ hb)) hx
  · intro hx
    have hx' := h4_conj_mem_conjClosure (hBL hb) (hBZ hb) hx
    have heq : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
    rwa [heq] at hx'

theorem str86_conjClosure_basics {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (_hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x) :
    IsElemAbelian 2 (conjClosure (Z2 L1 L2 S) L1) ∧
      conjClosure (Z2 L1 L2 S) L1 ≤ Q1 L1 L2 S ∧
      P1 L1 L2 S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) ∧
      ∀ h ∈ P1 L1 L2 S, MulAut.conj h • Z2 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 := by
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine CFSG.CGT.Timmesfeld75.isElemAbelian_closure_two ?_ ?_
    · rintro x ⟨h, hh, z, hz, rfl⟩
      have hz2 : z * z = 1 := by
        simpa [pow_two] using
          (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hz
      calc
        (h * z * h⁻¹) ^ 2 = h * (z * z) * h⁻¹ := by
          rw [pow_two]
          group
        _ = 1 := by
          rw [hz2]
          group
    · rintro x ⟨h, hh, z, hz, rfl⟩ y ⟨h', hh', z', hz', rfl⟩
      exact hab _ (mem_conjClosure hh hz) _ (mem_conjClosure hh' hz')
  · refine conjClosure_le ?_
    intro h hh z hz
    exact (Subgroup.mem_normalizer_iff.mp
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S))
        ((le_sup_left : L1 ≤ P1 L1 L2 S) hh)) z).mp (hZQ hz)
  · change L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G)
    exact sup_le (le_normalizer_conjClosure _ _) (h4_bigB_le_normalizer_conjClosure hF)
  · intro h hh
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hh
    intro x hx
    obtain ⟨z, hz, hzx⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj (l * b))
        (Z2 L1 L2 S)).mp hx
    have hbz : b * z * b⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hBZ hb) z).mp hz
    rw [← hzx, MulAut.smul_def, MulAut.conj_apply]
    rw [show (l * b) * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ by group]
    exact mem_conjClosure (Z := Z2 L1 L2 S) (H := L1) hl hbz

theorem str86_relIndex_inf_q1_le {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {A : Subgroup G} (hAS : A ≤ S) (hA : IsElemAbelian 2 A) :
    (A ⊓ Q1 L1 L2 S).relIndex A ≤ 2 ^ k := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hLhatQ]
    exact pCoreOf_sup_pCoreOf hF.1
  have hqLh : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
      Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hLhatQ]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he hq
  have hT : IsSylowTwoOf S (L1 ⊔ S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF.toW) le_sup_right
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)))
  have h := relIndex_inf_pCoreOf_le (L := L1 ⊔ S) (T := S) (A := A) (q := 2 ^ k)
    hqLh hT hAS (fun a ha => by
      rw [hQcore]
      have hsq := hA.2 a ha
      simpa [hsq] using (Q1 L1 L2 S).one_mem)
  rwa [hQcore] at h

theorem str86_conj_z2_index_le {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (_hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (_hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G} (hg : g ∈ P1 L1 L2 S) :
    (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Q2 L1 L2 S).relIndex A := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQnorm : MulAut.conj g • Q1 L1 L2 S = Q1 L1 L2 S := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    exact le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg
  have hYS : MulAut.conj g • Z2 L1 L2 S ≤ S := by
    calc MulAut.conj g • Z2 L1 L2 S ≤ MulAut.conj g • Q1 L1 L2 S := Subgroup.map_mono hZQ
      _ = Q1 L1 L2 S := hQnorm
      _ ≤ S := hQ1S
  have hYe : IsElemAbelian 2 (MulAut.conj g • Z2 L1 L2 S) :=
    CFSG.Open.IsElemAbelian.map (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
      (MulAut.conj g).toMonoidHom
  have hRY : A ⊓ MulAut.conj g • Q2 L1 L2 S ≤
      Subgroup.centralizer (MulAut.conj g • Z2 L1 L2 S : Set G) := by
    intro r hr
    obtain ⟨-, hrQ⟩ := hr
    have hrQ' : g⁻¹ * r * g ∈ Q2 L1 L2 S := by
      simpa [MulAut.smul_def, MulAut.conj_apply]
        using (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
          (S := Q2 L1 L2 S) (x := r)).mp hrQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.mp hy
    have hcomm := Subgroup.mem_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hrQ') z hz
    have h2 := congrArg (MulAut.conj g) hcomm
    simp only [map_mul] at h2
    have hy' : g * z * g⁻¹ = y := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hzy
    rw [← hy']
    simpa [mul_assoc] using h2
  have h := relIndex_inf_le_relIndex_of_isMaxElemAbelian (T := S) (A := A)
    (Y := MulAut.conj g • Z2 L1 L2 S) (R := A ⊓ MulAut.conj g • Q2 L1 L2 S)
    hA hYS hYe inf_le_left hRY
  have hR : (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A :=
    Subgroup.inf_relIndex_left A (MulAut.conj g • Q2 L1 L2 S)
  rwa [hR] at h

end CFSG.Quasithin.Stroth

end
