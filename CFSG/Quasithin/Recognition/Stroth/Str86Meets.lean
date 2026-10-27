module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBridge
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelFixedComm

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem str86_exists_orth_chief
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4) [Fintype (GaloisField 2 (2 * k))] :
    ∃ (W : Subgroup G) (hWZ2 : W ≤ Z2 L1 L2 S)
      (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
      (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W)
      (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
      (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 (2 * k)))
      (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) (hW : W = Z2 L1 L2 S)
      (l : ℕ) (hl : Fintype.card (GaloisField 2 (2 * k)) = 2 ^ (2 * l)),
      letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hn : 2 ≤ 2 * k := by omega
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  obtain ⟨W, hWZ2, hstepW, hncW⟩ :=
    str86_exists_chiefStep_u3H hF hSB hk hFc hU3 hB2 ⟨2 * k, hL2⟩ hZI
  have h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ (2 * k)) ^ 2 :=
    str86_card_z2_le_sq hF hSB hk hFc hU3 hn hL2 hZQ hB2 hZI
  have hcomm : ⁅Z2 L1 L2 S, H⁆ = W :=
    str86_z2_commutator_eq_chief hF hSB hk hFc hU3 hn hL2 hZQ h376 hstepW hncW hWZ2
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W) :=
    isElemAbelian_chiefMod hstepW hUH (pCoreOf_isPGroup 2 (P2 L1 L2 S))
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  obtain ⟨e₀⟩ := str86_isL2Quot_u3H hF.toW hL2
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 (2 * k)) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 (2 * k)))
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hHP2 : H ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hSylH : IsSylowTwoOf S H :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSleH hHP2
  let Tsub : Subgroup (oTwoQuot ↥H) := CFSG.Quasithin.imageOTwoQuot H S
  have hT2 : IsPGroup 2 Tsub :=
    CFSG.Quasithin.Stroth.isPGroup_imageOTwoQuot_of_isSylow hSylH
  have hTidx : ¬ 2 ∣ Tsub.index :=
    CFSG.Quasithin.Stroth.not_two_dvd_index_imageOTwoQuot hSylH
  let T : Sylow 2 (oTwoQuot ↥H) := hT2.toSylow hTidx
  have hTcoe : (T : Subgroup (oTwoQuot ↥H)) = Tsub := IsPGroup.toSylow_coe hT2 hTidx
  let A : Subgroup (SL(2, GaloisField 2 (2 * k))) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hTcard : Nat.card ↥Tsub = 2 ^ (2 * k) := by
    rw [← hTcoe]
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
  have hAcard : Nat.card A = 2 ^ (2 * k) := by
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥Tsub := by rw [hTcoe]
      _ = 2 ^ (2 * k) := hTcard
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstepW hUH hE e hncW
  have hirr : ρ.IsIrreducible := l2ChiefSectionRep_irreducible hstepW hUH hE e
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hWcardEq : Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
    calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
          Nat.card_congr (chiefModBotMulEquiv W).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
          Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)
  have hWlt : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) < 2 ^ (4 * (2 * k)) := by
    rw [← hWcardEq]
    have hle : Nat.card W ≤ 2 ^ (4 * k) := by
      have hZ2' : Nat.card (Z2 L1 L2 S) = 2 ^ (4 * k) := by
        rw [hZ2]
        norm_num [pow_mul, mul_comm]
      rw [← hZ2']
      exact Subgroup.card_le_of_le hWZ2
    have hlt : 4 * k < 4 * (2 * k) := by omega
    exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by norm_num) hlt)
  have hcardGF : Fintype.card (GaloisField 2 (2 * k)) = 2 ^ (2 * k) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * k) (by omega)
  have htri := isNaturalModule_or_isOrthModule_or_of_card_lt (by omega : 1 ≤ 2 * k) hcardGF
    ρ hnt A hA2 hAcard hWlt
  rcases htri with hnat | ⟨l, hl, hn2l, horth⟩ | ⟨l, hn3l, hWcard3, hfix3⟩
  · have hfix := str86_natural_case_false hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hnat
    exact hfix.elim
  ·
    have hlk : l = k := by
      have h1 : 2 ^ (2 * l) = 2 ^ (2 * k) := by rw [← hl, hcardGF]
      have h2 : 2 * l = 2 * k := Nat.pow_right_injective (by norm_num) h1
      omega
    have hcards := str86_orth_case_cards hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hl horth
    have hWcard : Nat.card W = (2 ^ k) ^ 4 := hcards.2
    have hZ2W : W = Z2 L1 L2 S := by
      refine Subgroup.eq_of_le_of_card_ge hWZ2 ?_
      rw [hZ2, hWcard]
    exact ⟨W, hWZ2, hstepW, hncW, hE, e, hcomm, hZ2W, l, hl, horth⟩
  ·
    exfalso
    have hWle : 2 ^ (8 * l) ≤ 2 ^ (4 * k) := by
      have hWle' : Nat.card W ≤ Nat.card (Z2 L1 L2 S) := Subgroup.card_le_of_le hWZ2
      rw [hWcardEq, hWcard3, hZ2] at hWle'
      have hZ2' : (2 ^ k) ^ 4 = 2 ^ (4 * k) := by norm_num [pow_mul, mul_comm]
      rw [hZ2'] at hWle'
      exact hWle'
    have h8 : 8 * l ≤ 4 * k := Nat.pow_le_pow_iff_right (by norm_num) |>.mp hWle
    omega

end CFSG.Quasithin.Stroth

end

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem mem_commSub_iff_commutator {H U W : Subgroup G} {m : ℕ}
    (hstep : IsChiefStep H U ⊥ W) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hW2 : ∀ w : ↥W, w * w = 1)
    (P : Subgroup ↥H) (hPW : P.map H.subtype ≤ Subgroup.normalizer (W : Set G))
    (w : ↥W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Additive.ofMul (chiefModBotMulEquiv W w) ∈
        CFSG.QuasithinUnique.Setup.X7.commSub (l2ChiefSectionRep hstep hUH hE e)
          ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) ↔
      (w : G) ∈ ⁅W, P.map H.subtype⁆ := by
  classical
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstep hUH hE e
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom
  let θ := chiefModBotMulEquiv W
  let K : Subgroup G := ⁅W, P.map H.subtype⁆
  have hKW : K ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hPW
  let Ksub : Subgroup ↥(Ch3z.chiefMod ⊥ W) := (K.subgroupOf W).map θ.toMonoidHom
  let Kmod : Submodule (ZMod 2) (Additive ↥(Ch3z.chiefMod ⊥ W)) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' Ksub)
  have hmemKmod : ∀ x : ↥W, Additive.ofMul (θ x) ∈ Kmod ↔ (x : G) ∈ K := by
    intro x
    constructor
    · intro hx
      have h2 : Additive.ofMul (θ x) ∈ Subgroup.toAddSubgroup' Ksub :=
        (AddSubgroup.mem_toZModSubmodule 2).mp hx
      have h3 : θ x ∈ Ksub :=
        (Subgroup.mem_toAddSubgroup' Ksub (Additive.ofMul (θ x))).mp h2
      obtain ⟨y, hyK, hyeq⟩ := Subgroup.mem_map.mp h3
      have hyx : y = x := θ.injective hyeq
      rw [hyx] at hyK
      exact Subgroup.mem_subgroupOf.mp hyK
    · intro hx
      have hxK : x ∈ K.subgroupOf W := Subgroup.mem_subgroupOf.mpr hx
      have h3 : θ x ∈ Ksub := Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
      exact (AddSubgroup.mem_toZModSubmodule 2).mpr
        ((Subgroup.mem_toAddSubgroup' Ksub (Additive.ofMul (θ x))).mpr h3)
  constructor
  ·
    intro hw
    have hcomm_le : CFSG.QuasithinUnique.Setup.X7.commSub ρ A ≤ Kmod := by
      change (⨆ a ∈ A, LinearMap.range (ρ a - 1)) ≤ Kmod
      refine iSup_le fun a => iSup_le fun ha => ?_
      rintro v ⟨u, rfl⟩
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu'
      let w' : ↥W := θ.symm (Additive.toMul u)
      have hw' : Additive.ofMul (θ w') = u := by
        dsimp [w', θ]
        rw [MulEquiv.apply_symm_apply]
        rfl
      have hxK : (⁅(w' : G), (p : G)⁆ : G) ∈ K :=
        Subgroup.commutator_mem_commutator w'.2 (Subgroup.mem_map_of_mem H.subtype hp)
      have hxW : (⁅(w' : G), (p : G)⁆ : G) ∈ W := hKW hxK
      have htrans := chiefModBot_commutator_eq (H := H) (U := U) (W := W) (m := m)
        hstep hUH hE e hW2 p w' ⟨⁅(w' : G), (p : G)⁆, hxW⟩ (by rfl)
      rw [hw'] at htrans
      have hgoal : (ρ (e (QuotientGroup.mk p)) - 1) u ∈ Kmod := by
        rw [← htrans]
        exact (hmemKmod ⟨⁅(w' : G), (p : G)⁆, hxW⟩).mpr hxK
      simpa only [QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom] using hgoal
    exact (hmemKmod w).mp (hcomm_le hw)
  ·
    intro hwK
    let Cw : Subgroup ↥W :=
      { carrier := {x | Additive.ofMul (θ x) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A}
        one_mem' := by
          change Additive.ofMul (θ (1 : ↥W)) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          rw [map_one]
          exact (CFSG.QuasithinUnique.Setup.X7.commSub ρ A).zero_mem
        mul_mem' := by
          intro x y hx hy
          change Additive.ofMul (θ (x * y)) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          rw [map_mul]
          change Additive.ofMul (θ x) + Additive.ofMul (θ y) ∈
            CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          exact (CFSG.QuasithinUnique.Setup.X7.commSub ρ A).add_mem hx hy
        inv_mem' := by
          intro x hx
          change Additive.ofMul (θ (x⁻¹)) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          rw [map_inv]
          change -Additive.ofMul (θ x) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          exact (CFSG.QuasithinUnique.Setup.X7.commSub ρ A).neg_mem hx }
    have hKleC : K ≤ Cw.map W.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hb
      have hxK : (⁅a, (p : G)⁆ : G) ∈ K :=
        Subgroup.commutator_mem_commutator ha (Subgroup.mem_map_of_mem H.subtype hp)
      have hxW : (⁅a, (p : G)⁆ : G) ∈ W := hKW hxK
      refine Subgroup.mem_map.mpr ⟨⟨⁅a, (p : G)⁆, hxW⟩, ?_, rfl⟩
      change Additive.ofMul (θ ⟨⁅a, (p : G)⁆, hxW⟩) ∈
        CFSG.QuasithinUnique.Setup.X7.commSub ρ A
      have htrans := chiefModBot_commutator_eq (H := H) (U := U) (W := W) (m := m)
        hstep hUH hE e hW2 p ⟨a, ha⟩ ⟨⁅a, (p : G)⁆, hxW⟩ (by rfl)
      have haA : e (QuotientGroup.mk p) ∈ A :=
        Subgroup.mem_map_of_mem e.toMonoidHom
          (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H)) hp)
      rw [htrans]
      exact range_le_commSub (ρ := ρ) (A := A) haA
        ⟨Additive.ofMul (θ ⟨a, ha⟩), rfl⟩
    obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp (hKleC hwK)
    have hcw : c = w := Subtype.ext hceq
    rw [hcw] at hc
    exact hc

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem u3Y_inf_conj_q2_le_centralizer {L1 L2 S : Subgroup G} {l : G} :
    u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S ≤
      Subgroup.centralizer (MulAut.conj l • u3Y L1 L2 S : Set G) := by
  intro a ha
  obtain ⟨haY, haQ⟩ := Subgroup.mem_inf.mp ha
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hQ2Z2 : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hmap : MulAut.conj l • Q2 L1 L2 S ≤
      Subgroup.centralizer (MulAut.conj l • Z2 L1 L2 S : Set G) := by
    let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj l)
    have h := (Subgroup.map_mono (f := f) hQ2Z2).trans
      (Subgroup.map_centralizer_le_centralizer_image (Z2 L1 L2 S : Set G) f)
    rwa [map_mulDistrib_eq_smul] at h
  have heZ : e ∈ MulAut.conj l • Z2 L1 L2 S :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
      (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S))) he
  exact Subgroup.mem_centralizer_iff.mp (hmap haQ) e heZ

private theorem u3Y_inf_conj_q2_le_centralizer_q2 {L1 L2 S : Subgroup G} {l : G} :
    u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S ≤
      Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
  intro a ha
  obtain ⟨haY, _⟩ := Subgroup.mem_inf.mp ha
  have haZ : a ∈ Z2 L1 L2 S := u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S) haY
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (Subgroup.mem_centralizer_iff.mp
    (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) a haZ).symm

theorem str86_z2_inf_q1_inf_conj_q2_le_z1
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    :
    ∀ h ∈ L1 ⊔ bigB L1 L2 S, h ∉ bigB L1 L2 S →
      (Z2 L1 L2 S ⊓ Q1 L1 L2 S) ⊓
        (Q1 L1 L2 S ⊓ (MulAut.conj h • Q2 L1 L2 S)) ≤ Z1 L1 L2 S := by
  classical
  intro h hh hhB
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  obtain ⟨l, hlL1, b, hbB, hlb⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hh
  have hlB : l ∉ bigB L1 L2 S := by
    intro hl
    exact hhB (hlb ▸ (bigB L1 L2 S).mul_mem hl hbB)
  have hbQ2N : b ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
      ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hbB)
  have hbQ2 : MulAut.conj b • Q2 L1 L2 S = Q2 L1 L2 S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hbQ2N
  have hhQ2 : MulAut.conj h • Q2 L1 L2 S = MulAut.conj l • Q2 L1 L2 S := by
    calc MulAut.conj h • Q2 L1 L2 S
        = MulAut.conj (l * b) • Q2 L1 L2 S := by rw [hlb]
      _ = MulAut.conj l • (MulAut.conj b • Q2 L1 L2 S) := by rw [map_mul, mul_smul]
      _ = MulAut.conj l • Q2 L1 L2 S := by rw [hbQ2]
  have hAle : (Z2 L1 L2 S ⊓ Q1 L1 L2 S) ⊓
      (Q1 L1 L2 S ⊓ (MulAut.conj h • Q2 L1 L2 S)) ≤
        u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S := by
    rw [show (Z2 L1 L2 S ⊓ Q1 L1 L2 S) = u3Y L1 L2 S from rfl, hhQ2]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hcentY := u3Y_inf_conj_q2_le_centralizer (L1 := L1) (L2 := L2) (S := S) (l := l)
  have hcentQ2 := u3Y_inf_conj_q2_le_centralizer_q2 (L1 := L1) (L2 := L2) (S := S) (l := l)
  have hlsup : MulAut.conj l • u3Y L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_u3Y_conj_sup_q2 hF hSB hk hFc hU3 (by omega : 2 ≤ 2 * k) hL2 hZQ
      (Subgroup.mem_sup_left hlL1) hlB
  have hcentS : u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S ≤
      Subgroup.centralizer (S : Set G) := by
    have h : u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S ≤
        Subgroup.centralizer
          (((MulAut.conj l • u3Y L1 L2 S) ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
      rw [CFSG.centralizer_sup_eq]
      exact le_inf hcentY hcentQ2
    rwa [hlsup] at h
  have hAZ1 : u3Y L1 L2 S ⊓ MulAut.conj l • Q2 L1 L2 S ≤ Z1 L1 L2 S := by
    have hZ2S : Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S :=
      (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.2.2.2
    rw [← hZ2S]
    exact le_inf (inf_le_left.trans (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S))) hcentS
  exact hAle.trans hAZ1

theorem str86_z1_inf_conj_q1_eq_bot
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    :
    ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
      Z1 L1 L2 S ⊓ (MulAut.conj g • Q1 L1 L2 S) = ⊥ := by
  classical
  haveI : Fintype (GaloisField 2 (2 * k)) := Fintype.ofFinite _
  obtain ⟨W, hWZ2, hstepW, hncW, hE, e, hcomm, hZ2W, l, hl, horth⟩ :=
    str86_exists_orth_chief hF hSB hk hFc hU3 hB2 hL2 hZI hZQ hZ2
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  let θ := chiefModBotMulEquiv W
  have hn : 2 ≤ 2 * k := by omega
  have hcardGF : Fintype.card (GaloisField 2 (2 * k)) = 2 ^ (2 * k) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * k) (by omega)
  have hlk : l = k := by
    have h1 : 2 ^ (2 * l) = 2 ^ (2 * k) := by rw [← hl, hcardGF]
    have h2 : 2 * l = 2 * k := Nat.pow_right_injective (by norm_num) h1
    omega
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hcase := str86_caseI_basics hF hSB h1 hB2 ⟨2 * k, hL2⟩ hZI
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := hcase.2.1
  have hZ2C : Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := hcase.2.2.2.2
  have hZ1W : Z1 L1 L2 S ≤ W := by rw [hZ2W]; exact hZ1Z2
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hQ1sup : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf hF.toW hSB (Or.inr h1) hn hL2
  have hSylH : IsSylowTwoOf S H :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSleH
      (u3H_le_p2 L1 L2 S)
  let Tsub : Subgroup (oTwoQuot ↥H) := CFSG.Quasithin.imageOTwoQuot H S
  have hT2 : IsPGroup 2 Tsub :=
    CFSG.Quasithin.Stroth.isPGroup_imageOTwoQuot_of_isSylow hSylH
  have hTidx : ¬ 2 ∣ Tsub.index :=
    CFSG.Quasithin.Stroth.not_two_dvd_index_imageOTwoQuot hSylH
  let T : Sylow 2 (oTwoQuot ↥H) := hT2.toSylow hTidx
  have hTcoe : (T : Subgroup (oTwoQuot ↥H)) = Tsub := IsPGroup.toSylow_coe hT2 hTidx
  let A : Subgroup (SL(2, GaloisField 2 (2 * k))) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hTcard : Nat.card ↥Tsub = 2 ^ (2 * k) := by
    rw [← hTcoe]
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
  have hAcard : Nat.card A = 2 ^ (2 * k) := by
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥Tsub := by rw [hTcoe]
      _ = 2 ^ (2 * k) := hTcard
  have hAcard_l : Nat.card A = 2 ^ (2 * l) := by rw [hlk, hAcard]
  have hW2 : ∀ w : ↥W, w * w = 1 := by
    intro w
    apply Subtype.ext
    have hwZ : (w : G) ∈ Z2 L1 L2 S := by rw [← hZ2W]; exact w.2
    simpa [pow_two] using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 (w : G) hwZ
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hZ2W]
    exact le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S)
  have hPW : (S.subgroupOf H).map H.subtype ≤ Subgroup.normalizer (W : Set G) := by
    rwa [Subgroup.map_subgroupOf_eq_of_le hSleH]
  have hAsub : ((S.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom = A := by
    dsimp [A, Tsub]
    rw [hTcoe]
    rfl
  have hiffS : ∀ w : ↥W, Additive.ofMul (θ w) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A ↔
      (w : G) ∈ ⁅W, S⁆ := by
    intro w
    have h := mem_commSub_iff_commutator hstepW (q2_le_u3H L1 L2 S) hE e hW2 (S.subgroupOf H) hPW w
    rw [hAsub, Subgroup.map_subgroupOf_eq_of_le hSleH] at h
    exact h
  let K : Subgroup G := ⁅W, S⁆
  have hKW : K ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hSW
  let eK : ↥K ≃ ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) :=
    { toFun := fun x =>
        ⟨Additive.ofMul (θ ⟨x.1, hKW x.2⟩), (hiffS ⟨x.1, hKW x.2⟩).mpr x.2⟩
      invFun := fun v =>
        let w : ↥W := θ.symm (Additive.toMul v.1)
        have hw : Additive.ofMul (θ w) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A := by
          have h1 : Additive.ofMul (θ w) = v.1 := by
            dsimp [w]
            rw [MulEquiv.apply_symm_apply]
            rfl
          simpa [h1] using v.2
        ⟨(w : G), (hiffS w).mp hw⟩
      left_inv := by
        intro x
        apply Subtype.ext
        dsimp
        rw [MulEquiv.symm_apply_apply]
      right_inv := by
        intro v
        apply Subtype.ext
        dsimp
        rw [MulEquiv.apply_symm_apply]
        rfl }
  have hcardK : Nat.card ↥K = Nat.card ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) :=
    Nat.card_congr eK
  have hcommSubCard : Nat.card ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) = 2 ^ (3 * l) :=
    IsOrthModule.card_commSub (hF := hl) horth A hA2 hAcard_l
  have hKcard : Nat.card ↥K = (2 ^ k) ^ 3 := by
    rw [hcardK, hcommSubCard, hlk]
    rw [show 3 * k = k * 3 by ring, pow_mul]
  have hKleY : K ≤ u3Y L1 L2 S := by
    dsimp [K]
    rw [hZ2W]
    exact commutator_z2_s_le_u3Y hF hQ1sup
  have hYcard : Nat.card ↥(u3Y L1 L2 S) = (2 ^ k) ^ 3 := by
    simpa [u3Y] using hY
  have hYleK : Nat.card ↥(u3Y L1 L2 S) ≤ Nat.card ↥K := by rw [hYcard, hKcard]
  have hYeqK : u3Y L1 L2 S = K := (Subgroup.eq_of_le_of_card_ge hKleY hYleK).symm
  have hP2L2 : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer (by
      simpa [bigB_comm] using bigB_le_normalizer_of_hyp111 hF.1.symm)
  have hP2Q2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hP2H : P2 L1 L2 S ≤ Subgroup.normalizer (H : Set G) := by
    refine (le_inf hP2L2 hP2Q2).trans ?_
    simpa [H, u3H] using
      (Subgroup.inf_normalizer_le_normalizer_sup (L2 : Subgroup G) (Q2 L1 L2 S))
  have hP2N : P2 L1 L2 S ⊓ Subgroup.normalizer (S : Set G) ≤ bigB L1 L2 S := by
    have hSB' : bigB L2 L1 S ≤ Subgroup.normalizer (S : Set G) := by
      rw [bigB_comm]; exact hSB
    have h := str86_p1_inf_normalizer_le_bigB (L1 := L2) (L2 := L1) (S := S)
      (F112Hyp.symm hF).toW hSB'
    simpa [P1, P2, bigB_comm L1 L2 S] using h
  intro g hg hgB
  have hgP2 : g ∈ P2 L1 L2 S := hg
  have hgH : g ∈ Subgroup.normalizer (H : Set G) := hP2H hgP2
  have hgZ2 : g ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)) hgP2
  have hgW : g ∈ Subgroup.normalizer (W : Set G) := by
    rw [hZ2W]; exact hgZ2
  have hgQ2 : g ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) hgP2
  have hgQ2eq : MulAut.conj g • Q2 L1 L2 S = Q2 L1 L2 S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgQ2
  let S' : Subgroup G := conjSub g S
  have hconjH : conjSub g H = H := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgH
  have hS'leH : S' ≤ H :=
    (conjSub_mono g hSleH).trans (le_of_eq hconjH)
  have hSylS' : IsSylowTwoOf S' H := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hSylH g
    rwa [hconjH] at h
  let Tsub' : Subgroup (oTwoQuot ↥H) := CFSG.Quasithin.imageOTwoQuot H S'
  have hT2' : IsPGroup 2 Tsub' :=
    CFSG.Quasithin.Stroth.isPGroup_imageOTwoQuot_of_isSylow hSylS'
  have hTidx' : ¬ 2 ∣ Tsub'.index :=
    CFSG.Quasithin.Stroth.not_two_dvd_index_imageOTwoQuot hSylS'
  let T' : Sylow 2 (oTwoQuot ↥H) := hT2'.toSylow hTidx'
  have hTcoe' : (T' : Subgroup (oTwoQuot ↥H)) = Tsub' := IsPGroup.toSylow_coe hT2' hTidx'
  let A' : Subgroup (SL(2, GaloisField 2 (2 * k))) := (T' : Subgroup _).map e.toMonoidHom
  have hA2' : ∀ a ∈ A', a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T').1 t ht
    rw [ht2, map_one]
  have hTcard' : Nat.card ↥Tsub' = 2 ^ (2 * k) := by
    rw [← hTcoe']
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T').2
  have hAcard' : Nat.card A' = 2 ^ (2 * k) := by
    calc Nat.card A' = Nat.card ↥(T' : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥Tsub' := by rw [hTcoe']
      _ = 2 ^ (2 * k) := hTcard'
  have hAcard_l' : Nat.card A' = 2 ^ (2 * l) := by rw [hlk, hAcard']
  have hAA' : A ≠ A' := by
    intro hEq
    have hTTeq : (T : Subgroup (oTwoQuot ↥H)) = (T' : Subgroup (oTwoQuot ↥H)) :=
      Subgroup.map_injective e.injective hEq
    have hTsubeq : Tsub = Tsub' := by rw [← hTcoe, ← hTcoe']; exact hTTeq
    have hQ2S : Q2 L1 L2 S ≤ S :=
      CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
    have hQ2S' : Q2 L1 L2 S ≤ S' := by
      calc Q2 L1 L2 S = conjSub g (Q2 L1 L2 S) := by
            simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgQ2).symm
        _ ≤ conjSub g S := conjSub_mono g hQ2S
    have hcomap : (CFSG.Quasithin.imageOTwoQuot H S).comap
        (QuotientGroup.mk' (pCore 2 ↥H)) =
        (CFSG.Quasithin.imageOTwoQuot H S').comap
          (QuotientGroup.mk' (pCore 2 ↥H)) := by
      rw [show CFSG.Quasithin.imageOTwoQuot H S = Tsub from rfl,
        show CFSG.Quasithin.imageOTwoQuot H S' = Tsub' from rfl, hTsubeq]
    have hOX : pCoreOf 2 H ≤ S := by
      rw [show pCoreOf 2 H = Q2 L1 L2 S from str86_pCoreOf_u3H hF.toW]
      exact hQ2S
    have hOX' : pCoreOf 2 H ≤ S' := by
      rw [show pCoreOf 2 H = Q2 L1 L2 S from str86_pCoreOf_u3H hF.toW]
      exact hQ2S'
    rw [imageOTwoQuot_comap (H := H) hOX, imageOTwoQuot_comap (H := H) hOX'] at hcomap
    have hSS' : S = S' := by
      have h := Subgroup.subgroupOf_inj.mp hcomap
      rwa [inf_eq_left.mpr hSleH, inf_eq_left.mpr hS'leH] at h
    have hgN : g ∈ Subgroup.normalizer (S : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hSS'.symm
    exact hgB (hP2N (Subgroup.mem_inf.mpr ⟨hgP2, hgN⟩))
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hZ2W]
    exact le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S)
  have hSW' : S' ≤ Subgroup.normalizer (W : Set G) := by
    have hgNNW : g ∈ Subgroup.normalizer
        ((Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hgW
    calc S' = conjSub g S := rfl
      _ ≤ conjSub g (Subgroup.normalizer (W : Set G)) := conjSub_mono g hSW
      _ = Subgroup.normalizer (W : Set G) := by
          simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNNW
  have hPW : (S.subgroupOf H).map H.subtype ≤ Subgroup.normalizer (W : Set G) := by
    rwa [Subgroup.map_subgroupOf_eq_of_le hSleH]
  have hPW' : (S'.subgroupOf H).map H.subtype ≤ Subgroup.normalizer (W : Set G) := by
    rwa [Subgroup.map_subgroupOf_eq_of_le hS'leH]
  have hAsub' :
      ((S'.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom = A' := by
    dsimp [A', Tsub']
    rw [hTcoe']
    rfl
  have hiffS' : ∀ w : ↥W, Additive.ofMul (θ w) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A' ↔
      (w : G) ∈ ⁅W, S'⁆ := by
    intro w
    have h := mem_commSub_iff_commutator hstepW (q2_le_u3H L1 L2 S) hE e hW2 (S'.subgroupOf H)
      hPW' w
    rw [hAsub', Subgroup.map_subgroupOf_eq_of_le hS'leH] at h
    exact h
  have hdisj : fixedSub ρ A ⊓ CFSG.QuasithinUnique.Setup.X7.commSub ρ A' = ⊥ :=
    IsOrthModule.fixedSub_inf_commSub_eq_bot (hF := hl) horth hA2 hAcard_l hA2' hAcard_l' hAA'
  have hconjK : conjSub g K = ⁅W, S'⁆ := by
    rw [show K = ⁅W, S⁆ from rfl, conjSub, Subgroup.map_commutator]
    change ⁅conjSub g W, conjSub g S⁆ = ⁅W, S'⁆
    rw [show conjSub g W = W from by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgW]
  refine eq_bot_iff.mpr ?_
  intro z hz
  obtain ⟨hzZ1, hzgQ1⟩ := Subgroup.mem_inf.mp hz
  have hzW : z ∈ W := hZ1W hzZ1
  have hzC : z ∈ Subgroup.centralizer (S : Set G) := by
    have hzinf : z ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) := by
      rw [hZ2C]; exact hzZ1
    exact (Subgroup.mem_inf.mp hzinf).2
  have hfixA : Additive.ofMul (θ ⟨z, hzW⟩) ∈ fixedSub ρ A := by
    have h := (mem_fixSub_chiefMod_bot_iff hstepW hUH hE e (S.subgroupOf H) ⟨z, hzW⟩).mpr ?_
    · rw [hAsub] at h
      exact h
    · rwa [Subgroup.map_subgroupOf_eq_of_le hSleH]
  have hginvQ1 : g⁻¹ * z * g ∈ Q1 L1 L2 S := by
    have hzgQ1' : z ∈ Subgroup.map
        ((MulDistribMulAction.toMonoidEnd (MulAut G) G) (MulAut.conj g))
        (Q1 L1 L2 S) := by
      simpa [Subgroup.pointwise_smul_def] using hzgQ1
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hzgQ1'
    have hq' : g⁻¹ * z * g = q := by
      rw [← hqeq]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hq']; exact hq
  have hginvW : g⁻¹ * z * g ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (W : Set G)).inv_mem hgW) z).mp hzW
    simpa [mul_assoc] using h
  have hginvWZ : g⁻¹ * z * g ∈ Z2 L1 L2 S := by
    rwa [hZ2W] at hginvW
  have hginvY : g⁻¹ * z * g ∈ u3Y L1 L2 S := by
    rw [u3Y]
    exact Subgroup.mem_inf.mpr ⟨hginvWZ, hginvQ1⟩
  have hginvK : g⁻¹ * z * g ∈ K := by
    rw [← hYeqK]; exact hginvY
  have hzK' : z ∈ ⁅W, S'⁆ := by
    rw [← hconjK]
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, hginvK, ?_⟩
    simp [conjSub, MulAut.conj_apply, mul_assoc]
  have hcommA' : Additive.ofMul (θ ⟨z, hzW⟩) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A' :=
    (hiffS' ⟨z, hzW⟩).mpr hzK'
  have hbot : Additive.ofMul (θ ⟨z, hzW⟩) ∈
      (⊥ : Submodule (ZMod 2) (Additive ↥(Ch3z.chiefMod ⊥ W))) := by
    rw [← hdisj]
    exact Submodule.mem_inf.mpr ⟨hfixA, hcommA'⟩
  have hzero : Additive.ofMul (θ ⟨z, hzW⟩) = 0 := by simpa using hbot
  have h1 : θ ⟨z, hzW⟩ = 1 := Additive.ofMul.injective (by simpa using hzero)
  have h2 : (⟨z, hzW⟩ : ↥W) = 1 := θ.injective (by simpa using h1)
  have hz1 : z = 1 := congrArg Subtype.val h2
  exact Subgroup.mem_bot.mpr hz1

end CFSG.Quasithin.Stroth
