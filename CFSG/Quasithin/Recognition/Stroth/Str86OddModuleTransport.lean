module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleFrame
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans2
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalInvariant
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelInvariant

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_orth_pow_mul_relIndex_le {L1 L2 S : Subgroup G}
    {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {D : Subgroup G} (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S) :
    2 ^ l * (Q2 L1 L2 S).relIndex D ≤ (Subgroup.centralizer (D : Set G)).relIndex W := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let Abar : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom
  let Dbar : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom
  have hSu : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  have hDU : D ≤ u3H L1 L2 S := hDS.trans hSu
  have hDA : Dbar ≤ Abar :=
    Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hDS))
  have hA2 : ∀ a ∈ Abar, a * a = 1 := (str86_imageS_props hF hSB hm hL2 e).1
  have hAcard : Nat.card Abar = 2 ^ (2 * l) := by
    rw [(str86_imageS_props hF hSB hm hL2 e).2, hml]
  have hDcard : Nat.card Dbar = (Q2 L1 L2 S).relIndex D := by
    rw [show Dbar = (imageOTwoQuot (u3H L1 L2 S) D).map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.injective]
    exact str86_card_imageOTwoQuot_u3H hF hDU
  have hDgt : 1 < Nat.card Dbar := by
    rw [hDcard]
    have hne1 : (Q2 L1 L2 S).relIndex D ≠ 1 :=
      fun h => hDQ ((Subgroup.relIndex_eq_one).mp h)
    have hpos : 0 < (Q2 L1 L2 S).relIndex D :=
      Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    omega
  have hDne : Dbar ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (H := Dbar)).mp hDgt
  have hM2 := IsOrthModule.pow_mul_card_mul_card_fixedSub_le (hF := hl) horth
    (A := Abar) (D := Dbar) hA2 hAcard hDA hDne
  have hH2 := str86_card_fixedSub_image (hstepW := hstepW) hE e hDU
  have hWcardEq : Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
    calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
          Nat.card_congr (chiefModBotMulEquiv W).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
          Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)
  have hineq : 2 ^ l * (Q2 L1 L2 S).relIndex D *
      Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) ≤ Nat.card W := by
    have h := hM2
    rw [hDcard, hH2, ← hWcardEq] at h
    simpa [mul_assoc] using h
  have hmul := Subgroup.relIndex_mul_card
    (H := Subgroup.centralizer (D : Set G)) (K := W)
  rw [inf_comm] at hmul
  have hc : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) := Nat.card_pos
  have hmain : 2 ^ l * (Q2 L1 L2 S).relIndex D *
      Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) ≤
      (Subgroup.centralizer (D : Set G)).relIndex W *
        Nat.card ↥(W ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hmul]
    exact hineq
  exact Nat.le_of_mul_le_mul_right hmain hc

theorem str86_orth_pow_mul_relIndex_le_conj
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {g : G} {D : Subgroup G} (hDS : D ≤ MulAut.conj g • S)
    (hDQ : ¬ D ≤ MulAut.conj g • Q2 L1 L2 S) :
    2 ^ l * (MulAut.conj g • Q2 L1 L2 S).relIndex D ≤
      (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
  let D' : Subgroup G := MulAut.conj g⁻¹ • D
  have hDg : MulAut.conj g • D' = D := by
    change MulAut.conj g • (MulAut.conj g⁻¹ • D) = D
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hDS' : D' ≤ S := by
    calc D' = MulAut.conj g⁻¹ • D := rfl
      _ ≤ MulAut.conj g⁻¹ • (MulAut.conj g • S) := Subgroup.map_mono hDS
      _ = S := by rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hDQ' : ¬ D' ≤ Q2 L1 L2 S := by
    intro h
    apply hDQ
    calc D = MulAut.conj g • D' := hDg.symm
      _ ≤ MulAut.conj g • Q2 L1 L2 S := Subgroup.map_mono h
  have hT1 := str86_orth_pow_mul_relIndex_le hF hSB hm hL2 hstepW hE e hl hml horth
    hDS' hDQ'
  have hcc : Subgroup.centralizer (D : Set G) =
      MulAut.conj g • Subgroup.centralizer (D' : Set G) := by
    rw [smul_centralizer, ← Subgroup.coe_pointwise_smul, hDg]
  have hq : (MulAut.conj g • Q2 L1 L2 S).relIndex D =
      (Q2 L1 L2 S).relIndex D' := by
    rw [show D = MulAut.conj g • D' from hDg.symm]
    exact Subgroup.relIndex_pointwise_smul (MulAut.conj g) (Q2 L1 L2 S) D'
  have hstep1 : (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • W) =
      (Subgroup.centralizer (D' : Set G)).relIndex W := by
    rw [hcc]
    exact Subgroup.relIndex_pointwise_smul (MulAut.conj g)
      (Subgroup.centralizer (D' : Set G)) W
  have hWZ2g : MulAut.conj g • W ≤ MulAut.conj g • Z2 L1 L2 S :=
    Subgroup.map_mono hWZ2
  have hstep2 : (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • W) ≤
      (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
    rw [hcc]
    exact Subgroup.relIndex_le_of_le_right hWZ2g (D15Proof.relIndex_ne_zero _ _)
  calc 2 ^ l * (MulAut.conj g • Q2 L1 L2 S).relIndex D
      = 2 ^ l * (Q2 L1 L2 S).relIndex D' := by rw [hq]
    _ ≤ (Subgroup.centralizer (D' : Set G)).relIndex W := hT1
    _ = (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • W) := hstep1.symm
    _ ≤ (Subgroup.centralizer (D : Set G)).relIndex (MulAut.conj g • Z2 L1 L2 S) := hstep2

private theorem t2_invariant {L1 L2 S X W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ v : Additive (Ch3z.chiefMod ⊥ W), v ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧ v = Additive.ofMul (chiefModBotMulEquiv W w)) →
      ∀ n ∈ Subgroup.normalizer
        (((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :
          Subgroup (SL(2, GaloisField 2 m))) : Set (SL(2, GaloisField 2 m))),
        ∀ u ∈ U, (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e) n u ∈ U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem n hn u hu
  let θ := chiefModBotMulEquiv W
  rw [hUmem] at hu ⊢
  obtain ⟨w, hwX, rfl⟩ := hu
  obtain ⟨h, hhB, hhe⟩ := str86_exists_bigB_lift hF hSB hm hL2 e hn
  rw [← hhe]
  rw [l2ChiefSectionRep_apply_mk hstepW (q2_le_u3H L1 L2 S) hE e h (θ w)]
  rw [chiefModBotMulEquiv_conj hstepW (q2_le_u3H L1 L2 S) hE h w]
  refine ⟨⟨(h : G) * (w : G) * (h : G)⁻¹, ?_⟩, ?_, rfl⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      ((D14.le_normalizer_of_isNormalIn hstepW.1) h.2) (w : G)).mp w.2
  · exact (Subgroup.mem_normalizer_iff.mp (hXB hhB) (w : G)).mp hwX

private theorem t2_fixedSub_lt {L1 L2 S X W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    (hXW : X ≤ W) (hZX : Z1 L1 L2 S ≤ X) (hXZ : X ≠ Z1 L1 L2 S) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ v : Additive (Ch3z.chiefMod ⊥ W), v ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧ v = Additive.ofMul (chiefModBotMulEquiv W w)) →
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) < U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem
  let θ := chiefModBotMulEquiv W
  let ρ := l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom
  have hD : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  have hfixmem : ∀ w : ↥W, Additive.ofMul (θ w) ∈ fixedSub ρ A ↔
      (w : G) ∈ Subgroup.centralizer (S : Set G) :=
    fun w => str86_mem_fixedSub_image_iff hstepW hE e hD w
  have hle : fixedSub ρ A ≤ U := by
    intro v hv
    rw [hUmem]
    let w : ↥W := θ.symm (Additive.toMul v)
    have hwv : v = Additive.ofMul (θ w) := by simp [w, θ]
    refine ⟨w, ?_, hwv⟩
    have hfix : Additive.ofMul (θ w) ∈ fixedSub ρ A := hwv ▸ hv
    have hcent : (w : G) ∈ Subgroup.centralizer (S : Set G) := (hfixmem w).mp hfix
    have hmem : (w : G) ∈ W ⊓ Subgroup.centralizer (S : Set G) :=
      Subgroup.mem_inf.mpr ⟨w.2, hcent⟩
    rw [hWS] at hmem
    exact hZX hmem
  have hne : fixedSub ρ A ≠ U := by
    intro heq
    have hnot : ¬ X ≤ Z1 L1 L2 S := fun h => hXZ (le_antisymm h hZX)
    obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp hnot
    let w : ↥W := ⟨x, hXW hxX⟩
    have hUmem' : Additive.ofMul (θ w) ∈ U := (hUmem _).mpr ⟨w, hxX, rfl⟩
    have hfix : Additive.ofMul (θ w) ∈ fixedSub ρ A := by
      rw [heq]
      exact hUmem'
    have hcent : (w : G) ∈ Subgroup.centralizer (S : Set G) := (hfixmem w).mp hfix
    have hmem : (w : G) ∈ W ⊓ Subgroup.centralizer (S : Set G) :=
      Subgroup.mem_inf.mpr ⟨w.2, hcent⟩
    rw [hWS] at hmem
    exact hxZ (by simpa using hmem)
  exact lt_of_le_of_ne hle hne

private theorem t2s_exists_submodule {W X : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) (hXW : X ≤ W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∃ U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)),
      (∀ v : Additive (Ch3z.chiefMod ⊥ W), v ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧ v = Additive.ofMul (chiefModBotMulEquiv W w)) ∧
      Nat.card U = Nat.card X := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let θ := chiefModBotMulEquiv W
  let θadd : Additive ↥W →+ Additive (Ch3z.chiefMod ⊥ W) :=
    { toFun := fun x => Additive.ofMul (θ (Additive.toMul x))
      map_zero' := by simp [θ]
      map_add' := by
        intro x y
        simp only [toMul_add, map_mul, ofMul_mul] }
  have hθinj : Function.Injective θadd := fun x y hxy =>
    Additive.toMul.injective (θ.injective (Additive.ofMul.injective hxy))
  let Uadd : AddSubgroup (Additive (Ch3z.chiefMod ⊥ W)) :=
    (Subgroup.toAddSubgroup (X.subgroupOf W)).map θadd
  let U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) :=
    AddSubgroup.toZModSubmodule 2 Uadd
  have hUmem : ∀ v : Additive (Ch3z.chiefMod ⊥ W), v ∈ U ↔
      ∃ w : ↥W, (w : G) ∈ X ∧ v = Additive.ofMul (θ w) := by
    intro v
    rw [show U = AddSubgroup.toZModSubmodule 2 Uadd from rfl,
      AddSubgroup.mem_toZModSubmodule]
    constructor
    · intro hv
      obtain ⟨y, hy, hyv⟩ := AddSubgroup.mem_map.mp hv
      refine ⟨Additive.toMul y, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp
          ((Additive.mem_toAddSubgroup (X.subgroupOf W) y).1 hy)
      · rw [← hyv]
        rfl
    · rintro ⟨w, hwX, rfl⟩
      refine AddSubgroup.mem_map.mpr ⟨Additive.ofMul w, ?_, rfl⟩
      exact (Additive.mem_toAddSubgroup (X.subgroupOf W) _).2
        (Subgroup.mem_subgroupOf.mpr hwX)
  have hcardUadd : Nat.card Uadd = Nat.card X := by
    rw [show Uadd = (Subgroup.toAddSubgroup (X.subgroupOf W)).map θadd from rfl,
      AddSubgroup.card_map_of_injective hθinj]
    calc Nat.card ↥(Subgroup.toAddSubgroup (X.subgroupOf W))
        = Nat.card ↥(X.subgroupOf W) := Nat.card_congr
          { toFun := fun y => ⟨Additive.toMul y.1,
              (Additive.mem_toAddSubgroup (X.subgroupOf W) y.1).1 y.2⟩
            invFun := fun x => ⟨Additive.ofMul (x : ↥W),
              (Additive.mem_toAddSubgroup (X.subgroupOf W) _).2 x.2⟩
            left_inv := fun y => Subtype.ext rfl
            right_inv := fun x => Subtype.ext rfl }
      _ = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXW).toEquiv
  exact ⟨U, hUmem, by
    rw [show U = AddSubgroup.toZModSubmodule 2 Uadd from rfl,
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun x => AddSubgroup.mem_toZModSubmodule 2))]
    exact hcardUadd⟩

theorem str86_orth_card_le_of_bigB_invariant
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    {X : Subgroup G} (hXW : X ≤ W) (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    (hZX : Z1 L1 L2 S ≤ X) (hXZ : X ≠ Z1 L1 L2 S) :
    Nat.card W ≤ 2 ^ l * Nat.card X := by
  classical
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have horth' : IsOrthModule hl ρ := horth
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom
  have hSprops := str86_imageS_props hF hSB hm hL2 e
  have hA2 : ∀ a ∈ A, a * a = 1 := hSprops.1
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    rw [← hml]
    exact hSprops.2
  obtain ⟨U, hUmem, hcardU⟩ := t2s_exists_submodule hE hXW
  have hUinv : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, GaloisField 2 m))),
      ∀ u ∈ U, ρ n u ∈ U :=
    t2_invariant hF hSB hm hL2 hstepW hE e hXB U hUmem
  have hlt : fixedSub ρ A < U :=
    t2_fixedSub_lt hF hSB hm hL2 hstepW hE e hWS hXW hZX hXZ U hUmem
  have hM3c := IsOrthModule.card_le_of_normalizer_invariant (l := l)
    (W := Additive (Ch3z.chiefMod ⊥ W)) hl horth' hA2 hAcard (U := U) hUinv hlt
  calc Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
        calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
              Nat.card_congr (chiefModBotMulEquiv W).toEquiv
          _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
              (Nat.card_congr (Additive.ofMul :
                Ch3z.chiefMod ⊥ W ≃ Additive (Ch3z.chiefMod ⊥ W))).symm
    _ ≤ 2 ^ l * Nat.card U := hM3c
    _ = 2 ^ l * Nat.card X := by rw [hcardU]

private theorem t3s_mem_image {X W : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ x : Additive (Ch3z.chiefMod ⊥ W),
      x ∈ AddSubgroup.toZModSubmodule (n := 2)
        (Subgroup.toAddSubgroup
          ((X.subgroupOf W).map (chiefModBotMulEquiv W).toMonoidHom)) ↔
      ∃ w : ↥W, (w : G) ∈ X ∧
        Additive.ofMul (chiefModBotMulEquiv W w) = x := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro x
  rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwx⟩
    exact ⟨w, Subgroup.mem_subgroupOf.mp hw, by simpa using congrArg Additive.ofMul hwx⟩
  · rintro ⟨w, hw, hwx⟩
    exact ⟨w, Subgroup.mem_subgroupOf.mpr hw, hwx⟩

private theorem t3s_fixedSub_le {L1 L2 S X W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    (hZX : Z1 L1 L2 S ≤ X) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ x : Additive (Ch3z.chiefMod ⊥ W), x ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧
          Additive.ofMul (chiefModBotMulEquiv W w) = x) →
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) ≤ U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem x hx
  have hSle : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  let w : ↥W := (chiefModBotMulEquiv W).symm (Additive.toMul x)
  have hxw : Additive.ofMul (chiefModBotMulEquiv W w) = x := by
    rw [show chiefModBotMulEquiv W w = Additive.toMul x from
      MulEquiv.apply_symm_apply _ _, ofMul_toMul]
  rw [← hxw] at hx
  have hcent : (w : G) ∈ Subgroup.centralizer (S : Set G) :=
    (str86_mem_fixedSub_image_iff (D := S) hstepW hE e hSle w).mp hx
  have hwZ1 : (w : G) ∈ Z1 L1 L2 S := by
    rw [← hWS]
    exact Subgroup.mem_inf.mpr ⟨w.2, hcent⟩
  exact (hUmem _).mpr ⟨w, hZX hwZ1, hxw⟩

private theorem t3s_fixedSub_ne {L1 L2 S X W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    (hXW : X ≤ W) (hZX : Z1 L1 L2 S ≤ X) (hXZ : X ≠ Z1 L1 L2 S) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ x : Additive (Ch3z.chiefMod ⊥ W), x ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧
          Additive.ofMul (chiefModBotMulEquiv W w) = x) →
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) ≠ U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem heq
  have hSle : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  apply hXZ
  refine le_antisymm ?_ hZX
  intro y hyX
  have hyW : y ∈ W := hXW hyX
  have hmem : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈
      fixedSub (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)
        ((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom) :=
    heq ▸ ((hUmem _).mpr ⟨⟨y, hyW⟩, hyX, rfl⟩)
  have hcent : y ∈ Subgroup.centralizer (S : Set G) :=
    (str86_mem_fixedSub_image_iff (D := S) hstepW hE e hSle ⟨y, hyW⟩).mp hmem
  have hyZ1 : y ∈ Z1 L1 L2 S := by
    rw [← hWS]
    exact Subgroup.mem_inf.mpr ⟨hyW, hcent⟩
  exact hyZ1

private theorem t3s_normalizer_invariant {L1 L2 S X W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ x : Additive (Ch3z.chiefMod ⊥ W), x ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧
          Additive.ofMul (chiefModBotMulEquiv W w) = x) →
      ∀ n ∈ Subgroup.normalizer
        (((imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom :
          Subgroup (SL(2, GaloisField 2 m))) : Set (SL(2, GaloisField 2 m))),
        ∀ x ∈ U, (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e) n x ∈ U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem n hn x hx
  obtain ⟨w, hwX, hwx⟩ := (hUmem x).mp hx
  obtain ⟨h, hhB, hhn⟩ := str86_exists_bigB_lift hF hSB hm hL2 e hn
  have hconj : (h : G) * (w : G) * (h : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hXB hhB) (w : G)).mp hwX
  have h1 : l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e n
        (Additive.ofMul (chiefModBotMulEquiv W w)) =
      Additive.ofMul (chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            ((D14.le_normalizer_of_isNormalIn hstepW.1) h.2) (w : G)).mp w.2⟩) := by
    rw [← hhn,
      l2ChiefSectionRep_apply_mk hstepW (q2_le_u3H L1 L2 S) hE e h (chiefModBotMulEquiv W w)]
    rw [chiefModBotMulEquiv_conj hstepW (q2_le_u3H L1 L2 S) hE h w]
  rw [← hwx, h1]
  exact (hUmem _).mpr ⟨_, hconj, rfl⟩

private theorem t3s_eq_of_image_eq_top {X W : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) (hXW : X ≤ W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ (U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W))),
      (∀ x : Additive (Ch3z.chiefMod ⊥ W), x ∈ U ↔
        ∃ w : ↥W, (w : G) ∈ X ∧
          Additive.ofMul (chiefModBotMulEquiv W w) = x) →
      U = ⊤ → X = W := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro U hUmem htop
  refine le_antisymm hXW ?_
  intro y hyW
  have hmem : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈ U := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hwX, hwx⟩ := (hUmem _).mp hmem
  have hw : w = ⟨y, hyW⟩ :=
    (chiefModBotMulEquiv W).injective (Additive.ofMul.injective hwx)
  have hy : (w : G) = y := congrArg Subtype.val hw
  rwa [hy] at hwX

theorem str86_natural_eq_of_bigB_invariant
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    {X : Subgroup G} (hXW : X ≤ W) (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    (hZX : Z1 L1 L2 S ≤ X) (hXZ : X ≠ Z1 L1 L2 S) :
    X = W := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let hUH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hnat' : IsNaturalModule ρ := hnat
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (imageOTwoQuot (u3H L1 L2 S) S).map e.toMonoidHom
  have hH1 := str86_imageS_props hF hSB hm hL2 e
  have hA2 : ∀ a ∈ A, a * a = 1 := hH1.1
  have hAcard : Nat.card A = Nat.card (GaloisField 2 m) := by
    rw [hH1.2, ← GaloisField.card 2 m (by omega)]
  let U : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) :=
    AddSubgroup.toZModSubmodule (n := 2)
      (Subgroup.toAddSubgroup ((X.subgroupOf W).map (chiefModBotMulEquiv W).toMonoidHom))
  have hmemU : ∀ x : Additive (Ch3z.chiefMod ⊥ W), x ∈ U ↔
      ∃ w : ↥W, (w : G) ∈ X ∧ Additive.ofMul (chiefModBotMulEquiv W w) = x :=
    t3s_mem_image (X := X) (W := W) hE
  have hfix_le : fixedSub ρ A ≤ U :=
    t3s_fixedSub_le hF hSB hm hL2 hstepW hE e hWS hZX U hmemU
  have hnot : fixedSub ρ A ≠ U :=
    t3s_fixedSub_ne hF hSB hm hL2 hstepW hE e hWS hXW hZX hXZ U hmemU
  have hlt : fixedSub ρ A < U := lt_of_le_of_ne hfix_le hnot
  have hUinv : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, GaloisField 2 m))),
      ∀ x ∈ U, ρ n x ∈ U :=
    t3s_normalizer_invariant hF hSB hm hL2 hstepW hE e hXB U hmemU
  have htop : U = ⊤ :=
    IsNaturalModule.eq_top_of_normalizer_invariant hnat' hA2 hAcard hUinv hlt
  exact t3s_eq_of_image_eq_top hE hXW U hmemU htop

end CFSG.Quasithin.Stroth

end
