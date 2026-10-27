module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofCommRel
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofModel
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofField
public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def Comm1119For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z y δ g : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      y ∈ J → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      δ ∈ Subgroup.zpowers y → δ ^ 3 = 1 → δ ≠ 1 →
      g ^ 3 = 1 → g * δ = δ * g → g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers δ → g * z ≠ z * g →
        y * (g⁻¹ * y * g) = (g⁻¹ * y * g) * y ∧
        y * (g⁻¹ * y * g) * (g⁻¹ * (g⁻¹ * y * g) * g) = 1 ∧
        ∀ w : Z, (∃ k : ℕ, w ^ 3 ^ k = 1) → w * y = y * w → w * g = g * w →
          w ∈ Subgroup.zpowers δ

@[expose] def Comm1119G2Ss : Prop :=
  Comm1119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def Comm1119D4Even : Prop :=
  Comm1119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

namespace Item1117Res3Proof

theorem comm1119For_of_split {F F' : ∀ (X : Type) [Group X], Prop}
    (hs : KS11Lie3Proof.SplitFamily F F') (h : Comm1119For F') : Comm1119For F := by
  intro Z _ _ hZ z y δ g J hz3 hJ hJT hyJ hyk hy3 hδ hδ3 hδ1 hg3 hgδ hgz hgz'
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z y δ g J hz3 hJ hJT hyJ hyk hy3 hδ hδ3 hδ1 hg3 hgδ hgz hgz'
  · exact (hno z J hz3 hJ hJT).elim

section Glue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem step1119Comm_concl_of_family (h45 : Sec4.Item4_5) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g) {F : ∀ (X : Type) [Group X], Prop}
    (hNo : NoOuterType424For F) (hK : Comm1119For F)
    (hZ : ∃ (X : Type) (_ : Group X), F X ∧
      Nonempty ((Y ⧸ aschbacherSolvableCore 3 Y) ≃* _root_.commutator X))
    (hcen : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥) :
    ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
      g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
      (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
        z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
      ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have hAe := h.mem_partTwoF.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY h.mem_A
  obtain ⟨z, -, hz3, hJ, hJT, hgbv, hgbzv, hgbz⟩ := exists_inner_model h117 h hNo hZ hcen hcN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hgY : g ∈ Y := h.g_mem.1
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hdY : d ∈ Y := h.sec11K_le hdK
  have hx3K := Item1117Proof.x_cube_mem_sec11K h
  have hx3Y : x ^ 3 ∈ Y := h.sec11K_le hx3K
  set X3 : Y := ⟨x ^ 3, hx3Y⟩ with hX3
  set Gg : Y := ⟨g, hgY⟩ with hGg
  set D : Y := ⟨d, hdY⟩ with hD
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hdP : d ∈ sec11P R g :=
    Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 (Item1117Proof.d_mem_A h))
  have hYP : ∀ w : Y, (w : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) → (w : G) ∈ sec11P R g :=
    fun w hw => by
      refine (Subgroup.closure_le _).mpr ?_ hw
      rintro u (rfl | rfl | rfl)
      · exact (sec11P R g).pow_mem hxP 3
      · exact hgP
      · exact hdP
  have hmem : ∀ u ∈ ({x ^ 3, g, d} : Set G), u ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) :=
    fun u hu => Subgroup.subset_closure hu
  have hone : ∀ w : Y, (w : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) → π w = 1 → w = 1 :=
    fun w hw h1 => Subtype.ext (eq_one_of_mk_eq_one h (hYP w hw) w.2 h1)
  have hX3m : (X3 : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) := hmem _ (Or.inl rfl)
  have hGgm : (Gg : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) :=
    hmem _ (Or.inr (Or.inl rfl))
  have hDm : (D : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) :=
    hmem _ (Or.inr (Or.inr rfl))
  have hyJ : π X3 ∈ ((sec11K L a).subgroupOf Y).map π :=
    ⟨X3, Subgroup.mem_subgroupOf.mpr hx3K, rfl⟩
  have hyk : ∃ k : ℕ, π X3 ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : X3 ^ 3 ^ k = 1 := Subtype.ext (by
      simp only [hX3, SubgroupClass.coe_pow, Subgroup.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
    rw [this, map_one]
  have hy3 : π X3 ^ 3 ≠ 1 := by
    intro h1
    rw [← map_pow] at h1
    have h2 := hone (X3 ^ 3) (Subgroup.pow_mem _ hX3m 3) h1
    have h3 : x ^ 9 = 1 := by
      have := congrArg Subtype.val h2
      simp only [hX3, SubgroupClass.coe_pow, Subgroup.coe_one] at this
      rw [← pow_mul] at this
      exact this
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
    have := hbig.orderOf_x_gt
    omega
  have hδy : π D ∈ Subgroup.zpowers (π X3) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Item1117Proof.d_mem_zpowers_x_cube h)
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa [hX3] using hn)
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  have hδ3 : π D ^ 3 = 1 := by
    rw [← map_pow]
    have : D ^ 3 = 1 := Subtype.ext (by simpa [hD] using hd3)
    rw [this, map_one]
  have hδ1 : π D ≠ 1 := by
    intro h1
    have h2 := hone D hDm h1
    exact (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.2
      (by simpa [hD] using congrArg Subtype.val h2)
  have hg3 : π Gg ^ 3 = 1 := by
    rw [← map_pow]
    have : Gg ^ 3 = 1 := Subtype.ext (by
      simp only [hGg, SubgroupClass.coe_pow, Subgroup.coe_one]
      rw [← hbig.orderOf_g, pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨hR1, hR2, hR3⟩ := hK _ hZ z (π X3) (π D) (π Gg) _ hz3 hJ hJT hyJ hyk hy3 hδy hδ3
    hδ1 hg3 hgbv hgbzv hgbz
  have hR1' : x ^ 3 * (g⁻¹ * x ^ 3 * g) = (g⁻¹ * x ^ 3 * g) * x ^ 3 := by
    have hw := hone (X3 * (Gg⁻¹ * X3 * Gg) * X3⁻¹ * (Gg⁻¹ * X3 * Gg)⁻¹)
      (by
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hX3m ?_)
          (Subgroup.inv_mem _ hX3m)) (Subgroup.inv_mem _ ?_) <;>
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hGgm) hX3m) hGgm)
      (by
        simp only [map_mul, map_inv]
        rw [hR1]
        group)
    have := congrArg Subtype.val hw
    simp only [hX3, hGg, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc x ^ 3 * (g⁻¹ * x ^ 3 * g) =
        (x ^ 3 * (g⁻¹ * x ^ 3 * g) * (x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g)⁻¹) *
          ((g⁻¹ * x ^ 3 * g) * x ^ 3) := by group
      _ = (g⁻¹ * x ^ 3 * g) * x ^ 3 := by rw [this, one_mul]
  have hR2' : x ^ 3 * (g⁻¹ * x ^ 3 * g) * (g⁻¹ * (g⁻¹ * x ^ 3 * g) * g) = 1 := by
    have hw := hone (X3 * (Gg⁻¹ * X3 * Gg) * (Gg⁻¹ * (Gg⁻¹ * X3 * Gg) * Gg))
      (by
        have h1 : ((Gg⁻¹ * X3 * Gg : Y) : G) ∈ Subgroup.closure ({x ^ 3, g, d} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hGgm) hX3m) hGgm
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hX3m h1)
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hGgm) h1) hGgm))
      (by simp only [map_mul, map_inv]; exact hR2)
    have := congrArg Subtype.val hw
    simpa [hX3, hGg] using this
  have hR3' : ∀ w ∈ sec11P R g ⊓ Y, w * x ^ 3 = x ^ 3 * w → w * g = g * w →
      w ∈ Subgroup.zpowers d := by
    intro w hw hwx hwg
    set W : Y := ⟨w, hw.2⟩ with hW
    have hWk : ∃ k : ℕ, π W ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := h.isPGroup_sec11P ⟨w, hw.1⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : W ^ 3 ^ k = 1 := Subtype.ext (by simpa [hW] using congrArg Subtype.val hk)
      rw [this, map_one]
    have hWx : π W * π X3 = π X3 * π W := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hwx
    have hWg : π W * π Gg = π Gg * π W := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hwg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hR3 (π W) hWk hWx hWg)
    have hWD : W * (D ^ n)⁻¹ = 1 := by
      apply Subtype.ext
      have h1 := eq_one_of_mk_eq_one h (w := w * (d ^ n)⁻¹)
        ((sec11P R g).mul_mem hw.1 ((sec11P R g).inv_mem ((sec11P R g).zpow_mem hdP n)))
        (Y.mul_mem hw.2 (Y.inv_mem (Y.zpow_mem hdY n)))
        (by
          have e : (⟨w * (d ^ n)⁻¹, Y.mul_mem hw.2 (Y.inv_mem (Y.zpow_mem hdY n))⟩ : Y) =
              W * (D ^ n)⁻¹ := Subtype.ext (by simp [hW, hD])
          rw [e, map_mul, map_inv, map_zpow, hn, mul_inv_cancel])
      simpa [hW, hD] using h1
    have hwd : w = d ^ n := by
      have := congrArg Subtype.val hWD
      simp only [hW, hD, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
        Subgroup.coe_zpow] at this
      exact mul_inv_eq_one.mp this
    rw [hwd]
    exact Subgroup.zpow_mem_zpowers d n
  exact step1119Comm_concl_of_relations hbig hR1' hR2' hR3'

end Glue

end Item1117Res3Proof

section Main

open Item1117Res3Proof in
theorem step1119CommG2_of (h45 : Sec4.Item4_5) (h117 : Item117) (hK : Comm1119G2Ss) :
    Step1119CommG2 := by
  intro G _ _ A c L a R Y d x s r g hbig hG2
  obtain ⟨q, hq, ⟨f⟩⟩ := hG2
  have hXp := SetUp1118Proof.isPerfect_lie_G2 q hq
  have e : Y ⧸ aschbacherSolvableCore 3 Y ≃*
      _root_.commutator (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
    f.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) :=
    ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
  exact step1119Comm_concl_of_family h45 h117 hbig noOuterType424G2_holds
    (comm1119For_of_split KS11Lie3Proof.splitFamily_g2 hK) hZ
    (KS11Lie3Proof.center_eq_bot_g2 _ hZ)

end Main

end CFSG.RankThree.PartTwo.Sec11
