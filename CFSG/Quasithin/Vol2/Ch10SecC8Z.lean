module

public import CFSG.Quasithin.Vol2.Ch10SecC8X

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem commutator_mem_of_le_sup {X V A : Subgroup G} (hVX : V ≤ X)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (h : X ≤ V ⊔ (X ⊓ Subgroup.centralizer (A : Set G))) {x a : G} (hx : x ∈ X) (ha : a ∈ A) :
    x * a * x⁻¹ * a⁻¹ ∈ V := by
  have hYV : X ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    refine (inf_le_left.trans ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hX v (hVX hv) y hy
  have hx' : x ∈ (↑(V ⊔ (X ⊓ Subgroup.centralizer (A : Set G))) : Set G) := h hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hYV] at hx'
  obtain ⟨v, hv, c, hc, rfl⟩ := hx'
  have hca : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hc.2 a ha).symm
  have e : v * c * a * (v * c)⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by
    calc v * c * a * (v * c)⁻¹ * a⁻¹ = v * (c * a) * c⁻¹ * v⁻¹ * a⁻¹ := by group
      _ = v * (a * c) * c⁻¹ * v⁻¹ * a⁻¹ := by rw [hca]
      _ = v * (a * v⁻¹ * a⁻¹) := by group
  rw [e]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hAV ha) _).mp (V.inv_mem hv))

theorem conj_mem_centralizerSection {X V : Subgroup G} {n c : G}
    (hnX : n ∈ Subgroup.normalizer (X : Set G)) (hnV : n ∈ Subgroup.normalizer (V : Set G))
    (hc : c ∈ centralizerSection ⊤ X V) : n * c * n⁻¹ ∈ centralizerSection ⊤ X V := by
  obtain ⟨-, hcX, hcV, hc⟩ := hc
  refine ⟨Subgroup.mem_top _, ?_, ?_, fun x hx => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnX hcX) (Subgroup.inv_mem _ hnX)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnV hcV) (Subgroup.inv_mem _ hnV)
  · have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnX) x).mp hx
    have h2 := (Subgroup.mem_normalizer_iff.mp hnV _).mp (hc _ hx')
    have e : x * (n * c * n⁻¹) * x⁻¹ * (n * c * n⁻¹)⁻¹ =
        n * (n⁻¹ * x * n⁻¹⁻¹ * c * (n⁻¹ * x * n⁻¹⁻¹)⁻¹ * c⁻¹) * n⁻¹ := by group
    rw [e]
    exact h2

theorem le_centralizerSection_of_perfect {L X V W : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hVX : V ≤ X)
    (hLX : L ≤ centralizerSection ⊤ X V) (hLV : L ≤ centralizerSection ⊤ V W) :
    L ≤ centralizerSection ⊤ X W := by
  have hN : (W.subgroupOf V).Normal := ⟨fun a ha b => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have e : ((b * a * b⁻¹ : ↥V) : G) = a := by
      change (b : G) * a * (b : G)⁻¹ = a
      rw [hX b (hVX b.2) a (hVX a.2)]
      group
    rw [e]
    exact ha⟩
  have hcomm : ∀ a b : ↥V ⧸ W.subgroupOf V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext (hX a (hVX a.2) b (hVX b.2)))
  intro l hl
  refine ⟨Subgroup.mem_top _, (hLX hl).2.1, (hLV hl).2.2.1, fun x hx => ?_⟩
  let d : ↥L → ↥V := fun g => ⟨x * g * x⁻¹ * (g : G)⁻¹, (hLX g.2).2.2.2 x hx⟩
  let φ : ↥L →* ↥V ⧸ W.subgroupOf V :=
    { toFun := fun g => (d g : ↥V ⧸ W.subgroupOf V)
      map_one' := by
        have h1 : d 1 = 1 := Subtype.ext (by simp [d])
        simp only [h1]
        rfl
      map_mul' := fun g h => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h1 := (hLV (L.inv_mem g.2)).2.2.2 ((d h : G)⁻¹) (V.inv_mem (d h).2)
        have h2 := (Subgroup.mem_normalizer_iff.mp (hLV g.2).2.2.1 _).mp h1
        convert h2 using 1
        simp only [d, Subgroup.coe_mul, Subgroup.coe_inv]
        group }
  have hS : ⁅L, L⁆ ≤ φ.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro l1 h1 l2 h2
    refine ⟨(⁅(⟨l1, h1⟩ : ↥L), ⟨l2, h2⟩⁆ : ↥L), ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hl' : l ∈ ⁅L, L⁆ := by rw [hL]; exact hl
  obtain ⟨l', hl'k, rfl⟩ := hS hl'
  have h1 : (d l' : ↥V ⧸ W.subgroupOf V) = 1 := hl'k
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

variable [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem le_normalizer_omegaOne_Q (T L I : Subgroup G) :
    T ≤ Subgroup.normalizer
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) : Set G) :=
  (le_normalizer_inf' Subgroup.le_normalizer
    (SecA.le_normalizer_centralizer (SecA.le_normalizer_fsuVM T L I))).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem L_le_normalizer_omegaOne_Q (hyp : Hyp10 G T L I) (h1027 : Stmt10_2_7) :
    L ≤ Subgroup.normalizer
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) : Set G) := by
  rw [(h1027 G T L I hyp).2]
  refine le_trans ?_ (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  exact ((SecA.le_fsuL0 T L).trans le_sup_left).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (fsuL0 T L ⊔ T))

omit [Finite G] in
theorem fsuCVM_ne_bot_of_cV1 (hne : cV1 T L I ≠ ⊥) : fsuCVM T L I ≠ ⊥ := by
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  intro h
  apply hv1
  have h1 : ((v : ↥(fsuUL T L I)) : G) ∈ fsuCVM T L I :=
    ⟨hV1V (v : ↥(fsuUL T L I)).2, v.2⟩
  rw [h, Subgroup.mem_bot] at h1
  exact Subtype.ext (Subtype.ext h1)

theorem thompsonJ_le_centralizerSection (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I)
    (hne : cV1 T L I ≠ ⊥) :
    thompsonJ T ≤ centralizerSection ⊤
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))) (fsuVM T L I) := by
  refine iSup₂_le fun A hA a ha => ⟨Subgroup.mem_top _, le_normalizer_omegaOne_Q T L I (hA.1 ha),
    SecA.le_normalizer_fsuVM T L I (hA.1 ha), fun x hx => ?_⟩
  exact commutator_mem_of_le_sup (fsuVM_le_omegaOneCenterOf hyp)
    (fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb)
    (hA.1.trans (SecA.le_normalizer_fsuVM T L I))
    (le_sup_inf_centralizer h37 h38 hyp h1011 h1012 h484 h3 hne hA) hx ha

theorem L_le_centralizerSection (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    L ≤ centralizerSection ⊤
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))) (fsuVM T L I) := by
  have hJ := thompsonJ_le_centralizerSection h37 h38 hyp h1011 h1012 h484 h3 hne
  have hL := eq_commutator_thompsonJ hyp h1011 h1012 h3 h3210 (fsuCVM_ne_bot_of_cV1 hne)
  have hLX := L_le_normalizer_omegaOne_Q hyp h1027
  have hLV := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  calc L = ⁅L, thompsonJ T⁆ := hL
    _ ≤ _ := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (conj_mem_centralizerSection (hLX hl) (hLV hl) (hJ hj))
        (Subgroup.inv_mem _ (hJ hj))

theorem L_le_centralizerSection_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    L ≤ centralizerSection ⊤
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))) (fsuUL T L I) := by
  refine le_centralizerSection_of_perfect hyp.fsu.faithful.1.2.1.2.1
    (fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb)
    (fsuVM_le_omegaOneCenterOf hyp)
    (L_le_centralizerSection h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne) fun l hl => ?_
  exact ⟨Subgroup.mem_top _, (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I) hl,
    le_normalizer_fsuUL T L I hl, fun v hv => Subgroup.commutator_mem_commutator hv hl⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
