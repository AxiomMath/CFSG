module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837C
public import CFSG.Quasithin.EmptyFaithful.Der6DMain
public import CFSG.Quasithin.EmptyFaithful.S152He4Groups
public import CFSG.Quasithin.EmptyFaithful.S152He4Inv
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open S152N

@[expose] noncomputable def baseW : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) →* W3 where
  toFun p := ⟨fun q => if q = 1 then p.1 else p.2, 1⟩
  map_one' := by
    refine RegularWreathProduct.ext (funext fun q => ?_) rfl
    rcases mz2_cases q with rfl | rfl <;> rfl
  map_mul' p p' := by
    refine RegularWreathProduct.ext (funext fun q => ?_) (mul_one 1).symm
    rw [RegularWreathProduct.mul_left]
    change (if q = 1 then (p * p').1 else (p * p').2) =
      (if q = 1 then p.1 else p.2) *
        (if (1 : Multiplicative (ZMod 2))⁻¹ * q = 1 then p'.1 else p'.2)
    rw [one_inv_mul_mz2]
    rcases mz2_cases q with rfl | rfl <;> simp

theorem baseW_left (p : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (q : Multiplicative (ZMod 2)) :
    (baseW p).left q = if q = 1 then p.1 else p.2 := rfl

theorem isSolvable_W3 : Group.IsSolvable W3 := by
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  refine Group.isSolvable_of_ker_le_range baseW RegularWreathProduct.rightHom fun w hw => ?_
  have hw1 : w.right = 1 := hw
  refine ⟨(w.left 1, w.left tq), RegularWreathProduct.ext (funext fun q => ?_) hw1.symm⟩
  rw [baseW_left]
  rcases mz2_cases q with rfl | rfl
  · exact ite_eq_left rfl
  · exact ite_eq_right tq_ne_one

theorem mul_comm_of_mem_Shat {a b : MulAut WMod} (ha : a ∈ Shat) (hb : b ∈ Shat) :
    a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Shat ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Shat hb)
  have hab : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Shat (Shat.mul_mem ha hb))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem isSolvable_stabE : Group.IsSolvable ↥stabE := by
  have : Group.IsSolvable W3 := isSolvable_W3
  have : Group.IsSolvable ↥(Shat.subgroupOf stabE) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (mul_comm_of_mem_Shat a.2 b.2))
  refine Group.isSolvable_of_ker_le_range (Shat.subgroupOf stabE).subtype omegaW fun x hx => ?_
  exact ⟨⟨x, (omegaW_eq_one_iff x).1 hx⟩, rfl⟩

end L3Wr

end H

namespace H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_perfect_of_isSolvable {Γ : Type*} [Group Γ] {B : Subgroup Γ}
    (hB : ⁅B, B⁆ = B) [Group.IsSolvable B] : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem le_centralizer_of_perfect (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) {z : G} (hz1 : z ≠ 1)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {K : Subgroup G}
    (hKM : K ≤ fsuM T L) (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) (hK : ⁅K, K⁆ = K) :
    K ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨e, he, -, -, hz, hez⟩ := exists_model_eW00_T hyp hV hrow hz1 hzV
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have h1 : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      le_normalizer_conjClosure (fsuV T I) (fsuM T L)
    rwa [← hVVM] at h1
  have hKN : K ≤ Subgroup.normalizer (fsuV T I : Set G) := hKM.trans hMV
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  set act := actOn hV e hKN with hact
  have hstab : ∀ k : ↥K, act k ∈ stabE := by
    intro k
    refine mem_stabE_iff.2 ⟨congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hKM k.2)), ?_⟩
    rw [actOn_apply]
    change e (convI hV ⟨k, hKN k.2⟩ (e.symm (eW 0 0))) = eW 0 0
    rw [hezs, ← hez]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    change (k : G) * z * (k : G)⁻¹ = z
    rw [(Subgroup.mem_centralizer_iff.mp (hKz k.2) z rfl).symm, mul_inv_cancel_right]
  set ι : ↥K →* ↥stabE := act.codRestrict stabE hstab with hι
  have hperf : ⁅ι.range, ι.range⁆ = ι.range := by
    have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hK]
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have : Group.IsSolvable ↥stabE := isSolvable_stabE
  have hbot := eq_bot_of_perfect_of_isSolvable hperf
  intro k hk
  have h1 : ι ⟨k, hk⟩ = 1 := by
    have : ι ⟨k, hk⟩ ∈ ι.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have h2 : act ⟨k, hk⟩ = 1 := congrArg Subtype.val h1
  rw [actOn_apply] at h2
  exact (convI_eq_one_iff hV _).1 (congrHom_injective e (h2.trans (map_one _).symm))

theorem not_ch83X_le_centralizer
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) {z : G}
    (hi : (pCoreOf 2 (ch83X T L z)).relIndex (ch83X T L z) = 9) :
    ¬ ch83X T L z ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hXC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have h2 := isPGroup_inf_centralizer h37 h38 h326 hyp hrow
  have hX2 : IsPGroup 2 (ch83X T L z) :=
    h2.to_le (le_inf (hXL.trans le_sup_left) hXC)
  have hres : twoResidual (ch83X T L z) = ch83X T L z :=
    twoResidual_twoResidual (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))
  have hbot : ch83X T L z = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hres]
    refine twoResidual_le_of_isTwoQuotient bot_le (fun _ _ => Subgroup.mem_normalizer_iff.mpr
      fun _ => by simp) fun y hy => ?_
    obtain ⟨n, hn⟩ := hX2 ⟨y, hy⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  rw [hbot, Subgroup.relIndex_bot_right] at hi
  exact absurd hi (by norm_num)

theorem false_of_l33_m11
    {T Mc H L : Subgroup G} (hT : quasithinIsSylowTwo T) (hTMc : T ≤ Mc) (hTH : T ≤ H)
    (hMcL : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : oTwoUpper H ≤ L)
    (φ : OTwoQuot H ≃* S152N.W3)
    (hlist : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) :
    False := by
  classical
  have hHcard : Nat.card H = 72 * Nat.card (pCoreOf 2 H) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
    have h2 : Nat.card (OTwoQuot H) = 72 := by
      rw [Nat.card_congr φ.toEquiv]
      exact S152N.W3.card_eq
    have h3 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [h3, h1]
    change Nat.card (OTwoQuot H) * _ = _
    rw [h2]
  obtain ⟨P, hY, ⟨φL⟩⟩ := He4.exists_yData hT hTMc hTH hMcL hKL hHcard
  have hLt : ↥(imageOTwoQuot (L ⊔ T) L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    φL.symm.trans (Der6D.oTwoQuotEquiv L)
  rcases hlist with h | h | h
  · have hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(imageOTwoQuot (L ⊔ T) L)
        .PSL 3 3 1 :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv hLt h
    exact He4.coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (He4.smallFacts_l33 (Or.inl hmod) (He4.noInvCommNine_l33 hmod))
  · obtain ⟨e⟩ := h
    have h' : Nonempty (↥(imageOTwoQuot (L ⊔ T) L) ≃*
        ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) := ⟨hLt.trans e⟩
    have hmod := He4.statedClassicalModel_of_statedSL_three_three h'
    exact He4.coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (He4.smallFacts_l33 (Or.inr h') (He4.noInvCommNine_l33 hmod))
  · obtain ⟨e⟩ := h
    have h' : Nonempty (↥(imageOTwoQuot (L ⊔ T) L) ≃*
        CFSG.Blueprint.NativeSporadic.Carrier .M11) := ⟨hLt.trans e⟩
    exact He4.coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (He4.smallFacts_m11 h' (He4.noInvCommNine_m11 h'))

theorem not_centralizer_le_fsuM (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ fsuM T L := by
  intro hle
  have h37' := a37ForSQTK_of_cat h37
  have h38' := a38ForSQTK_of_cat h38
  have h39' := a39ForSQTK_of_cat h39
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hzsq : z ^ 2 = 1 := by
    rw [← hz2]
    exact pow_orderOf_eq_one z
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37' h38' h39'
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨M₁, M₂, hne12, hM₁, hM₂, hTM₁, hTM₂⟩ := h332 G T hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow L hyp.fsu.maximal hyp.fsu.quasisimple
  obtain ⟨H₁, hH₁⟩ : ∃ H : Subgroup G, IsHStar T (fsuM T L) H := by
    by_cases h : M₁ = fsuM T L
    · exact exists_isHStar_of hU.1.1 hM₂ hTM₂ fun h' => hne12 (h.trans h'.symm)
    · exact exists_isHStar_of hU.1.1 hM₁ hTM₁ h
  have hzΩ : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hzT, hzmem.2⟩, hzsq⟩
  have hzH₁ := ((center_facts_fsu hC58 h317 h37' h38' h39' h3228 hyp hH₁).1 hzΩ).2
  have hH₁Gz : H₁ ≤ Subgroup.centralizer ({z} : Set G) := fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact (Subgroup.mem_centralizer_iff.1 hzH₁ h hh).symm
  exact hH₁.2.1 (hH₁Gz.trans hle)

end Ch837

end H13

end CFSG.Quasithin
