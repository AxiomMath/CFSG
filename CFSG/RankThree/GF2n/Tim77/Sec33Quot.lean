module

public import CFSG.RankThree.GF2n.Tim77.Sec33Basic
public import CFSG.RankThree.GF2n.Tim77.Sec32b

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec33_s_mem_normalizer_Y [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) :
    s ∈ normalizer (Section3.Y A Abar s : Set G) := by
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts h hs).2
  have hsq := sec33_sq_mem_N h hs
  obtain ⟨x₁, hx₁X, hx₁⟩ := h.setup.exists_conj_eq
  have hx₁Y : x₁ ∈ Section3.Y A Abar s := by
    have : A ⊔ Abar ≤ Section3.Y A Abar s := by unfold Section3.Y; exact le_sup_left
    exact this hx₁X
  have hNAb : ∀ n ∈ Section3.N A Abar s, n ∈ normalizer (Abar : Set G) := by
    intro n hn
    rw [hx₁]
    exact sec33_N_le_normalizer_conj h hs hx₁Y n hn
  have hle : conjSubgroup s (Section3.Y A Abar s) ≤ Section3.Y A Abar s := by
    unfold Section3.Y
    rw [conjSubgroup_sup_t77, conjSubgroup_sup_t77]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 s A x).1 hx
      rw [sec32a_conj_eq_of_comm (hsA a ha)]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)
    · intro x hx
      exact (le_sup_right (a := A ⊔ Abar)) hx
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := (mem_conjSubgroup_exists_t77 s _ x).1 hx
      obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 s Abar u).1 hu
      have h2 := (Subgroup.mem_normalizer_iff.mp (hNAb (s * s) hsq) y).mp hy
      have e : s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ := by group
      show s * (s * y * s⁻¹) * s⁻¹ ∈ _
      rw [e]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (by simpa using h2))
  exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hle)

section Certified

theorem sec33_data [Finite G] {A Abar S₀ B : Subgroup G} {s : G} (hC : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) (hq : 2 < Section3.q A Abar)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] :
    Sec32dData (↥(Section3.Y A Abar s))
      ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
      {t | (t : G) ∈ Section4.D A Abar s} := by
  obtain ⟨hNY, hNnorm, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  obtain ⟨-, hcomm2⟩ := sec32b_of tim77Sec32a_holds G A Abar S₀ B s hC hs
  obtain ⟨hcls, hRI, hne4, hcent⟩ := sec41_of tim77Sec32a_holds G A Abar S₀ B s hC hs
  have hsC := sec32d_mem_centralizer hC hs
  have hDY : Section4.D A Abar s ⊆ Section3.Y A Abar s := sec32d_D_subset_Y
  obtain ⟨d₀, hd₀, hcl⟩ := hcls
  obtain ⟨hRI1, hRI2, -⟩ := hRI
  have hA0A : Section3.A0 A Abar ≤ A := by
    rw [hC.a0_eq]
    exact inf_le_left
  refine
      { sq := fun n hn =>
          Subtype.ext (by simpa using hNab.2 (n : G) (Subgroup.mem_subgroupOf.mp hn))
        disj := fun t ht htN =>
          sec32d_D_not_mem_N hC hNab hNnorm ht (Subgroup.mem_subgroupOf.mp htN)
        invol := ?_
        ord := ?_
        conjD := ?_
        gen := ?_
        cent := ?_
        nonc := ?_
        idx := ?_
        single := ?_
        O2 := ?_ }
  · intro t ht
    apply Subtype.ext
    have h2 : (t : G) ^ 2 = 1 := by
      rw [← hRI1 (t : G) ht]
      exact pow_orderOf_eq_one _
    simpa using h2
  · intro t ht t' ht'
    have e : orderOf (t * t') = orderOf ((t : G) * (t' : G)) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    rw [e]
    rcases hRI2 (t : G) ht (t' : G) ht' with h2 | h4 | hodd
    · exact Or.inl (dvd_of_eq h2)
    · exact absurd h4 (hne4 _ ht _ ht')
    · exact Or.inr hodd
  · intro g t ht
    have := sec32d_D_conj g.2 ht
    simpa using this
  · intro y
    have hK := sec32d_gen hC hs hNnorm
    have hle : Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) ≤
        (Subgroup.closure ({t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} ∪
          (((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s) : Subgroup
            ↥(Section3.Y A Abar s)) : Set ↥(Section3.Y A Abar s)))).map
          (Section3.Y A Abar s).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (hg | hg)
      · exact Subgroup.mem_map.mpr ⟨⟨g, hDY hg⟩, Subgroup.subset_closure (Or.inl hg), rfl⟩
      · exact Subgroup.mem_map.mpr ⟨⟨g, hNY hg⟩,
          Subgroup.subset_closure (Or.inr (Subgroup.mem_subgroupOf.mpr hg)), rfl⟩
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp (hle (hK y y.2))
    have hwy' : w = y := Subtype.ext hwy
    rw [← hwy']
    exact hw
  · intro t ht x hx y hy hxt hyt
    have hxt' : (x : G) * (t : G) = (t : G) * (x : G) := congrArg Subtype.val hxt
    have hyt' : (y : G) * (t : G) = (t : G) * (y : G) := congrArg Subtype.val hyt
    have hxS : (x : G) ∈
        Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * (t : G) = (t : G) * e} :=
      Subgroup.subset_closure
        (show (x : G) ∈ Section4.D A Abar s ∧ (x : G) * (t : G) = (t : G) * (x : G) from
          ⟨hx, hxt'⟩)
    have hyS : (y : G) ∈
        Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * (t : G) = (t : G) * e} :=
      Subgroup.subset_closure
        (show (y : G) ∈ Section4.D A Abar s ∧ (y : G) * (t : G) = (t : G) * (y : G) from
          ⟨hy, hyt'⟩)
    exact Subtype.ext (sec32d_comm_of_isElemAbelian (hcent (t : G) ht) hxS hyS)
  · obtain ⟨b, hbD, hbN⟩ := sec32d_exists_outside hC hs hNnorm
    obtain ⟨a, haA, ha0, hab⟩ := sec32d_exists_noncomm hC hbN
    have haD : a ∈ Section4.D A Abar s :=
      sec32d_mem_D_iff.mpr ⟨1, one_mem _, a, haA, ha0, by simp⟩
    refine ⟨⟨a, hDY haD⟩, haD, ⟨b, hDY hbD⟩, hbD, fun hc => hab (congrArg Subtype.val hc), ?_⟩
    intro hmem
    have hab' : a * b ∈ Section3.N A Abar s := Subgroup.mem_subgroupOf.mp hmem
    apply hbN
    have := mul_mem (inv_mem (Subgroup.le_normalizer haA)) (sec32d_N_le_normalizer hC hsC hab')
    simpa using this
  · have hq' : 2 < (Section3.A0 A Abar).relIndex A := by
      have h1 := hC.setup.relIndex_Lb
      unfold Section3.q at hq
      rw [h1] at hq
      exact hq
    obtain ⟨a, haA, ha0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hA0A hC.a0_ne)
    obtain ⟨a', ha'A, ha'0, hla⟩ :=
      sec32d_exists_third hC hC.hyp.elemAbelian hq' haA ha0
    have hainv : a⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hC.hyp.elemAbelian.2 a haA)
    have haD : a ∈ Section4.D A Abar s :=
      sec32d_mem_D_iff.mpr ⟨1, one_mem _, a, haA, ha0, by simp⟩
    have ha'D : a' ∈ Section4.D A Abar s :=
      sec32d_mem_D_iff.mpr ⟨1, one_mem _, a', ha'A, ha'0, by simp⟩
    refine ⟨⟨a, hDY haD⟩, haD, ⟨a', hDY ha'D⟩, ha'D, ?_, ?_, ?_⟩
    · intro hmem
      have hmemAN : a⁻¹ * a' ∈ A ⊓ Section3.N A Abar s :=
        ⟨A.mul_mem (A.inv_mem haA) ha'A, Subgroup.mem_subgroupOf.mp hmem⟩
      exact hla (sec32d_inf_N_le hC hNab hmemAN)
    · exact Subtype.ext (sec32d_comm_of_isElemAbelian hC.hyp.elemAbelian haA ha'A)
    · have hprod : a * a' ∈ Section4.D A Abar s := by
        refine sec32d_mem_D_iff.mpr ⟨1, one_mem _, a * a', mul_mem haA ha'A, ?_, by simp⟩
        have e : a * a' = a⁻¹ * a' := by rw [hainv]
        rw [e]
        exact hla
      exact hprod
  · refine ⟨⟨d₀, hDY hd₀⟩, hd₀, fun d hd => ?_⟩
    obtain ⟨y, hy, hdy⟩ := hcl d hd
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩
  · intro z hz g
    rw [Subgroup.mem_subgroupOf]
    have hz' : (z : G) ∈ (pCore 2 ↥(Section3.Y A Abar s)).map (Section3.Y A Abar s).subtype :=
      Subgroup.mem_map_of_mem _ hz
    have := hcomm2 (Subgroup.commutator_mem_commutator hz' g.2)
    simpa [commutatorElement_def] using this

theorem sec33_quot_bender [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : 2 < Section3.q A Abar)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] :
    _root_.commutator (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = ⊤ ∧
    CFSG.BenderSuzuki.IsBenderGroup
      ((↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸
        Subgroup.center (↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) := by
  have h := sec33_data hC hs hq
  have hodd := sec32d_q_isOddTransp h
  have hnorm := sec32d_q_normal h
  have hgen := sec32d_q_closure h
  have huv := sec32d_q_uv h
  have hdisc := sec32d_q_disc h
  have hperf := sec32d_q_perfect h
  have hO := sec32d_q_O2 h
  obtain ⟨hS, hB⟩ :=
    CFSG.Timmesfeld.Bridge.OddTransp.oddTranspRadical
      (↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
      (QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t | (t : G) ∈ Section4.D A Abar s}) hodd hnorm hgen huv hdisc
  have hzc := sec32d_zStar_le_center hperf hO
  have hsr : CFSG.solvableRadical (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ≤ Subgroup.center _ := by
    rw [hS]
    exact hzc
  have hrc : CFSG.solvableRadical (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = Subgroup.center _ :=
    le_antisymm hsr (le_sSup ⟨inferInstance, inferInstance⟩)
  exact ⟨hperf, CFSG.GH74.Uniqueness.isBenderGroup_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq hrc.symm) hB⟩

end Certified

@[expose] def sec33ConjAut (Y : Subgroup G) {s : G} (hs : s ∈ normalizer (Y : Set G)) :
    ↥Y ≃* ↥Y where
  toFun z := ⟨s * z * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs z).mp z.2⟩
  invFun z := ⟨s⁻¹ * z * s, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) z).mp z.2
    rwa [inv_inv] at this⟩
  left_inv z := Subtype.ext (by simp only; group)
  right_inv z := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem sec33ConjAut_apply (Y : Subgroup G) {s : G} (hs : s ∈ normalizer (Y : Set G))
    (z : ↥Y) : (sec33ConjAut Y hs z : G) = s * z * s⁻¹ := rfl

theorem sec33ConjAut_map {Y N : Subgroup G} {s : G} (hs : s ∈ normalizer (Y : Set G))
    (hsN : s ∈ normalizer (N : Set G)) :
    (N.subgroupOf Y).map (sec33ConjAut Y hs).toMonoidHom = N.subgroupOf Y := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ N := Subgroup.mem_subgroupOf.mp hw
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hsN w).mp hw')
  · intro hx
    have hx' : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
    refine ⟨(sec33ConjAut Y hs).symm x, Subgroup.mem_subgroupOf.mpr ?_,
      (sec33ConjAut Y hs).apply_symm_apply x⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) (x : G))
    rw [inv_inv] at h1
    exact h1.mp hx'

@[expose] noncomputable def sec33Tau {Y N : Subgroup G} [hNn : (N.subgroupOf Y).Normal] {s : G}
    (hs : s ∈ normalizer (Y : Set G)) (hsN : s ∈ normalizer (N : Set G)) :
    (↥Y ⧸ N.subgroupOf Y) ≃* (↥Y ⧸ N.subgroupOf Y) :=
  QuotientGroup.congr (N.subgroupOf Y) (N.subgroupOf Y) (sec33ConjAut Y hs)
    (sec33ConjAut_map hs hsN)

theorem sec33Tau_mk {Y N : Subgroup G} [hNn : (N.subgroupOf Y).Normal] {s : G}
    (hs : s ∈ normalizer (Y : Set G)) (hsN : s ∈ normalizer (N : Set G)) (z : ↥Y) :
    sec33Tau hs hsN (QuotientGroup.mk z) = QuotientGroup.mk (sec33ConjAut Y hs z) :=
  QuotientGroup.congr_mk _ _ _ _ z

theorem sec33_mk_eq_iff {Y N : Subgroup G} [hNn : (N.subgroupOf Y).Normal] (y z : ↥Y) :
    (QuotientGroup.mk y : ↥Y ⧸ N.subgroupOf Y) = QuotientGroup.mk z ↔
      (y : G)⁻¹ * z ∈ N := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

def sec33Fix (Y N : Subgroup G) (s : G) (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G)) :
    Subgroup G where
  carrier := {y | y ∈ Y ∧ s * y * s⁻¹ * y⁻¹ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, by simpa using N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨Subgroup.mul_mem _ haY hbY, ?_⟩
    have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ =
        (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact N.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hYN a haY) _).mp hb)
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    refine ⟨Subgroup.inv_mem _ haY, ?_⟩
    have e : s * a⁻¹ * s⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYN a⁻¹ (Subgroup.inv_mem _ haY)) _).mp
      (N.inv_mem ha)

theorem sec33_comm_of_fixed_central [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hne : conjSubgroup s Abar ≠ Abar) {k : G} (hk : k ∈ Section3.Y A Abar s)
    (hz : ∀ y ∈ Section3.Y A Abar s,
      (k⁻¹ * (s * k * s⁻¹)) * y * (k⁻¹ * (s * k * s⁻¹))⁻¹ * y⁻¹ ∈ Section3.N A Abar s) :
    ∀ x ∈ A, ∀ w ∈ conjSubgroup k A, x * w = w * x := by
  by_contra hnc
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts h hs).2
  have hAY : A ≤ Section3.Y A Abar s := by unfold Section3.Y; exact le_sup_left.trans le_sup_left
  set F := sec33Fix (Section3.Y A Abar s) (Section3.N A Abar s) s hYN with hF
  have hAF : A ≤ F := by
    intro a ha
    refine ⟨hAY ha, ?_⟩
    rw [sec32a_conj_eq_of_comm (hsA a ha), mul_inv_cancel]
    exact Subgroup.one_mem _
  have hAkF : conjSubgroup k A ≤ F := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 k A w).1 hw
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk (hAY ha)) (Subgroup.inv_mem _ hk)
    · set z := k⁻¹ * (s * k * s⁻¹) with hzdef
      have hsa : s * a * s⁻¹ = a := sec32a_conj_eq_of_comm (hsA a ha)
      have e : s * (k * a * k⁻¹) * s⁻¹ * (k * a * k⁻¹)⁻¹ =
          k * (z * a * z⁻¹ * a⁻¹) * k⁻¹ := by
        have e1 : s * (k * a * k⁻¹) * s⁻¹ = (s * k * s⁻¹) * (s * a * s⁻¹) * (s * k * s⁻¹)⁻¹ := by
          group
        have e2 : s * k * s⁻¹ = k * z := by rw [hzdef]; group
        rw [e1, hsa, e2, hzdef]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hYN k hk) _).mp (hz a (hAY ha))
  have hnc' : ¬ ∀ x ∈ conjSubgroup 1 A, ∀ w ∈ conjSubgroup k A, x * w = w * x :=
    fun hall => hnc fun x hx w hw => hall x (by rwa [conjSubgroup_one]) w hw
  have S := sec41_prop24 h hYN hNc (one_mem _) hk hnc'
  rw [conjSubgroup_one, conjSubgroup_one] at S
  obtain ⟨x, hxX, hx⟩ := S.exists_conj_eq
  obtain ⟨hxY, hxN⟩ := (sup_le hAF hAkF) hxX
  have hn : x⁻¹ * (s * x * s⁻¹ * x⁻¹) * x ∈ Section3.N A Abar s := by
    have := (Subgroup.mem_normalizer_iff.mp (hYN x⁻¹ (Subgroup.inv_mem _ hxY)) _).mp hxN
    simpa using this
  have hxn : s * x * s⁻¹ = x * (x⁻¹ * (s * x * s⁻¹ * x⁻¹) * x) := by group
  have hcomm := sec33_comm_of_fixed h hs hne hxY hn hxn
  exact hnc fun a ha w hw => hcomm a ha w (hx ▸ hw)

theorem sec33_tau_sq {Y N : Subgroup G} [hNn : (N.subgroupOf Y).Normal] {s : G}
    (hs : s ∈ normalizer (Y : Set G)) (hsN : s ∈ normalizer (N : Set G))
    (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G)) (hsq : s * s ∈ N) :
    sec33Tau hs hsN * sec33Tau hs hsN = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    show sec33Tau hs hsN (sec33Tau hs hsN (QuotientGroup.mk y)) = QuotientGroup.mk y
    rw [sec33Tau_mk, sec33Tau_mk, sec33_mk_eq_iff]
    have e : ((sec33ConjAut Y hs (sec33ConjAut Y hs y) : ↥Y) : G)⁻¹ * (y : G) =
        (s * s) * ((y : G)⁻¹ * (s * s)⁻¹ * (y : G)) := by
      simp only [sec33ConjAut_apply, mul_inv_rev, inv_inv, mul_assoc]
    rw [e]
    refine N.mul_mem hsq ?_
    have := (Subgroup.mem_normalizer_iff.mp (hYN (y : G)⁻¹ (Subgroup.inv_mem _ y.2)) _).mp
      (N.inv_mem hsq)
    simpa using this

theorem sec33_sq_of_comm {Q : Type} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hc : a * b = b * a) : (a * b) ^ 2 = 1 := by
  rw [sq]
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem sec33_not_central [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] {a₀ : G}
    (ha₀ : a₀ ∈ A) (ha₀L : a₀ ∉ Section3.A0 A Abar) :
    (QuotientGroup.mk ⟨a₀, sec32d_A_le_Y ha₀⟩ : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∉ Subgroup.center _ := by
  intro hcen
  obtain ⟨u, huAb, huL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hC.setup.Lb_le hC.setup.Lb_ne)
  have hodd := hC.setup.odd_orderOf_mul ha₀ ha₀L huAb huL
  have huY : u ∈ Section3.Y A Abar s := sec32d_Abar_le_Y huAb
  set x : ↥(Section3.Y A Abar s) := ⟨a₀, sec32d_A_le_Y ha₀⟩ with hx
  set y : ↥(Section3.Y A Abar s) := ⟨u, huY⟩ with hy
  have hxx : x * x = 1 := Subtype.ext (by simpa using hC.setup.sq_A ha₀)
  have hyy : y * y = 1 := Subtype.ext (by simpa using hC.setup.sq_Ab huAb)
  have hcomm := (Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk y)).symm
  have hsq : (QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
      (x * y)) ^ 2 = 1 := by
    rw [map_mul]
    refine sec33_sq_of_comm ?_ ?_ ?_
    · rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one]
    · rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hyy, QuotientGroup.mk_one]
    · exact hcomm
  have hdvd := orderOf_map_dvd (QuotientGroup.mk'
    ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) (x * y)
  have hord : orderOf (x * y) = orderOf (a₀ * u) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  have hodd' : Odd (orderOf (QuotientGroup.mk'
      ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) (x * y))) :=
    Odd.of_dvd_nat (hord ▸ hodd) hdvd
  have h2dvd := orderOf_dvd_of_pow_eq_one hsq
  have hone : QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
      (x * y) = 1 := by
    rw [← orderOf_eq_one_iff]
    rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h1 | h1
    · exact h1
    · rw [h1] at hodd'
      exact absurd hodd' (by decide)
  have hmem : a₀ * u ∈ Section3.N A Abar s := by
    have := (QuotientGroup.eq_one_iff _).mp hone
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hsC := sec32d_mem_centralizer hC hs
  have hNA := sec32d_N_le_normalizer hC hsC hmem
  have huN : u ∈ normalizer (A : Set G) := by
    have := mul_mem (Subgroup.inv_mem _ (Subgroup.le_normalizer ha₀)) hNA
    simpa using this
  apply huL
  rw [hC.abar0_eq]
  exact Subgroup.mem_inf.mpr ⟨huAb, huN⟩

theorem sec33_mem_center_iff {Y N : Subgroup G} [hNn : (N.subgroupOf Y).Normal]
    (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G)) (z : ↥Y) :
    (QuotientGroup.mk z : ↥Y ⧸ N.subgroupOf Y) ∈ Subgroup.center _ ↔
      ∀ y ∈ Y, (z : G) * y * (z : G)⁻¹ * y⁻¹ ∈ N := by
  rw [Subgroup.mem_center_iff]
  have key : ∀ y : ↥Y, ((y * z : ↥Y) : G)⁻¹ * ((z * y : ↥Y) : G) =
      ((y : G) * z)⁻¹ * ((z : G) * y * (z : G)⁻¹ * (y : G)⁻¹) * ((y : G) * z) := by
    intro y
    simp only [Subgroup.coe_mul]
    group
  constructor
  · intro h y hy
    have h1 := h (QuotientGroup.mk ⟨y, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, sec33_mk_eq_iff, key ⟨y, hy⟩] at h1
    have hyz : (y * (z : G)) ∈ Y := Subgroup.mul_mem _ hy z.2
    have := (Subgroup.mem_normalizer_iff.mp (hYN _ hyz) _).mp h1
    simpa [mul_assoc] using this
  · intro h g
    induction g using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, sec33_mk_eq_iff, key y]
      have hyz : ((y : G) * z) ∈ Y := Subgroup.mul_mem _ y.2 z.2
      have hyz' : ((y : G) * z)⁻¹ ∈ Y := Subgroup.inv_mem _ hyz
      have := (Subgroup.mem_normalizer_iff.mp (hYN _ hyz') _).mp (h y y.2)
      simpa using this

end CFSG.RankThree.GF2n.Tim77
