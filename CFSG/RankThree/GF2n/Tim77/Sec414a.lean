module

public import CFSG.RankThree.GF2n.Tim77.Sec413
public import CFSG.RankThree.GF2n.Tim77.Sec49
public import CFSG.RankThree.GF2n.Tim77.Sec48
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

@[expose] def Sec414Comm (C D : Subgroup G) : Prop := ∀ a ∈ C, ∀ b ∈ D, a * b = b * a

@[expose] def Sec414D (A A0 : Subgroup G) : Set G :=
  {x | ∃ g : G, ∃ a ∈ A, a ∉ A0 ∧ x = g * a * g⁻¹}

structure Sec414Sys (A A0 : Subgroup G) : Prop where
  elem : IsElemAbelian 2 A
  ti : IsTI A
  a0_le : A0 ≤ A
  a0_ne : A0 ≠ ⊥
  a0_idx : A0.relIndex A = 2
  a0_norm : ∀ g ∈ normalizer (A : Set G), ∀ a ∈ A0, g * a * g⁻¹ ∈ A0
  linked : ∀ g : G, normalizerIn A (conjSubgroup g A) ≠ ⊥ →
    ¬ Sec414Comm A (conjSubgroup g A) → normalizerIn A (conjSubgroup g A) = A0
  four : ∀ a ∈ A, a ∉ A0 → ∀ g : G, ∀ y ∈ A, y ∉ A0 → orderOf (a * (g * y * g⁻¹)) ≠ 4
  four12 : ∀ a ∈ A, a ∉ A0 → ∀ g : G, ∀ x ∈ conjSubgroup g A, orderOf (a * x) = 4 →
    x ∈ normalizer (A : Set G)
  rootCent : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) →
    IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup g A)

variable [Finite G]

theorem Sec414Sys.of_ctx (h49 : Tim77Sec49Statement) (h412 : Tim77Sec412Statement)
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hA0 : Sec4A0LeCenterH A Abar) : Sec414Sys A (Section3.A0 A Abar) := by
  have hS : Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.M A Abar) := h.setup
  have h49' := h49 G A Abar S₀ B h hq hA0
  refine
    { elem := h.hyp.elemAbelian
      ti := h.hyp.ti
      a0_le := hS.L_le
      a0_ne := h.a0_ne_bot
      a0_idx := by rw [← hS.relIndex_Lb]; exact hq
      a0_norm := h49'.2.2.1
      linked := ?_
      four := sec413_of h412 G A Abar S₀ B h hq hA0
      four12 := h412 G A Abar S₀ B h hq hA0
      rootCent := h.hyp.rootTypeInCentralizer }
  intro g hN hnc
  set C := conjSubgroup g A with hC
  have hAeq : conjSubgroup g⁻¹ C = A := by
    rw [hC, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hNA : normalizerIn A C ≠ A := by
    intro hEq
    have hle : A ≤ normalizer (C : Set G) := by
      intro a ha
      have h1 : a ∈ normalizerIn A C := by rw [hEq]; exact ha
      unfold normalizerIn at h1
      exact (Subgroup.mem_inf.mp h1).2
    have hel := tim77_2_3 (isElemAbelian_conj h.hyp.elemAbelian g)
      (isTI_conjSubgroup h.hyp.ti g) (g := g⁻¹) (by rw [hAeq]; exact hle)
    apply hnc
    intro a ha c hc
    have hc' := congrArg Subtype.val (hel.1.is_comm.comm
      (⟨a, Subgroup.mem_sup_right (hAeq ▸ ha)⟩ : ↥(C ⊔ conjSubgroup g⁻¹ C))
      ⟨c, Subgroup.mem_sup_left hc⟩)
    exact hc'
  have S : Prop24Setup A C (normalizerIn A C) (normalizerIn C A)
      (normalizerIn A C ⊔ normalizerIn C A) :=
    { elem := h.hyp.elemAbelian
      ti := h.hyp.ti
      conj := ⟨g, rfl⟩
      hL := by unfold normalizerIn; rfl
      hLb := by unfold normalizerIn; rfl
      hM := rfl
      ne_bot := hN
      ne := hNA }
  obtain ⟨⟨x, hxLb⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.Lb_ne_bot
  have hx1 : x ≠ 1 := fun e => hx1' (Subtype.ext e)
  obtain ⟨hxC, hxN⟩ := S.mem_Lb.mp hxLb
  rcases h49'.2.2.2 x hxN hx1 ⟨g, hxC⟩ with hA0eq | hcen
  · rw [hA0eq]
    ext c
    constructor
    · intro hc
      have hcA : c ∈ A := S.L_le hc
      refine Subgroup.mem_inf.mpr ⟨hcA, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      rw [Set.mem_singleton_iff.mp hd]
      exact (S.comm_L_Lb hc hxLb).symm
    · intro hc
      obtain ⟨hcA, hcc⟩ := Subgroup.mem_inf.mp hc
      have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hcc x (Set.mem_singleton x)).symm
      exact S.mem_L_of_commute hcA hxC hx1 hcx
  · exfalso
    apply hNA
    apply le_antisymm S.L_le
    intro c hc
    exact S.mem_L_of_commute hc hxC hx1 (Subgroup.mem_centralizer_iff.mp hcen c hc)

theorem sec414Comm_conj_iff (g : G) (C D : Subgroup G) :
    Sec414Comm (conjSubgroup g C) (conjSubgroup g D) ↔ Sec414Comm C D := by
  constructor
  · intro hc a ha b hb
    have h1 := hc (g * a * g⁻¹) ((mem_conjSubgroup_conj_t77 g a C).2 ha) (g * b * g⁻¹)
      ((mem_conjSubgroup_conj_t77 g b D).2 hb)
    exact (conj_mul_comm_t77 g a b).1 h1
  · intro hc a ha b hb
    obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 g C a).1 ha
    obtain ⟨b', hb', rfl⟩ := (mem_conjSubgroup_exists_t77 g D b).1 hb
    exact (conj_mul_comm_t77 g a' b').2 (hc a' ha' b' hb')

theorem Sec414Sys.conj {A A0 : Subgroup G} (S : Sec414Sys A A0) (g : G) :
    Sec414Sys (conjSubgroup g A) (conjSubgroup g A0) where
  elem := isElemAbelian_conj S.elem g
  ti := isTI_conjSubgroup S.ti g
  a0_le := sec49_conjSubgroup_mono S.a0_le
  a0_ne := fun e => S.a0_ne ((conjSubgroup_eq_bot_t77 g A0).1 e)
  a0_idx := by rw [relIndex_conjSubgroup_t77]; exact S.a0_idx
  a0_norm := by
    intro h hh a ha
    obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 g A0 a).1 ha
    have hh' := (sec49_mem_normalizer_conj g h A).1 hh
    have h1 := S.a0_norm _ hh' a' ha'
    have e : h * (g * a' * g⁻¹) * h⁻¹ = g * ((g⁻¹ * h * g) * a' * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact (mem_conjSubgroup_conj_t77 g _ A0).2 h1
  linked := by
    intro k hN hnc
    rw [conjSubgroup_conj_twist g k A] at hN hnc ⊢
    rw [normalizerIn_conjSubgroup_t77] at hN ⊢
    rw [sec414Comm_conj_iff] at hnc
    have hN' : normalizerIn A (conjSubgroup (g⁻¹ * k * g) A) ≠ ⊥ :=
      fun e => hN (by rw [e, conjSubgroup_bot_t77])
    rw [S.linked _ hN' hnc]
  four := by
    intro a ha ha0 h y hy hy0
    obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 g A a).1 ha
    obtain ⟨y', hy', rfl⟩ := (mem_conjSubgroup_exists_t77 g A y).1 hy
    have ha0' : a' ∉ A0 := fun h0 => ha0 ((mem_conjSubgroup_conj_t77 g a' A0).2 h0)
    have hy0' : y' ∉ A0 := fun h0 => hy0 ((mem_conjSubgroup_conj_t77 g y' A0).2 h0)
    have e : g * a' * g⁻¹ * (h * (g * y' * g⁻¹) * h⁻¹) =
        g * (a' * ((g⁻¹ * h * g) * y' * (g⁻¹ * h * g)⁻¹)) * g⁻¹ := by group
    rw [e, orderOf_conjugate_t77]
    exact S.four a' ha' ha0' _ y' hy' hy0'
  four12 := by
    intro a ha ha0 k x hx h4
    obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 g A a).1 ha
    have ha0' : a' ∉ A0 := fun h0 => ha0 ((mem_conjSubgroup_conj_t77 g a' A0).2 h0)
    rw [conjSubgroup_conj_twist g k A] at hx
    obtain ⟨x', hx', rfl⟩ := (mem_conjSubgroup_exists_t77 g _ x).1 hx
    rw [show g * a' * g⁻¹ * (g * x' * g⁻¹) = g * (a' * x') * g⁻¹ by group,
      orderOf_conjugate_t77] at h4
    have := S.four12 a' ha' ha0' (g⁻¹ * k * g) x' hx' h4
    rw [sec49_mem_normalizer_conj, show g⁻¹ * (g * x' * g⁻¹) * g = x' by group]
    exact this
  rootCent := by
    intro k hk
    rw [conjSubgroup_conj_twist g k A, centralizer_conjSubgroup_eq] at hk ⊢
    exact isRootTypeIn_conjSubgroup_t77 g (S.rootCent _ ((conjSubgroup_le_conj_iff g).1 hk))

theorem sec414_prop24 {A C : Subgroup G} (hA : IsElemAbelian 2 A) (hti : IsTI A)
    (hC : ∃ g : G, C = conjSubgroup g A)
    (hN : normalizerIn A C ≠ ⊥) (hnc : ¬ Sec414Comm A C) :
    Prop24Setup A C (normalizerIn A C) (normalizerIn C A)
      (normalizerIn A C ⊔ normalizerIn C A) := by
  obtain ⟨g, rfl⟩ := hC
  set C := conjSubgroup g A with hC
  have hAeq : conjSubgroup g⁻¹ C = A := by
    rw [hC, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hNA : normalizerIn A C ≠ A := by
    intro hEq
    have hle : A ≤ normalizer (C : Set G) := by
      intro a ha
      have h1 : a ∈ normalizerIn A C := by rw [hEq]; exact ha
      unfold normalizerIn at h1
      exact (Subgroup.mem_inf.mp h1).2
    have hel := tim77_2_3 (isElemAbelian_conj hA g) (isTI_conjSubgroup hti g) (g := g⁻¹)
      (by rw [hAeq]; exact hle)
    apply hnc
    intro a ha c hc
    exact congrArg Subtype.val (hel.1.is_comm.comm
      (⟨a, Subgroup.mem_sup_right (hAeq ▸ ha)⟩ : ↥(C ⊔ conjSubgroup g⁻¹ C))
      ⟨c, Subgroup.mem_sup_left hc⟩)
  exact
    { elem := hA
      ti := hti
      conj := ⟨g, rfl⟩
      hL := by unfold normalizerIn; rfl
      hLb := by unfold normalizerIn; rfl
      hM := rfl
      ne_bot := hN
      ne := hNA }

namespace Sec414Sys

variable {A A0 : Subgroup G} (S : Sec414Sys A A0)
include S

theorem comm_A {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (S.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem sq_A {a : G} (ha : a ∈ A) : a * a = 1 := by
  rw [← sq]
  exact S.elem.2 a ha

theorem a0_ne_A : A0 ≠ A := by
  intro h
  have h1 := S.a0_idx
  rw [h, Subgroup.relIndex_self] at h1
  exact absurd h1 (by norm_num)

theorem exists_not_mem : ∃ a ∈ A, a ∉ A0 :=
  SetLike.exists_of_lt (lt_of_le_of_ne S.a0_le S.a0_ne_A)

theorem ne_one_of_not_mem {a : G} (ha0 : a ∉ A0) : a ≠ 1 := fun h => ha0 (h ▸ A0.one_mem)

theorem closure_diff : Subgroup.closure {x | x ∈ A ∧ x ∉ A0} = A := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · intro y hy
    obtain ⟨a, ha, ha0⟩ := S.exists_not_mem
    by_cases hy0 : y ∈ A0
    · have hay : a * y ∈ Subgroup.closure {x | x ∈ A ∧ x ∉ A0} := by
        apply Subgroup.subset_closure
        refine ⟨A.mul_mem ha hy, fun h => ha0 ?_⟩
        have := A0.mul_mem h (A0.inv_mem hy0)
        rwa [mul_inv_cancel_right] at this
      have h2 : a ∈ Subgroup.closure {x | x ∈ A ∧ x ∉ A0} := Subgroup.subset_closure ⟨ha, ha0⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) hay
      rwa [inv_mul_cancel_left] at this
    · exact Subgroup.subset_closure ⟨hy, hy0⟩

theorem mem_D_conj {x : G} (g : G) (hx : x ∈ Sec414D A A0) : g * x * g⁻¹ ∈ Sec414D A A0 := by
  obtain ⟨h, a, ha, ha0, rfl⟩ := hx
  exact ⟨g * h, a, ha, ha0, by group⟩

theorem D_sq {x : G} (hx : x ∈ Sec414D A A0) : x * x = 1 := by
  obtain ⟨h, a, ha, ha0, rfl⟩ := hx
  calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
    _ = 1 := by rw [S.sq_A ha]; group

theorem rel (g : G) :
    Sec414Comm A (conjSubgroup g A) ∨
    (normalizerIn A (conjSubgroup g A) = A0 ∧
      normalizerIn (conjSubgroup g A) A = conjSubgroup g A0) ∨
    (normalizerIn A (conjSubgroup g A) = ⊥ ∧ normalizerIn (conjSubgroup g A) A = ⊥ ∧
      ¬ Sec414Comm A (conjSubgroup g A)) := by
  by_cases hc : Sec414Comm A (conjSubgroup g A)
  · exact Or.inl hc
  right
  have hSg := S.conj g
  have hAeq : conjSubgroup g⁻¹ (conjSubgroup g A) = A := conjSubgroup_inv_conj_cancel g A
  have hnc2 : ¬ Sec414Comm (conjSubgroup g A) (conjSubgroup g⁻¹ (conjSubgroup g A)) := by
    rw [hAeq]
    exact fun h => hc (fun a ha b hb => (h b hb a ha).symm)
  have hX : normalizerIn (conjSubgroup g A) A ≠ ⊥ →
      normalizerIn (conjSubgroup g A) A = conjSubgroup g A0 := by
    intro hN2
    have := hSg.linked g⁻¹ (by rw [hAeq]; exact hN2) hnc2
    rwa [hAeq] at this
  by_cases hN : normalizerIn A (conjSubgroup g A) = ⊥
  · right
    refine ⟨hN, ?_, hc⟩
    by_contra hN2
    have hnc3 : ¬ Sec414Comm (conjSubgroup g A) A :=
      fun h => hc (fun a ha b hb => (h b hb a ha).symm)
    have S'' := sec414_prop24 hSg.elem hSg.ti ⟨g⁻¹, hAeq.symm⟩ hN2 hnc3
    exact S''.Lb_ne_bot hN
  · left
    refine ⟨S.linked g hN hc, hX ?_⟩
    exact (sec414_prop24 S.elem S.ti ⟨g, rfl⟩ hN hc).Lb_ne_bot

theorem comm_of_commute {a e : G} (ha : a ∈ A) (ha0 : a ∉ A0) (g : G) (he : e ∈ conjSubgroup g A)
    (he0 : e ∉ conjSubgroup g A0) (hae : a * e = e * a) : Sec414Comm A (conjSubgroup g A) := by
  have he1 : e ≠ 1 := fun h => he0 (h ▸ (conjSubgroup g A0).one_mem)
  have haN : a ∈ normalizer (conjSubgroup g A : Set G) :=
    mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti g) he he1 hae
  rcases S.rel g with hc | ⟨hlink, -⟩ | ⟨hfree, -⟩
  · exact hc
  · exfalso
    apply ha0
    rw [← hlink]
    unfold normalizerIn
    exact Subgroup.mem_inf.mpr ⟨ha, haN⟩
  · exfalso
    have : a ∈ normalizerIn A (conjSubgroup g A) := by
      unfold normalizerIn
      exact Subgroup.mem_inf.mpr ⟨ha, haN⟩
    rw [hfree, Subgroup.mem_bot] at this
    exact S.ne_one_of_not_mem ha0 this

theorem conj_a0 {m : G} (hm : m ∈ normalizer (A : Set G)) : conjSubgroup m A0 = A0 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 m A0 x).1 hx
    exact S.a0_norm m hm a ha
  · intro x hx
    rw [mem_conjSubgroup]
    have := S.a0_norm m⁻¹ (Subgroup.inv_mem _ hm) x hx
    simpa using this

end Sec414Sys

theorem sec414_exists_partner (h47 : Tim77Sec47Statement)
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (S : Sec414Sys A (Section3.A0 A Abar))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPA : P ≤ centralizer (A : Set G)) :
    ∃ f : G, f ∈ normalizer (A : Set G) ∧ f ≠ 1 ∧ f * f = 1 ∧
      ∀ k : G, conjSubgroup k A ≤ P →
        f ∈ normalizer (conjSubgroup k A : Set G) ∧
        ∀ x ∈ conjSubgroup k A, (f * x = x * f ↔ x ∈ conjSubgroup k (Section3.A0 A Abar)) := by
  have hPN : P ≤ normalizer (A : Set G) := hPA.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨n, hn, hnP⟩ := sec48_exists_conj_le_S0 h hP hPN
  have hAe : conjSubgroup n⁻¹ A = A := conjSubgroup_eq_self_iff.mpr (Subgroup.inv_mem _ hn)
  have h' := h.conj n⁻¹
  rw [hAe] at h'
  set Ab' := conjSubgroup n⁻¹ Abar with hAb'
  set S₀' := conjSubgroup n⁻¹ S₀ with hS₀'
  have hq' : Section3.q A Ab' = 2 := by
    have := section3_q_conj A Abar n⁻¹
    rw [hAe] at this
    rw [this]; exact hq
  have hA0' : Section3.A0 A Ab' = Section3.A0 A Abar := by
    have := section3_A0_conj A Abar n⁻¹
    rw [hAe] at this
    rw [this]
    exact S.conj_a0 (Subgroup.inv_mem _ hn)
  have hPS : P ≤ S₀' := by
    intro b hb
    rw [hS₀', mem_conjSubgroup]
    simpa using hnP b hb
  have hS' : Prop24Setup A Ab' (Section3.A0 A Ab') (Section3.Abar0 A Ab') (Section3.M A Ab') :=
    h'.setup
  obtain ⟨⟨f, hfL⟩, hf1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS'.Lb_ne_bot
  have hf1 : f ≠ 1 := fun e => hf1' (Subtype.ext e)
  have hfAb : f ∈ Ab' := hS'.Lb_le hfL
  have hfN : f ∈ normalizer (A : Set G) := (hS'.mem_Lb.mp hfL).2
  obtain ⟨ĝ, hĝ⟩ := h'.exists_abar_eq
  refine ⟨f, hfN, hf1, hS'.sq_Ab hfAb, fun k hk => ?_⟩
  set C := conjSubgroup k A with hC
  have hfC : f ∈ normalizer (C : Set G) :=
    h47 G A Ab' S₀' (conjSubgroup n⁻¹ B) h' hq' C ⟨k, rfl⟩ (hk.trans hPS) hfL
  have hSk := S.conj k
  have hCAb : conjSubgroup (ĝ * k⁻¹) C = Ab' := by
    rw [hC, ← conjSubgroup_mul, inv_mul_cancel_right, hĝ]
  have hnc1 : ¬ Sec414Comm Ab' C := by
    intro hcomm
    have hAC : A ≤ centralizer (C : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp (hPA (hk hc)) a ha).symm
    have hAbC : Ab' ≤ centralizer (C : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (hcomm b hb c hc).symm
    obtain ⟨x, hxX, hxeq⟩ := hS'.exists_conj_eq
    have hxC : x ∈ centralizer (C : Set G) := (sup_le hAC hAbC) hxX
    have hrt := hSk.rootCent k⁻¹ (by rw [conjSubgroup_inv_conj_cancel]; exact hAC)
    rw [conjSubgroup_inv_conj_cancel] at hrt
    have hN : normalizerIn A (conjSubgroup x A) ≠ ⊥ := by
      rw [← hxeq]; exact h'.a0_ne_bot
    have h4 := hrt.2.2.2 x hxC hN
    obtain ⟨a₁, ha₁, ha₁L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hS'.L_le hS'.ne)
    obtain ⟨⟨b₁, hb₁⟩, hb₁1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS'.Ab_ne_bot
    have hb₁1 : b₁ ≠ 1 := fun e => hb₁1' (Subtype.ext e)
    exact ha₁L (hS'.mem_L_of_commute ha₁ hb₁ hb₁1 (h4 a₁ ha₁ b₁ (hxeq ▸ hb₁)))
  have hnc1' : ¬ Sec414Comm C Ab' := fun hc => hnc1 (fun a ha b hb => (hc b hb a ha).symm)
  have hfN' : normalizerIn Ab' C ≠ ⊥ := by
    intro hbot
    have : f ∈ normalizerIn Ab' C := by
      unfold normalizerIn; exact Subgroup.mem_inf.mpr ⟨hfAb, hfC⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hf1 this
  have hlink : normalizerIn C Ab' = conjSubgroup k (Section3.A0 A Abar) := by
    rcases hSk.rel (ĝ * k⁻¹) with hc | ⟨hl, -⟩ | ⟨-, hfree, -⟩
    · rw [hCAb] at hc; exact absurd hc hnc1'
    · rw [hCAb] at hl; exact hl
    · rw [hCAb] at hfree; exact absurd hfree hfN'
  have hne : normalizerIn C Ab' ≠ ⊥ := by
    rw [hlink]
    exact fun e => S.a0_ne ((conjSubgroup_eq_bot_t77 k _).1 e)
  have S3 := sec414_prop24 hSk.elem hSk.ti ⟨ĝ * k⁻¹, hCAb.symm⟩ hne hnc1'
  refine ⟨hfC, fun x hx => ⟨fun hxf => ?_, fun hx0 => ?_⟩⟩
  · rw [← hlink]
    exact S3.mem_L_of_commute hx hfAb hf1 hxf.symm
  · rw [← hlink] at hx0
    exact (S3.comm_L_Lb hx0 (S3.mem_Lb.mpr ⟨hfAb, hfC⟩)).symm

end CFSG.RankThree.GF2n.Tim77
