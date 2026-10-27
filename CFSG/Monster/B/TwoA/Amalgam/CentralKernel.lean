module

public import CFSG.Monster.B.TwoA.Amalgam.Chamber
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.TwoA.Amalgam.Flag1
public import CFSG.Monster.B.TwoA.Unitary.Twenty
public import CFSG.Monster.B.TwoA.Amalgam.CosetStepBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

theorem mem_normalCore' {G : Type*} [Group G] {H : Subgroup G} {a : G} :
    a ∈ H.normalCore ↔ ∀ b : G, b * a * b⁻¹ ∈ H := Iff.rfl

@[expose] def chamberKernel :
    Subgroup Dfull := ((Bam.subgroupOf Eam).normalCore).map Eam.subtype

theorem mem_chamberKernel_iff
    {g : Dfull} :
    g ∈ chamberKernel ↔ g ∈ Eam ∧ ∀ x ∈ Eam, x * g * x⁻¹ ∈ Bam := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, fun x hx => ?_⟩
    have h := (mem_normalCore'.1 hg') ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 h
  · rintro ⟨hgE, hg⟩
    exact ⟨⟨g, hgE⟩, mem_normalCore'.2 fun x => Subgroup.mem_subgroupOf.2 (hg x x.2), rfl⟩

theorem chamberKernel_le_Bam :
    chamberKernel ≤ Bam := fun g hg => by
  have h := (mem_chamberKernel_iff.1 hg).2 1 Eam.one_mem
  rwa [one_mul, inv_one, mul_one] at h

theorem conj_mem_chamberKernel
    {g x : Dfull} (hg : g ∈ chamberKernel) (hx : x ∈ Eam) :
    x * g * x⁻¹ ∈ chamberKernel := by
  rw [mem_chamberKernel_iff] at hg ⊢
  refine ⟨Eam.mul_mem (Eam.mul_mem hx hg.1) (Eam.inv_mem hx), fun y hy => ?_⟩
  have h := hg.2 (y * x) (Eam.mul_mem hy hx)
  rwa [show y * x * g * (y * x)⁻¹ = y * (x * g * x⁻¹) * y⁻¹ by group] at h

theorem cQ_mem_chamberKernel :
    cQ ∈ chamberKernel := by
  rw [mem_chamberKernel_iff]
  refine ⟨cQ_mem_Eam, fun x hx => ?_⟩
  have hc : x * cQ = cQ * x := Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hx)
  rw [hc, mul_inv_cancel_right]
  exact Nc_le_Bam 0 (Nc_zero ▸ cQ_mem_N1)

theorem chamberKernel_le_N1 :
    chamberKernel ≤ N1 := by
  intro g hg
  have hgB := chamberKernel_le_Bam hg
  have hgP1 : g ∈ Pc 0 := Bam_le_Pc 0 hgB
  have hcore : (⟨g, hgP1⟩ : Pc 0) ∈ ((Pc 1).subgroupOf (Pc 0)).normalCore := by
    rw [mem_normalCore']
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact Bam_le_Pc 1 ((mem_chamberKernel_iff.1 hg).2 x (Pc_le_Eam 0 x.2))
  rw [normalCore_Pc_one, Subgroup.mem_subgroupOf, Nc_zero] at hcore
  exact hcore

@[expose] def kImage :
    Submodule (ZMod 2) Unitary.sigmaPerp where
  carrier := {x | ∃ e : Ehat, (e : Dfull) ∈ chamberKernel ∧ psiW e = x.1}
  add_mem' := by
    rintro _ _ ⟨e, he, h1⟩ ⟨e', he', h2⟩
    exact ⟨e * e', chamberKernel.mul_mem he he', by rw [psiW_mul, h1, h2]; rfl⟩
  zero_mem' := ⟨1, chamberKernel.one_mem, psiW_one⟩
  smul_mem' := by
    intro t x hx
    rcases zmod2_cases t with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, chamberKernel.one_mem, psiW_one⟩
    · rwa [one_smul]

theorem kImage_invariant
    (u : Unitary.Usig) {x : Unitary.sigmaPerp} (hx : x ∈ kImage) :
    Unitary.perpEnd u x ∈ kImage := by
  obtain ⟨e, he, hex⟩ := hx
  obtain ⟨p, hp⟩ := p1Proj_surjective u
  have hpg : jhatToKv0 ⟨p, P1_le_Jhat p.2⟩ = u := by
    have h := congrArg Subtype.val hp
    rwa [coe_p1Proj] at h
  have hpJ : (p : Dfull) ∈ Jhat := P1_le_Jhat p.2
  refine ⟨⟨(p : Dfull)⁻¹ * e * p, conj_mem_Ehat hpJ e.2⟩, ?_, ?_⟩
  · have h := conj_mem_chamberKernel he (Eam.inv_mem (Pc_le_Eam 0 p.2))
    rwa [inv_inv] at h
  · rw [psiW_conj hpJ e.2, hpg, hex]
    rfl

@[expose] def kImageQ :

    Submodule (ZMod 2) Unitary.W20 := kImage.map Unitary.sigLine.mkQ

theorem eq_bot_or_eq_top_of_adjoin {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {T : Set (Module.End K V)} (hT : Algebra.adjoin K T = ⊤) {S : Submodule K V}
    (hS : ∀ f ∈ T, ∀ v ∈ S, f v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have hall : ∀ f : Module.End K V, ∀ v ∈ S, f v ∈ S := by
    intro f
    have hf : f ∈ Algebra.adjoin K T := hT ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem f hf => exact hS f hf
    | algebraMap r =>
      intro v hv
      rw [Module.algebraMap_end_apply]
      exact S.smul_mem r hv
    | add f g _ _ hf hg => exact fun v hv => S.add_mem (hf v hv) (hg v hv)
    | mul f g _ _ hf hg => exact fun v hv => hf _ (hg v hv)
  by_cases h : S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hs0
    rw [eq_top_iff]
    intro v _
    have h1 := hall ((LinearMap.toSpanSingleton K V v).comp φ) s hs
    rwa [LinearMap.comp_apply, hφ, LinearMap.toSpanSingleton_apply, one_smul] at h1

theorem kImageQ_eq :
    kImageQ = ⊥ ∨ kImageQ = ⊤ := by
  apply eq_bot_or_eq_top_of_adjoin Unitary.adjoin_w20End
  rintro _ ⟨u, rfl⟩ _ ⟨x, hx, rfl⟩
  exact ⟨Unitary.perpEnd u x, kImage_invariant u hx, rfl⟩

theorem mem_Ehat_of_chamberKernel
    {g : Dfull} (hg : g ∈ chamberKernel) : g ∈ Ehat :=
  (chamberKernel_le_N1 hg).1

theorem psiW_mem_sigmaPerp_of_ker
    {g : Dfull} (hg : g ∈ chamberKernel) :
    psiW ⟨g, mem_Ehat_of_chamberKernel hg⟩ ∈ Unitary.sigmaPerp :=
  psiW_mem_sigmaPerp (chamberKernel_le_N1 hg)

theorem cases_of_psiW_mem_sigLine
    {e : Ehat} (h : psiW e = 0 ∨ psiW e = Unitary.sigmaW) :
    (e : Dfull) = 1 ∨ (e : Dfull) = xhat ∨ (e : Dfull) = cQ ∨ (e : Dfull) = xhat * cQ := by
  rcases h with h | h
  · rcases (psiW_eq_zero_iff e).1 h with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
  · have h2 : psiW (e * cE⁻¹) = 0 := by
      rw [psiW_mul, psiW_inv, h, psiW_cE, add_neg_cancel]
    rcases (psiW_eq_zero_iff _).1 h2 with h1 | h1
    · have e1 : (e : Dfull) * cQ⁻¹ = 1 := congrArg Subtype.val h1
      exact Or.inr (Or.inr (Or.inl (mul_inv_eq_one.1 e1)))
    · have e1 : (e : Dfull) * cQ⁻¹ = xhat := congrArg Subtype.val h1
      exact Or.inr (Or.inr (Or.inr (mul_inv_eq_iff_eq_mul.1 e1)))

theorem wFr_ne_sigmaW :
    wFr ≠ Unitary.sigmaW := by
  rw [wFr_eq_decW, Unitary.sigmaW_eq_decW]
  intro h
  have := CFSG.Monster.B.Co2.decW_injective (by norm_num) (by norm_num) h
  norm_num at this

theorem mem_sigLine_cases
    {x : Unitary.sigmaPerp} (hx : x ∈ Unitary.sigLine) :
    (x : Wv v0) = 0 ∨ (x : Wv v0) = Unitary.sigmaW := by
  rw [Unitary.sigLine, Submodule.mem_span_singleton] at hx
  obtain ⟨t, rfl⟩ := hx
  rcases zmod2_cases t with rfl | rfl
  · left
    rw [zero_smul, ZeroMemClass.coe_zero]
  · right
    rw [one_smul]
    rfl

theorem psiW_cases_of_bot
    (hb : kImageQ = ⊥) {g : Dfull} (hg : g ∈ chamberKernel) :
    psiW ⟨g, mem_Ehat_of_chamberKernel hg⟩ = 0 ∨
      psiW ⟨g, mem_Ehat_of_chamberKernel hg⟩ = Unitary.sigmaW := by
  have hq : Unitary.sigLine.mkQ (⟨psiW ⟨g, mem_Ehat_of_chamberKernel hg⟩,
      psiW_mem_sigmaPerp_of_ker hg⟩ : Unitary.sigmaPerp) ∈ kImageQ :=
    Submodule.mem_map_of_mem ⟨⟨g, mem_Ehat_of_chamberKernel hg⟩, hg, rfl⟩
  rw [hb] at hq
  have h0 := (Submodule.mem_bot (ZMod 2)).1 hq
  exact mem_sigLine_cases ((Submodule.Quotient.mk_eq_zero Unitary.sigLine).1 h0)

theorem xhat_not_mem_chamberKernel
    (hb : kImageQ = ⊥) : xhat ∉ chamberKernel := by
  intro hx
  have h := conj_mem_chamberKernel hx (Pc_le_Eam 1 tauhat_mem_P2)
  rw [tauhat_conj_xhat'] at h
  have hc := psiW_cases_of_bot hb h
  have e : psiW ⟨xhat * yhat, mem_Ehat_of_chamberKernel h⟩ = wFr := by
    rw [show (⟨xhat * yhat, mem_Ehat_of_chamberKernel h⟩ : Ehat) = xhatE * yhatE from rfl,
      psiW_mul, psiW_xhatE, psiW_yhat, zero_add]
  rw [e] at hc
  rcases hc with hc | hc
  · exact wFr_ne_zero hc
  · exact wFr_ne_sigmaW hc

theorem uhat_mem_N1 :
    uhat ∈ N1 := by
  have hA : uhat ∈ A8 := Subgroup.subset_closure (Set.mem_insert_of_mem _
    (Subgroup.subset_closure (by simp)))
  exact ⟨uhat_mem_Ehat, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 cQ_mem_centralizer_A8 uhat hA)⟩

theorem conj_tauhat_mem_Ehat
    {d : Dfull}
    (hd : d = 1 ∨ d = xhat ∨ d = cQ ∨ d = xhat * cQ) : tauhat * d * tauhat⁻¹ ∈ Ehat := by
  have hx : tauhat * xhat * tauhat⁻¹ ∈ Ehat := by
    rw [tauhat_conj_xhat']
    exact Ehat.mul_mem (Vhat_le_Ehat xhat_mem_Vhat) (Vhat_le_Ehat yhat_mem_Vhat)
  have hc : tauhat * cQ * tauhat⁻¹ ∈ Ehat := by
    rw [show tauhat * cQ * tauhat⁻¹ = cQ by rw [cQ, tauhat_mul_dhat, mul_inv_cancel_right]]
    exact cQ_mem_Ehat
  rcases hd with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Ehat.one_mem
  · exact hx
  · exact hc
  · rw [show tauhat * (xhat * cQ) * tauhat⁻¹ =
        (tauhat * xhat * tauhat⁻¹) * (tauhat * cQ * tauhat⁻¹) by group]
    exact Ehat.mul_mem hx hc

theorem not_kImageQ_top :
    kImageQ ≠ ⊤ := by
  intro ht
  have hq : Unitary.sigLine.mkQ (⟨psiW ⟨uhat, uhat_mem_N1.1⟩, psiW_mem_sigmaPerp uhat_mem_N1⟩ :
      Unitary.sigmaPerp) ∈ kImageQ := by
    rw [ht]
    exact Submodule.mem_top
  obtain ⟨x, ⟨e, he, hex⟩, hxe⟩ := hq
  have hxe' := (Submodule.Quotient.eq Unitary.sigLine).1 hxe
  have hd0 := mem_sigLine_cases hxe'
  have hd : psiW (e⁻¹ * ⟨uhat, uhat_mem_N1.1⟩) = 0 ∨
      psiW (e⁻¹ * ⟨uhat, uhat_mem_N1.1⟩) = Unitary.sigmaW := by
    have hsub : ((x - ⟨psiW ⟨uhat, uhat_mem_N1.1⟩, psiW_mem_sigmaPerp uhat_mem_N1⟩ :
        Unitary.sigmaPerp) : Wv v0) = psiW e - psiW ⟨uhat, uhat_mem_N1.1⟩ := by
      rw [Submodule.coe_sub, ← hex]
    rw [psiW_mul, psiW_inv]
    rw [hsub] at hd0
    rcases hd0 with h | h
    · left
      rw [sub_eq_zero] at h
      rw [h, neg_add_cancel]
    · right
      rw [← h, sub_eq_add_neg, ZModModule.neg_eq_self (psiW ⟨uhat, uhat_mem_N1.1⟩),
        ZModModule.neg_eq_self (psiW e), add_comm]
  have hcase := cases_of_psiW_mem_sigLine hd
  have hdE := conj_tauhat_mem_Ehat hcase
  have heK : tauhat * e * tauhat⁻¹ ∈ Ehat :=
    mem_Ehat_of_chamberKernel (conj_mem_chamberKernel he (Pc_le_Eam 1 tauhat_mem_P2))
  apply ghat8_not_mem_Ehat
  have e1 : ghat8 = (tauhat * e * tauhat⁻¹) *
      (tauhat * ((e⁻¹ * ⟨uhat, uhat_mem_N1.1⟩ : Ehat) : Dfull) * tauhat⁻¹) := by
    rw [← tauhat_conj_uhat]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e1]
  exact Ehat.mul_mem heK hdE

theorem chamberKernel_eq :
    chamberKernel = Subgroup.zpowers cQ := by
  have hb : kImageQ = ⊥ := kImageQ_eq.resolve_right not_kImageQ_top
  apply le_antisymm
  · intro g hg
    have hc := cases_of_psiW_mem_sigLine (psiW_cases_of_bot hb hg)
    rcases hc with h | h | h | h
    · have h' : g = 1 := h
      rw [h']
      exact Subgroup.one_mem _
    · have h' : g = xhat := h
      rw [h'] at hg
      exact absurd hg (xhat_not_mem_chamberKernel hb)
    · have h' : g = cQ := h
      rw [h']
      exact Subgroup.mem_zpowers _
    · exfalso
      have h' : g = xhat * cQ := h
      apply xhat_not_mem_chamberKernel hb
      have e2 : xhat = g * cQ⁻¹ := by rw [h', mul_inv_cancel_right]
      rw [e2]
      exact chamberKernel.mul_mem hg (chamberKernel.inv_mem cQ_mem_chamberKernel)
  · rw [Subgroup.zpowers_le]
    exact cQ_mem_chamberKernel

theorem short_F4_chamber_action_central_kernel :
    ((Bam.subgroupOf Eam).normalCore).map Eam.subtype = Subgroup.zpowers cQ ∧
    Nat.card (Subgroup.zpowers cQ) = 2 ∧
    (∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ) ∧
    (∀ ch ch' : Chamber, ∃ g : Eam, chamberMul ch g = ch') := by
  refine ⟨chamberKernel_eq, ?_, fun g => ?_, fun ch ch' => ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact cQ_mul_self) cQ_ne_one]
  · have key : ∀ x : Eam, ((x * (x * g)⁻¹ : Eam) : Dfull)⁻¹ = (x : Dfull) * g * (x : Dfull)⁻¹ :=
      fun x => by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    rw [← chamberKernel_eq, mem_chamberKernel_iff]
    constructor
    · intro h
      refine ⟨g.2, fun x hx => ?_⟩
      have h1 := h (chamberOf ⟨x, hx⟩)
      rw [chamberMul_chamberOf, chamberOf_eq_iff] at h1
      have h2 := Bam.inv_mem h1
      rwa [key ⟨x, hx⟩] at h2
    · rintro ⟨-, h⟩ ch
      obtain ⟨x, rfl⟩ := chamberOf_surjective ch
      rw [chamberMul_chamberOf, chamberOf_eq_iff]
      have h1 := Bam.inv_mem (h x x.2)
      rwa [← key x, inv_inv] at h1
  · obtain ⟨x, rfl⟩ := chamberOf_surjective ch
    obtain ⟨y, rfl⟩ := chamberOf_surjective ch'
    exact ⟨x⁻¹ * y, by rw [chamberMul_chamberOf, mul_inv_cancel_left]⟩

end CFSG.Monster.B.TwoA.Amalgam
