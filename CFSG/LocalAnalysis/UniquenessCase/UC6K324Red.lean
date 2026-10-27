module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem card_modEq_card_inf_centralizer {p : ℕ} [Fact p.Prime] {N Q : Subgroup G}
    (hQN : Q ≤ normalizer (N : Set G)) (hQ : IsPGroup p Q) :
    Nat.card N ≡ Nat.card ↥(N ⊓ centralizer (Q : Set G)) [MOD p] := by
  classical
  set Q' : Subgroup (normalizer (N : Set G)) := Q.subgroupOf (normalizer (N : Set G)) with hQ'
  have hQp : IsPGroup p Q' := hQ.comap_subtype
  have key := hQp.card_modEq_card_fixedPoints N
  have hfix : ∀ x : N, x ∈ MulAction.fixedPoints Q' N ↔ (x : G) ∈ centralizer (Q : Set G) := by
    intro x
    rw [MulAction.mem_fixedPoints, mem_centralizer_iff]
    constructor
    · intro h q hq
      have h1 := congrArg Subtype.val (h ⟨⟨q, hQN hq⟩, hq⟩)
      change q * (x : G) * q⁻¹ = x at h1
      calc q * (x : G) = q * x * q⁻¹ * q := by group
        _ = x * q := by rw [h1]
    · intro h g
      apply Subtype.ext
      change ((g : normalizer (N : Set G)) : G) * x * ((g : normalizer (N : Set G)) : G)⁻¹ = x
      have hg : ((g : normalizer (N : Set G)) : G) ∈ Q := g.2
      rw [h _ hg]
      group
  have e : MulAction.fixedPoints Q' N ≃ ↥(N ⊓ centralizer (Q : Set G)) :=
    { toFun := fun x => ⟨x.1, mem_inf.2 ⟨x.1.2, (hfix x.1).1 x.2⟩⟩
      invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩, (hfix _).2 (mem_inf.1 y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at key

theorem inf_ne_bot_of_dvd_card {p : ℕ} [hp : Fact p.Prime] {P N : Subgroup G}
    (hP : CFSG.Open.IsElemAbelian p P) (hPc : Nat.card P = p ^ CFSG.Open.pRank p (⊤ : Subgroup G))
    (hPN : P ≤ normalizer (N : Set G)) (hpN : p ∣ Nat.card N) : P ⊓ N ≠ ⊥ := by
  intro hbot
  have hmod := card_modEq_card_inf_centralizer hPN hP.isPGroup
  have hdvd : p ∣ Nat.card ↥(N ⊓ centralizer (P : Set G)) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpN))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have huN : (u : G) ∈ N := (mem_inf.1 u.2).1
  have huC : (u : G) ∈ centralizer (P : Set G) := (mem_inf.1 u.2).2
  have huo : orderOf (u : G) = p := by rw [Subgroup.orderOf_coe]; exact hu
  have hcomm : ∀ a ∈ P, ∀ b ∈ zpowers (u : G), a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a (u : G) from mem_centralizer_iff.1 huC a ha) k).eq
  have hZu : CFSG.Open.IsElemAbelian p (zpowers (u : G)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 a.2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 b.2
      change (a : G) * b = b * a
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self (u : G) i j).eq
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← huo, pow_orderOf_eq_one,
        one_zpow]
  have hE : CFSG.Open.IsElemAbelian p (P ⊔ zpowers (u : G)) := hP.sup_of_commute hZu hcomm
  have huP : (u : G) ∉ P := by
    intro h
    have h1 : (u : G) ∈ P ⊓ N := mem_inf.2 ⟨h, huN⟩
    rw [hbot, mem_bot] at h1
    rw [h1, orderOf_one] at huo
    exact hp.out.one_lt.ne huo
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hlt : Nat.card P < Nat.card ↥(P ⊔ zpowers (u : G)) := by
    by_contra hle
    push Not at hle
    have heq : P = P ⊔ zpowers (u : G) := eq_of_le_of_card_ge le_sup_left hle
    have hmem : (u : G) ∈ P ⊔ zpowers (u : G) := mem_sup_right (mem_zpowers (u : G))
    rw [← heq] at hmem
    exact huP hmem
  rw [hPc, hk] at hlt
  have hkm : CFSG.Open.pRank p (⊤ : Subgroup G) < k :=
    (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hlt
  have := CFSG.SectionRank.le_pRank hp.out.one_lt le_top hE hk
  omega

theorem le_of_dvd_card {p : ℕ} [Fact p.Prime] {X P N : Subgroup G} (hX : IsSimpleGroup ↥X)
    (hPX : P ≤ X) (hP : CFSG.Open.IsElemAbelian p P)
    (hPc : Nat.card P = p ^ CFSG.Open.pRank p (⊤ : Subgroup G))
    (hXN : X ≤ normalizer (N : Set G)) (hpN : p ∣ Nat.card N) : X ≤ N := by
  haveI hn : (N.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hXN g.2) n).1 hn⟩
  haveI := hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf X) with h | h
  · exfalso
    refine inf_ne_bot_of_dvd_card hP hPc (hPX.trans hXN) hpN (eq_bot_iff.2 fun x hx => ?_)
    have h1 : (⟨x, hPX (mem_inf.1 hx).1⟩ : X) ∈ N.subgroupOf X := (mem_inf.1 hx).2
    rw [h, mem_bot] at h1
    exact (mem_bot).2 (congrArg Subtype.val h1)
  · intro x hx
    have h1 : (⟨x, hx⟩ : X) ∈ N.subgroupOf X := by
      rw [h]
      exact mem_top _
    exact h1

end Rank

section Section

variable {G : Type*} [Group G] [Finite G]

theorem normal_map_pPrimeCore (p : ℕ) (M : Subgroup G) [M.Normal] :
    ((CFSG.pPrimeCore p ↥M).map M.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hfix := (Subgroup.characteristic_iff_map_eq.1 (CFSG.pPrimeCore_characteristic (p := p)
    (G := ↥M))) (MulAut.conjNormal (H := M) g)
  refine ⟨MulAut.conjNormal (H := M) g k, ?_, rfl⟩
  rw [← hfix]
  exact ⟨k, hk, rfl⟩

theorem conj_mem_map_conj {M : Subgroup G} [M.Normal] {K : Subgroup ↥M} (hK : K.Normal) (g : G)
    {m : G} (hm : m ∈ M) {h : G} (hh : h ∈ (K.map M.subtype).map (MulAut.conj g).toMonoidHom) :
    m * h * m⁻¹ ∈ (K.map M.subtype).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hh
  have hm' : g⁻¹ * m * g ∈ M := by
    have := (inferInstance : M.Normal).conj_mem m hm g⁻¹
    rwa [inv_inv] at this
  have hconj : (⟨g⁻¹ * m * g, hm'⟩ : ↥M) * k * (⟨g⁻¹ * m * g, hm'⟩ : ↥M)⁻¹ ∈ K :=
    hK.conj_mem k hk _
  refine ⟨_, ⟨_, hconj, rfl⟩, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.toMonoidHom_eq_coe, MulAut.conj_apply, coe_subtype,
    Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem isSimpleGroup_normalClosure_quot {p : ℕ} [hp : Fact p.Prime] {X P : Subgroup G}
    (hX : IsSimpleGroup ↥X) (hPX : P ≤ X) (hP : CFSG.Open.IsElemAbelian p P)
    (hPc : Nat.card P = p ^ CFSG.Open.pRank p (⊤ : Subgroup G)) (hpX : p ∣ Nat.card X) :
    IsSimpleGroup (↥(normalClosure (X : Set G)) ⧸
      CFSG.pPrimeCore p ↥(normalClosure (X : Set G))) := by
  classical
  set M := normalClosure (X : Set G) with hMdef
  set R := CFSG.pPrimeCore p ↥M with hRdef
  have hXM : X ≤ M := le_normalClosure
  have hpM : p ∣ Nat.card M := hpX.trans (Subgroup.card_dvd_of_le hXM)
  have hcopR : Nat.Coprime p (Nat.card R) := CFSG.pPrimeCore_coprime_card
  have key : ∀ K : Subgroup ↥M, K.Normal → p ∣ Nat.card K → K = ⊤ := by
    intro K hK hpK
    have hconj : ∀ g : G, ∀ x ∈ X, g⁻¹ * x * g ∈ K.map M.subtype := by
      intro g x hx
      set KG := (K.map M.subtype).map (MulAut.conj g).toMonoidHom with hKG
      have hcard : Nat.card KG = Nat.card K := by
        rw [hKG, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          Subgroup.card_map_of_injective M.subtype_injective]
      have hXN : X ≤ normalizer (KG : Set G) := by
        intro y hy
        rw [mem_normalizer_iff]
        intro h
        constructor
        · exact conj_mem_map_conj hK g (hXM hy)
        · intro h1
          have h2 := conj_mem_map_conj hK g (inv_mem (hXM hy)) h1
          have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
          rwa [e] at h2
      have hxKG := le_of_dvd_card hX hPX hP hPc hXN (hcard ▸ hpK) hx
      obtain ⟨_, ⟨k, hk, rfl⟩, hkx⟩ := hxKG
      have hkx' : (k : G) = g⁻¹ * x * g := by
        simp only [MonoidHom.coe_coe, MulEquiv.toMonoidHom_eq_coe, MulAut.conj_apply,
          coe_subtype] at hkx
        rw [← hkx]
        group
      exact ⟨k, hk, hkx'⟩
    have hMK : M ≤ K.map M.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
      have := hconj c⁻¹ x hx
      rwa [inv_inv] at this
    rw [eq_top_iff]
    intro m _
    obtain ⟨k, hk, hkm⟩ := hMK m.2
    have : k = m := Subtype.ext hkm
    exact this ▸ hk
  have hRtop : R ≠ ⊤ := by
    intro h
    have h1 : Nat.card R = Nat.card M := by
      rw [h, Subgroup.card_top]
    rw [h1] at hcopR
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcopR hpM
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top_of_normal := ?_ }
  · obtain ⟨x, hx⟩ : ∃ x : ↥M, x ∉ R := by
      by_contra h
      push Not at h
      exact hRtop (eq_top_iff.2 fun x _ => h x)
    refine ⟨QuotientGroup.mk' R x, 1, fun h => hx ?_⟩
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  · intro H hH
    set K := H.comap (QuotientGroup.mk' R) with hK
    have hKn : K.Normal := hH.comap _
    by_cases hpK : p ∣ Nat.card K
    · right
      have hKt := key K hKn hpK
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
      have hx : x ∈ K := by rw [hKt]; exact mem_top x
      exact hx
    · left
      have hKR : K ≤ R :=
        le_sSup ⟨hKn, (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpK⟩
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
      have hxR : x ∈ R := hKR hy
      rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxR

theorem eq_one_of_mem_pPrimeCore {p : ℕ} [hp : Fact p.Prime] {X : Subgroup G}
    (hX : IsSimpleGroup ↥X) (hpX : p ∣ Nat.card X) {x : G} (hx : x ∈ X)
    (hxR : (⟨x, le_normalClosure hx⟩ : ↥(normalClosure (X : Set G))) ∈
      CFSG.pPrimeCore p ↥(normalClosure (X : Set G))) : x = 1 := by
  classical
  set M := normalClosure (X : Set G) with hMdef
  set RG := (CFSG.pPrimeCore p ↥M).map M.subtype with hRG
  haveI : RG.Normal := normal_map_pPrimeCore p M
  haveI hn : (RG.subgroupOf X).Normal := inferInstance
  have hxRG : x ∈ RG := ⟨_, hxR, rfl⟩
  haveI := hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (RG.subgroupOf X) with h | h
  · have h1 : (⟨x, hx⟩ : X) ∈ RG.subgroupOf X := hxRG
    rw [h, mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    have hXR : X ≤ RG := fun y hy => by
      have h1 : (⟨y, hy⟩ : X) ∈ RG.subgroupOf X := by rw [h]; exact mem_top _
      exact h1
    have hcop : Nat.Coprime p (Nat.card RG) := by
      rw [hRG, Subgroup.card_map_of_injective M.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop
      (hpX.trans (Subgroup.card_dvd_of_le hXR))

theorem pRank_normalClosure_quot_le (p : ℕ) [hp : Fact p.Prime] (X : Subgroup G) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥(normalClosure (X : Set G)) ⧸
      CFSG.pPrimeCore p ↥(normalClosure (X : Set G)))) ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hR : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥(normalClosure (X : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 CFSG.pPrimeCore_coprime_card
  rw [CFSG.SectionRank.pRank_quotient_eq _ hR]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt _
    (normalClosure (X : Set G)).subtype_injective

end Section

end CFSG.LocalAnalysis.UniquenessCase.UCK
