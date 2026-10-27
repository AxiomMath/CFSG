module

public import CFSG.RankThree.PartOne.N143.JFacts

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem order_sl2_injective : Function.Injective (fun f : ℕ => 2 ^ f * (2 ^ (2 * f) - 1)) := by
  have hmono : StrictMono (fun f : ℕ => 2 ^ f * (2 ^ (2 * f) - 1)) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show 2 ^ n * (2 ^ (2 * n) - 1) < 2 ^ (n + 1) * (2 ^ (2 * (n + 1)) - 1)
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h2 : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      ring
    have h3 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [h2, h3]
    have h5 : 2 ^ (2 * n) - 1 < 4 * 2 ^ (2 * n) - 1 := by omega
    calc 2 ^ n * (2 ^ (2 * n) - 1) < 2 ^ n * (4 * 2 ^ (2 * n) - 1) :=
          Nat.mul_lt_mul_of_pos_left h5 (by omega)
      _ ≤ 2 * 2 ^ n * (4 * 2 ^ (2 * n) - 1) := by
          apply Nat.mul_le_mul_right
          omega
  exact hmono.injective

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_commutator {N : Subgroup G} {x : G} (hx : ∀ n ∈ N, x * n * x⁻¹ ∈ N) {k : G}
    (hk : k ∈ ⁅N, N⁆) : x * k * x⁻¹ ∈ ⁅N, N⁆ := by
  have hN : N.map (MulAut.conj x).toMonoidHom ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact hx n hn
  have h1 : (⁅N, N⁆).map (MulAut.conj x).toMonoidHom ≤ ⁅N, N⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hN hN
  exact h1 ⟨k, hk, rfl⟩

section Share

variable {p : ℕ} {A : Subgroup G}

theorem JGood.mem_autFixedInG {c : G} {J : Subgroup G} (h : JGood p A c J) {t : MulAut A}
    (ht : t ∈ torusImage A J) : c ∈ autFixedInG A t := by
  obtain ⟨w, hwJ, hwN, rfl⟩ := Sec12Three.mem_torusImage_iff.mp ht
  refine ⟨⟨c, h.hyp.c_mem⟩, ?_, rfl⟩
  show A.normalizerMonoidHom ⟨w, hwN⟩ ⟨c, h.hyp.c_mem⟩ = ⟨c, h.hyp.c_mem⟩
  apply Subtype.ext
  show w * c * w⁻¹ = c
  rw [← Sec12Three.comm_c_L h.hyp w hwJ]
  group

theorem JGood.centralizer_fixed_le_normalizer {c : G} {J : Subgroup G} (h : JGood p A c J)
    {t : MulAut A} (ht : t ∈ torusImage A J) :
    Subgroup.centralizer (autFixedInG A t : Set G) ≤ Subgroup.normalizer (J : Set G) := fun _ hx =>
  h.cent (Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 hx c (h.mem_autFixedInG ht)).symm))

theorem JGood.conj_mem_Kof {c : G} {J : Subgroup G} (h : JGood p A c J) {t : MulAut A}
    (ht : t ∈ torusImage A J) {x : G}
    (hx : x ∈ Subgroup.centralizer (autFixedInG A t : Set G)) {k : G} (hk : k ∈ Kof A J t) :
    x * k * x⁻¹ ∈ Kof A J t := by
  refine conj_mem_commutator (N := Nt A J t) (fun n hn => ?_) hk
  exact ⟨(Subgroup.mem_normalizer_iff.1 (h.centralizer_fixed_le_normalizer ht hx) n).1 hn.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn.2) (Subgroup.inv_mem _ hx)⟩

omit [Finite G] in
theorem Kof_le_centralizer (J : Subgroup G) (t : MulAut A) :
    Kof A J t ≤ Subgroup.centralizer (autFixedInG A t : Set G) := by
  have hNt : Nt A J t ≤ Subgroup.centralizer (autFixedInG A t : Set G) := inf_le_right
  have hK : Kof A J t ≤ Nt A J t := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  exact hK.trans hNt

theorem Kof_le_of_share {c' : G} {J J' : Subgroup G} (h' : JGood p A c' J')
    {t : MulAut A} (htJ' : t ∈ torusImage A J')
    (hsimple : IsSimpleGroup (Kof A J t)) {m : G} (hm1 : m ≠ 1) (hmK : m ∈ Kof A J t)
    (hmK' : m ∈ Kof A J' t) : Kof A J t ≤ Kof A J' t := by
  let N' : Subgroup (Kof A J t) := (Kof A J t ⊓ Kof A J' t).subgroupOf (Kof A J t)
  have hnorm : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Kof A J t ⊓ Kof A J' t := hn
    show ((g * n * g⁻¹ : Kof A J t) : G) ∈ Kof A J t ⊓ Kof A J' t
    refine ⟨(g * n * g⁻¹).2, ?_⟩
    show (g : G) * n * (g : G)⁻¹ ∈ Kof A J' t
    exact h'.conj_mem_Kof htJ' (Kof_le_centralizer J t g.2) hn'.2
  have hne : N' ≠ ⊥ := by
    intro hbot
    have : (⟨m, hmK⟩ : Kof A J t) ∈ N' := ⟨hmK, hmK'⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hm1 (congrArg Subtype.val this)
  have htop : N' = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal N').resolve_left hne
  intro k hk
  have : (⟨k, hk⟩ : Kof A J t) ∈ N' := by rw [htop]; trivial
  exact this.2

theorem Kof_eq_of_share (hKt1 : JLemmaKt1) {c c' : G} {J J' : Subgroup G} (h : JGood p A c J)
    (h' : JGood p A c' J') (hctx : ∀ t ∈ reflectionSet p A, Nat.card (autMovedInG A t) = p)
    {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J)
    (htJ' : t ∈ torusImage A J') {f f' : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) (hf' : p ∣ 2 ^ f' - 1)
    (hm' : StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 f') :
    Kof A J t = Kof A J' t := by
  obtain ⟨hs1, -, hM1⟩ := hKt1 G p A c J h t ht htJ f hf hm
  obtain ⟨hs2, -, hM2⟩ := hKt1 G p A c' J' h' t ht htJ' f' hf' hm'
  have hp := h.hyp.prime
  have hMcard := hctx t ht
  have hMne : ∃ m ∈ autMovedInG A t, m ≠ 1 := by
    by_contra hall
    push Not at hall
    have : autMovedInG A t = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      exact Subgroup.mem_bot.2 (hall m hm)
    rw [this, Subgroup.card_bot] at hMcard
    exact hp.one_lt.ne hMcard
  obtain ⟨m, hmM, hm1⟩ := hMne
  exact le_antisymm (Kof_le_of_share h' htJ' hs1 hm1 (hM1 hmM) (hM2 hmM))
    (Kof_le_of_share h htJ hs2 hm1 (hM2 hmM) (hM1 hmM))

theorem models_eq_of_share (hKt1 : JLemmaKt1) {c c' : G} {J J' : Subgroup G} (h : JGood p A c J)
    (h' : JGood p A c' J') (hctx : ∀ t ∈ reflectionSet p A, Nat.card (autMovedInG A t) = p)
    {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J)
    (htJ' : t ∈ torusImage A J') {f f' : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) (hf' : p ∣ 2 ^ f' - 1)
    (hm' : StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 f') : f = f' := by
  obtain ⟨-, hc1, -⟩ := hKt1 G p A c J h t ht htJ f hf hm
  obtain ⟨-, hc2, -⟩ := hKt1 G p A c' J' h' t ht htJ' f' hf' hm'
  have heq : Kof A J t = Kof A J' t := Kof_eq_of_share hKt1 h h' hctx ht htJ htJ' hf hm hf' hm'
  have hcard : 2 ^ f * (2 ^ (2 * f) - 1) = 2 ^ f' * (2 ^ (2 * f') - 1) := by
    rw [← hc1, ← hc2, heq]
  exact order_sl2_injective hcard

theorem JGood.exists_reflection {c : G} {J : Subgroup G} (h : JGood p A c J) :
    ∃ s ∈ reflectionSet p A, s ∈ torusImage A J := by
  by_contra hno
  push Not at hno
  have hbot : torusImage A J = ⊥ := by
    have h1 := h.facts12.three.1
    have h2 : (reflectionSet p A ∩ (torusImage A J : Set (MulAut A))) = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
      exact hno s
    rw [h2, Subgroup.closure_empty] at h1
    exact h1
  obtain ⟨e⟩ := h.weyl
  have := Nat.card_congr e.toEquiv
  rw [hbot, Subgroup.card_bot] at this
  simp [Nat.card_eq_fintype_card, Fintype.card_perm] at this
  revert this
  decide

theorem models_eq_all (hKt1 : JLemmaKt1) {c : G} {L : Subgroup G} (hctx : HessCtx p A c L)
    (hpair : KF134Pair) (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {J J' : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p A) (hJ' : J' ∈ thetaCompZeroStarE p A)
    {f f' : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) (hf' : p ∣ 2 ^ f' - 1)
    (hm' : StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 f') : f = f' := by
  have hmoved : ∀ t ∈ reflectionSet p A, Nat.card (autMovedInG A t) = p := fun t ht =>
    (hctx.facts13.reflection t ht).2.2
  obtain ⟨c1, h1⟩ := hgood J hJ
  obtain ⟨c2, h2⟩ := hgood J' hJ'
  obtain ⟨s, hs, hsJ⟩ := h1.exists_reflection
  obtain ⟨s', hs', hs'J'⟩ := h2.exists_reflection
  by_cases hss : s = s'
  · subst hss
    exact models_eq_of_share hKt1 h1 h2 hmoved hs hsJ hs'J' hf hm hf' hm'
  · have hnc : s * s' ≠ s' * s := hctx.hess s hs s' hs' hss
    obtain ⟨I, hI, hsI, hs'I⟩ := hpair G p A c L A hctx.hyp hctx.facts12 hctx.facts13 hctx.notFive
      (Or.inr ⟨rfl, hctx.allL3⟩) s hs s' hs' hnc
    obtain ⟨c3, h3⟩ := hgood I hI
    obtain ⟨fI, -, hfI, hmI⟩ := h3.model
    have e1 := models_eq_of_share hKt1 h1 h3 hmoved hs hsJ hsI hf hm hfI hmI
    have e2 := models_eq_of_share hKt1 h3 h2 hmoved hs' hs'I hs'J' hfI hmI hf' hm'
    exact e1.trans e2

end Share

end CFSG.RankThree.PartOne.N143
