module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace TI

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_iff_conj {H : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ conjSubgroup g H = H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem conj_eq_of_mem_M {M : Subgroup G} {g : G} (hg : g ∈ M) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M :=
  Setting.map_conj_eq_of_normalized (fun _ hx => pCoreOf_normalized M hg hx)
    (fun _ hx => pCoreOf_normalized M (M.inv_mem hg) hx)

theorem conj_le_TOf {M : Subgroup G}
    (hQab : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M)
    {a g : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (ha1 : a ≠ 1)
    (hag : g⁻¹ * a * g ∈ CFSG.Open.pCoreOf 2 M) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ TOf M a := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  set q : G := g⁻¹ * a * g with hq
  have hq1 : q ≠ 1 := by
    intro h
    apply ha1
    have : a = g * q * g⁻¹ := by rw [hq]; group
    rw [this, h]
    group
  have hMa : ∀ k : G, k * a * k⁻¹ = a → k ∈ M := fun k hk =>
    hH a ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc k * a = (k * a * k⁻¹) * k := by group
        _ = a * k := by rw [hk]))
  have hMq : ∀ k : G, k * q * k⁻¹ = q → k ∈ M := fun k hk =>
    hH q hag hq1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc k * q = (k * q * k⁻¹) * k := by group
        _ = q * k := by rw [hk]))
  have hU2 : IsPGroup 2 (conjSubgroup g Q) := (isPGroup_pCoreOf' M).map _
  have hUC : conjSubgroup g Q ≤
      M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    have hcomm : u * a * u⁻¹ = a := by
      have h1 := hQab _ hu' _ hag
      have h2 : u * a = a * u :=
        calc u * a = g * ((g⁻¹ * u * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
          _ = a * u := by group
      calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [h2]
        _ = a := by group
    exact Subgroup.mem_inf.2 ⟨hMa u hcomm, mem_centralizer_zpowers_iff.2 hcomm⟩
  have hnorm : ∀ k ∈ M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G),
      ∀ u ∈ conjSubgroup g Q, k * u * k⁻¹ ∈ conjSubgroup g Q := by
    intro k hk u hu
    have hka : k * a * k⁻¹ = a := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
    have hkq : (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = q := by
      calc (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * a * k⁻¹) * g := by rw [hq]; group
        _ = q := by rw [hka]
    have hk'M : g⁻¹ * k * g ∈ M := hMq _ hkq
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    refine mem_conjSubgroup.2 ?_
    have e : g⁻¹ * (k * u * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * u * g) * (g⁻¹ * k * g)⁻¹ := by
      group
    rw [e]
    exact pCoreOf_normalized M hk'M hu'
  exact le_pCoreOf_of_normalized hUC hnorm hU2

theorem weaklyClosed_of_cent {Q B : Subgroup G} (hBQ : B ≤ Q) (hB : B ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ c : G, (∀ b ∈ B, c * b = b * c) → c ∈ Q)
    (hNQB : Subgroup.normalizer (B : Set G) = Subgroup.normalizer (Q : Set G))
    (hTI : ∀ g : G, Q ⊓ conjSubgroup g Q ≠ ⊥ → conjSubgroup g Q = Q) :
    WeaklyClosedIn B (Subgroup.normalizer (B : Set G)) := by
  classical
  refine ⟨Subgroup.le_normalizer, fun g hg => ?_⟩
  set U : Subgroup G := conjSubgroup g B with hU
  have hUN : U ≤ Subgroup.normalizer (Q : Set G) := hNQB ▸ hg
  have hU2 : IsPGroup 2 U := (isPGroup_of_le hQ2 hBQ).map _
  have hN2 : IsPGroup 2 (Q ⊔ U : Subgroup G) := hQ2.to_sup_of_normal_left' hU2 hUN
  have : Group.IsNilpotent ↥(Q ⊔ U : Subgroup G) := hN2.isNilpotent
  have hQN : Q ≤ Q ⊔ U := le_sup_left
  have : (Q.subgroupOf (Q ⊔ U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 (sup_le Subgroup.le_normalizer hUN)
  have hQne : Q ≠ ⊥ := fun hbot => hB (le_bot_iff.1 (hbot ▸ hBQ))
  have hne : Q.subgroupOf (Q ⊔ U) ≠ ⊥ := by
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨(q : G), hQN q.2⟩, Subgroup.mem_subgroupOf.2 q.2⟩, ?_⟩
    intro h
    apply hq1
    have := congrArg (fun z : ↥(Q.subgroupOf (Q ⊔ U)) => ((z : ↥(Q ⊔ U)) : G)) h
    exact Subtype.ext this
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  have hzQ : ((z : ↥(Q ⊔ U)) : G) ∈ Q := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz).1
  have hzc : ∀ m ∈ Q ⊔ U, m * ((z : ↥(Q ⊔ U)) : G) = ((z : ↥(Q ⊔ U)) : G) * m := fun m hm =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hz).2 ⟨m, hm⟩)
  have hz1' : ((z : ↥(Q ⊔ U)) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  set y : G := ((z : ↥(Q ⊔ U)) : G) with hy
  have hyU : y ∈ conjSubgroup g Q := by
    refine mem_conjSubgroup.2 (hcent _ fun b hb => ?_)
    have hgb : g * b * g⁻¹ ∈ U := by
      refine mem_conjSubgroup.2 ?_
      have : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rw [this]
      exact hb
    have h1 := hzc _ ((le_sup_right : U ≤ Q ⊔ U) hgb)
    calc g⁻¹ * y * g * b = g⁻¹ * (y * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * y) * g := by rw [h1]
      _ = b * (g⁻¹ * y * g) := by group
  have hbot : Q ⊓ conjSubgroup g Q ≠ ⊥ := by
    intro h
    have : y ∈ Q ⊓ conjSubgroup g Q := Subgroup.mem_inf.2 ⟨hzQ, hyU⟩
    rw [h] at this
    exact hz1' (Subgroup.mem_bot.1 this)
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := mem_normalizer_iff_conj.2 (hTI g hbot)
  exact mem_normalizer_iff_conj.1 (hNQB ▸ hgQ)

theorem card_le_two_of_fix {d : ℕ} {i j : Fin d} (hij : i ≠ j) {N : Subgroup (Perm (Fin d))}
    (hNI : N ≤ setStab ({i, j} : Finset (Fin d)))
    (hfix : ∀ σ ∈ N, ∀ x, x ≠ i → x ≠ j → σ x = x) : Nat.card N ≤ 2 := by
  classical
  have hcases : ∀ σ ∈ N, σ = 1 ∨ σ = swap i j := by
    intro σ hσ
    have hpres := mem_setStab.1 (hNI hσ)
    have hout : ∀ x, x ≠ i → x ≠ j → σ x = x := fun x hxi hxj => hfix σ hσ x hxi hxj
    have hi : σ i ∈ ({i, j} : Finset (Fin d)) := (hpres i).2 (by simp)
    have hj : σ j ∈ ({i, j} : Finset (Fin d)) := (hpres j).2 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi
    · left
      refine Equiv.ext fun x => ?_
      by_cases hxi : x = i
      · subst hxi; simpa using hi
      by_cases hxj : x = j
      · subst hxj
        rcases hj with hj | hj
        · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
        · simpa using hj
      · simpa using hout x hxi hxj
    · right
      refine Equiv.ext fun x => ?_
      by_cases hxi : x = i
      · subst hxi; simpa using hi
      by_cases hxj : x = j
      · subst hxj
        rcases hj with hj | hj
        · simpa using hj
        · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
      · rw [swap_apply_of_ne_of_ne hxi hxj]
        exact hout x hxi hxj
  have hinj : Function.Injective (fun σ : ↥N => decide ((σ : Perm (Fin d)) = 1)) := by
    intro σ τ h
    simp only [decide_eq_decide] at h
    by_cases h1 : (σ : Perm (Fin d)) = 1
    · exact Subtype.ext (h1.trans (h.1 h1).symm)
    · have h2 : (τ : Perm (Fin d)) ≠ 1 := fun h' => h1 (h.2 h')
      rcases hcases σ σ.2 with h3 | h3
      · exact absurd h3 h1
      · rcases hcases τ τ.2 with h4 | h4
        · exact absurd h4 h2
        · exact Subtype.ext (h3.trans h4.symm)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

end Generic

end TI

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 10)

theorem qB_isElemAbelian (hR : Nat.card ↥(Rc X) ≤ 2) : CFSG.Open.IsElemAbelian 2 C.qB :=
  C.isElemAbelian_qB (C.Q_comm hR)

theorem four_le_card_qB (hR : Nat.card ↥(Rc X) ≤ 2) : 4 ≤ Nat.card ↥C.qB := by
  have h1 : Nat.card ↥(blockU X) ≤ Nat.card ↥C.qB :=
    Subgroup.card_le_of_le (C.blockU_le_qB (C.Q_comm hR))
  have h2 : 2 ^ (10 - 2) ≤ Nat.card ↥(blockU X) := C.S.card_blockU_ge
  have h3 : (2 : ℕ) ^ (10 - 2) = 256 := by norm_num
  omega

end Cfg

namespace TI

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 10) (D : C.PiData)

theorem qB_ne_bot (hR : Nat.card ↥(Rc X) ≤ 2) : C.qB ≠ ⊥ := by
  intro h
  have h4 := C.four_le_card_qB hR
  rw [h, Subgroup.card_bot] at h4
  omega

theorem card_thetaN_le_two {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : I.card = 2) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Nat.card ↥(C.thetaN x) ≤ 2 := by
  have hI' : 2 * I.card < 10 := by omega
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hI
  exact card_le_two_of_fix hij (D.thetaN_le_setStab hx hI' hπ) fun σ hσ y hyi hyj =>
    D.thetaN_fix_compl hx hI' hπ σ hσ y (by simp [hyi, hyj])

theorem card_le_two_mul_of_len_two (hR : Nat.card ↥(Rc X) ≤ 2) {a : G}
    (ha : a ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨a, ha⟩) = barInd I) {U : Subgroup G}
    (hUT : U ≤ TOf M a) : Nat.card ↥U ≤ 2 * Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) := by
  have hUM : U ≤ M := hUT.trans (TOf_le_M M a)
  have h1 := Cfg.card_eq_card_inf_mul (C := C) hR hUM
  have hsub : (U.subgroupOf M).map C.θ ≤ C.thetaN a := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact C.mem_thetaN.2 ⟨m, hUT (Subgroup.mem_subgroupOf.1 hm), rfl⟩
  have h2 : Nat.card ↥((U.subgroupOf M).map C.θ) ≤ 2 :=
    (Subgroup.card_le_of_le hsub).trans (card_thetaN_le_two C D ha hI hπ)
  calc Nat.card ↥U = Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) *
        Nat.card ↥((U.subgroupOf M).map C.θ) := h1
    _ ≤ Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) := mul_comm _ _

theorem mem_M_of_len_ne_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M)
    {g h : G} (hh : h ∈ CFSG.Open.pCoreOf 2 M) (hh1 : h ≠ 1)
    (hhg : g⁻¹ * h * g ∈ CFSG.Open.pCoreOf 2 M)
    (hlen : barLen (Multiplicative.toAdd (D.piQ ⟨h, hh⟩)) ≠ 2) : g ∈ M := by
  have hQ := C.Q_comm hR
  have hle := conj_le_TOf hQ hH hh hh1 hhg
  have hcardg : Nat.card ↥(conjSubgroup g (CFSG.Open.pCoreOf 2 M)) =
      Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_cases hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨h, hh⟩)) = 4
  · obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨h, hh⟩))
    rw [hl4] at hIc
    have hET : conjSubgroup g C.qB ≤ TOf M h := fun e he =>
      hle (mem_conjSubgroup.2 (C.qB_le_Q (mem_conjSubgroup.1 he)))
    obtain ⟨-, hEq⟩ := D.elem_le_of_len_four hR hh hIc hI hET
      (isElemAbelian_conjSubgroup (C.isElemAbelian_qB hQ) g)
    have hcardB : Nat.card ↥(conjSubgroup g C.qB) = Nat.card ↥C.qB :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hgB : g ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) :=
      mem_normalizer_iff_conj.2 (hEq hcardB)
    rw [← C.normalizer_qB_eq hR]
    exact hgB
  · have hcent := centralizer_singleton_eq_zpowers h
    have hTQ : TOf M h ≤ CFSG.Open.pCoreOf 2 M := by
      have h1 := D.pCore_centralizer_le_Q_of_len hR ⟨h, hh⟩ ⟨hlen, hl4⟩
      have h2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({h} : Set G)) ≤
          CFSG.Open.pCoreOf 2 M := h1
      rw [hcent] at h2
      exact h2
    have hEq : conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M :=
      Subgroup.eq_of_le_of_card_ge (hle.trans hTQ) hcardg.ge
    rw [← C.S.normalizer_Q_eq]
    exact mem_normalizer_iff_conj.2 hEq

include C D in
theorem conj_eq_of_inf_ne_bot (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) {g : G}
    (hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  classical
  by_contra hQg
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  set Qg : Subgroup G := conjSubgroup g Q with hQg'
  have hQab := C.Q_comm hR
  have hgM : g ∉ M := fun hg => hQg (conj_eq_of_mem_M hg)
  have hall : ∀ (h : G) (hh : h ∈ Q ⊓ Qg), h ≠ 1 →
      barLen (Multiplicative.toAdd (D.piQ ⟨h, (Subgroup.mem_inf.1 hh).1⟩)) = 2 := by
    intro h hh hh1
    by_contra hlen
    exact hgM (mem_M_of_len_ne_two C D hR hH (Subgroup.mem_inf.1 hh).1 hh1
      (mem_conjSubgroup.1 (Subgroup.mem_inf.1 hh).2) hlen)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : a ∈ Q := (Subgroup.mem_inf.1 ha).1
  have haQg : g⁻¹ * a * g ∈ Q := mem_conjSubgroup.1 (Subgroup.mem_inf.1 ha).2
  have hlen2 := hall a ha ha1'
  obtain ⟨I, hIc, hIπ⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
  rw [hlen2] at hIc
  have hle : Qg ≤ TOf M a := conj_le_TOf hQab hH haQ ha1' haQg
  have hcard1 : Nat.card ↥Qg ≤ 2 * Nat.card ↥(Qg ⊓ Q) :=
    card_le_two_mul_of_len_two C D hR haQ hIc hIπ hle
  have hcardg : Nat.card ↥Qg = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hH2 : Nat.card ↥Q ≤ 2 * Nat.card ↥(Q ⊓ Qg) :=
    calc Nat.card ↥Q = Nat.card ↥Qg := hcardg.symm
      _ ≤ 2 * Nat.card ↥(Qg ⊓ Q) := hcard1
      _ = 2 * Nat.card ↥(Q ⊓ Qg) := by rw [inf_comm]
  have hP4 : Nat.card ↥(((Q ⊓ Qg).subgroupOf Q).map D.piQ) ≤ 4 := by
    set P : Subgroup (Multiplicative (permBar 10)) := ((Q ⊓ Qg).subgroupOf Q).map D.piQ with hP
    have hV : ∀ v ∈ Subgroup.toAddSubgroup' P, v ≠ 0 → barLen v = 2 := by
      intro v hv hv0
      obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.1 ((Subgroup.mem_toAddSubgroup' P v).1 hv)
      have hkH : (k : G) ∈ Q ⊓ Qg := Subgroup.mem_subgroupOf.1 hk
      have hv' : Multiplicative.toAdd (D.piQ k) = v := by rw [hkv]; rfl
      have hk1 : (k : G) ≠ 1 := by
        intro h1
        apply hv0
        rw [← hv', show k = 1 from Subtype.ext h1, map_one]
        rfl
      rw [← hv']
      exact hall (k : G) hkH hk1
    have h4 := card_le_four_of_len_two (Subgroup.toAddSubgroup' P) hV
    have e : ↥(Subgroup.toAddSubgroup' P) ≃ ↥P :=
      Multiplicative.ofAdd.subtypeEquiv fun a => Subgroup.mem_toAddSubgroup' P a
    calc Nat.card ↥P = Nat.card ↥(Subgroup.toAddSubgroup' P) := (Nat.card_congr e).symm
      _ ≤ 4 := h4
  have hcardH := D.card_eq_card_inf_R_mul (inf_le_left : Q ⊓ Qg ≤ Q)
  have hRle : Nat.card ↥((Q ⊓ Qg) ⊓ Rc X) ≤ 2 :=
    (Subgroup.card_le_of_le inf_le_right).trans hR
  have hH8 : Nat.card ↥(Q ⊓ Qg) ≤ 8 := by
    refine hcardH.trans_le ?_
    calc Nat.card ↥((Q ⊓ Qg) ⊓ Rc X) * Nat.card ↥(((Q ⊓ Qg).subgroupOf Q).map D.piQ)
        ≤ 2 * 4 := Nat.mul_le_mul hRle hP4
      _ = 8 := by norm_num
  have hcardW : 2 ^ (10 - 2) ≤ Nat.card ↥(blockU X) := C.S.card_blockU_ge
  have hWQ : Nat.card ↥(blockU X) ≤ Nat.card ↥Q := Subgroup.card_le_of_le C.S.W_le_Q
  have h256 : (2 : ℕ) ^ (10 - 2) = 256 := by norm_num
  omega

end TI

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 10) (D : C.PiData)

include C D in
theorem qB_isTI (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    IsTI C.qB := by
  intro g
  by_cases hbot : C.qB ⊓ conjSubgroup g C.qB = ⊥
  · exact Or.inl hbot
  · right
    have hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥ := by
      intro h
      apply hbot
      refine le_bot_iff.1 ?_
      rw [← h]
      exact inf_le_inf C.qB_le_Q fun e he =>
        mem_conjSubgroup.2 (C.qB_le_Q (mem_conjSubgroup.1 he))
    have hQg := TI.conj_eq_of_inf_ne_bot C D hR hH hne
    have hgM : g ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact TI.mem_normalizer_iff_conj.2 hQg
    have hgB : g ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
      rw [C.normalizer_qB_eq hR]
      exact hgM
    rw [TI.mem_normalizer_iff_conj.1 hgB, inf_idem]

include C D in
theorem qB_weaklyClosed (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    WeaklyClosedIn C.qB (Subgroup.normalizer ((C.qB : Subgroup G) : Set G)) := by
  have hQ := C.Q_comm hR
  refine TI.weaklyClosed_of_cent C.qB_le_Q (TI.qB_ne_bot C hR) (isPGroup_pCoreOf' M) ?_
    ((C.normalizer_qB_eq hR).trans C.S.normalizer_Q_eq.symm)
    (fun _ hg => TI.conj_eq_of_inf_ne_bot C D hR hH hg)
  intro c hc
  have hcN : c ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer ((C.qB : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc b hb).symm)
  have hcM : c ∈ M := by
    rw [← C.normalizer_qB_eq hR]
    exact hcN
  have hcK : c ∈ C.K :=
    C.mem_K_of_comm_W hcM fun w hw => hc w (C.blockU_le_qB hQ hw)
  rw [C.K_eq_Q hR] at hcK
  exact hcK

end Cfg.PiData

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem inCatalog_of_centInM
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (C : Cfg G M X 10) (D : C.PiData)
    (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode C.S.simple C.S.nonab
    (C.qB_isElemAbelian hR) (TI.qB_ne_bot C hR) (qB_isTI C D hR hH) (qB_weaklyClosed C D hR hH)

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
