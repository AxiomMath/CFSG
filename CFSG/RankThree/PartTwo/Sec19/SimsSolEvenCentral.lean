module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTheta
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenPi
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTight
public import CFSG.CGT.PushingUpLit.SolK.PermBlock
public import CFSG.CGT.PushingUpLit.SolK.ThetaKer

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open scoped commutatorElement

theorem eq_one_of_pow_odd {H : Type*} [Group H] {r : H} {m j : ℕ} (hm : Odd m)
    (h1 : r ^ m = 1) (h2 : r ^ (2 ^ j) = 1) : r = 1 := by
  have h := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [((Nat.coprime_two_right.2 hm).pow_right j).gcd_eq_one, pow_one] at h

theorem isPGroup_two_of_forall {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, ∃ j : ℕ, x ^ (2 ^ j) = 1) : IsPGroup 2 H := fun x => by
  obtain ⟨j, hj⟩ := h x x.2
  exact ⟨j, Subtype.ext (by simpa using hj)⟩

theorem exists_two_pow_of_mem_pCoreOf {G : Type} [Group G] (H : Subgroup G) {r : G}
    (hr : r ∈ CFSG.Open.pCoreOf 2 H) : ∃ j : ℕ, r ^ (2 ^ j) = 1 := by
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf' H ⟨r, hr⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem mk_mem_range_heartToBar {n : ℕ} {c : Fin n → ZMod 2} (h : ∑ i, c i = 0) :
    (c : permBar n) ∈ Set.range (heartToBar (n := n)) :=
  ⟨((⟨c, by simpa [evenWeight, AddMonoidHom.mem_ker] using h⟩ : evenWeight n) : altHeart n),
    heartToBar_mk _⟩

theorem add_mem_range_heartToBar {n : ℕ} {x y : permBar n}
    (hx : x ∉ Set.range (heartToBar (n := n))) (hy : y ∉ Set.range (heartToBar (n := n))) :
    x + y ∈ Set.range (heartToBar (n := n)) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  have ha : ∑ i, a i = 1 := by
    rcases zmod_two_cases' (∑ i, a i) with h | h
    · exact absurd (mk_mem_range_heartToBar h) hx
    · exact h
  have hb : ∑ i, b i = 1 := by
    rcases zmod_two_cases' (∑ i, b i) with h | h
    · exact absurd (mk_mem_range_heartToBar h) hy
    · exact h
  rw [← QuotientAddGroup.mk_add]
  apply mk_mem_range_heartToBar
  simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb]
  decide

section PermLemmas

variable {d : ℕ}

theorem altOn_le_of_threeCycles (B : Finset (Fin d)) (L : Subgroup (Perm (Fin d)))
    (h : ∀ τ : Perm (Fin d), τ.IsThreeCycle → (∀ a, a ∉ B → τ a = a) → τ ∈ L) :
    altOn B ≤ L := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
  have hcl : alternatingGroup ↥B ≤ L.comap (Perm.ofSubtype : Perm ↥B →* Perm (Fin d)) := by
    rw [← Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro τ hτ
    show Perm.ofSubtype τ ∈ L
    refine h _ ?_ (fun a ha => Perm.ofSubtype_apply_of_not_mem τ ha)
    have hτ' : τ.IsThreeCycle := hτ
    unfold Perm.IsThreeCycle at hτ' ⊢
    simpa [Perm.cycleType_ofSubtype] using hτ'
  exact hcl hg'

theorem setStab_compl_le (I : Finset (Fin d)) : setStab Iᶜ ≤ setStab I := by
  intro σ hσ x
  have := mem_setStab.1 hσ x
  simp only [Finset.mem_compl] at this
  exact not_iff_not.1 this

theorem eq_bot_of_stabilizer {I : Finset (Fin d)} {N : Subgroup (Perm (Fin d))} (hd : 5 ≤ d)
    (hN2 : IsPGroup 2 N)
    (hstab : ∀ σ ∈ N, σ ∈ setStab I ∨ ∀ x, σ x ∈ I ↔ x ∉ I)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hI : I.card ≤ 1 ∨ I.card = 3 ∨ 5 ≤ I.card)
    (hI' : Iᶜ.card ≤ 1 ∨ Iᶜ.card = 3 ∨ 5 ≤ Iᶜ.card) : N = ⊥ := by
  have hN0 : N ⊓ setStab I = ⊥ := by
    refine eq_bot_of_blocks (isPGroup_of_le hN2 inf_le_left) inf_le_right ?_ ?_ hI hI'
    · intro τ hτ σ hσ
      exact ⟨hA τ hτ σ hσ.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (altOn_le_setStab I hτ) hσ.2)
        ((setStab I).inv_mem (altOn_le_setStab I hτ))⟩
    · intro τ hτ σ hσ
      have hτ' : τ ∈ setStab I := setStab_compl_le I (altOn_le_setStab Iᶜ hτ)
      exact ⟨hA' τ hτ σ hσ.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hτ' hσ.2)
        ((setStab I).inv_mem hτ')⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  rcases hstab σ hσ with hs | hswap
  · have : σ ∈ N ⊓ setStab I := ⟨hσ, hs⟩
    rw [hN0] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    have h1 : I.card ≤ Iᶜ.card := by
      refine Finset.card_le_card_of_injOn σ (fun a ha => ?_) σ.injective.injOn
      simp only [Finset.mem_coe, Finset.mem_compl] at ha ⊢
      intro h
      exact (hswap a).1 h ha
    have h2 : Iᶜ.card ≤ I.card := by
      refine Finset.card_le_card_of_injOn σ (fun a ha => ?_) σ.injective.injOn
      simp only [Finset.mem_coe, Finset.mem_compl] at ha ⊢
      exact (hswap a).2 ha
    have h3 := Finset.card_add_card_compl I
    simp only [Fintype.card_fin] at h3
    have h4 : 2 < I.card := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h4
    set τ : Perm (Fin d) := cyc a b c with hτ
    have hτA : τ ∈ altOn I := cyc_mem_altOn_of_mem ha hb hc hab hac hbc
    have hτst := altOn_le_setStab I hτA
    have hc1N : σ * (τ * σ⁻¹ * τ⁻¹) ∈ N :=
      N.mul_mem hσ (hA τ hτA σ⁻¹ (N.inv_mem hσ))
    have hσinv : ∀ y, σ⁻¹ y ∈ I ↔ y ∉ I := fun y => by
      have h := hswap (σ⁻¹ y)
      have e : σ (σ⁻¹ y) = y := by simp
      rw [e] at h
      tauto
    have hc1S : σ * (τ * σ⁻¹ * τ⁻¹) ∈ setStab I := by
      intro x
      simp only [Perm.mul_apply, hswap, mem_setStab.1 hτst, hσinv,
        mem_setStab.1 ((setStab I).inv_mem hτst), not_not]
    have hc1 : σ * (τ * σ⁻¹ * τ⁻¹) ∈ N ⊓ setStab I := ⟨hc1N, hc1S⟩
    rw [hN0, Subgroup.mem_bot] at hc1
    have hcomm : σ * τ * σ⁻¹ = τ := by
      calc σ * τ * σ⁻¹ = (σ * (τ * σ⁻¹ * τ⁻¹)) * τ := by group
        _ = τ := by rw [hc1, one_mul]
    have hσa : σ a ∉ I := fun h => (hswap a).1 h ha
    have hne : ∀ y ∈ I, σ a ≠ y := fun y hy h => hσa (h ▸ hy)
    have hτσa : τ (σ a) = σ a := cyc_apply_of_ne (hne a ha) (hne b hb) (hne c hc)
    have h5 : σ (τ a) = σ a := by
      have := congrArg (fun f : Perm (Fin d) => f (σ a)) hcomm
      simpa [Perm.mul_apply, hτσa] using this
    have h6 : τ a = a := σ.injective h5
    have h7 : τ a = c := cyc_apply_first hac hbc
    exact hac (h7.symm.trans h6).symm

end PermLemmas

section Supp

variable {n : ℕ}

@[expose] def supp2 (a : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i = 1

theorem mem_supp2 {a : Fin n → ZMod 2} {i : Fin n} : i ∈ supp2 a ↔ a i = 1 := by
  simp [supp2]

theorem barAct_eq_self_of_mem_setStab {σ : Perm (Fin n)} (a : Fin n → ZMod 2)
    (h : σ ∈ setStab (supp2 a)) : barAct σ (a : permBar n) = (a : permBar n) := by
  have hv : vecPerm σ a = a := by
    funext i
    rw [vecPerm_apply]
    have h1 := mem_setStab.1 h (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e, mem_supp2, mem_supp2] at h1
    generalize a (σ⁻¹ i) = p at h1 ⊢
    generalize a i = q at h1 ⊢
    revert p q
    decide
  rw [barAct_mk, hv]

private theorem zmod2_aux_a : ∀ p q : ZMod 2, -p + q = 0 → (q = 1 ↔ p = 1) := by decide

private theorem zmod2_aux_b : ∀ p q : ZMod 2, -p + q = 1 → (q = 1 ↔ ¬ p = 1) := by decide

theorem stab_or_swap_of_barAct_eq {σ : Perm (Fin n)} (a : Fin n → ZMod 2)
    (h : barAct σ (a : permBar n) = (a : permBar n)) :
    σ ∈ setStab (supp2 a) ∨ ∀ x, σ x ∈ supp2 a ↔ x ∉ supp2 a := by
  rw [barAct_mk, QuotientAddGroup.eq] at h
  rcases (mem_zmultiples_allOnes_iff _).1 h with h0 | h1
  · left
    intro x
    have h2 := congrFun h0 (σ x)
    simp only [Pi.add_apply, Pi.neg_apply, vecPerm_apply, Pi.zero_apply] at h2
    have e : σ⁻¹ (σ x) = x := by simp
    rw [e] at h2
    rw [mem_supp2, mem_supp2]
    exact zmod2_aux_a _ _ h2
  · right
    intro x
    have h2 := congrFun h1 (σ x)
    simp only [Pi.add_apply, Pi.neg_apply, vecPerm_apply, allOnes] at h2
    have e : σ⁻¹ (σ x) = x := by simp
    rw [e] at h2
    rw [mem_supp2, mem_supp2]
    exact zmod2_aux_b _ _ h2

end Supp

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : Setting G M X n)
include S

theorem W_comm {a b : G} (ha : a ∈ blockU X) (hb : b ∈ blockU X) : a * b = b * a :=
  congrArg Subtype.val (S.elemU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem blockU_ne_bot : blockU X ≠ ⊥ := fun h => by
  have := S.block.1.blockZ_lt_blockU
  rw [h] at this
  exact not_lt_bot this

theorem normalizer_Q_eq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) = M := by
  have hM : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => pCoreOf_normalized M hm hq, fun hq => ?_⟩
    have h1 := pCoreOf_normalized M (M.inv_mem hm) hq
    have e : m⁻¹ * (m * q * m⁻¹) * (m⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hne : CFSG.Open.pCoreOf 2 M ≠ ⊥ := by
    intro hbot
    apply S.blockU_ne_bot
    exact le_bot_iff.1 (hbot ▸ S.W_le_Q)
  have hloc : CFSG.IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 M, hne, isPGroup_pCoreOf' M, rfl⟩
  by_contra hne'
  exact S.maxLocal.2 _ (lt_of_le_of_ne hM (Ne.symm hne')) hloc

theorem R_normalized {m r : G} (hm : m ∈ M) (hr : r ∈ Rc X) : m * r * m⁻¹ ∈ Rc X := by
  rw [S.R_eq_inf] at hr ⊢
  exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized M hm (Subgroup.mem_inf.1 hr).1,
    Theta.conj_mem_centralizer_of_mem S hm (Subgroup.mem_inf.1 hr).2⟩

theorem R_central (hR : Nat.card ↥(Rc X) ≤ 2) {m r : G} (hm : m ∈ M) (hr : r ∈ Rc X) :
    m * r * m⁻¹ = r := by
  by_cases hr1 : r = 1
  · rw [hr1]; group
  · have hmr := S.R_normalized hm hr
    have hne : (⟨m * r * m⁻¹, hmr⟩ : ↥(Rc X)) ≠ 1 := fun h => hr1 (by
      have h1 : m * r * m⁻¹ = 1 := congrArg Subtype.val h
      have h2 := congrArg (fun t => m⁻¹ * t * m) h1
      simpa [mul_assoc] using h2)
    have hne' : (⟨r, hr⟩ : ↥(Rc X)) ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (eq_of_card_le_two hR hne hne')

theorem blockZ_le_R : blockZ X ≤ Rc X := by
  rw [S.R_eq_inf]
  exact le_inf (inf_le_left.trans S.W_le_Q) inf_le_right

theorem card_blockZ_le_two (hR : Nat.card ↥(Rc X) ≤ 2) : Nat.card ↥(blockZ X) ≤ 2 :=
  (Subgroup.card_le_of_le S.blockZ_le_R).trans hR

theorem centralizer_le_M
    (hQab : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q)
    {B : Subgroup G} (hBQ : B ≤ CFSG.Open.pCoreOf 2 M) (hB : B ≠ ⊥)
    (hO2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (B : Set G)) ≤
      CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = CFSG.Open.pCoreOf 2 M ∧
      Subgroup.normalizer (B : Set G) ≤ M := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  set K : Subgroup G := Subgroup.centralizer (B : Set G) with hK
  set K1 : Subgroup G := M ⊓ K with hK1
  set P : Subgroup G := CFSG.Open.pCoreOf 2 K with hP
  have hB2 : IsPGroup 2 B := isPGroup_of_le (isPGroup_pCoreOf' M) hBQ
  have hQ2 : IsPGroup 2 Q := isPGroup_pCoreOf' M
  have hP2 : IsPGroup 2 P := isPGroup_pCoreOf' K
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_iff.2 fun b hb => hQab b (hBQ hb) q hq
  have hQM : Q ≤ M := pCoreOf_le_self M
  have hQK1 : Q ≤ K1 := le_inf hQM hQK
  have hQnorm : ∀ k ∈ K1, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
    pCoreOf_normalized M hk.1 hq
  have hQ1 : CFSG.Open.pCoreOf 2 K1 = Q := le_antisymm hO2
    (le_pCoreOf_of_normalized hQK1 hQnorm hQ2)
  have hPnormK : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized K hk hp
  have hQNP : Q ≤ Subgroup.normalizer (P : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hPnormK q (hQK hq) p hp, fun hp => ?_⟩
    have := hPnormK q⁻¹ (K.inv_mem (hQK hq)) _ hp
    simpa [mul_assoc] using this
  have hT2 : IsPGroup 2 (P ⊔ Q : Subgroup G) := hP2.to_sup_of_normal_left' hQ2 hQNP
  have hTK : P ⊔ Q ≤ K := sup_le (pCoreOf_le_self K) hQK
  have hTnorm : ∀ k ∈ K1, ∀ t ∈ P ⊔ Q, k * t * k⁻¹ ∈ P ⊔ Q := by
    intro k hk t ht
    have hle : (P ⊔ Q).map (MulAut.conj k).toMonoidHom ≤ P ⊔ Q := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hPnormK k hk.2 z hz
      · rintro _ ⟨z, hz, rfl⟩
        exact hQnorm k hk z hz
    exact hle ⟨t, ht, rfl⟩
  have hNQ : (P ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G) ≤ Q := by
    have hnormM := S.normalizer_Q_eq
    intro g hg
    have hgM : g ∈ M := by rw [← hnormM]; exact hg.2
    have hle : (P ⊔ Q) ⊓ M ≤ CFSG.Open.pCoreOf 2 K1 := by
      refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTK ht.1⟩) (fun k hk z hz => ?_)
        (isPGroup_of_le hT2 inf_le_left)
      exact Subgroup.mem_inf.2 ⟨hTnorm k hk z hz.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1
        hz.2) (M.inv_mem hk.1)⟩
    exact hQ1.le (hle ⟨hg.1, hgM⟩)
  have hPQ : P ≤ Q := by
    by_contra hnot
    have hne : Q ≠ P ⊔ Q := by
      intro heq
      apply hnot
      rw [heq]
      exact le_sup_left
    obtain ⟨t, htT, htQ, htN⟩ := exists_mem_normalizer_of_lt hT2 le_sup_right hne
    exact htQ (hNQ ⟨htT, htN⟩)
  have hPeq : P = Q := by
    refine le_antisymm hPQ ?_
    have hcen : Q ≤ K ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf hQK (fun q hq => Subgroup.mem_centralizer_iff.2 fun p hp => hQab p (hPQ hp) q hq)
    exact (hcen.trans (centralizer_two_constrained S.charTwo hB hB2 |> fun h => by
      intro x hx
      exact h hx))
  refine ⟨hPeq, ?_⟩
  intro n hn
  have hKnorm : ∀ n ∈ Subgroup.normalizer (B : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K :=
    fun n hn k hk => centralizer_normalized hn hk
  have hPn : ∀ n ∈ Subgroup.normalizer (B : Set G), ∀ p ∈ P, n * p * n⁻¹ ∈ P :=
    fun n hn p hp => pCoreOf_normalized_of_normal hKnorm hn hp
  have hnP : n ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [← hPeq]
    refine ⟨fun hq => hPn n hn q hq, fun hq => ?_⟩
    have := hPn n⁻¹ ((Subgroup.normalizer (B : Set G)).inv_mem hn) _ hq
    simpa [mul_assoc] using this
  rw [← S.normalizer_Q_eq]
  exact hnP

end Setting

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

theorem Q_le_K : CFSG.Open.pCoreOf 2 M ≤ C.K := fun q hq =>
  C.mem_K.2 ⟨pCoreOf_le_self M hq, C.theta_Q C.S.five_le_degree hq⟩

theorem K_comm_W (D : C.PiData) (hW0 : Nat.card ↥(blockZ X) ≤ 2) {k w : G} (hk : k ∈ C.K)
    (hw : w ∈ blockU X) : k * w = w * k := by
  have hkM : k ∈ M := C.K_le hk
  have hcommW : ∀ w' ∈ blockU X, k * w' * k⁻¹ * w'⁻¹ ∈ blockZ X := by
    intro w' hw'
    have hkw : k * w' * k⁻¹ ∈ blockU X := C.S.W_normalized hkM hw'
    have hmem : k * w' * k⁻¹ * w'⁻¹ ∈ blockU X :=
      (blockU X).mul_mem hkw ((blockU X).inv_mem hw')
    have h1 : C.β ⟨k * w' * k⁻¹ * w'⁻¹, hmem⟩ = 1 := by
      have e : (⟨k * w' * k⁻¹ * w'⁻¹, hmem⟩ : ↥(blockU X)) =
          ⟨k * w' * k⁻¹, hkw⟩ * (⟨w', hw'⟩ : ↥(blockU X))⁻¹ := rfl
      have h2 : C.β ⟨k * w' * k⁻¹, hkw⟩ = C.β ⟨w', hw'⟩ :=
        Multiplicative.toAdd.injective (C.β_conj_K ⟨k, hk⟩ ⟨w', hw'⟩ ⟨k * w' * k⁻¹, hkw⟩ rfl)
      rw [e, map_mul, map_inv, h2, mul_inv_cancel]
    have h3 : (⟨k * w' * k⁻¹ * w'⁻¹, hmem⟩ : ↥(blockU X)) ∈ C.β.ker := h1
    rw [C.β_ker, Subgroup.mem_subgroupOf] at h3
    exact h3
  set W' : Subgroup G := blockU X ⊓ Subgroup.centralizer ({k} : Set G) with hW'
  have hmemW' : ∀ g, g ∈ W' ↔ g ∈ blockU X ∧ g * k = k * g := fun g => by
    rw [hW', Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hZW' : blockZ X ≤ W' := by
    intro z hz
    rw [hmemW']
    refine ⟨(Subgroup.mem_inf.1 hz).1, ?_⟩
    have hkz : k * z * k⁻¹ ∈ blockZ X :=
      Subgroup.mem_inf.2 ⟨C.S.W_normalized hkM (Subgroup.mem_inf.1 hz).1,
        Theta.conj_mem_centralizer_of_mem C.S hkM (Subgroup.mem_inf.1 hz).2⟩
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · have hne : (⟨k * z * k⁻¹, hkz⟩ : ↥(blockZ X)) ≠ 1 := fun h => hz1 (by
        have h1 : k * z * k⁻¹ = 1 := congrArg Subtype.val h
        have h2 := congrArg (fun t => k⁻¹ * t * k) h1
        simpa [mul_assoc] using h2)
      have hne' : (⟨z, hz⟩ : ↥(blockZ X)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
      have h3 : k * z * k⁻¹ = z := congrArg Subtype.val (eq_of_card_le_two hW0 hne hne')
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hXinv : ∀ x ∈ X, ∀ g ∈ W', x * g * x⁻¹ ∈ W' := by
    intro x hx g hg
    rw [hmemW'] at hg ⊢
    obtain ⟨hgW, hgk⟩ := hg
    have hxM : x ∈ M := C.S.le hx
    have hu : k * x * k⁻¹ * x⁻¹ ∈ blockU X := D.comm_mem ⟨k, hk⟩ x hx
    have hxg : x * g * x⁻¹ ∈ blockU X := C.S.W_normalized hxM hgW
    refine ⟨hxg, ?_⟩
    obtain ⟨u, hu_def⟩ : ∃ u : G, u = k * x * k⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hu_def] at hu
    have hkx : k * x = u * x * k := by rw [hu_def]; group
    have hcomm : u * (x * g * x⁻¹) = (x * g * x⁻¹) * u := C.S.W_comm hu hxg
    have hkg : k * g * k⁻¹ = g := mul_inv_eq_iff_eq_mul.2 hgk.symm
    have hconj : k * (x * g * x⁻¹) * k⁻¹ = x * g * x⁻¹ := by
      calc k * (x * g * x⁻¹) * k⁻¹ = (k * x) * g * (k * x)⁻¹ := by group
        _ = (u * x * k) * g * (u * x * k)⁻¹ := by rw [hkx]
        _ = u * x * (k * g * k⁻¹) * x⁻¹ * u⁻¹ := by group
        _ = u * (x * g * x⁻¹) * u⁻¹ := by rw [hkg]; group
        _ = x * g * x⁻¹ := by rw [hcomm]; group
    exact (mul_inv_eq_iff_eq_mul.1 hconj).symm
  have hnorm : X ≤ Subgroup.normalizer (W' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hXinv x hx g hg, fun hg => ?_⟩
    have := hXinv x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  rcases C.S.block.1.irreducible W' hZW' inf_le_left hnorm with h | h
  · exfalso
    let f : ↥(blockU X) →* ↥(blockZ X) :=
      MonoidHom.mk' (fun w' => ⟨k * (w' : G) * k⁻¹ * (w' : G)⁻¹, hcommW w' w'.2⟩) (fun a b => by
        apply Subtype.ext
        have ha : k * (a : G) * k⁻¹ ∈ blockU X := C.S.W_normalized hkM a.2
        have hb : k * (b : G) * k⁻¹ * (b : G)⁻¹ ∈ blockU X :=
          (blockU X).mul_mem (C.S.W_normalized hkM b.2) ((blockU X).inv_mem b.2)
        have hc : (k * (b : G) * k⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
            (a : G)⁻¹ * (k * (b : G) * k⁻¹ * (b : G)⁻¹) :=
          C.S.W_comm hb ((blockU X).inv_mem a.2)
        show k * ((a : G) * (b : G)) * k⁻¹ * ((a : G) * (b : G))⁻¹ =
          (k * (a : G) * k⁻¹ * (a : G)⁻¹) * (k * (b : G) * k⁻¹ * (b : G)⁻¹)
        calc k * ((a : G) * (b : G)) * k⁻¹ * ((a : G) * (b : G))⁻¹
            = (k * (a : G) * k⁻¹) * ((k * (b : G) * k⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = (k * (a : G) * k⁻¹) * ((a : G)⁻¹ * (k * (b : G) * k⁻¹ * (b : G)⁻¹)) := by rw [hc]
          _ = (k * (a : G) * k⁻¹ * (a : G)⁻¹) * (k * (b : G) * k⁻¹ * (b : G)⁻¹) := by group)
    have hker : ∀ w' : ↥(blockU X), f w' = 1 → (w' : G) ∈ blockZ X := by
      intro w' hw'
      have h1 : k * (w' : G) * k⁻¹ * (w' : G)⁻¹ = 1 := congrArg Subtype.val hw'
      have h2 : (w' : G) ∈ W' := by
        rw [hmemW']
        refine ⟨w'.2, ?_⟩
        have h3 : k * (w' : G) * k⁻¹ = w' := mul_inv_eq_one.1 h1
        exact (mul_inv_eq_iff_eq_mul.1 h3).symm
      rw [h] at h2
      exact h2
    have hcard := Subgroup.card_ker_mul_card_range f
    have hk1 : Nat.card f.ker ≤ 2 := by
      refine le_trans ?_ hW0
      refine Nat.card_le_card_of_injective
        (fun w' : f.ker => (⟨((w' : ↥(blockU X)) : G), hker w' (MonoidHom.mem_ker.1 w'.2)⟩ :
          ↥(blockZ X))) ?_
      intro a b hab
      have h5 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h5)
    have hk2 : Nat.card f.range ≤ 2 :=
      (Nat.card_le_card_of_injective (fun y : f.range => (y : ↥(blockZ X)))
        Subtype.val_injective).trans hW0
    have h4 : Nat.card ↥(blockU X) ≤ 2 * 2 := hcard ▸ Nat.mul_le_mul hk1 hk2
    have h16 := C.S.sixteen_le_card_blockU
    omega
  · have hwW' : w ∈ W' := by rw [h]; exact hw
    exact ((hmemW' w).1 hwW').2.symm

include C in
theorem W_le_center_Q (hW0 : Nat.card ↥(blockZ X) ≤ 2) :
    ∀ w ∈ blockU X, ∀ q ∈ CFSG.Open.pCoreOf 2 M, w * q = q * w := by
  obtain ⟨D⟩ := C.exists_piData C.six_le C.even_n
  exact fun w hw q hq => (C.K_comm_W D hW0 (C.Q_le_K hq) hw).symm

theorem mem_K_of_comm_W {m : G} (hm : m ∈ M) (h : ∀ w ∈ blockU X, m * w = w * m) : m ∈ C.K := by
  rw [C.mem_K]
  refine ⟨hm, (C.theta_eq_one_iff C.S.five_le_degree ⟨m, hm⟩).2 ?_⟩
  intro u v hv
  have h1 : (v : G) = u := by
    rw [hv]
    exact mul_inv_eq_iff_eq_mul.2 (h u u.2)
  rw [Subtype.ext h1]

@[expose] noncomputable def PiData.piQ {C : Cfg G M X n} (D : C.PiData) :
    ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (permBar n) :=
  D.π.comp (Subgroup.inclusion C.Q_le_K)

namespace PiData

variable {C} (D : C.PiData)

theorem piQ_apply (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    D.piQ q = D.π ⟨(q : G), C.Q_le_K q.2⟩ := rfl

theorem piQ_eq_one_iff (q : ↥(CFSG.Open.pCoreOf 2 M)) : D.piQ q = 1 ↔ (q : G) ∈ Rc X := by
  rw [piQ_apply, D.ker, C.S.R_eq_inf]
  exact ⟨fun h => Subgroup.mem_inf.2 ⟨q.2, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩

theorem piQ_conj (m : ↥M) (q q' : ↥(CFSG.Open.pCoreOf 2 M)) (h : (q' : G) = m * q * m⁻¹) :
    Multiplicative.toAdd (D.piQ q') = barAct (C.θ m) (Multiplicative.toAdd (D.piQ q)) :=
  D.equivar m ⟨(q : G), C.Q_le_K q.2⟩ ⟨(q' : G), C.Q_le_K q'.2⟩ h

theorem piQ_W (u : ↥(blockU X)) (q : ↥(CFSG.Open.pCoreOf 2 M)) (h : (q : G) = u) :
    Multiplicative.toAdd (D.piQ q) = heartToBar (Multiplicative.toAdd (C.β u)) :=
  D.π_W ⟨(q : G), C.Q_le_K q.2⟩ u h

theorem exists_mul_of_mem_range {x : ↥(CFSG.Open.pCoreOf 2 M)}
    (h : Multiplicative.toAdd (D.piQ x) ∈ Set.range (heartToBar (n := n))) :
    ∃ w ∈ blockU X, ∃ r ∈ Rc X, (x : G) = w * r := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨u, hu⟩ := C.β_surj (Multiplicative.ofAdd a)
  have hua : Multiplicative.toAdd (C.β u) = a := by rw [hu]; rfl
  let qu : ↥(CFSG.Open.pCoreOf 2 M) := ⟨(u : G), C.S.W_le_Q u.2⟩
  have hqu : Multiplicative.toAdd (D.piQ qu) = Multiplicative.toAdd (D.piQ x) := by
    rw [D.piQ_W u qu rfl, hua, ha]
  have h1 : D.piQ (qu⁻¹ * x) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_one, hqu]
    exact neg_add_cancel _
  refine ⟨(u : G), u.2, ((qu⁻¹ * x : ↥(CFSG.Open.pCoreOf 2 M)) : G), (D.piQ_eq_one_iff _).1 h1, ?_⟩
  show (x : G) = (u : G) * ((u : G)⁻¹ * (x : G))
  group

theorem exists_comm_lift (x : ↥(CFSG.Open.pCoreOf 2 M)) {c : Equiv.Perm (Fin n)}
    (hc : c.IsThreeCycle)
    (hfix : barAct c (Multiplicative.toAdd (D.piQ x)) = Multiplicative.toAdd (D.piQ x)) :
    ∃ y : ↥X, C.θ ⟨(y : G), C.S.le y.2⟩ = c ∧ (y : G) * (x : G) = (x : G) * (y : G) := by
  have hcA : c ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hc.sign
  obtain ⟨y₀, hy₀⟩ := C.exists_lift hcA
  have hαy₀ : (C.α y₀ : Equiv.Perm (Fin n)) = c := by rw [← C.θ_X y₀, hy₀]
  have hc3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
  have hy3 : C.α (y₀ ^ 3) = 1 := Subtype.ext (by rw [map_pow, Subgroup.coe_pow, hαy₀, hc3]; rfl)
  have hy3Y : ((y₀ ^ 3 : ↥X) : G) ∈ CFSG.Open.pCoreOf 2 X := (C.α_eq_one_iff _).1 hy3
  obtain ⟨a, ha⟩ := exists_two_pow_of_mem_pCoreOf X hy3Y
  rw [Subgroup.coe_pow] at ha
  have hyc : (C.α (y₀ ^ (4 ^ a)) : Equiv.Perm (Fin n)) = c := by
    rw [map_pow, Subgroup.coe_pow, hαy₀, ← pow_mod_orderOf, hc.orderOf]
    have : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [this, pow_one]
  have hyG : ((y₀ ^ (4 ^ a) : ↥X) : G) ^ 3 = 1 := by
    have h4a : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by rw [← mul_pow]; norm_num
    rw [Subgroup.coe_pow, ← pow_mul, h4a]
    calc (y₀ : G) ^ (2 ^ a * 2 ^ a * 3) = (((y₀ : G) ^ 3) ^ 2 ^ a) ^ 2 ^ a := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [ha, one_pow]
  refine ⟨y₀ ^ (4 ^ a), (C.θ_X _).trans hyc, ?_⟩
  generalize y₀ ^ (4 ^ a) = y at hyc hyG ⊢
  have hy3' : (y : G) * y * y = 1 := by rw [← pow_three']; exact hyG
  have hxK : (x : G) ∈ C.K := C.Q_le_K x.2
  have hu : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ blockU X := D.comm_mem ⟨(x : G), hxK⟩ y y.2
  have hspec := D.spec ⟨(x : G), hxK⟩ y ⟨_, hu⟩ rfl
  have hπk : Multiplicative.toAdd (D.π ⟨(x : G), hxK⟩) = Multiplicative.toAdd (D.piQ x) := rfl
  rw [hπk, hyc, hfix, sub_self] at hspec
  have hβu : C.β ⟨_, hu⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact heartToBar_injective (hspec.trans (map_zero heartToBar).symm)
  have hρZ : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ blockZ X := by
    have h1 : (⟨_, hu⟩ : ↥(blockU X)) ∈ C.β.ker := hβu
    rw [C.β_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G, ρ = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ := ⟨_, rfl⟩
  rw [← hρ] at hρZ
  have hρW : ρ ∈ blockU X := (Subgroup.mem_inf.1 hρZ).1
  have hρy : (y : G) * ρ = ρ * y :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hρZ).2 (y : G) y.2
  have hρ2 : ρ * ρ = 1 := by
    have := C.S.elemU.2 ρ hρW
    rwa [pow_two] at this
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hB : (y : G) * x * (y : G)⁻¹ = ρ * x := by
    have h1 : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ = ρ := by
      rw [← hρinv, hρ]; group
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hA2 : (y : G) * y * x * ((y : G) * y)⁻¹ = x := by
    calc (y : G) * y * x * ((y : G) * y)⁻¹ = y * ((y : G) * x * (y : G)⁻¹) * (y : G)⁻¹ := by group
      _ = y * (ρ * x) * (y : G)⁻¹ := by rw [hB]
      _ = ((y : G) * ρ * (y : G)⁻¹) * ((y : G) * x * (y : G)⁻¹) := by group
      _ = ρ * (ρ * x) := by
          rw [hρy, hB]; group
      _ = (ρ * ρ) * x := by group
      _ = x := by rw [hρ2, one_mul]
  have hA : (y : G) * y * x = x * ((y : G) * y) := mul_inv_eq_iff_eq_mul.1 hA2
  have h4 : (y : G) * y * ((y : G) * y) = y := by
    calc (y : G) * y * ((y : G) * y) = ((y : G) * y * y) * y := by group
      _ = y := by rw [hy3', one_mul]
  calc (y : G) * x = ((y : G) * y * ((y : G) * y)) * x := by rw [h4]
    _ = (y : G) * y * (((y : G) * y) * x) := by group
    _ = (y : G) * y * (x * ((y : G) * y)) := by rw [hA]
    _ = ((y : G) * y * x) * ((y : G) * y) := by group
    _ = (x * ((y : G) * y)) * ((y : G) * y) := by rw [hA]
    _ = x * ((y : G) * y * ((y : G) * y)) := by group
    _ = x * y := by rw [h4]

end PiData

include C in
theorem R_central (hR : Nat.card ↥(Rc X) ≤ 2) :
    ∀ m ∈ M, ∀ r ∈ Rc X, m * r * m⁻¹ = r := fun _ hm _ hr => C.S.R_central hR hm hr

include C in
theorem centralizer_X_eq (hR : Nat.card ↥(Rc X) ≤ 2) :
    Subgroup.centralizer (X : Set G) = Rc X := by
  refine le_antisymm ?_ (pCoreOf_le_self _)
  have hCxM : Subgroup.centralizer (X : Set G) ≤ M := C.S.centralizer_le
  have hCxn : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer (X : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := fun m hm c hc =>
    Theta.conj_mem_centralizer_of_mem C.S hm hc
  have hodd : ∀ h ∈ Subgroup.centralizer (X : Set G), ∀ m : ℕ, Odd m → h ^ m = 1 → h = 1 := by
    intro h hh m hm hhm
    have hhM : h ∈ M := hCxM hh
    have hcomm : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * h = h * q := by
      intro q hq
      have hqM : q ∈ M := pCoreOf_le_self M hq
      have hrQ : h * q * h⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
        (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M hhM hq)
          ((CFSG.Open.pCoreOf 2 M).inv_mem hq)
      have hr : h * q * h⁻¹ * q⁻¹ ∈ Rc X := by
        rw [C.S.R_eq_inf]
        refine Subgroup.mem_inf.2 ⟨hrQ, ?_⟩
        have e : h * q * h⁻¹ * q⁻¹ = h * (q * h⁻¹ * q⁻¹) := by group
        rw [e]
        exact (Subgroup.centralizer (X : Set G)).mul_mem hh
          (hCxn q hqM h⁻¹ ((Subgroup.centralizer (X : Set G)).inv_mem hh))
      obtain ⟨r, hr_def⟩ : ∃ r : G, r = h * q * h⁻¹ * q⁻¹ := ⟨_, rfl⟩
      rw [← hr_def] at hr hrQ
      have hhr : h * r * h⁻¹ = r := C.S.R_central hR hhM hr
      have hhq : h * q * h⁻¹ = r * q := by rw [hr_def]; group
      have hk : ∀ k : ℕ, h ^ k * q * (h ^ k)⁻¹ = r ^ k * q := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc h ^ (k + 1) * q * (h ^ (k + 1))⁻¹ = h * (h ^ k * q * (h ^ k)⁻¹) * h⁻¹ := by group
            _ = h * (r ^ k * q) * h⁻¹ := by rw [ih]
            _ = (h * r * h⁻¹) ^ k * (h * q * h⁻¹) := by rw [conj_pow]; group
            _ = r ^ (k + 1) * q := by rw [hhr, hhq, pow_succ, mul_assoc]
      have hrm : r ^ m = 1 := by
        have h4 := hk m
        rw [hhm] at h4
        have h5 : r ^ m * q = 1 * q := by rw [← h4]; group
        exact mul_right_cancel h5
      obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf M hrQ
      have hr1 : r = 1 := eq_one_of_pow_odd hm hrm hj
      rw [hr1] at hr_def
      have h6 : h * q * h⁻¹ = q := by
        have := congrArg (fun t => t * q) hr_def
        simpa [mul_assoc] using this.symm
      exact (mul_inv_eq_iff_eq_mul.1 h6).symm
    have hcent : h ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.2 hcomm
    have hhQ : h ∈ CFSG.Open.pCoreOf 2 M := C.S.charTwo M C.S.maxLocal.1 ⟨hhM, hcent⟩
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf M hhQ
    exact eq_one_of_pow_odd hm hhm hj
  have hP : IsPGroup 2 (Subgroup.centralizer (X : Set G)) := by
    refine isPGroup_two_of_forall fun c hc => ?_
    obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨a, hodd (c ^ (2 ^ a)) ((Subgroup.centralizer (X : Set G)).pow_mem hc _) m hm ?_⟩
    rw [← pow_mul, ← hcm]
    exact pow_orderOf_eq_one c
  have hle : Subgroup.centralizer (X : Set G) ≤ CFSG.Open.pCoreOf 2 M :=
    le_pCoreOf_of_normalized hCxM hCxn hP
  rw [C.S.R_eq_inf]
  exact le_inf hle le_rfl

include C in
theorem K_eq_Q (hR : Nat.card ↥(Rc X) ≤ 2) : C.K = CFSG.Open.pCoreOf 2 M := by
  obtain ⟨D⟩ := C.exists_piData C.six_le C.even_n
  refine le_antisymm ?_ C.Q_le_K
  have hP : IsPGroup 2 C.K := by
    refine isPGroup_two_of_forall fun k hk => ?_
    have h1 : D.π (⟨k, hk⟩ * ⟨k, hk⟩) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact permBar_add_self _
    have h2 : k * k ∈ Subgroup.centralizer (X : Set G) := (D.ker _).1 h1
    rw [C.centralizer_X_eq hR] at h2
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf (Subgroup.centralizer (X : Set G)) h2
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hj
  refine le_pCoreOf_of_normalized C.K_le (fun m hm k hk => ?_) hP
  obtain ⟨hkM, hθ⟩ := C.mem_K.1 hk
  refine C.mem_K.2 ⟨M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm), ?_⟩
  have e : (⟨m * k * m⁻¹, M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm)⟩ : ↥M) =
      ⟨m, hm⟩ * ⟨k, hkM⟩ * ⟨m, hm⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hθ]
  simp

include C in
theorem Q_comm (hR : Nat.card ↥(Rc X) ≤ 2) :
    ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q := by
  obtain ⟨D⟩ := C.exists_piData C.six_le C.even_n
  have hWc := C.W_le_center_Q (C.S.card_blockZ_le_two hR)
  have hRc : ∀ r ∈ Rc X, ∀ y ∈ CFSG.Open.pCoreOf 2 M, y * r = r * y := fun r hr y hy =>
    mul_inv_eq_iff_eq_mul.1 (C.S.R_central hR (pCoreOf_le_self M hy) hr)
  have hcommute : ∀ x : ↥(CFSG.Open.pCoreOf 2 M),
      Multiplicative.toAdd (D.piQ x) ∈ Set.range (heartToBar (n := n)) →
      ∀ y ∈ CFSG.Open.pCoreOf 2 M, (x : G) * y = y * x := by
    intro x hx y hy
    obtain ⟨w, hw, r, hr, hxwr⟩ := D.exists_mul_of_mem_range hx
    rw [hxwr]
    calc w * r * y = w * (r * y) := by group
      _ = w * (y * r) := by rw [hRc r hr y hy]
      _ = (w * y) * r := by group
      _ = (y * w) * r := by rw [hWc w hw y hy]
      _ = y * (w * r) := by group
  intro q hq q' hq'
  by_cases h1 : Multiplicative.toAdd (D.piQ ⟨q, hq⟩) ∈ Set.range (heartToBar (n := n))
  · exact hcommute ⟨q, hq⟩ h1 q' hq'
  by_cases h2 : Multiplicative.toAdd (D.piQ ⟨q', hq'⟩) ∈ Set.range (heartToBar (n := n))
  · exact (hcommute ⟨q', hq'⟩ h2 q hq).symm
  have h3 : Multiplicative.toAdd (D.piQ ((⟨q, hq⟩ : ↥(CFSG.Open.pCoreOf 2 M))⁻¹ * ⟨q', hq'⟩)) ∈
      Set.range (heartToBar (n := n)) := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, permBar_neg_eq]
    exact add_mem_range_heartToBar h1 h2
  have h5 : q⁻¹ * q' * q = q * (q⁻¹ * q') := hcommute _ h3 q hq
  calc q * q' = q * (q * (q⁻¹ * q')) := by group
    _ = q * ((q⁻¹ * q') * q) := by rw [h5]
    _ = q' * q := by group

include C in
theorem centralizer_Q_eq (hR : Nat.card ↥(Rc X) ≤ 2) :
    Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) = CFSG.Open.pCoreOf 2 M := by
  refine le_antisymm (fun g hg => ?_) (fun q hq => ?_)
  · have hgM : g ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact Subgroup.centralizer_le_normalizer _ hg
    exact C.S.charTwo M C.S.maxLocal.1 ⟨hgM, hg⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q' hq'
    exact (C.Q_comm hR q hq q' hq').symm

include C in
theorem normalizer_le_M_of_W_le {P : Subgroup G} (hWP : blockU X ≤ P)
    (hPQ : P ≤ CFSG.Open.pCoreOf 2 M) : Subgroup.normalizer (P : Set G) ≤ M := by
  have hXP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    have hpK : p ∈ C.K := C.Q_le_K (hPQ hp)
    have hc : ⁅p, x⁆ ∈ blockU X := C.comm_mem_W ⟨p, hpK⟩ hx
    have : x * p * x⁻¹ = (⁅p, x⁆)⁻¹ * p := by
      rw [commutator_inv' p x]
      exact conj_eq_commutator_mul x p
    rw [this]
    exact P.mul_mem (P.inv_mem (hWP hc)) hp
  have hXN : X ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hXP x hx p hp, fun hp => ?_⟩
    have := hXP x⁻¹ (X.inv_mem hx) _ hp
    simpa [mul_assoc] using this
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply C.S.blockU_ne_bot
    exact le_bot_iff.1 (hbot ▸ hWP)
  have hloc : CFSG.IsPLocal 2 (Subgroup.normalizer (P : Set G)) :=
    ⟨P, hPne, isPGroup_of_le (isPGroup_pCoreOf' M) hPQ, rfl⟩
  exact local_le_of_unique C.S.uniq hloc hXN

include C in
theorem centralizer_le_M (hR : Nat.card ↥(Rc X) ≤ 2) {B : Subgroup G}
    (hBQ : B ≤ CFSG.Open.pCoreOf 2 M) (hB : B ≠ ⊥)
    (hO2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (B : Set G)) ≤
      CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = CFSG.Open.pCoreOf 2 M ∧
      Subgroup.normalizer (B : Set G) ≤ M :=
  C.S.centralizer_le_M (C.Q_comm hR) hBQ hB hO2

namespace PiData

variable {C} (D : C.PiData)

theorem pCore_centralizer_le_Q_of_len (hR : Nat.card ↥(Rc X) ≤ 2)
    (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ x)) ≠ 4) :
    CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({(x : G)} : Set G)) ≤
      CFSG.Open.pCoreOf 2 M := by
  classical
  set C1 : Subgroup G := M ⊓ Subgroup.centralizer ({(x : G)} : Set G) with hC1
  set T0 : Subgroup G := CFSG.Open.pCoreOf 2 C1 with hT0
  have hT0C : T0 ≤ C1 := pCoreOf_le_self C1
  have hT0M : T0 ≤ M := hT0C.trans inf_le_left
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (D.piQ x))
  set I : Finset (Fin n) := supp2 a with hI
  have hfixC : ∀ m : ↥M, (m : G) ∈ C1 → barAct (C.θ m) (a : permBar n) = a := by
    intro m hm
    have hmx : (m : G) * (x : G) = (x : G) * (m : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2
    have h1 := D.piQ_conj m x x (mul_inv_eq_iff_eq_mul.2 hmx).symm
    rw [← ha] at h1
    exact h1.symm
  let K0 : Subgroup ↥M := T0.subgroupOf M
  have hmemK0 : ∀ m : ↥M, m ∈ K0 ↔ (m : G) ∈ T0 := fun m => Iff.rfl
  have hK02 : IsPGroup 2 ↥K0 :=
    (isPGroup_pCoreOf' C1).of_equiv (Subgroup.subgroupOfEquivOfLe hT0M).symm
  set N : Subgroup (Perm (Fin n)) := K0.map C.θ with hNdef
  have hN2 : IsPGroup 2 N := hK02.map C.θ
  have hstab : ∀ σ ∈ N, σ ∈ setStab I ∨ ∀ y, σ y ∈ I ↔ y ∉ I := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact stab_or_swap_of_barAct_eq a (hfixC m (hT0C ((hmemK0 m).1 hm)))
  have h3cyc : ∀ B : Finset (Fin n), (B = I ∨ B = Iᶜ) → ∀ τ : Perm (Fin n), τ.IsThreeCycle →
      (∀ y, y ∉ B → τ y = y) → ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
    intro B hB τ hτ hsupp σ hσ
    have hτA : τ ∈ altOn B := mem_altOn.2 ⟨hsupp, hτ.sign⟩
    have hτI : τ ∈ setStab I := by
      rcases hB with rfl | rfl
      · exact altOn_le_setStab _ hτA
      · exact setStab_compl_le I (altOn_le_setStab _ hτA)
    have hfix : barAct τ (Multiplicative.toAdd (D.piQ x)) = Multiplicative.toAdd (D.piQ x) := by
      rw [← ha]
      exact barAct_eq_self_of_mem_setStab a hτI
    obtain ⟨y, hyθ, hyx⟩ := D.exists_comm_lift x hτ hfix
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hyM : (y : G) ∈ M := C.S.le y.2
    have hyC1 : (y : G) ∈ C1 :=
      Subgroup.mem_inf.2 ⟨hyM, Subgroup.mem_centralizer_singleton_iff.2 hyx⟩
    have hmT : (m : G) ∈ T0 := (hmemK0 m).1 hm
    have hcmT : (y : G) * (m : G) * (y : G)⁻¹ ∈ T0 := pCoreOf_normalized C1 hyC1 hmT
    refine Subgroup.mem_map.2 ⟨⟨(y : G) * (m : G) * (y : G)⁻¹, hT0M hcmT⟩, (hmemK0 _).2 hcmT, ?_⟩
    have e : (⟨(y : G) * (m : G) * (y : G)⁻¹, hT0M hcmT⟩ : ↥M) =
        ⟨(y : G), hyM⟩ * m * ⟨(y : G), hyM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hyθ]
  have hnormB : ∀ B : Finset (Fin n), (B = I ∨ B = Iᶜ) →
      altOn B ≤ Subgroup.normalizer (N : Set (Perm (Fin n))) := by
    intro B hB
    refine altOn_le_of_threeCycles B _ (fun τ' h3 hs => ?_)
    have hs' : ∀ y, y ∉ B → τ'⁻¹ y = y := fun y hy => by
      rw [Perm.inv_eq_iff_eq]
      exact (hs y hy).symm
    rw [Subgroup.mem_normalizer_iff]
    intro σ'
    refine ⟨fun hσ' => h3cyc B hB τ' h3 hs σ' hσ', fun h => ?_⟩
    have := h3cyc B hB τ'⁻¹ h3.inv hs' _ h
    simpa [mul_assoc] using this
  have hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := fun τ hτ σ hσ =>
    (Subgroup.mem_normalizer_iff.1 (hnormB I (Or.inl rfl) hτ) σ).1 hσ
  have hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := fun τ hτ σ hσ =>
    (Subgroup.mem_normalizer_iff.1 (hnormB Iᶜ (Or.inr rfl) hτ) σ).1 hσ
  have hlen : barLen (a : permBar n) = min I.card (n - I.card) := by
    rw [barLen_mk]
    rfl
  rw [← ha, hlen] at hl
  have hIc : Iᶜ.card = n - I.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hIle : I.card ≤ n := by
    have := Finset.card_le_univ I
    simpa using this
  have hn6 : 6 ≤ n := C.six_le
  have hnmem := C.S.n_mem
  have hI1 : I.card ≤ 1 ∨ I.card = 3 ∨ 5 ≤ I.card := by omega
  have hI2 : Iᶜ.card ≤ 1 ∨ Iᶜ.card = 3 ∨ 5 ≤ Iᶜ.card := by omega
  have hNbot : N = ⊥ := eq_bot_of_stabilizer (by omega) hN2 hstab hA hA' hI1 hI2
  intro t ht
  have htM : t ∈ M := hT0M ht
  have hmem : C.θ ⟨t, htM⟩ ∈ N := Subgroup.mem_map.2 ⟨⟨t, htM⟩, (hmemK0 _).2 ht, rfl⟩
  rw [hNbot] at hmem
  have hK : t ∈ C.K := C.mem_K.2 ⟨htM, Subgroup.mem_bot.1 hmem⟩
  rwa [C.K_eq_Q hR] at hK

theorem centralizer_le_of_len (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hx1 : (x : G) ≠ 1)
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ x)) ≠ 4) :
    Subgroup.centralizer ({(x : G)} : Set G) ≤ M ∧
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({(x : G)} : Set G)) =
        CFSG.Open.pCoreOf 2 M := by
  have hBQ : (Subgroup.zpowers (x : G) : Subgroup G) ≤ CFSG.Open.pCoreOf 2 M :=
    Subgroup.zpowers_le.2 x.2
  have hB : (Subgroup.zpowers (x : G) : Subgroup G) ≠ ⊥ := fun h =>
    hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hcent := centralizer_singleton_eq_zpowers (x : G)
  have hO2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (x : G) : Subgroup G) : Set G)) ≤ CFSG.Open.pCoreOf 2 M := by
    rw [← hcent]
    exact D.pCore_centralizer_le_Q_of_len hR x hl
  obtain ⟨h1, h2⟩ := C.centralizer_le_M hR hBQ hB hO2
  rw [hcent]
  exact ⟨(Subgroup.centralizer_le_normalizer _).trans h2, h1⟩

theorem conj_le_of_len (hR : Nat.card ↥(Rc X) ≤ 2) {x y : ↥(CFSG.Open.pCoreOf 2 M)} {g : G}
    (hx1 : (x : G) ≠ 1) (hy1 : (y : G) ≠ 1)
    (hlx : barLen (Multiplicative.toAdd (D.piQ x)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ x)) ≠ 4)
    (hly : barLen (Multiplicative.toAdd (D.piQ y)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ y)) ≠ 4)
    (hg : g * (x : G) * g⁻¹ = (y : G)) :
    ∀ q ∈ CFSG.Open.pCoreOf 2 M, g * q * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have hX := (D.centralizer_le_of_len hR x hx1 hlx).2
  have hY := (D.centralizer_le_of_len hR y hy1 hly).2
  have hQab := C.Q_comm hR
  set H : Subgroup G := Subgroup.centralizer ({(y : G)} : Set G) with hH
  set P : Subgroup G := (CFSG.Open.pCoreOf 2 M).map (MulAut.conj g).toMonoidHom with hP
  have hP2 : IsPGroup 2 P := (isPGroup_pCoreOf' M).map _
  have hPH : P ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    have hqx : q * (x : G) = (x : G) * q := hQab q hq x x.2
    rw [← hg]
    show g * q * g⁻¹ * (g * (x : G) * g⁻¹) = g * (x : G) * g⁻¹ * (g * q * g⁻¹)
    calc g * q * g⁻¹ * (g * (x : G) * g⁻¹) = g * (q * (x : G)) * g⁻¹ := by group
      _ = g * ((x : G) * q) * g⁻¹ := by rw [hqx]
      _ = g * (x : G) * g⁻¹ * (g * q * g⁻¹) := by group
  have hnorm : ∀ k ∈ H, ∀ p ∈ P, k * p * k⁻¹ ∈ P := by
    intro k hk p hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hk' : g⁻¹ * k * g ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : k * (y : G) = (y : G) * k := Subgroup.mem_centralizer_singleton_iff.1 hk
      rw [← hg] at h1
      calc g⁻¹ * k * g * (x : G) = g⁻¹ * (k * (g * (x : G) * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * (x : G) * g⁻¹) * k) * g := by rw [h1]
        _ = (x : G) * (g⁻¹ * k * g) := by group
    have hq' : (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      rw [← hX] at hq ⊢
      exact pCoreOf_normalized _ hk' hq
    refine ⟨(g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹, hq', ?_⟩
    show g * ((g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹) * g⁻¹ = k * (g * q * g⁻¹) * k⁻¹
    group
  have hle : P ≤ CFSG.Open.pCoreOf 2 H := le_pCoreOf_of_normalized hPH hnorm hP2
  rw [hH, hY] at hle
  intro q hq
  exact hle ⟨q, hq, rfl⟩

theorem mem_of_conj_of_len (hR : Nat.card ↥(Rc X) ≤ 2) {x y : ↥(CFSG.Open.pCoreOf 2 M)} {g : G}
    (hx1 : (x : G) ≠ 1) (hy1 : (y : G) ≠ 1)
    (hlx : barLen (Multiplicative.toAdd (D.piQ x)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ x)) ≠ 4)
    (hly : barLen (Multiplicative.toAdd (D.piQ y)) ≠ 2 ∧
      barLen (Multiplicative.toAdd (D.piQ y)) ≠ 4)
    (h : (y : G) = g * (x : G) * g⁻¹) : g ∈ M := by
  have h1 := D.conj_le_of_len hR hx1 hy1 hlx hly h.symm
  have h2 : g⁻¹ * (y : G) * g⁻¹⁻¹ = (x : G) := by rw [h]; group
  have h3 := D.conj_le_of_len hR hy1 hx1 hly hlx h2
  rw [← C.S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨h1 q, fun hq => ?_⟩
  have := h3 _ hq
  simpa [mul_assoc] using this

end PiData

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
