module

public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.H13.NQCoreP134Pair

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3 CFSG.Quasithin.H13.NQCore
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem pair_case_five (hOut : OutAbelianFact) (hBorel : Psl2BorelFact) (hSz : SzNoFiveFact)
    (hJ1 : J1NoFiveFact) (hyp : SQTKHypCat Γ) (h37 : A37Statement Γ) (h38 : A38Part3 Γ)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : p = 5) {P T N O L : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : ¬ L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
      L ⊓ L.map (MulAut.conj n).toMonoidHom = ⊥ ∧
      P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom ∧ Nat.card (P ⊓ L : Subgroup Γ) = p ∧
      Nat.card P = p ^ 2 ∧
      ((∃ m : ℕ, p ∣ 2 ^ m - 1 ∧ StatedClassicalModel ↥L .PSL 2 2 m) ∨
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel ↥L .PSL 2 q 1) := by
  have hp5' : 5 ≤ p := hp5.ge
  have hp2 : p ≠ 2 := by omega
  have hrank : Open.pRank p (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) p hp.out hp2
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := hcard.ge
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rw [hcard]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  obtain ⟨hpart, -⟩ := h38 L hLc
  rcases hpart with hn | ⟨htypes, t, htn, hcomm, hinf, hcl⟩
  · exact absurd hn hLn
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  have hL'c : L' ∈ cComp (⊤ : Subgroup Γ) := A38.cComp_conj hLc
  have hconj : ∀ g : Γ, L.map (MulAut.conj g).toMonoidHom = L ∨
      L.map (MulAut.conj g).toMonoidHom = L' := by
    intro g
    have hle : L.map (MulAut.conj g).toMonoidHom ≤ L ⊔ L' := by
      rw [← hcl]
      intro x hx
      rw [A38.mem_map_conj] at hx
      have := mem_conjClosure (Subgroup.mem_top g) hx
      simpa [mul_assoc] using this
    exact A38.eq_or_eq_of_le_sup h37 (A38.cComp_conj hLc) hLc hL'c hle
  have hidx : ∀ x y : Γ, x ∉ Subgroup.normalizer (L : Set Γ) →
      y ∉ Subgroup.normalizer (L : Set Γ) → x⁻¹ * y ∈ Subgroup.normalizer (L : Set Γ) :=
    fun x y hx hy => index_two' hconj hx hy
  have hPNL : P ≤ Subgroup.normalizer (L : Set Γ) := by
    intro a ha
    by_contra hna
    have hodd : 2 * ((p + 1) / 2) = p + 1 := by
      obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
      omega
    have ha2 : a * a ∉ Subgroup.normalizer (L : Set Γ) := by
      intro h
      apply hna
      have e : (a * a) ^ ((p + 1) / 2) = a := by
        rw [← pow_two, ← pow_mul, hodd, pow_succ, hexp a ha, one_mul]
      rw [← e]
      exact Subgroup.pow_mem _ h _
    have := hidx a (a * a) hna ha2
    rw [show a⁻¹ * (a * a) = a by group] at this
    exact hna this
  have hKn : (L ⊔ L').Normal := by
    rw [← hcl]
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure L ⊤))
  have hL'C : L' ≤ Subgroup.centralizer (L : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hKNL : L ⊔ L' ≤ Subgroup.normalizer (L : Set Γ) :=
    sup_le Subgroup.le_normalizer (hL'C.trans (P134.centralizer_le_normalizer_self L))
  have hNL' : Subgroup.normalizer (L : Set Γ) ≤ Subgroup.normalizer (L' : Set Γ) := by
    intro g hg
    have hgt : L'.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj (g * t)).toMonoidHom := by
      rw [hL', Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rcases hconj (g * t) with h | h
    · exfalso
      apply htn
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) (A38.map_conj_eq_iff.mp h)
      rwa [inv_mul_cancel_left] at this
    · exact A38.map_conj_eq_iff.mp (hgt.trans h)
  have hTL : ¬ T ≤ Subgroup.normalizer (L : Set Γ) := by
    intro hTle
    have hidx2 : (Subgroup.normalizer (L : Set Γ)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨t, fun b => ?_⟩
      by_cases hb : b ∈ Subgroup.normalizer (L : Set Γ)
      · refine Or.inr ⟨hb, fun h => htn ?_⟩
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
        rwa [inv_mul_cancel_left] at this
      · refine Or.inl ⟨?_, hb⟩
        have hbi : b⁻¹ ∉ Subgroup.normalizer (L : Set Γ) := by
          intro h
          apply hb
          simpa using Subgroup.inv_mem _ h
        have := hidx b⁻¹ t hbi htn
        rwa [inv_inv] at this
    have h2 : 2 ∣ T.index := hidx2 ▸ Subgroup.index_dvd_of_le hTle
    have hT2 : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rw [Subgroup.relIndex_top_right] at hT2
    exact hT2 h2
  have hN2 : IsPGroup 2 N := hT.2.1.to_le hNT
  have hirrΦ : ∀ U : Subgroup Γ, frattiniIn P ≤ U → U ≤ P →
      N ≤ Subgroup.normalizer (U : Set Γ) → U = frattiniIn P ∨ U = P := by
    intro U hΦU hUP hNU
    rw [hΦ] at hΦU ⊢
    exact hirr U hΦU hUP hNU
  have hPN₀ : P ≤ ⁅P, N ⊓ Subgroup.normalizer (L : Set Γ)⁆ := by
    have h1 := eq_commutator_frattiniIn_of_irreducible hPp hexp hc2 hN2 hNP hirrΦ
    have h2 : frattiniIn N ≤ N ⊓ Subgroup.normalizer (L : Set Γ) :=
      frattiniIn_le_of_index_two fun x _ y _ hx hy => hidx x y hx hy
    calc P = ⁅P, frattiniIn N⁆ := h1
      _ ≤ ⁅P, N ⊓ Subgroup.normalizer (L : Set Γ)⁆ := Subgroup.commutator_mono le_rfl h2
  have hcommP : ∀ a ∈ P, ∀ n ∈ N, ⁅a, n⁆ ∈ P := by
    intro a ha n hn
    rw [commutatorElement_def]
    have h1 : n * a⁻¹ * n⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hNP hn) a⁻¹).mp (P.inv_mem ha)
    have e : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
    rw [e]
    exact P.mul_mem ha h1
  have hpL : p ∣ Nat.card L := by
    by_contra hpL
    apply hLP
    refine hPN₀.trans ?_
    rw [Subgroup.commutator_le]
    intro a ha n hn
    have h1 : ⁅a, n⁆ ∈ L ⊔ Subgroup.centralizer (L : Set Γ) :=
      hOut Γ L hyp hL htypes a (hPNL ha) n hn.2
    exact mem_of_mem_sup_of_coprime le_rfl hpL h1 (hexp _ (hcommP a ha n hn.1))
  have hPL1 : P ⊓ L ≠ ⊥ := fun h => false_of_normalizes' hrank hexp hc2 hPNL h hpL
  have hPNL' : P ≤ Subgroup.normalizer (L' : Set Γ) := hPNL.trans hNL'
  have hcardL' : Nat.card L' = Nat.card L := (Nat.card_congr (A38.conjEquiv t L).toEquiv).symm
  obtain ⟨n, hnN, hnL⟩ : ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) := by
    by_contra hall
    push Not at hall
    have hNL : N ≤ Subgroup.normalizer (L : Set Γ) := fun n hn => hall n hn
    have hNK : N ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup Γ) : Set Γ) :=
      le_normalizer_of_normal hKn N
    rcases inf_le_or_le_of_irreducible hPp hexp hNP hirr hNK with h | h
    ·
      have hPL : P ⊓ L ≤ ⁅P, P⁆ := (inf_le_inf_left P le_sup_left).trans h
      have hPL' : P ⊓ L' ≤ ⁅P, P⁆ := (inf_le_inf_left P le_sup_right).trans h
      have h4 := card_commutator_le hexp hc2 hc3
      have hPLeq : P ⊓ L = ⁅P, P⁆ := Subgroup.eq_of_le_of_card_ge hPL
        (h4.trans (le_card_of_ne_bot (hPp.to_le inf_le_left) hPL1))
      have hPL'1 : P ⊓ L' = ⊥ := by
        by_contra hne
        have hPL'eq : P ⊓ L' = ⁅P, P⁆ := Subgroup.eq_of_le_of_card_ge hPL'
          (h4.trans (le_card_of_ne_bot (hPp.to_le inf_le_left) hne))
        apply hPL1
        refine eq_bot_iff.mpr fun x hx => ?_
        have hx' : x ∈ P ⊓ L' := hPL'eq ▸ hPLeq ▸ hx
        have hxLL : x ∈ L ⊓ L' := ⟨hx.2, hx'.2⟩
        rw [hinf] at hxLL
        exact hxLL
      exact false_of_normalizes' hrank hexp hc2 hPNL' hPL'1 (hcardL' ▸ hpL)
    ·
      have hOK : O ≤ L ⊔ L' := hOX _ hKn h
      exact hTL (hTON.trans (sup_le (hOK.trans hKNL) hNL))
  have hnL' : L.map (MulAut.conj n).toMonoidHom = L' :=
    (hconj n).resolve_left fun h => hnL (A38.map_conj_eq_iff.mp h)
  set A := P ⊓ L with hA
  set A' := P ⊓ L' with hA'
  have hPn : P.map (MulAut.conj n).toMonoidHom = P := A38.map_conj_eq_iff.mpr (hNP hnN)
  have hAA'map : A.map (MulAut.conj n).toMonoidHom = A' := by
    rw [hA, hA', Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective,
      hPn, hnL']
  have hcardA' : Nat.card A' = Nat.card A := by
    rw [← hAA'map, Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hAA' : A ⊓ A' = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ L ⊓ L' := ⟨hx.1.2, hx.2.2⟩
    rw [hinf] at this
    exact this
  have hA'NA : A' ≤ Subgroup.normalizer (A : Set Γ) :=
    inf_le_left.trans (le_normalizer_inf' Subgroup.le_normalizer hPNL)
  have hcardAA' := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A A' hA'NA
    (disjoint_iff.mpr hAA')
  have hAA'P : A ⊔ A' ≤ P := sup_le inf_le_left inf_le_left
  have hAp : Nat.card A = p := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hPp.to_le (inf_le_left : A ≤ P))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hPL1 (Subgroup.card_eq_one.mp hk)
    have hle : Nat.card A * Nat.card A ≤ p ^ 3 := by
      calc Nat.card A * Nat.card A = Nat.card A * Nat.card A' := by rw [hcardA']
        _ = Nat.card (A ⊔ A' : Subgroup Γ) := hcardAA'.symm
        _ ≤ p ^ 3 := (Subgroup.card_le_of_le hAA'P).trans hc3
    rw [hk, ← pow_add] at hle
    have hk2 : k + k ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
    have hk1 : k = 1 := by omega
    rw [hk, hk1, pow_one]
  have hA'p : Nat.card A' = p := hcardA'.trans hAp
  have hPAA : P = A ⊔ A' := by
    refine (Subgroup.eq_of_le_of_card_ge hAA'P ?_).symm
    rw [hcard, hcardAA', hAp, hA'p, sq]
  have hPK : P ≤ L ⊔ L' := by
    rw [hPAA]
    exact sup_le_sup inf_le_right inf_le_right
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hPL1 ((Subgroup.eq_bot_iff_forall A).2 hall)
  have hao : orderOf a = p := by
    have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hexp a haA.1)
    rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hU : IsSylowTwoOf (T ⊓ L) L := by
    have h1 : IsSylowTwoOf (T ⊓ (L ⊔ L')) (L ⊔ L') :=
      A4.isSylowTwoOf_inf_normal hT le_top (le_normalizer_of_normal hKn ⊤)
    have h2 := A4.isSylowTwoOf_inf_normal h1 le_sup_left hKNL
    rwa [inf_assoc, show (L ⊔ L') ⊓ L = L from inf_eq_right.mpr le_sup_left] at h2
  have hB2p : ∀ q : ℕ, q.Prime → q ∣ Nat.card (L ⊓ (P ⊔ T) : Subgroup Γ) → q = 2 ∨ q = p :=
    prime_dvd_of_le_sup' hp2 hPp hT.2.1 hmul inf_le_right
  have hUB : T ⊓ L ≤ L ⊓ (P ⊔ T) := le_inf inf_le_right (inf_le_left.trans le_sup_right)
  have haB : a ∈ L ⊓ (P ⊔ T) := ⟨haA.2, Subgroup.mem_sup_left haA.1⟩
  refine ⟨n, hnN, hnL, by rw [hnL']; exact hinf, hnL' ▸ hPK, hAp, hcard, ?_⟩
  rcases htypes with ⟨m, hm⟩ | ⟨m, hsz⟩ | eJ | ⟨q, hq, hq3, hpsl⟩
  ·
    exact Or.inl ⟨m, hBorel Γ L _ _ m p a hp.out hp5' hm hUB inf_le_left hU hB2p haB hao, hm⟩
  ·
    subst hp5
    exact (hSz Γ L _ _ m a hsz hUB inf_le_left hU hB2p haB hao).elim
  ·
    subst hp5
    exact (hJ1 Γ L _ _ a eJ hUB inf_le_left hU hB2p haB hao).elim
  ·
    exact Or.inr ⟨q, hq, by omega, hpsl⟩

end CFSG.Quasithin.S146zY
