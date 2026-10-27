module

public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem index_two' {L L' : Subgroup Γ}
    (hconj : ∀ g : Γ, L.map (MulAut.conj g).toMonoidHom = L ∨
      L.map (MulAut.conj g).toMonoidHom = L')
    {x y : Γ} (hx : x ∉ Subgroup.normalizer (L : Set Γ))
    (hy : y ∉ Subgroup.normalizer (L : Set Γ)) :
    x⁻¹ * y ∈ Subgroup.normalizer (L : Set Γ) := by
  have hxL : L.map (MulAut.conj x).toMonoidHom = L' :=
    (hconj x).resolve_left fun h => hx (A38.map_conj_eq_iff.mp h)
  have hyL : L.map (MulAut.conj y).toMonoidHom = L' :=
    (hconj y).resolve_left fun h => hy (A38.map_conj_eq_iff.mp h)
  have hxy := hxL.trans hyL.symm
  rw [Subgroup.mem_normalizer_iff]
  intro l
  have h1 := (SetLike.ext_iff.mp hxy) (y * l * y⁻¹)
  rw [A38.mem_map_conj, A38.mem_map_conj] at h1
  have e1 : y⁻¹ * (y * l * y⁻¹) * y = l := by group
  have e2 : x⁻¹ * (y * l * y⁻¹) * x = x⁻¹ * y * l * (x⁻¹ * y)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1.symm

theorem frattiniIn_le_of_index_two [Finite Γ] {N M : Subgroup Γ}
    (hidx : ∀ x ∈ N, ∀ y ∈ N, x ∉ M → y ∉ M → x⁻¹ * y ∈ M) : frattiniIn N ≤ N ⊓ M := by
  by_cases hall : ∀ n ∈ N, n ∈ M
  · exact le_inf (Subgroup.map_subtype_le _) ((Subgroup.map_subtype_le _).trans hall)
  push Not at hall
  obtain ⟨x, hxN, hxM⟩ := hall
  have hidx2 : (M.subgroupOf N).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hxN⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : Γ) ∈ M
    · refine Or.inr ⟨hb, fun h => hxM ?_⟩
      have := M.mul_mem (M.inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hb⟩
      have hbi : (b : Γ)⁻¹ ∉ M := fun h => hb (by simpa using M.inv_mem h)
      have := hidx (b : Γ)⁻¹ (N.inv_mem b.2) x hxN hbi hxM
      rwa [inv_inv] at this
  have hco : IsCoatom (M.subgroupOf N) :=
    Subgroup.isCoatom_of_index_prime (hidx2 ▸ Nat.prime_two)
  have h1 : frattini ↥N ≤ M.subgroupOf N := frattini_le_coatom hco
  refine le_inf (Subgroup.map_subtype_le _) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hz)

variable [Finite Γ]

theorem pair_case_odd (hyp : SQTKHypCat Γ) (h37 : A37Statement Γ) (h38 : A38Part3 Γ)
    (hF : Facts134Odd) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {P T N O L : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3)
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
      ((∃ m : ℕ, Even m ∧ p ∣ 2 ^ m - 1 ∧ StatedClassicalModel ↥L .PSL 2 2 m) ∨
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel ↥L .PSL 2 q 1) := by
  have hp2 : p ≠ 2 := by omega
  have hrank : Open.pRank p (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) p hp.out hp2
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rcases hcard with h | h <;> rw [h]
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
      hF.outAbelian Γ L hyp hL htypes a (hPNL ha) n hn.2
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
  have hP2 : Nat.card P = p ^ 2 := by
    rcases hcard with h | h
    · exact h
    exfalso
    have hAc := commute_of_normal_of_card_eq_prime hPp inf_le_left
      (le_normalizer_inf' Subgroup.le_normalizer hPNL) hAp
    have hA'c := commute_of_normal_of_card_eq_prime hPp inf_le_left
      (le_normalizer_inf' Subgroup.le_normalizer hPNL') hA'p
    set E := A ⊔ A' with hE
    have hEcard : Nat.card E = p ^ 2 := by rw [hcardAA', hAp, hA'p, sq]
    have hEZ : E ≤ (Subgroup.center ↥P).map P.subtype := by
      refine sup_le ?_ ?_
      · intro a ha
        refine ⟨⟨a, ha.1⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩
        exact (hAc a ha x x.2).symm
      · intro a ha
        refine ⟨⟨a, ha.1⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩
        exact (hA'c a ha x x.2).symm
    have hcen : ∀ a ∈ E, ∀ x ∈ P, a * x = x * a := by
      intro a ha x hx
      obtain ⟨z, hz, rfl⟩ := hEZ ha
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)).symm
    have hEel : IsElemAbelian p E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hexp x (hAA'P hx)⟩
      exact hcen a a.2 b (hAA'P b.2)
    obtain ⟨x, hxP, hxE⟩ : ∃ x ∈ P, x ∉ E := by
      by_contra hall
      push Not at hall
      have hle : Nat.card P ≤ Nat.card E := Subgroup.card_le_of_le hall
      rw [h, hEcard] at hle
      have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
      omega
    exact false_of_commute' hrank hEel hEcard hxE (hexp x hxP)
      fun a ha => (hcen a ha x hxP)
  have hPAA : P = A ⊔ A' := by
    refine (Subgroup.eq_of_le_of_card_ge hAA'P ?_).symm
    rw [hP2, hcardAA', hAp, hA'p, sq]
  have hPK : P ≤ L ⊔ L' := by
    rw [hPAA]
    exact sup_le_sup inf_le_right inf_le_right
  have hNinv : ∀ g ∈ N ⊓ Subgroup.normalizer (L : Set Γ),
      g ∈ Subgroup.normalizer (A : Set Γ) := fun _ hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNP hg.1, hg.2⟩
  obtain ⟨g, hgN₀, a, haA, hga⟩ : ∃ g ∈ N ⊓ Subgroup.normalizer (L : Set Γ), ∃ a ∈ A,
      g * a * g⁻¹ ≠ a := by
    by_contra hall
    push Not at hall
    have hall' : ∀ g ∈ N ⊓ Subgroup.normalizer (L : Set Γ), ∀ b ∈ A', g * b * g⁻¹ = b := by
      intro g hg b hb
      have hg'N : n⁻¹ * g * n ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hnN) hg.1) hnN
      have hg'L : n⁻¹ * g * n ∈ Subgroup.normalizer (L : Set Γ) := by
        have h1 : L.map (MulAut.conj (n⁻¹ * g * n)).toMonoidHom = L := by
          have e : L.map (MulAut.conj (n⁻¹ * g * n)).toMonoidHom =
              ((L.map (MulAut.conj n).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
                (MulAut.conj n⁻¹).toMonoidHom := by
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          rw [e, hnL', A38.map_conj_eq_iff.mpr (hNL' hg.2), ← hnL', Subgroup.map_map]
          have e2 : ((MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom) =
              MonoidHom.id Γ := by
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          rw [e2, Subgroup.map_id]
        exact A38.map_conj_eq_iff.mp h1
      have hbA : n⁻¹ * b * n ∈ A := by
        rw [← hAA'map] at hb
        rw [A38.mem_map_conj] at hb
        exact hb
      have h1 := hall _ ⟨hg'N, hg'L⟩ _ hbA
      calc g * b * g⁻¹ = n * ((n⁻¹ * g * n) * (n⁻¹ * b * n) * (n⁻¹ * g * n)⁻¹) * n⁻¹ := by
            group
        _ = n * (n⁻¹ * b * n) * n⁻¹ := by rw [h1]
        _ = b := by group
    apply hP1
    refine eq_bot_iff.mpr (hPN₀.trans ?_)
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have hgC : P ≤ Subgroup.centralizer ({g} : Set Γ) := by
      rw [hPAA]
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hall g hg a ha
        calc a * g = g * a * g⁻¹ * g := by rw [this]
          _ = g * a := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hall' g hg b hb
        calc b * g = g * b * g⁻¹ * g := by rw [this]
          _ = g * b := by group
    have hxg := Subgroup.mem_centralizer_singleton_iff.mp (hgC hx)
    rw [Subgroup.mem_bot, commutatorElement_def, hxg]
    group
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hga (by group)
  have hao : orderOf a = p := by
    have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hexp a haA.1)
    rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hza : Subgroup.zpowers a = A := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr haA) (by rw [hAp, Nat.card_zpowers, hao])
  have hU : IsSylowTwoOf (T ⊓ L) L := by
    have h1 : IsSylowTwoOf (T ⊓ (L ⊔ L')) (L ⊔ L') :=
      A4.isSylowTwoOf_inf_normal hT le_top (le_normalizer_of_normal hKn ⊤)
    have h2 := A4.isSylowTwoOf_inf_normal h1 le_sup_left hKNL
    rwa [inf_assoc, show (L ⊔ L') ⊓ L = L from inf_eq_right.mpr le_sup_left] at h2
  have hB2p : ∀ q : ℕ, q.Prime → q ∣ Nat.card (L ⊓ (P ⊔ T) : Subgroup Γ) → q = 2 ∨ q = p :=
    prime_dvd_of_le_sup' hp2 hPp hT.2.1 hmul inf_le_right
  have hUB : T ⊓ L ≤ L ⊓ (P ⊔ T) := le_inf inf_le_right (inf_le_left.trans le_sup_right)
  have haB : a ∈ L ⊓ (P ⊔ T) := ⟨haA.2, Subgroup.mem_sup_left haA.1⟩
  have hgL : g ∈ Subgroup.normalizer (L : Set Γ) := hgN₀.2
  have hgU : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hNT hgN₀.1), hgL⟩
  have hgy : g ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) := by
    rw [hza]
    exact hNinv g hgN₀
  have hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT.2.1 ⟨g, hNT hgN₀.1⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨n, hnN, hnL, by rw [hnL']; exact hinf, hnL' ▸ hPK, hAp, hP2, ?_⟩
  rcases htypes with ⟨m, hm⟩ | ⟨m, hsz⟩ | eJ | ⟨q, hq, hq3, hpsl⟩
  ·
    refine Or.inl ⟨m, ?_, ?_, hm⟩
    · exact hF.psl2Even Γ L _ _ m p a g hyp hp.out hp5 hm hUB inf_le_left hU hB2p haB hao hgL
        hgU hgy hg2 hga
    · exact hF.psl2Borel Γ L _ _ m p a hyp hp.out hp5 hm hUB inf_le_left hU hB2p haB hao
  ·
    exact absurd (hF.szLocal Γ L _ _ m p a g hyp hp.out hp5 hsz hUB inf_le_left hU hB2p haB hao
      hgL hgU hgy hg2) hga
  ·
    exact absurd (hF.j1Local Γ L _ _ p a g hyp hp.out hp5 eJ hUB inf_le_left hU hB2p haB hao
      hgL hgU hgy hg2) hga
  ·
    exact Or.inr ⟨q, hq, by omega, hpsl⟩

end CFSG.Quasithin.H13.NQCore
