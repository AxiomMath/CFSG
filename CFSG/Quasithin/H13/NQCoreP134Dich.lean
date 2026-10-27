module

public import CFSG.Quasithin.H13.NQCoreP134
public import CFSG.Quasithin.Vol2.Ch1Sec3Thm137
public import CFSG.Quasithin.H13.NQCoreP134Pair
public import CFSG.Quasithin.H13.NQCoreP134Setup
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Fitting

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def OutCyclicFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L U : Subgroup A) (p : ℕ), p.Prime → 5 ≤ p →
    SQTKHypCat A → L.Normal → CFSG.IsComponent L → IsPGroup p U →
    ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ (L ⊔ Subgroup.centralizer (L : Set A))

@[expose] def OutAbelianFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
    CFSG.IsComponent L → A38Types ↥L → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A)

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_of_normal_case_odd (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    (hOC : OutCyclicFact)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {P N L : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    P ≤ L := by
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
  have hpsq : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  set C := Subgroup.centralizer (L : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  set D := L ⊔ C with hDdef
  have hDn : D.Normal := Subgroup.sup_normal L C
  have hinv := fun (W : Subgroup Γ) (hW : N ≤ Subgroup.normalizer (W : Set Γ)) =>
    inf_le_or_le_of_irreducible hPp hexp hNP hirr hW
  have hPD : P ≤ D := by
    rcases hinv D (le_normalizer_of_normal hDn N) with h | h
    · exfalso
      obtain ⟨u, huP, hu⟩ := hOC Γ L P p hp.out hp5 hyp hLn hL hPp
      have huP' : Subgroup.zpowers u ≤ P := Subgroup.zpowers_le.mpr huP
      have h1 : P ≤ Subgroup.zpowers u ⊔ (P ⊓ D) := by
        intro x hx
        have hx' := hu hx
        rw [sup_comm] at hx'
        obtain ⟨d, hd, v, hv, rfl⟩ :=
          (mem_sup_iff_of_le_normalizer (le_normalizer_of_normal hDn _)).1 hx'
        have hvP : v ∈ P := huP' hv
        have hdP : d ∈ P := by
          have := P.mul_mem hx (P.inv_mem hvP)
          simpa using this
        rw [sup_comm]
        exact Subgroup.mul_mem_sup ⟨hdP, hd⟩ hv
      have h2 : Subgroup.zpowers u ⊔ frattiniIn P = P :=
        le_antisymm (sup_le huP' (Subgroup.map_subtype_le _))
          (h1.trans (sup_le_sup_left (hΦ ▸ h) _))
      have h3 := eq_of_sup_frattiniIn_eq huP' h2
      have : Nat.card P ≤ p := by
        rw [← h3, Nat.card_zpowers]
        exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp u huP))
      omega
    · exact h
  have hPC : P ⊓ C ≤ ⁅P, P⁆ := by
    rcases hinv C (le_normalizer_of_normal hCn N) with h | h
    · exact h
    · exact absurd h hLP
  have hZ : Nat.card (L ⊓ C : Subgroup Γ) = 1 ∨ Nat.card (L ⊓ C : Subgroup Γ) = 3 := by
    rw [card_inf_centralizer]
    exact card_center_of_a36Common' hL.1 (h36 L hLc).2.1
  have hPZ : P ⊓ (L ⊓ C) = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hPp.to_le (inf_le_left : P ⊓ (L ⊓ C) ≤ P))
    have hdvd : Nat.card (P ⊓ (L ⊓ C) : Subgroup Γ) ∣ Nat.card (L ⊓ C : Subgroup Γ) :=
      Subgroup.card_dvd_of_le inf_le_right
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exfalso
      have hpd : p ∣ Nat.card (L ⊓ C : Subgroup Γ) :=
        (dvd_pow_self p h0.ne').trans (hk ▸ hdvd)
      rcases hZ with h1 | h3
      · rw [h1] at hpd
        exact hp.out.one_lt.ne' (Nat.dvd_one.mp hpd)
      · rw [h3] at hpd
        have := Nat.le_of_dvd (by norm_num) hpd
        omega
  have hPL : P ≤ L := by
    rcases hinv L (le_normalizer_of_normal hLn N) with h | h
    swap
    · exact h
    exfalso
    by_cases hpC : p ∣ Nat.card C
    · by_cases hPC1 : P ⊓ C = ⊥
      · exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hCn P) hPC1 hpC
      by_cases hPL1 : P ⊓ L = ⊥
      · by_cases hpL : p ∣ Nat.card L
        · exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hLn P) hPL1 hpL
        · apply hLP
          intro x hx
          exact mem_of_mem_sup_of_coprime (M := L) (M' := C) le_rfl hpL (hPD hx) (hexp x hx)
      have hle : (P ⊓ L) ⊔ (P ⊓ C) ≤ ⁅P, P⁆ := sup_le h hPC
      have hnorm : P ⊓ C ≤ Subgroup.normalizer ((P ⊓ L : Subgroup Γ) : Set Γ) :=
        le_normalizer_inf' (inf_le_left.trans Subgroup.le_normalizer)
          (inf_le_right.trans (P134.centralizer_le_normalizer_self L))
      have hdisj : Disjoint (P ⊓ L) (P ⊓ C) := by
        rw [disjoint_iff]
        refine eq_bot_iff.mpr fun x hx => ?_
        have hx' : x ∈ P ⊓ (L ⊓ C) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
        rw [hPZ] at hx'
        exact hx'
      have hcard' := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
      have h1 := le_card_of_ne_bot (hPp.to_le inf_le_left) hPL1
      have h2 := le_card_of_ne_bot (hPp.to_le inf_le_left) hPC1
      have h3 := Subgroup.card_le_of_le hle
      have h4 := card_commutator_le hexp hc2 hc3
      have h5 : p * p ≤ Nat.card (P ⊓ L : Subgroup Γ) * Nat.card (P ⊓ C : Subgroup Γ) :=
        Nat.mul_le_mul h1 h2
      rw [← hcard'] at h5
      have h6 : p < p * p := by
        have := hp.out.one_lt
        nlinarith
      omega
    ·
      have hPL' : P ≤ L := by
        intro x hx
        have hx' : x ∈ C ⊔ L := by rw [sup_comm]; exact hPD hx
        refine mem_of_mem_sup_of_coprime (M := C) (M' := L) ?_ hpC hx' (hexp x hx)
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm
      have hPc : P ≤ ⁅P, P⁆ := by
        have := (inf_eq_left.mpr hPL') ▸ h
        exact this
      exact frattiniIn_ne_of_ne_bot hP1 (le_antisymm (Subgroup.map_subtype_le _) (hΦ ▸ hPc))
  exact hPL

theorem le_sup_of_pair_case_odd (hyp : SQTKHypCat Γ) (h37 : A37Statement Γ)
    (h38 : A38Part3 Γ) (hOA : OutAbelianFact) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P T N O L : Subgroup Γ} (hexp : ∀ x ∈ P, x ^ p = 1)
    (hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : ¬ L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
      P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom := by
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
      hOA Γ L hyp hL htypes a (hPNL ha) n hn.2
    exact mem_of_mem_sup_of_coprime le_rfl hpL h1 (hexp _ (hcommP a ha n hn.1))
  have hPL1 : P ⊓ L ≠ ⊥ := fun h => false_of_normalizes' hrank hexp hc2 hPNL h hpL
  have hPNL' : P ≤ Subgroup.normalizer (L' : Set Γ) := hPNL.trans hNL'
  have hcardL' : Nat.card L' = Nat.card L := (Nat.card_congr (A38.conjEquiv t L).toEquiv).symm
  have hPK : P ≤ L ⊔ L' := by
    rcases inf_le_or_le_of_irreducible hPp hexp hNP hirr (le_normalizer_of_normal hKn N) with
      h | h
    ·
      exfalso
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
    · exact h
  obtain ⟨n, hnN, hnL⟩ : ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) := by
    by_contra hall
    push Not at hall
    have hOK : O ≤ L ⊔ L' := hOX _ hKn hPK
    exact hTL (hTON.trans (sup_le (hOK.trans hKNL) fun n hn => hall n hn))
  have hnL' : L.map (MulAut.conj n).toMonoidHom = L' :=
    (hconj n).resolve_left fun h => hnL (A38.map_conj_eq_iff.mp h)
  exact ⟨n, hnN, hnL, hnL' ▸ hPK⟩

theorem quotient_main_odd_dich (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    (h37 : A37Statement Γ) (h38 : A38Part3 Γ) (hOC : OutCyclicFact) (hOA : OutAbelianFact)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {P T N O : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hPc : P ≤ commutator Γ) :
    P.Normal ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧ L.Normal ∧ P ≤ L) ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧
        ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
          P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom) := by
  have hp2 : p ≠ 2 := by omega
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rcases hcard with h | h <;> rw [h]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  rcases P134.normal_or_centralizes_fitting hyp.o2 hrank hp2 hPp hexp hc2 hc3 hNP hirr hPc with
    hn | ⟨hFit, hrk⟩
  · exact Or.inl hn
  right
  have hrkP : 2 ≤ Open.pRank p P := two_le_pRank_of_pow_eq_one hexp hc2
  obtain ⟨L, hL, hLP⟩ := P134.exists_component_not_le_centralizer hPp hrkP hFit hrk
  have hLc : L ∈ cComp (⊤ : Subgroup Γ) := mem_cComp_top_of_isComponent hL
  by_cases hLn : L.Normal
  · exact Or.inl ⟨L, hLc, hL, hLn,
      le_of_normal_case_odd hyp h36 hOC hp5 hexp hcard hNP hirr hLc hL hLn hLP⟩
  · exact Or.inr ⟨L, hLc, hL,
      le_sup_of_pair_case_odd hyp h37 h38 hOA hp2 hexp hcard hT hNT hNP hirr hTON hOX hLc hL hLn
        hLP⟩

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem prop134_odd_case_dich (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hOC : OutCyclicFact) (hOA : OutAbelianFact) {H S X P : Subgroup G}
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hsqtk : CFSG.SectionRank.IsSQTKCat ↥H)
    (hS : IsSylowTwoOf S H) (hXH : X ≤ H) (hX : IsXi S X) (hPX : P ≤ X) (hPp : IsPGroup p P)
    (hPcard : Nat.card P = (pCoreOf 2 X).relIndex X) :
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L ∈ cComp H, CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ X ≤ conjClosure L S := by
  have hp2 : p ≠ 2 := by omega
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hyp : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHypCat.quotient_pCore ↥H hsqtk
  obtain ⟨hpX, hSyl⟩ := sylow_of_card_eq_relIndex hX hp2 hPX hPp hPcard
  have hPH : P ≤ H := hPX.trans hXH
  have hexp := exp_of_sylow hX hp2 hpX hSyl
  have hPO : P ⊓ pCoreOf 2 H = ⊥ := inf_pCoreOf_eq_bot' hp2 hPp
  have hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3 := by
    obtain ⟨k, hk2, hk3, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
    rw [hPcard, hk]
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcardb : Nat.card (modO2Image H P) = p ^ 2 ∨ Nat.card (modO2Image H P) = p ^ 3 := by
    rw [card_bar_of_sylow hXH hp2 hSyl]
    exact hcard
  have hirr := irr_modO2Image' hPH (inf_le_left.trans hS.1) inf_le_right
    (irr_of_sylow hS hXH hX hp2 hpX hSyl)
  have hNT : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤ modO2Image H S :=
    P134.modO2Image_mono inf_le_left
  have hNP : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    P134.modO2Image_le_normalizer inf_le_right
  have hXK : ∀ K : Subgroup G, H ≤ Subgroup.normalizer (K : Set G) → P ≤ K → X ≤ K := by
    intro K hHK hPK
    rw [cl_of_sylow hX hp2 hpX hSyl]
    exact conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHK (hXH hh)) z).mp (hPK hz)
  have hPpull : ∀ K : Subgroup G, pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) →
      modO2Image H P ≤ modO2Image H K → P ≤ K := fun K hOK hPK a ha =>
    mem_of_mem_modO2Image' hp2 hOK (hPH ha) (hexp a ha)
      (hPK (P134.mk_mem_modO2Image ha (hPH ha)))
  rcases quotient_main_odd_dich hyp (h36 _ hyp) (h37 _ hyp) (h38 _ hyp) hOC hOA hp5
      (exp_bar_of_sylow hX hp2 hpX hSyl) hcardb (P134.sylow_bar hS) hNT hNP hirr
      (sup_bar_of_sylow hS hXH hX hp2 hpX hSyl) (oX_bar_of_sylow hXH hX hp2 hpX hSyl)
      (comm_bar_of_sylow hS hXH hX hp2 hpX hSyl) with
    hn | ⟨Lb, hLbc, hLb, hLbn, hPLb⟩ | ⟨Lb, hLbc, hLb, nb, hnbN, -, hPK⟩
  ·
    exact Or.inl (le_normalizer_of_normal_of_sylow hS hXH hX hp2 hpX hSyl hn)
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    have hLH : L ≤ H := le_of_mem_cComp hL
    have hLnH : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hLbn
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnH
    have hSL : S ≤ Subgroup.normalizer (L : Set G) := hS.1.trans hHL
    have hPL : P ≤ L := hPpull L (P134.pCoreOf_le_normalizer_of_mem_cComp hL) hPLb
    have hcl : conjClosure L S = L := by
      refine le_antisymm (conjClosure_le fun g hg l hl => ?_) (le_conjClosure L S)
      exact (Subgroup.mem_normalizer_iff.mp (hSL hg) l).mp hl
    exact ⟨L, hL, hq, hcl.symm ▸ hXK L hHL hPL⟩
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    obtain ⟨t', ht', rfl⟩ := hnbN
    set t : G := (t' : G) with ht
    have htSN : t ∈ S ⊓ Subgroup.normalizer (P : Set G) := ht'
    have htH : t ∈ H := t'.2
    set Lt := L.map (MulAut.conj t).toMonoidHom with hLt
    have hLtc : Lt ∈ cComp H := map_conj_mem_cComp hL htH
    have hLtb : modO2Image H Lt = (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
      modO2Image_conj t'
    have hOLt : pCoreOf 2 H ≤ Subgroup.normalizer ((L ⊔ Lt : Subgroup G) : Set G) :=
      fun o ho => Subgroup.inf_normalizer_le_normalizer_sup L Lt
        ⟨P134.pCoreOf_le_normalizer_of_mem_cComp hL ho,
          P134.pCoreOf_le_normalizer_of_mem_cComp hLtc ho⟩
    have hPLLt : P ≤ L ⊔ Lt := by
      refine hPpull _ hOLt (hPK.trans ?_)
      rw [← hLtb]
      exact sup_le (P134.modO2Image_mono le_sup_left) (P134.modO2Image_mono le_sup_right)
    have hLLtS : L ⊔ Lt ≤ conjClosure L S := by
      refine sup_le (le_conjClosure L S) ?_
      rintro _ ⟨l, hl, rfl⟩
      exact mem_conjClosure htSN.1 hl
    have hHcl : H ≤ Subgroup.normalizer (conjClosure L S : Set G) :=
      normal_conjClosure_of_subgroup hS hL (h37 _ hyp) (h38 _ hyp)
    exact ⟨L, hL, hq, hXK _ hHcl (hPLLt.trans hLLtS)⟩

theorem prop134Dich_of (hE9 : EmptyFaithfulMultiple.Prop134E9He)
    (h3x : Prop134ThreeExtraspecial) (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hOC : OutCyclicFact) (hOA : OutAbelianFact) : Prop134Dich := by
  intro G _ _ H S X P p hp hH hR hS hXH hX hp2 _ hPX hPp hPcard
  have hp3 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.out.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · left
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp.out (by decide)
    · exact Or.inr h
  rcases hp3 with rfl | hp5
  ·
    obtain ⟨hpX, -⟩ := sylow_of_card_eq_relIndex hX hp2 hPX hPp hPcard
    obtain ⟨k, hk2, hk3, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
    interval_cases k
    ·
      have h9 : (pCoreOf 2 X).relIndex X = 9 := by rw [hk]; norm_num
      rcases hE9 G H S X P hH hR hS hXH hX h9 hPX hPp (hPcard.trans h9) with
        hn | ⟨L, hL, hq, hXL, -⟩
      · exact Or.inl hn
      · exact Or.inr ⟨L, hL, hq, hXL⟩
    ·
      have h27 : (pCoreOf 2 X).relIndex X = 27 := by rw [hk]; norm_num
      exact Or.inl (h3x G H S X P hH hR hS hXH hX h27 hPX hPp (hPcard.trans h27))
  · exact prop134_odd_case_dich h36 h37 h38 hOC hOA hp5 hH hS hXH hX hPX hPp hPcard

theorem input137_of_dich (hE9 : EmptyFaithfulMultiple.Prop134E9He)
    (h3x : Prop134ThreeExtraspecial) (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hOC : OutCyclicFact) (hOA : OutAbelianFact) :
    EmptyFaithfulMultiple.Input137 :=
  Thm137.input137_of_prop134Dich (prop134Dich_of hE9 h3x h36 h37 h38 hOC hOA)

end CFSG.Quasithin.H13.NQCore
