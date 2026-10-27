module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Normal

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem index_two {L L' : Subgroup Γ}
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

omit [Finite Γ] in
theorem inf_centralizer_eq_bot (h36 : A36CoreStatementCat Γ) {L : Subgroup Γ}
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (h3 : ¬ 3 ∣ Nat.card L) :
    L ⊓ Subgroup.centralizer (L : Set Γ) = ⊥ := by
  have hZ1 : Subgroup.center ↥L = ⊥ := by
    rcases card_center_of_a36Common hL.1 (h36 L hLc).2.1 with h1 | h3'
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply h3
      rw [← h3']
      exact Subgroup.card_subgroup_dvd_card _
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxZ : (⟨x, hx.1⟩ : L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) l l.2)
  rw [hZ1, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)

theorem pair_case (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ) (h37 : A37Statement Γ)
    (h38 : A38Part3 Γ) (hF : Facts134E9He) {P T N O L : Subgroup Γ} (hP9 : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) → U = ⊥ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : ¬ L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
      L ⊓ L.map (MulAut.conj n).toMonoidHom = ⊥ ∧
      P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom ∧ Nat.card (P ⊓ L : Subgroup Γ) = 3 ∧
      ((∃ m : ℕ, Even m ∧ StatedClassicalModel ↥L .PSL 2 2 m) ∨
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel ↥L .PSL 2 q 1) := by
  have hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) 3 Nat.prime_three (by norm_num)
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
    fun x y hx hy => index_two hconj hx hy
  have hPNL : P ≤ Subgroup.normalizer (L : Set Γ) := by
    intro a ha
    by_contra hna
    have ha2 : a * a ∉ Subgroup.normalizer (L : Set Γ) := by
      intro h
      apply hna
      have e : a = (a * a)⁻¹ * a ^ 3 := by group
      rw [e, hexp a ha, mul_one]
      exact Subgroup.inv_mem _ h
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
    sup_le Subgroup.le_normalizer (hL'C.trans (centralizer_le_normalizer_self L))
  have hnK : ∀ K : Subgroup Γ, K ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup Γ) : Set Γ) :=
    fun K => by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
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
  have hNinv : ∀ {A : Subgroup Γ}, N ≤ Subgroup.normalizer (A : Set Γ) →
      N ≤ Subgroup.normalizer ((P ⊓ A : Subgroup Γ) : Set Γ) :=
    fun hA => le_normalizer_inf hNP hA
  have hnotcen : ¬ ∀ n ∈ N, n ∈ Subgroup.normalizer (L : Set Γ) → ∀ a ∈ P, n * a * n⁻¹ = a := by
    intro hcen
    obtain ⟨U, hUP, hU1, hUP', hNU⟩ := exists_invariant_of_index_two
      (N₀ := Subgroup.normalizer (L : Set Γ)) hP9 hexp hNP hcen
      (fun x _ y _ hx hy => hidx x y hx hy)
    rcases hirr U hUP hNU with h | h
    · exact hU1 h
    · exact hUP' h
  have hstruct : 3 ∣ Nat.card L → ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
      L.map (MulAut.conj n).toMonoidHom = L' ∧ P ≤ L ⊔ L' ∧
      Nat.card (P ⊓ L : Subgroup Γ) = 3 := by
    intro h3
    have hPL1 : P ⊓ L ≠ ⊥ := fun h => false_of_normalizes hrank hP9 hexp hPNL h h3
    obtain ⟨n, hnN, hnL⟩ : ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) := by
      by_contra hall
      push Not at hall
      rcases hirr (P ⊓ L) inf_le_left (hNinv hall) with h | h
      · exact hPL1 h
      · have hPK : P ≤ L ⊔ L' := (h ▸ inf_le_right : P ≤ L).trans le_sup_left
        have hOK : O ≤ L ⊔ L' := hOX _ hKn hPK
        exact hTL (hTON.trans (sup_le (hOK.trans hKNL) hall))
    have hnL' : L.map (MulAut.conj n).toMonoidHom = L' :=
      (hconj n).resolve_left fun h => hnL (A38.map_conj_eq_iff.mp h)
    have hPLP : P ⊓ L ≠ P := by
      intro h
      have hPL : P ≤ L := h ▸ inf_le_right
      have hPn : P.map (MulAut.conj n).toMonoidHom = P := A38.map_conj_eq_iff.mpr (hNP hnN)
      have hPL' : P ≤ L' := by
        rw [← hPn, ← hnL']
        exact Subgroup.map_mono hPL
      have hbot : P ≤ L ⊓ L' := le_inf hPL hPL'
      rw [hinf] at hbot
      have := Subgroup.card_le_of_le hbot
      rw [Subgroup.card_bot, hP9] at this
      omega
    refine ⟨n, hnN, hnL, hnL', ?_, card_eq_three_of_lt hP9 inf_le_left hPL1 hPLP⟩
    rcases hirr (P ⊓ (L ⊔ L')) inf_le_left (hNinv (hnK N)) with h | h
    · exact absurd (eq_bot_iff.mpr ((inf_le_inf_left P le_sup_left).trans h.le)) hPL1
    · exact h ▸ inf_le_right
  have hy : Nat.card (P ⊓ L : Subgroup Γ) = 3 → ∃ y : Γ, y ∈ P ⊓ L ∧ orderOf y = 3 ∧
      Subgroup.zpowers y = P ⊓ L := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ L)) 3 (by rw [h3])
    have hy3 : orderOf (y : Γ) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
    refine ⟨y, y.2, hy3, ?_⟩
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2) ?_
    rw [h3, Nat.card_zpowers, hy3]
  have hU : IsSylowTwoOf (T ⊓ L) L := by
    have h1 : IsSylowTwoOf (T ⊓ (L ⊔ L')) (L ⊔ L') :=
      A4.isSylowTwoOf_inf_normal hT le_top (hnK ⊤)
    have h2 := A4.isSylowTwoOf_inf_normal h1 le_sup_left hKNL
    rwa [inf_assoc, show (L ⊔ L') ⊓ L = L from inf_eq_right.mpr le_sup_left] at h2
  have hB23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (L ⊓ (P ⊔ T) : Subgroup Γ) → q = 2 ∨ q = 3 :=
    prime_dvd_of_le_sup hP9 hT.2.1 hmul inf_le_right
  have hUB : T ⊓ L ≤ L ⊓ (P ⊔ T) := le_inf inf_le_right (inf_le_left.trans le_sup_right)
  have hyB : ∀ y, y ∈ P ⊓ L → y ∈ L ⊓ (P ⊔ T) := fun y hy =>
    ⟨hy.2, Subgroup.mem_sup_left hy.1⟩
  rcases htypes with ⟨m, hm⟩ | ⟨m, hsz⟩ | eJ | ⟨q, hq, hq3, hpsl⟩
  ·
    obtain ⟨n, hnN, hnL, hnL', hPK, h3⟩ := hstruct (hF.psl2EvenOrder m ↥L hm)
    obtain ⟨y, hyPL, hy3, -⟩ := hy h3
    refine ⟨n, hnN, hnL, by rw [hnL']; exact hinf, hnL' ▸ hPK, h3, Or.inl ⟨m, ?_, hm⟩⟩
    exact hF.psl2EvenBorel Γ L _ _ m y hyp hm hUB inf_le_left hU hB23 (hyB y hyPL) hy3
  ·
    exfalso
    have h3 : ¬ 3 ∣ Nat.card L := hF.szOrder m ↥L hsz
    have hcardL' : Nat.card L' = Nat.card L :=
      (Nat.card_congr (A38.conjEquiv t L).toEquiv).symm
    have hsz' : SuzukiModel ↥L' 2 m :=
      CFSG.SectionRank.suzukiModel_of_mulEquiv (A38.conjEquiv t L).symm hsz
    have hZ := inf_centralizer_eq_bot h36 hLc hL h3
    have hZ' := inf_centralizer_eq_bot h36 hL'c (A38.isComponent_conj hL) (hcardL' ▸ h3)
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
    have : (Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ)).Normal :=
      Subgroup.normal_centralizer
    have hnC : ∀ K : Subgroup Γ,
        K ≤ Subgroup.normalizer (Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ) : Set Γ) :=
      fun K => by
        rw [Subgroup.normalizer_eq_top]
        exact le_top
    rcases hirr _ inf_le_left (hNinv (hnC N)) with hW | hW
    · apply hnotcen
      intro n hnN hnL a ha
      have hnL'' := hNL' hnL
      have haL := hPNL ha
      have hc : ⁅n, a⁆ ∈ P := by
        rw [commutatorElement_def]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNP hnN) a).mp ha) (P.inv_mem ha)
      have hc3 : ⁅n, a⁆ ^ 3 = 1 := hexp _ hc
      have hcL := mem_centralizer_of_pow_three_eq_one hZ h3
        ((hF.szOut m) Γ L hyp hsz n hnL a haL) hc3
      have hcL' := mem_centralizer_of_pow_three_eq_one hZ' (hcardL' ▸ h3)
        ((hF.szOut m) Γ L' hyp hsz' n hnL'' a (hNL' haL)) hc3
      have hcK : ⁅n, a⁆ ∈ Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ) := by
        rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hcL
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hcL'
      have h0 : ⁅n, a⁆ ∈ P ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ) := ⟨hc, hcK⟩
      rw [hW, Subgroup.mem_bot, commutatorElement_def] at h0
      calc n * a * n⁻¹ = n * a * n⁻¹ * a⁻¹ * a := by group
        _ = a := by rw [h0, one_mul]
    · apply hLP
      calc P = P ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ) := hW.symm
        _ ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup Γ) : Set Γ) := inf_le_right
        _ ≤ Subgroup.centralizer (L : Set Γ) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)
  ·
    exfalso
    obtain ⟨n₀, hn₀N, hn₀L, hn₀L', -, h3⟩ := hstruct (hF.j1Order ↥L eJ)
    obtain ⟨y, hyPL, hy3, hyz⟩ := hy h3
    have hcy : ∀ n ∈ N, n ∈ Subgroup.normalizer (L : Set Γ) → n * y * n⁻¹ = y := by
      intro n hnN hnL
      have hnU : n ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Γ) : Set Γ) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hNT hnN), hnL⟩
      have hny : n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Γ) : Set Γ) := by
        rw [hyz]
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hNP hnN, hnL⟩
      exact hF.j1Local Γ L _ _ y n hyp eJ hUB inf_le_left hU hB23 (hyB y hyPL) hy3 hnL
        hnU hny
    apply hnotcen
    intro n hnN hnL
    have hm : n₀⁻¹ * (n * n₀) ∈ Subgroup.normalizer (L : Set Γ) := by
      refine hidx n₀ (n * n₀) hn₀L fun h => hn₀L ?_
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hnL) h
      rwa [inv_mul_cancel_left] at this
    have hmN : n₀⁻¹ * (n * n₀) ∈ N := N.mul_mem (N.inv_mem hn₀N) (N.mul_mem hnN hn₀N)
    have h1 := hcy _ hmN hm
    have hcy' : n * (n₀ * y * n₀⁻¹) * n⁻¹ = n₀ * y * n₀⁻¹ := by
      calc n * (n₀ * y * n₀⁻¹) * n⁻¹ =
          n₀ * ((n₀⁻¹ * (n * n₀)) * y * (n₀⁻¹ * (n * n₀))⁻¹) * n₀⁻¹ := by group
        _ = n₀ * y * n₀⁻¹ := by rw [h1]
    have hy'P : n₀ * y * n₀⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hNP hn₀N) y).mp hyPL.1
    have hy'L' : n₀ * y * n₀⁻¹ ∈ L' := by
      rw [← hn₀L']
      exact ⟨y, hyPL.2, rfl⟩
    have hPgen : P = Subgroup.zpowers y ⊔ Subgroup.zpowers (n₀ * y * n₀⁻¹) := by
      symm
      by_contra hne
      have hle : Subgroup.zpowers y ⊔ Subgroup.zpowers (n₀ * y * n₀⁻¹) ≤ P :=
        sup_le (Subgroup.zpowers_le.mpr hyPL.1) (Subgroup.zpowers_le.mpr hy'P)
      have hne1 : Subgroup.zpowers y ⊔ Subgroup.zpowers (n₀ * y * n₀⁻¹) ≠ ⊥ := by
        intro h
        have : y ∈ (⊥ : Subgroup Γ) := h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
        rw [Subgroup.mem_bot] at this
        rw [this, orderOf_one] at hy3
        omega
      have hc3 := card_eq_three_of_lt hP9 hle hne1 hne
      have heq : Subgroup.zpowers y = Subgroup.zpowers y ⊔ Subgroup.zpowers (n₀ * y * n₀⁻¹) :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc3, Nat.card_zpowers, hy3])
      have hmem : n₀ * y * n₀⁻¹ ∈ L ⊓ L' := by
        refine ⟨?_, hy'L'⟩
        have : n₀ * y * n₀⁻¹ ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_sup_right
          (Subgroup.mem_zpowers _)
        exact (Subgroup.zpowers_le.mpr hyPL.2) this
      rw [hinf, Subgroup.mem_bot] at hmem
      have : y = 1 := by
        calc y = n₀⁻¹ * (n₀ * y * n₀⁻¹) * n₀ := by group
          _ = 1 := by rw [hmem]; group
      rw [this, orderOf_one] at hy3
      omega
    have hPC : P ≤ Subgroup.centralizer ({n} : Set Γ) := by
      rw [hPgen]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hcy n hnN hnL
        calc y * n = n * y * n⁻¹ * n := by rw [this]
          _ = n * y := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc n₀ * y * n₀⁻¹ * n = n * (n₀ * y * n₀⁻¹) * n⁻¹ * n := by rw [hcy']
          _ = n * (n₀ * y * n₀⁻¹) := by group
    intro a ha
    have := (Subgroup.mem_centralizer_singleton_iff.mp (hPC ha))
    calc n * a * n⁻¹ = a * n * n⁻¹ := by rw [this]
      _ = a := by group
  ·
    obtain ⟨n, hnN, hnL, hnL', hPK, h3⟩ :=
      hstruct (hF.psl2OddOrder q 1 hq (by omega) (Or.inl rfl) ↥L hpsl)
    exact ⟨n, hnN, hnL, by rw [hnL']; exact hinf, hnL' ▸ hPK, h3,
      Or.inr ⟨q, hq, by omega, hpsl⟩⟩

end CFSG.Quasithin.P134
