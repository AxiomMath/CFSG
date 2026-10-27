module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXM
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

private theorem w16g_zpow_eq_one_or_self_of_sq_eq_one {G : Type*} [Group G] {t : G}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem w16g_conj_commutatorElement_eq_inv' {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) (e : G) : t * ⁅e, t⁆ * t⁻¹ = ⁅e, t⁆⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have key : (e * t * e⁻¹ * t) * (t * e * t * e⁻¹) = 1 := by
    calc (e * t * e⁻¹ * t) * (t * e * t * e⁻¹)
        = e * t * e⁻¹ * (t * t) * e * t * e⁻¹ := by group
      _ = e * t * e⁻¹ * e * t * e⁻¹ := by rw [htt, mul_one]
      _ = e * (t * t) * e⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  rw [commutatorElement_def, hti]
  calc t * (e * t * e⁻¹ * t) * t = t * e * t * e⁻¹ * (t * t) := by group
    _ = t * e * t * e⁻¹ := by rw [htt, mul_one]
    _ = (e * t * e⁻¹ * t)⁻¹ := (inv_eq_of_mul_eq_one_right key).symm

private theorem w16g_abelian_conj_eq_inv_of_commutator_eq_self {G : Type*} [Group G]
    {P : Subgroup G} {t : G} (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (ht2 : orderOf t = 2) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) :
    ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  let J : Subgroup G :=
    { carrier := {x | x ∈ P ∧ t * x * t⁻¹ = x⁻¹}
      one_mem' := ⟨P.one_mem, by rw [mul_one, inv_one, mul_inv_cancel]⟩
      mul_mem' := by
        rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        have hxy : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ :=
          hcomm x⁻¹ (P.inv_mem hxP) y⁻¹ (P.inv_mem hyP)
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx, hy]
          _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxy]
      inv_mem' := by
        rintro x ⟨hxP, hx⟩
        refine ⟨P.inv_mem hxP, ?_⟩
        calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [hx] }
  have hPleJ : P ≤ J := by
    rw [← hc]
    refine Subgroup.commutator_le.mpr ?_
    intro x hx s hs
    rcases Subgroup.mem_zpowers_iff.mp hs with ⟨k, rfl⟩
    rcases w16g_zpow_eq_one_or_self_of_sq_eq_one htt k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact J.one_mem
    · rw [hk]
      refine ⟨?_, w16g_conj_commutatorElement_eq_inv' ht2 x⟩
      rw [commutatorElement_def]
      simpa only [mul_assoc] using P.mul_mem hx (hn x⁻¹ (P.inv_mem hx))
  intro x hx
  exact (hPleJ hx).2

private theorem w16g_conj_mem_conjClosure (A Q : Subgroup (MulAut W)) {g : MulAut W}
    (hg : g ∈ A) {x : MulAut W} (hx : x ∈ conjClosure A Q) :
    g * x * g⁻¹ ∈ conjClosure A Q := by
  unfold conjClosure at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, ha, q, hq, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨g * a, A.mul_mem hg ha, q, hq, by group⟩
  | one => simpa using Subgroup.one_mem _
  | mul y z _ _ ihy ihz =>
      have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [h]; exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [h]; exact Subgroup.inv_mem _ ihy

private theorem w16g_mem_conjClosure (A Q : Subgroup (MulAut W)) {g : MulAut W} (hg : g ∈ A)
    {y : MulAut W} (hy : y ∈ Q) : g * y * g⁻¹ ∈ conjClosure A Q := by
  unfold conjClosure
  exact Subgroup.subset_closure ⟨g, hg, y, hy, rfl⟩

private theorem w16g_le_conjClosure (A Q : Subgroup (MulAut W)) : Q ≤ conjClosure A Q := by
  intro q hq
  exact w16g_mem_conjClosure A Q A.one_mem (by simpa using hq)

private theorem w16g_conjClosure_le {A Q O : Subgroup (MulAut W)} (hQO : Q ≤ O)
    (hOA : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) : conjClosure A Q ≤ O := by
  unfold conjClosure
  rw [Subgroup.closure_le]
  rintro x ⟨a, ha, q, hq, rfl⟩
  exact hOA a ha q (hQO hq)

private theorem w16g_omegaOne_le (p : ℕ) (P : Subgroup (MulAut W)) : omegaOne p P ≤ P := by
  rw [omegaOne, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact hx

private theorem w16g_isElemAbelian_omegaOne_of_commute {p : ℕ} {P : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : IsElemAbelian p (omegaOne p P) := by
  rw [omegaOne]
  refine IsElemAbelian.closure_of_commute (s := {x | x ∈ P ∧ x ^ p = 1}) ?_ ?_
  · intro a ha b hb
    exact hcomm a ha.1 b hb.1
  · intro a ha
    exact ha.2

private theorem w16g_isElemAbelian_conjClosure {p : ℕ} {A Q : Subgroup (MulAut W)}
    (hcomm : ∀ g ∈ A, ∀ y ∈ Q, ∀ g' ∈ A, ∀ y' ∈ Q,
      (g * y * g⁻¹) * (g' * y' * g'⁻¹) = (g' * y' * g'⁻¹) * (g * y * g⁻¹))
    (hexp : ∀ q ∈ Q, q ^ p = 1) : IsElemAbelian p (conjClosure A Q) := by
  rw [conjClosure]
  refine IsElemAbelian.closure_of_commute (s := {x | ∃ g ∈ A, ∃ y ∈ Q, x = g * y * g⁻¹})
    ?_ ?_
  · rintro x ⟨g, hg, y, hy, rfl⟩ z ⟨g', hg', y', hy', rfl⟩
    exact hcomm g hg y hy g' hg' y' hy'
  · rintro x ⟨g, hg, y, hy, rfl⟩
    rw [show g * y * g⁻¹ = MulAut.conj g y from (MulAut.conj_apply g y).symm]
    rw [← map_pow, hexp y hy, map_one]

private theorem w16g_conj_generators_commute_of_card_prime {p : ℕ} (hp : p.Prime)
    {O P A : Subgroup (MulAut W)} (hO : IsPGroup p O) (hPcard : Nat.card P = p)
    (hOA : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) (hPO : P ≤ O)
    (hOP : ∀ o ∈ O, ∀ x ∈ P, o * x * o⁻¹ ∈ P) :
    ∀ g ∈ A, ∀ y ∈ P, ∀ g' ∈ A, ∀ y' ∈ P,
      (g * y * g⁻¹) * (g' * y' * g'⁻¹) = (g' * y' * g'⁻¹) * (g * y * g⁻¹) := by
  have hcentP : O ≤ Subgroup.centralizer (P : Set (MulAut W)) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq hp hO hPcard
      (Subgroup.le_set_normalizer_iff.mpr hOP)
  intro g hg y hy g' hg' y' hy'
  have haO : g * y * g⁻¹ ∈ O := hOA g hg y (hPO hy)
  have hmem : g'⁻¹ * (g * y * g⁻¹) * g' ∈ O := hOA g'⁻¹ (A.inv_mem hg') _ haO
  have hconj : (g'⁻¹ * (g * y * g⁻¹) * g') * y' * (g'⁻¹ * (g * y * g⁻¹) * g')⁻¹ = y' := by
    have hc := Subgroup.mem_centralizer_iff.mp (hcentP hmem) y' hy'
    rw [← hc]; group
  have hfix : (g * y * g⁻¹) * (g' * y' * g'⁻¹) * (g * y * g⁻¹)⁻¹ = g' * y' * g'⁻¹ := by
    calc (g * y * g⁻¹) * (g' * y' * g'⁻¹) * (g * y * g⁻¹)⁻¹
        = g' * ((g'⁻¹ * (g * y * g⁻¹) * g') * y' *
            (g'⁻¹ * (g * y * g⁻¹) * g')⁻¹) * g'⁻¹ := by group
      _ = g' * y' * g'⁻¹ := by rw [hconj]
  calc (g * y * g⁻¹) * (g' * y' * g'⁻¹)
      = ((g * y * g⁻¹) * (g' * y' * g'⁻¹) * (g * y * g⁻¹)⁻¹) * (g * y * g⁻¹) := by group
    _ = (g' * y' * g'⁻¹) * (g * y * g⁻¹) := by rw [hfix]

theorem s13_abelian_branch (h : HAb A X Q t p) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  rcases h.hp with rfl | h7
  · by_cases hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1
    · rcases s13_three_shape h hH0 with ⟨h2, hQ3⟩ | ⟨h3, hQ3⟩ | ⟨h3, hQ9⟩
      · exact s13_three_case_one h hH0 hQ3 h2
      · by_cases hov : ∃ a ∈ A,
            (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard = 2
        · exact s13_three_case_two_tetracode h hH0 hQ3 h3 hov
        · have hsupp := (s13_three_case_two_supports h hH0 hQ3 h3).2
          have hno2 : ∀ a ∈ A,
              (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard ≠ 2 := by
            intro a ha hc
            exact hov ⟨a, ha, hc⟩
          exact s13_three_case_two_blocks h hH0 hQ3 h3 (hsupp hno2)
      · exact s13_three_case_three h hH0 hQ9 h3
    · push Not at hH0
      obtain ⟨y, hyX, hy1, hysupp⟩ := hH0
      obtain ⟨L, hLX, htL, hind, hsupp1, hcase⟩ := exists_of_singleton_supp h hyX hy1 hysupp
      have hcase3 : Nat.card ↥L = 3 ∧ (rk ↥(commSub ⊤ L) = 2 ∨
          rk ↥(commSub ⊤ L) = 4 ∨ rk ↥(commSub ⊤ L) = 6) := by
        rcases hcase with ⟨-, hcard, hrk⟩ | ⟨h37, -⟩
        · exact ⟨hcard, hrk⟩
        · exact absurd h37 (by norm_num)
      have hcycL : IsCyclic ↥L := by
        haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        exact isCyclic_of_prime_card (p := 3) hcase3.1
      have hconc : Conc4_133 A t L :=
        ⟨3, by norm_num, hLX.trans h.hXO, htL, hind,
          Or.inl ⟨⟨hcycL, hcase3.1⟩, hcase3.2⟩⟩
      obtain ⟨U, hUeq⟩ := Set.ncard_eq_one.mp hsupp1
      have hsupp_eq : s13Supp X L = {U} := hUeq
      have hUmem : U ∈ s13IsoComps X := by
        have h : U ∈ s13Supp X L := by rw [hsupp_eq]; exact Set.mem_singleton U
        exact h.1
      have hle_closure : L ≤ s13XSupp X (s13Supp X L) :=
        (le_s13XSupp_iff h.hW (p := 3) (by norm_num) (by norm_num) h.hXe hLX).mpr subset_rfl
      have hcard_le : Nat.card ↥(s13XSupp X (s13Supp X L)) ≤ 3 := by
        rw [hsupp_eq]
        exact card_s13XSupp_singleton_le h.hW (p := 3) (by norm_num) (by norm_num) h.hXe hUmem
      have hclosure : L = s13XSupp X (s13Supp X L) :=
        Subgroup.eq_of_le_of_card_ge hle_closure (by rw [hcase3.1]; exact hcard_le)
      exact ⟨L, hLX, hconc, hclosure⟩
  · subst h7
    exact s13_seven_branch h

theorem s13_HAb_three (h : Cfg133 A t 3)
    (hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
      x * y = y * x)
    (hX : ∀ a ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆),
      ∀ b ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆), a * b = b * a) :
    HAb A (conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆))
      (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆) t 3 := by
  classical
  let O : Subgroup (MulAut W) := pCoreOf 3 A
  let P : Subgroup (MulAut W) := ⁅O, Subgroup.zpowers t⁆
  let Q' : Subgroup (MulAut W) := omegaOne 3 P
  obtain ⟨hPO, hPp, hPne, hnP, hcP, hOn⟩ := s13_P_facts h
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htord : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  have hQleP : Q' ≤ P := w16g_omegaOne_le 3 P
  have hQe : IsElemAbelian 3 Q' := w16g_isElemAbelian_omegaOne_of_commute hab
  have hcommGen : ∀ g ∈ A, ∀ y ∈ Q', ∀ g' ∈ A, ∀ y' ∈ Q',
      (g * y * g⁻¹) * (g' * y' * g'⁻¹) = (g' * y' * g'⁻¹) * (g * y * g⁻¹) := by
    intro g hg y hy g' hg' y' hy'
    exact hX _ (w16g_mem_conjClosure A Q' hg hy) _ (w16g_mem_conjClosure A Q' hg' hy')
  have hXe : IsElemAbelian 3 (conjClosure A Q') :=
    w16g_isElemAbelian_conjClosure hcommGen hQe.2
  have hQ1 : Q' ≠ ⊥ := by
    intro hbot
    have hcne : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥ := by rw [hcP]; exact hPne
    obtain ⟨x, hxP, hxord, -⟩ :=
      exists_inverted_orderOf_eq_prime htt (p := 3) (by norm_num) hPp hnP hcne
    have hxQ : x ∈ Q' := by
      rw [show Q' = omegaOne 3 P from rfl, omegaOne]
      exact Subgroup.subset_closure ⟨hxP, by rw [← hxord]; exact pow_orderOf_eq_one x⟩
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hxord
      exact (by norm_num : (1 : ℕ) ≠ 3) hxord
    exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxQ))
  have hQinv : ∀ q ∈ Q', t * q * t⁻¹ = q⁻¹ :=
    fun q hq => w16g_abelian_conj_eq_inv_of_commutator_eq_self hab htord hnP hcP q (hQleP hq)
  exact ⟨h.hW, Or.inl rfl, h.htA, h.ht2, h.ht1, h.hrk, hXe,
    fun g hg x hx => w16g_conj_mem_conjClosure A Q' hg hx,
    w16g_conjClosure_le (hQleP.trans hPO) (s13_pCore_facts A 3).1,
    w16g_le_conjClosure A Q', hQ1, hQinv, rfl, fun hp => absurd hp (by norm_num)⟩

theorem s13_HAb_seven (h : Cfg133 A t 7) :
    HAb A (conjClosure A ⁅pCoreOf 7 A, Subgroup.zpowers t⁆) ⁅pCoreOf 7 A, Subgroup.zpowers t⁆
      t 7 := by
  classical
  let O : Subgroup (MulAut W) := pCoreOf 7 A
  let P : Subgroup (MulAut W) := ⁅O, Subgroup.zpowers t⁆
  obtain ⟨hPO, hPp, hPne, hnP, hcP, hOn⟩ := s13_P_facts h
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have htord : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  have hcardP : Nat.card ↥P = 7 :=
    (w4Lem13_1_holds W hW2 t htord h.hrk 7 P Nat.prime_seven hPp hPne hnP hcP).2
      (Or.inl (by norm_num))
  have hO7 : IsPGroup 7 O := (s13_pCore_facts A 7).2.2
  have hcommGen : ∀ g ∈ A, ∀ y ∈ P, ∀ g' ∈ A, ∀ y' ∈ P,
      (g * y * g⁻¹) * (g' * y' * g'⁻¹) = (g' * y' * g'⁻¹) * (g * y * g⁻¹) :=
    w16g_conj_generators_commute_of_card_prime (p := 7) Nat.prime_seven hO7 hcardP
      (s13_pCore_facts A 7).1 hPO hOn
  have hexp : ∀ q ∈ P, q ^ 7 = 1 := by
    intro q hq
    have hdvd : orderOf q ∣ Nat.card ↥P := by
      rw [← Subgroup.orderOf_mk q hq]
      exact orderOf_dvd_natCard (⟨q, hq⟩ : ↥P)
    rw [hcardP] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hXe : IsElemAbelian 7 (conjClosure A P) :=
    w16g_isElemAbelian_conjClosure hcommGen hexp
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : IsCyclic ↥P := isCyclic_of_prime_card (p := 7) hcardP
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥P) ⟨y, hy⟩)
  have hQinv : ∀ q ∈ P, t * q * t⁻¹ = q⁻¹ :=
    w16g_abelian_conj_eq_inv_of_commutator_eq_self hPcomm htord hnP hcP
  exact ⟨h.hW, Or.inr rfl, h.htA, h.ht2, h.ht1, h.hrk, hXe,
    fun g hg x hx => w16g_conj_mem_conjClosure A P hg hx,
    w16g_conjClosure_le hPO (s13_pCore_facts A 7).1,
    w16g_le_conjClosure A P, hPne, hQinv, rfl, fun _ => hcardP⟩

end CFSG.LocalAnalysis.WeakClosure81
