module

public import CFSG.Quasithin.Vol2.Ch7Sec77A23Stmts
public import CFSG.Quasithin.H13.KGFact68CSLin
public import CFSG.Sporadic.J1
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
public import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Blueprint

section Rank

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem isPGroup_of_isElemAbelian {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) :
    IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem card_le_of_isElemAbelian_of_card {a m : ℕ} (hS : Nat.card S = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  have h1 : 2 ^ k ∣ 2 ^ a * m := by
    rw [← hk, ← hS]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have h2 : 2 ^ k ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right h1
  rw [hk]
  exact Nat.le_of_dvd (by positivity) h2

theorem card_le_of_isElemAbelian_of_twoRank_le {r : ℕ} (h : CFSG.Assembly.twoRank S ≤ r)
    {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  have hk' : k ≤ CFSG.Assembly.twoRank S := by
    refine le_csSup ⟨Nat.card S, ?_⟩ ⟨E, le_top, hE, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card S := Subgroup.card_le_card_group B
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (hk'.trans h)

end Rank

section Small

variable {S : Type} [Group S] [Finite S]

theorem card_le_eight_of_alt {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 7) (e : S ≃* alternatingGroup (Fin n))
    {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  have hcard : Nat.card S = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  obtain ⟨h5, h7⟩ := hn
  interval_cases n
  · have hA : Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 15 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := card_le_of_isElemAbelian_of_card (hcard.trans hA) (by decide) hE
    omega
  · have hA : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    exact card_le_of_isElemAbelian_of_card (hcard.trans hA) (by decide) hE
  · have hA : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    exact card_le_of_isElemAbelian_of_card (hcard.trans hA) (by decide) hE

theorem card_le_eight_of_j1
    (e : S ≃* NativeSporadic.Carrier .J1) {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 8 := by
  have hcard : Nat.card S = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  exact card_le_of_isElemAbelian_of_card (a := 3) (m := 21945) (by rw [hcard]; norm_num)
    (by decide) hE

end Small

section Transport

variable {S T : Type} [Group S] [Group T]

theorem isElemAbelian_map (f : S →* T) {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

end Transport

section OddLie

open CFSG.Assembly.LowTwoRank

variable {S : Type} [Group S] [Finite S]

theorem card_le_four_of_psl2_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : StatedClassicalModel S .PSL 2 p f) {E : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ := CFSG.QuasithinUnique.K1.psl2_model_data hp2 h
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, by rw [Nat.card_eq_fintype_card, hcard]⟩
  have hD := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hK
  obtain ⟨T, hET⟩ := IsPGroup.exists_le_sylow (isPGroup_of_isElemAbelian hE)
  obtain ⟨m, hm, ⟨eT⟩⟩ := hD (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let eT' : ↥(T : Subgroup S) ≃* DihedralGroup (2 ^ m) :=
    ((T : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective).trans eT
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact CFSG.QuasithinUnique.card_le_four_of_dihedral T.isPGroup' h2m eT' hET
    (fun x hx => hE.2 x hx)

theorem twoRank_proj_le_two_of_det {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.Assembly.twoRank (StatedProj H) ≤ 2 := by
  classical
  let N : Subgroup ↥H := (StatedScalars (Fin 3) K).subgroupOf H
  have hN : ¬ 2 ∣ Nat.card N := by
    intro h2
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 g.2 : ((g : ↥H) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K)
      have hdg := hdet (g : ↥H) (g : ↥H).2
      rw [← hc] at hdg
      have hc3 : c ^ 3 = 1 := by
        apply Units.ext
        have : (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)).det = (c : K) ^ 3 := by
          simp
        rw [this] at hdg
        simpa using hdg
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
      show (((g : ↥H) : GL (Fin 3) K)) ^ 3 = 1
      rw [← hc, ← map_pow, hc3, map_one]
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    omega
  unfold CFSG.Assembly.twoRank
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd Nat.prime_two N
    hN]
  exact CFSG.RankThree.SubgroupLists.twoRank_le_two_of_det_eq_one hodd hdet

theorem det_eq_one_of_mem_closure {K : Type} [Field K] {X : Set (GL (Fin 3) K)}
    (hX : ∀ A ∈ X, (A : Matrix (Fin 3) (Fin 3) K).det = 1) {g : GL (Fin 3) K}
    (hg : g ∈ Subgroup.closure X) : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h1 : g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_ hg
    intro A hA
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hX A hA
  have h2 := congrArg Units.val (MonoidHom.mem_ker.1 h1)
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2

omit [Finite S] in
theorem card_le_four_of_psl3_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSL 3 p 1) {E : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hcard, pow_one]; exact hp.odd_of_ne_two hp2
  have h1 := card_le_of_isElemAbelian_of_twoRank_le
    (twoRank_proj_le_two_of_det hodd fun g hg => det_eq_one_of_mem_closure (fun A hA => hA) hg)
    (isElemAbelian_map e.toMonoidHom hE)
  calc Nat.card E = Nat.card ↥(E.map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ 2 ^ 2 := h1
    _ = 4 := by norm_num

omit [Finite S] in
theorem card_le_four_of_psu3_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSU 3 p 1) {E : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by
    rw [hcard, pow_one]
    exact (hp.odd_of_ne_two hp2).pow
  have h1 := card_le_of_isElemAbelian_of_twoRank_le
    (twoRank_proj_le_two_of_det hodd fun g hg => det_eq_one_of_mem_closure (fun A hA => hA.1) hg)
    (isElemAbelian_map e.toMonoidHom hE)
  calc Nat.card E = Nat.card ↥(E.map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ 2 ^ 2 := h1
    _ = 4 := by norm_num

end OddLie

section L32

open CFSG.Assembly.LowTwoRank

variable {S : Type} [Group S] [Finite S]

theorem card_le_eight_of_psl3_two (h : StatedClassicalModel S .PSL 3 2 1) {E : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hZ := center_sl_eq_bot_of_card_two (n := 3) hK
  let e' : S ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hS : Nat.card S = 2 ^ 3 * 21 := by
    rw [Nat.card_congr e'.toEquiv, Matrix.card_SL_field, hq]
    norm_num [Fin.prod_univ_succ]
  exact card_le_of_isElemAbelian_of_card hS (by decide) hE

end L32

theorem a23SmallTwoRankFact_holds :
    CFSG.Quasithin.H13.A23SmallTwoRankFact := by
  intro S _ _ hS E hE
  rcases hS with ⟨n, h5, h7, he⟩ | ⟨p, hp, hp2, hS⟩ | h | he
  · obtain ⟨e⟩ := he
    exact card_le_eight_of_alt ⟨h5, h7⟩ e hE
  · rcases hS with ⟨f, hf, h⟩ | h | h
    · have hf1 : 1 ≤ f := by omega
      exact (card_le_four_of_psl2_odd hp hp2 hf1 h hE).trans (by norm_num)
    · exact (card_le_four_of_psl3_odd hp hp2 h hE).trans (by norm_num)
    · exact (card_le_four_of_psu3_odd hp hp2 h hE).trans (by norm_num)
  · exact card_le_eight_of_psl3_two h hE
  · obtain ⟨e⟩ := he
    exact card_le_eight_of_j1 e hE

end CFSG.Quasithin.H13.KG68
