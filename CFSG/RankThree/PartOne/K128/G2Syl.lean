module

public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.KF.ClsExcE
public import CFSG.RankThree.PartOne.KF.QuadExt
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.RankThree.PartOne.K128.TorusShape
public import CFSG.RankThree.PartOne.K128.FixCenter
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitPrime
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.K1214 CFSG.Open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne
open CFSG.Assembly (evenRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem pow3_sub_one (y : ℕ) (hy : 1 ≤ y) : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h : (w + 1) ^ 3 = w * ((w + 1) ^ 2 + (w + 1) + 1) + 1 := by ring
  omega

theorem sq_sub_one_eq (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, Q = w + 1 := ⟨Q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h : (w + 1) ^ 2 = w * (w + 1 + 1) + 1 := by ring
  omega

theorem not_dvd_sq_add_add_one {p y : ℕ} (hp5 : 5 ≤ p) (hy : 1 ≤ y) (h : p ∣ y - 1) :
    ¬ p ∣ y ^ 2 + y + 1 := by
  intro h2
  have h3 : y ^ 2 + y + 1 = (y - 1) * (y + 2) + 3 := by
    obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [h3] at h2
  have h4 : p ∣ 3 := (Nat.dvd_add_right (h.mul_right _)).1 h2
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem factorization_ordG2 {p Q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hd : p ∣ Q ^ 2 - 1) :
    (ordG2 Q).factorization p = 2 * (Q ^ 2 - 1).factorization p := by
  have hy : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : Q ^ 6 - 1 = (Q ^ 2 - 1) * ((Q ^ 2) ^ 2 + Q ^ 2 + 1) := by
    have := pow3_sub_one (Q ^ 2) hy
    rwa [← pow_mul] at this
  have hA : Q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Q ^ 2 := by nlinarith
    omega
  have hB : (Q ^ 2) ^ 2 + Q ^ 2 + 1 ≠ 0 := by positivity
  have hQ6 : Q ^ 6 ≠ 0 := by positivity
  have hpB : ¬ p ∣ (Q ^ 2) ^ 2 + Q ^ 2 + 1 := not_dvd_sq_add_add_one hp5 hy hd
  unfold ordG2
  rw [h6, Nat.factorization_mul (mul_ne_zero hQ6 (mul_ne_zero hA hB)) hA,
    Nat.factorization_mul hQ6 (mul_ne_zero hA hB), Nat.factorization_mul hA hB]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hpQ (hp.dvd_of_dvd_pow h)),
    Nat.factorization_eq_zero_of_not_dvd hpB]
  ring

theorem dvd_pred_or_succ_of_dvd_sq_sub_one {p Q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ : 1 ≤ Q)
    (hd : p ∣ Q ^ 2 - 1) :
    (p ∣ Q - 1 ∧ p ^ (Q ^ 2 - 1).factorization p ∣ Q - 1) ∨
      (p ∣ Q + 1 ∧ p ^ (Q ^ 2 - 1).factorization p ∣ Q + 1) := by
  have hfac := sq_sub_one_eq Q hQ
  have hpe : p ^ (Q ^ 2 - 1).factorization p ∣ (Q - 1) * (Q + 1) := by
    rw [← hfac]
    exact Nat.ordProj_dvd _ _
  have hnot : ¬ (p ∣ Q - 1 ∧ p ∣ Q + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : p ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub h2 h1
    have h4 : (Q + 1) - (Q - 1) = 2 := by omega
    rw [h4] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  rw [hfac] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    have hcop : Nat.Coprime (p ^ (Q ^ 2 - 1).factorization p) (Q + 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hnot ⟨h1, h⟩)
    exact hcop.dvd_of_dvd_mul_right hpe
  · right
    refine ⟨h1, ?_⟩
    have hcop : Nat.Coprime (p ^ (Q ^ 2 - 1).factorization p) (Q - 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hnot ⟨h, h1⟩)
    exact hcop.dvd_of_dvd_mul_left hpe


theorem factorization_sq_pow {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) :
    ((q ^ p) ^ 2 - 1).factorization p =
      (q ^ 2 - 1).factorization p + if p ∣ q ^ 2 - 1 then 1 else 0 := by
  have h := factorization_pow_sub_one hp hp2 (x := q ^ 2) (by nlinarith)
    (fun h => hpq (hp.dvd_of_dvd_pow h))
  have e : (q ^ p) ^ 2 = (q ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e]
  exact h

theorem dvd_sq_sub_one_of_dvd_pow {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (h : p ∣ (q ^ p) ^ 2 - 1) : p ∣ q ^ 2 - 1 := by
  by_contra hn
  have h1 := factorization_sq_pow hp hp2 hq hpq
  simp only [hn, ↓reduceIte] at h1
  rw [Nat.factorization_eq_zero_of_not_dvd hn] at h1
  have hq2 : 2 ≤ q ^ p := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hne : (q ^ p) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (q ^ p) ^ 2 := by nlinarith
    omega
  have h2 : 1 ≤ ((q ^ p) ^ 2 - 1).factorization p := (hp.dvd_iff_one_le_factorization hne).1 h
  omega

set_option linter.unusedSectionVars false

theorem torusGroup_le_adjointGroup' {τ : Tag} {K : Type} [Field K] :
    torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem exists_injective_G2_split (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) {e : ℕ} (he : p ^ e ∣ Nat.card K - 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* adjointGroup .G2 K,
      Function.Injective Ψ := by
  obtain ⟨-, ⟨φ⟩, -⟩ := even_G2_split_prime_centralizers_and_plane_normalizers K hp hp3 hpq
  obtain ⟨ι, hι⟩ := exists_injective_units (K := K) he
  let π₂ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* (Fin Tag.G2.rank → Kˣ) :=
    MonoidHom.pi fun i =>
      ι.comp (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative (ZMod (p ^ e))) i)
  have hπ₂ : Function.Injective π₂ := fun x y h => funext fun i => hι (congrFun h i)
  have hle : torusGroup .G2 K ≤ adjointGroup .G2 K := torusGroup_le_adjointGroup'
  refine ⟨(Subgroup.inclusion hle).comp (φ.toMonoidHom.comp π₂), ?_⟩
  exact (Subgroup.inclusion_injective hle).comp (φ.injective.comp hπ₂)

theorem exists_injective_G2_qplus (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) {e : ℕ} (he : p ^ e ∣ Nat.card K + 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* adjointGroup .G2 K,
      Function.Injective Ψ := by
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φ⟩, -⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp hp3 hpq (KFQ.Qext K) KFQ.finrank_qext
      (KFQ.frobQ K).toRingEquiv fun c => KFQ.frobQ_apply c
  have hm : Nat.card K + 1 ≠ 0 := Nat.succ_ne_zero _
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_injective_of_dvd hm hm he he
  let ψ : ModGL .G2 K →* ModGL .G2 (KFQ.Qext K) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (KFQ.Qext K)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K (KFQ.Qext K)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  have hle : torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g :=
    inf_le_right
  refine ⟨ε.symm.toMonoidHom.comp ((Subgroup.inclusion hle).comp (φ.symm.toMonoidHom.comp Ψ₀)), ?_⟩
  exact ε.symm.injective.comp ((Subgroup.inclusion_injective hle).comp
    (φ.symm.injective.comp hΨ₀))

theorem exists_equiv_adjoint_G2 {X : Type} [Group X] {q : ℕ}
    (h : UntwistedChevalleyModel X .G2 q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (X ≃* adjointGroup .G2 K) := by
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, hKf, hKfin, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)⟩⟩

theorem sylowShape_G2 (K : Type) [Field K] [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) (hd : p ∣ Nat.card K ^ 2 - 1) :
    SylowShape p 2 ((Nat.card K ^ 2 - 1).factorization p) (adjointGroup .G2 K) := by
  have hQ : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpQ : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have hord : (Nat.card (adjointGroup .G2 K)).factorization p =
      2 * (Nat.card K ^ 2 - 1).factorization p := by
    rw [card_adjointGroup_G2]
    exact factorization_ordG2 hp hp5 hQ hpQ hd
  rcases dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_split K hp (by omega) h1 h2
    exact sylowShape_of_injective hp Ψ hΨ hord
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_qplus K hp (by omega) h1 h2
    exact sylowShape_of_injective hp Ψ hΨ hord

theorem pRank_le_one_G2 (K : Type) [Field K] [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m)
    (hdvd : p ∣ Nat.card (adjointGroup .G2 K)) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) :
    CFSG.pRank p (adjointGroup .G2 K) ≤ 1 := by
  have hQ : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpQ : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hy : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [card_adjointGroup_G2] at hdvd
  have h6 : p ∣ Nat.card K ^ 6 - 1 := by
    unfold ordG2 at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpQ
      · exact h
    · exact absurd h hnd
  have hfac : Nat.card K ^ 6 - 1 =
      (Nat.card K ^ 2 - 1) * ((Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1) := by
    have := pow3_sub_one (Nat.card K ^ 2) hy
    rwa [← pow_mul] at this
  rw [hfac] at h6
  have hΦ : p ∣ (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 :=
    ((Nat.Prime.dvd_mul hp).1 h6).resolve_left hnd
  have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hΦfac : (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 =
      (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 - Nat.card K + 1) := by
    zify [hle]
    ring
  rw [hΦfac] at hΦ
  rcases (Nat.Prime.dvd_mul hp).1 hΦ with h | h
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := even_G2_cyclotomic_three_six_tori_and_prime_centralizers K 1
      (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hp (by omega) h
    exact pRank_le_one_of_cyclic_pSubgroups hp hcyc
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := even_G2_cyclotomic_three_six_tori_and_prime_centralizers K (-1)
      (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hle]; ring) hp
      (by omega) h
    exact pRank_le_one_of_cyclic_pSubgroups hp hcyc

theorem kf128SylTag_G2 : KF128SylTag .G2 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hZ hLR2 n f₀ hf₀ hM α hαp hinn hLRA hFix hF hrk
  have hadm := statedLieAdmissible_of_lieModel hM
  obtain ⟨hn0, -⟩ := hadm.2.2
  subst hn0
  have hp2 : p ≠ 2 := by omega
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  obtain ⟨K, hKf, hKfin, hK, ⟨eT⟩⟩ := exists_equiv_adjoint_G2 hch.2
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hm1 : 1 ≤ p * f₀ := hadm.2.1
  have hpT : p ∣ Nat.card (adjointGroup .G2 K) := by
    rw [← Nat.card_congr eT.toEquiv]
    exact dvd_card_of_pRank_pos hp (by omega)
  have hmodN : LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .G2 0 2 f₀ := by
    rcases hFix with h | ⟨ht, -⟩
    · exact h
    · exact absurd ht (by decide)
  have hch' := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodN
  obtain ⟨K', hK'f, hK'fin, hK', ⟨e'⟩⟩ := exists_equiv_adjoint_G2 hch'.2
  have : CharP K' 2 := charP_two_of_card_eq_two_pow hK'
  have eN : ↥(fixRes α) ≃* adjointGroup .G2 K' := (fixResEquivQuotient hF).trans e'
  have hKK : Nat.card K = Nat.card K' ^ p := by rw [hK, hK', ← pow_mul, mul_comm]
  have hq2 : 2 ≤ Nat.card K' := by
    rw [hK']
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hpq : ¬ p ∣ Nat.card K' := by
    rw [hK']
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hd : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hnd
    have h1 := pRank_le_one_G2 K hp hp5 hK hm1 hpT hnd
    have h2 := pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT
    omega
  have hd' : p ∣ Nat.card K' ^ 2 - 1 := by
    rw [hKK] at hd
    exact dvd_sq_sub_one_of_dvd_pow hp hp2 hq2 hpq hd
  have hlte := factorization_sq_pow hp hp2 hq2 hpq
  simp only [hd', ↓reduceIte] at hlte
  rw [← hKK] at hlte
  have hone : 1 ≤ (Nat.card K' ^ 2 - 1).factorization p := by
    have hne : Nat.card K' ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ Nat.card K' ^ 2 := by nlinarith
      omega
    exact (hp.dvd_iff_one_le_factorization hne).1 hd'
  refine ⟨(Nat.card K ^ 2 - 1).factorization p, by omega,
    SylowShape.of_mulEquiv eT (sylowShape_G2 K hp hp5 hK hm1 hd), ?_⟩
  have hsh := sylowShape_G2 K' hp hp5 hK' hf₀ hd'
  have he1 : (Nat.card K ^ 2 - 1).factorization p - 1 = (Nat.card K' ^ 2 - 1).factorization p := by
    omega
  rw [he1]
  exact SylowShape.of_mulEquiv eN hsh

end CFSG.RankThree.PartOne.K128
