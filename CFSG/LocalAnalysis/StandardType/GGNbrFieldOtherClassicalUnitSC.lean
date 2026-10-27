module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU UCoord
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

theorem UCoord.pow_le_card_sumZero (m p : ℕ) [NeZero p] :
    p ^ m ≤ Nat.card ↥(sumZero (m + 1) p) := by
  let G : (Fin m → ZMod p) → ↥(sumZero (m + 1) p) := fun v =>
    ⟨fun k => Multiplicative.ofAdd ((Fin.cons (-∑ i, v i) v : Fin (m + 1) → ZMod p) k), by
      show ∑ k, (Fin.cons (-∑ i, v i) v : Fin (m + 1) → ZMod p) k = 0
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      exact neg_add_cancel _⟩
  have hG : Function.Injective G := by
    intro v w hvw
    funext i
    have h1 := congrFun (congrArg Subtype.val hvw) i.succ
    simp only [G, Fin.cons_succ] at h1
    exact Multiplicative.ofAdd.injective h1
  calc p ^ m = Nat.card (Fin m → ZMod p) := by rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    _ ≤ Nat.card ↥(sumZero (m + 1) p) := Nat.card_le_card_of_injective G hG

theorem pow_le_card_of_selfCent_unitarySC {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hE : IsElemAbelian p E)
    (hscE : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    p ^ (d - 1) ≤ Nat.card E := by
  classical
  have hd : d ≠ 0 := by
    rintro rfl
    exact hpd (dvd_zero p)
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnp : ∀ z ∈ (projU n (m + 1) K).ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hAmap, -, hA, -⟩ :=
    TableBUE.exists_lift_of_noTorsion (projU n (m + 1) K) projU_surjective hp hnp hE
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA
  obtain ⟨u, hord, huq⟩ : ∃ u : Kˣ, orderOf u = p ∧ u ^ (2 ^ n + 1) = 1 := by
    have := Fact.mk hp
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have := Nat.sq_sub_sq (2 ^ n) 1
        rwa [one_pow] at this
      rw [e]
      exact Dvd.dvd.mul_right hpq _
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpK
    refine ⟨u, hu, ?_⟩
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hDmem : ∀ f : ↥(sumZero (m + 1) p), diagHom (m + 1) (UModel.uvec hu f) ∈
      unitarySU 2 n K (m + 1) := fun f =>
    TableBUE.diagHom_mem_unitarySU h (fun k => UModel.uvec_pow_norm hu huq f k)
      (UModel.prod_uvec hu hord f)
  set Dsu : ↥(sumZero (m + 1) p) →* ↥(unitarySU 2 n K (m + 1)) :=
    ((diagHom (m + 1)).comp (UModel.uvec hu)).codRestrict _ hDmem
  have hDsu_coe : ∀ f, ((Dsu f : ↥(unitarySU 2 n K (m + 1))) : GL (Fin (m + 1)) K) =
      diagHom (m + 1) (UModel.uvec hu f) := fun f => rfl
  set τ : ↥(sumZero (m + 1) p) →* LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)) :=
    (frameMk h P hP).comp Dsu
  have hτapp : ∀ f, τ f = projU n (m + 1) K ((TableBUE.conjSU h P hP).symm (Dsu f)) :=
    fun f => rfl
  have hEA : ∀ e ∈ E, ∃ y ∈ A, projU n (m + 1) K y = e := by
    intro e he
    rw [← hAmap] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hcommA : ∀ f, ∀ y ∈ A, τ f * projU n (m + 1) K y = projU n (m + 1) K y * τ f := by
    intro f y hy
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hc : (TableBUE.conjSU h P hP).symm (Dsu f) * y =
        y * (TableBUE.conjSU h P hP).symm (Dsu f) := by
      apply (TableBUE.conjSU h P hP).injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hσ,
        hDsu_coe, ← map_mul, ← map_mul, mul_comm]
    rw [hτapp, ← map_mul, hc, map_mul]
  have hτE : ∀ f, τ f ∈ E := by
    intro f
    refine hscE (τ f) (fun e he => ?_) (by rw [← map_pow, pow_p_eq_one, map_one])
    obtain ⟨y, hy, rfl⟩ := hEA e he
    exact hcommA f y hy
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    rw [hτapp] at hf
    have h1 := hnp _ (MonoidHom.mem_ker.mpr hf)
      (by rw [← map_pow, ← map_pow, pow_p_eq_one, map_one, map_one])
    have h2 : Dsu f = 1 := by
      have := congrArg (TableBUE.conjSU h P hP) h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h3 : UModel.uvec hu f = 1 := by
      apply diagHom_injective (m + 1)
      rw [map_one, ← hDsu_coe, h2, Subgroup.coe_one]
    apply UModel.uvec_injective hu hord
    rw [h3, map_one]
  calc p ^ (m + 1 - 1) = p ^ m := by rw [Nat.add_sub_cancel]
    _ ≤ Nat.card ↥(sumZero (m + 1) p) := UCoord.pow_le_card_sumZero m p
    _ ≤ Nat.card E := Nat.card_le_card_of_injective (fun f => (⟨τ f, hτE f⟩ : E))
        fun f g hfg => hτinj (congrArg Subtype.val hfg)

theorem ggTorusSCRank_unitary
    {K : Type} [Field K] [Finite K] {d j p : ℕ} (hd : 3 ≤ d)
    (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (hp : p.Prime) (hpq : p ∣ 2 ^ j + 1)
    (hpd : ¬ p ∣ d) :
    GGTorusSCRank p (d - 1) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ j))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hsc
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hj hpq
  have hdq : (d, 2 ^ j) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hd3, h2⟩ := h
    have h3 : p ∣ 3 := by simpa [h2] using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    apply hpd
    simp [hd3, hp3]
  obtain ⟨Λ, -, -, -, -, hEab, hcardE, hscE⟩ := TwE6TB.exists_innerModel hp
    (TableBUE.center_proj_eq_bot hK hd hdq)
    (InndiagSU.ggOutdiagPrime_unitary hK hj hd hdq hp hpq hpd)
    (StdSubRestU.ggCenterPrime_unitary hK hj hd hdq hp hp2 hpd) ψ hψ hker hperf hA hAI hsc
  rw [← hcardE]
  exact pow_le_card_of_selfCent_unitarySC hK hj hp hpq hpd hEab hscE

theorem recipeUnitary_torusSCRank
    {d n p k : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : ¬ p ∣ d) (hk : k + 1 = d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusSCRank p k R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have h := ggTorusSCRank_unitary hd hn hK hp hpq hpd
  rwa [show d - 1 = k by omega] at h

theorem largeEvenLabelAll_torusSCRank_unitary
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryCoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusSCRank p (if lab.tag = .twA then lab.rank else 3) R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl ⊢
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    rw [if_pos rfl]
    exact recipeUnitary_torusSCRank hp hpn hn (by omega) hpl rfl hQ
  · dsimp only at h hl hpn ⊢
    subst h hl
    rw [ite_self]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (show ¬ (3 = 2) by decide), if_pos rfl] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_torusSCRank hp hpn hn (by norm_num) (fun h4 => hp2 ?_) rfl hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

end CFSG.StandardType

end
