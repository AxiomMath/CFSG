module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_exists_noncyclic_stab {T : Type} [CommGroup T] [Finite T] {p : ℕ} (hp : p.Prime)
    {E : Type} [Group E] [Finite E] (ψ : E →* MulAut T) (hE : ∀ x : E, x ^ p = 1)
    (hEc : p ^ 3 ≤ Nat.card E) {Y : Subgroup T} (hY : Nat.card Y < p ^ 2)
    (hEY : ∀ x : E, Y.map (ψ x).toMonoidHom = Y) {n : T} (hn : n ∈ Y) :
    ∃ P : Subgroup E, ¬ IsCyclic ↥P ∧ ∀ x ∈ P, ψ x n = n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction E T := MulAction.compHom T ψ
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact hE g⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  set S : Subgroup E := MulAction.stabilizer E n with hS
  have hidx : S.index = (MulAction.orbit E n).ncard := MulAction.index_stabilizer E n
  have horb : MulAction.orbit E n ⊆ (Y : Set T) := by
    rintro _ ⟨f, rfl⟩
    have h1 : (ψ f) n ∈ Y.map (ψ f).toMonoidHom := ⟨n, hn, rfl⟩
    rw [hEY f] at h1
    exact h1
  have hle : S.index ≤ Nat.card Y := by
    rw [hidx]
    have h1 := Set.ncard_le_ncard horb (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq] at h1
  have hdvd : S.index ∣ p ^ k := hk ▸ Dvd.intro _ (Subgroup.index_mul_card S)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj2 : j < 2 := by
    have h1 : p ^ j < p ^ 2 := hj ▸ lt_of_le_of_lt hle hY
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  have hidxp : S.index ≤ p := by
    interval_cases j
    · rw [hj]
      exact hp.one_lt.le.trans' (by simp)
    · rw [hj]
      simp
  have hcardS : p ^ 2 ≤ Nat.card S := by
    have h1 : Nat.card S * S.index = Nat.card E := Subgroup.card_mul_index S
    have h2 : p * p ^ 2 ≤ p * Nat.card S := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hEc
        _ = Nat.card S * S.index := h1.symm
        _ ≤ Nat.card S * p := Nat.mul_le_mul_left _ hidxp
        _ = p * Nat.card S := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  refine ⟨S, ?_, fun x hx => hx⟩
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg1 : g ^ p = 1 := Subtype.ext (hE g)
  have hle2 := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hg1)
  have h3 : p < p ^ 2 := by
    calc p < p * p := lt_mul_of_one_lt_left hp.pos hp.one_lt
      _ = p ^ 2 := by ring
  omega

theorem s16t_a_insp_of_orbit (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p ∈ D.sig) {E : Subgroup G} (hEM : E ≤ D.M) (hEel : IsElemAbelian p E)
    (hEc : p ^ 3 ≤ Nat.card E) {Y : Subgroup (Vtil ⊥ V h.isElemAbelian)}
    (hY : Nat.card Y < p ^ 2)
    (hEY : ∀ b ∈ barSub ⊥ V h.isElemAbelian E, Y.map b.toMonoidHom = Y)
    {n : Vtil ⊥ V h.isElemAbelian} (hnY : n ∈ Y) (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T))) :
    Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  have hpf := h.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hEst : E ≤ stabTil ⊥ V := hEM.trans hMst
  have hpp : p.Prime := (D.sig_prime p hp).1
  let ψ : ↥E →* MulAut (Vtil ⊥ V hV) := (actTil ⊥ V hV).comp (Subgroup.inclusion hEst)
  have hψ : ∀ x : ↥E, ψ x ∈ barSub ⊥ V hV E := fun x =>
    actTil_mem_barSub ⊥ V hV x.2 (hEst x.2)
  obtain ⟨P, hPc, hPfix⟩ := s16t_a_exists_noncyclic_stab hpp ψ
    (fun x => Subtype.ext (hEel.2 x x.2)) hEc hY (fun x => hEY _ (hψ x)) hnY
  have hXE : P.map E.subtype ≤ E := Subgroup.map_subtype_le P
  refine s16t_a_insp_of_stable_subgroup D h hp (Ut := Subgroup.zpowers n)
    (Subgroup.zpowers_eq_bot.not.2 hn1) (Subgroup.zpowers_le.2 hnfix)
    (X := P.map E.subtype) (hXE.trans hEM)
    (fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 x (hXE x.2))⟩)
    (fun hc => hPc ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective P E.subtype E.subtype_injective)).2 hc)) ?_
  intro xb hxb u hu
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub ⊥ V hV _ xb).1 hxb
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hgX
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hact : actTil ⊥ V hV g = ψ x := by
    have hg : g = ⟨(x : G), hEst x.2⟩ := Subtype.ext hxg.symm
    rw [hg]
    rfl
  rw [hact]
  have h3 : (ψ x) (n ^ i) = (ψ x) n ^ i := map_zpow (ψ x) n i
  rw [h3, hPfix x hx]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers n) i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
