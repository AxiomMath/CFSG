module

public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvD4Q
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvCore

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.LargeExtraspecial.S63 Subgroup

theorem d4_finite : Finite trialityGroup8 :=
  Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)

theorem d4_card_sylow {P : Subgroup trialityGroup8}
    (hP : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) : Nat.card P = 4096 := by
  have : Finite trialityGroup8 := d4_finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.card P = 2 ^ (Nat.card trialityGroup8).factorization 2 :=
    Sylow.card_eq_multiplicity (hP.toSylow hPi)
  rw [card_trialityGroup8] at h
  have e : (211341312 : ℕ) = 2 ^ 12 * 51597 := by norm_num
  rw [e, Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)] at h
  simpa using h

theorem d4_conj_z0
    {P : Subgroup trialityGroup8} (hP : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) {c : trialityGroup8}
    (hc : c ∈ centerOf P) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) : ∃ g, c = g * d4z * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite trialityGroup8 := d4_finite
  obtain ⟨g, hg | hg⟩ := exists_conj_of_orderOf_eq_two (orderOf_eq_prime hc2 hc1)
  · exact ⟨g, hg⟩
  · exfalso
    rw [ZPInv.mem_centerOf_iff] at hc
    have hPC : P ≤ centralizer ({c} : Set trialityGroup8) := fun x hx =>
      mem_centralizer_singleton_iff.2 (hc.2 x hx)
    have h1 : Nat.card P ≤ Nat.card (centralizer ({c} : Set trialityGroup8)) :=
      Subgroup.card_le_of_le hPC
    have hmap : ∀ x ∈ centralizer ({c} : Set trialityGroup8),
        g⁻¹ * x * g ∈ centralizer ({d4t} : Set trialityGroup8) := by
      intro x hx
      have hx' := mem_centralizer_singleton_iff.1 hx
      rw [hg] at hx'
      refine mem_centralizer_singleton_iff.2 ?_
      calc g⁻¹ * x * g * d4t = g⁻¹ * (x * (g * d4t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * d4t * g⁻¹) * x) * g := by rw [hx']
        _ = d4t * (g⁻¹ * x * g) := by group
    have h2 : Nat.card (centralizer ({c} : Set trialityGroup8)) ≤
        Nat.card (centralizer ({d4t} : Set trialityGroup8)) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨g⁻¹ * (x : trialityGroup8) * g, hmap x x.2⟩) ?_
      intro x y hxy
      have := congrArg Subtype.val hxy
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    have h3 := card_centralizer_d4t_le
    have h4 := d4_card_sylow hP hPi
    omega

theorem d4_core
    {P : Subgroup trialityGroup8} (hP : IsPGroup 2 ↥P)
    (hPi : ¬ 2 ∣ P.index) (hz : d4z ∈ centerOf P) {d : trialityGroup8} (hd : d ∈ centerOf P)
    (hd1 : d ≠ 1) : d = d4z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite trialityGroup8 := d4_finite
  rw [ZPInv.mem_centerOf_iff] at hz hd
  have hPC : P ≤ centralizer ({d4z} : Set trialityGroup8) := fun x hx =>
    mem_centralizer_singleton_iff.2 (hz.2 x hx)
  have hQ2 : IsPGroup 2 ↥d4Q := IsPGroup.of_card (n := 9) (by rw [card_d4Q]; norm_num)
  have hQP : d4Q ≤ P :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 d4Q_le_centralizer
      centralizer_d4z_le_normalizer_d4Q hQ2).trans
      (pCoreOf_two_le_sylow _ (hP.toSylow hPi) hPC)
  have hdC : d ∈ centralizer ({d4z} : Set trialityGroup8) :=
    mem_centralizer_singleton_iff.2 (hd.2 _ hz.1).symm
  obtain ⟨q, hq, l, hl, hdeq⟩ := exists_of_mem_centralizer_d4z hdC
  have hl1 : l = 1 := d4L_faithful q hq l hl fun x hx => by
    rw [← hdeq]
    exact (hd.2 x (hQP hx)).symm
  rw [hl1, mul_one] at hdeq
  subst hdeq
  exact (d4Q_central_eq hq fun x hx => hd.2 x (hQP hx)).resolve_left hd1

theorem zpSylow_trialityGroup8 :
    ZPSylow trialityGroup8 := by
  intro P hP hPi c d hc hd hc2 hd2 hc1 hd1
  obtain ⟨g, rfl⟩ := d4_conj_z0 hP hPi hc hc2 hc1
  have hz : d4z ∈ centerOf (P.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (mem_centerOf_map_conj P g⁻¹ d4z).2 (by simpa using hc)
  have hd' : g⁻¹ * d * g ∈ centerOf (P.map (MulAut.conj g⁻¹).toMonoidHom) := by
    refine (mem_centerOf_map_conj P g⁻¹ _).2 ?_
    have e : g⁻¹⁻¹ * (g⁻¹ * d * g) * g⁻¹ = d := by group
    rw [e]
    exact hd
  have hP' : IsPGroup 2 ↥(P.map (MulAut.conj g⁻¹).toMonoidHom) := hP.map _
  have hPi' : ¬ 2 ∣ (P.map (MulAut.conj g⁻¹).toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective (MulAut.conj g⁻¹).bijective]
  have h := d4_core hP' hPi' hz hd' (fun h1 => hd1 (by
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group))
  calc g * d4z * g⁻¹ = g * (g⁻¹ * d * g) * g⁻¹ := by rw [h]
    _ = d := by group

theorem zpUniq_3d4
    {Q : Type} [Group Q] (h : CFSG.Blueprint.ChevalleyExceptionalModel Q .trialityD4 2 1) :
    ZPUniq Q := by
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 Q (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  refine ⟨?_, ZPSylow.of_mulEquiv e zpSylow_trialityGroup8⟩
  exact center_eq_bot_of_simple (CFSG.LieType.Simplicity.fam_3d4_simplicity Q 2 1 h).2
    (N := 211341312) (by rw [Nat.card_congr e.toEquiv]; exact card_trialityGroup8)
    (by norm_num) (by norm_num)

end CFSG.Quasithin.ZPInv
