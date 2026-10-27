module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup F11

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_twostep_mul_comm {T Z : Subgroup G} (hcent : ⁅T, Z⁆ = ⊥) {t z : G} (ht : t ∈ T)
    (hz : z ∈ Z) : t * z = z * t := by
  have h := Subgroup.commutator_mem_commutator ht hz
  rw [hcent, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem uc22p22u_twostep_pow_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T Z : Subgroup G}
    (hcomm : ⁅T, T⁆ ≤ Z) (hcent : ⁅T, Z⁆ = ⊥) (hpow : ∀ t ∈ T, t ^ p ∈ Z) :
    ∀ x ∈ T, ∀ y ∈ T, (x * y) ^ p = x ^ p * y ^ p := by
  intro x hx y hy
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  set c := (x * y)⁻¹ * (y * x) with hc
  have hyx : y * x = x * y * c := by rw [hc]; group
  have hcZ : c ∈ Z := by
    refine hcomm ?_
    have h := Subgroup.commutator_mem_commutator (T.inv_mem hy) (T.inv_mem hx)
    convert h using 1
    rw [hc, commutatorElement_def]; group
  have hcx : Commute c x := (uc22p22u_twostep_mul_comm hcent hx hcZ).symm
  have hcy : Commute c y := (uc22p22u_twostep_mul_comm hcent hy hcZ).symm
  have hcp : c ^ p = 1 := by
    have h := uc22p22u_pow_mul_of_commutator hyx hcy p
    rw [uc22p22u_twostep_mul_comm hcent hx (hpow y hy)] at h
    exact mul_eq_left.1 h.symm
  rw [uc22p22u_mul_pow_of_commutator hyx hcx hcy p]
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero hp3
  rw [hk, pow_mul, hcp, one_pow, mul_one]

theorem uc22p22u_exists_pow_subgroup {α : Type*} [Group α] [Finite α] [IsCyclic α] {p : ℕ} (hp : 0 < p) :
    ∃ N : Subgroup α, (∀ x, x ∈ N ↔ ∃ z : α, z ^ p = x) ∧ N.index ≤ p := by
  letI : CommGroup α := IsCyclic.commGroup
  refine ⟨(powMonoidHom p : α →* α).range, fun x => ?_, ?_⟩
  · simp [MonoidHom.mem_range]
  · rw [IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_le_right _ hp

theorem uc22p22u_twostep_card_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T Z : Subgroup G}
    (hT : IsPGroup p ↥T) (hZc : IsCyclic ↥Z) (hZT : Z ≤ T) (hcomm : ⁅T, T⁆ ≤ Z) (hcent : ⁅T, Z⁆ = ⊥)
    (hpow : ∀ t ∈ T, t ^ p ∈ Z) : Nat.card ↥T ≤ p * Nat.card ↥(Omega1p p T ⊔ Z) := by
  have _ := hT
  haveI := hZc
  have hmul := uc22p22u_twostep_pow_mul hp hp2 hcomm hcent hpow
  obtain ⟨N, hN, hNp⟩ := uc22p22u_exists_pow_subgroup (α := ↥Z) hp.pos
  let θ : ↥T →* ↥Z :=
    { toFun := fun t => ⟨(t : G) ^ p, hpow t t.2⟩
      map_one' := Subtype.ext (one_pow p)
      map_mul' := fun a b => Subtype.ext (hmul a a.2 b b.2) }
  let φ : ↥T →* ↥Z ⧸ N := (QuotientGroup.mk' N).comp θ
  have h1 : Nat.card ↥T = Nat.card φ.ker * Nat.card φ.range := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
  have h2 : Nat.card φ.range ≤ p :=
    (Subgroup.card_le_card_group _).trans (by rw [← Subgroup.index_eq_card]; exact hNp)
  have h3 : Nat.card φ.ker ≤ Nat.card ↥(Omega1p p T ⊔ Z) := by
    have hle : φ.ker.map T.subtype ≤ Omega1p p T ⊔ Z := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨z, hz⟩ := (hN _).1 ((QuotientGroup.eq_one_iff _).1 ht)
      have hz' : (z : G) ^ p = (t : G) ^ p := congrArg Subtype.val hz
      have hzT : (z : G)⁻¹ ∈ T := T.inv_mem (hZT z.2)
      have hs : (t : G) * (z : G)⁻¹ ∈ Omega1p p T := by
        refine Subgroup.subset_closure ⟨T.mul_mem t.2 hzT, ?_⟩
        rw [hmul _ t.2 _ hzT, inv_pow, hz', mul_inv_cancel]
      have h : (t : G) = (t : G) * (z : G)⁻¹ * z := by group
      show (t : G) ∈ Omega1p p T ⊔ Z
      rw [h]
      exact Subgroup.mul_mem_sup hs z.2
    rw [← Subgroup.card_map_of_injective T.subtype_injective]
    exact Subgroup.card_le_of_le hle
  calc Nat.card ↥T = Nat.card φ.ker * Nat.card φ.range := h1
    _ ≤ Nat.card ↥(Omega1p p T ⊔ Z) * p := Nat.mul_le_mul h3 h2
    _ = p * Nat.card ↥(Omega1p p T ⊔ Z) := mul_comm _ _

theorem uc22p22u_twostep_inf_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T Z : Subgroup G}
    (hT : IsPGroup p ↥T) (hZT : Z ≤ T) (hcomm : ⁅T, T⁆ ≤ Z) (hcent : ⁅T, Z⁆ = ⊥)
    (hpow : ∀ t ∈ T, t ^ p ∈ Z) (hne : Omega1p p T ⊔ Z ≠ T) : Omega1p p T ⊓ Z ≠ ⊥ := by
  have _ := hp2
  have _ := hcomm
  have _ := hcent
  haveI : Fact p.Prime := ⟨hp⟩
  intro hbot
  have hZne : Z ≠ ⊥ := by
    rintro rfl
    refine hne (le_antisymm (sup_le ((Subgroup.closure_le T).2 fun x hx => hx.1) hZT) fun t ht => ?_)
    have h := hpow t ht
    rw [Subgroup.mem_bot] at h
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨ht, h⟩)
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  obtain ⟨k, hk, hkcard⟩ := ((hT.to_le hZT).nontrivial_iff_card).1 inferInstance
  have hdvd : p ∣ Nat.card ↥Z := by
    rw [hkcard]
    exact dvd_pow_self p hk.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) p hdvd
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hx, h, orderOf_one])
  have hxp : (x : G) ^ p = 1 := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  have hmem : (x : G) ∈ Omega1p p T ⊓ Z := ⟨Subgroup.subset_closure ⟨hZT x.2, hxp⟩, x.2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext hmem)

theorem uc22p22u_twostep_bundle {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T Z : Subgroup G}
    (hT : IsPGroup p ↥T) (hZc : IsCyclic ↥Z) (hZT : Z ≤ T) (hcomm : ⁅T, T⁆ ≤ Z) (hcent : ⁅T, Z⁆ = ⊥)
    (hpow : ∀ t ∈ T, t ^ p ∈ Z) {n : ℕ} (hn : 1 < n) (hcard : Nat.card ↥T = p ^ n * Nat.card ↥Z) :
    (∀ x ∈ Omega1p p T, x ^ p = 1) ∧
      (IsMulCommutative (Omega1p p T) ∨
        (Nat.card ↥⁅Omega1p p T, Omega1p p T⁆ = p ∧
          ⁅Omega1p p T, Omega1p p T⁆ ≤ Omega1p p T ⊓ centralizer ((Omega1p p T : Subgroup G) : Set G))) ∧
      p ^ n ≤ Nat.card (Omega1p p T) ∧ n / 2 + 1 ≤ CFSG.Open.pRank p (Omega1p p T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hZc
  have hp1 : 1 < p := hp.one_lt
  have hclT : ⁅⁅T, T⁆, T⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono_left hcomm).trans (by rw [Subgroup.commutator_comm, hcent]))
  set Y := Omega1p p T
  have hYT : Y ≤ T := (Subgroup.closure_le T).2 fun x hx => hx.1
  have hexp : ∀ x ∈ Y, x ^ p = 1 := uc22p22u_omega1p_exponent hp hp2 hT hclT
  have hclY : ⁅⁅Y, Y⁆, Y⁆ = ⊥ := eq_bot_iff.2
    ((Subgroup.commutator_mono (Subgroup.commutator_mono hYT hYT) hYT).trans hclT.le)
  have hYYZ : ⁅Y, Y⁆ ≤ Z := (Subgroup.commutator_mono hYT hYT).trans hcomm
  have hYY : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.2 fun a ha b hb =>
    Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  have hcyc : IsCyclic ↥⁅Y, Y⁆ := by
    have : IsCyclic (⁅Y, Y⁆.subgroupOf Z) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe hYYZ).isCyclic.mp this
  have hdvd : Nat.card ↥⁅Y, Y⁆ ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hexp x (hYY x.2))
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Y Z fun y hy z hz =>
    uc22p22u_twostep_mul_comm hcent (hYT hy) hz).1
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hcardY : p ^ n ≤ Nat.card ↥Y := by
    by_cases hYZ : Y ⊔ Z = T
    · have h1 : Nat.card ↥(Y ⊔ Z) = p ^ n * Nat.card ↥Z := by rw [hYZ, hcard]
      have h2 : 0 < Nat.card ↥(Y ⊓ Z) := Nat.card_pos
      refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥Z) ?_ hZpos
      calc p ^ n * Nat.card ↥Z = Nat.card ↥(Y ⊔ Z) * 1 := by rw [h1, mul_one]
        _ ≤ Nat.card ↥(Y ⊔ Z) * Nat.card ↥(Y ⊓ Z) := Nat.mul_le_mul_left _ h2
        _ = Nat.card ↥Y * Nat.card ↥Z := hprod
    · have hinf := uc22p22u_twostep_inf_ne_bot hp hp2 hT hZT hcomm hcent hpow hYZ
      haveI : Nontrivial ↥(Y ⊓ Z) := (Subgroup.nontrivial_iff_ne_bot (Y ⊓ Z)).2 hinf
      have hYZT : Y ⊓ Z ≤ T := inf_le_left.trans hYT
      obtain ⟨k, hk, hkcard⟩ := ((hT.to_le hYZT).nontrivial_iff_card).1 inferInstance
      have hpinf : p ≤ Nat.card ↥(Y ⊓ Z) := by
        rw [hkcard]
        exact Nat.le_self_pow hk.ne' p
      have hle := uc22p22u_twostep_card_le hp hp2 hT hZc hZT hcomm hcent hpow
      refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥Z) ?_ hZpos
      calc p ^ n * Nat.card ↥Z = Nat.card ↥T := hcard.symm
        _ ≤ p * Nat.card ↥(Y ⊔ Z) := hle
        _ ≤ Nat.card ↥(Y ⊓ Z) * Nat.card ↥(Y ⊔ Z) := Nat.mul_le_mul_right _ hpinf
        _ = Nat.card ↥(Y ⊔ Z) * Nat.card ↥(Y ⊓ Z) := mul_comm _ _
        _ = Nat.card ↥Y * Nat.card ↥Z := hprod
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥Y = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : 1 < p ^ n := Nat.one_lt_pow (by omega) hp1
    omega
  have hrank : n / 2 + 1 ≤ CFSG.Open.pRank p Y := by
    have h := hcardY.trans (uc22p22u_card_le_pow_pRank hp hp2 hexp hclY (Nat.le_of_dvd hp.pos hdvd) hYne)
    have := (Nat.pow_le_pow_iff_right hp1).1 h
    omega
  refine ⟨hexp, ?_, hcardY, hrank⟩
  by_cases hab : IsMulCommutative ↥Y
  · exact Or.inl hab
  · refine Or.inr ⟨?_, le_inf hYY fun c hc => Subgroup.mem_centralizer_iff.2 fun y hy =>
      uc22p22u_twostep_mul_comm hcent (hYT hy) (hYYZ hc)⟩
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (Subgroup.commutator_self_eq_bot_iff.1 (Subgroup.eq_bot_of_card_eq _ h1)) hab
    · exact h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
