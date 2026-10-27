module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.RankThree.PartOne.KFU

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem localRank_le_one_of_small_centralizers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcent : ∀ a : G, orderOf a = p → ¬ 4 ∣ Nat.card (centralizer ({a} : Set G)))
    (hE : ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      Odd (Nat.card (centralizer (E : Set G)))) : localRank p G ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hlt
  have : Fact p.Prime := ⟨hp⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  let _ : MulDistribMulAction E U :=
    MulDistribMulAction.compHom U (U.normalizerMonoidHom.comp (Subgroup.inclusion hEU))
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hEcomm a a.2 b b.2) }
  have : Fact (IsPGroup p E) := ⟨hEel.isPGroup⟩
  have hsmul : ∀ (e : E) (u : U), ((e • u : U) : G) = (e : G) * u * (e : G)⁻¹ := fun e u => rfl
  have hncyc : ¬ IsCyclic E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEexp g g.2)
    have h1 : Nat.card E ≤ p := hord ▸ Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
    rw [hEc] at h1
    have := hp.two_le
    nlinarith
  have hUnt : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU0
  have hcop : Nat.Coprime p (Nat.card U) := by
    obtain ⟨n, -, hn⟩ := hU2.nontrivial_iff_card.mp hUnt
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := U) (A := E) p hcop hncyc
  obtain ⟨a, ha1, hFa⟩ : ∃ a : E, a ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers a)) U ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hbot : (⨆ (a : E) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) U) = ⊥ := by
      refine iSup₂_eq_bot.mpr fun a ha => hno a ha
    rw [hbot] at hgen
    exact bot_ne_top hgen
  obtain ⟨vF, hvF1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFa
  set v : U := (vF : U) with hvdef
  have hvF : v ∈ fixedPointSubgroup (↥(Subgroup.zpowers a)) U := vF.2
  have hv1 : v ≠ 1 := fun h => hvF1 (Subtype.ext h)
  have hvfix : ∀ z : Subgroup.zpowers a, ((z : E) • (v : U)) = v := by
    rw [FixedPoints.mem_subgroup] at hvF
    intro z
    exact hvF z
  have haord : orderOf (a : G) = p := by
    refine orderOf_eq_prime (hEexp a a.2) ?_
    intro h
    exact ha1 (Subtype.ext h)
  have hav : (a : G) * v * (a : G)⁻¹ = v := by
    have := congrArg Subtype.val (hvfix ⟨a, Subgroup.mem_zpowers a⟩)
    rwa [hsmul] at this
  set W : Subgroup G := U ⊓ centralizer ({(a : G)} : Set G) with hW
  have hvW : ((v : U) : G) ∈ W := by
    refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hav
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hv1' : ((v : U) : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hW2 : IsPGroup 2 W := hU2.to_inf_left
  have hW0 : W ≠ ⊥ := fun h => hv1' (Subgroup.mem_bot.mp (h ▸ hvW))
  have hWnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW0
  obtain ⟨n, hn, hWn⟩ := hW2.nontrivial_iff_card.mp hWnt
  have hn1 : n = 1 := by
    by_contra hne
    have h4 : 4 ∣ Nat.card W := by
      rw [hWn]
      have h22 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      simpa using h22
    exact hcent (a : G) haord (h4.trans (Subgroup.card_dvd_of_le
      (inf_le_right : W ≤ centralizer ({(a : G)} : Set G))))
  have hWcard : Nat.card W = 2 := by rw [hWn, hn1, pow_one]
  have hvord : orderOf ((v : U) : G) = 2 := by
    have hdvd : orderOf ((v : U) : G) ∣ 2 := hWcard ▸ Subgroup.orderOf_dvd_natCard W hvW
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv1'
    · exact h
  have hWz : W = Subgroup.zpowers ((v : U) : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvW) ?_).symm
    rw [hWcard, Nat.card_zpowers, hvord]
  have hvC : ((v : U) : G) ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heU : (e : G) * v * (e : G)⁻¹ ∈ U := ((Subgroup.mem_normalizer_iff.mp (hEU he)) _).mp v.2
    have heW : (e : G) * v * (e : G)⁻¹ ∈ W := by
      refine ⟨heU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hav' : (a : G) * v = v * a := by
        have := hav
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      have hea := hEcomm e he a a.2
      have hea' : e * (a : G) * e⁻¹ = a := by rw [hea, mul_assoc, mul_inv_cancel, mul_one]
      refine Eq.symm ?_
      calc (a : G) * (e * v * e⁻¹) = (e * a * e⁻¹) * (e * v * e⁻¹) := by rw [hea']
        _ = e * (a * v) * e⁻¹ := by group
        _ = e * (v * a) * e⁻¹ := by rw [hav']
        _ = (e * v * e⁻¹) * (e * a * e⁻¹) := by group
        _ = (e * v * e⁻¹) * a := by rw [hea']
    rw [hWz] at heW
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp heW
    have hsq : ((v : U) : G) ^ 2 = 1 := by rw [← hvord]; exact pow_orderOf_eq_one _
    have hconj1 : (e : G) * v * (e : G)⁻¹ ≠ 1 := by
      intro h
      apply hv1'
      have : (e : G) * v * (e : G)⁻¹ = 1 := h
      rw [mul_inv_eq_one] at this
      have := mul_eq_left.mp this
      exact this
    have hkv : (e : G) * v * (e : G)⁻¹ = ((v : U) : G) := by
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        apply hconj1
        rw [← hk, ← Int.emod_add_mul_ediv k 2, h0, zpow_add, zpow_mul]
        simp [hsq]
      · rw [← hk, ← Int.emod_add_mul_ediv k 2, h1, zpow_add, zpow_mul]
        simp [hsq]
    calc (e : G) * v = (e : G) * v * (e : G)⁻¹ * e := by group
      _ = v * e := by rw [hkv]
  have hodd := hE E hEel hEc
  have h2 : 2 ∣ Nat.card (centralizer (E : Set G)) := hvord ▸ Subgroup.orderOf_dvd_natCard _ hvC
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.RankThree.PartOne.KFU
