module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem exists_ne_one_centralizes {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal]
    (hOut : IsCyclic (Outer ↥N))
    (h3 : ∀ g : ↥N ⧸ Subgroup.center ↥N, g ^ 3 = 1 → g = 1)
    (P : Subgroup Y) (hP3 : ∀ p ∈ P, p ^ 3 = 1) (hPnc : ¬ IsCyclic ↥P) :
    ∃ x ∈ P, x ≠ 1 ∧ x ∈ Subgroup.centralizer (N : Set Y) := by
  let θ : ↥P →* Outer ↥N :=
    (QuotientGroup.mk' (inner ↥N)).comp ((MulAut.conjNormal (H := N)).comp P.subtype)
  have hker : θ.ker ≠ ⊥ := by
    intro hbot
    exact hPnc (isCyclic_of_injective θ ((MonoidHom.ker_eq_bot_iff θ).1 hbot))
  obtain ⟨⟨⟨p, hpP⟩, hpker⟩, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext (Subtype.ext h))
  have hin : MulAut.conjNormal (H := N) p ∈ inner ↥N := by
    have := (MonoidHom.mem_ker).1 hpker
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨n, hn⟩ := hin
  have hconj : ∀ m : ↥N, ((n : ↥N) : Y) * m * ((n : ↥N) : Y)⁻¹ = p * m * p⁻¹ := by
    intro m
    have h1 := congrArg (fun φ : MulAut ↥N => ((φ m : ↥N) : Y)) hn
    simpa using h1
  set c : Y := ((n : ↥N) : Y)⁻¹ * p with hc
  have hcC : c ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := hconj ⟨m, hm⟩
    simp only at h1
    have h2 : c * m = m * c := by
      rw [hc]
      calc ((n : ↥N) : Y)⁻¹ * p * m
          = ((n : ↥N) : Y)⁻¹ * (p * m * p⁻¹) * p := by group
        _ = ((n : ↥N) : Y)⁻¹ * (((n : ↥N) : Y) * m * ((n : ↥N) : Y)⁻¹) * p := by rw [h1]
        _ = m * (((n : ↥N) : Y)⁻¹ * p) := by group
    exact h2.symm
  have hpnc : p = ((n : ↥N) : Y) * c := by rw [hc]; group
  have hnc : Commute (((n : ↥N) : Y)) c :=
    Subgroup.mem_centralizer_iff.1 hcC ((n : ↥N) : Y) (n : ↥N).2
  have hp3 := hP3 p hpP
  have hn3 : ((n : ↥N) : Y) ^ 3 = (c ^ 3)⁻¹ := by
    have : p ^ 3 = ((n : ↥N) : Y) ^ 3 * c ^ 3 := by
      rw [hpnc]; exact hnc.mul_pow 3
    rw [hp3] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hn3Z : (n ^ 3 : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have h1 : ((n ^ 3 : ↥N) : Y) = (c ^ 3)⁻¹ := by simpa using hn3
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
    have hc3 : c ^ 3 ∈ Subgroup.centralizer (N : Set Y) := Subgroup.pow_mem _ hcC 3
    have hc3' : (c ^ 3)⁻¹ ∈ Subgroup.centralizer (N : Set Y) := Subgroup.inv_mem _ hc3
    exact (Subgroup.mem_centralizer_iff.1 hc3' (m : Y) m.2)
  have hnbar : (QuotientGroup.mk n : ↥N ⧸ Subgroup.center ↥N) = 1 := by
    apply h3
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn3Z
  have hnZ : n ∈ Subgroup.center ↥N := (QuotientGroup.eq_one_iff _).1 hnbar
  have hnC : ((n : ↥N) : Y) ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := congrArg (fun z : ↥N => (z : Y)) (Subgroup.mem_center_iff.1 hnZ ⟨m, hm⟩)
    simpa using h1
  exact ⟨p, hpP, hp1', by rw [hpnc]; exact Subgroup.mul_mem _ hnC hcC⟩

section OddNormal

variable {Y : Type*} [Group Y]

theorem exists_odd_normal_le [Finite Y]
    (hO2 : ∀ M : Subgroup Y, M.Normal → IsPGroup 2 M → M = ⊥)
    (E₀ : Subgroup Y) [hE₀ : E₀.Normal] (hsolv : Group.IsSolvable ↥E₀) (hne : E₀ ≠ ⊥) :
    ∃ D : Subgroup Y, D.Normal ∧ D ≤ E₀ ∧ D ≠ ⊥ ∧ Odd (Nat.card D) := by
  classical
  obtain ⟨m, hm⟩ := hsolv.solvable
  have hex : ∃ n, derivedSeries ↥E₀ n = ⊥ := ⟨m, hm⟩
  set k := Nat.find hex with hk
  have hk0 : k ≠ 0 := by
    intro h0
    have h1 : derivedSeries ↥E₀ 0 = ⊥ := by
      have := Nat.find_spec hex
      rwa [← hk, h0] at this
    rw [derivedSeries_zero] at h1
    apply hne
    have : Nat.card ↥E₀ = 1 := by
      rw [← Subgroup.card_top (G := ↥E₀), h1, Subgroup.card_bot]
    exact (Subgroup.card_eq_one).1 this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjne : derivedSeries ↥E₀ j ≠ ⊥ := Nat.find_min hex (by omega)
  have hjsucc : derivedSeries ↥E₀ (j + 1) = ⊥ := by
    have := Nat.find_spec hex
    rwa [← hk, hj] at this
  set D' : Subgroup ↥E₀ := derivedSeries ↥E₀ j with hD'
  set D : Subgroup Y := D'.map E₀.subtype with hD
  have hDE : D ≤ E₀ := Subgroup.map_subtype_le D'
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ⁅D', D'⁆ := Subgroup.commutator_mem_commutator ha hb
    have h2 : ⁅D', D'⁆ = ⊥ := by rw [← derivedSeries_succ]; exact hjsucc
    rw [h2, Subgroup.mem_bot] at h1
    have := (commutatorElement_eq_one_iff_mul_comm).1 h1
    exact congrArg Subtype.val this
  have hDnormal : D.Normal := by
    constructor
    intro d hd y
    obtain ⟨d', hd', rfl⟩ := hd
    have hchar : D'.Characteristic := inferInstance
    have h1 := (Subgroup.characteristic_iff_map_eq.1 hchar) (MulAut.conjNormal (H := E₀) y)
    have h2 : (MulAut.conjNormal (H := E₀) y) d' ∈ D' := by
      rw [← h1]; exact ⟨d', hd', rfl⟩
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conjNormal_apply]
  have hDne : D ≠ ⊥ := by
    intro hDbot
    apply hjne
    rw [eq_bot_iff]
    intro d hd
    have : (d : Y) ∈ D := ⟨d, hd, rfl⟩
    rw [hDbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  refine ⟨D, hDnormal, hDE, hDne, ?_⟩
  have hno : ∀ z ∈ D, z ^ 2 = 1 → z = 1 := by
    intro z hz hz2
    let Z : Subgroup Y :=
      { carrier := {z | z ∈ D ∧ z ^ 2 = 1}
        one_mem' := ⟨D.one_mem, one_pow 2⟩
        mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by
          rw [(Commute.mul_pow (hcomm a ha.1 b hb.1) 2) , ha.2, hb.2, one_mul]⟩
        inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    haveI : Z.Normal := ⟨fun a ha y => ⟨(hDnormal.conj_mem a ha.1 y), by
      rw [conj_pow, ha.2]; simp⟩⟩
    have hZ2 : IsPGroup 2 Z := by
      intro a
      refine ⟨1, Subtype.ext ?_⟩
      simpa using a.2.2
    have := hO2 Z inferInstance hZ2
    have hzZ : z ∈ Z := ⟨hz, hz2⟩
    rw [this, Subgroup.mem_bot] at hzZ
    exact hzZ
  by_contra hodd
  have h2 : 2 ∣ Nat.card D := by
    rcases Nat.even_or_odd (Nat.card D) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 h2
  have hz2 : (z : Y) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have := hno z z.2 hz2
  have hz1 : z = 1 := Subtype.ext this
  rw [hz1, orderOf_one] at hz
  omega

end OddNormal

end CFSG.Quasithin.H13.P31Sz
