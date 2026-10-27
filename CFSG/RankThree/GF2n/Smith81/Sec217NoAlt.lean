module

public import CFSG.RankThree.GF2n.Smith81.ESetup
public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.Sec217Perfect
public import CFSG.RankThree.GF2n.Smith81.Sec217AltPerm
public import CFSG.RankThree.GF2n.Smith81.OrthSetup
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

section Width

variable [Finite G] {M Q Z B : Subgroup G}

theorem RemCfg.exists_width (hc : RemCfg M Q Z B) : ∃ k : ℕ, 2 ≤ k ∧ Width Q Z k := by
  rcases hc.remaining with hO | hE | ⟨n, hn⟩
  · obtain ⟨k, hk, -, h4⟩ := hO.exists_width
    exact ⟨k, by omega, hk⟩
  · obtain ⟨k, m, hk, hnm⟩ := hE.exists_width
    refine ⟨k, ?_, hk⟩
    unfold ETypeNM at hnm
    omega
  · rcases hn with ⟨hnTI, hE6⟩ | ⟨rfl, hD2, -⟩
    · exact ⟨n, CaseE6.two_le hc.ctx hnTI hE6, CaseE6.width hc.ctx.hyp hE6⟩
    · exact ⟨2, le_rfl, hD2.1⟩

theorem RemCfg.two_pow_nine_lt_card (hc : RemCfg M Q Z B) : 2 ^ 9 < Nat.card Q := by
  obtain ⟨k, hk2, hw⟩ := hc.exists_width
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hw' : Nat.card Q = Nat.card Z ^ (2 * k + 1) := hw
  have h1 : Nat.card Z ^ 5 ≤ Nat.card Z ^ (2 * k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 4 ^ 5 ≤ Nat.card Z ^ 5 := Nat.pow_le_pow_left hq4 5
  rw [hw']
  omega

end Width

section Transport

variable {X S : Subgroup G} {P : Type*} [Group P]

theorem mem_map_subgroupOf_iff_exists (π : ↥X →* P) {b : P} :
    b ∈ (S.subgroupOf X).map π ↔ ∃ x : ↥X, (x : G) ∈ S ∧ π x = b := by
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem map_mem_normalizer_map_subgroupOf_iff (hSX : S ≤ X) (π : ↥X →* P)
    (hπ : Function.Injective π) (x : ↥X) :
    π x ∈ Subgroup.normalizer (((S.subgroupOf X).map π : Subgroup P) : Set P) ↔
      (x : G) ∈ Subgroup.normalizer (S : Set G) := by
  have h1 := Subgroup.comap_normalizer_eq_of_le_range (f := π)
    (H := (S.subgroupOf X).map π) (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  rw [Subgroup.comap_map_eq_self_of_injective hπ] at h1
  have h2 := Subgroup.subgroupOf_normalizer_eq hSX
  have h3 : x ∈ (Subgroup.normalizer (((S.subgroupOf X).map π : Subgroup P) : Set P)).comap π ↔
      x ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [h1]
  have h4 : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf X ↔
      x ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [h2]
  exact h3.trans (h4.symm.trans Subgroup.mem_subgroupOf)

end Transport

section Main

variable [Finite G] {M Q Z B : Subgroup G}

theorem not_nonempty_equiv_alternatingGroup (hc : RemCfg M Q Z B) (n : ℕ) :
    ¬ Nonempty (FStar G ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  classical
  have H := hc.ctx.hyp
  have hQX : Q ≤ generalizedFitting G := Q_le_generalizedFitting H
  have hZX : Z ≤ generalizedFitting G := H.Z_normal.1.trans hQX
  let π : FStar G →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hπinj : Function.Injective π := Subtype.val_injective.comp e.injective
  have hπalt : ∀ x, π x ∈ alternatingGroup (Fin n) := fun x => (e x).2
  have hπsurj : ∀ c ∈ alternatingGroup (Fin n), ∃ x, π x = c := fun c hc =>
    ⟨e.symm ⟨c, hc⟩, by simp [π]⟩
  set A : Subgroup (Equiv.Perm (Fin n)) := (Z.subgroupOf (generalizedFitting G)).map π with hA
  set Qp : Subgroup (Equiv.Perm (Fin n)) := (Q.subgroupOf (generalizedFitting G)).map π with hQp
  have memA : ∀ b, b ∈ A ↔ ∃ x : FStar G, (x : G) ∈ Z ∧ π x = b := fun b =>
    mem_map_subgroupOf_iff_exists π
  have memQ : ∀ b, b ∈ Qp ↔ ∃ x : FStar G, (x : G) ∈ Q ∧ π x = b := fun b =>
    mem_map_subgroupOf_iff_exists π
  have hMZ : Subgroup.normalizer (Z : Set G) = M := H.normalizer_Z.1
  have hMQ : Subgroup.normalizer (Q : Set G) = M := H.normalizer_Z.2
  have hnZ : ∀ x : FStar G,
      π x ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin n))) ↔ (x : G) ∈ M := by
    intro x
    rw [← hMZ]
    exact map_mem_normalizer_map_subgroupOf_iff hZX π hπinj x
  have hA2 : ∀ u ∈ A, u * u = 1 := by
    intro u hu
    obtain ⟨x, hxZ, rfl⟩ := (memA u).mp hu
    have : x * x = 1 := Subtype.ext (by simpa [pow_two] using Z_sq H hxZ)
    rw [← map_mul, this, map_one]
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    intro u hu v hv
    obtain ⟨x, hxZ, rfl⟩ := (memA u).mp hu
    obtain ⟨y, hyZ, rfl⟩ := (memA v).mp hv
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hc.ctx.Z_comm _ hxZ _ hyZ))
  have hA4 : 4 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective hπinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv]
    exact H.q4
  have hT1 : ∀ u ∈ A, u ≠ 1 → ∀ c ∈ alternatingGroup (Fin n), c * u = u * c →
      c ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin n))) := by
    intro u hu hu1 c hcalt hcomm
    obtain ⟨x, hxZ, rfl⟩ := (memA u).mp hu
    obtain ⟨c', rfl⟩ := hπsurj c hcalt
    have hx1 : (x : G) ≠ 1 := by
      intro h
      apply hu1
      have hx : x = 1 := Subtype.ext (by simpa using h)
      rw [hx, map_one]
    have hcomm' : (c' : G) * x = x * c' := by
      have : c' * x = x * c' := hπinj (by rw [map_mul, map_mul]; exact hcomm)
      exact congrArg Subtype.val this
    exact (hnZ c').mpr (mem_M_of_commute_Z H hxZ hx1 hcomm')
  have hT2 : ∀ P : Subgroup (Equiv.Perm (Fin n)), P ≤ alternatingGroup (Fin n) →
      P ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin n))) → Group.IsPerfect P →
      ∀ p ∈ P, ∀ b ∈ A, p * b = b * p := by
    intro P hPalt hPN hPperf p hp b hb
    set Pc : Subgroup (FStar G) := P.comap π with hPc
    have hPcmap : Pc.map π = P := Subgroup.map_comap_eq_self fun x hx => by
      obtain ⟨y, rfl⟩ := hπsurj x (hPalt hx)
      exact ⟨y, rfl⟩
    have hPcperf : ⁅Pc, Pc⁆ = Pc := by
      apply Subgroup.map_injective hπinj
      rw [Subgroup.map_commutator, hPcmap]
      exact Subgroup.isPerfect_iff.mp hPperf
    let PG : Subgroup G := Pc.map (generalizedFitting G).subtype
    have hPGperf : Group.IsPerfect PG :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hPcperf])
    have hPGM : PG ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hnZ x).mp (hPN hx)
    have hcent := perfect_centralizes_of_semilinAct (semilinAct_Z H) hPGM hPGperf
    obtain ⟨p', rfl⟩ := hπsurj p (hPalt hp)
    obtain ⟨y, hyZ, rfl⟩ := (memA b).mp hb
    have hp' : p' ∈ Pc := by
      show π p' ∈ P
      exact hp
    have := hcent (p' : G) ⟨p', hp', rfl⟩ (y : G) hyZ
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext this)
  have hQalt : Qp ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨x, -, rfl⟩
    exact hπalt x
  have hQ2 : IsPGroup 2 Qp :=
    ((isPGroup_Q' H).of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm).map π
  have hQN : Qp ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hnZ x).mpr (H.Q_normal.1 (Subgroup.mem_subgroupOf.mp hx))
  have hNQ : ∀ t ∈ alternatingGroup (Fin n),
      t ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin n))) →
        t ∈ Subgroup.normalizer (Qp : Set (Equiv.Perm (Fin n))) := by
    intro t ht htN
    obtain ⟨t', rfl⟩ := hπsurj t ht
    have hM : (t' : G) ∈ M := (hnZ t').mp htN
    rw [← hMQ] at hM
    exact (map_mem_normalizer_map_subgroupOf_iff hQX π hπinj t').mpr hM
  have hCQ : ∀ c ∈ alternatingGroup (Fin n), (∀ q ∈ Qp, c * q = q * c) → c ∈ A := by
    intro c hcalt hcomm
    obtain ⟨c', rfl⟩ := hπsurj c hcalt
    refine (memA _).mpr ⟨c', ?_, rfl⟩
    rw [← H.centralizer_Q, Subgroup.mem_centralizer_iff]
    intro q hq
    have hqX : q ∈ generalizedFitting G := hQX hq
    have h1 := hcomm (π ⟨q, hqX⟩) ((memQ _).mpr ⟨⟨q, hqX⟩, hq, rfl⟩)
    have h2 : c' * ⟨q, hqX⟩ = ⟨q, hqX⟩ * c' := hπinj (by rw [map_mul, map_mul]; exact h1)
    exact (congrArg Subtype.val h2).symm
  have hQbig : 2 ^ 9 < Nat.card Qp := by
    rw [hQp, Subgroup.card_map_of_injective hπinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
    exact hc.two_pow_nine_lt_card
  exact false_of_alternating_config hA2 hAc hA4 hT1 hT2 hQalt hQ2 hQN hNQ hCQ hQbig

end Main

end CFSG.RankThree.GF2n.Smith81
