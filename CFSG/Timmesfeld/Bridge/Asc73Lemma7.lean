module

public import CFSG.Timmesfeld.Bridge.InvolutionSet

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type*} [Group G] {D : Set G}

theorem conj_mem_compStab_iff (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hodd : OddAcross D)
    {z : G} (hz : z ∈ D) (g : G) : g * z * g⁻¹ ∈ compStab hN z ↔ g ∈ compStab hN z := by
  constructor
  · intro h
    exact reach_of_mem_compStab_of_odd hN hD hodd hz (hN g z hz) h
  · intro h
    exact (compStab hN z).mul_mem ((compStab hN z).mul_mem h (mem_compStab_self hN z))
      ((compStab hN z).inv_mem h)

theorem centralizer_conj_eq (g z : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

theorem exists_pow_not_mem_sq_mem {P : Subgroup G} {y : G} {n : ℕ} (hy : y ^ 2 ^ n = 1)
    (hyP : y ∉ P) : ∃ t ∈ Subgroup.zpowers y, t ∉ P ∧ t * t ∈ P := by
  classical
  have hex : ∃ k, y ^ 2 ^ k ∈ P := ⟨n, by rw [hy]; exact P.one_mem⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀P : y ^ 2 ^ k₀ ∈ P := Nat.find_spec hex
  have hk₀pos : k₀ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk₀P
    exact hyP hk₀P
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk₀pos
  refine ⟨y ^ 2 ^ j, Subgroup.npow_mem_zpowers y _, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · rw [← pow_add, ← two_mul, ← pow_succ']
    have hj' : k₀ = j + 1 := hj
    rw [hj'] at hk₀P
    exact hk₀P

theorem exists_sylow_le_centralizer [Finite G] (hN : IsNormalSet D) (hD : IsInvolutionSet D)
    (hnp : Moufang.NoPolar D) (hclass : ∀ x ∈ D, ∀ y ∈ D, IsConj x y) {z : G} (hz : z ∈ D) :
    ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), Commute s z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  set P' : Subgroup G := (P : Subgroup C).map C.subtype with hP'
  have hP'C : P' ≤ C := Subgroup.map_subtype_le _
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hcomm : ∀ s ∈ P', Commute s z := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hP'C hs)
  have hzP' : z ∈ P' := by
    have hnorm : (Subgroup.zpowers (⟨z, hzC⟩ : C)).Normal := by
      refine ⟨fun x hx c => ?_⟩
      have hzc : c * ⟨z, hzC⟩ * c⁻¹ = ⟨z, hzC⟩ := by
        apply Subtype.ext
        have hcz := Subgroup.mem_centralizer_singleton_iff.1 c.2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcz, mul_inv_cancel_right]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← conj_zpow, hzc]
      exact Subgroup.zpow_mem_zpowers _ k
    have h2 : IsPGroup 2 (Subgroup.zpowers (⟨z, hzC⟩ : C)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
      exact hD.orderOf_eq_two hz
    exact ⟨⟨z, hzC⟩, h2.le_sylow_of_normal P (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨S, hS⟩ := hP'2.exists_le_sylow
  refine ⟨S, hS hzP', ?_⟩
  suffices hSP : (S : Subgroup G) = P' by
    rw [hSP]; exact hcomm
  by_contra hne
  have hlt : P'.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm ?_ hS
    intro y hy
    have : (⟨y, hy⟩ : S) ∈ P'.subgroupOf S := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyP' : (y : G) ∉ P' := fun h => hyP (Subgroup.mem_subgroupOf.2 h)
  have hyNG : (y : G) ∈ Subgroup.normalizer (P' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := (Subgroup.mem_normalizer_iff.1 hyN ⟨h, hS hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hh
      have hhS : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem y.2)
          (hS hh)) y.2
      have hh' : h ∈ (S : Subgroup G) := by simpa [mul_assoc] using hhS
      have := (Subgroup.mem_normalizer_iff.1 hyN ⟨h, hh'⟩).2 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨n, hn⟩ := S.isPGroup' y
  have hyn : (y : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨t, htY, htP, ht2⟩ := exists_pow_not_mem_sq_mem hyn hyP'
  have htN : t ∈ Subgroup.normalizer (P' : Set G) := by
    rw [← Subgroup.zpowers_le] at hyNG
    exact hyNG htY
  have htS : t ∈ (S : Subgroup G) := by
    have : Subgroup.zpowers (y : G) ≤ S := by rw [Subgroup.zpowers_le]; exact y.2
    exact this htY
  have hconjP : ∀ s ∈ P', t * s * t⁻¹ ∈ P' := fun s hs =>
    (Subgroup.mem_normalizer_iff.1 htN s).1 hs
  set R : Subgroup G := P' ⊔ Subgroup.zpowers t with hR
  have hR2 : IsPGroup 2 R := by
    refine hP'2.to_sup_of_normal_left' ?_ ?_
    · exact S.isPGroup'.to_le (by rw [Subgroup.zpowers_le]; exact htS)
    · rw [Subgroup.zpowers_le]; exact htN
  have hP'R : P' < R := by
    refine lt_of_le_of_ne le_sup_left fun heq => htP ?_
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  set z' := t * z * t⁻¹ with hz'
  have hz'D : z' ∈ D := hN t z hz
  have hz'P : z' ∈ P' := hconjP z hzP'
  have hne' : z ≠ z' := by
    intro heq
    have htC : t ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [← hz', ← heq]
    have hRC : R ≤ C := sup_le hP'C (by rw [Subgroup.zpowers_le]; exact htC)
    have hcomap : IsPGroup 2 (R.comap C.subtype) :=
      hR2.comap_of_injective C.subtype Subtype.val_injective
    have hPle : (P : Subgroup C) ≤ R.comap C.subtype := fun q hq =>
      Subgroup.mem_sup_left ⟨q, hq, rfl⟩
    have heqP := P.is_maximal' hcomap hPle
    have htmem : (⟨t, htC⟩ : C) ∈ R.comap C.subtype :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rw [heqP] at htmem
    exact htP ⟨_, htmem, rfl⟩
  have hzz' : Commute z z' := (hcomm z' hz'P).symm
  set w := z * z' with hw
  have hwD : w ∈ D := hnp z hz z' hz'D hzz' hne'
  have hz'c : ∀ s ∈ P', Commute s z' := by
    intro s hs
    have h1 : t⁻¹ * s * t ∈ P' := by
      have := (Subgroup.mem_normalizer_iff.1 htN (t⁻¹ * s * t)).2 (by simpa [mul_assoc] using hs)
      exact this
    have h2 := (hcomm _ h1).eq
    show s * (t * z * t⁻¹) = t * z * t⁻¹ * s
    calc s * (t * z * t⁻¹) = t * ((t⁻¹ * s * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * s * t)) * t⁻¹ := by rw [h2]
      _ = t * z * t⁻¹ * s := by group
  have hwR : R ≤ Subgroup.centralizer ({w} : Set G) := by
    refine sup_le ?_ ?_
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff, hw]
      exact ((hcomm s hs).mul_right (hz'c s hs)).eq
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have htt : t * t * z * (t * t)⁻¹ = z := by
        rw [(hcomm (t * t) ht2).eq, mul_inv_cancel_right]
      have hconjw : t * w * t⁻¹ = w := by
        calc t * w * t⁻¹ = (t * z * t⁻¹) * (t * z' * t⁻¹) := by rw [hw]; group
          _ = z' * (t * t * z * (t * t)⁻¹) := by rw [hz']; group
          _ = z' * z := by rw [htt]
          _ = w := by rw [hw, hzz'.eq]
      calc t * w = (t * w * t⁻¹) * t := by group
        _ = w * t := by rw [hconjw]
  obtain ⟨g, hg⟩ := isConj_iff.1 (hclass z hz w hwD)
  have hCw : Subgroup.centralizer ({w} : Set G) = C.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, centralizer_conj_eq]
  have hcardC : Nat.card (Subgroup.centralizer ({w} : Set G)) = Nat.card C := by
    rw [hCw]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hR2' : IsPGroup 2 (R.comap (Subgroup.centralizer ({w} : Set G)).subtype) :=
    hR2.comap_of_injective _ Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hR2'.exists_le_sylow
  have hcardR : Nat.card R ≤ Nat.card (Q : Subgroup (Subgroup.centralizer ({w} : Set G))) := by
    have h1 : Nat.card R = Nat.card (R.comap (Subgroup.centralizer ({w} : Set G)).subtype) := by
      have hmap : (R.comap (Subgroup.centralizer ({w} : Set G)).subtype).map
          (Subgroup.centralizer ({w} : Set G)).subtype = R := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
        exact inf_eq_right.2 hwR
      conv_lhs => rw [← hmap]
      exact Subgroup.card_map_of_injective (Subgroup.centralizer ({w} : Set G)).subtype_injective
    rw [h1]
    exact Subgroup.card_le_of_le hQ
  have hcardQ : Nat.card (Q : Subgroup (Subgroup.centralizer ({w} : Set G))) =
      Nat.card (P : Subgroup C) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, hcardC]
  have hcardP' : Nat.card P' = Nat.card (P : Subgroup C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have := Subgroup.card_lt_of_lt hP'R
  omega

end CFSG.Timmesfeld.Bridge
