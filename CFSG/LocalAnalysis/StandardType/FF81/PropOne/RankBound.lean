module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeBasic

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

theorem card_le_of_normalizer_isPGroup_two {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (hA : HypA G n b L) (hM : GGFF.Model ↥L z)
    {T E : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hE : E ≤ Subgroup.normalizer (T : Set G)) (hEa : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let C : Subgroup G := Subgroup.centralizer ({b} : Set G)
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEa).exists_card_eq
  have hk_le : k ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    CFSG.GGQ2Prime.le_twoLocalPrimeRank (by norm_num : 2 ≤ 3) T E hT hT2 hE hEa hk
  have hk_le' : k ≤ CFSG.Open.twoLocalPrimeRank 3 ↥C := by
    rw [← hA.rank]
    exact hk_le
  have hclaim : ∀ F : Subgroup ↥C, CFSG.Open.IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 4 := by
    intro F hFa
    let iota : F →* Subgroup.normalizer (L : Set G) :=
      { toFun := fun x => ⟨(x.1 : G), hA.nor x.1.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    let phi : F →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp iota
    have hker_a : CFSG.Open.IsElemAbelian 3 phi.ker :=
      (hFa.subgroupOf F).mono (by intro x _; exact Subgroup.mem_subgroupOf.mpr x.2)
    let D : Subgroup G := Subgroup.centralizer (L : Set G)
    have hmem : ∀ x : phi.ker, (((x.1 : F) : ↥C) : G) ∈ D := by
      intro x
      have hx' : iota x.1 ∈ (Subgroup.normalizerMonoidHom L).ker := by
        rw [MonoidHom.mem_ker]
        exact x.2
      rw [Subgroup.normalizerMonoidHom_ker] at hx'
      show ((iota x.1 : Subgroup.normalizer (L : Set G)) : G) ∈ Subgroup.centralizer (L : Set G)
      exact Subgroup.mem_subgroupOf.mp hx'
    let rho : phi.ker →* ↥D :=
      { toFun := fun x => ⟨(((x.1 : F) : ↥C) : G), hmem x⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    have hrho_inj : Function.Injective rho := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥D => (t : G)) hxy
    let Kd : Subgroup ↥D := (⊤ : Subgroup phi.ker).map rho
    have hKd_card : Nat.card Kd = Nat.card phi.ker := by
      have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup phi.ker)) hrho_inj
      rw [Subgroup.card_top] at h
      exact h
    have hKd_elem : CFSG.Open.IsElemAbelian 3 Kd := by
      have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup phi.ker) :=
        (hker_a.subgroupOf phi.ker).mono
          (by intro x _; exact Subgroup.mem_subgroupOf.mpr x.2)
      exact htop.map rho
    have hKd3 : IsPGroup 3 Kd := hKd_elem.isPGroup
    obtain ⟨P, hKdP⟩ := hKd3.exists_le_sylow
    have : IsCyclic P := hA.cyc P
    have hKdcyc : IsCyclic Kd := Subgroup.isCyclic_of_le hKdP
    have : IsCyclic Kd := hKdcyc
    have hKd_le : Nat.card Kd ≤ 3 := GGFF.card_le_three_of_cyclic hKd_elem
    have hker_card : Nat.card phi.ker ≤ 3 := by
      rw [← hKd_card]
      exact hKd_le
    have hrange_a : CFSG.Open.IsElemAbelian 3 phi.range := by
      have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup F) :=
        (hFa.subgroupOf F).mono (by intro x _; exact Subgroup.mem_subgroupOf.mpr x.2)
      have h := htop.map phi
      rw [← MonoidHom.range_eq_map phi] at h
      exact h
    have hconj_inj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
      rw [← MonoidHom.ker_eq_bot_iff (MulAut.conj : ↥L →* MulAut ↥L),
        Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      apply hM.eq_one_of_forall_comm
      intro y
      have hy : x * y * x⁻¹ = y := by
        have := congrArg (fun α : MulAut ↥L => (α y : ↥L)) hx
        simpa [MulAut.conj_apply] using this
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hy]
    have hle : phi.range ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
      rintro α ⟨c, rfl⟩
      obtain ⟨l, hl⟩ := hM.inner_odd (phi c) 3 (by decide) (by
        have hc3 : c ^ 3 = 1 := Subtype.ext (hFa.2 (c : ↥C) c.2)
        rw [← map_pow, hc3, map_one])
      exact ⟨l, hl.symm⟩
    let Q : Subgroup ↥L := phi.range.comap (MulAut.conj : ↥L →* MulAut ↥L)
    have hQ_card : Nat.card Q = Nat.card phi.range := by
      have hmap := Subgroup.map_comap_eq_self (f := (MulAut.conj : ↥L →* MulAut ↥L)) hle
      have hcard := Subgroup.card_map_of_injective (K := Q) hconj_inj
      rw [hmap] at hcard
      exact hcard.symm
    have hQ_a : CFSG.Open.IsElemAbelian 3 Q := hrange_a.comap hconj_inj
    have hrange_card : Nat.card phi.range ≤ 27 := by
      have h := hM.rank Q hQ_a
      rwa [hQ_card] at h
    calc Nat.card F = Nat.card phi.ker * Nat.card phi.range :=
          (Subgroup.card_ker_mul_card_range phi).symm
      _ ≤ 3 * 27 := Nat.mul_le_mul hker_card hrange_card
      _ = 3 ^ 4 := by norm_num
  have hpRank : ∀ H : Subgroup ↥C, CFSG.Open.pRank 3 H ≤ 4 := by
    intro H
    rw [CFSG.Open.pRank]
    apply csSup_le'
    intro j hj
    obtain ⟨F, -, hFa, hFcard⟩ := hj
    have h := hclaim F hFa
    rw [hFcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have htwo : CFSG.Open.twoLocalPrimeRank 3 ↥C ≤ 4 := by
    rw [CFSG.Open.twoLocalPrimeRank]
    apply csSup_le'
    intro j hj
    obtain ⟨H, -, rfl⟩ := hj
    exact hpRank H
  calc Nat.card E = 3 ^ k := hk
    _ ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (hk_le'.trans htwo)

end CFSG.StandardType.FF81.PropOne

end
