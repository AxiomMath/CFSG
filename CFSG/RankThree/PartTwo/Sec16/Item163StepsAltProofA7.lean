module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec16.Step163Alt

open CFSG Equiv CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_vOne_of_mem_centOne {z v : Perm (Fin 7)} (hz : z ∈ centOne) (hv : v ∈ vOne) :
    z * v * z⁻¹ ∈ vOne := by
  rw [← pCore_two_centOne] at hv ⊢
  obtain ⟨p, hp, rfl⟩ := hv
  exact ⟨⟨z, hz⟩ * p * ⟨z, hz⟩⁻¹, (CFSG.pCore_normal).conj_mem p hp ⟨z, hz⟩, rfl⟩

theorem vOne_spec {v : Perm (Fin 7)} (hv : v ∈ vOne) :
    v * cOne = cOne * v ∧ v ∈ alternatingGroup (Fin 7) ∧ v ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := hv
  exact ⟨(vOneF_spec m).1, Perm.mem_alternatingGroup.mpr (vOneF_spec m).2, vOneF_sq m⟩

theorem vOneF_one_spec : vOneF 1 ∈ vOne ∧ vOneF 1 ≠ 1 :=
  ⟨⟨1, rfl⟩, by decide⟩

theorem cOne_cycleType : cOne.cycleType = {3} := by
  have h := (eNineF_cycleType 1 0 (by decide)).1.mpr (Or.inr rfl)
  rwa [show eNineF 1 0 = cOne by decide] at h

theorem pCoreOf_inf_centralizer_ne_bot {Y : Subgroup G} {c g : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1) (hgY : g ∈ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))
    (hcg : ∀ y ∈ Y, (g * y * g⁻¹)⁻¹ * (c * y * c⁻¹) ∈ CFSG.Open.pCoreOf 2 Y)
    (hσ : ((φ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨g, hgY⟩) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)).cycleType = {3}) :
    CFSG.Open.pCoreOf 2 (Y ⊓ Subgroup.centralizer {c}) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set g₀ : ↥Y := ⟨g, hgY⟩ with hg₀
  set ψ7 : (↥Y ⧸ N) →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom
    with hψ7
  have hψinj : Function.Injective ψ7 := Subtype.val_injective.comp φ.injective
  have hψA : ∀ q, ψ7 q ∈ alternatingGroup (Fin 7) := fun q => (φ q).2
  have hact : ∀ y : ↥Y, π ⟨c * y * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y).mp y.2⟩ =
      π g₀ * π y * (π g₀)⁻¹ := by
    intro y
    rw [← map_inv, ← map_mul, ← map_mul, eq_comm, hπ, mk_eq_mk_iff]
    simpa using hcg y y.2
  obtain ⟨τ, hτ⟩ := isConj_iff.mp ((Perm.isConj_iff_cycleType_eq).mpr
    (hσ.trans cOne_cycleType.symm))
  change τ * ψ7 (π g₀) * τ⁻¹ = cOne at hτ
  set Nb : Subgroup (↥Y ⧸ N) := (vOne.map (MulAut.conj τ⁻¹).toMonoidHom).comap ψ7 with hNb
  have hmemNb : ∀ q, q ∈ Nb ↔ τ * ψ7 q * τ⁻¹ ∈ vOne := by
    intro q
    rw [hNb, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hcomm_iff : ∀ q, q * π g₀ = π g₀ * q ↔
      (τ * ψ7 q * τ⁻¹) * cOne = cOne * (τ * ψ7 q * τ⁻¹) := by
    intro q
    rw [← hτ]
    constructor
    · intro hq
      have := congrArg ψ7 hq
      rw [map_mul, map_mul] at this
      calc τ * ψ7 q * τ⁻¹ * (τ * ψ7 (π g₀) * τ⁻¹) = τ * (ψ7 q * ψ7 (π g₀)) * τ⁻¹ := by group
        _ = τ * (ψ7 (π g₀) * ψ7 q) * τ⁻¹ := by rw [this]
        _ = τ * ψ7 (π g₀) * τ⁻¹ * (τ * ψ7 q * τ⁻¹) := by group
    · intro hq
      apply hψinj
      rw [map_mul, map_mul]
      have h1 : τ * (ψ7 q * ψ7 (π g₀)) * τ⁻¹ = τ * (ψ7 (π g₀) * ψ7 q) * τ⁻¹ := by
        calc τ * (ψ7 q * ψ7 (π g₀)) * τ⁻¹ = τ * ψ7 q * τ⁻¹ * (τ * ψ7 (π g₀) * τ⁻¹) := by group
          _ = τ * ψ7 (π g₀) * τ⁻¹ * (τ * ψ7 q * τ⁻¹) := hq
          _ = τ * (ψ7 (π g₀) * ψ7 q) * τ⁻¹ := by group
      simpa using h1
  have hnorm : ∀ q, q * π g₀ = π g₀ * q → ∀ n ∈ Nb, q * n * q⁻¹ ∈ Nb := by
    intro q hq n hn
    have hz : τ * ψ7 q * τ⁻¹ ∈ centOne := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · exact (hcomm_iff q).mp hq
      · have := (alternatingGroup.normal (α := Fin 7)).conj_mem _ (hψA q) τ
        exact this
    rw [hmemNb] at hn ⊢
    have := conj_mem_vOne_of_mem_centOne hz hn
    rw [map_mul, map_mul, map_inv]
    have e : τ * (ψ7 q * ψ7 n * (ψ7 q)⁻¹) * τ⁻¹ =
        τ * ψ7 q * τ⁻¹ * (τ * ψ7 n * τ⁻¹) * (τ * ψ7 q * τ⁻¹)⁻¹ := by group
    rw [e]
    exact this
  have hNb2 : IsPGroup 2 Nb := by
    intro q
    refine ⟨1, Subtype.ext ?_⟩
    have hq := (vOne_spec ((hmemNb q).mp q.2)).2.2
    apply hψinj
    rw [pow_one, Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    calc ψ7 q ^ 2 = τ⁻¹ * (τ * ψ7 q * τ⁻¹) ^ 2 * τ := by rw [sq, sq]; group
      _ = 1 := by rw [hq]; group
  set n₇ := τ⁻¹ * vOneF 1 * τ with hn₇
  have hn₇A : n₇ ∈ alternatingGroup (Fin 7) := by
    have := (alternatingGroup.normal (α := Fin 7)).conj_mem _ (vOne_spec vOneF_one_spec.1).2.1 τ⁻¹
    rwa [inv_inv] at this
  set q₀ := φ.symm ⟨n₇, hn₇A⟩ with hq₀
  have hψq₀ : ψ7 q₀ = n₇ := by
    simp [hψ7, hq₀]
  have hq₀Nb : q₀ ∈ Nb := by
    rw [hmemNb, hψq₀, hn₇]
    rw [show τ * (τ⁻¹ * vOneF 1 * τ) * τ⁻¹ = vOneF 1 by group]
    exact vOneF_one_spec.1
  have hq₀1 : q₀ ≠ 1 := by
    intro h1
    have : ψ7 q₀ = 1 := by rw [h1, map_one]
    rw [hψq₀, hn₇] at this
    apply vOneF_one_spec.2
    calc vOneF 1 = τ * (τ⁻¹ * vOneF 1 * τ) * τ⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hq₀g : q₀ * π g₀ = π g₀ * q₀ := by
    rw [hcomm_iff]
    have h1 := (vOne_spec ((hmemNb q₀).mp hq₀Nb)).1
    exact h1
  have hzN : Subgroup.zpowers c ≤ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr hcN
  set α : ↥(Subgroup.zpowers c) →* MulAut ↥Y :=
    Y.normalizerMonoidHom.comp (Subgroup.inclusion hzN) with hα
  have hαN : ∀ a : ↥(Subgroup.zpowers c), ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    have h : N.map (α a).toMonoidHom = N := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 ↥Y).Characteristic) (α a)
    exact h ▸ Subgroup.mem_map_of_mem (α a).toMonoidHom hn
  have hcP : IsPGroup 3 (Subgroup.zpowers c) := by
    rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hcop : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hN, hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  set gen : ↥(Subgroup.zpowers c) := ⟨c, Subgroup.mem_zpowers c⟩ with hgen
  have hfix_gen : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN gen q₀ =
      q₀ := by
    obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk'_surjective N q₀
    rw [← hy₁]
    change ((α gen y₁ : ↥Y) : ↥Y ⧸ N) = π y₁
    have h1 : α gen y₁ = ⟨c * y₁ * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y₁).mp y₁.2⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe Y _ y₁)
    rw [h1]
    change π _ = π y₁
    rw [hact, show π y₁ = q₀ from hy₁, ← hq₀g, mul_inv_cancel_right]
  have hfix : q₀ ∈ {q : ↥Y ⧸ N | ∀ a : ↥(Subgroup.zpowers c),
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = gen ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])
    have hst : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN gen ∈
        MulAction.stabilizer (MulAut (↥Y ⧸ N)) q₀ := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix_gen
    have := (MulAction.stabilizer (MulAut (↥Y ⧸ N)) q₀).zpow_mem hst k
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow] at this
    rw [ha]
    exact this
  rw [CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hcP α N hαN hcop] at hfix
  obtain ⟨y₀, hy₀fix, hy₀⟩ := hfix
  have hy₀c : (y₀ : G) ∈ Subgroup.centralizer {c} := by
    have h1 : c * (y₀ : G) * c⁻¹ = y₀ := by
      have h2 := congrArg Subtype.val (hy₀fix gen)
      rw [hα, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      exact h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y₀ : G) * c = (c * y₀ * c⁻¹) * c := by rw [h1]
      _ = c * y₀ := by group
  set P₀ : Subgroup ↥Y := Nb.comap π ⊓ (Subgroup.centralizer {c}).subgroupOf Y with hP₀
  set P : Subgroup G := P₀.map Y.subtype with hP
  have hPK : P ≤ Y ⊓ Subgroup.centralizer {c} := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.2, hp.2⟩
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hP2 : IsPGroup 2 P :=
    ((hNb2.comap_of_ker_isPGroup π hker).to_le inf_le_left).map Y.subtype
  have hKP : Y ⊓ Subgroup.centralizer {c} ≤ Subgroup.normalizer (P : Set G) := by
    intro z hz
    obtain ⟨hzY, hzc⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := hx
    set z₀ : ↥Y := ⟨z, hzY⟩ with hz₀
    have hzq : π z₀ * π g₀ = π g₀ * π z₀ := by
      have h1 := hact z₀
      have hczc : c * z * c⁻¹ = z := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hzc, mul_inv_cancel_right]
      have h2 : (⟨c * z₀ * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN z₀).mp z₀.2⟩ : ↥Y) = z₀ :=
        Subtype.ext hczc
      rw [h2] at h1
      calc π z₀ * π g₀ = π g₀ * π z₀ * (π g₀)⁻¹ * π g₀ := by rw [← h1]
        _ = π g₀ * π z₀ := by group
    have hp' := Subgroup.mem_inf.mp hp
    refine ⟨z₀ * p * z₀⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · change π (z₀ * p * z₀⁻¹) ∈ Nb
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ hzq _ hp'.1
    · have hpc : (p : G) ∈ Subgroup.centralizer {c} := Subgroup.mem_subgroupOf.mp hp'.2
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzc hpc) (Subgroup.inv_mem _ hzc)
  have hPle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPK hKP hP2
  intro hbot
  have hy₀P : (y₀ : G) ∈ P := ⟨y₀, ⟨by
    change π y₀ ∈ Nb
    rw [hπ, hy₀]
    exact hq₀Nb, hy₀c⟩, rfl⟩
  have hy₀1 : (y₀ : G) = 1 := by
    have := hPle hy₀P
    rwa [hbot, Subgroup.mem_bot] at this
  apply hq₀1
  rw [← hy₀, show y₀ = 1 from Subtype.ext hy₀1, map_one]

end CFSG.RankThree.PartTwo.Sec16.Step163Alt
