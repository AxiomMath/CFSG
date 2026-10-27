module

public import CFSG.Quasithin.H13.L32AKG1468e
public import CFSG.Sporadic.Schreier.RuIso

public noncomputable section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix

theorem exists_rho
    {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hRu : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .Ru))
    {S : Subgroup G} (hS : IsSylowTwoOf S Y) :
    ∃ ρ : ↥Y →* ↥ruP, Function.Surjective ρ ∧ ρ.ker = CFSG.pCore 2 ↥Y ∧
      (S.subgroupOf Y).map ρ = ruS.subgroupOf ruP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hRu
  let e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥ruP := e₀.trans ruEquivP
  let ρ₀ : ↥Y →* ↥ruP := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hρ₀s : Function.Surjective ρ₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρ₀k : ρ₀.ker = CFSG.pCore 2 ↥Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hS2 : IsPGroup 2 ((S.subgroupOf Y).map ρ₀) :=
    (hS.2.1.comap_of_injective Y.subtype Y.subtype_injective).map ρ₀
  have hSi : ¬ 2 ∣ ((S.subgroupOf Y).map ρ₀).index := fun h2 =>
    hS.2.2 (h2.trans (Subgroup.index_map_dvd _ hρ₀s))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥ruP (hS2.toSylow hSi) ruSylow
  refine ⟨(MulAut.conj g).toMonoidHom.comp ρ₀, (MulAut.conj g).surjective.comp hρ₀s, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hρ₀k]
  · rw [← Subgroup.map_map, ← ruSylow_coe, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.pointwise_smul_def]
    rfl

theorem eq_ruZ_of_comm
    {w : ↥ruP} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hc : ∀ s ∈ ruS.subgroupOf ruP, s * w = w * s) : (w : Equiv.Perm (Fin 4060)) = ruZ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwS : w ∈ ruS.subgroupOf ruP := by
    have hzp : IsPGroup 2 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1, pow_one])
    have hN : Subgroup.zpowers w ≤ Subgroup.normalizer
        ((ruSylow : Subgroup ↥ruP) : Set ↥ruP) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro s
      rw [ruSylow_coe]
      constructor
      · intro hs
        rw [← hc s hs, mul_inv_cancel_right]
        exact hs
      · intro hs
        have hs' : w * s * w⁻¹ ∈ ruS.subgroupOf ruP := hs
        have e1 : s = w⁻¹ * (w * s * w⁻¹) * w := by group
        rw [e1]
        have h2 := hc _ hs'
        rw [show w⁻¹ * (w * s * w⁻¹) * w = w⁻¹ * ((w * s * w⁻¹) * w) by group, h2,
          inv_mul_cancel_left]
        exact hs'
    have hQ := IsPGroup.to_sup_of_normal_right' hzp (ruSylow : Sylow 2 ↥ruP).isPGroup' hN
    have hmax := (ruSylow : Sylow 2 ↥ruP).is_maximal' hQ le_sup_right
    have hw : w ∈ Subgroup.zpowers w ⊔ (ruSylow : Subgroup ↥ruP) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
    rw [hmax, ruSylow_coe] at hw
    exact hw
  have hwS' : (w : Equiv.Perm (Fin 4060)) ∈ ruS := Subgroup.mem_subgroupOf.mp hwS
  have hwZ : (w : Equiv.Perm (Fin 4060)) ∈ (Subgroup.center ruS).map ruS.subtype := by
    refine ⟨⟨_, hwS'⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    have h1 := hc ⟨s, ruS_le s.2⟩ (Subgroup.mem_subgroupOf.mpr s.2)
    have h2 : ((⟨s, ruS_le s.2⟩ : ↥ruP) * w : ↥ruP).1 = (w * ⟨s, ruS_le s.2⟩ : ↥ruP).1 :=
      congrArg Subtype.val h1
    exact h2
  rw [center_ruS] at hwZ
  rcases mem_zpowers_ruZ hwZ with h | h
  · exact absurd (Subtype.ext h) hw1
  · exact h

theorem centralizer_ruZ_P :
    Subgroup.centralizer ({(⟨ruZ, ruZ_mem⟩ : ↥ruP)} : Set ↥ruP) = ruC.subgroupOf ruP := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, ruC_eq_centralizer,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨x.2, (congrArg Subtype.val h :)⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h

theorem oTwoUpper_top_sl32 :
    oTwoUpper (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ := by
  have := Vol2Native.A312L.Seven.slThree_isSimple
  have hn : (oTwoUpper (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper ⊤ (Subgroup.mem_top g)) n).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (oTwoUpper (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))) with h | h
  · exfalso
    have h3 : ruSL1 ∈ oTwoUpper (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))) := by
      refine mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_
      have : orderOf ruSL1 = 3 := by
        apply orderOf_eq_prime (hp := ⟨Nat.prime_three⟩)
        · exact Subtype.ext (show ruM1 ^ 3 = 1 by decide +kernel)
        · intro h
          have h' : ruM1 = 1 := congrArg Subtype.val h
          revert h'
          decide +kernel
      rw [this]
      decide
    rw [h, Subgroup.mem_bot] at h3
    have h' : ruM1 = 1 := congrArg Subtype.val h3
    revert h'
    decide +kernel
  · exact h

end CFSG.Quasithin.H13.KGRu
