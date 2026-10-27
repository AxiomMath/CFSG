module

public import CFSG.Quasithin.Vol2.Ch11SecD556G
public import CFSG.Quasithin.Vol2.Ch11SecDNat
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecDFStar
public import CFSG.Quasithin.Vol2.Ch11SecDO22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

omit [Group G] in
theorem commutator_subgroupOf [Group G] {G₁ P X : Subgroup G} (hP : P ≤ G₁) (hX : X ≤ G₁) :
    ⁅P.subgroupOf G₁, X.subgroupOf G₁⁆ = ⁅P, X⁆.subgroupOf G₁ := by
  apply Subgroup.map_injective G₁.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le
      ((Subgroup.commutator_mono hP hX).trans (commutator_le_self' G₁))]

theorem isElemAbelian_map_of_frattini [Finite G] {G₁ P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hΦ : (frattini ↥P).map P.subtype ≤ pCoreOf 2 G₁) :
    IsElemAbelian 2 ((P.subgroupOf G₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ g : ↥G₁, (g : G) ∈ pCoreOf 2 G₁ →
      QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) g = 1 := fun g hg => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact hg
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haa, ← hbb, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hc := CFSG.SectionRank.Ccomm.commutator_mem_frattini hP2 (⟨a', ha'⟩ : ↥P) ⟨b', hb'⟩
    have hc' : ⁅a', b'⁆ ∈ CFSG.pCore 2 ↥G₁ := by
      rw [← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
      exact hΦ ⟨_, hc, rfl⟩
    have hn := (CFSG.pCore_normal (p := 2) (G := ↥G₁)).conj_mem _ (Subgroup.inv_mem _ hc')
      (a' * b')⁻¹
    convert hn using 1
    rw [commutatorElement_def]
    group
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow]
    apply hker
    have hs := CFSG.SectionRank.Ccomm.pow_mem_frattini hP2 (⟨x', hx'⟩ : ↥P)
    exact hΦ ⟨_, hs, rfl⟩

theorem layer_le_perfectCore {H : Type} [Group H] [Finite H] :
    CFSG.layer H ≤ perfectCore (⊤ : Subgroup H) := by
  refine sSup_le fun K hK => le_perfectCore_of_perfect le_top ?_
  have hperf : commutator ↥K = ⊤ := hK.1.1.commutator_eq_top
  have h1 := congrArg (Subgroup.map K.subtype) hperf
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  exact h1

theorem commutator_le_pCoreOf_of_perfectCore [Finite G] {G₁ Y P X : Subgroup G}
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ G₁ → IsElemAbelian p E →
      ∀ r, Nat.card E = p ^ r → r ≤ 2)
    (hYG : Y ≤ G₁) (hYN : G₁ ≤ Subgroup.normalizer (Y : Set G))
    (hXG : X ≤ G₁) (hXodd : Odd (Nat.card X))
    (hPG : P ≤ G₁) (hP2 : IsPGroup 2 P) (hPX : ⁅P, X⁆ = P)
    (hΦ : (frattini ↥P).map P.subtype ≤ pCoreOf 2 G₁)
    (hPY : ⁅P, perfectCore Y⁆ ≤ pCoreOf 2 G₁) :
    ⁅P, Y⁆ ≤ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ g : ↥G₁, π g = 1 ↔ (g : G) ∈ pCoreOf 2 G₁ := fun g => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf,
      Subgroup.mem_subgroupOf]
  have hO2 := pCore_two_quotient_eq_bot ↥G₁
  have hY'n : (Y.subgroupOf G₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYG).mpr hYN
  set Ŷ := (Y.subgroupOf G₁).map π with hŶdef
  have hŶn : Ŷ.Normal := hY'n.map π hπs
  have hO2Y : CFSG.pCore 2 ↥Ŷ = ⊥ := by
    have hc : (CFSG.pCore 2 ↥Ŷ).Characteristic := pCore_characteristic' 2 ↥Ŷ
    have hle := (CFSG.LieType.BorelTits.le_pCore 2 (normal_map_of_characteristic hŶn hc)
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥Ŷ)).map Ŷ.subtype)).trans_eq
        (SecA.open_pCore_eq 2 _)
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Ŷ.subtype_injective] at hle
    exact hle
  set Ph := (P.subgroupOf G₁).map π with hPhdef
  set Xh := (X.subgroupOf G₁).map π with hXhdef
  have hXhodd : Odd (Nat.card Xh) := by
    have h1 : Nat.card Xh ∣ Nat.card ↥(X.subgroupOf G₁) := Subgroup.card_map_dvd _ π
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv] at h1
    exact Odd.of_dvd_nat hXodd h1
  have hPh2 : IsPGroup 2 Ph := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm).map π
  have hPhX : ⁅Ph, Xh⁆ = Ph := by
    rw [hPhdef, hXhdef, ← Subgroup.map_commutator, commutator_subgroupOf hPG hXG, hPX]
  have hΦ' : frattiniIn Ph = ⊥ :=
    C2Nine.frattiniIn_eq_bot_of_isElemAbelian (isElemAbelian_map_of_frattini hP2 hΦ)
  have hA := a126_one (H := ⊤) (X := Xh) (V := Ph) le_top (opResidual_eq_self_of_odd hXhodd)
    le_top hPh2 hPhX (fun p hp hp2 => csSup_le' fun r hr => by
      obtain ⟨E, -, hE, hEc⟩ := hr
      exact le_two_of_elemAbelian_quotient hp hp2 (hrank p hp hp2) hE hEc) hΦ'
  have hFle : (CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype ≤
      fusionOddCoreOf (⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)) := by
    have hNn := normal_map_of_characteristic hŶn
      (CFSG.fittingSubgroup_characteristic (G := ↥Ŷ))
    have hNnil : Group.IsNilpotent ↥((CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype) :=
      Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ Ŷ.subtype_injective)
    have hNodd := odd_card_of_isNilpotent_of_normal hO2 hNn hNnil
    intro z hz
    refine ⟨⟨z, trivial⟩, ?_, rfl⟩
    refine le_sSup (s := {M : Subgroup ↥(⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)) |
      M.Normal ∧ Odd (Nat.card M)})
      (a := ((CFSG.fittingSubgroup ↥Ŷ).map Ŷ.subtype).subgroupOf ⊤) ⟨hNn.subgroupOf _, ?_⟩ hz
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv]
    exact hNodd
  rw [Subgroup.commutator_le]
  intro p hp y hy
  have hpPh : π ⟨p, hPG hp⟩ ∈ Ph := ⟨⟨p, hPG hp⟩, hp, rfl⟩
  let φ : MulAut ↥Ŷ := MulAut.conjNormal (π ⟨p, hPG hp⟩)
  have hφ_apply : ∀ z : ↥Ŷ, ((φ z : ↥Ŷ) : ↥G₁ ⧸ CFSG.pCore 2 ↥G₁) =
      π ⟨p, hPG hp⟩ * z * (π ⟨p, hPG hp⟩)⁻¹ := fun z => MulAut.conjNormal_apply _ _
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hφk : φ ^ 2 ^ k = 1 := by
    have h1 : (π ⟨p, hPG hp⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨p, hPG hp⟩ : ↥G₁) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    change (MulAut.conjNormal (π ⟨p, hPG hp⟩)) ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hcomm : ∀ z ∈ fusionOddCoreOf (⊤ : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)),
      π ⟨p, hPG hp⟩ * z * (π ⟨p, hPG hp⟩)⁻¹ = z := fun z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp (hA hpPh) z hz).symm, mul_inv_cancel_right]
  have hfixF : CFSG.fittingSubgroup ↥Ŷ ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) :=
    fun z hz => by
      show φ z = z
      exact Subtype.ext ((hφ_apply z).trans (hcomm _ (hFle ⟨z, hz, rfl⟩)))
  have hfixE : CFSG.layer ↥Ŷ ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) := by
    intro z hz
    show φ z = z
    have hz' := layer_le_perfectCore hz
    have hzc : (z : ↥G₁ ⧸ CFSG.pCore 2 ↥G₁) ∈ perfectCore Ŷ := by
      have := Subgroup.mem_map_of_mem Ŷ.subtype hz'
      rwa [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    have hzc' : (z : ↥G₁ ⧸ CFSG.pCore 2 ↥G₁) ∈ (perfectCore (Y.subgroupOf G₁)).map π := by
      rw [map_perfectCore]
      exact hzc
    rw [← SecA.perfectCore_subgroupOf hYG] at hzc'
    obtain ⟨w, hw, hwz⟩ := hzc'
    refine Subtype.ext ((hφ_apply z).trans ?_)
    rw [← hwz]
    have hc : p * w * p⁻¹ * (w : G)⁻¹ ∈ pCoreOf 2 G₁ := by
      have := Subgroup.commutator_le.mp hPY p hp w hw
      rwa [commutatorElement_def] at this
    have h1 : π (⟨p, hPG hp⟩ * w * (⟨p, hPG hp⟩ : ↥G₁)⁻¹ * w⁻¹) = 1 := (hker _).mpr hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hfix : ∀ z ∈ CFSG.generalizedFitting ↥Ŷ, φ z = z := fun z hz =>
    (sup_le hfixF hfixE : CFSG.generalizedFitting ↥Ŷ ≤ _) hz
  have hφ1 := mulAut_eq_one_of_fixes_generalizedFitting hO2Y φ hφk hfix
  have hyŶ : π ⟨y, hYG hy⟩ ∈ Ŷ := ⟨⟨y, hYG hy⟩, hy, rfl⟩
  have h2 : π ⟨p, hPG hp⟩ * π ⟨y, hYG hy⟩ * (π ⟨p, hPG hp⟩)⁻¹ = π ⟨y, hYG hy⟩ := by
    rw [← hφ_apply ⟨_, hyŶ⟩, hφ1]
    rfl
  have h3 : π (⟨p, hPG hp⟩ * ⟨y, hYG hy⟩ * (⟨p, hPG hp⟩ : ↥G₁)⁻¹ *
      (⟨y, hYG hy⟩ : ↥G₁)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2, mul_inv_cancel]
  rw [commutatorElement_def]
  exact (hker _).mp h3

end CFSG.Quasithin.Vol2.Ch11.SecD
