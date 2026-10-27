module

public import CFSG.LocalAnalysis.StandardType.GGNbrCan
public import CFSG.LocalAnalysis.StandardType.GGTBWNormNbr
public import CFSG.LocalAnalysis.StandardType.GGHLDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggXFixedRefl_mem_ggHL_K {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} (hW : GGTBWNormInputNbr S) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K) (hnt : ggAutomizer K Bs ≠ ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥(ggGamma K hBsN).range ≃+ V) (φ : Λ → MulAut ↥(ggGamma K hBsN).range)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hA : ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hBsN).range =
      Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t) (hyB : y ∈ Bs)
    (hty : t ⟨y, hyB⟩ = ⟨y, hyB⟩) :
    ∃ g ∈ Subgroup.normalizer (Bs : Set G), ∃ hgK : g ∈ Subgroup.normalizer (K : Set G),
      (∀ b : ↥Bs, ((t b : ↥Bs) : G) = g * b * g⁻¹) ∧
      ∀ φ' : MulAut ↥(ggGamma K hBsN).range,
        (∀ a, ((φ' a : ↥(ggGamma K hBsN).range) : MulAut K) =
          K.normalizerMonoidHom ⟨g, hgK⟩ * a * (K.normalizerMonoidHom ⟨g, hgK⟩)⁻¹) →
        ggLin (p := p) ι φ' ∈ ggHL ι φ h α := by
  obtain ⟨hp, hBs, -, -, -⟩ := hH.1.tableB_facts
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨g, -, hgB, hg⟩ := ht
  have hgy : g * y * g⁻¹ = y := by
    have h2 := hg ⟨y, hyB⟩
    rw [hty] at h2
    exact h2.symm
  have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
    ggNbr_mem_normalizer hH hCent hnt hgB hgy
  refine ⟨g, hgB, hgK, hg, fun φ' hφ' => ?_⟩
  refine (hW G p B Bs x L D J y K hH hM hBsN Λ M C V ι φ h α hMw hC hpair hlin hA g hgB
    hgK φ' hφ').2 ?_
  have hinf : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggNbr_inf_centralizer hH hCent
  have hy1 : y ≠ 1 := hH.2.2.2.2.1.1.2.2.1
  have hy_mem : y ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
    rw [hinf]; exact Subgroup.mem_zpowers y
  have hkey : ∀ b : ↥Bs, φ' ((ggGamma K hBsN).rangeRestrict b) =
      (ggGamma K hBsN).rangeRestrict (t b) := by
    intro b
    apply Subtype.ext
    have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB b).mp b.2
    have htb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = t b := Subtype.ext (hg b).symm
    rw [hφ', MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict,
      ggGamma_conj_normalizer K hBsN ⟨g, hgK⟩ b hgb, htb]
  have htt : ∀ b : ↥Bs, t (t b) = b := fun b => by
    have := congrArg (fun f : MulAut ↥Bs => f b) htr.1
    simpa [pow_two] using this
  have hfixB : ∀ b : ↥Bs, ggGamma K hBsN (t b) = ggGamma K hBsN b → t b = b := by
    intro b hb
    set u : ↥Bs := t b * b⁻¹ with hu_def
    have hu1 : ggGamma K hBsN u = 1 := by
      rw [hu_def, map_mul, map_inv, hb, mul_inv_cancel]
    have h2 : (u : G) ∈ Bs ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨u.2, (ggGamma_eq_one_iff K hBsN u).mp hu1⟩
    rw [hinf] at h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    have hu : u = (⟨y, hyB⟩ : ↥Bs) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    have htu : t u = u := by rw [hu, map_zpow, hty]
    have htu' : t u = u⁻¹ := by rw [hu_def, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      calc u * u = u * t u := by rw [htu]
        _ = 1 := by rw [htu', mul_inv_cancel]
    have hup : u ^ p = 1 := Subtype.ext (by simpa using hBs.2 _ u.2)
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have ho : orderOf u = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hu2) hcop)
        (orderOf_dvd_of_pow_eq_one hup)
    have hu1' : u = 1 := orderOf_eq_one_iff.mp ho
    rw [hu_def, mul_inv_eq_one] at hu1'
    exact hu1'
  set E : Subgroup G := (ggFix t).map Bs.subtype with hE_def
  have hEBs : E ≤ Bs := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := hEBs.trans hBsN
  have hyE : y ∈ E := ⟨⟨y, hyB⟩, hty, rfl⟩
  have hq : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
    rw [hinf, Nat.card_zpowers]
    exact orderOf_eq_prime (hBs.2 y hy_mem.1) hy1
  have hqE : Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set G)) = p := by
    have hEq : E ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
      apply le_antisymm
      · calc E ⊓ Subgroup.centralizer (K : Set G)
            ≤ Bs ⊓ Subgroup.centralizer (K : Set G) := inf_le_inf_right _ hEBs
          _ = Subgroup.zpowers y := hinf
      · rw [Subgroup.zpowers_le]
        exact ⟨hyE, hy_mem.2⟩
    rw [hEq, Nat.card_zpowers]
    exact orderOf_eq_prime (hBs.2 y hy_mem.1) hy1
  have hcA := NbrU63.card_range_ggGamma_mul_card_inf (K := K) hBsN
  rw [hq] at hcA
  have hcE := NbrU63.card_range_ggGamma_mul_card_inf (Bs := E) (K := K) hEN
  rw [hqE] at hcE
  have hEF : Nat.card E = Nat.card {b : ↥Bs // t b = b} :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (ggFix t) Bs.subtype
      Bs.subtype_injective).toEquiv).symm
  have hfix : Nat.card {a : ↥(ggGamma K hBsN).range // φ' a = a} =
      Nat.card (ggGamma K hEN).range := by
    refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨(a.1 : MulAut K), ?_⟩) ⟨?_, ?_⟩)
    · obtain ⟨⟨_, b, rfl⟩, ha⟩ := a
      have hrr : (⟨ggGamma K hBsN b, b, rfl⟩ : ↥(ggGamma K hBsN).range) =
          (ggGamma K hBsN).rangeRestrict b := rfl
      rw [hrr, hkey] at ha
      have hb := hfixB b (congrArg Subtype.val ha)
      exact ⟨⟨b, ⟨b, hb, rfl⟩⟩, rfl⟩
    · intro a a' haa
      simp only [Subtype.mk.injEq] at haa
      exact Subtype.ext (Subtype.ext haa)
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩⟩, rfl⟩
      refine ⟨⟨(ggGamma K hBsN).rangeRestrict b, ?_⟩, rfl⟩
      rw [hkey]
      exact congrArg _ hb
  refine ⟨?_, ?_⟩
  · refine MulEquiv.ext fun a => ?_
    obtain ⟨b, rfl⟩ := (ggGamma K hBsN).rangeRestrict_surjective a
    rw [pow_two, MulAut.mul_apply, hkey, hkey, htt, MulAut.one_apply]
  · rw [hfix]
    refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
    rw [hcE, hEF, htr.2, ← hcA]

end CFSG.StandardType
