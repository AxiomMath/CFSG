module

public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.Background.E2Frattini
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem inputD14Solvable_holds :
    ∀ (A : Type) [Group A] [Finite A] (G₁ G₂ T V M₂ : Subgroup A) (h : D11Hyp G₁ G₂ T V M₂),
      V ≤ pCoreOf 2 G₂ →
      IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 →
      ¬ IsDualFFInt G₁ V h.reduced.2.2.1 →
      Group.IsSolvable G₂ → CharTwo G₂ →
      IsSylowTwoOf (pCoreOf 2 G₁) (oTwoUpper G₂ ⊔ pCoreOf 2 G₁) := by
  intro A _ _ G₁ G₂ T V M₂ h hVR₂ hchief hdual hsolv _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup A) : Set A) :=
    D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  set R := pCoreOf 2 G₁ with hRdef
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set P := oTwoUpper G₂ with hPdef
  have hRT : R ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₁
  have hRG₂ : R ≤ G₂ := hRT.trans h.sylow₂.1
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 G₁
  have hVR : V ≤ R :=
    le_pCoreOf_of_le_normalizer 2 h.reduced.1 h.reduced.2.1
      (B6.isPGroup_of_isElemAbelian h.reduced.2.2.1)
  have hRR₂ : ¬ R ≤ R₂ := by
    intro hle
    have hCR : R ⊓ R₂ = R := inf_eq_left.mpr hle
    rw [hCR] at hC
    have hR : R = ⊥ := h.no_normal R le_rfl
      ((Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 G₁).trans le_sup_left)).mpr
        (sup_le (le_normalizer_pCoreOf 2 G₁) hC))
    exact h.nontrivial (le_bot_iff.mp (hR ▸ hVR))
  have hmp : MinParabolic G₂ T M₂ := by
    refine ⟨h.sylow₂, fun hle => hRR₂ (hRT.trans ?_), h.unique_max⟩
    exact le_pCoreOf_of_le_normalizer 2 h.sylow₂.1 hle h.sylow₂.2.1
  have hPres : P = twoResidual G₂ := (F6.twoResidual_eq_oTwoUpper G₂).symm
  have hR₂P : ⁅R₂, P⁆ ≤ R ⊓ R₂ := by
    have hYG₂ : conjClosure R G₂ ≤ G₂ := conjClosure_le fun g hg r hr =>
      G₂.mul_mem (G₂.mul_mem hg (hRG₂ hr)) (G₂.inv_mem hg)
    rcases hmp.le_kerIn_or_twoResidual_le hYG₂ (le_normalizer_conjClosure R G₂) with hker | hres
    · exact absurd (hmp.le_pCoreOf_of_isPGroup_of_le_kerIn hR2
        ((le_conjClosure R G₂).trans hker)) hRR₂
    rw [← hPres] at hres
    refine (Subgroup.commutator_mono le_rfl hres).trans ?_
    refine D14.commutator_le_closure (S := {x | ∃ g ∈ G₂, ∃ r ∈ R, g * r * g⁻¹ = x})
      (hYG₂.trans hC) ?_
    rintro x hx _ ⟨g, hg, r, hr, rfl⟩
    have hx' : g⁻¹ * x * g ∈ R₂ :=
      (Subgroup.mem_normalizer_iff''.mp (le_normalizer_pCoreOf 2 G₂ hg) x).mp hx
    have hxG₁ : g⁻¹ * x * g ∈ G₁ :=
      ((B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂).trans h.sylow₁.1) hx'
    have hc : ⁅g⁻¹ * x * g, r⁆ ∈ R ⊓ R₂ := by
      refine ⟨?_, ?_⟩
      · have h1 : (g⁻¹ * x * g) * r * (g⁻¹ * x * g)⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hxG₁) r).mp hr
        rw [commutatorElement_def]
        exact R.mul_mem h1 (R.inv_mem hr)
      · have h1 : r * (g⁻¹ * x * g)⁻¹ * r⁻¹ ∈ R₂ :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ (hRG₂ hr)) _).mp
            (R₂.inv_mem hx')
        have e : ⁅g⁻¹ * x * g, r⁆ = (g⁻¹ * x * g) * (r * (g⁻¹ * x * g)⁻¹ * r⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact R₂.mul_mem hx' h1
    have e : ⁅x, g * r * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, r⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hC hg) _).mp hc
  obtain ⟨p, hp, hp2, hpow⟩ := hmp.exists_prime_pow_mem_pCoreOf hsolv
  have hS : IsSylowTwoOf (P ⊓ R₂) P := by
    obtain ⟨S₀, hS₀, -⟩ := B6.exists_isSylowTwoOf_ge (J := P) (X := ⊥) IsPGroup.of_bot bot_le
    have hS₀R₂ : S₀ ≤ R₂ := by
      intro x hx
      obtain ⟨a, ha⟩ := hpow x (hPres ▸ hS₀.1 hx)
      obtain ⟨b, hb⟩ := hS₀.2.1 ⟨x, hx⟩
      have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have hcop : Nat.Coprime (p ^ a) (orderOf x) :=
        Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb')
          (Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
      exact (Subgroup.zpowers_le.mpr ha) (A4.mem_zpowers_pow_of_coprime hcop)
    refine ⟨inf_le_left, (pCoreOf_isPGroup 2 G₂).to_le inf_le_right, fun h2 => hS₀.2.2 ?_⟩
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left P (le_inf hS₀.1 hS₀R₂))
  have hPC : P ≤ Subgroup.normalizer ((R ⊓ R₂ : Subgroup A) : Set A) :=
    (oTwoUpper_le G₂).trans hC
  have hSC : P ⊓ R₂ ≤ R ⊓ R₂ :=
    D14.le_of_commutator_le hS hPC ((Subgroup.commutator_mono inf_le_right le_rfl).trans hR₂P)
  refine ⟨le_sup_right, hR2, fun h2 => hS.2.2 ?_⟩
  have hRP : R ≤ Subgroup.normalizer (P : Set A) := hRG₂.trans (le_normalizer_oTwoUpper G₂)
  have e1 : (R ⊓ P).relIndex P = R.relIndex (R ⊔ P) := B6.relIndex_inf_eq_relIndex_sup hRP
  have h3 : 2 ∣ (R ⊓ P).relIndex P := by
    rw [e1, sup_comm]
    exact h2
  exact h3.trans (Subgroup.relIndex_dvd_of_le_left P (le_inf (hSC.trans inf_le_left) inf_le_left))

end CFSG.Quasithin.EmptyFaithfulMultiple
