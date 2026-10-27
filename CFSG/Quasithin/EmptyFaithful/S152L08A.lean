module

public import CFSG.Quasithin.EmptyFaithful.S152FinShape
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152L08

section Chief

variable {H U L N : Subgroup G}

theorem cSecIn_conj_mem (hs : IsChiefStep H U L N) {h c : G} (hh : h ∈ H)
    (hc : c ∈ cSecIn H L N) : h * c * h⁻¹ ∈ cSecIn H L N := by
  have hN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N := hs.1.2
  have hL : ∀ g ∈ H, ∀ x ∈ L, g * x * g⁻¹ ∈ L := hs.2.1.2
  unfold cSecIn at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem f hf =>
    apply Subgroup.subset_closure
    refine ⟨H.mul_mem (H.mul_mem hh hf.1) (H.inv_mem hh), fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h ∈ N := by simpa using hN h⁻¹ (H.inv_mem hh) x hx
    have h1 := hL h hh _ (hf.2 _ hx')
    have e : h * (f * (h⁻¹ * x * h) * f⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ =
        (h * f * h⁻¹) * x * (h * f * h⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h1
  | one => simp
  | mul a b _ _ ha hb =>
    have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem normalizes_cSecIn (hs : IsChiefStep H U L N) :
    H ≤ Subgroup.normalizer (cSecIn H L N : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => cSecIn_conj_mem hs hh hx, fun hx => ?_⟩
  have := cSecIn_conj_mem hs (H.inv_mem hh) hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem not_oTwoUpper_le_of_quotIsoWith [Finite G] {C J : Subgroup G} {X Y : Type*} [Group X]
    [Group Y] (h : QuotIsoWith H C J X Y) (hX : 3 ∣ Nat.card X) : ¬ oTwoUpper H ≤ C := by
  intro hle
  obtain ⟨φ, hφ, hker, -⟩ := h
  have hfin : Finite X := Finite.of_surjective φ hφ
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 X := by
    intro x
    obtain ⟨y, rfl⟩ := hφ x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H y.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : y ^ 2 ^ k ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hle hk
    exact this
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at hX
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hX
  omega

theorem not_oTwoUpper_le_cSecIn [Finite G] {L N : Subgroup G} {H U : Subgroup G}
    (_hs : IsChiefStep H U L N) (hshape : ChiefFactorShape H L N) :
    ¬ oTwoUpper H ≤ cSecIn H L N := by
  obtain ⟨_, h | h | h | h⟩ := hshape
  · refine not_oTwoUpper_le_of_quotIsoWith h.1 ?_
    rw [Nat.card_perm]
    simp [Nat.factorial]
  · refine not_oTwoUpper_le_of_quotIsoWith h.1 ?_
    rw [S152Fin.card_Perm_five]
    norm_num
  · refine not_oTwoUpper_le_of_quotIsoWith h.1 ?_
    rw [S152Fin.card_Wr]
    norm_num
  · refine not_oTwoUpper_le_of_quotIsoWith h.1 ?_
    rw [S152Fin.card_Wr_five]
    norm_num

theorem nonempty_oTwoQuot_equiv {H J : Subgroup G} {X Y : Type*} [Group X] [Group Y]
    (h : QuotIsoWith H (pCoreOf 2 H) J X Y) : Nonempty (OTwoQuot H ≃* X) := by
  obtain ⟨φ, hφ, hker, -⟩ := h
  have hker' : φ.ker = CFSG.Open.pCore 2 ↥H := by
    rw [hker, S152Fin.pCoreOf_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end Chief

section Main

variable [Finite G]

open S152N

theorem minParabolic_of_hStar {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (hN : Subgroup.normalizer (T : Set G) ≤ M) :
    MinParabolic H T (H ⊓ M) := by
  obtain ⟨S, hS⟩ := hs.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hs.mf.1.1.2
  have hH' : IsHStar (S : Subgroup G) M H := hS ▸ hH
  refine ⟨isSylowTwoOf_hStar hs hH, hH.not_le_normalizer hN, ?_⟩
  have := hH'.isUniqueMaxOver S hSM
  rwa [hS] at this

theorem cSecIn_eq_pCoreOf {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) {Y₁ : Subgroup G} (h15207 : Lemma15207Concl T Mc M Y₁)
    {U L N : Subgroup G} (hU : IsElemAbelian 2 U) (hst : IsChiefStep H U L N)
    (hshape : ChiefFactorShape H L N) : cSecIn H L N = pCoreOf 2 H := by
  have hQC : pCoreOf 2 H ≤ cSecIn H L N := S152Fin.pCoreOf_le_cSecIn hU hst
  by_contra hne
  have hCH : cSecIn H L N ≤ H := S152Fin.cSecIn_le_left H L N
  have hCn : H ≤ Subgroup.normalizer (cSecIn H L N : Set G) := normalizes_cSecIn hst
  have hK : ¬ twoResidual H ≤ cSecIn H L N := by
    rw [F6.twoResidual_eq_oTwoUpper]
    exact not_oTwoUpper_le_cSecIn hst hshape
  have hmp := minParabolic_of_hStar hs hH h1519.seven_normalizer
  have hCker : cSecIn H L N ≤ kerIn (H ⊓ M) H :=
    hmp.le_kerIn_of_not_twoResidual_le hCH hCn hK
  have hCM : cSecIn H L N ≤ H ⊓ M := hCker.trans kerIn_le
  have hX1 : oTwoUpper (cSecIn H L N) ≠ ⊥ := by
    intro hXbot
    apply hne
    have hp : IsPGroup 2 (cSecIn H L N) := by
      intro c
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (cSecIn H L N) c.2
      refine ⟨k, ?_⟩
      apply Subtype.ext
      rw [hXbot, Subgroup.mem_bot] at hk
      simpa using hk
    exact le_antisymm (le_pCoreOf_of_le_normalizer 2 hCH hCn hp) hQC
  have hXX : oTwoUpper (cSecIn H L N) = oTwoUpper (oTwoUpper (cSecIn H L N)) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => ?_) (oTwoUpper_le _)
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩
  have hXle : oTwoUpper (cSecIn H L N) ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (((oTwoUpper_le _).trans hCM).trans inf_le_right)
      ((oTwoUpper_mono hCM).trans (h1519.four H hH))
  have hHX : H ≤ Subgroup.normalizer (oTwoUpper (cSecIn H L N) : Set G) :=
    hCn.trans (normalizer_le_normalizer_oTwoUpper _)
  have hTH : T ≤ H := hH.1.1
  have hNM := h15207.normalizer_le _ hX1 hXX hXle (hTH.trans hHX)
  exact hH.2.1 (hHX.trans hNM)

end Main

end S152L08

end CFSG.Quasithin
