module

public import CFSG.Quasithin.EmptyFaithful.S152UBase
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.S152UGen2
public import CFSG.Quasithin.EmptyFaithful.S152UOm4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Small

variable {A : Type*} [Group A]

theorem comm_of_card_dvd_five {E : Subgroup A} (h : Nat.card E ∣ 5) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | h5
  · intro x hx y hy
    have : E = ⊥ := Subgroup.card_eq_one.mp h1
    rw [this, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : IsCyclic E := isCyclic_of_prime_card h5
    obtain ⟨g, hg⟩ := hc.exists_generator
    intro x hx y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have : (⟨x, hx⟩ : E) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    exact congrArg Subtype.val this

theorem exists_zpowers_eq_of_card_two {B : Subgroup A} (h : Nat.card B = 2) :
    ∃ b : A, b ≠ 1 ∧ b ^ 2 = 1 ∧ B = Subgroup.zpowers b := by
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have hne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha2 : a ^ 2 = 1 := by
    have := pow_card_eq_one' (G := B) (x := a)
    rwa [h] at this
  have hb1 : (a : A) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  have hb2 : (a : A) ^ 2 = 1 := by
    have := congrArg Subtype.val ha2
    simpa using this
  have hord : orderOf (a : A) = 2 := orderOf_eq_prime hb2 hb1
  refine ⟨a, hb1, hb2, ?_⟩
  have hle : Subgroup.zpowers (a : A) ≤ B := Subgroup.zpowers_le.mpr a.2
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, hord, h]

theorem eq_one_or_eq_of_mem_zpowers {b x : A} (hb : b ^ 2 = 1) (hx : x ∈ Subgroup.zpowers b) :
    x = 1 ∨ x = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hb, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hb, one_zpow, one_mul, zpow_one]

end Small

section Struct

variable {G : Type} [Group G] [Finite G]
variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem isElemAbelian_V152 (hs : Setting152 T Mc M) : IsElemAbelian 2 (V154 T Mc M) :=
  isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hs.qtfe hs.mf.1.1)

theorem om4Facts_of152 (hOm : Om4FactsStatement) {M V : Subgroup G}
    (h : IsOmegaFourPlusOn M V) : ∃ hV : IsElemAbelian 2 V, Om4Facts (autI hV M) := by
  obtain ⟨hV, h'⟩ := h
  exact ⟨hV, hOm (IntMod V hV) (autI hV M) h'⟩

theorem om4_card152 (hOm : Om4FactsStatement) {M V : Subgroup G} (h : IsOmegaFourPlusOn M V) :
    Nat.card (autOn M V) = 36 ∧ Nat.card (oTwoUpper (autOn M V)) = 9 := by
  obtain ⟨hV, hF⟩ := om4Facts_of152 hOm h
  exact ⟨hF.card_eq, hF.card_oTwoUpper⟩

theorem om4_stab152 (hOm : Om4FactsStatement) {M P V : Subgroup G} (h : IsOmegaFourPlusOn M V)
    {B A : Subgroup (MulAut V)} (hBP : B ≤ autOn P V) (hBM : B ≤ autOn M V)
    (hB2 : Nat.card B = 2)
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ e ∈ oTwoUpper (autOn M V), b * e = e * b → e = 1)
    (hAE : A ≤ oTwoUpper (autOn M V)) (hAne : A ≠ ⊥)
    (hAn : ¬ ∀ g ∈ autOn M V, ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    ∃ z : V, (z : G) ≠ 1 ∧ (z : G) ∈ ⁅V, preOn P V B⁆ ∧
      (∀ g ∈ autOn M V, g z = z ↔ g ∈ A ⊔ B) ∧
      ∃ t ∈ autOn M V, (∀ b ∈ B, t * b = b * t) ∧ t z ≠ z := by
  obtain ⟨hV, hF⟩ := om4Facts_of152 hOm h
  obtain ⟨z, hz1, hzc, hzs, t, ht, htB, htz⟩ := hF.stab B A hBM hB2 hfpf hAE hAne hAn
  exact ⟨z, fun h' => hz1 (Subtype.ext h'),
    coe_mem_commutator_of_mem_commV hV hBP hzc, hzs, t, ht, htB, htz⟩

theorem preOn_le_centralizer_zS (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    preOn T (V154 T Mc M) B₀ ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  have hV := isElemAbelian_V152 hs
  let _ : CommGroup (V154 T Mc M) := commGroupOfElemAbelian hV
  obtain ⟨b, -, hb2, hB₀eq⟩ := exists_zpowers_eq_of_card_two hB₀.2.1
  have hV2 : ∀ v : V154 T Mc M, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hquad : commV B₀ ≤ fixV B₀ := by
    rw [hB₀eq]
    exact commV_zpowers_le_fixV hV2 hb2
  intro p hp
  have hzcent : ⁅V154 T Mc M, preOn T (V154 T Mc M) B₀⁆ ≤ Subgroup.centralizer ({p} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv p' hp'
    obtain ⟨hp'T, hp'N, hp'B⟩ := mem_preOn.mp hp'
    obtain ⟨hpT, hpN, hpB⟩ := mem_preOn.mp hp
    let vv : V154 T Mc M := ⟨v, hv⟩
    let c : V154 T Mc M := conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ * vv
    have hc : c ∈ commV B₀ := by
      have : c = conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ * (vv⁻¹)⁻¹ := by simp [c]
      rw [this]
      exact Subgroup.subset_closure ⟨_, hp'B, vv⁻¹, rfl⟩
    have hfix : conjAct (V154 T Mc M) ⟨p, hpN⟩ c = c := hquad hc _ hpB
    have h1 : ((conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ : V154 T Mc M) : G) = p' * v⁻¹ * p'⁻¹ :=
      conj_coe_apply (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹
    have hcG : (c : G) = (p' * v⁻¹ * p'⁻¹) * v := by
      show ((conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ : V154 T Mc M) : G) * (v : G) = _
      rw [h1]
    have hcomm : (⁅v, p'⁆ : G) = (c : G) := by
      rw [hcG, commutatorElement_def]
      have hvu : v * (p' * v⁻¹ * p'⁻¹) = (p' * v⁻¹ * p'⁻¹) * v := by
        have := congrArg Subtype.val (mul_comm vv (conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹))
        rw [show ((vv * conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ : V154 T Mc M) : G) =
          v * ((conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ : V154 T Mc M) : G) from rfl,
          show ((conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ * vv : V154 T Mc M) : G) =
          ((conjAct (V154 T Mc M) ⟨p', hp'N⟩ vv⁻¹ : V154 T Mc M) : G) * v from rfl, h1] at this
        exact this
      calc v * p' * v⁻¹ * p'⁻¹ = v * (p' * v⁻¹ * p'⁻¹) := by group
        _ = _ := hvu
    have hcoe : p * (c : G) * p⁻¹ = c := by
      have := conj_coe_apply (V154 T Mc M) ⟨p, hpN⟩ c
      rw [hfix] at this
      exact this.symm
    rw [Subgroup.mem_centralizer_singleton_iff, hcomm]
    calc (c : G) * p = (p * (c : G) * p⁻¹) * p := by rw [hcoe]
      _ = p * c := by group
  intro z hz
  exact Subgroup.mem_centralizer_singleton_iff.mp (hzcent hz)

theorem preOn_le_S152 (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    preOn T (V154 T Mc M) B₀ ≤ sOf152 T Mc M B₀ :=
  fun _ hp => ⟨(mem_preOn.mp hp).1, preOn_le_centralizer_zS hs hB₀ hp⟩

theorem inf_centralizer_le_S152 (hs : Setting152 T Mc M) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ sOf152 T Mc M B₀ := fun _ hx =>
  ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (zS_le_V152 hs B₀)) hx.2⟩

theorem B₀_le_autOn_S152 (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    B₀ ≤ autOn (sOf152 T Mc M B₀) (V154 T Mc M) := by
  intro x hx
  obtain ⟨p, hpN, hpT, hpx⟩ := mem_autOn_iff_exists.mp (hB₀.1 hx)
  have hpP : p ∈ preOn T (V154 T Mc M) B₀ := mem_preOn.mpr ⟨hpT, hpN, by rw [hpx]; exact hx⟩
  rw [← hpx]
  exact mem_autOn_of_mem hpN (preOn_le_S152 hs hB₀ hpP)

theorem oTwoUpper_Mb_odd_comm (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    Odd (Nat.card (oTwoUpper (autOn M (V154 T Mc M)))) ∧
      ∀ x ∈ oTwoUpper (autOn M (V154 T Mc M)), ∀ y ∈ oTwoUpper (autOn M (V154 T Mc M)),
        x * y = y * x := by
  rcases hD.h17.1 with ⟨⟨e⟩⟩ | h
  · have h20 : Nat.card (autOn M (V154 T Mc M)) = 20 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_sz_zero
    have h5 := card_oTwoUpper_dvd_five h20
    exact ⟨Odd.of_dvd_nat (by decide) h5, comm_of_card_dvd_five h5⟩
  · have h9 := (om4_card152 hOm h).2
    refine ⟨by rw [h9]; decide, ?_⟩
    have h32 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 3 ^ 2 := by rw [h9]; norm_num
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) h32
    intro x hx y hy
    have := mul_comm' (⟨x, hx⟩ : oTwoUpper (autOn M (V154 T Mc M))) ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem B₀_le_autOn_M152 (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    B₀ ≤ autOn M (V154 T Mc M) := hB₀.1.trans (A4.autOn_mono (T_le_M152 hs))

theorem oddCoreIn_Mb_eq (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    oddCoreIn (autOn M (V154 T Mc M)) = oTwoUpper (autOn M (V154 T Mc M)) :=
  oddCoreIn_eq_oTwoUpper (oTwoUpper_Mb_odd_comm hD hOm).1

theorem B₀_inverts (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    ∀ b ∈ B₀, b ≠ 1 → ∀ e ∈ oTwoUpper (autOn M (V154 T Mc M)), b * e * b⁻¹ = e⁻¹ := by
  obtain ⟨hodd, hab⟩ := oTwoUpper_Mb_odd_comm hD hOm
  obtain ⟨b, hb1, hb2, hB₀eq⟩ := exists_zpowers_eq_of_card_two hB₀.2.1
  have hcomm : ⁅oTwoUpper (autOn M (V154 T Mc M)), B₀⁆ = oTwoUpper (autOn M (V154 T Mc M)) := by
    have := hB₀.2.2
    rw [oddCoreIn_Mb_eq hD hOm] at this
    exact this.symm
  have hBb : ∀ x ∈ B₀, x = 1 ∨ x = b := fun x hx =>
    eq_one_or_eq_of_mem_zpowers hb2 (hB₀eq ▸ hx)
  have hbB₀ : b ∈ B₀ := hB₀eq ▸ Subgroup.mem_zpowers b
  have hbE : b ∈ Subgroup.normalizer (oTwoUpper (autOn M (V154 T Mc M)) :
      Set (MulAut (V154 T Mc M))) :=
    le_normalizer_oTwoUpper _ (B₀_le_autOn_M152 hs hB₀ hbB₀)
  intro b' hb' hb'1
  have : b' = b := (hBb b' hb').resolve_left hb'1
  subst this
  exact inverts_of_commutator_eq_of_comm hb2 hbE hBb hab hcomm

theorem B₀_fpf (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    ∀ b ∈ B₀, b ≠ 1 → ∀ e ∈ oTwoUpper (autOn M (V154 T Mc M)), b * e = e * b → e = 1 := by
  obtain ⟨hodd, hab⟩ := oTwoUpper_Mb_odd_comm hD hOm
  obtain ⟨b, hb1, hb2, hB₀eq⟩ := exists_zpowers_eq_of_card_two hB₀.2.1
  have hcomm : ⁅oTwoUpper (autOn M (V154 T Mc M)), B₀⁆ = oTwoUpper (autOn M (V154 T Mc M)) := by
    have := hB₀.2.2
    rw [oddCoreIn_Mb_eq hD hOm] at this
    exact this.symm
  have hBb : ∀ x ∈ B₀, x = 1 ∨ x = b := fun x hx =>
    eq_one_or_eq_of_mem_zpowers hb2 (hB₀eq ▸ hx)
  have hbB₀ : b ∈ B₀ := hB₀eq ▸ Subgroup.mem_zpowers b
  have hbE : b ∈ Subgroup.normalizer (oTwoUpper (autOn M (V154 T Mc M)) :
      Set (MulAut (V154 T Mc M))) :=
    le_normalizer_oTwoUpper _ (B₀_le_autOn_M152 hs hB₀ hbB₀)
  intro b' hb' hb'1
  have : b' = b := (hBb b' hb').resolve_left hb'1
  subst this
  exact eq_one_of_commutator_eq_of_comm hb2 hbE hBb hab hcomm hodd

theorem autOn_M_eq_sup152 (hs : Setting152 T Mc M) :
    autOn M (V154 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)) ⊔ autOn T (V154 T Mc M) := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  have hMeq : M = oTwoUpper M ⊔ T :=
    eq_oTwoUpper_sup_of_isSylowTwoOf (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM)
  have h1 : autOn M (V154 T Mc M) = autOn (oTwoUpper M ⊔ T) (V154 T Mc M) :=
    congrArg (fun X => autOn X (V154 T Mc M)) hMeq
  calc autOn M (V154 T Mc M) = autOn (oTwoUpper M ⊔ T) (V154 T Mc M) := h1
    _ = autOn (oTwoUpper M) (V154 T Mc M) ⊔ autOn T (V154 T Mc M) :=
        autOn_sup ((oTwoUpper_le M).trans hMV) hTV
    _ = oTwoUpper (autOn M (V154 T Mc M)) ⊔ autOn T (V154 T Mc M) := by
        rw [A4.oTwoUpper_autOn hMV]

theorem normalizer_autS_le_autT (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    ∀ g ∈ autOn M (V154 T Mc M),
      g ∈ Subgroup.normalizer (autOn (sOf152 T Mc M B₀) (V154 T Mc M) :
        Set (MulAut (V154 T Mc M))) → g ∈ autOn T (V154 T Mc M) := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  obtain ⟨hodd, hab⟩ := oTwoUpper_Mb_odd_comm hD hOm
  obtain ⟨b, hb1, hb2, hB₀eq⟩ := exists_zpowers_eq_of_card_two hB₀.2.1
  have hbB₀ : b ∈ B₀ := hB₀eq ▸ Subgroup.mem_zpowers b
  have hMb := autOn_M_eq_sup152 hs
  have hTb_le : autOn T (V154 T Mc M) ≤ autOn M (V154 T Mc M) := A4.autOn_mono hTM
  have hTbN : autOn T (V154 T Mc M) ≤
      Subgroup.normalizer (oTwoUpper (autOn M (V154 T Mc M)) : Set (MulAut (V154 T Mc M))) :=
    hTb_le.trans (le_normalizer_oTwoUpper _)
  have hdec : ∀ g ∈ autOn M (V154 T Mc M), ∃ e ∈ oTwoUpper (autOn M (V154 T Mc M)),
      ∃ t ∈ autOn T (V154 T Mc M), e * t = g := by
    intro g hg
    rw [hMb] at hg
    exact (mem_sup_iff_of_le_normalizer hTbN).mp hg
  have hEn : ∀ g ∈ autOn M (V154 T Mc M), ∀ e ∈ oTwoUpper (autOn M (V154 T Mc M)),
      g * e * g⁻¹ ∈ oTwoUpper (autOn M (V154 T Mc M)) := fun g hg e he =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hg) e).mp he
  have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := isPGroup_autOn hs.qtfe.sylow.1 hTV
  have hSTb : autOn (sOf152 T Mc M B₀) (V154 T Mc M) ≤ autOn T (V154 T Mc M) :=
    A4.autOn_mono S_le_T152
  have hidx : (autOn (sOf152 T Mc M B₀) (V154 T Mc M)).relIndex (autOn T (V154 T Mc M)) = 2 := by
    rw [relIndex_autOn S_le_T152 hTV (inf_centralizer_le_S152 hs B₀), hD.h17.2.2]
  have hSn : autOn T (V154 T Mc M) ≤
      Subgroup.normalizer (autOn (sOf152 T Mc M B₀) (V154 T Mc M) :
        Set (MulAut (V154 T Mc M))) := by
    have : ((autOn (sOf152 T Mc M B₀) (V154 T Mc M)).subgroupOf (autOn T (V154 T Mc M))).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSTb).mp this
  have hBS : b ∈ autOn (sOf152 T Mc M B₀) (V154 T Mc M) := B₀_le_autOn_S152 hs hB₀ hbB₀
  have hfpf := B₀_fpf hs hB₀ hD hOm b hbB₀ hb1
  exact normalizer_le_of_decomp hdec hTb_le hEn hodd hT2 hSTb hSn hBS hfpf

end Struct

end CFSG.Quasithin
