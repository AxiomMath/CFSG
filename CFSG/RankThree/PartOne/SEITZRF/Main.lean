module

public import CFSG.RankThree.PartOne.SEITZRF.Chain
public import CFSG.RankThree.PartOne.SEITZRF.Embed
public import CFSG.RankThree.PartOne.SEITZRF.Fus
public import CFSG.RankThree.PartOne.SEITZRF.Unip
public import CFSG.RankThree.PartOne.SEITZRF.Rank1
public import CFSG.RankThree.PartOne.SEITZRF.SL2Max
public import CFSG.RankThree.PartOne.SEITZRF.SzMax
public import CFSG.RankThree.PartOne.SEITZ2.ReeOuter
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair)

open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

open CFSG.RankThree.PartOne.CTP (fixedSubgroup)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem card_eq_pow_fixSubfield (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hβ : orderOf β = p) :
    Nat.card K = Nat.card (fixSubfield β) ^ p ∧ ∃ μ : Kˣ, β (μ : K) ≠ μ := by
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK β
  rw [hβ] at hdvd hcard
  have hpow : Nat.card K = Nat.card (fixSubfield β) ^ p := by
    rw [hcard, hK, ← pow_mul, Nat.div_mul_cancel hdvd]
  refine ⟨hpow, ?_⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ c : K, β c = c := by
    intro c
    by_cases hc : c = 0
    · rw [hc, map_zero]
    · exact hcon (Units.mk0 c hc)
  have h1 : β = 1 := RingEquiv.ext hall
  rw [h1, orderOf_one] at hβ
  exact hp.one_lt.ne' hβ.symm

theorem r1Dich (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk4 : 4 ≤ Nat.card (fixSubfield β)) : R1Dich K a β := by
  have : CharP K 2 := ‹CharP K F4.prime›
  intro Y hY hRY hne
  exact eq_rankOneGroupOne_of_not_le hK β
    (fun M hM hMne => sl2Sub_maximal hp hp2 (card_eq_pow_fixSubfield hK β hp hβ).1 hk4 hM hMne)
    hY hRY hne

theorem r2Dich_odd (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk2 : 2 < Nat.card (fixSubfield β)) : R2Dich K a β := by
  intro Y hY hRY hne
  exact eq_rankOneGroupTwo_of_not_le ha hK β
    (fun M hM hMne => suzuki_subfield_maximal_odd hK β hp hp2 hβ hk2 hM hMne) hY hRY hne

theorem r1Dich2_of_r1Dich (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : K ≃+* K}
    (hd : R1Dich K a β) : R1Dich2 K a β := fun Y hY hRY s hs hsY =>
  hd Y hY hRY fun hle => hs ((sylowA_mem_Rf_iff hK β s).1 (hle hsY))

theorem r2Dich2_of_r2Dich (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : K ≃+* K}
    (hd : R2Dich K a β) : R2Dich2 K a β := fun Y hY hRY b c hbc hbcY =>
  hd Y hY hRY fun hle => hbc ((Unip.sylowB_mem_Rf_iff hK β b c).1 (hle hbcY))

theorem Y1_le_Rf (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (hd1 : R1Dich K a β) (hd2 : R2Dich K a β) {p : ℕ} (hp : p.Prime)
    (hβ : orderOf β = p) {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hnot : ¬ F4.reeGamma K a ≤ H) : Y1 K a hK H ≤ Rf K a β := by
  by_contra hne
  obtain ⟨hKk, μ, hμ⟩ := card_eq_pow_fixSubfield hK β hp hβ
  have hY := hd1 (Y1 K a hK H) leviImage_le
    (fun x hx => inf_le_leviImage ⟨hx.1, hRH hx.2⟩) hne
  exact hnot (reeGamma_le_of_le_Y1 ha hK β (r1Dich2_of_r1Dich hK hd1) (r2Dich2_of_r2Dich hK hd2)
    hp hKk hRH hY.ge hμ)

theorem exists_mul_sylowA_of_conj
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {v : ModGL F4.tag K}
    (hv : v ∈ F4.reeFixedPosUnipotent K a) (c : K) :
    ∃ w ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
      v * sylowA a K c * v⁻¹ = w * sylowA a K c := by
  obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hv
  rw [sylowVec_eq_sylowA_mul]
  set w₀ := sylowV a K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
  have hw₀ : w₀ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  have hN := reeFixedPosUnipotent_le_normalizer (K := K) (a := a) ⟨0, by decide⟩
  have hAc : sylowA a K c ∈ F4.reeFixedPosUnipotent K a :=
    reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK c)
  have hA0 : sylowA a K (x 0) ∈ F4.reeFixedPosUnipotent K a :=
    reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK (x 0))
  set w₁ := w₀ * (sylowA a K c * w₀⁻¹ * (sylowA a K c)⁻¹) with hw₁
  have hw₁m : w₁ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    Subgroup.mul_mem _ hw₀ ((Subgroup.mem_normalizer_iff.1 (hN hAc) _).1 (Subgroup.inv_mem _ hw₀))
  refine ⟨sylowA a K (x 0) * w₁ * (sylowA a K (x 0))⁻¹,
    (Subgroup.mem_normalizer_iff.1 (hN hA0) _).1 hw₁m, ?_⟩
  have hcomm : sylowA a K (x 0) * sylowA a K c = sylowA a K c * sylowA a K (x 0) := by
    rw [sylowA_mul hK, sylowA_mul hK, add_comm]
  calc sylowA a K (x 0) * w₀ * sylowA a K c * (sylowA a K (x 0) * w₀)⁻¹ =
      sylowA a K (x 0) * w₁ * sylowA a K c * (sylowA a K (x 0))⁻¹ := by
        rw [hw₁]
        group
    _ = sylowA a K (x 0) * w₁ * (sylowA a K (x 0))⁻¹ *
          (sylowA a K (x 0) * sylowA a K c * (sylowA a K (x 0))⁻¹) := by group
    _ = sylowA a K (x 0) * w₁ * (sylowA a K (x 0))⁻¹ * sylowA a K c := by
        rw [hcomm]
        group

theorem Y2_le_Rf (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (hd1 : R1Dich K a β) (hd2 : R2Dich K a β) {p : ℕ} (hp : p.Prime)
    (hβ : orderOf β = p) {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hnot : ¬ F4.reeGamma K a ≤ H) : Y2 K a hK H ≤ Rf K a β := by
  by_contra hne
  obtain ⟨-, l, hl⟩ := card_eq_pow_fixSubfield hK β hp hβ
  have hY := hd2 (Y2 K a hK H) leviImage_le
    (fun x hx => inf_le_leviImage ⟨hx.1, hRH hx.2⟩) hne
  obtain ⟨-, v, hv, hvT⟩ := hY.ge (torusTwo_mem_rankOneGroupTwo' l)
  have hvU : v ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le _ hv
  set c : K := ((l⁻¹ : Kˣ) : K) ^ 2 ^ a * 1 with hc
  obtain ⟨w, hw, hwe⟩ := exists_mul_sylowA_of_conj hK hvU c
  have hA1 : sylowA a K 1 ∈ H := hRH ((sylowA_mem_Rf_iff hK β 1).2 (map_one β))
  have hmem : w * sylowA a K c ∈ H := by
    have h1 := H.mul_mem (H.mul_mem hvT hA1) (H.inv_mem hvT)
    have e : v * pairedTorusHom a (f4i 1) (f4i 2) l * sylowA a K 1 *
        (v * pairedTorusHom a (f4i 1) (f4i 2) l)⁻¹ = v * sylowA a K c * v⁻¹ := by
      rw [hc, ← torusTwo_conj_sylowA hK]
      group
    rwa [e, hwe] at h1
  have hY1 := Y1_le_Rf ha hK β hd1 hd2 hp hβ hRH hnot
    ⟨sylowA_mem_rankOneGroupOne' hK c, w, hw, hmem⟩
  rw [sylowA_mem_Rf_iff hK β c, hc, mul_one] at hY1
  apply hl
  have h' := eq_of_map_pow_two_pow_eq β a hY1
  have : ((l⁻¹ : Kˣ) : K) = (l : K)⁻¹ := Units.val_inv_eq_inv_val l
  rw [this, map_inv₀] at h'
  exact inv_injective h'

theorem map_eq_of_sylowA_mem_Y1 (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (hd1 : R1Dich2 K a β)
    (hd2 : R2Dich2 K a β) {p : ℕ} (hp : p.Prime) (hβ : orderOf β = p)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hnot : ¬ F4.reeGamma K a ≤ H) {s : K}
    (hs : sylowA a K s ∈ Y1 K a hK H) : β s = s := by
  by_contra hne
  obtain ⟨hKk, μ, hμ⟩ := card_eq_pow_fixSubfield hK β hp hβ
  have hY := hd1 (Y1 K a hK H) leviImage_le (fun x hx => inf_le_leviImage ⟨hx.1, hRH hx.2⟩) s
    hne hs
  exact hnot (reeGamma_le_of_le_Y1 ha hK β hd1 hd2 hp hKk hRH hY.ge hμ)

theorem map_eq_of_sylowB_mem_Y2 (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (hd1 : R1Dich2 K a β)
    (hd2 : R2Dich2 K a β) {p : ℕ} (hp : p.Prime) (hβ : orderOf β = p)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hnot : ¬ F4.reeGamma K a ≤ H)
    {b c : K} (hbc : sylowB a K b c ∈ Y2 K a hK H) : β b = b ∧ β c = c := by
  by_contra hne
  obtain ⟨-, l, hl⟩ := card_eq_pow_fixSubfield hK β hp hβ
  have hY := hd2 (Y2 K a hK H) leviImage_le (fun x hx => inf_le_leviImage ⟨hx.1, hRH hx.2⟩) b c
    hne hbc
  obtain ⟨-, v, hv, hvT⟩ := hY.ge (torusTwo_mem_rankOneGroupTwo' l)
  have hvU : v ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le _ hv
  set c' : K := ((l⁻¹ : Kˣ) : K) ^ 2 ^ a * 1 with hc'
  obtain ⟨w, hw, hwe⟩ := exists_mul_sylowA_of_conj hK hvU c'
  have hA1 : sylowA a K 1 ∈ H := hRH ((sylowA_mem_Rf_iff hK β 1).2 (map_one β))
  have hmem : w * sylowA a K c' ∈ H := by
    have h1 := H.mul_mem (H.mul_mem hvT hA1) (H.inv_mem hvT)
    have e : v * pairedTorusHom a (f4i 1) (f4i 2) l * sylowA a K 1 *
        (v * pairedTorusHom a (f4i 1) (f4i 2) l)⁻¹ = v * sylowA a K c' * v⁻¹ := by
      rw [hc', ← torusTwo_conj_sylowA hK]
      group
    rwa [e, hwe] at h1
  have hc'R := map_eq_of_sylowA_mem_Y1 ha hK β hd1 hd2 hp hβ hRH hnot
    ⟨sylowA_mem_rankOneGroupOne' hK c', w, hw, hmem⟩
  rw [hc', mul_one] at hc'R
  apply hl
  have h' := eq_of_map_pow_two_pow_eq β a hc'R
  have : ((l⁻¹ : Kˣ) : K) = (l : K)⁻¹ := Units.val_inv_eq_inv_val l
  rw [this, map_inv₀] at h'
  exact inv_injective h'

omit [Finite K] [CharP K F4.prime] in
theorem four_le_card_fixSubfield (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hβ : orderOf β = p) (hk : Nat.card (fixSubfield β) ≠ 2) :
    4 ≤ Nat.card (fixSubfield β) := by
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK β
  rw [hβ] at hdvd hcard
  have h1 : 1 ≤ (2 * a + 1) / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
  have hm : 2 ≤ (2 * a + 1) / p := by
    by_contra hlt
    apply hk
    rw [hcard, show (2 * a + 1) / p = 1 by omega, pow_one]
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ ((2 * a + 1) / p) := Nat.pow_le_pow_right (by norm_num) hm

theorem closure_eq_top_of_maximal (β : K ≃+* K) (g : F4.reeGamma K a)
    (hne : (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
      fixedSubgroup (F4.reeGammaFieldAut K a β))
    (hmax : ∀ H : Subgroup (ModGL F4.tag K), H ≤ F4.reeGamma K a → Rf K a β ≤ H →
      ¬ H ≤ Rf K a β → F4.reeGamma K a ≤ H) :
    Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
      ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
        Set (F4.reeGamma K a))) = ⊤ := by
  classical
  set S := fixedSubgroup (F4.reeGammaFieldAut K a β) with hS
  set C := Subgroup.closure ((S : Set (F4.reeGamma K a)) ∪
    (S.map (MulAut.conj g).toMonoidHom : Set (F4.reeGamma K a))) with hC
  set H : Subgroup (ModGL F4.tag K) := C.map (F4.reeGamma K a).subtype with hH
  have hHΓ : H ≤ F4.reeGamma K a := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hSC : S ≤ C := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hSgC : S.map (MulAut.conj g).toMonoidHom ≤ C := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hRH : Rf K a β ≤ H := by
    rw [← map_fixedSubgroup_eq_Rf]
    exact Subgroup.map_mono hSC
  have hHR : ¬ H ≤ Rf K a β := by
    intro hHR
    have hCS : C ≤ S := fun x hx => (mem_fixedSubgroup_iff x).2 (hHR ⟨x, hx, rfl⟩)
    apply hne
    refine Subgroup.eq_of_le_of_card_ge (hSgC.trans hCS) ?_
    exact (Subgroup.card_map_of_injective (fun x y hxy => (MulAut.conj g).injective hxy)).ge
  have hle := hmax H hHΓ hRH hHR
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

theorem false_of_overgroup
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hHΓ : H ≤ F4.reeGamma K a) (hRH : Rf K a β ≤ H)
    (hHR : ¬ H ≤ Rf K a β) (hY1 : Y1 K a hK H ≤ Rf K a β) (hY2 : Y2 K a hK H ≤ Rf K a β)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β)
    (hfus : ∀ x ∈ Rf K a β, x ^ 2 = 1 → x ≠ 1 →
      ∃ r ∈ Rf K a β, r * x * r⁻¹ = centralZ K a 1 ∨ r * x * r⁻¹ = sylowL a K 1) : False := by
  classical
  have hCz := inf_centralizer_centralZ_le_Rf ha hK β hHΓ hRH hY2 hU
  have hCt := inf_centralizer_sylowL_le_Rf ha hK β hHΓ hRH hY1 hU
  have hzH : centralZ K a 1 ∈ H := hRH (centralZ_one_mem_Rf hK β)
  have htH : sylowL a K 1 ∈ H := hRH (sylowL_one_mem_Rf hK β)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine false_of_two_involution_classes (G := H) (R := (Rf K a β).subgroupOf H)
    (z := ⟨centralZ K a 1, hzH⟩) (t := ⟨sylowL a K 1, htH⟩) ?_
    (Subgroup.mem_subgroupOf.2 (centralZ_one_mem_Rf hK β))
    ((Subgroup.orderOf_coe _).symm.trans (orderOf_eq_prime centralZ_one_sq centralZ_one_ne_one))
    ((Subgroup.orderOf_coe _).symm.trans
      (orderOf_eq_prime sylowL_one_sq (sylowL_one_ne_one hK))) ?_ ?_ ?_ ?_
  ·
    intro htop
    apply hHR
    intro x hx
    have hx' : (⟨x, hx⟩ : H) ∈ (Rf K a β).subgroupOf H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hx'
  ·
    intro h hh
    have e := congrArg Subtype.val hh
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      Subgroup.coe_mk] at e
    exact centralZ_one_not_conj_sylowL ha hK h (hHΓ h.2) e
  ·
    intro x hx hx2
    have hxR : (x : ModGL F4.tag K) ∈ Rf K a β := Subgroup.mem_subgroupOf.1 hx
    have hx2' : orderOf (x : ModGL F4.tag K) = 2 := (Subgroup.orderOf_coe x).trans hx2
    have hsq : (x : ModGL F4.tag K) ^ 2 = 1 := by
      rw [← hx2']
      exact pow_orderOf_eq_one _
    have hx1 : (x : ModGL F4.tag K) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx2'
      exact absurd hx2' (by norm_num)
    obtain ⟨r, hr, hrx⟩ := hfus _ hxR hsq hx1
    refine ⟨⟨r, hRH hr⟩, Subgroup.mem_subgroupOf.2 hr, ?_⟩
    rcases hrx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  ·
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have e := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk] at e
    exact Subgroup.mem_subgroupOf.2 (hCz ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 e⟩)
  ·
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have e := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk] at e
    exact Subgroup.mem_subgroupOf.2 (hCt ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 e⟩)

theorem reeGamma_le_of_overgroup_odd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk : Nat.card (fixSubfield β) ≠ 2) {H : Subgroup (ModGL F4.tag K)}
    (hHΓ : H ≤ F4.reeGamma K a) (hRH : Rf K a β ≤ H) (hHR : ¬ H ≤ Rf K a β) :
    F4.reeGamma K a ≤ H := by
  by_contra hnot
  have hk4 := four_le_card_fixSubfield hK β hp hβ hk
  have hd1 := r1Dich hK β hp hp2 hβ hk4
  have hd2 := r2Dich_odd ha hK β hp hp2 hβ (by omega)
  have hY1 := Y1_le_Rf ha hK β hd1 hd2 hp hβ hRH hnot
  have hY2 := Y2_le_Rf ha hK β hd1 hd2 hp hβ hRH hnot
  exact false_of_overgroup ha hK β hHΓ hRH hHR hY1 hY2
    (inf_reeFixedPosUnipotent_le_Rf hK β hRH hY1 hY2)
    fun x hx hx2 hx1 => exists_conj_of_involution_Rf_odd hK β hp hp2 hβ hk hx hx2 hx1

theorem closure_eq_top_odd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk : Nat.card (fixSubfield β) ≠ 2) (g : F4.reeGamma K a)
    (hne : (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
      fixedSubgroup (F4.reeGammaFieldAut K a β)) :
    Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
      ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
        Set (F4.reeGamma K a))) = ⊤ :=
  closure_eq_top_of_maximal β g hne fun _ hHΓ hRH hHR =>
    reeGamma_le_of_overgroup_odd ha hK β hp hp2 hβ hk hHΓ hRH hHR

theorem closure_eq_top
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hβ : orderOf β = p)
    (hk : Nat.card (fixSubfield β) ≠ 2) (g : F4.reeGamma K a)
    (hne : (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
      fixedSubgroup (F4.reeGammaFieldAut K a β)) :
    Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
      ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
        Set (F4.reeGamma K a))) = ⊤ :=
  closure_eq_top_odd ha hK β hp (by omega) hβ hk g hne

theorem reeGamma_le_of_overgroup_of_parts
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hβ : orderOf β = p) (hd1 : R1Dich2 K a β)
    (hd2 : R2Dich2 K a β)
    (hLR1 : ∀ H : Subgroup (ModGL F4.tag K), Rf K a β ≤ H →
      H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β → Y1 K a hK H ≤ Rf K a β)
    (hLR2 : ∀ H : Subgroup (ModGL F4.tag K), Rf K a β ≤ H →
      H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β → Y2 K a hK H ≤ Rf K a β)
    (hfus : ∀ x ∈ Rf K a β, x ^ 2 = 1 → x ≠ 1 →
      ∃ r ∈ Rf K a β, r * x * r⁻¹ = centralZ K a 1 ∨ r * x * r⁻¹ = sylowL a K 1)
    {H : Subgroup (ModGL F4.tag K)} (hHΓ : H ≤ F4.reeGamma K a) (hRH : Rf K a β ≤ H)
    (hHR : ¬ H ≤ Rf K a β) : F4.reeGamma K a ≤ H := by
  by_contra hnot
  have hU := inf_reeFixedPosUnipotent_le_Rf_of_roots hK β hRH
    (fun s hs => map_eq_of_sylowA_mem_Y1 ha hK β hd1 hd2 hp hβ hRH hnot hs)
    (fun b c hbc => map_eq_of_sylowB_mem_Y2 ha hK β hd1 hd2 hp hβ hRH hnot hbc)
  exact false_of_overgroup ha hK β hHΓ hRH hHR (hLR1 H hRH hU) (hLR2 H hRH hU) hU hfus

@[expose] def SubfieldPairReeF4Two : Prop :=
  ∀ (a : ℕ), (2 * a + 1 = 5 ∨ 2 * a + 1 = 13) →
    ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime], Nat.card K = 2 ^ (2 * a + 1) →
      ∀ β : K ≃+* K, orderOf β = 2 * a + 1 → ∀ g : F4.reeGamma K a,
        (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (F4.reeGammaFieldAut K a β) →
        Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
          ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
            Set (F4.reeGamma K a))) = ⊤

theorem eq_five_or_eq_thirteen (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hβ : orderOf β = p) (hk : Nat.card (fixSubfield β) = 2)
    (hpd : p ∣ Nat.card (fixedSubgroup (F4.reeGammaFieldAut K a β))) : p = 5 ∨ p = 13 := by
  obtain ⟨b, hb, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data ha hK hp (by omega) β hβ
  have hb0 : b = 0 := by
    rw [hk] at hb
    have h1 := Nat.pow_right_injective (le_refl 2) (hb.symm.trans (pow_one 2).symm)
    omega
  subst hb0
  have : Finite (fixSubfield β) := Subtype.finite
  have : CharP (fixSubfield β) F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hk]; rfl)
  have hSe : fixedSubgroup (F4.reeGammaFieldAut K a β) =
      (F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  have hRcard : Nat.card (fixedSubgroup (F4.reeGammaFieldAut K a β)) =
      Nat.card (F4.reeGamma (fixSubfield β) 0) := by
    rw [← Subgroup.card_map_of_injective (f := (F4.reeGamma K a).subtype) Subtype.val_injective,
      ← Subgroup.card_map_of_injective (f := baseChangeGL (fixSubfield β).subtype)
        (K := F4.reeGamma (fixSubfield β) 0) (baseChangeGL_injective _), hSe, hfix]
  rw [hRcard] at hpd
  have key := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    0 (fixSubfield β) hk).2 p hp (by omega) hpd
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at key
  rcases key with h1 | h1 | h1 | h1 | h1
  · exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
  · exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

theorem subfieldPairReeF4_of_two
    (h : SubfieldPairReeF4Two) : SEITZ2.SubfieldPairReeF4 := by
  intro a ha K _ _ _ hK β p hp hp5 hβ g hne
  by_cases hk : Nat.card (fixSubfield β) = 2
  · by_cases hpd : p ∣ Nat.card (fixedSubgroup (F4.reeGammaFieldAut K a β))
    · left
      obtain ⟨hdvd, hcard⟩ :=
        CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK β
      rw [hβ] at hdvd hcard
      have h1 : (2 * a + 1) / p = 1 := by
        rw [hk] at hcard
        exact Nat.pow_right_injective (le_refl 2) (hcard.symm.trans (pow_one 2).symm)
      have hpa : 2 * a + 1 = p := by
        obtain ⟨d, hd⟩ := hdvd
        rw [hd, Nat.mul_div_cancel_left _ hp.pos] at h1
        rw [hd, h1, mul_one]
      have hp513 := eq_five_or_eq_thirteen ha hK β hp hp5 hβ hk hpd
      exact h a (by omega) K hK β (hβ.trans hpa.symm) g hne
    · exact Or.inr hpd
  · exact Or.inl (closure_eq_top ha hK β hp hp5 hβ hk g hne)

end CFSG.RankThree.PartOne.SEITZRF
