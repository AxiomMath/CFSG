module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Comm
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBOdd
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JNormal
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JSylow
public import CFSG.Mathlib.GroupTheory.OddAutSylowCentralizer

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem mulMap_injective {G : Type*} [Group G] {H K : Subgroup G} (hi : H ⊓ K = ⊥) :
    Function.Injective (fun p : ↥H × ↥K => (p.1 : G) * p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  have h1 : (x : G) * y = x' * y' := hxy
  have h2 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
    calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
      _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h1]
      _ = y' * (y : G)⁻¹ := by group
  have hmem : (x' : G)⁻¹ * x ∈ H ⊓ K :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ x'.2) x.2,
      h2 ▸ Subgroup.mul_mem _ y'.2 (Subgroup.inv_mem _ y.2)⟩
  rw [hi, Subgroup.mem_bot] at hmem
  have hx : (x : G) = x' := by rw [← mul_inv_cancel_left (x' : G) x, hmem, mul_one]
  have hy : (y : G) = y' := by rw [hx] at h1; exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

theorem exists_rCenJ {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ : Subgroup G}
    (hJ : JData n L z J) (hB₂ : B2Package b z B₂) :
    ∃ R : Subgroup G, R ≤ B₂ ∧ Nat.card R = 9 ∧ GGFF.zs z 0 ∈ R ∧
      (∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ Subgroup.zpowers (GGFF.zs z 0)) ∧
      (∃ r ∈ R, b * r * b⁻¹ * r⁻¹ ≠ 1) ∧ ∀ r ∈ R, ∀ x ∈ J, r * x = x * r := by
  obtain ⟨T, hTB₂, hB₁T, hTcard, hTbr⟩ := exists_commSubgroup h hB₂
  obtain ⟨hY3, hY9, hYmax⟩ := sylow_B₁_inf_J h hJ
  have hodd : Odd (Nat.card ↥(cB b z)) := odd_cen h
  have hcommB : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp (hB₂.abel.1.is_comm.comm (⟨x, hx⟩ : ↥B₂) ⟨y, hy⟩)
  have hb₁B₂ : GGFF.zs z 0 ∈ B₂ :=
    hB₂.B₁_le (Subgroup.subset_closure (Set.mem_range_self 0))
  have hb₁bOne : GGFF.zs z 0 ∈ bOne z :=
    Subgroup.subset_closure (Set.mem_range_self 0)
  have hb₁T : GGFF.zs z 0 ∈ T := hB₁T hb₁bOne
  let Y : Subgroup G := bOne z ⊓ J
  let R : Subgroup G := T ⊓ Subgroup.centralizer (J : Set G)
  have hRT : R ≤ T := inf_le_left
  have hYbOne : Y ≤ bOne z := inf_le_left
  have hYT : Y ≤ T := hYbOne.trans hB₁T
  have hY9' : Nat.card Y = 9 := hY9
  have hexists : ∀ t ∈ T, ∃ y ∈ Y, ∀ x ∈ J, t * x * t⁻¹ = y * x * y⁻¹ := by
    intro t htT
    have htB₂ : t ∈ B₂ := hTB₂ htT
    have ht3 : t ^ 3 = 1 := hB₂.abel.2 t htB₂
    have ht₀ : t * GGFF.zs z 0 = GGFF.zs z 0 * t := hcommB t htB₂ _ hb₁B₂
    have htb : ∃ k : ℤ, t * b * t⁻¹ = GGFF.zs z 0 ^ k * b := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hTbr t htT)
      refine ⟨-j, ?_⟩
      rw [zpow_neg, hj]
      group
    have htJ : ∀ x ∈ J, t * x * t⁻¹ ∈ J := conj_mem_J h hodd hJ ht₀ htb
    have htY : ∀ y ∈ Y, t * y = y * t :=
      fun y hy => hcommB t htB₂ y (hB₂.B₁_le (hYbOne hy))
    exact CFSG.OddAutSylowCentralizer.exists_mem_conj_eq (inner_odd_J h hJ) (center_J h hJ)
      inf_le_right hY3 hYmax ht3 htJ htY
  have hRY_bot : R ⊓ Y = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    rw [Subgroup.mem_bot]
    have hyR : y ∈ R := (Subgroup.mem_inf.1 hy).1
    have hyY : y ∈ Y := (Subgroup.mem_inf.1 hy).2
    have hyC : y ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.1 hyR).2
    have hyJ : y ∈ J := (Subgroup.mem_inf.1 hyY).2
    exact center_J h hJ y hyJ fun z hz => ((Subgroup.mem_centralizer_iff.mp hyC) z hz).symm
  let f : ↥R × ↥Y → ↥T := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem T (hRT p.1.2) (hYT p.2.2)⟩
  have hf_surj : Function.Surjective f := by
    rintro ⟨t, htT⟩
    obtain ⟨y, hyY, hyprop⟩ := hexists t htT
    have hyT : y ∈ T := hYT hyY
    have hyJ : y ∈ J := (Subgroup.mem_inf.1 hyY).2
    have hryT : t * y⁻¹ ∈ T := Subgroup.mul_mem T htT (Subgroup.inv_mem T hyT)
    have hryC : t * y⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : y⁻¹ * z * y ∈ J :=
        Subgroup.mul_mem J (Subgroup.mul_mem J (Subgroup.inv_mem J hyJ) hz) hyJ
      have hkey := hyprop (y⁻¹ * z * y) hz'
      have hs : (t * y⁻¹) * z * (t * y⁻¹)⁻¹ = z := by
        calc (t * y⁻¹) * z * (t * y⁻¹)⁻¹ = t * (y⁻¹ * z * y) * t⁻¹ := by group
          _ = y * (y⁻¹ * z * y) * y⁻¹ := hkey
          _ = z := by group
      calc z * (t * y⁻¹) = ((t * y⁻¹) * z * (t * y⁻¹)⁻¹) * (t * y⁻¹) := by rw [hs]
        _ = (t * y⁻¹) * z := by group
    refine ⟨(⟨t * y⁻¹, Subgroup.mem_inf.2 ⟨hryT, hryC⟩⟩, ⟨y, hyY⟩), ?_⟩
    apply Subtype.ext
    change (t * y⁻¹) * y = t
    group
  have hf_inj : Function.Injective f :=
    fun p q hpq => mulMap_injective hRY_bot (congrArg Subtype.val hpq)
  have hcard : Nat.card R * Nat.card Y = Nat.card T := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hcardR : Nat.card R = 9 := by
    have hc := hcard
    rw [hTcard, hY9'] at hc
    norm_num at hc
    omega
  refine ⟨R, hRT.trans hTB₂, hcardR, Subgroup.mem_inf.2 ⟨hb₁T, ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hJ.comm x hx
  · intro r hr
    exact hTbr r (hRT hr)
  ·
    by_contra hcon
    push Not at hcon
    have hR_bOne : R ≤ bOne z := by
      intro r hr
      have hrB₂ : r ∈ B₂ := hTB₂ (hRT hr)
      have hcommbr : r * b = b * r := by
        have h1 : b * r * b⁻¹ * r⁻¹ = 1 := hcon r hr
        calc r * b = (b * r * b⁻¹ * r⁻¹) * (r * b) := by rw [h1, one_mul]
          _ = b * r := by group
      exact hB₂.fix r hrB₂ hcommbr
    let g : ↥R × ↥Y → ↥(bOne z) := fun p =>
      ⟨(p.1 : G) * p.2, Subgroup.mul_mem (bOne z) (hR_bOne p.1.2) (hYbOne p.2.2)⟩
    have hg_inj : Function.Injective g :=
      fun p q hpq => mulMap_injective hRY_bot (congrArg Subtype.val hpq)
    have hle : Nat.card (↥R × ↥Y) ≤ Nat.card ↥(bOne z) :=
      Nat.card_le_card_of_injective g hg_inj
    rw [Nat.card_prod, hcardR, hY9'] at hle
    rw [h.settingCore.card_torG] at hle
    norm_num at hle
  · intro r hr x hx
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 hr).2) x hx).symm

end CFSG.StandardType.FF81.PropOne

end
