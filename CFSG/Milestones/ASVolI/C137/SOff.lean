module

public import CFSG.Milestones.ASVolI.C137.SCrd
public import CFSG.Quasithin.H13.GoldschmidtC137L3Fin

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3.GC137

theorem burnsideC137_mem_fixS {g : Γ} {v : Vec} : v ∈ fixS g ↔ act g v = v := by
  simp [fixS]

theorem burnsideC137_mem_BS {S : Finset Vec} {g : Γ} : g ∈ BS S ↔ ∀ v ∈ S, act g v = v := by
  simp [BS]

theorem burnsideC137_mem_cent {z x : Γ} : x ∈ cent z ↔ x * z = z * x := by
  simp [cent]

theorem burnsideC137_isPlane_fixS {g : Γ} (hg : IsInvol g) : IsPlane (fixS g) := by
  refine ⟨invol_fixS_card g hg, burnsideC137_mem_fixS.2 (act_zero g), ?_⟩
  intro x hx y hy
  rw [burnsideC137_mem_fixS] at hx hy ⊢
  rw [act_add, hx, hy]

theorem burnsideC137_natCard_le {β : Type*} [Fintype β] (s : Set β) (F : Finset β)
    (h : ∀ x ∈ s, x ∈ F) : Nat.card s ≤ F.card := by
  rw [← Set.ncard_coe_finset F, ← Nat.card_coe_set_eq]
  exact Nat.card_mono (Set.toFinite _) (fun x hx => h x hx)

theorem burnsideC137_eq_of_natCard_le {β : Type*} [Fintype β] (s : Set β) (F : Finset β)
    (h : ∀ x ∈ s, x ∈ F) (hc : F.card ≤ Nat.card s) : ∀ x ∈ F, x ∈ s := by
  have hsub : s ⊆ (F : Set β) := fun x hx => h x hx
  have hc' : (F : Set β).ncard ≤ s.ncard := by
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact hc
  have := Set.eq_of_subset_of_ncard_le hsub hc' (Set.toFinite _)
  intro x hx
  have hx' : x ∈ (F : Set β) := hx
  rw [← this] at hx'
  exact hx'

theorem burnsideC137_natCard_eq {β : Type*} [Fintype β] (s : Set β) (F : Finset β)
    (h : ∀ x, x ∈ s ↔ x ∈ F) : Nat.card s = F.card := by
  have : s = (F : Set β) := Set.ext fun x => (h x).trans Iff.rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem burnsideC137_offΓ (H : Subgroup Γ) (h1 : H ≠ ⊥) (hsq : ∀ g ∈ H, g * g = 1)
    (hc : 64 ≤ Nat.card H * Nat.card (burnsideC137_fixVec H) ^ 2) :
    ∃ S : Finset Vec, IsPlane S ∧ (∀ g, g ∈ H ↔ g ∈ BS S) ∧
      (∀ v, v ∈ burnsideC137_fixVec H ↔ v ∈ S) := by
  obtain ⟨⟨g, hgH⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h1
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hinv : IsInvol g := ⟨hsq g hgH, hg1'⟩
  set S := fixS g with hSdef
  have hS : IsPlane S := burnsideC137_isPlane_fixS hinv
  have hCS : ∀ v ∈ ((burnsideC137_fixVec H : AddSubgroup Vec) : Set Vec), v ∈ S :=
    fun v hv => burnsideC137_mem_fixS.2 (hv g hgH)
  have hC4 : Nat.card (burnsideC137_fixVec H) ≤ 4 := by
    have := burnsideC137_natCard_le _ S hCS
    rw [hS.1] at this
    exact this
  have hHcent : ∀ h ∈ (H : Set Γ), h ∈ cent g := by
    intro h hh
    rw [burnsideC137_mem_cent]
    have e : h * g * (h * g) = 1 := hsq _ (H.mul_mem hh hgH)
    have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hsq h hh)
    have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g hgH)
    calc h * g = (h * g)⁻¹ := eq_inv_of_mul_eq_one_left e
      _ = g * h := by rw [mul_inv_rev, hh', hg']
  have hH8 : Nat.card H ≤ 8 := by
    have := burnsideC137_natCard_le _ (cent g) hHcent
    rw [cent_card g hinv] at this
    exact this
  have hCd : Nat.card (burnsideC137_fixVec H) ∣ 8 := by
    have := AddSubgroup.card_addSubgroup_dvd_card (burnsideC137_fixVec H)
    simpa [Nat.card_eq_fintype_card] using this
  have hC : Nat.card (burnsideC137_fixVec H) = 4 := by
    have hpos : 0 < Nat.card (burnsideC137_fixVec H) := Nat.card_pos
    interval_cases hk : Nat.card (burnsideC137_fixVec H)
    · norm_num at hc; omega
    · norm_num at hc; omega
    · exact absurd hCd (by norm_num)
    · rfl
  have hCeq : ∀ v ∈ S, v ∈ burnsideC137_fixVec H := by
    refine burnsideC137_eq_of_natCard_le _ S hCS ?_
    rw [hS.1]
    exact hC.ge
  have hHBS : ∀ h ∈ (H : Set Γ), h ∈ BS S := fun h hh =>
    burnsideC137_mem_BS.2 fun v hv => (hCeq v hv) h hh
  have hH4 : 4 ≤ Nat.card H := by
    rw [hC] at hc
    omega
  have hHeq : ∀ h ∈ BS S, h ∈ (H : Set Γ) := by
    refine burnsideC137_eq_of_natCard_le _ (BS S) hHBS ?_
    rw [BS_card S hS]
    exact hH4
  exact ⟨S, hS, fun h => ⟨hHBS h, hHeq h⟩, fun v => ⟨hCS v, hCeq v⟩⟩

theorem burnsideC137_not_ord3 {g : Γ} (h3 : IsOrd3 g) {k : ℕ} (hk : g ^ 2 ^ k = 1) : False := by
  have hy3 : g ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h3.1
  have hd3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have hd2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have : orderOf g ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hd3 hd2
  exact h3.2 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))

theorem burnsideC137_stab_of_norm {S : Finset Vec} (hS : IsPlane S) {h : Γ}
    (hn : ∀ t ∈ BS S, h * t * h⁻¹ ∈ BS S) : ∀ v ∈ S, act h v ∈ S := by
  obtain ⟨t, ht, htS⟩ := exists_invol_fixS S hS
  have htB : t ∈ BS S := burnsideC137_mem_BS.2 fun v hv => by
    rw [← htS] at hv
    exact burnsideC137_mem_fixS.1 hv
  have ht' := hn t htB
  have ht'1 : h * t * h⁻¹ ≠ 1 := fun h1 => ht.2 (by
    have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
    rw [this, h1]; group)
  have hfix := BS_fixS S hS _ ht' ht'1
  intro v hv
  rw [← hfix, burnsideC137_mem_fixS]
  have hv' : act t v = v := (burnsideC137_mem_BS.1 htB) v hv
  rw [← act_mul, show h * t * h⁻¹ * h = h * t by group, act_mul, hv']

section Off

variable {G : Type} [Group G] [Finite G] {L U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂) (hU : IsElemAbelian 2 U)
include hs hU

theorem burnsideC137_offender {B : Subgroup (MulAut (IntMod U hU))} (hBL : B ≤ autI hU L)
    (hB1 : B ≠ ⊥) (hsq : ∀ b ∈ B, b * b = 1)
    (hc : Nat.card (IntMod U hU) ≤ Nat.card B * Nat.card (fixV B)) :
    ∃ S : Finset Vec, IsPlane S ∧
      (∀ a : ↥(autI hU L), (a : MulAut (IntMod U hU)) ∈ B ↔ burnsideC137_ψ hs hU a ∈ BS S) ∧
      Nat.card B = 4 ∧ Nat.card (fixV B) = 16 := by
  set H := burnsideC137_bar hs hU B with hH
  have hH1 : H ≠ ⊥ := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    intro hbot
    have hmem := (burnsideC137_mem_bar_iff hs hU (B := B) ⟨b, hBL hb⟩).2 hb
    rw [← hH, hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
    exact hb1' (congrArg Subtype.val hmem)
  have hHsq : ∀ g ∈ H, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (burnsideC137_mem_bar hs hU).1 hg
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hsq _ ha)
    rw [this, map_one]
  have hHc : 64 ≤ Nat.card H * Nat.card (burnsideC137_fixVec H) ^ 2 := by
    rw [hH, burnsideC137_card_bar hs hU hBL, ← burnsideC137_card_fixV hs hU hBL,
      ← burnsideC137_card_U hs hU]
    exact hc
  obtain ⟨S, hS, hHS, hCS⟩ := burnsideC137_offΓ H hH1 hHsq hHc
  have hCcard : Nat.card (burnsideC137_fixVec H) = 4 := by
    rw [← hS.1]
    exact burnsideC137_natCard_eq _ S hCS
  refine ⟨S, hS, fun a => ⟨fun ha => (hHS _).1 ((burnsideC137_mem_bar_iff hs hU a).2 ha),
    fun ha => (burnsideC137_mem_bar_iff hs hU a).1 ((hHS _).2 ha)⟩, ?_, ?_⟩
  · rw [← burnsideC137_card_bar hs hU hBL, ← hH, ← BS_card S hS]
    exact burnsideC137_natCard_eq _ (BS S) hHS
  · rw [burnsideC137_card_fixV hs hU hBL, ← hH, hCcard]
    norm_num

end Off

end CFSG.ASVolI
