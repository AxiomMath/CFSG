module

public import CFSG.Quasithin.Background.FFC6P
public import CFSG.Quasithin.Background.B4L3Two
public import CFSG.Quasithin.Background.B5IrrA

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5
open scoped commutatorElement

namespace B59

section CaseV

variable {M : Type} [CommGroup M] [Finite M]

theorem caseV_M (hM : ∀ v : M, v ^ 2 = 1) {X K Ab : Subgroup (MulAut M)} (hXK : X = K)
    (hmin : IsFFStarMin X Ab) (hirr : commV K ∈ IrrPlus K ⊤) (hα : commV K ⊔ fixV K = ⊤)
    (hnat : BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 1) (hcard : Nat.card ↥(commV K) = 2 ^ 4) :
    B482Module K (commV K) ∧ Nat.card ↥Ab = 4 ∧ 1 ≤ rAV Ab := by
  subst hXK
  obtain ⟨hinv, hcomm, hlt, hirr'⟩ := irr_data hirr
  have hC2 : Nat.card ↥(commV X ⊓ fixV X) = 2 := by
    obtain ⟨K', hK', hfin, hc, π, hπ⟩ := hnat
    have e := card_eq_of_realizes (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K')) rfl hπ
    rw [card_sec_nat, hc, hcard] at e
    have hZ : Nat.card ↥(fixV X ⊓ commV X) = 2 := by
      rw [show ((2 : ℕ) ^ 1) ^ 3 = 8 by norm_num, show (2 : ℕ) ^ 4 = 16 by norm_num] at e
      omega
    rwa [inf_comm] at hZ
  have hcard' : Nat.card ↥(commV X) = 16 := by rw [hcard]; norm_num
  have hind := not_decomp_of_card (L := X) (U := commV X) hcomm hirr' hcard' hC2
  have hB482 : B482Module X (commV X) := ⟨hcard, hnat, hind⟩
  refine ⟨hB482, ?_⟩
  obtain ⟨F'', hF''F, hF''C, hF''sup⟩ :=
    exists_complement_in hM (C := fixV X ⊓ commV X) (F := fixV X) inf_le_left
  have hsup : F'' ⊔ commV X = ⊤ := by
    have h1 : fixV X ≤ F'' ⊔ commV X :=
      calc fixV X = F'' ⊔ (fixV X ⊓ commV X) := hF''sup.symm
        _ ≤ F'' ⊔ commV X := sup_le_sup_left inf_le_right F''
    have h2 : commV X ⊔ fixV X ≤ F'' ⊔ commV X := sup_le le_sup_right h1
    rw [hα] at h2
    exact top_le_iff.1 h2
  have hinf : F'' ⊓ commV X = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ F'' ⊓ (fixV X ⊓ commV X) := ⟨hx1, hF''F hx1, hx2⟩
    rw [hF''C] at h1
    exact h1
  have hst : X ≤ stabSub (commV X) := fun g hg u =>
    ⟨fun hu => by simpa using hinv g⁻¹ (X.inv_mem hg) _ hu, hinv g hg u⟩
  have hfaith : ∀ g ∈ X, (∀ v ∈ commV X, g v = v) → g = 1 := by
    intro g hg hgU
    refine MulEquiv.ext fun m => ?_
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 (hα ▸ Subgroup.mem_top m)
    show g (u * f) = u * f
    rw [map_mul, hgU u hu, hf g hg]
  have hGV₁ : ∀ b ∈ X, ∀ v ∈ F'', b v = v := fun b hb v hv => hF''F hv b hb
  have hAbX : Ab ≤ X := hmin.1.1
  have hAbU : Ab ≤ stabSub (commV X) := hAbX.trans hst
  have hoff : IsFFStarOffender (autSub X (commV X)) (autSub Ab (commV X)) :=
    FFC.isFFStarOffender_autSub hsup hinf hst hfaith hGV₁ hmin.1 hAbX
  have hnatU : BinaryNaturalSL (autSub X (commV X)) (⊤ : Subgroup ↥(commV X))
      (fixV (autSub X (commV X))) 3 1 := by
    obtain ⟨K', hK', hfin, hc, hr⟩ := hnat
    refine ⟨K', hK', hfin, hc, ?_⟩
    have h1 := realizes_comap hst hfaith hr
    have hC' : (fixV X ⊓ commV X).comap (commV X).subtype = fixV (autSub X (commV X)) := by
      rw [inf_comm, ← map_subtype_fixV_autSub hst]
      exact Subgroup.comap_map_eq_self_of_injective (commV X).subtype_injective _
    rwa [hC'] at h1
  have hindU : IsIndecompModule (autSub X (commV X)) := isIndecompModule_autSub hst hind
  have hVU : ∀ v : ↥(commV X), v ^ 2 = 1 := B1.sq_eq_one_sub hM _
  have hcardU : Nat.card ↥(commV X) = 16 := hcard'
  obtain ⟨D⟩ := hnatU.toL3Coord
  have H := offHyp_two D hVU hcardU rfl rfl hindU
  obtain ⟨hAb4, hfix4⟩ := offHyp_card_offender H hoff
  have hAbc : Nat.card ↥Ab = 4 := by
    rw [← card_autSub_eq hAbU (faithful_of_le hfaith hAbX)]
    exact hAb4
  have hfixAb : Nat.card ↥(fixV Ab) = Nat.card ↥F'' * 4 := by
    rw [card_fixV_eq_mul_autSub hsup hinf hAbU (fun b hb v hv => hGV₁ b (hAbX hb) v hv), hfix4]
  have hMc : Nat.card M = Nat.card ↥F'' * 16 := by
    have h := card_sup_mul_card_inf F'' (commV X)
    rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top, hcardU] at h
    exact h
  have hr : rAV Ab = 1 := by
    rw [rAV_eq_one_iff hM hmin.1.isA2, hMc, hfixAb, hAbc]
    ring
  exact ⟨hAbc, hr.ge⟩

end CaseV

end B59

end FFC

end CFSG.Quasithin
