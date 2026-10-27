module

public import CFSG.Quasithin.Background.RonanD39Chief
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Background.F918N9
public import CFSG.Quasithin.Background.F918R4
public import CFSG.Quasithin.Background.F918S3
public import CFSG.Quasithin.Background.F918U9
public import CFSG.Quasithin.Background.F918WF
public import CFSG.Quasithin.Background.F918WG
public import CFSG.Quasithin.Background.F918WH
public import CFSG.Quasithin.Background.F918XY
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin.RonanD39

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_conj_offender_le {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) {A : Subgroup (MulAut W)} (hA : A ∈ QhatStar M)
    (hAf : ∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) :
    ∃ A' : Subgroup (MulAut W), IsA2 M A' ∧ A' ≤ T ∧ commSeries A' 3 = ⊥ ∧ rAV A' ≤ 2 ∧
      ∀ a ∈ A', (∀ x ∈ Mp, a * x = x * a) → a = 1 := by
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAp : IsPGroup 2 ↥A := hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hAx⟩ := F7.isSylowTwoOf_exists_conj_le hD.hyp.sylow (QhatStar_le hA) hAp
  set A' := conjBy x⁻¹ A with hA'def
  have hA'Q : A' ∈ QhatStar M := conjBy_mem_QhatStar hA (M.inv_mem hx)
  have hA'T : A' ≤ T := by
    intro y hy
    rw [mem_conjBy_iff, inv_inv] at hy
    have := hAx hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  obtain ⟨r', -, hr'2, ⟨⟨hA'2, hA'r⟩, hA'3⟩, -⟩ := QhatStar_spec hA'Q
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  refine ⟨A', hA'2, hA'T, hA'3, hA'r.le.trans hr'2, fun a ha hac => ?_⟩
  rw [mem_conjBy_iff, inv_inv] at ha
  have hb1 : x * a * x⁻¹ = 1 := by
    refine hAf _ ha fun z hz => ?_
    have hz' : x⁻¹ * z * x⁻¹⁻¹ ∈ Mp := hMn _ (M.inv_mem hx) z hz
    have e := hac _ hz'
    have e' : x * (a * (x⁻¹ * z * x⁻¹⁻¹)) * x⁻¹ = x * ((x⁻¹ * z * x⁻¹⁻¹) * a) * x⁻¹ := by rw [e]
    simp only [inv_inv] at e'
    calc x * a * x⁻¹ * z = x * (a * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * z * x * a) * x⁻¹ := e'
      _ = z * (x * a * x⁻¹) := by group
  calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
    _ = 1 := by rw [hb1]; group

theorem d39_one_L
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hcase : V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L))
    {A : Subgroup (MulAut W)} (hA : A ∈ QhatStar M)
    (hAf : ∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) :
    orbSup T V = ⊤ ∨
      (V = orbSup T V ∧ Mp = L ∧ IsFFModule (autSec (L ⊔ T) V (fixV Mp)) ∧
        ∀ r : ℚ, qhatOf (autSec (L ⊔ T) V (fixV Mp)) = (r : WithTop ℚ) →
          ∃ n : ℕ, (∃ N : Fin (n + 1) → Subgroup W, N 0 = fixV Mp ∧ N (Fin.last n) = ⊤ ∧
            ∀ i : Fin n, XMod.IsInv ↥L (N i.castSucc) ∧ XMod.IsInv ↥L (N i.succ) ∧
              XMod.IsIrrSec ↥L (N i.castSucc) (N i.succ)) ∧ (n : ℚ) * r ≤ 2) := by
  obtain ⟨A', hA'2, hA'T, hA'3, hA'r, hA'f⟩ := exists_conj_offender_le hD hA hAf
  by_cases htop : orbSup T V = ⊤
  · exact Or.inl htop
  rcases hcase with hVT | hdeep
  · rcases d391V_proved W M Mp T L V hMp hD hqM hVT A' hA'2 hA'T hA'3 hA'r hA'f with h | hFF
    · exact absurd h htop
    · subst hMp
      exact Or.inr ⟨hVT, rfl, hFF, fun r hr =>
        chief_bound hD hVT hA'2 hA'T hA'3 hA'r hA'f htop hr⟩
  · exact Or.inl (d391Deep_of_inputs
      (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
          (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
          (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
          (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
      B5.asB51_holds asA21SQTKSection W M Mp T L V hMp hD hqM hdeep A' hA'2 hA'T hA'3 hA'r hA'f)

end CFSG.Quasithin.RonanD39
