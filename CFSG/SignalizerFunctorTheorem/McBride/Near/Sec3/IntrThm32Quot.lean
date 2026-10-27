module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type u} [Group Γ] {R : Subgroup Γ}

theorem isChiefFactorOf_qimg {H L : Subgroup Γ} (hHN : H ≤ AChief.nrm R)
    (h : IsChiefFactorOf H L R) :
    IsChiefFactorOf (AChief.qimg R H) (AChief.qimg R L) ⊥ := by
  obtain ⟨hR, hL, hlt, hmin⟩ := h
  have hLN : L ≤ AChief.nrm R := hL.1.trans hHN
  refine ⟨⟨bot_le, ?_⟩, ⟨SolQuot.qimg_mono hL.1, AChief.qimg_le_normalizer hL.2⟩, ?_, ?_⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup (AChief.QG R)).Normal)]
    exact le_top
  · refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    exact hlt.not_ge ((SolQuot.qimg_eq_bot_iff hLN).mp hb)
  · intro K' hK' _ hK'L
    have hMN : L ⊓ SolQuot.qpre R K' ≤ AChief.nrm R := inf_le_left.trans hLN
    have hqM : AChief.qimg R (L ⊓ SolQuot.qpre R K') = K' := by
      rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm K') (SolQuot.le_qpre K'),
        SolQuot.qimg_qpre]
      exact inf_eq_right.mpr hK'L
    have hRM : R ≤ L ⊓ SolQuot.qpre R K' := le_inf hlt.le (SolQuot.le_qpre K')
    have hMH : L ⊓ SolQuot.qpre R K' ≤ H := inf_le_left.trans hL.1
    have hnorM : H ≤ Subgroup.normalizer ((L ⊓ SolQuot.qpre R K' : Subgroup Γ) : Set Γ) := by
      refine (SolQuot.qimg_le_normalizer_iff (R := R) (Y := H) (M := L ⊓ SolQuot.qpre R K')
        (X := H) hMH (inf_le_right.trans hRM) hHN le_rfl).mp ?_
      rw [hqM]
      exact hK'.2
    rcases hmin (L ⊓ SolQuot.qpre R K') ⟨hMH, hnorM⟩ hRM inf_le_left with h | h
    · left
      rw [← hqM, h, SolQuot.qimg_self]
    · right
      rw [← hqM, h]

theorem qimg_inf_centralizer_eq_bot {G X₁ : Subgroup Γ} (hGN : G ≤ AChief.nrm R)
    (hX₁G : X₁ ≤ G) (hGX : G ≤ Subgroup.normalizer (X₁ : Set Γ))
    (hsec : G ⊓ sectionCentralizer R X₁ ≤ R) :
    AChief.qimg R G ⊓ Subgroup.centralizer
      ((AChief.qimg R X₁ : Subgroup (AChief.QG R)) : Set (AChief.QG R)) = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hzG, hzC⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨g, hg, rfl⟩ := (AChief.mem_qimg_iff R G z).mp hzG
  have hgR : (g : Γ) ∈ R := by
    refine hsec (Subgroup.mem_inf.mpr ⟨hg, g.2, hGX hg, fun y hy => ?_⟩)
    have hyN : y ∈ AChief.nrm R := hGN (hX₁G hy)
    have h1 := Subgroup.mem_centralizer_iff.mp hzC (AChief.qmap R ⟨y, hyN⟩)
      ((AChief.mem_qimg_iff R X₁ _).mpr ⟨⟨y, hyN⟩, hy, rfl⟩)
    have h2 : AChief.qmap R (g * ⟨y, hyN⟩ * g⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have h3 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    simpa [commutatorElement_def] using h3
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hgR))

theorem exists_preimage {A : Subgroup Γ} (hA : A ≤ AChief.nrm R) {B' : Subgroup (AChief.QG R)}
    (hB' : B' ≤ AChief.qimg R A) (hcyc : CyclicMod (AChief.qimg R A) B') :
    ∃ B : Subgroup Γ, B ≤ A ∧ AChief.qimg R B = B' ∧ CyclicMod A B := by
  have hBle : A ⊓ SolQuot.qpre R B' ≤ A := inf_le_left
  have hBN : A ⊓ SolQuot.qpre R B' ≤ AChief.nrm R := hBle.trans hA
  have hqB : AChief.qimg R (A ⊓ SolQuot.qpre R B') = B' := by
    rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm B') (SolQuot.le_qpre B'), SolQuot.qimg_qpre]
    exact inf_eq_right.mpr hB'
  refine ⟨A ⊓ SolQuot.qpre R B', hBle, hqB, ?_⟩
  obtain ⟨b, hbA, hle⟩ := hcyc
  obtain ⟨a₀, ha₀, rfl⟩ := (AChief.mem_qimg_iff R A b).mp hbA
  have hza : Subgroup.zpowers (a₀ : Γ) ≤ A := Subgroup.zpowers_le.mpr ha₀
  have hMA : (A ⊓ SolQuot.qpre R B') ⊔ Subgroup.zpowers (a₀ : Γ) ≤ A := sup_le hBle hza
  have hRM : A ⊓ R ≤ (A ⊓ SolQuot.qpre R B') ⊔ Subgroup.zpowers (a₀ : Γ) :=
    le_sup_of_le_left (le_inf inf_le_left (inf_le_right.trans (SolQuot.le_qpre B')))
  have hqM : AChief.qimg R ((A ⊓ SolQuot.qpre R B') ⊔ Subgroup.zpowers (a₀ : Γ)) =
      B' ⊔ Subgroup.zpowers (AChief.qmap R a₀) := by
    rw [SolQuot.qimg_sup hBN (hza.trans hA), hqB]
    exact congrArg (B' ⊔ ·) (SolQuot.qimg_zpowers a₀.2)
  refine ⟨(a₀ : Γ), ha₀, fun a ha => ?_⟩
  refine SolQuot.mem_of_qmap_mem_qimg (R := R) (Y := A) hMA hRM (z := ⟨a, hA ha⟩) ha ?_
  rw [hqM]
  exact hle ((AChief.mem_qimg_iff R A _).mpr ⟨⟨a, hA ha⟩, ha, rfl⟩)

theorem inf_centralizer_self_eq_bot {H Z : Subgroup Γ} (h : IsChiefFactorOf H Z ⊥)
    (hns : ¬ Group.IsSolvable ↥Z) : Z ⊓ Subgroup.centralizer (Z : Set Γ) = ⊥ := by
  have hn : H ≤ Subgroup.normalizer ((Z ⊓ Subgroup.centralizer (Z : Set Γ) : Subgroup Γ) : Set Γ) :=
    le_normalizer_inf h.2.1.2 (le_normalizer_centralizer h.2.1.2)
  rcases h.2.2.2 (Z ⊓ Subgroup.centralizer (Z : Set Γ)) ⟨inf_le_left.trans h.2.1.1, hn⟩ bot_le
    inf_le_left with h1 | h1
  · exact h1
  · exfalso
    apply hns
    have hZc : Z ≤ Subgroup.centralizer (Z : Set Γ) := inf_eq_left.mp h1
    exact Group.isSolvable_of_comm fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hZc a.2) b b.2).symm

theorem inf_centralizer_eq_bot [Finite Γ] {C Z D' : Subgroup Γ}
    (hC : C ≤ Subgroup.normalizer (Z : Set Γ)) (hDC : D' ≤ C) (hsup : C ≤ Z ⊔ D')
    (hD' : Group.IsSolvable ↥D') (hcenter : Z ⊓ Subgroup.centralizer (Z : Set Γ) = ⊥)
    (hsol : sol C = ⊥) : C ⊓ Subgroup.centralizer (Z : Set Γ) = ⊥ := by
  have hMC : C ⊓ Subgroup.centralizer (Z : Set Γ) ≤ C := inf_le_left
  have hMN : C ⊓ Subgroup.centralizer (Z : Set Γ) ≤ AChief.nrm Z := hMC.trans hC
  have hDN : D' ≤ AChief.nrm Z := hDC.trans hC
  have hMZ : (C ⊓ Subgroup.centralizer (Z : Set Γ)) ⊓ Z = ⊥ := by
    rw [eq_bot_iff, ← hcenter, inf_comm Z]
    exact inf_le_inf_right _ inf_le_right
  have hinj : Function.Injective (SolQuot.qres Z (C ⊓ Subgroup.centralizer (Z : Set Γ)) hMN) := by
    rw [← MonoidHom.ker_eq_bot_iff, SolQuot.ker_qres, eq_bot_iff]
    intro x hx
    have h1 : (x : Γ) ∈ (C ⊓ Subgroup.centralizer (Z : Set Γ)) ⊓ Z :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hMZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hsolD : Group.IsSolvable ↥(AChief.qimg Z D') :=
    Group.isSolvable_of_surjective (SolQuot.qres_surjective hDN)
  have hle : AChief.qimg Z (C ⊓ Subgroup.centralizer (Z : Set Γ)) ≤ AChief.qimg Z D' := by
    have h1 : AChief.qimg Z C ≤ AChief.qimg Z (Z ⊔ D') := SolQuot.qimg_mono hsup
    rw [SolQuot.qimg_sup Subgroup.le_normalizer hDN, SolQuot.qimg_self, bot_sup_eq] at h1
    exact (SolQuot.qimg_mono hMC).trans h1
  have hsolM : Group.IsSolvable ↥(AChief.qimg Z (C ⊓ Subgroup.centralizer (Z : Set Γ))) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hsolM' : Group.IsSolvable ↥(C ⊓ Subgroup.centralizer (Z : Set Γ)) :=
    Group.isSolvable_of_isSolvable_injective hinj
  have hCM : C ≤ AChief.nrm (C ⊓ Subgroup.centralizer (Z : Set Γ)) :=
    le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hC)
  have h2 := SolQuot.inf_le_sol hsolM' hCM
  rw [hsol] at h2
  exact le_bot_iff.mp ((le_inf inf_le_left le_rfl).trans h2)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32
