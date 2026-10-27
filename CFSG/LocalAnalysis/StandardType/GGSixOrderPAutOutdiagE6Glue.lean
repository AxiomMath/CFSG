module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagExcPpd
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Model
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Frames

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

section Inputs

@[expose] def GGE6NontoralFixPpdInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → 3 ∣ 2 ^ f - 1 →
    ∀ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), α ^ 3 = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
      ∃ r, (∃ e ∈ ggOutdiagExpsE6, IsTwoPowPpd f e r) ∧
        ∃ z : adjointGroup .E6 (GaloisField 2 f), orderOf z = r ∧ α z = z

@[expose] def GGE6ToralFixNoPpdInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → 3 ∣ 2 ^ f - 1 →
    ∀ α : MulAut (adjointGroup .E6 (GaloisField 2 f)), α ≠ 1 → α ^ 3 = 1 →
      LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
      ∀ r, (∃ e ∈ ggOutdiagExpsE6, IsTwoPowPpd f e r) →
        ∀ z : adjointGroup .E6 (GaloisField 2 f), orderOf z = r → α z ≠ z

end Inputs

section E6

theorem GGOutdiagPrimeConfig.of_E6 {p n f : ℕ} (h : GGOutdiagPrimeConfig p .E6 n f) :
    p = 3 ∧ 3 ∣ 2 ^ f - 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp, h3⟩ | ⟨h, -⟩
  · exact nomatch h
  · exact nomatch h
  · exact ⟨hp, h3⟩
  · exact nomatch h

theorem ggOutdiagTwistedPpdAt_E6_of_input (hK1 : GGE6NontoralFixPpdInput) :
    GGOutdiagTwistedPpdAt .E6 ggOutdiagExpsE6 := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hcfg y hyN hyo hyi hnc
  obtain ⟨rfl, h3⟩ := GGOutdiagPrimeConfig.of_E6 hcfg
  obtain ⟨χ, hχ, hrange, hind, -, hyt⟩ := OutdiagE6.exists_frame_data hS h3
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hχN : χ.range ≤ Subgroup.normalizer (G₀ : Set G) := by
    rw [hrange]
    exact Subgroup.le_normalizer
  have hy3 : y ^ 3 = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  obtain ⟨α, hαD, hα⟩ := hind y hyN hyi
  have hα3 : α ^ 3 = 1 := by
    have h1 := hα.pow 3
    rw [hy3] at h1
    exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
  have hnt : ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) := fun hT => by
    obtain ⟨m, hm, hmB⟩ := hyt y hyN hy3 α hα hαD hT
    exact hnc m hm hmB
  obtain ⟨r, hr, z, hzo, hαz⟩ := hK1 f hf h3 α hαD hα3 hnt
  refine ⟨r, hr, χ z, ⟨hχN ⟨z, rfl⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    calc y * χ z = (y * χ z * y⁻¹) * y := by group
      _ = χ (α z) * y := by rw [hα z]
      _ = χ z * y := by rw [hαz]
  · rw [orderOf_injective χ hχ z, hzo]

theorem ggOutdiagToralNoPpdAt_E6_of_input (hK2 : GGE6ToralFixNoPpdInput) :
    GGOutdiagToralNoPpdAt .E6 ggOutdiagExpsE6 := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hcfg b hb hb1 r hr z hz hzr
  obtain ⟨rfl, h3⟩ := GGOutdiagPrimeConfig.of_E6 hcfg
  obtain ⟨χ, hχ, hrange, hind, hbt, -⟩ := OutdiagE6.exists_frame_data hS h3
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hC : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  obtain ⟨e, he, hppd⟩ := hr
  have he' : e = 9 ∨ e = 12 := by
    simpa [ggOutdiagExpsE6] using he
  have hef : 3 ≤ e * f := by
    rcases he' with rfl | rfl <;> omega
  have hrp : r.Prime := hppd.1
  have hr2 : r ≠ 2 := hppd.ne_two (by omega)
  have hr3 : r ≠ 3 := hppd.ne_three hef
  have hrf : ¬ r ∣ f := hppd.not_dvd (by rcases he' with rfl | rfl <;> omega) hf
  have hzr1 : z ^ r = 1 := by
    rw [← hzr]
    exact pow_orderOf_eq_one z
  have hzN : z ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hz.1
  obtain ⟨z', rfl⟩ := OutdiagE6.mem_range_of_pow_eq_one hf hrp hr2 hr3 hrf hχ hC hzN hzr1
  have hbN : b ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hS.2.2.2.1.1 hb
  obtain ⟨α, hbα⟩ := OutdiagModel.exists_induces hχ hbN
  have hb3 : b ^ 3 = 1 := hS.2.2.2.1.2.1.2 b hb
  have hα3 : α ^ 3 = 1 := by
    have h1 := hbα.pow 3
    rw [hb3] at h1
    exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
  have hα1 : α ≠ 1 := by
    intro h
    rw [h] at hbα
    exact hb1 (OutdiagModel.Induces.inj hC hbα OutdiagModel.Induces.one)
  have hfix : α z' = z' := by
    refine hχ ?_
    rw [← hbα z']
    have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 b (Set.mem_singleton b)
    calc b * χ z' * b⁻¹ = (χ z' * b) * b⁻¹ := by rw [← hcomm]
      _ = χ z' := by group
  have hord : orderOf z' = r := by
    rw [← orderOf_injective χ hχ z']
    exact hzr
  exact hK2 f hf h3 α hα1 hα3 (hbt b hb α hbα) r ⟨e, he, hppd⟩ z' hord hfix

end E6

end CFSG.StandardType
