module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Hyper
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Coprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c11_barSub_self_eq_bot {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) :
    barSub V₀ V hV V = ⊥ := by
  refine le_bot_iff.1 fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV V φ).1 hφ
  rw [Subgroup.mem_bot, actTil_eq_one_iff]
  intro v hv
  have hc : (g : G) * v = v * (g : G) := by
    have := hV.1.is_comm.comm (⟨g, hg⟩ : V) ⟨v, hv⟩
    simpa using congrArg Subtype.val this
  have : (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact V₀.one_mem

theorem s16c11_barSub_gammaSet_zero_eq_bot_or_mem (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V)
    (hm : MBarGT D.M V₀ V 1) (hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hγ : V₀ = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V)
    (hTI : ∀ g : G, g ∉ D.M → conjSubgroup V g ≤ D.T → V ≤ conjSubgroup D.M g →
      V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.T) :
    barSub V₀ V hV A = ⊥ ∨ barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV := by
  obtain ⟨hAT, g, hAg, hA0⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg.isPGroup hAg).1 hA0
  subst hAeq
  by_cases hg : g ∈ D.M
  · left
    have hgN : g ∈ normalizer (V : Set G) := h.normalizer_eq ▸ hg
    have hVV : conjSubgroup V g = V := by
      ext x
      rw [mem_conjSubgroup_iff]
      exact (Subgroup.mem_normalizer_iff.1 hgN x).symm
    rw [hVV]
    exact s16c11_barSub_self_eq_bot hV
  · have hAM : conjSubgroup V g ≤ D.M := hAT.trans D.sylowM.le
    refine s16c11_barSub_conj_eq_bot_or_mem_calABar_two D hV h hAM hm hr ?_ ?_
    · rcases hγ with h0 | h1
      · exact Or.inl (by rw [h0]; exact bot_inf_eq _)
      · exact Or.inr h1
    · by_cases hVg' : V ≤ conjSubgroup D.M g
      · exact Or.inl (hTI g hg hAT hVg')
      · exact Or.inr hVg'

theorem s16c11_barSub_wClos_le_centralizer {M V₀ V T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : T ≤ stabTil V₀ V)
    (hA : ∀ A ∈ E3.gammaSet V 0 T,
      barSub V₀ V hV A = ⊥ ∨ barSub V₀ V hV A ∈ calABar 2 M V₀ V hV)
    {Y : Subgroup (MulAut (Vtil V₀ V hV))} (hY : ¬ 2 ∣ Nat.card Y)
    (hWY : barSub V₀ V hV (E3.wClos V 0 T) ≤ normalizer (Y : Set (MulAut (Vtil V₀ V hV)))) :
    barSub V₀ V hV (E3.wClos V 0 T) ≤ centralizer (Y : Set (MulAut (Vtil V₀ V hV))) := by
  have hsq := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hinner : ∀ A, (⨆ (_ : A ∈ E3.gammaSet V 0 T), A) ≤ stabTil V₀ V := fun A =>
    iSup_le fun hA' => hA'.1.trans hT
  have h1 := barSub_iSup_of_le (V₀ := V₀) hV (K := fun A => ⨆ (_ : A ∈ E3.gammaSet V 0 T), A)
    hinner
  unfold E3.wClos
  rw [h1]
  refine iSup_le fun A => ?_
  have h2 := barSub_iSup_of_le (V₀ := V₀) hV (K := fun _ : A ∈ E3.gammaSet V 0 T => A)
    (fun hA' => hA'.1.trans hT)
  rw [h2]
  refine iSup_le fun hAΓ => ?_
  rcases hA A hAΓ with h0 | hmem
  · rw [h0]
    exact bot_le
  · refine s16c11_le_centralizer_of_mem_aSet_two hsq hmem hY ?_
    exact (barSub_mono V₀ V hV (E3.le_wClos hAΓ)).trans hWY

theorem s16c11_normalizer_le_of_routeA (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V)
    (hA : ∀ A ∈ E3.gammaSet V 0 D.T,
      barSub V₀ V hV A = ⊥ ∨ barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV)
    {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup (MulAut (Vtil V₀ V hV))}
    (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P) (hPc : ¬ IsCyclic ↥P)
    (hPW : barSub V₀ V hV (E3.wClos V 0 D.T) ≤
      normalizer (P : Set (MulAut (Vtil V₀ V hV)))) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hTst : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMst
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hpp : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hodd : ¬ 2 ∣ Nat.card P := by
    intro h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
    rw [hk] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hcent := s16c11_barSub_wClos_le_centralizer hV hTst hA hodd hPW
  have hPW' : P ≤ normalizer ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) := by
    intro x hx
    have hx' : x ∈ centralizer (barSub V₀ V hV (E3.wClos V 0 D.T) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hcent hy) x hx).symm
    exact Subgroup.centralizer_le_normalizer _ hx'
  exact s16c11_normalizer_le_of_bar_noncyclic D h61 hV h hp hPM hPp hPc hPW'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
