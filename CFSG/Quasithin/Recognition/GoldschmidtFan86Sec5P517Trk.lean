module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517Ker
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512B

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

theorem exists_conj_track (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h40 : Fan40 F)
    (hXi : ∃ T : Track Γ G, InXi T) {α : V} {z : G} (hz : z ∈ Cinv G α) :
    ∃ (T : Track Γ G) (a : ℤ) (g : G), InXi T ∧ g • α = T.line.vert (a + 1) ∧
      g * z * g⁻¹ ∈ T.line.ZZ ∧ g * z * g⁻¹ ≠ 1 ∧ T.line.IsCore (g * z * g⁻¹) a (a + 2) := by
  obtain ⟨T, hT⟩ := hXi
  set ℓ := T.line with hℓ
  have hc : ∃ c : ℤ, valence Γ (ℓ.vert c) = valence Γ α := by
    by_cases h0 : valence Γ (ℓ.vert 0) = valence Γ α
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have h1 := F.alternating _ _ (ℓ.adj 0)
      have e0 : valence Γ (ℓ.vert 0) = 3 ∨ valence Γ (ℓ.vert 0) = 5 := F.valence _
      have e1 : valence Γ (ℓ.vert (0 + 1)) = 3 ∨ valence Γ (ℓ.vert (0 + 1)) = 5 := F.valence _
      have eα : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence _
      rw [zero_add] at e1 h1
      change valence Γ (ℓ.vert 0) ≠ valence Γ (ℓ.vert 1) at h1
      omega
  obtain ⟨c, hc⟩ := hc
  obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := ℓ.vert c) hc
  have hz' : g * z * g⁻¹ ∈ Cinv G (ℓ.vert c) := by
    rw [← hg]
    exact P512.cinv_conj hz g
  have hE0 : g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (c - 1) : Set G) :=
    P512.cinv_cen_right F ℓ (i := c - 1) (by rw [show c - 1 + 1 = c by ring]; exact hz')
  have hE1 : g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) c : Set G) := P512.cinv_cen_left F ℓ hz'
  have hzz : g * z * g⁻¹ ∈ ℓ.ZZ := ⟨hz'.2.1, c, hE1⟩
  obtain ⟨⟨a', b', tL, tR, hf⟩, huniv⟩ := P512.coreSat2 h510 h511 h40 hT hzz hz'.1
  have hP : ∀ k, g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) k : Set G) →
      k ∈ ℓ.fixIdx (g * z * g⁻¹) ∧ k + 1 ∈ ℓ.fixIdx (g * z * g⁻¹) := fun k hk => P512.fix_of_cen hk
  obtain ⟨A, B, hA, hB, hcA⟩ := P514.exists_isCoreWith ℓ hf.fix hP hE0
  have hBc : c + 1 ≤ B := by
    by_contra hlt
    have hBe : B = c := by omega
    apply hcA.2.2.2.2
    rw [hBe]
    exact ⟨(P512.fix_of_cen hE1).1, hE1⟩
  have h2 := (huniv A B tL tR ⟨hf.fix, hcA⟩).1
  have hAe : A = c - 1 := by omega
  have hBe : B = c - 1 + 2 := by omega
  subst hAe hBe
  exact ⟨T, c - 1, g, hT, by rw [show c - 1 + 1 = c by ring]; exact hg, hzz, hz'.1, hcA⟩

theorem nbrStab_of_conj (F : FanTree Γ G) (g : G) {v : V} {y : G}
    (h : g * y * g⁻¹ ∈ nbrStab Γ G (g • v)) : y ∈ nbrStab Γ G v := by
  have := F.conj_mem_nbrStab_smul g⁻¹ h
  rwa [inv_smul_smul, show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem ball2_conj (F : FanTree Γ G) (g : G) {v : V} {y : G}
    (h : g * y * g⁻¹ ∈ ballStab Γ G 2 (g • v)) : y ∈ ballStab Γ G 2 v := by
  obtain ⟨h1, h2⟩ := P512.nbrStab_of_ballStab_two h
  refine P512.ballStab_two_of F (nbrStab_of_conj F g h1) fun ν hν => ?_
  exact nbrStab_of_conj F g (v := ν) (h2 (g • ν) ((F.adj_smul g v ν).2 hν))

structure Lab5 (Γ : SimpleGraph V) (α : V) (z : G) : Prop where
  cinv : z ∈ Cinv G α
  val5 : valence Γ α = 5
  ball2 : z ∈ ballStab Γ G 2 α
  noCinv : ∀ β, ¬ Equiv3 G α β → Cinv G β = ∅
  ker : ∀ g : G, Γ.dist α (g • α) = 2 → g * z * g⁻¹ ∈ nbrStab Γ G α

theorem lab5_of (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (h40 : Fan40 F) (hXi : ∃ T : Track Γ G, InXi T) {α : V} {z : G} (hz : z ∈ Cinv G α)
    (hα : valence Γ α = 5) : Lab5 Γ α z := by
  obtain ⟨T, a, g, hT, hgα, hzZ, hz1, hcore⟩ := exists_conj_track F h510 h511 h40 hXi hz
  refine ⟨hz, hα, ?_, ?_, ?_⟩
  · apply ball2_conj F g (v := α)
    rw [hgα]
    exact P512.ball2_track F h510 h511 h53a h40 hT hzZ hz1 hcore
  · intro β hβ
    refine P512.fan512a_aux h510 h511 h40 hT hzZ hz1 hcore ?_
    rintro ⟨k, hk⟩
    exact hβ ⟨k * g, by rw [mul_smul, hgα, hk]⟩
  · intro g' hg'
    have hv : valence Γ (T.line.vert (a + 1)) = 5 := by
      rw [← hgα, F.valence_smul_eq]
      exact hα
    obtain ⟨ν, hν⟩ := P62.exists_br F hg'
    have hbr := P62.Br.smul F g hν
    have hkk : (g * g' * g⁻¹) • g • α = g • g' • α := by
      rw [mul_smul, mul_smul, inv_smul_smul]
    have hd : Γ.dist (T.line.vert (a + 1)) ((g * g' * g⁻¹) • T.line.vert (a + 1)) = 2 := by
      rw [← hgα, hkk]
      exact P62.Br.dist_two F hbr
    have := ker_track F h510 h511 h53a h40 hT hzZ hz1 hcore hv (g * g' * g⁻¹) hd
    rw [← hgα] at this
    refine nbrStab_of_conj F g (v := α) ?_
    have heq : g * (g' * z * g'⁻¹) * g⁻¹ = g * g' * g⁻¹ * (g * z * g⁻¹) * (g * g' * g⁻¹)⁻¹ := by
      group
    rw [heq]
    exact this

end P517

end CFSG.Quasithin.Fan86
