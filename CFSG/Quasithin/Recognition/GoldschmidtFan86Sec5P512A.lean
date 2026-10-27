module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Cen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P512

theorem cen_mul {S : Subgroup G} {x y : G} (hx : x ∈ Cen (S : Set G)) (hy : y ∈ Cen (S : Set G)) :
    x * y ∈ Cen (S : Set G) :=
  ⟨S.mul_mem hx.1 hy.1, fun h hh => by
    rw [← mul_assoc, hx.2 h hh, mul_assoc, hy.2 h hh, ← mul_assoc]⟩

theorem fix_of_cen {ℓ : Line Γ} {i : ℤ} {y : G} (h : y ∈ Cen (ℓ.edgeStab (G := G) i : Set G)) :
    y • ℓ.vert i = ℓ.vert i ∧ y • ℓ.vert (i + 1) = ℓ.vert (i + 1) :=
  ⟨MulAction.mem_stabilizer_iff.1 h.1.1, MulAction.mem_stabilizer_iff.1 h.1.2⟩

theorem cen_pair (F : FanTree Γ G) (ℓ : Line Γ) {a : ℤ} {z₁ : G}
    (hz₁ : z₁ ∈ Cinv G (ℓ.vert (a + 2))) :
    z₁ ∈ Cen (ℓ.edgeStab (G := G) (a + 1) : Set G) ∧
      z₁ ∈ Cen (ℓ.edgeStab (G := G) (a + 2) : Set G) :=
  ⟨cinv_cen_right F ℓ (i := a + 1) (by rw [show a + 1 + 1 = a + 2 by ring]; exact hz₁),
    cinv_cen_left F ℓ hz₁⟩

variable {F : FanTree Γ G} (h510 : Fan510 F) (h511 : Fan511 F) (h40 : Fan40 F)
include h510 h511 h40

theorem no_long_core {T : Track Γ G} (hT : InXi T) {u : G} (hu : u ∈ T.line.ZZ) (hu1 : u ≠ 1)
    {a : ℤ} (h0 : u ∈ Cen (T.line.edgeStab (G := G) a : Set G))
    (h1 : u ∈ Cen (T.line.edgeStab (G := G) (a + 1) : Set G))
    (h2 : u ∈ Cen (T.line.edgeStab (G := G) (a + 2) : Set G)) : False := by
  obtain ⟨⟨a', b', tL, tR, hf⟩, huniv⟩ := coreSat2 h510 h511 h40 hT hu hu1
  have hP : ∀ k, u ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx u ∧ k + 1 ∈ T.line.fixIdx u := fun k hk => fix_of_cen hk
  obtain ⟨A, B, hA, hB, hcA⟩ := P514.exists_isCoreWith T.line hf.fix hP h1
  have hAa : A ≤ a := by
    by_contra hlt
    have hAe : A = a + 1 := by omega
    apply hcA.2.2.2.1
    rw [hAe, show a + 1 - 1 = a by ring]
    exact ⟨(fix_of_cen h0).1, h0⟩
  have hBa : a + 3 ≤ B := by
    by_contra hlt
    have hBe : B = a + 2 := by omega
    apply hcA.2.2.2.2
    rw [hBe]
    exact ⟨(fix_of_cen h2).1, h2⟩
  have := (huniv A B tL tR ⟨hf.fix, hcA⟩).1
  omega

theorem no_cinv_next {T : Track Γ G} (hT : InXi T) {z : G} {a : ℤ} (hz : z ∈ T.line.ZZ)
    (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2)) {z₁ : G}
    (hz₁ : z₁ ∈ Cinv G (T.line.vert (a + 2))) : False := by
  set ℓ := T.line with hℓ
  have hzα : z ∈ Cinv G (ℓ.vert (a + 1)) := fan512cen F h40 T z a hT hz hz1 hcore
  have hK₁ := P62.cinv_mem_nbrStab F hz₁
  have hadj : Γ.Adj (ℓ.vert (a + 2)) (ℓ.vert (a + 1)) := by
    have := (ℓ.adj (a + 1)).symm
    rwa [show a + 1 + 1 = a + 2 by ring] at this
  have hz₁α : z₁ ∈ MulAction.stabilizer G (ℓ.vert (a + 1)) :=
    MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK₁ _ hadj)
  have hcomm : z₁ * z = z * z₁ := hzα.2.2.2 z₁ hz₁α
  have hzz : z * z = 1 := hz.1
  have hz₁z₁ : z₁ * z₁ = 1 := hz₁.2.1
  have hww : (z * z₁) * (z * z₁) = 1 := by
    calc z * z₁ * (z * z₁) = z * (z₁ * z) * z₁ := by simp only [mul_assoc]
      _ = z * (z * z₁) * z₁ := by rw [hcomm]
      _ = (z * z) * (z₁ * z₁) := by simp only [mul_assoc]
      _ = 1 := by rw [hzz, hz₁z₁, one_mul]
  have hzE1 : z ∈ Cen (ℓ.edgeStab (G := G) (a + 1) : Set G) :=
    hcore.2.2.1 (a + 1) (by omega) (by omega)
  obtain ⟨hz₁E1, hz₁E2⟩ := cen_pair F ℓ hz₁
  have hwE1 : z * z₁ ∈ Cen (ℓ.edgeStab (G := G) (a + 1) : Set G) := cen_mul hzE1 hz₁E1
  have hwz : z * z₁ ∈ ℓ.ZZ := ⟨hww, a + 1, hwE1⟩
  have hcoreR : ¬ (z ∈ Cen (ℓ.edgeStab (G := G) (a + 2) : Set G)) := fun hc =>
    hcore.2.2.2.2 ⟨hcore.2.1 (a + 2) (by omega) le_rfl, hc⟩
  have hw1 : z * z₁ ≠ 1 := by
    intro h
    have hzz₁ : z = z₁ := by
      rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hz₁z₁]
    exact hcoreR (hzz₁ ▸ hz₁E2)
  have hE2 : ¬ (a + 2 ∈ ℓ.fixIdx (z * z₁) ∧
      z * z₁ ∈ Cen (ℓ.edgeStab (G := G) (a + 2) : Set G)) := by
    rintro ⟨-, hwE2⟩
    apply hcoreR
    have := cen_mul hwE2 hz₁E2
    rwa [mul_assoc, hz₁z₁, mul_one] at this
  have hE0 : ¬ (a + 1 - 1 ∈ ℓ.fixIdx (z * z₁) ∧
      z * z₁ ∈ Cen (ℓ.edgeStab (G := G) (a + 1 - 1) : Set G)) := by
    rintro ⟨-, hwE0⟩
    rw [show a + 1 - 1 = a by ring] at hwE0
    have hzE0 : z ∈ Cen (ℓ.edgeStab (G := G) a : Set G) := hcore.2.2.1 a le_rfl (by omega)
    have h0 := cen_mul hzE0 hwE0
    rw [← mul_assoc, hzz, one_mul] at h0
    exact no_long_core h510 h511 h40 hT ⟨hz₁z₁, a + 1, hz₁E1⟩ hz₁.1 h0 hz₁E1 hz₁E2
  have hcw : ℓ.IsCore (z * z₁) (a + 1) (a + 2) := by
    refine ⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, hE0, hE2⟩
    · rcases (show i = a + 1 ∨ i = a + 2 by omega) with rfl | rfl
      · exact (fix_of_cen hwE1).1
      · have := (fix_of_cen hwE1).2
        rwa [show a + 1 + 1 = a + 2 by ring] at this
    · rw [show i = a + 1 by omega]
      exact hwE1
  obtain ⟨⟨a', b', tL, tR, hf⟩, huniv⟩ := coreSat2 h510 h511 h40 hT hwz hw1
  have := (huniv (a + 1) (a + 2) tL tR ⟨hf.fix, hcw⟩).1
  omega

theorem fan512a_aux {T : Track Γ G} (hT : InXi T) {z : G} {a : ℤ} (hz : z ∈ T.line.ZZ)
    (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2)) {β : V}
    (hβ : ¬ Equiv3 G (T.line.vert (a + 1)) β) : Cinv G β = ∅ := by
  ext z₁
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz₁
  have hv1 : valence Γ β ≠ valence Γ (T.line.vert (a + 1)) := fun h =>
    hβ (P62.exists_smul_of_valence_eq F h)
  have hv2 : valence Γ (T.line.vert (a + 2)) ≠ valence Γ (T.line.vert (a + 1)) := by
    have := F.alternating _ _ (T.line.adj (a + 1))
    rw [show a + 1 + 1 = a + 2 by ring] at this
    exact fun h => this h.symm
  have h3 : valence Γ β = 3 ∨ valence Γ β = 5 := F.valence β
  have h4 : valence Γ (T.line.vert (a + 2)) = 3 ∨ valence Γ (T.line.vert (a + 2)) = 5 :=
    F.valence _
  have h5 : valence Γ (T.line.vert (a + 1)) = 3 ∨ valence Γ (T.line.vert (a + 1)) = 5 :=
    F.valence _
  obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := T.line.vert (a + 2)) (w := β)
    (by omega)
  have := cinv_conj hz₁ g⁻¹
  rw [← hg, inv_smul_smul] at this
  exact no_cinv_next h510 h511 h40 hT hz hz1 hcore this

end P512

theorem fan512a (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) : Fan512a F := by
  intro h40 T z a hT hz hz1 hcore β hβ
  exact P512.fan512a_aux h510 h511 h40 hT hz hz1 hcore hβ

end CFSG.Quasithin.Fan86
