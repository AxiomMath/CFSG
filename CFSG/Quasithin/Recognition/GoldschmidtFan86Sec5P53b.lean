module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem not_lineSingLe_of_fan40 {F : FanTree Γ G} (h40 : Fan40 F) (ℓ : Line Γ) {n : ℕ}
    (hn : n ≤ 3) : ¬ LineSingLe Γ G ℓ n := by
  rintro ⟨k, a, hk1, hk2, h | h⟩
  · exact lineNSR_of_fan40 h40 ℓ hk1 (by omega) a h
  · exact lineNSL_of_fan40 h40 ℓ hk1 (by omega) a h

namespace Line

theorem cen_edgeCirc_of_cen_edgeStab (ℓ : Line Γ) {z : G} (hzz : z * z = 1) {i : ℤ}
    (hz : z ∈ Cen (ℓ.edgeStab (G := G) i : Set G)) : z ∈ Cen (ℓ.edgeCirc (G := G) i) := by
  have hz' : z ∈ ℓ.edgeStab (G := G) i := hz.1
  refine ⟨?_, fun h hh => hz.2 h ?_⟩
  · unfold edgeCirc
    split_ifs
    · exact ⟨hz', by rw [hzz]; exact one_mem _⟩
    · exact ⟨⟨hz'.2, hz'.1⟩, by rw [hzz]; exact one_mem _⟩
  · have := ℓ.edgeCirc_fix hh
    exact ⟨MulAction.mem_stabilizer_iff.2 this.1, MulAction.mem_stabilizer_iff.2 this.2⟩

theorem one_mem_cen_edgeCirc (ℓ : Line Γ) (i : ℤ) : (1 : G) ∈ Cen (ℓ.edgeCirc (G := G) i) :=
  ℓ.cen_edgeCirc_of_cen_edgeStab (mul_one 1) ⟨one_mem _, fun h _ => by simp⟩

end Line

theorem cen_edgeStab_of_cen_edgeCirc (F : FanTree Γ G) (h36 : Fan36 F) (h40 : Fan40 F)
    (ℓ : Line Γ) {z : G} (hzz : z * z = 1) {b : ℤ}
    (hz1 : z ∈ Cen (ℓ.edgeStab (G := G) (b - 1) : Set G))
    (hz2 : z ∈ Cen (ℓ.edgeCirc (G := G) b)) : z ∈ Cen (ℓ.edgeStab (G := G) b : Set G) := by
  have hz1' := ℓ.cen_edgeCirc_of_cen_edgeStab hzz hz1
  have hs := not_lineSingLe_of_fan40 h40 ℓ (n := 2 - 1) (by norm_num)
  obtain ⟨y, hyH, hyo⟩ := fan51a F h36 h40 ℓ (b - 1) 2 le_rfl hs 1 le_rfl (by norm_num)
  have e1 : b - 1 + ((1 : ℕ) : ℤ) = b := by push_cast; ring
  have e2 : b - 1 + ((2 - 1 : ℕ) : ℤ) = b := by norm_num
  rw [e2] at hyH
  rw [e1] at hyo
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
    refine closure_le_centralizer (S := ℓ.edgeCirc (b - 1) ∪ ℓ.edgeCirc b) ?_ hyH.1
    rintro s (hs | hs)
    · exact hz1'.2 s hs
    · exact hz2.2 s hs
  have hcy : Commute y z := (Subgroup.mem_centralizer_iff.1 hyC z rfl).symm
  have hyz : ∀ i : ℕ, y ^ i * z = z * y ^ i := fun i => (hcy.pow_left i).eq
  have hGb : ∀ g ∈ MulAction.stabilizer G (ℓ.vert b), g * z = z * g := by
    intro g hg
    have hg' : g • ℓ.vert b = ℓ.vert b := MulAction.mem_stabilizer_iff.1 hg
    have hadj : Γ.Adj (ℓ.vert b) (ℓ.vert (b - 1)) := by
      have := (ℓ.adj (b - 1)).symm
      rwa [show b - 1 + 1 = b by omega] at this
    have hadj' : Γ.Adj (ℓ.vert b) (g • ℓ.vert (b - 1)) := by
      have := (F.adj_smul g _ _).2 hadj
      rwa [hg'] at this
    obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hyH.2 hyo hadj hadj'
    have hyb : (y ^ i)⁻¹ • ℓ.vert b = ℓ.vert b := by
      rw [inv_smul_eq_iff]
      exact (MulAction.mem_stabilizer_iff.1
        ((MulAction.stabilizer G (ℓ.vert b)).pow_mem hyH.2 i)).symm
    have he : (y ^ i)⁻¹ * g ∈ ℓ.edgeStab (G := G) (b - 1) := by
      refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
      · rw [mul_smul, ← hi, inv_smul_smul]
      · rw [show b - 1 + 1 = b by omega, mul_smul, hg', hyb]
    have hec := hz1.2 _ he
    have hy : Commute (y ^ i) z := hyz i
    have := hy.mul_left (show Commute ((y ^ i)⁻¹ * g) z from hec)
    rwa [mul_inv_cancel_left] at this
  refine ⟨?_, fun h hh => hGb h hh.1⟩
  have := ℓ.edgeCirc_fix hz2.1
  exact ⟨MulAction.mem_stabilizer_iff.2 this.1, MulAction.mem_stabilizer_iff.2 this.2⟩

theorem not_cen_edgeCirc_right (F : FanTree Γ G) (h36 : Fan36 F) (h40 : Fan40 F) (ℓ : Line Γ)
    {z : G} (hzz : z * z = 1) {a b : ℤ} (hcore : ℓ.IsCore z a b) :
    z ∉ Cen (ℓ.edgeCirc (G := G) b) := by
  intro hP
  obtain ⟨hab, hfix, hcen, -, hmax⟩ := hcore
  exact hmax ⟨hfix b hab.le le_rfl,
    cen_edgeStab_of_cen_edgeCirc F h36 h40 ℓ hzz (hcen (b - 1) (by omega) (by omega)) hP⟩

theorem fan53b (F : FanTree Γ G) (h36 : Fan36 F) : Fan53b F := by
  intro h40 ℓ z a b hz hcore
  have hzz : z * z = 1 := hz.1
  refine ⟨hcore.1, hcore.2.1,
    fun i h1 h2 => ℓ.cen_edgeCirc_of_cen_edgeStab hzz (hcore.2.2.1 i h1 h2), ?_, ?_⟩
  · rintro ⟨-, hP⟩
    refine not_cen_edgeCirc_right F h36 h40 ℓ.rev hzz hcore.rev ?_
    rw [Line.rev_edgeCirc ℓ F, show -(-a) - 1 = a - 1 by omega]
    exact hP
  · rintro ⟨-, hP⟩
    exact not_cen_edgeCirc_right F h36 h40 ℓ hzz hcore hP

theorem fan53c (F : FanTree Γ G) (h36 : Fan36 F) : Fan53c F := by
  intro h40 ℓ z a b hz hcore
  by_contra hcon
  obtain ⟨hab, hfix, hcen, -, hmax⟩ := hcore
  have hs := not_lineSingLe_of_fan40 h40 ℓ (n := 3 - 1) (by norm_num)
  have e : a + ((3 - 1 : ℕ) : ℤ) = a + 2 := by norm_num
  have hH : Subgroup.closure (ℓ.edgeCirc (G := G) a ∪ ℓ.edgeCirc (a + ((3 - 1 : ℕ) : ℤ))) ≤
      Subgroup.centralizer ({z} : Set G) := by
    refine closure_le_centralizer ?_
    rintro s (hs | hs)
    · exact (hcen a le_rfl (by omega)).2 s hs
    · rw [e] at hs
      exact (hcen (a + 2) (by omega) (by omega)).2 s hs
  obtain ⟨y1, hy1, hy1o⟩ := fan51a F h36 h40 ℓ a 3 (by norm_num) hs 1 le_rfl (by norm_num)
  obtain ⟨y2, hy2, hy2o⟩ := fan51a F h36 h40 ℓ a 3 (by norm_num) hs 2 (by norm_num) (by norm_num)
  have l1 := F.locTr_of_pow (hH hy1.1) hy1.2 hy1o
  have l2 := F.locTr_of_pow (hH hy2.1) hy2.2 hy2o
  rw [show a + ((1 : ℕ) : ℤ) = a + 1 by push_cast; ring] at l1
  rw [show a + ((2 : ℕ) : ℤ) = a + 1 + 1 by push_cast; ring] at l2
  have hz1 : z = 1 := F.eq_one_of_locTr_centralizer (ℓ.adj (a + 1))
    (hfix (a + 1) (by omega) (by omega)) (hfix (a + 1 + 1) (by omega) (by omega)) l1 l2
  refine hmax ⟨hfix b hab.le le_rfl, ?_⟩
  rw [hz1]
  exact ℓ.one_mem_cen_edgeCirc b

end CFSG.Quasithin.Fan86
