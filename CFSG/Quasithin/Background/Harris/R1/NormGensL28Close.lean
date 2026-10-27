module

public import CFSG.Quasithin.Background.Harris.R1.SignChoice

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

theorem conj_sigma_pt {σ : Ω → G} {u : G} (hu : u ∈ signStab C σ) (hB : u ∈ borelOf K1 S) :
    u * σ C.D.pt * u⁻¹ = σ C.D.pt := by
  obtain ⟨huK, h⟩ := hu
  rw [h C.D.pt, (C.D.stab ⟨u, huK⟩).mpr hB]

theorem exists_act_eq_of_mem_sup {a b : G} (ha : a ∈ K1) (hb : b ∈ K1)
    (hWK : vBeta K1 L2 S Zs ≤ K1) {k : G}
    (hk : k ∈ vBeta K1 L2 S Zs ⊔ Subgroup.closure ({a, b} : Set G)) :
    ∃ hkK : k ∈ K1, ∃ w ∈ Subgroup.closure ({a, b} : Set G), ∃ hwK : w ∈ K1,
      C.D.act ⟨k, hkK⟩ = C.D.act ⟨w, hwK⟩ := by
  have hcK : Subgroup.closure ({a, b} : Set G) ≤ K1 := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    exacts [ha, hb]
  rw [Subgroup.sup_eq_closure] at hk
  induction hk using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · refine ⟨hWK hy, 1, Subgroup.one_mem _, K1.one_mem, ?_⟩
      rw [act_eq_one_of_mem_vBeta C hy (hWK hy)]
      exact (map_one C.D.act).symm
    · exact ⟨hcK hy, y, hy, hcK hy, rfl⟩
  | one => exact ⟨K1.one_mem, 1, Subgroup.one_mem _, K1.one_mem, rfl⟩
  | mul y y' _ _ ihy ihy' =>
    obtain ⟨hyK, w, hw, hwK, hyw⟩ := ihy
    obtain ⟨hyK', w', hw', hwK', hyw'⟩ := ihy'
    refine ⟨K1.mul_mem hyK hyK', w * w', Subgroup.mul_mem _ hw hw', K1.mul_mem hwK hwK', ?_⟩
    have e1 : (⟨y * y', K1.mul_mem hyK hyK'⟩ : ↥K1) = ⟨y, hyK⟩ * ⟨y', hyK'⟩ := rfl
    have e2 : (⟨w * w', K1.mul_mem hwK hwK'⟩ : ↥K1) = ⟨w, hwK⟩ * ⟨w', hwK'⟩ := rfl
    rw [e1, e2, map_mul, map_mul, hyw, hyw']
  | inv y _ ih =>
    obtain ⟨hyK, w, hw, hwK, hyw⟩ := ih
    refine ⟨K1.inv_mem hyK, w⁻¹, Subgroup.inv_mem _ hw, K1.inv_mem hwK, ?_⟩
    have e1 : (⟨y⁻¹, K1.inv_mem hyK⟩ : ↥K1) = (⟨y, hyK⟩ : ↥K1)⁻¹ := rfl
    have e2 : (⟨w⁻¹, K1.inv_mem hwK⟩ : ↥K1) = (⟨w, hwK⟩ : ↥K1)⁻¹ := rfl
    rw [e1, e2, map_inv, map_inv, hyw]

theorem closure_signStab_eq {z : G} (hz : z ∈ Zs) (hz1 : z ≠ 1) {σ : Ω → G}
    (hσ : IsSignChoice C z σ) (hWK : vBeta K1 L2 S Zs ≤ K1) {a b : G}
    (ha : a ∈ signStab C σ) (hb : b ∈ signStab C σ)
    (hab : vBeta K1 L2 S Zs ⊔ Subgroup.closure ({a, b} : Set G) = K1) {x : G}
    (hx : x = σ C.D.pt ∨ x = z * σ C.D.pt) :
    Subgroup.closure ({z, x, a, b} : Set G) = K1 := by
  set H := Subgroup.closure ({z, x, a, b} : Set G) with hH
  have haK : a ∈ K1 := signStab_le C σ ha
  have hbK : b ∈ K1 := signStab_le C σ hb
  have hzW : z ∈ vBeta K1 L2 S Zs := F112J2.Zs_le_vBeta K1 L2 S Zs hz
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  have hσW : ∀ ω, σ ω ∈ vBeta K1 L2 S Zs := fun ω => hσ.mem_vBeta C hz ω
  have hHK : H ≤ K1 := by
    rw [hH, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hWK hzW
    · rcases hx with rfl | rfl
      · exact hWK (hσW _)
      · exact hWK ((vBeta K1 L2 S Zs).mul_mem hzW (hσW _))
    · exact haK
    · exact hbK
  have habH : Subgroup.closure ({a, b} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    exacts [haH, hbH]
  have habσ : Subgroup.closure ({a, b} : Set G) ≤ signStab C σ := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    exacts [ha, hb]
  have hσpt : σ C.D.pt ∈ H := by
    rcases hx with h | h
    · exact h ▸ hxH
    · have hzz : z * z = 1 := C.Zs_sq hz
      have : σ C.D.pt = z * x := by rw [h, ← mul_assoc, hzz, one_mul]
      rw [this]
      exact H.mul_mem hzH hxH
  have hσH : ∀ ω, σ ω ∈ H := by
    intro ω
    obtain ⟨k, hk⟩ := C.D.trans ω
    have hkS : (k : G) ∈ vBeta K1 L2 S Zs ⊔ Subgroup.closure ({a, b} : Set G) := by
      rw [hab]; exact k.2
    obtain ⟨hkK, w, hw, hwK, hkw⟩ := exists_act_eq_of_mem_sup C haK hbK hWK hkS
    have hwσ := habσ hw
    obtain ⟨hwK', hwact⟩ := hwσ
    have hω : C.D.act ⟨w, hwK'⟩ C.D.pt = ω := by
      have : C.D.act ⟨w, hwK'⟩ = C.D.act ⟨(k : G), hkK⟩ := hkw.symm
      rw [this]
      exact hk
    have := hwact C.D.pt
    rw [hω] at this
    rw [← this]
    exact H.mul_mem (H.mul_mem (habH hw) hσpt) (H.inv_mem (habH hw))
  have hWH : vBeta K1 L2 S Zs ≤ H := by
    rw [C.U_eq_closure hz hz1, Subgroup.closure_le]
    rintro y (rfl | ⟨ω, rfl⟩)
    · exact hzH
    · rcases hσ ω with h | h
      · rw [← h]; exact hσH ω
      · have hzz : z * z = 1 := C.Zs_sq hz
        have : C.zf ω = z * σ ω := by rw [h, ← mul_assoc, hzz, one_mul]
        rw [this]
        exact H.mul_mem hzH (hσH ω)
  exact le_antisymm hHK (hab ▸ sup_le hWH habH)

end CFSG.Quasithin.Background.Harris.R1
