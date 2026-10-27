module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.M23Sigma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
import CFSG.Quasithin.Background.E2TwoProofSporM23
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB
  CFSG.Quasithin.H.MathieuLat CFSG.Blueprint

namespace Stellmacher.L3YC

namespace Row13

theorem idx_eq_21 : ∀ j < 16, (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[j]! = 21 → j = 4 ∨ j = 6 := by decide

theorem idx_coprime_two : ∀ j < 16, Nat.Coprime ((#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[j]!) 2 := by decide

theorem idx_dvd_21 : ∀ j < 16, (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[j]! ∣ 21 →
    j = 0 ∨ j = 4 ∨ j = 6 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by decide

theorem m23_core
    {S₁ Y P : Subgroup ↥NativeSporadic.M23} (hS : IsSylowTwoOf S₁ ⊤) (hSY : S₁ ≤ Y)
    (hSP : S₁ ≤ P) (hY : Nat.card Y = 2 ^ 7 * 21) (hP : ∃ K : ℕ, Nat.card P ∣ 2 ^ K * 21)
    {e x σ : ↥NativeSporadic.M23} (he : e ∈ Y) (he3 : orderOf e = 3) (hx : x ∈ P) (hxY : x ∉ Y)
    (hx3 : orderOf x = 3) (hcomm : e * x = x * e) (hσ : σ ∈ S₁) (hinv : σ * e * σ⁻¹ = e⁻¹)
    (hcen : σ * x * σ⁻¹ = x) : False := by
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := m23_lat_cert.2.2
  have hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have hΓc : Nat.card ↥NativeSporadic.M23 = 79695 * 2 ^ 7 := by rw [m23CtxB.hΓ, hN]; rfl
  have hCS : IsSylowTwoOf m23CtxB.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m23CtxB.S
    rw [m23CtxB.S_card, hΓc] at h1
    have h2 : m23CtxB.S.index = 79695 := by
      have : m23CtxB.k = 7 := rfl
      rw [this] at h1
      omega
    rw [h2]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.L246C127.exists_conj_of_isSylowTwoOf' hS hCS
  set c : MulAut ↥NativeSporadic.M23 := MulAut.conj g with hc
  have hmem : ∀ (A : Subgroup ↥NativeSporadic.M23) (a : ↥NativeSporadic.M23),
      c a ∈ A.map c.toMonoidHom ↔ a ∈ A := fun A a => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hcard : ∀ A : Subgroup ↥NativeSporadic.M23, Nat.card (A.map c.toMonoidHom) = Nat.card A :=
    fun A => Subgroup.card_map_of_injective c.injective
  have hSle : ∀ A : Subgroup ↥NativeSporadic.M23, S₁ ≤ A → m23CtxB.S ≤ A.map c.toMonoidHom :=
    fun A hA => hg ▸ Subgroup.map_mono hA
  have hsize : (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ).size
      = 16 := rfl
  have hmo : ∀ j, j < 16 → memberOrTop 16 m23CtxB.Y j = m23CtxB.Y j := fun j hj => by
    simp [memberOrTop, hj]
  have hmoT : memberOrTop 16 m23CtxB.Y 16 = ⊤ := by simp [memberOrTop]
  have hcardY : ∀ j < 16, Nat.card (m23CtxB.Y j) =
      (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[j]! * 2 ^ 7 :=
    fun j hj => lat_card m23CtxB hL j (by rw [hsize]; exact hj)
  have hall := lat_all m23CtxB hL
  rw [hsize] at hall
  obtain ⟨j, hj, hjY⟩ := hall _ (hSle Y hSY)
  have hj16 : j < 16 := by
    rcases Nat.lt_or_ge j 16 with h | h
    · exact h
    · exfalso
      have hj' : j = 16 := le_antisymm hj h
      rw [hj', hmoT] at hjY
      have := hcard Y
      rw [hjY, Subgroup.card_top, hΓc, hY] at this
      omega
  rw [hmo j hj16] at hjY
  have hjc : j = 4 ∨ j = 6 := by
    have h1 := hcardY j hj16
    rw [← hjY, hcard, hY] at h1
    have h2 : (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[j]! = 21 :=
      by omega
    exact idx_eq_21 j hj16 h2
  obtain ⟨k, hk, hkP⟩ := hall _ (hSle P hSP)
  obtain ⟨K, hK⟩ := hP
  have hk16 : k < 16 := by
    rcases Nat.lt_or_ge k 16 with h | h
    · exact h
    · exfalso
      have hk' : k = 16 := le_antisymm hk h
      rw [hk', hmoT] at hkP
      have h1 : Nat.card (P.map c.toMonoidHom) ∣ 2 ^ K * 21 := by rw [hcard]; exact hK
      rw [hkP, Subgroup.card_top, hΓc] at h1
      have h2 : 79695 ∣ 2 ^ K * 21 := (Dvd.intro _ rfl).trans h1
      have h3 : Nat.Coprime 79695 (2 ^ K) := Nat.Coprime.pow_right K (by norm_num)
      have := h3.dvd_of_dvd_mul_left h2
      omega
  rw [hmo k hk16] at hkP
  have hkc : k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by
    have h1 : Nat.card (m23CtxB.Y k) ∣ 2 ^ K * 21 := by rw [← hkP, hcard]; exact hK
    rw [hcardY k hk16] at h1
    have h2 : (#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[k]! ∣
        2 ^ K * 21 := (Dvd.intro _ rfl).trans h1
    have h3 : Nat.Coprime
        ((#[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] : Array ℕ)[k]!) (2 ^ K) :=
      Nat.Coprime.pow_right K (idx_coprime_two k hk16)
    exact idx_dvd_21 k hk16 (h3.dvd_of_dvd_mul_left h2)
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hxS : c x ∈ m23CtxB.S := by
      have := (hmem P x).mpr hx
      rw [hkP, m23CtxB.Y_zero] at this
      exact this
    have h1 := orderOf_dvd_natCard (⟨c x, hxS⟩ : m23CtxB.S)
    rw [m23CtxB.S_card] at h1
    have h3 : orderOf (⟨c x, hxS⟩ : m23CtxB.S) = 3 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (c x) = 3
      rw [MulEquiv.orderOf_eq]; exact hx3
    rw [h3] at h1
    exact absurd h1 (by show ¬ 3 ∣ 2 ^ 7; decide)
  have hkmem : k ∈ ({4, 6, 10, 11, 12, 13, 14} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hjmem : j ∈ ({4, 6} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hjc
  refine m23_sigma_test j hjmem k hkmem (c e) (c x) (c σ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hjY]; exact (hmem Y e).mpr he
  · rw [MulEquiv.orderOf_eq]; exact he3
  · rw [← hkP]; exact (hmem P x).mpr hx
  · rw [← hjY]; exact fun h => hxY ((hmem Y x).mp h)
  · rw [MulEquiv.orderOf_eq]; exact hx3
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [hg.symm]; exact (hmem S₁ σ).mpr hσ
  · rw [← map_mul, ← map_inv, ← map_mul, hinv, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hcen]

end Row13

end Stellmacher.L3YC

end CFSG.Quasithin
