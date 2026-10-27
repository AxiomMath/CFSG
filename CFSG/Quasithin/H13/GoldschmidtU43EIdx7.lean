module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6Cen
public import CFSG.Quasithin.H13.GoldschmidtU43EA6Syl1
public import CFSG.Quasithin.H13.GoldschmidtU43EUas
public import CFSG.Quasithin.H13.GoldschmidtU43EMat5

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

theorem u43_unique_abelian_81_three {G : Type} [Group G] [Finite G] {M S M' : Subgroup G}
    (hMS : M ≤ S) (hMnorm : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M) (hM : Nat.card M = 81)
    (hS : Nat.card S = 81 * 3)
    (hF1 : ∀ x ∈ S, x ∉ M → Nat.card {m : ↥M // x * m = m * x} ≤ 9)
    (hM'S : M' ≤ S) (hM'ab : ∀ a ∈ M', ∀ b ∈ M', a * b = b * a) (hM' : Nat.card M' = 81) :
    M' = M := by
  by_contra hne
  have hnot : ∃ x ∈ M', x ∉ M := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_of_le_of_card_ge h (by rw [hM, hM']))
  obtain ⟨x, hxM', hxM⟩ := hnot
  have hxS : x ∈ S := hM'S hxM'
  have hKM : M ⊓ M' ≤ M := inf_le_left
  have hKM' : M ⊓ M' ≤ M' := inf_le_right
  have hK9 : Nat.card ↥(M ⊓ M') ≤ 9 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : ↥(M ⊓ M') => (⟨⟨k.1, hKM k.2⟩, hM'ab x hxM' k (hKM' k.2)⟩ :
        {m : ↥M // x * m = m * x})) ?_) (hF1 x hxS hxM)
    intro a b hab
    exact Subtype.ext (congrArg (fun t : {m : ↥M // x * m = m * x} => (t.1 : G)) hab)
  have h5 : M.relIndex M' * Nat.card ↥(M ⊓ M') = 81 := by
    rw [Subgroup.relIndex_mul_card, hM']
  have h6 : M.relIndex M' ∣ 3 := u43_relIndex_dvd hMS hMnorm hM'S hM hS
  have h7 : M.relIndex M' ≤ 3 := Nat.le_of_dvd (by decide) h6
  have := Nat.mul_le_mul h7 hK9
  omega

theorem card_fix_sq_le {X : Mat3} (h3 : X ^ 3 = 1) :
    Nat.card {v : Fin 4 → ZMod 3 // (X ^ 2).mulVec v = v} ≤
      Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v} := by
  refine Nat.card_le_card_of_injective (fun v => ⟨v.1, ?_⟩) ?_
  · calc X.mulVec v.1 = X.mulVec ((X ^ 2).mulVec v.1) := by rw [v.2]
      _ = (X * X ^ 2).mulVec v.1 := Matrix.mulVec_mulVec _ _ _
      _ = v.1 := by rw [← pow_succ' X 2, h3, Matrix.one_mulVec]
  · intro a b hab
    exact Subtype.ext (congrArg (fun t : {v : Fin 4 → ZMod 3 // X.mulVec v = v} => t.1) hab)

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem chiBar_npow (g : S.Nbar) (n : ℕ) : S.chiBar r (g ^ n) = S.chiBar r g ^ n :=
  map_pow (⟨⟨S.chiBar r, S.chiBar_one r⟩, S.chiBar_mul r⟩ : S.Nbar →* Mat3) g n

theorem card_fix_chiBar_nu_le {ν : S.Nbar}
    (hrel : (ν * S.zbar = S.ubar * ν ∧ ν * S.ubar = (S.zbar * S.ubar) * ν) ∨
      (ν * S.zbar = (S.ubar * S.vbar) * ν ∧
        ν * (S.ubar * S.vbar) = (S.zbar * (S.ubar * S.vbar)) * ν)) :
    Nat.card {v : Fin 4 → ZMod 3 // (S.chiBar r ν).mulVec v = v} ≤ 9 := by
  rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply card_fix_of_A
    · have := congrArg (S.chiBar r) h1
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r] at this
      exact this
    · have := congrArg (S.chiBar r) h2
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r] at this
      exact this
  · apply card_fix_of_B
    · have := congrArg (S.chiBar r) h1
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r, S.chiBar_vbar r] at this
      exact this
    · have := congrArg (S.chiBar r) h2
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r, S.chiBar_vbar r] at this
      exact this

theorem card_centralizer_Mnu {ν : S.Nbar} (hν3 : ν ^ 3 = 1)
    (hrel : (ν * S.zbar = S.ubar * ν ∧ ν * S.ubar = (S.zbar * S.ubar) * ν) ∨
      (ν * S.zbar = (S.ubar * S.vbar) * ν ∧
        ν * (S.ubar * S.vbar) = (S.zbar * (S.ubar * S.vbar)) * ν))
    {P : Subgroup S.Nbar} (hP : P = Subgroup.zpowers ν) {x : G}
    (hx : x ∈ S.preimageNbar P) (hxM : x ∉ S.Mg) :
    Nat.card {m : ↥S.Mg // x * m = m * x} ≤ 9 := by
  obtain ⟨r⟩ := S.nonempty_Rho
  obtain ⟨hxN, hxP⟩ := S.mem_preimageNbar.mp hx
  have h1 : S.piN ⟨x, hxN⟩ ≠ 1 := fun h =>
    hxM ((QuotientGroup.eq_one_iff (⟨x, hxN⟩ : ↥S.Ng)).mp h)
  rw [hP] at hxP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxP
  have hX9 := S.card_fix_chiBar_nu_le r hrel
  have hX3 : S.chiBar r ν ^ 3 = 1 := by rw [← S.chiBar_npow r, hν3, S.chiBar_one r]
  have hν3' : ν ^ (3 : ℤ) = 1 := by simpa using hν3
  have hk3 : ν ^ k = ν ^ (k % 3) := zpow_eq_zpow_emod k hν3'
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hfix : Nat.card {v : Fin 4 → ZMod 3 // (S.chiN r ⟨x, hxN⟩).mulVec v = v} ≤ 9 := by
    rcases hmod with h | h | h
    · exfalso
      apply h1
      rw [← hk, hk3, h]
      simp
    · have : S.piN ⟨x, hxN⟩ = ν := by
        rw [← hk, hk3, h]
        simp
      rw [← S.chiBar_piN r, this]
      exact hX9
    · have : S.piN ⟨x, hxN⟩ = ν ^ 2 := by
        rw [← hk, hk3, h]
        simp
      rw [← S.chiBar_piN r, this, S.chiBar_npow r]
      exact (card_fix_sq_le hX3).trans hX9
  exact S.card_centralizer_le r ⟨x, hxN⟩ hfix

theorem unique_abelian_Mnu {ν : S.Nbar} (hν3 : ν ^ 3 = 1)
    (hrel : (ν * S.zbar = S.ubar * ν ∧ ν * S.ubar = (S.zbar * S.ubar) * ν) ∨
      (ν * S.zbar = (S.ubar * S.vbar) * ν ∧
        ν * (S.ubar * S.vbar) = (S.zbar * (S.ubar * S.vbar)) * ν))
    {P : Subgroup S.Nbar} (hP : P = Subgroup.zpowers ν) (hP3 : Nat.card P = 3)
    {M' : Subgroup G} (hM'S : M' ≤ S.preimageNbar P)
    (hab : ∀ a ∈ M', ∀ b ∈ M', a * b = b * a) (hcard : Nat.card M' = 81) : M' = S.Mg := by
  refine u43_unique_abelian_81_three (S.Mg_le_preimageNbar _) ?_ S.card_Mg_eq_81
    (by rw [S.card_preimageNbar, hP3]) ?_ hM'S hab hcard
  · intro s hs m hm
    obtain ⟨hsN, -⟩ := S.mem_preimageNbar.mp hs
    exact (S.mem_Ng.mp hsN m).mp hm
  · intro x hx hxM
    exact S.card_centralizer_Mnu hν3 hrel hP hx hxM

end JWSetup

end CFSG.Quasithin.H13.U43
