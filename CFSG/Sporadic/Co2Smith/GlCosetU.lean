module

public import CFSG.Sporadic.Co2Smith.GlCosetCompat
public import CFSG.Sporadic.Co2Smith.GlCosetFacts

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem psiK_conj_apply_cPerm
    {g k : K} {x y : Fin 2300} (hg : co2PermHom g x = y) (hk : co2PermHom k x = x) :
    (psiK g * psiK k * (psiK g)⁻¹) (cPerm y) = cPerm y := by
  have h1 : (psiK g)⁻¹ (cPerm y) = cPerm x := by
    rw [Equiv.Perm.inv_eq_iff_eq, psiK_apply_cPerm, hg]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, psiK_apply_cPerm, hk, psiK_apply_cPerm, hg]

theorem v1K_eq :
    v1K = β3K * (β3K * (uK * (w0K * (uK * β3K)))) := by
  simp only [v1K, vK, mul_assoc]

theorem vK_eq : vK = β3K⁻¹ * β3K⁻¹ * v1K * β3K⁻¹ := by
  simp only [v1K]
  group

theorem glM2Words_tail_let :
    ∀ w ∈ Native.glM2Words.tail, ∀ k ∈ w, k ∈ Native.glC0Let := by decide

namespace SmithMarkedData

variable
  {G : Type*} [Group G] {z : G} (S : SmithMarkedData z)

@[expose] noncomputable def u : G := S.phiInv ⟨uK, uK_mem_Cz⟩

@[expose] noncomputable def v : G := S.ρ ⟨v1K, v1K_mem_C0c⟩

theorem ρ_uK : S.ρ ⟨uK, uK_mem_C0c⟩ = S.u := S.ρ_eq_phiInv uK_mem_C0c uK_mem_Cz

theorem u_mul_self : S.u * S.u = 1 := by
  have e : (⟨uK, uK_mem_Cz⟩ : Cz) * ⟨uK, uK_mem_Cz⟩ = 1 := Subtype.ext uK_mul_self
  rw [u, ← map_mul, e, map_one]

theorem u_inv : S.u⁻¹ = S.u := inv_eq_of_mul_eq_one_right S.u_mul_self

variable {S} in
theorem Compat.eq {x : G} {xc : K} {h : S.G₁} (hx : S.Compat x xc h) :
    (S.ψ ⟨_, hx.mem⟩ : Equiv.Perm (Fin 2300)) =
      psiK xc * (S.ψ h : Equiv.Perm (Fin 2300)) * (psiK xc)⁻¹ :=
  hx.2

variable {S} in
theorem Compat.congr {x x' : G} {xc xc' : K} {h : S.G₁} (hx : S.Compat x xc h) (e : x = x')
    (ec : xc = xc') : S.Compat x' xc' h := by
  subst e
  subst ec
  exact hx


theorem v_eq : S.v = S.Ψ ⟨β3K, β3K_mem_G1c⟩ * (S.Ψ ⟨β3K, β3K_mem_G1c⟩ *
    (S.u * (S.Ψ ⟨w0K, w0K_mem_G1c⟩ * (S.u * S.Ψ ⟨β3K, β3K_mem_G1c⟩)))) := by
  have e : (⟨v1K, v1K_mem_C0c⟩ : C0c) = ⟨β3K, β3K_mem_C0c⟩ * (⟨β3K, β3K_mem_C0c⟩ *
      (⟨uK, uK_mem_C0c⟩ * (⟨w0K, w0K_mem_C0c⟩ * (⟨uK, uK_mem_C0c⟩ * ⟨β3K, β3K_mem_C0c⟩)))) :=
    Subtype.ext v1K_eq
  rw [v, e, map_mul, map_mul, map_mul, map_mul, map_mul, S.ρ_uK,
    S.ρ_eq_Ψ β3K_mem_C0c β3K_mem_G1c, S.ρ_eq_Ψ w0K_mem_C0c w0K_mem_G1c]


theorem compat_u {h : S.G₁} (h3 : (S.ψ h : Equiv.Perm (Fin 2300)) 3 = 3) :
    S.Compat S.u uK h := by
  refine S.mem_of_mem_closure (T := S.compatSubgroup S.u uK)
    (A := {σ | ∃ w ∈ Native.glNWords, psiK (glE w) = σ}) ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h0, h1⟩ := glNWords_fix w hw
    have hw1 : glE w ∈ G1c := h0
    have h3' : psiK (glE w) 3 = 3 := by
      rw [← cPerm_1172, psiK_fix_iff]
      exact h1
    have hc := uK_conj_mem_G1c h3'
    refine ⟨⟨S.Ψ ⟨glE w, hw1⟩, S.Ψ_mem _⟩, ?_, S.ψ_Ψ _⟩
    rcases glNWords_mem w hw with hwz | hw0
    · exact S.compat_phiInv z0_mem_G1c uK_mem_Cz hw1 hwz hc
    · have := S.compat_ρ uK_mem_C0c hw1 hw0 hc
      rwa [S.ρ_uK] at this
  · rw [closure_psiK_N]
    exact ⟨(S.ψ h).2, MulAction.mem_stabilizer_iff.2 h3⟩

variable {S} in
theorem Compat.eq_Ψ {x : G} {xc k : K} {hk : k ∈ G1c}
    (hx : S.Compat x xc ⟨S.Ψ ⟨k, hk⟩, S.Ψ_mem _⟩) :
    (S.ψ ⟨_, hx.mem⟩ : Equiv.Perm (Fin 2300)) = psiK xc * psiK k * (psiK xc)⁻¹ := by
  rw [hx.eq, S.ψ_Ψ]

theorem compat_v_path {k : K} (hk : k ∈ G1c) (h942 : co2PermHom k 942 = 942)
    (h582 : co2PermHom k 582 = 582) : S.Compat S.v v1K ⟨S.Ψ ⟨k, hk⟩, S.Ψ_mem _⟩ := by
  have c1 := S.compat_Ψ ⟨β3K, β3K_mem_G1c⟩ ⟨S.Ψ ⟨k, hk⟩, S.Ψ_mem _⟩
  have f1 : (S.ψ ⟨_, c1.mem⟩ : Equiv.Perm (Fin 2300)) 3 = 3 := by
    rw [c1.eq_Ψ, ← cPerm_1172]
    exact psiK_conj_apply_cPerm β3K_942 h942
  have c3 := (c1.trans (S.compat_u f1)).trans (S.compat_Ψ ⟨w0K, w0K_mem_G1c⟩ _)
  have f3 : (S.ψ ⟨_, c3.mem⟩ : Equiv.Perm (Fin 2300)) 3 = 3 := by
    rw [c3.eq_Ψ, ← cPerm_1172]
    refine psiK_conj_apply_cPerm ?_ h582
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    change co2PermHom w0K (co2PermHom uK (co2PermHom β3K 582)) = 1172
    rw [β3K_582, uK_1348, w0K_728]
  have c6 := ((c3.trans (S.compat_u f3)).trans (S.compat_Ψ ⟨β3K, β3K_mem_G1c⟩ _)).trans
    (S.compat_Ψ ⟨β3K, β3K_mem_G1c⟩ _)
  exact c6.congr S.v_eq.symm v1K_eq.symm

theorem compat_v {h : S.G₁}
    (h1 : (S.ψ h : Equiv.Perm (Fin 2300)) 1 = 1) : S.Compat S.v v1K h := by
  refine S.mem_of_mem_closure (T := S.compatSubgroup S.v v1K)
    (A := {σ | ∃ w ∈ Native.glM2Words, psiK (glE w) = σ}) ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h0, h582⟩ := glM2Words_fix w hw
    have hw1 : glE w ∈ G1c := h0
    refine ⟨⟨S.Ψ ⟨glE w, hw1⟩, S.Ψ_mem _⟩, ?_, S.ψ_Ψ _⟩
    have hw' : w = Native.glM2Words[0]! ∨ w ∈ Native.glM2Words.tail := by
      simp only [Native.glM2Words, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hw' with rfl | hwt
    · exact S.compat_v_path hw1 glM2Words_zero_942 h582
    · have h1' : psiK (glE w) 1 = 1 := by
        rw [← cPerm_582, psiK_fix_iff]
        exact h582
      exact S.compat_ρ v1K_mem_C0c hw1 (glE_mem_C0c (glM2Words_tail_let w hwt))
        (v1K_conj_mem_G1c h1')
  · rw [closure_psiK_M2]
    exact ⟨(S.ψ h).2, MulAction.mem_stabilizer_iff.2 h1⟩

end SmithMarkedData

end CFSG.Sporadic.Co2Smith
