module

public import CFSG.Quasithin.Background.E11Aux
public import CFSG.Quasithin.Background.G118CanonNineF2TensorLin

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Tensor

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem two_eq_zero (D : E11Data H I) : (2 : D.F) = 0 := by
  have h := CharP.cast_eq_zero D.F 2
  simpa using h

theorem card_irrPlus (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hF : Nat.card D.F = 2) : Nat.card {J : Submodule (ZMod 2) V // IrrPlus H J} = 3 := by
  have h1 := D.natCard_irrPlus
  rw [D.natCard_U, hU, hF] at h1
  norm_num at h1
  omega

theorem finrank_I (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) : Module.finrank (ZMod 2) I = 4 := by
  have h := D.finrank_mul
  rw [hU, hdim] at h
  omega

theorem four_dvd (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) {M : Submodule (ZMod 2) V} (hM : Invariant H M) :
    4 ∣ Module.finrank (ZMod 2) M := by
  obtain ⟨S, -, hS⟩ := D.exists_subspace M hM
  rw [finrank_I D hU hdim] at hS
  exact ⟨Module.finrank D.F S, by rw [← hS, mul_comm]⟩

theorem irr_of_finrank_four (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) {B : Submodule (ZMod 2) V}
    (h4 : Module.finrank (ZMod 2) B = 4) {J : Submodule (ZMod 2) V} (hJ : Invariant H J)
    (hJB : J ≤ B) : J = ⊥ ∨ J = B := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨k, hk⟩ := four_dvd D hU hdim hJ
  have hle : Module.finrank (ZMod 2) J ≤ Module.finrank (ZMod 2) B := Submodule.finrank_mono hJB
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · left
    exact Submodule.finrank_eq_zero.1 (by omega)
  · right
    exact Submodule.eq_of_le_of_finrank_eq hJB (by omega)

theorem irrPlus_conj (D : E11Data H I) {c : GLV V} (hc : ∀ h ∈ H, h * c = c * h)
    {J : Submodule (ZMod 2) V} (hJ : IrrPlus H J) : IrrPlus H (conjSub c J) := by
  have hmem : c ∈ Subgroup.centralizer (H : Set (GLV V)) := Subgroup.mem_centralizer_iff.2 hc
  obtain ⟨hJ', -⟩ := D.θ_acts ⟨c, hmem⟩ J hJ
  exact hJ'

theorem conjSub_ne (D : E11Data H I) (hU : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2)
    {c : GLV V} (hc : ∀ h ∈ H, h * c = c * h) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {J : Submodule (ZMod 2) V} (hJ : IrrPlus H J) : conjSub c J ≠ J := by
  intro hcJ
  have hmem : c ∈ Subgroup.centralizer (H : Set (GLV V)) := Subgroup.mem_centralizer_iff.2 hc
  obtain ⟨hJ', hψ⟩ := D.θ_acts ⟨c, hmem⟩ J hJ
  have hsub : (⟨conjSub c J, hJ'⟩ : {J : Submodule (ZMod 2) V // IrrPlus H J}) = ⟨J, hJ⟩ :=
    Subtype.ext hcJ
  have hψ' : D.θ ⟨c, hmem⟩ • D.ψ ⟨J, hJ⟩ = D.ψ ⟨J, hJ⟩ := by
    have h := hψ
    rw [hsub] at h
    exact h.symm
  obtain ⟨u, hu, hgu⟩ := fixed_vec_of_smul_eq hF (D.θ ⟨c, hmem⟩) _ hψ'
  have hg3 : D.θ ⟨c, hmem⟩ * D.θ ⟨c, hmem⟩ * D.θ ⟨c, hmem⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have h3 : (⟨c, hmem⟩ : Subgroup.centralizer (H : Set (GLV V))) *
        ⟨c, hmem⟩ * ⟨c, hmem⟩ = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using hc3)
    rw [h3, map_one]
  have hone := eq_one_of_fixed_of_cube hF (two_eq_zero D) hU (D.θ ⟨c, hmem⟩) hg3 hu hgu
  exact hc1 (congrArg Subtype.val (D.θ.injective (hone.trans (map_one D.θ).symm)))

theorem orbit_cases (D : E11Data H I) (hU : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2)
    {c : GLV V} (hcH : ∀ h ∈ H, h * c = c * h) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {J J' : Submodule (ZMod 2) V} (hJ : IrrPlus H J) (hJ' : IrrPlus H J') :
    J' = J ∨ J' = conjSub c J ∨ J' = conjSub c (conjSub c J) := by
  classical
  have hX := card_irrPlus D hU hF
  have hJ1 := irrPlus_conj D hcH hJ
  have hJ2 := irrPlus_conj D hcH hJ1
  have n0 := conjSub_ne D hU hF hcH hc3 hc1 hJ
  have n1 := conjSub_ne D hU hF hcH hc3 hc1 hJ1
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have h3 : conjSub c (conjSub c (conjSub c J)) = J := by
    rw [← conjSub_mul, ← conjSub_mul, hc3', conjSub_one]
  have n2 : conjSub c (conjSub c J) ≠ J := by
    intro h
    apply n0
    have h4 : conjSub c (conjSub c (conjSub c J)) = conjSub c J := by rw [h]
    rw [h3] at h4
    exact h4.symm
  haveI : Finite {J : Submodule (ZMod 2) V // IrrPlus H J} :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  haveI : Fintype {J : Submodule (ZMod 2) V // IrrPlus H J} := Fintype.ofFinite _
  have hcard : Fintype.card {J : Submodule (ZMod 2) V // IrrPlus H J} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hX
  let S : Finset {J : Submodule (ZMod 2) V // IrrPlus H J} :=
    {⟨J, hJ⟩, ⟨conjSub c J, hJ1⟩, ⟨conjSub c (conjSub c J), hJ2⟩}
  have hS : S.card = 3 := by
    apply Finset.card_eq_three.2
    refine ⟨⟨J, hJ⟩, ⟨conjSub c J, hJ1⟩, ⟨conjSub c (conjSub c J), hJ2⟩, ?_, ?_, ?_, rfl⟩
    · intro h
      exact n0 (congrArg Subtype.val h).symm
    · intro h
      exact n2 (congrArg Subtype.val h).symm
    · intro h
      exact n1 (congrArg Subtype.val h).symm
  have hall : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, hcard])
  have hmem : (⟨J', hJ'⟩ : {J : Submodule (ZMod 2) V // IrrPlus H J}) ∈ S := by
    rw [hall]
    exact Finset.mem_univ _
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

theorem exists_fixed_point_involution (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    {y : GLV V} (hyH : ∀ h ∈ H, h * y = y * h) (hy2 : y * y = 1) :
    ∃ J : Submodule (ZMod 2) V, IrrPlus H J ∧ conjSub y J = J := by
  have hmem : y ∈ Subgroup.centralizer (H : Set (GLV V)) := Subgroup.mem_centralizer_iff.2 hyH
  have hg2 : D.θ ⟨y, hmem⟩ * D.θ ⟨y, hmem⟩ = 1 := by
    rw [← map_mul]
    have h2 : (⟨y, hmem⟩ : Subgroup.centralizer (H : Set (GLV V))) * ⟨y, hmem⟩ = 1 :=
      Subtype.ext hy2
    rw [h2, map_one]
  haveI : Nontrivial D.U := Module.nontrivial_of_finrank_pos (R := D.F) (M := D.U) (by omega)
  obtain ⟨u, hu, hgu⟩ := exists_fixed_of_sq (two_eq_zero D) (D.θ ⟨y, hmem⟩) hg2
  have hP : D.θ ⟨y, hmem⟩ • Projectivization.mk D.F u hu = Projectivization.mk D.F u hu :=
    smul_eq_of_fixed_vec _ hu hgu
  set P : ℙ D.F D.U := Projectivization.mk D.F u hu with hPdef
  refine ⟨(D.ψ.symm P).1, (D.ψ.symm P).2, ?_⟩
  obtain ⟨hJ', hψ⟩ := D.θ_acts ⟨y, hmem⟩ (D.ψ.symm P).1 (D.ψ.symm P).2
  have hψP : D.ψ ⟨(D.ψ.symm P).1, (D.ψ.symm P).2⟩ = P := D.ψ.apply_symm_apply P
  have hψ2 : D.ψ ⟨conjSub y (D.ψ.symm P).1, hJ'⟩ = P := by
    have h1 : D.ψ ⟨conjSub y (D.ψ.symm P).1, hJ'⟩ =
        D.θ ⟨y, hmem⟩ • D.ψ ⟨(D.ψ.symm P).1, (D.ψ.symm P).2⟩ := hψ
    rw [h1, hψP, hP]
  have := D.ψ.injective (hψ2.trans hψP.symm)
  exact congrArg Subtype.val this

theorem fixed_eq_zero (D : E11Data H I) (hU : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2)
    {c : GLV V} (hcH : ∀ h ∈ H, h * c = c * h) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∀ v : V, c v = v → v = 0 := by
  intro v hv
  by_contra hv0
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set M : Submodule (ZMod 2) V := LinearMap.ker (c.toLinearMap - LinearMap.id) with hM
  have hmemM : ∀ w : V, w ∈ M ↔ c w = w := fun w => by
    simp [hM, LinearMap.mem_ker, sub_eq_zero]
  have hMinv : Invariant H M := by
    intro h hh w hw
    rw [hmemM] at hw ⊢
    have h1 := congrArg (fun g : GLV V => g w) (hcH h hh)
    have h2 : h (c w) = c (h w) := h1
    rw [← h2, hw]
  obtain ⟨S, hS1, hS2⟩ := D.exists_subspace M hMinv
  have hfr : 0 < Module.finrank (ZMod 2) M :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨v, (hmemM v).2 hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  obtain ⟨s, hsS, hs0⟩ : ∃ s ∈ S, s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hSbot : S = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      exact hcon x hx
    rw [hSbot, finrank_bot, zero_mul] at hS2
    omega
  set P : ℙ D.F D.U := Projectivization.mk D.F s hs0 with hPdef
  have hJ : IrrPlus H (D.ψ.symm P).1 := (D.ψ.symm P).2
  have hψJ : D.ψ ⟨(D.ψ.symm P).1, hJ⟩ = P := D.ψ.apply_symm_apply P
  have hJM : (D.ψ.symm P).1 ≤ M := by
    rw [hS1 _ hJ, hψJ, hPdef, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
    exact hsS
  have hfix : conjSub c (D.ψ.symm P).1 = (D.ψ.symm P).1 := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_conjSub c _)
    rintro _ ⟨x, hx, rfl⟩
    show c x ∈ (D.ψ.symm P).1
    rw [(hmemM x).1 (hJM hx)]
    exact hx
  exact conjSub_ne D hU hF hcH hc3 hc1 hJ hfix

end F2Tensor

end Canon

end G11

end CFSG.Quasithin
