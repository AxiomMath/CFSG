module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Four
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Gu2

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.Quasithin CFSG.RankThree.Classical

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem factorization_card_su3 (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    (Nat.card ↥(unitarySU p 1 F 3)).factorization 2 =
      (p - 1).factorization 2 + 2 * (p + 1).factorization 2 := by
  have hU := uniData (p := p) hF
  have hcp := charP_of_card_sq (p := p) hF
  have hG : ∀ i j : Fin 3, hU.bar ((1 : Matrix (Fin 3) (Fin 3) F) j i) =
      (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have h := ordProj_two_card_SUgram hU hp2 (G₀ := (1 : Matrix (Fin 3) (Fin 3) F)) hG
    (by simp)
  rw [SUgram_bar_one hU 3, CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
    (card_eq_sq_of_unitaryFieldData hU) 3] at h
  simp only [pow_one] at h
  rw [← pow_mul, ← pow_add] at h
  have := Nat.pow_right_injective (le_refl 2) h
  simpa [unitarySU, pow_one, mul_comm] using this

theorem two_pow_dvd_card_of_odd_index (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (M : Subgroup ↥(unitarySU p 1 F 3)) (hodd : Odd M.index) :
    2 ^ (3 + (p + 1).factorization 2) ∣ Nat.card M := by
  have hfac : (Nat.card ↥(unitarySU p 1 F 3)).factorization 2 = (Nat.card M).factorization 2 := by
    rw [← Subgroup.card_mul_index M, Nat.factorization_mul Nat.card_pos.ne'
      (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
  have h1 := factorization_card_su3 hp2 hF
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h8 : 2 ^ 3 ∣ (p - 1) * (p + 1) := by
    obtain ⟨m, rfl⟩ := hpodd
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
    refine ⟨j, ?_⟩
    have e : (2 * m + 1 - 1) * (2 * m + 1 + 1) = 4 * (m * (m + 1)) := by
      rw [show 2 * m + 1 - 1 = 2 * m by omega]
      ring
    rw [e, hj]
    ring
  have hp0 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h3 : 3 ≤ (p - 1).factorization 2 + (p + 1).factorization 2 := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (mul_ne_zero hp0 (Nat.succ_ne_zero p))).mp h8
    rwa [Nat.factorization_mul hp0 (Nat.succ_ne_zero p), Finsupp.add_apply] at this
  refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr ?_
  omega

open CFSG.GH74.GLS.IVK.Proofs2 in
theorem reducible_core (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (M : Subgroup ↥(unitarySU p 1 F 3)) (hodd : Odd M.index)
    (hE : ∀ k, dS (uniData (p := p) hF) k ∈ M) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ M, ∀ w ∈ W, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    (hbot : W ≠ ⊥) (htop : W ≠ ⊤) :
    Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) := by
  classical
  have hU := uniData (p := p) hF
  have h2 := two_ne_zero_of_card_sq (p := p) hp2 hF
  have h8 := two_pow_dvd_card_of_odd_index hp2 hF M hodd
  let Mgl : Subgroup (GL (Fin 3) F) := M.map (unitarySU p 1 F 3).subtype
  have hM : ∀ g ∈ Mgl, ((g : Matrix (Fin 3) (Fin 3) F).map hU.bar)ᵀ *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((mem_unitarySU_iff hU).mp x.2).2
  have hd : ∀ k, dsignGL F k ∈ Mgl := fun k => ⟨dS hU k, hE k, rfl⟩
  have hW' : ∀ g ∈ Mgl, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    exact hW x hx w hw
  obtain ⟨k, -, hcomm⟩ := exists_central_dsign hU h2 hM hd hW' hbot htop
  have hcomm' : ∀ x ∈ M, x * dS hU k = dS hU k * x := fun x hx =>
    Subtype.ext (hcomm _ ⟨x, hx, rfl⟩)
  have hc1 : dS hU k ≠ 1 := by
    intro h1
    obtain ⟨i, hik⟩ := exists_ne k
    have := congrArg (fun x : ↥(unitarySU p 1 F 3) =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) h1
    simp [dS, dsign, hik] at this
    exact h2 (by linear_combination -this)
  have hc2 : orderOf (dS hU k) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsq : dS hU k ^ 2 = 1 := by rw [sq]; exact dS_mul_self hU k
    exact orderOf_eq_prime hsq hc1
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf hU hp2 hc2)
  have hMrange : M ≤ (Lemma41aU3.phi hU g₀).range := by
    rw [Lemma41aU3.phi_range hU hp2 g₀, hg₀]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' x hx)
  have hφinj := Lemma41aU3.phi_injective hU g₀
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Subgroup ↥(GU2Stated (p ^ 1) F),
      H₀.map (Lemma41aU3.phi hU g₀) = M :=
    ⟨M.comap (Lemma41aU3.phi hU g₀), Subgroup.map_comap_eq_self hMrange⟩
  subst hH₀
  let θ := (GU2Stated (p ^ 1) F).subtype
  have hθinj : Function.Injective θ := (GU2Stated (p ^ 1) F).subtype_injective
  have hHgl_le : H₀.map θ ≤ GU2Stated (p ^ 1) F := Subgroup.map_subtype_le _
  have hcard : Nat.card (H₀.map θ) = Nat.card (H₀.map (Lemma41aU3.phi hU g₀)) := by
    rw [Subgroup.card_map_of_injective hθinj, Subgroup.card_map_of_injective hφinj]
  rcases gu2_core hp2 hF hHgl_le (hcard ▸ h8) with hs | ⟨e⟩
  · left
    have := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((H₀.equivMapOfInjective (Lemma41aU3.phi hU g₀) hφinj).symm.trans
        (H₀.equivMapOfInjective θ hθinj)).toMonoidHom) (MulEquiv.injective _)
  · right
    let eP : ↥(perfectCore (H₀.map (Lemma41aU3.phi hU g₀))) ≃*
        ↥(perfectCore (H₀.map θ)) :=
      (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore (Lemma41aU3.phi hU g₀) H₀).symm).trans
        (((perfectCore H₀).equivMapOfInjective (Lemma41aU3.phi hU g₀) hφinj).symm.trans
          (((perfectCore H₀).equivMapOfInjective θ hθinj).trans
            (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore θ H₀))))
    obtain ⟨e'⟩ := e
    exact ⟨eP.trans e'⟩

end CFSG.Quasithin.A312U3
