module

public import CFSG.Quasithin.EmptyFaithful.S153NBase

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Ms5

private theorem exists_three_cycle_fixing :
    ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → x ≠ 0 →
      ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ ∀ i, x (σ⁻¹ i) = x i := by
  decide +kernel

private theorem exists_even_moved :
    ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 →
      ∃ y : Fin 5 → ZMod 2, ∑ i, y i = 0 ∧ ∃ i, y (σ⁻¹ i) ≠ y i := by
  decide +kernel

private theorem ker_five :
    Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = (⊥ : Subgroup (G6.PermMod 5)) := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide +kernel
  have hnot : G6.allOnes 5 ∉ G6.coreMod 5 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 5) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 5) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

private theorem false_of_data {W : Type} [CommGroup W] (hW : ∀ v : W, v ^ 2 = 1)
    {Γ J : Subgroup (MulAut W)} {w : W} (hJΓ : J ≤ Γ) (hw : w ∉ fixV J)
    (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w)) (π : Equiv.Perm (Fin 5) →* ↥J)
    (β : ↥(⊤ : Subgroup W) →*
      ↥(G6.coreMod 5) ⧸ (Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5))
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥(⊤ : Subgroup W), β u = 1 ↔ (u : W) ∈ fixV J)
    (hβe : ∀ (γ : Equiv.Perm (Fin 5)) (u : ↥(⊤ : Subgroup W)) (m : ↥(G6.coreMod 5))
      (hu : ((π γ : ↥J) : MulAut W) (u : W) ∈ (⊤ : Subgroup W))
      (hm : G6.permAct 5 γ (m : G6.PermMod 5) ∈ G6.coreMod 5),
      β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥J) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk ⟨G6.permAct 5 γ (m : G6.PermMod 5), hm⟩) : False := by
  set w' : ↥(⊤ : Subgroup W) := ⟨w, Subgroup.mem_top w⟩ with hw'
  have hβw : β w' ≠ 1 := fun h => hw ((hβk w').1 h)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β w')
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hβw (hm.symm.trans (QuotientGroup.mk_one _))
  have hx0 : Multiplicative.toAdd (m : G6.PermMod 5) ≠ 0 := by
    intro h
    apply hm1
    exact Subtype.ext (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))
  obtain ⟨σ, hσ3, hσ1, hσx⟩ := exists_three_cycle_fixing _ (G6.mem_coreMod.1 m.2) hx0
  have hfix : G6.permAct 5 σ (m : G6.PermMod 5) = (m : G6.PermMod 5) := by
    apply Multiplicative.toAdd.injective
    funext i
    exact hσx i
  have hmem : G6.permAct 5 σ (m : G6.PermMod 5) ∈ G6.coreMod 5 := G6.permAct_mem_coreMod σ m.2
  have hu : ((π σ : ↥J) : MulAut W) (w' : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
  have h1 := hβe σ w' m hu hmem hm.symm
  have h2 : (⟨G6.permAct 5 σ (m : G6.PermMod 5), hmem⟩ : ↥(G6.coreMod 5)) = m := Subtype.ext hfix
  rw [h2, hm] at h1
  have h5 : β (⟨((π σ : ↥J) : MulAut W) (w' : W), hu⟩ * w'⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  have h4 : ((π σ : ↥J) : MulAut W) w * w⁻¹ ∈ fixV J := (hβk _).1 h5
  have hg3 : ((π σ : ↥J) : MulAut W) ^ 3 = 1 := by
    have : (π σ) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
    exact congrArg Subtype.val this
  have hg1 : ((π σ : ↥J) : MulAut W) ≠ 1 := by
    intro hone
    obtain ⟨y, hy, i, hi⟩ := exists_even_moved σ hσ1
    set ym : ↥(G6.coreMod 5) := ⟨Multiplicative.ofAdd y, G6.mem_coreMod.2 hy⟩ with hym
    obtain ⟨u, hu'⟩ := hβs (QuotientGroup.mk ym)
    have hmem' : G6.permAct 5 σ (ym : G6.PermMod 5) ∈ G6.coreMod 5 :=
      G6.permAct_mem_coreMod σ ym.2
    have hu1 : ((π σ : ↥J) : MulAut W) (u : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
    have h6 := hβe σ u ym hu1 hmem' hu'
    have h7 : (⟨((π σ : ↥J) : MulAut W) (u : W), hu1⟩ : ↥(⊤ : Subgroup W)) = u := by
      apply Subtype.ext
      show ((π σ : ↥J) : MulAut W) (u : W) = u
      rw [hone]
      rfl
    rw [h7, hu'] at h6
    have h8 := QuotientGroup.eq.1 h6
    rw [Subgroup.mem_subgroupOf, ker_five, Subgroup.mem_bot] at h8
    have h9 : (ym : G6.PermMod 5) = G6.permAct 5 σ (ym : G6.PermMod 5) := inv_mul_eq_one.1 h8
    exact hi (congrArg (fun m : G6.PermMod 5 => Multiplicative.toAdd m i) h9).symm
  exact false_of_lift hW hJΓ h3 (π σ).2 hg1 hg3 h4

variable {W : Type} [CommGroup W] [Finite W]

set_option linter.unusedSectionVars false in
theorem false_of_symmetric_five (hW : ∀ v : W, v ^ 2 = 1) {Γ J : Subgroup (MulAut W)} {w : W}
    (hJΓ : J ≤ Γ) (hsym : SymmetricNatural J ⊤ (fixV J) 5) (hw : w ∉ fixV J)
    (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w)) : False := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hsym
  exact false_of_data hW hJΓ hw h3 π β hβs hβk hβe

end Ms5

end CFSG.Quasithin.S153N
