module

public import CFSG.RankThree.GF2n.Stroth80.Sec33Weyl

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem ulu_weyl_eq (K : Type*) [Field K] [CharP K 2] :
    upperElt K 1 * lowerElt K 1 * upperElt K 1 = ARS.NaturalModule.weylElt K := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ARS.NaturalModule.coe_weylElt, ARS.NaturalModule.coe_upperElt,
    ARS.NaturalModule.coe_lowerElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private theorem ulu_coord_zero_of_mem_U {V Q₀ : Subgroup G} {g : G} {n : ℕ}
    (N : Tim79.NatData V Q₀ g n)
    (hUc : ∀ q ∈ conjSubgroup g Q₀, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (w : ↥(V ⊔ conjSubgroup g V)) (hw : (w : G) ∈ conjSubgroup g V) :
    Multiplicative.toAdd (N.ψ w) 0 = 0 := by
  have hv : ∀ t : GaloisField 2 n, (lowerElt (GaloisField 2 n) t :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (N.ψ w) =
        Multiplicative.toAdd (N.ψ w) := by
    intro t
    have hl : lowerElt (GaloisField 2 n) t ∈ lowerUnipotent (GaloisField 2 n) :=
      (mem_lowerUnipotent_iff _).mpr ⟨t, rfl⟩
    rw [← N.lower] at hl
    obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.mp hl
    have hzQ : (z : G) ∈ conjSubgroup g Q₀ := Subgroup.mem_subgroupOf.mp hz
    have hcomm := hUc z hzQ w hw
    have h1 := N.compat z w w (by rw [hcomm, mul_inv_cancel_right])
    rw [hzt] at h1
    exact h1.symm
  exact (ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff _).mp hv

private theorem ulu_mem_U_iff {V Q₀ : Subgroup G} {g : G} {n : ℕ}
    (N : Tim79.NatData V Q₀ g n) (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q₀, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (w : ↥(V ⊔ conjSubgroup g V)) :
    (w : G) ∈ conjSubgroup g V ↔ Multiplicative.toAdd (N.ψ w) 0 = 0 := by
  refine ⟨ulu_coord_zero_of_mem_U N hUc w, fun hw0 => ?_⟩
  have hUW : conjSubgroup g V ≤ V ⊔ conjSubgroup g V := le_sup_right
  let f : ↥(conjSubgroup g V) → GaloisField 2 n := fun u =>
    Multiplicative.toAdd (N.ψ ⟨u, hUW u.2⟩) 1
  have hext : ∀ a b : ↥(V ⊔ conjSubgroup g V), Multiplicative.toAdd (N.ψ a) 0 = 0 →
      Multiplicative.toAdd (N.ψ b) 0 = 0 → Multiplicative.toAdd (N.ψ a) 1 =
        Multiplicative.toAdd (N.ψ b) 1 → a = b := by
    intro a b ha hb hab
    apply N.ψ.injective
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact ha.trans hb.symm
    · exact hab
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : ↥(V ⊔ conjSubgroup g V) => (x : G)) (hext ⟨a, hUW a.2⟩ ⟨b, hUW b.2⟩
      (ulu_coord_zero_of_mem_U N hUc _ a.2) (ulu_coord_zero_of_mem_U N hUc _ b.2) hab)
  have hcard : Nat.card (conjSubgroup g V) = Nat.card (GaloisField 2 n) := by
    rw [card_conjSubgroup, hVn, GaloisField.card 2 n hn]
  have hf_bij : Function.Bijective f := hf_inj.bijective_of_nat_card_le hcard.ge
  obtain ⟨u, hu⟩ := hf_bij.2 (Multiplicative.toAdd (N.ψ w) 1)
  have h1 : (⟨u, hUW u.2⟩ : ↥(V ⊔ conjSubgroup g V)) = w :=
    hext _ _ (ulu_coord_zero_of_mem_U N hUc _ u.2) hw0 hu
  rw [← h1]
  exact u.2

private theorem ulu_swap_of_weyl {V Q₀ : Subgroup G} {g : G} {n : ℕ}
    (N : Tim79.NatData V Q₀ g n) (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q₀, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (z : ↥(Q₀ ⊔ conjSubgroup g Q₀))
    (hz : N.φ z = ARS.NaturalModule.weylElt (GaloisField 2 n)) :
    conjSubgroup (z : G) V = conjSubgroup g V ∧
      conjSubgroup (z : G) (conjSubgroup g V) = V := by
  have hmul : ∀ v : Fin 2 → GaloisField 2 n,
      ((ARS.NaturalModule.weylElt (GaloisField 2 n) : Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v = ![v 1, v 0] := by
    intro v
    ext i
    fin_cases i <;> simp [ARS.NaturalModule.coe_weylElt, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hUV : conjSubgroup g V ≤ V ⊔ conjSubgroup g V := le_sup_right
  have hVW : V ≤ V ⊔ conjSubgroup g V := le_sup_left
  have h1 : ∀ v ∈ V, (z : G) * v * (z : G)⁻¹ ∈ conjSubgroup g V := by
    intro v hv
    have hvW : v ∈ V ⊔ conjSubgroup g V := hVW hv
    have hw' : (z : G) * v * (z : G)⁻¹ ∈ V ⊔ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp (N.norm z.2) v).mp hvW
    have hc := N.compat z ⟨v, hvW⟩ ⟨_, hw'⟩ rfl
    rw [hz, hmul] at hc
    have h0 : Multiplicative.toAdd (N.ψ ⟨(z : G) * v * (z : G)⁻¹, hw'⟩) 0 =
        Multiplicative.toAdd (N.ψ ⟨v, hvW⟩) 1 := by rw [hc]; rfl
    refine (ulu_mem_U_iff N hVn hn hUc ⟨_, hw'⟩).mpr ?_
    rw [h0]
    exact (N.hV ⟨v, hvW⟩).mp hv
  have h2 : ∀ u ∈ conjSubgroup g V, (z : G) * u * (z : G)⁻¹ ∈ V := by
    intro u hu
    have huW : u ∈ V ⊔ conjSubgroup g V := hUV hu
    have hw' : (z : G) * u * (z : G)⁻¹ ∈ V ⊔ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp (N.norm z.2) u).mp huW
    have hc := N.compat z ⟨u, huW⟩ ⟨_, hw'⟩ rfl
    rw [hz, hmul] at hc
    have h0 : Multiplicative.toAdd (N.ψ ⟨(z : G) * u * (z : G)⁻¹, hw'⟩) 1 =
        Multiplicative.toAdd (N.ψ ⟨u, huW⟩) 0 := by rw [hc]; rfl
    refine (N.hV ⟨_, hw'⟩).mpr ?_
    rw [h0]
    exact ulu_coord_zero_of_mem_U N hUc ⟨u, huW⟩ hu
  refine ⟨?_, ?_⟩
  · refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · rw [mem_conjSubgroup] at hx
      have := h1 _ hx
      rwa [show (z : G) * ((z : G)⁻¹ * x * (z : G)) * (z : G)⁻¹ = x by group] at this
    · rw [card_conjSubgroup, card_conjSubgroup]
  · refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · rw [mem_conjSubgroup] at hx
      have := h2 _ hx
      rwa [show (z : G) * ((z : G)⁻¹ * x * (z : G)) * (z : G)⁻¹ = x by group] at this
    · rw [card_conjSubgroup]
      exact (card_conjSubgroup g V).ge

theorem Ctx.exists_weyl_ulu (hc : Ctx M Q Z B) :
    ∃ u ∈ Q, ∃ l ∈ QB B, u ∉ Subgroup.centralizer (B : Set G) ∧
      conjSubgroup (u * l * u) Q = QB B ∧ conjSubgroup (u * l * u) (QB B) = Q ∧
      conjSubgroup (u * l * u) Z = B ∧ conjSubgroup (u * l * u) B = Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hc.le
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have H79 : Tim79.Hyp79 M Z Q := hc.hyp.toHyp79
  obtain ⟨n, hn2, hVn, ⟨N⟩⟩ := Tim79.exists_natData H79 hgV hgQ
  have hn : n ≠ 0 := by omega
  have hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g Z, q * u = u * q :=
    fun q hq u hu => (H79.conj_central g hu hq).symm
  have hUp : upperElt (GaloisField 2 n) 1 ∈ upperUnipotent (GaloisField 2 n) :=
    (mem_upperUnipotent_iff _).mpr ⟨1, rfl⟩
  have hLo : lowerElt (GaloisField 2 n) 1 ∈ lowerUnipotent (GaloisField 2 n) :=
    (mem_lowerUnipotent_iff _).mpr ⟨1, rfl⟩
  rw [← N.upper] at hUp
  rw [← N.lower] at hLo
  obtain ⟨z₁, hz₁, hz₁φ⟩ := Subgroup.mem_map.mp hUp
  obtain ⟨z₂, hz₂, hz₂φ⟩ := Subgroup.mem_map.mp hLo
  have hz₁Q : (z₁ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz₁
  have hz₂Q : (z₂ : G) ∈ conjSubgroup g Q := Subgroup.mem_subgroupOf.mp hz₂
  obtain ⟨z, hzdef⟩ : ∃ z : ↥(Q ⊔ conjSubgroup g Q), z = z₁ * z₂ * z₁ := ⟨_, rfl⟩
  have hz : N.φ z = ARS.NaturalModule.weylElt (GaloisField 2 n) := by
    rw [hzdef, map_mul, map_mul, hz₁φ, hz₂φ]
    exact ulu_weyl_eq _
  have hzG : (z : G) = (z₁ : G) * (z₂ : G) * (z₁ : G) := congrArg Subtype.val hzdef
  obtain ⟨hA, hB⟩ := ulu_swap_of_weyl N hVn hn hUc z hz
  have hh := H79.toHyp218 hgV hgQ
  have hPQ := (hh.conclusions H79.q4 rfl).2.2.2.1
  have hP1 : conjSubgroup (z : G) Q = conjSubgroup g Q := by
    have h := hh.conjSubgroup_P_eq hA
    rwa [hPQ] at h
  have hP2 : conjSubgroup (z : G) (conjSubgroup g Q) = Q := by
    have h3 : conjSubgroup ((z : G) * g) Z = conjSubgroup 1 Z := by
      rw [conjSubgroup_mul, hB, conjSubgroup_one]
    have h := hh.conjSubgroup_P_eq h3
    rw [hPQ, conjSubgroup_one, conjSubgroup_mul] at h
    exact h
  refine ⟨(z₁ : G), hz₁Q, (z₂ : G), by rw [hQB]; exact hz₂Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcent
    have hZB : ∀ a ∈ Z ⊔ conjSubgroup g Z, a * (z₁ : G) = (z₁ : G) * a := by
      rw [← hg]
      exact hc.ZB_comm_CB (y := (z₁ : G)) ⟨hz₁Q, hcent⟩
    have hcz : (z₁ : G) ∈ Subgroup.centralizer ((Z ⊔ conjSubgroup g Z : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun a ha => hZB a ha
    have hker : z₁ ∈ N.φ.ker := by
      rw [N.ker]
      exact Subgroup.mem_subgroupOf.mpr hcz
    have h1 : upperElt (GaloisField 2 n) 1 = 1 := by
      rw [← hz₁φ]
      exact MonoidHom.mem_ker.mp hker
    exact one_ne_zero (upperElt_injective _ (h1.trans (upperElt_zero _).symm))
  · rw [← hzG, hQB]
    exact hP1
  · rw [← hzG, hQB]
    exact hP2
  · rw [← hzG]
    exact hA.trans hg.symm
  · rw [← hzG, hg]
    exact hB

end CFSG.RankThree.GF2n.Stroth80
