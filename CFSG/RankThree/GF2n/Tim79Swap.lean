module

public import CFSG.RankThree.GF2n.Tim79Local
import CFSG.RankThree.GF2n.Tim79CentBasic
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement Matrix

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.RankOne

variable {G : Type} [Group G]

namespace NatData

variable {V Q : Subgroup G} {g : G} {n : ℕ} (N : NatData V Q g n)

private theorem swap_coord_zero_of_mem_U
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q)
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
    have hzQ : (z : G) ∈ conjSubgroup g Q := Subgroup.mem_subgroupOf.mp hz
    have hcomm := hUc z hzQ w hw
    have h1 := N.compat z w w (by rw [hcomm, mul_inv_cancel_right])
    rw [hzt] at h1
    exact h1.symm
  exact (ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff _).mp hv

private theorem swap_mem_U_iff [Finite G] (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (w : ↥(V ⊔ conjSubgroup g V)) :
    (w : G) ∈ conjSubgroup g V ↔ Multiplicative.toAdd (N.ψ w) 0 = 0 := by
  refine ⟨N.swap_coord_zero_of_mem_U hUc w, fun hw0 => ?_⟩
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
      (N.swap_coord_zero_of_mem_U hUc _ a.2) (N.swap_coord_zero_of_mem_U hUc _ b.2) hab)
  have hcard : Nat.card (conjSubgroup g V) = Nat.card (GaloisField 2 n) := by
    rw [card_conjSubgroup, hVn, GaloisField.card 2 n hn]
  have hf_bij : Function.Bijective f := hf_inj.bijective_of_nat_card_le hcard.ge
  obtain ⟨u, hu⟩ := hf_bij.2 (Multiplicative.toAdd (N.ψ w) 1)
  have h1 : (⟨u, hUW u.2⟩ : ↥(V ⊔ conjSubgroup g V)) = w :=
    hext _ _ (N.swap_coord_zero_of_mem_U hUc _ u.2) hw0 hu
  rw [← h1]
  exact u.2

end NatData

variable [Finite G] {M V Q : Subgroup G}

private theorem Hyp79.exists_swap_V (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n₀ ∈ Q ⊔ conjSubgroup g Q, conjSubgroup n₀ V = conjSubgroup g V ∧
      conjSubgroup n₀ (conjSubgroup g V) = V := by
  obtain ⟨n, hn2, hVn, ⟨N⟩⟩ := exists_natData H hgV hgQ
  have hn : n ≠ 0 := by omega
  have hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q :=
    fun q hq u hu => (H.conj_central g hu hq).symm
  obtain ⟨z, hz⟩ := N.surj (ARS.NaturalModule.weylElt (GaloisField 2 n))
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
    refine (N.swap_mem_U_iff hVn hn hUc ⟨_, hw'⟩).mpr ?_
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
    exact N.swap_coord_zero_of_mem_U hUc ⟨u, huW⟩ hu
  refine ⟨(z : G), z.2, ?_, ?_⟩
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

theorem Hyp79.exists_swap (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n ∈ Q ⊔ conjSubgroup g Q, conjSubgroup n Q = conjSubgroup g Q ∧
      conjSubgroup n (conjSubgroup g Q) = Q := by
  obtain ⟨n₀, hn₀H, h1, h2⟩ := H.exists_swap_V hgV hgQ
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  refine ⟨n₀, hn₀H, ?_, ?_⟩
  · have := h.conjSubgroup_P_eq h1
    rwa [hPQ] at this
  · have h3 : conjSubgroup (n₀ * g) V = conjSubgroup 1 V := by
      rw [conjSubgroup_mul, h2, conjSubgroup_one]
    have := h.conjSubgroup_P_eq h3
    rw [hPQ, conjSubgroup_one, conjSubgroup_mul] at this
    exact this

theorem Hyp79.inf_conj_eq (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {x : G} (hx : x ∈ Q)
    (hxg : conjSubgroup (x * g) V ≠ conjSubgroup g V) :
    conjSubgroup g Q ⊓ conjSubgroup (x * g) Q = Q ⊓ conjSubgroup g Q := by
  obtain ⟨n₀, hn₀H, h1, h2⟩ := H.exists_swap_V hgV hgQ
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x', hx'W, hx'V⟩ := h.exists_conj_eq_V1 hy
  have hxP : x ∈ Q ⊓ Subgroup.centralizer (V : Set G) := by rw [hPQ]; exact hx
  have hU'W : conjSubgroup (x * g) V ≤ V ⊔ conjSubgroup g V := h.conj_V1_le_W hxP
  obtain ⟨u, hu, hu'⟩ := h.exists_Pg_conj_eq hx'W hx'V hy
    (U := V) (U' := conjSubgroup (x * g) V)
    ⟨⟨1, (conjSubgroup_one V).symm⟩, h.V_le_W⟩ hgV.symm ⟨⟨x * g, rfl⟩, hU'W⟩ hxg
  rw [hPQ] at hu
  have hun : u ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
    Subgroup.mem_normalizer_fintype fun a ha => by
      have := H.conj_central g ha hu
      rw [show u * a = a * u from this.symm, mul_inv_cancel_right]
      exact ha
  have hkV : conjSubgroup (u * n₀) V = conjSubgroup g V := by
    rw [conjSubgroup_mul, h1]
    exact conjSubgroup_eq_self_iff.mpr hun
  have hkU : conjSubgroup ((u * n₀) * g) V = conjSubgroup (x * g) V := by
    rw [mul_assoc, conjSubgroup_mul, conjSubgroup_mul n₀ g, h2]
    exact hu'
  have hQk : conjSubgroup (u * n₀) Q = conjSubgroup g Q := by
    have := h.conjSubgroup_P_eq hkV
    rwa [hPQ] at this
  have hQkg : conjSubgroup ((u * n₀) * g) Q = conjSubgroup (x * g) Q := by
    have := h.conjSubgroup_P_eq hkU
    rwa [hPQ] at this
  have hkH : u * n₀ ∈ Q ⊔ conjSubgroup g Q :=
    mul_mem (Subgroup.mem_sup_right hu) hn₀H
  have hkL : conjSubgroup (u * n₀) (Q ⊓ conjSubgroup g Q) = Q ⊓ conjSubgroup g Q :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun l hl =>
      H.L_normal hgV hgQ _ hkH l hl)
  calc conjSubgroup g Q ⊓ conjSubgroup (x * g) Q
      = conjSubgroup (u * n₀) Q ⊓ conjSubgroup (u * n₀) (conjSubgroup g Q) := by
        rw [hQk, ← hQkg, conjSubgroup_mul (u * n₀) g Q]
    _ = conjSubgroup (u * n₀) (Q ⊓ conjSubgroup g Q) := (conjSubgroup_inf _ _ _).symm
    _ = Q ⊓ conjSubgroup g Q := hkL

theorem Hyp79.mem_L_of_comm_mem (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {c : G} (hc : c ∈ conjSubgroup g Q)
    (h : ∀ x ∈ Q, ⁅x, c⁆ ∈ Q ⊓ conjSubgroup g Q) : c ∈ Q ⊓ conjSubgroup g Q := by
  obtain ⟨x, hx, hxg⟩ : ∃ x ∈ Q, conjSubgroup (x * g) V ≠ conjSubgroup g V := by
    by_contra hcon
    push Not at hcon
    have hinf : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgV
    have hUV : conjSubgroup g V ≤ V := by
      intro u hu
      have huQ : u ∈ Q := hgQ hu
      have hcent : u ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
        refine ⟨huQ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hn : x * u * x⁻¹ ∈ conjSubgroup g V := by
          have := hcon x hx
          rw [conjSubgroup_mul] at this
          rw [← this, mem_conjSubgroup]
          simpa [mul_assoc] using hu
        have h1 : ⁅x, u⁆ ∈ conjSubgroup g V := by
          rw [commutatorElement_def]
          exact mul_mem hn (inv_mem hu)
        have h2 : ⁅x, u⁆ ∈ V := H.comm_mem_V hx huQ
        have h3 : ⁅x, u⁆ ∈ V ⊓ conjSubgroup g V := ⟨h2, h1⟩
        rw [hinf, Subgroup.mem_bot] at h3
        exact commutatorElement_eq_one_iff_mul_comm.mp h3
      exact ((H.special).2.1 ▸ hcent : u ∈ V)
    have hbot : conjSubgroup g V = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf hUV le_rfl
    exact (H.toHyp218 hgV hgQ).conj_ne_bot g hbot
  have hxc : x * c * x⁻¹ ∈ Q ⊓ conjSubgroup g Q := by
    have hL1 : ⁅x, c⁆ ∈ Q ⊓ conjSubgroup g Q := h x hx
    have hQg : x * c * x⁻¹ ∈ conjSubgroup g Q := by
      rw [show x * c * x⁻¹ = ⁅x, c⁆ * c by rw [commutatorElement_def]; group]
      exact mul_mem hL1.2 hc
    have hQxg : x * c * x⁻¹ ∈ conjSubgroup (x * g) Q := by
      rw [conjSubgroup_mul, mem_conjSubgroup]
      simpa [mul_assoc] using hc
    rw [← H.inf_conj_eq hgV hgQ hx hxg]
    exact ⟨hQg, hQxg⟩
  have := H.L_normal hgV hgQ x⁻¹ (Subgroup.mem_sup_left (inv_mem hx)) _ hxc
  simpa [mul_assoc] using this

end CFSG.RankThree.GF2n.Tim79
