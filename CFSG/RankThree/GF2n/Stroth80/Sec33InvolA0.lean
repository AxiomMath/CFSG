module

public import CFSG.RankThree.GF2n.Stroth80.QuadWittPerp
public import CFSG.RankThree.GF2n.Stroth80.Conj2
public import CFSG.RankThree.GF2n.Stroth80.Sec33A0

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_involution_A0 (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w)
    (hlt : Nat.card ↥(Q ⊓ QB B) < Nat.card Z ^ (w + 1)) :
    ∃ t ∈ A0 Q Z B, t ∉ Q ∧ t ^ 2 = 1 := by
  classical
  obtain ⟨g, rfl⟩ := hc.conj
  have hQB : QB (conjSubgroup g Z) = conjSubgroup g Q := (Ctx.QB_eq hc rfl).2
  by_contra hno
  have hnot : ∀ t ∈ A0 Q Z (conjSubgroup g Z), t ∉ Q → t ^ 2 ≠ 1 :=
    fun t ht htQ h2 => hno ⟨t, ht, htQ, h2⟩
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hK : 1 < Nat.card (GaloisField 2 m) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim : Module.finrank (GaloisField 2 m) M₀.E = 2 * w := h.finrank_E hw hK
  have h' := h.conj g
  have hZeq : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hZQ : Z ≤ conjSubgroup g Q := by
    rw [← hQB]
    exact hc.Z_le_QB.1
  have hZline : (M₀.conj g).IsLine Z := by
    have hne : conjSubgroup g⁻¹ (conjSubgroup g Z) ≠ conjSubgroup g Z := by
      rw [hZeq]
      exact hc.ne.symm
    have hle : conjSubgroup g⁻¹ (conjSubgroup g Z) ≤ conjSubgroup g Q := by
      rw [hZeq]
      exact hZQ
    have := h'.line g⁻¹ hne hle
    rwa [hZeq] at this
  obtain ⟨e, -, he⟩ := hZline
  have hLQ : Q ⊓ QB (conjSubgroup g Z) ≤ conjSubgroup g Q := by
    rw [hQB]
    exact inf_le_right
  have hBL : conjSubgroup g Z ≤ Q ⊓ QB (conjSubgroup g Z) := by
    refine le_inf hc.le ?_
    rw [hQB]
    intro x hx
    rw [mem_conjSubgroup] at hx ⊢
    exact hc.Z_le_Q hx
  have hZL : Z ≤ Q ⊓ QB (conjSubgroup g Z) := le_inf hc.Z_le_Q hc.Z_le_QB.1
  obtain ⟨U, hUdef⟩ : ∃ U : AddSubgroup (M₀.conj g).E,
      U = (M₀.conj g).img (Q ⊓ QB (conjSubgroup g Z)) := ⟨_, rfl⟩
  have hU : ∀ x ∈ U, (M₀.conj g).Qf x = 0 := by
    rw [hUdef]
    exact ((M₀.conj g).isElemAbelian_iff h'.reg hLQ).mp hc.inf_QB_elemAbelian
  have heU : e ∈ U := by
    have heZ : e ∈ (M₀.conj g).img Z :=
      (he e).mpr ⟨1, (one_smul (GaloisField 2 m) e).symm⟩
    rw [hUdef]
    exact (M₀.conj g).img_mono hZL heZ
  have hcardL : Nat.card ↥(Q ⊓ QB (conjSubgroup g Z)) =
      Nat.card (conjSubgroup g Z) * Nat.card ↥U := by
    rw [hUdef]
    exact (M₀.conj g).card_eq hLQ hBL
  have hperp : ∀ v : (M₀.conj g).E, (∀ u ∈ U, (M₀.conj g).B v u = 0) →
      (M₀.conj g).Qf v = 0 → v ∈ U := by
    intro v hvU hvQ
    obtain ⟨t, htQF, rfl⟩ := (M₀.conj g).π_surj v
    have htQB : t ∈ QB (conjSubgroup g Z) := by
      rw [hQB]
      exact htQF
    have hcentZ : t ∈ Subgroup.centralizer (Z : Set G) :=
      (Tim79.QuadModel.centralizer_iff (M₀ := M₀.conj g) h'.reg hZQ he htQF).mpr
        (hvU e heU)
    have hcommL : ∀ r ∈ Q ⊓ QB (conjSubgroup g Z), ⁅t, r⁆ ∈ Z := by
      intro r hr
      have hrQF : r ∈ conjSubgroup g Q := hLQ hr
      have hrU : (M₀.conj g).π r ∈ U := by
        rw [hUdef]
        exact (M₀.conj g).pi_mem_img hr hrQF
      have htr : t * r = r * t :=
        ((M₀.conj g).comm_iff_B h'.reg htQF hrQF).mpr (hvU _ hrU)
      have h1 : ⁅t, r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr htr
      rw [h1]
      exact Z.one_mem
    have htA0 : t ∈ A0 Q Z (conjSubgroup g Z) :=
      mem_A0.mpr ⟨⟨htQB, hcentZ⟩, hcommL⟩
    have hsq : t ^ 2 = 1 := ((M₀.conj g).sq_iff_Qf h'.reg htQF).mpr hvQ
    have htQ : t ∈ Q := by
      by_contra htQ
      exact hnot t htA0 htQ hsq
    have htL : t ∈ Q ⊓ QB (conjSubgroup g Z) := ⟨htQ, htQB⟩
    rw [hUdef]
    exact (M₀.conj g).pi_mem_img htL htQF
  have hcardU : Nat.card (GaloisField 2 m) ^ w ≤ Nat.card ↥U :=
    Tim79.QuadModel.card_ge_of_perp_singular (M₀.conj g) h'.hyperbolic hdim hU hperp
  rw [h.card] at hcardU
  rw [card_conjSubgroup] at hcardL
  have hpow : Nat.card Z ^ (w + 1) = Nat.card Z * Nat.card Z ^ w := by ring
  have key : Nat.card Z ^ (w + 1) ≤ Nat.card ↥(Q ⊓ QB (conjSubgroup g Z)) := by
    rw [hcardL, hpow]
    exact Nat.mul_le_mul (le_refl _) hcardU
  exact (not_lt.mpr key) hlt

end CFSG.RankThree.GF2n.Stroth80
