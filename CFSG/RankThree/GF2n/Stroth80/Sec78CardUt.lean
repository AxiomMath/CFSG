module

public import CFSG.RankThree.GF2n.Stroth80.Sec83UpperModule

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_secHyp (hc : Ctx M Q Z B) {R : Subgroup G} (hRM : R ≤ M) : SecHyp R Q Z :=
  ⟨hc.Z_le_Q, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy,
    fun x hx => hc.hyp.toHyp79.sq_mem_V hx,
    fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hr)) x).mp hx,
    fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hRM hr)) x).mp hx⟩

theorem sec7ctr_card_Ut_le (hc : Ctx M Q Z B) {R : Subgroup G} (hRM : R ≤ M) {s : G}
    (hsR : s ∈ R) (hsc : ∀ ρ ∈ R, ⁅ρ⁻¹, s⁆ ∈ Q) {W : Subgroup G} (hZW : Z ≤ W) (hWQ : W ≤ Q)
    (hW : ∀ w ∈ W, ⁅w, s⁆ ∈ Z) :
    Nat.card ↥(Ut Q Z s) * Nat.card ↥W ≤ Nat.card ↥Z * Nat.card ↥Q := by
  classical
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hSec := sec7ctr_secHyp hc hRM
  have hP := hSec.normP
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Md := hκ.finite
  obtain ⟨ε, hε, hεR⟩ := exists_comm_endo hc hRM hκ (hRM hsR) hsc
  obtain ⟨U, hZU, hUQ, hUε⟩ := exists_secSub_eq hZQ hκ ε.range
  have hinvU : ∀ z : ↥R, ∀ a ∈ secSub κ U, z • a ∈ secSub κ U := by
    intro z a ha
    rw [hUε] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨z • b, hεR z b⟩
  have hRU := conj_mem_of_secSub_invariant hκ hP hZU hUQ hinvU
  have hsM : s ∈ M := hRM hsR
  have hsU : ∀ x ∈ Q, ⁅x, s⁆ ∈ U := by
    intro x hx
    have h1 : Multiplicative.toAdd (κ ⟨⁅x, s⁆, hc.comm_mem_Q hsM hx⟩) ∈ secSub κ U := by
      rw [hUε, ← hε ⟨x, hx⟩]
      exact ⟨_, rfl⟩
    exact (toAdd_mem_secSub_iff hκ hZU _).mp h1
  have hsNorm : s ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_normalizer_fintype fun u hu => hRU s hsR u hu
  have hUt : Ut Q Z s ≤ U := sup_le (commutator_zpowers_le hsNorm hsU) hZU
  have hcardU : Nat.card ↥(secSub κ U) * Nat.card ↥Z = Nat.card ↥U :=
    natCard_secSub_mul hZQ hκ hZU hUQ
  have hcardW : Nat.card ↥(secSub κ W) * Nat.card ↥Z = Nat.card ↥W :=
    natCard_secSub_mul hZQ hκ hZW hWQ
  have hcardQ : Nat.card ↥Q = Nat.card ↥Z * Nat.card Md := natCard_eq_of_isSecMod hZQ hκ
  have hkerW : secSub κ W ≤ ε.ker := by
    intro a ha
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [AddMonoidHom.mem_ker, ← hxa', hε x]
    have h1 : κ ⟨⁅(x : G), s⁆, hc.comm_mem_Q hsM x.2⟩ = 1 := (hκ.ker _).mpr (hW _ hxW)
    rw [h1]
    rfl
  have hrk := AddSubgroup.card_ker_mul_card_range ε
  have h2 : Nat.card ↥(secSub κ W) ≤ Nat.card ↥ε.ker := Nat.card_mono (Set.toFinite _) hkerW
  have h3 : Nat.card ↥(Ut Q Z s) ≤ Nat.card ↥U := Nat.card_mono (Set.toFinite _) hUt
  have h4 : Nat.card ↥(secSub κ U) = Nat.card ↥ε.range := by rw [hUε]
  have hpos : 0 < Nat.card ↥ε.range := Nat.card_pos
  calc Nat.card ↥(Ut Q Z s) * Nat.card ↥W ≤ Nat.card ↥U * Nat.card ↥W :=
        Nat.mul_le_mul_right _ h3
    _ = (Nat.card ↥ε.range * Nat.card ↥Z) * (Nat.card ↥(secSub κ W) * Nat.card ↥Z) := by
        rw [← hcardU, ← hcardW, h4]
    _ ≤ (Nat.card ↥ε.range * Nat.card ↥Z) * (Nat.card ↥ε.ker * Nat.card ↥Z) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = Nat.card ↥Z * (Nat.card ↥Z * Nat.card Md) := by
        rw [← hrk]; ring
    _ = Nat.card ↥Z * Nat.card ↥Q := by rw [hcardQ]

end CFSG.RankThree.GF2n.Stroth80
