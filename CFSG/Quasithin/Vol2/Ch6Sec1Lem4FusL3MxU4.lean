module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCover3
public import CFSG.Quasithin.Vol2.Ch6SL2Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

private theorem odd_card_of_pow_three_L3mxU4 {Z : Type*} [Group Z] [Finite Z]
    (h : ∀ z : Z, z ^ 3 = 1) : Odd (Nat.card Z) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card Z := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at h3
  omega

theorem rank_statedSU {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = (p ^ 1) ^ 2) {G : Type*} [Group G] (ψ : ↥(StatedSU 3 (p ^ 1) F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ 1) F)) :
    ∀ V : Subgroup G, V ≤ ψ.range → IsElemAbelian 2 V → Nat.card V ≤ 4 := by
  intro V hV hVel
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, hF.trans (by ring)⟩
  haveI : CharP F p := hU.charP
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  have hcen : ∀ z ∈ ψ.ker, z ∈ Subgroup.center ↥(StatedSU 3 (p ^ 1) F) := fun z hz =>
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center (StatedSU 3 (p ^ 1) F) (hker hz)
  have hz3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := fun z hz =>
    CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three hU z
      (by rw [QuotientGroup.ker_mk']; exact hker hz)
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_of_pow_three_L3mxU4 (fun z => Subtype.ext (by simpa using hz3 z.1 z.2))
  have hkerc : ∀ g ∈ ψ.ker, ∀ h : ↥(StatedSU 3 (p ^ 1) F), g * h = h * g := fun g hg h =>
    (Subgroup.mem_center_iff.mp (hcen g hg) h).symm
  have hm : ∀ T : Subgroup ↥(StatedSU 3 (p ^ 1) F), (∀ x ∈ T, x * x = 1) → Nat.card T ≤ 4 :=
    fun T hT => CFSG.QuasithinUnique.Setup.Family.card_le_four_of_det_one h2
      (H := StatedSU 3 (p ^ 1) F) (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU hx) T hT
  have hE2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hVel.2 x hx
  have hEc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact CFSG.QuasithinUnique.Setup.Family.card_le_of_lifts ψ hkerc hodd 4 hm V hV hE2 hEc

end CFSG.Quasithin.H13
