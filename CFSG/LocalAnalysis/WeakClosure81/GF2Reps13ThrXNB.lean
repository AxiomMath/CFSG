module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXFB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

structure HNon (A Q O : Subgroup (MulAut W)) (t : MulAut W) : Prop where
  hW : ∀ w : W, w * w = 1
  htA : t ∈ A
  ht2 : t ^ 2 = 1
  ht1 : t ≠ 1
  hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  hO3 : IsPGroup 3 ↥O
  hOle : O ≤ A
  hOA : ∀ g ∈ A, ∀ x ∈ O, g * x * g⁻¹ ∈ O
  hQe : IsElemAbelian 3 Q
  hQO : Q ≤ O
  hQN : ∀ n ∈ O, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q
  hQ1 : Q ≠ ⊥
  hQinv : ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹
  hnc : ∃ g ∈ A, ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16n_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Finite X := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 (x : MulAut W) x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn]
  exact Odd.pow (hp.odd_of_ne_two hp2)

private theorem w16n_dParam_three : dParam 3 = 2 := by
  rw [dParam]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by decide) (by decide)

private theorem w16n_two_mul_card_le_sum {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h2 : ∀ i, 2 ≤ f i) : 2 * Nat.card ι ≤ ∑ i, f i := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : ι => 2) (g := f)
    (fun i _ => h2 i)
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    mul_comm] at h
  exact h


public theorem w16n_components_kernel (h : HNon A Q O t) :
    ∀ U ∈ s13IsoComps Q, ∀ U' ∈ s13IsoComps Q, s13KerOn Q U = s13KerOn Q U' → U = U' :=
  fun _ hU _ hU' hk => s13_isoComps_eq_of_kerOn_eq h.hW h.hQe hU hU' hk

theorem w16n_components (h : HNon A Q O t) :
    (∀ U ∈ s13IsoComps Q, ∀ U' ∈ s13IsoComps Q, s13KerOn Q U = s13KerOn Q U' → U = U') ∧
      (∑ᶠ (U : Subgroup W) (_ : U ∈ s13IsoComps Q), rk ↥U) ≤ 6 ∧
      (s13IsoComps Q).ncard ≤ 3 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd (Nat.card Q) := w16n_odd_card_of_isElemAbelian hp3 hp32 h.hQe
  have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := by
    intro x hx
    rw [h.hQinv x hx]
    exact Q.inv_mem hx
  have htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := by
    intro x hx
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
    simpa only [htinv] using htQ x hx
  have hsS : ∀ U ∈ s13IsoComps Q, U.map t.toMonoidHom ∈ s13IsoComps Q :=
    fun U hU => map_mem_s13IsoComps htQ htQ' hU
  have hfix : ∀ U ∈ s13IsoComps Q, U.map t.toMonoidHom = U →
      3 = 3 ∧ ∀ x ∈ Q, t * x * t⁻¹ * x ∈ s13KerOn Q U := by
    intro U hU _
    refine ⟨rfl, fun x hx => ?_⟩
    rw [h.hQinv x hx, inv_mul_cancel]
    exact (s13KerOn Q U).one_mem
  have hcost := s13_cost_eq h.hW (Or.inl rfl) h.hQe ht2' htQ (fun U hU => hU) hsS hfix
  have hsup : (⨆ U ∈ s13IsoComps Q, U) = commSub ⊤ Q := iSup_s13IsoComps h.hW hodd
  rw [hsup] at hcost
  have hle : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
    rk_mono (commSub_mono le_top le_rfl)
  have h3 : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) ≤ 3 := le_trans hle h.hrk
  have hsum6 : (∑ᶠ (U : Subgroup W) (_ : U ∈ s13IsoComps Q), rk ↥U) ≤ 6 := by
    rw [← hcost]
    omega
  refine ⟨?_, hsum6, ?_⟩
  · exact w16n_components_kernel h
  · classical
    haveI : Finite (Subgroup W) :=
      Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
    haveI : Fintype {U : Subgroup W // U ∈ s13IsoComps Q} := Fintype.ofFinite _
    have hsum' : (∑ i : {U : Subgroup W // U ∈ s13IsoComps Q}, rk ↥(i.1)) ≤ 6 := by
      rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype] at hsum6
      exact hsum6
    have h2rk : ∀ i : {U : Subgroup W // U ∈ s13IsoComps Q}, 2 ≤ rk ↥(i.1) := by
      intro i
      obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hQe i.2
      rw [w16n_dParam_three] at hsrk
      omega
    have hcardN : Nat.card {U : Subgroup W // U ∈ s13IsoComps Q} = (s13IsoComps Q).ncard :=
      Nat.card_coe_set_eq _
    have htwo : 2 * Nat.card {U : Subgroup W // U ∈ s13IsoComps Q} ≤
        ∑ i : {U : Subgroup W // U ∈ s13IsoComps Q}, rk ↥(i.1) :=
      w16n_two_mul_card_le_sum _ h2rk
    rw [hcardN] at htwo
    omega

end CFSG.LocalAnalysis.WeakClosure81
