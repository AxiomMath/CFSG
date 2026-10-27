module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FQ
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FChief

public section

namespace CFSG.Quasithin.H13.M22F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

@[expose] def Code22Ord3Rank6_m22f : Prop :=
  ∀ g : ↥mog22plus, orderOf g = 3 →
    6 ≤ rkIdx (fixV (Subgroup.zpowers (rhoC10 mog22plus le_rfl g)))

theorem rkIdx_fixV_ord3_of_normalizer
    {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} (hL : MathieuCode22 L ⊤ ⊥)
    (hord : Code22Ord3Rank6_m22f) {t : MulAut V}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (ht3 : orderOf t = 3) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨e, he⟩ := code22_std hL
  have hA : Subgroup.zpowers t ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    Subgroup.zpowers_le.mpr ht
  have hIO : IsOver L (Subgroup.normalizer (L : Set (MulAut V))) :=
    ⟨Subgroup.le_normalizer, le_rfl⟩
  have hle := map_le_of_normalizer hIO he normalizer_rhoC10_mog22 hA
  have hmem : congrHom e t ∈ (rhoC10 mog22plus le_rfl).range :=
    hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers t))
  obtain ⟨g, hg⟩ := hmem
  have hord3 : orderOf g = 3 := by
    have h1 := orderOf_injective _ rhoC10_mog22plus_injective g
    have h2 := orderOf_injective _ (congrHom_injective e) t
    have h3 : orderOf (rhoC10 mog22plus le_rfl g) = 3 := by
      rw [hg]
      exact h2.trans ht3
    exact h1.symm.trans h3
  have h6 := hord g hord3
  have hM' : (Subgroup.zpowers t).map (congrHom e) = Subgroup.zpowers (rhoC10 mog22plus le_rfl g) :=
    (MonoidHom.map_zpowers (congrHom e) t).trans (congrArg Subgroup.zpowers hg.symm)
  calc 6 ≤ rkIdx (fixV (Subgroup.zpowers (rhoC10 mog22plus le_rfl g))) := h6
    _ = rkIdx (fixV ((Subgroup.zpowers t).map (congrHom e))) :=
      congrArg (fun H : Subgroup _ => rkIdx (fixV H)) hM'.symm
    _ = rkIdx (fixV (Subgroup.zpowers t)) := rkIdx_fixV_map_congrHom e _

theorem six6iii_img_m22f
    {G : Type} [Group G] [Finite G] {V L₀ M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (L₀ : Set G)) (hL : CodeHyp22_m22f hV L₀) (hord : Code22Ord3Rank6_m22f) :
    ∀ X : Subgroup G, X ≤ M → X ≤ Subgroup.normalizer (V : Set G) → Nat.card (autOn X V) = 3 →
      ∀ k : ℕ, IsChiefSeriesFrom X V V k → 3 ≤ k := by
  intro X hXM hXN hcard k hk
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autOn X V)) 3 (by rw [hcard])
  have hτ3 : orderOf (t : MulAut ↥V) = 3 := (Subgroup.orderOf_coe t).trans ht
  have hτX : (t : MulAut ↥V) ∈ autOn X V := t.2
  have hτN : (t : MulAut ↥V) ∈ Subgroup.normalizer (autOn L₀ V : Set (MulAut ↥V)) :=
    (AutOn.autOn_le_normalizer_autOn (hXM.trans hMN)) hτX
  have hcodim' : 6 ≤ rkIdx (fixV (Subgroup.zpowers (t : MulAut ↥V))) :=
    rkIdx_fixV_ord3_of_normalizer hL hord hτN hτ3
  obtain ⟨n, hnX, hnt⟩ := AutOn.mem_autOn_iff.mp hτX
  have hτ3' : (t : MulAut ↥V) ^ 3 = 1 := by
    rw [← hτ3]
    exact pow_orderOf_eq_one _
  have hy3 : ∀ v ∈ V, (n : G) ^ 3 * v * ((n : G) ^ 3)⁻¹ = v := by
    intro v hv
    have h1 : conjAct V (n ^ 3) = 1 := by
      rw [map_pow, hnt]
      exact hτ3'
    have h2 : ((conjAct V (n ^ 3) ⟨v, hv⟩ : ↥V) : G) = v := by
      rw [h1]
      rfl
    rw [conjAct_apply_m22f] at h2
    simpa using h2
  have hzp : Subgroup.zpowers (t : MulAut ↥V) = autOn X V := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hτX) ?_
    exact le_of_eq (by rw [Nat.card_zpowers, hτ3, hcard])
  have hX : ∀ g ∈ X, ∃ j : ℕ, ∀ v ∈ V, g * v * g⁻¹ = (n : G) ^ j * v * ((n : G) ^ j)⁻¹ := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := hXN hg
    have hgX : conjAct V ⟨g, hgN⟩ ∈ autOn X V := AutOn.conjAct_mem_autOn_of_mem hgN hg
    have hmem : conjAct V ⟨g, hgN⟩ ∈ Subgroup.zpowers (t : MulAut ↥V) := by
      rw [hzp]
      exact hgX
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    refine ⟨j, fun v hv => ?_⟩
    have e2 : (t : MulAut ↥V) ^ j = conjAct V (n ^ j) := by
      rw [map_pow, hnt]
    have h4 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) (hj.symm.trans e2)
    rw [conjAct_apply_m22f, conjAct_apply_m22f] at h4
    simpa using h4
  let S : OrdThreeAct_m22f V X (n : G) :=
    ⟨hV, n.2, hy3, hnX, hX⟩
  have hC : centV_m22f S = fixV (Subgroup.zpowers (t : MulAut ↥V)) := by
    ext v
    rw [mem_fixV_zpowers_iff_apply]
    change (((n : G) * (v : G) * (n : G)⁻¹) = (v : G)) ↔ _
    constructor
    · intro h
      apply Subtype.ext
      rw [← hnt, conjAct_apply_m22f]
      exact h
    · intro h
      have h' := congrArg Subtype.val h
      rw [← hnt, conjAct_apply_m22f] at h'
      exact h'
  have hcodim : 6 ≤ rkIdx (centV_m22f S) := by
    rw [hC]
    exact hcodim'
  exact three_le_of_codim_m22f S hcodim hk

end CFSG.Quasithin.H13.M22F
