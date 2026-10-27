module

import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_zpowers_sq_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1)
    {x : G} (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  let H : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = g}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hg]
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (inv_eq_of_mul_eq_one_right hg) }
  exact Subgroup.zpowers_le.mpr (show g ∈ H from Or.inr rfl) hx

private theorem s16h_e3_l3_commSub_iSup {ι : Sort*} (U : ι → Subgroup W)
    (X : Subgroup (MulAut W)) : commSub (⨆ i, U i) X = ⨆ i, commSub (U i) X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    refine Subgroup.iSup_induction U (C := fun w => x w * w⁻¹ ∈ ⨆ i, commSub (U i) X) hw ?_ ?_ ?_
    · intro i w hw
      exact le_iSup (fun i => commSub (U i) X) i
        (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
    · simp
    · intro a b ha hb
      have heq : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [heq]
      exact Subgroup.mul_mem _ ha hb
  · exact iSup_le fun i => commSub_mono (le_iSup U i) le_rfl

private theorem s16h_e3_l3_commSub_sup_left (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have heq : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [heq]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem s16h_e3_l3_rk_commSub_invol_le_summand (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} (hI : BinaryNaturalSL L I Z 3 1)
    {γ : MulAut W} (hγL : γ ∈ L) (hγ2 : γ ^ 2 = 1) :
    rk ↥(commSub I (Subgroup.zpowers γ) ⊔ Z) ≤ rk ↥Z + 1 := by
  classical
  let D : L3Data L I Z := Classical.choice (BinaryNaturalSL.toL3Coord hI)
  obtain ⟨δ, hδ⟩ := D.exists_rho hγL
  by_cases hδ1 : δ = 1
  · have hγ1 : γ = 1 := by rw [← hδ, hδ1, map_one]
    have hcomm : commSub I (Subgroup.zpowers γ) = ⊥ := by
      rw [hγ1, Subgroup.zpowers_one_eq_bot, commSub_eq_bot_iff]
      intro x _ g hg
      rw [Subgroup.mem_bot.mp hg]
      simp
    rw [hcomm, bot_sup_eq]
    omega
  · have hδ2 : δ * δ = 1 := by
      apply D.rho_injective
      rw [map_mul, hδ, map_one, ← pow_two]
      exact hγ2
    have hδinvol : L3.IsInvol δ := ⟨hδ2, hδ1⟩
    obtain ⟨c, _hc0, hcim⟩ := L3.invol_center δ hδinvol
    set A : Subgroup W := commSub I (Subgroup.zpowers γ) ⊔ Z with hA
    change rk ↥A ≤ rk ↥Z + 1
    have hAI : A ≤ I := by
      rw [hA]
      exact sup_le (commSub_le_of_invariant fun x hx w hw =>
        D.inv_U x (Subgroup.zpowers_le.mpr hγL hx) w hw) D.Z_le
    let K : Subgroup ↥I := (Subgroup.zpowers (Multiplicative.ofAdd c)).comap D.β
    let KW : Subgroup W := K.map (Subgroup.subtype I)
    have hA_KW : A ≤ KW := by
      rw [hA]
      refine sup_le ?_ ?_
      · rw [commSub, Subgroup.closure_le]
        rintro y ⟨x, hx, w, hw, rfl⟩
        have hxL : x ∈ L := Subgroup.zpowers_le.mpr hγL hx
        have hxwI : x w ∈ I := D.inv_U x hxL w hw
        have hyI : x w * w⁻¹ ∈ I := I.mul_mem hxwI (I.inv_mem hw)
        refine Subgroup.mem_map.mpr ⟨⟨x w * w⁻¹, hyI⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
        let δ₀ : L3.Γ := δ ^ n
        have hxρ : D.rho δ₀ = x := by
          show D.rho (δ ^ n) = x
          rw [MonoidHom.map_zpow, hδ, hn]
        have hδ₀case : δ₀ = 1 ∨ δ₀ = δ :=
          s16h_e3_l3_zpowers_sq_eq_one hδ2 (Subgroup.zpow_mem_zpowers δ n)
        let z : Multiplicative L3.Vec := D.β ⟨w, hw⟩
        let v : L3.Vec := Multiplicative.toAdd z
        have hv : D.β ⟨x w * w⁻¹, hyI⟩ = Multiplicative.ofAdd (L3.act δ₀ v - v) := by
          have h1 : (⟨x w * w⁻¹, hyI⟩ : ↥I) = ⟨x w, hxwI⟩ * ⟨w, hw⟩⁻¹ :=
            Subtype.ext (by simp [mul_assoc])
          rw [h1, map_mul, map_inv]
          have h2 : (⟨x w, hxwI⟩ : ↥I) =
              ⟨D.rho δ₀ w, D.inv_U (D.rho δ₀) (D.rho_mem δ₀) w hw⟩ :=
            Subtype.ext ((congrArg (fun f : MulAut W => f w) hxρ).symm)
          rw [h2, D.β_rho δ₀ w hw (D.inv_U (D.rho δ₀) (D.rho_mem δ₀) w hw)]
          show Multiplicative.ofAdd (L3.act δ₀ (Multiplicative.toAdd z)) * z⁻¹ =
            Multiplicative.ofAdd (L3.act δ₀ v - v)
          rw [ofAdd_sub, div_eq_mul_inv]
          rw [show z = Multiplicative.ofAdd v from (ofAdd_toAdd z).symm]
          rw [toAdd_ofAdd]
          rfl
        rw [hv]
        rcases hδ₀case with hδ₀1 | hδ₀δ
        · rw [hδ₀1, L3.act_one, sub_self, ofAdd_zero]
          exact Subgroup.one_mem _
        · rw [hδ₀δ]
          have hcv : L3.act δ v - v ∈ L3.cim δ :=
            Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
          rw [hcim] at hcv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcv
          rcases hcv with h0 | hc
          · rw [h0, ofAdd_zero]
            exact Subgroup.one_mem _
          · rw [hc]
            exact Subgroup.mem_zpowers _
      · intro z hz
        refine Subgroup.mem_map.mpr ⟨⟨z, D.Z_le hz⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap, (D.ker_β ⟨z, D.Z_le hz⟩).2 hz]
        exact Subgroup.one_mem _
    have hAK : A.subgroupOf I ≤ K := by
      intro u hu
      obtain ⟨k, hkK, hkW⟩ := Subgroup.mem_map.mp (hA_KW (Subgroup.mem_subgroupOf.mp hu))
      rwa [Subtype.ext hkW] at hkK
    have himg : (A.subgroupOf I).map D.β ≤ Subgroup.zpowers (Multiplicative.ofAdd c) := by
      rw [Subgroup.map_le_iff_le_comap]
      exact hAK
    have himgcard : Nat.card ((A.subgroupOf I).map D.β) ≤ 2 := by
      have h2 : (Multiplicative.ofAdd c) ^ 2 = 1 := by
        rw [pow_two, ← ofAdd_add]
        have hcc : c + c = 0 := by
          funext i
          exact CharTwo.add_self_eq_zero (c i)
        rw [hcc, ofAdd_zero]
      have hcard : Nat.card (Subgroup.zpowers (Multiplicative.ofAdd c)) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) h2
      exact le_trans (Subgroup.card_le_of_le himg) hcard
    have hcardA : Nat.card ↥A =
        Nat.card ((A.subgroupOf I).map D.β) * Nat.card ↥Z := by
      have h1 := B1More.card_map_mul_card_inf_ker (A.subgroupOf I) D.β
      have hker : (A.subgroupOf I) ⊓ D.β.ker = Z.subgroupOf I := by
        ext u
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨-, hβ⟩
          exact (D.ker_β u).1 hβ
        · intro hu
          have huZ : (u : W) ∈ Z := Subgroup.mem_subgroupOf.mp hu
          have hZA : Z ≤ A := by rw [hA]; exact le_sup_right
          exact ⟨Subgroup.mem_subgroupOf.mpr (hZA huZ), (D.ker_β u).2 huZ⟩
      have hcardZ : Nat.card ↥(Z.subgroupOf I) = Nat.card ↥Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.Z_le).toEquiv
      have hcardA' : Nat.card ↥(A.subgroupOf I) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv
      rw [hker, hcardZ, hcardA'] at h1
      exact h1.symm
    have hbound : Nat.card ↥A ≤ 2 * Nat.card ↥Z := by
      rw [hcardA]
      exact Nat.mul_le_mul_right _ himgcard
    have hpow : 2 ^ rk ↥A ≤ 2 ^ (rk ↥Z + 1) := by
      calc 2 ^ rk ↥A = Nat.card ↥A := (card_eq_two_pow hW A).symm
        _ ≤ 2 * Nat.card ↥Z := hbound
        _ = 2 ^ (rk ↥Z + 1) := by rw [card_eq_two_pow hW Z, pow_succ]; ring
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

private theorem s16h_e3_l3_rk_iSup_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Subgroup W) (Z : Subgroup W) (hZ : ∀ i, Z ≤ A i) :
    rk ↥(Z ⊔ ⨆ i, A i) ≤ rk ↥Z + ∑ i, (rk ↥(A i) - rk ↥Z) := by
  have hfin : ∀ s : Finset ι,
      rk ↥(Z ⊔ ⨆ i ∈ s, A i) ≤ rk ↥Z + ∑ i ∈ s, (rk ↥(A i) - rk ↥Z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hbot : (⨆ i ∈ (∅ : Finset ι), A i) = ⊥ := by
          refine iSup_eq_bot.2 fun i => iSup_eq_bot.2 fun hi => ?_
          exact absurd hi (Finset.notMem_empty i)
        rw [hbot, sup_bot_eq]
        simp
    | insert a s ha ih =>
        have hsup : Z ⊔ ⨆ i ∈ insert a s, A i = (Z ⊔ ⨆ i ∈ s, A i) ⊔ A a := by
          rw [Finset.iSup_insert]
          ac_rfl
        rw [hsup]
        have hmod := rk_sup_add_rk_inf (Z ⊔ ⨆ i ∈ s, A i) (A a)
        have hZle : Z ≤ (Z ⊔ ⨆ i ∈ s, A i) ⊓ A a := le_inf le_sup_left (hZ a)
        have hrkinf := rk_mono hZle
        have hsum : ∑ i ∈ insert a s, (rk ↥(A i) - rk ↥Z) =
            (∑ i ∈ s, (rk ↥(A i) - rk ↥Z)) + (rk ↥(A a) - rk ↥Z) := by
          rw [Finset.sum_insert ha]
          omega
        rw [hsum]
        omega
  have huniv : (⨆ i ∈ (Finset.univ : Finset ι), A i) = ⨆ i, A i := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun _ => le_iSup (fun i => A i) i
    · refine iSup_le fun i =>
        le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset ι)) => A i) i (Finset.mem_univ i)
  have h := hfin Finset.univ
  rw [huniv] at h
  exact h

theorem s16h_e3_l3_rk_commSub_invol_le (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {Z : Subgroup W} {k : ℕ} (hZ : Z ≤ fixV L)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ Z k) {γ : MulAut W}
    (hγL : γ ∈ L) (hγ2 : γ ^ 2 = 1) :
    rk ↥(commSub ⊤ (Subgroup.zpowers γ) ⊔ Z) ≤ rk ↥Z + k := by
  obtain ⟨I, _hZI, _hind, hsup, hnat⟩ := hsum
  have hstep1 : ∀ i, rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) ≤ rk ↥Z + 1 :=
    fun i => s16h_e3_l3_rk_commSub_invol_le_summand hW (hnat i) hγL hγ2
  have hstep2 : commSub ⊤ (Subgroup.zpowers γ) ≤
      ⨆ i, commSub (I i) (Subgroup.zpowers γ) := by
    have hZfix : Z ≤ fixV (Subgroup.zpowers γ) := by
      intro z hz x hx
      exact hZ hz x (Subgroup.zpowers_le.mpr hγL hx)
    have hZbot : commSub Z (Subgroup.zpowers γ) = ⊥ := commSub_eq_bot_iff.mpr hZfix
    have h1 : commSub ⊤ (Subgroup.zpowers γ) =
        ⨆ i, commSub (I i) (Subgroup.zpowers γ) := by
      rw [← hsup, s16h_e3_l3_commSub_sup_left, s16h_e3_l3_commSub_iSup, hZbot, bot_sup_eq]
    exact h1.le
  have hstep3 : rk ↥(Z ⊔ ⨆ i, (commSub (I i) (Subgroup.zpowers γ) ⊔ Z)) ≤
      rk ↥Z + ∑ i, (rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) - rk ↥Z) :=
    s16h_e3_l3_rk_iSup_le (fun i => commSub (I i) (Subgroup.zpowers γ) ⊔ Z) Z
      (fun _ => le_sup_right)
  have hmono : rk ↥(commSub ⊤ (Subgroup.zpowers γ) ⊔ Z) ≤
      rk ↥(Z ⊔ ⨆ i, (commSub (I i) (Subgroup.zpowers γ) ⊔ Z)) := by
    apply rk_mono
    refine sup_le ?_ le_sup_left
    refine hstep2.trans ?_
    exact (iSup_le fun i => le_sup_left.trans
      (le_iSup (fun j => commSub (I j) (Subgroup.zpowers γ) ⊔ Z) i)).trans le_sup_right
  have hsumle : ∑ i : Fin k,
      (rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) - rk ↥Z) ≤ k := by
    have h1 : ∀ i, rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) - rk ↥Z ≤ 1 := by
      intro i
      have := hstep1 i
      omega
    calc ∑ i, (rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) - rk ↥Z)
        ≤ ∑ _i : Fin k, (1 : ℕ) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = k := by simp
  calc rk ↥(commSub ⊤ (Subgroup.zpowers γ) ⊔ Z)
      ≤ rk ↥(Z ⊔ ⨆ i, (commSub (I i) (Subgroup.zpowers γ) ⊔ Z)) := hmono
    _ ≤ rk ↥Z + ∑ i, (rk ↥(commSub (I i) (Subgroup.zpowers γ) ⊔ Z) - rk ↥Z) := hstep3
    _ ≤ rk ↥Z + k := Nat.add_le_add_left hsumle _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
