module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Asym

variable {G : Type} [Group G] [Finite G]

theorem asym_numerics {Z U UK Up X C A₁ D Dg : Subgroup G}
    (hUab : IsElemAbelian 2 U) (hXab : IsElemAbelian 2 X)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hUKU : UK ≤ U) (hUpU : Up ≤ U) (hZK : Z ≤ UK) (hZp : Z ≤ Up) (hinf : UK ⊓ Up = Z)
    (hCU : C ≤ U)
    (hdec : ∀ v ∈ U, ∃ a ∈ UK, ∃ b ∈ Up, ∃ c ∈ C, v = a * (b * c))
    (hCc : ∀ c ∈ C, ∀ e ∈ X, c * e * c⁻¹ * e⁻¹ ∈ Z)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hXK : ∀ e ∈ X, ∀ y ∈ UK, e * y * e⁻¹ ∈ UK) (hXp : ∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ ∈ Up)
    (hXU : ∀ e ∈ X, ∀ y ∈ U, e * y * e⁻¹ ∈ U)
    (hA₁X : A₁ ≤ X) (hA₁c : Nat.card A₁ = 2) (hD : D = centralizerMod A₁ U X)
    (hA₁Z : A₁ ⊓ Z = ⊥) (hA₁K : A₁ ≤ UK)
    (hDgX : Dg ≤ X) (hDg : ∀ x ∈ Dg, ∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z)
    (hfaith : ∀ x ∈ X, (∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z) → x ∈ Dg)
    (hlt : mIdx X Dg < mIdx U (centralizerMod Z U X)) (hasym : mIdx U D < mIdx X Dg)
    (ha2 : mIdx X (centralizerMod Z X UK) ≤ 2)
    (hNK : ¬ X ≤ centralizerMod Z X UK →
      mIdx X (centralizerMod Z X UK) + 1 ≤ mIdx UK (centralizerMod Z UK X))
    (hNp : ¬ X ≤ centralizerMod Z X Up →
      mIdx X (centralizerMod Z X Up) + 1 ≤ mIdx Up (centralizerMod Z Up X)) :
    (∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ * y⁻¹ ∈ Z) ∧ mIdx U D = 1 ∧ mIdx X Dg = 2 ∧
      ¬ X ≤ centralizerMod Z X UK := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hXp2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => isElemAbelian_comm hXab hx hy
  set XK := centralizerMod Z X UK with hXK'
  set Xp := centralizerMod Z X Up with hXp'
  set CU := centralizerMod Z U X with hCU'
  have hXZ : ∀ e ∈ X, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := fun e he z hz =>
    (Subgroup.mem_normalizer_iff.mp (hXN he) z).mp hz
  have hDU : D ≤ U := hD ▸ centralizerMod_le_left _ _ _
  have hDp2 : IsPGroup 2 D := hUp2.to_le hDU
  have hnp : ¬ A₁ ≤ Up := by
    intro h
    have h1 : A₁ ≤ Z := hinf ▸ le_inf hA₁K h
    have h2 : A₁ ≤ ⊥ := hA₁Z ▸ le_inf le_rfl h1
    have h3 : Nat.card A₁ = 1 := by
      rw [le_bot_iff.mp h2]; exact Subgroup.card_bot
    omega
  have hdecK' : ∀ v ∈ U, ∃ a ∈ Up, ∃ b ∈ UK, ∃ c ∈ C, v = a * (b * c) := by
    intro v hv
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdec v hv
    refine ⟨b, hb, a, ha, c, hc, ?_⟩
    have hbU := hUpU hb
    have haU := hUKU ha
    have hcU := hCU hc
    calc a * (b * c) = a * b * c := by group
      _ = b * a * c := by rw [hUc a haU b hbU]
      _ = b * (a * c) := by group
  have hXKD0 : ∀ e ∈ XK, e ∈ Subgroup.centralizer (D : Set G) := by
    intro e he
    obtain ⟨heX, -, heW⟩ := he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdD : d ∈ D := hd
    rw [hD] at hdD
    obtain ⟨hdU, -, hdA⟩ := hdD
    have hA : d * e * d⁻¹ * e⁻¹ ∈ A₁ := hdA e heX
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdecK' d hdU
    have haU := hUpU ha
    have hbU := hUKU hb
    have hcU := hCU hc
    have hbcU : b * c ∈ U := U.mul_mem hbU hcU
    have hexp : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ =
        (e * a * e⁻¹ * a⁻¹) * ((e * b * e⁻¹ * b⁻¹) * (e * c * e⁻¹ * c⁻¹)) := by
      rw [comm_mul_of_abelian hUc (fun x hx => hXU e heX x hx) haU hbcU,
        comm_mul_of_abelian hUc (fun x hx => hXU e heX x hx) hbU hcU]
    have h1 : e * a * e⁻¹ * a⁻¹ ∈ Up := Up.mul_mem (hXp e heX a ha) (Up.inv_mem ha)
    have h2 : e * b * e⁻¹ * b⁻¹ ∈ Z := heW b hb
    have h3 : e * c * e⁻¹ * c⁻¹ ∈ Z := by
      have := hCc c hc e heX
      have e1 : e * c * e⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹)⁻¹ := by group
      rw [e1]; exact Z.inv_mem this
    have hmemV : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ ∈ Up := by
      rw [hexp]; exact Up.mul_mem h1 (Up.mul_mem (hZp h2) (hZp h3))
    have hmemA : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ ∈ A₁ := by
      have e1 : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ =
          ((a * (b * c)) * e * (a * (b * c))⁻¹ * e⁻¹)⁻¹ := by group
      rw [e1]; exact A₁.inv_mem hA
    have h1' := eq_one_of_mem_inf_of_card_two hA₁c hnp hmemA hmemV
    have : e * (a * (b * c)) = (a * (b * c)) * e := by
      calc e * (a * (b * c)) = (e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹) * (a * (b * c)) * e := by
            group
        _ = (a * (b * c)) * e := by rw [h1']; group
    exact this.symm
  have hXKD : XK ≤ X ⊓ Subgroup.centralizer (D : Set G) := fun e he => ⟨he.1, hXKD0 e he⟩
  set CX := X ⊓ Subgroup.centralizer (D : Set G) with hCX
  set CD := D ⊓ Subgroup.centralizer (X : Set G) with hCD
  have hcomm : ⁅D, X⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro d hd x hx
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    exact hd'.2.2 x hx
  have hCXc : A₁ ≤ Subgroup.centralizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    have hdN : d ∈ Subgroup.normalizer (A₁ : Set G) := hd'.2.1
    rw [normalizer_eq_centralizer_of_card_eq_two hA₁c] at hdN
    exact (Subgroup.mem_centralizer_iff.mp hdN a ha).symm
  have hCYc : A₁ ≤ Subgroup.centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hXc x hx a (hA₁X ha)
  have hpair := relIndex_eq_of_commutator_le (X := D) (Y := X) (C := A₁) hXab hA₁c hcomm hCXc hCYc
  have hmDX : mIdx D CD = mIdx X CX := by
    have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CD) hDp2
    have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := CX) hXp2
    rw [e1, e2] at hpair
    exact Nat.pow_right_injective (le_refl 2) hpair
  have hCDle : CD ≤ CU := by
    intro d hd
    refine ⟨hDU hd.1, hUN (hDU hd.1), fun e he => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hd.2 e he
    have e1 : d * e * d⁻¹ * e⁻¹ = 1 := by
      calc d * e * d⁻¹ * e⁻¹ = (e * d) * d⁻¹ * e⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e1]; exact Z.one_mem
  have hf1 : mIdx U CU ≤ mIdx U D + mIdx D CD := by
    have h1 : mIdx U CU ≤ mIdx U CD := mIdx_anti_of_le (X := U) hCDle
    have h2 : mIdx U CD = mIdx U D + mIdx D CD := mIdx_add hUp2 hDU (inf_le_left : CD ≤ D)
    omega
  have hDgXK : Dg ≤ XK := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUKU hy)⟩
  have hDgXp : Dg ≤ Xp := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUpU hy)⟩
  have hXKXp : XK ⊓ Xp = Dg := by
    apply le_antisymm
    · rintro x ⟨hxK, hxp⟩
      refine hfaith x hxK.1 fun v hv => ?_
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdec v hv
      have haU := hUKU ha
      have hbU := hUpU hb
      have hcU := hCU hc
      have hbcU : b * c ∈ U := U.mul_mem hbU hcU
      have hexp : x * (a * (b * c)) * x⁻¹ * (a * (b * c))⁻¹ =
          (x * a * x⁻¹ * a⁻¹) * ((x * b * x⁻¹ * b⁻¹) * (x * c * x⁻¹ * c⁻¹)) := by
        rw [comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) haU hbcU,
          comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) hbU hcU]
      rw [hexp]
      have h3 : x * c * x⁻¹ * c⁻¹ ∈ Z := by
        have := hCc c hc x hxK.1
        have e1 : x * c * x⁻¹ * c⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
        rw [e1]; exact Z.inv_mem this
      exact Z.mul_mem (hxK.2.2 a ha) (Z.mul_mem (hxp.2.2 b hb) h3)
    · exact le_inf hDgXK hDgXp
  have hXKX : XK ≤ X := centralizerMod_le_left _ _ _
  have hXpX : Xp ≤ X := centralizerMod_le_left _ _ _
  have hsupX : XK ⊔ Xp ≤ X := sup_le hXKX hXpX
  have hPsupX : IsPGroup 2 ↥(XK ⊔ Xp) := hXp2.to_le hsupX
  have hP2 : mIdx (XK ⊔ Xp) Dg = mIdx XK Dg + mIdx Xp Dg :=
    mIdx_sup_of_inf_eq (fun x hx y hy => hXc x (hXKX hx) y (hXpX hy)) hDgXK hDgXp hXKXp hPsupX
  have hm1 : mIdx X Dg = mIdx X (XK ⊔ Xp) + mIdx (XK ⊔ Xp) Dg :=
    mIdx_add hXp2 hsupX (hDgXK.trans le_sup_left)
  have hmXK : mIdx X Dg = mIdx X XK + mIdx XK Dg := mIdx_add hXp2 hXKX hDgXK
  have hmXp : mIdx X Dg = mIdx X Xp + mIdx Xp Dg := mIdx_add hXp2 hXpX hDgXp
  have hCXle : mIdx X CX ≤ mIdx X XK := mIdx_anti_of_le (X := X) hXKD
  have hCXtop : X ≤ CX → mIdx X CX = 0 := by
    intro h
    have : CX = X := le_antisymm inf_le_left h
    rw [this]
    unfold mIdx
    rw [Subgroup.relIndex_self]
    simp
  have hnXK : ¬ X ≤ XK := by
    intro h
    have h0 := hCXtop (h.trans hXKD)
    omega
  have hNK' := hNK hnXK
  have hsum : mIdx UK (centralizerMod Z UK X) + mIdx Up (centralizerMod Z Up X) ≤ mIdx U CU :=
    mIdx_centralizerMod_sum_le hUp2 hUc hUKU hUpU hZK hZp hinf hUN hXZ hXK hXp hXU
  by_cases hX : X ≤ Xp
  · have hXpeq : Xp = X := le_antisymm hXpX hX
    have hDgeq : Dg = XK := by
      rw [← hXKXp, hXpeq]; exact inf_eq_left.mpr hXKX
    have hz : mIdx XK Dg = 0 := by
      rw [hDgeq]; unfold mIdx; rw [Subgroup.relIndex_self]; simp
    refine ⟨fun e he y hy => ?_, by omega, by omega, hnXK⟩
    have : e ∈ Xp := hX he
    exact this.2.2 y hy
  · exfalso
    have hNp' := hNp hX
    omega

end Asym

end CFSG.Quasithin.ThreeC
