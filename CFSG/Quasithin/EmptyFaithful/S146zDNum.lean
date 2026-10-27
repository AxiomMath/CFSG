module

public import CFSG.Quasithin.EmptyFaithful.S146zNCount

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Num

variable {G : Type} [Group G] [Finite G]

theorem r_lt_f {Z U UK Up X C : Subgroup G}
    (hUab : IsElemAbelian 2 U) (hXab : IsElemAbelian 2 X)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hUKU : UK ≤ U) (hUpU : Up ≤ U) (hZK : Z ≤ UK) (hZp : Z ≤ Up) (hinf : UK ⊓ Up = Z)
    (hCU : C ≤ U)
    (hdec : ∀ v ∈ U, ∃ a ∈ UK, ∃ b ∈ Up, ∃ c ∈ C, v = a * (b * c))
    (hCc : ∀ c ∈ C, ∀ e ∈ X, c * e * c⁻¹ * e⁻¹ ∈ Z)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hXK : ∀ e ∈ X, ∀ y ∈ UK, e * y * e⁻¹ ∈ UK) (hXp : ∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ ∈ Up)
    (hXU : ∀ e ∈ X, ∀ y ∈ U, e * y * e⁻¹ ∈ U)
    (hnt : ¬ X ≤ centralizerMod Z X U)
    (hNK : ¬ X ≤ centralizerMod Z X UK →
      mIdx X (centralizerMod Z X UK) + 1 ≤ mIdx UK (centralizerMod Z UK X))
    (hNp : ¬ X ≤ centralizerMod Z X Up →
      mIdx X (centralizerMod Z X Up) + 1 ≤ mIdx Up (centralizerMod Z Up X)) :
    mIdx X (centralizerMod Z X U) < mIdx U (centralizerMod Z U X) := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hXp2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => isElemAbelian_comm hXab hx hy
  set Dg := centralizerMod Z X U with hDg
  set XK := centralizerMod Z X UK with hXK'
  set Xp := centralizerMod Z X Up with hXp'
  have hXZ : ∀ e ∈ X, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := fun e he z hz =>
    (Subgroup.mem_normalizer_iff.mp (hXN he) z).mp hz
  have hDgXK : Dg ≤ XK := fun x hx => ⟨hx.1, hx.2.1, fun y hy => hx.2.2 y (hUKU hy)⟩
  have hDgXp : Dg ≤ Xp := fun x hx => ⟨hx.1, hx.2.1, fun y hy => hx.2.2 y (hUpU hy)⟩
  have hXKXp : XK ⊓ Xp = Dg := by
    apply le_antisymm
    · rintro x ⟨hxK, hxp⟩
      refine ⟨hxK.1, hxK.2.1, fun v hv => ?_⟩
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
    ThreeC.mIdx_sup_of_inf_eq (fun x hx y hy => hXc x (hXKX hx) y (hXpX hy)) hDgXK hDgXp hXKXp hPsupX
  have hm1 : mIdx X Dg = mIdx X (XK ⊔ Xp) + mIdx (XK ⊔ Xp) Dg :=
    ThreeC.mIdx_add hXp2 hsupX (hDgXK.trans le_sup_left)
  have hmXK : mIdx X Dg = mIdx X XK + mIdx XK Dg := ThreeC.mIdx_add hXp2 hXKX hDgXK
  have hmXp : mIdx X Dg = mIdx X Xp + mIdx Xp Dg := ThreeC.mIdx_add hXp2 hXpX hDgXp
  have hsum : mIdx UK (centralizerMod Z UK X) + mIdx Up (centralizerMod Z Up X) ≤
      mIdx U (centralizerMod Z U X) :=
    ThreeC.mIdx_centralizerMod_sum_le hUp2 hUc hUKU hUpU hZK hZp hinf hUN hXZ hXK hXp hXU
  by_cases hK : X ≤ XK
  · by_cases hp : X ≤ Xp
    · exact absurd (fun x hx => (hXKXp ▸ (⟨hK hx, hp hx⟩ : x ∈ XK ⊓ Xp))) hnt
    · have h2 := hNp hp
      have h0 : mIdx X XK = 0 := by
        have : XK = X := le_antisymm hXKX hK
        rw [this]; unfold mIdx; rw [Subgroup.relIndex_self]; simp
      omega
  · have h1 := hNK hK
    by_cases hp : X ≤ Xp
    · have h0 : mIdx X Xp = 0 := by
        have : Xp = X := le_antisymm hXpX hp
        rw [this]; unfold mIdx; rw [Subgroup.relIndex_self]; simp
      omega
    · have h2 := hNp hp
      omega

end Num

end CFSG.Quasithin.ThreeD
