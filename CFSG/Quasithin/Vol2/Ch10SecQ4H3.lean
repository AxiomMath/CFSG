module

public import CFSG.Quasithin.Vol2.Ch10SecQ4H2
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {H V : Subgroup G} {t v : G}
  (hUe : IsElemAbelian 2 (conjClosure (Subgroup.zpowers v) H))

@[expose] noncomputable def centreI : IntMod (conjClosure (Subgroup.zpowers v) H) hUe :=
  IntMod.mk hUe ⟨v, le_conjClosure _ H (Subgroup.mem_zpowers v)⟩

@[expose] noncomputable def transvI (htH : t ∈ H) :
    MulAut (IntMod (conjClosure (Subgroup.zpowers v) H) hUe) :=
  convI hUe ⟨t, le_normalizer_conjClosure _ H htH⟩

theorem centreI_val : (centreI hUe).val = v := rfl

theorem transvI_apply_val (htH : t ∈ H) (u : IntMod (conjClosure (Subgroup.zpowers v) H) hUe) :
    (transvI hUe htH u).val = t * u.val * t⁻¹ :=
  convI_apply_val hUe _ u

theorem transvI_mem (htH : t ∈ H) : transvI hUe htH ∈ autI hUe H :=
  convI_mem_autI hUe htH _

theorem centreI_ne_one (hv1 : v ≠ 1) : centreI hUe ≠ 1 := fun h =>
  hv1 (congrArg IntMod.val h)

theorem transvI_apply (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hv : v ∈ V)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v) (htH : t ∈ H)
    (u : IntMod (conjClosure (Subgroup.zpowers v) H) hUe) :
    transvI hUe htH u = u ∨ transvI hUe htH u = u * centreI hUe := by
  rcases htr u.val (conjClosure_zpowers_le hHV hv u.val_mem) with h | h
  · left
    apply IntMod.val_injective
    rw [transvI_apply_val]
    exact h
  · right
    apply IntMod.val_injective
    rw [transvI_apply_val, IntMod.val_mul]
    exact h

theorem transvI_centreI (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) (hv1 : v ≠ 1)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v) (htH : t ∈ H) :
    transvI hUe htH (centreI hUe) = centreI hUe := by
  rcases transvI_apply hUe hHV hv htr htH (centreI hUe) with h | h
  · exact h
  · exfalso
    rw [← pow_two, IntMod.sq_eq_one] at h
    exact centreI_ne_one hUe hv1 ((transvI hUe htH).injective (h.trans (map_one _).symm))

theorem transvI_sq (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) (hv1 : v ≠ 1)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v) (htH : t ∈ H) :
    transvI hUe htH ^ 2 = 1 := by
  ext u
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  rcases transvI_apply hUe hHV hv htr htH u with h | h
  · rw [h, h]
  · rw [h, map_mul, h, transvI_centreI hUe hHV hv hv1 htr htH, mul_assoc, ← pow_two,
      IntMod.sq_eq_one, mul_one]

theorem transvI_ne_one (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) : transvI hUe htH ≠ 1 :=
  (convI_eq_one_iff hUe _).not.mpr (not_mem_centralizer_conjClosure hR htH hv htr htC)

theorem zpow_eq_one_or_eq {M : Type*} [Group M] {a : M} (ha : a ^ 2 = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_ofNat, ha, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, ha, one_zpow, one_mul]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
