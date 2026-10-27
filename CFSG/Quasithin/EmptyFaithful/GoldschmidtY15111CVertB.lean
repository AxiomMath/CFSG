module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CVertA
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Free

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

variable {Z : Type} [Group Z]

theorem card_mod_three_inf_normal [Finite Z] {V N : Subgroup Z} (hV : V.Normal) (hN : N.Normal)
    {c : Z} (hc3 : c ^ 3 = 1) (hfree : ∀ v ∈ V, c * v * c⁻¹ = v → v = 1) :
    Nat.card ↥(V ⊓ N) % 3 = 1 :=
  have : (V ⊓ N).Normal := by
    have := hV
    have := hN
    infer_instance
  card_mod_three_of_free (le_normalizer_of_normal this (Subgroup.zpowers c)
    (Subgroup.mem_zpowers c)) hc3 fun w hw hcw => hfree w hw.1 hcw

theorem noVc_of_autM12_left [Finite Z] (hQ : Nat.card ↥(Open.pCore 2 Z) = 64)
    (hext : F6.IsExtensionWith Z (DihedralGroup 6)
      (fun N => F6.IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2))) :
    NoVc Z := by
  intro V c hVn hV16 hVe hc3 hfree
  obtain ⟨φ, -, hcp⟩ := hext
  have hNn : φ.ker.Normal := φ.normal_ker
  have hN32 : Nat.card φ.ker = 32 := card_centralProduct hcp
  have hVle := le_pCore_of_card_sixteen hVn hV16
  have hNle : φ.ker ≤ Open.pCore 2 Z := CFSG.LieType.BorelTits.le_pCore 2 hNn
    (IsPGroup.of_card (n := 5) (by rw [hN32]; norm_num))
  have hprod := card_sup_mul_card_inf (A := V) (B := φ.ker) (le_normalizer_of_normal hNn V)
  have hsup : Nat.card ↥(V ⊔ φ.ker) ≤ 64 := hQ ▸ Subgroup.card_le_of_le (sup_le hVle hNle)
  rw [hV16, hN32] at hprod
  have hge : 8 ≤ Nat.card ↥(V ⊓ φ.ker) := by
    by_contra hlt
    have := Nat.mul_le_mul hsup (Nat.le_of_lt_succ (not_le.mp hlt))
    omega
  have hsq : ∀ w ∈ (V ⊓ φ.ker).subgroupOf φ.ker, w * w = 1 := fun w hw => by
    have := mul_self_eq_one_of_isElemAbelian hVe w (Subgroup.mem_inf.mp
      (Subgroup.mem_subgroupOf.mp hw)).1
    exact Subtype.ext (by simpa using this)
  have hle := card_le_eight_of_centralProduct hcp ((V ⊓ φ.ker).subgroupOf φ.ker) hsq
  have hcard : Nat.card ↥((V ⊓ φ.ker).subgroupOf φ.ker) = Nat.card ↥(V ⊓ φ.ker) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hmod := card_mod_three_inf_normal hVn hNn hc3 hfree
  omega

end Y15111

end CFSG.Quasithin
