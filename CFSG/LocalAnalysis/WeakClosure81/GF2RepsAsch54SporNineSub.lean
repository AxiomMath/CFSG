module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporNine

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem not_hasCompFactor_isCalL0_of_dvd_of_forall_mem_pow_nine (hO : LieOrderFormulasInput)
    {k N : ℕ} (h : calL0NineCheck k N = true) {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    (h9 : ∀ g ∈ A, g ^ 9 = 1 → g ^ 3 = 1) (hA : Nat.card A ∣ N) :
    ¬ HasCompFactor A IsCalL0 := by
  have h' := not_hasCompFactor_isCalL0_of_dvd_of_pow_nine hO h (Y := A) (A := ⊤)
    (fun g hg => Subtype.ext (by
      rw [Subgroup.coe_pow, h9 g g.2 (by rw [← Subgroup.coe_pow, hg, Subgroup.coe_one]),
        Subgroup.coe_one]))
    (by rwa [Subgroup.card_top])
  rwa [← hasCompFactor_map_of_injective A.subtype A.subtype_injective ⊤,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h'

theorem pow_three_eq_one_of_pow_nine_of_ker {G H : Type} [Group G] [Group H] (f : G →* H)
    (hK : Nat.Coprime (Nat.card f.ker) 3) (hH : ∀ h : H, h ^ 9 = 1 → h ^ 3 = 1) (g : G)
    (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  have hk : g ^ 3 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hH _ (by rw [← map_pow, hg, map_one])
  have h3 : (⟨g ^ 3, hk⟩ : f.ker) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul]; exact hg)
  have h1 := pow_gcd_eq_one.2 ⟨(pow_card_eq_one' : (⟨g ^ 3, hk⟩ : f.ker) ^ Nat.card f.ker = 1), h3⟩
  rw [hK, pow_one] at h1
  exact congrArg Subtype.val h1

theorem pow_three_eq_one_of_pow_nine_prod {A B : Type} [Group A] [Group B]
    (hA : ∀ a : A, a ^ 9 = 1 → a ^ 3 = 1) (hB : ∀ b : B, b ^ 9 = 1 → b ^ 3 = 1) (p : A × B)
    (hp : p ^ 9 = 1) : p ^ 3 = 1 :=
  Prod.ext (by rw [Prod.pow_fst, Prod.fst_one]; exact hA _ (by rw [← Prod.pow_fst, hp, Prod.fst_one]))
    (by rw [Prod.pow_snd, Prod.snd_one]; exact hB _ (by rw [← Prod.pow_snd, hp, Prod.snd_one]))

theorem pow_three_eq_one_of_pow_nine_M24
    (g : NativeSporadic.M24) (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx, hy, -, hzx, hzy, hQ, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  set Q := Subgroup.closure ({x, y} : Set NativeSporadic.M24)
  have hidx : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index Q
    rw [hQ, CFSG.Sporadic.Mathieu.card_M24] at h1
    omega
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_eq_one_of_index Q hQ hidx
    (fun q hq =>
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
        hx hy hzx hzy hq) (n := 2) (by rw [show 3 ^ 2 = 9 by norm_num]; exact hg)

end CFSG.LocalAnalysis.WeakClosure81

end
