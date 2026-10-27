module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeKG
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffCore
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffCover
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open

theorem ggNbrG2Off_recipe
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h6 : 6 ∣ n) :
    GGTorusNoLineFieldCompOff 3 2 (TableBExc.RecipeGroup Tag.G2 K) (TableBExc.RecipeID Tag.G2 K)
      (CFSG.Assembly.LargeEvenChevFieldImage Tag.G2.cartan K
        (CFSG.Assembly.LargeEvenChevH Tag.G2.cartan K false)) (ggG2SL3Card n) := by
  intro L' _ _ ψ hψ hker hperf A hA _ h27 _ _
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := K)
    simp [hK] at this
  have h6n : 6 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h6
  have h5 : 5 ≤ Nat.card K := by
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  set e₀ := TableBExc.recipeEquiv Tag.G2 K with he₀
  let ψ' : L' →* adjointGroup Tag.G2 K := e₀.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := e₀.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e₀.map_eq_one_iff.mp hx)
  have hinj' : Function.Injective ψ' := ggNbrG2Off_cover_injective h5 ψ' hψ' hker' hperf
  have hinj : Function.Injective ψ := fun a b h => hinj' (by simp [ψ', h])
  let e : L' ≃* adjointGroup Tag.G2 K := MulEquiv.ofBijective ψ' ⟨hinj', hψ'⟩
  obtain ⟨W, hW1, hW2⟩ := ggNbrG2Off_weyl_set hK h6 e A hA (by norm_num at h27; exact h27)
  have hI := TableBExc.idImage_subset_inn_of_top Tag.G2 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
  refine ⟨W, hW1, fun _ a₀ ha₀ hne hI₀ _ hN => ?_⟩
  obtain ⟨φ, hφ, hφψ⟩ := hI₀
  obtain ⟨r, hr⟩ := hI hφ
  obtain ⟨l₀, rfl⟩ := hψ r
  have hψa : ∀ l, ψ (a₀ l) = ψ l₀ * ψ l * (ψ l₀)⁻¹ := fun l => by
    rw [← hφψ l, ← hr, MulAut.conj_apply]
  have hinner : a₀ ∈ (MulAut.conj : L' →* MulAut L').range :=
    ⟨l₀, MulEquiv.ext fun l => hinj (by rw [hψa l, MulAut.conj_apply, map_mul, map_mul, map_inv])⟩
  exact hW2 a₀ ha₀ hne hinner (by rw [hK]; exact hN)

theorem ggNbrKGFieldG2ThreeOff_holds :
    GGNbrKGFieldG2ThreeOff := by
  intro lab _ ht h6
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h6
  subst ht
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  exact recipeChevalley_and
    (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineFieldCompOff 3 2 R I F (ggG2SL3Card n))
    (fun K _ _ hK _ _ => ggNbrG2Off_recipe hK h6) hQ

theorem ggNbrKGFieldG2Three_holds :
    GGNbrKGFieldG2Three :=
  ggNbrKGFieldG2Three_of_off ggNbrKGFieldG2ThreeOff_holds

end CFSG.StandardType

end
