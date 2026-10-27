module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBWeylImage
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeModel

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExc.Three
  TableBExcTwoFusion TableBExcTwoTB TableBExc.E6Three


theorem exists_conj_torusGroup_three_of_model {τ : Tag} {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ K 3) = 3 ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {n : ℕ} {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1} (F : Model π hπ →* WeylGroup τ)
    (hidx : ¬ 3 ∣ (weylX τ K F.range).index)
    (hKey : ∀ A : Subgroup (WeylGroup τ), A ≤ F.range → IsElemAbelian 3 A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} <
          3 ^ (τ.rank - 1) ∨
        ∃ i, A = Subgroup.zpowers (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))))
    (hT : ∀ {ζ : Kˣ}, orderOf ζ = 3 → ∀ (i : Fin n) {E : Subgroup (ModGL τ K)},
      IsElemAbelian 3 E →
      E ≤ xHat τ K (Subgroup.zpowers (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))))) →
        ∃ y ∈ adjointGroup τ K, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit τ c)
    {A : Subgroup (ModGL τ K)} (hA : A ≤ adjointGroup τ K)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hpow : ∀ x ∈ A, x ^ 3 = 1)
    (hcard : 3 ^ (τ.rank - 1) ≤ Nat.card A) :
    ∃ g ∈ adjointGroup τ K, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ K := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  set E := A.subgroupOf (adjointGroup τ K) with hEdef
  have hE : IsElemAbelian 3 E :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩,
      fun x hx => Subtype.ext ((Subgroup.coe_pow _ x 3).trans (hpow _ hx))⟩
  have hEcard : Nat.card E = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  obtain ⟨k, hk⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  set E' := E.map (MulAut.conj k).toMonoidHom with hE'def
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE _
  have hcard' : Nat.card E' = Nat.card A := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj k).injective, hEcard]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨hAS, hAe, hEeq, hfix, hker⟩ :=
    weylImage_spec Nat.prime_three hdet hV hsymm hζo hζ hE' hk
  obtain ⟨y, hyC, hy⟩ : ∃ y ∈ adjointGroup τ K, ∀ e ∈ E',
      ∃ c, y * ((e : adjointGroup τ K) : ModGL τ K) * y⁻¹ = rootDiagUnit τ c := by
    by_cases hbot : (weylImageHom E' hk).range = ⊥
    · refine ⟨1, one_mem _, fun e he => ?_⟩
      have h1 : weylImageHom E' hk ⟨e, he⟩ = 1 := by
        have hmem : weylImageHom E' hk ⟨e, he⟩ ∈ (weylImageHom E' hk).range := ⟨_, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hker ⟨e, he⟩ h1).1
      exact ⟨c, by rw [one_mul, inv_one, mul_one]; exact hc⟩
    rcases hKey _ hAS hAe hbot with hlt | ⟨i, hi⟩
    · exfalso
      have hinj : Nat.card (torusSet hζ E') ≤ Nat.card {x : Fin τ.rank → ZMod 3 //
          ∀ a ∈ (weylImageHom E' hk).range, torusAct τ 3 a x = x} :=
        Nat.card_le_card_of_injective (fun x => ⟨x.1, fun a ha => hfix x.1 x.2 a ha⟩)
          fun a b hab => Subtype.ext (Subtype.mk.inj hab)
      have hlt' : Nat.card A < Nat.card A :=
        calc Nat.card A = Nat.card E' := hcard'.symm
          _ = _ := hEeq
          _ ≤ _ := Nat.mul_le_mul_left _ hinj
          _ < 3 ^ (τ.rank - 1) := hlt
          _ ≤ Nat.card A := hcard
      exact lt_irrefl _ hlt'
    · have hEX : E'.map (adjointGroup τ K).subtype ≤ xHat τ K
          (Subgroup.zpowers (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))))) := by
        rintro _ ⟨e, he, rfl⟩
        refine mem_weylX_iff_mem_xHat.mp (mem_weylX.mpr ⟨(mem_weylX.mp (hk he)).1, ?_⟩)
        rw [← hi]
        exact ⟨⟨e, he⟩, rfl⟩
      obtain ⟨y, hyC, hy⟩ := hT hζo i (TableB.isElemAbelian_map hE' _) hEX
      exact ⟨y, hyC, fun e he => hy _ ⟨e, he, rfl⟩⟩
  refine ⟨(y * (k : ModGL τ K))⁻¹, inv_mem (mul_mem hyC k.2), fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hy ((MulAut.conj k).toMonoidHom ⟨x, hA hx⟩)
    ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have heq : (y * (k : ModGL τ K))⁻¹⁻¹ * x * (y * (k : ModGL τ K))⁻¹ = rootDiagUnit τ c := by
    rw [← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmem : (y * (k : ModGL τ K))⁻¹⁻¹ * x * (y * (k : ModGL τ K))⁻¹ ∈ adjointGroup τ K :=
    mul_mem (mul_mem (inv_mem (inv_mem (mul_mem hyC k.2))) (hA hx)) (inv_mem (mul_mem hyC k.2))
  rw [heq] at hmem ⊢
  exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup c hmem

end CFSG.StandardType.ExcFramesHalf

end
