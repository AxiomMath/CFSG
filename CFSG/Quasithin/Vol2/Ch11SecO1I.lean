module

public import CFSG.Quasithin.Vol2.Ch11SecO1H
public import CFSG.Quasithin.Vol2.Ch11SecO1C
public import CFSG.Quasithin.Vol2.Ch11SecO1G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.QuasithinUnique.Vol2Native (A312L.exists_finset_card_four)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem eq_fsuV_of_isVi_three (hS : SecD.NatSetting11 G T L I n) (hk : KindSL3 L (fsuV T I) n)
    {V₃ : Subgroup G} (hV₃ : IsVi T L I n 3 V₃) : V₃ = fsuV T I := by
  obtain ⟨⟨-, hV₃V, -, hidx, -⟩, -⟩ := hV₃
  rw [hS.cV, Subgroup.relIndex_bot_left] at hidx
  refine Subgroup.eq_of_le_of_card_ge hV₃V ?_
  rw [(SecD.cardVFact_holds G T L I n hS).1 hk, hidx, mul_comm]

theorem natV3_sl3 (hS : SecD.NatSetting11 G T L I n) (hk : KindSL3 L (fsuV T I) n)
    {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) :
    V₁ ≤ V₃ ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (LOf L V₁) V₃ V₁ (CFSG.pCore 2 ↥(LOf L V₁))
        (Assembly.LowTwoRank.StatedSL 2 F) := by
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain rfl := eq_fsuV_of_isVi_three hS hk hV₃
  refine ⟨SecA.IsVi.le_fsuV hV₁, ?_⟩
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hV₁f, hL₁⟩ := exists_adapted_sl3 hS hk hV₁
  have hK4 := A312L.exists_finset_card_four (four_le_card hn hK)
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hLV : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := hL₁L.trans hS.le_normalizer
  have hC : IsPGroup 2 ↥(LOf L V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    (isPGroup_inf_centralizer hS).to_le (inf_le_inf_right _ hL₁L)
  obtain ⟨θ, hθs, hθk, hθ⟩ := exists_levi_of_autOn hLV hC (psiW_injective hf g) hL₁
  have hlk : IsPGroup 2 ↥(leviHom K).ker := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      have := sq_eq_one_of_mem_rad1 (K := K) ⟨x, x.2, rfl⟩
      simpa using this))⟩
  set gi : Matrix (Fin 3) (Fin 3) K :=
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hgi
  let β : ↥(fsuV T I) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd fun i : Fin 2 => (gi *ᵥ f v) i.succ
      map_one' := by
        rw [hf.map_one, Matrix.mulVec_zero]
        rfl
      map_mul' := fun u v => by
        rw [hf.map_mul, Matrix.mulVec_add]
        rfl }
  have hβ : ∀ v, Multiplicative.toAdd (β v) = fun i : Fin 2 => (gi *ᵥ f v) i.succ := fun _ => rfl
  let : Fintype K := Fintype.ofFinite K
  refine ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK],
    isNaturalSection_of_levi hK4 hLV ((leviHom K).comp θ) (leviHom_surjective.comp hθs)
      (by rw [← MonoidHom.comap_ker]; exact hlk.comap_of_ker_isPGroup θ hθk) β ?_ ?_ ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, y 0, y 1])
    refine ⟨v, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, hv, hgi, ginv_g_mulVec]
    funext i
    fin_cases i <;> rfl
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hV₁f v, mem_gmap, ← stdLine_eq_flagSpace,
      mem_stdLine, ← Multiplicative.toAdd.injective.eq_iff, hβ, toAdd_one]
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h1, h2⟩
      funext i
      fin_cases i
      · exact h1
      · exact h2
  · intro a u v huv
    have hv : v = conjV (fsuV T I) a (hLV a.2) u :=
      Subtype.ext (by rw [conjV_apply_coe, huv, InvMemClass.coe_inv])
    rw [hβ, hβ, hv, ← hθ, psiW_apply, hf.act3, hgi, conj_mulVec,
      tail_mulVec_of_mem_stabE0 (θ a).2, MonoidHom.comp_apply, leviHom_coe]

end CFSG.Quasithin.Vol2.Ch11.SecO1
