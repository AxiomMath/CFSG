module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem ringEquiv_eq_one_of_card_eq_prime {K : Type*} [Field K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp le_rfl (by rw [pow_one, hK])
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hp.ne_zero)
  set f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hbij : Function.Bijective f :=
    f.injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  have hσf : σ.toRingHom.comp f = f := RingHom.ext_zmod _ _
  refine RingEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hbij.2 x
  exact DFunLike.congr_fun hσf y

@[expose] def centralizerMulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer {x} : Subgroup G) ≃* (Subgroup.centralizer {e x} : Subgroup H) :=
  (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
        MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [← map_mul, ← map_mul, hz]
      · intro hy
        refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
        rw [map_mul, map_mul, e.apply_symm_apply, hy]))

theorem prime_field_G2_order_p_centralizer_local_cores_trivial {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (K : Type) [Field K] (hK : Nat.card K = p) :
    (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range = ⊤ ∧
    ∀ B : Subgroup (MulAut (adjointGroup .G2 K)),
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B →
      ∀ a : B, orderOf a = p →
        CFSG.IsCharacteristicP p (Subgroup.centralizer {a} : Subgroup B) ∧
        CFSG.RankThree.LocalRank.aschbacherSolvableCore p
          (Subgroup.centralizer {a} : Subgroup B) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hp.ne_zero)
  have : CharP K p := finite_field_prime_power_characteristic hp le_rfl (by rw [pow_one, hK])
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  set C := adjointGroup Tag.G2 K
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp
    (by omega) le_rfl K (by rw [pow_one, hK]) Tag.G2 (Or.inr ⟨rfl, by omega⟩)
  have hinner : (MulAut.conj : C →* MulAut C).range = ⊤ := by
    rw [eq_top_iff, ← hker]
    intro α _
    exact ringEquiv_eq_one_of_card_eq_prime hp hK (Θ α)
  refine ⟨hinner, fun B hB a ha => ?_⟩
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcen : c ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun g => by
      have := DFunLike.congr_fun hc g
      rw [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * c = c * g * c⁻¹ * c := by rw [this]
        _ = c * g := by group
    rw [hZ] at hcen
    exact hcen
  let ψ₀ : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩
  have hψ : Function.Bijective ψ₀ := by
    refine ⟨fun c d h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    obtain ⟨c, hc⟩ : (b : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range := by
      rw [hinner]
      exact Subgroup.mem_top _
    exact ⟨c, Subtype.ext hc⟩
  let ψ : C ≃* B := MulEquiv.ofBijective ψ₀ hψ
  set x := ψ.symm a with hx
  have hxp : orderOf x = p := by rw [hx, MulEquiv.orderOf_eq, ha]
  have hP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  have hP1 : Subgroup.zpowers x ≠ ⊥ := by
    intro h
    have h1 : x = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_zpowers x
    rw [h1, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  obtain ⟨hchar, -⟩ := RootWeightDatum.defining_characteristic_root_local_groups_component_free
    (RootWeightDatum.ordinary Tag.G2) p (Subgroup.zpowers x) hP hP1
    (Subgroup.centralizer (Subgroup.zpowers x : Set C)) (Or.inr rfl)
  have hcent : Subgroup.centralizer (Subgroup.zpowers x : Set C) = Subgroup.centralizer {x} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcharB : CFSG.IsCharacteristicP p (Subgroup.centralizer {a} : Subgroup B) := by
    have e := (MulEquiv.subgroupCongr hcent).trans (centralizerMulEquiv ψ x)
    rw [hx, MulEquiv.apply_symm_apply] at e
    exact isCharacteristicP_of_mulEquiv e hchar
  obtain ⟨-, _, hθp, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := (Subgroup.centralizer {a} : Subgroup B)) hp
  refine ⟨hcharB, (CFSG.characteristic_p_normal_prime_complement_trivial hcharB).1 _ ?_ hθp⟩
  exact Subgroup.normal_of_characteristic _

end CFSG.RankThree.Chevalley
