module

public import CFSG.Quasithin.H13.VolIAltCoverG2Dual
public import CFSG.Quasithin.H13.VolIAltCoverG2Field
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open Matrix Subgroup
open scoped commutatorElement

theorem g2Derived_two_eq
    : ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ = subG2 := by
  rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact g2Two_commutator_eq

@[expose] def g2TwoEquiv
    : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≃* ↥subG2 :=
  MulEquiv.subgroupCongr g2Derived_two_eq

theorem muK_g2TwoEquiv
    (γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) (w : Ix3 → ZMod 2) :
    muK (g2TwoEquiv γ) w = g2Act (inclusion (g2Derived_le (ZMod 2)) γ) w := rfl

theorem g2Derived_two_le : ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≤ quasithinG2 (ZMod 2) :=
  (g2Derived_le (ZMod 2)).trans (G11.P3G2.quasithinG2_eq_cayleyGroup (K := ZMod 2)).symm.le

theorem coverG2_two_bound
    : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ C : ModelCover (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) W,
      Nat.card C.β.ker ≤ 2 := by
  intro W _ _ hW2 C
  let ρ' : ↥subG2 →* MulAut W := C.ρ.comp g2TwoEquiv.symm.toMonoidHom
  let β' : W →* Multiplicative (Ix3 → ZMod 2) := (zornSecEquiv _).toMonoidHom.comp C.β
  have hβe : ∀ g w, Multiplicative.toAdd (β' (ρ' g w)) =
      muQ g *ᵥ Multiplicative.toAdd (β' w) := by
    intro g w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (C.β w)
    have hm0 : (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).act
        (g2TwoEquiv.symm g) m.1 ∈
          (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).sec :=
      zornAct_mem_O0 _ g2Derived_two_le _ m.2
    have h1 := C.equiv (g2TwoEquiv.symm g) w m hm0 hm.symm
    have h2 : Multiplicative.toAdd (β' w) = zP (Multiplicative.toAdd m.1) := by
      show Multiplicative.toAdd (zornSecEquiv _ (C.β w)) = _
      rw [← hm]
      rfl
    have h3 : Multiplicative.toAdd (β' (ρ' g w)) = zP (((g2TwoEquiv.symm g :
        ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
          quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))
            (Multiplicative.toAdd m.1)) := by
      show Multiplicative.toAdd (zornSecEquiv _ (C.β (C.ρ (g2TwoEquiv.symm g) w))) = _
      rw [h1]
      rfl
    rw [h3, h2, zP_act _ m.2, ← muK_g2TwoEquiv, MulEquiv.apply_symm_apply, muK_eq_mulVec]
  have hβk : ∀ w, β' w = 1 ↔ w ∈ C.β.ker := fun w => by
    show zornSecEquiv _ (C.β w) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MonoidHom.mem_ker]
  have hgen : ∀ w : W, w ∈ closure {x | ∃ g v, x = ρ' g v * v⁻¹} := by
    intro w
    refine closure_mono ?_ (C.gen w)
    rintro _ ⟨γ, v, rfl⟩
    refine ⟨g2TwoEquiv γ, v, ?_⟩
    have h := MulEquiv.symm_apply_apply g2TwoEquiv γ
    exact (congrArg (fun γ' => C.ρ γ' v * v⁻¹) h).symm
  exact card_le_two_of_card_Z1A (μ := muQ) (θ := MulEquiv.refl ↥subG2) (ν := muKdual)
    (fun g x => muKdual_eq g x) card_Z1A_muKdual hW2 ((zornSecEquiv _).surjective.comp C.surj)
    hβk (fun g z hz => C.fix _ z (MonoidHom.mem_ker.1 hz)) hβe hgen

@[expose] def zornSecAct :
    ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ →* MulAut ↥(zornO0 (ZMod 2)) where
  toFun γ :=
    { toFun := fun m => ⟨zornAct _ γ m.1, zornAct_mem_O0 _ g2Derived_two_le γ m.2⟩
      invFun := fun m => ⟨zornAct _ γ⁻¹ m.1, zornAct_mem_O0 _ g2Derived_two_le γ⁻¹ m.2⟩
      left_inv := fun m => Subtype.ext (by
        show zornAct _ γ⁻¹ (zornAct _ γ m.1) = m.1
        rw [← zornAct_mul_act, inv_mul_cancel, zornAct_one])
      right_inv := fun m => Subtype.ext (by
        show zornAct _ γ (zornAct _ γ⁻¹ m.1) = m.1
        rw [← zornAct_mul_act, mul_inv_cancel, zornAct_one])
      map_mul' := fun x y => Subtype.ext (zornAct_mul _ γ x.1 y.1) }
  map_one' := MulEquiv.ext fun m => Subtype.ext (zornAct_one _ m.1)
  map_mul' γ δ := MulEquiv.ext fun m => Subtype.ext (zornAct_mul_act _ γ δ m.1)

theorem zornSecAct_ker (γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
    (m : ↥(zornO0 (ZMod 2))) (hm : m.1 ∈ zornR (ZMod 2)) : zornSecAct γ m = m := by
  obtain ⟨c, hc⟩ := hm
  apply Subtype.ext
  show Multiplicative.ofAdd ((γ : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))
    (Multiplicative.toAdd m.1)) = m.1
  rw [hc, (mem_quasithinG2_isZornAuto (g2Derived_two_le γ.2)).map_smul_one c, ← hc]
  rfl

theorem card_zornR_two :
    Nat.card ↥((zornR (ZMod 2)).subgroupOf (zornO0 (ZMod 2))) = 2 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe zornR_le_zornO0).toEquiv]
  have e : ZMod 2 ≃ ↥(zornR (ZMod 2)) :=
    { toFun := fun c => ⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩
      invFun := fun x => (Multiplicative.toAdd x.1).1
      left_inv := fun _ => rfl
      right_inv := fun x => by
        obtain ⟨y, c, hc⟩ := x
        apply Subtype.ext
        show Multiplicative.ofAdd ((Multiplicative.toAdd y).1, 0, 0, (Multiplicative.toAdd y).1) = y
        rw [hc]
        exact Multiplicative.toAdd.injective hc.symm }
  rw [← Nat.card_congr e, Nat.card_zmod]

theorem zornO0_sq (m : ↥(zornO0 (ZMod 2))) : m ^ 2 = 1 := by
  have h : ∀ x : Multiplicative (quasithinZorn (ZMod 2)), x ^ 2 = 1 := by decide +kernel
  exact Subtype.ext (h m.1)

@[expose] def liftsQ : Finset (Fin 8 → ZMod 2) := Finset.univ.filter fun y =>
  y 0 = 0 ∧ y 1 = 0 ∧ y 4 = 0 ∧ y 7 = 0

theorem o0_comm : ∀ c : Fin 8 → ZMod 2, c 0 + c 7 = 0 → ∃ y ∈ liftsQ, ∃ y' ∈ liftsQ,
    c = (matA2 *ᵥ y + y) + (matB2 *ᵥ y' + y') := by
  decide +kernel

theorem zornCoord_gensK
    (i : Fin 2) (y : Fin 8 → ZMod 2) :
    zornCoord (((g2TwoEquiv.symm (gensK i) : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) (zornCoord.symm y)) =
      ![matA2, matB2] i *ᵥ y := by
  have h := zornCoord_cg (Subgroup.inclusion subG2_le (gensK i)) (zornCoord.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  refine h.trans ?_
  fin_cases i
  · exact congrArg (· *ᵥ y) cmat_g2a
  · exact congrArg (· *ᵥ y) cmat_g2b

theorem zornO0_gen
    (m : ↥(zornO0 (ZMod 2))) :
    m ∈ Subgroup.closure {x | ∃ γ y, x = zornSecAct γ y * y⁻¹} := by
  have hx : (Multiplicative.toAdd m.1).1 + (Multiplicative.toAdd m.1).2.2.2 = 0 := m.2
  obtain ⟨y, hy, y', hy', hc⟩ := o0_comm (zornCoord (Multiplicative.toAdd m.1)) hx
  have hl : ∀ z ∈ liftsQ, (zornCoord.symm z).1 + (zornCoord.symm z).2.2.2 = 0 := by
    intro z hz
    have h0 := (Finset.mem_filter.1 hz).2
    have e0 : (zornCoord.symm z).1 = z 0 := congrFun (LinearEquiv.apply_symm_apply zornCoord z) 0
    have e7 : (zornCoord.symm z).2.2.2 = z 7 :=
      congrFun (LinearEquiv.apply_symm_apply zornCoord z) 7
    rw [e0, e7, h0.1, h0.2.2.2, add_zero]
  let ya : ↥(zornO0 (ZMod 2)) := ⟨Multiplicative.ofAdd (zornCoord.symm y), hl y hy⟩
  let yb : ↥(zornO0 (ZMod 2)) := ⟨Multiplicative.ofAdd (zornCoord.symm y'), hl y' hy'⟩
  have e : m = zornSecAct (g2TwoEquiv.symm (gensK 0)) ya * ya⁻¹ *
      (zornSecAct (g2TwoEquiv.symm (gensK 1)) yb * yb⁻¹) := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply zornCoord.injective
    show zornCoord (Multiplicative.toAdd m.1) =
      zornCoord (((g2TwoEquiv.symm (gensK 0) : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
          quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) (zornCoord.symm y) +
        -zornCoord.symm y +
        (((g2TwoEquiv.symm (gensK 1) : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
          quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) (zornCoord.symm y') +
        -zornCoord.symm y'))
    have hneg : ∀ x : quasithinZorn (ZMod 2), -x = x := by decide +kernel
    rw [hneg, hneg, map_add, map_add, map_add, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, zornCoord_gensK, zornCoord_gensK, hc]
    rfl
  rw [e]
  exact mul_mem (Subgroup.subset_closure ⟨_, ya, rfl⟩) (Subgroup.subset_closure ⟨_, yb, rfl⟩)

theorem card_zornQSec {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec = 64 := by
  rw [Nat.card_congr (zornSecEquiv (F := K) ⁅quasithinG2 K, quasithinG2 K⁆).toEquiv]
  show Nat.card (Ix3 → K) = 64
  rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  rfl

theorem g2NaturalCover_holds :
    H13.G2NaturalCover := by
  intro V _ _ hV2 H Z hZ hcomm h
  obtain ⟨K, _, _, hK, hR⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hKf, pow_one])
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hKf).symm
  obtain ⟨C, π, hπs, hρ, hβk⟩ := ModelCover.exists_of_realizes hZ hcomm hR
  have hker : C.β.ker = Z := by
    ext v
    exact MonoidHom.mem_ker.trans (hβk v)
  have hle : Nat.card Z ≤ 2 := by
    rw [← hker, ← C.mapZorn_ker e]
    exact coverG2_two_bound V hV2 (C.mapZorn e)
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rcases (by omega : Nat.card Z = 1 ∨ Nat.card Z = 2) with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq Z h1)
  · right
    have hV : Nat.card V = 2 ^ 7 := by
      rw [C.card_eq, hker, h2, card_zornQSec hK2]
      norm_num
    refine ⟨h2, hV, ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ?_⟩
    have : Finite ↥(FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).sec :=
      Finite.of_injective (Subtype.val : ↥(zornO0 (ZMod 2)) → _) Subtype.val_injective
    obtain ⟨Φ, hΦ⟩ := ModelCover.exists_mulEquiv
      (D := FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) zornSecAct
      (fun _ _ => rfl) zornSecAct_ker card_zornR_two zornO0_gen zornO0_sq coverG2_two_bound hV2
      (C.mapZorn e) (by rw [C.mapZorn_ker, hker, h2])
    exact realizes_of_mulEquiv
      (E := zornO0Model ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) rfl
      (π.comp (g2DerivedFieldEquiv e).symm.toMonoidHom)
      (hπs.comp (g2DerivedFieldEquiv e).symm.surjective) Φ fun γ v =>
        (congrArg (fun w => (Φ w).val) (congrArg (fun f : MulAut V => f v) (hρ _))).symm.trans
          (congrArg Subtype.val (hΦ γ v))

end CFSG.Quasithin.H13.VolI
