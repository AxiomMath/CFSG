module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
public import CFSG.Goldschmidt75.Sig3Four
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open CFSG.Wreathed
open CFSG.GH74.GLS.IVK

variable {Q : Type} [Group Q] [Finite Q]


theorem exists_wreath_iso {L : Subgroup Q} [L.Normal] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : (LieModel ↥L .PSL 3 p 1 ∧ p % 4 = 1) ∨ (LieModel ↥L .PSU 3 p 1 ∧ p % 4 = 3))
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥(T ⊓ L) ≃* Wreath (2 ^ n)) := by
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp5
    norm_num at hp5
  have hNsub : (L.subgroupOf (⊤ : Subgroup Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := (⊤ : Subgroup Q)) (N := L) (by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : L.Normal)])
  have hSyl : IsSylowIn 2 (T ⊓ L) L := hT.inf_normal le_top hNsub
  let S : Subgroup Q := T ⊓ L
  have hSylS : IsSylowIn 2 S L := hSyl
  let Ssyl : Sylow 2 ↥L := hSylS.toSylow
  rcases hL with ⟨hPL, hq⟩ | ⟨hPU, hq⟩
  · have hst : CFSG.Open.StatedClassicalModel ↥L .PSL 3 p 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hPL (by decide)
    have hI : IsLnEps 3 ↥L 1 (p ^ 1) := by
      obtain ⟨-, K, hK, hFin, hcard, ⟨eK⟩⟩ := hst
      exact Or.inl ⟨rfl, K, hK, hFin, by simpa using hcard, ⟨eK⟩⟩
    obtain ⟨n, hn, ⟨eL⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_wr hp hp2 hI (by simpa using hq)
        (by simpa using hp.one_lt) Ssyl
    exact ⟨n, hn, ⟨(Subgroup.subgroupOfEquivOfLe (show S ≤ L from inf_le_right)).symm.trans eL⟩⟩
  · have hst : CFSG.Open.StatedClassicalModel ↥L .PSU 3 p 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hPU (by decide)
    have hI : IsLnEps 3 ↥L (-1) (p ^ 1) := by
      obtain ⟨-, K, hK, hFin, hcard, ⟨eK⟩⟩ := hst
      exact Or.inr ⟨rfl, K, hK, hFin, by simpa using hcard, ⟨eK⟩⟩
    obtain ⟨n, hn, ⟨eL⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr hp hp2 hI (by simpa using hq) Ssyl
    exact ⟨n, hn, ⟨(Subgroup.subgroupOfEquivOfLe (show S ≤ L from inf_le_right)).symm.trans eL⟩⟩

theorem mem_baseOmega_map_of_mem_center {n : ℕ} (hn : 1 ≤ n) {z : Wreath (2 ^ n)}
    (hzc : z ∈ Subgroup.center (Wreath (2 ^ n))) (hz2 : z ^ 2 = 1) :
    z ∈ (baseOmega (2 ^ n)).map (baseSubgroup (2 ^ n)).subtype := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  rw [center_eq_diagonal_range (2 ^ n) hm] at hzc
  obtain ⟨c, hc⟩ := hzc
  let a : ZMod (2 ^ n) := Multiplicative.toAdd c
  have hzc' : z = element (2 ^ n) a a 0 := by
    rw [← hc]
    rfl
  have hsq : (element (2 ^ n) a a 0) ^ 2 = 1 := by
    rw [← hzc']
    exact hz2
  let b : baseSubgroup (2 ^ n) :=
    ⟨element (2 ^ n) a a 0, (element_mem_base (2 ^ n) a a 0).mpr rfl⟩
  refine Subgroup.mem_map.mpr ⟨b, ?_, ?_⟩
  · rw [mem_baseOmega]
    apply Subtype.ext
    exact hsq
  · exact hzc'.symm

theorem swap_not_centralizes_baseOmega_map {n : ℕ} (hn : 1 ≤ n) :
    ∃ w ∈ (baseOmega (2 ^ n)).map (baseSubgroup (2 ^ n)).subtype,
      element (2 ^ n) 0 0 1 * w * (element (2 ^ n) 0 0 1)⁻¹ ≠ w := by
  let t : ZMod (2 ^ n) := (2 ^ (n - 1) : ℕ)
  have ht0 : t ≠ 0 := by
    intro h
    have hdvd : 2 ^ n ∣ 2 ^ (n - 1) := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hle : n ≤ n - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  have h2t : (2 : ZMod (2 ^ n)) * t = 0 := by
    dsimp only [t]
    rw [show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_num]
    rw [← Nat.cast_mul, twice_half_two_pow n hn]
    exact ZMod.natCast_self _
  let b : baseSubgroup (2 ^ n) :=
    ⟨element (2 ^ n) t 0 0, (element_mem_base (2 ^ n) t 0 0).mpr rfl⟩
  have hb : b ∈ baseOmega (2 ^ n) := by
    rw [mem_baseOmega]
    apply Subtype.ext
    have hsq : (element (2 ^ n) t 0 0) ^ 2 = 1 := by
      rw [element_base_pow]
      have h2t' : (2 : ℕ) • t = 0 := by
        rw [nsmul_eq_mul]
        exact h2t
      rw [h2t']
      simp
    simpa using hsq
  refine ⟨element (2 ^ n) t 0 0, Subgroup.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
  rw [conjugate_base_by_swap]
  intro h
  have h' := (element_eq_iff (2 ^ n) 0 t t 0 0 0).mp h
  exact ht0 h'.2.1


theorem exists_omega_base_and_swap {L : Subgroup Q} [L.Normal] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hL : (LieModel ↥L .PSL 3 p 1 ∧ p % 4 = 1) ∨ (LieModel ↥L .PSU 3 p 1 ∧ p % 4 = 3))
    {T : Subgroup Q} {z : Q} (hT : IsSylowIn 2 T ⊤) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ (W : Subgroup Q) (σ : Q), W ≤ T ⊓ L ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      z ∈ W ∧ z ∈ T ⊓ L ∧ T ≤ normalizer (W : Set Q) ∧ σ ∈ T ⊓ L ∧ σ ∉ W ∧
      orderOf σ = 2 ∧ σ * z = z * σ ∧ ¬ ∀ w ∈ W, σ * w * σ⁻¹ = w := by
  obtain ⟨n, hn2, ⟨e⟩⟩ := exists_wreath_iso hp hp5 hL hT
  have hn1 : 1 ≤ n := by omega
  have hzTmem : z ∈ T := by
    have hzpow : IsPGroup 2 (Subgroup.zpowers z : Subgroup Q) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz2, pow_one]
    have hzcent : T ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Q) : Set Q) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ((show Commute t z from hzT t ht).zpow_right k).symm
    let P : Subgroup Q := T ⊔ Subgroup.zpowers z
    have hsup : IsPGroup 2 P :=
      IsPGroup.to_sup_of_normal_right' (H := T) (K := Subgroup.zpowers z) hT.2.1 hzpow
        (hzcent.trans (Subgroup.centralizer_le_normalizer _))
    let Tq : Sylow 2 Q := hT.isPGroup.toSylow (by simpa using hT.not_dvd_relIndex)
    have hmax : P = T := Tq.is_maximal' hsup le_sup_left
    have hle : Subgroup.zpowers z ≤ T := by
      calc Subgroup.zpowers z ≤ T ⊔ Subgroup.zpowers z := le_sup_right
        _ = T := hmax
    exact hle (Subgroup.mem_zpowers z)
  let S : Subgroup Q := T ⊓ L
  have hzS : z ∈ S := ⟨hzTmem, hzL⟩
  let zS : ↥S := ⟨z, hzS⟩
  have hzS_center : zS ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    change (s : Q) * z = z * (s : Q)
    exact hzT (s : Q) s.2.1
  let zm : Wreath (2 ^ n) := e zS
  have hzm_center : zm ∈ Subgroup.center (Wreath (2 ^ n)) := by
    have hmap : e zS ∈ (Subgroup.center ↥S).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hzS_center
    have hcenter : (Subgroup.center ↥S).map e.toMonoidHom =
        Subgroup.center (Wreath (2 ^ n)) := Subgroup.map_center_eq e
    rw [hcenter] at hmap
    exact hmap
  have hzm_order : orderOf zm = 2 := by
    dsimp only [zm]
    rw [MulEquiv.orderOf_eq e, Subgroup.orderOf_mk, hz2]
  have hzm_sq : zm ^ 2 = 1 := by
    simpa [hzm_order] using pow_orderOf_eq_one zm
  let Wmodel : Subgroup (Wreath (2 ^ n)) :=
    (baseOmega (2 ^ n)).map (baseSubgroup (2 ^ n)).subtype
  have hzm_Wmodel : zm ∈ Wmodel :=
    mem_baseOmega_map_of_mem_center hn1 hzm_center hzm_sq
  let Wsub : Subgroup ↥S := Wmodel.map e.symm.toMonoidHom
  let W : Subgroup Q := Wsub.map S.subtype
  have hmemWsub (y : ↥S) : y ∈ Wsub ↔ e y ∈ Wmodel := by
    constructor
    · intro hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      have h : e y = w := by
        rw [← hwy]
        exact e.apply_symm_apply w
      rwa [h]
    · intro hy
      exact Subgroup.mem_map.mpr ⟨e y, hy, e.symm_apply_apply y⟩
  have hWleS : W ≤ S := Subgroup.map_subtype_le Wsub
  have hWle : W ≤ T ⊓ L := by simpa [S, W] using hWleS
  have hWmodel_ab : IsMulCommutative Wmodel := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    obtain ⟨bx, -, hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨by_, -, hy⟩ := Subgroup.mem_map.mp y.2
    change (x : Wreath (2 ^ n)) * (y : Wreath (2 ^ n)) =
      (y : Wreath (2 ^ n)) * (x : Wreath (2 ^ n))
    rw [← hx, ← hy]
    exact congrArg (baseSubgroup (2 ^ n)).subtype ((base_is_abelian (2 ^ n)).1.1 bx by_)
  have hWmodel_sq : ∀ x ∈ Wmodel, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hb2 : b ^ 2 = 1 := (mem_baseOmega (2 ^ n) b).mp hb
    simpa using congrArg (baseSubgroup (2 ^ n)).subtype hb2
  have hWsub_ab : IsMulCommutative Wsub := Subgroup.map_isMulCommutative _ _
  have hWsub_sq : ∀ x ∈ Wsub, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy2 : y ^ 2 = 1 := hWmodel_sq y hy
    simpa using congrArg e.symm hy2
  have hWel : IsElemAbelian 2 W := by
    refine ⟨Subgroup.map_isMulCommutative _ _, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy2 : y ^ 2 = 1 := hWsub_sq y hy
    simpa using congrArg S.subtype hy2
  have hcardWmodel : Nat.card Wmodel = 4 := by
    dsimp only [Wmodel]
    rw [Subgroup.card_map_of_injective (baseSubgroup (2 ^ n)).subtype_injective,
      baseOmega_card n hn1]
  have hcardWsub : Nat.card Wsub = 4 := by
    dsimp only [Wsub]
    rw [Subgroup.card_map_of_injective e.symm.injective, hcardWmodel]
  have hcardW : Nat.card W = 4 := by
    dsimp only [W]
    rw [Subgroup.card_map_of_injective S.subtype_injective, hcardWsub]
  have hzWsub : zS ∈ Wsub := (hmemWsub zS).mpr hzm_Wmodel
  have hzW : z ∈ W := Subgroup.mem_map.mpr ⟨zS, hzWsub, rfl⟩
  have h2n : 2 < 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hn2
  have hWmodel_char : Wmodel.Characteristic := by
    have h1 : (baseSubgroup (2 ^ n)).Characteristic := base_characteristic (2 ^ n) h2n
    have h2 : (baseOmega (2 ^ n)).Characteristic := baseOmega_characteristic (2 ^ n)
    dsimp only [Wmodel]
    exact Subgroup.characteristic_of_characteristic_of_characteristic
      (H := baseSubgroup (2 ^ n)) (K := baseOmega (2 ^ n))
  have hWsub_char : Wsub.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have hmap1 : (Wsub.map φ.toMonoidHom).map e.toMonoidHom = Wmodel := by
      dsimp only [Wsub]
      rw [Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc]
      exact Subgroup.characteristic_iff_map_eq.mp hWmodel_char (e.symm.trans (φ.trans e))
    have hmap2 : Wsub.map e.toMonoidHom = Wmodel := by
      dsimp only [Wsub]
      rw [Subgroup.map_map]
      simp
    rw [hmap1, hmap2]
  have hTN : T ≤ Subgroup.normalizer (S : Set Q) := by
    refine (le_inf T.le_normalizer ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := L))
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : L.Normal)]
    exact le_top
  have hTW : T ≤ Subgroup.normalizer (W : Set Q) :=
    hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := S) (K := Wsub))
  let sm : Wreath (2 ^ n) := element (2 ^ n) 0 0 1
  have hsm_order : orderOf sm = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · dsimp only [sm]
      simpa using element_swap_sq (2 ^ n) 0 0
    · intro h
      have h0 : sm = element (2 ^ n) 0 0 0 := by
        simpa [sm, element_zero] using h
      have h' := (element_eq_iff (2 ^ n) 0 0 0 0 1 0).mp h0
      exact one_ne_zero h'.2.2
  let σS : ↥S := e.symm sm
  let σ : Q := (σS : Q)
  have hσ_mem : σ ∈ T ⊓ L := σS.2
  have hσ2 : orderOf σ = 2 := by
    dsimp only [σ, σS]
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm sm, hsm_order]
  have hsm_notWmodel : sm ∉ Wmodel := by
    intro hsm
    obtain ⟨b, -, hbm⟩ := Subgroup.mem_map.mp hsm
    have hbase : sm ∈ baseSubgroup (2 ^ n) := by
      rw [← hbm]
      exact b.2
    have hcoord := (element_mem_base (2 ^ n) 0 0 1).mp hbase
    exact one_ne_zero hcoord
  have hσ_notW : σ ∉ W := by
    intro hσ
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hσ
    have hyS : y = σS := Subtype.ext hyeq
    have hσS : σS ∈ Wsub := hyS ▸ hy
    have hmem : e σS ∈ Wmodel := (hmemWsub σS).mp hσS
    rw [e.apply_symm_apply] at hmem
    exact hsm_notWmodel hmem
  have hσz : σ * z = z * σ := by
    have hcomm : σS * zS = zS * σS := Subgroup.mem_center_iff.mp hzS_center σS
    have h := congrArg (fun x : ↥S => (x : Q)) hcomm
    dsimp only [σ, zS] at h
    exact h
  obtain ⟨w0, hw0Wmodel, hw0move⟩ := swap_not_centralizes_baseOmega_map hn1
  let wS : ↥S := e.symm w0
  let w : Q := (wS : Q)
  have hw_Wsub : wS ∈ Wsub := (hmemWsub wS).mpr (by
    rw [show e wS = w0 from e.apply_symm_apply w0]
    exact hw0Wmodel)
  have hw_W : w ∈ W := Subgroup.mem_map.mpr ⟨wS, hw_Wsub, rfl⟩
  have hσmove : ¬ ∀ w' ∈ W, σ * w' * σ⁻¹ = w' := by
    intro hfix
    have hfixw : σ * w * σ⁻¹ = w := hfix w hw_W
    have hconjS : σS * wS * σS⁻¹ = wS := by
      apply Subtype.ext
      change (σ * w * σ⁻¹ : Q) = w
      exact hfixw
    have hmodel : element (2 ^ n) 0 0 1 * w0 * (element (2 ^ n) 0 0 1)⁻¹ = w0 := by
      have h1 : e (σS * wS * σS⁻¹) =
          element (2 ^ n) 0 0 1 * w0 * (element (2 ^ n) 0 0 1)⁻¹ := by
        dsimp only [σS, sm, wS]
        simp [e.apply_symm_apply]
      rw [← h1, hconjS]
      exact e.apply_symm_apply w0
    exact hw0move hmodel
  exact ⟨W, σ, hWle, hWel, hcardW, hzW, ⟨hzTmem, hzL⟩, hTW, hσ_mem, hσ_notW, hσ2,
    hσz, hσmove⟩

theorem exists_frame_four_wr {L : Subgroup Q} [L.Normal] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : (LieModel ↥L .PSL 3 p 1 ∧ p % 4 = 1) ∨ (LieModel ↥L .PSU 3 p 1 ∧ p % 4 = 3))
    {T : Subgroup Q} {z : Q} (hT : IsSylowIn 2 T ⊤) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ W A : Subgroup Q, W ≤ T ⊓ L ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ z ∈ W ∧
      T ≤ normalizer (W : Set Q) ∧ A ≤ T ⊓ L ∧ IsElemAbelian 2 A ∧ Nat.card A = 4 ∧
      ¬ A ≤ centralizer (W : Set Q) := by
  obtain ⟨W, σ, hWle, hWel, hWcard, hzW, hzTL, hTW, hσTL, hσnotW, hσ2, hσz, hσmove⟩ :=
    exists_omega_base_and_swap hp hp5 hL hT hzL hz2 hzT
  have hzσ : z ≠ σ := fun h => hσnotW (h ▸ hzW)
  let A : Subgroup Q := Subgroup.zpowers z ⊔ Subgroup.zpowers σ
  have hAle : A ≤ T ⊓ L := by
    dsimp only [A]
    exact sup_le (Subgroup.zpowers_le.mpr hzTL) (Subgroup.zpowers_le.mpr hσTL)
  have hK4 : IsKleinFour A := by
    dsimp only [A]
    exact CFSG.Goldschmidt75.isKleinFour_sup hz2 hσ2 hzσ hσz.symm
  have hAel : IsElemAbelian 2 A := by
    refine ⟨@IsKleinFour.isMulCommutative A _ hK4, ?_⟩
    intro x hx
    have h := congrArg (fun y : A => (y : Q))
      (@IsKleinFour.mul_self A _ hK4 ⟨x, hx⟩)
    simpa [pow_two] using h
  have hAcard : Nat.card A = 4 := hK4.card_four
  have hAnot : ¬ A ≤ centralizer (W : Set Q) := by
    intro hAcent
    have hσcent : σ ∈ Subgroup.centralizer (W : Set Q) :=
      hAcent (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
    have hfix : ∀ w ∈ W, σ * w * σ⁻¹ = w := by
      intro w hw
      have hcomm : w * σ = σ * w := (Subgroup.mem_centralizer_iff.mp hσcent) w hw
      calc σ * w * σ⁻¹ = w * σ * σ⁻¹ := by rw [← hcomm]
        _ = w := by group
    exact hσmove hfix
  exact ⟨W, A, hWle, hWel, hWcard, hzW, hTW, hAle, hAel, hAcard, hAnot⟩

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
