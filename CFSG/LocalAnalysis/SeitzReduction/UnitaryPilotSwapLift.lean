module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftDecomp
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftSplit
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBLiftSetting
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamNormal

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift SwapComponentData)

section Range

variable {H : Type} [Group H] [Finite H]

theorem range_eq_oddCoreLift_of_swapLift {t : H} {Kb Db : Subgroup (H ⧸ oddCore H)}
    (h : SwapComponentData (QuotientGroup.mk' (oddCore H) t) Kb Db) (hBK : HasBLift Kb)
    (hcard : Nat.card Kb = Nat.card Db) {S : Type*} [Group S] {φ ι : S →* H}
    (hφK : ∀ x, φ x ∈ oddCoreLift Kb) (hφ : ∀ x, φ x * (t * φ x * t⁻¹) = ι x)
    (hι : ι.range.map (QuotientGroup.mk' (oddCore H)) = Db) : φ.range = oddCoreLift Kb := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set τ := π t with hτ
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp h.isComponent.1.1
  have hKhp : ⁅oddCoreLift Kb, oddCoreLift Kb⁆ = oddCoreLift Kb := F4Pilot.commutator_oddCoreLift Kb
  have hπK : (oddCoreLift Kb).map π = Kb := F4Pilot.map_oddCoreLift hKp
  have hgK : ∀ x, π (φ x) ∈ Kb := fun x => hπK ▸ mem_map_of_mem π (hφK x)
  have hker : (π.comp ι).ker = (π.comp φ).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    rw [← hφ x, map_mul, map_mul, map_mul, map_inv]
    constructor
    · intro h1
      have h2 : π (φ x) = (π t * π (φ x) * (π t)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : π (φ x) ∈ Kb ⊓ Kb.map (MulAut.conj τ).toMonoidHom := by
        refine Subgroup.mem_inf.2 ⟨hgK x, ?_⟩
        rw [h2]
        exact inv_mem ⟨π (φ x), hgK x, rfl⟩
      rw [h.inf_eq_bot hO, mem_bot] at h3
      exact h3
    · intro h1
      rw [h1]
      group
  have hcardg : Nat.card (π.comp φ).range = Nat.card Kb := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp φ)).toEquiv, ← hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp ι)).toEquiv,
      MonoidHom.range_comp, hι, hcard]
  have hgle : (π.comp φ).range ≤ Kb := by
    rintro _ ⟨x, rfl⟩
    exact hgK x
  have hgeq : (π.comp φ).range = Kb := Subgroup.eq_of_le_of_card_ge hgle hcardg.ge
  have hle : φ.range ≤ oddCoreLift Kb := by
    rintro _ ⟨x, rfl⟩
    exact hφK x
  refine le_antisymm hle (F4Pilot.perfect_le_of_forall_exists_commute hKhp hle fun a ha => ?_)
  have hπa : π a ∈ (π.comp φ).range := hgeq ▸ hπK ▸ mem_map_of_mem π ha
  obtain ⟨x, hx⟩ := hπa
  refine ⟨φ x, ⟨x, rfl⟩, (φ x)⁻¹ * a, by group, fun b hb => ?_⟩
  have hz : (φ x)⁻¹ * a ∈ oddCore H := by
    have h2 : π ((φ x)⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, ← MonoidHom.comp_apply π φ, hx, inv_mul_cancel]
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact mem_centralizer_iff.1 (hBK hb) _ hz

end Range

section Split

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem oddCentralSplit_unitarySU
    {m : ℕ} (hm : 2 ≤ m) (hmq : (m, 2 ^ f) ≠ (3, 2)) :
    OddCentralSplit (unitarySU 2 f K m) :=
  oddCentralSplit_statedSU h.card_eq_sq hm hmq

theorem oddCentralSplit_unitaryBlock
    {n : ℕ} {N : Finset (Fin n)} (hN : 2 ≤ N.card)
    (hNq : (N.card, 2 ^ f) ≠ (3, 2)) : OddCentralSplit (unitaryBlock h N) :=
  (oddCentralSplit_unitarySU h hN hNq).of_mulEquiv (unitaryBlockEquiv h N)

theorem oddCentralSplit_unitaryBlock_compl_pair
    {n : ℕ} (hn : 6 ≤ n)
    {a b : Fin n} (hab : a ≠ b) : OddCentralSplit (unitaryBlock h ({a, b}ᶜ : Finset (Fin n))) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  refine oddCentralSplit_unitaryBlock h (by omega) fun h3 => ?_
  have := congrArg Prod.fst h3
  simp only at this
  omega

theorem isPerfect_unitaryBlock {n : ℕ} {N : Finset (Fin n)} (hN : 4 ≤ N.card) :
    Group.IsPerfect (unitaryBlock h N) := by
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (unitarySU 2 f K N.card) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq (by omega) fun h3 => by
      have := congrArg Prod.fst h3
      simp only at this
      omega
  exact Group.IsPerfect.ofSurjective (f := (unitaryBlockEquiv h N).toMonoidHom)
    (unitaryBlockEquiv h N).surjective

end Split

section Diag

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem unitaryProj_torusDiagSU_mem_centralizer_unitaryRootTorus {a b : Fin n} (hab : a ≠ b)
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    unitaryProj h n (torusDiagSU h c) ∈
      centralizer (unitaryRootTorus h hab : Set (unitaryPSU h n)) := by
  refine mem_centralizer_iff.2 fun x hx => ?_
  obtain ⟨c', -, rfl⟩ := (mem_unitaryBlockTorus h).1
    (unitaryRootTorus_le_unitaryBlockTorus_of_subset h hab (Finset.empty_subset _) hx)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm c' c]

theorem pow_card_units_eq_one_unitaryTorusParam [Finite K]
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) : c ^ Nat.card Kˣ = 1 := by
  apply Subtype.ext
  funext i
  change (c.1 i) ^ Nat.card Kˣ = 1
  exact pow_card_eq_one'

end Diag

theorem eq_one_of_pow_eq_one_of_odd {x : Multiplicative (ZMod 2)} {m : ℕ} (hm : Odd m)
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : x ^ 2 = 1 := by
    have := pow_card_eq_one (G := Multiplicative (ZMod 2)) (x := x)
    simpa using this
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hx
  exact hx

theorem commutator_map_conj_eq_bot_of_mem_centralizer {Y : Type*} [Group Y] {s : Y}
    {A D : Subgroup Y} (hs : s ∈ centralizer (D : Set Y)) (hAD : ⁅A, D⁆ = ⊥) :
    ⁅A.map (MulAut.conj s).toMonoidHom, D⁆ = ⊥ := by
  have hDs : D.map (MulAut.conj s).toMonoidHom = D := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      change s * d * s⁻¹ ∈ D
      rw [← mem_centralizer_iff.1 hs d hd, mul_inv_cancel_right]
      exact hd
    · intro hx
      refine ⟨x, hx, ?_⟩
      change s * x * s⁻¹ = x
      rw [← mem_centralizer_iff.1 hs x hx, mul_inv_cancel_right]
  rw [← hDs, ← map_commutator, hAD, Subgroup.map_bot]

theorem eq_bot_of_le_sup_of_commutator_eq_bot {Y : Type*} [Group Y] {A B D : Subgroup Y}
    (hD : D ≤ A ⊔ B) (hDp : ⁅D, D⁆ = D) (hA : ⁅A, D⁆ = ⊥) (hB : ⁅B, D⁆ = ⊥) : D = ⊥ := by
  have hDD : D ≤ centralizer (D : Set Y) :=
    hD.trans (sup_le (commutator_eq_bot_iff_le_centralizer.1 hA)
      (commutator_eq_bot_iff_le_centralizer.1 hB))
  rw [← hDp]
  exact commutator_eq_bot_iff_le_centralizer.2 hDD

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem nonempty_swapNeighbourParam_of_swapRow_of_split (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G))
    (hsplit : OddCentralSplit (unitaryBlock h ({a, b}ᶜ : Finset (Fin n))))
    (hrow : ∃ Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
          oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))),
        IsComponent Kc ∧
        ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G)))) ≤
          Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
        center Kc = ⊥ ∧
        Nonempty (Kc ≃* ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G)))))) :
    Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))) := by
  have := h.finite
  have := h.charP
  set X := modelToG e (unitaryRootTorus h hab) with hXdef
  set H := centralizer (X : Set G) with hHdef
  set N : Finset (Fin n) := ({a, b}ᶜ : Finset (Fin n)) with hNdef
  set D := modelToG e (blockSU h N) with hDdef
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set τ := π t' with hτ
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hcard : N.card = n - 2 := card_compl_pair hab
  obtain ⟨Kc, hKc, hDKK, hne, hcomm, -, ⟨eKD⟩⟩ := hrow
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC
    ht hab (X := X) rfl htX (D := D) rfl
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -, -⟩ :=
    neighbour_data_unitaryRootTorus h e hn hab htC (X := X) rfl (D := D) rfl
  have hDH : D ≤ H := hDC.trans inf_le_left
  have hDt : D ≤ centralizer ({t} : Set G) := hDC.trans inf_le_right
  have hτD : τ ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData τ Kc Db :=
    ⟨by rw [hτ, ← map_mul, ht't', map_one], hKc, hne, hcomm, hDKK, hτD, hsyl⟩
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hDbne : Db ≠ ⊥ := CFSG.SeitzReduction.ne_bot_of_isQuasisimple hcomp.2.2
  have hDbp : ⁅Db, Db⁆ = Db := Subgroup.isPerfect_iff.1 (⟨hcomp.2.2.1⟩ : Group.IsPerfect _)
  have hττ : (Kc.map (MulAut.conj τ).toMonoidHom).map (MulAut.conj τ).toMonoidHom = Kc := by
    rw [F4Pilot.map_conj_map_conj_eq_map_conj_mul, hdata.mul_self, map_one]
    ext x
    simp
  have h1 : ⁅Kc, Db⁆ ≠ ⊥ := fun hb => hDbne (eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDbp hb
    (commutator_map_conj_eq_bot_of_mem_centralizer hτD hb))
  have h2 : ⁅Kc.map (MulAut.conj τ).toMonoidHom, Db⁆ ≠ ⊥ := fun hb => hDbne
    (eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDbp
      (hττ ▸ commutator_map_conj_eq_bot_of_mem_centralizer hτD hb) hb)
  obtain ⟨-, -, hB⟩ := bLift_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab (X := X) rfl
    (D := D) rfl
  obtain ⟨hBK, hBsup⟩ := hB Kc (Kc.map (MulAut.conj τ).toMonoidHom) hKc
    (F4Pilot.isComponent_map_conj hKc τ) h1 h2
  let eN : N ≃ Fin (n - 2) := N.equivFinOfCardEq hcard
  have hZDb : center Db = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : eKD.symm y ∈ center Kc := by
      rw [mem_center_iff] at hy ⊢
      intro z
      apply eKD.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
    rw [hdata.center_eq_bot hO, mem_bot] at hy'
    rw [mem_bot, ← eKD.apply_symm_apply y, hy', map_one]
  obtain ⟨ε, hεinj, hεrange, -⟩ := exists_unitaryPSU_embedding e hab eN (by omega) hDbne hZDb
    (Kc := Db) le_rfl
  have hεsurj : Function.Surjective ε := by
    intro y
    have hy : y ∈ ε.range := by
      rw [hεrange]
      exact mem_subgroupOf.2 y.2
    exact hy
  have hOut : Group.IsSolvable (Outer Kc) :=
    isSolvable_outer_of_mulEquiv h (by omega) (fun h3 => by
      have := congrArg Prod.fst h3
      simp only at this
      omega) (eKD.trans (MulEquiv.ofBijective ε ⟨hεinj, hεsurj⟩).symm)
  obtain ⟨hcH, hdH, hsH, hKhp, hπK⟩ := swapLift_decomposition_of_hasBLift hdata hOut hBK hBsup
  have hodd : Odd (Nat.card (oddCoreLift Kc ⊓ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom :
      Subgroup H)) :=
    (CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := H)).of_dvd_nat
      (Subgroup.card_dvd_of_le hdH)
  have hSperf : Group.IsPerfect (unitaryBlock h N) := isPerfect_unitaryBlock h (by omega)
  let ιG : unitaryBlock h N →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((unitaryProj h n).comp (unitaryBlock h N).subtype))
  have hιG : ∀ x : unitaryBlock h N, ιG x = ((e.symm (unitaryProj h n x) : L) : G) := fun x => rfl
  have hιD : ∀ x : unitaryBlock h N, ιG x ∈ D := fun x =>
    symm_mem_modelToG e (unitaryProj_mem_blockSU h x.2)
  let ι : unitaryBlock h N →* H := ιG.codRestrict H fun x => hDH (hιD x)
  have hιinj : ∀ x, ι x = 1 → x = 1 := by
    intro x hx
    have h0 : ((ι x : H) : G) = 1 := congrArg Subtype.val hx
    have h1 : e.symm (unitaryProj h n x) = 1 := Subtype.ext h0
    have h2 : unitaryProj h n x = 1 := by
      rw [← map_one e.symm] at h1
      exact e.symm.injective h1
    exact Subtype.ext (eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one h (by omega) x.2 h2)
  have hPmap : (perfectCore (⊤ : Subgroup H)).map H.subtype = centralizerPerfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hDE : D ≤ centralizerPerfectCore X := modelToG_blockSU_compl_le_neighbourCore e hn hab
  have hιK : ∀ x, ι x ∈ oddCoreLift Kc ⊔ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom := by
    intro x
    rw [hsH]
    have h1 : (ι x : G) ∈ (perfectCore (⊤ : Subgroup H)).map H.subtype := hPmap ▸ hDE (hιD x)
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [show y = ι x from Subtype.ext hyx] at hy
  have hιt : ∀ x, t' * ι x * t'⁻¹ = ι x := fun x => Subtype.ext (by
    change t * ιG x * t⁻¹ = ιG x
    rw [← mem_centralizer_iff.1 htC (ιG x) (e.symm _).2, mul_inv_cancel_right])
  have hιrange : ι.range = D.subgroupOf H := by
    ext ⟨g, hg⟩
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨x, hx⟩
      rw [← congrArg Subtype.val hx]
      exact hιD x
    · intro hgD
      obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hgD
      obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hy
      exact ⟨⟨A, hA⟩, Subtype.ext rfl⟩
  obtain ⟨φ, hφK, hφ⟩ := exists_swapLift hcH ht't' hsplit hodd ι hιK hιt
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hιinj
    rw [← hφ x, hx, mul_one, mul_inv_cancel, mul_one]
  have hφrange : φ.range = oddCoreLift Kc :=
    range_eq_oddCoreLift_of_swapLift hdata hBK (Nat.card_congr eKD.toEquiv) hφK hφ
      (by rw [hιrange])
  refine ⟨{ Ψ := H.subtype.comp (swapParamHom hcH hφK)
            range_eq := ?_
            ker_le := ?_
            diag := fun x => congrArg Subtype.val (hφ x)
            N2 := ?_
            swap := fun x y => congrArg Subtype.val (conj_swapParamHom hcH hφK ht't' x y) }⟩
  · rw [MonoidHom.range_comp, range_swapParamHom, hφrange, hsH, hPmap]
  · intro x hx
    exact ker_swapParamHom_le_center hcH hφK ht't' hφinj (Subtype.ext hx)
  ·
    intro c _ x
    have hgX : ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) ∈ H :=
      modelToG_le_centralizer e (le_refl (centralizer (unitaryRootTorus h hab :
        Set (unitaryPSU h n))))
        (symm_mem_modelToG e (unitaryProj_torusDiagSU_mem_centralizer_unitaryRootTorus hab c))
    set g' : H := ⟨_, hgX⟩ with hg'def
    have hg't : g' * t' = t' * g' := Subtype.ext (mem_centralizer_iff.1 htC _ (e.symm _).2)
    have hr : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      exact LinearPilot.odd_natCard_sub_one
    have hgr : g' ^ Nat.card Kˣ = 1 := Subtype.ext (by
      change ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) ^ Nat.card Kˣ = 1
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, ← map_pow,
        pow_card_units_eq_one_unitaryTorusParam c, map_one, map_one, map_one,
        OneMemClass.coe_one])
    obtain ⟨σs, hσs⟩ := hdata.exists_sign
    have hσ1 : σs (π g') = 1 :=
      eq_one_of_pow_eq_one_of_odd hr (by rw [← map_pow, ← map_pow, hgr, map_one, map_one])
    have hg'N : g' ∈ normalizer (oddCoreLift Kc : Set H) :=
      F4Pilot.mem_normalizer_oddCoreLift Kc (hσs _ hσ1)
    have hα : ∀ y, ι ((conjTorusSU h N c).toMonoidHom y) = g' * ι y * g'⁻¹ := fun y =>
      Subtype.ext (by
        change ((e.symm (unitaryProj h n ((conjTorusSU h N c y : unitaryBlock h N) :
          unitarySU 2 f K n)) : L) : G) = _
        rw [coe_conjTorusSU_apply, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
        rfl)
    have hφα := swapLift_comp_eq_conj hcH hφK hφ hg'N hg't (conjTorusSU h N c).toMonoidHom hα
    have h1 : g'⁻¹ * t' * g' = t' := by
      rw [mul_assoc, ← hg't, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : g'⁻¹ * t'⁻¹ = t'⁻¹ * g'⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hg't]
    have key : swapParamHom hcH hφK (conjTorusSU h N c x.1, conjTorusSU h N c x.2) =
        g' * swapParamHom hcH hφK x * g'⁻¹ := by
      rw [swapParamHom_apply, swapParamHom_apply]
      change φ ((conjTorusSU h N c).toMonoidHom x.1) *
        (t' * φ ((conjTorusSU h N c).toMonoidHom x.2) * t'⁻¹) = _
      rw [hφα, hφα]
      calc g' * φ x.1 * g'⁻¹ * (t' * (g' * φ x.2 * g'⁻¹) * t'⁻¹)
          = g' * φ x.1 * (g'⁻¹ * t' * g') * φ x.2 * (g'⁻¹ * t'⁻¹) := by group
        _ = g' * φ x.1 * t' * φ x.2 * (t'⁻¹ * g'⁻¹) := by rw [h1, h2]
        _ = g' * (φ x.1 * (t' * φ x.2 * t'⁻¹)) * g'⁻¹ := by group
    exact congrArg Subtype.val key

theorem nonempty_swapNeighbourParam_of_swapRow
    (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    (htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G))
    (hrow : ∃ Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
          oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))),
        IsComponent Kc ∧
        ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G)))) ≤
          Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
        center Kc = ⊥ ∧
        Nonempty (Kc ≃* ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
              Set G)))))) :
    Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))) :=
  nonempty_swapNeighbourParam_of_swapRow_of_split h hset e hn htC ht hab htX
    (oddCentralSplit_unitaryBlock_compl_pair h hn hab) hrow

end Swap

end CFSG.SeitzReduction.UnitaryPilot
