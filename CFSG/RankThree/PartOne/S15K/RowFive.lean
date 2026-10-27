module

public import CFSG.RankThree.PartOne.S15K.U5Layer
public import CFSG.RankThree.PartOne.S15K.AutTorus
public import CFSG.RankThree.PartOne.U5K.Final

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem AutLayerFamily.mono {P : Type*} [Group P] {p : ℕ} {β : MulAut P} {S S' : Set (MulAut P)}
    {ι : Type*} {F : ι → Subgroup P} (hF : AutLayerFamily p β S F) (hS : S' ⊆ S) :
    AutLayerFamily p β S' F :=
  { le := hF.le
    comp := hF.comp
    perfect := hF.perfect
    inner := fun α hα i => hF.inner α (hS hα) i
    center := hF.center }

theorem U5Act_trans {G : Type*} [Group G] {I : Subgroup G} {P Q : Type*} [Group P] [Group Q]
    (e : ↥I ⧸ Subgroup.center ↥I ≃* P) (u : P ≃* Q)
    (y : ↥(Subgroup.normalizer (I : Set G))) :
    U5K.U5Act I (e.trans u) y = MulAut.congr u (U5K.U5Act I e y) := by
  refine MulEquiv.ext fun z => ?_
  simp [U5K.U5Act, MulAut.congr_apply]


open CFSG.LocalAnalysis.ComponentInitial in
theorem layerRowFive_of (hEin : U5K.U5EInndiag) : LayerRowFive := by
  intro G _ _ p A c L E h15 hF12 hout
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h15.h12.three_lt; omega)
    (by have := h15.h12.three_lt; omega)
  have hEI : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) := E_le_normalizer_lieGenerated hp
  have hEel := h15.h12.E_elem
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := (IsMulCommutative.is_comm (M := ↥E)).comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
    exact congrArg Subtype.val this
  set I := lieGenerated p E with hI
  let u := U5K.u5Equiv f hf
  let e₀ := e.trans u
  let act : ↥E →* MulAut (primeFormP (U5K.u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) :=
    (U5K.U5Act I e₀).comp (Subgroup.inclusion hEI)
  have hact : ∀ (x : ↥E) (y : ↥I), act x (e₀ (y : ↥I ⧸ Subgroup.center ↥I)) =
      e₀ ((I.normalizerMonoidHom ⟨(x : G), hEI x.2⟩ y : ↥I) : ↥I ⧸ Subgroup.center ↥I) :=
    fun x y => U5K.U5Act_apply I e₀ ⟨(x : G), hEI x.2⟩ y
  have hactE : ∀ x : ↥E, act x = MulAut.congr u (U5K.U5Act I e ⟨(x : G), hEI x.2⟩) :=
    fun x => U5Act_trans e u ⟨(x : G), hEI x.2⟩
  have hD : ∀ x : ↥E, act x ∈ primeFormD (U5K.u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) := by
    intro x
    have h1 := (hEin G p A c L E h15 hF12 hout f hf e (x : G) (hEI x.2) x.2).1
    rw [hactE x]
    have h2 : U5K.U5Act I e ⟨(x : G), hEI x.2⟩ ∈ (U5K.u5FieldFactor f hf).ker := by
      simpa [U5K.U5Inndiag, hf] using h1
    rw [← ker_primeFormFieldFactor (U5K.u5FieldData f hf)
      (isPrimeFormGram_idGram (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num)
      (by intro hh; omega)]
    exact h2
  have hfaith : ∀ x : ↥E, x ≠ 1 → act x ≠ 1 := by
    intro x hx1 h1
    apply hx1
    have h2 : U5K.U5Act I e ⟨(x : G), hEI x.2⟩ = 1 := by
      rw [hactE x] at h1
      exact (MulEquiv.map_eq_one_iff _).mp h1
    exact Subtype.ext ((hEin G p A c L E h15 hF12 hout f hf e (x : G) (hEI x.2) x.2).2 h2)
  have hord : ∀ x : ↥E, act x ^ p = 1 := by
    intro x
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hEexp x x.2)
    rw [this, map_one]
  have hker := U5K.ker_not_dvd_p_of_max hp e hEel hEI h15.h12.A_le_E h15.h12.E_le h15.h12.E_max
    (fun x hx hxE h => (hEin G p A c L E h15 hF12 hout f hf e x hx hxE).2 h)
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥I) := by
    intro hdvd
    apply hker
    have h1 : Nat.card ((Subgroup.center ↥I).map (Subgroup.inclusion (Subgroup.le_normalizer :
        I ≤ Subgroup.normalizer (I : Set G)))) = Nat.card (Subgroup.center ↥I) :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    have h2 : (Subgroup.center ↥I).map (Subgroup.inclusion (Subgroup.le_normalizer :
        I ≤ Subgroup.normalizer (I : Set G))) ≤ (U5K.U5Act I e).ker := by
      rintro _ ⟨z, hz, rfl⟩
      rw [MonoidHom.mem_ker]
      have h3 := U5K.U5Act_of_mem I e z
      have h4 : (z : ↥I ⧸ Subgroup.center ↥I) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      rw [h4, map_one] at h3
      exact h3.trans (map_one _)
    exact hdvd.trans (h1 ▸ Subgroup.card_dvd_of_le h2)
  refine layerDataW_of_autFamily hp e₀ hEI hEexp hEcomm hZ act hact fun b hb1 => ?_
  obtain ⟨ι, F, hF⟩ := exists_autLayerFamily (U5K.u5FieldData f hf) hp hp5 hpf (β := act b) (hD b)
    (hord b) (hfaith b hb1)
  refine ⟨ι, F, hF.mono ?_⟩
  rintro _ ⟨x, rfl⟩
  have hxb : x * b = b * x := Subtype.ext (hEcomm x x.2 b b.2)
  exact ⟨hD x, by rw [← map_mul, ← map_mul, hxb], hord x⟩


theorem layerRowFive_of_package (hMod : KFU5Mod) (hAt : KFU5At) (h5 : U5FiveInndiag) :
    LayerRowFive :=
  layerRowFive_of (U5K.u5EInndiag_of hMod hAt h5)

end CFSG.RankThree.PartOne.S15K
