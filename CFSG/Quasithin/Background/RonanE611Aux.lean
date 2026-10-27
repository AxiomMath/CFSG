module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.ONanE68LieFacts

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6
open scoped Pointwise commutatorElement

section Normalizer

variable {G : Type} [Group G]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext z
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * z * g)
  rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this
  exact this

theorem mem_normalizer_of_map_conj_eq {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have : g * z * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom ↔ z ∈ A := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  rw [h] at this
  exact this.symm

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

end Normalizer

section Normalizer2

variable {G : Type} [Group G]

theorem le_normalizer_of_commute {A W : Subgroup G} (hcomm : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) :
    A ≤ Subgroup.normalizer (W : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hc : ∀ w' ∈ W, a * w' * a⁻¹ = w' := fun w' hw' => by rw [hcomm a ha w' hw']; group
  have hc' : ∀ w' ∈ W, a⁻¹ * w' * a = w' := fun w' hw' => by
    rw [hcomm a⁻¹ (A.inv_mem ha) w' hw']
    group
  constructor
  · intro hw
    rw [hc w hw]
    exact hw
  · intro hw
    have := hc' _ hw
    rw [show a⁻¹ * (a * w * a⁻¹) * a = w by group] at this
    rw [this]
    exact hw

end Normalizer2

section Commutator

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem commutator_eq_of_autI_eq {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K ≤ Subgroup.normalizer (V : Set G)) (h : autI hV X = autI hV K) : ⁅V, X⁆ = ⁅V, K⁆ := by
  refine le_antisymm (Subgroup.commutator_mono le_rfl hXK) ?_
  rw [Subgroup.commutator_le]
  intro v hv k hk
  have hkN := hK hk
  have h1 : convI hV ⟨k, hkN⟩ ∈ autI hV X := by
    rw [h]
    exact convI_mem_autI hV hk hkN
  obtain ⟨x, hxX, hx⟩ := (mem_autI hV).1 h1
  have hxv : (x : G) * v⁻¹ * (x : G)⁻¹ = k * v⁻¹ * k⁻¹ := by
    have := congrArg (fun φ : MulAut (IntMod V hV) =>
      (φ (IntMod.mk hV ⟨v⁻¹, V.inv_mem hv⟩)).val) hx
    have hval : (IntMod.mk hV ⟨v⁻¹, V.inv_mem hv⟩).val = v⁻¹ := rfl
    simpa [convI_apply_val, hval] using this
  have : ⁅v, k⁆ = ⁅v, (x : G)⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
      _ = v * ((x : G) * v⁻¹ * (x : G)⁻¹) := by rw [hxv]
      _ = v * (x : G) * v⁻¹ * (x : G)⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator hv hxX

end Commutator

section Card

variable {G : Type} [Group G]

theorem card_mul_eq_of_inf_sup {U W V : Subgroup G} (hUW : U ⊓ W = ⊥) (hsup : U ⊔ W = V)
    (hcomm : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) : Nat.card V = Nat.card U * Nat.card W := by
  have hUN : U ≤ Subgroup.normalizer (W : Set G) := fun u hu => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hc : ∀ w' ∈ W, u * w' * u⁻¹ = w' := fun w' hw' => by rw [hcomm u hu w' hw']; group
    have hc' : ∀ w' ∈ W, u⁻¹ * w' * u = w' := fun w' hw' => by
      rw [hcomm u⁻¹ (U.inv_mem hu) w' hw']
      group
    constructor
    · intro hw
      rw [hc w hw]
      exact hw
    · intro hw
      have := hc' _ hw
      rw [show u⁻¹ * (u * w * u⁻¹) * u = w by group] at this
      rw [this]
      exact hw
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right U W hUN
  rw [hsup] at hmul
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : ↥U × ↥W => (⟨(p.1 : G) * (p.2 : G), by
      rw [← hsup]
      exact Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥V)) ⟨fun a b hab => ?_, fun v => ?_⟩).symm
  · have h1 : (a.1 : G) * (a.2 : G) = (b.1 : G) * (b.2 : G) := congrArg Subtype.val hab
    have h2 : (b.1 : G)⁻¹ * (a.1 : G) = (b.2 : G) * (a.2 : G)⁻¹ := by
      calc (b.1 : G)⁻¹ * (a.1 : G) = (b.1 : G)⁻¹ * ((a.1 : G) * (a.2 : G)) * (a.2 : G)⁻¹ := by group
        _ = (b.1 : G)⁻¹ * ((b.1 : G) * (b.2 : G)) * (a.2 : G)⁻¹ := by rw [h1]
        _ = (b.2 : G) * (a.2 : G)⁻¹ := by group
    have h3 : (b.1 : G)⁻¹ * (a.1 : G) ∈ U ⊓ W :=
      ⟨U.mul_mem (U.inv_mem b.1.2) a.1.2, by rw [h2]; exact W.mul_mem b.2.2 (W.inv_mem a.2.2)⟩
    rw [hUW, Subgroup.mem_bot] at h3
    have h4 : a.1 = b.1 := Subtype.ext (inv_mul_eq_one.1 h3).symm
    have h5 : (a.2 : G) = b.2 := by
      have : (a.1 : G) * (a.2 : G) = (a.1 : G) * (b.2 : G) := by rw [h1, ← h4]
      exact mul_left_cancel this
    exact Prod.ext h4 (Subtype.ext h5)
  · have hv : (v : G) ∈ (U : Set G) * (W : Set G) := by rw [← hmul]; exact v.2
    obtain ⟨u, hu, w, hw, huw⟩ := hv
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), Subtype.ext huw⟩

theorem commutator_le_of_sup {U W V X : Subgroup G} (hsup : U ⊔ W = V)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) (hXU : ∀ x ∈ X, ∀ u ∈ U, x * u = u * x) :
    ⁅V, X⁆ ≤ ⁅W, X⁆ := by
  have hUN : U ≤ Subgroup.normalizer (W : Set G) := fun u hu => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hc : ∀ w' ∈ W, u * w' * u⁻¹ = w' := fun w' hw' => by rw [hUW u hu w' hw']; group
    have hc' : ∀ w' ∈ W, u⁻¹ * w' * u = w' := fun w' hw' => by
      rw [hUW u⁻¹ (U.inv_mem hu) w' hw']
      group
    constructor
    · intro hw
      rw [hc w hw]
      exact hw
    · intro hw
      have := hc' _ hw
      rw [show u⁻¹ * (u * w * u⁻¹) * u = w by group] at this
      rw [this]
      exact hw
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right U W hUN
  rw [hsup] at hmul
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hv' : v ∈ (U : Set G) * (W : Set G) := by rw [← hmul]; exact hv
  obtain ⟨u, hu, w, hw, rfl⟩ := hv'
  have hux : Commute u x := (hXU x hx u hu).symm
  have huw : Commute u w := hUW u hu w hw
  have hcom : u * (w * x * w⁻¹) = (w * x * w⁻¹) * u :=
    ((huw.mul_right hux).mul_right huw.inv_right).eq
  have : ⁅u * w, x⁆ = ⁅w, x⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc u * w * x * (u * w)⁻¹ * x⁻¹ = u * (w * x * w⁻¹) * u⁻¹ * x⁻¹ := by group
      _ = (w * x * w⁻¹) * u * u⁻¹ * x⁻¹ := by rw [hcom]
      _ = w * x * w⁻¹ * x⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator hw hx

end Card

end CFSG.Quasithin.RonanE611
