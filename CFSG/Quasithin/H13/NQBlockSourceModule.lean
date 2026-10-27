module

public import CFSG.Quasithin.H13.NQBlockNoEscape
public import CFSG.Quasithin.H13.NQBlockOriginalReducedModule

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElementaryAbelian_of_le_omegaOneCenterOf {W X : Subgroup G}
    (h : W ≤ omegaOneCenterOf 2 X) : CFSG.IsElementaryAbelian 2 ↥W :=
  { is_comm := ⟨fun a b => Subtype.ext ((mem_omegaOneCenterOf_iff.mp (h a.2)).2.1 b
      (mem_omegaOneCenterOf_iff.mp (h b.2)).1)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (pow_eq_one_of_mem_omegaOneCenterOf (h a.2)) }

theorem conj_inv_mem_nqSourceModule {Y R : Subgroup G} {x z : G} (hx : x ∈ Y ⊔ R)
    (hz : z ∈ omegaOneCenterOf 2 R) : x⁻¹ * z * x ∈ nqSourceModule Y R := by
  have hle : CFSG.conjugate (omegaOneCenterOf 2 R) x ≤ nqSourceModule Y R :=
    le_sSup ⟨x, hx, rfl⟩
  apply hle
  refine ⟨z, hz, ?_⟩
  change x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * z * x
  rw [inv_inv]

theorem omegaOneCenterOf_le_nqSourceModule (Y R : Subgroup G) :
    omegaOneCenterOf 2 R ≤ nqSourceModule Y R := fun z hz => by
  have := conj_inv_mem_nqSourceModule (Y := Y) (one_mem _) hz
  rwa [inv_one, one_mul, mul_one] at this

theorem nqSourceModule_le {Y R U : Subgroup G}
    (h : ∀ x ∈ Y ⊔ R, ∀ z ∈ omegaOneCenterOf 2 R, x⁻¹ * z * x ∈ U) :
    nqSourceModule Y R ≤ U := by
  apply sSup_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
  change x⁻¹ * z * x⁻¹⁻¹ ∈ U
  rw [inv_inv]
  exact h x hx z hz

theorem conj_mem_nqSourceModule {Y R : Subgroup G} {g w : G} (hg : g ∈ Y ⊔ R)
    (hw : w ∈ nqSourceModule Y R) : g * w * g⁻¹ ∈ nqSourceModule Y R := by
  have hle : nqSourceModule Y R ≤ (nqSourceModule Y R).comap (MulAut.conj g).toMonoidHom :=
    nqSourceModule_le fun x hx z hz => by
      change g * (x⁻¹ * z * x) * g⁻¹ ∈ nqSourceModule Y R
      have e : g * (x⁻¹ * z * x) * g⁻¹ = (x * g⁻¹)⁻¹ * z * (x * g⁻¹) := by group
      rw [e]
      exact conj_inv_mem_nqSourceModule ((Y ⊔ R).mul_mem hx ((Y ⊔ R).inv_mem hg)) hz
  exact hle hw

theorem conj_mem_nqSourceModule_of_normalizer {Y R : Subgroup G} {g w : G}
    (hgS : ∀ x ∈ Y ⊔ R, g * x * g⁻¹ ∈ Y ⊔ R) (hgR : g ∈ normalizer (R : Set G))
    (hw : w ∈ nqSourceModule Y R) : g * w * g⁻¹ ∈ nqSourceModule Y R := by
  have hle : nqSourceModule Y R ≤ (nqSourceModule Y R).comap (MulAut.conj g).toMonoidHom :=
    nqSourceModule_le fun x hx z hz => by
      change g * (x⁻¹ * z * x) * g⁻¹ ∈ nqSourceModule Y R
      have e : g * (x⁻¹ * z * x) * g⁻¹ =
          (g * x * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * x * g⁻¹) := by group
      rw [e]
      exact conj_inv_mem_nqSourceModule (hgS x hx) (conj_mem_omegaOneCenterOf hgR hz)
  exact hle hw

theorem le_normalizer_nqSourceModule (Y R : Subgroup G) :
    Y ⊔ R ≤ normalizer (nqSourceModule Y R : Set G) := fun g hg =>
  mem_normalizer_of_conj_mem (fun _ hw => conj_mem_nqSourceModule hg hw) fun w hw => by
    have := conj_mem_nqSourceModule ((Y ⊔ R).inv_mem hg) hw
    rwa [inv_inv] at this

theorem mem_normalizer_nqSourceModule {Y R : Subgroup G} {g : G}
    (hgY : g ∈ normalizer (Y : Set G)) (hgR : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer (nqSourceModule Y R : Set G) := by
  have hS : ∀ h : G, h ∈ normalizer (Y : Set G) → h ∈ normalizer (R : Set G) →
      ∀ x ∈ Y ⊔ R, h * x * h⁻¹ ∈ Y ⊔ R := fun h hY hR x hx => by
    have hle : Y ⊔ R ≤ (Y ⊔ R).comap (MulAut.conj h).toMonoidHom :=
      sup_le (fun y hy => le_sup_left (a := Y) ((mem_normalizer_iff.mp hY y).mp hy))
        (fun r hr => le_sup_right (a := Y) ((mem_normalizer_iff.mp hR r).mp hr))
    exact hle hx
  refine mem_normalizer_of_conj_mem
    (fun _ hw => conj_mem_nqSourceModule_of_normalizer (hS g hgY hgR) hgR hw) fun w hw => by
    have := conj_mem_nqSourceModule_of_normalizer
      (hS g⁻¹ (inv_mem hgY) (inv_mem hgR)) (inv_mem hgR) hw
    rwa [inv_inv] at this

theorem conj_mem_centralizer_of_normalizer {W : Subgroup G} {g c : G}
    (hg : g ∈ normalizer (W : Set G)) (hc : c ∈ centralizer (W : Set G)) :
    g * c * g⁻¹ ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : g⁻¹ * w * g ∈ W := by
    refine (mem_normalizer_iff.mp hg (g⁻¹ * w * g)).mpr ?_
    have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    rw [e]
    exact hw
  have h1 := hc _ hw'
  calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * w := by group

theorem nqSourceModule_le_omegaOneCenterOf_pCoreOf [Finite G] {Y R : Subgroup G}
    (hRS : QuasithinUnique.IsSylowTwoOf R (Y ⊔ R)) (hchar : QuasithinUnique.CharTwo (Y ⊔ R)) :
    nqSourceModule Y R ≤ omegaOneCenterOf 2 (pCoreOf 2 (Y ⊔ R)) := by
  have hOR : pCoreOf 2 (Y ⊔ R) ≤ R :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRS
  have hSO : Y ⊔ R ≤ normalizer (pCoreOf 2 (Y ⊔ R) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  apply nqSourceModule_le
  intro x hx z hz
  obtain ⟨hzR, hzc, hz2⟩ := mem_omegaOneCenterOf_iff.mp hz
  have hzc' : ∀ o ∈ pCoreOf 2 (Y ⊔ R), z * o = o * z := fun o ho => hzc o (hOR ho)
  have hzO : z ∈ pCoreOf 2 (Y ⊔ R) :=
    hchar ⟨le_sup_right (a := Y) hzR, mem_centralizer_iff.mpr fun o ho => (hzc' o ho).symm⟩
  have := conj_mem_omegaOneCenterOf (hSO ((Y ⊔ R).inv_mem hx))
    (mem_omegaOneCenterOf_iff.mpr ⟨hzO, hzc', hz2⟩)
  rwa [inv_inv] at this

theorem mem_centralizer_nqSourceModule_of_commutator {Y R : Subgroup G}
    (hRY : R ≤ normalizer (Y : Set G)) {r : G} (hr : r ∈ R)
    (hry : ∀ y ∈ Y, ⁅r, y⁆ ∈ centralizer (nqSourceModule Y R : Set G)) :
    r ∈ centralizer (nqSourceModule Y R : Set G) := by
  set W := nqSourceModule Y R with hWdef
  set C := centralizer (W : Set G) with hCdef
  have hSN := le_normalizer_nqSourceModule Y R
  have hNC : ∀ g ∈ Y ⊔ R, ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g hg c hc =>
    conj_mem_centralizer_of_normalizer (hSN hg) hc
  let X : Subgroup G :=
    { carrier := {x | x ∈ R ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ C}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨R.mul_mem ha.1 hb.1, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact C.mul_mem (hNC a (le_sup_right (a := Y) ha.1) _ (hb.2 y hy)) (ha.2 y hy)
      one_mem' := ⟨R.one_mem, fun y _ => by
        rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact C.one_mem⟩
      inv_mem' := fun {a} ha => by
        refine ⟨R.inv_mem ha.1, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hNC a⁻¹ (le_sup_right (a := Y) (R.inv_mem ha.1)) _ (C.inv_mem (ha.2 y hy)) }
  have hXR : X ≤ R := fun x hx => hx.1
  set U := X ⊔ C with hUdef
  have hUZ : U ≤ centralizer (omegaOneCenterOf 2 R : Set G) := by
    refine sup_le (fun x hx => mem_centralizer_iff.mpr fun z hz => ?_)
      (fun c hc => mem_centralizer_iff.mpr fun z hz => ?_)
    · exact (mem_omegaOneCenterOf_iff.mp hz).2.1 x (hXR hx)
    · exact (mem_centralizer_iff.mp hc) z (omegaOneCenterOf_le_nqSourceModule Y R hz)
  have hCU : ∀ g ∈ Y ⊔ R, C ≤ U.comap (MulAut.conj g).toMonoidHom := fun g hg c hc =>
    le_sup_right (a := X) (hNC g hg c hc)
  have hYU : ∀ g ∈ Y, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have hle : U ≤ U.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (hCU g (le_sup_left (a := Y) hg))
      change g * x * g⁻¹ ∈ U
      have e : g * x * g⁻¹ = x * ⁅x⁻¹, g⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact U.mul_mem (le_sup_left (a := X) hx) (le_sup_right (a := X) ((X.inv_mem hx).2 g hg))
    exact hle hu
  have hRU : ∀ g ∈ R, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have hle : U ≤ U.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (hCU g (le_sup_right (a := Y) hg))
      change g * x * g⁻¹ ∈ U
      refine le_sup_left (a := X) ⟨R.mul_mem (R.mul_mem hg hx.1) (R.inv_mem hg), fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ Y := by
        have := (mem_normalizer_iff.mp (hRY (R.inv_mem hg)) y).mp hy
        rwa [inv_inv] at this
      have e : ⁅g * x * g⁻¹, y⁆ = g * ⁅x, g⁻¹ * y * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hNC g (le_sup_right (a := Y) hg) _ (hx.2 _ hy')
    exact hle hu
  let P : Subgroup G :=
    { carrier := {s | ∀ u ∈ U, s * u * s⁻¹ ∈ U ∧ s⁻¹ * u * s ∈ U}
      mul_mem' := fun {a b} ha hb u hu => by
        refine ⟨?_, ?_⟩
        · have e : a * b * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
          rw [e]
          exact (ha _ (hb u hu).1).1
        · have e : (a * b)⁻¹ * u * (a * b) = b⁻¹ * (a⁻¹ * u * a) * b := by group
          rw [e]
          exact (hb _ (ha u hu).2).2
      one_mem' := fun u hu => by simpa using hu
      inv_mem' := fun {a} ha u hu => by
        refine ⟨?_, ?_⟩
        · have := (ha u hu).2
          rwa [inv_inv]
        · have := (ha u hu).1
          rwa [inv_inv] }
  have hSP : Y ⊔ R ≤ P := by
    refine sup_le (fun g hg u hu => ⟨hYU g hg u hu, ?_⟩) (fun g hg u hu => ⟨hRU g hg u hu, ?_⟩)
    · have := hYU g⁻¹ (Y.inv_mem hg) u hu
      rwa [inv_inv] at this
    · have := hRU g⁻¹ (R.inv_mem hg) u hu
      rwa [inv_inv] at this
  have hrX : r ∈ X := ⟨hr, hry⟩
  have hWr : W ≤ centralizer ({r} : Set G) := by
    apply nqSourceModule_le
    intro x hx z hz
    have h1 : x * r * x⁻¹ ∈ U := ((hSP hx) r (le_sup_left (a := X) hrX)).1
    have h2 := (mem_centralizer_iff.mp (hUZ h1)) z hz
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    calc r * (x⁻¹ * z * x) = x⁻¹ * (x * r * x⁻¹ * z) * x := by group
      _ = x⁻¹ * (z * (x * r * x⁻¹)) * x := by rw [h2]
      _ = x⁻¹ * z * x * r := by group
  rw [mem_centralizer_iff]
  intro w hw
  exact ((mem_centralizer_iff.mp (hWr hw)) r (Set.mem_singleton r)).symm

end CFSG.Quasithin.H13.NQBlock
