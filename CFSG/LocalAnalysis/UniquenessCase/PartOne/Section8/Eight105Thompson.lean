module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Grow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Transvection
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.Quasithin.EmptyFaithful.A10ConfigurationSetup
import CFSG.Quasithin.EmptyFaithful.S1414Group
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma ncl_le (N X : Subgroup G) (hX : X ≤ N) : ncl N X ≤ N := by
  rw [ncl]
  refine (Subgroup.closure_le N).mpr ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact N.mul_mem (N.mul_mem hg (hX hx)) (N.inv_mem hg)

private lemma ncl_normal (N X : Subgroup G) : N ≤ normalizer (ncl N X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ncl, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨s, ⟨m, hm, x, hx, rfl⟩, rfl⟩
    refine ⟨g * m, N.mul_mem hg hm, x, hx, ?_⟩
    show g * (m * x * m⁻¹) * g⁻¹ = g * m * x * (g * m)⁻¹
    group
  · rintro ⟨m, hm, x, hx, rfl⟩
    refine ⟨(g⁻¹ * m) * x * (g⁻¹ * m)⁻¹,
      ⟨g⁻¹ * m, N.mul_mem (N.inv_mem hg) hm, x, hx, rfl⟩, ?_⟩
    show g * ((g⁻¹ * m) * x * (g⁻¹ * m)⁻¹) * g⁻¹ = m * x * m⁻¹
    group

private def modCentralizer (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) : Subgroup G where
  carrier := {r | r ∈ R ∧ CentMod N₂ Q r}
  one_mem' := by
    refine ⟨R.one_mem, ?_⟩
    intro x _
    simp [CentMod]
  mul_mem' := by
    rintro r s ⟨hrR, hr⟩ ⟨hsR, hs⟩
    refine ⟨R.mul_mem hrR hsR, ?_⟩
    intro x hx
    have hq : r * (s * x * s⁻¹ * x⁻¹) * r⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hNQ (hRN hrR)) _).mp (hs x hx)
    have e : (r * s) * x * (r * s)⁻¹ * x⁻¹ =
        r * (s * x * s⁻¹ * x⁻¹) * r⁻¹ * (r * x * r⁻¹ * x⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq (hr x hx)
  inv_mem' := by
    rintro r ⟨hrR, hr⟩
    refine ⟨R.inv_mem hrR, ?_⟩
    intro x hx
    have hq : r⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * r ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (hNQ (hRN (R.inv_mem hrR))) _).mp
        (Q.inv_mem (hr x hx))
      simpa using h
    have e : r⁻¹ * x * (r⁻¹)⁻¹ * x⁻¹ = r⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * r := by group
    rw [e]
    exact hq

private lemma modCentralizer_le (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) :
    modCentralizer N N₂ Q R hRN hNQ ≤ R := fun _ h => h.1

private lemma modCentralizer_normal (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hN₂ : N ≤ normalizer (N₂ : Set G)) :
    R ≤ normalizer (modCentralizer N N₂ Q R hRN hNQ : Set G) := by
  have key : ∀ s ∈ R, ∀ x ∈ modCentralizer N N₂ Q R hRN hNQ,
      s * x * s⁻¹ ∈ modCentralizer N N₂ Q R hRN hNQ := by
    intro s hs x hx
    obtain ⟨hxR, hxc⟩ := hx
    refine ⟨R.mul_mem (R.mul_mem hs hxR) (R.inv_mem hs), ?_⟩
    intro y hy
    have hy' : s⁻¹ * y * s ∈ N₂ := by
      have h := (Subgroup.mem_normalizer_iff.mp (hN₂ (N.inv_mem (hRN hs))) y).mp hy
      simpa using h
    have hq := hxc _ hy'
    have hconj : s * (x * (s⁻¹ * y * s) * x⁻¹ * (s⁻¹ * y * s)⁻¹) * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hNQ (hRN hs)) _).mp hq
    have e : (s * x * s⁻¹) * y * (s * x * s⁻¹)⁻¹ * y⁻¹ =
        s * (x * (s⁻¹ * y * s) * x⁻¹ * (s⁻¹ * y * s)⁻¹) * s⁻¹ := by group
    rw [e]
    exact hconj
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key s hs x, fun hx => ?_⟩
  have h2 := key s⁻¹ (R.inv_mem hs) (s * x * s⁻¹) hx
  have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
  simpa [e] using h2

private lemma modCentralizer_conj_mem (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hN₂ : N ≤ normalizer (N₂ : Set G))
    (hN₂N : N₂ ≤ N) (hQR : Q ≤ R) :
    N₂ ≤ normalizer (modCentralizer N N₂ Q R hRN hNQ : Set G) := by
  have key : ∀ s ∈ N₂, ∀ x ∈ modCentralizer N N₂ Q R hRN hNQ,
      s * x * s⁻¹ ∈ modCentralizer N N₂ Q R hRN hNQ := by
    intro s hs x hx
    have hsN : s ∈ N := hN₂N hs
    obtain ⟨hxR, hxc⟩ := hx
    have hcomm : s * x * s⁻¹ * x⁻¹ ∈ Q := by
      have e : (x * s * x⁻¹ * s⁻¹)⁻¹ = s * x * s⁻¹ * x⁻¹ := by group
      rw [← e]
      exact Q.inv_mem (hxc s hs)
    refine ⟨?_, ?_⟩
    · have e : s * x * s⁻¹ = (s * x * s⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact R.mul_mem (hQR hcomm) hxR
    · intro z hz
      have hz' : s⁻¹ * z * s ∈ N₂ := by
        have h := (Subgroup.mem_normalizer_iff.mp (hN₂ (N.inv_mem hsN)) z).mp hz
        simpa using h
      have hq := hxc _ hz'
      have hconj : s * (x * (s⁻¹ * z * s) * x⁻¹ * (s⁻¹ * z * s)⁻¹) * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hNQ hsN) _).mp hq
      have e : (s * x * s⁻¹) * z * (s * x * s⁻¹)⁻¹ * z⁻¹ =
          s * (x * (s⁻¹ * z * s) * x⁻¹ * (s⁻¹ * z * s)⁻¹) * s⁻¹ := by group
      rw [e]
      exact hconj
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have h2 := key y⁻¹ (N₂.inv_mem hy) (y * x * y⁻¹) hx
  have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
  simpa [e] using h2

private lemma le_modCentralizer_Q (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hN₂N : N₂ ≤ N) (hQR : Q ≤ R) :
    Q ≤ modCentralizer N N₂ Q R hRN hNQ := by
  intro q hq
  have hqN : q ∈ N := hRN (hQR hq)
  refine ⟨hQR hq, ?_⟩
  intro x hx
  have hxN : x ∈ N := hN₂N hx
  have hxq : x * q⁻¹ * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hNQ hxN) q⁻¹).mp (Q.inv_mem hq)
  have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
  rw [e]
  exact Q.mul_mem hq hxq

private lemma omegaOneCenterIn_eq_omegaOneCenterOf (T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T = CFSG.Quasithin.omegaOneCenterOf T := by
  rw [CFSG.RankThree.PartOne.omegaOneCenterIn, CFSG.Quasithin.omegaOneCenterOf,
    CFSG.Quasithin.omegaOneOf, CFSG.Quasithin.centerOf, CFSG.RankThree.PartOne.omegaOne,
    ← CFSG.centerIn_eq_map_center]
  unfold CFSG.centerIn
  rfl

private lemma omegaOneCenterIn_characteristic (T : Subgroup G) :
    ((CFSG.RankThree.PartOne.omegaOneCenterIn T).subgroupOf T).Characteristic := by
  rw [omegaOneCenterIn_eq_omegaOneCenterOf T]
  exact CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T

private lemma le_centralizer_omegaOneCenterIn (T : Subgroup G) :
    T ≤ Subgroup.centralizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 t ht).symm

private lemma isElemAbelian_omegaOneCenterIn (T : Subgroup G) :
    IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOneCenterIn T) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hb := (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp b.2).2.1
    exact hb a (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T a.2)
  · exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2

private lemma omegaOneCenterIn_le (T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ T :=
  CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T

private lemma normalizer_le_calCGS_of_characteristic {R C : Subgroup G} (hC1 : C ≠ ⊥)
    (hCR : C ≤ R) (hchar : (C.subgroupOf R).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ UC6.calCGS R := by
  rw [UC6.calCGS]
  exact le_iSup_of_le C (le_iSup_of_le hC1 (le_iSup_of_le hCR (le_iSup_of_le hchar le_rfl)))

private lemma centerIn_le_modCentralizer (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hN₂N : N₂ ≤ N) (hQR : Q ≤ R)
    (hchar : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    CFSG.centerIn R ≤ modCentralizer N N₂ Q R hRN hNQ := by
  intro z hz
  obtain ⟨hzR, hzC⟩ := hz
  have hzN : z ∈ N := hRN hzR
  have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp hzC) q (hQR hq)
  have hzQ : z ∈ Q := hchar ⟨hzN, hzCQ⟩
  exact le_modCentralizer_Q N N₂ Q R hRN hNQ hN₂N hQR hzQ

private lemma omegaOneCenterIn_le_of_centerIn_le {A B : Subgroup G}
    (h : CFSG.centerIn A ≤ CFSG.centerIn B) :
    CFSG.RankThree.PartOne.omegaOneCenterIn A ≤
      CFSG.RankThree.PartOne.omegaOneCenterIn B := by
  have h' : (Subgroup.center A).map A.subtype ≤ (Subgroup.center B).map B.subtype := by
    rw [← CFSG.centerIn_eq_map_center, ← CFSG.centerIn_eq_map_center]
    exact h
  unfold CFSG.RankThree.PartOne.omegaOneCenterIn CFSG.RankThree.PartOne.omegaOne
  exact Subgroup.closure_mono fun x hx => ⟨h' hx.1, hx.2⟩

private lemma centerIn_le_centerIn (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hZ : CFSG.centerIn R ≤
      modCentralizer N N₂ Q R hRN hNQ) :
    CFSG.centerIn R ≤ CFSG.centerIn (modCentralizer N N₂ Q R hRN hNQ) := by
  intro z hz
  obtain ⟨hzR, hzC⟩ := hz
  refine ⟨hZ ⟨hzR, hzC⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp hzC) r ((modCentralizer_le N N₂ Q R hRN hNQ) hr)

private lemma inf_centralizer_le_pCoreOf (N N₂ Q V₁ V M : Subgroup G)
    (hN₂V : N₂ ≤ Subgroup.normalizer (V : Set G))
    (hQV : Q ≤ Subgroup.centralizer (V : Set G)) (hV₁V : V₁ ≤ V)
    (hMV₁ : Subgroup.normalizer (V₁ : Set G) ≤ M) (hnot : ¬ N₂ ≤ M)
    (hsimp : ∀ X : Subgroup G, X ≤ N₂ → N₂ ≤ Subgroup.normalizer (X : Set G) →
      X ≤ Q ∨ N₂ ≤ X ⊔ Q) :
    N₂ ⊓ Subgroup.centralizer (V : Set G) ≤ Q := by
  set X := N₂ ⊓ Subgroup.centralizer (V : Set G) with hX
  have hX_le : X ≤ N₂ := inf_le_left
  have hNX : N₂ ≤ Subgroup.normalizer (X : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V (hN₂V hy)⟩
  rcases hsimp X hX_le hNX with h | h
  · exact h
  · exfalso
    have hCV : N₂ ≤ Subgroup.centralizer (V : Set G) :=
      h.trans (sup_le inf_le_right hQV)
    have hCV₁ : N₂ ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hCV hy)) v (hV₁V hv)
    have hNV₁ : N₂ ≤ Subgroup.normalizer (V₁ : Set G) :=
      hCV₁.trans (Subgroup.centralizer_le_normalizer (V₁ : Set G))
    exact hnot (hNV₁.trans hMV₁)
private lemma thompsonJ_normalized_by_ncl {N₂ R R₀ J : Subgroup G}
    (hJ : J = CFSG.Quasithin.thompsonJ R) (hJle : J ≤ R₀) (hR₀R : R₀ ≤ R)
    (hN₂R₀ : N₂ ≤ Subgroup.normalizer (R₀ : Set G)) :
    N₂ ≤ Subgroup.normalizer (J : Set G) := by
  have hle : ∀ y ∈ N₂, (CFSG.Quasithin.thompsonJ R).map
      (MulAut.conj y).toMonoidHom ≤ CFSG.Quasithin.thompsonJ R := by
    intro y hy
    simp only [CFSG.Quasithin.thompsonJ, Subgroup.map_iSup]
    refine iSup₂_le fun A hA => ?_
    have hJle' : CFSG.Quasithin.thompsonJ R ≤ R₀ := hJ ▸ hJle
    have hAR₀ : A ≤ R₀ := (CFSG.Quasithin.B6.le_thompsonJ hA).trans hJle' 
    have hmapR₀ : A.map (MulAut.conj y).toMonoidHom ≤ R₀ := by
      rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hN₂R₀ hy) a).mp (hAR₀ ha)
    have hmapR : A.map (MulAut.conj y).toMonoidHom ≤ R := hmapR₀.trans hR₀R
    exact CFSG.Quasithin.B6.le_thompsonJ
      (CFSG.Quasithin.A10.isMaxElemAbelian_map_conj hA y hmapR)
  have key : ∀ y ∈ N₂, J.map (MulAut.conj y).toMonoidHom ≤ J := by
    intro y hy
    calc J.map (MulAut.conj y).toMonoidHom
        = (CFSG.Quasithin.thompsonJ R).map (MulAut.conj y).toMonoidHom := by rw [hJ]
      _ ≤ CFSG.Quasithin.thompsonJ R := hle y hy
      _ = J := by rw [hJ]
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key y hy) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom)
    (key y⁻¹ (N₂.inv_mem hy))
  rw [Subgroup.map_conj_map_conj, mul_inv_cancel] at h
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
  rwa [hone, Subgroup.map_id] at h

private lemma false_of_thompsonJ_le {N₂ R R₀ J M : Subgroup G}
    (hC : UC6.calCGS R ≤ M) (hJ : J = CFSG.Quasithin.thompsonJ R)
    (hJle : J ≤ R₀) (hR₀R : R₀ ≤ R) (hN₂R₀ : N₂ ≤ Subgroup.normalizer (R₀ : Set G))
    (hJne : J ≠ ⊥) (hJchar : (J.subgroupOf R).Characteristic) (hJR : J ≤ R)
    (hnot : ¬ N₂ ≤ M) : False := by
  have hN₂J : N₂ ≤ Subgroup.normalizer (J : Set G) :=
    thompsonJ_normalized_by_ncl hJ hJle hR₀R hN₂R₀
  have hJM : Subgroup.normalizer (J : Set G) ≤ M :=
    (normalizer_le_calCGS_of_characteristic hJne hJR hJchar).trans hC
  exact hnot (hN₂J.trans hJM)



private lemma card_le_two_mul_card_of_cover (A B : Subgroup G) (hBA : B ≤ A) {t : G}
    (htA : t ∈ A) (hcover : ∀ x ∈ A, x ∈ B ∨ ∃ b ∈ B, x = b * t) :
    Nat.card A ≤ 2 * Nat.card B := by
  let f : ↥B × Fin 2 → ↥A := fun p =>
    ⟨(p.1 : G) * (if p.2 = 0 then 1 else t), by
      have hbA : (p.1 : G) ∈ A := hBA p.1.2
      by_cases h : p.2 = 0
      · simpa [h] using hbA
      · simpa [h] using A.mul_mem hbA htA⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rcases hcover a ha with hb | ⟨b, hbB, rfl⟩
    · refine ⟨(⟨a, hb⟩, 0), Subtype.ext ?_⟩
      simp [f]
    · refine ⟨(⟨b, hbB⟩, 1), Subtype.ext ?_⟩
      simp [f]
  calc Nat.card A ≤ Nat.card (↥B × Fin 2) := Nat.card_le_card_of_surjective f hsurj
    _ = Nat.card B * Nat.card (Fin 2) := Nat.card_prod B (Fin 2)
    _ = 2 * Nat.card B := by simp [Nat.mul_comm]

private lemma card_le_two_mul_card_inf_centralizer {V A B : Subgroup G}
    (hBA : B ≤ A ⊓ Subgroup.centralizer (V : Set G))
    (hcard : Nat.card A ≤ 2 * Nat.card B)
    (hineq : Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :
    Nat.card V ≤ 2 * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have h1 : Nat.card V * Nat.card B ≤
      Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (Subgroup.inclusion hBA)
      (Subgroup.inclusion_injective hBA))
  have h2 : Nat.card V * Nat.card B ≤
      Nat.card B * (2 * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by
    calc Nat.card V * Nat.card B
        ≤ Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
          h1.trans hineq
      _ ≤ (2 * Nat.card B) *
          Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hcard
      _ = Nat.card B *
          (2 * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by ring
  have hcomm : Nat.card B * Nat.card V ≤
      Nat.card B * (2 * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by
    rwa [Nat.mul_comm (Nat.card V) (Nat.card B)] at h2
  exact Nat.le_of_mul_le_mul_left hcomm Nat.card_pos

private lemma card_inf_centralizer_le_of_mem {V A : Subgroup G} {t : G} (ht : t ∈ A) :
    Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤
      Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  refine Nat.card_le_card_of_injective
    (Subgroup.inclusion (show V ⊓ Subgroup.centralizer (A : Set G) ≤
      V ⊓ Subgroup.centralizer ({t} : Set G) from ?_))
    (Subgroup.inclusion_injective _)
  intro x hx
  refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : y = t := by simpa using hy
  subst t
  exact (Subgroup.mem_centralizer_iff.mp hx.2) y ht

private lemma card_inf_centralizer_conj (V : Subgroup G) {g t : G}
    (hV : V.map (MulAut.conj g).toMonoidHom = V) :
    Nat.card (V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  have hmap : (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G).map
      (MulAut.conj g).toMonoidHom =
      V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyV, hyt⟩, rfl⟩
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      · rw [← hV]
        exact Subgroup.mem_map_of_mem _ hyV
      · have hz' : z = g * t * g⁻¹ := by simpa using hz
        subst z
        have h := (Subgroup.mem_centralizer_iff.mp hyt) t (by simp)
        calc (g * t * g⁻¹) * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
          _ = g * (y * t) * g⁻¹ := by rw [h]
          _ = (g * y * g⁻¹) * (g * t * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, ?_⟩
      · rcases Subgroup.mem_map.mp (by rw [hV]; exact hx.1) with ⟨v, hv, hvx⟩
        have e : g⁻¹ * x * g = v := by
          rw [← hvx]
          show g⁻¹ * (g * v * g⁻¹) * g = v
          group
        rwa [e]
      · have hz' : z = t := by simpa using hz
        subst z
        have h := (Subgroup.mem_centralizer_iff.mp hx.2) (g * t * g⁻¹) (by simp)
        calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h]
          _ = (g⁻¹ * x * g) * t := by group
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  rw [← hmap]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

private lemma pow_mul_pow_mem_mul {Q N : Subgroup G} (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    {q g : G} (hq : q ∈ Q) (hg : g ∈ N) (m k : ℕ) :
    ∃ q' ∈ Q, (q * g ^ m) ^ k = q' * g ^ (m * k) := by
  induction k with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨q', hq', hpow⟩ := ih
    refine ⟨q' * (g ^ (m * k) * q * (g ^ (m * k))⁻¹), ?_, ?_⟩
    · exact Q.mul_mem hq' ((Subgroup.mem_normalizer_iff.mp
        (hNQ (N.pow_mem hg (m * k))) q).mp hq)
    · rw [pow_succ, hpow, Nat.mul_succ, pow_add]
      have e : (q' * g ^ (m * k)) * (q * g ^ m) =
          (q' * (g ^ (m * k) * q * (g ^ (m * k))⁻¹)) * (g ^ (m * k) * g ^ m) := by
        group
      rw [e]

private lemma offender_card_le {N₂ Q R R₀ V A : Subgroup G} {t : G}
    (hVR : V ≤ R) (hR₀R : R₀ ≤ R) (hR₀CV : R₀ ≤ Subgroup.centralizer (V : Set G))
    (hA : CFSG.Quasithin.IsMaxElemAbelian R A) (htA : t ∈ A) (htR₀ : t ∉ R₀)
    (hcent : ∀ r ∈ R, (r ∈ R₀ ↔ CentMod N₂ Q r))
    (hidx : ∀ x ∈ R, ∀ y ∈ R, ¬ CentMod N₂ Q x → ¬ CentMod N₂ Q y →
      CentMod N₂ Q (x * y⁻¹))
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1) :
    Nat.card V ≤ 2 * Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  let B : Subgroup G := A ⊓ R₀
  have htR : t ∈ R := hA.1 htA
  have hcover : ∀ x ∈ A, x ∈ B ∨ ∃ b ∈ B, x = b * t := by
    intro x hxA
    by_cases hxR₀ : x ∈ R₀
    · exact Or.inl ⟨hxA, hxR₀⟩
    · right
      have hxR : x ∈ R := hA.1 hxA
      have hxtR : x * t⁻¹ ∈ R := R.mul_mem hxR (R.inv_mem htR)
      have hx_not : ¬ CentMod N₂ Q x := fun hc => hxR₀ ((hcent x hxR).mpr hc)
      have ht_not : ¬ CentMod N₂ Q t := fun hc => htR₀ ((hcent t htR).mpr hc)
      refine ⟨x * t⁻¹, ⟨A.mul_mem hxA (A.inv_mem htA), (hcent _ hxtR).mpr
        (hidx x hxR t htR hx_not ht_not)⟩, by group⟩
  have hAe := hA.2.1
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    (CFSG.Quasithin.B6.isElemAbelian_iff.mp hAe).1
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    simpa [sq] using (CFSG.Quasithin.B6.isElemAbelian_iff.mp hAe).2 a ha
  have hmax : ∀ E : Subgroup G, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E ≤ Nat.card A := by
    intro E hER hab h2
    refine hA.2.2 E hER (CFSG.Quasithin.B6.isElemAbelian_iff.mpr ⟨hab, fun x hx => ?_⟩)
    simpa [sq] using h2 x hx
  have hineq : Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    card_mul_card_le_of_max (R := R) (V := V) (A := A) hVR hA.1 hVab hV2 hAab hA2 hmax
  have hcardA : Nat.card A ≤ 2 * Nat.card B :=
    card_le_two_mul_card_of_cover A B inf_le_left htA hcover
  have hB : B ≤ A ⊓ Subgroup.centralizer (V : Set G) := inf_le_inf_left A hR₀CV
  have h2 := card_le_two_mul_card_inf_centralizer (V := V) hB hcardA hineq
  exact h2.trans (Nat.mul_le_mul_left 2
    (card_inf_centralizer_le_of_mem (V := V) (A := A) htA))

private lemma offender_pow_twelve {V : Subgroup G} {g t : G}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (ht2 : t * t = 1)
    (htcard : Nat.card V ≤
      2 * Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G))
    (ht'card : Nat.card V ≤
      2 * Nat.card (V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) : Subgroup G)) :
    (t * (g * t * g⁻¹)) ^ 12 ∈ Subgroup.centralizer (V : Set G) := by
  have ht'V : g * t * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem hgV htV)
      ((Subgroup.normalizer (V : Set G)).inv_mem hgV)
  have ht'2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  exact pow_twelve_mem_centralizer hVab hV2 htV ht'V ht2 ht'2 htcard ht'card

private lemma offender_g_pow {N N₂ Q V : Subgroup G} {g t : G}
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    (hQV : Q ≤ Subgroup.centralizer (V : Set G)) (hN₂N : N₂ ≤ N) (hg : g ∈ N₂)
    (ht2 : t * t = 1) (hq : t * g * t⁻¹ * g ∈ Q)
    (hpowC : (t * (g * t * g⁻¹)) ^ 12 ∈ Subgroup.centralizer (V : Set G))
    (hCX : N₂ ⊓ Subgroup.centralizer (V : Set G) ≤ Q) :
    g ^ 24 ∈ Q := by
  have hgN : g ∈ N := hN₂N hg
  obtain ⟨q', hq'Q, hpow⟩ := pow_mul_pow_mem_mul hNQ hq (N.inv_mem hgN) 2 12
  have ht_inv : t⁻¹ = t := by
    rw [← mul_one t⁻¹, ← ht2]
    group
  have hq2 : (t * g * t⁻¹ * g) * (g⁻¹) ^ 2 = t * (g * t * g⁻¹) := by
    rw [ht_inv]
    group
  have hpow' : (t * (g * t * g⁻¹)) ^ 12 = q' * (g ^ 24)⁻¹ := by
    rw [← hq2, hpow]
    norm_num [inv_pow]
  have hq'C : q' ∈ Subgroup.centralizer (V : Set G) := hQV hq'Q
  have hprod : q' * (g ^ 24)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [← hpow']
    exact hpowC
  have hinv : (g ^ 24)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have h := (Subgroup.centralizer (V : Set G)).mul_mem
      ((Subgroup.centralizer (V : Set G)).inv_mem hq'C) hprod
    have e : q'⁻¹ * (q' * (g ^ 24)⁻¹) = (g ^ 24)⁻¹ := by group
    rwa [e] at h
  have hg24C : g ^ 24 ∈ Subgroup.centralizer (V : Set G) := by
    have h := (Subgroup.centralizer (V : Set G)).inv_mem hinv
    simpa using h
  exact hCX ⟨N₂.pow_mem hg 24, hg24C⟩

private lemma not_dvd_twentyfour {n : ℕ} (hn : 2 ≤ n) : ¬ (2 ^ (2 * n) + 1) ∣ 24 := by
  intro hdvd
  have heven : Even (2 ^ (2 * n)) :=
    Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) (by omega : 2 * n ≠ 0)
  have hodd : Odd (2 ^ (2 * n) + 1) := heven.add_one
  have hcop : Nat.Coprime (2 ^ (2 * n) + 1) 8 := by
    have h2 : Nat.Coprime (2 ^ (2 * n) + 1) 2 := Nat.coprime_two_right.mpr hodd
    simpa using h2.pow_right 3
  have hdvd' : (2 ^ (2 * n) + 1) ∣ 8 * 3 := by
    rw [show (8 * 3 : ℕ) = 24 by norm_num]
    exact hdvd
  have hdvd3 : (2 ^ (2 * n) + 1) ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd'
  have hle3 : 2 ^ (2 * n) + 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
  have hge : 17 ≤ 2 ^ (2 * n) + 1 := by
    have h4 : 4 ≤ 2 * n := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) h4
    norm_num at hpow ⊢
    omega
  omega

private lemma false_of_offender {N N₂ Q R R₀ V A : Subgroup G} {g t : G} {n : ℕ}
    (hVR : V ≤ R) (hR₀R : R₀ ≤ R) (hR₀C : R₀ ≤ Subgroup.centralizer (V : Set G))
    (hQR₀ : Q ≤ R₀) (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (hN₂N : N₂ ≤ N)
    (hN₂R₀ : N₂ ≤ Subgroup.normalizer (R₀ : Set G))
    (hA : CFSG.Quasithin.IsMaxElemAbelian R A) (htA : t ∈ A) (htR₀ : t ∉ R₀)
    (hcent : ∀ r ∈ R, (r ∈ R₀ ↔ CentMod N₂ Q r))
    (hidx : ∀ x ∈ R, ∀ y ∈ R, ¬ CentMod N₂ Q x → ¬ CentMod N₂ Q y →
      CentMod N₂ Q (x * y⁻¹))
    (hinv : t * g * t⁻¹ * g ∈ Q) (hg : g ∈ N₂)
    (hgo : ∀ k : ℕ, g ^ k ∈ Q → 2 ^ (2 * n) + 1 ∣ k)
    (hCX : N₂ ⊓ Subgroup.centralizer (V : Set G) ≤ Q)
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hN₂V : N₂ ≤ Subgroup.normalizer (V : Set G))
    (hVg : V.map (MulAut.conj g).toMonoidHom = V) (hn : 2 ≤ n) : False := by
  have hcardt := offender_card_le hVR hR₀R hR₀C hA htA htR₀ hcent hidx hVab hV2
  have ht2 : t * t = 1 := by
    simpa [sq] using (CFSG.Quasithin.B6.isElemAbelian_iff.mp hA.2.1).2 t htA
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hRV (hA.1 htA)
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := hN₂V hg
  have hcardt' : Nat.card V ≤
      2 * Nat.card (V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) := by
    rw [card_inf_centralizer_conj V hVg]
    exact hcardt
  have hpowC := offender_pow_twelve hVab hV2 hgV htV ht2 hcardt hcardt'
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := hQR₀.trans hR₀C
  have hg24Q : g ^ 24 ∈ Q := offender_g_pow hNQ hQV hN₂N hg ht2 hinv hpowC hCX
  exact not_dvd_twentyfour hn (hgo 24 hg24Q)

private lemma R0V_facts (N N₂ Q R : Subgroup G) (hRN : R ≤ N)
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    (hN₂norm : N ≤ Subgroup.normalizer (N₂ : Set G)) (hN₂N : N₂ ≤ N)
    (hQR : Q ≤ R) (hcharN : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hR2 : IsPGroup 2 R) (hRne : R ≠ ⊥) :
    let R₀ := modCentralizer N N₂ Q R hRN hNQ
    let V := CFSG.RankThree.PartOne.omegaOneCenterIn R₀
    let V₁ := CFSG.RankThree.PartOne.omegaOneCenterIn R
    (R₀ ≤ R) ∧ (R ≤ Subgroup.normalizer (R₀ : Set G)) ∧
      (N₂ ≤ Subgroup.normalizer (R₀ : Set G)) ∧ (Q ≤ R₀) ∧ (V₁ ≤ V) ∧ (V ≤ R) ∧
      (R₀ ≤ Subgroup.centralizer (V : Set G)) ∧
      (R ≤ Subgroup.normalizer (V : Set G)) ∧
      (N₂ ≤ Subgroup.normalizer (V : Set G)) ∧ (V₁ ≠ ⊥) ∧
      ((V₁.subgroupOf R).Characteristic) ∧ IsElemAbelian 2 V ∧
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, v * v = 1) := by
  dsimp only
  let R₀ : Subgroup G := modCentralizer N N₂ Q R hRN hNQ
  let V : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R₀
  let V₁ : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  have hR₀_le_R : R₀ ≤ R := modCentralizer_le N N₂ Q R hRN hNQ
  have hR₀_normal : R ≤ Subgroup.normalizer (R₀ : Set G) :=
    modCentralizer_normal N N₂ Q R hRN hNQ hN₂norm
  have hN₂R₀ : N₂ ≤ Subgroup.normalizer (R₀ : Set G) :=
    modCentralizer_conj_mem N N₂ Q R hRN hNQ hN₂norm hN₂N hQR
  have hQ_le_R₀ : Q ≤ R₀ := le_modCentralizer_Q N N₂ Q R hRN hNQ hN₂N hQR
  have hZR₀ : CFSG.centerIn R ≤ R₀ :=
    centerIn_le_modCentralizer N N₂ Q R hRN hNQ hN₂N hQR hcharN
  have hZ : CFSG.centerIn R ≤ CFSG.centerIn R₀ :=
    centerIn_le_centerIn N N₂ Q R hRN hNQ hZR₀
  have hV₁_le_V : V₁ ≤ V := omegaOneCenterIn_le_of_centerIn_le hZ
  have hV_le_R₀ : V ≤ R₀ := omegaOneCenterIn_le R₀
  have hV_le_R : V ≤ R := hV_le_R₀.trans hR₀_le_R
  have hR₀_le_CV : R₀ ≤ Subgroup.centralizer (V : Set G) :=
    le_centralizer_omegaOneCenterIn R₀
  have hcharV : ((V.subgroupOf R₀).Characteristic) := omegaOneCenterIn_characteristic R₀
  have hNR₀V : Subgroup.normalizer (R₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic
      (omegaOneCenterIn_le R₀) hcharV
  have hV₁_ne_bot : V₁ ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hR2 hRne
  have hV_el : IsElemAbelian 2 V := isElemAbelian_omegaOneCenterIn R₀
  exact ⟨hR₀_le_R, hR₀_normal, hN₂R₀, hQ_le_R₀, hV₁_le_V, hV_le_R, hR₀_le_CV,
    hR₀_normal.trans hNR₀V, hN₂R₀.trans hNR₀V, hV₁_ne_bot,
    omegaOneCenterIn_characteristic R, hV_el,
    (CFSG.Quasithin.B6.isElemAbelian_iff.mp hV_el).1,
    fun v hv => by simpa [sq] using (CFSG.Quasithin.B6.isElemAbelian_iff.mp hV_el).2 v hv⟩
theorem false_of_action {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ} {g : G}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hC : UC6.calCGS (pCoreOf 2 H) ≤ D.M)
    (hsimp : ∀ X : Subgroup G, X ≤ ncl N B' → ncl N B' ≤ normalizer (X : Set G) →
      X ≤ pCoreOf 2 N ∨ ncl N B' ≤ X ⊔ pCoreOf 2 N)
    (hg : g ∈ ncl N B') (hgo : ∀ k : ℕ, g ^ k ∈ pCoreOf 2 N → 2 ^ (2 * n) + 1 ∣ k)
    (hidx : ∀ r ∈ pCoreOf 2 H, ∀ r' ∈ pCoreOf 2 H, ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
      ¬ CentMod (ncl N B') (pCoreOf 2 N) r' → CentMod (ncl N B') (pCoreOf 2 N) (r * r'⁻¹))
    (hinv : ∀ r ∈ pCoreOf 2 H, ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
      r * g * r⁻¹ * g ∈ pCoreOf 2 N) :
    False := by
  let R : Subgroup G := pCoreOf 2 H
  let Q : Subgroup G := pCoreOf 2 N
  let N₂ : Subgroup G := ncl N B'
  have hRN : R ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.memN.2
  have hN₂N : N₂ ≤ N := ncl_le N B' ((c.le.trans c.memH.2.2.1).trans c.memN.2)
  have hN₂norm : N ≤ Subgroup.normalizer (N₂ : Set G) := ncl_normal N B'
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hR_ne_bot : R ≠ ⊥ := c.memH.2.1
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hcharN : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q :=
    D.standing.charTwo N c.memN.1.1
  let R₀ : Subgroup G := modCentralizer N N₂ Q R hRN hNQ
  let V : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R₀
  let V₁ : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  obtain ⟨hR₀_le_R, hR₀_normal, hN₂R₀, hQ_le_R₀, hV₁_le_V, hV_le_R, hR₀_le_CV,
    hR_le_NV, hN₂_le_NV, hV₁_ne_bot, hV₁_char, hV_el, hVab, hV2⟩ :=
    R0V_facts N N₂ Q R hRN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
      hN₂norm hN₂N (pCoreOf_le_of_calCGS_le c.toCex8105 hC) hcharN hR2 hR_ne_bot
  have hQ_le_CV : Q ≤ Subgroup.centralizer (V : Set G) := hQ_le_R₀.trans hR₀_le_CV
  have hNV₁M : Subgroup.normalizer (V₁ : Set G) ≤ D.M :=
    (normalizer_le_calCGS_of_characteristic hV₁_ne_bot (omegaOneCenterIn_le R) hV₁_char).trans
      hC
  have hCX : N₂ ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
    inf_centralizer_le_pCoreOf N N₂ Q V₁ V D.M hN₂_le_NV hQ_le_CV hV₁_le_V hNV₁M
      (not_ncl_le c) hsimp
  by_cases hJ : CFSG.Quasithin.thompsonJ R ≤ R₀
  · exact false_of_thompsonJ_le hC rfl hJ hR₀_le_R hN₂R₀
      (CFSG.Quasithin.S1414.thompsonJ_ne_bot hR2 hR_ne_bot)
      (CFSG.Quasithin.S1414.characteristic_thompsonJ R)
      (CFSG.Quasithin.B6.thompsonJ_le R) (not_ncl_le c)
  · obtain ⟨A, hA, hA_not⟩ :
        ∃ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian R A ∧ ¬ A ≤ R₀ := by
      by_contra hall
      push Not at hall
      exact hJ (by
        rw [CFSG.Quasithin.thompsonJ]
        exact iSup₂_le fun A hA => hall A hA)
    obtain ⟨t, htA, htR₀⟩ := Set.not_subset.mp hA_not
    have hcent : ∀ r ∈ R, (r ∈ R₀ ↔ CentMod N₂ Q r) := fun r hr =>
      ⟨fun h => h.2, fun hc => ⟨hr, hc⟩⟩
    have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN₂_le_NV hg)
    exact false_of_offender hV_le_R hR₀_le_R hR₀_le_CV hQ_le_R₀ hNQ hN₂N hN₂R₀
      hA htA htR₀ hcent (fun x hx y hy => hidx x hx y hy)
      (hinv t (hA.1 htA) (fun hc => htR₀ ((hcent t (hA.1 htA)).mpr hc)))
      hg hgo hCX hVab hV2 hR_le_NV hN₂_le_NV hVg c.two_le


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
