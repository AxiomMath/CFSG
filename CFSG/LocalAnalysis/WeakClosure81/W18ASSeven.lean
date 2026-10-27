module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLift
public import CFSG.LocalAnalysis.WeakClosure81.W18ASBasic
public import CFSG.LocalAnalysis.WeakClosure81.W18Seven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (InCalA)

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (X : Set G))
    (K := Subgroup.normalizer (X : Set G))
    (Subgroup.centralizer_le_normalizer (X : Set G))

private theorem conjSub_centralizer (g : G) (X : Subgroup G) :
    A1b.conjSub g (Subgroup.centralizer (X : Set G)) =
      Subgroup.centralizer ((A1b.conjSub g X : Subgroup G) : Set G) := by
  ext y
  rw [A1b.mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have h1 := h (g⁻¹ * z * g) (A1b.mem_conjSub_iff.mp hz)
    calc z * y = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
      _ = y * z := by group
  · intro h x hx
    have h1 := h (g * x * g⁻¹) (A1b.mem_conjSub_of_mem hx)
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * y * g) * x := by group

private theorem conjSub_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : A1b.conjSub g X = X := by
  simpa [A1b.conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

private theorem conjSub_inf_centralizer {H E : Subgroup G} {h : G} (hh : h ∈ H)
    (hEH : H ≤ Subgroup.normalizer (E : Set G)) :
    A1b.conjSub h (H ⊓ Subgroup.centralizer (E : Set G)) =
      H ⊓ Subgroup.centralizer (E : Set G) := by
  rw [show A1b.conjSub h (H ⊓ Subgroup.centralizer (E : Set G)) =
      A1b.conjSub h H ⊓ A1b.conjSub h (Subgroup.centralizer (E : Set G)) from
    Subgroup.map_inf H (Subgroup.centralizer (E : Set G)) (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective,
    conjSub_eq_self_of_mem_normalizer (H.le_normalizer hh), conjSub_centralizer,
    conjSub_eq_self_of_mem_normalizer (hEH hh)]

private theorem inf_centralizer_sup_eq_of_le_centralizer {E X C : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer (C : Set G)) :
    E ⊓ Subgroup.centralizer ((X ⊔ C : Subgroup G) : Set G) =
      E ⊓ Subgroup.centralizer (X : Set G) := by
  refine le_antisymm ?_ ?_
  · exact inf_le_inf_left E (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (le_sup_left : X ≤ X ⊔ C)))
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hcl : (X ⊔ C : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hx.2 y hy
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hEC hx.1) z hz
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [← Subgroup.mem_centralizer_singleton_iff]
      exact hcl hy

private theorem relIndex_sup_sup_le {H A B C : Subgroup G} (hAH : A ≤ H) (hCH : C ≤ H)
    (hBA : B ≤ A) (hCn : (C.subgroupOf H).Normal) :
    (B ⊔ C).relIndex (A ⊔ C) ≤ B.relIndex A := by
  have hBH : B ≤ H := hBA.trans hAH
  have hBA' : B.subgroupOf H ≤ A.subgroupOf H := by
    intro x hx
    exact hBA (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hkey := CFSG.ABGLocalTools.relIndex_sup_dvd_relIndex (H := ↥H)
    (A := B.subgroupOf H) (B := A.subgroupOf H) (K := C.subgroupOf H) hBA'
  rw [← Subgroup.subgroupOf_sup hBH hCH, ← Subgroup.subgroupOf_sup hAH hCH] at hkey
  rw [Subgroup.relIndex_subgroupOf (H := B ⊔ C) (K := A ⊔ C) (L := H) (sup_le hAH hCH),
    Subgroup.relIndex_subgroupOf (H := B) (K := A) (L := H) hAH] at hkey
  exact Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf A))) hkey

private theorem inCalA_conjSub {k : ℕ} {H E A : Subgroup G}
    (hEH : H ≤ Subgroup.normalizer (E : Set G)) {h : G} (hh : h ∈ H)
    (hA : InCalA k H E A) : InCalA k H E (A1b.conjSub h A) := by
  have hE : A1b.conjSub h E = E := conjSub_eq_self_of_mem_normalizer (hEH hh)
  have hH : A1b.conjSub h H = H := conjSub_eq_self_of_mem_normalizer (H.le_normalizer hh)
  have hconjC : A1b.conjSub h (H ⊓ Subgroup.centralizer (E : Set G)) =
      H ⊓ Subgroup.centralizer (E : Set G) := conjSub_inf_centralizer hh hEH
  have hconjC' : A1b.conjSub h⁻¹ (H ⊓ Subgroup.centralizer (E : Set G)) =
      H ⊓ Subgroup.centralizer (E : Set G) := conjSub_inf_centralizer (H.inv_mem hh) hEH
  have hh'inv : h⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).inv_mem (hEH hh)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hconjC]
    exact A1b.conjSub_mono h hA.1
  · exact (A1b.conjSub_mono h hA.2.1).trans_eq hH
  · intro hle
    have hc : A1b.conjSub h⁻¹ (Subgroup.centralizer (E : Set G)) =
        Subgroup.centralizer (E : Set G) := by
      rw [conjSub_centralizer, conjSub_eq_self_of_mem_normalizer hh'inv]
    have hle' : A1b.conjSub h⁻¹ (A1b.conjSub h A) ≤
        A1b.conjSub h⁻¹ (Subgroup.centralizer (E : Set G)) := A1b.conjSub_mono h⁻¹ hle
    rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, hc] at hle'
    exact hA.2.2.1 hle'
  · rintro x hx y hy
    have hx' : h⁻¹ * x * h ∈ A := A1b.mem_conjSub_iff.mp hx
    have hy' : h⁻¹ * y * h ∈ A := A1b.mem_conjSub_iff.mp hy
    have hz := hA.2.2.2.1 _ hx' _ hy'
    have hmem : h * (h⁻¹ * x * h * (h⁻¹ * y * h) * (h⁻¹ * x * h)⁻¹ *
        (h⁻¹ * y * h)⁻¹) * h⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
      have h1 := A1b.mem_conjSub_of_mem (g := h) hz
      rwa [conjSub_centralizer, hE] at h1
    have he : x * y * x⁻¹ * y⁻¹ = h * (h⁻¹ * x * h * (h⁻¹ * y * h) *
        (h⁻¹ * x * h)⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ := by group
    rw [he]; exact hmem
  · rintro x hx
    have hx' : h⁻¹ * x * h ∈ A := A1b.mem_conjSub_iff.mp hx
    have hz := hA.2.2.2.2.1 _ hx'
    have hmem : h * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) * h⁻¹ ∈
        Subgroup.centralizer (E : Set G) := by
      have h1 := A1b.mem_conjSub_of_mem (g := h) hz
      rwa [conjSub_centralizer, hE] at h1
    have he : x * x = h * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) * h⁻¹ := by group
    rw [he]; exact hmem
  · intro B hCB hBA hr
    set B₀ : Subgroup G := A1b.conjSub h⁻¹ B with hB₀
    have hCB₀ : H ⊓ Subgroup.centralizer (E : Set G) ≤ B₀ := by
      rw [hB₀, ← hconjC']
      exact A1b.conjSub_mono h⁻¹ hCB
    have hBA₀ : B₀ ≤ A := by
      rw [hB₀]
      refine (A1b.conjSub_mono h⁻¹ hBA).trans_eq ?_
      rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    have hr₀ : B₀.relIndex A < 2 ^ k := by
      have h : B₀.relIndex A = B.relIndex (A1b.conjSub h A) := by
        have h1 := Subgroup.relIndex_map_map_of_injective
          (f := (MulAut.conj h⁻¹).toMonoidHom) B (A1b.conjSub h A)
          (MulAut.conj h⁻¹).injective
        have h2 : (A1b.conjSub h A).map (MulAut.conj h⁻¹).toMonoidHom = A := by
          show A1b.conjSub h⁻¹ (A1b.conjSub h A) = A
          rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
        rw [h2] at h1
        rw [show B₀ = B.map (MulAut.conj h⁻¹).toMonoidHom from hB₀]
        exact h1
      rw [h]; exact hr
    have heq := hA.2.2.2.2.2 B₀ hCB₀ hBA₀ hr₀
    have hsrc : E ⊓ Subgroup.centralizer ((A1b.conjSub h A : Subgroup G) : Set G) =
        A1b.conjSub h (E ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [show A1b.conjSub h (E ⊓ Subgroup.centralizer (A : Set G)) =
          A1b.conjSub h E ⊓ A1b.conjSub h (Subgroup.centralizer (A : Set G)) from
        Subgroup.map_inf E (Subgroup.centralizer (A : Set G)) (MulAut.conj h).toMonoidHom
          (MulAut.conj h).injective,
        hE, conjSub_centralizer]
    have htgt : E ⊓ Subgroup.centralizer (B : Set G) =
        A1b.conjSub h (E ⊓ Subgroup.centralizer (B₀ : Set G)) := by
      have hB : A1b.conjSub h B₀ = B := by
        rw [hB₀, ← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
      rw [show A1b.conjSub h (E ⊓ Subgroup.centralizer (B₀ : Set G)) =
          A1b.conjSub h E ⊓ A1b.conjSub h (Subgroup.centralizer (B₀ : Set G)) from
        Subgroup.map_inf E (Subgroup.centralizer (B₀ : Set G)) (MulAut.conj h).toMonoidHom
          (MulAut.conj h).injective,
        hE, conjSub_centralizer, hB]
    rw [hsrc, heq, htgt]

theorem four_seven_of_inFSqAS {j k : ℕ} (hjk : j < k) {H T E A : Subgroup G}
    (hT : IsSylowIn 2 T H) (hF : InFSqAS j H) (hEH : H ≤ normalizer (E : Set G))
    (hO : pCoreOf 2 H ≤ centralizer (E : Set G)) (hAH : A ≤ H) (hAab : IsElemAbelian 2 A)
    (hA : InCalA k H E (A ⊔ (H ⊓ centralizer (E : Set G)))) :
    H ≤ centralizer ((E ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  classical
  set C : Subgroup G := H ⊓ centralizer (E : Set G) with hC
  set M₀ : Subgroup G :=
    centralizer ((E ⊓ centralizer (T : Set G) : Subgroup G) : Set G) with hM₀
  by_contra hHM
  have hTM : T ≤ M₀ := by
    intro t ht
    rw [hM₀, Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Subgroup.centralizer (T : Set G) := by
      have hmem : x ∈ (E ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := hx
      exact (Subgroup.mem_inf.mp hmem).2
    exact (Subgroup.mem_centralizer_iff.mp hx' t ht).symm
  have hnotA : ¬ A ≤ pCoreOf 2 H := by
    intro hAp
    exact hA.2.2.1 (sup_le (hAp.trans hO) inf_le_right)
  let Ω : Set (Subgroup G) := {B | ∃ h ∈ H, B = A1b.conjSub h A}
  have hΩ : E1.IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro B ⟨h, hh, rfl⟩ x hx
      have hx' : h⁻¹ * x * h ∈ A := A1b.mem_conjSub_iff.mp hx
      simpa [mul_assoc] using H.mul_mem (H.mul_mem hh (hAH hx')) (H.inv_mem hh)
    · rintro B ⟨h, hh, rfl⟩
      exact hAab.map (MulAut.conj h).toMonoidHom
    · rintro B ⟨h, hh, rfl⟩ g hg
      exact ⟨g * h, H.mul_mem hg hh, (A1b.conjSub_mul g h A).symm⟩
  have hAΩ : A ∈ Ω := ⟨1, H.one_mem, (A1b.conjSub_one A).symm⟩
  obtain ⟨A₁, hA₁Ω, hA₁T, K, hK, hKM⟩ :=
    exists_isE_not_le_of_inFSqAS hT hF hTM hHM hΩ ⟨A, hAΩ, hnotA⟩
  have hA₁H : A₁ ≤ H := hΩ.le A₁ hA₁Ω
  have hA₁ab : IsElemAbelian 2 A₁ := hΩ.isElemAbelian A₁ hA₁Ω
  obtain ⟨h, hh, hA₁eq⟩ := hA₁Ω
  have hconjC : A1b.conjSub h C = C := by
    rw [hC]
    exact conjSub_inf_centralizer hh hEH
  have hsup : A1b.conjSub h (A ⊔ C) = A₁ ⊔ C := by
    rw [show A1b.conjSub h (A ⊔ C) = A1b.conjSub h A ⊔ A1b.conjSub h C from
      Subgroup.map_sup A C (MulAut.conj h).toMonoidHom, ← hA₁eq, hconjC]
  have hA₁cal : InCalA k H E (A₁ ⊔ C) := by
    have h' : InCalA k H E (A1b.conjSub h (A ⊔ C)) := inCalA_conjSub hEH hh hA
    rwa [hsup] at h'
  set B : Subgroup G := A₁ ⊓ pCoreOf 2 K with hB
  have hBA : B ≤ A₁ := by rw [hB]; exact inf_le_left
  have hpCoreK : pCoreOf 2 K ≤ T :=
    (E1.pCoreOf_two_le_of_isSylowIn hK.2.2.1).trans inf_le_left
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hC]
    exact (le_inf H.le_normalizer
      (hEH.trans (normalizer_le_normalizer_centralizer E))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hCnorm : (C.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHC
  have hBrel : B.relIndex A₁ ≤ 2 ^ j := by
    have hcard := (E3.card_le_of_isE hT hA₁T hA₁ab hK).2
    have hmul := Subgroup.relIndex_mul_card (H := B) (K := A₁)
    rw [inf_of_le_left hBA] at hmul
    have hcard' : Nat.card A₁ ≤ 2 ^ j * Nat.card B := by
      rw [hB]; exact hcard
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := B))
    calc B.relIndex A₁ * Nat.card B = Nat.card A₁ := hmul
      _ ≤ 2 ^ j * Nat.card B := hcard'
  have hrelB : (B ⊔ C).relIndex (A₁ ⊔ C) < 2 ^ k := by
    have h1 := relIndex_sup_sup_le (H := H) (A := A₁) (B := B) (C := C) hA₁H
      (by rw [hC]; exact inf_le_left) hBA hCnorm
    exact lt_of_le_of_lt (h1.trans hBrel) (Nat.pow_lt_pow_right (by norm_num) hjk)
  have hEC : E ≤ Subgroup.centralizer (C : Set G) := by
    rw [hC]
    exact Subgroup.le_centralizer_iff.mpr inf_le_right
  have hfixB : E ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G) =
      E ⊓ Subgroup.centralizer (A₁ : Set G) := by
    have hcl := hA₁cal.2.2.2.2.2 (B ⊔ C) (by rw [← hC]; exact le_sup_right)
      (sup_le (hBA.trans le_sup_left) le_sup_right) hrelB
    calc E ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G)
        = E ⊓ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) :=
          (inf_centralizer_sup_eq_of_le_centralizer hEC).symm
      _ = E ⊓ Subgroup.centralizer ((A₁ ⊔ C : Subgroup G) : Set G) := hcl.symm
      _ = E ⊓ Subgroup.centralizer (A₁ : Set G) :=
          inf_centralizer_sup_eq_of_le_centralizer hEC
  set U : Subgroup G := CFSG.Quasithin.conjClosure (E ⊓ centralizer (T : Set G)) K with hU
  have hUE : U ≤ E := by
    rw [hU]
    refine CFSG.Quasithin.conjClosure_le ?_
    intro k hk z hz
    exact (Subgroup.mem_normalizer_iff.mp (hEH (hK.1 hk)) z).mp hz.1
  have hUcentB : U ≤ Subgroup.centralizer (B : Set G) := by
    rw [hU]
    refine CFSG.Quasithin.conjClosure_le ?_
    intro k hk z hz
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hB] at hb
    rw [Subgroup.mem_inf] at hz
    obtain ⟨-, hbO⟩ := Subgroup.mem_inf.mp hb
    have hbk : k⁻¹ * b * k ∈ pCoreOf 2 K := by
      have hkn : k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K (K.inv_mem hk)
      simpa using (Subgroup.mem_normalizer_iff.mp hkn b).mp hbO
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz.2) (k⁻¹ * b * k) (hpCoreK hbk)
    calc b * (k * z * k⁻¹) = k * ((k⁻¹ * b * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * b * k)) * k⁻¹ := by rw [hcomm]
      _ = (k * z * k⁻¹) * b := by group
  have hUcentA : U ≤ Subgroup.centralizer (A₁ : Set G) := by
    have h1 : U ≤ E ⊓ Subgroup.centralizer (B : Set G) := le_inf hUE hUcentB
    rw [hfixB] at h1
    exact h1.trans inf_le_right
  have hA₁centU : A₁ ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mpr hUcentA
  have hclCentU : CFSG.Quasithin.conjClosure A₁ K ≤ Subgroup.centralizer (U : Set G) := by
    refine CFSG.Quasithin.conjClosure_le ?_
    intro k hk z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hkU : k ∈ Subgroup.normalizer (U : Set G) := by
      rw [hU]
      exact CFSG.Quasithin.le_normalizer_conjClosure (E ⊓ centralizer (T : Set G)) K hk
    have hku : k⁻¹ * u * k ∈ U := by
      have hkU' : k⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        (Subgroup.normalizer (U : Set G)).inv_mem hkU
      simpa using (Subgroup.mem_normalizer_iff.mp hkU' u).mp hu
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hA₁centU hz)) (k⁻¹ * u * k) hku
    calc u * (k * z * k⁻¹) = k * ((k⁻¹ * u * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * u * k)) * k⁻¹ := by rw [hcomm]
      _ = (k * z * k⁻¹) * u := by group
  have htwoRes : twoResidual K ≤ Subgroup.centralizer (U : Set G) :=
    (E1.twoResidual_le_conjClosure (⟨j, hK⟩ : E1.IsEAny H T A₁ K)).trans hclCentU
  have hcentU : Subgroup.centralizer (U : Set G) ≤ M₀ := by
    rw [hM₀]
    exact Subgroup.centralizer_le
      (CFSG.Quasithin.le_conjClosure (E ⊓ centralizer (T : Set G)) K)
  exact hKM (by
    rw [← CFSG.Quasithin.sup_twoResidual_eq (H := K) (T := T ⊓ K) hK.2.2.1]
    exact sup_le (inf_le_left.trans hTM) (htwoRes.trans hcentU))


namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem not_inCalA_of_inFSqAS {j k : ℕ} (hjk : j < k) (h : Hyp183 D V₀ V H i)
    (hF : InFSqAS j H) {A : Subgroup G} (hAH : A ≤ H) (hAab : IsElemAbelian 2 A) :
    ¬ InCalA k H (eOmegaZ H D.T) (A ⊔ (H ⊓ centralizer (eOmegaZ H D.T : Set G))) := by
  intro hA
  have hfix := four_seven_of_inFSqAS hjk h.isSylowIn_T hF (Hyp183.normalizer_eOmegaZ H D.T)
    h.pCoreOf_le_centralizer_eOmegaZ hAH hAab hA
  have hHE := h.le_centralizer_eOmegaZ_of_fix hfix
  exact hA.2.2.1 (sup_le (hAH.trans hHE) inf_le_right)

end Hyp183

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem inFSqAS_one (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) : InFSqAS 1 H := by
  obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := c.hyps_5_13 h1
  rcases (h5_13 G H D.T hK hT hTlt h3 hno hne).2 with h | h
  · exact h
  · exact absurd h (c.not_shape512Four_AS h5_11 h5_13 h1)

theorem inFSqAS_lt_three (h5_11 : Asch5_11AS) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) : ∃ j : ℕ, j < 3 ∧ InFSqAS j H := by
  obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := c.hyps_5_11 h2
  rcases (h5_11 G H D.T hK hT hTlt hno hne hp).2 with h | ⟨h, -⟩
  · exact ⟨1, by norm_num, h⟩
  · exact ⟨2, by norm_num, h⟩

theorem not_inCalA_two_AS (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) {A : Subgroup G}
    (hAH : A ≤ H) (hAab : IsElemAbelian 2 A) :
    ¬ InCalA 2 H (eOmegaZ H D.T) (A ⊔ (H ⊓ centralizer (eOmegaZ H D.T : Set G))) :=
  c.hyp.not_inCalA_of_inFSqAS (by norm_num : 1 < 2) (c.inFSqAS_one h5_11 h5_13 h1) hAH hAab

theorem not_inCalA_three_AS (h5_11 : Asch5_11AS) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {A : Subgroup G} (hAH : A ≤ H) (hAab : IsElemAbelian 2 A) :
    ¬ InCalA 3 H (eOmegaZ H D.T) (A ⊔ (H ⊓ centralizer (eOmegaZ H D.T : Set G))) := by
  obtain ⟨j, hj, hF⟩ := c.inFSqAS_lt_three h5_11 h2
  exact c.hyp.not_inCalA_of_inFSqAS hj hF hAH hAab

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
