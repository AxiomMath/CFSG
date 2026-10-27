module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineGen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16tenk_cong_of_spec {K N V : Subgroup G} (hVK : V ≤ K) {a v : G} (hvV : v ∈ V)
    (hv : ∀ k ∈ K, (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ N) :
    ∀ k ∈ K, (a * k * a⁻¹) * (v * k * v⁻¹)⁻¹ ∈ N := by
  intro k hk
  have hkv : v * k * v⁻¹ ∈ K := K.mul_mem (K.mul_mem (hVK hvV) hk) (K.inv_mem (hVK hvV))
  have hmem := hv (v * k * v⁻¹) hkv
  have hkey : (a * v⁻¹) * (v * k * v⁻¹) * (a * v⁻¹)⁻¹ * (v * k * v⁻¹)⁻¹ =
      (a * k * a⁻¹) * (v * k * v⁻¹)⁻¹ := by group
  rwa [hkey] at hmem

private theorem w16tenk_cong_mul {K N V : Subgroup G} (hVK : V ≤ K)
    {a b v v' : G} (haN : a ∈ Subgroup.normalizer (N : Set G)) (hvV : v ∈ V) (hv'V : v' ∈ V)
    (ha : ∀ k ∈ K, (a * k * a⁻¹) * (v * k * v⁻¹)⁻¹ ∈ N)
    (hb : ∀ k ∈ K, (b * k * b⁻¹) * (v' * k * v'⁻¹)⁻¹ ∈ N) :
    ∀ k ∈ K, ((a * b) * k * (a * b)⁻¹) * ((v * v') * k * (v * v')⁻¹)⁻¹ ∈ N := by
  intro k hk
  set m : G := v' * k * v'⁻¹ with hm
  have hmK : m ∈ K := K.mul_mem (K.mul_mem (hVK hv'V) hk) (K.inv_mem (hVK hv'V))
  have h1 : b * k * b⁻¹ * m⁻¹ ∈ N := by simpa [hm] using hb k hk
  have h1' : a * (b * k * b⁻¹ * m⁻¹) * a⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp haN _).mp h1
  have h2 : (a * m * a⁻¹) * (v * m * v⁻¹)⁻¹ ∈ N := ha m hmK
  have hkey : ((a * b) * k * (a * b)⁻¹) * ((v * v') * k * (v * v')⁻¹)⁻¹ =
      (a * (b * k * b⁻¹ * m⁻¹) * a⁻¹) * ((a * m * a⁻¹) * (v * m * v⁻¹)⁻¹) := by
    rw [hm]; group
  rw [hkey]
  exact N.mul_mem h1' h2

private theorem w16tenk_map_mem_center {K N : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : SevenK.IsBarMap K N φ) {d : G} (hdK : d ∈ K)
    (hd : ∀ m ∈ K, d * m * d⁻¹ * m⁻¹ ∈ N) :
    φ ⟨d, hdK⟩ ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨m, rfl⟩ := hφ.surjective x
  have hker : φ (⟨d, hdK⟩ * m * ⟨d, hdK⟩⁻¹ * m⁻¹) = 1 := by
    rw [hφ.ker_iff]
    simpa using hd (m : G) m.2
  have h1 : φ ⟨d, hdK⟩ * φ m * (φ ⟨d, hdK⟩)⁻¹ * (φ m)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using hker
  have h2 : (φ ⟨d, hdK⟩ * φ m) * (φ m * φ ⟨d, hdK⟩)⁻¹ = 1 := by
    rw [mul_inv_rev]
    simpa only [mul_assoc] using h1
  exact (mul_inv_eq_one.mp h2).symm

private theorem w16tenk_barSub_eq_one {K N V : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hVK : V ≤ K) (hφ : SevenK.IsBarMap K N φ)
    (hY : IsElemAbelian 2 (SevenK.barSub K φ V))
    (hodd : Odd (Nat.card (Subgroup.center X))) {d : G} (hdV : d ∈ V)
    (hd : ∀ m ∈ K, d * m * d⁻¹ * m⁻¹ ∈ N) :
    φ ⟨d, hVK hdV⟩ = 1 := by
  have hmem : φ ⟨d, hVK hdV⟩ ∈ SevenK.barSub K φ V :=
    SevenK.mem_barSub.mpr ⟨⟨d, hVK hdV⟩, hdV, rfl⟩
  have hcen : φ ⟨d, hVK hdV⟩ ∈ Subgroup.center X :=
    w16tenk_map_mem_center hφ (hVK hdV) hd
  exact CFSG.CGT.Timmesfeld75.eq_one_of_mem_of_odd_card hY hodd hmem hcen

private theorem w16tenk_conj_mem_of_cong {K N V : Subgroup G} (hVK : V ≤ K) {a v v' : G}
    (hvV : v ∈ V) (hv'V : v' ∈ V)
    (hv : ∀ k ∈ K, (a * k * a⁻¹) * (v * k * v⁻¹)⁻¹ ∈ N)
    (hv' : ∀ k ∈ K, (a * k * a⁻¹) * (v' * k * v'⁻¹)⁻¹ ∈ N) :
    ∀ m ∈ K, (v * v'⁻¹) * m * (v * v'⁻¹)⁻¹ * m⁻¹ ∈ N := by
  intro m hm
  have hk : v'⁻¹ * m * v' ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem (hVK hv'V)) hm) (hVK hv'V)
  have h1 := hv (v'⁻¹ * m * v') hk
  have h2 := hv' (v'⁻¹ * m * v') hk
  have hmem := N.mul_mem (N.inv_mem h1) h2
  have hkey : ((a * (v'⁻¹ * m * v') * a⁻¹) * (v * (v'⁻¹ * m * v') * v⁻¹)⁻¹)⁻¹ *
      ((a * (v'⁻¹ * m * v') * a⁻¹) * (v' * (v'⁻¹ * m * v') * v'⁻¹)⁻¹) =
      (v * v'⁻¹) * m * (v * v'⁻¹)⁻¹ * m⁻¹ := by group
  rwa [hkey] at hmem

private theorem w16tenk_eq_of_cong {K N V : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hVK : V ≤ K) (hφ : SevenK.IsBarMap K N φ)
    (hY : IsElemAbelian 2 (SevenK.barSub K φ V))
    (hodd : Odd (Nat.card (Subgroup.center X))) {a v v' : G} (hvV : v ∈ V) (hv'V : v' ∈ V)
    (hv : ∀ k ∈ K, (a * k * a⁻¹) * (v * k * v⁻¹)⁻¹ ∈ N)
    (hv' : ∀ k ∈ K, (a * k * a⁻¹) * (v' * k * v'⁻¹)⁻¹ ∈ N) :
    φ ⟨v, hVK hvV⟩ = φ ⟨v', hVK hv'V⟩ := by
  have hd : ∀ m ∈ K, (v * v'⁻¹) * m * (v * v'⁻¹)⁻¹ * m⁻¹ ∈ N :=
    w16tenk_conj_mem_of_cong hVK hvV hv'V hv hv'
  have h1 : φ ⟨v * v'⁻¹, hVK (V.mul_mem hvV (V.inv_mem hv'V))⟩ = 1 :=
    w16tenk_barSub_eq_one hVK hφ hY hodd (V.mul_mem hvV (V.inv_mem hv'V)) hd
  have hmul : φ ⟨v, hVK hvV⟩ =
      φ ⟨v * v'⁻¹, hVK (V.mul_mem hvV (V.inv_mem hv'V))⟩ * φ ⟨v', hVK hv'V⟩ := by
    rw [← map_mul]
    congr 1
    ext
    simp only [Subgroup.coe_mul]
    group
  rw [hmul, h1, one_mul]

theorem IsMinFam16.exists_hom_of_comm_mem (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n) {x : G}
    (hxS : conjSubgroup V x ≤ S)
    (h9 : ∀ a ∈ conjSubgroup V x, ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H)) :
    ∃ w : ↥(conjSubgroup V x) →* X, (∀ a, w a ∈ SevenK.barSub (conjClosure V H) φ V) ∧
      ∀ (a : ↥(conjSubgroup V x)) (k k' : ↥(conjClosure V H)),
        (k' : G) = (a : G) * k * (a : G)⁻¹ → φ k' = w a * φ k * (w a)⁻¹ := by
  classical
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hSH : S ≤ H := hH.1.1
  have hAH : conjSubgroup V x ≤ H := hxS.trans hSH
  have hnormK : H ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H
  have hnormN : H ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure V H) : Set G) :=
    hnormK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
      (r := 2) (conjClosure V H))
  have hY : IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) :=
    (h.hyp.h6.elemAbelian.subgroupOf (conjClosure V H)).map φ
  have hgen : normalClosure
      ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ :=
    IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
  have hodd : Odd (Nat.card (Subgroup.center X)) :=
    Shape166.odd_card_center hY hgen hX
  let vOf : ↥(conjSubgroup V x) → G := fun a => Classical.choose (h9 (a : G) a.2)
  have vOf_mem : ∀ a : ↥(conjSubgroup V x), vOf a ∈ V :=
    fun a => (Classical.choose_spec (h9 (a : G) a.2)).1
  have vOf_spec : ∀ a : ↥(conjSubgroup V x), ∀ k ∈ conjClosure V H,
      ((a : G) * (vOf a)⁻¹) * k * ((a : G) * (vOf a)⁻¹)⁻¹ * k⁻¹
        ∈ pCoreOf 2 (conjClosure V H) :=
    fun a => (Classical.choose_spec (h9 (a : G) a.2)).2
  have hcong : ∀ a : ↥(conjSubgroup V x), ∀ k ∈ conjClosure V H,
      ((a : G) * k * (a : G)⁻¹) * (vOf a * k * (vOf a)⁻¹)⁻¹
        ∈ pCoreOf 2 (conjClosure V H) :=
    fun a => w16tenk_cong_of_spec hVK (vOf_mem a) (vOf_spec a)
  have hcong_one : ∀ k ∈ conjClosure V H,
      ((1 : G) * k * (1 : G)⁻¹) * (1 * k * 1⁻¹)⁻¹ ∈ pCoreOf 2 (conjClosure V H) := by
    intro k _
    simpa using (pCoreOf 2 (conjClosure V H)).one_mem
  have hw1 : φ ⟨vOf 1, hVK (vOf_mem 1)⟩ = 1 := by
    have heq := w16tenk_eq_of_cong hVK hφ hY hodd (vOf_mem 1) V.one_mem (hcong 1) hcong_one
    have hone : (⟨(1 : G), hVK V.one_mem⟩ : ↥(conjClosure V H)) = 1 := Subtype.ext rfl
    rw [heq, hone, map_one]
  have hw_mul : ∀ a b : ↥(conjSubgroup V x),
      φ ⟨vOf (a * b), hVK (vOf_mem (a * b))⟩ =
        φ ⟨vOf a, hVK (vOf_mem a)⟩ * φ ⟨vOf b, hVK (vOf_mem b)⟩ := by
    intro a b
    have haH : (a : G) ∈ H := hAH a.2
    have hprod : ∀ k ∈ conjClosure V H,
        (((a : G) * (b : G)) * k * ((a : G) * (b : G))⁻¹) *
          ((vOf a * vOf b) * k * (vOf a * vOf b)⁻¹)⁻¹
            ∈ pCoreOf 2 (conjClosure V H) :=
      w16tenk_cong_mul (K := conjClosure V H) (N := pCoreOf 2 (conjClosure V H))
        (V := V) (a := (a : G)) (b := (b : G)) (v := vOf a) (v' := vOf b)
        hVK (hnormN haH) (vOf_mem a) (vOf_mem b) (hcong a) (hcong b)
    have hleft : ∀ k ∈ conjClosure V H,
        (((a * b : ↥(conjSubgroup V x)) : G) * k *
            (((a * b : ↥(conjSubgroup V x)) : G))⁻¹) *
          (vOf (a * b) * k * (vOf (a * b))⁻¹)⁻¹ ∈ pCoreOf 2 (conjClosure V H) :=
      w16tenk_cong_of_spec hVK (vOf_mem (a * b)) (vOf_spec (a * b))
    have heq := w16tenk_eq_of_cong hVK hφ hY hodd (vOf_mem (a * b))
      (V.mul_mem (vOf_mem a) (vOf_mem b)) hleft hprod
    rw [heq]
    have hsub : (⟨vOf a, hVK (vOf_mem a)⟩ * ⟨vOf b, hVK (vOf_mem b)⟩ :
        ↥(conjClosure V H)) = ⟨vOf a * vOf b, hVK (V.mul_mem (vOf_mem a) (vOf_mem b))⟩ :=
      Subtype.ext rfl
    rw [← hsub]
    exact map_mul φ _ _
  let w : ↥(conjSubgroup V x) →* X :=
    { toFun := fun a => φ ⟨vOf a, hVK (vOf_mem a)⟩
      map_one' := hw1
      map_mul' := hw_mul }
  refine ⟨w, ?_, ?_⟩
  · intro a
    exact SevenK.mem_barSub.mpr ⟨⟨vOf a, hVK (vOf_mem a)⟩, vOf_mem a, rfl⟩
  · intro a k k' hk'
    have hmem : (k' : G) * ((vOf a) * (k : G) * (vOf a)⁻¹)⁻¹
        ∈ pCoreOf 2 (conjClosure V H) := by
      have h := hcong a (k : G) k.2
      rw [← hk'] at h
      exact h
    have hker : φ (k' * (⟨vOf a, hVK (vOf_mem a)⟩ * k * ⟨vOf a, hVK (vOf_mem a)⟩⁻¹)⁻¹) = 1 := by
      rw [hφ.ker_iff]
      simpa using hmem
    have hm_eq : φ k' =
        φ (⟨vOf a, hVK (vOf_mem a)⟩ * k * ⟨vOf a, hVK (vOf_mem a)⟩⁻¹) := by
      have h1 : φ k' * (φ (⟨vOf a, hVK (vOf_mem a)⟩ * k *
          ⟨vOf a, hVK (vOf_mem a)⟩⁻¹))⁻¹ = 1 := by
        have := hker
        rwa [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp h1
    calc φ k'
        = φ (⟨vOf a, hVK (vOf_mem a)⟩ * k * ⟨vOf a, hVK (vOf_mem a)⟩⁻¹) := hm_eq
      _ = φ ⟨vOf a, hVK (vOf_mem a)⟩ * φ k * (φ ⟨vOf a, hVK (vOf_mem a)⟩)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = w a * φ k * (w a)⁻¹ := rfl

end CFSG.LocalAnalysis.WeakClosure81

end
