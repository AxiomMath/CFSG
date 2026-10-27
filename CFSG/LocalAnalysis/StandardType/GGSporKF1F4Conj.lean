module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private theorem gkj_map_centralizer_subgroup {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (Q : Subgroup G) :
    Subgroup.map e.toMonoidHom (Subgroup.centralizer (Q : Set G)) =
      Subgroup.centralizer (Subgroup.map e.toMonoidHom Q : Set G') := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image _ e.toMonoidHom) ?_
  intro y hy
  rw [Subgroup.mem_map]
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  apply e.injective
  rw [map_mul, map_mul, e.apply_symm_apply]
  exact hy (e s) ⟨s, hs, rfl⟩

private theorem gkj_F1At_map {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (p : ℕ) (e : K ≃* K') {x : K} (h : BMPCentralF1At p x) : BMPCentralF1At p (e x) := by
  obtain ⟨hxQ, hcomm, hcen, hle⟩ := h
  have hQ : BMOpCent p (e x) = Subgroup.map e.toMonoidHom (BMOpCent p x) :=
    bmOpCent_map_mulEquiv p e x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
  · rw [hQ, ← Subgroup.map_commutator (BMOpCent p x) (BMOpCent p x) e.toMonoidHom,
      hcomm, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
  · rw [hQ, ← gkj_map_centralizer_subgroup e (BMOpCent p x),
      ← Subgroup.map_inf (BMOpCent p x) (Subgroup.centralizer (BMOpCent p x : Set K))
        e.toMonoidHom e.injective, hcen, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
  · have hmono := Subgroup.map_mono (f := e.toMonoidHom) hle
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x,
      gkj_map_centralizer_subgroup e (BMOpCent p x), ← hQ] at hmono
    exact hmono

private theorem gkj_F4At_map {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (p : ℕ) (e : K ≃* K') {x : K} (h : BMPCentralF4At p x) : BMPCentralF4At p (e x) := by
  intro N' hN'le hN'normal hN'zp hN'Q
  have hQ : BMOpCent p (e x) = Subgroup.map e.toMonoidHom (BMOpCent p x) :=
    bmOpCent_map_mulEquiv p e x
  let N : Subgroup K := Subgroup.comap e.toMonoidHom N'
  have hNmap : Subgroup.map e.toMonoidHom N = N' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N'
  have hNle : N ≤ Subgroup.centralizer ({x} : Set K) := by
    have h1 : Subgroup.map e.toMonoidHom N ≤ Subgroup.centralizer ({e x} : Set K') := by
      rw [hNmap]
      exact hN'le
    have h2 : N ≤ Subgroup.comap e.toMonoidHom (Subgroup.centralizer ({e x} : Set K')) :=
      (Subgroup.map_le_iff_le_comap (f := e.toMonoidHom)).mp h1
    rwa [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x,
      Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  have hNnormal : ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have hg' : e g ∈ Subgroup.centralizer ({e x} : Set K') := by
      rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hn' : e n ∈ N' := hn
    have hstep := hN'normal (e g) hg' (e n) hn'
    change e (g * n * g⁻¹) ∈ N'
    simpa [map_mul] using hstep
  have hNzp : Subgroup.zpowers x ≤ N := by
    intro z hz
    have hz' : e z ∈ Subgroup.zpowers (e x) := by
      have h1 : e z ∈ Subgroup.zpowers (e.toMonoidHom x) := by
        rw [← MonoidHom.map_zpowers e.toMonoidHom x]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rwa [MulEquiv.coe_toMonoidHom] at h1
    have hz'N : e z ∈ N' := hN'zp hz'
    have : e z ∈ Subgroup.map e.toMonoidHom N := by
      rw [hNmap]
      exact hz'N
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp this
  have hNQ : N ≤ BMOpCent p x := by
    have h1 : Subgroup.map e.toMonoidHom N ≤ Subgroup.map e.toMonoidHom (BMOpCent p x) := by
      rw [hNmap, ← hQ]
      exact hN'Q
    have h2 : N ≤ Subgroup.comap e.toMonoidHom (Subgroup.map e.toMonoidHom (BMOpCent p x)) :=
      (Subgroup.map_le_iff_le_comap (f := e.toMonoidHom)).mp h1
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  rcases h N hNle hNnormal hNzp hNQ with hNz | hNQ'
  · left
    rw [← hNmap, hNz, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
  · right
    rw [← hNmap, hNQ']
    exact hQ.symm

private theorem gkj_zpowers_pow_eq {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) {t : K}
    (ht : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0) :
    Subgroup.zpowers (t ^ k) = Subgroup.zpowers t := by
  have hle : Subgroup.zpowers (t ^ k) ≤ Subgroup.zpowers t := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers t k
  have hcop : Nat.Coprime (orderOf t) k := by
    rw [ht]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hk (Nat.mod_eq_zero_of_dvd h)
  have hord : orderOf (t ^ k) = p := by
    rw [Nat.Coprime.orderOf_pow hcop, ht]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hord, ht]

private theorem gkj_centralizer_eq_of_zpowers_eq {K : Type} [Group K] {a b : K}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set K) = Subgroup.centralizer ({b} : Set K) := by
  rw [← Subgroup.centralizer_closure ({a} : Set K), ← Subgroup.centralizer_closure ({b} : Set K),
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, h]

private theorem gkj_bmOpCent_congr {K : Type} [Group K] (p : ℕ) {a b : K}
    (h : Subgroup.centralizer ({a} : Set K) = Subgroup.centralizer ({b} : Set K)) :
    BMOpCent p a = BMOpCent p b := by
  unfold BMOpCent
  rw [h]

private theorem gkj_At_of_pow {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) {t : K}
    (ht : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0)
    (h14 : BMPCentralF1At p t ∧ BMPCentralF4At p t) :
    BMPCentralF1At p (t ^ k) ∧ BMPCentralF4At p (t ^ k) := by
  have hz := gkj_zpowers_pow_eq hp ht hk
  have hC := gkj_centralizer_eq_of_zpowers_eq hz
  have hQ := gkj_bmOpCent_congr p hC
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h14
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hQ]
    exact Subgroup.pow_mem _ h1 k
  · rw [hQ, hz]
    exact h2
  · rw [hQ, hz]
    exact h3
  · rw [hC, hQ]
    exact h4
  · unfold BMPCentralF4At
    rw [hC, hz, hQ]
    exact h5

theorem bmPCentralF1At_F4At_of_conj_pow {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {t s m : K} (ht : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0) (h : m * s * m⁻¹ = t ^ k)
    (h14 : BMPCentralF1At p t ∧ BMPCentralF4At p t) :
    BMPCentralF1At p s ∧ BMPCentralF4At p s := by
  have he : (MulAut.conj m⁻¹ : K ≃* K) (t ^ k) = s := by
    rw [MulAut.conj_apply, ← h]
    group
  obtain ⟨hF1, hF4⟩ := gkj_At_of_pow hp ht hk h14
  rw [← he]
  exact ⟨gkj_F1At_map p (MulAut.conj m⁻¹ : K ≃* K) hF1,
    gkj_F4At_map p (MulAut.conj m⁻¹ : K ≃* K) hF4⟩

end CFSG.StandardType.SporadicShape
