module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.KGRig

open CFSG.Assembly

theorem mem_range_of_conj_eq {U G : Type*} [Group U] [Group G] {ψ : U →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {a : G} {g : U}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G))
    (hg : ∀ k : U, a * ψ k * a⁻¹ = ψ (g * k * g⁻¹)) :
    a ∈ ψ.range := by
  have hinner : ψ.range.normalizerMonoidHom ⟨a, ha⟩ =
      MulAut.conj (⟨ψ g, ⟨g, rfl⟩⟩ : ψ.range) := by
    ext x
    obtain ⟨k, hk⟩ := x.2
    rw [show x = ⟨ψ k, ⟨k, rfl⟩⟩ from Subtype.ext hk.symm]
    rw [GGRootNorm.coe_normalizerMonoidHom, MulAut.conj_apply, hg k, map_mul, map_mul, map_inv]
    simp
  have h := GGRootNorm.mem_sup_centralizer_of_induced_inner ha hinner
  rw [hC] at h
  simpa using h

theorem exists_levi_conj_eq_of_mem_pCoreOf {U G : Type} [Group U] [Group G]
    {ψ : U →* G} (hψ : Function.Injective ψ) {x₀ : U} {Q L : Subgroup U}
    (hCx : Subgroup.centralizer {x₀} = Q ⊔ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set U))
    (hdisj : Disjoint Q L) (hQ : pCoreOf 2 (Subgroup.centralizer {x₀}) = Q) {a : G}
    (ha : a ∈ pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ x₀}))
    {g : U} {c : U →* U} (hc0 : c x₀ = x₀)
    (hg : ∀ k : U, a * ψ k * a⁻¹ = ψ (g * c k * g⁻¹)) :
    ∃ h ∈ L, ∀ k ∈ L, c k ∈ L → h * c k * h⁻¹ = k := by
  set M : Subgroup G := Subgroup.normalizer (ψ.range : Set G) ⊓
    Subgroup.centralizer {ψ x₀} with hM
  set P : Subgroup G := pCoreOf 2 M with hP
  have hPM : P ≤ M := GGRootNorm.pCoreOf_le M
  have hP2 : IsPGroup 2 P := GGRootNorm.isPGroup_pCoreOf M
  have hMN : M ≤ Subgroup.normalizer (P : Set G) := GGRootNorm.le_normalizer_pCoreOf M
  have hLle : L ≤ Subgroup.centralizer {x₀} := hCx ▸ le_sup_right
  have hCxN : Subgroup.centralizer {x₀} ≤ Subgroup.normalizer (Q : Set U) := by
    rw [← hQ]
    exact GGRootNorm.le_normalizer_pCoreOf _
  have haM : a ∈ M := hPM ha
  have haN : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  have haC : a ∈ Subgroup.centralizer {ψ x₀} := haM.2
  have hgCx : g ∈ Subgroup.centralizer {x₀} := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp haC
    have h0 : ψ (g * x₀ * g⁻¹) = a * ψ x₀ * a⁻¹ := by
      have h := hg x₀
      rw [hc0] at h
      exact h.symm
    have h1 : ψ (g * x₀ * g⁻¹) = ψ x₀ := by
      rw [h0, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : g * x₀ * g⁻¹ = x₀ := hψ h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x₀ = (g * x₀ * g⁻¹) * g := by group
      _ = x₀ * g := by rw [h2]
  let N : Subgroup U := Subgroup.comap ψ P ⊓ Subgroup.centralizer {x₀}
  have hN2 : IsPGroup 2 N := (hP2.comap_of_injective ψ hψ).to_le inf_le_left
  have hNQ : N ≤ Q := by
    rw [← hQ]
    refine GGRootNorm.le_pCoreOf_of_normalized inf_le_right hN2 ?_
    intro m hm t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hψmM : ψ m ∈ M := by
        rw [hM]
        refine ⟨Subgroup.le_normalizer ⟨m, rfl⟩, ?_⟩
        change ψ m ∈ Subgroup.centralizer ({ψ x₀} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff] at hm ⊢
        rw [← map_mul, ← map_mul, hm]
      have hψtP : ψ t ∈ P := ht.1
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hMN hψmM) (ψ t)).mp hψtP
    · exact (Subgroup.centralizer {x₀}).mul_mem
        ((Subgroup.centralizer {x₀}).mul_mem hm ht.2)
        ((Subgroup.centralizer {x₀}).inv_mem hm)
  have hgQL : g ∈ Q ⊔ L := by rw [← hCx]; exact hgCx
  have hgQL' : g ∈ (↑(Q ⊔ L) : Set U) := hgQL
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ] at hgQL'
  obtain ⟨q₀, hq₀, h, hhL, hgeq⟩ := hgQL'
  have hhCx : h ∈ Subgroup.centralizer {x₀} := hLle hhL
  have hψmem : ∀ k : U, k ∈ Subgroup.centralizer {x₀} → ψ k ∈ M := by
    intro k hk
    rw [hM]
    refine ⟨Subgroup.le_normalizer ⟨k, rfl⟩, ?_⟩
    change ψ k ∈ Subgroup.centralizer ({ψ x₀} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    rw [← map_mul, ← map_mul, hk]
  refine ⟨h, hhL, ?_⟩
  intro k hkL hckL
  have hkCx : k ∈ Subgroup.centralizer {x₀} := hLle hkL
  have hckCx : c k ∈ Subgroup.centralizer {x₀} := hLle hckL
  set A : U := h * c k * h⁻¹ with hA
  have hAL : A ∈ L := L.mul_mem (L.mul_mem hhL hckL) (L.inv_mem hhL)
  have hACx : A ∈ Subgroup.centralizer {x₀} :=
    (Subgroup.centralizer {x₀}).mul_mem
      ((Subgroup.centralizer {x₀}).mul_mem hhCx hckCx)
      ((Subgroup.centralizer {x₀}).inv_mem hhCx)
  have hdCx : g * c k * g⁻¹ * k⁻¹ ∈ Subgroup.centralizer {x₀} :=
    (Subgroup.centralizer {x₀}).mul_mem
      ((Subgroup.centralizer {x₀}).mul_mem
        ((Subgroup.centralizer {x₀}).mul_mem hgCx hckCx)
        ((Subgroup.centralizer {x₀}).inv_mem hgCx))
      ((Subgroup.centralizer {x₀}).inv_mem hkCx)
  have hdP : ψ (g * c k * g⁻¹ * k⁻¹) ∈ P := by
    have hψkM : ψ k ∈ M := hψmem k hkCx
    have hgkP : ψ k * a * (ψ k)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hMN hψkM) a).mp ha
    have e : ψ (g * c k * g⁻¹ * k⁻¹) = a * (ψ k * a * (ψ k)⁻¹)⁻¹ := by
      calc ψ (g * c k * g⁻¹ * k⁻¹) = ψ (g * c k * g⁻¹) * ψ k⁻¹ := by
            rw [map_mul, map_inv]
        _ = (a * ψ k * a⁻¹) * (ψ k)⁻¹ := by
            rw [show ψ (g * c k * g⁻¹) = a * ψ k * a⁻¹ from (hg k).symm, map_inv]
        _ = a * (ψ k * a * (ψ k)⁻¹)⁻¹ := by group
    rw [e]
    exact P.mul_mem ha (P.inv_mem hgkP)
  have hdN : g * c k * g⁻¹ * k⁻¹ ∈ N :=
    Subgroup.mem_inf.mpr ⟨hdP, hdCx⟩
  have hconjQ : A * q₀ * A⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hCxN hACx) q₀).mp hq₀
  have hkeyQ : (g * c k * g⁻¹ * k⁻¹) * (A * k⁻¹)⁻¹ ∈ Q := by
    have e : (g * c k * g⁻¹ * k⁻¹) * (A * k⁻¹)⁻¹ =
        q₀ * (A * q₀ * A⁻¹)⁻¹ := by
      rw [← hgeq, hA]
      group
    rw [e]
    exact Q.mul_mem hq₀ (Q.inv_mem hconjQ)
  have hAkQ : A * k⁻¹ ∈ Q := by
    have h1 : (A * k⁻¹)⁻¹ ∈ Q := by
      have h2 := Q.mul_mem (Q.inv_mem (hNQ hdN)) hkeyQ
      have e : (g * c k * g⁻¹ * k⁻¹)⁻¹ *
          ((g * c k * g⁻¹ * k⁻¹) * (A * k⁻¹)⁻¹) = (A * k⁻¹)⁻¹ := by group
      rwa [e] at h2
    simpa using Q.inv_mem h1
  have hAkL : A * k⁻¹ ∈ L := L.mul_mem hAL (L.inv_mem hkL)
  have hone : A * k⁻¹ = 1 := by
    have hb := hdisj.le_bot ⟨hAkQ, hAkL⟩
    simpa using hb
  calc h * c k * h⁻¹ = A := rfl
    _ = k := by
      have h3 : A = (A * k⁻¹) * k := by group
      rw [h3, hone, one_mul]

end CFSG.StandardType.KGRig
