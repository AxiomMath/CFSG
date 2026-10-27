module

public import CFSG.Quasithin.Vol2.Ch10SecE9W
public import CFSG.Quasithin.Vol2.Ch10SecE9ZK
public import CFSG.Quasithin.Vol2.Ch10SecE9ZN

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Quasithin.B5
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def valZ {Z : Subgroup G} (hZ : IsElemAbelian 2 Z) : IntMod Z hZ →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem card_comap_valZ {Z U : Subgroup G} (hZ : IsElemAbelian 2 Z) (hUZ : U ≤ Z) :
    Nat.card ↥(U.comap (valZ hZ)) = Nat.card ↥U := by
  have e : (U.comap (valZ hZ)).map (valZ hZ) = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨IntMod.mk hZ ⟨x, hUZ hx⟩, hx, rfl⟩
  rw [← Subgroup.card_map_of_injective (f := valZ hZ) fun _ _ h => IntMod.val_injective h, e]

theorem card_conjugate_eq {K U : Subgroup G} {t : G}
    (htK : t ∈ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G))
    (hcard : Nat.card ↥U = 8 * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ U)) :
    Nat.card ↥(CFSG.conjugate U t) =
      8 * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ CFSG.conjugate U t) := by
  have hinj : Function.Injective (MulAut.conj t⁻¹).toMonoidHom := (MulAut.conj t⁻¹).injective
  have hCt : (Subgroup.centralizer (K : Set G)).map (MulAut.conj t⁻¹).toMonoidHom =
      Subgroup.centralizer (K : Set G) := SecA.conjugate_eq_self_iff.mpr htK
  have e : Subgroup.centralizer (K : Set G) ⊓ CFSG.conjugate U t =
      CFSG.conjugate (Subgroup.centralizer (K : Set G) ⊓ U) t := by
    rw [SecA.conjugate_eq_map, SecA.conjugate_eq_map, Subgroup.map_inf_eq _ _ _ hinj, hCt]
  rw [e, SecA.conjugate_eq_map, SecA.conjugate_eq_map, Subgroup.card_map_of_injective hinj,
    Subgroup.card_map_of_injective hinj]
  exact hcard

variable [Finite G]

theorem card_sup_fixV_autI {Z K U : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hK : K ≤ Subgroup.normalizer (Z : Set G)) (hUZ : U ≤ Z)
    (hcard : Nat.card ↥U = 8 * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ U)) :
    Nat.card ↥(U.comap (valZ hZ) ⊔ fixV (autI hZ K)) = 8 * Nat.card ↥(fixV (autI hZ K)) := by
  have hinf : U.comap (valZ hZ) ⊓ fixV (autI hZ K) =
      (Subgroup.centralizer (K : Set G) ⊓ U).comap (valZ hZ) := by
    ext u
    rw [Subgroup.mem_inf, mem_fixV_autI_iff hZ hK, Subgroup.mem_comap, Subgroup.mem_comap,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have key := card_sup_mul_card_inf (U.comap (valZ hZ)) (fixV (autI hZ K))
  rw [hinf, card_comap_valZ hZ hUZ,
    card_comap_valZ hZ (U := Subgroup.centralizer (K : Set G) ⊓ U) (inf_le_right.trans hUZ),
    hcard] at key
  have hm : 0 < Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ U) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hm ?_
  rw [key]
  ring

omit [Finite G] in
theorem ptCond_conjugate {T L I P : Subgroup G} {t : G} (hpt : PtCond T L I P)
    (htC : t ∈ Subgroup.normalizer (Subgroup.centralizer (fsuL0 T L : Set G) : Set G))
    (htO : t ∈ Subgroup.normalizer (oTwoUpper P : Set G))
    (htT : t⁻¹ ∈ Subgroup.normalizer (T1 T L : Set G)) :
    ∀ x ∈ oTwoUpper P, ∀ v ∈ CFSG.conjugate (fsuUL T L I) t,
      (∀ s ∈ T1 T L, s * v * s⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) →
      x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  unfold PtCond at hpt
  intro x hx v hv hvS
  rw [SecA.mem_conjugate_iff] at hv
  have hx₁ := (Subgroup.mem_normalizer_iff.mp htO x).mp hx
  have key := hpt _ hx₁ _ hv fun s hs => by
    have hs' := (Subgroup.mem_normalizer_iff.mp htT s).mp hs
    have h1 := (Subgroup.mem_normalizer_iff.mp htC _).mp (hvS _ hs')
    have e : s * (t * v * t⁻¹) * s⁻¹ * (t * v * t⁻¹)⁻¹ =
        t * (t⁻¹ * s * t⁻¹⁻¹ * v * (t⁻¹ * s * t⁻¹⁻¹)⁻¹ * v⁻¹) * t⁻¹ := by group
    rw [e]
    exact h1
  have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htC) _).mp key
  have e : x * v * x⁻¹ * v⁻¹ =
      t⁻¹ * (t * x * t⁻¹ * (t * v * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * v * t⁻¹)⁻¹) * t⁻¹⁻¹ := by
    group
  rw [e]
  exact h2

omit [Finite G] in
theorem fixSec_le_of_cond {Z K B O U : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hK : K ≤ Subgroup.normalizer (Z : Set G)) (hB : B ≤ Subgroup.normalizer (Z : Set G))
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hOK : O ≤ K)
    (hcond : ∀ x ∈ O, ∀ v ∈ U,
      (∀ s ∈ B, s * v * s⁻¹ * v⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    fixSec (autI hZ B) (U.comap (valZ hZ) ⊔ fixV (autI hZ K)) (fixV (autI hZ K)) ≤
      fixSec (autI hZ O) (U.comap (valZ hZ) ⊔ fixV (autI hZ K)) (fixV (autI hZ K)) := by
  set C := fixV (autI hZ K) with hC
  have hCiff : ∀ v : IntMod Z hZ, v ∈ C ↔ v.val ∈ Subgroup.centralizer (K : Set G) :=
    mem_fixV_autI_iff hZ hK
  have hBC : ∀ g : Subgroup.normalizer (Z : Set G), (g : G) ∈ B → ∀ c ∈ C, convI hZ g c ∈ C := by
    intro g hg c hc
    rw [hCiff, convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_centralizer hBK hg) _).mp
      ((hCiff c).mp hc)
  have hsplit : ∀ (ψ : MulAut (IntMod Z hZ)) (a c : IntMod Z hZ),
      ψ (a * c) * (a * c)⁻¹ = (ψ a * a⁻¹) * (ψ c * c⁻¹) := fun ψ a c => by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rintro u ⟨hu, huS⟩
  refine ⟨hu, fun φ hφ => ?_⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
  have haS : ∀ s ∈ B, s * a.val * s⁻¹ * a.val⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro s hs
    have h1 := huS _ (convI_mem_autI hZ hs (hB hs))
    rw [hsplit] at h1
    have h2 := C.mul_mem h1 (C.inv_mem (C.mul_mem (hBC ⟨s, hB hs⟩ hs c hc) (C.inv_mem hc)))
    rw [mul_inv_cancel_right] at h2
    have h3 := (hCiff _).mp h2
    rwa [IntMod.val_mul, IntMod.val_inv, convI_apply_val] at h3
  obtain ⟨g, hg, rfl⟩ := (mem_autI hZ).mp hφ
  have hgc : convI hZ g c = c := mem_fixV.mp hc _ (autI_mono hZ hOK (convI_mem_autI hZ hg g.2))
  rw [hsplit, hgc, mul_inv_cancel, mul_one, hCiff, IntMod.val_mul, IntMod.val_inv,
    convI_apply_val]
  exact hcond _ hg a.val ha haS

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
