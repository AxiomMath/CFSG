module

public import CFSG.Quasithin.Vol2.Ch11SecBK9Q
public import CFSG.Quasithin.Vol2.Ch11SecBK9P

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L V U : Subgroup G} [IsMulCommutative ↥V]
  {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4)
  (hLV : L ≤ Subgroup.normalizer (V : Set G)) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
  (hπ : Function.Bijective π) (C : CovData K ↥V)
  (hCpi : ∀ γ, C.pi' γ = ((π γ : ↥(autOn L V)) : MulAut ↥V))
  {Ψ : (Fin 2 ⊕ Fin 2 → K) ≃ (Fin 2 ⊕ Fin 2 → K)}
  (hΨ : ∀ γ a, Ψ (mat 2 K γ *ᵥ a + C.kappa hK γ) = mat 2 K γ *ᵥ Ψ a + bm hK γ)

include hCpi hΨ in
theorem mem_normalizer_iff_rho {U' : Subgroup G} (hU' : U' ≤ V) {a : Fin 2 ⊕ Fin 2 → K}
    (ha : U'.subgroupOf V = C.compl a) (l : ↥L) :
    (l : G) ∈ Subgroup.normalizer (U' : Set G) ↔ rhoL hLV hπ l ∈ stabQ (qOf (Ψ a)) := by
  rw [mem_normalizer_iff_subgroupOf (hLV l.2) hU', ha, ← rhoL_spec hLV hπ l, ← hCpi,
    C.map_compl_eq_iff hK hΨ]

include hK in
theorem exists_compl_conj (hUV : U ≤ V) (hCU : C.U₀ = U.subgroupOf V) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxz : x⁻¹ * (C.z : G) * x = C.z) :
    ∃ a', (U.map (MulAut.conj x).toMonoidHom).subgroupOf V = C.compl a' := by
  have hU2 : U ∈ hypSet V := ⟨hUV, by rw [Subgroup.relIndex, ← hCU, C.index₀]⟩
  refine C.exists_eq_compl hK (map_conj_mem_hypSet hxV hU2).2 fun hz => ?_
  obtain ⟨u, hu, hux⟩ := hz
  apply C.z_not_mem₀
  rw [hCU]
  show ((C.z : ↥V) : G) ∈ U
  have e : u = (C.z : G) := by
    change x * u * x⁻¹ = (C.z : G) at hux
    rw [← hxz, ← hux]
    group
  rwa [← e]

theorem mem_map_conj_iff {H : Subgroup G} (c y : G) :
    y ∈ H.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

include hLV hπ hCpi hΨ in
theorem exists_inv_mul_mem_normalizer (hUV : U ≤ V) (hCU : C.U₀ = U.subgroupOf V) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxz : x⁻¹ * (C.z : G) * x = C.z) :
    ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.normalizer (U : Set G) := by
  have hU'V : U.map (MulAut.conj x).toMonoidHom ≤ V := map_conj_le hxV hUV
  obtain ⟨a', ha'⟩ := exists_compl_conj hK C hUV hCU hxV hxz
  have hU0 : U.subgroupOf V = C.compl 0 := by rw [C.compl_zero, hCU]
  have hcomap : ∀ U'' : Subgroup G, U'' ≤ V → ∀ a, U''.subgroupOf V = C.compl a →
      (stabQ (qOf (Ψ a))).comap (rhoL hLV hπ) =
        (L ⊓ Subgroup.normalizer (U'' : Set G)).subgroupOf L := by
    intro U'' hU'' a ha
    ext l
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      ← mem_normalizer_iff_rho hK hLV hπ C hCpi hΨ hU'' ha l]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have hcardL : ∀ H : Subgroup G, Nat.card ↥((L ⊓ H).subgroupOf L) = Nat.card ↥(L ⊓ H) :=
    fun H => Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmap : (L ⊓ Subgroup.normalizer (U : Set G)).map (MulAut.conj x).toMonoidHom =
      L ⊓ Subgroup.normalizer ((U.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, map_conj_eq_of_mem_normalizer hxL,
      Subgroup.map_equiv_normalizer_eq]
  have hcard : Nat.card ↥(stabQ (qOf (Ψ 0))) = Nat.card ↥(stabQ (qOf (Ψ a'))) := by
    refine card_eq_of_card_comap_eq (rhoL_surjective hLV hπ) ?_
    rw [hcomap U hUV 0 hU0, hcomap _ hU'V a' ha', hcardL, hcardL, ← hmap,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  obtain ⟨γ, hγ⟩ := (C.exists_map_compl_iff hK hΨ 0 a').mpr
    (tr_eq_of_card_stabQ_eq hK hcard).symm
  obtain ⟨l, rfl⟩ := rhoL_surjective hLV hπ γ
  rw [hCpi, rhoL_spec, ← hU0, ← ha', ← subgroupOf_map_conj (hLV l.2) hUV,
    Subgroup.subgroupOf_inj, inf_of_le_left (map_conj_le (hLV l.2) hUV),
    inf_of_le_left hU'V] at hγ
  refine ⟨l, l.2, Subgroup.mem_normalizer_iff.mpr fun g => ?_⟩
  rw [show (l : G)⁻¹ * x * g * ((l : G)⁻¹ * x)⁻¹ = (l : G)⁻¹ * (x * g * x⁻¹) * l by group,
    ← mem_map_conj_iff, hγ, mem_map_conj_iff, show x⁻¹ * (x * g * x⁻¹) * x = g by group]

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
