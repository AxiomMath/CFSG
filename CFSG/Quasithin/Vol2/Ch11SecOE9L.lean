module

public import CFSG.Quasithin.Vol2.Ch11SecOE7L
public import CFSG.Quasithin.Vol2.Ch11SecOE9J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.X6 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin CFSG.Open
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem antiUnipotent_le_parC (i : Axis) : antiUnipotent K ≤ parC K i := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzZ : z ∈ antiUnipotentCenter K := by
    cases i
    · obtain ⟨b, rfl⟩ := hz
      exact ⟨b, 0, rfl⟩
    · obtain ⟨c, rfl⟩ := hz
      exact ⟨0, c, rfl⟩
  exact ((mem_antiUnipotentCenter_iff_central z).mp hzZ).2 g hg

theorem not_le_of_isSolvable (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {G : Type} [Group G]
    {f : antiSp K →* G} (hf : Function.Injective f) (i : Axis) {D : Subgroup G}
    (hD : Group.IsSolvable ↥D) : ¬ (parC K i).map f ≤ D := fun hle =>
  not_isSolvable_parC hK hn i (Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hle).comp
      ((parC K i).equivMapOfInjective f hf).toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _)))

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal] (ψ : antiSp K ≃* ↥L)

theorem isE_parC (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) (hT : IsSylowIn 2 T ⊤)
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (i : Axis)
    (hτ : ∀ t ∈ E1.tauOf ⊤ T A, (rootA K i).map (autHom ψ t).toMonoidHom = rootA K i)
    (hAC : ∃ b ∈ A, ∃ x ∈ parC K i, autHom ψ b x * x⁻¹ ∉ rootA K i) :
    E1.IsE n ⊤ T A ((parC K i).map (emb ψ) ⊔ E1.tauOf ⊤ T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  set X := (parC K i).map (emb ψ) with hX
  obtain ⟨lev, hlev, hker⟩ := exists_leviHom hK hn i
  set eq := (parC K i).equivMapOfInjective (emb ψ) (emb_injective ψ) with heq
  set φ : ↥X →* SL₂ K := lev.comp eq.symm.toMonoidHom with hφ
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (X : Set G) := fun t ht => by
    rw [hX, mem_normalizer_map_emb_iff]
    exact map_parC_of_map_rootA hK hn (hτ t ht)
  have hTX : T ⊓ X = (antiUnipotent K).map (emb ψ) := by
    have hXL : X ≤ L := (Subgroup.map_le_range _ _).trans (range_emb ψ).le
    rw [← inf_eq_right.mpr hXL, ← inf_assoc, inf_eq_map_emb ψ hψ, hX,
      ← Subgroup.map_inf_eq _ _ _ (emb_injective ψ),
      inf_eq_left.mpr (antiUnipotent_le_parC i)]
  have hL : IsSylowIn 2 (T ⊓ X) X := by
    refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
    rw [hTX, hX, Subgroup.relIndex_map_map_of_injective _ _ (emb_injective ψ)]
    intro hd
    have hU := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2.2.2
    apply hU
    rw [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
      Subgroup.relIndex_top_right _, ← Subgroup.relIndex_mul_index (antiUnipotent_le_parC i)]
    exact Dvd.dvd.mul_right hd _
  have hAC' : ¬ ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ φ.ker.map X.subtype := by
    obtain ⟨b, hb, x, hx, hbx⟩ := hAC
    intro hall
    obtain ⟨w, hw, hwx⟩ := hall b hb (emb ψ x) ⟨x, hx, rfl⟩
    apply hbx
    have hw' : ((eq.symm w : ↥(parC K i)) : antiSp K) ∈ rootA K i := by
      have h1 : eq.symm w ∈ lev.ker := hw
      rw [hker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have h2 : emb ψ ((eq.symm w : ↥(parC K i)) : antiSp K) = (w : G) := by
      have h3 := congrArg Subtype.val (eq.apply_symm_apply w)
      rw [← h3]
      rfl
    have h4 : emb ψ (autHom ψ b x * x⁻¹) = ⁅b, emb ψ x⁆ := by
      rw [map_mul, map_inv, emb_autHom, commutatorElement_def]
    rw [← emb_injective ψ (h4.trans (hwx.symm.trans h2.symm))] at hw'
    exact hw'
  have hkerφ : IsPGroup 2 φ.ker := by
    intro w
    refine ⟨1, Subtype.ext (eq.symm.injective (Subtype.ext ?_))⟩
    have h1 : eq.symm (w : ↥X) ∈ lev.ker := w.2
    rw [hker] at h1
    have h2 := mul_self_of_mem_rootA (Subgroup.mem_subgroupOf.mp h1)
    simpa [pow_two] using h2
  exact isE_sup_tauOf_of_quot_sl2 hT hAT hA φ (hlev.comp eq.symm.surjective) hkerφ hK h4 hτN hL
    hAC'

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
