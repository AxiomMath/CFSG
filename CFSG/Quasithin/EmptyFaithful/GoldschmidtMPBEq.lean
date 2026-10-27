module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Lift

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem card_map_eq {X R K L : Subgroup G} (hX : CharTwo X) (hR : IsSylowTwoOf R X)
    (hL : IsBlock2 X L) (hUV : blockU L ≤ VZ R X) (hKL : K ≤ L) {m n : ℕ}
    (α : ↥L →* alternatingGroup (Fin m)) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hK : IsAltQuotient K (Subgroup.centralizer (VZ R X : Set G)) n) :
    Nat.card ((K.subgroupOf L).map α) = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨φ, hφ, hφk⟩ := hK
  let β : ↥K →* alternatingGroup (Fin m) := α.comp (Subgroup.inclusion hKL)
  have hβ : β.ker = φ.ker := by
    ext k
    rw [hφk, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 := L246.centralizer_subgroupOf_eq_pCore hX hR hL hUV
    have h2 : (Subgroup.inclusion hKL k : ↥L) ∈ α.ker ↔
        (k : G) ∈ Subgroup.centralizer (VZ R X : Set G) := by
      rw [hker, ← h1, Subgroup.mem_subgroupOf]
      rfl
    rw [← h2, MonoidHom.mem_ker]
    rfl
  have hrange : (K.subgroupOf L).map α = β.range := by
    ext y
    simp only [Subgroup.mem_map, MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKL k, k.2, rfl⟩
  rw [hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv, hβ,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem eq_of_image_top {X R P K L : Subgroup G} (S : L246C127.Setting X R P K)
    (hL : IsBlock2 X L) (hKL : K ≤ L) {m : ℕ} (α : ↥L →* alternatingGroup (Fin m))
    (hker : α.ker = CFSG.pCore 2 ↥L) (hK : (K.subgroupOf L).map α = ⊤) : K = L := by
  have hQ : ∀ q ∈ α.ker, (q : G) ∈ Subgroup.normalizer (K : Set G) := fun q hq => by
    rw [hker] at hq
    exact S.Q_le_normalizer (A4.pCoreOf_le_of_subnormal 2 (C1GN.isSubnormal_of_isBlock2 hL)
      ((L246.mem_blockQ_iff q).2 hq))
  have hdecomp : ∀ y : ↥L, ∃ k : ↥L, k ∈ K.subgroupOf L ∧ k⁻¹ * y ∈ α.ker := fun y => by
    have hmem : α y ∈ (K.subgroupOf L).map α := by rw [hK]; trivial
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hmem
    exact ⟨k, hk, by rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]⟩
  have hLN : L ≤ Subgroup.normalizer (K : Set G) := fun l hl => by
    obtain ⟨k, hk, hq⟩ := hdecomp ⟨l, hl⟩
    have e : l = (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (hQ _ hq)
  have hnorm : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLN
  have hq2 : IsPGroup 2 (↥L ⧸ K.subgroupOf L) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk, hq⟩ := hdecomp y
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)) ⟨k⁻¹ * y, hker ▸ hq⟩
    refine ⟨j, ?_⟩
    have hj' : (k⁻¹ * y) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk y : ↥L ⧸ K.subgroupOf L) = QuotientGroup.mk (k⁻¹ * y) := by
      rw [QuotientGroup.eq]
      have := hnorm.conj_mem k⁻¹ ((K.subgroupOf L).inv_mem hk) y⁻¹
      simpa [mul_assoc] using this
    rw [hmk, ← QuotientGroup.mk_pow, hj', QuotientGroup.mk_one]
  have htop : K.subgroupOf L = ⊤ := hL.1.1 (K.subgroupOf L) hq2
  exact le_antisymm hKL (fun x hx => (Subgroup.subgroupOf_eq_top.1 htop) hx)

end CFSG.Quasithin.C58NS.MPB
