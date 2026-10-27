module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9DictTor
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModSyl

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_autI {V : Subgroup G} {hV : IsElemAbelian 2 V} {S K : Subgroup G}
    (hSK : S ≤ K) (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hS : IsPGroup 2 S)
    (h1 : IsSylowTwoOf (autI hV S) (autI hV K))
    (h2 : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
      (K ⊓ Subgroup.centralizer (V : Set G))) : IsSylowTwoOf S K := by
  have hcS := card_autI_mul_card_inf hV (hSK.trans hKN)
  have hcK := card_autI_mul_card_inf hV hKN
  refine isSylowTwoOf_of_card_eq hSK hS ?_
  rw [← hcS, h1.card_eq, h2.card_eq]
  unfold twoPart
  rw [← hcK, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [pow_add]

theorem isSylowTwoOf_inf_centralizer_of_le_normalizer {V T M : Subgroup G} (hsyl : IsSylowTwoOf T M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) (M ⊓ Subgroup.centralizer (V : Set G)) := by
  have hMN_N : M ≤ Subgroup.normalizer (M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    fun x hx => le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) hMN hx
  have := A4.isSylowTwoOf_inf_normal hsyl inf_le_left hMN_N
  have hTM : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = T ⊓ Subgroup.centralizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hsyl.1 h.1, h.2⟩⟩
  rwa [hTM] at this

variable {T Mc M : Subgroup G} {hVe : IsElemAbelian 2 (V154 T Mc M)}

theorem sylow_of_refl (d : Six5Data T M (V154 T Mc M) hVe)
    {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)} (r : ReflData T Mc M d x₁ x₂) {Z₁ : Subgroup G}
    (hZ : Z₁ = (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)).map (valHomI hVe)) :
    IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁ ⊓ M) := by
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hτ : d.S.τ ∈ autI hVe M := autI_mono hVe d.hTM d.hτ
  have hTb : IsSylowTwoOf (autI hVe T) (autI hVe M) := isSylowTwoOf_autOn' d.hsyl d.hMN
  have h1 := SixData151b.sylow_ptFix d.S hW d.hcard hTb d.hnorm hτ r.x₁_mem r.x₂_mem r.x₁_two
    r.x₂_two
  have hZV : Z₁ ≤ V154 T Mc M := by
    rw [hZ]
    exact (Subgroup.map_mono inf_le_left).trans d.V₁_le_V
  have hCC : Subgroup.centralizer (V154 T Mc M : Set G) ≤ Subgroup.centralizer (Z₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV)
  have hKN : g1_1516 Z₁ ⊓ M ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    inf_le_right.trans d.hMN
  have hSK : s1516 T Z₁ ≤ g1_1516 Z₁ ⊓ M := fun x hx => ⟨hx.2, d.hTM hx.1⟩
  have hKa : autI hVe (g1_1516 Z₁ ⊓ M) =
      SixData151b.ptFix (autI hVe M) (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) := by
    rw [inf_comm]
    unfold g1_1516
    rw [hZ]
    exact autI_inf_centralizer_map d.hMN _
  have hSa : autI hVe (s1516 T Z₁) =
      autI hVe T ⊓ SixData151b.ptFix (autI hVe M) (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) := by
    have h := autI_inf_centralizer_map (hVe := hVe) (K := T) d.hTN
      (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁))
    rw [← hZ] at h
    unfold s1516
    rw [h]
    ext φ
    constructor
    · rintro ⟨hφ, hfix⟩
      exact ⟨hφ, autI_mono hVe d.hTM hφ, hfix⟩
    · rintro ⟨hφ, -, hfix⟩
      exact ⟨hφ, hfix⟩
  have h1' : IsSylowTwoOf (autI hVe (s1516 T Z₁)) (autI hVe (g1_1516 Z₁ ⊓ M)) := by
    rw [hKa, hSa]
    exact h1
  have hSC : s1516 T Z₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
      T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
    ext x
    simp only [s1516, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCC h.2⟩, h.2⟩⟩
  have hKC : g1_1516 Z₁ ⊓ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
      M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
    ext x
    simp only [g1_1516, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hCC h.2, h.1⟩, h.2⟩⟩
  have h2 : IsSylowTwoOf (s1516 T Z₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
      (g1_1516 Z₁ ⊓ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [hSC, hKC]
    exact isSylowTwoOf_inf_centralizer_of_le_normalizer d.hsyl d.hMN
  exact isSylowTwoOf_of_autI hSK hKN (d.hsyl.2.1.to_le (inf_le_left)) h1' h2

end CFSG.Quasithin.E9
