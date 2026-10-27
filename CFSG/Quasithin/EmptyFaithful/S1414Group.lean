module

public import CFSG.Quasithin.EmptyFaithful.S1417Setup
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1414

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem characteristic_thompsonJ (S : Subgroup G) :
    ((thompsonJ S).subgroupOf S).Characteristic := by
  have h : (thompsonJ S).subgroupOf S = thompsonJ (⊤ : Subgroup S) := by
    rw [C1GN.thompsonJ_eq_map_top S, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  rw [h]
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [thompsonJ_map_mulEquiv φ, C1GN.map_top_mulEquiv]

omit [Finite G] in
theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := by
  refine le_inf (C1GN.thompsonJ_le T) fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heC : e ∈ Subgroup.centralizer (thompsonJ T : Set G) :=
    (C1GN.omegaOneCenterOf_le_centerOf (thompsonJ T) he).2
  exact (Subgroup.mem_centralizer_iff.mp heC x hx).symm

theorem thompsonJ_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    thompsonJ T ≠ ⊥ := by
  intro hbot
  have hZ : quasithinOmegaOneCenter T ≤ thompsonJ T :=
    (S1417.omegaOneCenter_le_omegaOneCenterOf T).trans (C1GN.omegaOneCenterOf_le_self _)
  exact quasithinOmegaOneCenter_ne_bot hT2 hT1 (le_bot_iff.mp (hbot ▸ hZ))

theorem normalizer_thompsonJ_le_CGS {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ CGS (baum T) := by
  have hJb : thompsonJ T ≤ baum T := thompsonJ_le_baum T
  have hchar : ((thompsonJ T).subgroupOf (baum T)).Characteristic := by
    have heq : thompsonJ (baum T) = thompsonJ T := B6.thompsonJ_eq_of_le hJb inf_le_left
    have := characteristic_thompsonJ (baum T)
    rwa [heq] at this
  exact le_iSup_of_le (thompsonJ T) (le_iSup_of_le hJb (le_iSup_of_le (thompsonJ_ne_bot hT2 hT1)
    (le_iSup_of_le hchar le_rfl)))

theorem frattini_decomp {M₁ N T : Subgroup G} (hT : IsSylowTwoOf T M₁) (hNM : N ≤ M₁)
    (hMN : M₁ ≤ Subgroup.normalizer (N : Set G)) (hJN : thompsonJ T ≤ N) :
    ∀ x ∈ M₁, ∃ n ∈ N, ∃ y ∈ M₁ ⊓ Subgroup.normalizer (thompsonJ T : Set G), x = n * y := by
  intro x hx
  have hS : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal hT hNM hMN
  have hx' := B6.frattini_two hNM hMN hS hx
  have hle : M₁ ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) ≤
      Subgroup.normalizer (N : Set G) := inf_le_left.trans hMN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N _ hle] at hx'
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.mp hx'
  refine ⟨n, hn, y, ⟨hy.1, ?_⟩, rfl⟩
  have hJ : thompsonJ (T ⊓ N) = thompsonJ T :=
    B6.thompsonJ_eq_of_le (le_inf (C1GN.thompsonJ_le T) hJN) inf_le_left
  rw [← hJ]
  exact normalizer_le_normalizer_thompsonJ (T ⊓ N) hy.2

theorem thompsonJ_le_conjClosure {M₁ X T : Subgroup G} (hT : IsSylowTwoOf T M₁) (hXM : X ≤ M₁)
    (hTX : T ≤ X) (hIX : thompsonJ M₁ ≤ X) : thompsonJ M₁ ≤ conjClosure T X := by
  have hTX' : IsSylowTwoOf T X := B6.isSylowTwoOf_mono hT hTX hXM
  have hJX : thompsonJ M₁ ≤ thompsonJ X := by
    refine iSup₂_le fun A hA => ?_
    have hAX : A ≤ X := (B6.le_thompsonJ hA).trans hIX
    exact B6.le_thompsonJ ⟨hAX, hA.2.1, fun B hBX hB => hA.2.2 B (hBX.trans hXM) hB⟩
  have hJT : thompsonJ T ≤ conjClosure T X := (C1GN.thompsonJ_le T).trans (le_conjClosure T X)
  exact hJX.trans (B6.thompsonJ_le_of_sylow_of_le hTX' hJT (le_normalizer_conjClosure T X))

theorem gen_parabolics {X T : Subgroup G} (hT : IsSylowTwoOf T X) (hlt : T < conjClosure T X) :
    ⨆ P ∈ uFamHat (conjClosure T X) T, P = conjClosure T X := by
  set K := conjClosure T X with hK
  have hKX : K ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem hh (hT.1 hz)) (X.inv_mem hh)
  have hTK : T ≤ K := le_conjClosure T X
  have hTK' : IsSylowTwoOf T K := B6.isSylowTwoOf_mono hT hTK hKX
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := le_normalizer_conjClosure T X
  have hres : twoPrimeResidual K = K := by
    apply le_antisymm
    · refine iInf₂_le K ⟨le_rfl, Subgroup.le_normalizer, ?_⟩
      rw [Subgroup.relIndex_self]
      norm_num
    · rw [← conjClosure_eq_twoPrimeResidual hTK']
      refine conjClosure_le fun x hx z hz => ?_
      have hx' := B6.frattini_two hKX hXK hTK' hx
      have hle : X ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (K : Set G) :=
        inf_le_left.trans hXK
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K _ hle] at hx'
      obtain ⟨k, hk, n, hn, rfl⟩ := Set.mem_mul.mp hx'
      have hnz : n * z * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn.2 z).mp hz
      have := mem_conjClosure hk hnz
      simpa [mul_assoc] using this
  exact generated_by_uFamHat hTK' hlt hres

end S1414

end CFSG.Quasithin
