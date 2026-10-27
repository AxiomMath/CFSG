module

public import CFSG.Quasithin.Background.C41PfA
public import CFSG.Quasithin.Background.C24PfF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C41Pf

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem isTwoRadicalIn_of_le (h : HypC28 H R M L V) {Y : Subgroup G} (hRY : R ≤ Y)
    (hYH : Y ≤ H) (hYN : conjClosure L M ≤ Subgroup.normalizer (Y : Set G)) :
    IsTwoRadicalIn Y R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M with hM₀
  set D := pCoreOf 2 (Y ⊓ Subgroup.normalizer (R : Set G)) with hD
  have hM₀R : M₀ ≤ Subgroup.normalizer (R : Set G) := (c2_9_two h).1
  refine ⟨hRY, C2Nine.ne_bot_of_hyp h, le_antisymm ?_ ?_⟩
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf hRY Subgroup.le_normalizer) inf_le_right h.pgroup
  · have hD2 : IsPGroup 2 ↥D := pCoreOf_isPGroup 2 _
    have hDYN : D ≤ Y ⊓ Subgroup.normalizer (R : Set G) := pCoreOf_le 2 _
    have hM₀D : M₀ ≤ Subgroup.normalizer (D : Set G) := by
      refine le_trans ?_ (normalizer_le_normalizer_pCoreOf 2 _)
      exact le_trans (le_inf hYN (hM₀R.trans Subgroup.le_normalizer))
        Subgroup.inf_normalizer_le_normalizer_inf
    have hDM : D ≤ M := hDYN.trans ((inf_le_inf_right _ hYH).trans (C2Nine.inf_normalizer_le_M h))
    have hMM₀ : M ≤ Subgroup.normalizer (M₀ : Set G) := le_normalizer_conjClosure L M
    have hDM₀ : D ⊓ M₀ ≤ pCoreOf 2 M₀ := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hD2.to_le inf_le_left)
      exact le_trans (le_inf hM₀D Subgroup.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf
    intro x hx
    have hxM : x ∈ M := hDM hx
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := (hDYN hx).2
    have hxC : x ∈ centralizerSection M M₀ (pCoreOf 2 M₀) := by
      refine ⟨hxM, hMM₀ hxM, normalizer_le_normalizer_pCoreOf 2 M₀ (hMM₀ hxM), fun y hy => ?_⟩
      refine hDM₀ ⟨?_, ?_⟩
      · have h1 : y * x * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hM₀D hy) x).mp hx
        exact D.mul_mem h1 (D.inv_mem hx)
      · have h1 : x * y⁻¹ * x⁻¹ ∈ M₀ :=
          (Subgroup.mem_normalizer_iff.mp (hMM₀ hxM) y⁻¹).mp (M₀.inv_mem hy)
        have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
        rw [e]
        exact M₀.mul_mem hy h1
    obtain ⟨k, hk⟩ := hD2 ⟨x, hx⟩
    refine C24Pf.mem_of_mem_normalizer_of_isSylowTwoOf h.sylow hxC hxR ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

theorem hypC23_of_le (h : HypC28 H R M L V) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H)
    (hYN : conjClosure L M ≤ Subgroup.normalizer (Y : Set G)) : HypC23 Y R (M ⊓ Y) where
  sqtk := h.sqtk.mono hYH
  radical := isTwoRadicalIn_of_le h hRY hYH hYN
  le := inf_le_right
  cgs := le_inf ((C2Nine.cgsIn_mono_left hYH R).trans h.cgs) (cgsIn_le Y R)
  sylow := by
    refine B6.isSylowTwoOf_mono (c2_10_four h).sylow (le_conjClosure R _) ?_
    exact conjClosure_le fun m hm r hr => mem_conjClosure hm.1 hr

theorem asc24Two_of_hypC28 (h82 : Asc82Thm2)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) (h : HypC28 H R M L V)
    (hK : K ∈ cComp H) (hKc : CharTwo K) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    IsSylowTwoOf (R ⊓ K) K ∨ R ≤ Subgroup.normalizer (K : Set G) := by
  have hRH : R ≤ H := h.le_M.trans h.le_H
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hR : IsTwoRadicalIn H R := (c2_9_two h).2
  have hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
    conjClosure_le_normalizer (a3Orbits_of_a37_a38 hA37 hA38) h hK
  have hNR : conjClosure L M ≤ Subgroup.normalizer (R : Set G) := (c2_9_two h).1
  set Y := conjClosure K R ⊔ R with hY
  have hRY : R ≤ Y := le_sup_right
  have hYH : Y ≤ H := sup_le (conjClosure_le fun r hr k hk =>
    H.mul_mem (H.mul_mem (hRH hr) (hKH hk)) (H.inv_mem (hRH hr))) hRH
  have hYN : conjClosure L M ≤ Subgroup.normalizer (Y : Set G) := by
    intro m hm
    refine C22Pf.mem_normalizer_of_conj_mem fun y hy => ?_
    have hle : Y ≤ Y.comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (conjClosure_le fun r hr k hk => ?_) fun r hr => ?_
      · show m * (r * k * r⁻¹) * m⁻¹ ∈ Y
        have e : m * (r * k * r⁻¹) * m⁻¹ =
            (m * r * m⁻¹) * (m * k * m⁻¹) * (m * r * m⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mem_sup_left (mem_conjClosure
          ((Subgroup.mem_normalizer_iff.mp (hNR hm) r).mp hr)
          ((Subgroup.mem_normalizer_iff.mp (hNK hm) k).mp hk))
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNR hm) r).mp hr)
    exact hle hy
  have hYc : CharTwo Y := C24Pf.charTwo_conjClosure_sup hA37 hA38 hS h.sqtk hR hK hKc hKq
  have hKY : K ∈ cComp Y := cComp_mem_of_le hK ((le_conjClosure K R).trans le_sup_left) hYH
  exact C24Pf.asc24TwoChar_of h82 hA37 hA38 Y R (M ⊓ Y) K (hypC23_of_le h hRY hYH hYN) hYc hKY
    hKc hKq

end C41Pf

end CFSG.Quasithin
