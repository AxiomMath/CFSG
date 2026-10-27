module

public import CFSG.Quasithin.Background.C41PfE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_le {X : Subgroup G} {x : G}
    (h : X.map (MulAut.conj x).toMonoidHom ≤ X) : x ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h (le_of_eq ?_)
  exact (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm

theorem eq_conjClosure_of_isSimpleGroup (hA3 : A3Orbits G) {M L : Subgroup G} (hM : IsSQTKIn M)
    (hL : L ∈ cComp M) (hS : IsSimpleGroup (ModO2 (conjClosure L M))) :
    L = conjClosure L M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M with hM₀
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hLM₀ : L ≤ M₀ := le_conjClosure L M
  have hMN₀ : M ≤ Subgroup.normalizer (M₀ : Set G) := le_normalizer_conjClosure L M
  have hM₀M : M₀ ≤ M := conjClosure_le fun m hm l hl =>
    M.mul_mem (M.mul_mem hm (hLM hl)) (M.inv_mem hm)
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (P := ⊥) (H := M) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨hMT, hcase⟩ := hA3 M T L hM hT hL
  rcases hcase with hTN | ⟨t, htT, -, hTL, hcomm, hint, -⟩
  ·
    refine le_antisymm hLM₀ (conjClosure_le fun m hm l hl => ?_)
    have hmem : conjByElt m L ∈ conjSubgroupsBy T L := by
      rw [← hMT]
      exact ⟨m, hm, rfl⟩
    obtain ⟨y, hy, he⟩ := hmem
    have hmL : conjByElt m L = L := by
      rw [he]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN y hy)
    have : m * l * m⁻¹ ∈ conjByElt m L := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hl
    rwa [hmL] at this
  · exfalso
    have htM : t ∈ M := hT.1 htT
    have hclass : ∀ m ∈ M, conjByElt m L = L ∨ conjByElt m L = conjByElt t L := by
      intro m hm
      have hmem : conjByElt m L ∈ conjSubgroupsBy T L := by
        rw [← hMT]
        exact ⟨m, hm, rfl⟩
      rw [hTL] at hmem
      exact hmem
    have hLtM₀ : conjByElt t L ≤ M₀ := conjByElt_le_conjClosure htM
    set N := pCoreOf 2 M₀ with hN
    have hNM₀ : N ≤ M₀ := pCoreOf_le 2 M₀
    have hN2 : IsPGroup 2 ↥N := pCoreOf_isPGroup 2 M₀
    have hNM : N ≤ pCoreOf 2 M :=
      le_pCoreOf_of_le_normalizer 2 (hNM₀.trans hM₀M)
        (hMN₀.trans (normalizer_le_normalizer_pCoreOf 2 M₀)) hN2
    have hON : M₀ ⊓ pCoreOf 2 M ≤ N := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
      exact (le_inf Subgroup.le_normalizer (hM₀M.trans (le_normalizer_pCoreOf 2 M))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    set X := L ⊔ N with hX
    have hXM₀ : X ≤ M₀ := sup_le hLM₀ hNM₀
    have hgen : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
      intro m hm l hl
      have hx : m * l * m⁻¹ ∈ conjByElt m L := by
        rw [mem_conjByElt]
        simpa [mul_assoc] using hl
      rcases hclass m hm with he | he
      · rw [he] at hx
        exact Subgroup.le_normalizer (Subgroup.mem_sup_left hx)
      · rw [he] at hx
        set x := m * l * m⁻¹ with hxdef
        have hxM₀ : x ∈ M₀ := hLtM₀ hx
        refine mem_normalizer_of_map_le ?_
        rw [hX, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨l', hl', rfl⟩
          have hc : ⁅l'⁻¹, x⁆ ∈ N := by
            refine hON ⟨?_, hcomm (Subgroup.commutator_mem_commutator (L.inv_mem hl') hx)⟩
            rw [commutatorElement_def, inv_inv]
            exact M₀.mul_mem (M₀.mul_mem (M₀.mul_mem (M₀.inv_mem (hLM₀ hl')) hxM₀)
              (hLM₀ hl')) (M₀.inv_mem hxM₀)
          have he' : (MulAut.conj x).toMonoidHom l' = l' * ⁅l'⁻¹, x⁆ := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
            group
          rw [he']
          exact X.mul_mem (Subgroup.mem_sup_left hl') (Subgroup.mem_sup_right hc)
        · have hxN : x ∈ Subgroup.normalizer (N : Set G) := le_normalizer_pCoreOf 2 M₀ hxM₀
          rintro _ ⟨n, hn, rfl⟩
          refine Subgroup.mem_sup_right ?_
          have := (Subgroup.mem_normalizer_iff.mp hxN n).mp hn
          simpa [MulAut.conj_apply] using this
    have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) := conjClosure_le hgen
    set π : ↥M₀ →* ModO2 M₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥M₀) with hπ
    have hmemN : ∀ y : ↥M₀, y ∈ CFSG.pCore 2 ↥M₀ ↔ (y : G) ∈ N := by
      intro y
      rw [hN, C2A3Orbits.pCoreOf_eq_map_pCore M₀]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y', hy', he⟩
        rwa [show y = y' from Subtype.ext he.symm]
    have hXn : (X.subgroupOf M₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXM₀).2 hM₀X
    have hXn' : ((X.subgroupOf M₀).map π).Normal :=
      hXn.map π (QuotientGroup.mk'_surjective _)
    have : IsSimpleGroup (ModO2 M₀) := hS
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X.subgroupOf M₀).map π) with hbot | htop
    ·
      have hLN : L ≤ N := by
        intro l hl
        have h1 : π ⟨l, hLM₀ hl⟩ ∈ (X.subgroupOf M₀).map π :=
          ⟨⟨l, hLM₀ hl⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl), rfl⟩
        rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact (hmemN _).mp h1
      have hL1 := eq_bot_of_perfect_of_isSolvable (perfect_of_mem_cComp hL)
        (by
          have := (hN2.to_le hLN).isNilpotent
          infer_instance)
      exact ne_bot_of_mem_cComp hL hL1
    ·
      have hM₀le : M₀ ≤ X := by
        intro y hy
        obtain ⟨x, hx, hxy⟩ : π ⟨y, hy⟩ ∈ (X.subgroupOf M₀).map π := by
          rw [htop]
          exact Subgroup.mem_top _
        have h1 : x⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥M₀ := by
          rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_inv,
            hxy, inv_mul_cancel]
        have h2 : ((x : G))⁻¹ * y ∈ N := by simpa using (hmemN _).mp h1
        have e : y = (x : G) * ((x : G)⁻¹ * y) := by group
        rw [e]
        exact X.mul_mem (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_sup_right h2)
      have hLt : conjByElt t L ≤ pCoreOf 2 M := by
        rw [← hint]
        refine le_inf ?_ le_sup_left
        exact hLtM₀.trans (hM₀le.trans (sup_le_sup_left hNM L))
      have hLt' : conjByElt t L ∈ cComp M := C2Nine.conjByElt_mem_cComp hL
        (Subgroup.le_normalizer htM)
      have hL1 := eq_bot_of_perfect_of_isSolvable (perfect_of_mem_cComp hLt')
        (by
          have := ((pCoreOf_isPGroup 2 M).to_le hLt).isNilpotent
          infer_instance)
      exact ne_bot_of_mem_cComp hLt' hL1

theorem c41Conclusion_of_case (hK0 : C41KZero G) (hA3 : A3Orbits G) {H R M L V K : Subgroup G}
    (hP : C41Post H R M L V K) (hS : IsSimpleGroup (ModO2 (conjClosure L M)))
    (hc : C41Case1 H R M L V K ∨ C41Case2 H R M L V K ∨ C41Case3 H R M L V K ∨
      C41Case4 H R M L V K) : C41Conclusion H R M L V K := by
  have h := hP.hyp
  have hLc := h.comp
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    hK0 H R M L V K h hP.comp hP.charTwo hP.quasi hP.not_le hP.le_normalizer
      ⟨L, ne_bot_of_mem_cComp hLc, perfect_of_mem_cComp hLc,
        le_inf (le_of_mem_cComp hLc) ((le_conjClosure L M).trans hP.le),
        (le_conjClosure L M).trans (c2_9_two h).1⟩
  have hK : conjClosure K H = K := by
    refine le_antisymm (conjClosure_le fun x hx k hk => ?_) (le_conjClosure K H)
    exact (Subgroup.mem_normalizer_iff.mp (hHN hx) k).mp hk
  have hL : L = conjClosure L M :=
    eq_conjClosure_of_isSimpleGroup hA3 (h.sqtk.mono h.le_H) hLc hS
  exact ⟨hL, hK.symm ▸ hP.le, hK, hc⟩

end C41Pf

end CFSG.Quasithin
