module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordLines

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

variable {G : Type} [Group G]

private lemma automizer_fixes_image {Bs : Subgroup G} {V : Type*} [Group V] {u : G}
    {P : Subgroup G} (h : GGFixLineComp Bs u P) (eta : ↥Bs ≃* V) :
    ∀ w ∈ (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom, w (eta ⟨u, h.mem⟩) =
      eta ⟨u, h.mem⟩ :=
  (GGFixLineComp.forall_map_congr_fix_iff h eta (eta ⟨u, h.mem⟩)).mpr (by simp)

private lemma mem_zpowers_of_forall_automizer_fix {Bs : Subgroup G} {V : Type*} [Group V]
    {u : G} {P : Subgroup G} (h : GGFixLineComp Bs u P) (eta : ↥Bs ≃* V) {f : V}
    (hf : ∀ w ∈ (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom, w f = f) :
    ((eta.symm f : ↥Bs) : G) ∈ Subgroup.zpowers u :=
  (GGFixLineComp.forall_map_congr_fix_iff h eta f).mp hf

private lemma mem_closure_pair_map_coord {Bs : Subgroup G} {V : Type*} [Group V]
    (eta : ↥Bs ≃* V) {x y y₀ : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hy₀ : y₀ ∈ Bs)
    (h : y ∈ Subgroup.closure ({x, y₀} : Set G)) :
    eta ⟨y, hy⟩ ∈ Subgroup.closure {eta ⟨x, hx⟩, eta ⟨y₀, hy₀⟩} := by
  simpa using mem_closure_pair_map eta (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (y₀ := ⟨y₀, hy₀⟩) h

private lemma not_mem_zpowers_map_coord {Bs : Subgroup G} {V : Type*} [Group V]
    (eta : ↥Bs ≃* V) {x y : G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (h : y ∉ Subgroup.zpowers x) : eta ⟨y, hy⟩ ∉ Subgroup.zpowers (eta ⟨x, hx⟩) := by
  simpa using not_mem_zpowers_map eta (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h

private lemma axis_of_mem_coordBlock {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {y : G}
    {K : Subgroup G} (h : GGFixLineComp Bs y K) {j : Fin n}
    (hj : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) :
    ∀ k, k ≠ j → eta ⟨y, h.mem⟩ k = 1 := by
  have hfix := automizer_fixes_image h eta
  rcases hj with hj | hj
  · rw [hj] at hfix
    exact (forall_bCoordinateBlock_fix_iff hp hp2 j _).mp hfix
  · rw [hj] at hfix
    exact (forall_dCoordinateBlock_fix_iff hp hp2 hn j _).mp hfix

private lemma exists_const_of_mem_map_conj_aPermutation {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {y : G} {K : Subgroup G}
    (h : GGFixLineComp Bs y K) {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) :
    ∃ c : ZMod p, eta ⟨y, h.mem⟩ = δ (fun _ => ofAdd c) := by
  have hfix := automizer_fixes_image h eta
  rw [hδ] at hfix
  exact exists_const_of_forall_map_conj_aPermutationFull_fix δ hfix

private lemma forall_coord_eq_of_map_eq_aPermutation {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {x : G} {L : Subgroup G}
    (h : GGFixLineComp Bs x L)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∀ a b, eta ⟨x, h.mem⟩ a = eta ⟨x, h.mem⟩ b := by
  have hfix := automizer_fixes_image h eta
  rw [hL] at hfix
  exact (forall_aPermutationFull_fix_iff _).mp hfix

private lemma axis_index_ne_of_anchor {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {x : G} {L : Subgroup G}
    (hL : GGFixLineComp Bs x L) {y₀ : G} {K₀ : Subgroup G} (h₀ : GGFixLineComp Bs y₀ K₀)
    {i0 j : Fin n}
    (hjL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0)
    (hj₀ : ∀ k, k ≠ j → eta ⟨y₀, h₀.mem⟩ k = 1) (hx : y₀ ∉ Subgroup.zpowers x) : j ≠ i0 := by
  intro hji
  have hj₀' : ∀ k, k ≠ i0 → eta ⟨y₀, h₀.mem⟩ k = 1 := by
    rwa [hji] at hj₀
  have hfix₀ : ∀ w ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨y₀, h₀.mem⟩) = eta ⟨y₀, h₀.mem⟩ := by
    rcases hjL with hjL | hjL
    · rw [hjL]
      exact (forall_bCoordinateBlock_fix_iff hp hp2 i0 _).mpr hj₀'
    · rw [hjL]
      exact (forall_dCoordinateBlock_fix_iff hp hp2 hn i0 _).mpr hj₀'
  exact hx (by simpa using mem_zpowers_of_forall_automizer_fix hL eta hfix₀)

private lemma eq_of_coordBlock_same_axis [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {y y₀ : G} {K K₀ : Subgroup G} {j : Fin n} (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (h : GGFixLineComp Bs y K) (h₀ : GGFixLineComp Bs y₀ K₀)
    (hnorm : Bs ≤ Subgroup.normalizer (K : Set G))
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j)
    (hK₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) :
    K = K₀ := by
  obtain ⟨τ, hτb, hτd, hτ2, hτ1⟩ := exists_involution_mem_bCoordinateBlock_dCoordinateBlock hp hn j
  refine GGFixLineComp.eq_of_map_congr h h₀ hBs hnorm eta ?_ ?_ ?_ hτ2 hτ1
  · intro f
    rcases hK with hK | hK <;> rcases hK₀ with hK₀ | hK₀
    · rw [hK, hK₀, forall_bCoordinateBlock_fix_iff hp hp2 j f]
    · rw [hK, hK₀, forall_bCoordinateBlock_fix_iff hp hp2 j f,
        forall_dCoordinateBlock_fix_iff hp hp2 hn j f]
    · rw [hK, hK₀, forall_dCoordinateBlock_fix_iff hp hp2 hn j f,
        forall_bCoordinateBlock_fix_iff hp hp2 j f]
    · rw [hK, hK₀, forall_dCoordinateBlock_fix_iff hp hp2 hn j f]
  · rcases hK with hK | hK <;> rw [hK] <;> first | exact hτb | exact hτd
  · rcases hK₀ with hK₀ | hK₀ <;> rw [hK₀] <;> first | exact hτb | exact hτd

private lemma eq_of_map_conj_eq [Finite G] {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {u v : G}
    {P Q : Subgroup G} (hP : GGFixLineComp Bs u P) (hQ : GGFixLineComp Bs v Q)
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hBP : Bs ≤ Subgroup.normalizer (P : Set G))
    {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hPδ : (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hQδ : (ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) : P = Q := by
  obtain ⟨τ, hτ, hτ2, hτ1⟩ := exists_involution_mem_aPermutationFull_map_conj hp hn δ
  refine GGFixLineComp.eq_of_map_congr hP hQ hBs hBP eta ?_ ?_ ?_ hτ2 hτ1
  · intro f
    rw [hPδ, hQδ]
  · rw [hPδ]
    exact hτ
  · rw [hQδ]
    exact hτ

private lemma exists_bCoordinateBlock_of_d_or_a {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {L : Subgroup G}
    {i0 : Fin n} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    (hsup : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
        ⨆ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (h𝒦 : ∀ K ∈ 𝒦, ∃ y, Nb y K)
    (htype : ∀ y K, Nb y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hLda : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∃ K ∈ 𝒦, ∃ j : Fin n,
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  by_contra hno
  have hno' : ∀ K ∈ 𝒦, ∀ j : Fin n,
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≠ bCoordinateBlock n p j := by
    intro K hK j hj
    exact hno ⟨K, hK, j, hj⟩
  have hKle : ∀ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤
      coordProdStab n p := by
    intro K hK
    obtain ⟨y, hy⟩ := h𝒦 K hK
    rcases htype y K hy with ⟨j, hj | hj⟩ | ⟨δ, hδ, hδeq⟩
    · exact absurd hj (hno' K hK j)
    · rw [hj]
      exact dCoordinateBlock_le_coordProdStab j
    · rw [hδeq]
      exact aPermutationFull_map_conj_le_coordProdStab hδ
  have hLle : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rcases hLda with hLda | hLda
    · rw [hLda]
      exact dCoordinateBlock_le_coordProdStab i0
    · rw [hLda]
      exact aPermutationFull_le_coordProdStab
  have hle : bSignedFull n p ≤ coordProdStab n p := by
    rw [← hsup]
    exact sup_le hLle (iSup₂_le hKle)
  exact sgnAut_not_mem_coordProdStab hp hp2 i0
    (hle (Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)))

private lemma exists_mem_of_map_eq_bCoordinateBlock {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {L : Subgroup G}
    {i0 : Fin n} {𝒦 : Finset (Subgroup G)}
    (hsup : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
        ⨆ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ K, K ∈ 𝒦 := by
  by_contra h
  have hbot : (⨆ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) = ⊥ :=
    le_antisymm (iSup₂_le_iff.mpr fun K hK => (h ⟨K, hK⟩).elim) bot_le
  have hbs : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
    rw [← hsup, hbot, sup_bot_eq]
  refine sgnAut_not_mem_bCoordinateBlock hp hp2 i0 ?_
  rw [← hL, hbs]
  exact Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)

private lemma le_join_of_mem {L K : Subgroup G} {𝒦 : Finset (Subgroup G)} (hK : K ∈ 𝒦) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' :=
  le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)

private lemma le_join_of_map_conj_le_left {L K₀ : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hK₀ : K₀ ∈ 𝒦) {g : G} (hg : g ∈ L) :
    K₀.map (MulAut.conj g).toMonoidHom ≤ L ⊔ ⨆ K' ∈ 𝒦, K' :=
  le_trans (map_conj_le_sup (W := L) (X := K₀) hg)
    (sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K₀ hK₀ le_rfl)))

private lemma le_join_of_map_conj_le_right {L K₀ : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hK₀ : K₀ ∈ 𝒦) {g : G} (hg : g ∈ K₀) :
    L.map (MulAut.conj g).toMonoidHom ≤ L ⊔ ⨆ K' ∈ 𝒦, K' :=
  le_trans (map_conj_le_sup (W := K₀) (X := L) hg)
    (by rw [sup_comm]
        exact sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K₀ hK₀ le_rfl)))

private lemma le_join_of_coordBlock_anchor [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) {Bs : Subgroup G} {x : G} {L : Subgroup G} {i0 : Fin n}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {𝒦 : Finset (Subgroup G)}
    {Nb : G → Subgroup G → Prop} (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (hL : GGFixLineComp Bs x L)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0)
    (hfix : ∀ y K, Nb y K → GGFixLineComp Bs y K)
    (hnorm : ∀ y K, Nb y K → Bs ≤ Subgroup.normalizer (K : Set G))
    (htype : ∀ y K, Nb y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hplane : ∀ y K y₀ K₀, Nb y K → Nb y₀ K₀ → y ∈ Subgroup.closure ({x, y₀} : Set G))
    (hx : ∀ y K, Nb y K → y ∉ Subgroup.zpowers x) {y₀ : G} {K₀ : Subgroup G} (h₀ : Nb y₀ K₀)
    (hK₀ : K₀ ∈ 𝒦) {j : Fin n}
    (hj₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have h₀fix := hfix y₀ K₀ h₀
  have hKfix := hfix y K hyK
  have hxax := axis_of_mem_coordBlock hp hp2 (by omega) eta hL hLpos
  have hy₀ax := axis_of_mem_coordBlock hp hp2 (by omega) eta h₀fix hj₀
  have hplane' := mem_closure_pair_map_coord eta hL.mem hKfix.mem h₀fix.mem
    (hplane y K y₀ K₀ hyK h₀)
  have hnotzp := not_mem_zpowers_map_coord eta hL.mem hKfix.mem (hx y K hyK)
  have hji : j ≠ i0 :=
    axis_index_ne_of_anchor hp hp2 (by omega) eta hL h₀fix hLpos hy₀ax (hx y₀ K₀ h₀)
  rcases htype y K hyK with ⟨j', hj'⟩ | ⟨δ, hδ, hδeq⟩
  · have hyax := axis_of_mem_coordBlock hp hp2 (by omega) eta hKfix hj'
    have hjeq : j' = j :=
      axis_eq_of_mem_closure_axis_axis hji hxax hy₀ax hplane' hnotzp hyax
    subst hjeq
    have hKeq : K = K₀ :=
      eq_of_coordBlock_same_axis hp hp2 (by omega) eta hBs hKfix h₀fix (hnorm y K hyK) hj' hj₀
    exact hKeq.symm ▸ le_join_of_mem hK₀
  · obtain ⟨c, hc⟩ := exists_const_of_mem_map_conj_aPermutation eta hKfix hδeq
    exact absurd hc (ne_apply_const_of_mem_closure_axis_axis (by omega) hji hxax hy₀ax hplane'
      hnotzp hδ c)

private lemma exists_conj_eq_of_const_anchor [Finite G] {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    {Bs : Subgroup G} {x : G} {L : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {y y₀ : G} {K K₀ : Subgroup G}
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hL : GGFixLineComp Bs x L) (hK : GGFixLineComp Bs y K) (h₀ : GGFixLineComp Bs y₀ K₀)
    (hnorm : Bs ≤ Subgroup.normalizer (K : Set G)) {j : Fin n}
    (hj₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j)
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p)
    (hδeq : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hxax : ∀ a b, eta ⟨x, hL.mem⟩ a = eta ⟨x, hL.mem⟩ b)
    (hy₀ax : ∀ k, k ≠ j → eta ⟨y₀, h₀.mem⟩ k = 1)
    (hplane' : eta ⟨y, hK.mem⟩ ∈
      Subgroup.closure {eta ⟨x, hL.mem⟩, eta ⟨y₀, h₀.mem⟩})
    (hnotzp : eta ⟨y, hK.mem⟩ ∉ Subgroup.zpowers (eta ⟨x, hL.mem⟩)) :
    ∃ g ∈ K₀, K = L.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨c, hc⟩ := exists_const_of_mem_map_conj_aPermutation eta hK hδeq
  have hδ' : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj (negOff j)).toMonoidHom := by
    rw [hδeq]
    exact aPermutationFull_map_conj_eq_negOff_of_mem_closure_const_axis hp hn hδ hxax hy₀ax
      hplane' hnotzp hc
  have hneg : negOff (p := p) j ∈ (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hj₀]
    exact negOff_mem_bCoordinateBlock j
  obtain ⟨g, hg, hgK₀, hgc⟩ := exists_mem_of_mem_map_congr eta hneg
  refine ⟨g, hgK₀, ?_⟩
  have hL' : (ggAutomizer (L.map (MulAut.conj g).toMonoidHom) Bs).map
      (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj (negOff j)).toMonoidHom := by
    rw [map_congr_ggAutomizer_map_conj eta hg L, hLpos, hgc]
  exact eq_of_map_conj_eq hp hn eta hK (hL.map_conj hg) hBs hnorm hδ' hL'

private lemma le_join_of_const_anchor [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) {Bs : Subgroup G} {x : G} {L : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {𝒦 : Finset (Subgroup G)}
    {Nb : G → Subgroup G → Prop} (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (hL : GGFixLineComp Bs x L)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hfix : ∀ y K, Nb y K → GGFixLineComp Bs y K)
    (hnorm : ∀ y K, Nb y K → Bs ≤ Subgroup.normalizer (K : Set G))
    (htype : ∀ y K, Nb y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hplane : ∀ y K y₀ K₀, Nb y K → Nb y₀ K₀ → y ∈ Subgroup.closure ({x, y₀} : Set G))
    (hx : ∀ y K, Nb y K → y ∉ Subgroup.zpowers x) {y₀ : G} {K₀ : Subgroup G} (h₀ : Nb y₀ K₀)
    (hK₀ : K₀ ∈ 𝒦) {j : Fin n}
    (hj₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have h₀fix := hfix y₀ K₀ h₀
  have hKfix := hfix y K hyK
  have hxax := forall_coord_eq_of_map_eq_aPermutation eta hL hLpos
  have hy₀ax := axis_of_mem_coordBlock hp hp2 (by omega) eta h₀fix (Or.inl hj₀)
  have hplane' := mem_closure_pair_map_coord eta hL.mem hKfix.mem h₀fix.mem
    (hplane y K y₀ K₀ hyK h₀)
  have hnotzp := not_mem_zpowers_map_coord eta hL.mem hKfix.mem (hx y K hyK)
  rcases htype y K hyK with ⟨j', hj'⟩ | ⟨δ, hδ, hδeq⟩
  · have hyax := axis_of_mem_coordBlock hp hp2 (by omega) eta hKfix hj'
    have hjeq : j' = j :=
      axis_eq_of_mem_closure_const_axis (by omega) hxax hy₀ax hplane' hnotzp hyax
    subst hjeq
    have hKeq : K = K₀ :=
      eq_of_coordBlock_same_axis hp hp2 (by omega) eta hBs hKfix h₀fix (hnorm y K hyK) hj'
        (Or.inl hj₀)
    exact hKeq.symm ▸ le_join_of_mem hK₀
  · obtain ⟨g, hgK₀, hKeq⟩ :=
      exists_conj_eq_of_const_anchor (p := p) (n := n) hp (by omega) eta hBs hLpos hL hKfix
        h₀fix (hnorm y K hyK) hj₀ hδ hδeq hxax hy₀ax hplane' hnotzp
    exact hKeq.symm ▸ le_join_of_map_conj_le_right hK₀ hgK₀

private lemma exists_conj_eq_of_map_conj_anchor [Finite G] {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    {Bs : Subgroup G} {L : Subgroup G} {i0 : Fin n}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {y y₀ : G} {K K₀ : Subgroup G}
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hK : GGFixLineComp Bs y K) (h₀ : GGFixLineComp Bs y₀ K₀)
    (hnorm : Bs ≤ Subgroup.normalizer (K : Set G))
    {δ₀ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ₀).toMonoidHom)
    {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδeq : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hconj : (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
      ((aPermutationFull n p).map (MulAut.conj δ₀).toMonoidHom).map
        (MulAut.conj (negOff i0)).toMonoidHom) :
    ∃ g ∈ L, K = K₀.map (MulAut.conj g).toMonoidHom := by
  have hneg : negOff (p := p) i0 ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hLpos]
    exact negOff_mem_bCoordinateBlock i0
  obtain ⟨g, hg, hgL, hgc⟩ := exists_mem_of_mem_map_congr eta hneg
  refine ⟨g, hgL, ?_⟩
  have hK₀' : (ggAutomizer (K₀.map (MulAut.conj g).toMonoidHom) Bs).map
      (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom := by
    rw [map_congr_ggAutomizer_map_conj eta hg K₀, hδ₀, hgc]
    exact hconj.symm
  exact eq_of_map_conj_eq hp hn eta hK (h₀.map_conj hg) hBs hnorm hδeq hK₀'

private lemma le_join_of_map_conj_anchor [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) {Bs : Subgroup G} {x : G} {L : Subgroup G} {i0 : Fin n}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {𝒦 : Finset (Subgroup G)}
    {Nb : G → Subgroup G → Prop} (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1)
    (hL : GGFixLineComp Bs x L)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hfix : ∀ y K, Nb y K → GGFixLineComp Bs y K)
    (hnorm : ∀ y K, Nb y K → Bs ≤ Subgroup.normalizer (K : Set G))
    (htype : ∀ y K, Nb y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hplane : ∀ y K y₀ K₀, Nb y K → Nb y₀ K₀ → y ∈ Subgroup.closure ({x, y₀} : Set G))
    (hx : ∀ y K, Nb y K → y ∉ Subgroup.zpowers x) {y₀ : G} {K₀ : Subgroup G} (h₀ : Nb y₀ K₀)
    (hK₀ : K₀ ∈ 𝒦) {δ₀ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ₀mem : δ₀ ∈ bSignedFull n p)
    (hδ₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ₀).toMonoidHom)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have h₀fix := hfix y₀ K₀ h₀
  have hKfix := hfix y K hyK
  have hxax := axis_of_mem_coordBlock hp hp2 (by omega) eta hL (Or.inl hLpos)
  obtain ⟨c₀, hc₀⟩ := exists_const_of_mem_map_conj_aPermutation eta h₀fix hδ₀
  have hnotzp := not_mem_zpowers_map_coord eta hL.mem hKfix.mem (hx y K hyK)
  have hplane'' : eta ⟨y, hKfix.mem⟩ ∈
      Subgroup.closure {eta ⟨x, hL.mem⟩, δ₀ (fun _ => ofAdd c₀)} := by
    simpa [hc₀] using
      mem_closure_pair_map_coord eta hL.mem hKfix.mem h₀fix.mem (hplane y K y₀ K₀ hyK h₀)
  rcases htype y K hyK with ⟨j', hj'⟩ | ⟨δ, hδ, hδeq⟩
  · exact absurd (axis_of_mem_coordBlock hp hp2 (by omega) eta hKfix hj')
      (not_axis_of_mem_closure_axis_const (by omega) hδ₀mem hxax hplane'' hnotzp j')
  · obtain ⟨c, hc⟩ := exists_const_of_mem_map_conj_aPermutation eta hKfix hδeq
    rcases aPermutationFull_map_conj_eq_of_mem_closure_axis_const hp (by omega) hδ₀mem hδ
      hxax hplane'' hnotzp hc with hsame | hconj
    · have hδ₀' : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom := hδ₀.trans hsame.symm
      have hKeq : K = K₀ :=
        eq_of_map_conj_eq hp (by omega) eta hKfix h₀fix hBs (hnorm y K hyK) hδeq hδ₀'
      exact hKeq.symm ▸ le_join_of_mem hK₀
    · obtain ⟨g, hgL, hKeq⟩ :=
        exists_conj_eq_of_map_conj_anchor (p := p) (n := n) hp (by omega) eta hBs hLpos
          hKfix h₀fix (hnorm y K hyK) hδ₀ hδeq hconj
      exact hKeq.symm ▸ le_join_of_map_conj_le_left hK₀ hgL

theorem le_join_of_signedCoordPosition [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) {Bs L : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    {Nb : G → Subgroup G → Prop} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hL : GGFixLineComp Bs x L)
    (hLpos : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (h𝒦 : ∀ K ∈ 𝒦, ∃ y, Nb y K) (hfix : ∀ y K, Nb y K → GGFixLineComp Bs y K)
    (hnorm : ∀ y K, Nb y K → Bs ≤ Subgroup.normalizer (K : Set G))
    (htype : ∀ y K, Nb y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom)
    (hplane : ∀ y K y₀ K₀, Nb y K → Nb y₀ K₀ → y ∈ Subgroup.closure ({x, y₀} : Set G))
    (hx : ∀ y K, Nb y K → y ∉ Subgroup.zpowers x) {y : G} {K : Subgroup G} (hyK : Nb y K) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hsup : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      ⨆ K' ∈ 𝒦, (ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
    rw [← hjoin]
    simp only [ggAutomizerJoin, Subgroup.map_sup, Subgroup.map_iSup]
  rcases hLpos with hLb | hLd | hLa
  · obtain ⟨K₀, hK₀⟩ := exists_mem_of_map_eq_bCoordinateBlock (p := p) (n := n) (Bs := Bs)
      (eta := eta) (L := L) (i0 := i0) (𝒦 := 𝒦) hp hp2 hsup hLb
    obtain ⟨y₀, hy₀⟩ := h𝒦 K₀ hK₀
    rcases htype y₀ K₀ hy₀ with ⟨j, hj⟩ | ⟨δ₀, hδ₀mem, hδ₀⟩
    · exact le_join_of_coordBlock_anchor (p := p) (n := n) (Bs := Bs) (x := x) (L := L)
        (i0 := i0) (eta := eta) (𝒦 := 𝒦) (Nb := Nb) hp hp2 hn hBs hL (Or.inl hLb) hfix hnorm
        htype hplane hx hy₀ hK₀ hj hyK
    · exact le_join_of_map_conj_anchor (p := p) (n := n) (Bs := Bs) (x := x) (L := L)
        (i0 := i0) (eta := eta) (𝒦 := 𝒦) (Nb := Nb) hp hp2 hn hBs hL hLb hfix hnorm htype
        hplane hx hy₀ hK₀ hδ₀mem hδ₀ hyK
  · obtain ⟨K₀, hK₀, j, hj⟩ := exists_bCoordinateBlock_of_d_or_a (p := p) (n := n) (Bs := Bs)
      (eta := eta) (L := L) (i0 := i0) (𝒦 := 𝒦) (Nb := Nb) hp hp2 hsup h𝒦 htype (Or.inl hLd)
    obtain ⟨y₀, hy₀⟩ := h𝒦 K₀ hK₀
    exact le_join_of_coordBlock_anchor (p := p) (n := n) (Bs := Bs) (x := x) (L := L)
      (i0 := i0) (eta := eta) (𝒦 := 𝒦) (Nb := Nb) hp hp2 hn hBs hL (Or.inr hLd) hfix hnorm
      htype hplane hx hy₀ hK₀ (Or.inl hj) hyK
  · obtain ⟨K₀, hK₀, j, hj⟩ := exists_bCoordinateBlock_of_d_or_a (p := p) (n := n) (Bs := Bs)
      (eta := eta) (L := L) (i0 := i0) (𝒦 := 𝒦) (Nb := Nb) hp hp2 hsup h𝒦 htype (Or.inr hLa)
    obtain ⟨y₀, hy₀⟩ := h𝒦 K₀ hK₀
    exact le_join_of_const_anchor (p := p) (n := n) (Bs := Bs) (x := x) (L := L) (eta := eta)
      (𝒦 := 𝒦) (Nb := Nb) hp hp2 hn hBs hL hLa hfix hnorm htype hplane hx hy₀ hK₀ hj hyK

end CFSG.StandardType

end
