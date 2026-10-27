module

public import CFSG.Quasithin.H13.U3S132210A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_mem_NV2_iff (S : A6.Setting134 G T L V) (g : ↥(normalizer (V : Set G))) :
    (g : G) ∈ normalizer (v2Of S : Set G) ↔ A6.InP2 (S.frame.ρ g) :=
  s134_normalizer_V2_iff S g.2

theorem s134_NLTV2_max (S : A6.Setting134 G T L V) (H : Subgroup G)
    (hMH : (L ⊔ T) ⊓ normalizer (v2Of S : Set G) ≤ H) (hHX : H ≤ L ⊔ T) :
    H = (L ⊔ T) ⊓ normalizer (v2Of S : Set G) ∨ H = L ⊔ T := by
  set M := (L ⊔ T) ⊓ normalizer (v2Of S : Set G) with hM
  by_cases hHM : H ≤ M
  · exact Or.inl (le_antisymm hHM hMH)
  right
  obtain ⟨h, hhH, hhM⟩ := IsConcreteLE.not_le_iff_exists.1 hHM
  obtain ⟨l, hl, t, ht, rfl⟩ := s134_mul_decomp S (hHX hhH)
  have htM : t ∈ M := ⟨mem_sup_right ht, s134_T_le_normalizer_V2 S ht⟩
  have hlH : l ∈ H := by
    have := H.mul_mem hhH (H.inv_mem (hMH htM))
    rwa [mul_inv_cancel_right] at this
  have hlM : l ∉ M := fun h' => hhM (M.mul_mem h' htM)
  set lN : ↥(normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  have hs1 : Perm.sign (S.frame.ρ lN) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨lN, hl, rfl⟩)
  have hsC : S.frame.ρ lN ∉ A6.P2sub ⊓ alternatingGroup (Fin 6) := fun hmem =>
    hlM ⟨mem_sup_left hl, (s134_mem_NV2_iff S lN).2 (mem_inf.1 hmem).1⟩
  set Y : Subgroup (Perm (Fin 6)) :=
    ((H ⊓ L).subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hY
  have hCY : A6.P2sub ⊓ alternatingGroup (Fin 6) ≤ Y := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (mem_inf.1 hσ).2
    have hgM : (g : G) ∈ M := ⟨mem_sup_left hgL,
      (s134_mem_NV2_iff S g).2 (by rw [hg]; exact (mem_inf.1 hσ).1)⟩
    exact ⟨g, mem_subgroupOf.2 ⟨hMH hgM, hgL⟩, hg⟩
  have hsY : S.frame.ρ lN ∈ Y := ⟨lN, mem_subgroupOf.2 ⟨hlH, hl⟩, rfl⟩
  have hA := alt6_le_of_overgroup24 A6.card_P2A6 inf_le_right hCY hsY hs1 hsC
  refine le_antisymm hHX (sup_le (fun l' hl' => ?_) fun t' ht' =>
    hMH ⟨mem_sup_right ht', s134_T_le_normalizer_V2 S ht'⟩)
  set l'N : ↥(normalizer (V : Set G)) := ⟨l', S.frame.L_le hl'⟩ with hl'N
  obtain ⟨g, hg, hgρ⟩ := hA ((S.frame.image_L _).1 ⟨l'N, hl', rfl⟩)
  have hgHL := mem_subgroupOf.1 hg
  have hk : S.frame.ρ (g⁻¹ * l'N) = 1 := by rw [map_mul, map_inv, hgρ, inv_mul_cancel]
  have hkM : ((g⁻¹ * l'N : ↥(normalizer (V : Set G))) : G) ∈ M := by
    refine ⟨mem_sup_left ?_, (s134_mem_NV2_iff S _).2 (by rw [hk]; decide)⟩
    simpa [hl'N] using L.mul_mem (L.inv_mem hgHL.2) hl'
  have := H.mul_mem hgHL.1 (hMH hkM)
  simpa [hl'N] using this

theorem s134_NLTV2_lt (S : A6.Setting134 G T L V) :
    (L ⊔ T) ⊓ normalizer (v2Of S : Set G) < L ⊔ T := by
  refine lt_of_le_of_ne inf_le_left fun h => ?_
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L (swap 0 2 * swap 1 4)).2
    (Perm.mem_alternatingGroup.2 (by decide))
  have hgN : (g : G) ∈ normalizer (v2Of S : Set G) := (h.symm.le (mem_sup_left hgL)).2
  have := (s134_mem_NV2_iff S g).1 hgN
  rw [hg] at this
  revert this
  decide

theorem s134_NLV2_le_L2T (S : A6.Setting134 G T L V) :
    L ⊓ normalizer (v2Of S : Set G) ≤ l2Of S ⊔ T := by
  have hTN : T ⊓ L ≤ L ⊓ normalizer (v2Of S : Set G) := fun t ht =>
    ⟨ht.2, s134_T_le_normalizer_V2 S ht.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ normalizer (v2Of S : Set G)) :=
    C1GN.isSylowTwoOf_of_le (s134_sylow_TL S) hTN inf_le_left
  have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  rw [← h, ← oTwoRes_eq_oTwoUpper]
  exact sup_le_sup le_rfl inf_le_left

theorem s134_L2T_eq_NLTV2 (S : A6.Setting134 G T L V) :
    l2Of S ⊔ T = (L ⊔ T) ⊓ normalizer (v2Of S : Set G) := by
  apply le_antisymm
  · exact le_inf (sup_le_sup_right (s134_L2_le_L S) T)
      (sup_le (s134_L2_le_normalizer_V2 S) (s134_T_le_normalizer_V2 S))
  · rintro x ⟨hx, hxN⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := s134_mul_decomp S hx
    have hlN : l ∈ normalizer (v2Of S : Set G) := by
      have := (normalizer (v2Of S : Set G)).mul_mem hxN
        ((normalizer (v2Of S : Set G)).inv_mem (s134_T_le_normalizer_V2 S ht))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (s134_NLV2_le_L2T S ⟨hl, hlN⟩) (mem_sup_right ht)

theorem s134_pCoreOf_L2T (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    pCoreOf 2 (l2Of S ⊔ T) = T ⊓ centralizer (v2Of S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro g hg
    have hgT := s134_R2_le_T S hg
    exact ⟨hgT, s134_mem_centralizer_V2_of_inE8 S ⟨g, S.frame.T_le hgT⟩
      (s134_rho_E8 S hg _)⟩
  · have hLT2 : l2Of S ⊔ T ≤ L ⊔ T := sup_le_sup_right (s134_L2_le_L S) T
    have hN2 : l2Of S ⊔ T ≤ normalizer (v2Of S : Set G) :=
      sup_le (s134_L2_le_normalizer_V2 S) (s134_T_le_normalizer_V2 S)
    have hXT : (l2Of S ⊔ T) ⊓ centralizer (v2Of S : Set G) ≤ T := by
      intro x hx
      have hxN : x ∈ normalizer (V : Set G) :=
        sup_le S.frame.L_le S.frame.T_le (hLT2 hx.1)
      have hE := s134_inE8_of_mem_centralizer_V2 S ⟨x, hxN⟩ hx.2
      exact s134_mem_T_of_inD6 S he (hLT2 hx.1) hxN (inD6_of_inE8 _ hE)
    have hXn : l2Of S ⊔ T ≤ normalizer
        (((l2Of S ⊔ T) ⊓ centralizer (v2Of S : Set G) : Subgroup G) : Set G) := fun y hy =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer hy, mem_normalizer_centralizer_of (hN2 hy)⟩
    have hX := le_pCoreOf_of_le_normalizer 2 inf_le_left hXn (S.h13.sylow.1.to_le hXT)
    exact fun x hx => hX ⟨mem_sup_right hx.1, hx.2⟩

theorem s134_lemma13_2_2_ten (hC137 : C137StatementFiveZ)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    CharNormal (baum T) (L ⊔ T) ∨
      (H13.IsA6Block L ∧ ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (L ⊔ T)) A →
        IsMaxElemAbelian T A) ∨
      ¬ thompsonJi T 1 ≤ centralizer (v2Of S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hQ := s134_cT S
  by_cases hJV : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ centralizer (V : Set G)
  ·
    left
    have hJQ : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← hQ]
      exact iSup₂_le fun A hA => le_inf hA.1 (hJV A hA)
    have hJeq := B6.thompsonJ_eq_of_le hJQ (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
    have hJB : thompsonJ (baum T) = thompsonJ T :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum _) inf_le_left
    refine ⟨thompsonJ T, B6.thompsonJ_le_baum _, ?_, ?_, ?_⟩
    · exact S1414.thompsonJ_ne_bot S.h13.sylow.1 fun h =>
        S.irr.2.1 (le_bot_iff.1 (h ▸ S.V_le_T))
    · rw [← hJB]
      exact S1414.characteristic_thompsonJ _
    · rw [← hJeq]
      exact (le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)
  by_cases hJ1 : thompsonJi T 1 ≤ centralizer (v2Of S : Set G)
  swap
  · exact Or.inr (Or.inr hJ1)
  push Not at hJV
  obtain ⟨A₀, hA₀, hA₀C⟩ := hJV
  obtain ⟨-, hA₀eq⟩ := s134_offender S he hJ1 hA₀ hA₀C
  have hJV2 : thompsonJ T ≤ T ⊓ centralizer (v2Of S : Set G) :=
    iSup₂_le fun A hA => le_inf hA.1 ((s134_le_thompsonJi_one S hA).trans hJ1)
  have hV2V : v2Of S ≤ V := S.pre_le_V _
  have hV2e : IsElemAbelian 2 (v2Of S) := B6.isElemAbelian_iff.2
    ⟨fun a ha b hb => (B6.isElemAbelian_iff.1 (s134_elemAbelian_V S)).1 a (hV2V ha) b (hV2V hb),
      fun a ha => (s134_elemAbelian_V S).2 a (hV2V ha)⟩
  have hbaum : baum T = baum (T ⊓ centralizer (v2Of S : Set G)) :=
    baum_eq_baum_centralizer hV2e (hV2V.trans S.V_le_T) hJV2
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hX := charTwo_sup_of_normalizes S.h13.sylow.1 S.T_le_NL hcharL
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => s134_mul_decomp S hx
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [S.irr.2.2.2.1]; exact S.irr.2.1
  have hM := s134_L2T_eq_NLTV2 S
  rcases hC137 G (L ⊔ T) T V L (l2Of S ⊔ T) ((L ⊔ T) ⊓ normalizer (v2Of S : Set G)) hX hTsyl
      hLT S.h13.faithful.1.2.1 hcharL (Or.inr (Or.inl he))
      (Or.inr (Or.inr (s134_alternatingNatural S))) le_sup_right hM.le (s134_NLTV2_lt S)
      (s134_NLTV2_max S) (Or.inl hM) (s134_reduced S) hVL
      (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, -, -, A, hA, hA2⟩
  · left
    rwa [s134_pCoreOf_L2T S he, ← hbaum] at h
  · refine Or.inr (Or.inl ⟨h.2.1 he, fun A hA => ?_⟩)
    have h3 := (B24_three (s134_elemAbelian_V S) S.V_le_T hA₀ hA₀eq).2.2.1
    rw [hQ] at h3
    exact h3 A hA
  · exact absurd h4 (s134_card_autOn_ne S)
  · exfalso
    have hAN : A ≤ normalizer (V : Set G) := hA.1.trans S.frame.T_le
    rw [card_autOn_eq_relIndex hAN] at hA2
    by_cases hAC : A ≤ centralizer (V : Set G)
    · rw [inf_eq_left.2 hAC, relIndex_self] at hA2
      omega
    · rw [(s134_offender S he hJ1 hA hAC).1] at hA2
      omega

end CFSG.Quasithin.H13.U3
