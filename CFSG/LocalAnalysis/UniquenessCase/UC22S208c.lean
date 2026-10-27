module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def s208Delta (N K : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ g ∈ N, C = uc22p20bCj g K}

theorem s208c_mem_delta_self {N K : Subgroup G} : K ∈ s208Delta N K :=
  ⟨1, N.one_mem, (uc22p20b_cj_one K).symm⟩

theorem s208c_cj_mem_delta {N K C : Subgroup G} (hC : C ∈ s208Delta N K) {g : G} (hg : g ∈ N) :
    uc22p20bCj g C ∈ s208Delta N K := by
  obtain ⟨h, hh, rfl⟩ := hC
  exact ⟨g * h, N.mul_mem hg hh, uc22p20b_cj_cj g h K⟩

theorem s208c_frattini {H K S : Subgroup G} (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) {h : G} (hh : h ∈ H) :
    ∃ n ∈ H ⊓ normalizer (S : Set G), ∃ k ∈ K, h = n * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨hSK, hSp, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSH : S ≤ H := hSK.trans hKH
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf H) (K.subgroupOf H) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => hSK hx, hSp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  obtain ⟨S₀, hS₀⟩ := hS'
  have hF : Subgroup.normalizer (((S₀ : Subgroup ↥(K.subgroupOf H)).map
      (K.subgroupOf H).subtype : Subgroup ↥H) : Set ↥H) ⊔ K.subgroupOf H = ⊤ :=
    Sylow.normalizer_sup_eq_top S₀
  rw [hS₀] at hF
  have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
      K.subgroupOf H := by
    rw [hF]
    trivial
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hnG : (n : G) ∈ normalizer (S : Set G) := by
    have hn' := hn
    rw [Subgroup.mem_normalizer_iff] at hn' ⊢
    intro x
    constructor
    · intro hx
      exact (hn' ⟨x, hSH hx⟩).1 hx
    · intro hx
      have hxH : x ∈ H := by
        have h1 : (n : G) * x * (n : G)⁻¹ ∈ H := hSH hx
        have := H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      exact (hn' ⟨x, hxH⟩).2 hx
  exact ⟨n, ⟨n.2, hnG⟩, k, hk, congrArg Subtype.val hnk.symm⟩

section Context

variable (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) (h205 : S20_5 D)
  {L N K : Subgroup G} (hL : L ∈ calLStar D.T D.M) (hN : N ∈ calMOf (L ⊔ D.T))
  (hK : K ∈ calC L) (hLK : L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
include h1930 h205 hL hN hK hLK

omit hK hLK in
theorem s208c_mem_calLOf : L ∈ calLOf D.T D.M N :=
  s208a_mem_calLOf_of_calLStar D h1930 h205 hL (s208a_mem_hSet_of_mem_calMOf D hL.1 hN)
    (le_sup_left.trans hN.2)

omit h1930 h205 hL hK hLK in
theorem s208c_T_le : D.T ≤ N := le_sup_right.trans hN.2

theorem s208c_K_mem_comps : K ∈ s208Comps D N := by
  have h := s208b_cj_mem_comps_of_calLOf D (s208a_mem_hSet_of_mem_calMOf D hL.1 hN)
    (s208c_mem_calLOf D h1930 h205 hL hN) hK hLK D.T.one_mem
  rwa [uc22p20b_cj_one] at h

include h204 in
theorem s208c_delta_subset : s208Delta N K ⊆ s208Comps D N := by
  rintro C ⟨g, hg, rfl⟩
  exact s208b_cj_mem_comps D h1930 h204 (s208a_mem_hSet_of_mem_calMOf D hL.1 hN)
    (s208c_K_mem_comps D h1930 h205 hL hN hK hLK) hg

omit h1930 h205 hL hN hK hLK in
theorem s208c_le_normalizer_delta : N ≤ normalizer ((sSup (s208Delta N K) : Subgroup G) : Set G) :=
  s208b_le_normalizer_sSup fun _ hg _ hC => s208c_cj_mem_delta hC hg

include h204 in
theorem s208c_delta_le : sSup (s208Delta N K) ≤ N :=
  sSup_le fun _ hC => CFSG.Quasithin.le_of_mem_cComp
    (s208c_delta_subset D h1930 h204 h205 hL hN hK hLK hC).1

include h204 in
theorem s208c_normalizer_delta_eq :
    normalizer ((sSup (s208Delta N K) : Subgroup G) : Set G) = N := by
  have hKne : K ≠ ⊥ := CFSG.Quasithin.ne_bot_of_mem_cComp
    (s208c_K_mem_comps D h1930 h205 hL hN hK hLK).1
  refine s208a_normalizer_eq_of_normal hN.1 (s208a_mem_hSet_of_mem_calMOf D hL.1 hN).2.2
    (s208c_delta_le D h1930 h204 h205 hL hN hK hLK) s208c_le_normalizer_delta ?_
  intro h
  exact hKne (eq_bot_iff.2 (h ▸ le_sSup s208c_mem_delta_self))

include h204 in
theorem s208c_X_le_of_le_normalizer
    (hX : s208Gen D (normalizer (L : Set G)) ≤
      normalizer ((sSup (s208Delta N K) : Subgroup G) : Set G)) :
    s208Gen D (normalizer (L : Set G)) ≤ N := by
  rwa [s208c_normalizer_delta_eq D h1930 h204 h205 hL hN hK hLK] at hX

include h204 in
theorem s208c_X_le_of_subset_orbit
    (hsub : ∀ C ∈ s208Delta N K, ∃ t ∈ D.T, C = uc22p20bCj t K) :
    s208Gen D (normalizer (L : Set G)) ≤ N := by
  have hW : sSup (s208Delta N K) = L := by
    apply le_antisymm
    · refine sSup_le fun C hC => ?_
      obtain ⟨t, ht, rfl⟩ := hsub C hC
      rw [hLK]
      exact uc22p20b_cj_le_orb ht
    · rw [hLK]
      exact iSup_le fun t => le_sSup ⟨t, s208c_T_le D hN t.2, rfl⟩
  have h := s208c_normalizer_delta_eq D h1930 h204 h205 hL hN hK hLK
  rw [hW] at h
  rw [← h]
  exact s208a_gen_le D _

include h204 in
theorem s208c_X_le_of_fixed (hfix : ∀ C ∈ s208Delta N K, ∀ t ∈ D.T, uc22p20bCj t C = C) :
    s208Gen D (normalizer (L : Set G)) ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNH : N ∈ hSet D.T D.M := s208a_mem_hSet_of_mem_calMOf D hL.1 hN
  have hTN : D.T ≤ N := s208c_T_le D hN
  have hLN : L ∈ calLOf D.T D.M N := s208c_mem_calLOf D h1930 h205 hL hN
  have hLeqK : L = K := by
    rw [hLK]
    apply le_antisymm
    · exact iSup_le fun t => (hfix K s208c_mem_delta_self t t.2).le
    · have := uc22p20b_le_orb D.T K
      exact this
  set N₀ : Subgroup G := N ⊓ ⨅ C ∈ s208Delta N K, normalizer (C : Set G) with hN₀
  have hN₀N : N₀ ≤ N := inf_le_left
  have hmemN₀ : ∀ {x : G}, x ∈ N₀ ↔ x ∈ N ∧ ∀ C ∈ s208Delta N K, x ∈ normalizer (C : Set G) := by
    intro x
    simp only [hN₀, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hTN₀ : D.T ≤ N₀ := fun t ht =>
    hmemN₀.2 ⟨hTN ht, fun C hC =>
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix C hC t ht)⟩
  have hNnN₀ : N ≤ normalizer (N₀ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ {m : G}, m ∈ N → ∀ {y : G}, y ∈ N₀ → m * y * m⁻¹ ∈ N₀ := by
      intro m hm y hy
      obtain ⟨hyN, hyC⟩ := hmemN₀.1 hy
      refine hmemN₀.2 ⟨N.mul_mem (N.mul_mem hm hyN) (N.inv_mem hm), fun C hC => ?_⟩
      have hC' : uc22p20bCj m⁻¹ C ∈ s208Delta N K := s208c_cj_mem_delta hC (N.inv_mem hm)
      have h1 := s208a_cj_eq_of_mem_normalizer (hyC _ hC')
      refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
      show uc22p20bCj (m * y * m⁻¹) C = C
      have h2 : uc22p20bCj (m * y * m⁻¹) C = uc22p20bCj m (uc22p20bCj y (uc22p20bCj m⁻¹ C)) := by
        rw [uc22p20b_cj_cj, uc22p20b_cj_cj]
      rw [h2, h1, s208a_cj_cj_inv]
    constructor
    · exact key hn
    · intro hx
      have := key (N.inv_mem hn) hx
      simpa [mul_assoc] using this
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T N₀ := D.sylowG.of_le hTN₀ le_top
  have hconj : ∀ C ∈ s208Delta N K, ∃ g ∈ N ⊓ normalizer (D.T : Set G), C = uc22p20bCj g K := by
    rintro C ⟨h, hh, rfl⟩
    obtain ⟨n, hn, k, hk, rfl⟩ := s208c_frattini hN₀N hNnN₀ hTsyl hh
    refine ⟨n, hn, ?_⟩
    have hkK : uc22p20bCj k K = K :=
      s208a_cj_eq_of_mem_normalizer ((hmemN₀.1 hk).2 K s208c_mem_delta_self)
    rw [← uc22p20b_cj_cj, hkK]
  have hXn : ∀ C ∈ s208Delta N K,
      s208Gen D (normalizer (L : Set G)) ≤ normalizer (C : Set G) := by
    intro C hC
    obtain ⟨g, hg, rfl⟩ := hconj C hC
    have hstar : uc22p20bCj g K ∈ calLStar D.T D.M := by
      have := s208a_cj_mem_calLStar D hg.2 hL
      rwa [hLeqK] at this
    have hcomp : uc22p20bCj g K ∈ CFSG.Quasithin.cComp N :=
      (s208c_delta_subset D h1930 h204 h205 hL hN hK hLK hC).1
    have hle : uc22p20bCj g K ≤ normalizer (L : Set G) :=
      (CFSG.Quasithin.le_cCompSpan hcomp).trans (s208a_cCompSpan_le_normalizer_of_mem D hTN hLN)
    have hmem : uc22p20bCj g K ∈ calLOf D.T D.M (normalizer (L : Set G)) :=
      s208a_mem_calLOf_of_calLStar D h1930 h205 hstar (s208a_normalizer_mem_hSet D hL.1) hle
    exact (s208a_gen_le_cCompSpan D hL.1.1).trans
      (s208a_cCompSpan_le_normalizer_of_mem D hL.1.1 hmem)
  refine s208c_X_le_of_le_normalizer D h1930 h204 h205 hL hN hK hLK ?_
  exact s208b_le_normalizer_sSup fun x hx C hC => by
    rw [s208a_cj_eq_of_mem_normalizer (hXn C hC hx)]
    exact hC

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22
