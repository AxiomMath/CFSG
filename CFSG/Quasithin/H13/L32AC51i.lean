module

public import CFSG.Quasithin.H13.L32AC51h
public import CFSG.Quasithin.H13.L32AC51d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem false_of_four_five (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h4 : Lemma14_7_4_two_three) (h11 : Lemma14_7_11)
    (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h32 : Lemma14_7_32) (h47 : Lemma14_7_47)
    (h48 : Lemma14_7_48) (hMod : Lemma14_7_51_Mod) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hP : IsPSL n 2 1 (cStar K)) : False := by
  obtain ⟨K', hcK', hHKT, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  have hKn := le_normalizer_of_setting h37 h38 S hK (h32 _ T L V H S K hK)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_sln hP hKH hKn hTsylH
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  obtain ⟨i₀, hi₀, hi₀n, hPi⟩ := exists_node h1222 h1332 h1334 S (by omega) hL1K hker hD
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  by_cases hinn : ∀ t (ht : t ∈ T),
      β ⟨t, hTH ht⟩ ∈ (MulAut.conj : Lin.SLn n →* MulAut (Lin.SLn n)).range
  ·
    have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = MulAut.conj (π ⟨k, hk⟩) := by
      intro k hk
      apply MulEquiv.ext
      intro a
      obtain ⟨x, rfl⟩ := hπ a
      rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hInn : ∀ y : ↥H, β y ∈ (MulAut.conj : Lin.SLn n →* MulAut (Lin.SLn n)).range := by
      have hle : K ⊔ T ≤
          (((MulAut.conj : Lin.SLn n →* MulAut (Lin.SLn n)).range).comap β).map H.subtype :=
        sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨π ⟨k, hk⟩, (hKin k hk).symm⟩, rfl⟩)
          (fun t ht => ⟨⟨t, hTH ht⟩, hinn t ht, rfl⟩)
      rw [← hHKT] at hle
      intro y
      obtain ⟨y', hy', hyy'⟩ := hle y.2
      have e : y = y' := Subtype.ext hyy'.symm
      rw [e]
      exact hy'
    have hZ : Subgroup.center (cStar K) = ⊥ := by
      obtain ⟨φ⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
      have hc := card_center_eq_of_mulEquiv φ
      rw [Lin.center_eq_bot, Subgroup.card_bot] at hc
      exact Subgroup.card_eq_one.mp hc
    obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π hπ hker hKH hKn hHN MulAut.conj
      (Lin.conj_injective n) hInn fun x hx hxc => mem_pCoreOf_of_comm h28 S hcK' hL1K hKn hZ hx hxc
    have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = π ⟨k, hk⟩ := fun k hk =>
      Lin.conj_injective n (by rw [hψ, hKin k hk])
    have hψs : Function.Surjective ψ := by
      intro g
      obtain ⟨k, rfl⟩ := hπ g
      exact ⟨⟨k, hKH k.2⟩, hψK k k.2⟩
    have hψT : (T.subgroupOf H).map ψ = unitriangular n (ZMod 2) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine Lin.eq_uni_of_le (by omega)
        ((hTsylH.2.1.comap_of_injective H.subtype H.subtype_injective).map ψ) ?_
      rw [← hD]
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨s, hKH s.2⟩, hs, hψK s s.2⟩
    have hLT : l1 T L V ⊔ T ≤ preimG ψ (Lin.par n i₀) := by
      rw [← hPi]
      refine sup_le (fun x hx => mem_preimG.mpr ⟨hKH (hL1K hx), ?_⟩)
        (fun t ht => mem_preimG.mpr ⟨hTH ht, ?_⟩)
      · rw [hψK x (hL1K hx)]
        exact Subgroup.mem_sup_right ⟨⟨x, hL1K hx⟩, hx, rfl⟩
      · have h1 : ψ ⟨t, hTH ht⟩ ∈ (T.subgroupOf H).map ψ := ⟨⟨t, hTH ht⟩, ht, rfl⟩
        rw [hψT] at h1
        exact Subgroup.mem_sup_left h1
    exact false_of_inner h11 h29 S (by omega) hψs hψker hi₀ hi₀n hLT
  ·
    push Not at hinn
    obtain ⟨t₀, ht₀T, hout⟩ := hinn
    obtain ⟨hU, hPst⟩ := T_maps h1332 S hKn hHN hπ hker hD t₀ (hTH ht₀T) ht₀T
    rcases Lin.aut_dichotomy (by omega) (β ⟨t₀, hTH ht₀T⟩) hU with ⟨g, hg⟩ | hswap
    · exact hout ⟨g, hg.symm⟩
    · have hP' : ∀ g ∈ Lin.par n i₀, β ⟨t₀, hTH ht₀T⟩ g ∈ Lin.par n i₀ := by
        rw [← hPi]
        exact hPst
      have hni := Lin.eq_of_swap hswap hi₀ hi₀n hP'
      obtain rfl : n = 4 := by omega
      exact false_of_graph h1222 h1332 h1334 h4 h28 hMod S hcK' hHKT hL1K hP hKn hHN hπ hker
        (hTH ht₀T) hout

theorem lemma14_7_51_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h4 : Lemma14_7_4_two_three) (h11 : Lemma14_7_11)
    (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h32 : Lemma14_7_32) (h47 : Lemma14_7_47)
    (h48 : Lemma14_7_48) (hMod : Lemma14_7_51_Mod) : Lemma14_7_51 := by
  intro G _ _ T L V H S K hK n hP
  have hn := Lin.three_le_of_isPSL hP
  rcases (by omega : n = 3 ∨ (4 ≤ n ∧ n ≤ 5) ∨ 6 ≤ n) with rfl | ⟨hn4, hn5⟩ | hn6
  · exact not_isPSL_three_two h1222 h1332 h1334 h37 h38 h11 h28 h32 h47 h48 S hK hP
  · exact false_of_four_five h1222 h1332 h1334 h37 h38 h4 h11 h28 h29 h32 h47 h48 hMod S hK
      hn4 hn5 hP
  · exact false_of_six_le S hK hn6 hP

end CFSG.Quasithin.H13.L32A.C
