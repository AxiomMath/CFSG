module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup Equiv Equiv.Perm
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Alt36

theorem alternatingGroup_le_of_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {N : Subgroup (Perm Ω)}
    {A B : Finset Ω} {r : Ω} (hrA : r ∈ A) (hrB : r ∈ B) (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hA : 3 ≤ (A \ B).card) (hB : 3 ≤ (B \ A).card)
    (hNA : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z)
    (hNB : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ B → y ∈ B → z ∈ B → C3 N x y z) :
    alternatingGroup Ω ≤ N := by
  have hAB : A ≠ B := by
    rintro rfl
    simp at hA
  have hmem : ∀ C, C ∈ ({A, B} : Finset (Finset Ω)) ↔ C = A ∨ C = B := fun C => by simp
  refine alternatingGroup_le_of_family {A, B} (r := r) ?_ ?_ ?_ ?_
  · intro C hC
    rcases (hmem C).1 hC with rfl | rfl
    · exact hrA
    · exact hrB
  · intro x
    rcases hcov x with h | h
    · exact ⟨A, (hmem A).2 (Or.inl rfl), h⟩
    · exact ⟨B, (hmem B).2 (Or.inr rfl), h⟩
  · intro C hC
    rcases (hmem C).1 hC with rfl | rfl
    · rw [Finset.erase_insert (by simpa using hAB)]
      simpa using hA
    · rw [Finset.erase_insert_of_ne hAB, Finset.erase_singleton, Finset.insert_empty]
      simpa using hB
  · intro C hC
    rcases (hmem C).1 hC with rfl | rfl
    · exact hNA
    · exact hNB

theorem isThreeCycle_swap_mul_swap {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {x y z : Ω} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : (swap x y * swap y z).IsThreeCycle := by
  rw [swap_comm x y]
  exact isThreeCycle_swap_mul_swap_same (Ne.symm hxy) hyz hxz

end Alt36

namespace Hyp36

open Alt36 Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem normalizer_le_rankThreeGamma {X S : Subgroup G} (hXS : X ≤ S) (hX : 1 ≤ CFSG.Open.pRank 3 X) :
    normalizer (X : Set G) ≤ rankThreeGamma 1 3 S :=
  le_sSup ⟨X, hXS, hX, rfl⟩

theorem one_le_pRank_zpowers {x : G} (hx : orderOf x = 3) : 1 ≤ CFSG.Open.pRank 3 (zpowers x) :=
  CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
    (CFSG.Open.isElemAbelian_zpowers (p := 3) (by rw [← hx]; exact pow_orderOf_eq_one x))
    (by rw [Nat.card_zpowers, hx, pow_one])

theorem rankThreeGamma_eq_top_of_alt (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    {n : ℕ} (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n)) (hn : 13 ≤ n) :
    ∃ S : Sylow 3 G, rankThreeGamma 1 3 (S : Subgroup G) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : center ↥L = ⊥ := h.center_eq_bot L hL.1.1 (by omega) φ
  set ψ : ↥L →* alternatingGroup (Fin n) := φ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L)) with hψdef
  have hker : ψ.ker = center ↥L := by
    ext x
    simp [ψ, MonoidHom.mem_ker]
  have hψi : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 (hker.trans hZ)
  have hψs : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  set c : Fin 2 → alternatingGroup (Fin n) := fun i => tcyc hn (Fin.castLE (by norm_num) i) with hc
  have hc3 : ∀ i, ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle := fun i =>
    tcyc_isThreeCycle hn _
  have hcdisj : Disjoint ((c 0 : alternatingGroup (Fin n)) : Perm (Fin n)).support
      ((c 1 : alternatingGroup (Fin n)) : Perm (Fin n)).support :=
    tcyc_disjoint hn _ _ (by decide)
  have hccomm : c 0 * c 1 = c 1 * c 0 :=
    Subtype.ext (disjoint_iff_disjoint_support.2 hcdisj).commute.eq
  choose y hy using fun i => hψs (c i)
  have hyo : ∀ i, orderOf ((y i : ↥L) : G) = 3 := fun i => by
    rw [Subgroup.orderOf_coe, ← orderOf_injective ψ hψi, hy i, ← Subgroup.orderOf_coe, (hc3 i).orderOf]
  have hycomm : ((y 0 : ↥L) : G) * (y 1 : ↥L) = (y 1 : ↥L) * (y 0 : ↥L) := by
    have h1 : y 0 * y 1 = y 1 * y 0 := hψi (by rw [map_mul, map_mul, hy, hy, hccomm])
    exact congrArg Subtype.val h1
  have hX0 : IsPGroup 3 (zpowers ((y 0 : ↥L) : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo 0, pow_one])
  have hX1 : IsPGroup 3 (zpowers ((y 1 : ↥L) : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo 1, pow_one])
  have hXN : zpowers ((y 0 : ↥L) : G) ≤ normalizer (zpowers ((y 1 : ↥L) : G) : Set G) := by
    refine (Subgroup.zpowers_le).2 (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_left hycomm.symm k)).eq
  obtain ⟨S, hXS⟩ := (hX0.to_sup_of_normal_right' hX1 hXN).exists_le_sylow
  have hyS : ∀ i, ((y i : ↥L) : G) ∈ (S : Subgroup G) := by
    intro i
    fin_cases i
    · exact hXS (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact hXS (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine ⟨S, ?_⟩
  set Γ := rankThreeGamma 1 3 (S : Subgroup G) with hΓ
  have hcent : ∀ i, ∀ l : ↥L, l * y i = y i * l → (l : G) ∈ Γ := by
    intro i l hl
    refine normalizer_le_rankThreeGamma ((Subgroup.zpowers_le).2 (hyS i)) (one_le_pRank_zpowers (hyo i))
      (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hl' : Commute ((y i : ↥L) : G) (l : G) := (congrArg Subtype.val hl).symm
    exact (hl'.zpow_left k).eq
  set N : Subgroup (Perm (Fin n)) := ((Γ.subgroupOf L).map ψ).map (alternatingGroup (Fin n)).subtype with hN
  have hNi : ∀ i, ∀ k : Perm (Fin n), k.IsThreeCycle →
      Disjoint k.support ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).support → k ∈ N := by
    intro i k hk hkd
    obtain ⟨l, hl⟩ := hψs ⟨k, hk.mem_alternatingGroup⟩
    have hlc : l * y i = y i * l := by
      apply hψi
      rw [map_mul, map_mul, hl, hy]
      exact Subtype.ext (disjoint_iff_disjoint_support.2 hkd).commute.eq
    refine ⟨⟨k, hk.mem_alternatingGroup⟩, ⟨l, hcent i l hlc, hl⟩, rfl⟩
  have hC3 : ∀ i, ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).supportᶜ →
      y ∈ ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).supportᶜ →
      z ∈ ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).supportᶜ → C3 N x y z := by
    intro i x y z hxy hyz hxz hx hy' hz
    refine hNi i _ (isThreeCycle_swap_mul_swap hxy hyz hxz) (Finset.disjoint_left.2 fun w hw hwc => ?_)
    have hw' : w = y ∨ w = x ∨ w = z := by
      have h1 := eq_of_mem_support_swap_mul_swap (a := y) (b := x) (c := z) (by rwa [swap_comm y x])
      exact h1
    rcases hw' with rfl | rfl | rfl
    · exact Finset.mem_compl.1 hy' hwc
    · exact Finset.mem_compl.1 hx hwc
    · exact Finset.mem_compl.1 hz hwc
  have hval : ∀ i : Fin 2, ∀ x, x ∈ ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).support →
      3 * i.val + 1 ≤ x.val ∧ x.val ≤ 3 * i.val + 3 := by
    intro i x hx
    have h1 := val_of_mem_support_tcyc hn hx
    simpa using h1
  have hcard3 : ∀ i, (((c i : alternatingGroup (Fin n)) : Perm (Fin n)).support).card = 3 := fun i =>
    (hc3 i).card_support
  have hsd : ∀ i j : Fin 2, i ≠ j → ((c i : alternatingGroup (Fin n)) : Perm (Fin n)).supportᶜ \
      ((c j : alternatingGroup (Fin n)) : Perm (Fin n)).supportᶜ =
      ((c j : alternatingGroup (Fin n)) : Perm (Fin n)).support := by
    intro i j hij
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_compl, not_not]
    constructor
    · exact fun h => h.2
    · intro hx
      refine ⟨fun hxi => ?_, hx⟩
      have h1 := hval i x hxi
      have h2 := hval j x hx
      exact hij (Fin.ext (by omega))
  have hAlt : alternatingGroup (Fin n) ≤ N := by
    refine alternatingGroup_le_of_two (r := pt n 0 (by omega)) ?_ ?_ ?_ ?_ ?_ (hC3 0) (hC3 1)
    · rw [Finset.mem_compl]
      intro h0
      have := hval 0 _ h0
      simp [pt] at this
    · rw [Finset.mem_compl]
      intro h0
      have := hval 1 _ h0
      simp [pt] at this
    · intro x
      by_contra hx
      simp only [Finset.mem_compl, not_or, not_not] at hx
      exact Finset.disjoint_left.1 hcdisj hx.1 hx.2
    · rw [hsd 0 1 (by decide), hcard3]
    · rw [hsd 1 0 (by decide), hcard3]
  have hLΓ : L ≤ Γ := by
    intro l hl
    obtain ⟨k, ⟨l', hl'Γ, hl'⟩, hk⟩ := hAlt (ψ ⟨l, hl⟩).2
    have h1 : l' = ⟨l, hl⟩ := hψi (by rw [hl']; exact Subtype.ext hk)
    have h2 : (l' : G) = l := by rw [h1]
    rw [← h2]
    exact hl'Γ
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hL.2
  have hSL : 1 ≤ CFSG.Open.pRank 3 ((S : Subgroup G) ⊓ L) :=
    (one_le_pRank_zpowers (hyo 0)).trans (CFSG.SectionRank.pRank_mono (by norm_num)
      ((Subgroup.zpowers_le).2 (Subgroup.mem_inf.2 ⟨hyS 0, (y 0).2⟩)))
  rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top R]
  refine sup_le ?_ hLΓ
  have hRmap : ((R : Subgroup ↥L).map L.subtype : Set G) = (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [hR]
  rw [hRmap]
  exact normalizer_le_rankThreeGamma inf_le_left hSL

theorem twoLocalPrimeRank_le_of_star (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    {n : ℕ} (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n)) (hn : 13 ≤ n)
    (hstar : ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q G →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q S ⊤ →
        (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup G) (_ : Y ≤ S) (_ : 1 < CFSG.Open.pRank q Y),
          ⨆ N ∈ calMOf Y, N) ≠ ⊤ ∨
        (3 < q ∧ (3 ∣ Nat.card G → ∃ N : Subgroup G, IsStronglyPEmbedded 3 N))) :
    twoLocalPrimeRank 3 G ≤ 3 := by
  by_contra hcon
  obtain ⟨S, hS⟩ := h.rankThreeGamma_eq_top_of_alt hL φ hn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup G) ⊤ :=
    ⟨S.subtype le_top, by rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq]⟩
  rcases hstar 3 Nat.prime_three (by norm_num) (by omega) S hSyl with h1 | ⟨h1, -⟩
  · exact h1 (by rw [hS, top_sup_eq])
  · exact absurd h1 (lt_irrefl 3)

theorem k36Concl_of_alt_of_star (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (hLM : L ⊔ M = ⊤) {n : ℕ} (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n))
    (hn : 5 ≤ n)
    (hstar : ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q G →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q S ⊤ →
        (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup G) (_ : Y ≤ S) (_ : 1 < CFSG.Open.pRank q Y),
          ⨆ N ∈ calMOf Y, N) ≠ ⊤ ∨
        (3 < q ∧ (3 ∣ Nat.card G → ∃ N : Subgroup G, IsStronglyPEmbedded 3 N))) :
    K36Concl M p :=
  h.k36Concl_of_alt hL hne hLM φ hn fun hn13 => h.twoLocalPrimeRank_le_of_star hL φ hn13 hstar

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
