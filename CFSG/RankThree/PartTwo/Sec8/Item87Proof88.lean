module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.PartTwo.Sec11.Item116FusionCases
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item87Proof

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_of_mem_closure {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {u v d : G} (huA : u ∈ A) (hvA : v ∈ A)
    (hd : d ∈ Subgroup.closure ({u, v} : Set G)) (hu1 : u ≠ 1)
    (hdu : d ∉ Subgroup.zpowers u) :
    Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {u} ≤
      Subgroup.centralizer {u} ⊓ Subgroup.centralizer {v} := by
  have hexp : ∀ w ∈ A, w ^ 3 = 1 := hA.2
  have hcomm : ∀ w ∈ A, ∀ z ∈ A, w * z = z * w := fun w hw z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨w, hw⟩ ⟨z, hz⟩)
  have hSA : Subgroup.closure ({u, v} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact huA
    · exact hvA
  have hdA : d ∈ A := hSA hd
  have h9 := Sec11.Item116Fusion.card_closure_pair_eq_nine hexp hcomm huA hdA hu1 hdu
  have hle9 := Sec10.card_closure_pair_le (hcomm u huA v hvA) (hexp u huA) (hexp v hvA)
  have hsub : Subgroup.closure ({u, d} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact hd
  have heq : Subgroup.closure ({u, d} : Set G) = Subgroup.closure ({u, v} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hsub (by omega)
  intro z hz
  obtain ⟨hzd, hzu⟩ := Subgroup.mem_inf.mp hz
  have hzS : z ∈ Subgroup.centralizer
      ((Subgroup.closure ({u, d} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hzu).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hzd).symm
  rw [heq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff] at hzS
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzS u (by simp)).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzS v (by simp)).symm

omit [Finite G] in
theorem mem_zpowers_of_mem_zpowers {a x : G} (ha3 : a ^ 3 = 1) (hx1 : x ≠ 1)
    (hx : x ∈ Subgroup.zpowers a) : a ∈ Subgroup.zpowers x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  rw [hk] at hx1 ⊢
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h, zpow_zero] at hx1
    exact absurd rfl hx1
  · rw [h, zpow_one]
    exact Subgroup.mem_zpowers a
  · rw [h]
    refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
    have e : a = (a ^ (2 : ℤ)) ^ (2 : ℤ) * (a ^ 3)⁻¹ := by group
    rw [ha3, inv_one, mul_one] at e
    exact e.symm

end Item87Proof


@[expose] def KF88Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧
        ∃ D ∈ thetaComponentsAt 3 d,
          inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ≤ D ∧
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ D ∧
          IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
          (∃ m : ℕ, 1 ≤ m ∧
            IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
              aschbacherSolvableCore 3
                (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
          KFacts.InducesStdKind
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field

@[expose] def KF88Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field ∧
        ¬ ⁅inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)),
            inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G))

theorem kF88Inner_of (h48 : Sec4.Item4_8) (hS : KF88Step) : KF88Inner := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY
  obtain ⟨d, hdS, hdx, hUq, htypeU, hUx, hlink⟩ := hS G A c L a b X n h Y hY hIJ x hx hxY
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hAn : ∃ k : ℕ, 3 ≤ k ∧ Nat.card A = 3 ^ k := ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hSA : Subgroup.closure ({c, b} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact h.mem_A
    · exact hbA
  have hdA : d ∈ A := hSA hdS
  have hd1 : d ≠ 1 := fun h1 => hdx (h1 ▸ Subgroup.one_mem _)
  have hxA : x ∈ A := by rcases hx with rfl | rfl; exacts [h.mem_A, hbA]
  have hx1 : x ≠ 1 := by rcases hx with rfl | rfl; exacts [h.ne_one, hb1]
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKmem, -, -⟩ :=
    Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt h.isGammaIndex
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdS).symm
  have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := by
    rcases hx with rfl | rfl
    · exact hKcb.trans inf_le_left
    · exact hKcb.trans inf_le_right
  have hCdx : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {x} ≤
      Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} := by
    rcases hx with rfl | rfl
    · exact Item87Proof.inf_centralizer_le_of_mem_closure hAel h.mem_A hbA hdS h.ne_one hdx
    · have hdS' : d ∈ Subgroup.closure ({x, c} : Set G) := by rwa [Set.pair_comm]
      rw [inf_comm (Subgroup.centralizer {c})]
      exact Item87Proof.inf_centralizer_le_of_mem_closure hAel hbA h.mem_A hdS' hb1 hdx
  have hKdx : K ∈ thetaComponentsIn (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {x}) := by
    obtain ⟨-, hK''⟩ := mem_thetaComponentsIn_iff.mp hKmem
    refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hKd hKx, ?_⟩
    exact PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hKd hKx) hCdx hK''
  have hUmem : U ∈ thetaComponentsIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {d}) :=
    Item87Proof.mem_thetaComponentsIn_residual hY hUq
  have hUda : U ∈ thetaComponentsIn (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {a}) := by
    rwa [inf_comm] at hUmem
  obtain ⟨D₁, hD₁, hUD₁⟩ := Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAel hAn
    hdA h.a_mem hd1 h.a_ne_one hUda
  obtain ⟨D₂, hD₂, hKD₂⟩ := Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAel hAn
    hdA hxA hd1 hx1 hKdx
  have heq := Item87Proof.eq_of_not_commutator_le hD₁ hD₂ hUD₁ hKD₂ hlink
  exact ⟨d, hdS, hdx, D₁, hD₁, hUD₁, heq ▸ hKD₂, hUq, htypeU, hUx⟩

theorem item88_of (h418 : Item418Theta) (h84 : Pair84A) (hF : KF84Field) (hI : KF88Inner) :
    Item88 := by
  intro G _ _ A c L a b X n h Y hY hIJ
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨hbA, hb1, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hY).1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  obtain ⟨hKmem, htypeK, -⟩ :=
    Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt h.isGammaIndex
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) :=
    (Item87Proof.residual_le _).trans (inf_le_left.trans hLc)
  have hKa : KFacts.InducesStdKind K a .field := hF G A c L a b X n h
  have houtL : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
  have houtX : Sec4.InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  have hac : a ∉ Subgroup.zpowers c := Item87Proof.not_mem_zpowers_of_inducesOuterTheta hLc houtL
  have hab : a ∉ Subgroup.zpowers b := Item87Proof.not_mem_zpowers_of_inducesOuterTheta hXb houtX
  have key : ∀ x : G, (x = c ∨ x = b) →
      ¬ (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) := by
    intro x hx hxY
    have hxA : x ∈ A := by rcases hx with rfl | rfl; exacts [h.mem_A, hbA]
    have hx1 : x ≠ 1 := by rcases hx with rfl | rfl; exacts [h.ne_one, hb1]
    have hx3 : x ^ 3 = 1 := hAel.2 x hxA
    have hax : a ∉ Subgroup.zpowers x := by rcases hx with rfl | rfl; exacts [hac, hab]
    have hxa : x ∉ Subgroup.zpowers a := fun hmem =>
      hax (Item87Proof.mem_zpowers_of_mem_zpowers ha3 hx1 hmem)
    have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := by
      rcases hx with rfl | rfl; exacts [hKc, hKb]
    obtain ⟨d, hdS, hdx, D, hD, hUD, hKD, hUq, ⟨m, hm, htypeU⟩, hUx⟩ :=
      hI G A c L a b X n h Y hY hIJ x hx hxY
    have hSA : Subgroup.closure ({c, b} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact h.mem_A
      · exact hbA
    have hdA : d ∈ A := hSA hdS
    have hd3 : d ^ 3 = 1 := hAel.2 d hdA
    have hd1 : d ≠ 1 := fun h1 => hdx (h1 ▸ Subgroup.one_mem _)
    have hDd : D ≤ Subgroup.centralizer ({d} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hD).1
    have haCd : a ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a h.a_mem d hdA)
    have hxCd : x ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hxA d hdA)
    have hCdx : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {x} ≤
        Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} := by
      rcases hx with rfl | rfl
      · exact Item87Proof.inf_centralizer_le_of_mem_closure hAel h.mem_A hbA hdS h.ne_one hdx
      · have hdS' : d ∈ Subgroup.closure ({x, c} : Set G) := by rwa [Set.pair_comm]
        rw [inf_comm (Subgroup.centralizer {c})]
        exact Item87Proof.inf_centralizer_le_of_mem_closure hAel hbA h.mem_A hdS' hb1 hdx
    have hKDx : K ∈ thetaComponentsIn (D ⊓ Subgroup.centralizer {x}) := by
      obtain ⟨-, hK''⟩ := mem_thetaComponentsIn_iff.mp hKmem
      refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hKD hKx, ?_⟩
      exact PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hKD hKx)
        ((inf_le_inf_right _ hDd).trans hCdx) hK''
    set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
    have hUa : U ≤ Subgroup.centralizer ({a} : Set G) :=
      (Item87Proof.residual_le _).trans (inf_le_left.trans hYa)
    have hUmem : U ∈ thetaComponentsIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {d}) :=
      Item87Proof.mem_thetaComponentsIn_residual hY hUq
    have hUDa : U ∈ thetaComponentsIn (D ⊓ Subgroup.centralizer {a}) := by
      obtain ⟨-, hU''⟩ := mem_thetaComponentsIn_iff.mp hUmem
      refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hUD hUa, ?_⟩
      refine PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hUD hUa) ?_ hU''
      rw [inf_comm (Subgroup.centralizer {a})]
      exact inf_le_inf_right _ hDd
    have h1 := (Item87Proof.item418_centralizer h418 hG hd3 hd1 haCd hxCd ha3 hx3
      (hcomm a h.a_mem x hxA) hx1 hax hD hKDx hn htypeK hKa).2
    have h2 := (Item87Proof.item418_centralizer h418 hG hd3 hd1 hxCd haCd hx3 ha3
      (hcomm x hxA a h.a_mem) h.a_ne_one hxa hD hUDa hm htypeU hUx).1
    exact h1 h2
  exact ⟨key c (Or.inl rfl), key b (Or.inr rfl)⟩

end CFSG.RankThree.PartTwo.Sec8
