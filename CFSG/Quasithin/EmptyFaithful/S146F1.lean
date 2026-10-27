module

public import CFSG.Quasithin.EmptyFaithful.F918C1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.isHTM_conjClosure_sup_of_isHTM (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting146 G T M) {H K : Subgroup G} (hH : IsHTM T M H) (hK : K ∈ cComp H) :
    IsHTM T M (conjClosure K T ⊔ T) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hH.1.1
  have hle : conjClosure K T ⊔ T ≤ H := conjClosure_sup_le hKH hTH
  refine ⟨⟨le_sup_right, ?_⟩, fun hM => S.not_le_M_of_cComp h37 h38 hH hK
    (((le_conjClosure K T).trans le_sup_left).trans hM)⟩
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 H ≤ pCoreOf 2 (conjClosure K T ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((isSylowTwoOf_pCoreOf_le hsyl).trans le_sup_right)
      (hle.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  intro h0
  exact hH.1.2 (le_bot_iff.mp (h0 ▸ h1))

theorem hypF918_of_isHTM (h37 : A37ForSQTK) (h38 : A38ForSQTK) (S : Setting146 G T M)
    {H K : Subgroup G} (hH : IsHTM T M H) (hK : K ∈ cComp H) (hs : IsSimpleGroup (KBar K)) :
    HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (conjClosure K T ⊔ T) K := by
  have hHTM := S.isHTM_conjClosure_sup_of_isHTM h37 h38 hH hK
  have hF := S.lemma_14_5_14 (S.isHz_iff.mpr hHTM)
  have hKH : K ≤ conjClosure K T ⊔ T := (le_conjClosure K T).trans le_sup_left
  have hHle : conjClosure K T ⊔ T ≤ H := conjClosure_sup_le (le_of_mem_cComp hK) hH.1.1
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
  refine ⟨hF.2, cComp_mem_of_le hK hKH hHle, ?_, ?_, HypF918.K₀T_le_normalizer_K₀ T K⟩
  · exact isQuasisimple_of_perfect_of_isSimpleGroup
      (Group.IsPerfect.ofSurjective (G := K) (G' := KBar K)
        (f := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) (QuotientGroup.mk'_surjective _)) hs
  · exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right (le_inf le_sup_right le_sup_right)))
      (sup_le le_sup_left inf_le_right)

@[expose] def solvGen (T H : Subgroup G) : Subgroup G :=
  ⨆ (X : Subgroup G) (_ : T ≤ X ∧ X ≤ H ∧ Group.IsSolvable ↥X), X

omit [Finite G] in
theorem le_solvGen {T H X : Subgroup G} (hTX : T ≤ X) (hXH : X ≤ H) (hX : Group.IsSolvable ↥X) :
    X ≤ solvGen T H :=
  le_iSup₂_of_le X ⟨hTX, hXH, hX⟩ le_rfl

omit [Finite G] in
theorem solvGen_le {T H N : Subgroup G} (h : ∀ X : Subgroup G, T ≤ X → X ≤ H → Group.IsSolvable ↥X → X ≤ N) :
    solvGen T H ≤ N :=
  iSup₂_le fun X hX => h X hX.1 hX.2.1 hX.2.2

omit [Finite G] in
theorem solvGen_le_right {T H : Subgroup G} : solvGen T H ≤ H :=
  solvGen_le fun _ _ hXH _ => hXH

theorem Setting146.le_M_of_solvable (S : Setting146 G T M)
    (h1611 : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) {H X : Subgroup G}
    (hH : IsHTM T M H) (hTX : T ≤ X) (hXH : X ≤ H) (hX : Group.IsSolvable ↥X) : X ≤ M := by
  refine S.theorem_14_6_18 h1611 ⟨hTX, ?_⟩ hX
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 H ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((isSylowTwoOf_pCoreOf_le hsyl).trans hTX)
      (hXH.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  intro h0
  exact hH.1.2 (le_bot_iff.mp (h0 ▸ h1))

theorem Setting146.solvGen_le_M (S : Setting146 G T M)
    (h1611 : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) {H : Subgroup G}
    (hH : IsHTM T M H) : solvGen T H ≤ M :=
  solvGen_le fun _ hTX hXH hX => S.le_M_of_solvable h1611 hH hTX hXH hX

theorem Setting146.solvGen_ne (S : Setting146 G T M)
    (h1611 : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) {H : Subgroup G}
    (hH : IsHTM T M H) : solvGen T H ≠ H := fun heq =>
  hH.2 (heq ▸ S.solvGen_le_M h1611 hH)

theorem Setting146.mem_centralizer_of_odd (S : Setting146 G T M) {x : G} (hxM : x ∈ M)
    (hxG : x ∈ mcOf T) (hx : Odd (orderOf x)) : x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  set X : Subgroup G := M ⊓ mcOf T with hX
  set C : Subgroup G := M ⊓ Subgroup.centralizer (VZ T M : Set G) with hC
  set Q : Subgroup G := pCoreOf 2 X with hQ
  have hmm : X = C ⊔ Q := S.facts.mmc_eq
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hCG : Subgroup.centralizer (VZ T M : Set G) ≤ mcOf T :=
    (Subgroup.centralizer_le (by exact_mod_cast hZV)).trans
      ((Subgroup.centralizer_le_normalizer _).trans S.normalizer_Z.le)
  have hCX : C ≤ X := le_inf inf_le_left (inf_le_right.trans hCG)
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hXN : X ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans S.hyp1281.normalizer_VZ.ge
  have hXC : X ≤ Subgroup.normalizer (C : Set G) :=
    A1a.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_centralizer hXN)
  have hnorm : (C.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXC
  set π : ↥X →* ↥X ⧸ C.subgroupOf X := QuotientGroup.mk' (C.subgroupOf X) with hπ
  have htop : (⊤ : Subgroup ↥X) = C.subgroupOf X ⊔ Q.subgroupOf X := by
    rw [← Subgroup.subgroupOf_sup hCX hQX, ← hmm, Subgroup.subgroupOf_self]
  have hmapC : (C.subgroupOf X).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hmapQ : (Q.subgroupOf X).map π = ⊤ := by
    have h1 : (⊤ : Subgroup ↥X).map π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [htop, Subgroup.map_sup, hmapC, bot_sup_eq] at h1
    exact h1
  have hx' : x ∈ X := ⟨hxM, hxG⟩
  obtain ⟨q, hq, hqx⟩ : ∃ q ∈ Q.subgroupOf X, π q = π ⟨x, hx'⟩ := by
    have : π ⟨x, hx'⟩ ∈ (Q.subgroupOf X).map π := by rw [hmapQ]; exact Subgroup.mem_top _
    obtain ⟨q, hq, hqe⟩ := this
    exact ⟨q, hq, hqe⟩
  have hq2 : ∃ k : ℕ, orderOf (q : G) = 2 ^ k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp := (pCoreOf_isPGroup 2 X : IsPGroup 2 ↥(pCoreOf 2 X))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨(q : G), Subgroup.mem_subgroupOf.mp hq⟩
    exact ⟨k, by simpa using hk⟩
  obtain ⟨k, hk⟩ := hq2
  have h1 : orderOf (π ⟨x, hx'⟩) ∣ 2 ^ k := by
    rw [← hqx, ← hk]
    have := orderOf_map_dvd π q
    simpa using this
  have h2 : orderOf (π ⟨x, hx'⟩) ∣ orderOf x := by
    have := orderOf_map_dvd π ⟨x, hx'⟩
    simpa using this
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ hx.coprime_two_right
  have h3 : orderOf (π ⟨x, hx'⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  have h4 : π ⟨x, hx'⟩ = 1 := orderOf_eq_one_iff.mp h3
  have h5 : (⟨x, hx'⟩ : ↥X) ∈ C.subgroupOf X := (QuotientGroup.eq_one_iff _).mp h4
  exact (Subgroup.mem_subgroupOf.mp h5).2

theorem Setting146.pRank_three_le_one_of_le_M (S : Setting146 G T M) {H P : Subgroup G}
    (hH : IsHTM T M H) (hPH : P ≤ H) (hPM : P ≤ M) : CFSG.Open.pRank 3 P ≤ 1 := by
  have hPG : P ≤ mcOf T := hPH.trans (S.le_mcOf hH)
  unfold CFSG.Open.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ?_, by simp⟩ ?_
  · refine ⟨inferInstance, fun x hx => ?_⟩
    have : x = 1 := by simpa using hx
    simp [this]
  · rintro k ⟨E, hEP, hE, hk⟩
    have hEC : E ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      intro e he
      have h3 : e ^ 3 = 1 := hE.2 e he
      have hodd : Odd (orderOf e) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
      exact ⟨hPM (hEP he), S.mem_centralizer_of_odd (hPM (hEP he)) (hPG (hEP he)) hodd⟩
    exact (CFSG.Quasithin.le_pRank Nat.prime_three hEC hE hk).trans S.facts.m3_le

end CFSG.Quasithin
