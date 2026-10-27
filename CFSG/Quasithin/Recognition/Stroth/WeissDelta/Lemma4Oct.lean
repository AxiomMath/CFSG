module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphFalse
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Half
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypesPolygon

public section

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y] [Finite Y]

theorem weissLemma4'_of_polygon8
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 8) (hW : WeissFree c.G0 c.graph 8)
    (hg : ((2 * 8 + 2 : ℕ) : ℕ∞) < c.graph.egirth) {a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m)
    (hK1 : ¬ IsPGroup 2 ↥((P1 ⊓ P2).subgroupOf P1).normalCore)
    (hK2 : ¬ IsPGroup 2 ↥((P2 ⊓ P1).subgroupOf P2).normalCore)
    (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    WeissLemma4' c.G0 c.graph 8 := by
  classical
  have hv1 : 3 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hv2 : 3 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hne : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w :=
    exists_adj_ne c hc hv1 hv2
  have hval : ∀ v w : c.Γ, c.graph.Adj v w →
      ∃ e : ℕ, Nat.card {y : c.Γ // c.graph.Adj v y ∧ y ≠ w} = 2 ^ e :=
    card_adj_ne_eq_two_pow c hc hV1 hV2
  have hthree : ∀ v w w' : c.Γ, c.graph.Adj v w → c.graph.Adj v w' →
      ∃ u, c.graph.Adj v u ∧ u ≠ w ∧ u ≠ w' := by
    intro v w w' _ _
    have hcard : 3 ≤ Nat.card (c.graph.neighborSet v) := by
      rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
      · rw [hv]; exact hv1
      · rw [hv]; exact hv2
    have hcard' : 3 ≤ (c.graph.neighborSet v).ncard := by
      rwa [Nat.card_coe_set_eq] at hcard
    by_contra hcon
    have hsub : c.graph.neighborSet v ⊆ ({w, w'} : Set c.Γ) := by
      intro u hu
      by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      exact hcon ⟨u, hu, hmem.1, hmem.2⟩
    have hle : (c.graph.neighborSet v).ncard ≤ ({w, w'} : Set c.Γ).ncard :=
      Set.ncard_le_ncard hsub
    have h2 : ({w, w'} : Set c.Γ).ncard ≤ 2 :=
      (Set.ncard_insert_le w {w'}).trans (by rw [Set.ncard_singleton])
    omega
  have hfacts := localFacts_of_polygon8 c hc hM hW hg ha hm hSz hL2 hV1 hV2
  have hLF : ∀ z : c.Γ, LocalFacts c.G0 c.graph z := fun z => (hfacts z).1
  have hZ : ∀ z : c.Γ, ZassenhausFacts c.G0 c.graph z := fun z => (hfacts z).2
  have hisLocal : ∀ g : c.G0,
      IsLocalSz c.G0 c.graph (g • c.xv) a ∧ IsLocalL2 c.G0 c.graph (g • c.lv) m :=
    fun g => isLocal_of_polygon8 c hc hM hW ha hm hSz hL2 hV1 hV2 g
  have hK : ∀ z : c.Γ, FixingNeighbourhoodFixesVertex (H := c.G0) (Γ := c.graph) z :=
    fun z => (hLF z).kernel_le
  have hR : ∀ z : c.Γ, RootFacts c.G0 c.graph 8 z := by
    intro z
    obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) z
    · rw [← hg]
      exact rootFacts_of_isLocalSz (n := 8) (by norm_num) hM hW hne hval hK ha
        (hisLocal g).1
    · rw [← hg]
      exact rootFacts_of_isLocalL2 (n := 8) (by norm_num) hM hW hne hval hK hm
        (hisLocal g).2
  have hloc : ∀ w u v : c.Γ, c.graph.Adj w u → c.graph.Adj w v →
      ∃ g : c.G0, g • w = w ∧ g • u = v := by
    intro w u v hwu hwv
    have h2tr : ∀ {a b a' b' : {x : c.Γ // c.graph.Adj w x}}, a ≠ b → a' ≠ b' →
        ∃ p : ↥(localGroup c.G0 c.graph w), p • a = a' ∧ p • b = b' := by
      obtain (⟨g, rfl⟩ | ⟨g, rfl⟩) := exists_smul_eq_xv_or_lv (c := c) w
      · exact MulAction.is_two_pretransitive_iff.mp (hisLocal g).1.2.1
      · exact MulAction.is_two_pretransitive_iff.mp (hisLocal g).2.2.1
    obtain ⟨b, hwb, hbu⟩ := exists_adj_ne c hc hv1 hv2 w u hwu
    obtain ⟨d, hwd, hdv⟩ := exists_adj_ne c hc hv1 hv2 w v hwv
    obtain ⟨p, hp1, hp2⟩ := h2tr (a := ⟨u, hwu⟩) (b := ⟨b, hwb⟩) (a' := ⟨v, hwv⟩)
      (b' := ⟨d, hwd⟩) (fun h => hbu (congrArg Subtype.val h).symm)
      (fun h => hdv (congrArg Subtype.val h).symm)
    obtain ⟨σ, hσ⟩ := p.2
    refine ⟨σ, MulAction.mem_stabilizer_iff.mp σ.2, ?_⟩
    have hp1' : (p.1 : Equiv.Perm {x : c.Γ // c.graph.Adj w x}) ⟨u, hwu⟩ = ⟨v, hwv⟩ := by
      simpa [Subgroup.smul_def] using hp1
    have h := congrArg (fun e : Equiv.Perm {x : c.Γ // c.graph.Adj w x} =>
      (e ⟨u, hwu⟩).1) hσ
    rw [localPermHom_apply] at h
    rw [hp1'] at h
    simpa using h
  intro w hw j hj0 hj8 z hzad hj1 hj2
  obtain ⟨W, hWwin⟩ := ClosedGoodPath.exists_of_noBack (n := 8) (by norm_num) hM hW hne hLF hw
  have hwin : W.window 0 9 = w := by
    apply GPath.ext'
    intro t ht
    rw [ClosedGoodPath.window_apply W 0 ht, zero_add]
    exact hWwin t ht
  have hstab : GPath.stabPath (H := c.G0) w = W.stab := by
    rw [← hwin]
    exact ClosedGoodPath.stabPath_window (n := 8) (by norm_num) hW hLF W 0
  have hW0 : W.x 0 = w 0 := hWwin 0 (by norm_num)
  have hker : W.kernelAt 0 = fixingSubgroup c.G0 (c.graph.neighborSet (w 0)) ⊓
      GPath.stabPath (H := c.G0) w := by
    rw [ClosedGoodPath.kernelAt, hW0, hstab]
  have hWi : W.x (j : ℤ) = w j := hWwin j (by omega)
  have hWim1 : W.x ((j : ℤ) - 1) = w (j - 1) := by
    rw [show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega]
    exact hWwin (j - 1) (by omega)
  have hWip1 : W.x ((j : ℤ) + 1) = w (j + 1) := by
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega]
    exact hWwin (j + 1) (by omega)
  obtain ⟨d, hdpos, hdvd, hd⟩ := W.exists_hasThirdFix_iff_dvd (n := 8) (by norm_num)
    hM hW hthree inf_le_right inf_le_left
  have hconv : ∀ i : ℤ, W.kernelAt 0 ≤ fixingSubgroup c.G0 (c.graph.neighborSet (W.x i)) ↔
      (d : ℤ) ∣ i := fun i =>
    ((W.hasThirdFix_iff_le (n := 8) (by norm_num) hW hLF hthree 0 i
      (hZ (W.x i))).symm).trans (hd i)
  have hdcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
    obtain ⟨k, hk, hdk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two (m := 3) (i := d)).mp (by simpa using hdvd)
    interval_cases k
    · exact Or.inl (by simpa using hdk)
    · exact Or.inr (Or.inl (by simpa using hdk))
    · exact Or.inr (Or.inr (Or.inl (by simpa using hdk)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hdk)))
  have hno : ¬ W.HasThirdFix (W.kernelAt 0) (j : ℤ) := by
    rcases hdcases with rfl | rfl | rfl | rfl
    ·
      intro _
      have h1 : W.HasThirdFix (W.kernelAt 0) (1 : ℤ) := (hd 1).mpr (by norm_num)
      have hle : W.kernelAt 0 ≤ fixingSubgroup c.G0 (c.graph.neighborSet (W.x 1)) :=
        (W.hasThirdFix_iff_le (n := 8) (by norm_num) hW hLF hthree 0 1
          (hZ (W.x 1))).mp h1
      have hbot : W.kernelAt 0 = ⊥ :=
        W.kernelAt_eq_bot_of_le_succ (n := 8) hW 0 hle
      have hnot : ¬ IsPGroup 2 ↥(W.kernelAt 0) :=
        W.not_isPGroup_kernelAt (n := 8) (by norm_num) hM hW hne hval hLF 0
          (not_isPGroup_fixingSubgroup c hc hK1 hK2 (W.x 0))
      rw [hbot] at hnot
      exact hnot IsPGroup.of_bot
    ·
      intro _
      have hQ : W.QuarterHyp :=
        { egirth := hg
          moufang := hM
          weissFree := hW
          ne := hne
          three := hthree
          val := hval
          loc := hloc
          localFacts := hLF
          zassenhaus := hZ
          rootFacts := hR
          notTwo := W.not_isPGroup_kernelAt (n := 8) (by norm_num) hM hW hne hval hLF 0
            (not_isPGroup_fixingSubgroup c hc hK1 hK2 (W.x 0))
          quarter := hconv }
      obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) (W.x 0)
      · have hSz0 : IsLocalSz c.G0 c.graph (W.x 0) a := by
          rw [← hg]
          exact (hisLocal g).1
        exact hQ.false_of_sz ha hSz0
      · have hL20 : IsLocalL2 c.G0 c.graph (W.x 0) m := by
          rw [← hg]
          exact (hisLocal g).2
        exact hQ.false_of_l2 hm hL20
    ·
      intro _
      have hfull : W.kernelAt 0 ≤ fixingSubgroup c.G0 (c.graph.neighborSet (W.x (4 : ℤ))) :=
        (hconv (4 : ℤ)).mpr (by norm_num)
      exact W.false_of_half (n := 8) (d := 4) (by norm_num) (by norm_num) hM hW hthree
        hLF hR hd hfull
    ·
      intro hthird
      have hdiv : (8 : ℤ) ∣ (j : ℤ) := (hd (j : ℤ)).mp hthird
      obtain ⟨k, hk⟩ := hdiv
      omega
  by_contra hcon
  push Not at hcon
  have hthird : W.HasThirdFix (W.kernelAt 0) (j : ℤ) := by
    refine ⟨z, ?_, ?_, ?_, fun g hg => hcon g ?_⟩
    · rwa [hWi]
    · rw [hWim1]
      exact hj1
    · rw [hWip1]
      exact hj2
    · rw [hker] at hg
      exact hg
  exact hno hthird

end CFSG.Quasithin.Stroth.WeissDelta

end
