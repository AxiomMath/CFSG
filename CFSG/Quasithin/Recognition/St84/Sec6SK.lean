module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen
public import CFSG.Quasithin.Recognition.St84.Sec6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem transitive_of_cover {v x y : V} {A B : Subgroup G}
    (hx : Γ.Adj v x) (hy : Γ.Adj v y) (hxy : x ≠ y)
    (h3 : 3 ≤ (Γ.neighborSet v).ncard)
    (hA : A ≤ MulAction.stabilizer G v) (hB : B ≤ MulAction.stabilizer G v)
    (hAt : ∀ a b : V, Γ.Adj v a → a ≠ x → Γ.Adj v b → b ≠ x → ∃ g ∈ A, g • a = b)
    (hBt : ∀ a b : V, Γ.Adj v a → a ≠ y → Γ.Adj v b → b ≠ y → ∃ g ∈ B, g • a = b) :
    ∀ a b : V, Γ.Adj v a → Γ.Adj v b → ∃ g ∈ A ⊔ B, g • a = b := by
  classical
  have hzex : ∃ z : V, Γ.Adj v z ∧ z ≠ x ∧ z ≠ y := by
    by_contra h
    push Not at h
    have hsub : Γ.neighborSet v ⊆ ({x, y} : Set V) := by
      intro z hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (h z hz hzx)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite ({x, y} : Set V))
    rw [Set.ncard_pair hxy] at hle
    omega
  have hfromx : ∀ c : V, Γ.Adj v c → ∃ g ∈ A ⊔ B, g • x = c := by
    intro c hc
    by_cases hcy : c = y
    · obtain ⟨z, hz, hzx, hzy⟩ := hzex
      obtain ⟨g, hgB, hgxz⟩ := hBt x z hx hxy hz hzy
      obtain ⟨h, hhA, hhy⟩ := hAt z y hz hzx hy hxy.symm
      refine ⟨h * g, Subgroup.mul_mem_sup hhA hgB, ?_⟩
      calc (h * g) • x = h • (g • x) := mul_smul h g x
        _ = h • z := by rw [hgxz]
        _ = y := hhy
        _ = c := hcy.symm
    · obtain ⟨g, hgB, hgxc⟩ := hBt x c hx hxy hc hcy
      exact ⟨g, Subgroup.mem_sup_right hgB, hgxc⟩
  intro a b ha hb
  by_cases hax : a = x
  · subst a
    exact hfromx b hb
  · by_cases hbx : b = x
    · obtain ⟨g, hg, hgxa⟩ := hfromx a ha
      refine ⟨g⁻¹, (A ⊔ B).inv_mem hg, ?_⟩
      calc g⁻¹ • a = g⁻¹ • (g • x) := by rw [hgxa]
        _ = x := by simp
        _ = b := hbx.symm
    · obtain ⟨g, hgA, hgab⟩ := hAt a b ha hax hb hbx
      exact ⟨g, Subgroup.mem_sup_left hgA, hgab⟩



namespace Setup


variable (X : Setup Γ G)

@[expose] def normGi (U : Subgroup G) (i : ℤ) : Subgroup G :=
  Subgroup.normalizer (U : Set G) ⊓ X.Gi i

@[expose] def skP (U : Subgroup G) : Subgroup G :=
  X.Q 1 ⊓ X.normGi U 0

structure IsSK (U : Subgroup G) : Prop where
  ne_bot : U ≠ ⊥
  le : U ≤ X.arcStab 0 2
  K_le : X.K ≤ Subgroup.normalizer (U : Set G)
  trans0 : ∀ a b : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) b →
    ∃ g ∈ X.normGi U 0, g • a = b
  trans2 : ∀ a b : V, Γ.Adj (X.vert 2) a → Γ.Adj (X.vert 2) b →
    ∃ g ∈ X.normGi U 2, g • a = b
  swap : ∃ g ∈ Subgroup.normalizer (U : Set G), g • X.vert 0 = X.vert 2

@[expose] def IsSKMax (U : Subgroup G) : Prop :=
  X.IsSK U ∧ ∀ U', X.IsSK U' → X.normGi U 0 ≤ X.normGi U' 0 → X.normGi U' 0 ≤ X.normGi U 0

theorem normGi_le_Gi (U : Subgroup G) (i : ℤ) : X.normGi U i ≤ X.Gi i :=
  inf_le_right

theorem normGi_le_normalizer (U : Subgroup G) (i : ℤ) :
    X.normGi U i ≤ Subgroup.normalizer (U : Set G) :=
  inf_le_left

theorem IsSK.K_le_normGi {X : Setup Γ G} {U : Subgroup G} (hU : X.IsSK U) (i : ℤ) :
    X.K ≤ X.normGi U i :=
  le_inf hU.K_le (X.K_le_Gi i)

theorem IsSK.pair {X : Setup Γ G} {U : Subgroup G} (hU : X.IsSK U) :
    ∀ g ∈ X.normGi U 1, g • X.vert 0 ∈ ({X.vert 0, X.vert 2} : Set V) := by
  classical
  intro g hg
  by_contra hgout
  have hg0 : g • X.vert 0 ≠ X.vert 0 := by
    intro h
    exact hgout (by simp [h])
  have hg2 : g • X.vert 0 ≠ X.vert 2 := by
    intro h
    exact hgout (by simp [h])
  obtain ⟨x₀, hx₀M, hx₀02⟩ := hU.swap
  have hx1adj : Γ.Adj (X.vert 2) (x₀ • X.vert 1) := by
    have h := (X.hyp.adj_smul x₀ (X.vert 1) (X.vert 0)).2 (X.adj 0).symm
    rw [hx₀02] at h
    exact h.symm
  obtain ⟨y, hyM2, hy⟩ := hU.trans2 (x₀ • X.vert 1) (X.vert 1) hx1adj (X.adj 1).symm
  have hxM1 : y * x₀ ∈ X.normGi U 1 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hyM2.1 hx₀M
    · rw [MulAction.mem_stabilizer_iff]
      calc (y * x₀) • X.vert 1 = y • (x₀ • X.vert 1) := mul_smul y x₀ _
        _ = X.vert 1 := hy
  have hx02 : (y * x₀) • X.vert 0 = X.vert 2 := by
    calc (y * x₀) • X.vert 0 = y • (x₀ • X.vert 0) := mul_smul y x₀ _
      _ = y • X.vert 2 := by rw [hx₀02]
      _ = X.vert 2 := MulAction.mem_stabilizer_iff.mp hyM2.2
  have hc_adj : Γ.Adj (X.vert 1) (g • X.vert 0) := by
    have h := (X.hyp.adj_smul g (X.vert 1) (X.vert 0)).2 (X.adj 0).symm
    simpa [MulAction.mem_stabilizer_iff.mp hg.2] using h
  have hc_mem : ∃ h ∈ X.normGi U 1, h • X.vert 0 = g • X.vert 0 := ⟨g, hg, rfl⟩
  have h0_mem : ∃ h ∈ X.normGi U 1, h • X.vert 0 = X.vert 0 := ⟨1, by simp, by simp⟩
  have h2_mem : ∃ h ∈ X.normGi U 1, h • X.vert 0 = X.vert 2 := ⟨y * x₀, hxM1, hx02⟩
  have horbit : ∀ b : V, Γ.Adj (X.vert 1) b →
      ∃ h ∈ X.normGi U 1, h • X.vert 0 = b := by
    intro b hb
    by_cases hb0 : b = X.vert 0
    · exact ⟨1, by simp, by simp [hb0]⟩
    by_cases hb2 : b = X.vert 2
    · exact ⟨y * x₀, hxM1, hx02.trans hb2.symm⟩
    by_cases hbc : b = g • X.vert 0
    · exact ⟨g, hg, hbc.symm⟩
    have hKsub : X.Ki 1 ≤ X.normGi U 1 := by
      intro k hk
      exact Subgroup.mem_inf.mpr ⟨hU.K_le hk.1, X.K_le_Gi 1 hk.1⟩
    have htr := X.Ki_transitive_gen 1 (a := g • X.vert 0) (b := b) hc_adj hb
      hg0 hg2 hb0 hb2
    obtain ⟨k, hk, hkab⟩ := htr
    refine ⟨k * g, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) (hKsub hk).1 hg.1
      · rw [MulAction.mem_stabilizer_iff]
        calc (k * g) • X.vert 1 = k • (g • X.vert 1) := mul_smul k g _
          _ = k • X.vert 1 := by rw [MulAction.mem_stabilizer_iff.mp hg.2]
          _ = X.vert 1 := MulAction.mem_stabilizer_iff.mp (hKsub hk).2
    · calc (k * g) • X.vert 0 = k • (g • X.vert 0) := mul_smul k g _
        _ = b := hkab

  have htrans1 : ∀ a b : V, Γ.Adj (X.vert 1) a → Γ.Adj (X.vert 1) b →
      ∃ h ∈ Subgroup.normalizer (U : Set G) ⊓ MulAction.stabilizer G (X.vert 1), h • a = b := by
    intro a b ha hb
    obtain ⟨ha', hha, hha0⟩ := horbit a ha
    obtain ⟨hb', hhb, hhb0⟩ := horbit b hb
    refine ⟨hb' * ha'⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hhb.1
          ((Subgroup.normalizer (U : Set G)).inv_mem hha.1)
      · rw [MulAction.mem_stabilizer_iff]
        calc (hb' * ha'⁻¹) • X.vert 1 = hb' • (ha'⁻¹ • X.vert 1) := mul_smul hb' ha'⁻¹ _
          _ = hb' • X.vert 1 := by
            rw [MulAction.mem_stabilizer_iff.mp
              ((MulAction.stabilizer G (X.vert 1)).inv_mem hha.2)]
          _ = X.vert 1 := MulAction.mem_stabilizer_iff.mp hhb.2
    · calc (hb' * ha'⁻¹) • a = hb' • (ha'⁻¹ • a) := mul_smul hb' ha'⁻¹ a
        _ = hb' • (ha'⁻¹ • (ha' • X.vert 0)) := by rw [hha0]
        _ = hb' • X.vert 0 := by rw [inv_smul_smul]
        _ = b := hhb0
  have hbot : U = ⊥ :=
    eq_bot_of_normalizer_trans X.hyp (X.adj (0 : ℤ))
      (hU.le.trans (le_inf
        (X.arcStab_le_Gi_left (by norm_num : (0 : ℤ) < 2))
        (X.arcStab_le_Gi_of_between (by norm_num : (0 : ℤ) ≤ 1)
          (by norm_num : (1 : ℤ) ≤ 2))))
      (fun a b ha hb => hU.trans0 a b ha hb) htrans1
  exact hU.ne_bot hbot


theorem IsSK.exists_swap₁ {X : Setup Γ G} {U : Subgroup G} (hU : X.IsSK U) :
    ∃ g ∈ X.normGi U 1,
      g • X.vert 0 = X.vert 2 ∧ g • X.vert 2 = X.vert 0 := by
  classical
  obtain ⟨x₀, hx₀M, hx₀02⟩ := hU.swap
  have hx1adj : Γ.Adj (X.vert 2) (x₀ • X.vert 1) := by
    have h := (X.hyp.adj_smul x₀ (X.vert 1) (X.vert 0)).2 (X.adj 0).symm
    rw [hx₀02] at h
    exact h.symm
  obtain ⟨y, hyM2, hy⟩ := hU.trans2 (x₀ • X.vert 1) (X.vert 1) hx1adj (X.adj 1).symm
  have hxM1 : y * x₀ ∈ X.normGi U 1 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hyM2.1 hx₀M
    · rw [MulAction.mem_stabilizer_iff]
      calc (y * x₀) • X.vert 1 = y • (x₀ • X.vert 1) := mul_smul y x₀ _
        _ = X.vert 1 := hy
  have hx02 : (y * x₀) • X.vert 0 = X.vert 2 := by
    calc (y * x₀) • X.vert 0 = y • (x₀ • X.vert 0) := mul_smul y x₀ _
      _ = y • X.vert 2 := by rw [hx₀02]
      _ = X.vert 2 := MulAction.mem_stabilizer_iff.mp hyM2.2
  have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hginv : (y * x₀)⁻¹ ∈ X.normGi U 1 := (X.normGi U 1).inv_mem hxM1
  have hmain : (y * x₀) • X.vert 2 = X.vert 0 := by
    have h := hU.pair ((y * x₀)⁻¹) hginv
    have hval : (y * x₀)⁻¹ • X.vert 0 ≠ X.vert 0 := by
      intro hz
      have hEq : X.vert 0 = (y * x₀) • ((y * x₀)⁻¹ • X.vert 0) := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [hz, hx02] at hEq
      exact h02 hEq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h0 | h2
    · exact absurd h0 hval
    · calc (y * x₀) • X.vert 2 = (y * x₀) • ((y * x₀)⁻¹ • X.vert 0) := by rw [h2]
        _ = X.vert 0 := by rw [← mul_smul, mul_inv_cancel, one_smul]
  exact ⟨y * x₀, hxM1, hx02, hmain⟩

theorem IsSK.inf₀₁ {X : Setup Γ G} {U : Subgroup G} (hU : X.IsSK U) :
    X.normGi U 0 ⊓ X.Gi 1 = X.normGi U 1 ⊓ X.Gi 2 := by
  classical
  obtain ⟨g, hgM1, hg02, hg20⟩ := hU.exists_swap₁
  have hgM : g ∈ Subgroup.normalizer (U : Set G) := hgM1.1
  have hgG1 : g ∈ X.Gi 1 := hgM1.2
  have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hfirst : X.normGi U 0 ⊓ X.Gi 1 ≤ X.normGi U 1 ⊓ X.Gi 2 := by
    intro x hx
    obtain ⟨hxN0, hxG1⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ Subgroup.normalizer (U : Set G) := hxN0.1
    have hxG0 : x ∈ X.Gi 0 := hxN0.2
    have hxg : x * g ∈ X.normGi U 1 := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hxM hgM
      · rw [MulAction.mem_stabilizer_iff]
        calc (x * g) • X.vert 1 = x • (g • X.vert 1) := mul_smul x g _
          _ = x • X.vert 1 := by rw [MulAction.mem_stabilizer_iff.mp hgG1]
          _ = X.vert 1 := MulAction.mem_stabilizer_iff.mp hxG1
    have hpair := hU.pair (x * g) hxg
    have hval : (x * g) • X.vert 0 = x • X.vert 2 := by
      rw [mul_smul, hg02]
    rw [hval] at hpair
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
    have hx2 : x ∈ X.Gi 2 := by
      rw [MulAction.mem_stabilizer_iff]
      rcases hpair with h0 | h2
      · exfalso
        have hx0 : x • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hxG0
        exact h02 (MulAction.injective x (h0.trans hx0.symm)).symm
      · exact h2
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxM, hxG1⟩, hx2⟩
  refine le_antisymm hfirst ?_
  intro x hx
  obtain ⟨hxN1, hxG2⟩ := Subgroup.mem_inf.mp hx
  have hxM : x ∈ Subgroup.normalizer (U : Set G) := hxN1.1
  have hxG1 : x ∈ X.Gi 1 := hxN1.2
  have hx2 : x • X.vert 2 = X.vert 2 := MulAction.mem_stabilizer_iff.mp hxG2
  have hyL : g * x * g⁻¹ ∈ X.normGi U 0 ⊓ X.Gi 1 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G))
          (Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hgM hxM)
          ((Subgroup.normalizer (U : Set G)).inv_mem hgM)
      · rw [MulAction.mem_stabilizer_iff]
        calc (g * x * g⁻¹) • X.vert 0 = g • (x • (g⁻¹ • X.vert 0)) := by simp only [mul_smul]
          _ = g • (x • X.vert 2) := by
            rw [show g⁻¹ • X.vert 0 = X.vert 2 from by
              calc g⁻¹ • X.vert 0 = g⁻¹ • (g • X.vert 2) := by rw [hg20]
                _ = X.vert 2 := by simp]
          _ = g • X.vert 2 := by rw [hx2]
          _ = X.vert 0 := hg20
    · rw [MulAction.mem_stabilizer_iff]
      calc (g * x * g⁻¹) • X.vert 1 = g • (x • (g⁻¹ • X.vert 1)) := by simp only [mul_smul]
        _ = g • (x • X.vert 1) := by
          rw [show g⁻¹ • X.vert 1 = X.vert 1 from
            MulAction.mem_stabilizer_iff.mp ((X.Gi 1).inv_mem hgG1)]
        _ = g • X.vert 1 := by rw [MulAction.mem_stabilizer_iff.mp hxG1]
        _ = X.vert 1 := MulAction.mem_stabilizer_iff.mp hgG1
  have hyR := hfirst hyL
  have hy2 : (g * x * g⁻¹) • X.vert 2 = X.vert 2 :=
    MulAction.mem_stabilizer_iff.mp hyR.2
  have hx0 : x • X.vert 0 = X.vert 0 := by
    have h : g • (x • (g⁻¹ • X.vert 2)) = X.vert 2 := by
      simpa only [mul_smul] using hy2
    rw [show g⁻¹ • X.vert 2 = X.vert 0 from by
      calc g⁻¹ • X.vert 2 = g⁻¹ • (g • X.vert 0) := by rw [hg02]
        _ = X.vert 0 := by simp] at h
    have h' : g • (x • X.vert 0) = g • X.vert 0 := by
      rw [h, hg02]
    exact MulAction.injective g h'
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxM, hx0⟩, hxG1⟩


theorem exists_isSKMax_above {U : Subgroup G} (hU : X.IsSK U) :
    ∃ U', X.IsSKMax U' ∧ X.normGi U 0 ≤ X.normGi U' 0 := by
  classical
  let A : Subgroup G := X.arcStab 0 2
  have hAfin : Finite ↥A :=
    finite_of_le_stabilizer X.hyp (H := A)
      (X.arcStab_le_Gi_of_between (by norm_num : (0 : ℤ) ≤ 1)
        (by norm_num : (1 : ℤ) ≤ 2))
  haveI : Finite ↥A := hAfin
  haveI : Finite (Subgroup ↥A) :=
    Finite.of_injective (fun H : Subgroup ↥A => (H : Set ↥A)) (by
      intro H K h
      exact Subgroup.ext (fun x => by
        simpa using Set.ext_iff.mp h x))
  let S : Set (Subgroup G) :=
    {V | X.IsSK V ∧ X.normGi U 0 ≤ X.normGi V 0}
  have hrange : (Set.range (fun H : Subgroup ↥A => H.map A.subtype)).Finite :=
    Set.finite_range _
  have hSfin : S.Finite := hrange.subset (by
    rintro V ⟨hV, -⟩
    exact ⟨V.subgroupOf A, Subgroup.map_subgroupOf_eq_of_le hV.le⟩)
  have hSne : S.Nonempty := ⟨U, hU, le_rfl⟩
  obtain ⟨V, hVS, hmax⟩ :=
    hSfin.exists_maximalFor (fun V : Subgroup G => Nat.card (X.normGi V 0)) S hSne
  refine ⟨V, ⟨hVS.1, ?_⟩, hVS.2⟩
  intro W hW hVW
  have hWS : W ∈ S := ⟨hW, hVS.2.trans hVW⟩
  haveI : Finite ↥(X.normGi W 0) :=
    finite_of_le_stabilizer X.hyp (H := X.normGi W 0) (X.normGi_le_Gi W 0)
  have hcardV : Nat.card (X.normGi V 0) ≤ Nat.card (X.normGi W 0) :=
    Subgroup.card_le_of_le hVW
  have hcardW : Nat.card (X.normGi W 0) ≤ Nat.card (X.normGi V 0) := hmax hWS hcardV
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hVW hcardW).symm


theorem isSylowTwoOf_inf_edgeSylow {A : Subgroup G} (i : ℤ) (hKA : X.K ≤ A)
    (hA : A ≤ X.Gi i ⊓ X.Gi (i + 1)) :
    IsSylowTwoOf (A ⊓ X.edgeSylow i) A := by
  classical
  obtain ⟨hpc, hsup⟩ := X.pCoreOf_eq_inf_edgeSylow i hKA hA
  have hKinf : X.K ⊓ (A ⊓ X.edgeSylow i) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hKA, X.K_inf_edgeSylow i]
  have hKnorm : X.K ≤ Subgroup.normalizer ((A ⊓ X.edgeSylow i : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (A ⊓ X.edgeSylow i) = A ⊓ X.edgeSylow i
    have hkA : conjSub k A = A := conjSub_eq_of_mem (hKA hk)
    have hkS : conjSub k (X.edgeSylow i) = X.edgeSylow i := by
      have hKedge : X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) :=
        (hKA.trans hA).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKedge hk)
    rw [conjSub_inf, hkA, hkS]
  have hsupP : (A ⊓ X.edgeSylow i) ⊔ X.K = A := by
    rw [← hpc, sup_comm]
    exact hsup
  have hcard : Nat.card ↥A = Nat.card ↥X.K * Nat.card ↥(A ⊓ X.edgeSylow i) := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A ⊓ X.edgeSylow i) X.K hKnorm
      (by rw [disjoint_iff, inf_comm]; exact hKinf)
    rw [hsupP, mul_comm] at h
    exact h
  haveI : Finite ↥(A ⊓ X.edgeSylow i) :=
    finite_of_le_stabilizer X.hyp (H := A ⊓ X.edgeSylow i)
      (inf_le_left.trans (hA.trans inf_le_left))
  have hrel : (A ⊓ X.edgeSylow i).relIndex A = Nat.card ↥X.K := by
    have hmul : (A ⊓ X.edgeSylow i).relIndex A * Nat.card ↥(A ⊓ X.edgeSylow i) =
        Nat.card ↥A := by
      have h := Subgroup.relIndex_mul_card (H := A ⊓ X.edgeSylow i) (K := A)
      rwa [inf_eq_left.mpr inf_le_left] at h
    have hmul' : (A ⊓ X.edgeSylow i).relIndex A * Nat.card ↥(A ⊓ X.edgeSylow i) =
        Nat.card ↥X.K * Nat.card ↥(A ⊓ X.edgeSylow i) := by
      rw [hmul, hcard]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul'
  refine F7.isSylowTwoOf_of_relIndex inf_le_left
    ((X.isPGroup_edgeSylow i).to_le inf_le_right) ?_
  rw [hrel]
  simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr X.odd_card_K)



theorem skP_eq_pCoreOf {U : Subgroup G} (hU : X.IsSK U) :
    X.skP U = pCoreOf 2 (X.normGi U 0 ⊓ X.Gi 1) := by
  classical
  set A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1 with hAdef
  have hKA : X.K ≤ A := le_inf (hU.K_le_normGi 0) (X.K_le_Gi 1)
  have hAGi : A ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (inf_le_left.trans (X.normGi_le_Gi U 0)) inf_le_right
  obtain ⟨hpc, -⟩ := X.pCoreOf_eq_inf_edgeSylow 0 hKA hAGi
  have hQ1S : X.Q 1 ≤ X.S := by
    simpa using X.Q_le_edgeSylow_right 1
  have hPA : X.skP U ≤ A := le_inf inf_le_right (inf_le_left.trans (X.Q_le_Gi 1))
  have hPS : X.skP U ≤ X.S := inf_le_left.trans hQ1S
  have hP_le : X.skP U ≤ A ⊓ X.edgeSylow 0 := by
    refine le_inf hPA ?_
    rwa [X.edgeSylow_zero]
  have hinf_le : A ⊓ X.edgeSylow 0 ≤ X.skP U := by
    intro x hx
    obtain ⟨hxA, hxS⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxM0, hxG1⟩ := Subgroup.mem_inf.mp hxA
    have hxM : x ∈ Subgroup.normalizer (U : Set G) := hxM0.1
    have hxG0 : x ∈ X.Gi 0 := hxM0.2
    have hSp : IsPGroup 2 X.S := by
      rw [← X.edgeSylow_zero]
      exact X.isPGroup_edgeSylow 0
    have hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hSp ⟨x, hxS⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨g, hgM1, hg02, hg20⟩ := hU.exists_swap₁
    have hxg : x * g ∈ X.normGi U 1 := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (U : Set G)) hxM hgM1.1
      · rw [MulAction.mem_stabilizer_iff]
        calc (x * g) • X.vert 1 = x • (g • X.vert 1) := mul_smul x g _
          _ = x • X.vert 1 := by rw [MulAction.mem_stabilizer_iff.mp hgM1.2]
          _ = X.vert 1 := MulAction.mem_stabilizer_iff.mp hxG1
    have hpair := hU.pair (x * g) hxg
    have hval : (x * g) • X.vert 0 = x • X.vert 2 := by rw [mul_smul, hg02]
    rw [hval] at hpair
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
    have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
      intro h
      have := X.vert_injective h
      norm_num at this
    have hx2fix : x • X.vert 2 = X.vert 2 := by
      rcases hpair with h0 | h2
      · exfalso
        have hx0 : x • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hxG0
        exact h02 (MulAction.injective x (h0.trans hx0.symm)).symm
      · exact h2
    have hleft : Γ.Adj (X.vert 1) (X.vert 0) := (X.adj 0).symm
    have hxQ1 : x ∈ X.Q 1 :=
      mem_pCoreOf_of_fixes_two X.hyp hxG1 hx2 hleft (X.adj 1) h02
        (MulAction.mem_stabilizer_iff.mp hxG0) hx2fix
    exact Subgroup.mem_inf.mpr ⟨hxQ1, hxM0⟩
  have hEq : X.skP U = A ⊓ X.edgeSylow 0 := le_antisymm hP_le hinf_le
  rw [hEq, hpc]


theorem normGi_zero_inf_one_eq_two {U : Subgroup G} (hU : X.IsSK U) :
    X.normGi U 0 ⊓ X.Gi 1 = X.normGi U 2 ⊓ X.Gi 1 := by
  rw [hU.inf₀₁]
  ext x
  simp only [Setup.normGi, Subgroup.mem_inf]
  tauto

theorem skP_eq_inf_two {U : Subgroup G} (hU : X.IsSK U) :
    X.skP U = X.Q 1 ⊓ X.normGi U 2 := by
  classical
  ext x
  simp only [Setup.skP, Setup.normGi, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxQ, hxN, hxG0⟩
    have hxG1 : x ∈ X.Gi 1 := X.Q_le_Gi 1 hxQ
    have hx1 : x ∈ X.normGi U 0 ⊓ X.Gi 1 := ⟨⟨hxN, hxG0⟩, hxG1⟩
    rw [hU.inf₀₁] at hx1
    exact ⟨hxQ, hxN, hx1.2⟩
  · rintro ⟨hxQ, hxN, hxG2⟩
    have hxG1 : x ∈ X.Gi 1 := X.Q_le_Gi 1 hxQ
    have hx2 : x ∈ X.normGi U 1 ⊓ X.Gi 2 := ⟨⟨hxN, hxG1⟩, hxG2⟩
    rw [← hU.inf₀₁] at hx2
    exact ⟨hxQ, hxN, hx2.1.2⟩

theorem normGi_zero_inf_one_normal_in_one {U : Subgroup G} (hU : X.IsSK U) :
    X.normGi U 1 ≤ Subgroup.normalizer ((X.normGi U 0 ⊓ X.Gi 1 : Subgroup G) : Set G) := by
  classical
  let A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1
  have hA2 : A = X.normGi U 2 ⊓ X.Gi 1 := by
    simpa [A] using normGi_zero_inf_one_eq_two X hU
  intro m hm
  obtain ⟨hmM, hmG1⟩ := Subgroup.mem_inf.mp hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub m A = A
  have hconjG1 : conjSub m (X.Gi 1) = X.Gi 1 := conjSub_eq_of_mem hmG1
  have hconjM : conjSub m (Subgroup.normalizer (U : Set G)) =
      Subgroup.normalizer (U : Set G) := conjSub_eq_of_mem hmM
  have hconjG0 : conjSub m (X.Gi 0) = X.Gi 0 ∨ conjSub m (X.Gi 0) = X.Gi 2 := by
    have hp := hU.pair m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h0 | h2
    · left
      rw [← stabilizer_smul_eq_conjSub, h0]
    · right
      rw [← stabilizer_smul_eq_conjSub, h2]
  rw [show A = X.normGi U 0 ⊓ X.Gi 1 from rfl, conjSub_inf, hconjG1,
    show X.normGi U 0 = Subgroup.normalizer (U : Set G) ⊓ X.Gi 0 from rfl,
    conjSub_inf, hconjM]
  rcases hconjG0 with hG0 | hG0
  · rw [hG0]
  · rw [hG0]
    exact hA2.symm

theorem isSylowTwoOf_skP_zero {U : Subgroup G} (hU : X.IsSK U) :
    IsSylowTwoOf (X.skP U) (X.normGi U 0) := by
  classical
  let M₀ : Subgroup G := X.normGi U 0
  let A : Subgroup G := M₀ ⊓ X.Gi 1
  have hKA : X.K ≤ A := le_inf (hU.K_le_normGi 0) (X.K_le_Gi 1)
  have hAGi : A ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (inf_le_left.trans (X.normGi_le_Gi U 0)) inf_le_right
  have hSylA : IsSylowTwoOf (A ⊓ X.edgeSylow 0) A :=
    X.isSylowTwoOf_inf_edgeSylow 0 hKA hAGi
  have hP_eq : X.skP U = A ⊓ X.edgeSylow 0 := by
    rw [skP_eq_pCoreOf X hU]
    exact (X.pCoreOf_eq_inf_edgeSylow 0 hKA hAGi).1
  have hSylPA : IsSylowTwoOf (X.skP U) A := hP_eq ▸ hSylA
  have hAM₀ : A ≤ M₀ := inf_le_left
  have hoddA : ¬ 2 ∣ A.relIndex M₀ := by
    have horbit : MulAction.orbit ↥M₀ (X.vert 1) = Γ.neighborSet (X.vert 0) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨m, rfl⟩
        have hm0 : (m : G) ∈ X.Gi 0 := (Subgroup.mem_inf.mp m.2).2
        have hadj : Γ.Adj (X.vert 0) ((m : G) • X.vert 1) := by
          have h := (X.hyp.adj_smul (m : G) (X.vert 0) (X.vert 1)).2 (X.adj 0)
          rwa [MulAction.mem_stabilizer_iff.mp hm0] at h
        simpa [SimpleGraph.mem_neighborSet, MulAction.subgroup_smul_def] using hadj
      · intro w hw
        obtain ⟨g, hg, hgw⟩ := hU.trans0 (X.vert 1) w (X.adj 0) hw
        exact ⟨⟨g, hg⟩, hgw⟩
    have hrel : A.relIndex M₀ = Nat.card (Γ.neighborSet (X.vert 0)) := by
      rw [show A = M₀ ⊓ X.Gi 1 from rfl, Subgroup.inf_relIndex_left,
        FanTree.relIndex_stabilizer_eq_ncard_orbit (H := M₀) (b := X.vert 1),
        horbit, Nat.card_coe_set_eq]
    rw [hrel, (X.hyp.valency (X.vert 0)).2]
    have hn : nOf Γ (X.vert 0) ≠ 0 := by
      have := (X.hyp.valency (X.vert 0)).1
      omega
    have hEven : Even (2 ^ nOf Γ (X.vert 0)) := by
      rw [Nat.even_pow' hn]
      exact even_two
    have hOdd : Odd (2 ^ nOf Γ (X.vert 0) + 1) := hEven.add_one
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hOdd
  have hP_A : X.skP U ≤ A := hP_eq.le.trans inf_le_left
  have hP_M₀ : X.skP U ≤ M₀ := hP_A.trans hAM₀
  have hoddP : ¬ 2 ∣ (X.skP U).relIndex A := by
    rw [hP_eq]
    exact hSylA.2.2
  refine F7.isSylowTwoOf_of_relIndex hP_M₀ (hP_eq.symm ▸ hSylA.2.1) ?_
  rw [← Subgroup.relIndex_mul_relIndex (X.skP U) A M₀ hP_A hAM₀]
  exact Nat.prime_two.not_dvd_mul hoddP hoddA


theorem isSylowTwoOf_skP_two {U : Subgroup G} (hU : X.IsSK U) :
    IsSylowTwoOf (X.skP U) (X.normGi U 2) := by
  classical
  let M₂ : Subgroup G := X.normGi U 2
  let A : Subgroup G := M₂ ⊓ X.Gi 1
  have hKA : X.K ≤ A := le_inf (hU.K_le_normGi 2) (X.K_le_Gi 1)
  have hAGi : A ≤ X.Gi 1 ⊓ X.Gi 2 :=
    le_inf inf_le_right (inf_le_left.trans (X.normGi_le_Gi U 2))
  have hSylA : IsSylowTwoOf (A ⊓ X.edgeSylow 1) A :=
    X.isSylowTwoOf_inf_edgeSylow 1 hKA hAGi
  have hAeq : X.normGi U 0 ⊓ X.Gi 1 = A := by
    rw [hU.inf₀₁]
    ext x
    simp only [A, M₂, Setup.normGi, Subgroup.mem_inf]
    tauto
  have hP_eq : X.skP U = A ⊓ X.edgeSylow 1 := by
    rw [skP_eq_pCoreOf X hU, hAeq]
    exact (X.pCoreOf_eq_inf_edgeSylow 1 hKA hAGi).1
  have hSylPA : IsSylowTwoOf (X.skP U) A := hP_eq ▸ hSylA
  have hAM₂ : A ≤ M₂ := inf_le_left
  have hoddA : ¬ 2 ∣ A.relIndex M₂ := by
    have horbit : MulAction.orbit ↥M₂ (X.vert 1) = Γ.neighborSet (X.vert 2) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨m, rfl⟩
        have hm2 : (m : G) ∈ X.Gi 2 := (Subgroup.mem_inf.mp m.2).2
        have hadj : Γ.Adj (X.vert 2) ((m : G) • X.vert 1) := by
          have h := (X.hyp.adj_smul (m : G) (X.vert 2) (X.vert 1)).2
            (show Γ.Adj (X.vert 2) (X.vert 1) from (X.adj 1).symm)
          rwa [MulAction.mem_stabilizer_iff.mp hm2] at h
        simpa [SimpleGraph.mem_neighborSet, MulAction.subgroup_smul_def] using hadj
      · intro w hw
        obtain ⟨g, hg, hgw⟩ := hU.trans2 (X.vert 1) w
          (show Γ.Adj (X.vert 2) (X.vert 1) from (X.adj 1).symm) hw
        exact ⟨⟨g, hg⟩, hgw⟩
    have hrel : A.relIndex M₂ = Nat.card (Γ.neighborSet (X.vert 2)) := by
      rw [show A = M₂ ⊓ X.Gi 1 from rfl, Subgroup.inf_relIndex_left,
        FanTree.relIndex_stabilizer_eq_ncard_orbit (H := M₂) (b := X.vert 1),
        horbit, Nat.card_coe_set_eq]
    rw [hrel, (X.hyp.valency (X.vert 2)).2]
    have hn : nOf Γ (X.vert 2) ≠ 0 := by
      have := (X.hyp.valency (X.vert 2)).1
      omega
    have hEven : Even (2 ^ nOf Γ (X.vert 2)) := by
      rw [Nat.even_pow' hn]
      exact even_two
    have hOdd : Odd (2 ^ nOf Γ (X.vert 2) + 1) := hEven.add_one
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hOdd
  have hP_A : X.skP U ≤ A := hP_eq.le.trans inf_le_left
  have hP_M₂ : X.skP U ≤ M₂ := hP_A.trans hAM₂
  have hoddP : ¬ 2 ∣ (X.skP U).relIndex A := by
    rw [hP_eq]
    exact hSylA.2.2
  refine F7.isSylowTwoOf_of_relIndex hP_M₂ (hP_eq.symm ▸ hSylA.2.1) ?_
  rw [← Subgroup.relIndex_mul_relIndex (X.skP U) A M₂ hP_A hAM₂]
  exact Nat.prime_two.not_dvd_mul hoddP hoddA

theorem QT_ne_bot (hGT : Even (Nat.card X.GT)) : X.QT ≠ ⊥ := by
  intro hbot
  have hGK : X.GT = X.K := by
    rw [(X.GT_eq_K_sup_QT).1, hbot, sup_bot_eq]
  rw [hGK] at hGT
  exact (Nat.not_even_iff_odd.mpr X.odd_card_K) hGT

theorem isSK_QT (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) : X.IsSK X.QT := by
  classical
  obtain ⟨m, hm, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hA₀M : X.arcStab 0 (2 * (m : ℤ)) ≤ Subgroup.normalizer (X.QT : Set G) :=
    X.arcStab_le_normalizer_QT_of_isMaxReg hreg
  unfold Setup.IsMaxReg at hreg
  obtain ⟨hm_lt, hleft0, hright0, _hextR0, _hextL0⟩ := hreg
  have hmpos : (0 : ℤ) < 2 * (m : ℤ) := hm_lt
  let A₀ : Subgroup G := X.arcStab 0 (2 * (m : ℤ))
  let A₁ : Subgroup G := X.arcStab (2 * (m : ℤ)) (4 * (m : ℤ))
  have hA₀G : A₀ ≤ X.Gi (2 * (m : ℤ)) :=
    X.arcStab_le_Gi_right hmpos
  have hτm : X.τ ^ (m : ℤ) ∈ Subgroup.normalizer (X.QT : Set G) :=
    zpow_mem X.tau_mem_normalizer_QT (m : ℤ)
  have hA₁eq : A₁ = conjSub (X.τ ^ (m : ℤ)) A₀ := by
    unfold A₁ A₀
    have h := X.arcStab_add (m : ℤ) 0 (2 * (m : ℤ))
    rw [show (0 : ℤ) + 2 * (m : ℤ) = 2 * (m : ℤ) by ring,
      show 2 * (m : ℤ) + 2 * (m : ℤ) = 4 * (m : ℤ) by ring] at h
    exact h
  have hA₁M : A₁ ≤ Subgroup.normalizer (X.QT : Set G) := by
    rw [hA₁eq]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem (Subgroup.normalizer (X.QT : Set G))
      (Subgroup.mul_mem _ hτm (hA₀M hy)) ((Subgroup.normalizer (X.QT : Set G)).inv_mem hτm)
  have hA₁G : A₁ ≤ X.Gi (2 * (m : ℤ)) :=
    X.arcStab_le_Gi_left (by linarith)
  have hA₀R : X.RightTransAt 0 (2 * (m : ℤ)) := hright0
  have hA₁L : X.LeftTransAt (2 * (m : ℤ)) (4 * (m : ℤ)) := by
    have h := X.leftTransAt_add (m : ℤ) 0 (2 * (m : ℤ)) hleft0
    rwa [show (0 : ℤ) + 2 * (m : ℤ) = 2 * (m : ℤ) by ring,
      show 2 * (m : ℤ) + 2 * (m : ℤ) = 4 * (m : ℤ) by ring] at h
  have h3 : 3 ≤ (Γ.neighborSet (X.vert (2 * (m : ℤ)))).ncard := by
    rw [← Nat.card_coe_set_eq]
    have hval := X.hyp.valency (X.vert (2 * (m : ℤ)))
    rw [hval.2]
    have h2 : 2 ≤ 2 ^ nOf Γ (X.vert (2 * (m : ℤ))) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ nOf Γ (X.vert (2 * (m : ℤ))) := Nat.pow_le_pow_right (by norm_num) hval.1
    omega
  have hxadj : Γ.Adj (X.vert (2 * (m : ℤ))) (X.vert (2 * (m : ℤ) - 1)) := by
    simpa [show 2 * (m : ℤ) - 1 + 1 = 2 * (m : ℤ) by ring]
      using (X.adj (2 * (m : ℤ) - 1)).symm
  have hyadj : Γ.Adj (X.vert (2 * (m : ℤ))) (X.vert (2 * (m : ℤ) + 1)) := X.adj _
  have hxy : X.vert (2 * (m : ℤ) - 1) ≠ X.vert (2 * (m : ℤ) + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hHtrans : ∀ a b : V, Γ.Adj (X.vert (2 * (m : ℤ))) a →
      Γ.Adj (X.vert (2 * (m : ℤ))) b →
      ∃ h ∈ A₀ ⊔ A₁, h • a = b :=
    transitive_of_cover (A := A₀) (B := A₁) hxadj hyadj hxy h3 hA₀G hA₁G
      hA₀R hA₁L
  have hHle : A₀ ⊔ A₁ ≤ X.normGi X.QT (2 * (m : ℤ)) :=
    le_inf (sup_le hA₀M hA₁M) (sup_le hA₀G hA₁G)
  have transport : ∀ (c : ℤ) (t : G), t ∈ Subgroup.normalizer (X.QT : Set G) →
      t • X.vert (2 * (m : ℤ)) = X.vert c →
      ∀ a b : V, Γ.Adj (X.vert c) a → Γ.Adj (X.vert c) b →
        ∃ g ∈ X.normGi X.QT c, g • a = b := by
    intro c t htM htc a b ha hb
    have htc' : t⁻¹ • X.vert c = X.vert (2 * (m : ℤ)) := by
      rw [← htc]; simp
    have ha' : Γ.Adj (X.vert (2 * (m : ℤ))) (t⁻¹ • a) := by
      have h := (X.hyp.adj_smul t⁻¹ (X.vert c) a).2 ha
      rwa [htc'] at h
    have hb' : Γ.Adj (X.vert (2 * (m : ℤ))) (t⁻¹ • b) := by
      have h := (X.hyp.adj_smul t⁻¹ (X.vert c) b).2 hb
      rwa [htc'] at h
    obtain ⟨h, hhH, hhab⟩ := hHtrans (t⁻¹ • a) (t⁻¹ • b) ha' hb'
    have hhN : h ∈ Subgroup.normalizer (X.QT : Set G) := (Subgroup.mem_inf.mp (hHle hhH)).1
    have hhG : h ∈ X.Gi (2 * (m : ℤ)) := (Subgroup.mem_inf.mp (hHle hhH)).2
    have hhfix : h • X.vert (2 * (m : ℤ)) = X.vert (2 * (m : ℤ)) :=
      MulAction.mem_stabilizer_iff.mp hhG
    refine ⟨t * h * t⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem (Subgroup.normalizer (X.QT : Set G))
          (Subgroup.mul_mem _ htM hhN) ((Subgroup.normalizer (X.QT : Set G)).inv_mem htM)
      · rw [MulAction.mem_stabilizer_iff]
        calc (t * h * t⁻¹) • X.vert c = t • (h • (t⁻¹ • X.vert c)) := by simp only [mul_smul]
          _ = t • (h • X.vert (2 * (m : ℤ))) := by rw [htc']
          _ = t • X.vert (2 * (m : ℤ)) := by rw [hhfix]
          _ = X.vert c := htc
    · calc (t * h * t⁻¹) • a = t • (h • (t⁻¹ • a)) := by simp only [mul_smul]
        _ = t • (t⁻¹ • b) := by rw [hhab]
        _ = b := by simp
  have htrans0 : ∀ a b : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) b →
      ∃ g ∈ X.normGi X.QT 0, g • a = b := by
    have htc : X.τ ^ (-(m : ℤ)) • X.vert (2 * (m : ℤ)) = X.vert 0 := by
      have h := X.zpow_smul_vert (-(m : ℤ)) (2 * (m : ℤ))
      simpa [show 2 * (m : ℤ) + 2 * (-(m : ℤ)) = (0 : ℤ) by ring] using h
    exact transport 0 (X.τ ^ (-(m : ℤ)))
      (zpow_mem X.tau_mem_normalizer_QT (-(m : ℤ))) htc
  have htrans2 : ∀ a b : V, Γ.Adj (X.vert 2) a → Γ.Adj (X.vert 2) b →
      ∃ g ∈ X.normGi X.QT 2, g • a = b := by
    have htc : X.τ ^ (1 - (m : ℤ)) • X.vert (2 * (m : ℤ)) = X.vert 2 := by
      have h := X.zpow_smul_vert (1 - (m : ℤ)) (2 * (m : ℤ))
      simpa [show 2 * (m : ℤ) + 2 * (1 - (m : ℤ)) = (2 : ℤ) by ring] using h
    exact transport 2 (X.τ ^ (1 - (m : ℤ)))
      (zpow_mem X.tau_mem_normalizer_QT (1 - (m : ℤ))) htc
  refine ⟨X.QT_ne_bot hGT, ?_, X.K_le_normalizer_QT, htrans0, htrans2, ?_⟩
  ·
    refine X.le_arcStab_of_fixSet ?_
    intro i hi
    rw [Set.mem_Icc] at hi
    exact fun q hq => X.QT_fixes_vert i hq
  ·
    exact ⟨X.τ, X.tau_mem_normalizer_QT, by simpa using X.zpow_smul_vert 1 0⟩

theorem IsSKMax.noCharNormal {U : Subgroup G} (hU : X.IsSKMax U) :
    NoCharNormal (X.skP U) (X.normGi U 0) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro C hCP hCne hCchar hM0norm
  let M : Subgroup G := Subgroup.normalizer (U : Set G)
  let P : Subgroup G := X.skP U
  let M₀ : Subgroup G := X.normGi U 0
  let M₁ : Subgroup G := X.normGi U 1
  let M₂ : Subgroup G := X.normGi U 2
  let A : Subgroup G := M₀ ⊓ X.Gi 1
  have hC_P : C ≤ P := hCP
  have hC_M₀ : C ≤ M₀ := hC_P.trans inf_le_right
  have hC_M : C ≤ M := hC_M₀.trans inf_le_left
  have hC_G0 : C ≤ X.Gi 0 := hC_M₀.trans inf_le_right
  have hC_G1 : C ≤ X.Gi 1 := hC_P.trans (inf_le_left.trans (X.Q_le_Gi 1))
  have hC_G2 : C ≤ X.Gi 2 :=
    hC_P.trans (inf_le_left.trans ((X.Q_le_Gi_adj 1).trans inf_le_right))
  have hC_arc : C ≤ X.arcStab 0 2 := by
    rw [X.arcStab_eq_inf (by norm_num : (0 : ℤ) ≤ 2)]
    exact le_inf hC_G0 hC_G2
  have hCnormP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf P).Characteristic := hCchar
    have hmap : (C.subgroupOf P).map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := P) (K := C.subgroupOf P)
    rwa [hmap] at h
  have hA_normal : M₁ ≤ Subgroup.normalizer (A : Set G) :=
    normGi_zero_inf_one_normal_in_one X hU.1
  have hP_normal : M₁ ≤ Subgroup.normalizer (P : Set G) := by
    have hP_eq : P = pCoreOf 2 A := by
      simpa [P, A, M₀] using skP_eq_pCoreOf X hU.1
    rw [hP_eq]
    exact hA_normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
  have hC_normal₁ : M₁ ≤ Subgroup.normalizer (C : Set G) := hP_normal.trans hCnormP
  obtain ⟨t, htM1, ht02, _ht20⟩ := hU.1.exists_swap₁
  have htM : t ∈ M := htM1.1
  have htN : t ∈ Subgroup.normalizer (C : Set G) := hC_normal₁ htM1
  have hM₂_eq : M₂ = conjSub t M₀ := by
    change Subgroup.normalizer (U : Set G) ⊓ X.Gi 2 =
      conjSub t (Subgroup.normalizer (U : Set G) ⊓ X.Gi 0)
    rw [conjSub_inf, conjSub_eq_of_mem htM, ← stabilizer_smul_eq_conjSub, ht02]
  have hM₂_normal : M₂ ≤ Subgroup.normalizer (C : Set G) := by
    intro m hm
    rw [hM₂_eq] at hm
    have hm0 : t⁻¹ * m * t ∈ M₀ := mem_conjSub.mp hm
    have hm_eq : m = t * (t⁻¹ * m * t) * t⁻¹ := by group
    rw [hm_eq]
    exact Subgroup.mul_mem (Subgroup.normalizer (C : Set G))
      (Subgroup.mul_mem (Subgroup.normalizer (C : Set G)) htN (hM0norm hm0))
      ((Subgroup.normalizer (C : Set G)).inv_mem htN)
  have hC_SK : X.IsSK C := by
    refine ⟨hCne, hC_arc, ?_, ?_, ?_, ?_⟩
    · exact (hU.1.K_le_normGi 0).trans hM0norm
    · intro a b ha hb
      obtain ⟨g, hg, hgab⟩ := hU.1.trans0 a b ha hb
      exact ⟨g, Subgroup.mem_inf.mpr ⟨hM0norm hg, hg.2⟩, hgab⟩
    · intro a b ha hb
      obtain ⟨g, hg, hgab⟩ := hU.1.trans2 a b ha hb
      exact ⟨g, Subgroup.mem_inf.mpr ⟨hM₂_normal hg, hg.2⟩, hgab⟩
    · exact ⟨t, hC_normal₁ htM1, ht02⟩
  have hle_max : M₀ ≤ X.normGi C 0 := by
    intro m hm
    exact Subgroup.mem_inf.mpr ⟨hM0norm hm, hm.2⟩
  have hM0C_le : X.normGi C 0 ≤ M₀ := hU.2 C hC_SK hle_max
  have hM0_eq : X.normGi C 0 = M₀ := le_antisymm hM0C_le hle_max
  have hSylM₀ : IsSylowTwoOf P M₀ := isSylowTwoOf_skP_zero X hU.1
  have hPG0 : P ≤ X.Gi 0 := hSylM₀.1.trans inf_le_right
  let N₀ : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ X.Gi 0
  have hPN₀ : P ≤ N₀ := le_inf Subgroup.le_normalizer hPG0
  have hN₀M₀ : N₀ ≤ M₀ := by
    intro n hn
    obtain ⟨hnN, hnG0⟩ := Subgroup.mem_inf.mp hn
    rw [← hM0_eq]
    exact Subgroup.mem_inf.mpr ⟨hCnormP hnN, hnG0⟩
  have hSylN₀ : IsSylowTwoOf P N₀ :=
    F7.isSylowTwoOf_mono_right hSylM₀ hPN₀ hN₀M₀
  have hPnormalN₀ : (P.subgroupOf N₀).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left
  haveI : Finite ↥N₀ := finite_of_le_stabilizer X.hyp (H := N₀) inf_le_right
  have hSylG₀ : IsSylowTwoOf P (X.Gi 0) := by
    refine F7.isSylowTwoOf_of_relIndex hPG0 hSylM₀.2.1 ?_
    by_contra h2dvd
    haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
    obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowTwoOf_ge_of_finite (J := X.Gi 0)
      hSylM₀.2.1 hPG0
    have hPneQ : P ≠ Q := by
      intro heq
      have hdvd : 2 ∣ Q.relIndex (X.Gi 0) := heq ▸ h2dvd
      exact hQ.2.2 hdvd
    have hPQlt : P < Q := lt_of_le_of_ne hPQ hPneQ
    haveI : Finite ↥Q :=
      finite_of_le_stabilizer X.hyp (H := Q) hQ.1
    have hQnil : Group.IsNilpotent ↥Q := hQ.2.1.isNilpotent
    have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
    have hsub_lt : P.subgroupOf Q < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact not_le_of_gt hPQlt (Subgroup.subgroupOf_eq_top.mp htop)
    obtain ⟨y, hyN, hyP⟩ := SetLike.exists_of_lt (hnc (P.subgroupOf Q) hsub_lt)
    have hxQ : (y : G) ∈ Q := y.2
    have hxN : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
      have hyN' : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
        rw [Subgroup.subgroupOf_normalizer_eq hPQ]
        exact hyN
      exact Subgroup.mem_subgroupOf.mp hyN'
    have hxP : (y : G) ∉ P := fun hx => hyP (Subgroup.mem_subgroupOf.mpr hx)
    have hzp : IsPGroup 2 (Subgroup.zpowers ((y : G))) :=
      hQ.2.1.to_le (Subgroup.zpowers_le.mpr hxQ)
    have hzN : Subgroup.zpowers ((y : G)) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hsupP : IsPGroup 2 (P ⊔ Subgroup.zpowers ((y : G)) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hSylM₀.2.1 hzp hzN
    have hsupN : (P ⊔ Subgroup.zpowers ((y : G)) : Subgroup G) ≤ N₀ := by
      refine sup_le hPN₀ ?_
      exact le_inf hzN (Subgroup.zpowers_le.mpr (hQ.1 hxQ))
    have hleP : (P ⊔ Subgroup.zpowers ((y : G)) : Subgroup G) ≤ P :=
      le_of_normal_isSylowTwoOf hSylN₀ hPnormalN₀ hsupN hsupP
    exact hxP (hleP (Subgroup.mem_sup_right (Subgroup.mem_zpowers (y : G))))
  have hSylS : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [X.edgeSylow_zero] using
      isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
  have hPS : P ≤ X.S := inf_le_left.trans (by
    have h := X.Q_le_edgeSylow_right 1
    simpa using h)
  have hPS_eq : P = X.S := by
    have h1 : P.relIndex X.S * X.S.relIndex (X.Gi 0) = P.relIndex (X.Gi 0) :=
      Subgroup.relIndex_mul_relIndex P X.S (X.Gi 0) hPS hSylS.1
    have hodd : ¬ 2 ∣ P.relIndex X.S := fun hd =>
      F7.isSylowTwoOf_odd_relIndex hSylG₀ (h1 ▸ hd.mul_right _)
    haveI : Finite ↥X.S := finite_of_le_stabilizer X.hyp (H := X.S) hSylS.1
    obtain ⟨k, hk⟩ := hSylS.2.1.index (P.subgroupOf X.S)
    have hk0 : k = 0 := by
      by_contra hk0
      have hdvd : 2 ∣ (P.subgroupOf X.S).index := by
        rw [hk]
        exact dvd_pow_self 2 hk0
      exact hodd hdvd
    have h2 : P.relIndex X.S = 1 := by
      change (P.subgroupOf X.S).index = 1
      rw [hk, hk0, pow_zero]
    exact le_antisymm hPS (Subgroup.relIndex_eq_one.mp h2)
  have hQ1S : X.Q 1 = X.S := by
    refine le_antisymm ?_ ?_
    · have h := X.Q_le_edgeSylow_right 1
      simpa using h
    · rw [← hPS_eq]
      exact inf_le_left
  have hSylS_G1 : IsSylowTwoOf X.S (X.Gi 1) := by
    have h := isSylowTwoOf_of_edgeStab X.hyp (X.adj 0).symm
      (show IsSylowTwoOf X.S (X.Gi 1 ⊓ X.Gi 0) from by
        simpa [X.edgeSylow_zero, inf_comm] using X.isSylowTwoOf_edgeSylow 0)
    simpa using h
  have hSylQ1G1 : IsSylowTwoOf (X.Q 1) (X.Gi 1) := by
    rwa [hQ1S]
  have hQ1normal : X.Gi 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)
  have hQ1normSub : ((X.Q 1).subgroupOf (X.Gi 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ1normal
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  have hL1eq : X.L 1 = X.Q 1 := by
    refine le_antisymm ?_ ?_
    · rw [Setup.L, CFSG.Quasithin.oTwoPrime, Subgroup.closure_le]
      rintro x ⟨hxG1, n, hxpow⟩
      have hzG1 : Subgroup.zpowers x ≤ X.Gi 1 := Subgroup.zpowers_le.mpr hxG1
      have hzp : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_two hxpow
      have hle := le_of_normal_isSylowTwoOf hSylQ1G1 hQ1normSub hzG1 hzp
      exact Subgroup.zpowers_le.mp hle
    · exact CFSG.Quasithin.le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1)
  have hL1p : IsPGroup 2 ↥(X.L 1) := by
    rw [hL1eq]
    exact pCoreOf_isPGroup' (X.Gi 1)
  have hpcTop : CFSG.pCore 2 ↥(X.L 1) = ⊤ := by
    refine top_le_iff.mp ?_
    exact le_sSup (show (⊤ : Subgroup ↥(X.L 1)) ∈ CFSG.normalPSubgroups 2 ↥(X.L 1) from
      ⟨inferInstance, hL1p.to_subgroup ⊤⟩)
  obtain ⟨e⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  haveI : Subsingleton (↥(X.L 1) ⧸ CFSG.pCore 2 ↥(X.L 1)) := by
    rw [hpcTop]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton (PSL(2, GaloisField 2 (nOf Γ (X.vert 1)))) :=
    e.toEquiv.symm.subsingleton
  haveI : Nontrivial (PSL(2, GaloisField 2 (nOf Γ (X.vert 1)))) := SL2Simple.PSL_nontrivial
  exact not_subsingleton (PSL(2, GaloisField 2 (nOf Γ (X.vert 1)))) inferInstance


theorem IsSKMax.noCharNormal_of_le {U H : Subgroup G} (hU : X.IsSKMax U)
    (hPH : X.skP U ≤ H)
    (hHM : H ≤ X.normGi U 0) (hMK : X.normGi U 0 = H ⊔ X.K) :
    NoCharNormal (X.skP U) H := by
  classical
  intro C hCP hCne hCchar hHnorm
  let P : Subgroup G := X.skP U
  let A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1
  have hC_P : C ≤ P := hCP
  have hCnormP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf P).Characteristic := hCchar
    have hmap : (C.subgroupOf P).map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := P) (K := C.subgroupOf P)
    rwa [hmap] at h
  have hP_eq : P = pCoreOf 2 A := by
    simpa [P, A] using skP_eq_pCoreOf X hU.1
  have hKA : X.K ≤ A := le_inf (hU.1.K_le_normGi 0) (X.K_le_Gi 1)
  have hP_normal_K : X.K ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP_eq]
    refine (show X.K ≤ Subgroup.normalizer (A : Set G) from ?_).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
    intro k hk
    obtain ⟨hkU0, hkG1⟩ := Subgroup.mem_inf.mp (hKA hk)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k A = A
    rw [show A = X.normGi U 0 ⊓ X.Gi 1 from rfl, conjSub_inf]
    change conjSub k (X.normGi U 0) ⊓ conjSub k (X.Gi 1) =
      X.normGi U 0 ⊓ X.Gi 1
    rw [conjSub_eq_of_mem hkG1,
      show X.normGi U 0 = Subgroup.normalizer (U : Set G) ⊓ X.Gi 0 from rfl,
      conjSub_inf, conjSub_eq_of_mem hkU0.1, conjSub_eq_of_mem hkU0.2]
  have hKnorm : X.K ≤ Subgroup.normalizer (C : Set G) := hP_normal_K.trans hCnormP
  have hM0norm : X.normGi U 0 ≤ Subgroup.normalizer (C : Set G) := by
    rw [hMK]
    exact sup_le hHnorm hKnorm
  exact hU.noCharNormal X C hCP hCne hCchar hM0norm

end Setup



end CFSG.Quasithin.St84
