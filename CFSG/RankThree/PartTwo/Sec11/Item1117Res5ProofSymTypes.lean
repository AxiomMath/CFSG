module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymC

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements


structure Sym1119Ctx (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) (d x s r g : G) : Prop where
  big : Sec11Big G A c L a R Y d x s r g
  A_le_Z2 : A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype
  Z2_le_R : (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R
  N_le_A : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
    Subgroup.normalizer (A : Set G)
  N_le_d : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
    Subgroup.normalizer (Subgroup.zpowers d : Set G)
  r_comm : r * a = a * r
  s_comm : s * a = a * s
  not_N_cd : ¬ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)
  s_eq_c : Subgroup.zpowers s = Subgroup.zpowers c
  rs_ne : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}
  exists_h : ∃ h ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
    h * c * h⁻¹ ∈ A ∧ h * c * h⁻¹ ∉ Subgroup.closure ({c, d} : Set G)

@[expose] def Step1119Lines : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ∧
      ∀ e ∈ A, e ∉ Subgroup.closure ({c, d} : Set G) → e ∉ Subgroup.closure ({a, d} : Set G) →
        ¬ YNotField c L e

@[expose] def Step1119AY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      ∃ f ∈ A, f ∉ Subgroup.closure ({a, d} : Set G) ∧ Subgroup.closure ({f, d} : Set G) ≤ Y ∧
        Subgroup.closure ({f, d} : Set G) =
          ⁅sec11P R g ⊓ Subgroup.centralizer ({a} : Set G),
            sec11P R g ⊓ Subgroup.centralizer ({a} : Set G)⁆ ⊓ A

end Statements

namespace Item1117Res5Proof

section Group

variable {G : Type} [Group G]

theorem mem_closure_pair_of_mem {u v w : G} (huv : u * v = v * u) (hu3 : u ^ 3 = 1)
    (hw : w ∈ Subgroup.closure ({u, v} : Set G)) (hwv : w ∉ Subgroup.zpowers v) :
    u ∈ Subgroup.closure ({w, v} : Set G) := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair huv hw
  have hi : ¬ (3 : ℤ) ∣ i := by
    rintro ⟨k, rfl⟩
    apply hwv
    rw [zpow_mul, show u ^ (3 : ℤ) = u ^ (3 : ℕ) by norm_cast, hu3, one_zpow, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) j
  have hui : u ^ i ∈ Subgroup.closure ({u ^ i * v ^ j, v} : Set G) := by
    have h1 : u ^ i * v ^ j ∈ Subgroup.closure ({u ^ i * v ^ j, v} : Set G) :=
      Subgroup.subset_closure (by simp)
    have h2 : v ^ j ∈ Subgroup.closure ({u ^ i * v ^ j, v} : Set G) :=
      Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j
    have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    simpa using this
  have hu : u = (u ^ i) ^ i := by
    obtain ⟨k, hk | hk⟩ : ∃ k : ℤ, i = 3 * k + 1 ∨ i = 3 * k + 2 := ⟨i / 3, by omega⟩
    · have : i * i = 3 * (3 * k * k + 2 * k) + 1 := by rw [hk]; ring
      rw [← zpow_mul, this, zpow_add, zpow_mul, show u ^ (3 : ℤ) = u ^ (3 : ℕ) by norm_cast, hu3,
        one_zpow, one_mul, zpow_one]
    · have : i * i = 3 * (3 * k * k + 4 * k + 1) + 1 := by rw [hk]; ring
      rw [← zpow_mul, this, zpow_add, zpow_mul, show u ^ (3 : ℤ) = u ^ (3 : ℕ) by norm_cast, hu3,
        one_zpow, one_mul, zpow_one]
  have h3 := Subgroup.zpow_mem _ hui i
  rwa [← hu] at h3

theorem conj_mem_commutator_of_conj_mem {M : Subgroup G} {k : G}
    (hk : ∀ m ∈ M, k * m * k⁻¹ ∈ M) : ∀ y ∈ ⁅M, M⁆, k * y * k⁻¹ ∈ ⁅M, M⁆ := by
  intro y hy
  have hmap : M.map (MulAut.conj k).toMonoidHom ≤ M := by
    rintro _ ⟨m, hm, rfl⟩
    exact hk m hm
  have h1 : (⁅M, M⁆).map (MulAut.conj k).toMonoidHom ≤ ⁅M, M⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact h1 ⟨y, hy, rfl⟩

theorem conj_mem_centralizer_of_mem_closure {a d m k : G}
    (hka : k⁻¹ * a * k ∈ Subgroup.closure ({a, d} : Set G)) (hma : m * a = a * m)
    (hmd : m * d = d * m) : k * m * k⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
  have hle : Subgroup.closure ({a, d} : Set G) ≤ Subgroup.centralizer ({m} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hma.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hmd.symm
  have h1 : (k⁻¹ * a * k) * m = m * (k⁻¹ * a * k) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hka)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc k * m * k⁻¹ * a = k * (m * (k⁻¹ * a * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * a * k) * m) * k⁻¹ := by rw [h1]
    _ = a * (k * m * k⁻¹) := by group

end Group

end Item1117Res5Proof

section Main


theorem step1119SymTypes_of_lines_ay (h113 : Item113) (h117 : Item117)
    (hL : Step1119Lines) (hAY : Step1119AY) : Step1119SymTypes := by
  intro G _ _ A c L a R Y d x s r g hbig hA2 hZR hNA hNd hra hsa hN hsc hrs hh
  have hctx : Sym1119Ctx G A c L a R Y d x s r g :=
    ⟨hbig, hA2, hZR, hNA, hNd, hra, hsa, hN, hsc, hrs, hh⟩
  obtain ⟨hLI, hOT⟩ := hL G A c L a R Y d x s r g hctx
  obtain ⟨f, hfA, hfad, hfY, hfeq⟩ := hAY G A c L a R Y d x s r g hctx
  have h := hbig.toSec11Data
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hdP : ∀ u ∈ sec11P R g, u * d = d * u := fun u hu =>
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d) hu
  have hMconj : ∀ k ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      ∀ m ∈ sec11P R g ⊓ Subgroup.centralizer ({a} : Set G),
        k * m * k⁻¹ ∈ sec11P R g ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro k hk m hm
    refine ⟨(Subgroup.mem_normalizer_iff.mp hk m).mp hm.1, ?_⟩
    have hka : k⁻¹ * a * k ∈ Subgroup.closure ({a, d} : Set G) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hLI (Subgroup.inv_mem _ hk)) a).mp
        (Subgroup.subset_closure (by simp))
      simpa using h1
    exact Item1117Res5Proof.conj_mem_centralizer_of_mem_closure hka
      (Subgroup.mem_centralizer_singleton_iff.mp hm.2) (hdP m hm.1)
  have hii : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {f, d} : Subgroup G) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, hfeq] at hx
    rw [SetLike.mem_coe, hfeq]
    exact ⟨Item1117Res5Proof.conj_mem_commutator_of_conj_mem (hMconj k hk) x hx.1,
      (Subgroup.mem_normalizer_iff.mp (hNA hk) x).mp hx.2⟩
  have hf3 : f ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hfA
  have hc3 : c ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.mem_A
  have hfdc : f * d = d * f := Item1117Proof.commute_of_mem_A h hfA hdA
  have hcdc : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have hfd : f ∉ Subgroup.zpowers d := fun hm => hfad
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)
  have hlineA : Subgroup.closure ({f, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [hfA, hdA]
  have hiii : ∀ f' ∈ Subgroup.closure ({f, d} : Set G), f' ∉ Subgroup.zpowers d →
      ∀ Y' ∈ thetaComponentsAt 3 f', sec11K L f' ≤ Y' → KFacts.InducesStdKind Y' c .field := by
    intro f' hf' hf'd
    have hf_in : f ∈ Subgroup.closure ({f', d} : Set G) :=
      Item1117Res5Proof.mem_closure_pair_of_mem hfdc hf3 hf' hf'd
    have hlineSub : ∀ T : Subgroup G, f' ∈ T → d ∈ T → f ∈ T := by
      intro T hf'T hdT
      have hcl : Subgroup.closure ({f', d} : Set G) ≤ T := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        exacts [hf'T, hdT]
      exact hcl hf_in
    have hnotcd : f' ∉ Subgroup.closure ({c, d} : Set G) := by
      intro hcd
      have hfcd : f ∈ Subgroup.closure ({c, d} : Set G) :=
        hlineSub _ hcd (Subgroup.subset_closure (by simp))
      have hcf : c ∈ Subgroup.closure ({f, d} : Set G) :=
        Item1117Res5Proof.mem_closure_pair_of_mem hcdc hc3 hfcd hfd
      have heq : Subgroup.closure ({f, d} : Set G) = Subgroup.closure ({c, d} : Set G) := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact hfcd
          · exact Subgroup.subset_closure (by simp)
        · rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact hcf
          · exact Subgroup.subset_closure (by simp)
      apply hN
      intro k hk
      have := hii hk
      rwa [heq] at this
    have hnotad : f' ∉ Subgroup.closure ({a, d} : Set G) := fun had =>
      hfad (hlineSub _ had (Subgroup.subset_closure (by simp)))
    intro Y' hY' hKY'
    by_contra hnot
    exact hOT f' (hlineA hf') hnotcd hnotad ⟨Y', hY', hKY', hnot⟩
  exact ⟨f, hfA, hfad, hfY, hii, hiii⟩

end Main

end CFSG.RankThree.PartTwo.Sec11

end
