module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCores
public import CFSG.LieType.Universal.Spin.Chevalley.Commutator
public import CFSG.LieType.Universal.Spin.PlusCT.Weyl
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Universal.Spin.PlusCT.Basic
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCoresPlus
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic
public import CFSG.LieType.HighestRoot.Gen
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigOdd
import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.Milestones.SG_two_signalizer_completeness

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.Open CFSG.LieType.HighestRoot CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.StandardType.LieKnownR2 CFSG.OddStandard.Solomon75.Sec6SigOdd
open scoped commutatorElement

private theorem rckp2_longRoot_proof_irrel {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (h₁ h₂ : i ≠ j) (s t : Bool) (c : F) :
    (Spin.plusFrame n F hn).longRoot h₁ s t (Multiplicative.ofAdd c) =
      (Spin.plusFrame n F hn).longRoot h₂ s t (Multiplicative.ofAdd c) :=
  congrArg (fun h => (Spin.plusFrame n F hn).longRoot h s t (Multiplicative.ofAdd c))
    (Subsingleton.elim h₁ h₂)

private theorem rckp2_eq_zero_or_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (c : F) : c = 0 ∨ c = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : ({0, 1} : Finset F).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [zero_ne_one]), Finset.card_singleton]
  have hcF : Fintype.card F = 2 := by rwa [Nat.card_eq_fintype_card] at hF
  have huniv : ({0, 1} : Finset F) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hcF])
  have : c ∈ ({0, 1} : Finset F) := huniv ▸ Finset.mem_univ c
  simpa using this

private theorem rckp2_mult_eq_one_or_ofAdd_one {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (c : Multiplicative F) :
    c = 1 ∨ c = Multiplicative.ofAdd 1 := by
  rcases rckp2_eq_zero_or_one hF (Multiplicative.toAdd c) with h | h
  · left
    exact Multiplicative.toAdd.injective (by simpa using h)
  · right
    exact Multiplicative.toAdd.injective (by simpa using h)

private theorem rckp2_rootForm_add {K : Type*} [Group K] (D : UniversalRootDatum K)
    (a b c : Fin D.rank → ℤ) :
    rootForm D (a + b) c = rootForm D a c + rootForm D b c := by
  simp only [rootForm, map_add, LinearMap.add_apply]

private theorem rckp2_exists_pair_POmegaPlus_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcardF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn3⟩) :
    ∃ (β : Fin L.D.rank → ℤ) (x : L.K) (V : Subgroup L.K),
      β ∈ L.D.roots ∧ GGLongRoot L.D β ∧
      L.D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ pCoreOf 2 (Subgroup.normalizer (L.D.rootGroup β : Set L.K)) ∧
      ∀ v ∈ V, v ≠ 1 → ∃ j : L.K, v = j * x * j⁻¹ := by
  subst hL
  haveI : Fintype F := Fintype.ofFinite F
  change ∃ (β : Fin (Spin.plusDatum n F hn3).rank → ℤ)
      (x : spinGroup (Spin.quadPlus n F)) (V : Subgroup (spinGroup (Spin.quadPlus n F))),
      β ∈ (Spin.plusDatum n F hn3).roots ∧ GGLongRoot (Spin.plusDatum n F hn3) β ∧
      (Spin.plusDatum n F hn3).rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ pCoreOf 2 (Subgroup.normalizer ((Spin.plusDatum n F hn3).rootGroup β :
        Set (spinGroup (Spin.quadPlus n F)))) ∧
      ∀ v ∈ V, v ≠ 1 → ∃ j : spinGroup (Spin.quadPlus n F), v = j * x * j⁻¹
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h; exact Nat.zero_ne_one (congrArg Fin.val h)
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h; exact (by omega : (0:ℕ) ≠ 2) (congrArg Fin.val h)
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h; exact (by omega : (1:ℕ) ≠ 2) (congrArg Fin.val h)
  have h21 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := h12.symm
  have h10 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := h01.symm
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := h02.symm
  obtain ⟨θ, hθmem, hθstd⟩ := Spin.exists_mem_rootsD_toStdD_eq n
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (s := 1) (t := 1) h01 (Or.inl rfl) (Or.inl rfl)
  have hθmemD : θ ∈ (Spin.plusDatum n F hn3).roots := hθmem
  have hθht : ht θ = 2 * (n : ℤ) - 3 := by
    rw [Spin.ht_of_toStdD_eq_add n (by omega) hθstd]
    have e0 : ((⟨0, by omega⟩ : Fin n).val : ℤ) = 0 := rfl
    have e1 : ((⟨1, by omega⟩ : Fin n).val : ℤ) = 1 := rfl
    rw [e0, e1]; ring
  have hroot_le : ∀ {γ : Fin n → ℤ}, γ ∈ roots (isFiniteType_cartanD n) ∅ →
      ht γ ≤ 2 * (n : ℤ) - 3 := by
    intro γ hγ
    rw [Spin.rootsD_eq n (by omega), Set.mem_setOf_eq] at hγ
    obtain ⟨i, j, s, t, hij, hs, hts, hstd⟩ := hγ
    rw [Spin.ht_of_toStdD_eq_add n (by omega) hstd]
    have hi : (i:ℤ) < (n:ℤ) := by exact_mod_cast i.isLt
    have hj : (j:ℤ) < (n:ℤ) := by exact_mod_cast j.isLt
    have hi0 : (0:ℤ) ≤ (i:ℤ) := by exact_mod_cast Nat.zero_le i.val
    have hj0 : (0:ℤ) ≤ (j:ℤ) := by exact_mod_cast Nat.zero_le j.val
    have hijz : (i:ℤ) ≠ (j:ℤ) := by intro hh; exact hij (Fin.ext (by exact_mod_cast hh))
    rcases lt_or_gt_of_ne hijz with hlt | hgt
    · rcases hs with rfl | rfl <;> rcases hts with rfl | rfl <;> omega
    · rcases hs with rfl | rfl <;> rcases hts with rfl | rfl <;> omega
  obtain ⟨hdiv, hirr, r, hr, hmax⟩ :=
    CFSG.StandardType.LieKnownR2.POmega.Cores.spinPlus_highest (n := n) (F := F) hn3
  have hθr : θ = r := hmax θ hθmemD (fun δ hδ => by
    calc ht δ ≤ 2 * (n : ℤ) - 3 := hroot_le hδ
      _ = ht θ := hθht.symm)
  have hrθ : IsHighestRoot (Spin.plusDatum n F hn3) θ := by rw [hθr]; exact hr
  obtain ⟨γ, hγmem, hγstd⟩ := Spin.exists_mem_rootsD_toStdD_eq n
    (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (s := 1) (t := 1) h02 (Or.inl rfl) (Or.inl rfl)
  have hγmemD : γ ∈ (Spin.plusDatum n F hn3).roots := hγmem
  obtain ⟨δ, hδmem, hδstd⟩ := Spin.exists_mem_rootsD_toStdD_eq n
    (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (s := 1) (t := -1) h12 (Or.inl rfl) (Or.inr rfl)
  have hδmemD : δ ∈ (Spin.plusDatum n F hn3).roots := hδmem
  have hγδ : γ + δ = θ := by
    apply Spin.toStdD_injective n
    rw [Spin.toStdD_add, hγstd, hδstd, hθstd]
    ext k
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have hγθ : γ ≠ θ := by
    intro h
    have hstd : Spin.toStdD n γ = Spin.toStdD n θ := by rw [h]
    rw [hγstd, hθstd] at hstd
    have hk := congrFun hstd (⟨2, by omega⟩ : Fin n)
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne h20, Pi.single_eq_same,
      Pi.single_eq_of_ne h21] at hk
    exact (by omega : (1:ℤ) ≠ 0) (by simpa using hk)
  have hδθ : δ ≠ θ := by
    intro h
    have hstd : Spin.toStdD n δ = Spin.toStdD n θ := by rw [h]
    rw [hδstd, hθstd] at hstd
    have hk := congrFun hstd (⟨0, by omega⟩ : Fin n)
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h02,
      Pi.single_eq_same] at hk
    exact (by omega : (1:ℤ) ≠ 0) (by simpa using hk.symm)
  have hrr : 0 < rootForm (Spin.plusDatum n F hn3) θ θ := by
    have hθ0 : toRat (I := Fin (Spin.plusDatum n F hn3).rank) θ ≠ 0 := fun e =>
      ne_zero_of_mem_roots (Spin.plusDatum n F hn3).isFiniteType (Spin.plusDatum n F hn3).divisible
        hrθ.mem_roots (toRat_injective (I := Fin (Spin.plusDatum n F hn3).rank)
          (by rw [e, map_zero]))
    exact form_pos (Spin.plusDatum n F hn3).isFiniteType hθ0
  have hlin : rootForm (Spin.plusDatum n F hn3) γ θ + rootForm (Spin.plusDatum n F hn3) δ θ =
      rootForm (Spin.plusDatum n F hn3) θ θ := by
    have h1 : rootForm (Spin.plusDatum n F hn3) (γ + δ) θ =
        rootForm (Spin.plusDatum n F hn3) γ θ + rootForm (Spin.plusDatum n F hn3) δ θ :=
      rckp2_rootForm_add (Spin.plusDatum n F hn3) γ δ θ
    rw [← h1, hγδ]
  have hpos : 0 < rootForm (Spin.plusDatum n F hn3) γ θ := by
    obtain ⟨cγ, hcγ⟩ := CFSG.StandardType.LieKnownR2.exists_pairing_int (Spin.plusDatum n F hn3)
      hdiv (r := θ) (γ := γ) hrθ.mem_roots
    obtain ⟨cδ, hcδ⟩ := CFSG.StandardType.LieKnownR2.exists_pairing_int (Spin.plusDatum n F hn3)
      hdiv (r := θ) (γ := δ) hrθ.mem_roots
    have hcγ_le : cγ ≤ 2 :=
      (CFSG.StandardType.LieKnownR2.pairing_le_two (Spin.plusDatum n F hn3) hrθ hγmemD hcγ).1
    have hcδ_le : cδ ≤ 2 :=
      (CFSG.StandardType.LieKnownR2.pairing_le_two (Spin.plusDatum n F hn3) hrθ hδmemD hcδ).1
    have hcγ_ne : cγ ≠ 2 := fun hc2 =>
      hγθ ((CFSG.StandardType.LieKnownR2.pairing_le_two (Spin.plusDatum n F hn3) hrθ hγmemD
        hcγ).2 hc2)
    have hcδ_ne : cδ ≠ 2 := fun hc2 =>
      hδθ ((CFSG.StandardType.LieKnownR2.pairing_le_two (Spin.plusDatum n F hn3) hrθ hδmemD
        hcδ).2 hc2)
    have hcγ_le1 : cγ ≤ 1 := by omega
    have hcδ_le1 : cδ ≤ 1 := by omega
    have hsum : cγ + cδ = 2 := by
      have h1 : ((cγ + cδ : ℤ) : ℚ) * rootForm (Spin.plusDatum n F hn3) θ θ =
          2 * rootForm (Spin.plusDatum n F hn3) θ θ := by
        rw [Int.cast_add, add_mul, hcγ, hcδ, ← hlin]; ring
      have hrr_ne : rootForm (Spin.plusDatum n F hn3) θ θ ≠ 0 := ne_of_gt hrr
      have h2 : ((cγ + cδ : ℤ) : ℚ) = 2 := mul_right_cancel₀ hrr_ne h1
      exact_mod_cast h2
    have hcγ_pos : 0 < cγ := by omega
    have hcγq : (0:ℚ) < (cγ:ℚ) := by exact_mod_cast hcγ_pos
    nlinarith [hcγ, hrr]
  have hγ_le_rad : (Spin.plusDatum n F hn3).rootGroup γ ≤
      highestRootRadical (Spin.plusDatum n F hn3) θ :=
    CFSG.LieType.HighestRoot.rootGroup_le_highestRootRadical hγmemD hpos
  have hθ_le_rad : (Spin.plusDatum n F hn3).rootGroup θ ≤
      highestRootRadical (Spin.plusDatum n F hn3) θ :=
    CFSG.LieType.HighestRoot.rootGroup_le_highestRootRadical hrθ.mem_roots hrr
  have hct : IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
      (weylAction (isFiniteType_cartanD n)) (roots (isFiniteType_cartanD n) ∅)
      (Spin.plusRootGroup n F hn3) (Spin.weylD F hn3) (fun k => (Spin.torusD F hn3 k).range) :=
    Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top n F hn3)
  have hext : SteinbergExtras (Spin.plusDatum n F hn3) (Spin.weylD F hn3)
      (fun k => (Spin.torusD F hn3 k).range) := Spin.plusDatum_steinbergExtras hn3
  have hN : DivisibleNormalizes (Spin.plusDatum n F hn3) :=
    CFSG.LieType.HighestRoot.divisibleNormalizes_of_divisible_eq_empty hdiv
  have hW : DivisibleWeylMem (Spin.plusDatum n F hn3) (Spin.weylD F hn3) :=
    CFSG.LieType.HighestRoot.divisibleWeylMem_of_divisible_eq_empty hdiv
  have hX : ∀ γ ∈ (Spin.plusDatum n F hn3).roots,
      IsPGroup 2 ((Spin.plusDatum n F hn3).rootGroup γ) := fun γ hγ =>
    CFSG.LieType.Steinberg.isPGroup_of_isParametrization
      (CFSG.LieType.Steinberg.SpinPlus.isParametrization (n := n) (K := F) hn3) hγ
  obtain ⟨-, hQp, hQN, hNQ, -⟩ :=
    CFSG.LieType.HighestRoot.highestRootGen_of_isHighestRoot hct hext hN hW hirr hX hrθ
  have hrad_le : highestRootRadical (Spin.plusDatum n F hn3) θ ≤
      pCoreOf 2 (Subgroup.normalizer ((Spin.plusDatum n F hn3).rootGroup θ :
        Set (spinGroup (Spin.quadPlus n F)))) :=
    CFSG.StandardType.GGRootNorm.le_pCoreOf_of_normalized hQN hQp
      (Subgroup.le_normalizer_iff.mp hNQ)
  let f : Multiplicative F →* spinGroup (Spin.quadPlus n F) :=
    (Spin.plusFrame n F hn3).longRoot h01 true true
  let x : spinGroup (Spin.quadPlus n F) := f (Multiplicative.ofAdd 1)
  let g : Multiplicative F →* spinGroup (Spin.quadPlus n F) :=
    (Spin.plusFrame n F hn3).longRoot h02 true true
  let y : spinGroup (Spin.quadPlus n F) := g (Multiplicative.ofAdd 1)
  have hf : Function.Injective f :=
    Spin.HypFrame.longRoot_injective (Spin.plusFrame n F hn3) h01 true true
  have hx2p : x ^ 2 = 1 := by
    dsimp only [x, f]
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]
  have hx2 : x * x = 1 := by rwa [pow_two] at hx2p
  have hx1 : x ≠ 1 := by
    intro h
    dsimp only [x, f] at h
    have h0 : (Spin.plusFrame n F hn3).longRoot h01 true true (Multiplicative.ofAdd 1) =
        (Spin.plusFrame n F hn3).longRoot h01 true true 1 := by rw [h, map_one]
    have h1 : (1 : F) = 0 := by
      have := Spin.HypFrame.longRoot_injective (Spin.plusFrame n F hn3) h01 true true h0
      simpa using congrArg Multiplicative.toAdd this
    exact one_ne_zero h1
  have hmem_zx : Subgroup.zpowers x ≤ f.range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩)
  have hrange_f : f.range = Subgroup.zpowers x := by
    apply le_antisymm
    · rintro y ⟨c, rfl⟩
      rcases rckp2_mult_eq_one_or_ofAdd_one hcardF c with rfl | rfl
      · rw [map_one]; exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers x
    · exact hmem_zx
  have hrootGroupθ : (Spin.plusDatum n F hn3).rootGroup θ = Subgroup.zpowers x := by
    change Spin.plusRootGroup n F hn3 θ = Subgroup.zpowers x
    rw [Spin.plusRootGroup_eq hn3 h01 true true hθstd]
    exact hrange_f
  have hx_mem : x ∈ (Spin.plusDatum n F hn3).rootGroup θ := by
    rw [hrootGroupθ]; exact Subgroup.mem_zpowers x
  have hx_core : x ∈ pCoreOf 2 (Subgroup.normalizer ((Spin.plusDatum n F hn3).rootGroup θ :
      Set (spinGroup (Spin.quadPlus n F)))) := hrad_le (hθ_le_rad hx_mem)
  have hg : Function.Injective g :=
    Spin.HypFrame.longRoot_injective (Spin.plusFrame n F hn3) h02 true true
  have hy2p : y ^ 2 = 1 := by
    dsimp only [y, g]
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]
  have hy2 : y * y = 1 := by rwa [pow_two] at hy2p
  have hy1 : y ≠ 1 := by
    intro h
    dsimp only [y, g] at h
    have h0 : (Spin.plusFrame n F hn3).longRoot h02 true true (Multiplicative.ofAdd 1) =
        (Spin.plusFrame n F hn3).longRoot h02 true true 1 := by rw [h, map_one]
    have h1 : (1 : F) = 0 := by
      have := Spin.HypFrame.longRoot_injective (Spin.plusFrame n F hn3) h02 true true h0
      simpa using congrArg Multiplicative.toAdd this
    exact one_ne_zero h1
  have hmem_zy : Subgroup.zpowers y ≤ g.range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩)
  have hrange_g : g.range = Subgroup.zpowers y := by
    apply le_antisymm
    · rintro w ⟨c, rfl⟩
      rcases rckp2_mult_eq_one_or_ofAdd_one hcardF c with rfl | rfl
      · rw [map_one]; exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers y
    · exact hmem_zy
  have hrootGroupγ : (Spin.plusDatum n F hn3).rootGroup γ = Subgroup.zpowers y := by
    change Spin.plusRootGroup n F hn3 γ = Subgroup.zpowers y
    rw [Spin.plusRootGroup_eq hn3 h02 true true hγstd]
    exact hrange_g
  have hy_mem : y ∈ (Spin.plusDatum n F hn3).rootGroup γ := by
    rw [hrootGroupγ]; exact Subgroup.mem_zpowers y
  have hy_core : y ∈ pCoreOf 2 (Subgroup.normalizer ((Spin.plusDatum n F hn3).rootGroup θ :
      Set (spinGroup (Spin.quadPlus n F)))) := hrad_le (hγ_le_rad hy_mem)
  have hxy : x * y = y * x := by
    dsimp only [x, y, f, g]
    exact (Spin.HypFrame.commute_longRoot_longRoot_left (Spin.plusFrame n F hn3)
      h01 h02 true true true 1 1).eq
  have hne0 : (Spin.plusFrame n F hn3).vec ⟨0, by omega⟩ true ≠ 0 := by
    intro h0
    have hp := (Spin.plusFrame n F hn3).polar_vec_not ⟨0, by omega⟩ true
    rw [h0] at hp
    simp at hp
  have hxy_ne : x ≠ y := by
    intro h
    have hxa : spinAction (Spin.quadPlus n F) x
        ((Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false) =
        (Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false +
          (Spin.plusFrame n F hn3).vec ⟨0, by omega⟩ true := by
      dsimp only [x, f]
      change spinAction (Spin.quadPlus n F) ((Spin.plusFrame n F hn3).longRoot h01 true true
          (Multiplicative.ofAdd 1)) ((Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) (!true)) =
        (Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false +
          (Spin.plusFrame n F hn3).vec (⟨0, by omega⟩ : Fin n) true
      rw [Spin.HypFrame.spinAction_longRoot_vec_not_right]
      simp only [Bool.not_true, one_smul]
    have hya : spinAction (Spin.quadPlus n F) y
        ((Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false) =
        (Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false := by
      dsimp only [y, g]
      rw [Spin.HypFrame.spinAction_longRoot_vec_of_ne (Spin.plusFrame n F hn3) h02 true true 1
        h10 h12 false]
    have heq : (Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false +
        (Spin.plusFrame n F hn3).vec ⟨0, by omega⟩ true =
        (Spin.plusFrame n F hn3).vec ⟨1, by omega⟩ false := by
      calc (Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false +
            (Spin.plusFrame n F hn3).vec (⟨0, by omega⟩ : Fin n) true
          = spinAction (Spin.quadPlus n F) x
              ((Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false) :=
            hxa.symm
        _ = spinAction (Spin.quadPlus n F) y
              ((Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false) := by rw [h]
        _ = (Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false := hya
    have hc : (Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false +
        (Spin.plusFrame n F hn3).vec (⟨0, by omega⟩ : Fin n) true =
        (Spin.plusFrame n F hn3).vec (⟨1, by omega⟩ : Fin n) false + 0 := by
      simpa using heq
    exact hne0 (add_left_cancel hc)
  let V : Subgroup (spinGroup (Spin.quadPlus n F)) := pairSub x y hx2p hy2p hxy
  have hV_card : Nat.card V = 4 := card_pairSub hx2p hy2p hxy hx1 hy1 hxy_ne
  have hV_elem : IsElemAbelian 2 V := isElemAbelian_pairSub hx2p hy2p hxy
  have hV_core : V ≤ pCoreOf 2 (Subgroup.normalizer ((Spin.plusDatum n F hn3).rootGroup θ :
      Set (spinGroup (Spin.quadPlus n F)))) := by
    intro v hv
    change v ∈ ({1, x, y, x * y} : Set (spinGroup (Spin.quadPlus n F))) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hx_core
    · exact hy_core
    · exact Subgroup.mul_mem _ hx_core hy_core
  have hy_conj : y = Spin.weylD F hn3 (⟨1, by omega⟩ : Fin n) * x *
      (Spin.weylD F hn3 (⟨1, by omega⟩ : Fin n))⁻¹ := by
    have hconj' : Spin.weylD F hn3 (⟨1, by omega⟩ : Fin n) * x *
        (Spin.weylD F hn3 (⟨1, by omega⟩ : Fin n))⁻¹ = y := by
      dsimp only [x, y, f, g]
      rw [Spin.weylD_conj_longRoot]
      rw [Spin.rootIdxD_of_lt n (by omega : (1:ℕ) + 1 < n),
        Spin.rootIdxD'_of_lt n (by omega : (1:ℕ) + 1 < n),
        Spin.rootSignD_of_lt n (by omega : (1:ℕ) + 1 < n)]
      have hb0 : longWeylBool (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ true false
          (⟨0, by omega⟩ : Fin n) true = true := longWeylBool_of_ne true false h01 h02 true
      have hb1 : longWeylBool (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ true false
          (⟨1, by omega⟩ : Fin n) true = true := longWeylBool_left true false
      have hs : longWeylSign (⟨1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n) *
          longWeylSign (⟨1, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) * (1:F) = 1 := by
        rw [longWeylSign_of_ne (i := (⟨1, by omega⟩ : Fin n)) h01, longWeylSign_self,
          CharTwo.neg_eq]
        ring
      rw [hb0, hb1, hs]
      exact rckp2_longRoot_proof_irrel hn3 _ h02 true true 1
    exact hconj'.symm
  have hx_eq_x' : x = (Spin.plusFrame n F hn3).longRoot h10 true true (Multiplicative.ofAdd 1) := by
    dsimp only [x, f]
    rw [Spin.HypFrame.longRoot_swap (Spin.plusFrame n F hn3) h01 true true 1,
      show (-(1:F)) = 1 from CharTwo.neg_eq 1]
  have hy_eq_y' : y = (Spin.plusFrame n F hn3).longRoot h20 true true (Multiplicative.ofAdd 1) := by
    dsimp only [y, g]
    rw [Spin.HypFrame.longRoot_swap (Spin.plusFrame n F hn3) h02 true true 1,
      show (-(1:F)) = 1 from CharTwo.neg_eq 1]
  let z : spinGroup (Spin.quadPlus n F) :=
    (Spin.plusFrame n F hn3).longRoot h21 true false (Multiplicative.ofAdd 1)
  have hcomm_zx : ⁅z, x⁆ = y := by
    have h1 : ⁅z, (Spin.plusFrame n F hn3).longRoot h10 true true (Multiplicative.ofAdd 1)⁆ =
        (Spin.plusFrame n F hn3).longRoot h20 true true (Multiplicative.ofAdd 1) := by
      dsimp only [z]
      change ⁅(Spin.plusFrame n F hn3).longRoot h21 true false (Multiplicative.ofAdd 1),
          (Spin.plusFrame n F hn3).longRoot h10 (!false) true (Multiplicative.ofAdd 1)⁆ =
        (Spin.plusFrame n F hn3).longRoot h20 true true (Multiplicative.ofAdd 1)
      rw [Spin.HypFrame.commutator_longRoot_longRoot (Spin.plusFrame n F hn3) h21 h10 h20
        true false true 1 1]
      rw [one_mul]
    rw [hx_eq_x', h1, hy_eq_y']
  have hxy_conj : x * y = z * x * z⁻¹ := by
    have h : z * x * z⁻¹ = x * y := by
      have h3 : z * x * z⁻¹ * x⁻¹ = y := by
        rw [← commutatorElement_def]; exact hcomm_zx
      have h2 : z * x * z⁻¹ * x⁻¹ * x = y * x := by rw [h3]
      calc z * x * z⁻¹ = z * x * z⁻¹ * x⁻¹ * x := by group
        _ = y * x := h2
        _ = x * y := hxy.symm
    exact h.symm
  refine ⟨θ, x, V, hθmemD, ?_, hrootGroupθ, hx2, hx1, ?_, hV_elem, hV_card, hV_core, ?_⟩
  · exact CFSG.StandardType.ggLongRoot_of_symmetric hirr
      (CFSG.ClassicalInvolution.ModelFacts.cartanD_symm n) rfl hθmemD
  · exact left_mem_pairSub
  · intro v hv hv1
    change v ∈ ({1, x, y, x * y} : Set (spinGroup (Spin.quadPlus n F))) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by simp⟩
    · exact ⟨Spin.weylD F hn3 (⟨1, by omega⟩ : Fin n), hy_conj⟩
    · exact ⟨z, hxy_conj⟩

theorem rckIIPair_OmegaPlus
    (n : ℕ) (hn : 4 ≤ n) (hadm : StatedLieAdmissible .POmegaPlus n 2 1) :
    RCKIIPair .POmegaPlus n := by
  have hn3 : 3 ≤ n := by omega
  have hcardF : Nat.card (GaloisField 2 1) = 2 := by
    have hc := GaloisField.card 2 1 (by norm_num : (1:ℕ) ≠ 0)
    simpa using hc
  have e : ggU .POmegaPlus n 1 =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 1)),
        Spin.plusDatum n (GaloisField 2 1) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  unfold RCKIIPair
  exact rckp2_exists_pair_POmegaPlus_of_eq hcardF hn hn3 (ggU .POmegaPlus n 1) e

end CFSG.StandardType.RCKK1II
