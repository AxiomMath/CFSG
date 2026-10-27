module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralCentralizer
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate113
public import Certificates.Certificate47
public import Certificates.Certificate114
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TrialityFold
open scoped Pointwise

namespace SteinbergBT.TrialityPlane

variable {K : Type} [Field K]



theorem foldChar_zpow (z : Kˣ) (m n : ℤ) (μ : ℤ × ℤ) :
    foldChar (z ^ m) (z ^ n) μ = z ^ (m * μ.1 + n * μ.2) := by
  rw [foldChar, ← zpow_mul, ← zpow_mul, ← zpow_add]

theorem dvd_of_foldChar_eq_one {z : Kˣ} {p : ℕ} (hz : orderOf z = p) {μ : ℤ × ℤ}
    (h1 : foldChar (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) μ = 1)
    (h2 : foldChar (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) μ = 1) :
    (p : ℤ) ∣ μ.1 ∧ (p : ℤ) ∣ μ.2 := by
  rw [foldChar_zpow, ← orderOf_dvd_iff_zpow_eq_one, hz] at h1 h2
  constructor
  · have : μ.1 = 2 * (2 * μ.1 + -3 * μ.2) + 3 * (-1 * μ.1 + 2 * μ.2) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  · have : μ.2 = (2 * μ.1 + -3 * μ.2) + 2 * (-1 * μ.1 + 2 * μ.2) := by ring
    rw [this]
    exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)

theorem g2FoldRoots_bound : ∀ μ ∈ g2FoldRoots, μ ≠ 0 ∧ μ.1.natAbs ≤ 3 ∧ μ.2.natAbs ≤ 3 := by
  decide

theorem weylCands_bound : ∀ P ∈ weylCands, (P.1.1 - 1).natAbs ≤ 4 ∧ P.1.2.natAbs ≤ 3 ∧
    P.2.1.natAbs ≤ 3 ∧ (P.2.2 - 1).natAbs ≤ 4 := by
  decide

theorem weylCands_diag : ∀ P ∈ weylCands, P.1.2 = 0 → P.2.1 = 0 →
    P = ((1, 0), (0, 1)) ∨ P = ((-1, 0), (0, -1)) := by
  decide

theorem eq_zero_of_dvd_of_natAbs_le {p : ℕ} (hp : 5 ≤ p) {m : ℤ} (hm : (p : ℤ) ∣ m)
    (hb : m.natAbs ≤ 4) : m = 0 := by
  by_contra h0
  have h1 : p ∣ m.natAbs := by simpa using Int.natAbs_dvd_natAbs.2 hm
  have := Nat.le_of_dvd (Int.natAbs_pos.2 h0) h1
  omega

abbrev outerTuple (z : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ :=
  d4Tuple (z ^ (2 : ℤ)) (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) (z ^ (2 : ℤ))

abbrev middleTuple (z : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ :=
  d4Tuple (z ^ (-1 : ℤ)) (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) (z ^ (-1 : ℤ))

theorem rootCharKernel_outer_inter_middle {z : Kˣ} {p : ℕ} (hp : 5 ≤ p) (hz : orderOf z = p) :
    rootCharKernel (outerTuple z) ∩ rootCharKernel (middleTuple z) = ∅ := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h₁ h₂
  rw [mem_rootCharKernel_iff rfl rfl rfl rfl] at h₁ h₂
  obtain ⟨hdv1, hdv2⟩ := dvd_of_foldChar_eq_one hz h₁.2 h₂.2
  obtain ⟨hne, hb1, hb2⟩ := g2FoldRoots_bound _ (fold_mem_of_isRoot h₁.1)
  exact hne (Prod.ext (eq_zero_of_dvd_of_natAbs_le hp hdv1 (by omega))
    (eq_zero_of_dvd_of_natAbs_le hp hdv2 (by omega)))

theorem eq_one_of_mem_rootCharStabilizer
    {z : Kˣ} {p : ℕ} (hp : 5 ≤ p) (hz : orderOf z = p)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (h₁ : w ∈ rootCharStabilizer (outerTuple z)) (h₂ : w ∈ rootCharStabilizer (middleTuple z)) :
    w = 1 := by
  have hx₁ : foldChar (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) ((foldPair w).1 - (1, 0)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (2 : ℤ)) (B := z ^ (-3 : ℤ)) rfl rfl rfl rfl h₁ i0
    rwa [fold_single0] at h
  have hy₁ : foldChar (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) ((foldPair w).2 - (0, 1)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (2 : ℤ)) (B := z ^ (-3 : ℤ)) rfl rfl rfl rfl h₁ i2
    rwa [fold_single2] at h
  have hx₂ : foldChar (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) ((foldPair w).1 - (1, 0)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (-1 : ℤ)) (B := z ^ (2 : ℤ)) rfl rfl rfl rfl h₂ i0
    rwa [fold_single0] at h
  have hy₂ : foldChar (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) ((foldPair w).2 - (0, 1)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (-1 : ℤ)) (B := z ^ (2 : ℤ)) rfl rfl rfl rfl h₂ i2
    rwa [fold_single2] at h
  obtain ⟨hX1, hX2⟩ := dvd_of_foldChar_eq_one hz hx₁ hx₂
  obtain ⟨hY1, hY2⟩ := dvd_of_foldChar_eq_one hz hy₁ hy₂
  obtain ⟨b1, b2, b3, b4⟩ := weylCands_bound _ (foldPair_mem hw)
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hX1 hX2 hY1 hY2
  have e1 := eq_zero_of_dvd_of_natAbs_le hp hX1 b1
  have e2 := eq_zero_of_dvd_of_natAbs_le hp hX2 (by omega)
  have e3 := eq_zero_of_dvd_of_natAbs_le hp hY1 (by omega)
  have e4 := eq_zero_of_dvd_of_natAbs_le hp hY2 b4
  apply eq_one_of_foldPair hw
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only <;> omega

theorem dvd_of_dvd_of_dvd {p X Y : ℤ} (h1 : p ∣ 2 * X - 3 * Y) (h2 : p ∣ -X + 2 * Y) :
    p ∣ X ∧ p ∣ Y := by
  constructor
  · have : X = 2 * (2 * X - 3 * Y) + 3 * (-X + 2 * Y) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  · have : Y = (2 * X - 3 * Y) + 2 * (-X + 2 * Y) := by ring
    rw [this]
    exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)

theorem zpow_eq_zpow_iff_dvd {z : Kˣ} {p : ℕ} (hz : orderOf z = p) {a b : ℤ} :
    z ^ a = z ^ b ↔ (p : ℤ) ∣ b - a := by
  rw [zpow_eq_zpow_iff_modEq, hz, Int.modEq_iff_dvd]

theorem foldPair_eq_of_scalar
    {z : Kˣ} {p : ℕ} (hp : 5 ≤ p) (hz : orderOf z = p)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) {c : ℤ}
    (h₁ : ∀ v, rootChar (outerTuple z) (w • v) = rootChar (outerTuple z) v ^ c)
    (h₂ : ∀ v, rootChar (middleTuple z) (w • v) = rootChar (middleTuple z) v ^ c) :
    foldPair w = ((1, 0), (0, 1)) ∨ foldPair w = ((-1, 0), (0, -1)) := by
  have e0 := h₁ (Pi.single i0 1)
  have e2 := h₁ (Pi.single i2 1)
  have f0 := h₂ (Pi.single i0 1)
  have f2 := h₂ (Pi.single i2 1)
  have ho := rootChar_eq_foldChar (a := outerTuple z) (A := z ^ (2 : ℤ)) (B := z ^ (-3 : ℤ))
    rfl rfl rfl rfl
  have hm := rootChar_eq_foldChar (a := middleTuple z) (A := z ^ (-1 : ℤ)) (B := z ^ (2 : ℤ))
    rfl rfl rfl rfl
  rw [ho, ho, fold_single0, foldChar_zpow, foldChar_zpow, ← zpow_mul,
    zpow_eq_zpow_iff_dvd hz] at e0
  rw [hm, hm, fold_single0, foldChar_zpow, foldChar_zpow, ← zpow_mul,
    zpow_eq_zpow_iff_dvd hz] at f0
  rw [ho, ho, fold_single2, foldChar_zpow, foldChar_zpow, ← zpow_mul,
    zpow_eq_zpow_iff_dvd hz] at e2
  rw [hm, hm, fold_single2, foldChar_zpow, foldChar_zpow, ← zpow_mul,
    zpow_eq_zpow_iff_dvd hz] at f2
  change (p : ℤ) ∣ _ - (2 * (foldPair w).1.1 + -3 * (foldPair w).1.2) at e0
  change (p : ℤ) ∣ _ - (-1 * (foldPair w).1.1 + 2 * (foldPair w).1.2) at f0
  change (p : ℤ) ∣ _ - (2 * (foldPair w).2.1 + -3 * (foldPair w).2.2) at e2
  change (p : ℤ) ∣ _ - (-1 * (foldPair w).2.1 + 2 * (foldPair w).2.2) at f2
  obtain ⟨-, hX2⟩ := dvd_of_dvd_of_dvd (X := (foldPair w).1.1 - c) (Y := (foldPair w).1.2)
    (by have := dvd_neg.2 e0; ring_nf at this ⊢; exact this)
    (by have := dvd_neg.2 f0; ring_nf at this ⊢; exact this)
  obtain ⟨hY1, -⟩ := dvd_of_dvd_of_dvd (X := (foldPair w).2.1) (Y := (foldPair w).2.2 - c)
    (by have := dvd_neg.2 e2; ring_nf at this ⊢; exact this)
    (by have := dvd_neg.2 f2; ring_nf at this ⊢; exact this)
  obtain ⟨-, b2, b3, -⟩ := weylCands_bound _ (foldPair_mem hw)
  exact weylCands_diag _ (foldPair_mem hw) (eq_zero_of_dvd_of_natAbs_le hp hX2 (by omega))
    (eq_zero_of_dvd_of_natAbs_le hp hY1 (by omega))

theorem eq_one_of_mem_posUnipotent
    {τ : Tag} {a₁ a₂ : Fin τ.rank → Kˣ}
    (hdisj : rootCharKernel a₁ ∩ rootCharKernel a₂ = ∅) {u : ModGL τ K}
    (hu : u ∈ posUnipotent τ K) (h₁ : rootDiagUnit τ a₁ * u * (rootDiagUnit τ a₁)⁻¹ = u)
    (h₂ : rootDiagUnit τ a₂ * u * (rootDiagUnit τ a₂)⁻¹ = u) : u = 1 := by
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hu₁ := mem_rootSpan_inter_of_conj_eq a₁ hposfin (fun β hβ => hβ.1)
    (fun α hα hr => (positive_root_collection τ K).2 α hα hr) hu h₁
  set S := rootCharKernel a₁ ∩ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} with hSdef
  have hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α := fun α hα => hα.2
  have hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S := by
    intro α hα β hβ a b ha hb hr
    refine ⟨⟨hr, ?_⟩, hr, ?_⟩
    · rw [rootChar_add, rootChar_nsmul, rootChar_nsmul, hα.1.2, hβ.1.2, one_pow, one_pow,
        one_mul]
    · rw [height_nsmul_add_nsmul]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith [hα.2.2, hβ.2.2]
  have hu₂ := mem_rootSpan_inter_of_conj_eq a₂ (hposfin.subset Set.inter_subset_right)
    (fun β hβ => hβ.2.1) (fun α hα hr => (positive_root_collection τ K).1 S hS hclosed α hα hr)
    hu₁ h₂
  have hempty : rootCharKernel a₂ ∩ S = ∅ := by
    rw [hSdef, ← Set.inter_assoc, Set.inter_comm (rootCharKernel a₂), hdisj, Set.empty_inter]
  rw [hempty] at hu₂
  simpa [rootSpan] using hu₂

theorem mul_comm_of_mem_torusGroup' {τ : Tag} {x y : ModGL τ K} (hx : x ∈ torusGroup τ K)
    (hy : y ∈ torusGroup τ K) : x * y = y * x := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hy

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {x u : G} (h : u * x = x * u) :
    x * u * x⁻¹ = u := by
  rw [← h, mul_inv_cancel_right]

theorem exists_eq_mul_canonicalRep_of_mem_normalizer
    (σ : K ≃+* K)
    {a₁ a₂ : Fin TwistTag.D4.tag.rank → Kˣ}
    (hdisj : rootCharKernel a₁ ∩ rootCharKernel a₂ = ∅) {V : Subgroup (ModGL TwistTag.D4.tag K)}
    (hVT : V ≤ torusGroup TwistTag.D4.tag K) (h₁ : rootDiagUnit TwistTag.D4.tag a₁ ∈ V)
    (h₂ : rootDiagUnit TwistTag.D4.tag a₂ ∈ V) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgV : g ∈ Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K))) :
    ∃ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∃ w ∈ relWeylTwist TwistTag.D4,
      g = h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by
  obtain ⟨-, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors TwistTag.D4.tag K a₁
  have hg' : g ∈ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective, Set.mem_iUnion] at hg'
  obtain ⟨⟨w, hw⟩, hcell⟩ := hg'
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := (bijOn_graphFixedRootBruhatCell σ.surjective hw).2.2 hcell
  simp only at hb hv hbv
  have hb' : b ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul σ.surjective]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  subst hbv
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w with hn
  have hhT : h ∈ torusGroup TwistTag.D4.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have huU : u ∈ posUnipotent TwistTag.D4.tag K := (Subgroup.mem_inf.1 hu).1
  have hvI : v ∈ rootSpan TwistTag.D4.tag K (inversionSet w) := (Subgroup.mem_inf.1 hv).1
  have hnN : n ∈ Subgroup.normalizer
      (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) :=
    mem_normalizer_torusGroup_of_mem_monomialSubgroup (canonicalRep_mem_monomialSubgroup K w)
  have hIU : rootSpan TwistTag.D4.tag K (inversionSet w) ≤ posUnipotent TwistTag.D4.tag K :=
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin TwistTag.D4.tag.rank → ℤ |
      IsRoot TwistTag.D4.tag β ∧ 0 < height β}) => rootSubgroup TwistTag.D4.tag K β) α
      ⟨hα.1, hα.2.1⟩ le_rfl
  have key : ∀ x ∈ V, ∀ y ∈ V, (h * u * n * v) * x * (h * u * n * v)⁻¹ = y →
      u * y = y * u ∧ v * x = x * v := by
    intro x hx y hy hxy
    have hxT := hVT hx
    have hyT := hVT hy
    have htT : n * x * n⁻¹ ∈ torusGroup TwistTag.D4.tag K :=
      (Subgroup.mem_normalizer_iff.1 hnN x).1 hxT
    have hcomm : h * y = y * h := mul_comm_of_mem_torusGroup' hhT hyT
    have heq : (h * (n * x * n⁻¹)) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)) * n *
        (x⁻¹ * v * x) = (h * y) * u * n * v := by
      have h1 : (h * u * n * v) * x = y * (h * u * n * v) := by
        rw [← hxy]
        group
      calc (h * (n * x * n⁻¹)) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)) * n * (x⁻¹ * v * x)
          = (h * u * n * v) * x := by group
        _ = y * (h * u * n * v) := h1
        _ = (y * h) * u * n * v := by group
        _ = (h * y) * u * n * v := by rw [hcomm]
    have hm3 : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹) ∈ posUnipotent TwistTag.D4.tag K := by
      have hN := torusGroup_le_normalizer_rootSpan (K := K)
        (S := {β : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag β ∧ 0 < height β})
        (fun β hβ => hβ.1) (inv_mem htT)
      have h' := (Subgroup.mem_normalizer_iff.1 hN u).1 huU
      rwa [inv_inv] at h'
    have hm4 : x⁻¹ * v * x ∈ rootSpan TwistTag.D4.tag K (inversionSet w) := by
      have hN := torusGroup_le_normalizer_rootSpan (K := K) (S := inversionSet w)
        (fun β hβ => hβ.1) (inv_mem hxT)
      have h' := (Subgroup.mem_normalizer_iff.1 hN v).1 hvI
      rwa [inv_inv] at h'
    obtain ⟨-, h1, h2, h3⟩ := huniq w w _ _ _ _ _ _ (mul_mem hhT htT) (mul_mem hhT hyT) hm3 huU
      hm4 hvI heq
    have hty : n * x * n⁻¹ = y := mul_left_cancel h1
    rw [hty] at h2
    refine ⟨?_, ?_⟩
    · calc u * y = y * (y⁻¹ * u * y) := by group
        _ = y * u := by rw [h2]
    · calc v * x = x * (x⁻¹ * v * x) := by group
        _ = x * v := by rw [h3]
  set g := h * u * n * v with hgdef
  have hgV' : g⁻¹ ∈ Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)) := inv_mem hgV
  have hu_of : ∀ d ∈ V, u * d = d * u := fun d hd =>
    (key (g⁻¹ * d * g⁻¹⁻¹) ((Subgroup.mem_normalizer_iff.1 hgV' d).1 hd) d hd (by group)).1
  have hv_of : ∀ d ∈ V, v * d = d * v := fun d hd =>
    (key d hd (g * d * g⁻¹) ((Subgroup.mem_normalizer_iff.1 hgV d).1 hd) rfl).2
  have hu1 : u = 1 := eq_one_of_mem_posUnipotent hdisj huU
    (conj_eq_of_mul_eq (hu_of _ h₁)) (conj_eq_of_mul_eq (hu_of _ h₂))
  have hv1 : v = 1 := eq_one_of_mem_posUnipotent hdisj (hIU hvI)
    (conj_eq_of_mul_eq (hv_of _ h₁)) (conj_eq_of_mul_eq (hv_of _ h₂))
  refine ⟨h, hh, w, hw, ?_⟩
  rw [hgdef, hu1, hv1, mul_one, mul_one]

theorem rootChar_zpow_tuple {τ : Tag} (a : Fin τ.rank → Kˣ) (c : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar (a ^ c) v = rootChar a v ^ c := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem rootChar_neg_vec {τ : Tag} (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

theorem canonicalRep_conj_rootDiagUnit_of_neg {τ : Tag} {w : WeylGroup τ}
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v) (l : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ l *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = (rootDiagUnit τ l)⁻¹ := by
  have hw' : ∀ v : Fin τ.rank → ℤ, w⁻¹ • v = -v := fun v => by
    have h := hw (w⁻¹ • v)
    rw [smul_inv_smul] at h
    calc w⁻¹ • v = -(-(w⁻¹ • v)) := (neg_neg _).symm
      _ = -v := by rw [← h]
  rw [canonicalRep_conj_rootDiagUnit, rootDiagUnit_inv]
  congr 1
  funext i
  rw [weylTuple, hw', rootChar_neg_vec, Pi.inv_apply]
  congr 1
  simpa using rootChar_nsmul_single l i 1

theorem conj_mul_conj {G : Type*} [Group G] (n x y : G) :
    n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group

theorem inv_smul_eq_neg {τ : Tag} {w : WeylGroup τ} (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    (v : Fin τ.rank → ℤ) : w⁻¹ • v = -v := by
  have h := hw (w⁻¹ • v)
  rw [smul_inv_smul] at h
  calc w⁻¹ • v = -(-(w⁻¹ • v)) := (neg_neg _).symm
    _ = -v := by rw [← h]

end SteinbergBT.TrialityPlane

open SteinbergBT.TrialityPlane

theorem triality_both_orientations_split_prime_plane_normalizers
    {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ r)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ ℓ ^ f - 1) (V : Subgroup (ModGL TwistTag.D4.tag K))
    (hV : ∀ x, x ∈ V ↔ x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧ x ^ p = 1) :
    Nat.card V = p ^ 2 ∧ (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ p = 1) ∧
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.centralizer (V : Set (ModGL TwistTag.D4.tag K)) =
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)) =
      graphFixedRootMonomial TwistTag.D4 K σ.toRingHom ∧
    (∀ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)),
      ∃ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∃ w ∈ relWeylTwist TwistTag.D4,
        g = h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) ∧
    (∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ h' ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ w ∈ relWeylTwist TwistTag.D4, ∀ w' ∈ relWeylTwist TwistTag.D4,
        h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
          h' * canonicalRep (coxeterSystem TwistTag.D4.tag) K w' → h = h' ∧ w = w') ∧
    (∀ w ∈ relWeylTwist TwistTag.D4,
      (∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x) → w = 1) ∧
    (∀ w ∈ relWeylTwist TwistTag.D4, ∀ c : ℤ,
      (∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x ^ c) →
      w = 1 ∨ ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = -v) ∧
    (∃ w ∈ relWeylTwist TwistTag.D4, ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = -v) ∧
    (∀ w ∈ relWeylTwist TwistTag.D4, (∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = -v) →
      ∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x⁻¹) ∧
    ∀ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p →
      (∀ x, x ∈ V ↔ ∃ u v : ℤ, x = trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
        trialityMiddleTorus K σ (ζ ^ v)) ∧
      (∀ u v u' v' : ℤ, trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
          trialityMiddleTorus K σ (ζ ^ v) =
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u') * trialityMiddleTorus K σ (ζ ^ v') ↔
          u ≡ u' [ZMOD p] ∧ v ≡ v' [ZMOD p]) ∧
      (∀ u v : ℤ, trialityOuterRep K * (trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
          trialityMiddleTorus K σ (ζ ^ v)) * (trialityOuterRep K)⁻¹ =
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ (-u + v)) *
          trialityMiddleTorus K σ (ζ ^ v)) ∧
      ∀ u v : ℤ, trialityMiddleRep K * (trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
          trialityMiddleTorus K σ (ζ ^ v)) * (trialityMiddleRep K)⁻¹ =
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
          trialityMiddleTorus K σ (ζ ^ (3 * u - v)) := by
  classical
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have h3 : ∀ c : K, σ (σ (σ c)) = c := by
    intro c
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show (ℓ ^ f) ^ r * ((ℓ ^ f) ^ r * (ℓ ^ f) ^ r) = ((ℓ ^ f) ^ 3) ^ r by ring, ← hK,
      Nat.card_eq_fintype_card, FiniteField.pow_card_pow]
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  obtain ⟨-, ⟨e, he⟩, -, hL2, -, hno, hnm, hnob, hnma⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hk : Nat.card (trialityFixedField K σ.toRingHom) = ℓ ^ f := by
    have h := card_orbitField_D4_orientation hℓ hf hK hr (σ := σ.toRingHom) hσ ⟨1, by decide⟩
    rw [hL2, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
    exact h
  have hHT : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤ torusGroup TwistTag.D4.tag K :=
    fun x hx => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  have hHC : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedRootTorus_le _ _ _
  have hVH : V ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := fun x hx => ((hV x).1 hx).1
  have hVT : V ≤ torusGroup TwistTag.D4.tag K := hVH.trans hHT
  obtain ⟨T, hTdef⟩ : ∃ T : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →* ModGL TwistTag.D4.tag K,
      T = trialityTorusHom σ := ⟨_, rfl⟩
  have hT : ∀ a b, T (a, b) = trialityOuterTorus K σ a * trialityMiddleTorus K σ b :=
    fun a b => by rw [hTdef]; exact trialityTorusHom_apply a b
  have hm1 : trialityMiddleTorus K σ 1 = 1 := by
    rw [trialityMiddleTorus, map_one, torusElt_one]
  have ho1 : trialityOuterTorus K σ 1 = 1 := by
    have h := map_one T
    rw [show (1 : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) = (1, 1) from rfl, hT, hm1,
      mul_one] at h
    exact h
  have hTo : ∀ a, trialityOuterTorus K σ a = T (a, 1) := fun a => by rw [hT, hm1, mul_one]
  have hTm : ∀ b, trialityMiddleTorus K σ b = T (1, b) := fun b => by rw [hT, ho1, one_mul]
  have hTH : ∀ q, T q ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := fun q => by
    obtain ⟨a, b⟩ := q
    rw [hT, ← he]
    exact (e (a, b)).2
  have hTinj : Function.Injective T := fun q q' h => by
    obtain ⟨a, b⟩ := q
    obtain ⟨a', b'⟩ := q'
    rw [hT, hT, ← he, ← he] at h
    exact e.injective (Subtype.ext h)
  have hTe : ∀ q, T q = (e q : ModGL TwistTag.D4.tag K) := fun q => by
    obtain ⟨a, b⟩ := q
    rw [hT, he]
  have hHT' : ∀ x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∃ q, x = T q := fun x hx =>
    ⟨e.symm ⟨x, hx⟩, by rw [hTe, MulEquiv.apply_symm_apply]⟩
  have hconjO : ∀ a b, trialityOuterRep K * T (a, b) * (trialityOuterRep K)⁻¹ =
      T (a⁻¹ * trialityFixedUnit K σ b, b) := by
    intro a b
    rw [hT, conj_mul_conj, hno, hnob]
    simp only [hTo, hTm]
    rw [← map_mul, ← map_mul]
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  have hconjM : ∀ a b, trialityMiddleRep K * T (a, b) * (trialityMiddleRep K)⁻¹ =
      T (a, trialityNorm σ hσ3 a * b⁻¹) := by
    intro a b
    rw [hT, conj_mul_conj, hnma, hnm]
    simp only [hTo, hTm]
    rw [← map_mul, ← map_mul]
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  have hFinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hζfacts : ∀ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p →
      orderOf (trialityFixedUnit K σ ζ) = p ∧
      (∀ u : ℤ, trialityNorm σ hσ3 (trialityFixedUnit K σ ζ ^ u) = ζ ^ (3 * u)) ∧
      (∀ x, x ∈ V ↔ ∃ u v : ℤ, x = T (trialityFixedUnit K σ ζ ^ u, ζ ^ v)) := by
    intro ζ hζ
    set z := trialityFixedUnit K σ ζ with hz
    have hzo : orderOf z = p := by rw [hz, orderOf_injective _ hFinj ζ, hζ]
    have hσz : Units.map σ.toRingHom.toMonoidHom z = z := units_map_trialityFixedUnit ζ
    refine ⟨hzo, fun u => hFinj ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
    · have hσzu := units_map_trialityFixedUnit (σ := σ) (ζ ^ u)
      rw [map_zpow] at hσzu
      rw [trialityFixedUnit_norm, hσzu, hσzu, map_zpow, ← hz]
      group
    · obtain ⟨hxH, hxp⟩ := (hV x).1 hx
      obtain ⟨⟨a, b⟩, rfl⟩ := hHT' x hxH
      rw [← map_pow, ← map_one T] at hxp
      have hab := hTinj hxp
      have ha : a ^ p = 1 := congrArg Prod.fst hab
      have hb : b ^ p = 1 := congrArg Prod.snd hab
      have : NeZero p := ⟨hp.ne_zero⟩
      have hprz : IsPrimitiveRoot z p := hzo ▸ IsPrimitiveRoot.orderOf z
      have hprζ : IsPrimitiveRoot ζ p := hζ ▸ IsPrimitiveRoot.orderOf ζ
      have ha' : a ∈ Subgroup.zpowers z := by
        rw [hprz.zpowers_eq, mem_rootsOfUnity]
        exact ha
      have hb' : b ∈ Subgroup.zpowers ζ := by
        rw [hprζ.zpowers_eq, mem_rootsOfUnity]
        exact hb
      obtain ⟨u, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
      exact ⟨u, v, rfl⟩
    · rintro ⟨u, v, rfl⟩
      refine (hV _).2 ⟨hTH _, ?_⟩
      have hzu : (z ^ u) ^ p = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
          pow_orderOf_eq_one, one_zpow]
      have hζv : (ζ ^ v) ^ p = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ,
          pow_orderOf_eq_one, one_zpow]
      rw [← map_pow, Prod.pow_mk, hzu, hζv]
      exact map_one T
  have : Finite (trialityFixedField K σ.toRingHom) := Subtype.finite
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_units, hk]
    exact hpq
  obtain ⟨hz₀, -, hV₀⟩ := hζfacts ζ₀ hζ₀
  have hσz₀ := units_map_trialityFixedUnit (σ := σ) ζ₀
  have hx₁ : T (trialityFixedUnit K σ ζ₀ ^ (1 : ℤ), ζ₀ ^ (0 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (outerTuple (trialityFixedUnit K σ ζ₀)) := by
    simp only [hT, trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, hσz₀, one_pow,
      inv_one, mul_one]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  have hx₂ : T (trialityFixedUnit K σ ζ₀ ^ (0 : ℤ), ζ₀ ^ (1 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (middleTuple (trialityFixedUnit K σ ζ₀)) := by
    simp only [hT, trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, one_pow, inv_one,
      mul_one, one_mul]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  have hd₁V : rootDiagUnit TwistTag.D4.tag (outerTuple (trialityFixedUnit K σ ζ₀)) ∈ V :=
    (hV₀ _).2 ⟨1, 0, hx₁.symm⟩
  have hd₂V : rootDiagUnit TwistTag.D4.tag (middleTuple (trialityFixedUnit K σ ζ₀)) ∈ V :=
    (hV₀ _).2 ⟨0, 1, hx₂.symm⟩
  have hdisj := rootCharKernel_outer_inter_middle hp5 hz₀
  have hdecomp : ∀ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)),
      ∃ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∃ w ∈ relWeylTwist TwistTag.D4,
        g = h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w := fun g hg =>
    exists_eq_mul_canonicalRep_of_mem_normalizer σ hdisj hVT hd₁V hd₂V (Subgroup.mem_inf.1 hg).1
      (Subgroup.mem_inf.1 hg).2
  have hfaith : ∀ w ∈ relWeylTwist TwistTag.D4,
      (∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x) → w = 1 := by
    intro w hw hfix
    have hstab : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ, rootDiagUnit TwistTag.D4.tag a ∈ V →
        w ∈ rootCharStabilizer a := fun a ha => by
      refine (conj_canonicalRep_eq_iff a w).1 ?_
      have h := hfix _ ha
      calc rootDiagUnit TwistTag.D4.tag a * canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            (rootDiagUnit TwistTag.D4.tag a)⁻¹
          = (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootDiagUnit TwistTag.D4.tag a *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) *
            canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            (rootDiagUnit TwistTag.D4.tag a)⁻¹ := by rw [h]
        _ = canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by group
    exact eq_one_of_mem_rootCharStabilizer hp5 hz₀ hw (hstab _ hd₁V) (hstab _ hd₂V)
  have hHcent : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∀ x ∈ V, x * h = h * x :=
    fun h hh x hx => mul_comm_of_mem_torusGroup' (hVT hx) (hHT hh)
  have hcent : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer (V : Set (ModGL TwistTag.D4.tag K)) =
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgC, hgZ⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨h, hh, w, hw, rfl⟩ := hdecomp _
        (Subgroup.mem_inf.2 ⟨hgC, Subgroup.centralizer_le_normalizer _ hgZ⟩)
      have hw1 : w = 1 := hfaith w hw fun x hx => by
        have h1 := Subgroup.mem_centralizer_iff.1 hgZ x hx
        have h2 := hHcent h hh x hx
        have h3 : x * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
            canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x := by
          have h4 : h * (x * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) =
              h * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x) := by
            rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
          exact mul_left_cancel h4
        rw [← h3, mul_inv_cancel_right]
      rw [hw1, canonicalRep_one, mul_one]
      exact hh
    · intro h hh
      exact Subgroup.mem_inf.2 ⟨hHC hh, Subgroup.mem_centralizer_iff.2 fun x hx => hHcent h hh x hx⟩
  have hHN : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial _ _ _)
  have hnorm : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)) =
      graphFixedRootMonomial TwistTag.D4 K σ.toRingHom := by
    apply le_antisymm
    · intro g hg
      obtain ⟨h, hh, w, hw, rfl⟩ := hdecomp g hg
      exact mul_mem (hHN hh) (canonicalRep_mem_graphFixedRootMonomial _ _ _ hw)
    · intro g hg
      have key : ∀ g ∈ graphFixedRootMonomial TwistTag.D4 K σ.toRingHom, ∀ x ∈ V,
          g * x * g⁻¹ ∈ V := by
        intro g hg x hx
        refine (hV _).2 ⟨?_, ?_⟩
        · have h := (graphFixedRootTorus_subgroupOf_normal TwistTag.D4 K σ.toRingHom).conj_mem
            ⟨x, hHN (hVH hx)⟩ (Subgroup.mem_subgroupOf.2 (hVH hx)) ⟨g, hg⟩
          exact Subgroup.mem_subgroupOf.1 h
        · rw [conj_pow, ((hV x).1 hx).2, mul_one, mul_inv_cancel]
      refine Subgroup.mem_inf.2 ⟨graphFixedRootMonomial_le _ _ _ hg,
        Subgroup.mem_normalizer_iff.2 fun x => ⟨key g hg x, fun hx => ?_⟩⟩
      have h := key g⁻¹ (inv_mem hg) _ hx
      rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
        mul_one] at h
  have hunique : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ h' ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ w ∈ relWeylTwist TwistTag.D4, ∀ w' ∈ relWeylTwist TwistTag.D4,
        h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
          h' * canonicalRep (coxeterSystem TwistTag.D4.tag) K w' → h = h' ∧ w = w' := by
    intro h hh h' hh' w _ w' _ heq
    obtain ⟨-, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors TwistTag.D4.tag K
      (outerTuple (trialityFixedUnit K σ ζ₀))
    obtain ⟨hw, hh, -, -⟩ := huniq w w' h h' 1 1 1 1 (hHT hh) (hHT hh') (one_mem _) (one_mem _)
      (one_mem _) (one_mem _) (by simpa using heq)
    exact ⟨hh, hw⟩
  have hw₀ : trialityOppositionWeyl ∈ relWeylTwist TwistTag.D4 := by
    have h0 := TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩
    have h1 := TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩
    exact mul_mem h0 (mul_mem (mul_mem (mul_mem h1 h0) h1) (inv_mem (mul_mem h1 h0)))
  have hfold₀ : foldPair trialityOppositionWeyl = ((-1, 0), (0, -1)) := by
    simp only [foldPair, trialityOppositionWeyl_smul, fold_neg, fold_single0, fold_single2]
    rfl
  have hscal : ∀ w ∈ relWeylTwist TwistTag.D4, ∀ c : ℤ,
      (∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x ^ c) →
      w = 1 ∨ ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = -v := by
    intro w hw c hc
    have hchar : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ, rootDiagUnit TwistTag.D4.tag a ∈ V →
        ∀ v, rootChar a (w⁻¹ • v) = rootChar a v ^ c := by
      intro a ha v
      have h := hc _ ha
      rw [canonicalRep_conj_rootDiagUnit] at h
      have h2 : rootDiagUnit TwistTag.D4.tag a ^ c = rootDiagUnit TwistTag.D4.tag (a ^ c) :=
        (map_zpow (rootDiagUnitHom TwistTag.D4.tag K) a c).symm
      rw [h2] at h
      rw [← rootChar_weylTuple, rootDiagUnit_injective h, rootChar_zpow_tuple]
    have hw' : w⁻¹ ∈ relWeylTwist TwistTag.D4 := inv_mem hw
    rcases foldPair_eq_of_scalar hp5 hz₀ hw' (hchar _ hd₁V) (hchar _ hd₂V) with h1 | h1
    · left
      exact inv_eq_one.1 (eq_one_of_foldPair hw' h1)
    · right
      have heq := foldPair_injective hw' hw₀ (h1.trans hfold₀.symm)
      have hw0 : w = trialityOppositionWeyl⁻¹ := by rw [← heq, inv_inv]
      intro v
      rw [hw0]
      exact inv_smul_eq_neg trialityOppositionWeyl_smul v
  have hinv : ∀ w ∈ relWeylTwist TwistTag.D4, (∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = -v) →
      ∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x⁻¹ := by
    intro w _ hneg x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hVT hx)
    exact canonicalRep_conj_rootDiagUnit_of_neg hneg l
  have hcoord : ∀ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p → ∀ u v u' v' : ℤ,
      T (trialityFixedUnit K σ ζ ^ u, ζ ^ v) = T (trialityFixedUnit K σ ζ ^ u', ζ ^ v') ↔
        u ≡ u' [ZMOD p] ∧ v ≡ v' [ZMOD p] := by
    intro ζ hζ u v u' v'
    have hzo := (hζfacts ζ hζ).1
    rw [hTinj.eq_iff, Prod.mk.injEq, zpow_eq_zpow_iff_modEq, zpow_eq_zpow_iff_modEq, hzo, hζ]
  have hcard : Nat.card V = p ^ 2 := by
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    let F : Fin p × Fin p → V := fun ij =>
      ⟨T (trialityFixedUnit K σ ζ₀ ^ ((ij.1 : ℕ) : ℤ), ζ₀ ^ ((ij.2 : ℕ) : ℤ)),
        (hV₀ _).2 ⟨_, _, rfl⟩⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨i, j⟩ ⟨i', j'⟩ hij
        obtain ⟨h1, h2⟩ := (hcoord ζ₀ hζ₀ _ _ _ _).1 (congrArg Subtype.val hij)
        have key : ∀ m m' : Fin p, ((m : ℕ) : ℤ) ≡ ((m' : ℕ) : ℤ) [ZMOD p] → m = m' := by
          intro m m' hm
          have e1 : ((m : ℕ) : ℤ) % p = (m : ℕ) :=
            Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast m.2)
          have e2 : ((m' : ℕ) : ℤ) % p = (m' : ℕ) :=
            Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast m'.2)
          have h : ((m : ℕ) : ℤ) = (m' : ℕ) := by
            unfold Int.ModEq at hm
            rw [e1, e2] at hm
            exact hm
          exact Fin.ext (by exact_mod_cast h)
        rw [key i i' h1, key j j' h2]
      · rintro ⟨x, hx⟩
        obtain ⟨u, v, rfl⟩ := (hV₀ x).1 hx
        have hu0 := Int.emod_nonneg u hp0.ne'
        have hv0 := Int.emod_nonneg v hp0.ne'
        have hu1 := Int.emod_lt_of_pos u hp0
        have hv1 := Int.emod_lt_of_pos v hp0
        refine ⟨(⟨(u % p).toNat, by omega⟩, ⟨(v % p).toNat, by omega⟩), Subtype.ext ?_⟩
        refine (hcoord ζ₀ hζ₀ _ _ _ _).2 ⟨?_, ?_⟩
        · change (((u % p).toNat : ℕ) : ℤ) ≡ u [ZMOD p]
          rw [Int.toNat_of_nonneg hu0]
          exact Int.mod_modEq u p
        · change (((v % p).toNat : ℕ) : ℤ) ≡ v [ZMOD p]
          rw [Int.toNat_of_nonneg hv0]
          exact Int.mod_modEq v p
    rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, Nat.card_fin, sq]
  refine ⟨hcard, fun x hx y hy => mul_comm_of_mem_torusGroup' (hVT hx) (hVT hy),
    fun x hx => ((hV x).1 hx).2, hcent, hnorm, hdecomp, hunique, hfaith, hscal,
    ⟨_, hw₀, trialityOppositionWeyl_smul⟩, hinv, fun ζ hζ => ?_⟩
  obtain ⟨-, hnormζ, hVζ⟩ := hζfacts ζ hζ
  refine ⟨fun x => by simpa only [hT] using hVζ x, fun u v u' v' => by
    simpa only [hT] using hcoord ζ hζ u v u' v', fun u v => ?_, fun u v => ?_⟩
  · rw [← hT, hconjO, ← hT, map_zpow, ← zpow_neg, ← zpow_add]
  · rw [← hT, hconjM, ← hT, hnormζ, ← zpow_neg, ← zpow_add, sub_eq_add_neg]

end CFSG.RankThree.Chevalley
