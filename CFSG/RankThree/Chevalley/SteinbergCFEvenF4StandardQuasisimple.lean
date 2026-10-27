module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.TitsSimplicity.Simplicity
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.Chevalley.FixedCollection
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
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
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {A : Set (Fin τ.rank)}

theorem exists_left_descent_mem_of_ne_one {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A)
    (h1 : w ≠ 1) : ∃ i ∈ A,
      (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w := by
  obtain ⟨⟨ω, hωA, hωw, hωl⟩, -⟩ := length_eq_parabolic_length hw
  cases ω with
  | nil =>
    exact absurd (by rw [← hωw]; rfl) h1
  | cons i ω' =>
    refine ⟨i, hωA i List.mem_cons_self, ?_⟩
    have hsw : simple τ i * w = (coxeterSystem τ).wordProd ω' := by
      rw [← hωw, CoxeterSystem.wordProd_cons, ← mul_assoc]
      change (coxeterSystem τ).simple i * (coxeterSystem τ).simple i * _ = _
      rw [CoxeterSystem.simple_mul_simple_self, one_mul]
    have hle : (coxeterSystem τ).length (simple τ i * w) ≤ ω'.length := by
      rw [hsw]
      exact (coxeterSystem τ).length_wordProd_le ω'
    have hge : (coxeterSystem τ).length w ≤ (coxeterSystem τ).length (simple τ i * w) + 1 := by
      have h2 := (coxeterSystem τ).length_mul_le (simple τ i) (simple τ i * w)
      rw [← mul_assoc] at h2
      change (coxeterSystem τ).length ((coxeterSystem τ).simple i * (coxeterSystem τ).simple i *
        w) ≤ (coxeterSystem τ).length ((coxeterSystem τ).simple i) + _ at h2
      rw [CoxeterSystem.simple_mul_simple_self, one_mul, CoxeterSystem.length_simple] at h2
      omega
    rw [List.length_cons] at hωl
    omega

theorem weylElt_mem_of_canonicalRep_mem {P : Subgroup (ModGL τ K)}
    (hBP : subsystemBorel τ K A ≤ P) {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A)
    {i : Fin τ.rank} (hi : i ∈ A)
    (hlen : (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w)
    (hn : canonicalRep (coxeterSystem τ) K w ∈ P) : weylElt τ K i 1 ∈ P := by
  have h' : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1 := by
    omega
  have hy : ∀ c : K, yUnit τ K i c ∈ P := by
    intro c
    have hyc : yUnit τ K i c ∈ rootSubgroup τ K (-Pi.single i 1) := by
      rw [← pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    obtain ⟨b, hb, hyb⟩ := exists_mul_canonicalRep_eq_subsystem hw
      (neg_mem_parabolicRoots (single_mem_parabolicRoots hi)) (height_inv_smul_neg_single_pos h')
      hyc
    have e : yUnit τ K i c = canonicalRep (coxeterSystem τ) K w * b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
      rw [← hyb, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hn (hBP hb)) (inv_mem hn)
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hBP (xUnit_mem_subsystemBorel hi _)) (hy _))
    (hBP (xUnit_mem_subsystemBorel hi _))

theorem le_subsystemBorel_of_forall_weylElt_notMem {P : Subgroup (ModGL τ K)}
    (hBP : subsystemBorel τ K A ≤ P) (hPQ : P ≤ subsystemGroup τ K A)
    (hn : ∀ i ∈ A, weylElt τ K i 1 ∉ P) : P ≤ subsystemBorel τ K A := by
  intro g hg
  have hgQ : g ∈ (subsystemGroup τ K A : Set (ModGL τ K)) := hPQ hg
  rw [subsystemGroup_eq_subsystemCells] at hgQ
  obtain ⟨w, hw, hgw⟩ := mem_subsystemCells.1 hgQ
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_subsystemCell.1 hgw
  have hnw : canonicalRep (coxeterSystem τ) K w ∈ P := by
    have e : canonicalRep (coxeterSystem τ) K w =
        b₁⁻¹ * (b₁ * canonicalRep (coxeterSystem τ) K w * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBP hb₁)) hg) (inv_mem (hBP hb₂))
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · obtain ⟨i, hi, hlen⟩ := exists_left_descent_mem_of_ne_one hw hw1
    exact absurd (weylElt_mem_of_canonicalRep_mem hBP hw hi hlen hnw) (hn i hi)

theorem subsystemGroup_le_of_forall_weylElt_mem {P : Subgroup (ModGL τ K)}
    (hBP : subsystemBorel τ K A ≤ P) (hn : ∀ i ∈ A, weylElt τ K i 1 ∈ P) :
    subsystemGroup τ K A ≤ P := by
  intro g hg
  have hgQ : g ∈ (subsystemGroup τ K A : Set (ModGL τ K)) := hg
  rw [subsystemGroup_eq_subsystemCells] at hgQ
  obtain ⟨w, hw, hgw⟩ := mem_subsystemCells.1 hgQ
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_subsystemCell.1 hgw
  obtain ⟨⟨ω, hωA, hωw, hωl⟩, -⟩ := length_eq_parabolic_length hw
  have hred : (coxeterSystem τ).IsReduced ω := by
    rw [CoxeterSystem.IsReduced, hωw, hωl]
  have hnw : canonicalRep (coxeterSystem τ) K w ∈ P := by
    rw [← hωw, canonicalRep_wordProd hred]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hn i (hωA i hi)
  exact mul_mem (mul_mem (hBP hb₁) hnw) (hBP hb₂)

theorem eq_one_of_mem_subsystemTorus_of_mem_parabolicLeviUnipotent {c : ModGL τ K}
    (hcT : c ∈ subsystemTorus τ K A) (hcU : c ∈ parabolicLeviUnipotent τ K A) : c = 1 :=
  (eq_of_mul_eq_subsystem (t := c) (t' := 1) (v := 1) (v' := c) hcT (one_mem _) (one_mem _) hcU
    (by rw [mul_one, one_mul])).1

theorem xUnit_mem_parabolicLeviUnipotent {i : Fin τ.rank} (hi : i ∈ A) (c : K) :
    xUnit τ K i c ∈ parabolicLeviUnipotent τ K A := by
  have hx : xUnit τ K i c ∈ rootSubgroup τ K (Pi.single i 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  exact Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
    (single_mem_parabolicPosRoots hi) hx)

theorem le_subsystemTorus_of_le_subsystemBorel {M : Subgroup (ModGL τ K)}
    (hnorm : subsystemGroup τ K A ≤ Subgroup.normalizer (M : Set (ModGL τ K)))
    (hMB : M ≤ subsystemBorel τ K A) :
    M ≤ subsystemTorus τ K A ∧ ∀ m ∈ M, ∀ g ∈ subsystemGroup τ K A, m * g = g * m := by
  classical
  obtain ⟨w₀, hw₀, -, hw₀img⟩ := exists_longest_mem_parabolicWeylGroup τ A
  set n := canonicalRep (coxeterSystem τ) K w₀ with hn
  have hnQ : n ∈ subsystemGroup τ K A := canonicalRep_mem_subsystemGroup hw₀
  obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
  obtain ⟨-, -, hBH, -⟩ := opposite_Borel_intersection τ K w₁ hw₁
  have hconjB : (subsystemBorel τ K A).map (MulAut.conj n).toMonoidHom ≤
      torusGroup τ K ⊔ negUnipotent τ K := by
    rw [subsystemBorel, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact subsystemTorus_le_torusGroup (canonicalRep_conj_mem_subsystemTorus hw₀ ht)
    · rw [parabolicLeviUnipotent, (canonical_weyl_root_transport τ K).1 w₀ _
        (fun α hα => hα.2.1), hw₀img]
      refine rootSpan_mono fun α hα => ?_
      obtain ⟨β, hβ, rfl⟩ := hα
      exact ⟨IsRoot.neg hβ.2.1, by rw [height_neg]; have := hβ.2.2; omega⟩
  have hMT : M ≤ subsystemTorus τ K A := by
    intro m hm
    have hn1 : n⁻¹ * m * n⁻¹⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.1 (hnorm (inv_mem hnQ)) m).1 hm
    rw [inv_inv] at hn1
    have hmB : m ∈ subsystemBorel τ K A := hMB hm
    have hm' : m ∈ torusGroup τ K ⊔ negUnipotent τ K :=
      hconjB ⟨n⁻¹ * m * n, hMB hn1, by
        change n * (n⁻¹ * m * n) * n⁻¹ = m
        group⟩
    have hmH : m ∈ torusGroup τ K := by
      rw [← hBH]
      exact ⟨subsystemBorel_le_borelGroup hmB, hm'⟩
    rw [← subsystemGroup_inf_torusGroup]
    exact ⟨subsystemBorel_le_subsystemGroup hmB, hmH⟩
  have hcommU : ∀ m ∈ M, ∀ u ∈ parabolicLeviUnipotent τ K A, m * u = u * m := by
    intro m hm u hu
    have hmT := hMT hm
    have hc : m * u * m⁻¹ * u⁻¹ ∈ M := by
      have h1 : u * m⁻¹ * u⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1
        (hnorm (parabolicLeviUnipotent_le_subsystemGroup hu)) _).1 (inv_mem hm)
      have h2 := mul_mem hm h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    have hcU : m * u * m⁻¹ * u⁻¹ ∈ parabolicLeviUnipotent τ K A := by
      have h1 : m * u * m⁻¹ ∈ parabolicLeviUnipotent τ K A :=
        (Subgroup.mem_normalizer_iff.1 (subsystemTorus_le_normalizer hmT) u).1 hu
      exact mul_mem h1 (inv_mem hu)
    have h1 := eq_one_of_mem_subsystemTorus_of_mem_parabolicLeviUnipotent (hMT hc) hcU
    calc m * u = m * u * m⁻¹ * u⁻¹ * u * m := by group
      _ = u * m := by rw [h1, one_mul]
  refine ⟨hMT, fun m hm g hg => ?_⟩
  have hle : subsystemGroup τ K A ≤ Subgroup.centralizer {m} := by
    rw [subsystemGroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (hcommU m hm _ (xUnit_mem_parabolicLeviUnipotent hi c)).symm
    ·
      have hmem : (-Pi.single i 1 : Fin τ.rank → ℤ) ∈
          (fun α => w₀ • α) '' parabolicPosRoots τ A := by
        rw [hw₀img]
        exact ⟨_, single_mem_parabolicPosRoots hi, rfl⟩
      obtain ⟨β, hβ, hβi⟩ := hmem
      have hyc : yUnit τ K i c ∈ rootSubgroup τ K (-Pi.single i 1) := by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      rw [← hβi, ← (canonical_weyl_root_transport τ K).2.1 w₀ β hβ.2.1] at hyc
      obtain ⟨u, hu, hu'⟩ := hyc
      have huU : u ∈ parabolicLeviUnipotent τ K A :=
        Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβ hu)
      have hm' : n⁻¹ * m * n ∈ M := by
        have := (Subgroup.mem_normalizer_iff.1 (hnorm (inv_mem hnQ)) m).1 hm
        rwa [inv_inv] at this
      have h1 := hcommU _ hm' u huU
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← hu']
      change n * u * n⁻¹ * m = m * (n * u * n⁻¹)
      calc n * u * n⁻¹ * m = n * (u * (n⁻¹ * m * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * m * n) * u) * n⁻¹ := by rw [h1]
        _ = m * (n * u * n⁻¹) := by group
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem weylElt_notMem_center_sup {i : Fin τ.rank} (hi : i ∈ A) :
    weylElt τ K i 1 ∉ (Subgroup.center (subsystemGroup τ K A)).map
      (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A := by
  classical
  set Z := (Subgroup.center (subsystemGroup τ K A)).map (subsystemGroup τ K A).subtype with hZ
  have hZcomm : ∀ z ∈ Z, ∀ g ∈ subsystemGroup τ K A, z * g = g * z := by
    rintro _ ⟨z, hz, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩).symm
  have hZN : Z ≤ Subgroup.normalizer (subsystemBorel τ K A : Set (ModGL τ K)) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have hzQ : z ∈ subsystemGroup τ K A := by
      obtain ⟨z', -, rfl⟩ := hz
      exact z'.2
    by_cases hb : b ∈ subsystemGroup τ K A
    · rw [show z * b * z⁻¹ = b by rw [hZcomm z hz b hb, mul_inv_cancel_right]]
    · constructor
      · intro hb'
        exact absurd (subsystemBorel_le_subsystemGroup hb') hb
      · intro hb'
        exact absurd (by
          have := mul_mem (mul_mem (inv_mem hzQ) (subsystemBorel_le_subsystemGroup hb')) hzQ
          rwa [show z⁻¹ * (z * b * z⁻¹) * z = b by group] at this) hb
  intro hmem
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN] at hmem
  obtain ⟨z, hz, b, hb, hzb⟩ := hmem
  obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
  obtain ⟨-, -, -, hBU⟩ := opposite_Borel_intersection τ K w₁ hw₁
  have hxB : weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ ∈ borelGroup τ K := by
    have hbx : b * xUnit τ K i 1 * b⁻¹ ∈ subsystemGroup τ K A :=
      mul_mem (mul_mem (subsystemBorel_le_subsystemGroup hb) (xUnit_mem_subsystemGroup hi 1))
        (inv_mem (subsystemBorel_le_subsystemGroup hb))
    rw [← hzb, show z * b * xUnit τ K i 1 * (z * b)⁻¹ = z * (b * xUnit τ K i 1 * b⁻¹) * z⁻¹ by
      group, hZcomm z hz _ hbx, mul_inv_cancel_right]
    exact subsystemBorel_le_borelGroup (mul_mem (mul_mem hb (xUnit_mem_subsystemBorel hi 1))
      (inv_mem hb))
  have hxU : weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ ∈ negUnipotent τ K := by
    have h1 := (canonical_weyl_root_transport τ K).2.1 (simple τ i) (Pi.single i 1)
      (isRoot_single τ i)
    rw [canonicalRep_simple, simple_smul, reflect_single_self] at h1
    have h2 : weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ ∈
        rootSubgroup τ K (-Pi.single i 1) := by
      rw [← h1]
      exact ⟨_, by rw [← pinnedX_single]; exact Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
    exact Subgroup.mem_iSup_of_mem (-Pi.single i 1) (Subgroup.mem_iSup_of_mem
      ⟨isRoot_neg_single τ i, by rw [height_neg, height_single]; omega⟩ h2)
  have h1 : weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ = 1 := by
    have := Subgroup.mem_inf.2 ⟨hxB, hxU⟩
    rwa [hBU, Subgroup.mem_bot] at this
  have h2 : xUnit τ K i 1 = 1 := by
    have := congrArg (fun y => (weylElt τ K i 1)⁻¹ * y * weylElt τ K i 1) h1
    simpa [mul_assoc] using this
  have h3 := pinnedX_injective (τ := τ) (R := K) (Pi.single i 1)
    (show pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 by
      rw [pinnedX_single, pinnedX_zero, h2])
  exact one_ne_zero h3

theorem center_le_subsystemTorus :
    (Subgroup.center (subsystemGroup τ K A)).map (subsystemGroup τ K A).subtype ≤
      subsystemTorus τ K A := by
  set Z := (Subgroup.center (subsystemGroup τ K A)).map (subsystemGroup τ K A).subtype with hZ
  have hZQ : Z ≤ subsystemGroup τ K A := Subgroup.map_subtype_le _
  have hP := le_subsystemBorel_of_forall_weylElt_notMem (P := Z ⊔ subsystemBorel τ K A)
    le_sup_right (sup_le hZQ subsystemBorel_le_subsystemGroup)
    fun i hi => weylElt_notMem_center_sup hi
  have hcomm : ∀ g ∈ subsystemGroup τ K A, ∀ z ∈ Z, g * z * g⁻¹ = z := by
    rintro g hg _ ⟨z, hz, rfl⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    change g * (z : ModGL τ K) = z * g at h1
    change g * (z : ModGL τ K) * g⁻¹ = z
    rw [h1, mul_inv_cancel_right]
  have hnorm : subsystemGroup τ K A ≤ Subgroup.normalizer (Z : Set (ModGL τ K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm g hg x hx]
      exact hx
    · intro hx
      have h1 := hcomm g⁻¹ (inv_mem hg) _ hx
      rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
      rw [h1]
      exact hx
  exact (le_subsystemTorus_of_le_subsystemBorel hnorm (le_sup_left.trans hP)).1

theorem weylElt_mem_sup_of_adjacent {M : Subgroup (ModGL τ K)}
    (hnorm : subsystemGroup τ K A ≤ Subgroup.normalizer (M : Set (ModGL τ K)))
    {i j : Fin τ.rank} (hi : i ∈ A) (hj : j ∈ A)
    (h2 : (coxeterSystem τ).length (simple τ i * simple τ j) =
      (coxeterSystem τ).length (simple τ j) + 1)
    (h3 : (coxeterSystem τ).length (simple τ j * (simple τ i * simple τ j)) =
      (coxeterSystem τ).length (simple τ i * simple τ j) + 1)
    (hni : weylElt τ K i 1 ∈ M ⊔ subsystemBorel τ K A) :
    weylElt τ K j 1 ∈ M ⊔ subsystemBorel τ K A := by
  classical
  have hBN : subsystemBorel τ K A ≤ Subgroup.normalizer (M : Set (ModGL τ K)) :=
    subsystemBorel_le_subsystemGroup.trans hnorm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hni
  obtain ⟨m, hm, b, hb, hmb⟩ := hni
  have hsi : simple τ i ∈ parabolicWeylGroup τ A := Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hsj : simple τ j ∈ parabolicWeylGroup τ A := Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hjQ : weylElt τ K j 1 ∈ subsystemGroup τ K A := weylElt_mem_subsystemGroup hj 1
  have hmD : m ∈ subsystemCell τ K A (simple τ i) := mem_subsystemCell.2 ⟨1, one_mem _, b⁻¹,
    inv_mem hb, by rw [one_mul, canonicalRep_simple, ← hmb, mul_inv_cancel_right]⟩
  have hnD : weylElt τ K j 1 ∈ subsystemCell τ K A (simple τ j) := mem_subsystemCell.2 ⟨1,
    one_mem _, 1, one_mem _, by rw [one_mul, mul_one, canonicalRep_simple]⟩
  have hd : (torusElt τ K j (-1))⁻¹ ∈ subsystemBorel τ K A :=
    inv_mem (torusElt_mem_subsystemBorel hj (-1))
  have hninvD : (weylElt τ K j 1)⁻¹ ∈ subsystemCell τ K A (simple τ j) := mem_subsystemCell.2
    ⟨1, one_mem _, _, hd, by
      rw [one_mul, canonicalRep_simple, ← weylElt_one_mul_self]
      group⟩
  have hcell : weylElt τ K j 1 * m * (weylElt τ K j 1)⁻¹ ∈
      subsystemCell τ K A (simple τ j * (simple τ i * simple τ j)) := by
    rw [← subsystemCell_simple_mul_of_length_eq_add_one hj (mul_mem hsi hsj) h3,
      ← subsystemCell_simple_mul_of_length_eq_add_one hi hsj h2, mul_assoc]
    exact Set.mul_mem_mul hnD (Set.mul_mem_mul hmD hninvD)
  have hconj : weylElt τ K j 1 * m * (weylElt τ K j 1)⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.1 (hnorm hjQ) m).1 hm
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_subsystemCell.1 hcell
  have hv : canonicalRep (coxeterSystem τ) K (simple τ j * (simple τ i * simple τ j)) ∈
      M ⊔ subsystemBorel τ K A := by
    have e : canonicalRep (coxeterSystem τ) K (simple τ j * (simple τ i * simple τ j)) =
        b₁⁻¹ * (weylElt τ K j 1 * m * (weylElt τ K j 1)⁻¹) * b₂⁻¹ := by
      rw [← he]
      group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right (inv_mem hb₁)) (Subgroup.mem_sup_left hconj))
      (Subgroup.mem_sup_right (inv_mem hb₂))
  refine weylElt_mem_of_canonicalRep_mem le_sup_right (mul_mem hsj (mul_mem hsi hsj)) hj ?_ hv
  rw [← mul_assoc, show simple τ j * simple τ j = 1 from by
    change (coxeterSystem τ).simple j * (coxeterSystem τ).simple j = 1
    exact CoxeterSystem.simple_mul_simple_self _ _, one_mul, h3]

theorem forall_mem_of_interval {n : ℕ} {A S : Set (Fin n)}
    (hconn : ∀ i ∈ A, ∀ j ∈ A, ∀ k, i ≤ k → k ≤ j → k ∈ A) {i₀ : Fin n} (hi₀ : i₀ ∈ A)
    (hi₀S : i₀ ∈ S)
    (hstep : ∀ i ∈ A, ∀ j ∈ A, i ∈ S → ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) → j ∈ S) :
    ∀ k ∈ A, k ∈ S := by
  have hup : ∀ m : ℕ, ∀ k ∈ A, (k : ℕ) = i₀ + m → k ∈ S := by
    intro m
    induction m with
    | zero =>
      intro k _ hk
      rwa [show k = i₀ from Fin.ext (by omega)]
    | succ m ih =>
      intro k hk hkm
      have hk' : (k : ℕ) - 1 < n := by omega
      set k' : Fin n := ⟨k - 1, hk'⟩
      have hk'A : k' ∈ A := hconn i₀ hi₀ k hk k'
        (Fin.le_iff_val_le_val.2 (by change (i₀ : ℕ) ≤ (k : ℕ) - 1; omega))
        (Fin.le_iff_val_le_val.2 (by change (k : ℕ) - 1 ≤ k; omega))
      exact hstep k' hk'A k hk (ih k' hk'A (by change (k : ℕ) - 1 = i₀ + m; omega))
        (Or.inl (by change (k : ℕ) - 1 + 1 = k; omega))
  have hdown : ∀ m : ℕ, ∀ k ∈ A, (k : ℕ) + m = i₀ → k ∈ S := by
    intro m
    induction m with
    | zero =>
      intro k _ hk
      rwa [show k = i₀ from Fin.ext (by omega)]
    | succ m ih =>
      intro k hk hkm
      have hk' : (k : ℕ) + 1 < n := by omega
      set k' : Fin n := ⟨k + 1, hk'⟩
      have hk'A : k' ∈ A := hconn k hk i₀ hi₀ k'
        (Fin.le_iff_val_le_val.2 (by change (k : ℕ) ≤ (k : ℕ) + 1; omega))
        (Fin.le_iff_val_le_val.2 (by change (k : ℕ) + 1 ≤ i₀; omega))
      exact hstep k' hk'A k hk (ih k' hk'A (by change (k : ℕ) + 1 + m = i₀; omega))
        (Or.inr (by change (k : ℕ) + 1 = (k : ℕ) + 1; rfl))
  intro k hk
  rcases le_total (i₀ : ℕ) k with h | h
  · exact hup (k - i₀) k hk (by omega)
  · exact hdown (i₀ - k) k hk (by omega)

theorem isSolvable_subsystemBorel : Group.IsSolvable (subsystemBorel τ K A) := by
  obtain ⟨φ, -, hker⟩ := exists_subsystemBorel_hom_ker (τ := τ) (J := A) K
  have : Group.IsSolvable (subsystemTorus τ K A) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (subsystemTorus_mul_comm K a.2 b.2)
  have : Group.IsNilpotent (parabolicLeviUnipotent τ K A) := isNilpotent_parabolicLeviUnipotent K
  have e : (parabolicLeviUnipotent τ K A).subgroupOf (subsystemBorel τ K A) ≃*
      parabolicLeviUnipotent τ K A :=
    Subgroup.subgroupOfEquivOfLe le_sup_right
  have : Group.IsNilpotent ((parabolicLeviUnipotent τ K A).subgroupOf (subsystemBorel τ K A)) :=
    Group.nilpotent_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact Group.isSolvable_of_ker_le_range
    ((parabolicLeviUnipotent τ K A).subgroupOf (subsystemBorel τ K A)).subtype φ
    (by rw [hker, Subgroup.range_subtype])

theorem subsystemGroup_le_center_or_eq_top (hperf : Group.IsPerfect (subsystemGroup τ K A))
    (hconn : ∀ i ∈ A, ∀ j ∈ A, ∀ k, i ≤ k → k ≤ j → k ∈ A)
    (hadj : ∀ i ∈ A, ∀ j ∈ A, ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) →
      (coxeterSystem τ).length (simple τ i * simple τ j) =
          (coxeterSystem τ).length (simple τ j) + 1 ∧
        (coxeterSystem τ).length (simple τ j * (simple τ i * simple τ j)) =
          (coxeterSystem τ).length (simple τ i * simple τ j) + 1)
    (M : Subgroup (subsystemGroup τ K A)) [hM : M.Normal] :
    M ≤ Subgroup.center (subsystemGroup τ K A) ∨ M = ⊤ := by
  classical
  have hMmQ : M.map (subsystemGroup τ K A).subtype ≤ subsystemGroup τ K A :=
    Subgroup.map_subtype_le _
  have hconjM : ∀ g ∈ subsystemGroup τ K A, ∀ x ∈ M.map (subsystemGroup τ K A).subtype,
      g * x * g⁻¹ ∈ M.map (subsystemGroup τ K A).subtype := by
    intro g hg x hx
    obtain ⟨m, hmM, hmx⟩ := hx
    have h1 := hM.conj_mem m hmM ⟨g, hg⟩
    refine ⟨_, h1, ?_⟩
    rw [← hmx]
    rfl
  have hnorm : subsystemGroup τ K A ≤
      Subgroup.normalizer (M.map (subsystemGroup τ K A).subtype : Set (ModGL τ K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjM g hg x, fun hx => ?_⟩
    have h1 := hconjM g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  by_cases hex : ∃ i₀ ∈ A,
      weylElt τ K i₀ 1 ∈ M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A
  · right
    obtain ⟨i₀, hi₀, hn₀⟩ := hex
    have hall : ∀ k ∈ A,
        weylElt τ K k 1 ∈ M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A :=
      forall_mem_of_interval (S := {k | weylElt τ K k 1 ∈
        M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A}) hconn hi₀
        hn₀ fun i hi j hj hiS hij =>
          weylElt_mem_sup_of_adjacent hnorm hi hj (hadj i hi j hj hij).1 (hadj i hi j hj hij).2
            hiS
    have hQP := subsystemGroup_le_of_forall_weylElt_mem le_sup_right hall
    have : Group.IsSolvable ((subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A)) := by
      have := isSolvable_subsystemBorel (τ := τ) (K := K) (A := A)
      have e := Subgroup.subgroupOfEquivOfLe (subsystemBorel_le_subsystemGroup (τ := τ) (K := K)
        (A := A))
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hsup : M ⊔ (subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (g : ModGL τ K) ∈
          M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A := hQP g.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (subsystemBorel_le_subsystemGroup.trans hnorm)] at hg
      obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, hmb⟩ := hg
      have hbQ : b ∈ subsystemGroup τ K A := subsystemBorel_le_subsystemGroup hb
      have hg' : g = m * ⟨b, hbQ⟩ := Subtype.ext (by rw [← hmb]; rfl)
      rw [hg']
      exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right
        (show (⟨b, hbQ⟩ : subsystemGroup τ K A) ∈
          (subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A) from hb))
    exact CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf inferInstance hsup
  · left
    push Not at hex
    have hPB := le_subsystemBorel_of_forall_weylElt_notMem le_sup_right
      (sup_le hMmQ subsystemBorel_le_subsystemGroup) hex
    have h1 := (le_subsystemTorus_of_le_subsystemBorel hnorm (le_sup_left.trans hPB)).2
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 m ⟨m, hm, rfl⟩ g g.2).symm

theorem isPerfect_subsystemGroup (hK : ∃ s : Finset K, s.card = 4) :
    Group.IsPerfect (subsystemGroup τ K A) := by
  classical
  have hSL : Group.IsPerfect (SL2 K) := CFSG.LinearGroups.special_linear_dimension_two_perfect hK
  have hrange : ∀ i ∈ A, (simpleRootSL2 τ K i).range ≤ subsystemGroup τ K A := by
    intro i hi
    rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨c, rfl⟩ := hg
      change simpleRootSL2 τ K i (uSL c) ∈ subsystemGroup τ K A
      rw [simpleRootSL2_uSL]
      exact xUnit_mem_subsystemGroup hi c
    · obtain ⟨c, rfl⟩ := hg
      change simpleRootSL2 τ K i (vSL c) ∈ subsystemGroup τ K A
      rw [simpleRootSL2_vSL]
      exact yUnit_mem_subsystemGroup hi c
  have hcomm : ∀ i ∈ A, (simpleRootSL2 τ K i).range ≤
      ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
    intro i hi
    rw [MonoidHom.range_eq_map, ← hSL.commutator_eq_top, commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map]
    exact Subgroup.commutator_mono (hrange i hi) (hrange i hi)
  have hle : subsystemGroup τ K A ≤ ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
    conv_lhs => rw [subsystemGroup]
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact hcomm i hi ⟨uSL c, simpleRootSL2_uSL i c⟩
    · exact hcomm i hi ⟨vSL c, simpleRootSL2_vSL i c⟩
  have hmap : (commutator (subsystemGroup τ K A)).map (subsystemGroup τ K A).subtype =
      ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨eq_top_iff.2 fun g _ => ?_⟩
  have hg : (g : ModGL τ K) ∈ ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := hle g.2
  rw [← hmap] at hg
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [show g' = g from Subtype.ext hgg'] at hg'

theorem nontrivial_subsystemGroup (hA : A.Nonempty) : Nontrivial (subsystemGroup τ K A) := by
  obtain ⟨i, hi⟩ := hA
  refine ⟨⟨⟨xUnit τ K i 1, xUnit_mem_subsystemGroup hi 1⟩, 1, fun h => ?_⟩⟩
  have h2 : xUnit τ K i 1 = 1 := congrArg Subtype.val h
  have h3 := pinnedX_injective (τ := τ) (R := K) (Pi.single i 1)
    (show pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 by
      rw [pinnedX_single, pinnedX_zero, h2])
  exact one_ne_zero h3

theorem list_prod_torusElt_conj_xUnit (L : List (Fin τ.rank × Kˣ)) (k : Fin τ.rank) (c : K) :
    (L.map fun p => torusElt τ K p.1 p.2).prod * xUnit τ K k c *
        ((L.map fun p => torusElt τ K p.1 p.2).prod)⁻¹ =
      xUnit τ K k (((L.map fun p => p.2 ^ τ.cartan p.1 k).prod : Kˣ) * c) := by
  induction L generalizing c with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    calc torusElt τ K p.1 p.2 * (L.map fun p => torusElt τ K p.1 p.2).prod * xUnit τ K k c *
          (((L.map fun p => torusElt τ K p.1 p.2).prod)⁻¹ * (torusElt τ K p.1 p.2)⁻¹) =
        torusElt τ K p.1 p.2 * ((L.map fun p => torusElt τ K p.1 p.2).prod * xUnit τ K k c *
          ((L.map fun p => torusElt τ K p.1 p.2).prod)⁻¹) * (torusElt τ K p.1 p.2)⁻¹ := by group
      _ = xUnit τ K k (((p.2 ^ τ.cartan p.1 k : Kˣ) : K) *
          (((L.map fun p => p.2 ^ τ.cartan p.1 k).prod : Kˣ) * c)) := by
        rw [ih, (simple_torus_root_conjugation τ K p.1 k p.2 _).1]
      _ = _ := by rw [Units.val_mul, mul_assoc]

theorem F4_adjacent_lengths : ∀ i j : Fin Tag.F4.rank, ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) →
    (coxeterSystem Tag.F4).length (simple Tag.F4 i * simple Tag.F4 j) =
        (coxeterSystem Tag.F4).length (simple Tag.F4 j) + 1 ∧
      (coxeterSystem Tag.F4).length (simple Tag.F4 j * (simple Tag.F4 i * simple Tag.F4 j)) =
        (coxeterSystem Tag.F4).length (simple Tag.F4 i * simple Tag.F4 j) + 1 := by
  intro i j hij
  rw [length_simple_mul_eq_add_one_iff, length_simple_mul_eq_add_one_iff, mul_inv_rev,
    simple_inv, simple_inv, mul_smul, simple_smul, simple_smul, simple_smul]
  revert i j
  decide

theorem units_eq_one_of_sq_eq_one_of_charTwo [CharP K 2] {u : Kˣ} (h : u ^ 2 = 1) : u = 1 :=
  Units.ext (CharTwo.sq_injective (by simpa using congrArg Units.val h))

theorem eq_one_of_torus_equations_12 {G : Type*} [CommGroup G] (hsq : ∀ x : G, x ^ 2 = 1 → x = 1)
    {a b : G} (e1 : a ^ 2 * (b ^ 2)⁻¹ = 1) (e2 : a⁻¹ * b ^ 2 = 1) : a = 1 ∧ b = 1 := by
  have h2 : a = b ^ 2 := inv_mul_eq_one.1 e2
  rw [← h2, sq, mul_inv_cancel_right] at e1
  exact ⟨e1, hsq b (h2 ▸ e1)⟩

theorem eq_one_of_torus_equations_012 {G : Type*} [CommGroup G]
    (hsq : ∀ x : G, x ^ 2 = 1 → x = 1) {a b c : G} (e0 : a ^ 2 * b⁻¹ = 1)
    (e1 : a⁻¹ * (b ^ 2 * (c ^ 2)⁻¹) = 1) (e2 : b⁻¹ * c ^ 2 = 1) : a = 1 ∧ b = 1 ∧ c = 1 := by
  have h0 : a ^ 2 = b := mul_inv_eq_one.1 e0
  have h2 : b = c ^ 2 := inv_mul_eq_one.1 e2
  rw [← h2, sq b, mul_inv_cancel_right, ← h0, sq, inv_mul_cancel_left] at e1
  have hb : b = 1 := by rw [← h0, e1, one_pow]
  exact ⟨e1, hb, hsq c (h2 ▸ hb)⟩

theorem eq_one_of_torus_equations_123 {G : Type*} [CommGroup G]
    (hsq : ∀ x : G, x ^ 2 = 1 → x = 1) {b c d : G} (e1 : b ^ 2 * (c ^ 2)⁻¹ = 1)
    (e2 : b⁻¹ * (c ^ 2 * d⁻¹) = 1) (e3 : c⁻¹ * d ^ 2 = 1) : b = 1 ∧ c = 1 ∧ d = 1 := by
  have h3 : c = d ^ 2 := inv_mul_eq_one.1 e3
  have hbc : b = c := by
    have h1 : (b * c⁻¹) ^ 2 = 1 := by rw [mul_pow, inv_pow, e1]
    exact mul_inv_eq_one.1 (hsq _ h1)
  rw [hbc, sq c, mul_assoc, inv_mul_cancel_left] at e2
  have hcd : c = d := mul_inv_eq_one.1 e2
  have hd : d = 1 := by
    have h1 : d ^ 2 = d := by rw [← h3, hcd]
    rw [sq] at h1
    exact mul_eq_left.1 h1
  exact ⟨hbc.trans (hcd.trans hd), hcd.trans hd, hd⟩

theorem center_subsystemGroup_F4_eq_bot [CharP K 2] {J : Set (Fin Tag.F4.rank)}
    (hJ : Fin.val '' J = ({1, 2} : Set ℕ) ∨ Fin.val '' J = {0, 1, 2} ∨
      Fin.val '' J = {1, 2, 3}) :
    Subgroup.center (subsystemGroup .F4 K J) = ⊥ := by
  classical
  have hmemJ : ∀ k : Fin Tag.F4.rank, k ∈ J ↔ (k : ℕ) ∈ Fin.val '' J := fun k =>
    ⟨fun h => ⟨k, h, rfl⟩, fun ⟨k', hk', hkk'⟩ => (Fin.ext hkk' : k' = k) ▸ hk'⟩
  rw [eq_bot_iff]
  intro z hz
  have hzT : (z : ModGL .F4 K) ∈ subsystemTorus .F4 K J := center_le_subsystemTorus ⟨z, hz, rfl⟩
  obtain ⟨s, ⟨hs1, hst⟩, -⟩ := existsUnique_subsystemTorus_coords_F4 hzT
  have hL : (List.ofFn fun i => torusElt .F4 K i (s i)) =
      (List.ofFn fun i => (i, s i)).map fun p => torusElt .F4 K p.1 p.2 := by
    rw [List.map_ofFn]
    rfl
  have heq : ∀ k ∈ J, (List.ofFn fun i => s i ^ Tag.F4.cartan i k).prod = 1 := by
    intro k hk
    have h1 := congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hz ⟨xUnit .F4 K k 1, xUnit_mem_subsystemGroup hk 1⟩)
    change xUnit .F4 K k 1 * (z : ModGL .F4 K) = z * xUnit .F4 K k 1 at h1
    have h2 : (z : ModGL .F4 K) * xUnit .F4 K k 1 * (z : ModGL .F4 K)⁻¹ = xUnit .F4 K k 1 := by
      rw [← h1, mul_inv_cancel_right]
    rw [hst, hL, list_prod_torusElt_conj_xUnit, List.map_ofFn, mul_one] at h2
    have h3 : (((List.ofFn fun i => s i ^ Tag.F4.cartan i k).prod : Kˣ) : K) = 1 :=
      pinnedX_injective (τ := .F4) (R := K) (Pi.single k 1) (by
        rw [pinnedX_single, pinnedX_single]
        exact h2)
    exact Units.ext h3
  have hsq : ∀ x : Kˣ, x ^ 2 = 1 → x = 1 := fun x hx => units_eq_one_of_sq_eq_one_of_charTwo hx
  have hin : ∀ k : Fin 4, (k : ℕ) ∈ Fin.val '' J → (k : Fin Tag.F4.rank) ∈ J := fun k hk =>
    (hmemJ k).2 hk
  have hout : ∀ k : Fin 4, (k : ℕ) ∉ Fin.val '' J → s k = 1 := fun k hk =>
    hs1 k fun h => hk ((hmemJ k).1 h)
  have hs : ∀ i, s i = 1 := by
    rcases hJ with hJ | hJ | hJ
    · have e1 := heq (1 : Fin 4) (hin 1 (by rw [hJ]; simp))
      have e2 := heq (2 : Fin 4) (hin 2 (by rw [hJ]; simp))
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (1 : Fin 4)).prod = 1 at e1
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (2 : Fin 4)).prod = 1 at e2
      have h0 := hout 0 (by rw [hJ]; simp)
      have h3 := hout 3 (by rw [hJ]; simp)
      simp [List.ofFn_succ, Tag.cartan, h0, h3] at e1 e2
      obtain ⟨ha, hb⟩ := eq_one_of_torus_equations_12 hsq e1 e2
      intro i
      fin_cases i <;> assumption
    · have e0 := heq (0 : Fin 4) (hin 0 (by rw [hJ]; simp))
      have e1 := heq (1 : Fin 4) (hin 1 (by rw [hJ]; simp))
      have e2 := heq (2 : Fin 4) (hin 2 (by rw [hJ]; simp))
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (0 : Fin 4)).prod = 1 at e0
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (1 : Fin 4)).prod = 1 at e1
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (2 : Fin 4)).prod = 1 at e2
      have h3 := hout 3 (by rw [hJ]; simp)
      simp [List.ofFn_succ, Tag.cartan, h3] at e0 e1 e2
      obtain ⟨ha, hb, hc⟩ := eq_one_of_torus_equations_012 hsq e0 e1 e2
      intro i
      fin_cases i <;> assumption
    · have e1 := heq (1 : Fin 4) (hin 1 (by rw [hJ]; simp))
      have e2 := heq (2 : Fin 4) (hin 2 (by rw [hJ]; simp))
      have e3 := heq (3 : Fin 4) (hin 3 (by rw [hJ]; simp))
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (1 : Fin 4)).prod = 1 at e1
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (2 : Fin 4)).prod = 1 at e2
      change (List.ofFn (n := 4) fun i => s i ^ Tag.F4.cartan i (3 : Fin 4)).prod = 1 at e3
      have h0 := hout 0 (by rw [hJ]; simp)
      simp [List.ofFn_succ, Tag.cartan, h0] at e1 e2 e3
      obtain ⟨hb, hc, hd⟩ := eq_one_of_torus_equations_123 hsq e1 e2 e3
      intro i
      fin_cases i <;> assumption
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hst]
  change _ = (1 : ModGL .F4 K)
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  change torusElt .F4 K i (s i) = 1
  rw [hs i, torusElt_one]

theorem even_F4_connected_standard_root_groups_quasisimple (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) (J : Set (Fin Tag.F4.rank)) (hJ : J.Nonempty)
    (hconn : ∀ i ∈ J, ∀ j ∈ J, ∀ k, i ≤ k → k ≤ j → k ∈ J) :
    Group.IsPerfect (subsystemGroup .F4 K J) ∧
    (Subgroup.center (subsystemGroup .F4 K J)).map (subsystemGroup .F4 K J).subtype ≤
      subsystemTorus .F4 K J ∧
    (∀ N : Subgroup (subsystemGroup .F4 K J), N.Normal → N ≠ ⊤ →
      N ≤ Subgroup.center (subsystemGroup .F4 K J)) ∧
    IsQuasisimple (subsystemGroup .F4 K J) ∧
    ((Fin.val '' J = ({1, 2} : Set ℕ) ∨ Fin.val '' J = {0, 1, 2} ∨ Fin.val '' J = {1, 2, 3}) →
      Subgroup.center (subsystemGroup .F4 K J) = ⊥ ∧ IsSimpleGroup (subsystemGroup .F4 K J) ∧
        ∃ a b : subsystemGroup .F4 K J, a * b ≠ b * a) := by
  classical
  have hperf := isPerfect_subsystemGroup (τ := .F4) (A := J) (exists_finset_card_four hK)
  have hnt := nontrivial_subsystemGroup (τ := .F4) (K := K) hJ
  have hdich : ∀ M : Subgroup (subsystemGroup .F4 K J), M.Normal →
      M ≤ Subgroup.center (subsystemGroup .F4 K J) ∨ M = ⊤ := fun M hM => by
    have := hM
    exact subsystemGroup_le_center_or_eq_top hperf hconn
      (fun i _ j _ hij => F4_adjacent_lengths i j hij) M
  have hqs : IsQuasisimple (subsystemGroup .F4 K J) :=
    CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf hdich
  refine ⟨hperf, center_le_subsystemTorus, fun N hN hNtop => (hdich N hN).resolve_right hNtop,
    hqs, fun hJ' => ?_⟩
  have hZ := center_subsystemGroup_F4_eq_bot (K := K) hJ'
  refine ⟨hZ, { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }, ?_⟩
  · rcases hdich N hN with h | h
    · left
      rw [hZ] at h
      exact le_bot_iff.1 h
    · exact Or.inr h
  · obtain ⟨-, -, a, b, hab⟩ := hqs
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

end CFSG.RankThree.Chevalley
