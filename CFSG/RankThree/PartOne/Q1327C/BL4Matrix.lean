module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.CentralLift.LinearRootRelations
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.R10Final
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BRows
public import CFSG.RankThree.PartOne.Q1327C.P5Glue
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.Q1327C

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.CentralLift.LinearRoots
open CFSG.RankThree.PartTwo.Census

abbrev SL4 (k : Type) [Field k] := Matrix.SpecialLinearGroup (Fin 4) k

variable {k : Type} [Field k]

theorem commute_diag_entry {x g : Matrix (Fin 4) (Fin 4) k} {D : Fin 4 → k}
    (hD : x = Matrix.diagonal D) (h : x * g = g * x) (a b : Fin 4) :
    D a * g a b = g a b * D b := by
  have := congrFun (congrFun h a) b
  rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  exact this

theorem entry_zero_of_ne {Pm : Subgroup (SL4 k)} {g x : SL4 k}
    (hg : g ∈ Subgroup.centralizer (Pm : Set (SL4 k))) (hx : x ∈ Pm) {D : Fin 4 → k}
    (hD : (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D) {a b : Fin 4} (hab : D a ≠ D b) :
    (g : Matrix (Fin 4) (Fin 4) k) a b = 0 := by
  have hxg : x * g = g * x := (Subgroup.mem_centralizer_iff.1 hg) x hx
  have hmat : (x : Matrix (Fin 4) (Fin 4) k) * (g : Matrix (Fin 4) (Fin 4) k) =
      (g : Matrix (Fin 4) (Fin 4) k) * (x : Matrix (Fin 4) (Fin 4) k) := by
    have := congrArg (fun m : SL4 k => (m : Matrix (Fin 4) (Fin 4) k)) hxg
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have h1 := commute_diag_entry hD hmat a b
  have h2 : (D a - D b) * (g : Matrix (Fin 4) (Fin 4) k) a b = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) hab
  · exact h

theorem commute_of_offdiag_zero {g h : SL4 k}
    (hg : ∀ a b : Fin 4, a ≠ b → (g : Matrix (Fin 4) (Fin 4) k) a b = 0)
    (hh : ∀ a b : Fin 4, a ≠ b → (h : Matrix (Fin 4) (Fin 4) k) a b = 0) : g * h = h * g := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  have hg' : (g : Matrix (Fin 4) (Fin 4) k).IsDiag := hg
  have hh' : (h : Matrix (Fin 4) (Fin 4) k).IsDiag := hh
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← hg'.diagonal_diag, ← hh'.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

theorem exists_complement : ∀ i j : Fin 4, i ≠ j → ∃ c l : Fin 4, (c ≠ i ∧ c ≠ j ∧ l ≠ i ∧ l ≠ j ∧
    c ≠ l) ∧ ∀ m : Fin 4, m = i ∨ m = j ∨ m = c ∨ m = l := by decide

theorem fin4_sum {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) {i j c l : Fin 4}
    (h : ∀ m : Fin 4, m = i ∨ m = j ∨ m = c ∨ m = l) (hij : i ≠ j) (hic : i ≠ c) (hil : i ≠ l)
    (hjc : j ≠ c) (hjl : j ≠ l) (hcl : c ≠ l) : ∑ m, f m = f i + f j + f c + f l := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {i, j, c, l} := by
    ext m
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact h m
  rw [huniv, Finset.sum_insert (by simp [hij, hic, hil]), Finset.sum_insert (by simp [hjc, hjl]),
    Finset.sum_insert (by simp [hcl]), Finset.sum_singleton]
  abel

theorem fin4_prod {α : Type*} [CommMonoid α] (f : Fin 4 → α) {i j c l : Fin 4}
    (h : ∀ m : Fin 4, m = i ∨ m = j ∨ m = c ∨ m = l) (hij : i ≠ j) (hic : i ≠ c) (hil : i ≠ l)
    (hjc : j ≠ c) (hjl : j ≠ l) (hcl : c ≠ l) : ∏ m, f m = f i * f j * f c * f l := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {i, j, c, l} := by
    ext m
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact h m
  rw [huniv, Finset.prod_insert (by simp [hij, hic, hil]), Finset.prod_insert (by simp [hjc, hjl]),
    Finset.prod_insert (by simp [hcl]), Finset.prod_singleton]
  simp only [mul_assoc]

theorem sl4_km_bot_of_no_pair {Pm Km : Subgroup (SL4 k)}
    (hKc : Km ≤ Subgroup.centralizer (Pm : Set (SL4 k)))
    (hnopair : ∀ a b : Fin 4, a ≠ b → ∃ x ∈ Pm, ∃ D : Fin 4 → k,
      (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ D a ≠ D b)
    (hKperf : Group.IsPerfect Km) : Km = ⊥ := by
  by_contra hne
  have : Nontrivial ↥Km := (Subgroup.nontrivial_iff_ne_bot Km).2 hne
  have hoff : ∀ g ∈ Km, ∀ a b : Fin 4, a ≠ b → (g : Matrix (Fin 4) (Fin 4) k) a b = 0 := by
    intro g hg a b hab
    obtain ⟨x, hx, D, hD, hDab⟩ := hnopair a b hab
    exact entry_zero_of_ne (hKc hg) hx hD hDab
  have hcomm : ∀ a b : ↥Km, a * b = b * a := fun a b =>
    Subtype.ext (commute_of_offdiag_zero (hoff a a.2) (hoff b b.2))
  exact Group.IsPerfect.not_isSolvable ↥Km (Group.isSolvable_of_comm hcomm)

theorem exists_separating [Finite k] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrK : p ∣ Nat.card kˣ) {Pm : Subgroup (SL4 k)}
    (hPd : ∀ x ∈ Pm, ∃ D : Fin 4 → k,
      (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ ∀ i, D i ^ p = 1)
    (hPcard : Nat.card Pm = p ^ 2) {i j c l : Fin 4}
    (hcover : ∀ m : Fin 4, m = i ∨ m = j ∨ m = c ∨ m = l) (hij : i ≠ j) (hic : i ≠ c)
    (hil : i ≠ l) (hjc : j ≠ c) (hjl : j ≠ l) (hcl : c ≠ l)
    (hrel : ∀ x ∈ Pm, ∀ D : Fin 4 → k, (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D →
      D i = D j) :
    ∃ x ∈ Pm, ∃ D : Fin 4 → k, (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧
      D i = D j ∧ D i ≠ D c ∧ D i ≠ D l ∧ D c ≠ D l := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let μ := rootsOfUnity p k
  have hμ : Nat.card μ = p := card_rootsOfUnity_of_dvd hp hrK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hrK
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hdiv : ∀ n : ℕ, ζ ^ n = 1 → p ∣ n := fun n hn => by
    rw [← hζ]; exact orderOf_dvd_of_pow_eq_one hn
  have hζ1 : ζ ≠ 1 := fun h1 => by
    have := hdiv 1 (by rw [h1]; simp)
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 => by
    have := Nat.le_of_dvd (by norm_num) (hdiv 2 h2)
    omega
  have hζ3 : ζ ^ 3 ≠ 1 := fun h3 => by
    have := Nat.le_of_dvd (by norm_num) (hdiv 3 h3)
    omega
  choose! Dx hDx using hPd
  have hDxne : ∀ x ∈ Pm, ∀ m, Dx x m ≠ 0 := fun x hx m h0 => by
    have := (hDx x hx).2 m
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  have hdetD : ∀ x ∈ Pm, Dx x i * Dx x j * Dx x c * Dx x l = 1 := by
    intro x hx
    have h1 : ((x : Matrix (Fin 4) (Fin 4) k)).det = 1 := x.2
    rw [(hDx x hx).1, Matrix.det_diagonal, fin4_prod _ hcover hij hic hil hjc hjl hcl] at h1
    exact h1
  let φ : Pm → μ × μ := fun x =>
    (⟨Units.mk0 (Dx x i) (hDxne x x.2 i), (mem_rootsOfUnity p _).2 (Units.ext (by
      simpa using (hDx x x.2).2 i))⟩,
     ⟨Units.mk0 (Dx x c) (hDxne x x.2 c), (mem_rootsOfUnity p _).2 (Units.ext (by
      simpa using (hDx x x.2).2 c))⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hxi : Dx x i = Dx y i := congrArg (fun z : μ × μ => ((z.1 : kˣ) : k)) hxy
    have hxc : Dx x c = Dx y c := congrArg (fun z : μ × μ => ((z.2 : kˣ) : k)) hxy
    have hxj : Dx x j = Dx y j := by
      rw [← hrel x x.2 _ (hDx x x.2).1, ← hrel y y.2 _ (hDx y y.2).1, hxi]
    have hxl : Dx x l = Dx y l := by
      have h1 := hdetD x x.2
      have h2 := hdetD y y.2
      have hne : Dx x i * Dx x j * Dx x c ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hDxne x x.2 i) (hDxne x x.2 j)) (hDxne x x.2 c)
      have h3 : Dx x l = Dx y l := by
        apply mul_left_cancel₀ hne
        have : Dx x i * Dx x j * Dx x c * Dx y l = 1 := by rw [hxi, hxj, hxc]; exact h2
        rw [h1, this]
      exact h3
    have hDeq : Dx x = Dx y := by
      funext m
      rcases hcover m with rfl | rfl | rfl | rfl
      · exact hxi
      · exact hxj
      · exact hxc
      · exact hxl
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    rw [(hDx x x.2).1, (hDx y y.2).1, hDeq]
  have hcard : Nat.card (μ × μ) ≤ Nat.card Pm := by
    rw [Nat.card_prod, hμ, hPcard, sq]
  have hbij := hφ.bijective_of_nat_card_le hcard
  set z1 : μ := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩ with hz1def
  obtain ⟨x, hx⟩ := hbij.2 (z1, z1⁻¹ ^ 2)
  have hxi : Dx x i = (ζ : k) := by
    have := congrArg (fun z : μ × μ => ((z.1 : kˣ) : k)) hx
    simpa [φ, z1] using this
  have hxc : Dx x c = ((ζ : k)⁻¹) ^ 2 := by
    have := congrArg (fun z : μ × μ => ((z.2 : kˣ) : k)) hx
    simpa [φ, z1] using this
  have hxj : Dx x j = Dx x i := (hrel x x.2 _ (hDx x x.2).1).symm
  have hz0 : (ζ : k) ≠ 0 := ζ.ne_zero
  have hxl : Dx x l = 1 := by
    have h1 := hdetD x x.2
    rw [hxj, hxi, hxc] at h1
    have h2 : (ζ : k) * ζ * (((ζ : k)⁻¹) ^ 2) = 1 := by field_simp
    rw [h2, one_mul] at h1
    exact h1
  have hz1 : (ζ : k) ≠ 1 := fun h => hζ1 (Units.ext (by simpa using h))
  have hz2 : (ζ : k) ^ 2 ≠ 1 := fun h => hζ2 (Units.ext (by simpa using h))
  have hz3 : (ζ : k) ^ 3 ≠ 1 := fun h => hζ3 (Units.ext (by simpa using h))
  refine ⟨x, x.2, Dx x, (hDx x x.2).1, hxj.symm, ?_, ?_, ?_⟩
  · rw [hxi, hxc]
    intro h
    apply hz3
    calc (ζ : k) ^ 3 = (ζ : k) * (ζ : k) ^ 2 := by ring
      _ = ((ζ : k)⁻¹) ^ 2 * (ζ : k) ^ 2 := by rw [← h]
      _ = 1 := by field_simp
  · rw [hxi, hxl]
    exact hz1
  · rw [hxc, hxl]
    intro h
    apply hz2
    simpa [inv_pow, inv_eq_one] using h

theorem perfect_hom_eq_one {H : Type} [Group H] (hH : Group.IsPerfect H) (φ : H →* k) (h : H) :
    φ h = 1 := by
  have h1 : commutator H ≤ φ.toHomUnits.ker := Abelianization.commutator_subset_ker φ.toHomUnits
  have h2 : h ∈ commutator H := by
    rw [hH.commutator_eq_top]
    exact Subgroup.mem_top h
  have h3 := h1 h2
  rw [MonoidHom.mem_ker] at h3
  have := congrArg Units.val h3
  simpa using this

theorem sl4_component_card [Finite k] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrK : p ∣ Nat.card kˣ) {Pm Km : Subgroup (SL4 k)}
    (hPd : ∀ x ∈ Pm, ∃ D : Fin 4 → k,
      (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ ∀ i, D i ^ p = 1)
    (hPcard : Nat.card Pm = p ^ 2) (hKc : Km ≤ Subgroup.centralizer (Pm : Set (SL4 k)))
    (hKperf : Group.IsPerfect Km) (hKne : Km ≠ ⊥)
    (hKsub : (Km.subgroupOf (Subgroup.centralizer (Pm : Set (SL4 k)))).IsSubnormal)
    (hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k)) :
    Nat.card Km = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  classical
  by_cases hex : ∃ i j : Fin 4, i ≠ j ∧ ∀ x ∈ Pm, ∀ D : Fin 4 → k,
      (x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D → D i = D j
  swap
  · exfalso
    push Not at hex
    exact hKne (sl4_km_bot_of_no_pair hKc (fun a b hab => hex a b hab) hKperf)
  obtain ⟨i, j, hij, hrel⟩ := hex
  obtain ⟨c, l, ⟨hci, hcj, hli, hlj, hcl⟩, hcover⟩ := exists_complement i j hij
  obtain ⟨xs, hxs, Ds, hDs, hDsij, hDsic, hDsil, hDscl⟩ := exists_separating hp hp5 hrK hPd hPcard
    hcover hij hci.symm hli.symm hcj.symm hlj.symm hcl hrel
  have hsep : ∀ a b : Fin 4, a ≠ b → ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) → Ds a ≠ Ds b := by
    intro a b hab hpair
    rcases hcover a with ha | ha | ha | ha <;> rcases hcover b with hb | hb | hb | hb <;>
      rw [ha, hb] at hab hpair ⊢ <;>
      first
      | exact absurd rfl hab
      | exact absurd (Or.inl ⟨rfl, rfl⟩) hpair
      | exact absurd (Or.inr ⟨rfl, rfl⟩) hpair
      | exact hDsic
      | exact hDsil
      | exact hDscl
      | exact Ne.symm hDsic
      | exact Ne.symm hDsil
      | exact Ne.symm hDscl
      | exact fun h => hDsic (hDsij.trans h)
      | exact fun h => hDsil (hDsij.trans h)
      | exact fun h => hDsic (hDsij.trans h.symm)
      | exact fun h => hDsil (hDsij.trans h.symm)
  have hzero : ∀ g ∈ Subgroup.centralizer (Pm : Set (SL4 k)), ∀ a b : Fin 4, a ≠ b →
      ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) → (g : Matrix (Fin 4) (Fin 4) k) a b = 0 :=
    fun g hg a b hab hpair => entry_zero_of_ne hg hxs hDs (hsep a b hab hpair)
  have hic : i ≠ c := hci.symm
  have hil : i ≠ l := hli.symm
  have hjc : j ≠ c := hcj.symm
  have hjl : j ≠ l := hlj.symm
  have hspKm : ∀ g ∈ Km, ∀ a b : Fin 4, a ≠ b → ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) →
      (g : Matrix (Fin 4) (Fin 4) k) a b = 0 := fun g hg => hzero g (hKc hg)
  have hmulentry : ∀ (g h : SL4 k), g ∈ Km → h ∈ Km → ∀ a b : Fin 4, (a = i ∨ a = j) →
      ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) a b =
        (g : Matrix (Fin 4) (Fin 4) k) a i * (h : Matrix (Fin 4) (Fin 4) k) i b +
          (g : Matrix (Fin 4) (Fin 4) k) a j * (h : Matrix (Fin 4) (Fin 4) k) j b := by
    intro g h hg hh a b ha
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      fin4_sum _ hcover hij hic hil hjc hjl hcl]
    have hac : a ≠ c := by rcases ha with rfl | rfl <;> assumption
    have hal : a ≠ l := by rcases ha with rfl | rfl <;> assumption
    have h1 : (g : Matrix (Fin 4) (Fin 4) k) a c = 0 := hspKm g hg a c hac (by
      rintro (⟨_, h1⟩ | ⟨_, h1⟩) <;> simp_all)
    have h2 : (g : Matrix (Fin 4) (Fin 4) k) a l = 0 := hspKm g hg a l hal (by
      rintro (⟨_, h1⟩ | ⟨_, h1⟩) <;> simp_all)
    rw [h1, h2]
    ring
  have hmulm : ∀ (g h : SL4 k), g ∈ Km → h ∈ Km → ∀ m : Fin 4, m ≠ i → m ≠ j →
      ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) m m =
        (g : Matrix (Fin 4) (Fin 4) k) m m * (h : Matrix (Fin 4) (Fin 4) k) m m := by
    intro g h hg hh m hmi hmj
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single m]
    · intro e _ hem
      have : (g : Matrix (Fin 4) (Fin 4) k) m e = 0 := hspKm g hg m e (Ne.symm hem) (by
        rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        exacts [hmi h1, hmj h1])
      rw [this, zero_mul]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  let ψc : ↥Km →* k :=
    { toFun := fun g => ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) c c
      map_one' := by simp
      map_mul' := fun g h => hmulm g h g.2 h.2 c hci hcj }
  let ψl : ↥Km →* k :=
    { toFun := fun g => ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) l l
      map_one' := by simp
      map_mul' := fun g h => hmulm g h g.2 h.2 l hli hlj }
  let ψd : ↥Km →* k :=
    { toFun := fun g => ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) i i *
        ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) j j -
        ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) i j * ((g : SL4 k) : Matrix (Fin 4) (Fin 4) k) j i
      map_one' := by simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij.symm]
      map_mul' := fun g h => by
        have e1 := hmulentry g h g.2 h.2 i i (Or.inl rfl)
        have e2 := hmulentry g h g.2 h.2 i j (Or.inl rfl)
        have e3 := hmulentry g h g.2 h.2 j i (Or.inr rfl)
        have e4 := hmulentry g h g.2 h.2 j j (Or.inr rfl)
        show ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) i i *
          ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) j j -
          ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) i j *
          ((g * h : SL4 k) : Matrix (Fin 4) (Fin 4) k) j i = _
        rw [e1, e2, e3, e4]
        ring }
  have hc1 : ∀ g ∈ Km, (g : Matrix (Fin 4) (Fin 4) k) c c = 1 := fun g hg =>
    perfect_hom_eq_one hKperf ψc ⟨g, hg⟩
  have hl1 : ∀ g ∈ Km, (g : Matrix (Fin 4) (Fin 4) k) l l = 1 := fun g hg =>
    perfect_hom_eq_one hKperf ψl ⟨g, hg⟩
  have hd1 : ∀ g ∈ Km, (g : Matrix (Fin 4) (Fin 4) k) i i * (g : Matrix (Fin 4) (Fin 4) k) j j -
      (g : Matrix (Fin 4) (Fin 4) k) i j * (g : Matrix (Fin 4) (Fin 4) k) j i = 1 := fun g hg =>
    perfect_hom_eq_one hKperf ψd ⟨g, hg⟩
  have hgB : ∀ g ∈ Km, ∃ B : Matrix.SpecialLinearGroup (Fin 2) k, rhoSL k i j B = g := by
    intro g hg
    have hdetB : (!![(g : Matrix (Fin 4) (Fin 4) k) i i, (g : Matrix (Fin 4) (Fin 4) k) i j;
        (g : Matrix (Fin 4) (Fin 4) k) j i, (g : Matrix (Fin 4) (Fin 4) k) j j] :
        Matrix (Fin 2) (Fin 2) k).det = 1 := by
      rw [Matrix.det_fin_two_of]
      exact hd1 g hg
    let B : Matrix.SpecialLinearGroup (Fin 2) k := ⟨_, hdetB⟩
    refine ⟨B, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro x y
    rw [coe_rhoSL hij B]
    symm
    refine pairMat_cases (P := fun x y c => (g : Matrix (Fin 4) (Fin 4) k) x y = c) hij
      rfl rfl rfl rfl ?_ ?_ ?_ x y
    · intro x y hx hya hyb
      refine hspKm g hg x y ?_ ?_
      · rintro rfl
        rcases hx with rfl | rfl
        · exact hya rfl
        · exact hyb rfl
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hyb h2
        · exact hya h2
    · intro x y hxa hxb hy
      refine hspKm g hg x y ?_ ?_
      · rintro rfl
        rcases hy with rfl | rfl
        · exact hxa rfl
        · exact hxb rfl
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hxa h1
        · exact hxb h1
    · intro x y hxa hxb hya hyb
      by_cases hxy : x = y
      · subst hxy
        rw [Matrix.one_apply_eq]
        rcases hcover x with h | h | h | h
        · exact absurd h hxa
        · exact absurd h hxb
        · rw [h]; exact hc1 g hg
        · rw [h]; exact hl1 g hg
      · rw [Matrix.one_apply_ne hxy]
        refine hspKm g hg x y hxy ?_
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hxa h1
        · exact hxb h1
  let C : Subgroup (SL4 k) := Subgroup.centralizer (Pm : Set (SL4 k))
  let N : Subgroup (SL4 k) := (rhoSL k i j).range
  have hKN : Km ≤ N := fun g hg => by
    obtain ⟨B, hB⟩ := hgB g hg
    exact ⟨B, hB⟩
  have hNC : N ≤ C := by
    rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨D, hD, -⟩ := hPd x hx
    have hDij : D i = D j := hrel x hx D hD
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD, coe_rhoSL hij,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    refine pairMat_cases (P := fun a b c => D a * c = c * D b) hij ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
    · exact mul_comm _ _
    · rw [hDij]; exact mul_comm _ _
    · rw [hDij]; exact mul_comm _ _
    · exact mul_comm _ _
    · intro x y _ _ _
      simp
    · intro x y _ _ _
      simp
    · intro x y _ _ _ _
      by_cases hxy : x = y
      · subst hxy
        exact mul_comm _ _
      · simp [Matrix.one_apply_ne hxy]
  have hsimpleN : IsSimpleGroup (N.subgroupOf C) := by
    have e1 : N.subgroupOf C ≃* N := Subgroup.subgroupOfEquivOfLe hNC
    have e2 : N ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
      (MonoidHom.ofInjective (rhoSL_injective hij)).symm
    have := hsimple
    exact MulEquiv.isSimpleGroup (e1.trans e2)
  have hsub1 : ((Km.subgroupOf C).comap (N.subgroupOf C).subtype).IsSubnormal :=
    hKsub.comap (N.subgroupOf C).subtype
  have hNK : N ≤ Km := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimpleN hsub1 with h0 | h0
    · exfalso
      obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hKne
      have hy : (⟨⟨(g : SL4 k), hKc g.2⟩, hKN g.2⟩ : ↥(N.subgroupOf C)) ∈
          (Km.subgroupOf C).comap (N.subgroupOf C).subtype := g.2
      rw [h0, Subgroup.mem_bot] at hy
      apply hg1
      have := congrArg (fun z : ↥(N.subgroupOf C) => ((z : ↥C) : SL4 k)) hy
      exact Subtype.ext this
    · intro n hn
      have hy : (⟨⟨n, hNC hn⟩, hn⟩ : ↥(N.subgroupOf C)) ∈
          (Km.subgroupOf C).comap (N.subgroupOf C).subtype := by
        rw [h0]
        exact Subgroup.mem_top _
      exact hy
  have hKeq : Km = N := le_antisymm hKN hNK
  rw [hKeq]
  exact (Nat.card_congr (MonoidHom.ofInjective (rhoSL_injective hij)).toEquiv).symm

end CFSG.RankThree.PartOne.Q1327C
