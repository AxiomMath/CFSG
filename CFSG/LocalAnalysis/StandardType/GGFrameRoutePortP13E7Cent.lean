module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7Hyp
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Cent
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Weyl
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.SmallF3.Omega.E7RootSet
  Certificates.OmegaSevenMax TableBExcTwo TableBExcTwoTB TableBExcTwoFusion TableBExc
  CFSG.RankThree.CentralCover CFSG.RankThree.PartOne.KE8F
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem mem_p13e7HypVec_frame
    {v : Fin 7 → ZMod 3} : v ∈ p13e7HypVec (redV (frameE7.root 0)) ↔ v 0 = 0 := by
  have hcoord : p13e7Coord (Pi.single 0 (1 : ZMod 3)) = redV (frameE7.root 0) := by
    have h : p13e7Coord (Pi.single 0 (1 : ZMod 3) : Fin 7 → ZMod 3) =
        ∑ i, (Pi.single 0 (1 : ZMod 3) : Fin 7 → ZMod 3) i •
          (redV (frameE7.root i) : V) := by
      funext k
      rfl
    rw [h, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h0
      simp at h0
  rw [mem_p13e7HypVec, ← hcoord, p13e7_polarV_coord_coord]
  have hsum : (∑ i, (Pi.single 0 (1 : ZMod 3) : Fin 7 → ZMod 3) i * v i) = v 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h0
      simp at h0
  rw [hsum]
  constructor
  · intro h
    exact zmod3_two_mul_eq_zero (v 0) h
  · intro h
    rw [h]
    ring

section E7


variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem p13e7Hyp_neg (ψ : V) : p13e7Hyp K (-ψ) = p13e7Hyp K ψ := by
  have h : p13e7HypVec (-ψ) = p13e7HypVec ψ := by
    ext v
    rw [mem_p13e7HypVec, mem_p13e7HypVec]
    have hneg : polarV (-ψ) (p13e7Coord v) = -polarV ψ (p13e7Coord v) := by
      simp only [polarV, Pi.neg_apply]
      ring
    rw [hneg, neg_eq_zero]
  rw [p13e7Hyp, p13e7Hyp, h]

omit [Finite K] in
private theorem p13e7Aux_hyp_le_range (ψ : V) :
    p13e7Hyp K ψ ≤ (tE K frameE7).range := by
  intro x hx
  rw [p13e7Hyp] at hx
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨a, rfl⟩

omit [Finite K] in
private theorem p13e7Aux_range_comm :
    ∀ x ∈ (tE K frameE7).range, ∀ y ∈ (tE K frameE7).range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

omit [Finite K] in
private theorem p13e7Aux_tE_split (v : Fin 7 → ZMod 3) :
    tE K frameE7 (Multiplicative.ofAdd v) =
      tE K frameE7 (Multiplicative.ofAdd (v - Pi.single 0 (v 0))) *
        tGen K frameE7 0 ^ (v 0).val := by
  have hv : v = (v - Pi.single 0 (v 0)) + Pi.single 0 (v 0) := by
    funext i
    simp
  conv_lhs => rw [hv]
  rw [ofAdd_add, map_mul, tE_single, tC_apply]
  rfl

omit [Finite K] in
private theorem p13e7Aux_tGen_mem_range :
    tGen K frameE7 0 ∈ (tE K frameE7).range := by
  have h : tGen K frameE7 0 = tE K frameE7 (Multiplicative.ofAdd (Pi.single 0 1)) := by
    rw [← tC_one, ← tE_single]
  rw [h]
  exact ⟨_, rfl⟩

omit
  [Finite K] [CharP K 2] in
private theorem p13e7Aux_tGen_mem_rho :
    tGen K frameE7 0 ∈ (rho K frameE7 0).range := by
  rw [tGen]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

omit [Finite K] in
private theorem p13e7Aux_tGen_mem_inf :
    tGen K frameE7 0 ∈ (tE K frameE7).range ⊓ (rho K frameE7 0).range :=
  Subgroup.mem_inf.mpr ⟨p13e7Aux_tGen_mem_range, p13e7Aux_tGen_mem_rho⟩

omit [Finite K] in
private theorem p13e7Aux_frame_le_torus :
    p13e7Hyp K (redV (frameE7.root 0)) ≤ (tE K frameE7).range :=
  p13e7Aux_hyp_le_range _

omit [Finite K] in
private theorem p13e7Aux_tE_mem_hyp (v : Fin 7 → ZMod 3) (hv : v 0 = 0) :
    tE K frameE7 (Multiplicative.ofAdd v) ∈ p13e7Hyp K (redV (frameE7.root 0)) := by
  rw [p13e7Hyp]
  exact Subgroup.mem_map.mpr ⟨Multiplicative.ofAdd v, (mem_p13e7HypVec_frame).mpr hv, rfl⟩

omit [Finite K] in
theorem p13e7_commute_rho_of_mem_hyp_frame {f : adjointGroup .E7 K}
    (hf : f ∈ p13e7Hyp K (redV (frameE7.root 0))) (A : SL2 K) :
    Commute f (TableBExcTwo.rho K frameE7 0 A) := by
  classical
  rw [p13e7Hyp] at hf
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hf
  let v : Fin 7 → ZMod 3 := a.toAdd
  have hv : v 0 = 0 := by
    have h := (mem_p13e7HypVec_frame).mp ha
    change (Multiplicative.toAdd a) 0 = 0 at h
    exact h
  have ha' : a = Multiplicative.ofAdd v := (ofAdd_toAdd a).symm
  let φ : (i : Fin 7) → Multiplicative (ZMod 3) →* adjointGroup .E7 K :=
    fun i => if i = 0 then 1 else tC K frameE7 i
  have hφ : ∀ i x, Commute (TableBExcTwo.rho K frameE7 0 A) (φ i x) := by
    intro i x
    by_cases hi : i = 0
    · subst hi
      simp [φ]
    · simp only [φ, if_neg hi]
      rw [tC_apply_rho]
      exact commute_rho frameE7 (Ne.symm hi) A _
  have hcommφ : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    by_cases hi : i = 0
    · subst hi
      simp [φ]
    · by_cases hj : j = 0
      · subst hj
        simp [φ]
      · simp only [φ, if_neg hi, if_neg hj]
        exact tC_commute frameE7 hij x y
  have hval : MonoidHom.noncommPiCoprod φ hcommφ
        (fun j => Multiplicative.ofAdd (v j)) =
      tD K frameE7 (fun j => Multiplicative.ofAdd (v j)) := by
    rw [tD, MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply]
    refine Finset.noncommProd_congr rfl ?_ _
    intro i _
    by_cases hi : i = 0
    · subst hi
      simp [φ, hv]
    · simp only [φ, if_neg hi]
  have hmain := MonoidHom.commute_noncommPiCoprod (ϕ := φ) (hcomm := hcommφ)
    (m := TableBExcTwo.rho K frameE7 0 A) hφ (fun j => Multiplicative.ofAdd (v j))
  rw [ha', tE_apply, ← hval]
  exact hmain.symm

theorem p13e7_centralizer_hyp_of_not_root (hK : Nat.card K = 2) {ψ : V} (hψ : ψ ≠ 0)
    (hroot : ∀ β, IsRoot Tag.E7 β → redV β ≠ ψ ∧ redV β ≠ -ψ) :
    Subgroup.centralizer (p13e7Hyp K ψ : Set (adjointGroup .E7 K)) = (tE K frameE7).range := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have h3 := three_dvd_natCard_ext_sub_one hK
  obtain ⟨ω, hω⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hV : Nat.card (torusPow .E7 L 3) = 3 ^ Tag.E7.rank :=
    card_torusPow_E7 (K := L) Nat.prime_three h3
  have hpow : ∀ a : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 a ^ 3 = 1 := fun a => by
    rw [ExcSplitL.rootDiagUnit_pow', show a ^ 3 = 1 from funext fun i => units_pow_three hK (a i),
      rootDiagUnit_one]
  set G := langElt frameE7 hω with hG
  set ι := adjointMap .E7 (algebraMap K L) with hι
  set T := (tE K frameE7).range with hT
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow .E7 L 3 :=
    langElt_conj_frame_eq_torusPow (Or.inl rfl) frameE7 rfl hV hω
  refine le_antisymm ?_ ?_
  · intro c hc
    set x : adjointGroup .E7 L := G⁻¹ * ι c * G with hx
    have hxmem : x ∈ LayerSixE.famCentralizer (p13e7Fam ω hω3 ψ) := by
      rw [hx]
      exact p13e7_mem_famCentralizer hω hω3 hc
    have hcomm : ∀ a ∈ p13e7Fam ω hω3 ψ,
        (x : ModGL .E7 L) * rootDiagUnit .E7 a =
          rootDiagUnit .E7 a * (x : ModGL .E7 L) := by
      intro a ha
      have h := (LayerSixE.mem_famCentralizer.mp hxmem) a ha
      have h' : rootDiagUnit .E7 a * (x : ModGL .E7 L) =
          (x : ModGL .E7 L) * rootDiagUnit .E7 a := by
        calc rootDiagUnit .E7 a * (x : ModGL .E7 L)
            = (rootDiagUnit .E7 a * (x : ModGL .E7 L) *
                (rootDiagUnit .E7 a)⁻¹) * rootDiagUnit .E7 a := by group
          _ = (x : ModGL .E7 L) * rootDiagUnit .E7 a := by rw [h]
      exact h'.symm
    have hker0 : famKernel (p13e7Fam ω hω3 ψ) = ∅ := by
      rw [p13e7_famKernel hω hω3 hψ]
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hα, h | h⟩
      · exact (hroot α hα).1 h
      · exact (hroot α hα).2 h
    have hstab : famStabilizer (p13e7Fam ω hω3 ψ) ⊆
        (Subgroup.closure {s | ∃ α ∈ famKernel (p13e7Fam ω hω3 ψ),
          s = rootReflection α} : Set (WeylGroup Tag.E7)) := by
      intro w hw
      rw [p13e7_famStabilizer hω hω3 ψ] at hw
      rcases p13a3_E7_pointwise_stabilizer ψ hψ w hw with h1 | ⟨β, hβ, hβψ, rfl⟩
      · rw [h1]
        exact Subgroup.one_mem _
      · exfalso
        rcases hβψ with h | h
        · exact (hroot β hβ).1 h
        · exact (hroot β hβ).2 h
    have hxmul : (x : ModGL .E7 L) ∈
        (torusGroup .E7 L : Set (ModGL .E7 L)) *
          (rootSpan .E7 L (∅ : Set (Fin Tag.E7.rank → ℤ)) : Set (ModGL .E7 L)) :=
      mem_torus_mul_rootSpan_of_commute_fam (F := p13e7Fam ω hω3 ψ) hstab
        (S := (∅ : Set (Fin Tag.E7.rank → ℤ))) (by simp) (by simp)
        (by rw [hker0]) x.2 hcomm
    rw [show rootSpan .E7 L (∅ : Set (Fin Tag.E7.rank → ℤ)) = ⊥ by simp [rootSpan]] at hxmul
    obtain ⟨h, hh, r, hr, hxr⟩ := Set.mem_mul.mp hxmul
    have hr1 : r = 1 := by simpa using hr
    subst r
    have hxT : (x : ModGL .E7 L) ∈ torusGroup .E7 L := by
      rw [← hxr]
      exact Subgroup.mul_mem _ hh (Subgroup.one_mem _)
    have hxV : x ∈ torusPow .E7 L 3 := by
      refine ⟨hxT, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
      rw [hb]
      exact hpow b
    rw [← hTV] at hxV
    obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hxV
    have hxt' : G⁻¹ * ι t * G = x := by
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxt
    have hιt : ι t = ι c := by
      have h1 : G * x * G⁻¹ = ι t := by
        rw [← hxt']
        group
      have h2 : G * x * G⁻¹ = ι c := by
        rw [hx]
        group
      exact h1.symm.trans h2
    have htc : t = c := adjointMap_injective (algebraMap K L) hιt
    rw [← htc]
    exact ht
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact p13e7Aux_range_comm y (p13e7Aux_hyp_le_range ψ hy) x hx

theorem p13e7_centralizer_hyp_frame (hK : Nat.card K = 2) :
    Subgroup.centralizer (p13e7Hyp K (redV (frameE7.root 0)) : Set (adjointGroup .E7 K)) =
      p13e7Hyp K (redV (frameE7.root 0)) ⊔ (TableBExcTwo.rho K frameE7 0).range := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have h3 := three_dvd_natCard_ext_sub_one hK
  obtain ⟨ω, hω⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hV : Nat.card (torusPow .E7 L 3) = 3 ^ Tag.E7.rank :=
    card_torusPow_E7 (K := L) Nat.prime_three h3
  have hpow : ∀ a : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 a ^ 3 = 1 := fun a => by
    rw [ExcSplitL.rootDiagUnit_pow', show a ^ 3 = 1 from funext fun i => units_pow_three hK (a i),
      rootDiagUnit_one]
  set G := langElt frameE7 hω with hG
  set ι := adjointMap .E7 (algebraMap K L) with hι
  set T := (tE K frameE7).range with hT
  set θ : V := redV (frameE7.root 0) with hθ
  have hθ0 : θ ≠ 0 := p13a2_E7_redV_ne_zero (frameE7.root 0) (frameE7.isRoot 0)
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow .E7 L 3 :=
    langElt_conj_frame_eq_torusPow (Or.inl rfl) frameE7 rfl hV hω
  have hredVneg : ∀ α : Fin Tag.E7.rank → ℤ, redV (-α) = -redV α := by
    intro α
    have h := redV_sub (0 : Fin Tag.E7.rank → ℤ) α
    have h0 : redV (0 : Fin Tag.E7.rank → ℤ) = 0 := by
      funext i
      rfl
    rw [h0, zero_sub] at h
    exact h
  have hfam_eq : famKernel (p13e7Fam ω hω3 θ) = {frameE7.root 0, -frameE7.root 0} := by
    ext α
    rw [p13e7_famKernel hω hω3 hθ0]
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hα, h | h⟩
      · left
        exact redV_injOn_roots hα (frameE7.isRoot 0) h
      · right
        refine redV_injOn_roots hα (IsRoot.neg (frameE7.isRoot 0)) ?_
        rw [hredVneg, h]
    · rintro (rfl | rfl)
      · exact ⟨frameE7.isRoot 0, Or.inl rfl⟩
      · exact ⟨IsRoot.neg (frameE7.isRoot 0), Or.inr (by rw [hredVneg])⟩
  have hrootmem : ∀ {β : Fin Tag.E7.rank → ℤ}, IsRoot Tag.E7 β →
      (redV β = θ ∨ redV β = -θ) → β ∈ famKernel (p13e7Fam ω hω3 θ) := by
    intro β hβ hβθ
    rw [p13e7_famKernel hω hω3 hθ0]
    exact ⟨hβ, hβθ⟩
  refine le_antisymm ?_ ?_
  · intro c hc
    set x : adjointGroup .E7 L := G⁻¹ * ι c * G with hx
    have hxmem : x ∈ LayerSixE.famCentralizer (p13e7Fam ω hω3 θ) := by
      rw [hx]
      exact p13e7_mem_famCentralizer hω hω3 hc
    have hcomm : ∀ a ∈ p13e7Fam ω hω3 θ,
        (x : ModGL .E7 L) * rootDiagUnit .E7 a =
          rootDiagUnit .E7 a * (x : ModGL .E7 L) := by
      intro a ha
      have h := (LayerSixE.mem_famCentralizer.mp hxmem) a ha
      have h' : rootDiagUnit .E7 a * (x : ModGL .E7 L) =
          (x : ModGL .E7 L) * rootDiagUnit .E7 a := by
        calc rootDiagUnit .E7 a * (x : ModGL .E7 L)
            = (rootDiagUnit .E7 a * (x : ModGL .E7 L) *
                (rootDiagUnit .E7 a)⁻¹) * rootDiagUnit .E7 a := by group
          _ = (x : ModGL .E7 L) * rootDiagUnit .E7 a := by rw [h]
      exact h'.symm
    have hstab : famStabilizer (p13e7Fam ω hω3 θ) ⊆
        (Subgroup.closure {s | ∃ α ∈ famKernel (p13e7Fam ω hω3 θ),
          s = rootReflection α} : Set (WeylGroup Tag.E7)) := by
      intro w hw
      rw [p13e7_famStabilizer hω hω3 θ] at hw
      rcases p13a3_E7_pointwise_stabilizer θ hθ0 w hw with h1 | ⟨β, hβ, hβθ, rfl⟩
      · rw [h1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨β, hrootmem hβ hβθ, rfl⟩
    have hS : ∀ α ∈ famKernel (p13e7Fam ω hω3 θ), IsRoot Tag.E7 α := by
      intro α hα
      rw [p13e7_famKernel hω hω3 hθ0] at hα
      exact hα.1
    have hSn : ∀ α ∈ famKernel (p13e7Fam ω hω3 θ),
        -α ∈ famKernel (p13e7Fam ω hω3 θ) := by
      intro α hα
      rw [p13e7_famKernel hω hω3 hθ0] at hα
      exact hrootmem (IsRoot.neg hα.1) (by
        rcases hα.2 with h | h
        · right
          rw [hredVneg, h]
        · left
          rw [hredVneg, h, neg_neg])
    have hxmul : (x : ModGL .E7 L) ∈
        (torusGroup .E7 L : Set (ModGL .E7 L)) *
          (rootSpan .E7 L (famKernel (p13e7Fam ω hω3 θ)) : Set (ModGL .E7 L)) :=
      mem_torus_mul_rootSpan_of_commute_fam (F := p13e7Fam ω hω3 θ) hstab
        (S := famKernel (p13e7Fam ω hω3 θ)) hS hSn subset_rfl x.2 hcomm
    rw [hfam_eq] at hxmul
    obtain ⟨h, hh, r, hr, hxr⟩ := Set.mem_mul.mp hxmul
    have hr_range : r ∈ (rootSL2 .E7 L (frameE7.root 0)).range := by
      rw [rootSpan, iSup_insert, iSup_singleton] at hr
      rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (frameE7.isRoot 0)]
      exact hr
    have hrS : r ∈ rootSpan .E7 L {frameE7.root 0, -frameE7.root 0} := by
      rw [rootSpan, iSup_insert, iSup_singleton,
        ← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (frameE7.isRoot 0)]
      exact hr_range
    obtain ⟨A, hA⟩ := hr_range
    let R0 : adjointGroup .E7 L :=
      ⟨r, CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ hrS⟩
    have hRrho : R0 = rho L frameE7 0 A := Subtype.ext (by rw [coe_rho, hA])
    let H0 : adjointGroup .E7 L := ⟨h, torusGroup_le_adjointGroup hh⟩
    have hhpow : h ^ 3 = 1 := by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [hb, ExcSplitL.rootDiagUnit_pow',
        show b ^ 3 = 1 from funext fun i => units_pow_three hK (b i), rootDiagUnit_one]
    have hHpow : H0 ∈ torusPow .E7 L 3 := by
      refine ⟨hh, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa [H0] using hhpow
    rw [← hTV] at hHpow
    obtain ⟨_, ⟨t, ht, rfl⟩, hHt⟩ := hHpow
    have hHt' : G⁻¹ * ι t * G = H0 := by
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hHt
    obtain ⟨a, -, rfl⟩ := ht
    let v : Fin 7 → ZMod 3 := a.toAdd
    have ha : a = Multiplicative.ofAdd v := (ofAdd_toAdd a).symm
    let f : adjointGroup .E7 K :=
      tE K frameE7 (Multiplicative.ofAdd (v - Pi.single 0 (v 0)))
    let s : adjointGroup .E7 K := tGen K frameE7 0 ^ (v 0).val
    have ht_split : tE K frameE7 a = f * s := by
      rw [ha, p13e7Aux_tE_split]
    have hfF : f ∈ p13e7Hyp K θ := by
      rw [hθ]
      exact p13e7Aux_tE_mem_hyp _ (by simp)
    have hsT : s ∈ T := by
      rw [hT]
      exact Subgroup.pow_mem _ p13e7Aux_tGen_mem_range _
    have hsR : s ∈ (rho K frameE7 0).range := by
      dsimp [s]
      exact Subgroup.pow_mem _ p13e7Aux_tGen_mem_rho _
    have hHsplit : H0 = (G⁻¹ * ι f * G) * (G⁻¹ * ι s * G) := by
      rw [← hHt', ht_split, map_mul]
      group
    have hxHR : x = H0 * R0 := Subtype.ext (by
      calc (x : ModGL .E7 L) = h * r := hxr.symm
        _ = (H0 : ModGL .E7 L) * (R0 : ModGL .E7 L) := rfl
        _ = ((H0 * R0 : adjointGroup .E7 L) : ModGL .E7 L) :=
            (Subgroup.coe_mul _ _ _).symm)
    have hgen : ι (tGen K frameE7 0) = G * rho L frameE7 0 (HSL ω) * G⁻¹ := by
      rw [hι, hG]
      exact (ExcFrameIso.langElt_conj_rho_HSL frameE7 hω 0).symm
    have hS1 : G⁻¹ * ι s * G = rho L frameE7 0 ((HSL ω) ^ (v 0).val) := by
      dsimp [s]
      rw [map_pow, hgen]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      have hconj : ((G : ModGL .E7 L) * (rho L frameE7 0 (HSL ω) : ModGL .E7 L) *
          (G : ModGL .E7 L)⁻¹) ^ (v 0).val =
          (G : ModGL .E7 L) * (rho L frameE7 0 (HSL ω) : ModGL .E7 L) ^ (v 0).val *
          (G : ModGL .E7 L)⁻¹ := conj_pow
      have hpow : (rho L frameE7 0 ((HSL ω) ^ (v 0).val) : ModGL .E7 L) =
          (rho L frameE7 0 (HSL ω) : ModGL .E7 L) ^ (v 0).val := by
        simp
      rw [hconj, hpow]
      group
    set P : SL2 L := langP (sq_add_self_add_one_eq_zero hω) with hP
    have hGP : G = frameProd L frameE7 P := by
      rw [hG, hP, langElt]
    set B' : SL2 L := (HSL ω) ^ (v 0).val * A with hB'
    set B : SL2 L := P * B' * P⁻¹ with hB
    have hx_eq : x = G⁻¹ * ι f * G * rho L frameE7 0 B' := by
      calc x = H0 * R0 := hxHR
        _ = ((G⁻¹ * ι f * G) * (G⁻¹ * ι s * G)) * R0 := by rw [hHsplit]
        _ = ((G⁻¹ * ι f * G) * rho L frameE7 0 ((HSL ω) ^ (v 0).val)) *
              rho L frameE7 0 A := by rw [hS1, hRrho]
        _ = (G⁻¹ * ι f * G) * (rho L frameE7 0 ((HSL ω) ^ (v 0).val) *
              rho L frameE7 0 A) := by group
        _ = (G⁻¹ * ι f * G) * rho L frameE7 0 ((HSL ω) ^ (v 0).val * A) := by
              rw [← (rho L frameE7 0).map_mul]
        _ = (G⁻¹ * ι f * G) * rho L frameE7 0 B' := by
              rw [hB']
    have hιc_eq : ι c = ι f * rho L frameE7 0 B := by
      have h1 : ι c = G * x * G⁻¹ := by
        rw [hx]
        group
      rw [h1, hx_eq]
      calc G * ((G⁻¹ * ι f * G) * rho L frameE7 0 B') * G⁻¹
          = ι f * (G * rho L frameE7 0 B' * G⁻¹) := by group
        _ = ι f * rho L frameE7 0 B := by
              have hfgp : G * rho L frameE7 0 B' * G⁻¹ = rho L frameE7 0 B := by
                rw [hGP, hB]
                exact ExcFrameIso.frameProd_conj_rho frameE7 0 P B'
              rw [hfgp]
    have hιfc : ι (f⁻¹ * c) = rho L frameE7 0 B := by
      rw [map_mul, map_inv, hιc_eq]
      group
    have hfixfield : ∀ z : L, frobHom K z = z ↔ z ∈ Set.range (algebraMap K L) := by
      intro z
      rw [frobHom_apply]
      exact CFSG.SeitzReduction.F4Pilot.frob_eq_self_iff z
    have hfix : adjointMap .E7 (frobHom K) (ι (f⁻¹ * c)) = ι (f⁻¹ * c) := by
      apply Subtype.ext
      calc (adjointMap .E7 (frobHom K) (ι (f⁻¹ * c)) : ModGL .E7 L)
          = baseChangeGL (frobHom K) (ι (f⁻¹ * c) : ModGL .E7 L) := coe_adjointMap _ _
        _ = baseChangeGL (frobHom K)
              (baseChangeGL (algebraMap K L)
                ((f⁻¹ * c : adjointGroup .E7 K) : ModGL .E7 K)) := by
              rw [coe_adjointMap]
        _ = CFSG.LieType.Chevalley.baseChangeGL ((frobHom K).comp (algebraMap K L))
              ((f⁻¹ * c : adjointGroup .E7 K) : ModGL .E7 K) :=
              CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL (f := algebraMap K L)
                (f' := frobHom K) _
        _ = baseChangeGL (algebraMap K L)
              ((f⁻¹ * c : adjointGroup .E7 K) : ModGL .E7 K) := by
              rw [frobHom_comp_algebraMap]
        _ = (ι (f⁻¹ * c) : ModGL .E7 L) := (coe_adjointMap _ _).symm
    have hfixB : adjointMap .E7 (frobHom K) (rho L frameE7 0 B) = rho L frameE7 0 B := by
      rw [← hιfc]
      exact hfix
    have hBmap : Matrix.SpecialLinearGroup.map (frobHom K) B = B := by
      apply rho_injective frameE7 0
      have h := hfixB
      rwa [adjointMap_rho] at h
    obtain ⟨B₀, hB₀⟩ := CFSG.SeitzReduction.F4Pilot.exists_map_eq_of_map_eq
      (algebraMap K L) (frobHom K) hfixfield B hBmap
    have hfc : f⁻¹ * c = rho K frameE7 0 B₀ := by
      apply adjointMap_injective (algebraMap K L)
      rw [hιfc, adjointMap_rho, hB₀]
    have hc_eq : c = f * rho K frameE7 0 B₀ := by
      calc c = f * (f⁻¹ * c) := by group
        _ = f * rho K frameE7 0 B₀ := by rw [hfc]
    rw [hc_eq]
    exact Subgroup.mul_mem_sup hfF (MonoidHom.mem_range.mpr ⟨B₀, rfl⟩)
  · refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact p13e7Aux_range_comm y (p13e7Aux_frame_le_torus hy) x
        (p13e7Aux_frame_le_torus hx)
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (p13e7_commute_rho_of_mem_hyp_frame hy A).eq

theorem p13e7_case_frame (hK : Nat.card K = 2) :
    P13aCase (adjointGroup .E7 K) (tE K frameE7).range (p13e7Hyp K (redV (frameE7.root 0))) := by
  classical
  set θ : V := redV (frameE7.root 0) with hθ
  have hθ0 : θ ≠ 0 := p13a2_E7_redV_ne_zero (frameE7.root 0) (frameE7.isRoot 0)
  refine Or.inr ⟨(rho K frameE7 0).range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_card_two hK
    exact ⟨(MonoidHom.ofInjective (rho_injective frameE7 0)).symm.trans e⟩
  · intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hr
    exact (p13e7_commute_rho_of_mem_hyp_frame hf A).symm.eq
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxR⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hxR
    have hcenter : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply rho_injective frameE7 0
      rw [map_mul, map_mul]
      exact (p13e7_commute_rho_of_mem_hyp_frame hxF B).symm.eq
    rw [center_specialLinear_two_eq_bot K,
      Subgroup.mem_bot] at hcenter
    rw [hcenter, map_one]
    exact Subgroup.one_mem _
  · exact p13e7_centralizer_hyp_frame hK
  ·
    apply le_antisymm
    · intro t ht
      obtain ⟨a, -, rfl⟩ := ht
      rw [show a = Multiplicative.ofAdd a.toAdd from (ofAdd_toAdd a).symm, p13e7Aux_tE_split]
      refine Subgroup.mul_mem_sup ?_ ?_
      · rw [hθ]
        exact p13e7Aux_tE_mem_hyp _ (by simp)
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.pow_mem _ p13e7Aux_tGen_mem_range _
        · exact Subgroup.pow_mem _ p13e7Aux_tGen_mem_rho _
    · refine sup_le (p13e7Aux_hyp_le_range θ) ?_
      exact inf_le_left
  ·
    have hTcard : Nat.card ↥(tE K frameE7).range = 3 ^ 7 := by
      calc Nat.card ↥(tE K frameE7).range =
            Nat.card (Multiplicative (Fin 7 → ZMod 3)) :=
            Nat.card_congr (Equiv.ofInjective (tE K frameE7) (tE_injective frameE7)).symm
        _ = Nat.card (Fin 7 → ZMod 3) := Nat.card_congr Multiplicative.toAdd
        _ = 3 ^ 7 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hRcard : Nat.card ↥(rho K frameE7 0).range = 6 := by
      obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_card_two hK
      have h1 : Nat.card ↥(rho K frameE7 0).range =
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
        Nat.card_congr (MonoidHom.ofInjective (rho_injective frameE7 0)).toEquiv.symm
      rw [h1, Nat.card_congr e.toEquiv, Nat.card_perm]
      norm_num
    have hdvd6 : Nat.card ↥((tE K frameE7).range ⊓ (rho K frameE7 0).range) ∣ 6 := by
      have h := Subgroup.card_dvd_of_le (H := (tE K frameE7).range ⊓ (rho K frameE7 0).range)
        (K := (rho K frameE7 0).range) inf_le_right
      rwa [hRcard] at h
    have hdvd37 : Nat.card ↥((tE K frameE7).range ⊓ (rho K frameE7 0).range) ∣ 3 ^ 7 := by
      have h := Subgroup.card_dvd_of_le (H := (tE K frameE7).range ⊓ (rho K frameE7 0).range)
        (K := (tE K frameE7).range) inf_le_left
      rwa [hTcard] at h
    have hdvd3 : Nat.card ↥((tE K frameE7).range ⊓ (rho K frameE7 0).range) ∣ 3 := by
      have h37 : (3 : ℕ) ^ 7 = 3 * 3 ^ 6 := by norm_num
      rw [h37] at hdvd37
      have hg : Nat.card ↥((tE K frameE7).range ⊓ (rho K frameE7 0).range) ∣
          Nat.gcd 6 (3 * 3 ^ 6) := Nat.dvd_gcd hdvd6 hdvd37
      simpa using hg
    have h3dvd : 3 ∣ Nat.card ↥((tE K frameE7).range ⊓ (rho K frameE7 0).range) := by
      have h : orderOf (tGen K frameE7 0) = 3 :=
        orderOf_eq_prime (tGen_pow_three frameE7 0) (tGen_ne_one frameE7 0)
      have hmem := Subgroup.orderOf_dvd_natCard
        ((tE K frameE7).range ⊓ (rho K frameE7 0).range)
        (p13e7Aux_tGen_mem_inf (K := K))
      rwa [h] at hmem
    exact Nat.dvd_antisymm hdvd3 h3dvd

end E7

end CFSG.StandardType.FrameRoute
