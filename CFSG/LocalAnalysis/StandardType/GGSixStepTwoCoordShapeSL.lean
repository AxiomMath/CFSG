module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSLBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane
open scoped commutatorElement

namespace CFSG.StandardType

namespace CoordSL

open Multiplicative CoordShape

section Setup

variable {G : Type} [Group G] {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [NeZero p] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}

theorem centralizer_eq_map_joint
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hnsplit : ∀ c : K, c ^ p = 1 → c = 1) {E : Subgroup G}
    (hE : E ≤ (frameHom ψ A₀ ε hC hCp).range) :
    ψ.range ⊓ Subgroup.centralizer (E : Set G) =
      (Subgroup.centralizer {Y | ∃ t : Fin s → ZMod p, frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ E ∧
        Y = SLNS.nsSL ε hC (fun i => (t i).val)}).map (SLRep.ggFrame ψ A₀) := by
  rw [← SLRep.range_ggFrame ψ A₀]
  ext x
  constructor
  · rintro ⟨⟨h, rfl⟩, hc⟩
    refine ⟨h, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ ht
    rw [frameHom_eq_ggFrame] at h1
    exact SLNS.commute_nsSL_of_map_commute ε hC (SLRep.ker_ggFrame_le hker A₀) hnsplit hCp _ h1
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨a, rfl⟩ := hE he
    have h1 := Subgroup.mem_centralizer_iff.mp hh _ ⟨toAdd a, he, rfl⟩
    change SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC fun i => (toAdd a i).val) *
        SLRep.ggFrame ψ A₀ h = SLRep.ggFrame ψ A₀ h *
          SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC fun i => (toAdd a i).val)
    rw [← map_mul, ← map_mul, h1]

end Setup

section Aligned

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

theorem coordShape_of_jointAligned (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) {hζ : AdjoinRoot.root g ^ p = 1} (hs : 4 ≤ s) {E J : Subgroup G}
    (hE : E ≤ (frameHom ψ A₀ ε hC hCp).range)
    (hal : JointAligned (galExp g hζ) {t | frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ E})
    (hcomp : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (J : Set G) :
      Subgroup G) ≤ p ^ 3) :
    StepTwoToral.GGStepTwoCoordShape p s (galExp g hζ) (frameHom ψ A₀ ε hC hCp) E := by
  classical
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim := root_isPrimitiveRoot hp hpK' hgd
  have hinj : Function.Injective (frameHom ψ A₀ ε hC hCp) :=
    frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp hpK hpK' hgd)
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc => OrdPNS.eq_one_of_pow_eq_one hp hpK hc
  rw [centralizer_eq_map_joint hker hnsplit hE] at hcomp
  set ι := frameHom ψ A₀ ε hC hCp with hιdef
  set T : Set (Fin s → ZMod p) := {t | ι (ofAdd t) ∈ E} with hTdef
  have hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T :=
    fun t ht t₀ ht₀ a => sub_smul_mem ht ht₀ a
  set φ := SLRep.ggFrame ψ A₀ with hφdef
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    SLRep.ker_ggFrame_le hker A₀
  set C₀ := Subgroup.centralizer {Y | ∃ t : Fin s → ZMod p, ι (ofAdd t) ∈ E ∧
    Y = SLNS.nsSL ε hC (fun i => (t i).val)} with hC₀
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ ∀ t ∈ T, u * SLNS.nsSL ε hC (fun i => (t i).val) =
      SLNS.nsSL ε hC (fun i => (t i).val) * u := by
    intro u
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      exact (h _ ⟨t, ht, rfl⟩).symm
    · rintro h _ ⟨t, ht, rfl⟩
      exact (h t ht).symm
  set KZ := coordBlockSL K (zeroCoords ε (jointSupp T)) with hKZ
  set KC : Fin s → Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := fun j =>
    (coordBlockSL (AdjoinRoot g) (classSet (jointClass T j) 1)).map (theta g ε) with hKC
  have halZ : Aligned hζ (jointSupp T) := aligned_of_zero_one jointSupp_zero_or_one
  have hKZC : KZ ≤ C₀ := fun M hM => (hmemC₀ M).mpr fun t ht =>
    (comm_zeroBlock_of_torus (k := fun i => (t i).val) (fun i hi => by
      rw [jointSupp_eq_zero_iff.mp hi t ht, ZMod.val_zero]) hM).symm
  have hKCC : ∀ j, KC j ≤ C₀ := by
    rintro j _ ⟨M, hM, rfl⟩
    refine (hmemC₀ _).mpr fun t ht => comm_classBlock_of_torus (fun i i' hi hi' => ?_) hM
    rw [jointClass_eq_one_iff.mp hi t ht, jointClass_eq_one_iff.mp hi' t ht]
  have hKZn : ((KZ.map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    have huZ := comm_nsSL_of_joint hprim hT hal ((hmemC₀ u).mp hu)
      (fun i hi => jointSupp_eq_zero_iff.mpr hi) (fun i j hij => jointSupp_eq_of hij)
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim halZ huZ hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ j, (∃ t ∈ T, t j ≠ 0) → (((KC j).map φ).subgroupOf (C₀.map φ)).Normal := by
    rintro j ⟨t₀, ht₀, hj⟩
    have halX : Aligned hζ (jointClass T j) := aligned_of_zero_one (jointClass_zero_or_one j)
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC j))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    have huX := comm_nsSL_of_joint hprim hT hal ((hmemC₀ u).mp hu) (β := jointClass T j)
      (fun k hk => jointClass_eq_zero_of_zero ht₀ hj hk) (fun k l hkl => jointClass_eq_of hkl)
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim halX one_ne_zero huX hM
    exact ⟨theta g ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hcJ : ∀ (N : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) (t : Fin s → ZMod p),
      J ≤ N.map φ → (∀ M ∈ N, SLNS.nsSL ε hC (fun i => (t i).val) * M =
        M * SLNS.nsSL ε hC (fun i => (t i).val)) →
      ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) := by
    intro N t hJN hcomm
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨M, hM, rfl⟩ := hJN hx
    rw [hιdef, frameHom_eq_ggFrame, ← map_mul, ← map_mul, hcomm M hM]
  have hlt : ¬ p ^ 4 ≤ p ^ 3 := not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  have hq := hcomp.2.2
  by_cases hZ : J ≤ KZ.map φ
  ·
    left
    by_contra hno
    push Not at hno
    have hall : ∀ t : Fin s → ZMod p, ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) :=
      fun t => hcJ KZ t hZ fun M hM => comm_zeroBlock_of_torus (fun i hi => by
        obtain ⟨t', ht', hi'⟩ := hno i
        exact absurd (jointSupp_eq_zero_iff.mp hi t' ht') hi') hM
    have hle := pow_four_le_of_dual hinj (H := ι.range ⊓ Subgroup.centralizer (J : Set G))
      (fun a => Pi.single (Fin.castLE hs a) 1) (Fin.castLE hs) (fun a b => by
        simp only [Pi.single_apply, (Fin.castLE_injective hs).eq_iff]
        by_cases hab : a = b
        · simp [hab]
        · simp [hab, Ne.symm hab]) fun x => hall _
    exact hlt (hle.trans hcard)
  · by_cases hCex : ∃ j₀, (∃ t ∈ T, t j₀ ≠ 0) ∧ J ≤ (KC j₀).map φ
    ·
      right
      obtain ⟨j₀, -, hJC⟩ := hCex
      set X := classSet (jointClass T j₀) 1 with hX
      have hmemX : ∀ i, i ∈ X ↔ ∀ t ∈ T, t i = t j₀ := fun i =>
        mem_classSet.trans jointClass_eq_one_iff
      have hj₀X : j₀ ∈ X := (hmemX j₀).mpr fun _ _ => rfl
      have hcX : ∀ t : Fin s → ZMod p, (∀ i i', i ∈ X → i' ∈ X → t i = t i') →
          ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) := by
        intro t ht
        refine hcJ (KC j₀) t hJC ?_
        rintro _ ⟨M, hM, rfl⟩
        exact (comm_classBlock_of_torus (fun i i' hi hi' => by
          rw [ht i i' (mem_classSet.mpr hi) (mem_classSet.mpr hi')]) hM).symm
      have hout : ∀ k₁ k₂ k₃, k₁ ≠ k₂ → k₁ ≠ k₃ → k₂ ≠ k₃ → k₁ ∉ X → k₂ ∉ X → k₃ ∉ X →
          False := by
        intro k₁ k₂ k₃ h12 h13 h23 h1 h2 h3
        have h10 : k₁ ≠ j₀ := fun h => h1 (h ▸ hj₀X)
        have h20 : k₂ ≠ j₀ := fun h => h2 (h ▸ hj₀X)
        have h30 : k₃ ≠ j₀ := fun h => h3 (h ▸ hj₀X)
        have hle := pow_four_le_of_dual hinj (H := ι.range ⊓ Subgroup.centralizer (J : Set G))
          ![Pi.single k₁ 1, Pi.single k₂ 1, Pi.single k₃ 1, fun i => if i ∈ X then 1 else 0]
          ![k₁, k₂, k₃, j₀] (fun a b => by
            fin_cases a <;> fin_cases b <;>
              simp [h12, h13, h23, h12.symm, h13.symm, h23.symm, h10.symm, h20.symm, h30.symm, h1,
                h2, h3, hj₀X]) fun x => hcX _ fun i i' hi hi' => by
            have hi1 : i ≠ k₁ := fun h => h1 (h ▸ hi)
            have hi2 : i ≠ k₂ := fun h => h2 (h ▸ hi)
            have hi3 : i ≠ k₃ := fun h => h3 (h ▸ hi)
            have hi1' : i' ≠ k₁ := fun h => h1 (h ▸ hi')
            have hi2' : i' ≠ k₂ := fun h => h2 (h ▸ hi')
            have hi3' : i' ≠ k₃ := fun h => h3 (h ▸ hi')
            simp [Fin.sum_univ_four, hi1, hi2, hi3, hi1', hi2', hi3', hi, hi']
        exact hlt (hle.trans hcard)
      have hjj : ∃ j j' : Fin s, ∀ i, i ≠ j → i ≠ j' → i ∈ X := by
        by_cases h1 : ∃ k₁, k₁ ∉ X
        · obtain ⟨k₁, hk₁⟩ := h1
          by_cases h2 : ∃ k₂, k₂ ≠ k₁ ∧ k₂ ∉ X
          · obtain ⟨k₂, h21, hk₂⟩ := h2
            refine ⟨k₁, k₂, fun i hi1 hi2 => ?_⟩
            by_contra hi
            exact hout k₁ k₂ i (Ne.symm h21) (Ne.symm hi1) (Ne.symm hi2) hk₁ hk₂ hi
          · push Not at h2
            exact ⟨k₁, k₁, fun i hi1 _ => h2 i hi1⟩
        · push Not at h1
          exact ⟨j₀, j₀, fun i _ _ => h1 i⟩
      obtain ⟨j, j', hjj'⟩ := hjj
      refine ⟨j, j', 1, fun _ => (galExp g hζ).one_mem, fun t ht => ⟨t j₀, fun i hij hij' => ?_⟩⟩
      rw [Pi.one_apply, Units.val_one, one_mul]
      exact (hmemX i).mp (hjj' i hij hij') t ht
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅J, KZ.map φ⁆ = ⊥ :=
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC) hKZn).resolve_left hZ
      have hCb : ∀ j₀, (∃ t ∈ T, t j₀ ≠ 0) → ⁅J, (KC j₀).map φ⁆ = ⊥ := fun j₀ hj₀ =>
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC j₀))
          (hKCn j₀ hj₀)).resolve_left (hCex j₀ hj₀)
      have hcommN : ∀ {N : Subgroup G}, ⁅J, N⁆ = ⊥ → ∀ x ∈ J, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hZw : ∀ w, φ w ∈ J → ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε (jointSupp T) →
          y ∈ zeroCoords ε (jointSupp T) →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : K)
        exact commute_of_map_commute_of_mul_self hkerφ
          (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ J → ∀ i j (hij : i ≠ j), (∀ t ∈ T, t i = t j) →
          (∃ t ∈ T, t i ≠ 0) → ∀ c' : AdjoinRoot g,
          w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c') =
            theta g ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hrel hi c'
        have hiX : i ∈ classSet (jointClass T i) 1 :=
          mem_classSet.mpr (jointClass_eq_one_iff.mpr fun _ _ => rfl)
        have hjX : j ∈ classSet (jointClass T i) 1 :=
          mem_classSet.mpr (jointClass_eq_one_iff.mpr fun t ht => (hrel t ht).symm)
        have hT' := SLRep.transvection_mem_coordBlockSL hiX hjX hij c'
        have hθT : theta g ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC i :=
          ⟨_, hT', rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ (theta_transvection_mul_self ε hij c')
          (hcommN (hCb i hi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks_joint hprim hT hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

end Aligned

section General

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

theorem coordShape_of_frame (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) (hs0 : 0 < s) {E J : Subgroup G}
    (hE : E ≤ (frameHom ψ A₀ ε hC hCp).range)
    (hcomp : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)))
    (hcard : Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (J : Set G) :
      Subgroup G) ≤ p ^ 3) :
    StepTwoToral.GGStepTwoCoordShape p s (galExp g hζ) (frameHom ψ A₀ ε hC hCp) E := by
  rcases le_or_gt s 3 with hs3 | hs4
  · exact coordShape_of_le_three _ _ _ hs0 hs3
  obtain ⟨η, hηO, hal⟩ := exists_jointAligned (galExp g hζ)
    {t | frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ E}
  obtain ⟨M, hM⟩ := exists_conj_frameHom g ψ A₀ ε hC hCp hζ (Equiv.refl _) η hηO
  set w := SLRep.ggFrame ψ A₀ M with hwdef
  have hw : ∀ u : Fin s → ZMod p, frameHom ψ (A₀ * M) ε hC hCp (ofAdd u) =
      w * frameHom ψ A₀ ε hC hCp (ofAdd u) * w⁻¹ := by
    intro u
    simp only [hwdef, frameHom_apply, SLRep.ggFrame_apply, ← map_inv, ← map_mul]
    congr 1
    group
  have hι' : ∀ t : Fin s → ZMod p,
      frameHom ψ (A₀ * M) ε hC hCp (ofAdd fun i => (η i : ZMod p) * t i) =
        frameHom ψ A₀ ε hC hCp (ofAdd t) := by
    intro t
    have h := hM t
    simp only [Equiv.refl_apply] at h
    rw [hw, ← h]
    group
  have hrange : (frameHom ψ (A₀ * M) ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨ofAdd fun i => ((η i)⁻¹ : (ZMod p)ˣ) * toAdd u i, ?_⟩
      rw [← hι']
      congr 1
      apply toAdd.injective
      funext i
      simp only [toAdd_ofAdd]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (toAdd u)⟩
  refine coordShape_of_mul hηO hι' ?_
  refine coordShape_of_jointAligned hp2 hpK hker hgd (by omega) (by rw [hrange]; exact hE) ?_
    hcomp (by rw [hrange]; exact hcard)
  rw [setOf_mem_eq_image hι' E]
  exact hal

end General

end CoordSL

open CoordSL

theorem ggSLCoordCompShapeInput_holds : GGSLCoordCompShapeInput := by
  intro G _ _ F _ _ _ n p _ hp2 hpF ψ hker g _ hgd s r ε A₀ hC hCp hζ hs0 E J hE hcomp hcard
  exact coordShape_of_frame hp2 hpF hker hgd hζ hs0 hE hcomp hcard

section Model

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggSLCoordContraryInput_holds : GGSLCoordContraryInput :=
  ggSLCoordContraryInput_of_compShape ggSLCoordCompShapeInput_holds

theorem ggStepTwoCoordModelOn_PSL_holds : GGStepTwoCoordModelOn .PSL :=
  ggStepTwoCoordModelOn_PSL_of_compShape ggSLCoordCompShapeInput_holds

theorem ggStepTwoToralWitnessOn_PSL_holds : GGStepTwoToralWitnessOn .PSL :=
  ggStepTwoToralWitnessOn_PSL_of_compShape ggSLCoordCompShapeInput_holds

end Model

end CFSG.StandardType
