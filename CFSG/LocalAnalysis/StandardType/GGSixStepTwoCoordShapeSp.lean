module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSpBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary

public section

open Matrix Multiplicative CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped commutatorElement

namespace CFSG.StandardType

namespace CoordSp

open CoordShape

section Aligned

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {n p : ℕ} [Fact p.Prime]
  {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ} {hζ : ζ ^ p = 1}

theorem coordShape_of_jointAligned (hp2 : p ≠ 2) (hψ : Function.Injective ψ)
    (hζo : orderOf ζ = p) (hs : 4 ≤ n) {E J : Subgroup G} (hE : E ≤ (frameHom ψ A₀ hζ).range)
    (hal : JointAligned (signs p) {t | frameHom ψ A₀ hζ (ofAdd t) ∈ E})
    (hcomp : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G) :
      Subgroup G) ≤ p ^ 3) :
    StepTwoToral.GGStepTwoCoordShape p n (signs p) (frameHom ψ A₀ hζ) E := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (frameHom ψ A₀ hζ) := frameHom_injective ψ A₀ hζ hψ hζo
  have hφinj : Function.Injective (frameConj ψ A₀) := frameConj_injective hψ A₀
  rw [centralizer_eq_map_joint hψ A₀ hζ hE] at hcomp
  set ι := frameHom ψ A₀ hζ with hιdef
  set T : Set (Fin n → ZMod p) := {t | ι (ofAdd t) ∈ E} with hTdef
  set φ := frameConj ψ A₀ with hφdef
  set C₀ := Subgroup.centralizer {Y | ∃ t : Fin n → ZMod p, ι (ofAdd t) ∈ E ∧
    Y = torusElt ζ t} with hC₀
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ ∀ t ∈ T, WtPres t (mat n F u) := by
    intro u
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      exact (commute_torusElt_iff hζ hζo t u).mp (h _ ⟨t, ht, rfl⟩).symm
    · rintro h _ ⟨t, ht, rfl⟩
      exact ((commute_torusElt_iff hζ hζo t u).mpr (h t ht)).symm
  have hkey : ∀ u ∈ C₀, ∀ β : Fin n → ZMod p, (∀ i, (∀ t ∈ T, t i = 0) → β i = 0) →
      (∀ i j, (∀ t ∈ T, t i = t j) → β i = β j) → u * torusElt ζ β = torusElt ζ β * u :=
    fun u hu β hβ0 hβc => (commute_torusElt_iff hζ hζo β u).mpr
      (wtPres_of_joint hp2 hal ((hmemC₀ u).mp hu) hβ0 hβc)
  set KZ := suppGroup (n := n) (K := F) (planeSet (spClass (jointSupp T) 0)) with hKZ
  set KC : Fin n → Subgroup (StatedSp n F) := fun j =>
    (classHom (F := F) (spClass (jointClass T j) 1)).range with hKC
  have hKZC : KZ ≤ C₀ := fun M hM => by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact torusElt_comm_zeroBlock hζ (fun i hi => jointSupp_eq_zero_iff.mp hi t ht) hM
  have hKCC : ∀ j, KC j ≤ C₀ := by
    rintro j _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact torusElt_comm_classBlock hp2 hζ one_ne_zero (fun i i' hi hi' => by
      rw [jointClass_eq_one_iff.mp hi t ht, jointClass_eq_one_iff.mp hi' t ht])
      (wtPres_classHom _ 1 A) (classHom_mem_suppGroup _ A)
  have hKZn : ((KZ.map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_suppGroup hζ hζo (planeSet_zero_union (jointSupp T))
      (hkey u hu _ (fun i hi => jointSupp_eq_zero_iff.mpr hi) (fun i j hij => jointSupp_eq_of hij))
      hM, by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ j, (∃ t ∈ T, t j ≠ 0) → (((KC j).map φ).subgroupOf (C₀.map φ)).Normal := by
    rintro j ⟨t₀, ht₀, hj⟩
    have halX : SpAligned (jointClass T j) := spAligned_of_zero_one hp2 (jointClass_zero_or_one j)
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC j))]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_range_classHom hp2 hζ hζo halX one_ne_zero
      (hkey u hu _ (fun k hk => jointClass_eq_zero_of_zero ht₀ hj hk)
        (fun k l hkl => jointClass_eq_of hkl)) hM, by rw [map_mul, map_mul, map_inv]⟩
  have hcJ : ∀ (N : Subgroup (StatedSp n F)) (t : Fin n → ZMod p), J ≤ N.map φ →
      (∀ M ∈ N, torusElt ζ t * M = M * torusElt ζ t) →
      ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) := by
    intro N t hJN hcomm
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨M, hM, rfl⟩ := hJN hx
    rw [hιdef, frameHom_eq_frameConj, ← map_mul, ← map_mul, hcomm M hM]
  have hlt : ¬ p ^ 4 ≤ p ^ 3 := not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  have hq := hcomp.2.2
  by_cases hZ : J ≤ KZ.map φ
  ·
    left
    by_contra hno
    push Not at hno
    have hall : ∀ t : Fin n → ZMod p, ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) :=
      fun t => hcJ KZ t hZ fun M hM => torusElt_comm_zeroBlock hζ (fun i hi => by
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
      set X := spClass (jointClass T j₀) 1 with hX
      have hmemX : ∀ i, i ∈ X ↔ ∀ t ∈ T, t i = t j₀ := fun i =>
        mem_spClass.trans jointClass_eq_one_iff
      have hj₀X : j₀ ∈ X := (hmemX j₀).mpr fun _ _ => rfl
      have hcX : ∀ t : Fin n → ZMod p, (∀ i i', i ∈ X → i' ∈ X → t i = t i') →
          ι (ofAdd t) ∈ ι.range ⊓ Subgroup.centralizer (J : Set G) := by
        intro t ht
        refine hcJ (KC j₀) t hJC ?_
        rintro _ ⟨A, rfl⟩
        exact torusElt_comm_classBlock hp2 hζ one_ne_zero (fun i i' hi hi' =>
          ht i i' (mem_spClass.mpr hi) (mem_spClass.mpr hi')) (wtPres_classHom _ 1 A)
          (classHom_mem_suppGroup _ A)
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
      have hjj : ∃ j j' : Fin n, ∀ i, i ≠ j → i ≠ j' → i ∈ X := by
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
      refine ⟨j, j', 1, fun _ => (signs p).one_mem, fun t ht => ⟨t j₀, fun i hij hij' => ?_⟩⟩
      rw [Pi.one_apply, Units.val_one, one_mul]
      exact (hmemX i).mp (hjj' i hij hij') t ht
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅J, KZ.map φ⁆ = ⊥ :=
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC)
          hKZn).resolve_left hZ
      have hCb : ∀ j₀, (∃ t ∈ T, t j₀ ≠ 0) → ⁅J, (KC j₀).map φ⁆ = ⊥ := fun j₀ hj₀ =>
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC j₀))
          (hKCn j₀ hj₀)).resolve_left (hCex j₀ hj₀)
      have hcommN : ∀ {N : Subgroup G}, ⁅J, N⁆ = ⊥ → ∀ x ∈ J, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hlift : ∀ w, φ w ∈ J → (∀ M ∈ KZ, w * M = M * w) ∧
          ∀ j, (∃ t ∈ T, t j ≠ 0) → ∀ M ∈ KC j, w * M = M * w := by
        intro w hw
        refine ⟨fun M hM => hφinj ?_, fun j hj M hM => hφinj ?_⟩
        · rw [map_mul, map_mul]
          exact hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ hM)
        · rw [map_mul, map_mul]
          exact hcommN (hCb j hj) _ hw _ (Subgroup.mem_map_of_mem φ hM)
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks_joint hp2 hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hlift u hx).1 (hlift v hy).1 (hlift u hx).2 (hlift v hy).2]

end Aligned

section General

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [CharP F 2] {n p : ℕ}
  [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ} {hζ : ζ ^ p = 1}

theorem coordShape_of_frame (hp2 : p ≠ 2) (hψ : Function.Injective ψ) (hζo : orderOf ζ = p)
    (hn0 : 0 < n) {E J : Subgroup G} (hE : E ≤ (frameHom ψ A₀ hζ).range)
    (hcomp : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)))
    (hcard : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G) :
      Subgroup G) ≤ p ^ 3) :
    StepTwoToral.GGStepTwoCoordShape p n (signs p) (frameHom ψ A₀ hζ) E := by
  rcases le_or_gt n 3 with hs3 | hs4
  · exact coordShape_of_le_three _ _ _ hn0 hs3
  obtain ⟨η, hηO, hal⟩ := exists_jointAligned (signs p) {t | frameHom ψ A₀ hζ (ofAdd t) ∈ E}
  obtain ⟨sw, hsw⟩ : ∃ sw : Fin n → Bool, ∀ i, η i = flipSign sw i := ⟨_, eq_flipSign hηO⟩
  have hι' : ∀ t : Fin n → ZMod p,
      frameHom ψ (A₀ * (spPerm sw (Equiv.refl (Fin n)))⁻¹) hζ
        (ofAdd fun i => (η i : ZMod p) * t i) = frameHom ψ A₀ hζ (ofAdd t) := by
    intro t
    have hfun : (fun i => (η i : ZMod p) * t i) =
        fun i => ((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i := funext fun i => by rw [hsw i]
    rw [hfun]
    exact frameHom_flipSign ψ A₀ hζ sw t
  have hrange : (frameHom ψ (A₀ * (spPerm sw (Equiv.refl (Fin n)))⁻¹) hζ).range =
      (frameHom ψ A₀ hζ).range := by
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
  refine coordShape_of_jointAligned hp2 hψ hζo (by omega) (by rw [hrange]; exact hE) ?_ hcomp
    (by rw [hrange]; exact hcard)
  rw [setOf_mem_eq_image hι' E]
  exact hal

end General

end CoordSp

open CoordSp

theorem ggSpCoordCompShapeInput_holds : GGSpCoordCompShapeInput := by
  intro G _ _ F _ _ _ n p _ hp2 _ ψ hψ A₀ ζ hζ hζo hn0 E J hE hcomp hcard
  exact coordShape_of_frame hp2 hψ hζo hn0 hE hcomp hcard

section Model

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem ggSpCoordContraryInput_holds : GGSpCoordContraryInput :=
  ggSpCoordContraryInput_of_compShape ggSpCoordCompShapeInput_holds

theorem ggStepTwoCoordModelOn_PSp_of_nonsplit (hns : GGSpCoordModelNonsplitInput) :
    GGStepTwoCoordModelOn .PSp :=
  ggStepTwoCoordModelOn_PSp_of_compShape ggSpCoordCompInput_holds ggSpCoordCompShapeInput_holds hns

theorem ggStepTwoToralWitnessOn_PSp_of_nonsplit (hns : GGSpCoordModelNonsplitInput) :
    GGStepTwoToralWitnessOn .PSp :=
  ggStepTwoToralWitnessOn_PSp_of_compShape ggSpCoordCompInput_holds ggSpCoordCompShapeInput_holds
    hns

end Model

end CFSG.StandardType
