module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2NoSwap
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Proj
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationFrattini
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.GroupTheory.PermutingProducts
import CFSG.GroupTheory.PRankBound
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitModels
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitInnerModels
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (K_FunCommute)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_innerHom_permutes_of_T {L R B T : Subgroup G}
    (hZ : center (BarInf L) = ⊥) (hRN : R ≤ normalizer (L : Set G))
    (hinn : ∀ x (hx : x ∈ R),
      inducedBarInfAutHom L ⟨x, hRN hx⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hBN : B ≤ normalizer (L : Set G))
    (hinnB : ∀ x (hx : x ∈ B),
      inducedBarInfAutHom L ⟨x, hBN hx⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hT : IsPGroup 2 ↥T) (hRT : Permutes R T)
    (hBT : Permutes B T) :
    ∃ (P : Sylow 2 (BarInf L)) (ψ : ↥R →* BarInf L) (ψB : ↥B →* BarInf L),
      (∀ x : ↥R, MulAut.conj (ψ x) = inducedBarInfAutHom L ⟨x, hRN x.2⟩) ∧
      (∀ x : ↥B, MulAut.conj (ψB x) = inducedBarInfAutHom L ⟨x, hBN x.2⟩) ∧
      (ψ.range : Set (BarInf L)) * (P : Set (BarInf L)) = (P : Set (BarInf L)) * ψ.range ∧
      (ψB.range : Set (BarInf L)) * (P : Set (BarInf L)) = (P : Set (BarInf L)) * ψB.range ∧
      ∀ u ∈ (P : Subgroup (BarInf L)), ∃ (s : G) (_hsT : s ∈ T) (hsN : s ∈ normalizer (L : Set G)),
        MulAut.conj u = inducedBarInfAutHom L ⟨s, hsN⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set φ := inducedBarInfAutHom L with hφdef
  set X : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hXdef
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  let eX : BarInf L ≃* ↥X := MonoidHom.ofInjective hinj
  have : Finite ↥X := Finite.of_equiv _ eX.toEquiv
  set Rφ : Subgroup (MulAut (BarInf L)) := (R.subgroupOf N).map φ with hRφdef
  set Sφ : Subgroup (MulAut (BarInf L)) := ((T ⊓ N).subgroupOf N).map φ with hSφdef
  have hRX : Rφ ≤ X := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    exact hinn x hx
  have hperm : (Rφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Rφ := by
    have h1 := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hRT.symm hRN
    exact CFSG.GroupTheory.map_permutes_map φ
      (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hRN inf_le_right h1.symm)
  have hpermX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hRX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hRX).symm
  set Bφ : Subgroup (MulAut (BarInf L)) := (B.subgroupOf N).map φ with hBφdef
  have hBX : Bφ ≤ X := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    exact hinnB x hx
  have hpermB : (Bφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Bφ := by
    have h1 := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hBT.symm hBN
    exact CFSG.GroupTheory.map_permutes_map φ
      (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBN inf_le_right h1.symm)
  have hpermBX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hpermB.symm hBX).symm
  have hS2 : IsPGroup 2 ↥((Sφ ⊓ X).subgroupOf X) := by
    have h2 : IsPGroup 2 ↥Sφ :=
      ((hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm).map φ
    exact (h2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  have hSidx : ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).index := by
    let f : ↥L →* ↥X := (MulAut.conj : BarInf L →* MulAut (BarInf L)).rangeRestrict.comp
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
    have hf : Function.Surjective f :=
      (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hle : ((T ⊓ L).subgroupOf L).map f ≤ (Sφ ⊓ X).subgroupOf X := by
      rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
      have htT : t ∈ T := (mem_inf.mp (show t ∈ T ⊓ L from ht)).1
      rw [mem_subgroupOf]
      refine ⟨⟨⟨t, le_normalizer htL⟩, ?_, uc22s2113_inducedBarInfAutHom_of_mem htL⟩,
        (f ⟨t, htL⟩).2⟩
      show t ∈ T ⊓ N
      exact mem_inf.mpr ⟨htT, le_normalizer htL⟩
    have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
    exact fun h2 => hidx
      (h2.trans ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)))
  let θR : ↥R →* ↥X := (φ.comp (Subgroup.inclusion hRN)).codRestrict X fun x => hinn x x.2
  let e' : ↥X →* BarInf L := eX.symm.toMonoidHom
  have he' : Function.Bijective e' := eX.symm.bijective
  have hθR : θR.range = Rφ.subgroupOf X := by
    ext z
    rw [MonoidHom.mem_range, mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hRN x.2⟩, x.2, rfl⟩
    · rintro ⟨⟨y, hyN⟩, hy, hyz⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hψ : ∀ x : ↥R, MulAut.conj ((e'.comp θR) x) = φ ⟨x, hRN x.2⟩ := fun x => by
    rw [← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val (eX.apply_symm_apply (θR x))
  let θB : ↥B →* ↥X := (φ.comp (Subgroup.inclusion hBN)).codRestrict X fun x => hinnB x x.2
  have hθB : θB.range = Bφ.subgroupOf X := by
    ext z
    rw [MonoidHom.mem_range, mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hBN x.2⟩, x.2, rfl⟩
    · rintro ⟨⟨y, hyN⟩, hy, hyz⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hψB : ∀ x : ↥B, MulAut.conj ((e'.comp θB) x) = φ ⟨x, hBN x.2⟩ := fun x => by
    rw [← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val (eX.apply_symm_apply (θB x))
  refine ⟨(hS2.map e').toSylow ?_, e'.comp θR, e'.comp θB, hψ, hψB, ?_, ?_, ?_⟩
  · rwa [Subgroup.index_map_of_bijective he']
  · show ((e'.comp θR).range : Set (BarInf L)) *
        (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) =
      (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) * (e'.comp θR).range
    rw [MonoidHom.range_comp, hθR]
    exact CFSG.GroupTheory.map_permutes_map e' hpermX
  · show ((e'.comp θB).range : Set (BarInf L)) *
        (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) =
      (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) * (e'.comp θB).range
    rw [MonoidHom.range_comp, hθB]
    exact CFSG.GroupTheory.map_permutes_map e' hpermBX
  ·
    intro u hu
    have hu' : u ∈ (((Sφ ⊓ X).subgroupOf X).map e' : Subgroup (BarInf L)) := hu
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu'
    obtain ⟨⟨t, htN⟩, htT, htv⟩ :=
      Subgroup.mem_map.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.mp hv)).1
    have htT' : t ∈ T := (mem_inf.1 htT).1
    refine ⟨t, htT', htN, ?_⟩
    rw [← hvu, htv, ← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val (eX.apply_symm_apply v)

private theorem uc22s2112r34_swap_map_conj_eq_of_acts {X : Type} [Group X]
    {K : Subgroup X} {u v : X} (hv : v ∈ K)
    (h : ∀ z ∈ K, MulAut.conj u z = MulAut.conj v z) :
    K.map (MulAut.conj u).toMonoidHom = K := by
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    change MulAut.conj u y ∈ K
    rw [h y hy, MulAut.conj_apply]
    exact K.mul_mem (K.mul_mem hv hy) (K.inv_mem hv)
  · intro z hz
    let y : X := (MulAut.conj v)⁻¹ z
    have hy : y ∈ K := by
      dsimp [y]
      exact K.mul_mem (K.mul_mem (K.inv_mem hv) hz) hv
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    change MulAut.conj u y = z
    rw [h y hy]
    dsimp [y]
    group

private theorem uc22s2112r34_swap_inverts_on_left {X : Type} [Group X]
    {K : Subgroup X} {θ : MulAut X} {u a b k : X}
    (ha : a ∈ K) (hk : k ∈ K)
    (hcomm : ∀ z ∈ K, b * z = z * b)
    (hinv : a * k * a⁻¹ = k⁻¹)
    (hθ : ∀ z ∈ K, θ z = k * z * k⁻¹)
    (hu : u = a * b) :
    ∀ z ∈ K, (MulAut.conj u * θ * (MulAut.conj u)⁻¹) z = θ⁻¹ z := by
  intro z hz
  have harg : a⁻¹ * z * a ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem ha) hz) ha
  have hargk : k⁻¹ * z * k ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk
  have hcomm_inv : b⁻¹ * (a⁻¹ * z * a) = (a⁻¹ * z * a) * b⁻¹ := by
    have h := hcomm (a⁻¹ * z * a) harg
    calc b⁻¹ * (a⁻¹ * z * a) = b⁻¹ * ((a⁻¹ * z * a) * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * (a⁻¹ * z * a)) * b⁻¹ := by rw [← h]
      _ = (a⁻¹ * z * a) * b⁻¹ := by group
  have harg_eq : u⁻¹ * z * u = a⁻¹ * z * a := by
    rw [hu, mul_inv_rev]
    calc (b⁻¹ * a⁻¹) * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
      _ = (a⁻¹ * z * a) * b⁻¹ * b := by rw [hcomm_inv]
      _ = a⁻¹ * z * a := by group
  have huact : ∀ w ∈ K, MulAut.conj u w = MulAut.conj a w := by
    intro w hw
    rw [hu]
    simp only [MulAut.conj_apply]
    have h := hcomm w hw
    calc (a * b) * w * (a * b)⁻¹ = a * (b * w) * b⁻¹ * a⁻¹ := by group
      _ = a * (w * b) * b⁻¹ * a⁻¹ := by rw [h]
      _ = a * w * a⁻¹ := by group
  have hθinv : θ⁻¹ z = k⁻¹ * z * k := by
    have h := hθ (k⁻¹ * z * k) hargk
    have hz' : θ (k⁻¹ * z * k) = z := by rw [h]; group
    have := congrArg (fun w => θ⁻¹ w) hz'
    simpa using this.symm
  calc (MulAut.conj u * θ * (MulAut.conj u)⁻¹) z
      = MulAut.conj u (θ ((MulAut.conj u)⁻¹ z)) := by
        simp only [MulAut.mul_apply]
    _ = MulAut.conj u (θ (u⁻¹ * z * u)) := by
        congr 1
    _ = MulAut.conj u (θ (a⁻¹ * z * a)) := by rw [harg_eq]
    _ = MulAut.conj u (k * (a⁻¹ * z * a) * k⁻¹) := by rw [hθ _ harg]
    _ = MulAut.conj a (k * (a⁻¹ * z * a) * k⁻¹) := by
        exact huact _ (K.mul_mem (K.mul_mem hk harg) (K.inv_mem hk))
    _ = k⁻¹ * z * k := by
        rw [MulAut.conj_apply]
        calc a * (k * (a⁻¹ * z * a) * k⁻¹) * a⁻¹
            = (a * k * a⁻¹) * z * (a * k * a⁻¹)⁻¹ := by group
          _ = k⁻¹ * z * k := by rw [hinv]; group
    _ = θ⁻¹ z := hθinv.symm

private theorem uc22s2112r34_swap_agrees_on_sup {X : Type} [Group X]
    {K₁ K₂ : Subgroup X} (hc : ⁅K₁, K₂⁆ = ⊥) {θ : MulAut X}
    {u u₁ u₂ k₁ k₂ : X} (hu₁ : u₁ ∈ K₁) (hu₂ : u₂ ∈ K₂)
    (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hinv₁ : u₁ * k₁ * u₁⁻¹ = k₁⁻¹) (hinv₂ : u₂ * k₂ * u₂⁻¹ = k₂⁻¹)
    (hθ₁ : ∀ z ∈ K₁, θ z = k₁ * z * k₁⁻¹)
    (hθ₂ : ∀ z ∈ K₂, θ z = k₂ * z * k₂⁻¹)
    (hu : u = u₁ * u₂) :
    ∀ z ∈ K₁ ⊔ K₂, (MulAut.conj u * θ * (MulAut.conj u)⁻¹) z = θ⁻¹ z := by
  have hcent : K₁ ≤ centralizer (K₂ : Set X) :=
    commutator_eq_bot_iff_le_centralizer.1 hc
  have hcent₂ : K₂ ≤ centralizer (K₁ : Set X) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hc
  have hcomm₂₁ : ∀ z ∈ K₁, u₂ * z = z * u₂ := by
    intro z hz
    exact (mem_centralizer_iff.1 (hcent₂ hu₂) z hz).symm
  have hcomm₁₂ : ∀ z ∈ K₂, u₁ * z = z * u₁ := by
    intro z hz
    exact (mem_centralizer_iff.1 (hcent hu₁) z hz).symm
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := (hcomm₂₁ u₁ hu₁).symm
  have hleft := uc22s2112r34_swap_inverts_on_left (u := u) (a := u₁) (b := u₂)
    (K := K₁) hu₁ hk₁ hcomm₂₁ hinv₁ hθ₁ hu
  have hright := uc22s2112r34_swap_inverts_on_left (u := u) (a := u₂) (b := u₁)
    (K := K₂) hu₂ hk₂ hcomm₁₂ hinv₂ hθ₂ (by rw [hu, hu₁₂])
  have hle : K₁ ⊔ K₂ ≤ MonoidHom.eqLocus
      (MulAut.conj u * θ * (MulAut.conj u)⁻¹).toMonoidHom (θ⁻¹).toMonoidHom :=
    sup_le hleft hright
  exact hle

private theorem uc22s2112r34_swap_conj_mul_apply {X : Type} [Group X]
    {K : Subgroup X} {u a b : X}
    (hcomm : ∀ z ∈ K, b * z = z * b) (hu : u = a * b) :
    ∀ z ∈ K, MulAut.conj u z = MulAut.conj a z := by
  intro z hz
  rw [hu]
  simp only [MulAut.conj_apply]
  have h := hcomm z hz
  calc (a * b) * z * (a * b)⁻¹ = a * (b * z) * b⁻¹ * a⁻¹ := by group
    _ = a * (z * b) * b⁻¹ * a⁻¹ := by rw [h]
    _ = a * z * a⁻¹ := by group

private theorem uc22s2112r34_fixed_conj_eq {X : Type} [Group X] (y : X) :
    signalizerFixedSubgroup (MulAut.conj y) = centralizer ({y} : Set X) := by
  ext k
  change y * k * y⁻¹ = k ↔ _
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

section Swap


private theorem uc22s2112r34_swap_isPGroup_inf {X : Type} [Group X] {p f : ℕ}
    {K₁ K₂ : Subgroup X} (hK₁ : IsFundamentalOver (p ^ f) K₁)
    (hc : ⁅K₁, K₂⁆ = ⊥) : IsPGroup 2 ↥(K₁ ⊓ K₂) := by
  have hc' : ⁅K₂, K₁⁆ = ⊥ := by rw [commutator_comm]; exact hc
  have hcent : K₂ ≤ centralizer (K₁ : Set X) :=
    commutator_eq_bot_iff_le_centralizer.1 hc'
  refine (IsPGroup.iff_orderOf (p := 2) (G := ↥(K₁ ⊓ K₂))).2 ?_
  intro z
  have hzK₁ : (z : X) ∈ K₁ := z.2.1
  have hzC : (z : X) ∈ centralizer (K₁ : Set X) := hcent z.2.2
  have hz2 : (z : X) ^ 2 = 1 :=
    sq_eq_one_of_mem_fundamental_centralizer hK₁ hzK₁ hzC
  have hdvd : orderOf z ∣ 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hz2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by rw [h]; rfl⟩
  · exact ⟨1, by rw [h]; rfl⟩

private theorem uc22s2112r34_swap_exists_inverter {X : Type} [Group X] [Finite X]
    {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K R Q : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K)
    (hRK : R ≤ K) (hR1 : R ≠ ⊥)
    (hRQ : (R : Set X) * (Q : Set X) = (Q : Set X) * (R : Set X))
    (hcardR : Nat.card R ∣ r ^ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) :
    ∃ t ∈ Q, ∀ y ∈ K ⊓ centralizer (R : Set X), t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨p', e₀, e, hp'fact, hp'2, he₀, hq', he, φ, hφrange, hφker⟩ :=
    uc22s2112r34_exists_sl2_cover hK
  have hp' : p'.Prime := hp'fact.out
  have hpp' : p' = p := by
    have hd : p' ∣ p ^ f := by
      rw [hq']
      exact dvd_pow_self p' (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).1 (hp'.dvd_of_dvd_pow hd)
  subst p'
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> omega
  have hr6 : ¬ r ∣ 6 := by
    intro h
    rw [show 6 = 2 * 3 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h2 | h3
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
      have := Nat.prime_two.two_le
      omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      have := Nat.prime_three.two_le
      omega
  have hrp' : ¬ r ∣ p := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
  have hcop6 : Nat.Coprime r 6 := (Nat.Prime.coprime_iff_not_dvd hr).2 hr6
  have hcopp : Nat.Coprime r p := (Nat.Prime.coprime_iff_not_dvd hr).2 hrp'
  have hcop' : Nat.Coprime r (6 * p) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hcop6, hcopp⟩
  have hcop : Nat.Coprime (r ^ 2) (6 * p) := hcop'.pow_left 2
  have hRc : Nat.Coprime (Nat.card R) (6 * p) :=
    Nat.Coprime.of_dvd_left hcardR hcop
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 Q φ.range := by
    rwa [hφrange]
  have hRK' : R ≤ φ.range := by rwa [hφrange]
  let hpFact : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htQ, htInv⟩ :=
    @uc22s2112r34_exists_inv_centralizer_sl2
      X _ _ p e hpFact hp2 he1 φ hφker Q R hQ' hRK' hRQ hR1 hRc
  exact ⟨t, htQ, by simpa [hφrange] using htInv⟩

private theorem uc22s2112r34_swap_normalizes {X : Type} [Group X] [Finite X]
    {p f r : ℕ} {K R : Subgroup X} (hK : IsFundamentalOver (p ^ f) K)
    (hRK : R ≤ K) {x y : X} (hxc : x ∈ centralizer (R : Set X))
    (hyR : y ∈ R) (hord : orderOf y = r)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) {Q : X → Prop} (hyQ : ¬ Q y)
    (huniq : ∀ K K' : Subgroup X, IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ z ∈ K ⊓ K', (orderOf z).Prime → 5 ≤ orderOf z →
        orderOf z ≠ p → K = K' ∨ Q z) :
    x ∈ normalizer (K : Set X) := by
  have hK' : IsFundamentalOver (p ^ f) (K.map (MulAut.conj x).toMonoidHom) :=
    isFundamentalOver_map_mulEquiv (MulAut.conj x) hK
  have hyK : y ∈ K := hRK hyR
  have hyK' : y ∈ K.map (MulAut.conj x).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨y, hyK, ?_⟩
    change MulAut.conj x y = y
    rw [MulAut.conj_apply]
    have h := mem_centralizer_iff.1 hxc y hyR
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
      _ = y := by group
  have hEq : K = K.map (MulAut.conj x).toMonoidHom :=
    (huniq K (K.map (MulAut.conj x).toMonoidHom) hK hK' y ⟨hyK, hyK'⟩
      (by rw [hord]; exact hr) (by rw [hord]; exact hr5) (by rw [hord]; exact hrp)).resolve_right
      hyQ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hEq.symm

private theorem uc22s2112r34_swap_inner_on {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    {K R : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hRK : R ≤ K) {x : X}
    (hxN : x ∈ normalizer (K : Set X)) (hxo : Odd (orderOf x))
    (hxc : x ∈ centralizer (R : Set X)) :
    ∃ k : ↥K, (∀ a ∈ K, x * a * x⁻¹ = (k : X) * a * (k : X)⁻¹) ∧
      (k : X) ∈ centralizer (R : Set X) := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (odd_normalizer_inner_of_isFundamentalOver_general hK hxN hxo)
  have hk' : K.normalizerMonoidHom ⟨x, hxN⟩ = MulAut.conj k := hk.symm
  have hact : ∀ a ∈ K, x * a * x⁻¹ = (k : X) * a * (k : X)⁻¹ := by
    intro a ha
    rw [← Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ ⟨a, ha⟩, hk']
    simp [MulAut.conj_apply]
  refine ⟨k, hact, ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have hyK : y ∈ K := hRK hy
  have hxy : x * y = y * x := (mem_centralizer_iff.1 hxc y hy).symm
  have hfix : x * y * x⁻¹ = y := by rw [hxy]; group
  have hky : (k : X) * y * (k : X)⁻¹ = y := by rw [← hact y hyK, hfix]
  calc y * (k : X) = ((k : X) * y * (k : X)⁻¹) * (k : X) := by rw [hky]
    _ = (k : X) * y := by group

private theorem uc22s2112r34_swap_faithful_on {D : Data G} (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq7 : 7 ≤ p ^ f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hMs : IsStronglyPEmbedded p D.M) {b : G} (hb : b ∈ c.B0) (hb1 : b ≠ 1)
    (hBN : c.B0 ≤ normalizer (L : Set G))
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 →
      ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {K₁ K₂ : Subgroup (BarInf L)} (h₁ : IsFundamentalOver (p ^ f) K₁)
    (h₂ : IsFundamentalOver (p ^ f) K₂) (hc : ⁅K₁, K₂⁆ = ⊥)
    (hfix : ∀ k ∈ K₁ ⊔ K₂, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) : False := by
  have hbord : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hbord
  let e := orderOf b / s
  let b' : G := b ^ e
  have hordb' : orderOf b' = s :=
    orderOf_pow_orderOf_div (orderOf_pos b).ne' hsdvd
  have hb'B : b' ∈ c.B0 := c.B0.pow_mem hb e
  have hb'N : b' ∈ normalizer (L : Set G) := hBN hb'B
  have hfix' : ∀ k ∈ K₁ ⊔ K₂, inducedBarInfAutHom L ⟨b', hb'N⟩ k = k := by
    intro k hk
    have hpow : inducedBarInfAutHom L ⟨b', hb'N⟩ =
        (inducedBarInfAutHom L ⟨b, hBN hb⟩) ^ e := by
      rw [show (⟨b', hb'N⟩ : ↥(normalizer (L : Set G))) = ⟨b, hBN hb⟩ ^ e from
        Subtype.ext rfl, map_pow]
    rw [hpow]
    have hfixpow : ∀ n : ℕ, ((inducedBarInfAutHom L ⟨b, hBN hb⟩) ^ n) k = k := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, hfix k hk, ih]
    exact hfixpow e
  refine uc22s2112r34_false_of_pair hKF7 hH c hL.1.le hp hp2 hq7 hpσ hMs hb'B hb'N ?_ ?_ hpN
    h₁ h₂ hc ?_
  · rw [hordb']; exact hs
  · rw [hordb']
    exact hπN s hs (hsdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb))
  · intro k hk
    exact hfix' k hk

private theorem uc22s2112r34_false_noswap_of {D : Data G} (c : Ctx21 D (Choice214U D))
    {L : Subgroup G} (hBN : c.B0 ≤ normalizer (L : Set G)) (hB0 : c.B0 ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpB : 5 ≤ p ∨ ¬ p ∣ Nat.card c.B0) {Q : BarInf L → Prop}
    (huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x →
        orderOf x ≠ p → K = K' ∨ Q x)
    (P : Sylow 2 (BarInf L)) (ψB : ↥c.B0 →* BarInf L)
    (hψB : ∀ x : ↥c.B0, MulAut.conj (ψB x) = inducedBarInfAutHom L ⟨x, hBN x.2⟩)
    (hpermB : (ψB.range : Set (BarInf L)) * (P : Set (BarInf L)) =
      (P : Set (BarInf L)) * ψB.range)
    (hPT : ∀ u ∈ (P : Subgroup (BarInf L)), ∃ (s : G) (_hsT : s ∈ D.T)
      (hsN : s ∈ normalizer (L : Set G)), MulAut.conj u = inducedBarInfAutHom L ⟨s, hsN⟩)
    {Ka Kb : Subgroup (BarInf L)} (ha : IsFundamentalOver (p ^ f) Ka) (hKab : ⁅Ka, Kb⁆ = ⊥)
    (hin : UC22NoSwapInput p (P : Subgroup (BarInf L)) Ka Kb)
    (hPa : (P : Subgroup (BarInf L)) ≤ normalizer (Ka : Set (BarInf L)))
    (hPb : (P : Subgroup (BarInf L)) ≤ normalizer (Kb : Set (BarInf L)))
    (hfaith : ∀ b (hb : b ∈ c.B0),
      (∀ k ∈ Ka ⊔ Kb, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) → b = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) {y : BarInf L} (hyB : y ∈ ψB.range)
    (hyK : y ∈ Ka) (hyr : orderOf y = r) (hyQ : ¬ Q y) (hyc : ∃ k ∈ Ka, y * k * y⁻¹ ≠ k) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have haC : Ka ≤ centralizer (Kb : Set (BarInf L)) :=
    commutator_eq_bot_iff_le_centralizer.1 hKab
  have hbC : Kb ≤ centralizer (Ka : Set (BarInf L)) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hKab
  have hCa : centralizer (Ka : Set (BarInf L)) = Kb := le_antisymm hin.1 hbC
  have hNab : ∀ g ∈ normalizer (Ka : Set (BarInf L)), g ∈ normalizer (Kb : Set (BarInf L)) := by
    intro g hg
    rw [mem_normalizer_iff] at hg ⊢
    intro k
    simp only [← hCa, SetLike.mem_coe, mem_centralizer_iff]
    constructor
    · intro hk z hz
      have hz' : g⁻¹ * z * g ∈ Ka := by
        refine (hg _).2 ?_
        have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
        rw [e]
        exact hz
      have h1 := hk _ hz'
      calc z * (g * k * g⁻¹) = g * ((g⁻¹ * z * g) * k) * g⁻¹ := by group
        _ = g * (k * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
        _ = g * k * g⁻¹ * z := by group
    · intro hk z hz
      have h1 := hk _ ((hg z).1 hz)
      have h2 : g * (z * k) * g⁻¹ = g * (k * z) * g⁻¹ := by
        calc g * (z * k) * g⁻¹ = g * z * g⁻¹ * (g * k * g⁻¹) := by group
          _ = g * k * g⁻¹ * (g * z * g⁻¹) := h1
          _ = g * (k * z) * g⁻¹ := by group
      simpa using h2
  have hmapN : ∀ (K : Subgroup (BarInf L)) (g : BarInf L), g ∈ normalizer (K : Set (BarInf L)) →
      K.map (MulAut.conj g).toMonoidHom = K := fun K g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  have hBc : ∀ a ∈ ψB.range, ∀ b ∈ ψB.range, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hb
    rw [← map_mul, ← map_mul, c.hB0.2.1.is_comm.comm a b]
  have hBo : Odd (Nat.card ψB.range) :=
    Odd.of_dvd_nat (ch214_odd_card c.hpi) (Subgroup.card_range_dvd ψB)
  have hpB' : 5 ≤ p ∨ ¬ p ∣ Nat.card ψB.range :=
    hpB.imp_right fun h h' => h (h'.trans (Subgroup.card_range_dvd ψB))
  have hBNa : ψB.range ≤ normalizer (Ka : Set (BarInf L)) := fun x hx =>
    uc22s2112r34_swap_normalizes ha (inf_le_right : ψB.range ⊓ Ka ≤ Ka)
      (Subgroup.centralizer_le inf_le_left (mem_centralizer_iff.2 fun z hz => hBc z hz x hx))
      ⟨hyB, hyK⟩ hyr hr hr5 hrp hyQ huniq
  have hBNb : ψB.range ≤ normalizer (Kb : Set (BarInf L)) := fun x hx => hNab x (hBNa hx)
  obtain ⟨F₁, _, _, _, ρ₁, hρ₁, hQ₁⟩ := hin.2.2.1 Ka (Set.mem_insert _ _)
  obtain ⟨F₂, _, _, _, ρ₂, hρ₂, hQ₂⟩ := hin.2.2.1 Kb (Set.mem_insert_of_mem _ rfl)
  obtain ⟨u, huP, hu⟩ := uc22s2112r34_noswap_exists_inverter hp2 ρ₁ ρ₂ hρ₁ hρ₂
    (fun a ha b hb => (mem_centralizer_iff.1 (haC ha) b hb).symm) P.isPGroup' hPa hPb hBNa
    hBNb hBc hBo hpB' hpermB (hQ₁ hPa) (hQ₂ hPb) (hin.2.2.2 hPa hPb Ka (Set.mem_insert _ _))
    (hin.2.2.2 hPa hPb Kb (Set.mem_insert_of_mem _ rfl)) hr hr5 hyB hyr hyc
  obtain ⟨s, hsT, hsN, hsu⟩ := hPT u huP
  have hθ : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ = MulAut.conj (ψB ⟨b, hb⟩) := fun b hb =>
    (hψB ⟨b, hb⟩).symm
  have hKB : ∀ b (hb : b ∈ c.B0),
      (Ka ⊔ Kb).map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = Ka ⊔ Kb := by
    intro b hb
    rw [hθ b hb, Subgroup.map_sup, hmapN Ka _ (hBNa ⟨_, rfl⟩), hmapN Kb _ (hBNb ⟨_, rfl⟩)]
  have hsK : (Ka ⊔ Kb).map (inducedBarInfAutHom L ⟨s, hsN⟩).toMonoidHom = Ka ⊔ Kb := by
    rw [← hsu, Subgroup.map_sup, hmapN Ka u (hPa huP), hmapN Kb u (hPb huP)]
  have hinvK : ∀ b (hb : b ∈ c.B0), ∀ k ∈ Ka ⊔ Kb,
      (inducedBarInfAutHom L ⟨s, hsN⟩ * inducedBarInfAutHom L ⟨b, hBN hb⟩ *
        (inducedBarInfAutHom L ⟨s, hsN⟩)⁻¹) k = (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ k := by
    intro b hb k hk
    have h := hu (ψB ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ k hk
    rw [← hsu, hθ b hb]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [← h]
    group
  exact uc22s2112r34_false_of_inverts_on c hBN hB0 hKB hfaith hsT hsN hsK hinvK

theorem uc22s2112r34_false_swap_core_of (hKS : KFunSplit) (hKC : KFunCount) (hFC : K_FunCommute)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n) (hq7 : 7 ≤ p ^ f)
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card c.B0) (hr5 : 5 ≤ r)
    (hrp : r ≠ p)
    (hpair : ∀ b (hb : b ∈ c.B0), b ≠ 1 → ∀ K₁ K₂ : Subgroup (BarInf L),
      IsFundamentalOver (p ^ f) K₁ → IsFundamentalOver (p ^ f) K₂ → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
      ¬ ∀ k ∈ K₁ ⊔ K₂, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k)
    (hswap : ∀ (P : Sylow 2 (BarInf L)) (K₁ K₂ : Subgroup (BarInf L)),
      K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) →
      K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) → K₁ ≠ K₂ →
      (∃ w ∈ (P : Subgroup (BarInf L)), K₁.map (MulAut.conj w).toMonoidHom = K₂) ∨
        (UC22NoSwapInput p (P : Subgroup (BarInf L)) K₁ K₂ ∧ (5 ≤ p ∨ ¬ p ∣ Nat.card c.B0)))
    (Q : BarInf L → Prop)
    (hQ : ∀ b (hb : b ∈ c.B0), (orderOf b).Prime → ∀ y : BarInf L,
      MulAut.conj y = inducedBarInfAutHom L ⟨b, hBN hb⟩ → ∀ K : Subgroup (BarInf L),
        IsFundamentalOver (p ^ f) K → K ≤ centralizer ({y} : Set (BarInf L)) → ¬ Q y)
    (huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x →
        orderOf x ≠ p → K = K' ∨ Q x) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p := by
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1
      (fun h => hA3 ⟨h.1, h.2.1⟩) hRee hpN
    rcases h4 with ⟨hexc, rfl⟩ | h4
    · exact uc22s2112r34_not_isL3EpsOdd17_of_exc hp hX hexc
    · exact uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  have hrπ : r ∈ piSet c.B0 := ⟨hr, hrB⟩
  have hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := hπN r hr hrπ.2
  obtain ⟨R, hRB, -, hrR, hRr2, hRT, hRr⟩ :=
    uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup hr hrπ.2
  have hRN : R ≤ normalizer (L : Set G) := hRB.trans hBN
  have hB0T : Permutes c.B0 D.T := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h, -, -⟩ := c.hB0
    exact h
  obtain ⟨P, ψ, ψB, hψ, hψB, hperm, hpermB, hPT⟩ :=
    uc22s2112r34_exists_innerHom_permutes_of_T hZ hRN (fun x hx => hinn x (hRB hx)) hBN hinn
      (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT hB0T
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ = 1 := by
      rw [← hψ x, hx, map_one]
    exact Subtype.ext (hfaith x (hRB x.2)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 _ h1))
  have hcardB : Nat.card ψ.range = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hne : ψ.range ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcardB
    rw [← hcardB] at hrR
    exact hr.one_lt.ne' (Nat.dvd_one.1 hrR)
  have : IsMulCommutative ↥c.B0 := c.hB0.2.1
  have : IsMulCommutative ↥R := isMulCommutative_anti hRB
  have hoddB : Odd (Nat.card ψ.range) := by
    rw [hcardB]
    exact (hr.odd_of_ne_two (by omega)).pow.of_dvd_nat hRr2
  have h3B : ¬ 3 ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow (h.trans hRr2))
    omega
  have hpB : ¬ p ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow (h.trans hRr2))).symm
  have hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range →
      CFSG.pRank s ψ.range ≤ 2 ∧ CFSG.pRank s (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro s hs hsd
    rw [hcardB] at hsd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hs hr).1 (hs.dvd_of_dvd_pow (hsd.trans hRr2))
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hs fun h => ?_
      rw [hcardB] at h
      have := (Nat.pow_dvd_pow_iff_le_right hs.one_lt).1 (h.trans hRr2)
      omega
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hs hrN]
      exact (CFSG.SectionRank.pRank_mono hs.one_lt hL.1.le).trans
        (uc22s2112r34_pRank_le_three hσ hH c hL hrπ (by omega))
  obtain ⟨K₁, K₂, hne12, hKeq⟩ :=
    Set.ncard_eq_two.1 ((hKC (BarInf L) t n p f hp hp2 hadm hX P).1 ht)
  have h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert _ _
  have h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hK12 : ⁅K₁, K₂⁆ = ⊥ :=
    uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree (by omega) P h₁ h₂ hne12
  have hR0 : ∀ y ∈ ψ.range, y ∈ centralizer (K₁ : Set (BarInf L)) →
      y ∈ centralizer (K₂ : Set (BarInf L)) → y = 1 := by
    intro y hy hy1 hy2
    by_contra hyne
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hx1 : (x : G) ≠ 1 := by
      intro h
      apply hyne
      rw [show x = 1 from Subtype.ext h, map_one]
    have hle : K₁ ⊔ K₂ ≤
        signalizerFixedSubgroup (inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩) := by
      refine sup_le ?_ ?_
      · intro k hk
        change inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ k = k
        rw [← hψ x, MulAut.conj_apply, ← mem_centralizer_iff.1 hy1 k hk, mul_inv_cancel_right]
      · intro k hk
        change inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ k = k
        rw [← hψ x, MulAut.conj_apply, ← mem_centralizer_iff.1 hy2 k hk, mul_inv_cancel_right]
    exact hpair x (hRB x.2) hx1 K₁ K₂ h₁.1 h₂.1 hne12 hK12 fun k hk => hle hk
  have hspl₁ := hKS (BarInf L) t n p f hp hp2 hadm hX hA1 hRee P ψ.range hne inferInstance
    hoddB h3B hpB hperm hrank K₁ h₁
  have hspl₂ := hKS (BarInf L) t n p f hp hp2 hadm hX hA1 hRee P ψ.range hne inferInstance
    hoddB h3B hpB hperm hrank K₂ h₂
  have hRsup : ψ.range = (ψ.range ⊓ K₁) ⊔ (ψ.range ⊓ K₂) :=
    uc22s2112r34_eq_sup_of_split hK12 hspl₁ hspl₂ hR0
  have hKK : IsPGroup 2 ↥(K₁ ⊓ K₂) := uc22s2112r34_swap_isPGroup_inf h₁.1 hK12
  have hK21 : ⁅K₂, K₁⁆ = ⊥ := by rw [commutator_comm]; exact hK12
  have hcent₂ : K₂ ≤ centralizer (K₁ : Set (BarInf L)) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hK12
  have hcent₁ : K₁ ≤ centralizer (K₂ : Set (BarInf L)) :=
    commutator_eq_bot_iff_le_centralizer.1 hK12
  have hfaithK : ∀ b (hb : b ∈ c.B0),
      (∀ k ∈ (K₁ ⊔ K₂ : Subgroup (BarInf L)),
        inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) → b = 1 := by
    intro b hb hfix
    by_contra hb1
    exact hpair b hb hb1 K₁ K₂ h₁.1 h₂.1 hne12 hK12 hfix
  have hB0 : c.B0 ≠ ⊥ := by
    have hdvdB : r ∣ Nat.card c.B0 := hrπ.2
    intro h
    rw [h, card_bot] at hdvdB
    exact hr.one_lt.ne' (Nat.dvd_one.1 hdvdB)
  obtain ⟨w, hwP, hwK⟩ : ∃ w ∈ (P : Subgroup (BarInf L)),
      K₁.map (MulAut.conj w).toMonoidHom = K₂ := by
    by_contra hsw
    obtain ⟨hin, hpB0⟩ := (hswap P K₁ K₂ h₁ h₂ hne12).resolve_left hsw
    have hinvmap : ∀ (g : BarInf L) (K K' : Subgroup (BarInf L)),
        K.map (MulAut.conj g).toMonoidHom = K' → K'.map (MulAut.conj g⁻¹).toMonoidHom = K := by
      intro g K K' h
      rw [← h, Subgroup.map_map,
        show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id (BarInf L) by ext z; simp]
      exact Subgroup.map_id K
    have hfix : ∀ g ∈ (P : Subgroup (BarInf L)), ∀ K ∈ FunSet (fundPred (p ^ f)) (BarInf L)
        (P : Subgroup (BarInf L)), K.map (MulAut.conj g).toMonoidHom = K := by
      intro g hg K hK
      have hgK := F14.mem_funSet_map_conj_of_mem_normalizer (𝔉 := fundPred (p ^ f))
        (fun g {_} hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK)
        (Subgroup.le_normalizer hg) hK
      rw [hKeq] at hK hgK
      rcases hK with rfl | rfl <;> rcases hgK with h | h
      · exact h
      · exact (hsw ⟨g, hg, h⟩).elim
      · exact (hsw ⟨g⁻¹, (P : Subgroup (BarInf L)).inv_mem hg, hinvmap g _ _ h⟩).elim
      · exact h
    have hPN₁ : (P : Subgroup (BarInf L)) ≤ normalizer (K₁ : Set (BarInf L)) := fun g hg =>
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg K₁ h₁)
    have hPN₂ : (P : Subgroup (BarInf L)) ≤ normalizer (K₂ : Set (BarInf L)) := fun g hg =>
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg K₂ h₂)
    have key : ∀ Ka Kb : Subgroup (BarInf L), IsFundamentalOver (p ^ f) Ka →
        IsFundamentalOver (p ^ f) Kb → ⁅Ka, Kb⁆ = ⊥ →
        UC22NoSwapInput p (P : Subgroup (BarInf L)) Ka Kb →
        (P : Subgroup (BarInf L)) ≤ normalizer (Ka : Set (BarInf L)) →
        (P : Subgroup (BarInf L)) ≤ normalizer (Kb : Set (BarInf L)) →
        (∀ b (hb : b ∈ c.B0),
          (∀ k ∈ Ka ⊔ Kb, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) → b = 1) →
        (∀ y ∈ ψ.range, y ∈ centralizer (Ka : Set (BarInf L)) →
          y ∈ centralizer (Kb : Set (BarInf L)) → y = 1) →
        ψ.range ⊓ Ka ≠ ⊥ → False := by
      intro Ka Kb ha hb hKab hinab hPa hPb hfa hR0' hRa
      obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRa
      obtain ⟨a, hψa⟩ := MonoidHom.mem_range.1 y.2.1
      have hy1' : (y : BarInf L) ≠ 1 := fun h => hy1 (Subtype.ext h)
      have haG1 : (a : G) ≠ 1 := by
        intro h
        apply hy1'
        rw [← hψa, show a = 1 from Subtype.ext h, map_one]
      have hord : orderOf (y : BarInf L) = r := by
        rw [← hψa]
        calc orderOf (ψ a) = orderOf a := orderOf_injective ψ hψinj a
          _ = orderOf (a : G) := (Subgroup.orderOf_coe a).symm
          _ = r := hRr a a.2 haG1
      have hyB : (y : BarInf L) ∈ ψB.range :=
        ⟨⟨a, hRB a.2⟩, by rw [← hψa]; exact hinj ((hψB _).trans (hψ a).symm)⟩
      have hyQ : ¬ Q (y : BarInf L) := by
        refine hQ a (hRB a.2) (by rw [hRr a a.2 haG1]; exact hr) _
          (by rw [← hψa]; exact hψ a) Kb hb fun k hk => ?_
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKab y.2.2) k hk
      have hyc : ∃ k ∈ Ka, (y : BarInf L) * k * (y : BarInf L)⁻¹ ≠ k := by
        by_contra hcon
        push Not at hcon
        refine hy1' (hR0' _ y.2.1 ?_ (commutator_eq_bot_iff_le_centralizer.1 hKab y.2.2))
        rw [mem_centralizer_iff]
        intro k hk
        calc k * (y : BarInf L) = ((y : BarInf L) * k * (y : BarInf L)⁻¹) * y := by
              rw [hcon k hk]
          _ = y * k := by group
      exact uc22s2112r34_false_noswap_of c hBN hB0 hp hp2 hpB0 huniq P ψB hψB hpermB hPT ha
        hKab hinab hPa hPb hfa hr hr5 hrp hyB y.2.2 hord hyQ hyc
    by_cases hR1 : ψ.range ⊓ K₁ = ⊥
    · refine key K₂ K₁ h₂.1 h₁.1 hK21 hin.symm hPN₂ hPN₁ (fun b hb hfix => hfaithK b hb fun k hk =>
        hfix k (by rw [sup_comm]; exact hk)) (fun y hy h2 h1 => hR0 y hy h1 h2) fun h2 => hne ?_
      rw [hRsup, hR1, h2, sup_bot_eq]
    · exact key K₁ K₂ h₁.1 h₂.1 hK12 hin hPN₁ hPN₂ hfaithK hR0 hR1
  have hwPinv : w⁻¹ ∈ (P : Subgroup (BarInf L)) := P.inv_mem hwP
  have hwK' : K₂.map (MulAut.conj w⁻¹).toMonoidHom = K₁ := by
    rw [← hwK, Subgroup.map_map]
    rw [show (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
        MonoidHom.id (BarInf L) by
      ext z
      simp]
    exact Subgroup.map_id K₁
  have hR2ne : ψ.range ⊓ K₂ ≠ ⊥ := by
    intro hbot
    have hle : ψ.range ≤ K₁ := by
      rw [hRsup, hbot, sup_bot_eq]
      exact inf_le_right
    exact hne (uc22s2112r34_eq_bot_of_swap hK12 hKK P.isPGroup' hwP hwK hoddB hle hperm)
  have hR1ne : ψ.range ⊓ K₁ ≠ ⊥ := by
    intro hbot
    have hle : ψ.range ≤ K₂ := by
      rw [hRsup, hbot, bot_sup_eq]
      exact inf_le_right
    have hKK' : IsPGroup 2 ↥(K₂ ⊓ K₁) := by rwa [inf_comm]
    exact hne (uc22s2112r34_eq_bot_of_swap hK21 hKK' P.isPGroup' hwPinv hwK' hoddB hle hperm)
  have hperm1 : ((ψ.range ⊓ K₁ : Subgroup (BarInf L)) : Set (BarInf L)) *
      (((P ⊓ K₁ : Subgroup (BarInf L))) : Set (BarInf L)) =
      (((P ⊓ K₁ : Subgroup (BarInf L))) : Set (BarInf L)) *
        ((ψ.range ⊓ K₁ : Subgroup (BarInf L)) : Set (BarInf L)) :=
    uc22s2112r34_proj_permutes hK12 hKK P.isPGroup' h₁.2 h₂.2 hRsup hperm
  have hKK' : IsPGroup 2 ↥(K₂ ⊓ K₁) := by rwa [inf_comm]
  have hRsup2 : ψ.range = (ψ.range ⊓ K₂) ⊔ (ψ.range ⊓ K₁) :=
    hRsup.trans (sup_comm _ _)
  have hperm2 : ((ψ.range ⊓ K₂ : Subgroup (BarInf L)) : Set (BarInf L)) *
      (((P ⊓ K₂ : Subgroup (BarInf L))) : Set (BarInf L)) =
      (((P ⊓ K₂ : Subgroup (BarInf L))) : Set (BarInf L)) *
        ((ψ.range ⊓ K₂ : Subgroup (BarInf L)) : Set (BarInf L)) :=
    uc22s2112r34_proj_permutes hK21 hKK' P.isPGroup' h₂.2 h₁.2 hRsup2 hperm
  have hcardR1 : Nat.card ↥(ψ.range ⊓ K₁) ∣ r ^ 2 :=
    (Subgroup.card_dvd_of_le (inf_le_left : ψ.range ⊓ K₁ ≤ ψ.range)).trans
      (by rw [hcardB]; exact hRr2)
  have hcardR2 : Nat.card ↥(ψ.range ⊓ K₂) ∣ r ^ 2 :=
    (Subgroup.card_dvd_of_le (inf_le_left : ψ.range ⊓ K₂ ≤ ψ.range)).trans
      (by rw [hcardB]; exact hRr2)
  obtain ⟨u₁, hu₁Q, hu₁inv⟩ :=
    uc22s2112r34_swap_exists_inverter hp hp2 h₁.1 h₁.2 inf_le_right hR1ne hperm1 hcardR1
      hr hr5 hrp
  obtain ⟨u₂, hu₂Q, hu₂inv⟩ :=
    uc22s2112r34_swap_exists_inverter hp hp2 h₂.1 h₂.2 inf_le_right hR2ne hperm2 hcardR2
      hr hr5 hrp
  let u : BarInf L := u₁ * u₂
  have hu₁K : u₁ ∈ K₁ := hu₁Q.2
  have hu₂K : u₂ ∈ K₂ := hu₂Q.2
  have hdata : ∀ b (hb : b ∈ c.B0),
      (∀ z ∈ K₁ ⊔ K₂, (MulAut.conj u * inducedBarInfAutHom L ⟨b, hBN hb⟩ *
        (MulAut.conj u)⁻¹) z = (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ z) ∧
      K₁.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K₁ ∧
      K₂.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K₂ := by
    intro b hb
    obtain ⟨x, hxb⟩ := MonoidHom.mem_range.1 (hinn b hb)
    have hxcomm : ∀ a : ↥R, x * ψ a = ψ a * x := by
      intro a
      have hba : b * (a : G) = (a : G) * b := by
        have := c.hB0.2.1.is_comm.comm ⟨b, hb⟩ ⟨(a : G), hRB a.2⟩
        exact congrArg Subtype.val this
      have hcommN : (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G))) * ⟨(a : G), hRN a.2⟩ =
          ⟨(a : G), hRN a.2⟩ * ⟨b, hBN hb⟩ := by
        exact Subtype.ext hba
      have hθcomm : inducedBarInfAutHom L ⟨b, hBN hb⟩ * inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩ =
          inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩ * inducedBarInfAutHom L ⟨b, hBN hb⟩ := by
        rw [← map_mul, ← map_mul, hcommN]
      rw [← hxb, ← hψ a] at hθcomm
      apply hinj
      rw [map_mul, map_mul]
      exact hθcomm
    have hxcentR : x ∈ centralizer (ψ.range : Set (BarInf L)) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
      exact (hxcomm a).symm
    have hxodd : Odd (orderOf x) := by
      have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
        have h := orderOf_map_dvd (inducedBarInfAutHom L) (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
        simpa [Subgroup.orderOf_mk] using h
      have hord : orderOf x = orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) := by
        rw [← hxb]
        exact (orderOf_injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) hinj x).symm
      rw [hord]
      exact Odd.of_dvd_nat (ch214_odd_card c.hpi)
        (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb))
    have hxc₁ : x ∈ centralizer ((ψ.range ⊓ K₁ : Subgroup (BarInf L)) : Set (BarInf L)) :=
      Subgroup.centralizer_le inf_le_left hxcentR
    obtain ⟨y₁, hy₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1ne
    obtain ⟨a₁, hψa₁⟩ := MonoidHom.mem_range.1 y₁.2.1
    have hy₁1' : (y₁ : BarInf L) ≠ 1 := fun h => hy₁1 (Subtype.ext h)
    have ha₁G1 : (a₁ : G) ≠ 1 := by
      intro h
      apply hy₁1'
      rw [← hψa₁, show a₁ = 1 from Subtype.ext h, map_one]
    have hord₁ : orderOf (y₁ : BarInf L) = r := by
      rw [← hψa₁]
      calc orderOf (ψ a₁) = orderOf a₁ := orderOf_injective ψ hψinj a₁
        _ = orderOf (a₁ : G) := (Subgroup.orderOf_coe a₁).symm
        _ = r := hRr a₁ a₁.2 ha₁G1
    have hyQ₁ : ¬ Q (y₁ : BarInf L) := by
      refine hQ a₁ (hRB a₁.2) (by rw [hRr a₁ a₁.2 ha₁G1]; exact hr) _
        (by rw [← hψa₁]; exact hψ a₁) K₂ h₂.1 fun k hk => ?_
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (hcent₁ y₁.2.2) k hk
    have hxN₁ : x ∈ normalizer (K₁ : Set (BarInf L)) :=
      uc22s2112r34_swap_normalizes h₁.1 inf_le_right hxc₁ y₁.2 hord₁ hr hr5 hrp hyQ₁ huniq
    obtain ⟨k₁, hk₁act, hk₁cent⟩ :=
      uc22s2112r34_swap_inner_on t n p f hp hp2 hadm hX hA1 hRee h₁.1 inf_le_right
        hxN₁ hxodd hxc₁
    have hθ₁ : ∀ z ∈ K₁, inducedBarInfAutHom L ⟨b, hBN hb⟩ z =
        (k₁ : BarInf L) * z * (k₁ : BarInf L)⁻¹ := by
      intro z hz
      rw [← hxb]
      exact hk₁act z hz
    have hmap₁ : K₁.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K₁ := by
      rw [← hxb]
      refine uc22s2112r34_swap_map_conj_eq_of_acts k₁.2 fun z hz => ?_
      simpa [MulAut.conj_apply] using hk₁act z hz
    have hu₁k₁ : u₁ * (k₁ : BarInf L) * u₁⁻¹ = (k₁ : BarInf L)⁻¹ :=
      hu₁inv (k₁ : BarInf L) ⟨k₁.2, hk₁cent⟩
    have hxc₂ : x ∈ centralizer ((ψ.range ⊓ K₂ : Subgroup (BarInf L)) : Set (BarInf L)) :=
      Subgroup.centralizer_le inf_le_left hxcentR
    obtain ⟨y₂, hy₂1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR2ne
    obtain ⟨a₂, hψa₂⟩ := MonoidHom.mem_range.1 y₂.2.1
    have hy₂1' : (y₂ : BarInf L) ≠ 1 := fun h => hy₂1 (Subtype.ext h)
    have ha₂G1 : (a₂ : G) ≠ 1 := by
      intro h
      apply hy₂1'
      rw [← hψa₂, show a₂ = 1 from Subtype.ext h, map_one]
    have hord₂ : orderOf (y₂ : BarInf L) = r := by
      rw [← hψa₂]
      calc orderOf (ψ a₂) = orderOf a₂ := orderOf_injective ψ hψinj a₂
        _ = orderOf (a₂ : G) := (Subgroup.orderOf_coe a₂).symm
        _ = r := hRr a₂ a₂.2 ha₂G1
    have hyQ₂ : ¬ Q (y₂ : BarInf L) := by
      refine hQ a₂ (hRB a₂.2) (by rw [hRr a₂ a₂.2 ha₂G1]; exact hr) _
        (by rw [← hψa₂]; exact hψ a₂) K₁ h₁.1 fun k hk => ?_
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (hcent₂ y₂.2.2) k hk
    have hxN₂ : x ∈ normalizer (K₂ : Set (BarInf L)) :=
      uc22s2112r34_swap_normalizes h₂.1 inf_le_right hxc₂ y₂.2 hord₂ hr hr5 hrp hyQ₂ huniq
    obtain ⟨k₂, hk₂act, hk₂cent⟩ :=
      uc22s2112r34_swap_inner_on t n p f hp hp2 hadm hX hA1 hRee h₂.1 inf_le_right
        hxN₂ hxodd hxc₂
    have hθ₂ : ∀ z ∈ K₂, inducedBarInfAutHom L ⟨b, hBN hb⟩ z =
        (k₂ : BarInf L) * z * (k₂ : BarInf L)⁻¹ := by
      intro z hz
      rw [← hxb]
      exact hk₂act z hz
    have hmap₂ : K₂.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K₂ := by
      rw [← hxb]
      refine uc22s2112r34_swap_map_conj_eq_of_acts k₂.2 fun z hz => ?_
      simpa [MulAut.conj_apply] using hk₂act z hz
    have hu₂k₂ : u₂ * (k₂ : BarInf L) * u₂⁻¹ = (k₂ : BarInf L)⁻¹ :=
      hu₂inv (k₂ : BarInf L) ⟨k₂.2, hk₂cent⟩
    refine ⟨?_, hmap₁, hmap₂⟩
    exact uc22s2112r34_swap_agrees_on_sup hK12 hu₁K hu₂K k₁.2 k₂.2 hu₁k₁ hu₂k₂ hθ₁ hθ₂ rfl
  have hKB : ∀ b (hb : b ∈ c.B0),
      (K₁ ⊔ K₂ : Subgroup (BarInf L)).map
        (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K₁ ⊔ K₂ := by
    intro b hb
    rw [Subgroup.map_sup, (hdata b hb).2.1, (hdata b hb).2.2]
  have huP : u ∈ (P : Subgroup (BarInf L)) := P.mul_mem hu₁Q.1 hu₂Q.1
  obtain ⟨s, hsT, hsN, hsu⟩ := hPT u huP
  have hcomm₂₁ : ∀ z ∈ K₁, u₂ * z = z * u₂ := by
    intro z hz
    exact (mem_centralizer_iff.1 (hcent₂ hu₂K) z hz).symm
  have hcomm₁₂ : ∀ z ∈ K₂, u₁ * z = z * u₁ := by
    intro z hz
    exact (mem_centralizer_iff.1 (hcent₁ hu₁K) z hz).symm
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := (hcomm₂₁ u₁ hu₁K).symm
  have hmapu₁ : K₁.map (MulAut.conj u).toMonoidHom = K₁ :=
    uc22s2112r34_swap_map_conj_eq_of_acts hu₁K
      (uc22s2112r34_swap_conj_mul_apply (u := u) (a := u₁) (b := u₂) (K := K₁) hcomm₂₁ rfl)
  have hmapu₂ : K₂.map (MulAut.conj u).toMonoidHom = K₂ :=
    uc22s2112r34_swap_map_conj_eq_of_acts hu₂K
      (uc22s2112r34_swap_conj_mul_apply (u := u) (a := u₂) (b := u₁) (K := K₂) hcomm₁₂
        (by rw [show u = u₁ * u₂ from rfl, hu₁₂]))
  have hsK : (K₁ ⊔ K₂ : Subgroup (BarInf L)).map
      (inducedBarInfAutHom L ⟨s, hsN⟩).toMonoidHom = K₁ ⊔ K₂ := by
    rw [← hsu, Subgroup.map_sup, hmapu₁, hmapu₂]
  have hinvK : ∀ b (hb : b ∈ c.B0), ∀ k ∈ (K₁ ⊔ K₂ : Subgroup (BarInf L)),
      (inducedBarInfAutHom L ⟨s, hsN⟩ * inducedBarInfAutHom L ⟨b, hBN hb⟩ *
        (inducedBarInfAutHom L ⟨s, hsN⟩)⁻¹) k =
        (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ k := by
    intro b hb k hk
    have h := (hdata b hb).1 k hk
    rwa [hsu] at h
  exact uc22s2112r34_false_of_inverts_on c hBN hB0 hKB hfaithK hsT hsN hsK hinvK

theorem uc22s2112r34_false_swap_core (hKS : KFunSplit) (hKC : KFunCount) (hFC : K_FunCommute)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n) (hq7 : 7 ≤ p ^ f)
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card c.B0) (hr5 : 5 ≤ r)
    (hrp : r ≠ p)
    (hpair : ∀ b (hb : b ∈ c.B0), b ≠ 1 → ∀ K₁ K₂ : Subgroup (BarInf L),
      IsFundamentalOver (p ^ f) K₁ → IsFundamentalOver (p ^ f) K₂ → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
      ¬ ∀ k ∈ K₁ ⊔ K₂, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k)
    (hswap : ∀ (P : Sylow 2 (BarInf L)) (K₁ K₂ : Subgroup (BarInf L)),
      K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) →
      K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) → K₁ ≠ K₂ →
      (∃ w ∈ (P : Subgroup (BarInf L)), K₁.map (MulAut.conj w).toMonoidHom = K₂) ∨
        (UC22NoSwapInput p (P : Subgroup (BarInf L)) K₁ K₂ ∧ (5 ≤ p ∨ ¬ p ∣ Nat.card c.B0)))
    (huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x →
        orderOf x ≠ p → K = K') : False :=
  uc22s2112r34_false_swap_core_of hKS hKC hFC hσ hH c hL hBN hfaith hp hp2 hadm ht hq7 hX hno
    hree hpN hinn hπN hr hrB hr5 hrp hpair hswap (fun _ => False)
    (fun _ _ _ _ _ _ _ _ => id) fun K K' hK hK' x hx h₁ h₂ h₃ =>
      Or.inl (huniq K K' hK hK' x hx h₁ h₂ h₃)

private theorem uc22s2112r34_false_of_fund_rank {D : Data G} {Ch : Choice2011 G}
    (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hLM : L ≤ D.M)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 7 ≤ p ^ f) (hpσ : p ∈ D.sig)
    (hMs : IsStronglyPEmbedded p D.M) {b : G} (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G))
    (hbp : (orderOf b).Prime) (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {K : Subgroup (BarInf L)}
    (hK : IsFundamentalOver (p ^ f) K)
    (hKb : K ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    (hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hfk, g, hg⟩ := uc22s2112r34_fund_onto_psl2 (by omega) hK
  obtain ⟨hs, hns, -, hdvd⟩ := uc22s2112r2_psl2_facts hp2 hk (by omega)
  have := hs
  refine uc22s2112r34_false_of_fixed hKF7 hH c hLM hpσ hMs hbB hb hbp hbN hpN hrank hKb hns g hg
    ((dvd_pow_self p (by omega)).trans hdvd) ?_
  rintro rfl ⟨e⟩
  have h7 : 7 ≤ 5 ^ k := hq.trans hfk
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k
    norm_num at h7
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h25 := (pow_dvd_pow 5 hk2).trans hdvd
  rw [Nat.card_congr e.toEquiv, h60] at h25
  norm_num at h25

theorem uc22s2112r34_false_swap_or_noswap (hKS : KFunSplit) (hKC : KFunCount)
    (hFC : K_FunCommute) {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n) (hq7 : 7 ≤ p ^ f)
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hswap : ∀ (P : Sylow 2 (BarInf L)) (K₁ K₂ : Subgroup (BarInf L)),
      K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) →
      K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) → K₁ ≠ K₂ →
      (∃ w ∈ (P : Subgroup (BarInf L)), K₁.map (MulAut.conj w).toMonoidHom = K₂) ∨
        UC22NoSwapInput p (P : Subgroup (BarInf L)) K₁ K₂)
    (huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x →
        orderOf x ≠ p → K = K' ∨ 2 ≤ Open.pRank p (centralizer ({x} : Set (BarInf L)))) :
    False := by
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  obtain ⟨r, hrπ, hrp, hr5, -⟩ := uc22s2112r34_exists_prime_mem_piSet hσ hH c hn3 hL hpσ
  have hpB0 : ¬ p ∣ Nat.card c.B0 := fun h => uc22s2112r34_not_mem_sig hσ hH c hL ⟨hp, h⟩ hpσ
  refine uc22s2112r34_false_swap_core_of hKS hKC hFC hσ hH c hL hBN hfaith hp hp2 hadm ht hq7
    hX hno hree hpN hinn hπN hrπ.1 hrπ.2 hr5 hrp (fun b hb hb1 K₁ K₂ hK₁ hK₂ _ hK12 hfix =>
      uc22s2112r34_swap_faithful_on hKF7 hH c hL hp hp2 hq7 hpσ hpN hMs hb hb1 hBN hπN hK₁ hK₂
        hK12 hfix)
    (fun P K₁ K₂ h₁ h₂ hne => (hswap P K₁ K₂ h₁ h₂ hne).imp_right fun h => ⟨h, Or.inr hpB0⟩)
    (fun x => 2 ≤ Open.pRank p (centralizer ({x} : Set (BarInf L)))) ?_ huniq
  intro b hb hbp y hy K hK hKy hrank
  refine uc22s2112r34_false_of_fund_rank hKF7 hH c hL.1.le hp hp2 hq7 hpσ hMs hb (hBN hb) hbp
    (hπN _ hbp (Subgroup.orderOf_dvd_natCard c.B0 hb)) hpN hK ?_ ?_
  · rw [← hy, uc22s2112r34_fixed_conj_eq]
    exact hKy
  · rw [← hy, uc22s2112r34_fixed_conj_eq]
    exact hrank

theorem uc22s2112r34_false_swap (hKS : KFunSplit) (hKC : KFunCount) (hFC : K_FunCommute)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n) (hq7 : 7 ≤ p ^ f)
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hswap : ∀ (P : Sylow 2 (BarInf L)) (K₁ K₂ : Subgroup (BarInf L)),
      K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) →
      K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) → K₁ ≠ K₂ →
      ∃ w ∈ (P : Subgroup (BarInf L)), K₁.map (MulAut.conj w).toMonoidHom = K₂)
    (huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x →
        orderOf x ≠ p → K = K') : False := by
  exact uc22s2112r34_false_swap_or_noswap hKS hKC hFC hσ hKF7 hH c hn3 hL hBN hfaith hp hp2
    hadm ht hq7 hX hno hree hpσ hpN hinn hπN
    (fun P K₁ K₂ h₁ h₂ hne => Or.inl (hswap P K₁ K₂ h₁ h₂ hne))
    fun K K' hK hK' x hx h₁ h₂ h₃ => Or.inl (huniq K K' hK hK' x hx h₁ h₂ h₃)

end Swap

end CFSG.LocalAnalysis.UniquenessCase.UC22
