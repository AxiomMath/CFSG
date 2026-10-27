module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.GroupTheory.ABGLocalTools.RelativeStability

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem IsOmegaPlus.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsOmegaPlus X n a) : IsOmegaPlus Y n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem IsOmegaMinus.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsOmegaMinus X n a) : IsOmegaMinus Y n a := by
  obtain ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e.symm.trans e'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem IsL2Square.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsL2Square X n) : IsL2Square Y n := by
  obtain ⟨A, B, hA, hB, ⟨e'⟩, hLA, hLB⟩ := h
  exact ⟨A, B, hA, hB, ⟨e.symm.trans e'⟩, hLA, hLB⟩

private theorem isPGroup_quotient_of_pow_two_mem {X : Type} [Group X]
    {C K : Subgroup X} [C.Normal]
    (hpow : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C) :
    IsPGroup 2 (K ⧸ C.subgroupOf K) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf K) q
  obtain ⟨a, ha⟩ := hpow k k.2
  refine ⟨a, ?_⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (k ^ 2 ^ a)).mpr ha

private theorem isNilpotent_of_pow_two_mem_of_le_center {X : Type} [Group X] [Finite X]
    {C K : Subgroup X} (hcenter : C ≤ Subgroup.center X)
    (hpow : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C) : Group.IsNilpotent K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCnormal : C.Normal := Subgroup.normal_of_le_center hcenter
  let π : K →* K ⧸ C.subgroupOf K := QuotientGroup.mk' (C.subgroupOf K)
  have hquot : IsPGroup 2 (K ⧸ C.subgroupOf K) :=
    isPGroup_quotient_of_pow_two_mem hpow
  haveI : Group.IsNilpotent (K ⧸ C.subgroupOf K) := hquot.isNilpotent
  have hkerπ : π.ker ≤ Subgroup.center K := by
    intro x hx
    have hxC : (x : X) ∈ C := by
      have hx' : x ∈ C.subgroupOf K := by simpa [π, QuotientGroup.ker_mk'] using hx
      exact hx'
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcenter hxC) (y : X))
  exact Subgroup.isNilpotent_of_ker_le_center π hkerπ

private theorem odd_card_of_pCore_eq_bot_of_isNilpotent {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] [Group.IsNilpotent K]
    (hbot : CFSG.pCore 2 X = ⊥) : Odd (Nat.card K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 K))
  have hPle : ((P : Subgroup K).map K.subtype) ≤ CFSG.pCore 2 X :=
    Sylow.map_le_pCore (N := K) inferInstance inferInstance 2 P
  have hPbot : (P : Subgroup K).map K.subtype = ⊥ := by
    rw [hbot] at hPle
    exact eq_bot_iff.mpr hPle
  have hPsub : (P : Subgroup K) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup K)) K.subtype_injective).mp hPbot
  have hcardP : Nat.card (P : Subgroup K) = 1 := by
    rw [hPsub]
    simp
  have hnot2 : ¬ 2 ∣ Nat.card K := by
    intro h2
    have hdvd : 2 ∣ Nat.card (P : Subgroup K) := Sylow.dvd_card_of_dvd_card P h2
    rw [hcardP] at hdvd
    omega
  exact Nat.not_even_iff_odd.mp fun he => hnot2 he.two_dvd

private theorem le_of_pow_two_mem_of_odd_card {X : Type} [Group X] [Finite X]
    {C K : Subgroup X} (hcenter : C ≤ Subgroup.center X)
    (hpow : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C)
    (hodd : Odd (Nat.card K)) : K ≤ C := by
  haveI hCnormal : C.Normal := Subgroup.normal_of_le_center hcenter
  have hquot : IsPGroup 2 (K ⧸ C.subgroupOf K) :=
    isPGroup_quotient_of_pow_two_mem hpow
  have hqodd : Odd (Nat.card (K ⧸ C.subgroupOf K)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card (C.subgroupOf K))
  have hq1 : Nat.card (K ⧸ C.subgroupOf K) = 1 := by
    rcases hquot.card_eq_or_dvd with h | h
    · exact h
    · exact absurd h hqodd.not_two_dvd_nat
  have hsub : Subsingleton (K ⧸ C.subgroupOf K) := (Nat.card_eq_one_iff_unique.mp hq1).1
  intro x hx
  have hxq : QuotientGroup.mk' (C.subgroupOf K) ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : K)).mp hxq

theorem eq_of_pow_two_mem_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    {C K : Subgroup X} [K.Normal] (hCK : C ≤ K)
    (hcenter : C ≤ Subgroup.center X)
    (hpow : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C)
    (hbot : CFSG.pCore 2 X = ⊥) : K = C ∧ Odd (Nat.card C) := by
  haveI hnil : Group.IsNilpotent K :=
    isNilpotent_of_pow_two_mem_of_le_center hcenter hpow
  have hoddK : Odd (Nat.card K) :=
    odd_card_of_pCore_eq_bot_of_isNilpotent (K := K) hbot
  have hKC : K ≤ C := le_of_pow_two_mem_of_odd_card hcenter hpow hoddK
  exact ⟨le_antisymm hKC hCK, Odd.of_dvd_nat hoddK (Subgroup.card_dvd_of_le hCK)⟩

section Transfer

variable {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]

theorem pCore_le_comap_of_surjective {X Y : Type} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) :
    CFSG.pCore 2 X ≤ (CFSG.pCore 2 Y).comap f :=
  Subgroup.map_le_iff_le_comap.mp
    (CFSG.ABGLocalTools.map_pCore_le_of_surjective (p := 2) f hf)

theorem image_ker_le_center_of_commutator_le {X Y : Type} [Group X] [Group Y]
    {N : Subgroup X} [N.Normal] {f : X →* Y}
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ N) :
    f.ker.map (QuotientGroup.mk' N) ≤ Subgroup.center (X ⧸ N) := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
  have hcomm : ⁅f.ker, (⊤ : Subgroup X)⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    simpa [commutatorElement_def] using hker x hx y
  have hNmap : N.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (by simpa [π] using (QuotientGroup.ker_mk' N).symm)
  have hmap : (⁅f.ker, (⊤ : Subgroup X)⁆).map π ≤ N.map π := Subgroup.map_mono hcomm
  rw [hNmap, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ] at hmap
  exact eq_bot_iff.mpr hmap

theorem pow_two_mem_map_of_isPGroup {X Y : Type} [Group X] [Group Y]
    {N : Subgroup X} [N.Normal] {P : Subgroup Y} (f : X →* Y)
    (hP : IsPGroup 2 P) :
    ∀ k ∈ (P.comap f).map (QuotientGroup.mk' N),
      ∃ a : ℕ, k ^ (2 ^ a) ∈ f.ker.map (QuotientGroup.mk' N) := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
  obtain ⟨a, ha⟩ := hP ⟨f x, hx⟩
  have hxker : x ^ (2 ^ a) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have ha' : (f x) ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    simpa [map_pow] using ha'
  refine ⟨a, ?_⟩
  rw [← map_pow]
  exact Subgroup.mem_map.mpr ⟨x ^ (2 ^ a), hxker, rfl⟩

noncomputable def quotientQuotientEquivQuotientOfSurjective
    {X Y : Type} [Group X] [Group Y] {N : Subgroup X} [N.Normal]
    {P : Subgroup Y} [P.Normal] (f : X →* Y) (hf : Function.Surjective f)
    (hNleM : N ≤ P.comap f) :
    (X ⧸ N) ⧸ (P.comap f).map (QuotientGroup.mk' N) ≃* Y ⧸ P := by
  let g : X →* Y ⧸ P := (QuotientGroup.mk' P).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective P).comp hf
  have hgker : g.ker = P.comap f := by
    ext x
    simp [g, MonoidHom.mem_ker, Subgroup.mem_comap, QuotientGroup.eq_one_iff]
  exact (QuotientGroup.quotientQuotientEquivQuotient N (P.comap f) hNleM).trans
    (QuotientGroup.liftEquiv (P.comap f) hg hgker.symm)

theorem comap_pCore_eq_of_surjective_of_schur (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hSchur : ∀ (Xb : Type) [Group Xb] [Finite Xb] (K : Subgroup Xb) [K.Normal],
      ⁅(⊤ : Subgroup Xb), (⊤ : Subgroup Xb)⁆ = ⊤ → K ≤ Subgroup.center Xb →
      Odd (Nat.card ↥K) →
      Nonempty (Xb ⧸ K ≃* Y ⧸ CFSG.pCore 2 Y) → K = ⊥) :
    (CFSG.pCore 2 Y).comap f = CFSG.pCore 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := CFSG.pCore 2 X
  let P : Subgroup Y := CFSG.pCore 2 Y
  have hNbot : CFSG.pCore 2 (X ⧸ N) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := X)
  have hNleM : N ≤ P.comap f := pCore_le_comap_of_surjective f hf
  haveI hMn : (P.comap f).Normal := (CFSG.pCore_normal (p := 2) (G := Y)).comap f
  let C : Subgroup (X ⧸ N) := f.ker.map (QuotientGroup.mk' N)
  let K : Subgroup (X ⧸ N) := (P.comap f).map (QuotientGroup.mk' N)
  have hKnormal : K.Normal :=
    hMn.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hCK : C ≤ K := Subgroup.map_mono (by
    rw [← MonoidHom.comap_bot (f := f)]
    exact Subgroup.comap_mono bot_le)
  have hcenterC : C ≤ Subgroup.center (X ⧸ N) :=
    image_ker_le_center_of_commutator_le (N := N) hker
  have hpowK : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C :=
    pow_two_mem_map_of_isPGroup (N := N) (P := P) f
      (CFSG.pCore_isPGroup (p := 2) (G := Y))
  haveI : K.Normal := hKnormal
  obtain ⟨hKC, hCodd⟩ :=
    eq_of_pow_two_mem_of_pCore_eq_bot (C := C) (K := K) hCK hcenterC hpowK hNbot
  rw [← hKC] at hcenterC hCodd
  have hperfectX : commutator X = ⊤ := by rwa [_root_.commutator_def]
  haveI hPerfX : Group.IsPerfect X := Group.IsPerfect.mk hperfectX
  haveI hPerfXbar : Group.IsPerfect (X ⧸ N) := inferInstance
  have hcommXbar : ⁅(⊤ : Subgroup (X ⧸ N)), (⊤ : Subgroup (X ⧸ N))⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have e : (X ⧸ N) ⧸ K ≃* Y ⧸ P :=
    quotientQuotientEquivQuotientOfSurjective (N := N) (P := P) f hf hNleM
  have hKbot : K = ⊥ := hSchur (X ⧸ N) K hcommXbar hcenterC hCodd ⟨e⟩
  have hMleN : P.comap f ≤ N := by
    have hKmap : (P.comap f).map (QuotientGroup.mk' N) = ⊥ := by
      simpa only [K] using hKbot
    have hle : P.comap f ≤ (QuotientGroup.mk' N).ker :=
      (Subgroup.map_eq_bot_iff (H := P.comap f) (f := QuotientGroup.mk' N)).mp hKmap
    simpa [N, QuotientGroup.ker_mk'] using hle
  exact le_antisymm hMleN hNleM

theorem comap_pCore_eq_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurL2) {j : ℕ}
    (hshape : IsL2 (Y ⧸ CFSG.pCore 2 Y) j ∨
      IsL2Square (Y ⧸ CFSG.pCore 2 Y) j) :
    (CFSG.pCore 2 Y).comap f = CFSG.pCore 2 X := by
  refine comap_pCore_eq_of_surjective_of_schur f hf hperfect hker ?_
  intro Xb _ _ K _ hcomm hcenter hodd ⟨e⟩
  have hshapeX : IsL2 (Xb ⧸ K) j ∨ IsL2Square (Xb ⧸ K) j := by
    rcases hshape with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
    · exact Or.inr (IsL2Square.of_mulEquiv e.symm h)
  exact hS Xb j hcomm K hcenter hodd hshapeX

noncomputable def quotientPCoreEquivOfSurjective (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurL2) {j : ℕ}
    (hshape : IsL2 (Y ⧸ CFSG.pCore 2 Y) j ∨
      IsL2Square (Y ⧸ CFSG.pCore 2 Y) j) :
    (X ⧸ CFSG.pCore 2 X) ≃* (Y ⧸ CFSG.pCore 2 Y) := by
  let N : Subgroup X := CFSG.pCore 2 X
  let P : Subgroup Y := CFSG.pCore 2 Y
  let g : X →* Y ⧸ P := (QuotientGroup.mk' P).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective P).comp hf
  have hgker : g.ker = P.comap f := by
    ext x
    simp [g, MonoidHom.mem_ker, Subgroup.mem_comap, QuotientGroup.eq_one_iff]
  have hmain := comap_pCore_eq_of_surjective f hf hperfect hker hS hshape
  exact QuotientGroup.liftEquiv N hg (hmain.symm.trans hgker.symm)

theorem isL2_quotientPCore_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurL2) {j : ℕ} (h : IsL2 (Y ⧸ CFSG.pCore 2 Y) j) :
    IsL2 (X ⧸ CFSG.pCore 2 X) j :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (quotientPCoreEquivOfSurjective f hf hperfect hker hS (Or.inl h)).symm h

theorem isL2Square_quotientPCore_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurL2) {j : ℕ} (h : IsL2Square (Y ⧸ CFSG.pCore 2 Y) j) :
    IsL2Square (X ⧸ CFSG.pCore 2 X) j :=
  IsL2Square.of_mulEquiv
    (quotientPCoreEquivOfSurjective f hf hperfect hker hS (Or.inr h)).symm h

theorem comap_pCore_eq_of_pCore_eq_bot (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurL2) {j : ℕ}
    (hshape : IsL2 (Y ⧸ CFSG.pCore 2 Y) j ∨
      IsL2Square (Y ⧸ CFSG.pCore 2 Y) j)
    (hbot : CFSG.pCore 2 Y = ⊥) :
    f.ker = CFSG.pCore 2 X ∧ Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* Y) := by
  have hmain := comap_pCore_eq_of_surjective f hf hperfect hker hS hshape
  refine ⟨?_, ?_⟩
  · rw [← hmain, hbot, MonoidHom.comap_bot]
  · have e := quotientPCoreEquivOfSurjective f hf hperfect hker hS hshape
    exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      QuotientGroup.quotientBot)⟩

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.UC22
