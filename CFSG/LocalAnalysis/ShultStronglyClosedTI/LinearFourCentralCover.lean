module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open Matrix
open scoped commutatorElement IsMulCommutative Pointwise

universe u v w

theorem linearFourCover_pGroup_sylow_eq_top {H : Type u} [Group H]
    {p : ℕ} (hp : IsPGroup p H) (C : Sylow p H) : (C : Subgroup H) = ⊤ :=
  top_unique ((hp.to_subgroup ⊤).le_sylow_of_normal C)

variable {K : Type u} [Field K] {E : Type v} [Group E]

theorem four_field_linear_cover_kernel_card_le_two [Finite K] [CharP K 2]
    [Finite E] [Group.IsPerfect E] (hcard : Nat.card K = 4)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Sylow 2 η.ker := default
  let Q := linearCoverRootSylow 2 (by simpa using hcard)
  have hbound := central_cover_elementary_rank_two_sylow_kernel_bound
    η hsurj hcentral C Q linearCoverRoot_elementary
    (by change Nat.card (linearCoverRootSubgroup K) = 2 ^ 2
        rw [linearCoverRoot_card, hcard]
        norm_num)
  have hC := linearFourCover_pGroup_sylow_eq_top hp C
  rw [hC, Subgroup.card_top] at hbound
  exact hbound.2

theorem linearCoverPreimageSylow_card [Finite K] [CharP K 2] [Finite E]
    (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hp : IsPGroup 2 η.ker) :
    Nat.card (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E) =
      Nat.card η.ker * Nat.card K := by
  let P : Subgroup E := linearCoverPreimageSylow f hcard η hsurj hp
  let r := η.subgroupMap P
  have hmap : P.map η = linearCoverRootSubgroup K :=
    Subgroup.map_comap_eq_self_of_surjective hsurj _
  have hker : r.ker = η.ker.subgroupOf P := by
    ext a
    constructor
    · intro ha
      exact congrArg Subtype.val ha
    · intro ha
      exact Subtype.ext ha
  have hKP : η.ker ≤ P := by
    intro x hx
    change η x ∈ linearCoverRootSubgroup K
    change η x = 1 at hx
    rw [hx]
    exact Subgroup.one_mem _
  have hkcard : Nat.card r.ker = Nat.card η.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
  have h := Subgroup.card_ker_mul_card_of_surjective (η.subgroupMap_surjective P)
  rw [hkcard, hmap, linearCoverRoot_card] at h
  exact h.symm

theorem linearFourCover_order_eight_center_eq_derived {H : Type w}
    [Group H] [Finite H] (hcard : Nat.card H = 8)
    (hderivedcard : Nat.card (commutator H) = 2)
    (hcentral : commutator H ≤ Subgroup.center H) :
    Subgroup.center H = commutator H := by
  apply (Subgroup.eq_of_le_of_card_ge hcentral ?_).symm
  rw [hderivedcard]
  by_contra hlarge
  have hzlarge : 3 ≤ Nat.card (Subgroup.center H) := by omega
  have hprod := (Subgroup.center H).card_eq_card_quotient_mul_card_subgroup
  rw [hcard] at hprod
  have hqle : Nat.card (H ⧸ Subgroup.center H) ≤ 2 := by nlinarith
  have hqpos : 0 < Nat.card (H ⧸ Subgroup.center H) := Nat.card_pos
  have hq : Nat.card (H ⧸ Subgroup.center H) = 1 ∨
      Nat.card (H ⧸ Subgroup.center H) = 2 := by omega
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (H ⧸ Subgroup.center H) := isCyclic_of_card_dvd_prime
    (p := 2) (by rcases hq with hq | hq <;> simp [hq])
  let : IsMulCommutative H := isMulCommutative_of_isCyclic_quotient_center_self H
  rw [commutator_eq_bot, Subgroup.card_bot] at hderivedcard
  contradiction

theorem linearCoverPreimageSylow_centralizer_le [Finite K] [CharP K 2]
    (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hp : IsPGroup 2 η.ker) :
    Subgroup.centralizer
      (linearCoverPreimageSylow f hcard η hsurj hp : Set E) ≤
        (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E) := by
  intro x hx
  have hxJ : η x ∈ Subgroup.centralizer (linearCoverRootSubgroup K : Set _) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨a, ha⟩ := hsurj y
    have haP : a ∈ linearCoverPreimageSylow f hcard η hsurj hp := by
      change η a ∈ linearCoverRootSubgroup K
      rwa [ha]
    have h := Subgroup.mem_centralizer_iff.mp hx a haP
    simpa only [map_mul, ha] using congrArg η h
  rw [linearCover_root_centralizer] at hxJ
  exact hxJ

theorem linearFourCover_central_subgroup_conj_map {H : Type w} [Group H]
    (C : Subgroup H) (hcentral : C ≤ Subgroup.center H) (g : H) :
    C.map (MulAut.conj g).toMonoidHom = C := by
  have hfixed : ∀ c ∈ C, (MulAut.conj g) c = c := by
    intro c hc
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp (hcentral hc) g,
      mul_inv_cancel_right]
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj g) c = x at hcx
    rw [hfixed c hc] at hcx
    exact hcx ▸ hc
  · intro c hc
    exact Subgroup.mem_map.mpr ⟨c, hc, hfixed c hc⟩

theorem linearFourCover_centralizer_map_equiv {H : Type u} {J : Type w}
    [Group H] [Group J] (P : Subgroup H) (e : H ≃* J) :
    (Subgroup.centralizer (P : Set H)).map e.toMonoidHom =
      Subgroup.centralizer (P.map e.toMonoidHom : Set J) := by
  apply le_antisymm
  · simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (P : Set H) e.toMonoidHom
  · intro y hy
    apply Subgroup.mem_map.mpr
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp hy (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem linearFourCover_mapped_center_eq_centralizer {H : Type w} [Group H]
    (P : Subgroup H) (hle : Subgroup.centralizer (P : Set H) ≤ P) :
    (Subgroup.center P).map P.subtype = Subgroup.centralizer (P : Set H) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    change a.val = x at hax
    rw [← hax]
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha (⟨y, hy⟩ : P))
  · intro x hx
    have hxP := hle hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y.val y.property)

theorem four_field_linear_cover_root_preimage_data [Finite K] [CharP K 2]
    [Finite E] [Group.IsPerfect E] (hcard : Nat.card K = 4)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker)
    (hne : η.ker ≠ ⊥) :
    let P : Subgroup E := linearCoverPreimageSylow 2 (by simpa using hcard) η hsurj hp
    Nat.card P = 8 ∧ (commutator P).map P.subtype = η.ker ∧
      (Subgroup.center P).map P.subtype = η.ker ∧
        Subgroup.centralizer (P : Set E) = η.ker ∧ η.ker = Subgroup.center E := by
  let hsize : Nat.card K = 2 ^ 2 := by simpa using hcard
  let P : Subgroup E := linearCoverPreimageSylow 2 hsize η hsurj hp
  change Nat.card P = 8 ∧ (commutator P).map P.subtype = η.ker ∧
    (Subgroup.center P).map P.subtype = η.ker ∧
      Subgroup.centralizer (P : Set E) = η.ker ∧ η.ker = Subgroup.center E
  have hbound := four_field_linear_cover_kernel_card_le_two hcard η hsurj hcentral hp
  have hnontrivial := η.ker.one_lt_card_iff_ne_bot.mpr hne
  have hCcard : Nat.card η.ker = 2 := by omega
  have hPcard : Nat.card P = 8 := by
    rw [linearCoverPreimageSylow_card, hCcard, hcard]
  have hderived : (commutator P).map P.subtype = η.ker :=
    linearCover_sylow_derived_eq_kernel 2 hsize η hsurj hcentral hp
  have hdcard : Nat.card (commutator P) = 2 := by
    rw [← Subgroup.card_map_of_injective (K := commutator P) P.subtype_injective,
      hderived, hCcard]
  have hdcentral : commutator P ≤ Subgroup.center P := by
    intro a ha
    have haC : a.val ∈ η.ker :=
      hderived ▸ Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hcentral haC) b.val))
  have hcenter : (Subgroup.center P).map P.subtype = η.ker := by
    rw [linearFourCover_order_eight_center_eq_derived hPcard hdcard hdcentral]
    exact hderived
  have hcle : Subgroup.centralizer (P : Set E) ≤ P :=
    linearCoverPreimageSylow_centralizer_le 2 hsize η hsurj hp
  have hcentralizer : Subgroup.centralizer (P : Set E) = η.ker :=
    (linearFourCover_mapped_center_eq_centralizer P hcle).symm.trans hcenter
  have hglobal : η.ker = Subgroup.center E := by
    apply le_antisymm hcentral
    rw [← hcentralizer]
    exact Subgroup.center_le_centralizer _
  exact ⟨hPcard, hderived, hcenter, hcentralizer, hglobal⟩

theorem four_field_linear_central_two_cover_sylow_centralizer [Finite K] [CharP K 2]
    [Finite E] [Group.IsPerfect E] (hcard : Nat.card K = 4)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 ∧ (η.ker ≠ ⊥ → ∀ R : Sylow 2 E,
      Nat.card (R : Subgroup E) = 8 ∧
        (commutator (R : Subgroup E)).map (R : Subgroup E).subtype = η.ker ∧
          (Subgroup.center (R : Subgroup E)).map (R : Subgroup E).subtype = η.ker ∧
            Subgroup.centralizer (R : Set E) = η.ker ∧ η.ker = Subgroup.center E) := by
  refine ⟨four_field_linear_cover_kernel_card_le_two hcard η hsurj hcentral hp, ?_⟩
  intro hne R
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := linearCoverPreimageSylow 2 (by simpa using hcard) η hsurj hp
  obtain ⟨hPcard, hPderived, hPcenter, hPcentralizer, hglobal⟩ :=
    four_field_linear_cover_root_preimage_data hcard η hsurj hcentral hp hne
  change Nat.card (P : Subgroup E) = 8 at hPcard
  change (commutator (P : Subgroup E)).map (P : Subgroup E).subtype = η.ker at hPderived
  change Subgroup.centralizer ((P : Subgroup E) : Set E) = η.ker at hPcentralizer
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P R
  let e := MulAut.conj g
  have hRmap : (P : Subgroup E).map e.toMonoidHom = (R : Subgroup E) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hRcard : Nat.card (R : Subgroup E) = 8 := by
    rw [← hRmap, Subgroup.card_map_of_injective e.injective]
    exact hPcard
  have hfixed : η.ker.map e.toMonoidHom = η.ker :=
    linearFourCover_central_subgroup_conj_map η.ker hcentral g
  have hRderived : (commutator (R : Subgroup E)).map (R : Subgroup E).subtype = η.ker := by
    rw [Subgroup.map_subtype_commutator, ← hRmap, ← Subgroup.map_commutator,
      ← Subgroup.map_subtype_commutator, hPderived, hfixed]
  have hRcentralizer : Subgroup.centralizer (R : Set E) = η.ker := by
    change Subgroup.centralizer ((R : Subgroup E) : Set E) = η.ker
    rw [← hRmap, ← linearFourCover_centralizer_map_equiv,
      hPcentralizer, hfixed]
  have hRcle : Subgroup.centralizer (R : Set E) ≤ (R : Subgroup E) := by
    rw [hRcentralizer]
    exact central_pSubgroup_le_sylow R η.ker hcentral hp
  have hRcenter : (Subgroup.center (R : Subgroup E)).map (R : Subgroup E).subtype = η.ker :=
    (linearFourCover_mapped_center_eq_centralizer _ hRcle).trans hRcentralizer
  exact ⟨hRcard, hRderived, hRcenter, hRcentralizer, hglobal⟩

theorem four_field_linear_central_two_cover_full {F : Type} [Field F] [Finite F]
    [CharP F 2] [Finite E] [Group.IsPerfect E] (hcard : Nat.card F = 4)
    (η : E →* GLAProj (GLASLGroup (Fin 2) F)) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 ∧ (η.ker ≠ ⊥ → ∀ P : Sylow 2 E,
      Nat.card (P : Subgroup E) = 8 ∧
        (commutator (P : Subgroup E)).map (P : Subgroup E).subtype = η.ker ∧
          (Subgroup.center (P : Subgroup E)).map (P : Subgroup E).subtype = η.ker ∧
            Subgroup.centralizer (P : Set E) = η.ker ∧ η.ker = Subgroup.center E) := by
  let eJ := linearCover_glaEquivSL (F := F)
  let φ := eJ.toMonoidHom.comp η
  have hker : φ.ker = η.ker := by
    ext x
    change eJ (η x) = 1 ↔ η x = 1
    exact eJ.map_eq_one_iff
  have h := four_field_linear_central_two_cover_sylow_centralizer hcard φ
    (eJ.surjective.comp hsurj) (hker.symm ▸ hcentral) (hker.symm ▸ hp)
  rwa [hker] at h

end CFSG.ShultStronglyClosedTI
