module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.BenderSylow

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem sz_data {L T : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    Nat.card ↥(imageOTwoQuot L T) = (2 ^ (2 * a + 1)) ^ 2 ∧
      Nat.card ↥(imageOTwoQuot L T ⊓ Subgroup.centralizer
        (imageOTwoQuot L T : Set (oTwoQuot ↥L))) = 2 ^ (2 * a + 1) ∧
      (∀ z : oTwoQuot ↥L, z ∈ imageOTwoQuot L T ⊓ Subgroup.centralizer
          (imageOTwoQuot L T : Set (oTwoQuot ↥L)) ↔
        z ∈ imageOTwoQuot L T ∧ z * z = 1) ∧
      (∀ s ∈ imageOTwoQuot L T, s ^ 2 ∈ imageOTwoQuot L T ⊓ Subgroup.centralizer
          (imageOTwoQuot L T : Set (oTwoQuot ↥L))) ∧
      (∀ s ∈ imageOTwoQuot L T, ∀ t ∈ imageOTwoQuot L T, ⁅s, t⁆ ∈
        imageOTwoQuot L T ⊓ Subgroup.centralizer
          (imageOTwoQuot L T : Set (oTwoQuot ↥L))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_imageOTwoQuot hT
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  let e : oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a K :=
    (Classical.choice hSz).trans (Classical.choice
      (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a))
  obtain ⟨h1, h2, h3, h4⟩ := CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center ha hK e S
  obtain ⟨-, h5⟩ := sz_center_card_and_mem ha e S
  rw [← hS]
  exact ⟨h1, h2, h5, h3, h4⟩

private theorem mk_mem_imageOTwoQuot_of_mem {L T : Subgroup G} (hTL : T ≤ L) {x : G}
    (hx : x ∈ T) :
    (QuotientGroup.mk ⟨x, hTL hx⟩ : oTwoQuot ↥L) ∈ imageOTwoQuot L T :=
  mem_imageOTwoQuot_iff.mpr ⟨x, hTL hx, hx, rfl⟩

private theorem mk_mul_self_eq_one_of_sq_mem {L T : Subgroup G} (hTL : T ≤ L) {x : G}
    (hx : x ∈ T) (hxx : x * x ∈ pCoreOf 2 L) :
    (QuotientGroup.mk ⟨x, hTL hx⟩ : oTwoQuot ↥L) *
      (QuotientGroup.mk ⟨x, hTL hx⟩ : oTwoQuot ↥L) = 1 := by
  rw [← QuotientGroup.mk_mul]
  exact (mk_eq_one_iff_mem_pCoreOf _).mpr (by
    simpa [Subgroup.coe_mul, pow_two] using hxx)

theorem commutator_mul_self_mem_pCoreOf_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    {x y : G} (hx : x ∈ T) (hy : y ∈ T) :
    ⁅x, y⁆ * ⁅x, y⁆ ∈ pCoreOf 2 L := by
  classical
  obtain ⟨-, -, hZmem, -, hcommZ⟩ := sz_data ha hSz hT
  have hTL : T ≤ L := hT.le
  let xL : ↥L := ⟨x, hTL hx⟩
  let yL : ↥L := ⟨y, hTL hy⟩
  have hxTq : (QuotientGroup.mk xL : oTwoQuot ↥L) ∈ imageOTwoQuot L T :=
    mk_mem_imageOTwoQuot_of_mem hTL hx
  have hyTq : (QuotientGroup.mk yL : oTwoQuot ↥L) ∈ imageOTwoQuot L T :=
    mk_mem_imageOTwoQuot_of_mem hTL hy
  have hmemT : ⁅x, y⁆ ∈ T :=
    Subgroup.commutator_le_of_le le_rfl le_rfl (Subgroup.commutator_mem_commutator hx hy)
  have hmemL : ⁅x, y⁆ ∈ L := hTL hmemT
  let cL : ↥L := ⟨⁅x, y⁆, hmemL⟩
  have hcZ : (QuotientGroup.mk cL : oTwoQuot ↥L) ∈
      imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) := by
    have hq : (QuotientGroup.mk cL : oTwoQuot ↥L) =
        ⁅(QuotientGroup.mk xL : oTwoQuot ↥L), (QuotientGroup.mk yL : oTwoQuot ↥L)⁆ := by
      have hc : cL = ⁅xL, yL⁆ := rfl
      rw [hc]
      exact map_commutatorElement (QuotientGroup.mk' (pCore 2 ↥L)) xL yL
    rw [hq]
    exact hcommZ _ hxTq _ hyTq
  have hsq : (QuotientGroup.mk cL : oTwoQuot ↥L) * (QuotientGroup.mk cL : oTwoQuot ↥L) = 1 :=
    ((hZmem _).mp hcZ).2
  have hsq' : (QuotientGroup.mk (cL * cL) : oTwoQuot ↥L) = 1 := by
    rw [QuotientGroup.mk_mul]
    exact hsq
  have h := (mk_eq_one_iff_mem_pCoreOf (cL * cL)).mp hsq'
  simpa [cL, Subgroup.coe_mul] using h

private theorem commutator_le_sylow_and_normalizer {L T : Subgroup G}
    (hT : IsSylowTwoOf T L) :
    ∃ S : Sylow 2 (oTwoQuot ↥L),
      (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T ∧
        ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ ≤ (S : Subgroup (oTwoQuot ↥L)) ∧
        Subgroup.normalizer ((S : Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L)) ≤
          Subgroup.normalizer ((⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ :
            Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L)) := by
  obtain ⟨S, hS⟩ := exists_sylow_imageOTwoQuot hT
  refine ⟨S, hS, ?_, ?_⟩
  · rw [hS]
    exact Subgroup.commutator_le_of_le le_rfl le_rfl
  · rw [hS]
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
    rw [Subgroup.map_commutator, hn]

private theorem commutator_eq_center_of_sz {L T : Subgroup G}
    {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ =
      imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTcard, hZcard, -, -, hcommZ⟩ := sz_data ha hSz hT
  obtain ⟨S, hS, hWS, hWN⟩ := commutator_le_sylow_and_normalizer hT
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  let e : oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a K :=
    (Classical.choice hSz).trans (Classical.choice
      (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a))
  have hclass := CFSG.RankThree.S4Free.Suzuki.eq_bot_or_eq_center_or_eq_sylow ha hK e S hWS hWN
  rw [hS] at hclass
  have hcard_ne : (2 ^ (2 * a + 1)) ^ 2 ≠ 2 ^ (2 * a + 1) := by
    have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hWne_bot : ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ ≠ ⊥ := by
    intro hbot
    have hle : imageOTwoQuot L T ≤
        Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have heq : imageOTwoQuot L T =
        imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
      le_antisymm (le_inf le_rfl hle) inf_le_left
    apply hcard_ne
    rw [← hTcard, ← hZcard]
    exact congrArg (fun X : Subgroup (oTwoQuot ↥L) => Nat.card ↥X) heq
  have hWleZ : ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ ≤
      imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
    Subgroup.commutator_le.mpr fun s hs t ht => hcommZ s hs t ht
  have hWne_top : ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ ≠ imageOTwoQuot L T := by
    intro hEq
    have hle : imageOTwoQuot L T ≤
        imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) := by
      intro x hx
      rw [← hEq] at hx
      exact hWleZ hx
    have heq : imageOTwoQuot L T =
        imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
      le_antisymm hle inf_le_left
    apply hcard_ne
    rw [← hTcard, ← hZcard]
    exact congrArg (fun X : Subgroup (oTwoQuot ↥L) => Nat.card ↥X) heq
  rcases hclass with h | h | h
  · exact absurd h hWne_bot
  · exact h
  · exact absurd h hWne_top

theorem mem_commutator_sup_pCoreOf_of_sq_mem_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    {x : G} (hx : x ∈ T) (hxx : x * x ∈ pCoreOf 2 L) :
    x ∈ ⁅T, T⁆ ⊔ pCoreOf 2 L := by
  classical
  obtain ⟨-, -, hZmem, -, -⟩ := sz_data ha hSz hT
  have hTL : T ≤ L := hT.le
  have hWZ := commutator_eq_center_of_sz ha hSz hT
  have hxZ : (QuotientGroup.mk ⟨x, hTL hx⟩ : oTwoQuot ↥L) ∈
      imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
    (hZmem _).mpr ⟨mk_mem_imageOTwoQuot_of_mem hTL hx,
      mk_mul_self_eq_one_of_sq_mem hTL hx hxx⟩
  have hsub : ⁅T, T⁆.subgroupOf L = ⁅T.subgroupOf L, T.subgroupOf L⁆ := by
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    simp only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTL,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hTL hTL)]
  have himg : imageOTwoQuot L ⁅T, T⁆ =
      ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ := by
    unfold imageOTwoQuot
    rw [hsub, Subgroup.map_commutator]
  exact mem_sup_pCoreOf_of_mk_mem (M := L) (A := ⁅T, T⁆) (x := ⟨x, hTL hx⟩)
    (by rw [himg, hWZ]; exact hxZ)

theorem exists_commutator_not_mem_pCoreOf_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    ∃ x ∈ T, ∃ y ∈ T, ⁅x, y⁆ ∉ pCoreOf 2 L := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hTcard, hZcard, -, -, -⟩ := sz_data ha hSz hT
  have hbot : ⁅imageOTwoQuot L T, imageOTwoQuot L T⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    obtain ⟨x, hxL, hxT, rfl⟩ := mem_imageOTwoQuot_iff.mp ha
    obtain ⟨y, hyL, hyT, rfl⟩ := mem_imageOTwoQuot_iff.mp hb
    have hxy : ⁅x, y⁆ ∈ pCoreOf 2 L := h x hxT y hyT
    have h1 : (QuotientGroup.mk (⟨⁅x, y⁆, pCoreOf_le 2 L hxy⟩ : ↥L) : oTwoQuot ↥L) = 1 :=
      (mk_eq_one_iff_mem_pCoreOf _).mpr hxy
    have h2 : (QuotientGroup.mk (⟨⁅x, y⁆, pCoreOf_le 2 L hxy⟩ : ↥L) : oTwoQuot ↥L) =
        ⁅(QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L),
          (QuotientGroup.mk ⟨y, hyL⟩ : oTwoQuot ↥L)⁆ := by
      have hc : (⟨⁅x, y⁆, pCoreOf_le 2 L hxy⟩ : ↥L) =
          ⁅(⟨x, hxL⟩ : ↥L), (⟨y, hyL⟩ : ↥L)⁆ := rfl
      rw [hc]
      exact map_commutatorElement (QuotientGroup.mk' (pCore 2 ↥L))
        (⟨x, hxL⟩ : ↥L) (⟨y, hyL⟩ : ↥L)
    exact h2 ▸ h1
  have hle : imageOTwoQuot L T ≤
      Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have heq : imageOTwoQuot L T =
      imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) :=
    le_antisymm (le_inf le_rfl hle) inf_le_left
  have hcard : Nat.card ↥(imageOTwoQuot L T) =
      Nat.card ↥(imageOTwoQuot L T ⊓
        Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) :=
    congrArg (fun X : Subgroup (oTwoQuot ↥L) => Nat.card ↥X) heq
  rw [hTcard, hZcard] at hcard
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

theorem exists_sq_mem_not_mem_pCoreOf_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    ∃ z ∈ T, z * z ∈ pCoreOf 2 L ∧ z ∉ pCoreOf 2 L := by
  classical
  obtain ⟨-, hZcard, hZmem, -, -⟩ := sz_data ha hSz hT
  have hTL : T ≤ L := hT.le
  have hZne : imageOTwoQuot L T ⊓ Subgroup.centralizer
      (imageOTwoQuot L T : Set (oTwoQuot ↥L)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZcard
    have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hwZ : (w : oTwoQuot ↥L) ∈ imageOTwoQuot L T ⊓
      Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) := w.2
  obtain ⟨z, hzL, hzT, hzw⟩ := mem_imageOTwoQuot_iff.mp ((hZmem w).mp hwZ).1
  refine ⟨z, hzT, ?_, ?_⟩
  · have hsq : (QuotientGroup.mk ((⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩) : oTwoQuot ↥L) = 1 := by
      rw [QuotientGroup.mk_mul, hzw]
      exact ((hZmem w).mp hwZ).2
    have h := (mk_eq_one_iff_mem_pCoreOf ((⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩)).mp hsq
    simpa [Subgroup.coe_mul] using h
  · intro hzq
    exact hw1 (Subtype.ext (hzw ▸ (mk_eq_one_iff_mem_pCoreOf ⟨z, hzL⟩).mpr hzq))

private theorem sz_conj_mem_center {L T : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    {H : Subgroup G} (hHT : H ≤ normalizer (T : Set G))
    (hHL : H ≤ normalizer (L : Set G)) {z : G} (hzT : z ∈ T)
    (hzz : z * z ∈ pCoreOf 2 L) (hz : z ∉ pCoreOf 2 L) {k : G} (hkH : k ∈ H) :
    (QuotientGroup.mk ⟨k * z * k⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHL hkH) z).mp (hT.le hzT)⟩ :
          oTwoQuot ↥L) ∈
        imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) ∧
      (QuotientGroup.mk ⟨k * z * k⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHL hkH) z).mp (hT.le hzT)⟩ :
          oTwoQuot ↥L) ≠ 1 := by
  classical
  obtain ⟨-, -, hZmem, -, -⟩ := sz_data ha hSz hT
  have hmemT : k * z * k⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hHT hkH) z).mp hzT
  have hmemL : k * z * k⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hHL hkH) z).mp (hT.le hzT)
  have hsqpc : (k * z * k⁻¹) * (k * z * k⁻¹) ∈ pCoreOf 2 L := by
    have h1 : k * (z * z) * k⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp
        ((normalizer_le_normalizer_pCoreOf 2 L) (hHL hkH)) (z * z)).mp hzz
    have heq : (k * z * k⁻¹) * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
    rwa [heq]
  have hnotpc : k * z * k⁻¹ ∉ pCoreOf 2 L := by
    intro hk
    apply hz
    have hkN : k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (normalizer_le_normalizer_pCoreOf 2 L)
        ((Subgroup.normalizer (L : Set G)).inv_mem (hHL hkH))
    have hk' : k⁻¹ * (k * z * k⁻¹) * k ∈ pCoreOf 2 L := by
      simpa using (Subgroup.mem_normalizer_iff.mp hkN (k * z * k⁻¹)).mp hk
    have heq : k⁻¹ * (k * z * k⁻¹) * k = z := by group
    rwa [heq] at hk'
  refine ⟨?_, ?_⟩
  · refine (hZmem _).mpr ⟨mem_imageOTwoQuot_iff.mpr ⟨_, hmemL, hmemT, rfl⟩, ?_⟩
    rw [← QuotientGroup.mk_mul]
    exact (mk_eq_one_iff_mem_pCoreOf _).mpr (by
      simpa [Subgroup.coe_mul] using hsqpc)
  · intro hcon
    exact hnotpc ((mk_eq_one_iff_mem_pCoreOf _).mp hcon)

private theorem sz_conj_mk_injective {L T : Subgroup G}
    (hT : IsSylowTwoOf T L) {H : Subgroup G}
    (hHL : H ≤ normalizer (L : Set G)) {z : G} (hzT : z ∈ T)
    (hfree : ∀ k ∈ H, ⁅k, z⁆ ∈ pCoreOf 2 L → k = 1) :
    Function.Injective (fun k : ↥H =>
      (QuotientGroup.mk ⟨(k : G) * z * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHL k.2) z).mp (hT.le hzT)⟩ :
          oTwoQuot ↥L)) := by
  intro k1 k2 hq
  set a : ↥L := ⟨(k1 : G) * z * (k1 : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hHL k1.2) z).mp (hT.le hzT)⟩
  set b : ↥L := ⟨(k2 : G) * z * (k2 : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hHL k2.2) z).mp (hT.le hzT)⟩
  change (QuotientGroup.mk a : oTwoQuot ↥L) = (QuotientGroup.mk b : oTwoQuot ↥L) at hq
  have hc : ((a / b : ↥L) : G) ∈ pCoreOf 2 L :=
    (F1.mem_pCore_iff_coe (a / b)).mp (QuotientGroup.eq_iff_div_mem.mp hq)
  have hkN : (k2 : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (normalizer_le_normalizer_pCoreOf 2 L)
      ((Subgroup.normalizer (L : Set G)).inv_mem (hHL k2.2))
  have hconj : (k2 : G)⁻¹ * ((a / b : ↥L) : G) * (k2 : G) ∈ pCoreOf 2 L := by
    simpa using (Subgroup.mem_normalizer_iff.mp hkN ((a / b : ↥L) : G)).mp hc
  have heq : (k2 : G)⁻¹ * ((a / b : ↥L) : G) * (k2 : G) =
      ⁅(k2 : G)⁻¹ * (k1 : G), z⁆ := by
    rw [div_eq_mul_inv]
    simp only [a, b, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hcomm : ⁅(k2 : G)⁻¹ * (k1 : G), z⁆ ∈ pCoreOf 2 L := by
    rw [← heq]
    exact hconj
  have hhH : (k2 : G)⁻¹ * (k1 : G) ∈ H := H.mul_mem (H.inv_mem k2.2) k1.2
  have h1 : (k2 : G)⁻¹ * (k1 : G) = 1 := hfree _ hhH hcomm
  exact Subtype.ext (inv_mul_eq_one.mp h1).symm

theorem card_le_of_commutator_mem_imp_eq_one_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    {H : Subgroup G} (hHT : H ≤ normalizer (T : Set G))
    (hHL : H ≤ normalizer (L : Set G)) {z : G} (hzT : z ∈ T)
    (hzz : z * z ∈ pCoreOf 2 L) (hz : z ∉ pCoreOf 2 L)
    (hfree : ∀ k ∈ H, ⁅k, z⁆ ∈ pCoreOf 2 L → k = 1) :
    Nat.card H ≤ 2 ^ (2 * a + 1) - 1 := by
  classical
  obtain ⟨-, hZcard, -, -, -⟩ := sz_data ha hSz hT
  have hzL : z ∈ L := hT.le hzT
  let Z : Subgroup (oTwoQuot ↥L) :=
    imageOTwoQuot L T ⊓ Subgroup.centralizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))
  have hmemL : ∀ k : ↥H, (k : G) * z * (k : G)⁻¹ ∈ L := fun k =>
    (Subgroup.mem_normalizer_iff.mp (hHL k.2) z).mp hzL
  let φ : ↥H → {w : oTwoQuot ↥L // w ∈ Z ∧ w ≠ 1} := fun k =>
    ⟨QuotientGroup.mk ⟨(k : G) * z * (k : G)⁻¹, hmemL k⟩,
      (sz_conj_mem_center ha hSz hT hHT hHL hzT hzz hz k.2).1,
      (sz_conj_mem_center ha hSz hT hHT hHL hzT hzz hz k.2).2⟩
  have hφinj : Function.Injective φ := by
    intro k1 k2 hk
    exact sz_conj_mk_injective hT hHL hzT hfree (congrArg Subtype.val hk)
  have hcardle : Nat.card ↥H ≤ Nat.card {w : oTwoQuot ↥L // w ∈ Z ∧ w ≠ 1} :=
    Nat.card_le_card_of_injective φ hφinj
  have hIcard : Nat.card {w : oTwoQuot ↥L // w ∈ Z ∧ w ≠ 1} = 2 ^ (2 * a + 1) - 1 := by
    have h1 : Nat.card {w : oTwoQuot ↥L // w ∈ Z ∧ w ≠ 1} =
        Nat.card ↥((Z : Set (oTwoQuot ↥L)) \ {1}) := rfl
    rw [h1, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (show (1 : oTwoQuot ↥L) ∈ Z from Z.one_mem)]
    rw [← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hZcard
  rwa [hIcard] at hcardle

variable {L1 L2 S : Subgroup G}

private theorem frame_sz_data {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* Sz a) ∧
      pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) = Q1 L1 L2 S := by
  have hF : Hyp111 L1 L2 S := hfr.hF.1
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  exact ⟨isSylowTwoOf_sup_pCoreOf hF hS1,
    ⟨(oTwoQuotSupEquiv hF).trans (Classical.choice hfr.hSz)⟩, pCoreOf_sup_pCoreOf hF⟩

theorem commutator_mul_self_mem_Q1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) :
    ⁅s, s'⁆ * ⁅s, s'⁆ ∈ Q1 L1 L2 S := by
  obtain ⟨hT, hSz', hpc⟩ := frame_sz_data hfr
  have h := commutator_mul_self_mem_pCoreOf_of_sz hfr.ha hSz' hT hs hs'
  rwa [hpc] at h

theorem mem_commutator_sup_Q1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {s : G} (hs : s ∈ S) (hss : s * s ∈ Q1 L1 L2 S) :
    s ∈ ⁅S, S⁆ ⊔ Q1 L1 L2 S := by
  obtain ⟨hT, hSz', hpc⟩ := frame_sz_data hfr
  have h := mem_commutator_sup_pCoreOf_of_sq_mem_of_sz hfr.ha hSz' hT hs
    (by rw [hpc]; exact hss)
  rwa [hpc] at h

theorem exists_commutator_not_mem_Q1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ∃ s ∈ S, ∃ s' ∈ S, ⁅s, s'⁆ ∉ Q1 L1 L2 S := by
  obtain ⟨hT, hSz', hpc⟩ := frame_sz_data hfr
  obtain ⟨s, hs, s', hs', h⟩ := exists_commutator_not_mem_pCoreOf_of_sz hfr.ha hSz' hT
  exact ⟨s, hs, s', hs', by rwa [hpc] at h⟩

end CFSG.Quasithin.Stroth.Rq

end
