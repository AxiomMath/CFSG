module

public import CFSG.RankThree.GF2n.Parrott.CommutatorDetermined
public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Facts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def Kimage (h : Tim79a.ParrottHyp z) (K : Subgroup (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup (K.map (QuotientV.pi z)))

@[expose] noncomputable def Cimage (h : Tim79a.ParrottHyp z) (K : Subgroup (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup
      ((Subgroup.centralizer (K : Set (J z))).map (QuotientV.pi z)))

@[expose] noncomputable def CimageZpowers (h : Tim79a.ParrottHyp z) (j : J z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup
      ((Subgroup.centralizer ({j} : Set (J z))).map (QuotientV.pi z)))

@[expose] noncomputable def Zimage (h : Tim79a.ParrottHyp z) (j : J z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup ((Subgroup.zpowers j).map (QuotientV.pi z)))

@[expose] noncomputable def PiZimage (h : Tim79a.ParrottHyp z) (j : J z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup (Subgroup.zpowers (QuotientV.pi z j)))

theorem mem_Kimage (h : Tim79a.ParrottHyp z) (K : Subgroup (J z))
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    v ∈ Kimage h K ↔ ∃ k ∈ K, QuotientV.pi z k = Additive.toMul v := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  dsimp only [Kimage]
  rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]

theorem mem_Cimage (h : Tim79a.ParrottHyp z) (K : Subgroup (J z))
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    v ∈ Cimage h K ↔
      ∃ c ∈ Subgroup.centralizer (K : Set (J z)), QuotientV.pi z c = Additive.toMul v := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  dsimp only [Cimage]
  rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]

theorem mem_PiZimage (h : Tim79a.ParrottHyp z) (j : J z)
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    v ∈ PiZimage h j ↔
      Additive.toMul v ∈ Subgroup.zpowers (QuotientV.pi z j) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  dsimp only [PiZimage]
  rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem map_centralizer_eq_orthogonal (h : Tim79a.ParrottHyp z) (K : Subgroup (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Cimage h K = (commutatorBilinForm h).orthogonal (Kimage h K) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext x
  rw [mem_Cimage, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩ y hy
    rw [mem_Kimage] at hy
    obtain ⟨k, hk, hky⟩ := hy
    have hy' : y = Additive.ofMul (QuotientV.pi z k) := by
      rw [← ofMul_toMul y, hky]
    have hx' : x = Additive.ofMul (QuotientV.pi z c) := by
      rw [← ofMul_toMul x, hcx]
    rw [hy', hx', commutatorBilinForm_apply]
    exact (polarVZMod_pi_eq_zero_iff h k c).mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc k hk))
  · intro hx
    obtain ⟨c, hcπ⟩ := QuotientV.pi_surjective z (Additive.toMul x)
    refine ⟨c, ?_, hcπ⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hmem : Additive.ofMul (QuotientV.pi z k) ∈ Kimage h K :=
      (mem_Kimage h K _).mpr ⟨k, hk, rfl⟩
    have hb := hx (Additive.ofMul (QuotientV.pi z k)) hmem
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm,
      commutatorBilinForm_apply, ← hcπ] at hb
    exact Subtype.ext ((polarVZMod_pi_eq_zero_iff h k c).mp hb)

theorem map_centralizer_eq_orthogonal_zpowers (h : Tim79a.ParrottHyp z) (j : J z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    CimageZpowers h j = (commutatorBilinForm h).orthogonal (PiZimage h j) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hcent : CimageZpowers h j = Cimage h (Subgroup.zpowers j) := by
    dsimp only [CimageZpowers, Cimage]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have himg : Kimage h (Subgroup.zpowers j) = PiZimage h j := by
    dsimp only [Kimage, PiZimage]
    rw [MonoidHom.map_zpowers]
  rw [hcent, map_centralizer_eq_orthogonal h (Subgroup.zpowers j), himg]

theorem Zimage_eq_PiZimage (h : Tim79a.ParrottHyp z) (j : J z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Zimage h j = PiZimage h j := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  dsimp only [Zimage, PiZimage]
  rw [MonoidHom.map_zpowers]

theorem centralizer_centralizer_eq_sup_center (h : Tim79a.ParrottHyp z) {j : J z} :
    Subgroup.centralizer (Subgroup.centralizer ({j} : Set (J z))) =
      Subgroup.zpowers j ⊔ Subgroup.center (J z) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  haveI : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  let C : Subgroup (J z) := Subgroup.centralizer ({j} : Set (J z))
  let D : Subgroup (J z) := Subgroup.centralizer (C : Set (J z))
  have hKC : Kimage h C = CimageZpowers h j := by
    dsimp only [Kimage, CimageZpowers, C]
  have h2 : Kimage h C = (commutatorBilinForm h).orthogonal (PiZimage h j) := by
    rw [hKC]
    exact map_centralizer_eq_orthogonal_zpowers h j
  have hD : Cimage h C = PiZimage h j := by
    rw [map_centralizer_eq_orthogonal h C, h2]
    exact LinearMap.BilinForm.orthogonal_orthogonal
      (commutatorBilinForm_nondegenerate h) (commutatorBilinForm_isRefl h) (PiZimage h j)
  have hDz : Cimage h C = Zimage h j := hD.trans (Zimage_eq_PiZimage h j).symm
  have hDsub : D.map (QuotientV.pi z) = (Subgroup.zpowers j).map (QuotientV.pi z) := by
    apply (Subgroup.toAddSubgroup (G := QuotientV.V z)).injective
    have h := congrArg (fun S : Submodule (ZMod 2) (Additive (QuotientV.V z)) =>
      S.toAddSubgroup) hDz
    simpa [Cimage, Zimage, D] using h
  have hDle : D ≤ Subgroup.zpowers j ⊔ Subgroup.center (J z) := by
    intro d hd
    have hdimg : QuotientV.pi z d ∈ (Subgroup.zpowers j).map (QuotientV.pi z) := by
      rw [← hDsub]
      exact Subgroup.mem_map_of_mem _ hd
    obtain ⟨t, ht, htd⟩ := Subgroup.mem_map.mp hdimg
    have hker : t⁻¹ * d ∈ (QuotientV.pi z).ker := by
      refine MonoidHom.mem_ker.mpr ?_
      rw [map_mul, map_inv, htd]
      simp
    have hcenter : t⁻¹ * d ∈ Subgroup.center (J z) := by
      rwa [QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center] at hker
    have hd_eq : d = t * (t⁻¹ * d) := by group
    rw [hd_eq]
    exact Subgroup.mul_mem_sup ht hcenter
  have hleD : Subgroup.zpowers j ⊔ Subgroup.center (J z) ≤ D := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      change j ∈ Subgroup.centralizer (C : Set (J z))
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    · intro x hx
      change x ∈ Subgroup.centralizer (C : Set (J z))
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subgroup.mem_center_iff.mp hx c
  exact le_antisymm hDle hleD

theorem card_centralizerJ_eq_two_pow_nine_of_notMem_center (h : Tim79a.ParrottHyp z) {j : J z}
    (hj : j ∉ Subgroup.center (J z)) :
    Nat.card ↥(Subgroup.centralizer ({j} : Set (J z))) = 2 ^ 9 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  haveI : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  let C : Subgroup (J z) := Subgroup.centralizer ({j} : Set (J z))
  let φ : C →* QuotientV.V z := (QuotientV.pi z).comp C.subtype
  change Nat.card ↥C = 2 ^ 9
  have hCne : QuotientV.pi z j ≠ 1 := by
    intro hpi
    apply hj
    have hker : j ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hpi
    rwa [QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center] at hker
  let v : Additive (QuotientV.V z) := Additive.ofMul (QuotientV.pi z j)
  have hmem_v : ∀ x : Additive (QuotientV.V z),
      Additive.toMul x ∈ Subgroup.zpowers (QuotientV.pi z j) ↔ x = 0 ∨ x = v := by
    intro x
    have horder : orderOf (QuotientV.pi z j) = 2 :=
      orderOf_eq_prime (QuotientV.pow_two_eq_one_V h _) hCne
    constructor
    · intro hx
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two horder hx with h | h
      · left
        rw [← ofMul_toMul x]
        simpa using congrArg Additive.ofMul h
      · right
        rw [← ofMul_toMul x]
        simpa [v] using congrArg Additive.ofMul h
    · rintro (rfl | rfl)
      · simp
      · simpa [v] using Subgroup.mem_zpowers (QuotientV.pi z j)
  have hWspan : PiZimage h j = (Submodule.span (ZMod 2) {v} :
      Submodule (ZMod 2) (Additive (QuotientV.V z))) := by
    ext x
    rw [mem_PiZimage, hmem_v, Submodule.mem_span_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨c, hc⟩
      have hc01 : c = 0 ∨ c = 1 := by
        have hlt : c.val < 2 := ZMod.val_lt c
        have hval : c.val = 0 ∨ c.val = 1 := by omega
        rcases hval with h | h
        · left
          exact ZMod.val_injective 2 (by simpa using h)
        · right
          exact ZMod.val_injective 2 (by rw [ZMod.val_one]; exact h)
      rcases hc01 with rfl | rfl
      · left
        simpa using hc.symm
      · right
        simpa using hc.symm
  have hvne : v ≠ 0 := by
    dsimp only [v]
    intro hv
    exact hCne (ofMul_eq_zero.mp hv)
  have hWfinrank : Module.finrank (ZMod 2) ↥(PiZimage h j) = 1 := by
    rw [hWspan]
    simpa using finrank_span_singleton (K := ZMod 2) hvne
  have hrange : φ.range = C.map (QuotientV.pi z) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact Subgroup.mem_map.mpr ⟨c, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hS : Kimage h C = (commutatorBilinForm h).orthogonal (PiZimage h j) := by
    have hKC : Kimage h C = CimageZpowers h j := by
      dsimp only [Kimage, CimageZpowers, C]
    rw [hKC]
    exact map_centralizer_eq_orthogonal_zpowers h j
  have hSfinrank : Module.finrank (ZMod 2) ↥(Kimage h C) = 7 := by
    rw [hS, LinearMap.BilinForm.finrank_orthogonal (commutatorBilinForm_nondegenerate h),
      finrank_addV h, hWfinrank]
  have hcardS : Nat.card ↥(Kimage h C) = 2 ^ 7 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(Kimage h C))
    rw [hSfinrank, Nat.card_zmod] at h
    exact h
  have hrangecard : Nat.card ↥φ.range = 2 ^ 7 := by
    rw [hrange]
    change Nat.card ↥(Kimage h C) = 2 ^ 7
    exact hcardS
  have hker_le : Subgroup.center (J z) ≤ C := by
    intro x hx
    change x ∈ Subgroup.centralizer ({j} : Set (J z))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx j).symm
  have hker_eq : φ.ker = (Subgroup.center (J z)).subgroupOf C := by
    ext c
    change QuotientV.pi z (c : J z) = 1 ↔ (c : J z) ∈ Subgroup.center (J z)
    constructor
    · intro hpc
      have hmem : (c : J z) ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hpc
      rwa [QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center] at hmem
    · intro hc
      have hmem : (c : J z) ∈ (QuotientV.pi z).ker := by
        rw [QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center]
        exact hc
      exact MonoidHom.mem_ker.mp hmem
  have hkercard : Nat.card ↥φ.ker = 4 := by
    rw [hker_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv).trans
      (card_center_subgroupOf_J (z := z) h)
  have hcardC : Nat.card ↥C = 2 ^ 9 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkercard, hrangecard] at h
    rw [← h]
    norm_num
  exact hcardC

theorem index_centralizerJ_eq_two (h : Tim79a.ParrottHyp z) {j : J z}
    (hj : j ∉ Subgroup.center (J z)) :
    (Subgroup.centralizer ({j} : Set (J z))).index = 2 := by
  have hcard := card_centralizerJ_eq_two_pow_nine_of_notMem_center h hj
  rw [Subgroup.index_eq_card_div, hcard, card_J h]
  norm_num

end CFSG.RankThree.GF2n.Parrott
