module

public import CFSG.RankThree.GF2n.Parrott.Section3Commutator
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def Fsub (σ : ↥(H z)) : Subgroup (QuotientV.V z) :=
  (centralizerJ σ).map (QuotientV.pi z)

@[expose] noncomputable def Wsub (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) : Subgroup (QuotientV.V z) :=
  commutatorV h σ

theorem conjV_trivial_on_Fsub (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) :
    ∀ v ∈ Fsub (z := z) σ, conjV h σ v = v := by
  rintro v ⟨j, hj, rfl⟩
  rw [conjV_mk]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hcomm : (j : G) * (σ : G) = (σ : G) * (j : G) := mem_centralizerJ_iff.mp hj
  calc (σ : G) * (j : G) * (σ : G)⁻¹ = (j : G) * (σ : G) * (σ : G)⁻¹ := by rw [hcomm]
    _ = (j : G) := by group

theorem conjV_trivial_on_Fsub_of_le (h : Tim79a.ParrottHyp z) {σ₁ σ₂ : ↥(H z)}
    (hle : centralizerJ σ₁ ≤ centralizerJ σ₂) :
    ∀ v ∈ Fsub (z := z) σ₁, conjV h σ₂ v = v := by
  rintro v ⟨j, hj, rfl⟩
  rw [conjV_mk]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hcomm : (j : G) * (σ₂ : G) = (σ₂ : G) * (j : G) := mem_centralizerJ_iff.mp (hle hj)
  calc (σ₂ : G) * (j : G) * (σ₂ : G)⁻¹ = (j : G) * (σ₂ : G) * (σ₂ : G)⁻¹ := by rw [hcomm]
    _ = (j : G) := by group

theorem CJ_sigma1_le_normalizer_commutator_sigma1Nine :
    CJ z (sigma1Nine D : G) ≤
      Subgroup.normalizer
        ((⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ :
          Subgroup G) : Set G) := by
  intro a ha
  let f : G →* G := (MulAut.conj (a : G)).toMonoidHom
  have haJ : (a : G) ∈ J z := ha.2
  have haC : (a : G) ∈ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) := ha.1
  have hcomm : Commute (a : G) (sigma1Nine D : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp haC
  have hconjσ : f (sigma1Nine D : G) = (sigma1Nine D : G) := by
    change (MulAut.conj (a : G)) (sigma1Nine D : G) = (sigma1Nine D : G)
    rw [MulAut.conj_apply]
    calc (a : G) * (sigma1Nine D : G) * (a : G)⁻¹
        = (sigma1Nine D : G) * (a : G) * (a : G)⁻¹ := by rw [hcomm.eq]
      _ = (sigma1Nine D : G) := by group
  have hB : (Subgroup.zpowers (sigma1Nine D : G)).map f =
      Subgroup.zpowers (sigma1Nine D : G) := by
    rw [MonoidHom.map_zpowers, hconjσ]
  have hJ : (J z).map f = J z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := J z) haJ)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ :
      Subgroup G).map (MulAut.conj (a : G)).toMonoidHom =
    ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆
  rw [Subgroup.map_commutator,
    map_zpowers_sigma_eq (z := z) (σ := sigma1Nine D), hB, hJ]

theorem sup_Fsub_Wsub_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Fsub (z := z) (sigma1Nine D) ⊔ Wsub h (sigma1Nine D) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
  let A : Subgroup G :=
    (J z) ⊓ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G)
  let P : Subgroup G :=
    ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆
  have hj : (j : G) ∈ A ⊔ P := by
    rw [show A ⊔ P = J z from
      (J_eq_centralizer_commutator_sigma1Nine (z := z) h D).symm]
    exact j.2
  have hnorm : A ≤ Subgroup.normalizer (P : Set G) := by
    have h := CJ_sigma1_le_normalizer_commutator_sigma1Nine (z := z) D
    have hA : A = CJ z (sigma1Nine D : G) := by
      simp only [A, CJ, inf_comm]
    rw [hA]
    exact h
  obtain ⟨b, hb, a, ha, hba⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (H := P) (K := A) hnorm).mp (show (j : G) ∈ P ⊔ A by rwa [sup_comm])
  change a ∈ (J z) ⊓ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) at ha
  have haJ : a ∈ J z := ha.1
  have haC : a ∈ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) := ha.2
  have hbJ : b ∈ J z := commutator_le_J_sigma1Nine (z := z) D hb
  have hjeq : j = (⟨b, hbJ⟩ : J z) * ⟨a, haJ⟩ := by
    apply Subtype.ext
    simpa using hba
  rw [hjeq, map_mul]
  rw [← sup_comm]
  apply Subgroup.mul_mem_sup
  · exact Subgroup.mem_map.mpr
      ⟨⟨b, hbJ⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  · exact Subgroup.mem_map.mpr
      ⟨⟨a, haJ⟩, by
        rw [mem_centralizerJ_iff]
        exact Subgroup.mem_centralizer_singleton_iff.mp haC, rfl⟩

theorem center_subgroupOf_le_centralizerJ_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Subgroup.center (J z) ≤ centralizerJ (sigma1Nine D) := by
  intro j hj
  rw [mem_centralizerJ_iff]
  have hjZ : (j : G) ∈ centerIn (J z) := by
    have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
      rwa [QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mp hj'
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := sigma1Nine D)
      (conjZ_sigma1Nine h D) hjZ)

theorem card_centralizerJ_inf_center_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Nat.card ↥(centralizerJ (sigma1Nine D) ⊓ Subgroup.center (J z)) = 4 := by
  rw [inf_eq_right.mpr (center_subgroupOf_le_centralizerJ_sigma1Nine (z := z) (D := D) h)]
  exact card_center_subgroupOf_J (z := z) h

theorem card_Fsub_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Nat.card (Fsub (z := z) (sigma1Nine D)) = 4 := by
  let f : centralizerJ (sigma1Nine D) →* QuotientV.V z :=
    (QuotientV.pi z).comp (centralizerJ (sigma1Nine D)).subtype
  have hrange : f.range = Fsub (z := z) (sigma1Nine D) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map.mpr ⟨j, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hker : f.ker =
      (centralizerJ (sigma1Nine D) ⊓ Subgroup.center (J z)).subgroupOf
        (centralizerJ (sigma1Nine D)) := by
    ext j
    change f j = 1 ↔ (j : J z) ∈
      centralizerJ (sigma1Nine D) ⊓ Subgroup.center (J z)
    rw [MonoidHom.comp_apply]
    constructor
    · intro hj
      have hj' : (j : J z) ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hj
      rw [QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center] at hj'
      exact ⟨j.2, hj'⟩
    · rintro ⟨-, hj⟩
      rw [← QuotientV.centerIn_subgroupOf_eq_center] at hj
      have hmem : (j : J z) ∈ (QuotientV.pi z).ker := by
        rw [QuotientV.pi_ker]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hj)
      exact MonoidHom.mem_ker.mp hmem
  have hkercard : Nat.card ↥(f.ker) = 4 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : centralizerJ (sigma1Nine D) ⊓ Subgroup.center (J z) ≤
        centralizerJ (sigma1Nine D))).toEquiv]
    exact card_centralizerJ_inf_center_sigma1Nine (z := z) (D := D) h
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hkercard, card_centralizerJ_sigma1Nine (z := z) h D] at hcard
  have hrangecard : Nat.card f.range = 4 := by
    have h4 : 4 * Nat.card f.range = 4 * 4 := by
      rw [hcard]
    exact Nat.mul_left_cancel (by norm_num) h4
  simpa [hrange] using hrangecard

theorem inf_Fsub_Wsub_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Fsub (z := z) (sigma1Nine D) ⊓ Wsub h (sigma1Nine D) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvF, hvW⟩ := Subgroup.mem_inf.mp hv
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hvF
  obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hvW
  have hker : a⁻¹ * b ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ]
    simp
  have hZle : (QuotientV.pi z).ker ≤ centralizerJ (sigma1Nine D) := by
    intro k hk
    rw [QuotientV.pi_ker] at hk
    rw [mem_centralizerJ_iff]
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := sigma1Nine D)
        (conjZ_sigma1Nine h D) (Subgroup.mem_subgroupOf.mp hk))
  have hbC : b ∈ centralizerJ (sigma1Nine D) := by
    have hkC : a⁻¹ * b ∈ centralizerJ (sigma1Nine D) := hZle hker
    have hb_eq : b = a * (a⁻¹ * b) := by group
    rw [hb_eq]
    exact (centralizerJ (sigma1Nine D)).mul_mem ha hkC
  have hbCentral : (b : G) ∈
      Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hbC)
  have hbP : (b : G) ∈
      ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ :=
    Subgroup.mem_subgroupOf.mp hb
  have hbz : (b : G) ∈ Subgroup.zpowers z := by
    rw [← centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨b.2, hbCentral⟩, hbP⟩
  have hbz_center : (b : G) ∈ centerIn (J z) :=
    Subgroup.zpowers_le_of_mem (show z ∈ centerIn (J z) from
      ⟨z_mem_J h, z_centralizes_J h⟩) hbz
  have hpb : QuotientV.pi z b = 1 := by
    rw [← MonoidHom.mem_ker, QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hbz_center
  have hpa : QuotientV.pi z a = 1 := by
    rw [← hbπ, hpb]
  simpa [Subgroup.mem_bot] using hpa

@[expose] noncomputable def FsubModule (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Fsub (z := z) (sigma1Nine D)).toAddSubgroup

@[expose] noncomputable def WsubModule (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Wsub h (sigma1Nine D)).toAddSubgroup

@[expose] noncomputable def fixW (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  fixSubmodule h x ⊓ WsubModule (z := z) (D := D) h

theorem Fsub_sigma1Nine_eq_autFixedSubgroup (h : Tim79a.ParrottHyp z) :
    Fsub (z := z) (sigma1Nine D) = autFixedSubgroup (conjV h (sigma1Nine D)) := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro v hv
    rw [mem_autFixedSubgroup]
    exact conjV_trivial_on_Fsub h (sigma1Nine D) v hv
  · rw [card_fix h (sigma1Nine D), fixDimV_sigma1Nine (z := z) (D := D) h,
      card_Fsub_sigma1Nine (z := z) (D := D) h]
    norm_num

theorem inf_Wsub_autFixedSubgroup_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Wsub h (sigma1Nine D) ⊓ autFixedSubgroup (conjV h (sigma1Nine D)) = ⊥ := by
  rw [← Fsub_sigma1Nine_eq_autFixedSubgroup (z := z) (D := D) h, inf_comm]
  exact inf_Fsub_Wsub_sigma1Nine (z := z) (D := D) h

theorem conjV_mem_Wsub_of_commute (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hcomm : conjV h x * conjV h (sigma1Nine D) =
      conjV h (sigma1Nine D) * conjV h x) :
    ∀ v ∈ Wsub h (sigma1Nine D), conjV h x v ∈ Wsub h (sigma1Nine D) := by
  intro v hv
  rw [Wsub, commutatorV_eq_range (z := z) h (sigma1Nine_order (z := z) D)] at hv ⊢
  obtain ⟨u, rfl⟩ := hv
  refine ⟨conjV h x u, ?_⟩
  rw [VComplementHom_apply, VComplementHom_apply, map_mul]
  congr 1
  rw [← MulAut.mul_apply, ← hcomm, MulAut.mul_apply]

end CFSG.RankThree.GF2n.Parrott
