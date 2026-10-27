module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDCfg
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

private theorem w16q_map_ker_normalizerMonoidHom (d : DichCfg M V₀ V U S H φ) {n : G}
    (hnK : n ∈ Subgroup.normalizer (conjClosure V H : Set G))
    (hnI : n ∈ Subgroup.normalizer (iSub16 V H : Set G)) :
    φ.ker.map ((Subgroup.normalizerMonoidHom (conjClosure V H) ⟨n, hnK⟩ :
        MulAut ↥(conjClosure V H)) : ↥(conjClosure V H) →* ↥(conjClosure V H)) = φ.ker := by
  have hker : φ.ker = (iSub16 V H).subgroupOf (conjClosure V H) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact d.bar.ker_iff k
  have hstep : ∀ x : ↥(conjClosure V H), x ∈ φ.ker →
      (Subgroup.normalizerMonoidHom (conjClosure V H) ⟨n, hnK⟩) x ∈ φ.ker := by
    intro x hx
    rw [hker] at hx ⊢
    have hxI : (x : G) ∈ iSub16 V H := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hnI (x : G)).1 hxI
  have hle : φ.ker.map ((Subgroup.normalizerMonoidHom (conjClosure V H) ⟨n, hnK⟩ :
      MulAut ↥(conjClosure V H)) : ↥(conjClosure V H) →* ↥(conjClosure V H)) ≤ φ.ker := by
    rintro y ⟨x, hx, rfl⟩
    exact hstep x hx
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq
    (Subgroup.card_map_of_injective
      (Subgroup.normalizerMonoidHom (conjClosure V H) ⟨n, hnK⟩).injective).symm)

theorem exists_actAut (d : DichCfg M V₀ V U S H φ) :
    ∃ ρ : ↥(tSub16 V₀ S) →* MulAut X, ∀ (t : ↥(tSub16 V₀ S)) (k k' : ↥(conjClosure V H)),
      (k' : G) = (t : G) * k * (t : G)⁻¹ → ρ t (φ k) = φ k' := by
  let T := tSub16 V₀ S
  have hTK : T ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hTI : T ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans
      (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  let e := QuotientGroup.quotientKerEquivOfSurjective φ d.bar.surjective
  have he_mk : ∀ k : ↥(conjClosure V H), e (QuotientGroup.mk k) = φ k := fun k =>
    QuotientGroup.kerLift_mk φ k
  let α (t : ↥T) : MulAut X :=
    e.symm.trans ((QuotientGroup.congr φ.ker φ.ker
      (Subgroup.normalizerMonoidHom (conjClosure V H) ⟨(t : G), hTK t.2⟩)
      (w16q_map_ker_normalizerMonoidHom d (hTK t.2) (hTI t.2))).trans e)
  have hα : ∀ (t : ↥T) (k : ↥(conjClosure V H)),
      α t (φ k) = φ (Subgroup.normalizerMonoidHom (conjClosure V H) ⟨(t : G), hTK t.2⟩ k) := by
    intro t k
    have h1 : e.symm (φ k) = QuotientGroup.mk k := by
      rw [← he_mk k, MulEquiv.symm_apply_apply]
    simp only [α, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
    exact he_mk _
  have hmul : ∀ s t : ↥T, α (s * t) = α s * α t := by
    intro s t
    ext x
    obtain ⟨k, rfl⟩ := d.bar.surjective x
    rw [MulAut.mul_apply, hα, hα, hα]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul]
    group
  refine ⟨MonoidHom.mk' α hmul, ?_⟩
  intro t k k' hkk'
  show α t (φ k) = φ k'
  rw [hα]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hkk']

private theorem w16q_le_normalizer_sup_of_le {K I C : Subgroup G}
    (hKI : K ≤ Subgroup.normalizer (I : Set G))
    (hKC : ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ I ⊔ C) :
    K ≤ Subgroup.normalizer ((I ⊔ C : Subgroup G) : Set G) := by
  have hmap_le : ∀ k ∈ K, (I ⊔ C).map (MulAut.conj k) ≤ I ⊔ C := by
    intro k hk
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKI hk)]
    refine sup_le le_sup_left ?_
    rintro x ⟨y, hy, rfl⟩
    change k * y * k⁻¹ ∈ I ⊔ C
    exact hKC k hk y hy
  have hconj_mem : ∀ k ∈ K, ∀ x ∈ I ⊔ C, (MulAut.conj k) x ∈ I ⊔ C :=
    fun k hk x hx => hmap_le k hk ⟨x, hx, rfl⟩
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hmap_le k hk) ?_
  intro x hx
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj k⁻¹) x, hconj_mem k⁻¹ (K.inv_mem hk) x hx, ?_⟩
  change k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ = x
  group

theorem mem_of_forall_comm_mem (d : DichCfg M V₀ V U S H φ) {a : G} (ha : a ∈ tSub16 V₀ S)
    (h : ∀ k ∈ conjClosure V H, a * k * a⁻¹ * k⁻¹ ∈ iSub16 V H) : a ∈ qSub16 V₀ V S H := by
  let T := tSub16 V₀ S
  let K := conjClosure V H
  let I := iSub16 V H
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hTI : T ≤ Subgroup.normalizer (I : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans
      (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  obtain ⟨ρ, hρ⟩ := d.exists_actAut
  let C : Subgroup G := (ρ.ker).map T.subtype
  have hC_le_T : C ≤ T := Subgroup.map_subtype_le ρ.ker
  have haC : a ∈ C := by
    refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    obtain ⟨k, rfl⟩ := d.bar.surjective x
    have hkK : (a : G) * k * (a : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK ha) k).1 k.2
    have hcomm : (a : G) * (k : G) * (a : G)⁻¹ * (k : G)⁻¹ ∈ I := h k k.2
    have hfact : (⟨(a : G) * k * (a : G)⁻¹, hkK⟩ : ↥K) =
        (⟨(a : G) * (k : G) * (a : G)⁻¹ * (k : G)⁻¹,
          d.cfg.iSub16_le_conjClosure hcomm⟩ : ↥K) * k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    rw [hρ ⟨a, ha⟩ k ⟨(a : G) * k * (a : G)⁻¹, hkK⟩ rfl, MulAut.one_apply, hfact,
      map_mul, (d.bar.ker_iff _).2 hcomm, one_mul]
  have hKC : ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ I ⊔ C := by
    intro k hk x hx
    obtain ⟨s, hs_ker, rfl⟩ := Subgroup.mem_map.mp hx
    have hs1 : ρ s = 1 := MonoidHom.mem_ker.mp hs_ker
    have hsK : (s : G) ∈ Subgroup.normalizer (K : Set G) := hTK s.2
    have hksK : (s : G) * k * (s : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hsK k).1 hk
    have hphi : φ ⟨(s : G) * k * (s : G)⁻¹, hksK⟩ = φ ⟨k, hk⟩ := by
      have hh := hρ s ⟨k, hk⟩ ⟨(s : G) * k * (s : G)⁻¹, hksK⟩ rfl
      rw [hs1, MulAut.one_apply] at hh
      exact hh.symm
    let x₀ : ↥K :=
      ⟨(s : G) * (k : G) * (s : G)⁻¹ * (k : G)⁻¹, K.mul_mem hksK (K.inv_mem hk)⟩
    have hfac : x₀ = (⟨(s : G) * k * (s : G)⁻¹, hksK⟩ : ↥K) * ⟨k, hk⟩⁻¹ := by
      apply Subtype.ext
      rfl
    have hcomm : (s : G) * (k : G) * (s : G)⁻¹ * (k : G)⁻¹ ∈ I :=
      (d.bar.ker_iff x₀).1 (by rw [hfac, map_mul, map_inv, hphi, mul_inv_cancel])
    have hcommI : k * (s : G) * k⁻¹ * (s : G)⁻¹ ∈ I := by
      have hh := I.inv_mem hcomm
      rwa [show ((s : G) * (k : G) * (s : G)⁻¹ * (k : G)⁻¹)⁻¹ =
        k * (s : G) * k⁻¹ * (s : G)⁻¹ by group] at hh
    change k * (s : G) * k⁻¹ ∈ I ⊔ C
    rw [show k * (s : G) * k⁻¹ = (k * (s : G) * k⁻¹ * (s : G)⁻¹) * (s : G) by group]
    exact (I ⊔ C).mul_mem (Subgroup.mem_sup_left hcommI)
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨s, hs_ker, rfl⟩))
  have hCQ : C ≤ qSub16 V₀ V S H := by
    have hT2 : IsPGroup 2 T := d.cfg.cex.sylow.isPGroup.to_le inf_le_left
    have hI_le_T : I ≤ T := d.cfg.iSub16_le_tSub16
    have hnormC : (C.subgroupOf T).Normal := by
      rw [show C.subgroupOf T = ρ.ker from
        Subgroup.comap_map_eq_self_of_injective T.subtype_injective ρ.ker]
      infer_instance
    have hT_le_NC : T ≤ Subgroup.normalizer (C : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hC_le_T
    have hKI : K ≤ Subgroup.normalizer (I : Set G) :=
      d.cfg.conjClosure_le_H.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
    have hK_le_NR : K ≤ Subgroup.normalizer ((I ⊔ C : Subgroup G) : Set G) :=
      w16q_le_normalizer_sup_of_le hKI hKC
    have hT_le_NR : T ≤ Subgroup.normalizer ((I ⊔ C : Subgroup G) : Set G) :=
      (le_inf hTI hT_le_NC).trans (inf_normalizer_le_normalizer_sup I C)
    have hR2 : IsPGroup 2 (I ⊔ C : Subgroup G) := hT2.to_le (sup_le hI_le_T hC_le_T)
    have hR_le_KT : (I ⊔ C : Subgroup G) ≤ K ⊔ T :=
      sup_le (d.cfg.iSub16_le_conjClosure.trans le_sup_left) (hC_le_T.trans le_sup_right)
    have hN : K ⊔ T ≤ Subgroup.normalizer ((I ⊔ C : Subgroup G) : Set G) :=
      sup_le hK_le_NR hT_le_NR
    have hRQ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (N := I ⊔ C)
      (H := K ⊔ T) hR_le_KT hN hR2
    exact le_trans le_sup_right hRQ
  exact hCQ haC

theorem exists_subgroup_aut (d : DichCfg M V₀ V U S H φ) {A : Subgroup G}
    (hAT : A ≤ tSub16 V₀ S) (hA2 : IsElemAbelian 2 A) :
    ∃ E : Subgroup (MulAut X), IsElemAbelian 2 E ∧
      (∀ α ∈ E, ∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y) ∧
      (∀ α ∈ E, ∃ a ∈ A, ∀ k k' : ↥(conjClosure V H),
        (k' : G) = a * (k : G) * a⁻¹ → α (φ k) = φ k') ∧
      Nat.card E * Nat.card ↥(A ⊓ qSub16 V₀ V S H) = Nat.card A := by
  let T := tSub16 V₀ S
  let K := conjClosure V H
  let I := iSub16 V H
  obtain ⟨ρ, hρ⟩ := d.exists_actAut
  let A' : Subgroup ↥T := A.subgroupOf T
  let E : Subgroup (MulAut X) := A'.map ρ
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hE2 : IsElemAbelian 2 E :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf hA2 T) ρ
  have hEY : ∀ α ∈ E, ∀ y ∈ SevenK.barSub K φ V, α y = y := by
    intro α hα y hy
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hα
    obtain ⟨v, hvV, rfl⟩ := SevenK.mem_barSub.mp hy
    have haS : (a' : G) ∈ S := (inf_le_left : T ≤ S) a'.2
    have havK : (a' : G) * v * (a' : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK a'.2) v).1 v.2
    have hcommI : (a' : G) * (v : G) * (a' : G)⁻¹ * (v : G)⁻¹ ∈ I :=
      d.cfg.le_iSub16 (Subgroup.mem_sup_right (d.cfg.cex.comm_mem_V₀ haS hvV))
    have hphi_eq : φ (⟨(a' : G) * v * (a' : G)⁻¹, havK⟩ : ↥K) = φ v := by
      have h1 : φ ((⟨(a' : G) * v * (a' : G)⁻¹, havK⟩ : ↥K) * v⁻¹) = 1 :=
        (d.bar.ker_iff _).2 hcommI
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [hρ a' v ⟨(a' : G) * v * (a' : G)⁻¹, havK⟩ rfl, hphi_eq]
  have hEind : ∀ α ∈ E, ∃ a ∈ A, ∀ k k' : ↥K,
      (k' : G) = a * (k : G) * a⁻¹ → α (φ k) = φ k' := by
    intro α hα
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hα
    exact ⟨(a' : G), Subgroup.mem_subgroupOf.mp ha', fun k k' hk' => hρ a' k k' hk'⟩
  have hcard : Nat.card E * Nat.card ↥(A ⊓ qSub16 V₀ V S H) = Nat.card A := by
    let ρ'' : ↥A →* MulAut X := ρ.comp (Subgroup.inclusion hAT)
    have hrange : ρ''.range = E := by
      ext α
      constructor
      · rintro ⟨a, rfl⟩
        exact Subgroup.mem_map.mpr ⟨⟨(a : G), hAT a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
      · rintro ⟨a', ha', rfl⟩
        exact ⟨⟨(a' : G), Subgroup.mem_subgroupOf.mp ha'⟩, rfl⟩
    have hker : ρ''.ker = (A ⊓ qSub16 V₀ V S H).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨a.2, d.mem_of_forall_comm_mem (hAT a.2) ?_⟩
        intro k hk
        have hkK : (a : G) * k * (a : G)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hTK (hAT a.2)) k).1 hk
        have h1 : ρ'' a (φ ⟨k, hk⟩) = φ ⟨(a : G) * k * (a : G)⁻¹, hkK⟩ :=
          hρ ⟨(a : G), hAT a.2⟩ ⟨k, hk⟩ ⟨(a : G) * k * (a : G)⁻¹, hkK⟩ rfl
        rw [h, MulAut.one_apply] at h1
        have h2 : φ ((⟨(a : G) * k * (a : G)⁻¹, hkK⟩ : ↥K) * ⟨k, hk⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, ← h1, mul_inv_cancel]
        exact (d.bar.ker_iff _).1 h2
      · rintro ⟨-, haQ⟩
        ext x
        obtain ⟨k, rfl⟩ := d.bar.surjective x
        have hwant : (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ I := by
          have hh := I.inv_mem (d.comm_mem_qSub16 haQ k.2)
          simpa only [mul_inv_rev, inv_inv, mul_assoc, Subgroup.coe_inv] using hh
        have hkK : (a : G) * k * (a : G)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hTK (hAT a.2)) k).1 k.2
        have h1 : ρ'' a (φ k) = φ ⟨(a : G) * k * (a : G)⁻¹, hkK⟩ :=
          hρ ⟨(a : G), hAT a.2⟩ k ⟨(a : G) * k * (a : G)⁻¹, hkK⟩ rfl
        rw [h1]
        have h2 : φ ((⟨(a : G) * k * (a : G)⁻¹, hkK⟩ : ↥K) * k⁻¹) = 1 :=
          (d.bar.ker_iff _).2 hwant
        rw [map_mul, map_inv] at h2
        exact mul_inv_eq_one.mp h2
    have hmain := Subgroup.card_ker_mul_card_range ρ''
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      Nat.mul_comm] at hmain
    exact hmain
  exact ⟨E, hE2, hEY, hEind, hcard⟩

theorem card_mul_le_of_offender (d : DichCfg M V₀ V U S H φ)
    (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 (tSub16 V₀ S)) :
    Nat.card ↥(iSub16 V H) * Nat.card ↥(A ⊓ qSub16 V₀ V S H) ≤
      Nat.card A * Nat.card ↥(iSub16 V H ⊓ centralizer (A : Set G)) := by
  obtain ⟨hAT, hAe, hAcard⟩ := mem_elemFamilyIn.1 hA
  have hA2 : IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAe
  have hQ_le_CI : qSub16 V₀ V S H ≤ centralizer (iSub16 V H : Set G) :=
    d.cfg.qSub16_le_centralizer hQT
  have hI2 : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hIe : IsElementaryAbelian 2 (iSub16 V H) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).2 hI2
  have hAQe : IsElementaryAbelian 2 ↥(A ⊓ qSub16 V₀ V S H) :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_of_le inf_le_left hAe
  have hI_le_cent : iSub16 V H ≤
      centralizer ((A ⊓ qSub16 V₀ V S H : Subgroup G) : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hQ_le_CI hx.2) i hi).symm
  have hBe : IsElementaryAbelian 2 ↥((A ⊓ qSub16 V₀ V S H) ⊔ iSub16 V H) :=
    isElementaryAbelian_sup_of_le_centralizer hAQe hIe hI_le_cent
  have hB_le_T : (A ⊓ qSub16 V₀ V S H) ⊔ iSub16 V H ≤ tSub16 V₀ S :=
    sup_le (inf_le_left.trans hAT) d.cfg.iSub16_le_tSub16
  have hB_card : Nat.card ↥((A ⊓ qSub16 V₀ V S H) ⊔ iSub16 V H) ≤ Nat.card A := by
    have h := card_le_pow_pRank_of_le hB_le_T hBe
    rw [← hAcard] at h
    exact h
  have hAnorm : A ⊓ qSub16 V₀ V S H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    (le_trans inf_le_right hQ_le_CI).trans (Subgroup.centralizer_le_normalizer _)
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAnorm
  have hinf : (A ⊓ qSub16 V₀ V S H) ⊓ iSub16 V H = A ⊓ iSub16 V H := by
    rw [inf_assoc, inf_eq_right.mpr d.cfg.iSub16_le_qSub16]
  have hAI_le : A ⊓ iSub16 V H ≤ iSub16 V H ⊓ centralizer (A : Set G) := by
    refine le_inf inf_le_right ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (B2F.isElemAbelian_comm hA2 hx.1 ha).symm
  have hcardAI : Nat.card ↥(A ⊓ iSub16 V H) ≤
      Nat.card ↥(iSub16 V H ⊓ centralizer (A : Set G)) := Subgroup.card_le_of_le hAI_le
  rw [hinf] at hprod
  calc Nat.card ↥(iSub16 V H) * Nat.card ↥(A ⊓ qSub16 V₀ V S H)
      = Nat.card ↥(A ⊓ qSub16 V₀ V S H) * Nat.card ↥(iSub16 V H) := Nat.mul_comm _ _
    _ = Nat.card ↥((A ⊓ qSub16 V₀ V S H) ⊔ iSub16 V H) * Nat.card ↥(A ⊓ iSub16 V H) :=
        hprod.symm
    _ ≤ Nat.card A * Nat.card ↥(iSub16 V H ⊓ centralizer (A : Set G)) :=
        Nat.mul_le_mul hB_card hcardAI

private theorem w16q_barSub_conjSubgroup {K : Subgroup G} {X : Type} [Group X]
    (φ : ↥K →* X) (A : Subgroup G) (k : ↥K) :
    SevenK.barSub K φ (conjSubgroup A (k : G)) =
      conjSubgroup (SevenK.barSub K φ A) (φ k) := by
  ext x
  rw [mem_conjSubgroup_iff, SevenK.mem_barSub, SevenK.mem_barSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨k * y * k⁻¹, ?_, ?_⟩
    · have hy' : (k : G) * (y : G) * (k : G)⁻¹ ∈ A := mem_conjSubgroup_iff.mp hy
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hy'
    · rw [map_mul, map_mul, map_inv]
  · rintro ⟨a, ha, haφ⟩
    refine ⟨k⁻¹ * a * k, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have hco : (k : G) * ((k⁻¹ * a * k : ↥K) : G) * (k : G)⁻¹ = (a : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hco]
      exact ha
    · rw [map_mul, map_mul, map_inv, haφ]
      group

theorem exists_not_mem_conj (d : DichCfg M V₀ V U S H φ)
    (hNN : ∀ α : MulAut X, (∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y) →
      (∀ x : X, (conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x).map α.toMonoidHom =
        conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x) → α = 1)
    {a : G} (ha : a ∈ tSub16 V₀ S) (haQ : a ∉ qSub16 V₀ V S H) :
    ∃ g ∈ conjClosure V H, a ∉ conjSubgroup M g := by
  let T := tSub16 V₀ S
  let K := conjClosure V H
  let I := iSub16 V H
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  haveI : Finite X := Finite.of_surjective φ d.bar.surjective
  obtain ⟨ρ, hρ⟩ := d.exists_actAut
  by_contra hnot
  have h' : ∀ g ∈ K, a ∈ conjSubgroup M g := by
    intro g hg
    by_contra hg'
    exact hnot ⟨g, hg, hg'⟩
  have hα1 : ρ ⟨a, ha⟩ ≠ 1 := by
    intro hα
    apply haQ
    refine d.mem_of_forall_comm_mem ha ?_
    intro k hk
    have hkK : a * k * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ha) k).1 hk
    have h1 : φ (⟨a * k * a⁻¹, hkK⟩ : ↥K) = φ ⟨k, hk⟩ := by
      have hh := hρ ⟨a, ha⟩ ⟨k, hk⟩ ⟨a * k * a⁻¹, hkK⟩ rfl
      rw [hα, MulAut.one_apply] at hh
      exact hh.symm
    have h2 : φ ((⟨a * k * a⁻¹, hkK⟩ : ↥K) * ⟨k, hk⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (d.bar.ker_iff _).1 h2
  have hαY : ∀ y ∈ SevenK.barSub K φ V, ρ ⟨a, ha⟩ y = y := by
    intro y hy
    obtain ⟨v, hvV, rfl⟩ := SevenK.mem_barSub.mp hy
    have haS : a ∈ S := (inf_le_left : T ≤ S) ha
    have havK : a * v * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ha) v).1 v.2
    have hcommI : a * (v : G) * a⁻¹ * (v : G)⁻¹ ∈ I :=
      d.cfg.le_iSub16 (Subgroup.mem_sup_right (d.cfg.cex.comm_mem_V₀ haS hvV))
    have hphi_eq : φ (⟨a * v * a⁻¹, havK⟩ : ↥K) = φ v := by
      have h1 : φ ((⟨a * v * a⁻¹, havK⟩ : ↥K) * v⁻¹) = 1 := (d.bar.ker_iff _).2 hcommI
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [hρ ⟨a, ha⟩ v ⟨a * v * a⁻¹, havK⟩ rfl, hphi_eq]
  have heq : ∀ g : ↥K, (conjSubgroup (SevenK.barSub K φ V) (φ g)).map
      (ρ ⟨a, ha⟩).toMonoidHom = conjSubgroup (SevenK.barSub K φ V) (φ g) := by
    intro g
    have hgaM : (g : G) * a * (g : G)⁻¹ ∈ M := mem_conjSubgroup_iff.mp (h' g g.2)
    have hgaN : (g : G) * a * (g : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      rw [d.cfg.cex.hyp.h6.normalizer_eq]
      exact hgaM
    have hNorm : a ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer]
      calc conjSubgroup (conjSubgroup V g) a = conjSubgroup V ((g : G) * a) :=
            conjSubgroup_conjSubgroup V (g : G) a
        _ = conjSubgroup V (((g : G) * a * (g : G)⁻¹) * (g : G)) := by
            rw [show (g : G) * a * (g : G)⁻¹ * (g : G) = (g : G) * a by group]
        _ = conjSubgroup (conjSubgroup V ((g : G) * a * (g : G)⁻¹)) (g : G) :=
            (conjSubgroup_conjSubgroup V ((g : G) * a * (g : G)⁻¹) (g : G)).symm
        _ = conjSubgroup V g := by
            rw [conjSubgroup_eq_iff_mem_normalizer.mpr hgaN]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← w16q_barSub_conjSubgroup (K := K) φ V g]
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨w, hwYg, hw⟩ := SevenK.mem_barSub.mp hy
      have hawK : a * w * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ha) w).1 w.2
      have hawY : a * w * a⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.mp hNorm w).1 hwYg
      refine SevenK.mem_barSub.mpr ⟨⟨a * w * a⁻¹, hawK⟩, hawY, ?_⟩
      rw [← hw]
      exact (hρ ⟨a, ha⟩ w ⟨a * w * a⁻¹, hawK⟩ rfl).symm
    · rw [← w16q_barSub_conjSubgroup (K := K) φ V g]
      exact le_of_eq (Subgroup.card_map_of_injective (ρ ⟨a, ha⟩).injective).symm
  have hall : ∀ x : X, (conjSubgroup (SevenK.barSub K φ V) x).map
      (ρ ⟨a, ha⟩).toMonoidHom = conjSubgroup (SevenK.barSub K φ V) x := by
    intro x
    obtain ⟨g, rfl⟩ := d.bar.surjective x
    exact heq g
  exact hα1 (hNN (ρ ⟨a, ha⟩) hαY hall)

theorem card_mul_le_of_not_mem_conj (d : DichCfg M V₀ V U S H φ) {a g : G}
    (ha : a ∈ tSub16 V₀ S) (hg : g ∈ conjClosure V H) (hag : a ∉ conjSubgroup M g) :
    Nat.card ↥V₀ * Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) ≤
      Nat.card ↥(iSub16 V H) := by
  let I := iSub16 V H
  let W := conjSubgroup V₀ g
  let Cg := I ⊓ centralizer ({a} : Set G)
  have hKI : conjClosure V H ≤ Subgroup.normalizer (I : Set G) :=
    d.cfg.conjClosure_le_H.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hW_le_I : W ≤ I := by
    have hV0I : V₀ ≤ I := le_sup_right.trans d.cfg.le_iSub16
    exact (E3.conjSubgroup_mono_left g hV0I).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr (hKI hg)))
  have hI2 : IsElemAbelian 2 I :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hC_le_I : Cg ≤ I := inf_le_left
  have hcomm : W ≤ Subgroup.normalizer (Cg : Set G) := by
    have hcent : W ≤ Subgroup.centralizer (Cg : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact B2F.isElemAbelian_comm hI2 (hC_le_I hx) (hW_le_I hw)
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hinf : W ⊓ Cg = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨hwW, hwCg⟩ := Subgroup.mem_inf.mp hw
    by_contra hw1
    have hwV₀ : g * w * g⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hwW
    have hwV₀1 : g * w * g⁻¹ ≠ 1 := by
      intro h
      apply hw1
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    have hwa : w * a = a * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwCg).2
    have hgaC : g * a * g⁻¹ ∈ Subgroup.centralizer ({(g * w * g⁻¹)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g * a * g⁻¹) * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by group
        _ = g * (w * a) * g⁻¹ := by rw [hwa]
        _ = (g * w * g⁻¹) * (g * a * g⁻¹) := by group
    exact hag (mem_conjSubgroup_iff.mpr
      (d.cfg.cex.hyp.centralizer_le hwV₀ hwV₀1 hgaC))
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hcomm
  rw [hinf, Subgroup.card_bot, mul_one] at hprod
  have hsup_le_I : W ⊔ Cg ≤ I := sup_le hW_le_I hC_le_I
  have hcard := Subgroup.card_le_of_le hsup_le_I
  calc Nat.card ↥V₀ * Nat.card ↥Cg
      = Nat.card ↥W * Nat.card ↥Cg := by rw [E3.card_conjSubgroup]
    _ = Nat.card ↥(W ⊔ Cg) := hprod.symm
    _ ≤ Nat.card ↥I := hcard

theorem card_mul_le_of_not_le (d : DichCfg M V₀ V U S H φ)
    (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S)
    (hNN : ∀ α : MulAut X, (∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y) →
      (∀ x : X, (conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x).map α.toMonoidHom =
        conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x) → α = 1)
    {A : Subgroup G} (hA : A ∈ elemFamilyIn 2 (tSub16 V₀ S)) (hAQ : ¬ A ≤ qSub16 V₀ V S H) :
    Nat.card ↥V₀ * Nat.card ↥(A ⊓ qSub16 V₀ V S H) ≤ Nat.card A := by
  obtain ⟨hAT, -, -⟩ := mem_elemFamilyIn.1 hA
  obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.1 hAQ
  obtain ⟨g, hgK, hag⟩ := d.exists_not_mem_conj hNN (hAT haA) haQ
  have h1 := d.card_mul_le_of_not_mem_conj (hAT haA) hgK hag
  have h2 := d.card_mul_le_of_offender hQT hA
  have h3 : Nat.card ↥(iSub16 V H ⊓ centralizer (A : Set G)) ≤
      Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA)))
  have hpos : 0 < Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) *
        (Nat.card ↥V₀ * Nat.card ↥(A ⊓ qSub16 V₀ V S H))
      = (Nat.card ↥V₀ * Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G))) *
        Nat.card ↥(A ⊓ qSub16 V₀ V S H) := by ring
    _ ≤ Nat.card ↥(iSub16 V H) * Nat.card ↥(A ⊓ qSub16 V₀ V S H) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ Nat.card A * Nat.card ↥(iSub16 V H ⊓ centralizer (A : Set G)) := h2
    _ ≤ Nat.card A * Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) :=
        Nat.mul_le_mul_left _ h3
    _ = Nat.card ↥(iSub16 V H ⊓ centralizer ({a} : Set G)) * Nat.card A := by ring

theorem exists_aut_subgroup (d : DichCfg M V₀ V U S H φ)
    (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S)
    (hNN : ∀ α : MulAut X, (∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y) →
      (∀ x : X, (conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x).map α.toMonoidHom =
        conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x) → α = 1)
    {A : Subgroup G} (hA : A ∈ elemFamilyIn 2 (tSub16 V₀ S)) (hAQ : ¬ A ≤ qSub16 V₀ V S H) :
    ∃ E : Subgroup (MulAut X), IsElemAbelian 2 E ∧
      (∀ α ∈ E, ∀ y ∈ SevenK.barSub (conjClosure V H) φ V, α y = y) ∧
      Nat.card ↥V₀ ≤ Nat.card E := by
  obtain ⟨hAT, hAe, -⟩ := mem_elemFamilyIn.1 hA
  have hA2 : IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAe
  obtain ⟨E, hE2, hEc, -, hEcard⟩ := d.exists_subgroup_aut hAT hA2
  refine ⟨E, hE2, hEc, ?_⟩
  have h := d.card_mul_le_of_not_le hQT hNN hA hAQ
  rw [← hEcard] at h
  exact Nat.le_of_mul_le_mul_right h Nat.card_pos

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
