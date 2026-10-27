module

public import CFSG.Quasithin.Recognition.L34CIT.Parabolics
public import CFSG.Quasithin.Recognition.L34CIT.SteinerIdent

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open CFSG.Quasithin.A94.He42Plane CFSG.ComponentClassification.WittDesign
open scoped Pointwise commutatorElement

variable {A : Type} [Group A]

namespace Config

theorem exists_mul_mul (C : Config A) [Finite A] (hA : Nat.card A = 20160) (g : A) :
    ∃ h ∈ normalizer (C.L : Set A), ∃ m ∈ normalizer (C.M : Set A),
      ∃ h' ∈ normalizer (C.L : Set A), g = h * m * h' := by
  classical
  set Lset : Finset (A ⧸ C.K₂) :=
    Finset.univ.filter (fun ℓ => Inc C.K₁ C.K₂ ((1 : A) : A ⧸ C.K₁) ℓ) with hLset
  set S : Finset (A ⧸ C.K₁) := Lset.biUnion (fun ℓ => pts C.K₁ C.K₂ ℓ) with hS
  have hcardL : Nat.card (A ⧸ C.K₁) = 21 := by
    have h := Subgroup.card_mul_index C.K₁
    rw [Subgroup.index_eq_card, C.card_normalizer_L, hA] at h
    omega
  have hlines_card : Lset.card = 5 :=
    he42pl_card_lines_thru C.relIndex_inf_normalizer_L (1 : A)
  have hline_card : ∀ ℓ ∈ Lset, (pts C.K₁ C.K₂ ℓ).card = 5 := by
    intro ℓ hℓ
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
    exact he42pl_card_pts C.relIndex_inf_normalizer_M y
  have hbase_mem : ∀ ℓ ∈ Lset, ((1 : A) : A ⧸ C.K₁) ∈ pts C.K₁ C.K₂ ℓ := by
    intro ℓ hℓ
    rw [hLset, Finset.mem_filter] at hℓ
    exact (he42pl_mem_pts_iff C.K₁ C.K₂ _ ℓ).2 hℓ.2
  have hdisj : (↑Lset : Set (A ⧸ C.K₂)).PairwiseDisjoint
      fun ℓ => (pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁) := by
    intro ℓ hℓ ℓ' hℓ' hne
    rw [Finset.mem_coe] at hℓ hℓ'
    refine Finset.disjoint_left.2 fun p hp hp' => hne ?_
    obtain ⟨hp1, hpℓ⟩ := Finset.mem_erase.1 hp
    obtain ⟨-, hpℓ'⟩ := Finset.mem_erase.1 hp'
    rw [he42pl_mem_pts_iff] at hpℓ hpℓ'
    exact he42pl_eq_line C.eq_line_of_two_points (Ne.symm hp1)
      ((he42pl_mem_pts_iff C.K₁ C.K₂ _ ℓ).1 (hbase_mem ℓ hℓ)) hpℓ
      ((he42pl_mem_pts_iff C.K₁ C.K₂ _ ℓ').1 (hbase_mem ℓ' hℓ')) hpℓ'
  have hterm : ∀ ℓ ∈ Lset, ((pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁)).card = 4 := by
    intro ℓ hℓ
    rw [Finset.card_erase_of_mem (hbase_mem ℓ hℓ), hline_card ℓ hℓ]
  have hS_card : S.card = 21 := by
    have hTcard :
        (Lset.biUnion fun ℓ => (pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁)).card = 20 := by
      rw [Finset.card_biUnion hdisj]
      calc ∑ ℓ ∈ Lset, ((pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁)).card
          = ∑ ℓ ∈ Lset, 4 := Finset.sum_congr rfl hterm
        _ = Lset.card * 4 := by rw [Finset.sum_const, smul_eq_mul]
        _ = 20 := by rw [hlines_card]
    have hS_eq : S = insert ((1 : A) : A ⧸ C.K₁)
        (Lset.biUnion fun ℓ => (pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁)) := by
      ext p
      simp only [hS, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨ℓ, hℓ, hp⟩
        by_cases hp1 : p = ((1 : A) : A ⧸ C.K₁)
        · exact Or.inl hp1
        · exact Or.inr ⟨ℓ, hℓ, hp1, hp⟩
      · rintro (rfl | ⟨ℓ, hℓ, -, hp⟩)
        · obtain ⟨ℓ₀, hℓ₀⟩ := Finset.card_pos.mp (by rw [hlines_card]; norm_num)
          exact ⟨ℓ₀, hℓ₀, hbase_mem ℓ₀ hℓ₀⟩
        · exact ⟨ℓ, hℓ, hp⟩
    have hnot : ((1 : A) : A ⧸ C.K₁) ∉
        (Lset.biUnion fun ℓ => (pts C.K₁ C.K₂ ℓ).erase ((1 : A) : A ⧸ C.K₁)) := by
      rw [Finset.mem_biUnion]
      rintro ⟨ℓ, -, hp⟩
      exact (Finset.mem_erase.1 hp).1 rfl
    rw [hS_eq, Finset.card_insert_of_notMem hnot, hTcard]
  have hSuniv : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hS_card, ← Nat.card_eq_fintype_card, hcardL]
  have hgp : (g : A ⧸ C.K₁) ∈ S := by rw [hSuniv]; exact Finset.mem_univ _
  rw [hS, Finset.mem_biUnion] at hgp
  obtain ⟨ℓ, hℓ, hpℓ⟩ := hgp
  rw [hLset, Finset.mem_filter] at hℓ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
  rw [he42pl_mem_pts_iff, he42pl_inc_iff_exists] at hpℓ
  rw [he42pl_inc_iff_exists] at hℓ
  obtain ⟨l₁, hl₁, l₂, hl₂, hgl⟩ := hpℓ
  obtain ⟨l₁', hl₁', l₂', hl₂', hbase⟩ := hℓ.2
  refine ⟨l₁', hl₁', l₂'⁻¹ * l₂, C.K₂.mul_mem (C.K₂.inv_mem hl₂') hl₂, l₁⁻¹,
    C.K₁.inv_mem hl₁, ?_⟩
  have hy : y = l₁' * l₂'⁻¹ := by
    rw [one_mul] at hbase
    rw [hbase, mul_inv_cancel_right]
  have hgl' : g * l₁ = l₁' * (l₂'⁻¹ * l₂) := by
    rw [hgl, hy]
    group
  calc g = (g * l₁) * l₁⁻¹ := by group
    _ = (l₁' * (l₂'⁻¹ * l₂)) * l₁⁻¹ := by rw [hgl']

private theorem commutator_normalizer_L (C : Config A) [Finite A] :
    ⁅C.K₁, C.K₁⁆ = C.K₁ := by
  have hLle : C.L ≤ ⁅C.K₁, C.K₁⁆ := by
    obtain ⟨f, hfK, hf⟩ := C.exists_fpf_L
    have hconj : ∀ l ∈ C.L, f * l * f⁻¹ ∈ C.L := by
      intro l hl
      have hmap : MulAut.conj f • (C.L : Subgroup A) = C.L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hfK
      have hmem : MulAut.conj f l ∈ MulAut.conj f • (C.L : Subgroup A) :=
        Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      rw [hmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    let φ : C.L → C.L := fun l =>
      ⟨(l : A)⁻¹ * f * l * f⁻¹, by
        have h := C.L.mul_mem (C.L.inv_mem l.2) (hconj l l.2)
        simpa [mul_assoc] using h⟩
    have hφinj : Function.Injective φ := by
      intro l₁ l₂ h
      have h' : (l₁ : A)⁻¹ * f * l₁ * f⁻¹ = (l₂ : A)⁻¹ * f * l₂ * f⁻¹ := by
        simpa only [φ] using congrArg Subtype.val h
      have h1 : (l₁ : A)⁻¹ * f * l₁ = (l₂ : A)⁻¹ * f * l₂ := by
        have := congrArg (fun x => x * f) h'
        simpa [mul_assoc] using this
      have h2 : (l₂ : A) * (l₁ : A)⁻¹ * f = f * ((l₂ : A) * (l₁ : A)⁻¹) := by
        have h3 : (l₂ : A) * ((l₁ : A)⁻¹ * f * l₁) =
            (l₂ : A) * ((l₂ : A)⁻¹ * f * l₂) := by rw [h1]
        have h4 : (l₂ : A) * (l₁ : A)⁻¹ * f * l₁ = f * l₂ := by
          simpa [mul_assoc] using h3
        have h5 := congrArg (fun x => x * (l₁ : A)⁻¹) h4
        calc (l₂ : A) * (l₁ : A)⁻¹ * f =
              ((l₂ : A) * (l₁ : A)⁻¹ * f * l₁) * (l₁ : A)⁻¹ := by group
          _ = (f * l₂) * (l₁ : A)⁻¹ := h5
          _ = f * ((l₂ : A) * (l₁ : A)⁻¹) := by group
      have haL : (l₂ : A) * (l₁ : A)⁻¹ ∈ C.L := C.L.mul_mem l₂.2 (C.L.inv_mem l₁.2)
      have ha1 : (l₂ : A) * (l₁ : A)⁻¹ = 1 := hf _ haL h2.symm
      have ha1' : (l₂ : C.L) * l₁⁻¹ = 1 := Subtype.ext (by simpa using ha1)
      exact (by
        calc l₁ = 1 * l₁ := (one_mul _).symm
          _ = ((l₂ : C.L) * l₁⁻¹) * l₁ := by rw [ha1']
          _ = l₂ := by group)
    have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
    intro l hl
    obtain ⟨l₀, hl₀⟩ := hφsurj ⟨l, hl⟩
    have hval : ((φ l₀ : C.L) : A) = l := congrArg Subtype.val hl₀
    rw [← hval]
    have hcomm := Subgroup.commutator_mem_commutator (H₁ := C.K₁) (H₂ := C.K₁)
      (C.K₁.inv_mem (Subgroup.le_normalizer l₀.2)) hfK
    convert hcomm using 1
    have hφval : ((φ l₀ : C.L) : A) = (l₀ : A)⁻¹ * f * l₀ * f⁻¹ := rfl
    rw [hφval, commutatorElement_def]
    group
  refine le_antisymm (Subgroup.commutator_le_self C.K₁) ?_
  intro x hx
  have hqtop : (_root_.commutator ↥C.K₁).map C.quotL = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective C.quotL C.quotL_surjective]
    exact CFSG.GroupTheory.AlternatingFive.commutator_eq_top
  have hx' : C.quotL ⟨x, hx⟩ ∈ (⊤ : Subgroup (alternatingGroup (Fin 5))) := trivial
  rw [← hqtop] at hx'
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hyK : (y : A) ∈ ⁅C.K₁, C.K₁⁆ := by
    rw [← Subgroup.map_subtype_commutator C.K₁]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hmem : (⟨x, hx⟩ * y⁻¹ : ↥C.K₁) ∈ C.quotL.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]
    group
  rw [C.ker_quotL] at hmem
  have hL : (x * (y : A)⁻¹) ∈ C.L := by
    simpa using Subgroup.mem_subgroupOf.1 hmem
  have hxeq : x = (x * (y : A)⁻¹) * (y : A) := by group
  rw [hxeq]
  exact ⁅C.K₁, C.K₁⁆.mul_mem (hLle hL) hyK

theorem commutator_eq_top (C : Config A) [Finite A] (hA : Nat.card A = 20160) :
    commutator A = ⊤ := by
  have hK₁ : ⁅C.K₁, C.K₁⁆ = C.K₁ := C.commutator_normalizer_L
  have hK₂ : ⁅C.K₂, C.K₂⁆ = C.K₂ := C.swap.commutator_normalizer_L
  rw [_root_.commutator_def]
  refine le_antisymm le_top ?_
  have htop : (⊤ : Subgroup A) ≤ C.K₁ ⊔ C.K₂ := by
    intro g _
    obtain ⟨h, hh, m, hm, h', hh', rfl⟩ := C.exists_mul_mul hA g
    exact (C.K₁ ⊔ C.K₂).mul_mem
      ((C.K₁ ⊔ C.K₂).mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hm))
      (Subgroup.mem_sup_left hh')
  calc (⊤ : Subgroup A) ≤ C.K₁ ⊔ C.K₂ := htop
    _ = ⁅C.K₁, C.K₁⁆ ⊔ ⁅C.K₂, C.K₂⁆ := by rw [hK₁, hK₂]
    _ ≤ ⁅(⊤ : Subgroup A), ⊤⁆ :=
      sup_le (Subgroup.commutator_mono le_top le_top) (Subgroup.commutator_mono le_top le_top)

private theorem exists_ne_one_mem_Z (C : Config A) : ∃ z ∈ C.Z, z ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : C.Z = ⊥ := by
    rw [eq_bot_iff_forall]
    intro z hz
    simpa using h z hz
  have hZ4 : Nat.card C.Z = 4 := C.card_Z
  rw [hbot, Subgroup.card_bot] at hZ4
  norm_num at hZ4

private theorem exists_involution_of_even_card {G : Type} [Group G] [Finite G]
    (h : Even (Nat.card G)) :
    ∃ x : G, x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (G := G) (even_iff_two_dvd.mp h)
  refine ⟨x, ?_, ?_⟩
  · have h2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa [pow_two] using h2
  · intro h1
    rw [h1] at hx
    simp at hx

private theorem eq_one_of_mem_odd_card_of_sq {G : Type} [Group G] {F : Subgroup G}
    (hFodd : Odd (Nat.card ↥F)) {x : G} (hxF : x ∈ F) (hx2 : x * x = 1) : x = 1 := by
  have hdvdF : orderOf x ∣ Nat.card ↥F := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers (⟨x, hxF⟩ : F))
    rw [Nat.card_zpowers, Subgroup.orderOf_mk] at h
    rw [← h]
    exact dvd_mul_right _ _
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hx2
  have hcop : Nat.Coprime (Nat.card ↥F) 2 := Nat.coprime_two_right.mpr hFodd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdF hdvd2)

private theorem eq_one_of_odd_orderOf_dvd_pow_two {G : Type} [Group G] {x : G} {n : ℕ}
    (hodd : Odd (orderOf x)) (hdvd : orderOf x ∣ 2 ^ n) : x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    (Nat.Coprime.pow_right n) (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

theorem eq_one_of_forall_smul_eq (C : Config A) [Finite A] (hA : Nat.card A = 20160) (g : A)
    (hg : ∀ p : A ⧸ normalizer (C.L : Set A), g • p = p) : g = 1 := by
  classical
  let F : Subgroup A := (MulAction.toPermHom A (A ⧸ C.K₁)).ker
  have hgF : g ∈ F := by
    rw [show F = (MulAction.toPermHom A (A ⧸ C.K₁)).ker from rfl, MonoidHom.mem_ker,
      Equiv.Perm.ext_iff]
    intro p
    simpa using hg p
  have hFnormal : F.Normal := MonoidHom.normal_ker _
  haveI : F.Normal := hFnormal
  have hFle : F ≤ C.K₁ := by
    intro x hx
    have hx' : x ∈ (MulAction.toPermHom A (A ⧸ C.K₁)).ker := hx
    rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff] at hx'
    have h1 : x • (QuotientGroup.mk (1 : A) : A ⧸ C.K₁) =
        (QuotientGroup.mk (1 : A) : A ⧸ C.K₁) := by
      simpa using hx' (QuotientGroup.mk (1 : A))
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq] at h1
    simpa using C.K₁.inv_mem h1
  rcases Nat.even_or_odd (Nat.card ↥F) with hFeven | hFodd
  ·
    obtain ⟨x, hx2, hx1⟩ := exists_involution_of_even_card hFeven
    have hxA2 : (x : A) * x = 1 := by simpa using congrArg Subtype.val hx2
    have hxA1 : (x : A) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hall : ∀ y : A, y * y = 1 → y ≠ 1 → y ∈ F := by
      intro y hy2 hy1
      obtain ⟨z, hz, hz1⟩ := C.exists_ne_one_mem_Z
      have hconj1 : IsConj z (x : A) := C.isConj_of_mem_Z hz hz1 hxA2 hxA1
      have hconj2 : IsConj z y := C.isConj_of_mem_Z hz hz1 hy2 hy1
      obtain ⟨c, hc⟩ := isConj_iff.mp (hconj1.symm.trans hconj2)
      rw [← hc]
      exact hFnormal.conj_mem (x : A) x.2 c
    have hTle : (C.T : Subgroup A) ≤ F := by
      have hLle : (C.L : Subgroup A) ≤ F := by
        intro l hl
        by_cases hl1 : l = 1
        · rw [hl1]; exact F.one_mem
        · exact hall l (by have := C.isElemAbelian_L.2 l hl; simpa [pow_two] using this) hl1
      have hMle : (C.M : Subgroup A) ≤ F := by
        intro m hm
        by_cases hm1 : m = 1
        · rw [hm1]; exact F.one_mem
        · exact hall m (by have := C.isElemAbelian_M.2 m hm; simpa [pow_two] using this) hm1
      rw [← C.sup_eq]
      exact sup_le hLle hMle
    have hSylow_le : ∀ P : Sylow 2 A, (P : Subgroup A) ≤ F := by
      intro P
      obtain ⟨a, ha⟩ := C.exists_conj_eq P
      rw [ha]
      intro p hp
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hp
      have hmemF := hFnormal.conj_mem t (hTle ht) a
      rw [← MulAut.conj_apply] at hmemF
      exact hmemF
    have haK : ∃ a : A, a ∉ C.K₁ := by
      have hne : C.K₁ ≠ ⊤ := by
        intro htop
        have hc : Nat.card ↥C.K₁ = Nat.card A := by rw [htop, Subgroup.card_top]
        rw [C.card_normalizer_L, hA] at hc
        norm_num at hc
      have hnotle : ¬ (⊤ : Subgroup A) ≤ C.K₁ := by rwa [top_le_iff]
      obtain ⟨a, -, ha⟩ := SetLike.not_le_iff_exists.mp hnotle
      exact ⟨a, ha⟩
    obtain ⟨a, ha⟩ := haK
    have hPle : ((a • C.T : Sylow 2 A) : Subgroup A) ≤ C.K₁ :=
      (hSylow_le (a • C.T)).trans hFle
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥C.K₁ C.isSylow_normalizer_L
      ((a • C.T).subtype hPle)
    have hsub : MulAut.conj (k : A) • (C.T : Subgroup A) =
        MulAut.conj a • (C.T : Subgroup A) := by
      have hcoe : ((k • C.isSylow_normalizer_L : Sylow 2 ↥C.K₁) : Subgroup ↥C.K₁) =
          ((a • C.T).subtype hPle : Subgroup ↥C.K₁) :=
        congrArg (fun Q : Sylow 2 ↥C.K₁ => (Q : Subgroup ↥C.K₁)) hk
      rw [Sylow.coe_subgroup_smul, C.coe_isSylow_normalizer_L, Sylow.coe_subtype,
        Subgroup.conj_smul_subgroupOf C.T_le_normalizer_L k, Sylow.coe_subgroup_smul] at hcoe
      have hPle' : MulAut.conj a • (C.T : Subgroup A) ≤ C.K₁ := hPle
      have hinf : (MulAut.conj (k : A) • (C.T : Subgroup A)) ⊓ C.K₁ =
          MulAut.conj a • (C.T : Subgroup A) := by
        have h := Subgroup.subgroupOf_inj.mp hcoe
        rw [inf_eq_left.mpr hPle'] at h
        exact h
      have hle : MulAut.conj a • (C.T : Subgroup A) ≤
          MulAut.conj (k : A) • (C.T : Subgroup A) := by
        rw [← hinf]; exact inf_le_left
      have hcard : Nat.card ↥(MulAut.conj a • (C.T : Subgroup A)) =
          Nat.card ↥(MulAut.conj (k : A) • (C.T : Subgroup A)) := by
        rw [card_conj, card_conj]
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm
    have hfix : MulAut.conj ((k : A)⁻¹ * a) • (C.T : Subgroup A) = (C.T : Subgroup A) := by
      rw [map_mul, mul_smul, ← hsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hmem : (k : A)⁻¹ * a ∈ normalizer (C.T : Set A) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix
    have hmem' : (k : A)⁻¹ * a ∈ C.K₁ := (C.normalizer_T_le hmem).1
    have hak : a ∈ C.K₁ := by
      have h := C.K₁.mul_mem k.2 hmem'
      simpa [mul_assoc] using h
    exact absurd hak ha
  ·
    have hFL : ⁅F, C.L⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro f hf l hl
      have hmemF : ⁅f, l⁆ ∈ F :=
        Subgroup.commutator_le_left F C.L (Subgroup.commutator_mem_commutator hf hl)
      have hmemL : ⁅f, l⁆ ∈ C.L := by
        have hconj : f * l * f⁻¹ ∈ C.L := by
          have hmap : MulAut.conj f • (C.L : Subgroup A) = C.L :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (hFle hf)
          have hmem : MulAut.conj f l ∈ MulAut.conj f • (C.L : Subgroup A) :=
            Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
          rw [hmap] at hmem
          simpa [MulAut.conj_apply] using hmem
        have heq : ⁅f, l⁆ = (f * l * f⁻¹) * l⁻¹ := by
          rw [commutatorElement_def]
        rw [heq]
        exact C.L.mul_mem hconj (C.L.inv_mem hl)
      have hx2 : ⁅f, l⁆ * ⁅f, l⁆ = 1 := by
        have := C.isElemAbelian_L.2 ⁅f, l⁆ hmemL
        simpa [pow_two] using this
      simpa using eq_one_of_mem_odd_card_of_sq hFodd hmemF hx2
    have hFcent : F ≤ Subgroup.centralizer (C.L : Set A) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFL
    have hFL2 : F ≤ C.L := hFcent.trans C.centralizer_L_le
    have hFbot : F = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      exact eq_one_of_mem_odd_card_of_sq hFodd hx (by
        have := C.isElemAbelian_L.2 x (hFL2 hx)
        simpa [pow_two] using this)
    rw [hFbot, Subgroup.mem_bot] at hgF
    exact hgF

theorem center_eq_bot (C : Config A) [Finite A] (hA : Nat.card A = 20160) :
    Subgroup.center A = ⊥ := by
  rw [eq_bot_iff_forall]
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1
  rcases Nat.even_or_odd (orderOf z) with hev | hod
  ·
    obtain ⟨x, hx2, hx1⟩ := exists_involution_of_even_card (G := ↥(Subgroup.zpowers z))
      (by rw [Nat.card_zpowers]; exact hev)
    have hxA2 : (x : A) * x = 1 := by simpa using congrArg Subtype.val hx2
    have hxA1 : (x : A) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxcenter : (x : A) ∈ Subgroup.center A := (Subgroup.zpowers_le.mpr hz) x.2
    have hcent : Subgroup.centralizer ({(x : A)} : Set A) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact (Subgroup.mem_center_iff.mp hxcenter y).symm
    have h2A : IsPGroup 2 ↥(Subgroup.centralizer ({(x : A)} : Set A)) :=
      C.isPGroup_centralizer (x : A) hxA2 hxA1
    rw [hcent] at h2A
    have htop : (⊤ : Subgroup A) = C.T := C.T.is_maximal' h2A le_top
    have h64 : Nat.card A = 64 := by
      rw [← Subgroup.card_top (G := A), htop, C.card_T]
    omega
  ·
    obtain ⟨w, hwZ, hw1⟩ := C.exists_ne_one_mem_Z
    have hw2 : w * w = 1 := C.mul_self_eq_one_of_mem_Z hwZ
    have hzw : w * z = z * w := Subgroup.mem_center_iff.mp hz w
    have hzT : z ∈ C.T := by
      have hzcentw : z ∈ Subgroup.centralizer ({w} : Set A) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hzw
      rwa [C.centralizer_eq_T hwZ hw1] at hzcentw
    have hdvd : orderOf z ∣ 2 ^ 6 := by
      have h := Subgroup.card_mul_index (Subgroup.zpowers (⟨z, hzT⟩ : C.T))
      rw [Nat.card_zpowers, Subgroup.orderOf_mk] at h
      have h' : orderOf z * (Subgroup.zpowers (⟨z, hzT⟩ : C.T)).index = 64 := by
        rw [h]; exact C.card_T
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← h']
      exact dvd_mul_right _ _
    exfalso
    exact hz1 (eq_one_of_odd_orderOf_dvd_pow_two hod hdvd)

theorem isSteinerPlane (C : Config A) [Finite A] (hA : Nat.card A = 20160) :
    IsSteinerPlane (lineSet (normalizer (C.L : Set A)) (normalizer (C.M : Set A))) :=
  isSteinerPlane_lineSet C.relIndex_inf_normalizer_L C.relIndex_inf_normalizer_M
    (C.exists_mul_mul hA) C.eq_line_of_two_points

theorem typeL34
    (C : Config A) [Finite A] (hA : Nat.card A = 20160) :
    CFSG.ComponentClassification.AS81.TypeL34 A :=
  typeL34_of_steinerPlane (normalizer (C.L : Set A)) (normalizer (C.M : Set A))
    (C.isSteinerPlane hA) C.card_normalizer_L (C.eq_one_of_forall_smul_eq hA)
    (C.commutator_eq_top hA)

end Config

end CFSG.Quasithin.L34CIT
