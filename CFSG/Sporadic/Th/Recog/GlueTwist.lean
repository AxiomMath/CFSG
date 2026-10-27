module

public import CFSG.Sporadic.Th.Recog.GlueFacts
public import CFSG.Sporadic.Th.Recog.AutD
public import CFSG.Sporadic.Th.Recog.YGhat
public import CFSG.Sporadic.Th.Recog.SplitT
public import CFSG.Sporadic.Th.Recog.ConjE8

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords
open CFSG.GH74.QTGen4.Recog.G23 (Ghat ghat_simple ghat_card ghat_involutions_conj)

variable {G : Type} [Group G] [Finite G]

section Psi


theorem ThCore.orderOf_psi_t (C : ThCore G) : orderOf (C.ψ tLetter : G) = 3 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_tLetter]

theorem ThCore.psi_mem_normalizer (C : ThCore G) {m : ↥Max3.M}
    (hm : (m : ↥J) ∈ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) :
    (C.ψ m : G) ∈ Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G) := by
  rw [mem_normalizer_zpowers_iff orderOf_hswJ_six] at hm
  rw [mem_normalizer_zpowers_iff C.orderOf_psi_t]
  have key : ∀ n : ↥Max3.M, (m : ↥J) * hswJ 6 * (m : ↥J)⁻¹ = (n : ↥J) →
      (C.ψ m : G) * (C.ψ tLetter : G) * (C.ψ m : G)⁻¹ = (C.ψ n : G) := by
    intro n hn
    have h : m * tLetter * m⁻¹ = n := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hn
    rw [← h, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rcases hm with h | h
  · exact Or.inl (key tLetter h)
  · right
    rw [key tLetter⁻¹ h, map_inv, Subgroup.coe_inv]

end Psi

section Chain


theorem ThCore.centralizer_t_split (C : ThCore G) (hMF : GlueMFacts) :
    ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G) ∧
      K ⊓ Subgroup.zpowers (C.ψ tLetter : G) = ⊥ ∧
      K ⊔ Subgroup.zpowers (C.ψ tLetter : G) =
        Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G) ∧
      K = ⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
        Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆ ∧
      Nonempty (↥K ≃* Ghat) := by
  obtain ⟨E₀, e₀, hE⟩ := hMF.e8
  have htM : orderOf tLetter = 3 := orderOf_tLetter
  have hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z := C.psi_z
  have he₀2 : e₀ * e₀ = 1 := hE.sq e₀ hE.mem
  have hC13 := exists_conj_le_Q C hψa hE.mem_Q he₀2 hE.ne_one hE.ne_z hE.card_centralizer
    hE.abelian hE.three
  have hj : (C.ψ e₀ : G) ∈ Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← map_mul, ← map_mul, hE.comm_t e₀ hE.mem]
  have hj2 : orderOf (C.ψ e₀ : G) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact he₀2) hE.ne_one
  have hy := C.exists_conj_eq_z htM hMF.conj_three hj hj2
  let tT : ↥(Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)) :=
    ⟨(C.ψ tLetter : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcen : Subgroup.zpowers tT ≤ Subgroup.center _ := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  haveI : (Subgroup.zpowers tT).Normal := Subgroup.normal_of_le_center hcen
  have hG1 := C.exists_g23One htM hMF.card_centralizer_t hMF.g1
    (QuotientGroup.mk' (Subgroup.zpowers tT)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  have hY := exists_surjective_ghat C hψa htM hE.mem hE.ne_one hE.ne_z hE.comm hE.sq hE.card
    hE.z_mem hE.comm_t hE.cent hE.trans hMF.center_t hC13 hy
    (QuotientGroup.mk' (Subgroup.zpowers tT)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hG1
  have h7 : ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) := by
    rw [hMF.card_centralizer_t]
    norm_num
  exact centralizer_split C tLetter htM hMF.complement_t h7 ghat_simple ghat_card
    ghat_involutions_conj hY

end Chain

section Twist


@[expose] noncomputable def DJtoY :
    ↥DJ →* ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) :=
  Subgroup.inclusion DJ_le_normalizer

theorem coe_DJtoY (x : ↥DJ) :
    ((DJtoY x : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) = x :=
  rfl

@[expose] noncomputable def ThCore.psiDY (C : ThCore G) :
    ↥DJ →* ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)) :=
  (C.psiG.comp (Subgroup.inclusion DJ_le_M)).codRestrict _ fun x =>
    C.psi_mem_normalizer (DJ_le_normalizer x.2)

theorem ThCore.coe_psiDY (C : ThCore G) (x : ↥DJ) :
    (C.psiDY x : G) = (C.ψ (Subgroup.inclusion DJ_le_M x) : G) :=
  rfl

@[expose] def ThCore.GlueAt (C : ThCore G)
    (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))) (k : OutD) : Prop :=
  ∀ x : ↥DJ, ψ' (DJtoY (fAut k x)) = C.psiDY x

@[expose] def ThCore.KCompat (C : ThCore G)
    (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))) : Prop :=
  ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
    (y : ↥J) ∈ Subgroup.closure (Set.range lJ) ↔
    (ψ' y : G) ∈ ⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
      Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆

theorem ThCore.KCompat.trans_conj {C : ThCore G}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))} (h : C.KCompat ψ')
    (g : ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))) :
    C.KCompat (ψ'.trans (MulAut.conj g)) := by
  intro y
  rw [h y, MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp
    (mem_normalizer_commutator_centralizer C.orderOf_psi_t g.2) _

theorem ThCore.KCompat.conj_trans {C : ThCore G}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))} (h : C.KCompat ψ')
    (hK : Subgroup.closure (Set.range lJ) = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
      Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆)
    (g : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) :
    C.KCompat ((MulAut.conj g).trans ψ') := by
  intro y
  rw [MulEquiv.trans_apply, ← h, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hK]
  exact Subgroup.mem_normalizer_iff.mp
    (mem_normalizer_commutator_centralizer orderOf_hswJ_six g.2) _

theorem ThCore.KCompat.symm_trans {C : ThCore G}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))} (h : C.KCompat ψ')
    (ι : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)))
    (hι : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) ∈ Subgroup.closure (Set.range lJ) → ι y = y) :
    C.KCompat (ι.symm.trans ψ') := by
  intro y
  rw [MulEquiv.trans_apply, ← h]
  constructor
  · intro hy
    rw [(MulEquiv.symm_apply_eq ι).mpr (hι y hy).symm]
    exact hy
  · intro hy
    have h2 := hι _ hy
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2]
    exact hy

theorem iota_DJtoY
    (ι : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)))
    (h1 : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) ∈ Subgroup.closure (Set.range lJ) → ι y = y)
    (h2 : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) = hswJ 6 → (ι y : ↥J) = (hswJ 6)⁻¹)
    (h3 : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) = hswJ 7 → ι y = y)
    (hdJ : ∀ j : Fin 6, j ≠ 4 → j ≠ 5 → dJ j ∈ Subgroup.closure (Set.range lJ)) (x : ↥DJ) :
    ι (DJtoY x) = DJtoY (iotaD x) := by
  let φ₁ : ↥DJ →* ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) :=
    (ι : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) →*
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))).comp DJtoY
  let φ₂ : ↥DJ →* ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) :=
    DJtoY.comp (iotaD : ↥DJ →* ↥DJ)
  have h : φ₁ = φ₂ := by
    apply DJ_hom_ext
    intro j
    simp only [φ₁, φ₂, MonoidHom.comp_apply, MonoidHom.coe_coe]
    by_cases h5 : j = 5
    · subst h5
      apply Subtype.ext
      rw [h2 _ rfl, iotaD_t, map_inv, Subgroup.coe_inv, coe_DJtoY, coe_dJD, dJ_five]
    by_cases h4 : j = 4
    · subst h4
      rw [h3 _ rfl, iotaD_letter 4 (by decide)]
    rw [h1 _ (hdJ j h4 h5), iotaD_letter j h5]
  exact DFunLike.congr_fun h x

theorem ThCore.GlueAt.false_of_true {C : ThCore G}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))} {k : Twist}
    (h : C.GlueAt ψ' (k, true))
    (ι : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)))
    (hι : ∀ x : ↥DJ, ι (DJtoY x) = DJtoY (iotaD x)) :
    C.GlueAt (ι.symm.trans (ψ'.trans (MulAut.conj (C.psiDY (mD k))))) (k, false) := by
  intro x
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply, partner k x]
  have e : ι.symm (DJtoY (iotaD (fAut (k, true) ((mD k)⁻¹ * x * mD k)))) =
      DJtoY (fAut (k, true) ((mD k)⁻¹ * x * mD k)) := by
    rw [MulEquiv.symm_apply_eq, hι]
  rw [e, h]
  simp only [map_mul, map_inv]
  group

theorem ThCore.GlueAt.letters {C : ThCore G}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))} {k : Twist}
    (h : C.GlueAt ψ' (k, false)) (j : Fin 6) :
    (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j) := by
  have e1 : lettersY (dLet j) = DJtoY (fAut (k, false) ((fAut (k, false)).symm (dJD j))) := by
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_lettersY _ (dLet_ne j).2, coe_DJtoY, coe_dJD]
    rfl
  have e2 : Subgroup.inclusion DJ_le_M ((fAut (k, false)).symm (dJD j)) =
      wprod lettersM (wY k j) := by
    apply Subtype.ext
    rw [coe_wprod_lettersM (fun l hl => (wY_letters k j l hl).1), ← fAut_symm_letter_twist k j]
    rfl
  rw [e1, h, ThCore.coe_psiDY, e2, ← C.psiG_apply, map_wprod]
  rfl

theorem ThCore.exists_glueAt (C : ThCore G)
    (h3 : ∀ x w : ↥Max3.M, orderOf x = 3 → w * w = 1 → w ≠ 1 → (w : J) ≠ Max3.z →
      w * x = x * w → ∃ m : ↥Max3.M, m * x * m⁻¹ = tLetter)
    (hMD : Max3.M ⊓ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J) = DJ)
    (ψ'₀ : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)))
    (ht : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) = hswJ 6 → (ψ'₀ y : G) = C.ψ tLetter)
    (hK : C.KCompat ψ'₀)
    (hK₀ : Subgroup.closure (Set.range lJ) = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
      Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆) :
    ∃ (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))) (k : OutD),
      C.GlueAt ψ' k ∧ C.KCompat ψ' := by
  classical
  have haY : lettersY 0 * lettersY 6 = lettersY 6 * lettersY 0 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_lettersY 0 (by decide),
      coe_lettersY 6 (by decide)]
    exact hswJ_comm_six 0 (by decide)
  have hj : (ψ'₀ (lettersY 0) : G) ∈
      Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G) := by
    have h := congrArg Subtype.val (congrArg ψ'₀ haY)
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      ht (lettersY 6) (coe_lettersY 6 (by decide))] at h
    exact Subgroup.mem_centralizer_singleton_iff.mpr h
  have ha1 : lettersY 0 ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    rw [coe_lettersY 0 (by decide), Subgroup.coe_one, hswJ_zero, ← Max3.z_eq_a] at h'
    exact Max3.z_ne_one h'
  have hj2 : orderOf (ψ'₀ (lettersY 0) : G) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ha1
    apply Subtype.ext
    rw [sq, Subgroup.coe_mul, coe_lettersY 0 (by decide), Subgroup.coe_one]
    exact hswJ_mul_self 0 (by decide)
  obtain ⟨y, hy, hyz⟩ := C.exists_conj_eq_z orderOf_tLetter h3 hj hj2
  let gy : ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)) :=
    ⟨y, centralizer_le_normalizer_zpowers _ hy⟩
  let ψ'₁ := ψ'₀.trans (MulAut.conj gy)
  have hψa : (ψ'₁ (lettersY 0) : G) = C.z := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact hyz
  have hmemM : ∀ x : ↥DJ, ((ψ'₁.symm (C.psiDY x) :
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈ Max3.M := by
    intro x
    have hc : ((ψ'₁.symm (C.psiDY x) :
        ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈
        Subgroup.centralizer ({(a : ↥J)} : Set ↥J) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hswJ_zero, ← coe_lettersY 0 (by decide),
        ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      refine congrArg Subtype.val (ψ'₁.injective ?_)
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hψa,
        ThCore.coe_psiDY]
      exact Subgroup.mem_centralizer_singleton_iff.mp (C.ψ (Subgroup.inclusion DJ_le_M x)).2
    rwa [CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts] at hc
  have hmem : ∀ x : ↥DJ, ((ψ'₁.symm (C.psiDY x) :
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈ DJ := by
    intro x
    have hM : ((ψ'₁.symm (C.psiDY x) :
        ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈
        Max3.M ⊓ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J) :=
      ⟨hmemM x, (ψ'₁.symm (C.psiDY x)).2⟩
    rw [hMD] at hM
    exact hM
  let f : ↥DJ →* ↥DJ :=
    ((Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)).subtype.comp
      ((ψ'₁.symm : ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)) →*
        ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))).comp
        C.psiDY)).codRestrict DJ hmem
  have hf : Function.Injective f := by
    intro x₁ x₂ h
    have h' := congrArg Subtype.val h
    simp only [f, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MonoidHom.coe_coe] at h'
    have h'' := ψ'₁.symm.injective (Subtype.ext h')
    have h3 := congrArg Subtype.val h''
    rw [ThCore.coe_psiDY, ThCore.coe_psiDY] at h3
    exact Subgroup.inclusion_injective DJ_le_M (C.ψ.injective (Subtype.ext h3))
  let α : ↥DJ ≃* ↥DJ := MulEquiv.ofBijective f hf.bijective_of_finite
  obtain ⟨k, m, hm⟩ := aut_DJ α
  refine ⟨(MulAut.conj (DJtoY m)).trans ψ'₁, k, fun x => ?_,
    (hK.trans_conj gy).conj_trans hK₀ (DJtoY m)⟩
  have e : DJtoY (α x) = ψ'₁.symm (C.psiDY x) := rfl
  rw [MulEquiv.trans_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hm, e,
    MulEquiv.apply_symm_apply]

end Twist

section Glue


theorem ThCore.exists_glue (C : ThCore G) (hMF : GlueMFacts) :
    ∃ (k : Twist) (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
        ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))),
      (∀ j : Fin 6,
        (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j)) ∧
      ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) ∈ Subgroup.closure (Set.range lJ) ↔
          (ψ' y : G) ∈ ⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
            Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆ := by
  have hJ := splitJ_of_core rfl (thCoreJ.centralizer_t_split hMF)
  have hK₀ := closure_lJ_eq_commutator ghat_simple ghat_card nonempty_K₀_ghat hJ
  obtain ⟨ψ'₀, ht, hK⟩ := exists_normT_iso C rfl hMF.card_centralizer_t ghat_simple ghat_card
    nonempty_K₀_ghat hJ (C.centralizer_t_split hMF)
  obtain ⟨ψ', ⟨k, b⟩, hglue, hK'⟩ := C.exists_glueAt hMF.conj_three
    (M_inf_normalizer_eq_DJ rfl hMF.card_centralizer_t) ψ'₀ ht hK hK₀
  cases b
  · exact ⟨k, ψ', hglue.letters, hK'⟩
  · obtain ⟨ι, h1, h2, h3⟩ := exists_iota ghat_simple ghat_card nonempty_K₀_ghat hJ
    have hι := iota_DJtoY ι h1 h2 h3
      (dJ_mem_closure_lJ ghat_simple ghat_card nonempty_K₀_ghat hJ)
    exact ⟨k, _, (hglue.false_of_true ι hι).letters, (hK'.trans_conj _).symm_trans ι h1⟩

end Glue

end CFSG.Sporadic.Th.Recog
