module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairGen
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin
public import CFSG.LocalAnalysis.WeakClosure81.W183Cited
import CFSG.LocalAnalysis.WeakClosure81.W183B2Pair
import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
import CFSG.LocalAnalysis.WeakClosure81.W183FourBigSideAux1
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator
  lieOrderDivisor)

variable {G : Type} [Group G] [Finite G]

private theorem w183fourside_card_alt6 {X : Type} [Group X] (h : IsAlt X 6) :
    Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

private theorem w183fourside_card_l3_1 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsL3 X 1) : Nat.card X = 168 := by
  obtain ⟨-, hM, -⟩ := hO X .PSL 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]

private theorem w183fourside_card_l3_2 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsL3 X 2) : Nat.card X = 20160 := by
  obtain ⟨-, hM, -⟩ := hO X .PSL 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
  rw [hd] at hM
  have hnum : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by
    simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]
  rw [hnum] at hM
  omega

private theorem w183fourside_card_sp4_2 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsSp4 X 2) : Nat.card X = 979200 := by
  obtain ⟨-, hM, -⟩ := hO X .PSp 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]

private theorem w183fourside_conjSubgroup_injective (s : G) :
    Function.Injective (fun A : Subgroup G => conjSubgroup A s) := by
  intro A B h
  have h' := congrArg (fun C : Subgroup G => conjSubgroup C s⁻¹) h
  simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using h'

private theorem w183fourside_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

private theorem w183fourside_isComponentModN_map_mulEquiv {K H L : Subgroup G} (e : G ≃* G)
    (hK : K.map e.toMonoidHom = K) (hH : H.map e.toMonoidHom = H)
    (h : IsComponentModN K H L) :
    IsComponentModN K H (L.map e.toMonoidHom) := by
  have hfe : Function.Injective e.toMonoidHom := fun a _b hab => e.injective (by simpa using hab)
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : e.symm k ∈ K := by
      rw [← hK] at hk
      obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.1 hk
      have hkk : k' = e.symm k := by
        rw [← hk'eq]
        change k' = e.symm (e k')
        rw [e.symm_apply_apply]
      rwa [hkk] at hk'K
    exact Subgroup.mem_map.2 ⟨e.symm k, h.2.1 hk', by simp⟩
  · rintro x ⟨l, hl, rfl⟩
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.2.2.1 hl)
  · have hsub := h.2.2.2.1.map e.toMonoidHom
    rwa [hH] at hsub
  · refine w183fourside_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom hfe) ?_ h.2.2.2.2
    intro l
    constructor
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK] at hl
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.1 hl
      have hkl : k = l := e.injective hkeq
      rwa [hkl] at hkK

private theorem w183fourside_conjSubgroup_isComponentModN {K H L : Subgroup G}
    (h : IsComponentModN K H L) {t : G} (ht : t ∈ H) :
    IsComponentModN K H (conjSubgroup L t) := by
  have hKH : K ≤ H := h.2.1.trans h.2.2.1
  have hnormK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp h.1
  have hKmap : K.map (MulAut.conj t⁻¹).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hnormK (H.inv_mem ht))
  have hHmap : H.map (MulAut.conj t⁻¹).toMonoidHom = H :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer (H.inv_mem ht))
  have := w183fourside_isComponentModN_map_mulEquiv (MulAut.conj t⁻¹) hKmap hHmap h
  simpa only [conjSubgroup] using this

private theorem w183fourside_hasQuotShape_conj {K H L : Subgroup G} {t : G} (ht : t ∈ H)
    (h : IsComponentModN K H L) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape (conjSubgroup L t) K P := by
  have hKH : K ≤ H := h.2.1.trans h.2.2.1
  have hnormK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp h.1
  have hKmem : ∀ l : ↥L, (l : G) ∈ K ↔
      ((Subgroup.equivMapOfInjective L (MulAut.conj t⁻¹).toMonoidHom
        (fun a b hab => (MulAut.conj t⁻¹).injective hab)) l : G) ∈ K := by
    intro l
    change (l : G) ∈ K ↔ (MulAut.conj t⁻¹) (l : G) ∈ K
    have h1 := (Subgroup.mem_normalizer_iff'' (H := K) (g := t)).mp (hnormK ht) (l : G)
    simpa [MulAut.conj_apply] using h1
  have hQ' := w183fourside_hasQuotShape_of_mulEquiv (K := K)
    (Subgroup.equivMapOfInjective L (MulAut.conj t⁻¹).toMonoidHom
      (fun a b hab => (MulAut.conj t⁻¹).injective hab)) hKmem hQ
  simpa only [conjSubgroup] using hQ'

private theorem w183fourside_pRank_five_subgroupOf {X Y : Subgroup G} (h : X ≤ Y) :
    CFSG.Open.pRank 5 (X.subgroupOf Y) = CFSG.Open.pRank 5 X := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (X.subgroupOf Y),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
    (Subgroup.subgroupOfEquivOfLe h)

private theorem w183fourside_isCyclic_of_isSylowIn_img {J E : Subgroup G} (M : ModDataE J E)
    {S : Subgroup G} (hSJ : S ≤ J) (hS : CFSG.Open.pRank 5 (S.subgroupOf J) ≤ 1)
    {P : Subgroup (LGL 2 M.W)} (hP : IsSylowIn 5 P (M.img S)) : IsCyclic ↥P := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let T : Subgroup ↥J := S.subgroupOf J
  let φ : ↥T →* ↥(M.img S) := (M.ρ.comp T.subtype).codRestrict (M.img S) (fun t =>
    Subgroup.mem_map.mpr ⟨t.1, t.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    intro r
    obtain ⟨j, hj, hjr⟩ := M.mem_img.1 r.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjr⟩
  have hsurj : Function.Surjective (Sylow.mapSurjective (p := 5) (f := φ) hφs) :=
    Sylow.mapSurjective_surjective (p := 5) (f := φ) (hf := hφs)
  obtain ⟨Q, hQ⟩ := hsurj hP.toSylow
  have hQmap : (Q : Subgroup ↥T).map φ = P.subgroupOf (M.img S) := by
    have h1 : ((Sylow.mapSurjective hφs Q : Sylow 5 ↥(M.img S)) : Subgroup ↥(M.img S)) =
        (Q : Subgroup ↥T).map φ := Sylow.coe_mapSurjective (P := Q) (hf := hφs)
    rw [hQ] at h1
    rw [← h1, IsSylowIn.coe_toSylow hP]
  haveI hQp : IsPGroup 5 (Q : Subgroup ↥T) := Q.isPGroup'
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥T) := by
    refine CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_five (by norm_num) hQp le_top ?_
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup T]
    exact hS
  haveI := hQcyc
  have hmap' : (Q : Subgroup ↥T).map ((M.img S).subtype.comp φ) = P := by
    rw [show (Q : Subgroup ↥T).map ((M.img S).subtype.comp φ) =
        ((Q : Subgroup ↥T).map φ).map (M.img S).subtype from
      (Subgroup.map_map (Q : Subgroup ↥T) (M.img S).subtype φ).symm]
    rw [hQmap]
    exact Subgroup.map_subgroupOf_eq_of_le hP.le
  let ψ : ↥(Q : Subgroup ↥T) →* ↥P :=
    (((M.img S).subtype.comp φ).comp (Q : Subgroup ↥T).subtype).codRestrict P (fun q => by
      have hmem : ((M.img S).subtype.comp φ).comp (Q : Subgroup ↥T).subtype q ∈
          (Q : Subgroup ↥T).map ((M.img S).subtype.comp φ) :=
        Subgroup.mem_map.mpr ⟨q, q.2, rfl⟩
      rwa [hmap'] at hmem)
  have hψsurj : Function.Surjective ψ := by
    intro p
    have hp : (p : LGL 2 M.W) ∈ (Q : Subgroup ↥T).map ((M.img S).subtype.comp φ) := by
      rw [hmap']; exact p.2
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hp
    exact ⟨⟨q, hq⟩, Subtype.ext hqeq⟩
  exact isCyclic_of_surjective ψ hψsurj

private theorem w183fourside_not_dvd_of_shape (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2) : ¬ 13 ∣ Nat.card X := by
  intro h13
  rcases h with h6 | h31 | h32 | hsp
  · rw [w183fourside_card_alt6 h6] at h13; norm_num at h13
  · rw [w183fourside_card_l3_1 hO h31] at h13; norm_num at h13
  · rw [w183fourside_card_l3_2 hO h32] at h13; norm_num at h13
  · rw [w183fourside_card_sp4_2 hO hsp] at h13; norm_num at h13

private theorem w183fourside_not_dvd_relIndex {K L X T H : Subgroup G} (hKH : K ≤ H)
    (hKL : K ≤ L) (hLX : L ≤ X) (hXH : X ≤ H) (hXsup : X ⊔ T = H)
    (hXnorm : T ≤ Subgroup.normalizer (X : Set G)) (hT2 : IsPGroup 2 T)
    (hdvd : L.relIndex X ∣ K.relIndex L) (hnot13 : ¬ 13 ∣ K.relIndex L) :
    ¬ 13 ∣ K.relIndex H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : K ≤ X := hKL.trans hLX
  have hprime : Nat.Prime 13 := by norm_num
  intro h13
  rw [← Subgroup.relIndex_mul_relIndex (H := K) (K := X) (L := H) hKX hXH] at h13
  rcases (Nat.Prime.dvd_mul hprime).mp h13 with h13a | h13b
  · rw [← Subgroup.relIndex_mul_relIndex (H := K) (K := L) (L := X) hKL hLX] at h13a
    rcases (Nat.Prime.dvd_mul hprime).mp h13a with h13L | h13LX
    · exact hnot13 h13L
    · exact hnot13 (h13LX.trans hdvd)
  · have hrel : X.relIndex H = X.relIndex T := by
      rw [← hXsup, sup_comm]
      exact CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer hXnorm
    rw [hrel] at h13b
    have hdvd2 : X.relIndex T ∣ Nat.card ↥T := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_dvd_card (H := X.subgroupOf T) (G := ↥T)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hT2
    have h13T : 13 ∣ Nat.card ↥T := h13b.trans hdvd2
    rw [hn] at h13T
    exact absurd (hprime.dvd_of_dvd_pow h13T) (by norm_num)

section Certified


theorem w183four_not_thirteen_dvd (hO : LieOrderFormulasInput) {D : Data G}
    {V₀ V H : Subgroup G} {i : ℕ} (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2))
    (hcases : (∀ t ∈ D.T, conjSubgroup L t = L) ∨
      ∃ t ∈ D.T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) :
    ¬ 13 ∣ Nat.card ↥(M.img H) := by
  classical
  have hKH : kerMV V H ≤ H := kerMV_le_self V H
  have hKL : kerMV V H ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hHinfC : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) = kerMV V H :=
    le_antisymm x.hyp.inf_centralizer_eOmegaZ_le_kerMV (le_inf hKH hK)
  have hcardH : Nat.card ↥(M.img H) = (kerMV V H).relIndex H := by
    rw [M.card_img le_rfl]
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (eOmegaZ H D.T : Set G)) H,
      inf_comm, hHinfC]
  rw [hcardH]
  have hnot13L : ¬ 13 ∣ (kerMV V H).relIndex L := by
    obtain ⟨X, _hXg, φ, hs, hk, hP⟩ := hX
    have hker : φ.ker = (kerMV V H).subgroupOf L := by
      ext k
      rw [MonoidHom.mem_ker, hk k, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
      Subgroup.card_top]
    exact w183fourside_not_dvd_of_shape hO hP
  rcases hcases with hn | ⟨t, htT, hne, hall⟩
  · have hTn : D.T ≤ Subgroup.normalizer (L : Set G) := fun s hs =>
      conjSubgroup_eq_iff_mem_normalizer.mp (hn s hs)
    exact w183fourside_not_dvd_relIndex hKH hKL le_rfl hLH hLT hTn
      x.hyp.isSylowIn_T.isPGroup (by rw [Subgroup.relIndex_self]; exact one_dvd _) hnot13L
  · let L₂ : Subgroup G := conjSubgroup L t
    have hL₂H : L₂ ≤ H := by
      intro y hy
      have hy' : y ∈ conjSubgroup L t := hy
      have hyL : t * y * t⁻¹ ∈ L := (mem_conjSubgroup_iff).mp hy'
      have hyy : y = t⁻¹ * (t * y * t⁻¹) * t := by group
      rw [hyy]
      exact H.mul_mem (H.mul_mem (H.inv_mem (hDT htT)) (hLH hyL)) (hDT htT)
    have hHnormK : H ≤ Subgroup.normalizer (kerMV V H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hKL.trans hLH)).mp hL.1
    have hKmap : (kerMV V H).map (MulAut.conj t⁻¹).toMonoidHom = kerMV V H :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hHnormK (H.inv_mem (hDT htT)))
    have hK₂ : kerMV V H ≤ L₂ := by
      have h := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hKL
      rwa [hKmap] at h
    have hL₂s : ∀ s ∈ D.T, conjSubgroup L₂ s = L ∨ conjSubgroup L₂ s = L₂ := by
      intro s hs
      have h := hall (t * s) (D.T.mul_mem htT hs)
      rw [← conjSubgroup_conjSubgroup L t s] at h
      exact h
    have hXnorm : D.T ≤ Subgroup.normalizer ((L ⊔ L₂ : Subgroup G) : Set G) := by
      intro s hs
      rw [← conjSubgroup_eq_iff_mem_normalizer]
      have h1 := hall s hs
      have h2 := hL₂s s hs
      have hconj : conjSubgroup (L ⊔ L₂) s = conjSubgroup L s ⊔ conjSubgroup L₂ s := by
        rw [conjSubgroup, Subgroup.map_sup]
        rfl
      rw [hconj]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso
        exact hne (w183fourside_conjSubgroup_injective s ((h1.trans h2.symm).symm))
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
      · exfalso
        exact hne (w183fourside_conjSubgroup_injective s ((h1.trans h2.symm).symm))
    have hL₂normL : L₂ ≤ Subgroup.normalizer (L : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr fun b hb l hl => ?_
      have hk : l * b * l⁻¹ * b⁻¹ ∈ kerMV V H :=
        w183_components_commute hL
          (w183fourside_conjSubgroup_isComponentModN hL (hDT htT)) hne.symm l hl b hb
      rw [show b * l * b⁻¹ = (l * b * l⁻¹ * b⁻¹)⁻¹ * l from by group]
      exact L.mul_mem (hKL ((kerMV V H).inv_mem hk)) hl
    have hdvd : L.relIndex (L ⊔ L₂) ∣ (kerMV V H).relIndex L := by
      have hrel : L.relIndex (L ⊔ L₂) = L.relIndex L₂ := by
        rw [sup_comm]
        exact CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer hL₂normL
      rw [hrel]
      have h1 : (L ⊓ L₂).relIndex L₂ ∣ (kerMV V H).relIndex L₂ :=
        Subgroup.relIndex_dvd_of_le_left (K := L ⊓ L₂) (L := L₂)
          (le_inf hKL hK₂)
      rw [Subgroup.inf_relIndex_right] at h1
      have h2 : (kerMV V H).relIndex L₂ = (kerMV V H).relIndex L := by
        have hmap := Subgroup.relIndex_map_map_of_injective
          (f := (MulAut.conj t⁻¹).toMonoidHom) (kerMV V H) L (MulAut.conj t⁻¹).injective
        rw [hKmap] at hmap
        exact hmap
      rwa [h2] at h1
    have hXsup : (L ⊔ L₂) ⊔ D.T = H := by
      refine le_antisymm (sup_le (sup_le hLH hL₂H) hDT) ?_
      rw [← hLT]
      exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right
    exact w183fourside_not_dvd_relIndex hKH hKL le_sup_left (sup_le hLH hL₂H) hXsup hXnorm
      x.hyp.isSylowIn_T.isPGroup hdvd hnot13L

theorem w183four_pairTest_big (hO : LieOrderFormulasInput) (hL28 : FinPairGenL28)
    (hSz8 : FinPairGenSz8) {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G))
    (hOK : OInf H = kerMV V H) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2))
    (hcases : (∀ t ∈ D.T, conjSubgroup L t = L) ∨
      ∃ t ∈ D.T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) :
    PairTest (M.img H) (Ctx188.packFamilyU D V H i M) := by
  have hHinfC : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) = kerMV V H :=
    le_antisymm x.hyp.inf_centralizer_eOmegaZ_le_kerMV
      (le_inf (kerMV_le_self V H) hK)
  have hsolv : IsSolvable ↥(H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) := by
    rw [hHinfC, ← hOK]
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    unfold OInf
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical ↥H).equivMapOfInjective H.subtype
        H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  exact Ctx188.pairTest hL28 hSz8 x M hsolv
    (w183four_not_thirteen_dvd hO x M hK hL hLT hX hcases)

theorem w183four_h5_sp44 (h22 : Asch2_2One) (hSp5 : FinSp44Noncyclic5) {D : Data G}
    {V₀ V H : Subgroup G} {i : ℕ} (c : MinCex183 D V₀ V H i) (x : Ctx188 D V₀ V H i 3)
    (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsSp4 X 2)) {t : G} (htT : t ∈ D.T)
    (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) :
    ∀ A ∈ Ctx188.packFamilyU D V H i M, ∀ P : Subgroup (LGL 2 M.W),
      IsSylowIn 5 P (M.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 M.W))) → IsCyclic ↥P := by
  intro A hA P hP
  obtain ⟨g, hg, hAeq⟩ := hA
  have hSJ : H ⊓ conjSubgroup D.M g ≤ H := inf_le_left
  have hL₂c : IsComponentModN (kerMV V H) H (conjSubgroup L t) :=
    w183fourside_conjSubgroup_isComponentModN hL (x.hyp.hyp171.2.1 htT)
  have hQ₂ : HasQuotShape (conjSubgroup L t) (kerMV V H : Set G) (fun X _ => IsSp4 X 2) :=
    w183fourside_hasQuotShape_conj (x.hyp.hyp171.2.1 htT) hL hX
  have hgt : 3 < CFSG.Open.pRank 5 H :=
    w183fourside_pRank_five_gt h22 hSp5 c.hyp.kgroup hL hL₂c hne.symm hX hQ₂
  have hgt' : 3 < CFSG.pRank 5 ↥H := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  have hle1 : ∀ g : G, CFSG.Open.pRank 5 (H ⊓ conjSubgroup D.M g) ≤ 1 := fun g => by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact x.hyp.hyp171.2.2 5 Nat.prime_five (by norm_num) hgt' g
  have hN : M.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 M.W)) =
      M.img (H ⊓ conjSubgroup D.M g) := by
    refine le_antisymm ?_ ?_
    · rintro r ⟨hrH, hrN⟩
      obtain ⟨j, _hjH, rfl⟩ := M.mem_img.1 hrH
      rw [hAeq] at hrN
      have hjM : (j : G) ∈ conjSubgroup D.M g :=
        x.mem_conj_M_of_img_normalizer M hg j.2 hrN
      exact M.mem_img.2 ⟨j, ⟨j.2, hjM⟩, rfl⟩
    · rintro r ⟨j, ⟨hjH, hjM⟩, rfl⟩
      refine ⟨M.mem_img.2 ⟨j, hjH, rfl⟩, ?_⟩
      rw [hAeq]
      exact Hyp183.img_normalizer_of_mem_conj x.hyp M j.2 hjM
  have hP' : IsSylowIn 5 P (M.img (H ⊓ conjSubgroup D.M g)) := by
    rwa [hN] at hP
  exact w183fourside_isCyclic_of_isSylowIn_img M hSJ
    (by rw [w183fourside_pRank_five_subgroupOf hSJ]; exact hle1 g) hP'

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
