module

public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Defs
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Core
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Lift
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveCfg
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenFischerLift
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Lifts

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section General

variable {X : Type} [Group X]

theorem commutator_zpowers_ne_bot {a b : X} (hab : a * b ≠ b * a) :
    ⁅Subgroup.zpowers a, Subgroup.zpowers b⁆ ≠ ⊥ := by
  intro hbot
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
  have ha : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
  have hb : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
  exact hab ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm

theorem zpowers_ne_zpowers {a b : X} (ha : a * a = 1) (hb1 : b ≠ 1) (hba : b ≠ a) :
    Subgroup.zpowers b ≠ Subgroup.zpowers a := by
  intro h
  have hbmem : b ∈ Subgroup.zpowers a := h ▸ Subgroup.mem_zpowers b
  rcases CFSG.GH74.Uniqueness.Bender.eq_one_or_eq_of_mem_zpowers ha hbmem with h1 | h1
  · exact hb1 h1
  · exact hba h1

end General

section Config

variable {G : Type} [Group G] [Finite G]


variable {V H E : Subgroup G}

theorem barSub_eq_zpowers {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    (hV2 : Nat.card (barSub K φ V) = 2) {v : ↥K} (hvV : (v : G) ∈ V) (hv1 : φ v ≠ 1) :
    barSub K φ V = Subgroup.zpowers (φ v) := by
  have htV : φ v ∈ barSub K φ V := mem_barSub.mpr ⟨v, hvV, rfl⟩
  haveI : Finite ↥(barSub K φ V) := Nat.finite_of_card_ne_zero (by rw [hV2]; norm_num)
  have hdvd : orderOf (φ v) ∣ Nat.card (barSub K φ V) :=
    Subgroup.orderOf_dvd_natCard (barSub K φ V) htV
  rw [hV2] at hdvd
  have hne1 : orderOf (φ v) ≠ 1 := fun h1 => hv1 (orderOf_eq_one_iff.mp h1)
  have hord : orderOf (φ v) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htV) ?_).symm
  rw [hV2, Nat.card_zpowers, hord]

private theorem mem_conjSubgroup_conj_mul_map {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} {v : ↥K} (hvV : (v : G) ∈ V) (k : ↥K) :
    ((k⁻¹ * v * k : ↥K) : G) ∈ conjSubgroup V (k : G) ∧
      φ (k⁻¹ * v * k) = (φ k)⁻¹ * φ v * φ k := by
  constructor
  · rw [mem_conjSubgroup_iff]
    have hcoe : ((k⁻¹ * v * k : ↥K) : G) = (k : G)⁻¹ * (v : G) * (k : G) := by simp
    rw [hcoe]
    have h : (k : G) * ((k : G)⁻¹ * (v : G) * (k : G)) * (k : G)⁻¹ =
        (v : G) := by group
    rw [h]
    exact hvV
  · simp

theorem exists_mem_sup_map_eq {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    {v k₂ k₃ : ↥(kSub V H E)} (hvV : (v : G) ∈ V) {g : X}
    (hg : g ∈ Subgroup.closure
      ({φ v, (φ k₂)⁻¹ * φ v * φ k₂, (φ k₃)⁻¹ * φ v * φ k₃} : Set X)) :
    ∃ x : ↥(kSub V H E),
      (x : G) ∈ V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G) ∧ φ x = g := by
  classical
  let X₀ : Subgroup G := V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G)
  have h₂ := mem_conjSubgroup_conj_mul_map (φ := φ) hvV k₂
  have h₃ := mem_conjSubgroup_conj_mul_map (φ := φ) hvV k₃
  have hcl : Subgroup.closure
      ({φ v, (φ k₂)⁻¹ * φ v * φ k₂, (φ k₃)⁻¹ * φ v * φ k₃} : Set X) ≤
      (X₀.subgroupOf (kSub V H E)).map φ := by
    refine (Subgroup.closure_le ((X₀.subgroupOf (kSub V H E)).map φ)).mpr ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_map.mpr ⟨v, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hvV)), rfl⟩
    · exact Subgroup.mem_map.mpr ⟨k₂⁻¹ * v * k₂,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂.1)),
        h₂.2⟩
    · exact Subgroup.mem_map.mpr ⟨k₃⁻¹ * v * k₃,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right h₃.1),
        h₃.2⟩
  obtain ⟨x, hx, hφx⟩ := Subgroup.mem_map.mp (hcl hg)
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hφx⟩

theorem exists_sevenSevenModule_of_not_isPGroup (h : Hyp711 V H E) {V₁ V₂ V₃ : Subgroup G}
    (h₁ : V₁ ∈ omegaSet V H E) (h₂ : V₂ ∈ omegaSet V H E) (h₃ : V₃ ∈ omegaSet V H E)
    (hX : ¬ IsPGroup 2 ↥(V₁ ⊔ V₂ ⊔ V₃)) :
    ∃ A : Subgroup G, SevenSevenModule V H E V₁ V₂ V₃ A := by
  classical
  let K : Subgroup G := kSub V H E
  let Xs : Subgroup G := V₁ ⊔ V₂ ⊔ V₃
  have hXH : Xs ≤ H :=
    sup_le (sup_le (h.omega_le V₁ h₁) (h.omega_le V₂ h₂)) (h.omega_le V₃ h₃)
  have hIH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hHNI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal h.le h.normal)
  have hXI : Xs ≤ Subgroup.normalizer (iSub V H E : Set G) := hXH.trans hHNI
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hXK : Xs ≤ K :=
    sup_le (sup_le (le_kSub h₁) (le_kSub h₂)) (le_kSub h₃)
  have hC_le : Xs ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤ pCoreOf 2 K :=
    (inf_le_inf hXK le_rfl).trans (centralizer_iSub_le_pCoreOf h)
  have hCp : IsPGroup 2 ↥(Xs ⊓ Subgroup.centralizer (iSub V H E : Set G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).to_le hC_le
  have hXnp : ¬ IsPGroup 2 ↥Xs := hX
  obtain ⟨A, hAI, hAN, hAcomm, hAne⟩ :=
    exists_commutator_eq_of_not_isPGroup hI hXI hXnp hCp
  exact ⟨A, hAI, hAN, hAcomm, hAne⟩

theorem sevenSevenCfg_of_szBarTriple (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) {v k₂ k₃ : ↥(kSub V H E)} {g : X}
    (hvV : (v : G) ∈ V) (hT : SzBarTriple (φ v) (φ k₂) (φ k₃) g) :
    SevenSevenCfg V H E V (conjSubgroup V (k₂ : G)) (conjSubgroup V (k₃ : G)) := by
  have hVbar : barSub (kSub V H E) φ V = Subgroup.zpowers (φ v) :=
    barSub_eq_zpowers (K := kSub V H E) (φ := φ) hV2 hvV hT.ne_one
  have hsq₂ : ((φ k₂)⁻¹ * φ v * φ k₂) * ((φ k₂)⁻¹ * φ v * φ k₂) = 1 := by
    rw [show ((φ k₂)⁻¹ * φ v * φ k₂) * ((φ k₂)⁻¹ * φ v * φ k₂) =
      (φ k₂)⁻¹ * (φ v * φ v) * φ k₂ from by group, hT.sq]
    group
  have hne₂ : (φ k₂)⁻¹ * φ v * φ k₂ ≠ 1 := by
    intro h1
    apply hT.ne_one
    calc φ v = (φ k₂) * ((φ k₂)⁻¹ * φ v * φ k₂) * (φ k₂)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hconj₂ : conjSubgroup (barSub (kSub V H E) φ V) (φ k₂) =
      Subgroup.zpowers ((φ k₂)⁻¹ * φ v * φ k₂) := by
    rw [hVbar, CFSG.LocalAnalysis.WeakClosure81.OddCoreLiftF.conjSubgroup_zpowers]
  have hconj₃ : conjSubgroup (barSub (kSub V H E) φ V) (φ k₃) =
      Subgroup.zpowers ((φ k₃)⁻¹ * φ v * φ k₃) := by
    rw [hVbar, CFSG.LocalAnalysis.WeakClosure81.OddCoreLiftF.conjSubgroup_zpowers]
  refine sevenSevenCfg_of_barSub h hφ hV2 k₂ k₃ ?_ ?_ ?_ ?_
  · rw [hconj₂, hVbar]
    exact OddCentral.isPGroup_sup_zpowers hT.sq hsq₂ hT.comm₁₂
  · rw [hconj₂, hVbar]
    exact zpowers_ne_zpowers hT.sq hne₂ hT.ne₁₂
  · rw [hconj₃, hVbar]
    exact commutator_zpowers_ne_bot hT.not_comm₁₃
  · rw [hconj₂, hconj₃]
    exact commutator_zpowers_ne_bot hT.not_comm₂₃

private theorem exists_conj_w_of_szBarTriple {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} {v k₂ k₃ : ↥(kSub V H E)} {g : X}
    (hvV : (v : G) ∈ V) (hT : SzBarTriple (φ v) (φ k₂) (φ k₃) g) :
    ∃ w : ↥(kSub V H E), (w : G) ∈ conjSubgroup V (k₃ : G) ∧
      φ w = (φ k₃)⁻¹ * φ v * φ k₃ ∧
      ¬ IsPGroup 2 ↥(Subgroup.closure ({φ v, φ w} : Set X)) := by
  obtain ⟨hmem, hmap⟩ := mem_conjSubgroup_conj_mul_map (φ := φ) hvV k₃
  refine ⟨k₃⁻¹ * v * k₃, hmem, hmap, ?_⟩
  rw [hmap]
  exact hT.not_isPGroup

private theorem not_isPGroup_of_not_isPGroup_closure {K X₀ : Subgroup G} {d e : ↥K}
    (hX₀K : X₀ ≤ K) (hd : (d : G) ∈ X₀) (he : (e : G) ∈ X₀)
    (hnp : ¬ IsPGroup 2 ↥(Subgroup.closure ({(d : G), (e : G)} : Set G))) :
    ¬ IsPGroup 2 ↥X₀ := by
  intro hP
  have hPK : IsPGroup 2 ↥(X₀.subgroupOf K) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hX₀K).symm
  have hcl_le : Subgroup.closure ({d, e} : Set ↥K) ≤ X₀.subgroupOf K := by
    refine (Subgroup.closure_le (X₀.subgroupOf K)).mpr ?_
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_subgroupOf.mpr hd
    · exact Subgroup.mem_subgroupOf.mpr he
  have hclP : IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set ↥K)) := hPK.to_le hcl_le
  have hmapP : IsPGroup 2 ↥((Subgroup.closure ({d, e} : Set ↥K)).map K.subtype) :=
    hclP.map K.subtype
  have hmap_eq : (Subgroup.closure ({d, e} : Set ↥K)).map K.subtype =
      Subgroup.closure ({(d : G), (e : G)} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [hmap_eq] at hmapP
  exact hnp hmapP

private theorem not_isPGroup_sup_conj_of_szBarTriple (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} {v k₂ k₃ : ↥(kSub V H E)} {g : X}
    (hvV : (v : G) ∈ V) (hT : SzBarTriple (φ v) (φ k₂) (φ k₃) g) :
    ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G)) := by
  obtain ⟨w, hwW, -, hnp⟩ := exists_conj_w_of_szBarTriple hvV hT
  have hnpK : ¬ IsPGroup 2 ↥(Subgroup.closure ({(v : G), (w : G)} : Set G)) :=
    not_isPGroup_closure_of_map (φ := φ) hnp
  have hX₀K : V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G) ≤ kSub V H E :=
    sup_le (sup_le (le_kSub h.mem)
      (le_kSub (conjSubgroup_mem_omegaSet h.le h.normal h.mem
        (kSub_le_of_forall_le h.omega_le k₂.2))))
      (le_kSub (conjSubgroup_mem_omegaSet h.le h.normal h.mem
        (kSub_le_of_forall_le h.omega_le k₃.2)))
  exact not_isPGroup_of_not_isPGroup_closure (K := kSub V H E) (d := v) (e := w)
    hX₀K (Subgroup.mem_sup_left (Subgroup.mem_sup_left hvV))
    (Subgroup.mem_sup_right hwW) hnpK

private theorem exists_centralizing_preimage_of_szBarTriple (h : Hyp711 V H E) {X : Type}
    [Group X] {φ : ↥(kSub V H E) →* X} {v k₂ k₃ : ↥(kSub V H E)} {g : X}
    (hvV : (v : G) ∈ V) (hT : SzBarTriple (φ v) (φ k₂) (φ k₃) g) :
    ∃ g' : ↥(kSub V H E),
      (g' : G) ∈ V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G) ∧
        (g' : G)⁻¹ * v * g' = v ∧ φ g' * φ g' = φ v := by
  classical
  obtain ⟨w, hwW, -, hnp⟩ := exists_conj_w_of_szBarTriple hvV hT
  have hW : conjSubgroup V (k₃ : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (kSub_le_of_forall_le h.omega_le k₃.2)
  obtain ⟨x, hxX₀, hφx⟩ := exists_mem_sup_map_eq (φ := φ) hvV hT.mem
  have hx : φ x * φ x = φ v := by rw [hφx, hT.mul_self]
  refine exists_centralizing_mul_self_eq (h := h.toHyp73) (U := V)
    (W := conjSubgroup V (k₃ : G))
    (X₀ := V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G))
    h.mem hW hvV hwW (Subgroup.mem_sup_left (Subgroup.mem_sup_left hvV))
    (Subgroup.mem_sup_right hwW) hxX₀ hx hnp

theorem false_of_szBarTriple (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) {v k₂ k₃ : ↥(kSub V H E)} {g : X}
    (hvV : (v : G) ∈ V) (hT : SzBarTriple (φ v) (φ k₂) (φ k₃) g) : False := by
  classical
  have hc := sevenSevenCfg_of_szBarTriple h hφ hV2 hvV hT
  have hX₀np := not_isPGroup_sup_conj_of_szBarTriple h hvV hT
  obtain ⟨A₀, hA₀⟩ :=
    exists_sevenSevenModule_of_not_isPGroup h hc.mem₁ hc.mem₂ hc.mem₃ hX₀np
  obtain ⟨A, -, hA⟩ := exists_sevenSevenMinimal_le hA₀
  obtain ⟨g', hg'X₀, hg'v, hg'φ⟩ :=
    exists_centralizing_preimage_of_szBarTriple h hvV hT
  have hgJ : (g' : G) * (g' : G) * (v : G)⁻¹ ∈ pCoreOf 2 (kSub V H E) := by
    have h1 := (hφ.ker_iff (g' * g' * v⁻¹)).mp (by
      rw [map_mul, map_mul, map_inv, hg'φ, mul_inv_cancel])
    simpa using h1
  have hvI : (v : G) ∉ iSub V H E := by
    intro hv
    exact hT.ne_one ((hφ.ker_iff v).mpr (h.iSub_le hv))
  exact false_of_mul_self_mem h.toHyp73 hc hA hvV hvI hg'X₀ hg'v hgJ

end Config

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
