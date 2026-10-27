module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsU58Blocks

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def TerminalRootComponentsU58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    (Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) →
    ∀ D : Set (MulAut A), (∀ φ ∈ D, IsReflectionOn φ) →
      (∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) → Subgroup.closure D = starOf A I →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
        ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
          CFSG.IsComponent X → ∃ φ ∈ D, ∀ P : Subgroup G, P ≤ I →
            P ≤ Subgroup.centralizer (fixedInG A φ : Set G) → Group.IsPerfect P →
              P ≤ X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype

namespace RootsU58

section Transport

variable {G : Type} [Group G] {N : Type} [Group N] {A₀ : Subgroup N}

@[expose] noncomputable def thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) : A ≃* A₀ :=
  (Subgroup.subgroupOfEquivOfLe hAI).symm.trans
    ((MulEquiv.subgroupMap Φ (A.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦA))

theorem coe_thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) (c : A) :
    ((thetaA hAI Φ hΦA c : A₀) : N) = Φ ⟨(c : G), hAI c.2⟩ := rfl

theorem mem_A_iff_Phi {I A : Subgroup G} (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) (h : I) :
    (h : G) ∈ A ↔ Φ h ∈ A₀ :=
  Subgroup.mem_subgroupOf.symm.trans
    ((Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).symm.trans
      (by rw [hΦA]; exact Iff.rfl))

theorem mem_normalizer_iff_Phi {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) (y : I) :
    (y : G) ∈ Subgroup.normalizer (A : Set G) ↔ Φ y ∈ Subgroup.normalizer (A₀ : Set N) := by
  have key := mem_A_iff_Phi Φ hΦA
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hy m
    obtain ⟨h, rfl⟩ := Φ.surjective m
    have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
    rw [e1]
    exact (key h).symm.trans ((hy (h : G)).trans (key (y * h * y⁻¹)))
  · intro hm g
    by_cases hg : g ∈ I
    · obtain ⟨h, rfl⟩ : ∃ h : I, (h : G) = g := ⟨⟨g, hg⟩, rfl⟩
      have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
      have k2 : Φ h ∈ A₀ ↔ Φ (y * h * y⁻¹) ∈ A₀ := by
        rw [← e1]
        exact hm (Φ h)
      exact (key h).trans (k2.trans (key (y * h * y⁻¹)).symm)
    · have hgA : g ∉ A := fun hgA => hg (hAI hgA)
      have hyg : (y : G) * g * (y : G)⁻¹ ∉ I := by
        intro hI
        apply hg
        have e : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) = g := by group
        rw [← e]
        exact I.mul_mem (I.mul_mem (I.inv_mem y.2) hI) y.2
      exact ⟨fun h => absurd h hgA, fun h => absurd (hAI h) hyg⟩

theorem congr_normalizer {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) (n : Subgroup.normalizer (A : Set G))
    (hn : (n : G) ∈ I) :
    MulAut.congr (thetaA hAI Φ hΦA) (A.normalizerMonoidHom n) =
      A₀.normalizerMonoidHom ⟨Φ ⟨(n : G), hn⟩,
        (mem_normalizer_iff_Phi hAI Φ hΦA ⟨(n : G), hn⟩).mp n.2⟩ := by
  apply MulEquiv.ext
  intro a'
  apply Subtype.ext
  obtain ⟨c, rfl⟩ := (thetaA hAI Φ hΦA).surjective a'
  have hxy : (⟨((A.normalizerMonoidHom n c : A) : G), hAI (A.normalizerMonoidHom n c).2⟩ : I) =
      (⟨(n : G), hn⟩ : I) * ⟨(c : G), hAI c.2⟩ * (⟨(n : G), hn⟩ : I)⁻¹ :=
    Subtype.ext (normalizerMonoidHom_coe_apply_G n c)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    normalizerMonoidHom_coe_apply_G, coe_thetaA hAI Φ hΦA, coe_thetaA hAI Φ hΦA, hxy, map_mul,
    map_mul, map_inv]

theorem starOf_map_TA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) :
    (starOf A I).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom =
      starOf A₀ (⊤ : Subgroup N) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hψ
    rw [MulEquiv.coe_toMonoidHom, congr_normalizer hAI Φ hΦA x (Subgroup.mem_subgroupOf.mp hx)]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), rfl⟩
  · intro hφ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨y, hy⟩ : ∃ y : I, Φ y = (m : N) := ⟨Φ.symm (m : N), Φ.apply_symm_apply _⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) :=
      (mem_normalizer_iff_Phi hAI Φ hΦA y).mpr (by rw [hy]; exact m.2)
    refine Subgroup.mem_map.mpr ⟨A.normalizerMonoidHom ⟨(y : G), hyN⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨(y : G), hyN⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, congr_normalizer hAI Φ hΦA ⟨(y : G), hyN⟩ y.2]
      congr 1
      apply Subtype.ext
      exact hy

theorem congr_thetaA_apply {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* N)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A₀) (φ : MulAut A) (a : A) :
    MulAut.congr (thetaA hAI Φ hΦA) φ (thetaA hAI Φ hΦA a) = thetaA hAI Φ hΦA (φ a) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def thetaC {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* N)
    {C : Subgroup N} (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) : H ≃* C :=
  (Subgroup.subgroupOfEquivOfLe hHI).symm.trans
    ((MulEquiv.subgroupMap Φ (H.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦH))

theorem coe_thetaC {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* N) {C : Subgroup N}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) (c : H) :
    ((thetaC hHI Φ hΦH c : C) : N) = Φ ⟨(c : G), hHI c.2⟩ := rfl

theorem isPerfect_map_subgroupOf {I P : Subgroup G} (hPI : P ≤ I) (Φ : I ≃* N)
    (hP : Group.IsPerfect P) : Group.IsPerfect ((P.subgroupOf I).map Φ.toMonoidHom) := by
  haveI : Group.IsPerfect (P.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPI).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPI).symm.surjective
  exact Group.IsPerfect.map Φ.toMonoidHom

end Transport

section Model

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.RankThree.PartTwo.Sec21.TablesU58 CFSG.RankThree.PartTwo.Sec21.Tables

variable {G : Type} [Group G]

theorem exists_Phi {I A : Subgroup G} (hAI : A ≤ I) (hAe : IsElemAbelian 3 A)
    (e : I ≃* projSU 5 2 3) (hA : Nat.card A = 3 ^ 4) :
    ∃ Φ : I ≃* SUI, (A.subgroupOf I).map Φ.toMonoidHom = A0 := by
  set e' : I ≃* SUI := e.trans equivSUI with he'
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  refine ⟨e'.trans (MulAut.conj x), ?_⟩
  rw [← hx, Subgroup.map_map]
  rfl

theorem exists_thetaA_eq {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (v : Fin 4 → ZMod 3) :
    ∃ a : A, ((thetaA hAI Φ hΦA a : A0) : SUI) = δ (Multiplicative.ofAdd v) :=
  ⟨(thetaA hAI Φ hΦA).symm ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩,
    congrArg Subtype.val ((thetaA hAI Φ hΦA).apply_symm_apply _)⟩

theorem swap_fix_of_eq (w : Fin 4 → ZMod 3) {i j : Fin 5} (h : ext3 w i = ext3 w j) :
    ext3 w ∘ Equiv.swap i j = ext3 w := by
  funext t
  by_cases hi : t = i
  · subst hi
    simp [Equiv.swap_apply_left, h]
  · by_cases hj : t = j
    · subst hj
      simp [Equiv.swap_apply_right, h]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem fix_of_ext {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 5}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j)) {v : Fin 4 → ZMod 3}
    (hv : ext3 v i = ext3 v j) {a : A}
    (ha : ((thetaA hAI Φ hΦA a : A0) : SUI) = δ (Multiplicative.ofAdd v)) :
    ψ a = a := by
  have hfix : (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈
      fixedSubgroupOf (permAut (Equiv.swap i j)) :=
    (mem_fixed_permAut_iff _ v).mpr (swap_fix_of_eq v hv)
  rw [mem_fixedSubgroupOf] at hfix
  have hx : thetaA hAI Φ hΦA a = ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ := Subtype.ext ha
  apply (thetaA hAI Φ hΦA).injective
  rw [← congr_thetaA_apply hAI Φ hΦA ψ a, hψ, hx]
  exact hfix

theorem exists_swap_in_D {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (D : Set (MulAut A))
    (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A I) {i j : Fin 5} (hij : i ≠ j) :
    ∃ ψ ∈ D, MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j) := by
  have hrefl0 : ∀ φ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D, IsReflectionOn φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact isReflectionOn_congr (thetaA hAI Φ hΦA) φ (hrefl φ hφ)
  have hconj0 : ∀ g ∈ starOf A0 (⊤ : Subgroup SUI), ∀ φ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D,
      g * φ * g⁻¹ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D := by
    intro g hg φ hφ
    obtain ⟨φ0, hφ0, rfl⟩ := hφ
    have hg' : g ∈ (starOf A I).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom := by
      rw [starOf_map_TA hAI Φ hΦA]
      exact hg
    obtain ⟨g', hg'I, rfl⟩ := Subgroup.mem_map.mp hg'
    refine ⟨g' * φ0 * g'⁻¹, hconj g' hg'I φ0 hφ0, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hcl0 : Subgroup.closure ((MulAut.congr (thetaA hAI Φ hΦA)) '' D) =
      starOf A0 (⊤ : Subgroup SUI) := by
    have h1 : Subgroup.closure ((MulAut.congr (thetaA hAI Φ hΦA)) '' D) =
        (Subgroup.closure D).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom := by
      rw [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom]
    rw [h1, hcl, starOf_map_TA hAI Φ hΦA]
  obtain ⟨ψ, hψD, hψ⟩ := permAut_swap_mem_D _ hrefl0 hconj0 hcl0 hij
  exact ⟨ψ, hψD, hψ⟩

theorem exists_v_of_thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (a : A) :
    ∃ v : Fin 4 → ZMod 3, ((thetaA hAI Φ hΦA a : A0) : SUI) = δ (Multiplicative.ofAdd v) := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (thetaA hAI Φ hΦA a).2
  exact ⟨Multiplicative.toAdd y, hy.symm⟩

theorem commute_delta_of_fixed {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 5}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j))
    {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer (fixedInG A ψ : Set G))
    {x : I} (hx : (x : G) ∈ P) {v : Fin 4 → ZMod 3} (hv : ext3 v i = ext3 v j) :
    Φ x * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * Φ x := by
  obtain ⟨a, ha⟩ := exists_thetaA_eq hAI Φ hΦA v
  have hfix : ψ a = a := fix_of_ext hAI Φ hΦA hψ hv ha
  have hcomm : (a : G) * (x : G) = (x : G) * (a : G) :=
    Subgroup.mem_centralizer_iff.mp (hPC hx) (a : G) (mem_fixedInG_of hfix)
  have hcomm' : (⟨(a : G), hAI a.2⟩ : I) * x = x * ⟨(a : G), hAI a.2⟩ := Subtype.ext hcomm
  have hΦa : Φ ⟨(a : G), hAI a.2⟩ = δ (Multiplicative.ofAdd v) :=
    (coe_thetaA hAI Φ hΦA a).symm.trans ha
  have h := (Phi_comm_iff Φ _ x).mpr hcomm'
  rw [hΦa] at h
  exact h.symm

theorem exists_pair_of_component {w : Fin 4 → ZMod 3}
    {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd w)} : Set SUI))}
    (hY : CFSG.IsComponent Y) :
    ∃ i j : Fin 5, i ≠ j ∧ ext3 w i = ext3 w j ∧
      ∀ z : Subgroup.centralizer ({δ (Multiplicative.ofAdd w)} : Set SUI),
        z ∈ Y ↔ (z : SUI) ∈ idOutsideSU {k : Fin 5 | ext3 w k = ext3 w i} := by
  have hmem : Y ∈ {Y : Subgroup (Subgroup.centralizer
      ({δ (Multiplicative.ofAdd w)} : Set SUI)) | CFSG.IsComponent Y} := hY
  rw [components_big w] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  obtain ⟨i, j, hij, hi, hj⟩ := κ.2
  subst hκ
  refine ⟨i, j, hij, hi.trans hj.symm, fun z => ?_⟩
  simp only [Subgroup.mem_subgroupOf]
  rw [hi]

theorem subgroupOf_le_of_perfect {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* SUI)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 5}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j)) (hij : i ≠ j)
    {v : Fin 4 → ZMod 3} (hfib : ext3 v i = ext3 v j)
    {H : Subgroup G} (hHI : H ≤ I) {C : Subgroup SUI}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) {X : Subgroup H}
    (hmemY : ∀ z : C, z ∈ X.map (thetaC hHI Φ hΦH).toMonoidHom ↔
      (z : SUI) ∈ idOutsideSU {k : Fin 5 | ext3 v k = ext3 v i})
    {P : Subgroup G} (hPI : P ≤ I)
    (hPC : P ≤ Subgroup.centralizer (fixedInG A ψ : Set G)) (hPperf : Group.IsPerfect P) :
    P.subgroupOf H ≤ X := by
  intro y hy
  have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
  have hyI : (y : G) ∈ I := hHI y.2
  have hmem : Φ ⟨(y : G), hyI⟩ ∈ (P.subgroupOf I).map Φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨⟨(y : G), hyI⟩, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩
  have hQ := isPerfect_map_subgroupOf hPI Φ hPperf
  have hcomm : ∀ g ∈ (P.subgroupOf I).map Φ.toMonoidHom, ∀ u : Fin 4 → ZMod 3,
      ext3 u i = ext3 u j → g * δ (Multiplicative.ofAdd u) = δ (Multiplicative.ofAdd u) * g := by
    intro g hg u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact commute_delta_of_fixed hAI Φ hΦA hψ hPC (Subgroup.mem_subgroupOf.mp hx) hu
  have hout := isIdOutside_of_perfect hij hQ hcomm
  have hpair : ({i, j} : Set (Fin 5)) ⊆ {k : Fin 5 | ext3 v k = ext3 v i} :=
    Set.insert_subset_iff.mpr ⟨rfl, Set.singleton_subset_iff.mpr hfib.symm⟩
  have hblk : Φ ⟨(y : G), hyI⟩ ∈ idOutsideSU {k : Fin 5 | ext3 v k = ext3 v i} :=
    idOutsideSU_mono hpair (mem_idOutsideSU.mpr (hout _ hmem))
  have hmY : thetaC hHI Φ hΦH y ∈ X.map (thetaC hHI Φ hΦH).toMonoidHom :=
    (hmemY (thetaC hHI Φ hΦH y)).mpr (by rw [coe_thetaC]; exact hblk)
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmY
  have hzy' : thetaC hHI Φ hΦH z = thetaC hHI Φ hΦH y := hzy
  rw [(thetaC hHI Φ hΦH).injective hzy'] at hz
  exact hz

theorem terminalRootComponents : TerminalRootComponentsU58 := by
  unfold TerminalRootComponentsU58
  intro G _ _ I A hAI hAe hT D hrefl hconj hcl B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ, hΦA⟩ := exists_Phi hAI hAe e hA
  obtain ⟨b, -, hb1, rfl⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA (Subgroup.mem_zpowers b)
  have hbI : b ∈ I := hAI hbA
  have ha1 : (⟨b, hbA⟩ : A) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨v, hv⟩ := exists_v_of_thetaA hAI Φ hΦA ⟨b, hbA⟩
  have hΦb : Φ ⟨b, hbI⟩ = δ (Multiplicative.ofAdd v) :=
    (coe_thetaA hAI Φ hΦA ⟨b, hbA⟩).symm.trans hv
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH : ((I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)).subgroupOf
      I).map Φ.toMonoidHom = Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI) := by
    rw [map_inf_centralizer_zpowers Φ hbI, hΦb]
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaC hHI Φ hΦH) hX
  obtain ⟨i, j, hij, hfib, hmemY⟩ := exists_pair_of_component hY
  obtain ⟨ψ, hψD, hψ⟩ := exists_swap_in_D hAI Φ hΦA D hrefl hconj hcl hij
  have hbfix : ψ ⟨b, hbA⟩ = ⟨b, hbA⟩ := fix_of_ext hAI Φ hΦA hψ hfib hv
  have hbC : b ∈ fixedInG A ψ := mem_fixedInG_of hbfix
  have hPB : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (fixedInG A ψ : Set G) →
      P ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    intro P hPC x hx
    exact mem_centralizer_zpowers_iff.mpr (Subgroup.mem_centralizer_iff.mp (hPC hx) b hbC)
  refine ⟨ψ, hψD, fun P hPI hPC hPperf => le_map_subtype_of_subgroupOf_le (le_inf hPI (hPB P hPC))
    (subgroupOf_le_of_perfect hAI Φ hΦA hψ hij hfib hHI hΦH hmemY hPI hPC hPperf)⟩

end Model

end RootsU58

theorem terminalRootComponentsU58 : TerminalRootComponentsU58 := RootsU58.terminalRootComponents

end CFSG.RankThree.PartTwo.Sec21
