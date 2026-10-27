module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4FactE
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Act
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalPerfect
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Aux
public import CFSG.Quasithin.H13.NQRigidWMRestrict
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4G0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InCalE InCalEi IsOmegaColl ECaseII tA)
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem relIndex_inf_eq_two (h : Setting L T P₀ P₁ n w) (hodd : Odd n) {a : Q}
    (haT : a ∈ T) (haL : a ∉ L) : (T ⊓ L).relIndex T = 2 := by
  haveI : L.Normal := h.normal
  have hnorm : T ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hrel : L.relIndex T = (T ⊓ L).relIndex T := by
    rw [← Subgroup.relIndex_sup_right T L]
    exact (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := T) (K := L) hnorm).2
  have hne1 : L.relIndex T ≠ 1 := by
    intro h1
    exact haL (Subgroup.relIndex_eq_one.mp h1 haT)
  have hne0 : L.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hleT : L.relIndex T ≤ L.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := L) (K := T) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right L] at h
  have hle : L.relIndex T ≤ 2 := hleT.trans (h.index_odd hodd)
  omega

private theorem mul_mem_inf_of_not_mem (h : Setting L T P₀ P₁ n w) {U : Subgroup Q}
    (hU : U = T ⊓ L) (hrel : U.relIndex T = 2) {t a : Q} (htT : t ∈ T) (haT : a ∈ T)
    (htL : t ∉ L) (haL : a ∉ L) (ha2 : a * a = 1) : t * a ∈ U := by
  subst hU
  obtain ⟨w, hwT, hwU, hb⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have htU : t ∉ T ⊓ L := fun hx => htL hx.2
  have haU : a ∉ T ⊓ L := fun hx => haL hx.2
  have htw : t * w ∈ T ⊓ L := (hb t htT).resolve_right htU
  have haw : a * w ∈ T ⊓ L := (hb a haT).resolve_right haU
  have haa : a⁻¹ = a := by
    rw [← mul_one a⁻¹, ← ha2, ← mul_assoc, inv_mul_cancel, one_mul]
  have heq : (t * w) * (a * w)⁻¹ = t * a := by
    rw [mul_inv_rev, haa]
    group
  rw [← heq]
  exact (T ⊓ L).mul_mem htw ((T ⊓ L).inv_mem haw)

private theorem map_conj_eq_of_not_mem (h : Setting L T P₀ P₁ n w) {a : Q} (haT : a ∈ T)
    (haL : a ∉ L) (ha2 : a * a = 1) (hsw : P₀.map (MulAut.conj a).toMonoidHom = P₁)
    {t : Q} (htT : t ∈ T) (htL : t ∉ L) : P₀.map (MulAut.conj t).toMonoidHom = P₁ := by
  have hodd : Odd n := odd_of_swap h haT ha2 hsw
  have hrel := relIndex_inf_eq_two h hodd haT haL
  have hta : t * a ∈ T ⊓ L := mul_mem_inf_of_not_mem h rfl hrel htT haT htL haL ha2
  have huP₀ : t * a ∈ P₀ := h.par₀.2.1 ⟨hta.2, Subgroup.le_normalizer hta⟩
  have huP₁ : t * a ∈ P₁ := h.par₁.2.1 ⟨hta.2, Subgroup.le_normalizer hta⟩
  have ht : t = (t * a) * a := by rw [mul_assoc, ha2, mul_one]
  rw [ht]
  have hcomp : (MulAut.conj ((t * a) * a)).toMonoidHom =
      (MulAut.conj (t * a)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply,
      mul_inv_rev, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, hsw]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer huP₁)

private theorem pCoreOf_perfectCore_map_conj {P P' : Subgroup Q} {x : Q}
    (hx : P.map (MulAut.conj x).toMonoidHom = P') :
    pCoreOf 2 (perfectCore P') =
      (pCoreOf 2 (perfectCore P)).map (MulAut.conj x).toMonoidHom := by
  rw [← hx, ← CFSG.Quasithin.map_perfectCore, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]

private theorem le_of_le_map_conj {R R' B : Subgroup Q} {x : Q} (hB : B ≤ R)
    (hcx : ∀ b ∈ B, x * b = b * x) (hR : R' = R.map (MulAut.conj x).toMonoidHom) :
    B ≤ R' := by
  intro b hb
  have hconj : (MulAut.conj x).toMonoidHom b = b := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcx b hb]
    group
  rw [hR, ← hconj, Subgroup.mem_map_iff_mem (MulAut.conj x).injective]
  exact hB hb

private theorem exists_involution_swap (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hAS : ∃ a ∈ A, P₀.map (MulAut.conj a).toMonoidHom ≠ P₀) :
    ∃ a ∈ A, a * a = 1 ∧ a ∉ L ∧ P₀.map (MulAut.conj a).toMonoidHom = P₁ ∧ Odd n := by
  obtain ⟨a, haA, haP⟩ := hAS
  have hAel : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have haT : a ∈ T := hAT haA
  have ha2 : a * a = 1 := hAel.mul_self_eq_one haA
  have hsw : P₀.map (MulAut.conj a).toMonoidHom = P₁ := by
    rcases map_conj_eq_or h haT with h0 | h0
    · exact absurd h0.1 haP
    · exact h0.1
  have haL : a ∉ L := by
    intro haLin
    have haU : a ∈ T ⊓ L := ⟨haT, haLin⟩
    exact haP (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (h.par₀.2.1 ⟨haLin, Subgroup.le_normalizer haU⟩)))
  exact ⟨a, haA, ha2, haL, hsw, odd_of_swap h haT ha2 hsw⟩

private theorem exists_conj_facts (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A S T' : Subgroup Q} {a g : Q} (hAΩ : A ∈ Ω) (haA : a ∈ A)
    (haL : a ∉ L) (ha2 : a * a = 1) (hAS : A ≤ S) (hST' : S ≤ T')
    (hgT' : T' = T.map (MulAut.conj g).toMonoidHom) :
    ∃ (A' : Subgroup Q) (a' : Q),
      A' = conjSubgroup A g ∧ A' ∈ Ω ∧ A' ≤ T ∧ IsElemAbelian 2 A' ∧
      Nat.card ↥A' = Nat.card ↥A ∧ a' = g⁻¹ * a * g ∧ a' ∈ A' ∧ a' ∈ T ∧ a' ∉ L ∧
      a' * a' = 1 := by
  classical
  have hAel : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  set A' : Subgroup Q := conjSubgroup A g with hA'
  set a' : Q := g⁻¹ * a * g with ha'
  have hA'T : A' ≤ T := by
    intro y hy
    rw [hA', CFSG.Quasithin.mem_conjSubgroup_iff] at hy
    have hyT' : g * y * g⁻¹ ∈ T' := hST' (hAS hy)
    rw [hgT'] at hyT'
    obtain ⟨t, htT, ht⟩ := hyT'
    have hconj : g * t * g⁻¹ = g * y * g⁻¹ := ht
    have hty : t = y := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hconj]
        _ = y := by group
    rwa [← hty]
  have hA'el : IsElemAbelian 2 A' := by
    rw [hA']
    simpa only [conjSubgroup, CFSG.Quasithin.cjSub] using
      CFSG.Quasithin.isElemAbelian_cjSub (g := g⁻¹) (A := A) hAel
  have hA'card : Nat.card ↥A' = Nat.card ↥A := by
    rw [hA', conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have ha'A' : a' ∈ A' := by
    rw [hA', CFSG.Quasithin.mem_conjSubgroup_iff, ha']
    have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [this]
    exact haA
  have ha'T : a' ∈ T := hA'T ha'A'
  have ha'L : a' ∉ L := by
    intro hL
    apply haL
    have hconj : g * a' * g⁻¹ = a := by rw [ha']; group
    exact hconj ▸ h.normal.conj_mem a' hL g
  have ha'2 : a' * a' = 1 := by
    rw [ha']
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hA'Ω : A' ∈ Ω := by
    rw [hA']
    exact hΩ.conj A hAΩ g
  exact ⟨A', a', hA', hA'Ω, hA'T, hA'el, hA'card, ha', ha'A', ha'T, ha'L, ha'2⟩

private theorem isSylowTwoOf_centralizer_conj {S T' : Subgroup Q} {a g : Q}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S (Subgroup.centralizer ({a} : Set Q)))
    (hST' : S ≤ T') (hT' : CFSG.QuasithinUnique.IsSylowTwoOf T' ⊤)
    (hgT' : T' = T.map (MulAut.conj g).toMonoidHom) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({g⁻¹ * a * g} : Set Q))
      (Subgroup.centralizer ({g⁻¹ * a * g} : Set Q)) := by
  have hSTC : T' ⊓ Subgroup.centralizer ({a} : Set Q) = S :=
    hS.eq_of_le (le_inf hST' hS.le) inf_le_right (hT'.isPGroup.to_le inf_le_left)
  have hcentmap : (Subgroup.centralizer ({a} : Set Q)).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({g⁻¹ * a * g} : Set Q) := by
    have h1 : Subgroup.centralizer ({a} : Set Q) =
        Subgroup.centralizer (↑(Subgroup.zpowers a) : Set Q) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : Subgroup.centralizer ({g⁻¹ * a * g} : Set Q) =
        Subgroup.centralizer (↑(Subgroup.zpowers (g⁻¹ * a * g)) : Set Q) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h3 : conjSubgroup (Subgroup.zpowers a) g = Subgroup.zpowers (g⁻¹ * a * g) := by
      rw [show conjSubgroup (Subgroup.zpowers a) g =
        (Subgroup.zpowers a).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
        MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h1, h2]
    change conjSubgroup (Subgroup.centralizer (↑(Subgroup.zpowers a) : Set Q)) g =
      Subgroup.centralizer (↑(Subgroup.zpowers (g⁻¹ * a * g)) : Set Q)
    rw [CFSG.Quasithin.E3.conjSubgroup_centralizer, h3]
  have hTmap : T'.map (MulAut.conj g⁻¹).toMonoidHom = T := by
    rw [hgT', Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id Q := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    rw [hcomp, Subgroup.map_id]
  have hminf : (T' ⊓ Subgroup.centralizer ({a} : Set Q)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      T'.map (MulAut.conj g⁻¹).toMonoidHom ⊓
        (Subgroup.centralizer ({a} : Set Q)).map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective
  have hmain := hS.map_equiv (MulAut.conj g⁻¹)
  rw [← hSTC, hminf, hTmap, hcentmap] at hmain
  exact hmain

private theorem exists_conj_sylow_data (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    {a : Q} (haA : a ∈ A) (haL : a ∉ L) (ha2 : a * a = 1) :
    ∃ (g : Q) (A' K : Subgroup Q) (a' : Q),
      A' = conjSubgroup A g ∧ A' ∈ Ω ∧ A' ≤ T ∧ IsElemAbelian 2 A' ∧
      Nat.card ↥A' = Nat.card ↥A ∧ a' = g⁻¹ * a * g ∧ a' ∈ A' ∧ a' ∈ T ∧ a' ∉ L ∧
      a' * a' = 1 ∧ K = Subgroup.centralizer ({a'} : Set Q) ∧
      CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := by
  classical
  have hAel : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hAC : A ≤ Subgroup.centralizer ({a} : Set Q) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hAel.comm hx haA)
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  obtain ⟨S, hAS, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le hAC hA2
  obtain ⟨T', hST', hT'⟩ :=
    CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS.isPGroup
  obtain ⟨g, -, hgT'⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj (S := T) (S' := T') (H := ⊤)
      (h.sylow : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) hT'
  obtain ⟨A', a', hA'eq, hA'Ω, hA'T, hA'el, hA'card, ha'eq, ha'A', ha'T, ha'L, ha'2⟩ :=
    exists_conj_facts h hΩ hAΩ haA haL ha2 hAS hST' hgT'
  have hSyl := isSylowTwoOf_centralizer_conj hS hST' hT' hgT'
  refine ⟨g, A', Subgroup.centralizer ({a'} : Set Q), a', hA'eq, hA'Ω, hA'T, hA'el, hA'card,
    ha'eq, ha'A', ha'T, ha'L, ha'2, rfl, ?_⟩
  simpa [ha'eq] using hSyl

private theorem le_rad_inf_of_swap (h : Setting L T P₀ P₁ n w) {B : Subgroup Q} {a' : Q}
    (ha'T : a' ∈ T) (hsw' : P₀.map (MulAut.conj a').toMonoidHom = P₁)
    (hBTL : B ≤ T ⊓ L) (hBelem : IsElemAbelian 2 B)
    (hcomm : ∀ b ∈ B, a' * b = b * a') :
    B ≤ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
  have hR : pCoreOf 2 (perfectCore P₁) =
      (pCoreOf 2 (perfectCore P₀)).map (MulAut.conj a').toMonoidHom :=
    pCoreOf_perfectCore_map_conj hsw'
  have hsw'' : P₁.map (MulAut.conj a').toMonoidHom = P₀ := by
    rcases map_conj_eq_or h ha'T with h0 | h0
    · exact absurd ((hsw'.symm.trans h0.1).symm) h.par_ne
    · exact h0.2
  have hR' : pCoreOf 2 (perfectCore P₀) =
      (pCoreOf 2 (perfectCore P₁)).map (MulAut.conj a').toMonoidHom :=
    pCoreOf_perfectCore_map_conj hsw''
  rcases le_or_le_of_isElemAbelian h hBTL hBelem with h0 | h1
  · exact le_inf h0 (le_of_le_map_conj h0 hcomm hR)
  · exact le_inf (le_of_le_map_conj h1 hcomm hR') h1

private theorem B_facts (h : Setting L T P₀ P₁ n w) {A' K B : Subgroup Q} {a' : Q}
    (hB : B = A' ⊓ L) (hcard : 2 ^ n < Nat.card ↥A') (hA'T : A' ≤ T)
    (hA'el : IsElemAbelian 2 A') (ha'A' : a' ∈ A') (ha'T : a' ∈ T) (ha'L : a' ∉ L)
    (hK : K = Subgroup.centralizer ({a'} : Set Q))
    (hsw' : P₀.map (MulAut.conj a').toMonoidHom = P₁) :
    B ≤ T ⊓ L ∧ IsElemAbelian 2 B ∧ B ≤ L ⊓ K ∧ A' ≤ K ∧
      Nat.card ↥A' ≤ 2 * Nat.card ↥B ∧
      B ≤ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) ∧
      Nat.card ↥B ≤ 2 ^ n ∧ B ≠ ⊥ := by
  have hAK : A' ≤ K := by
    rw [hK]
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hA'el.comm hx ha'A')
  have hBTL : B ≤ T ⊓ L := by
    rw [hB]
    exact le_inf (inf_le_left.trans hA'T) inf_le_right
  have hBelem : IsElemAbelian 2 B := by
    rw [hB]
    exact CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hA'el
  have hBJ : B ≤ L ⊓ K := by
    rw [hB]
    exact le_inf inf_le_right (inf_le_left.trans hAK)
  have hA'B : Nat.card ↥A' ≤ 2 * Nat.card ↥B := by
    rw [hB]
    exact h.out A' hA'T hA'el
  have hBcomm : ∀ b ∈ B, a' * b = b * a' := fun b hb => hA'el.comm ha'A' (hB ▸ hb).1
  have hBinf := le_rad_inf_of_swap h ha'T hsw' hBTL hBelem hBcomm
  have hBcard : Nat.card ↥B ≤ 2 ^ n := card_le_of_swap h ha'T hsw' hBinf hBcomm
  have hn2 : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h.two_le
    simpa using this
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hAcard2 : Nat.card ↥A' ≤ 2 := by
      calc Nat.card ↥A' ≤ 2 * Nat.card ↥B := hA'B
        _ = 2 * 1 := by rw [hbot, Subgroup.card_bot]
        _ = 2 := by norm_num
    have hlt : Nat.card ↥A' < 2 ^ n :=
      lt_of_le_of_lt hAcard2 (lt_of_lt_of_le (by norm_num) hn2)
    exact absurd hcard (not_lt.mpr hlt.le)
  exact ⟨hBTL, hBelem, hBJ, hAK, hA'B, hBinf, hBcard, hBne⟩

private theorem pCoreOf_inf_eq_bot (h : Setting L T P₀ P₁ n w) {K J : Subgroup Q}
    (hJ : J = L ⊓ K) (hsJ : IsSimpleGroup ↥J) (hnabJ : ∃ x y : ↥J, x * y ≠ y * x) :
    pCoreOf 2 K ⊓ L = ⊥ := by
  have hNK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hJK : J ≤ K := hJ.le.trans inf_le_right
  have hJN : J ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup Q) : Set Q) :=
    hJK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hnorm : J ≤ Subgroup.normalizer (((pCoreOf 2 K) ⊓ J : Subgroup Q) : Set Q) :=
    (le_inf hJN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNJ : (pCoreOf 2 K) ⊓ J ≤ J := inf_le_right
  haveI : (((pCoreOf 2 K) ⊓ J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr hnorm
  rcases hsJ.eq_bot_or_eq_top_of_normal (((pCoreOf 2 K) ⊓ J).subgroupOf J) with h | h
  · have hbot : (pCoreOf 2 K) ⊓ J = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hNJ, h, Subgroup.map_bot]
    calc (pCoreOf 2 K) ⊓ L = (pCoreOf 2 K) ⊓ (L ⊓ K) := by
          refine le_antisymm (fun x hx => ⟨hx.1, hx.2, hNK hx.1⟩)
            (fun x hx => ⟨hx.1, hx.2.1⟩)
      _ = (pCoreOf 2 K) ⊓ J := by rw [← hJ]
      _ = ⊥ := hbot
  · exfalso
    have hJleN : J ≤ pCoreOf 2 K := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥J) ∈ (((pCoreOf 2 K) ⊓ J).subgroupOf J) := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h1).1
    exact CFSG.Quasithin.H13.NQRigid.not_isPGroup_two_of_simple hnabJ
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hJleN)

private theorem card_zpowers_of_involution {a : Q} (ha2 : a * a = 1) (hne : a ≠ 1) :
    Nat.card ↥(Subgroup.zpowers a) = 2 := by
  rw [Nat.card_zpowers]
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ha2)
  have hne1 : orderOf a ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hpos : 0 < orderOf a := orderOf_pos a
  have hle : orderOf a ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem mem_pCoreOf_centralizer_of_involution {a' : Q} (ha'2 : a' * a' = 1)
    (ha'ne : a' ≠ 1) :
    a' ∈ pCoreOf 2 (Subgroup.centralizer ({a'} : Set Q)) := by
  have hzp : IsPGroup 2 (Subgroup.zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_of_involution ha'2 ha'ne]; norm_num)
  have hleK : Subgroup.zpowers a' ≤ Subgroup.centralizer ({a'} : Set Q) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hKnorm : Subgroup.centralizer ({a'} : Set Q) ≤
      Subgroup.normalizer ((Subgroup.zpowers a' : Subgroup Q) : Set Q) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hx' : x * a' = a' * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [MonoidHom.map_zpowers]
    congr 1
    change MulAut.conj x a' = a'
    rw [MulAut.conj_apply, hx']
    group
  exact CFSG.QuasithinUnique.le_pCoreOf_of_normalizes hleK hKnorm hzp
    (Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one a'⟩)

private theorem card_pCoreOf_le_two (h : Setting L T P₀ P₁ n w) (hodd : Odd n) {K : Subgroup Q}
    (hNL : pCoreOf 2 K ⊓ L = ⊥) : Nat.card ↥(pCoreOf 2 K) ≤ 2 := by
  have hcard := Subgroup.relIndex_mul_card (H := L) (K := pCoreOf 2 K)
  have hinf : L ⊓ pCoreOf 2 K = ⊥ := by rw [inf_comm]; exact hNL
  have h1 : Nat.card ↥(pCoreOf 2 K) = L.relIndex (pCoreOf 2 K) := by
    rw [hinf, Subgroup.card_bot, mul_one] at hcard
    exact hcard.symm
  rw [h1]
  have h2 : L.relIndex (pCoreOf 2 K) ≤ L.relIndex K :=
    Subgroup.relIndex_le_of_le_right (H := L) (K := pCoreOf 2 K) (L := K)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K) Subgroup.index_ne_zero_of_finite
  have h3 : L.relIndex K ≤ L.index := by
    have h4 := Subgroup.relIndex_le_of_le_right (H := L) (K := K) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right L] at h4
  exact (h2.trans h3).trans (h.index_odd hodd)

private theorem isSimpleGroup_modO2_of_simple {J : Subgroup Q} (hsJ : IsSimpleGroup ↥J)
    (hnabJ : ∃ x y : ↥J, x * y ≠ y * x) :
    IsSimpleGroup (CFSG.Quasithin.ModO2 J) := by
  have hnp : ¬ IsPGroup 2 ↥J := CFSG.Quasithin.H13.NQRigid.not_isPGroup_two_of_simple hnabJ
  have hpJ : pCoreOf 2 J = ⊥ := CFSG.Quasithin.H13.pCoreOf_eq_bot_of_simple hsJ hnp
  have hpJ' : CFSG.pCore 2 ↥J = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥J) J.subtype_injective).mp hpJ
  haveI : IsSimpleGroup ↥J := hsJ
  have e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hpJ').trans QuotientGroup.quotientBot
  exact e.isSimpleGroup

private theorem index_subgroupOf_inf_eq_two (h : Setting L T P₀ P₁ n w) (hodd : Odd n)
    {K : Subgroup Q} {a' : Q} (ha'K : a' ∈ K) (ha'L : a' ∉ L) :
    ((L ⊓ K).subgroupOf K).index = 2 := by
  have hsub : (L ⊓ K).subgroupOf K = L.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [hsub]
  have hne1 : (L.subgroupOf K).index ≠ 1 := by
    intro h1
    have h2 : L.relIndex K = 1 := h1
    exact ha'L (Subgroup.relIndex_eq_one.mp h2 ha'K)
  have hle : (L.subgroupOf K).index ≤ 2 := by
    have h4 := Subgroup.relIndex_le_of_le_right (H := L) (K := K) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rw [Subgroup.relIndex_top_right L] at h4
    exact h4.trans (h.index_odd hodd)
  have h0 : (L.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

private theorem mQuot_le_of_card_inf {A' N B : Subgroup Q} {n : ℕ}
    (hA2 : IsPGroup 2 A') (hinf2 : 2 ≤ Nat.card ↥(N ⊓ A'))
    (hAcard : Nat.card ↥A' ≤ 2 * Nat.card ↥B) (hBcard : Nat.card ↥B ≤ 2 ^ n) :
    CFSG.Quasithin.E3.mQuot A' N ≤ n := by
  have hcard := Subgroup.relIndex_mul_card (H := N) (K := A')
  have h1 : N.relIndex A' ≤ Nat.card ↥A' / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc N.relIndex A' * 2 ≤ N.relIndex A' * Nat.card ↥(N ⊓ A') := Nat.mul_le_mul_left _ hinf2
      _ = Nat.card ↥A' := hcard
  have h2 : Nat.card ↥A' / 2 ≤ Nat.card ↥B := by
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
    omega
  have h3 : N.relIndex A' ≤ 2 ^ n := h1.trans (h2.trans hBcard)
  rw [CFSG.Quasithin.E3.relIndex_eq_two_pow hA2 N] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3

private theorem not_le_normalizer_inf (h : Setting L T P₀ P₁ n w) {K J B U : Subgroup Q}
    (hJ : J = L ⊓ K) (hU : U = T ⊓ L) (hBJ : B ≤ J) (hBU : B ≤ U) (hBne : B ≠ ⊥)
    (hU2 : IsPGroup 2 ↥(T ⊓ L)) (hsJ : IsSimpleGroup ↥J)
    (hnabJ : ∃ x y : ↥J, x * y ≠ y * x) :
    ¬ K ≤ Subgroup.normalizer (U : Set Q) := by
  rw [hU] at hBU ⊢
  intro hKU
  have hJnorm : J ≤ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    hJ.le.trans (inf_le_right.trans hKU)
  have hJU : J ⊓ (T ⊓ L) ≤ J := inf_le_left
  haveI : ((J ⊓ (T ⊓ L)).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJU).mpr
      ((le_inf Subgroup.le_normalizer hJnorm).trans Subgroup.inf_normalizer_le_normalizer_inf)
  rcases hsJ.eq_bot_or_eq_top_of_normal ((J ⊓ (T ⊓ L)).subgroupOf J) with hbot | htop
  · have hbot' : J ⊓ (T ⊓ L) = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hJU, hbot, Subgroup.map_bot]
    have hBbot : B ≤ ⊥ := (le_inf hBJ hBU).trans (le_of_eq hbot')
    exact hBne (le_bot_iff.mp hBbot)
  · have hJUle : J ≤ T ⊓ L := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥J) ∈ (J ⊓ (T ⊓ L)).subgroupOf J := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1 |>.2
    exact CFSG.Quasithin.H13.NQRigid.not_isPGroup_two_of_simple hnabJ
      ((hU2.to_le hJUle) : IsPGroup 2 ↥J)

private theorem exists_commutator_not_mem_pCore {B J : Subgroup Q} (hBJ : B ≤ J)
    (hsJ : IsSimpleGroup ↥J) (hnabJ : ∃ x y : ↥J, x * y ≠ y * x) (hBne : B ≠ ⊥)
    (hpJ : pCoreOf 2 J = ⊥) :
    ∃ b ∈ B, ∃ x ∈ J, ⁅b, x⁆ ∉ pCoreOf 2 J := by
  have hbne : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    apply hBne
    refine le_antisymm (fun b hb => ?_) bot_le
    by_contra hb1
    exact h ⟨b, hb, fun h1 => hb1 (Subgroup.mem_bot.mpr h1)⟩
  obtain ⟨b, hbB, hb1⟩ := hbne
  have hbC : b ∉ Subgroup.centralizer (J : Set Q) := by
    intro hbc
    have hmem : b ∈ J ⊓ Subgroup.centralizer (J : Set Q) := ⟨hBJ hbB, hbc⟩
    rw [CFSG.Quasithin.H13.inf_centralizer_eq_bot_of_simple hsJ hnabJ] at hmem
    exact hb1 (Subgroup.mem_bot.mp hmem)
  have hnot : ∃ x ∈ J, b * x ≠ x * b := by
    by_contra h
    apply hbC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_contra hbx
    exact h ⟨x, hx, fun h1 => hbx h1.symm⟩
  obtain ⟨x, hxJ, hbx⟩ := hnot
  refine ⟨b, hbB, x, hxJ, ?_⟩
  rw [hpJ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hbx

private theorem eCaseII_centralizer (h : Setting L T P₀ P₁ n w) (hodd : Odd n) {A' K : Subgroup Q}
    {a' : Q} (hK : K = Subgroup.centralizer ({a'} : Set Q)) (ha'T : a' ∈ T) (ha'L : a' ∉ L)
    (ha'2 : a' * a' = 1) (hAK : A' ≤ K)
    (hAJ : ∃ b ∈ A', ∃ x ∈ L ⊓ K, ⁅b, x⁆ ∉ pCoreOf 2 (L ⊓ K)) :
    ECaseII T A' K := by
  have hJeq : L ⊓ K = L ⊓ Subgroup.centralizer ({a'} : Set Q) := by rw [hK]
  have su := h.suzuki hodd a' ha'T ha'L ha'2
  have hsJ : IsSimpleGroup ↥(L ⊓ K) := hJeq.symm ▸ su.1
  have hnabJ : ∃ x y : ↥(L ⊓ K), x * y ≠ y * x := hJeq.symm ▸ su.2
  haveI : L.Normal := h.normal
  have hKL : K ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hnormK : K ≤ Subgroup.normalizer ((L ⊓ K : Subgroup Q) : Set Q) :=
    (le_inf hKL Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hJn : ((L ⊓ K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnormK
  have hJne : L ⊓ K ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥(L ⊓ K) := by rw [hbot]; infer_instance
    obtain ⟨x, y, hxy⟩ := hnabJ
    have hxy' : x = y := Subsingleton.elim x y
    exact hxy (by rw [hxy'])
  have hJperf : ⁅L ⊓ K, L ⊓ K⁆ = L ⊓ K :=
    CFSG.Quasithin.H13.commutator_eq_of_simple hsJ hnabJ le_rfl hJne
  have hJs : IsSimpleGroup (CFSG.Quasithin.ModO2 (L ⊓ K)) :=
    isSimpleGroup_modO2_of_simple hsJ hnabJ
  have ha'K : a' ∈ K := by
    rw [hK]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hidx : ((L ⊓ K).subgroupOf K).index = 2 :=
    index_subgroupOf_inf_eq_two h hodd ha'K ha'L
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ L ⊓ K := by
    intro x hx
    have h := Subgroup.sq_mem_of_index_two hidx (⟨x, hx⟩ : K)
    exact ⟨1, by rw [pow_one]; exact Subgroup.mem_subgroupOf.mp h⟩
  exact CFSG.LocalAnalysis.WeakClosure81.eCaseII_of_normal_perfect inf_le_right hJn hJperf hJs
    hK2 hAK hAJ

private theorem centralizer_k_data (h : Setting L T P₀ P₁ n w) (hodd : Odd n)
    {A' K B : Subgroup Q} {a' : Q} (hK : K = Subgroup.centralizer ({a'} : Set Q))
    (hsJ : IsSimpleGroup ↥(L ⊓ K)) (hnabJ : ∃ x y : ↥(L ⊓ K), x * y ≠ y * x)
    (hA'el : IsElemAbelian 2 A') (ha'A' : a' ∈ A') (ha'T : a' ∈ T) (ha'L : a' ∉ L)
    (ha'2 : a' * a' = 1)
    (hcard : 2 ^ n < Nat.card ↥A') (hA'B : Nat.card ↥A' ≤ 2 * Nat.card ↥B)
    (hBcard : Nat.card ↥B ≤ 2 ^ n) :
    ¬ A' ≤ pCoreOf 2 K ∧ CFSG.Quasithin.E3.mQuot A' (pCoreOf 2 K) ≤ n ∧
      a' ∈ pCoreOf 2 K := by
  have ha'ne : a' ≠ 1 := fun h1 => ha'L (by rw [h1]; exact L.one_mem)
  have hNL : pCoreOf 2 K ⊓ L = ⊥ := pCoreOf_inf_eq_bot h rfl hsJ hnabJ
  have hNcard : Nat.card ↥(pCoreOf 2 K) ≤ 2 := card_pCoreOf_le_two h hodd hNL
  have hNmem : a' ∈ pCoreOf 2 K := by
    rw [hK]
    exact mem_pCoreOf_centralizer_of_involution ha'2 ha'ne
  have hn2 : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h.two_le
    simpa using this
  have hnotAN : ¬ A' ≤ pCoreOf 2 K := by
    intro hAN
    have hcardN : Nat.card ↥A' ≤ 2 := (Subgroup.card_le_of_le hAN).trans hNcard
    have hlt : Nat.card ↥A' < 2 ^ n :=
      lt_of_le_of_lt hcardN (lt_of_lt_of_le (by norm_num) hn2)
    exact absurd hcard (not_lt.mpr hlt.le)
  have hquot : CFSG.Quasithin.E3.mQuot A' (pCoreOf 2 K) ≤ n := by
    have hA2 : IsPGroup 2 ↥A' := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hA'el
    have hinfa' : a' ∈ (pCoreOf 2 K) ⊓ A' := ⟨hNmem, ha'A'⟩
    have hinf2 : 2 ≤ Nat.card ↥((pCoreOf 2 K) ⊓ A') := by
      have hle : Subgroup.zpowers a' ≤ (pCoreOf 2 K) ⊓ A' := Subgroup.zpowers_le.mpr hinfa'
      calc 2 = Nat.card ↥(Subgroup.zpowers a') := (card_zpowers_of_involution ha'2 ha'ne).symm
        _ ≤ Nat.card ↥((pCoreOf 2 K) ⊓ A') := Subgroup.card_le_of_le hle
    exact mQuot_le_of_card_inf hA2 hinf2 hA'B hBcard
  exact ⟨hnotAN, hquot, hNmem⟩

private theorem inCalEi_of_data (h : Setting L T P₀ P₁ n w) {A' K : Subgroup Q} {a' : Q}
    (hK : K = Subgroup.centralizer ({a'} : Set Q)) (ha'A' : a' ∈ A')
    (hKsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K) (hnotAN : ¬ A' ≤ pCoreOf 2 K)
    (heCase : ECaseII T A' K) (hquot : CFSG.Quasithin.E3.mQuot A' (pCoreOf 2 K) ≤ n) :
    InCalEi n T A' K := by
  have htA : tA T A' ≤ T ⊓ K := by
    rw [tA_eq h A', hK]
    exact inf_le_inf_left T fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx a' ha'A').symm
  exact ⟨⟨htA, hKsyl, hnotAN, Or.inr heCase⟩, hquot⟩

theorem exists_inCalEi_of_not_stab (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hcard : 2 ^ n < Nat.card ↥A) (hAS : ∃ a ∈ A, P₀.map (MulAut.conj a).toMonoidHom ≠ P₀) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ K : Subgroup Q, InCalEi n T A' K ∧
      ¬ K ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  classical
  obtain ⟨a, haA, ha2, haL, hsw, hodd⟩ := exists_involution_swap h hΩ hAΩ hAT hAS
  have haT : a ∈ T := hAT haA
  obtain ⟨g, A', K, a', hA'eq, hA'Ω, hA'T, hA'el, hA'card, ha'eq, ha'A', ha'T, ha'L, ha'2,
    hK, hKsyl⟩ := exists_conj_sylow_data h hΩ hAΩ hAT haA haL ha2
  rw [← hA'card] at hcard
  have hsw' : P₀.map (MulAut.conj a').toMonoidHom = P₁ :=
    map_conj_eq_of_not_mem h haT haL ha2 hsw ha'T ha'L
  set B : Subgroup Q := A' ⊓ L with hB
  obtain ⟨hBTL, hBelem, hBJ, hAK, hA'B, hBinf, hBcard, hBne⟩ :=
    B_facts h hB hcard hA'T hA'el ha'A' ha'T ha'L hK hsw'
  have hsu := h.suzuki hodd a' ha'T ha'L ha'2
  have hJeq : L ⊓ K = L ⊓ Subgroup.centralizer ({a'} : Set Q) := by rw [hK]
  have hsJ : IsSimpleGroup ↥(L ⊓ K) := hJeq.symm ▸ hsu.1
  have hnabJ : ∃ x y : ↥(L ⊓ K), x * y ≠ y * x := hJeq.symm ▸ hsu.2
  have hpJ : pCoreOf 2 (L ⊓ K) = ⊥ := CFSG.Quasithin.H13.pCoreOf_eq_bot_of_simple hsJ
    (CFSG.Quasithin.H13.NQRigid.not_isPGroup_two_of_simple hnabJ)
  obtain ⟨b, hbB, x, hxJ, hbx⟩ :=
    exists_commutator_not_mem_pCore hBJ hsJ hnabJ hBne hpJ
  have hAJ : ∃ b ∈ A', ∃ x ∈ L ⊓ K, ⁅b, x⁆ ∉ pCoreOf 2 (L ⊓ K) :=
    ⟨b, (hB ▸ hbB).1, x, hxJ, hbx⟩
  have heCase : ECaseII T A' K := eCaseII_centralizer h hodd hK ha'T ha'L ha'2 hAK hAJ
  obtain ⟨hnotAN, hquot, -⟩ :=
    centralizer_k_data h hodd hK hsJ hnabJ hA'el ha'A' ha'T ha'L ha'2 hcard hA'B hBcard
  refine ⟨A', hA'Ω, hA'T, K, inCalEi_of_data h hK ha'A'
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hKsyl) hnotAN heCase hquot, ?_⟩
  exact not_le_normalizer_inf h rfl rfl hBJ hBTL hBne
    (h.sylow.isPGroup.to_le (K := T) (H := T ⊓ L) inf_le_left) hsJ hnabJ

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
