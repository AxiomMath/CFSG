module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.StarA
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Lemma7f
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Cover

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem index_eq_relIndex_of_sup_eq_top' {H : Type} [Group H] [Finite H] (N K : Subgroup H)
    [K.Normal] (hNK : N ⊔ K = ⊤) : N.index = N.relIndex K := by
  have h1 : N.relIndex K * K.relIndex ⊤ = (N ⊓ K).relIndex ⊤ := by
    have := Subgroup.relIndex_inf_mul_relIndex (H := N) (K := K) (L := ⊤)
    rwa [inf_top_eq] at this
  have h2 : (N ⊓ K).relIndex N * N.relIndex ⊤ = (N ⊓ K).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex (N ⊓ K) N ⊤ inf_le_left le_top
  have h3 : (N ⊓ K).relIndex N = K.relIndex N := Subgroup.inf_relIndex_left N K
  have h4 : K.relIndex ⊤ = K.relIndex N := by
    have := Subgroup.relIndex_sup_right (K := K) (H := N)
    rwa [hNK] at this
  have hI : N.relIndex ⊤ = N.index := Subgroup.relIndex_top_right N
  have hKN : K.relIndex N ≠ 0 := by
    rw [← h4, Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have key : K.relIndex N * N.index = K.relIndex N * N.relIndex K := by
    calc K.relIndex N * N.index = K.relIndex N * N.relIndex ⊤ := by rw [hI]
      _ = (N ⊓ K).relIndex N * N.relIndex ⊤ := by rw [h3]
      _ = (N ⊓ K).relIndex ⊤ := h2
      _ = N.relIndex K * K.relIndex ⊤ := h1.symm
      _ = N.relIndex K * K.relIndex N := by rw [h4]
      _ = K.relIndex N * N.relIndex K := mul_comm _ _
  exact mul_left_cancel₀ hKN key

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_eq_of_mul_eq {A B X : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hAn : X ≤ Subgroup.normalizer (A : Set G)) (hX : ∀ g ∈ X, ∃ a ∈ A, ∃ b ∈ B, g = a * b) :
    B.relIndex X = B.relIndex A := by
  have : (A.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hAn
  have hsup : B.subgroupOf X ⊔ A.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, b, hb, hab⟩ := hX x x.2
    have : x = ⟨a, hAX ha⟩ * ⟨b, hBX hb⟩ := Subtype.ext hab
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ha))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hb))
  have h := index_eq_relIndex_of_sup_eq_top' (B.subgroupOf X) (A.subgroupOf X) hsup
  have e : (B.subgroupOf X).relIndex (A.subgroupOf X) = B.relIndex A :=
    Subgroup.relIndex_subgroupOf hAX
  exact h.trans e

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem oTwoRes_sup_Qv_eq {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    oTwoRes (stab δ) ⊔ Qv l = stab δ := by
  have hvl := vtype_true_of_mem_nbrs_false hl hδ
  have hδl : δ ∈ nbrs l := mem_nbrs_comm hl
  have hLs : oTwoRes (stab δ) ≤ stab δ := oTwoRes_le _
  have hQls : Qv l ≤ stab l ⊓ stab δ := Qv_le_inf C.hA hδl
  have hQl_stδ : Qv l ≤ stab δ := fun x hx => (hQls hx).2
  have h28 := C.h28 C.hb1 l δ hδl (C.bAt_eq_of_true hvl)
  have hcov : (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ = stab δ := by
    refine le_antisymm (sup_le (sup_le hLs hQl_stδ) (pCoreOf_le 2 (stab δ))) fun g hg => ?_
    obtain ⟨x, hxL, hxl⟩ := C.exists_oTwoRes_smul hl (smul_mem_nbrs_stab (g := ⟨g, stab_le δ hg⟩)
      (ν := δ) hg hl)
    have hxs : (x : G) ∈ stab δ := hLs hxL
    have hfix : (x⁻¹ * (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M))) • l = l := by
      rw [mul_smul, ← hxl, inv_smul_smul]
    have hy1 : (x : G)⁻¹ * g ∈ stab l := by
      have := mem_stab_of_smul_eq hfix
      simpa using this
    have hy2 : (x : G)⁻¹ * g ∈ stab δ := (stab δ).mul_mem ((stab δ).inv_mem hxs) hg
    have hy : (x : G)⁻¹ * g ∈ Qv l ⊔ Qv δ := by rw [h28]; exact ⟨hy1, hy2⟩
    have e : g = (x : G) * ((x : G)⁻¹ * g) := by group
    rw [e]
    have hx' : (x : G) ∈ (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hxL)
    have hsub : Qv l ⊔ Qv δ ≤ (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ :=
      sup_le (le_sup_right.trans le_sup_left) le_sup_right
    exact Subgroup.mul_mem _ hx' (hsub hy)
  exact C.eq_stab_of_cover hδ hl (sup_le hLs hQl_stδ) le_sup_right hcov

theorem inter_le_of_perfect {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ)
    (hperf : ⁅oTwoRes (stab δ), oTwoRes (stab δ)⁆ = oTwoRes (stab δ))
    (hQL : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l) : oTwoRes (stab δ) ⊓ Qv δ ≤ Qv l := by
  classical
  by_contra hcon
  obtain ⟨t, ⟨htL, htQ⟩, htl⟩ := Set.not_subset.mp hcon
  have hvl := vtype_true_of_mem_nbrs_false hl hδ
  have hδl : δ ∈ nbrs l := mem_nbrs_comm hl
  have hLs : oTwoRes (stab δ) ≤ stab δ := oTwoRes_le _
  have hLn : stab δ ≤ Subgroup.normalizer ((oTwoRes (stab δ) : Subgroup G) : Set G) :=
    le_normalizer_oTwoRes _
  have hQls : Qv l ≤ stab l ⊓ stab δ := Qv_le_inf C.hA hδl
  have hQl_stδ : Qv l ≤ stab δ := fun x hx => (hQls hx).2
  have hnorm := C.star_normal hl hQL
  have hN2 := C.relIndex_Qv_inf_Qv hδ hl
  have hU := C.oTwoRes_sup_Qv_eq hδ hl
  have hdec : ∀ g ∈ stab δ, ∃ a ∈ oTwoRes (stab δ), ∃ b ∈ Qv l, g = a * b := by
    intro g hg
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_le_normalizer (N := oTwoRes (stab δ)) (K := Qv l)
      (fun x hx => hLn (hQl_stδ hx)) (hU ▸ hg)
    exact ⟨a, ha, b, hb, hab⟩
  have h1 := relIndex_eq_of_mul_eq hLs hQl_stδ hLn hdec
  have hBst : stab δ ⊓ stab l ≤ stab δ := inf_le_left
  have hQlB : Qv l ≤ stab δ ⊓ stab l := fun x hx => ⟨(hQls hx).2, (hQls hx).1⟩
  have h2 := Subgroup.relIndex_mul_relIndex (Qv l) (stab δ ⊓ stab l) (stab δ) hQlB hBst
  have h3 : (Qv l).relIndex (stab δ ⊓ stab l) = 2 := by
    rw [inf_comm]; exact relIndex_Qv_inf_true C.hA hδl hvl
  have hodd : ¬ 2 ∣ (stab δ ⊓ stab l).relIndex (stab δ) := (sylow_stab_inf_left C.hA hl).2.2
  obtain ⟨r, hr⟩ : ∃ r, (Qv l).relIndex (oTwoRes (stab δ)) = 2 * r ∧ ¬ 2 ∣ r := by
    refine ⟨(stab δ ⊓ stab l).relIndex (stab δ), ?_, hodd⟩
    rw [← h1, ← h2, h3]
  set L : Subgroup G := oTwoRes (stab δ) with hLdef
  set M' : Subgroup ↥L := (Qv l).subgroupOf L with hM'
  have hcard : Nat.card (↥L ⧸ M') = 2 * r := by
    rw [← hr.1]; rfl
  let _ : Fintype (↥L ⧸ M') := Fintype.ofFinite _
  let σ0 : ↥L →* Equiv.Perm (↥L ⧸ M') := MulAction.toPermHom ↥L (↥L ⧸ M')
  let s : ↥L →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (↥L ⧸ M') →* ℤˣ).comp σ0
  have hs1 : ∀ x : ↥L, s x = 1 := by
    have hle : ⁅L, L⁆ ≤ s.ker.map L.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hxy : ⁅x, y⁆ ∈ L := by
        have := Subgroup.commutator_mem_commutator hx hy
        rwa [hperf] at this
      refine ⟨⟨⁅x, y⁆, hxy⟩, ?_, rfl⟩
      show s _ = 1
      have : (⟨⁅x, y⁆, hxy⟩ : ↥L) = ⁅(⟨x, hx⟩ : ↥L), (⟨y, hy⟩ : ↥L)⁆ := rfl
      rw [this, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    intro x
    have hxL : (x : G) ∈ ⁅L, L⁆ := by rw [hperf]; exact x.2
    have := hle hxL
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rw [← this]; exact hy
  set t' : ↥L := ⟨t, htL⟩ with ht'
  have htN : ∀ x : ↥L, ¬ ((x : G)⁻¹ * (t : G)⁻¹ * (x : G) ∈ Qv l) := by
    intro x hx
    have hxs : (x : G) ∈ stab δ := hLs x.2
    have hQn : ∀ g ∈ stab δ, g ∈ Subgroup.normalizer (Qv δ : Set G) := fun g hg =>
      le_normalizer_pCoreOf 2 (stab δ) hg
    have hy : (x : G)⁻¹ * (t : G)⁻¹ * (x : G) ∈ Qv δ := by
      have h := (Subgroup.mem_normalizer_iff.mp (hQn _ ((stab δ).inv_mem hxs)) _).mp
        ((Qv δ).inv_mem htQ)
      simpa using h
    have h1 := hnorm _ hxs _ ⟨hy, hx⟩
    have h2 : (t : G)⁻¹ ∈ Qv δ ⊓ Qv l := by
      have e : (t : G)⁻¹ = (x : G) * ((x : G)⁻¹ * (t : G)⁻¹ * (x : G)) * (x : G)⁻¹ := by group
      rw [e]; exact h1
    exact htl (by simpa using (Qv l).inv_mem h2.2)
  have hfix : ∀ q : ↥L ⧸ M', σ0 t' q ≠ q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      intro h
      have h' : (QuotientGroup.mk (t' * x) : ↥L ⧸ M') = QuotientGroup.mk x := h
      rw [QuotientGroup.eq, hM', Subgroup.mem_subgroupOf] at h'
      apply htN x
      simpa [mul_assoc] using h'
  have htt : (t : G) * (t : G) ∈ Qv δ ⊓ Qv l := by
    have := Subgroup.mul_self_mem_of_index_two (H := (Qv δ ⊓ Qv l).subgroupOf (Qv δ)) hN2
      (⟨t, htQ⟩ : ↥(Qv δ))
    exact Subgroup.mem_subgroupOf.mp this
  have hsq : σ0 t' ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      show (QuotientGroup.mk (t' * t' * x) : ↥L ⧸ M') = QuotientGroup.mk x
      rw [QuotientGroup.eq, hM', Subgroup.mem_subgroupOf]
      have hxs : (x : G) ∈ stab δ := hLs x.2
      have h1 := hnorm _ ((stab δ).inv_mem hxs) _ ((Qv δ ⊓ Qv l).inv_mem htt)
      have e : ((t' * t' * x)⁻¹ * x : ↥L) = x⁻¹ * (t' * t')⁻¹ * x := by group
      rw [e]
      simpa [mul_assoc, ht'] using h1.2
  have hfp : Fintype.card (Function.fixedPoints (σ0 t')) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨q, hq⟩ => hfix q hq⟩
  have hsign : Equiv.Perm.sign (σ0 t') = -1 := by
    rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hfp, Nat.sub_zero, ← Nat.card_eq_fintype_card,
      hcard, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
  have := hs1 t'
  change Equiv.Perm.sign (σ0 t') = 1 at this
  rw [hsign] at this
  exact absurd this (by decide)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
