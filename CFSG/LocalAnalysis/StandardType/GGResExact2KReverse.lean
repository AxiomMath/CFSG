module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA

public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggResKRevAux_pi_ker {p : ℕ} [Fact p.Prime] {ι' : Type} [Fintype ι']
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) (φ : ι' → MulAut E) (h : ι' → V)
    (α : ι' → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hdiag : ∀ i, α i (h i) = 2) (hp2 : p ≠ 2)
    (N : Subgroup (MulAut E)) (hgen : N = Subgroup.closure (Set.range φ)) :
    (LinearMap.pi α).ker = ggFixedSubmodule (p := p) ι N := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hh : ∀ i, h i ≠ 0 := by
    intro i hi
    apply h2
    rw [← hdiag i, hi, map_zero]
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hvα : ∀ i, α i v = 0 := by
      intro i
      have := congrFun hv i
      simpa using this
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    rw [hgen] at hψ
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨i, rfl⟩
      rw [hlin, hvα i, zero_smul, sub_zero]
    · simp
    · intro x y _ _ hx hy
      rw [map_mul]
      change ggLin (p := p) ι x (ggLin (p := p) ι y v) = v
      rw [hy, hx]
    · intro x _ hx
      calc
        ggLin (p := p) ι x⁻¹ v =
            ggLin (p := p) ι x⁻¹ (ggLin (p := p) ι x v) := by rw [hx]
        _ = (ggLin (p := p) ι x⁻¹ * ggLin (p := p) ι x) v := rfl
        _ = ggLin (p := p) ι (x⁻¹ * x) v := by rw [map_mul]
        _ = ggLin (p := p) ι 1 v := by rw [inv_mul_cancel]
        _ = v := by simp
  · intro hv
    rw [mem_ggFixedSubmodule_iff] at hv
    rw [LinearMap.mem_ker]
    funext i
    have hfix : ggLin (p := p) ι (φ i) v = v := by
      apply hv
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hzero : α i v • h i = 0 := by
      have h' : v - α i v • h i = v := by
        rw [← hlin i v, hfix]
      exact sub_eq_self.mp h'
    exact (smul_eq_zero.mp hzero).resolve_right (hh i)

private theorem ggResKRevAux_finrank_le_card_add {p : ℕ} [Fact p.Prime] {ι' : Type}
    [Fintype ι'] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (α : ι' → Module.Dual (ZMod p) V) :
    Module.finrank (ZMod p) V ≤
      Fintype.card ι' + Module.finrank (ZMod p) (LinearMap.pi α).ker := by
  let : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let hMod : Module (ZMod p) (ι' → ZMod p) :=
    Pi.module ι' (fun _ => ZMod p) (ZMod p)
  let := hMod
  let π : V →ₗ[ZMod p] (ι' → ZMod p) := LinearMap.pi α
  have h := @LinearMap.finrank_range_add_finrank_ker (ZMod p) V _ _ _
    (ι' → ZMod p) (inferInstance : AddCommGroup (ι' → ZMod p)) hMod _ π
  have hcod : Module.finrank (ZMod p) (ι' → ZMod p) = Fintype.card ι' := by simp
  have hrange : Module.finrank (ZMod p) π.range ≤ Fintype.card ι' := by
    rw [← hcod]
    exact Submodule.finrank_le _
  change Module.finrank (ZMod p) V ≤
    Fintype.card ι' + Module.finrank (ZMod p) π.ker
  rw [← h]
  exact Nat.add_le_add_right hrange _

private theorem ggResKRevAux_finrank_le_one_of_card_le {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (W : Submodule (ZMod p) V) (hW : Nat.card W ≤ p) :
    Module.finrank (ZMod p) W ≤ 1 := by
  have hpow : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    let : Module.Finite (ZMod p) W := Module.Finite.of_finite
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod p) (V := W))
  have hle : p ^ Module.finrank (ZMod p) W ≤ p ^ 1 := by
    rw [← hpow]
    simpa using hW
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle


theorem ggResTBFix_finrank_le_card_add_one {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    {ι' : Type} [Fintype ι'] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (φ : ι' → MulAut ↥Bs) (h : ι' → V)
    (α : ι' → Module.Dual (ZMod p) V)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hdiag : ∀ o, α o (h o) = 2)
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    Module.finrank (ZMod p) V ≤ Fintype.card ι' + 1 := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 (hH.1.1.2.2.2.2.2.2.1.2.1)
  have hxne : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  have hxp : x ^ p = 1 := hH.1.2.1.2.1.2 x hxBs
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hxne]
  have hker : (LinearMap.pi α).ker = ggFixedSubmodule (p := p) ι (ggAutomizer L Bs) :=
    ggResKRevAux_pi_ker ι φ h α hlin hdiag hp2 (ggAutomizer L Bs) hgen
  have hcard : Nat.card ↥(ggFixedSubmodule (p := p) ι (ggAutomizer L Bs)) ≤ p := by
    let F := ggFixedSubmodule (p := p) ι (ggAutomizer L Bs)
    let g : F → ↥(Subgroup.zpowers x) := fun v =>
      let b : ↥Bs := Additive.toMul (ι.symm v.1)
      ⟨b, hTBF G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
        hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b (by
          intro ψ hψ
          have hv := (mem_ggFixedSubmodule_iff.mp v.2) ψ hψ
          have hv' : ggLin (p := p) ι ψ (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
            rw [show ι (Additive.ofMul b) = v.1 from by simp [b]]
            exact hv
          exact (ggLin_fix_iff (p := p) ι ψ b).mpr hv')⟩
    have hg : Function.Injective g := by
      intro v w hvw
      have h1 : (Additive.toMul (ι.symm v.1) : ↥Bs) = Additive.toMul (ι.symm w.1) := by
        apply Subtype.ext
        simpa [g] using congrArg Subtype.val hvw
      have h2 : ι.symm v.1 = ι.symm w.1 := Additive.toMul.injective h1
      exact Subtype.ext (ι.symm.injective h2)
    calc Nat.card F ≤ Nat.card ↥(Subgroup.zpowers x) :=
          Nat.card_le_card_of_injective g hg
      _ = p := hxcard
  have hdim := ggResKRevAux_finrank_le_card_add α
  rw [hker] at hdim
  have hfixdim : Module.finrank (ZMod p)
      (ggFixedSubmodule (p := p) ι (ggAutomizer L Bs)) ≤ 1 :=
    ggResKRevAux_finrank_le_one_of_card_le _ hcard
  omega


theorem ggResExact2_K_reverse_or_singular {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    (GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) ∨
    (GGResLeviDatumCard 2 p Bs K J L ggSelAny (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypLE6)) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, _htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumCard 2 p Bs K J L ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  rcases (by omega : 2 ≤ Nat.card Λa ∨ Nat.card Λa = 1) with hΛa2 | hΛa1
  · left
    have hrev := ggResLeviDatumCard_reverse_of_witness (p := p) (Bs := Bs) (L := K) (J := J)
      (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK) (V := V)
      (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega) hML hCL hMK hCK hlin hrefl
      hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
    have hc : Nat.card Λa = 2 ∨ Nat.card Λa = 3 := by omega
    rcases hc with hc | hc
    · exact Or.inl (by rwa [hc] at hrev)
    · exact Or.inr (by rwa [hc] at hrev)
  · right
    have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
    let φ' : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
    let h' : ({i : Λ // i ∉ S} ⊕ Λa) → V := fun o => h (o.map Subtype.val id)
    let α' : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) V :=
      fun o => α (o.map Subtype.val id)
    have hlin' : ∀ o w, ggLin (p := p) ι (φ' o) w = w - α' o w • h' o := fun o w => hlin _ w
    have hdiag' : ∀ o, α' o (h' o) = 2 := by
      intro o
      change α (o.map Subtype.val id) (h (o.map Subtype.val id)) = 2
      rw [hpairK o o, hCK.1 o]
      norm_num
    have hrange : Set.range φ' =
        Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      ext z
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact ⟨Sum.inl j, rfl⟩
        · exact ⟨Sum.inr a, rfl⟩
    have hgen' : ggAutomizer L Bs = Subgroup.closure (Set.range φ') := by
      rw [hclosK, hrange]
    have hdim := ggResTBFix_finrank_le_card_add_one hTBF hH ι φ' h' α' hlin' hdiag' hgen'
    have hcardS : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
      have h := Fintype.card_subtype_compl (α := Λ) (p := fun i => i ∈ S)
      rw [Fintype.card_coe] at h
      exact h
    have hSle : S.card ≤ Fintype.card Λ := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    have hΛa1' : Fintype.card Λa = 1 := by
      rw [← Nat.card_eq_fintype_card, hΛa1]
    have hcardι : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) + 1 = Fintype.card Λ := by
      rw [Fintype.card_sum, hcardS, hΛa1', hS]
      omega
    have hdimΛ : Module.finrank (ZMod p) V ≤ Fintype.card Λ := by omega
    have haxis := ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpair hCL.1
      hclosL
    have hranklt : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) < Fintype.card Λ := by
      omega
    have hsing := ggIntCartan_A_or_E6_of_rank_lt hML hCL hp2 hranklt
    rcases ggTypLADvd_or_E6_of_cartan_singular hCL hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
    · exact Or.inl (pack (ggTypLADvd p) ⟨hA, hpd⟩)
    · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩

theorem ggResExact2_K_reverse_of_rank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hrank : ∀ r c : ℕ, GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs)) c →
      p ^ (r + 1) ≤ Nat.card ↥Bs)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, _htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  rcases (by omega : 2 ≤ Nat.card Λa ∨ Nat.card Λa = 1) with hΛa2 | hΛa1
  · have hrev := ggResLeviDatumCard_reverse_of_witness (p := p) (Bs := Bs) (L := K) (J := J)
      (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK) (V := V)
      (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega) hML hCL hMK hCK hlin hrefl
      hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
    have hc : Nat.card Λa = 2 ∨ Nat.card Λa = 3 := by omega
    rcases hc with hc | hc
    · exact Or.inl (by rwa [hc] at hrev)
    · exact Or.inr (by rwa [hc] at hrev)
  · exfalso
    have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
    let φ' : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
    let h' : ({i : Λ // i ∉ S} ⊕ Λa) → V := fun o => h (o.map Subtype.val id)
    let α' : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) V :=
      fun o => α (o.map Subtype.val id)
    have hlin' : ∀ o w, ggLin (p := p) ι (φ' o) w = w - α' o w • h' o := fun o w => hlin _ w
    have hdiag' : ∀ o, α' o (h' o) = 2 := by
      intro o
      change α (o.map Subtype.val id) (h (o.map Subtype.val id)) = 2
      rw [hpairK o o, hCK.1 o]
      norm_num
    have hrange : Set.range φ' =
        Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      ext z
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact ⟨Sum.inl j, rfl⟩
        · exact ⟨Sum.inr a, rfl⟩
    have hgen' : ggAutomizer L Bs = Subgroup.closure (Set.range φ') := by
      rw [hclosK, hrange]
    have hdim := ggResTBFix_finrank_le_card_add_one hTBF hH ι φ' h' α' hlin' hdiag' hgen'
    have hcardS : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
      have h := Fintype.card_subtype_compl (α := Λ) (p := fun i => i ∈ S)
      rw [Fintype.card_coe] at h
      exact h
    have hSle : S.card ≤ Fintype.card Λ := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    have hΛa1' : Fintype.card Λa = 1 := by
      rw [← Nat.card_eq_fintype_card, hΛa1]
    have hcardι : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) + 1 = Fintype.card Λ := by
      rw [Fintype.card_sum, hcardS, hΛa1', hS]
      omega
    have hdimΛ : Module.finrank (ZMod p) V ≤ Fintype.card Λ := by omega
    have hwt := ggWeylTypeData_of_isWeylMatrix hML
    have hcardML : Nat.card ML.Group = Nat.card ↥(ggAutomizer K Bs) :=
      Nat.card_congr fL.toEquiv
    rw [hcardML] at hwt
    have hleBs := hrank (Fintype.card Λ) (Nat.card ↥(Subgroup.center ML.Group)) hwt
    have hBsV : Nat.card ↥Bs = Nat.card V := by
      have h1 : Nat.card ↥Bs = Nat.card (Additive ↥Bs) :=
        (Nat.card_congr Additive.toMul).symm
      exact h1.trans (Nat.card_congr ι.toEquiv)
    have hVpow : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      let : Module.Finite (ZMod p) V := Module.Finite.of_finite
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod p) (V := V))
    have hle : p ^ (Fintype.card Λ + 1) ≤ p ^ Fintype.card Λ := by
      calc p ^ (Fintype.card Λ + 1) ≤ Nat.card ↥Bs := hleBs
        _ = Nat.card V := hBsV
        _ = p ^ Module.finrank (ZMod p) V := hVpow
        _ ≤ p ^ Fintype.card Λ :=
            Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdimΛ
    exact absurd hle (Nat.not_le.mpr
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self _)))


theorem GGResHyp.card_Bs_six_of_K_only_E6
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    Nat.card Bs = 3 ^ 6 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hE6 : GGIsTypeE6 ML := htyp
  obtain ⟨e6, _⟩ := hE6
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using (Fintype.card_congr e6).symm
  have hΛa1 : Nat.card Λa = 1 := by
    by_contra hne
    have h2 : 2 ≤ Nat.card Λa := by omega
    have hrev := ggResLeviDatumCard_reverse_of_witness (p := 3) (Bs := Bs) (L := K) (J := J)
      (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK)
      (V := V) (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega)
      hML hCL hMK hCK hlin hrefl hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
    have hc : Nat.card Λa = 2 ∨ Nat.card Λa = 3 := by omega
    rcases hc with hc | hc
    · have h2' : GGResLeviDatumCard 2 3 Bs L J K ggSelAny ggTypAny := by
        simpa only [hc] using hrev
      exact hno (Or.inl h2')
    · have h3' : GGResLeviDatumCard 3 3 Bs L J K ggSelAny ggTypAny := by
        simpa only [hc] using hrev
      exact hno (Or.inr h3')
  let IdxL : Type := {i : Λ // i ∉ S} ⊕ Λa
  let φL : IdxL → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  let hLf : IdxL → V := fun o => h (o.map Subtype.val id)
  let αL : IdxL → Module.Dual (ZMod 3) V := fun o => α (o.map Subtype.val id)
  have hlinL : ∀ o w, ggLin (p := 3) ι (φL o) w = w - αL o w • hLf o :=
    fun o w => hlin _ w
  have hdiagL : ∀ o, αL o (hLf o) = 2 := by
    intro o
    change α (o.map Subtype.val id) (h (o.map Subtype.val id)) = 2
    rw [hpairK o o, hCK.1 o]
    norm_num
  have hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    have hrange : Set.range φL =
        Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      ext z
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact ⟨Sum.inl j, rfl⟩
        · exact ⟨Sum.inr a, rfl⟩
    rw [hclosK, hrange]
  have hdim_le : Module.finrank (ZMod 3) V ≤ 6 := by
    have h := ggResTBFix_finrank_le_card_add_one hTBF hH ι φL hLf αL hlinL hdiagL hgenL
    have hcardS : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
      have hc := Fintype.card_subtype_compl (α := Λ) (p := fun i => i ∈ S)
      rw [Fintype.card_coe] at hc
      exact hc
    have hΛaF : Fintype.card Λa = 1 := by
      rw [← Nat.card_eq_fintype_card, hΛa1]
    have hcardIdx : Fintype.card IdxL = 5 := by
      change Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5
      rw [Fintype.card_sum, hcardS, hΛaF, hS, hcardΛ]
    omega
  have hdim_ge : 6 ≤ Module.finrank (ZMod 3) V := by
    have haxis := ggResK_rank_core_add_one hH
      (C := CL) (φ := fun i => φ (Sum.inl i)) (h := fun i => h (Sum.inl i))
      (α := fun i => α (Sum.inl i)) (fun i w => hlin (Sum.inl i) w) hpair hCL.1 hclosL
    have hrank := ggIntCartan_card_le_rank_add_one hML hCL 3 (by norm_num)
    omega
  have hdim : Module.finrank (ZMod 3) V = 6 := le_antisymm hdim_le hdim_ge
  have hcardV : Nat.card V = 3 ^ 6 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod] at h
    rw [h, hdim]
  have hBsV : Nat.card ↥Bs = Nat.card V := card_eq_of_ggLin ι
  rw [hBsV, hcardV]


theorem ggResK_fixedLine_of_twE6_card_six
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hp : p = 3)
    (hcard : Nat.card Bs = 3 ^ 6)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y := by
  classical
  subst hp
  have hNbr : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hyB : y ∈ B := hNbr.1.2.1
  have hy1 : y ≠ 1 := hNbr.1.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hNbr.1.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hyfix : ∀ φ ∈ ggAutomizer K Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
    ggResI_automizer_fix hyBs hKy
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, ha1, ha3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfull, hother, hgenK, hgenL, hc, hgenJ⟩ := hD
  letI := i1
  letI := i2
  letI := i5
  letI := i6
  letI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨e, he⟩ := htyp
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using Fintype.card_congr e.symm
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcard
  have hdimV : Module.finrank (ZMod 3) V = 6 := by
    have hv := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hv
    exact Nat.pow_right_injective (by omega : 2 ≤ 3) hv.symm
  have hML' : GGIsWeylMatrix ML := Or.inr (Or.inl ⟨e, he⟩)
  have hdiag : ∀ i : Λ, α (Sum.inl i) (h (Sum.inl i)) = 2 := by
    intro i
    rw [hpair i i, hCL.1 i]
    norm_num
  let F : V →ₗ[ZMod 3] (Λ → ZMod 3) := LinearMap.pi (fun i : Λ => α (Sum.inl i))
  have hrank5 : 5 ≤ Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) := by
    have h := ggIntCartan_card_le_rank_add_one (p := 3) hML' hCL (by norm_num : (3 : ℕ) ≠ 2)
    omega
  have hcol : ∀ j : Λ, (CL.map (Int.castRingHom (ZMod 3))).col j = F (h (Sum.inl j)) := by
    intro j
    funext i
    simpa [Matrix.col, F] using (hpair i j).symm
  have hspan_le : Submodule.span (ZMod 3)
      (Set.range (CL.map (Int.castRingHom (ZMod 3))).col) ≤ F.range := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_range.mpr ⟨h (Sum.inl j), (hcol j).symm⟩
  have hrank_le : Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) ≤
      Module.finrank (ZMod 3) F.range := by
    rw [Matrix.rank_eq_finrank_span_cols (CL.map (Int.castRingHom (ZMod 3)))]
    exact Submodule.finrank_mono hspan_le
  have hkerdim : Module.finrank (ZMod 3) (LinearMap.ker F) ≤ 1 := by
    have hrn := F.finrank_range_add_finrank_ker
    omega
  have hfixeq : ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) = LinearMap.ker F := by
    exact (ggResKRevAux_pi_ker ι (fun i : Λ => φ (Sum.inl i))
      (fun i : Λ => h (Sum.inl i)) (fun i : Λ => α (Sum.inl i))
      (fun i w => hlin (Sum.inl i) w) hdiag (by norm_num) (ggAutomizer K Bs) hgenK).symm
  have hyW : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ∈
      ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    exact (ggLin_fix_iff ι ψ (⟨y, hyBs⟩ : ↥Bs)).mp (hyfix ψ hψ)
  have hyv_ne : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y, hyBs⟩ : ↥Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨y, hyBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hy1 (congrArg Subtype.val h2)
  have hle_span : Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} ≤
      ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) :=
    Submodule.span_le.mpr (by
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact hyW)
  have hWle : Module.finrank (ZMod 3) (ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs)) ≤ 1 := by
    rw [hfixeq]
    exact hkerdim
  have hWeq : ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) =
      Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    apply Eq.symm
    refine Submodule.eq_of_le_of_finrank_eq hle_span ?_
    rw [finrank_span_singleton hyv_ne]
    have hge : 1 ≤
        Module.finrank (ZMod 3) (ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs)) := by
      have hmono := Submodule.finrank_mono hle_span
      rwa [finrank_span_singleton hyv_ne] at hmono
    omega
  intro b hb
  have hbW : ι (Additive.ofMul b) ∈ ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    exact (ggLin_fix_iff ι ψ b).mp (hb ψ hψ)
  have hmem : ι (Additive.ofMul b) ∈
      Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    rw [← hWeq]
    exact hbW
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcval : c.val • ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) =
      ι (Additive.ofMul b) := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3) c.val, ZMod.natCast_zmod_val]
    exact hc
  have hpow : (⟨y, hyBs⟩ : ↥Bs) ^ c.val = b := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, show ι (c.val • Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) =
        c.val • ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) from
      ι.toAddMonoidHom.map_nsmul c.val (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))]
    exact hcval
  exact Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), by
    rw [zpow_natCast]
    exact congrArg Subtype.val hpow⟩

theorem ggResExact3_K_reverse_or_exact2_singular {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      (GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
        (GGResLeviDatumCard 3 p Bs K J L ggSelAny (ggTypLADvd p) ∨
          (p = 3 ∧ GGResLeviDatumCard 3 p Bs K J L ggSelAny ggTypLE6))) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, _htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumCard 3 p Bs K J L ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  have hrev := ggResLeviDatumCard_reverse_of_witness (p := p) (Bs := Bs) (L := K) (J := J)
    (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK) (V := V)
    (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega) hML hCL hMK hCK hlin hrefl
    hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
  have hrange : Set.range (fun o : {i : Λ // i ∉ S} ⊕ Λa =>
      φ (o.map Subtype.val id)) =
      Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hgenL : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
    rw [hclosK, hrange]
  have hsqueeze := ggResK_exactThree_added_three_or_two_singular_of_tbFix
    hTBF hH ι φ h α hS hΛa3 hML hCL hlin hpair hclosL hgenL
  rcases hsqueeze with ha3 | ⟨ha2, _hrank, _hdim, hsing⟩
  · exact Or.inl (by rwa [ha3] at hrev)
  · right
    refine ⟨by rwa [ha2] at hrev, ?_⟩
    rcases hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
    · exact Or.inl (pack (ggTypLADvd p) ⟨hA, by simpa only [Nat.card_eq_fintype_card] using hpd⟩)
    · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩



theorem GGResHyp.not_exactThree_either_of_sideDatum_L_of_tbFix
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hSide : GGResSideDatum p Bs L J) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  have hNoL3 : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny :=
    fun h3 => not_ggResSideDatum_of_ggResLeviDatumCard_of_two_le hSide (by omega : 2 ≤ 3) h3
  rintro (hL3 | hK3)
  · exact hNoL3 hL3
  · rcases ggResExact3_K_reverse_or_exact2_singular hTBF hH hK3 with hL3 | ⟨hL2, _⟩
    · exact hNoL3 hL3
    · exact not_ggResSideDatum_of_ggResLeviDatumExact2 hSide hL2


end CFSG.StandardType
