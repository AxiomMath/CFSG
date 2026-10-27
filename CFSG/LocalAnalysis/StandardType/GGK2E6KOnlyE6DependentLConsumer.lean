module

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6DependentD5Span
public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6FrameK

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIsWeylMatrix_card_five
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (hcard : Fintype.card ι = 5) :
    (∃ e : Fin 5 ≃ ι, M = (CoxeterMatrix.A 5).reindex e) ∨
      (∃ e : Fin 5 ≃ ι, M = (CoxeterMatrix.B 5).reindex e) ∨
      (∃ e : Fin 5 ≃ ι, M = (ggCoxeterMatrixD 5).reindex e) := by
  rcases hM with ⟨n, e, -, hcase⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · have hn : n = 5 := by
      have hc : Fintype.card (Fin n) = Fintype.card ι := Fintype.card_congr e
      simpa [hcard] using hc
    subst n
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exact Or.inl ⟨e, hA⟩
    · exact Or.inr (Or.inl ⟨e, hB⟩)
    · exact Or.inr (Or.inr ⟨e, hD⟩)
  · exfalso
    have hc : Fintype.card (Fin 6) = Fintype.card ι := Fintype.card_congr e
    simpa [hcard] using hc
  · exfalso
    have hc : Fintype.card (Fin 7) = Fintype.card ι := Fintype.card_congr e
    simpa [hcard] using hc
  · exfalso
    have hc : Fintype.card (Fin 8) = Fintype.card ι := Fintype.card_congr e
    simpa [hcard] using hc
  · exfalso
    have hc : Fintype.card (Fin 4) = Fintype.card ι := Fintype.card_congr e
    simpa [hcard] using hc
  · exfalso
    have hc : Fintype.card (Fin 2) = Fintype.card ι := Fintype.card_congr e
    simpa [hcard] using hc

theorem ggResLeviDatumExact2_any_of_dep
    {G : Type} [Group G] [Finite G]
    {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6) :
    GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6 := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, trivial,
    hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩

theorem KOnlyE6_dependent_L_raw
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hS : S.card = 2) (hA1 : 1 ≤ Nat.card Λa) (hA3 : Nat.card Λa ≤ 3)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Λ) (hML : ML = (CoxeterMatrix.E₆).reindex e)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (fL : ML.Group ≃* ↥(ggAutomizer K Bs))
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (fK : MK.Group ≃* ↥(ggAutomizer L Bs))
    (hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer L Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hconn : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))) :
    Nat.card Λa = 1 ∧
      Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 ∧
      ((∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (CoxeterMatrix.A 5).reindex e5) ∨
        (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (CoxeterMatrix.B 5).reindex e5) ∨
        (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (ggCoxeterMatrixD 5).reindex e5)) ∧
      ∃ c : Fin 5 → ZMod 3,
        h (Sum.inl (e 0)) = ∑ i : Fin 5, c i • h (Sum.inl (e (d5Index i))) := by
  classical
  letI := Fact.mk (by norm_num : Nat.Prime 3)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hΛa1 : Nat.card Λa = 1 := by
    by_contra hne
    have h2 : 2 ≤ Nat.card Λa := by omega
    have hrev := ggResLeviDatumCard_reverse_of_witness (p := 3) (Bs := Bs)
      (L := K) (J := J) (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL)
      (MK := MK) (CK := CK) (V := V) (ι := ι) (φ := φ) (h := h) (α := α)
      (by omega) (by omega) hWML hCLL hWMK hCKK hlin hrefl hpair hpairK
      ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
    have hc : Nat.card Λa = 2 ∨ Nat.card Λa = 3 := by omega
    rcases hc with hc | hc
    · have h2' : GGResLeviDatumCard 2 3 Bs L J K ggSelAny ggTypAny := by
        simpa only [hc] using hrev
      exact hno (Or.inl h2')
    · have h3' : GGResLeviDatumCard 3 3 Bs L J K ggSelAny ggTypAny := by
        simpa only [hc] using hrev
      exact hno (Or.inr h3')
  have hcardΛ : Fintype.card Λ = 6 := by
    have hc : Fintype.card (Fin 6) = Fintype.card Λ := Fintype.card_congr e
    simpa using hc.symm
  have hcardSurv : Fintype.card {i : Λ // i ∉ S} = 4 := by
    have hc := Fintype.card_subtype_compl (α := Λ) (p := fun i => i ∈ S)
    rw [Fintype.card_coe] at hc
    omega
  have hcardL : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 := by
    rw [Fintype.card_sum, hcardSurv, ← Nat.card_eq_fintype_card, hΛa1]
  refine ⟨hΛa1, hcardL, ggIsWeylMatrix_card_five hWMK hcardL, ?_⟩
  have hSHat : LargeEvenSHat 3 B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hyK : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  let v : V := ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
  have hv : v ≠ 0 := by
    intro h0
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      exact ι.injective (by simpa [v] using h0)
    exact hy1 (by simpa using congrArg Subtype.val h1)
  have hpairE : ∀ i j : Fin 6,
      α (Sum.inl (e i)) (h (Sum.inl (e j))) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), ggIndep_cartan_of_reindexE6 e hCLL hML i j]
  have hker : ∀ i : Fin 6, α (Sum.inl (e i)) v = 0 := by
    intro i
    have hmem : φ (Sum.inl (e i)) ∈ ggAutomizer K Bs := by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfix := ggResI_automizer_fix hyBs hyK (φ (Sum.inl (e i))) hmem
    have hfixlin : ggLin (p := 3) ι (φ (Sum.inl (e i))) v = v := by
      dsimp only [v]
      exact (ggLin_fix_iff (p := 3) ι (φ (Sum.inl (e i))) ⟨y, hyBs⟩).mp hfix
    refine ggResI_alpha_eq_zero (by norm_num) (hlin (Sum.inl (e i))) ?_ hfixlin
    rw [hpair (e i) (e i), hCLL.1 (e i)]
    norm_num
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcardBs
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hv6 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hv6
    exact Nat.pow_right_injective (by omega : 2 ≤ 3) hv6.symm
  have hdepFin : ¬ LinearIndependent (ZMod 3) (fun i : Fin 6 => h (Sum.inl (e i))) := by
    intro hfin
    apply hsel
    simpa only [Function.comp_def] using (linearIndependent_equiv (e := e)).mp hfin
  exact e6_dependent_d5_span_reindex
    (h := fun i : Λ => h (Sum.inl i)) (α := fun i : Λ => α (Sum.inl i))
    e hpairE hv hker hdim hdepFin

theorem KOnlyE6_dependent_L_full
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
      (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
      (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
      (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
      (e : Fin 6 ≃ Λ),
      S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa = 1 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      GGIsTypeE6 ML ∧
      (∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection 3 (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3)) ∧
      (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3)) ∧
      (¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer K Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer L Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer L Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnectedS ML S ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∧
      ML = (CoxeterMatrix.E₆).reindex e ∧
      Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 ∧
      ((∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (CoxeterMatrix.A 5).reindex e5) ∨
        (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (CoxeterMatrix.B 5).reindex e5) ∨
        (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (ggCoxeterMatrixD 5).reindex e5)) ∧
      ∃ c : Fin 5 → ZMod 3,
        h (Sum.inl (e 0)) = ∑ i : Fin 5, c i • h (Sum.inl (e (d5Index i))) := by
  classical
  have hDany := ggResLeviDatumExact2_any_of_dep hD
  have hcardBs := hH.card_Bs_six_of_K_only_E6 hTBF hDany hno
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hMLW, hCLW, hMKW, hCKW, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩ := hD
  obtain ⟨e, heML⟩ := htyp
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hraw := KOnlyE6_dependent_L_raw hH hcardBs hno
    hS hA1 hA3 hMLW hCLW hMKW hCKW e heML hlin hrefl hpair hpairK
    fL hfL fK hfK hclosL hclosK hconn hclosJ hsel
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
    hS, hA1, hraw.1, hMLW, hCLW, hMKW, hCKW, ⟨e, heML⟩, hlin, hrefl, hpair, hpairK,
    hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hraw.2.1,
    hraw.2.2.1, hraw.2.2.2⟩

end CFSG.StandardType

end
