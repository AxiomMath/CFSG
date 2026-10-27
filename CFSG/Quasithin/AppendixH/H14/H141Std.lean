module

public import CFSG.Quasithin.AppendixH.H14.H142StdDefs
public import CFSG.Quasithin.AppendixH.Common.Sextet
public import CFSG.Quasithin.Background.H158TNF

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin.H158T
open CFSG.ASVolI.AppH CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem gimg_lt (j : ℕ) (x : Fin 24) : gimg j x < 24 := by
  by_cases hj : j < 4
  · interval_cases j <;> fin_cases x <;> decide
  · have hlen : genLs.length ≤ j := by
      simp only [genLs, List.length_cons, List.length_nil]
      omega
    have hget : genLs.getD j [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    unfold gimg
    rw [hget]
    simp

@[expose] def gimgF (j : ℕ) (x : Fin 24) : Fin 24 := ⟨gimg j x, gimg_lt j x⟩

@[expose] def gimgSet (j : ℕ) (X : Finset (Fin 24)) : Finset (Fin 24) := X.image (gimgF j)

theorem gimgSet_eq_smul (σ : ℕ → Equiv.Perm (Fin 24))
    (hσ : ∀ j ∈ [0, 1, 2, 3], ∀ i : Fin 24, ((σ j i : Fin 24) : ℕ) = gimg j i)
    (j : ℕ) (hj : j ∈ [0, 1, 2, 3]) (X : Finset (Fin 24)) :
    gimgSet j X = σ j • X := by
  ext y
  rw [gimgSet, Finset.mem_image, Finset.mem_smul_finset]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [Equiv.Perm.smul_def]
    apply Fin.ext
    exact hσ j hj x
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    rw [Equiv.Perm.smul_def] at hxy
    rw [← hxy]
    apply Fin.ext
    exact (hσ j hj x).symm

theorem tets_check_sub : ∀ X : ↥(Finset.powersetCard 4 o2F),
    (∀ j ∈ [0, 1, 2, 3], gimgSet j X.1 = X.1 ∨ gimgSet j X.1 = o2F \ X.1) →
    X.1 = stdB ∨ X.1 = stdB' := by
  decide +kernel

theorem tets_check : ∀ X ∈ Finset.powersetCard 4 o2F,
    (∀ j ∈ [0, 1, 2, 3], gimgSet j X = X ∨ gimgSet j X = o2F \ X) →
    X = stdB ∨ X = stdB' := by
  intro X hX h
  exact tets_check_sub ⟨X, hX⟩ h

theorem arr_getElem!_eq' (a : Array ℕ) (i : ℕ) : a[i]! = a.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem coe_phi24 (p : T24s2.Elem) :
    ((phi24 p : ↥AutPerm) : S24) = T24s2.perm p := rfl

theorem gen_perm_exists' (j : ℕ) (hj : j ∈ [0, 1, 2, 3]) :
    ∃ p : T24s2.Elem, ∀ i : Fin 24, ((T24s2.perm p i : Fin 24) : ℕ) = gimg j i := by
  have hg : ∃ g ∈ genList, g.toList = genLs.getD j [] := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨genList.getD 0 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 1 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 2 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 3 #[], by simp [genList], rfl⟩
  obtain ⟨g, hgm, hgl⟩ := hg
  obtain ⟨k, hk, hgk⟩ := Array.mem_iff_getElem.1 (T24s2_gen_mem hgm)
  have hkn : k < T24s2.n := by rw [← T24s2.size_elems]; exact hk
  refine ⟨⟨k, hkn⟩, fun i => ?_⟩
  have harr : T24s2.arr ⟨k, hkn⟩ = g := by
    unfold PT.arr
    rw [getElem!_pos _ k hk]
    exact hgk
  rw [PT.perm_val, harr, arr_getElem!_eq', hgl]
  rfl

theorem gens_choice' :
    ∃ σ : ℕ → Equiv.Perm (Fin 24), ∃ p : ℕ → T24s2.Elem,
      ∀ j ∈ [0, 1, 2, 3], σ j = T24s2.perm (p j) ∧
        ∀ i : Fin 24, ((σ j i : Fin 24) : ℕ) = gimg j i := by
  have key : ∀ j : ℕ, ∃ σ : Equiv.Perm (Fin 24), ∃ p : T24s2.Elem,
      j ∈ [0, 1, 2, 3] → σ = T24s2.perm p ∧
        ∀ i : Fin 24, ((σ i : Fin 24) : ℕ) = gimg j i := by
    intro j
    by_cases hj : j ∈ [0, 1, 2, 3]
    · obtain ⟨p, hp⟩ := gen_perm_exists' j hj
      exact ⟨T24s2.perm p, p, fun _ => ⟨rfl, hp⟩⟩
    · exact ⟨1, 1, fun h => absurd h hj⟩
  choose σ p hσ using key
  exact ⟨σ, p, fun j hj => hσ j hj⟩

theorem exists_conj_sylow'
    {T : Subgroup (Equiv.Perm (Fin 24))} (hT : CFSG.Quasithin.IsSylowIn 2 T AutPerm) :
    ∃ h : Equiv.Perm (Fin 24), h ∈ AutPerm ∧ ∀ p : T24s2.Elem, h⁻¹ * T24s2.perm p * h ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := card_sylow_two hT
  have hH : IsPGroup 2 ↥(qSub : Subgroup ↥AutPerm) := IsPGroup.of_card (n := 10) card_qSub
  obtain ⟨g, hg⟩ :=
    exists_conj_le_range (T.subgroupOf AutPerm).subtype Subtype.val_injective hsyl hH
  refine ⟨((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)), (g⁻¹).2, ?_⟩
  intro p
  have hy : phi24 p ∈ (qSub : Subgroup ↥AutPerm) := ⟨p, rfl⟩
  have h1 := hg _ hy
  rw [Subgroup.range_subtype, Subgroup.mem_subgroupOf] at h1
  have e1 : (((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)))⁻¹ = (g : Equiv.Perm (Fin 24)) := by
    rw [← Subgroup.coe_inv, inv_inv]
  have e2 : (g : Equiv.Perm (Fin 24)) * T24s2.perm p *
      ((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) =
      ((g * phi24 p * g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [e1, e2]
  exact h1

theorem eq_labTrio_of_inv (σ : ℕ → Equiv.Perm (Fin 24))
    (hσ : ∀ j ∈ [0, 1, 2, 3], ∀ i : Fin 24, ((σ j i : Fin 24) : ℕ) = gimg j i)
    (Tr' : Finset (Finset (Fin 24))) (hcard : Tr'.card = 3)
    (hblk : ∀ O ∈ Tr', O.card = 8)
    (hdisj : ∀ O ∈ Tr', ∀ O' ∈ Tr', O ≠ O' → Disjoint O O')
    (hcov : ∀ x : Fin 24, ∃ O ∈ Tr', x ∈ O)
    (hmem : o2F ∈ Tr')
    (hfix : ∀ j ∈ [0, 1, 2, 3], σ j • Tr' = Tr')
    (hfixo2 : ∀ j ∈ [0, 1, 2, 3], σ j • o2F = o2F) :
    Tr' = labTrio := by
  have hcardE : (Tr'.erase o2F).card = 2 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  obtain ⟨A, B, hAB, hE⟩ := Finset.card_eq_two.1 hcardE
  have hAmem : A ∈ Tr'.erase o2F := by rw [hE]; simp
  have hBmem : B ∈ Tr'.erase o2F := by rw [hE]; simp
  obtain ⟨hAne, hAT⟩ := Finset.mem_erase.1 hAmem
  obtain ⟨hBne, hBT⟩ := Finset.mem_erase.1 hBmem
  have hTr'eq : Tr' = {o2F, A, B} := by
    have := Finset.insert_erase hmem
    rw [hE] at this
    exact this.symm
  have hABcov : ∀ x : Fin 24, x ∈ o2F ∨ x ∈ A ∨ x ∈ B := by
    intro x
    obtain ⟨O', hO'T, hxO'⟩ := hcov x
    rw [hTr'eq] at hO'T
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO'T
    rcases hO'T with rfl | rfl | rfl
    · exact Or.inl hxO'
    · exact Or.inr (Or.inl hxO')
    · exact Or.inr (Or.inr hxO')
  have hABdisj : Disjoint A B := hdisj A hAT B hBT hAB
  have hAo2 : Disjoint A o2F := hdisj A hAT o2F hmem hAne
  have hBo2 : Disjoint B o2F := hdisj B hBT o2F hmem hBne
  have hAcard : A.card = 8 := hblk A hAT
  have hBcard : B.card = 8 := hblk B hBT
  have hmapX : ∀ j ∈ [0, 1, 2, 3], ∀ X ∈ Tr', X ≠ o2F →
      (σ j • X = A ∨ σ j • X = B) := by
    intro j hj X hX hXne
    have h1 : σ j • X ∈ Tr' := by
      have hmem' : σ j • X ∈ σ j • Tr' := Finset.mem_smul_finset.2 ⟨X, hX, rfl⟩
      rwa [hfix j hj] at hmem'
    have h2 : σ j • X ≠ o2F := by
      intro he
      apply hXne
      have e2 : σ j • X = σ j • o2F := by rw [he, hfixo2 j hj]
      have e3 := congrArg (fun Y : Finset (Fin 24) => (σ j)⁻¹ • Y) e2
      simp only [inv_smul_smul] at e3
      exact e3
    have := Finset.mem_erase.2 ⟨h2, h1⟩
    rw [hE] at this
    simpa using this
  have hσA : ∀ j ∈ [0, 1, 2, 3], (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ A) ∨
      (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ B) := by
    intro j hj
    rcases hmapX j hj A hAT hAne with e | e
    · left
      intro x
      have := mem_smul_perm_iff (σ j) A x
      rw [e] at this
      exact this.symm
    · right
      intro x
      have := mem_smul_perm_iff (σ j) A x
      rw [e] at this
      exact this.symm
  have hσB : ∀ j ∈ [0, 1, 2, 3], (∀ x : Fin 24, x ∈ B ↔ σ j x ∈ B) ∨
      (∀ x : Fin 24, x ∈ B ↔ σ j x ∈ A) := by
    intro j hj
    rcases hmapX j hj B hBT hBne with e | e
    · right
      intro x
      have := mem_smul_perm_iff (σ j) B x
      rw [e] at this
      exact this.symm
    · left
      intro x
      have := mem_smul_perm_iff (σ j) B x
      rw [e] at this
      exact this.symm
  have hc16 : ∀ x : Fin 24, x ∈ c16F ↔ x ∉ o2F := fun x => by simp [c16F]
  have hcon : ∀ x : Fin 24, (x ∈ A ∨ x ∈ B) ↔ x ∈ c16F := by
    intro x
    rw [hc16]
    constructor
    · rintro (hx | hx) hx2
      · exact Finset.disjoint_left.1 hAo2 hx hx2
      · exact Finset.disjoint_left.1 hBo2 hx hx2
    · intro hx
      rcases hABcov x with h2 | h2 | h2
      · exact absurd h2 hx
      · exact Or.inl h2
      · exact Or.inr h2
  have hzero : (0 : Fin 24) ∉ o2F := by
    rw [mem_o2F]
    decide
  have hANe : ∃ x : Fin 24, x ∈ A := Finset.card_pos.1 (by rw [hAcard]; norm_num)
  have hBNe : ∃ x : Fin 24, x ∈ B := Finset.card_pos.1 (by rw [hBcard]; norm_num)
  have hlab : Tr' = labTrio := by
    have hpart : (A = o0F ∧ B = o1F) ∨ (A = o1F ∧ B = o0F) := by
      by_cases h0A : (0 : Fin 24) ∈ A
      · left
        exact part_gen σ (fun j hj x => hσ j hj x) A B h0A hcon
          (fun x hx hxB => Finset.disjoint_left.1 hABdisj hx hxB) hBNe hσA
      · right
        have h0B : (0 : Fin 24) ∈ B := by
          rcases hABcov 0 with h2 | h2 | h2
          · exact absurd h2 hzero
          · exact absurd h2 h0A
          · exact h2
        have hres := part_gen σ (fun j hj x => hσ j hj x) B A h0B
          (fun x => by rw [or_comm]; exact hcon x)
          (fun x hx hxA => Finset.disjoint_left.1 hABdisj hxA hx) hANe hσB
        exact ⟨hres.2, hres.1⟩
    rw [hTr'eq]
    rcases hpart with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · unfold labTrio
      ext X
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · unfold labTrio
      ext X
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  exact hlab

theorem exists_conj_qPerms
    {A : Subgroup S24} (hA : A ≤ M24g) (hp : IsPGroup 2 A) :
    ∃ h ∈ M24g, ∀ a ∈ A, ∃ p : T24s2.Elem, h * a * h⁻¹ = T24s2.perm p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : Nat.card T24s2.Elem = 2 ^ (Nat.card ↥M24g).factorization 2 := card_T24s2
  have hH : IsPGroup 2 ↥(A.subgroupOf M24g) := hp.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_le_range (φ := (phi24 : T24s2.Elem →* ↥M24g))
    phi24_injective hsyl (H := A.subgroupOf M24g) hH
  refine ⟨(g : S24), g.2, ?_⟩
  intro a ha
  obtain ⟨p, hp_eq⟩ := hg ⟨a, hA ha⟩ ha
  refine ⟨p, ?_⟩
  have hcoe := congrArg (fun z : ↥M24g => (z : S24)) hp_eq
  have h1 : ((phi24 p : ↥M24g) : S24) = (g : S24) * a * (g : S24)⁻¹ := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcoe
  rw [coe_phi24] at h1
  exact h1.symm

theorem exists_std141
    {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {T₀ : Subgroup S24}
    (hTr : IsTrio Tr) (hS : IsSextet S) (hOT : O ∈ Tr)
    (hTu : ∀ P ∈ Tr, ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ P = B₁ ∪ B₂)
    (hT : CFSG.Quasithin.IsSylowIn 2 T₀ M24g)
    (hTO : ∀ g ∈ T₀, g • O = O) (hTTr : ∀ g ∈ T₀, g • Tr = Tr) (hTS : ∀ g ∈ T₀, g • S = S) :
    ∃ c ∈ M24g, (∀ t ∈ T₀, ∃ p : T24s2.Elem, c * t * c⁻¹ = T24s2.perm p) ∧ c • O = o2F ∧
      c • Tr = labTrio ∧ c • S = stdS := by
  obtain ⟨h, hhA, hconj⟩ := exists_conj_sylow' (show CFSG.Quasithin.IsSylowIn 2 T₀ AutPerm from hT)
  obtain ⟨σ, p, hσ⟩ := gens_choice'
  have ha : ∀ t ∈ T₀, ∃ q : T24s2.Elem, h * t * h⁻¹ = T24s2.perm q := by
    let f : T24s2.Elem → ↥T₀ := fun q => ⟨h⁻¹ * T24s2.perm q * h, hconj q⟩
    have hf_inj : Function.Injective f := by
      intro q₁ q₂ heq
      have h1 : h⁻¹ * T24s2.perm q₁ * h = h⁻¹ * T24s2.perm q₂ * h := by
        have := congrArg (fun z : ↥T₀ => (z : S24)) heq
        simpa [f] using this
      exact T24s2.perm_injective (mul_left_cancel (mul_right_cancel h1))
    have hcardT : Nat.card ↥T₀ = 2 ^ 10 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show T₀ ≤ AutPerm from hT.1)).toEquiv,
        card_sylow_two hT, factor_AutPerm]
    have hcardE : Nat.card T24s2.Elem = 2 ^ 10 := by
      rw [card_T24s2, factor_AutPerm]
    have hbij := hf_inj.bijective_of_nat_card_le
      (le_of_eq (by rw [hcardT, hcardE]))
    intro t ht
    obtain ⟨q, hq⟩ := hbij.2 ⟨t, ht⟩
    refine ⟨q, ?_⟩
    have h1 : h⁻¹ * T24s2.perm q * h = t := by
      have := congrArg (fun z : ↥T₀ => (z : S24)) hq
      simpa [f] using this
    rw [← h1]
    group
  have hfixO : ∀ j ∈ [0, 1, 2, 3], σ j • (h • O) = h • O := by
    intro j hj
    have hyT : h⁻¹ * σ j * h ∈ T₀ := by
      rw [(hσ j hj).1]
      exact hconj (p j)
    calc σ j • (h • O) = h • ((h⁻¹ * σ j * h) • O) := by
          rw [smul_smul, smul_smul, show h * (h⁻¹ * σ j * h) = σ j * h by group]
      _ = h • O := by rw [hTO _ hyT]
  have hO2 : h • O = o2F := by
    refine orbit_fin σ (fun j hj x => (hσ j hj).2 x) (h • O) ?_ ?_
    · rw [Finset.card_smul_finset]
      exact (hTr.2.1 O hOT).1
    · intro j hj x
      have e := mem_smul_perm_iff (σ j) (h • O) x
      rw [hfixO j hj] at e
      exact e
  have hfixo2 : ∀ j ∈ [0, 1, 2, 3], σ j • o2F = o2F := by
    intro j hj
    have := hfixO j hj
    rwa [hO2] at this
  have hmem : o2F ∈ h • Tr := by
    rw [← hO2]
    exact Finset.smul_mem_smul_finset hOT
  have hfixTr : ∀ j ∈ [0, 1, 2, 3], σ j • (h • Tr) = h • Tr := by
    intro j hj
    have hyT : h⁻¹ * σ j * h ∈ T₀ := by
      rw [(hσ j hj).1]
      exact hconj (p j)
    calc σ j • (h • Tr) = h • ((h⁻¹ * σ j * h) • Tr) := by
          rw [smul_smul, smul_smul, show h * (h⁻¹ * σ j * h) = σ j * h by group]
      _ = h • Tr := by rw [hTTr _ hyT]
  have hcard' : (h • Tr).card = 3 := by rw [Finset.card_smul_finset, hTr.1]
  have hblk' : ∀ O ∈ h • Tr, O.card = 8 := by
    intro O hO
    obtain ⟨O', hO', rfl⟩ := Finset.mem_smul_finset.1 hO
    rw [Finset.card_smul_finset]
    exact (hTr.2.1 O' hO').1
  have hdisj' : ∀ O ∈ h • Tr, ∀ O' ∈ h • Tr, O ≠ O' → Disjoint O O' := by
    intro O hO O' hO' hne
    obtain ⟨X, hX, rfl⟩ := Finset.mem_smul_finset.1 hO
    obtain ⟨X', hX', rfl⟩ := Finset.mem_smul_finset.1 hO'
    have hXX : X ≠ X' := fun e => hne (by rw [e])
    rw [smul_finset_eq_map, smul_finset_eq_map]
    exact (Finset.disjoint_map _).2 (hTr.2.2.1 X hX X' hX' hXX)
  have hcov' : ∀ x : Fin 24, ∃ O ∈ h • Tr, x ∈ O := by
    intro x
    have hx : h⁻¹ x ∈ Tr.biUnion id := by
      rw [hTr.2.2.2]
      exact Finset.mem_univ _
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    exact ⟨h • O, Finset.mem_smul_finset.2 ⟨O, hO, rfl⟩,
      Finset.mem_smul_finset.2 ⟨h⁻¹ x, hxO, by simp⟩⟩
  have hTr_lab : h • Tr = labTrio :=
    eq_labTrio_of_inv σ (fun j hj x => (hσ j hj).2 x) (h • Tr) hcard' hblk' hdisj' hcov' hmem
      hfixTr hfixo2
  have hfixS : ∀ j ∈ [0, 1, 2, 3], σ j • (h • S) = h • S := by
    intro j hj
    have hyT : h⁻¹ * σ j * h ∈ T₀ := by
      rw [(hσ j hj).1]
      exact hconj (p j)
    calc σ j • (h • S) = h • ((h⁻¹ * σ j * h) • S) := by
          rw [smul_smul, smul_smul, show h * (h⁻¹ * σ j * h) = σ j * h by group]
      _ = h • S := by rw [hTS _ hyT]
  have hSsext : IsSextet (h • S) := isSextet_smul hhA hS
  obtain ⟨B₁, hB₁, B₂, hB₂, hB₁B₂, hOU⟩ := hTu O hOT
  have hXmem : h • B₁ ∈ h • S := Finset.smul_mem_smul_finset hB₁
  have hYmem : h • B₂ ∈ h • S := Finset.smul_mem_smul_finset hB₂
  have hXYne : h • B₁ ≠ h • B₂ := fun hh => hB₁B₂ (smul_left_cancel h hh)
  have hXYunion : (h • B₁) ∪ (h • B₂) = o2F := by
    rw [← Finset.smul_finset_union, ← hOU, hO2]
  have hXYdisj : Disjoint (h • B₁) (h • B₂) := by
    rw [smul_finset_eq_map, smul_finset_eq_map]
    exact (Finset.disjoint_map _).2 (hS.2.2.1 B₁ hB₁ B₂ hB₂ hB₁B₂)
  have hYeq : h • B₂ = o2F \ (h • B₁) := by
    rw [← Finset.union_sdiff_cancel_left hXYdisj, hXYunion]
  have hXsub : h • B₁ ⊆ o2F := fun z hz => by
    rw [← hXYunion]
    exact Finset.mem_union_left _ hz
  have hZeq : ∀ j ∈ [0, 1, 2, 3], σ j • (h • B₁) = h • B₁ ∨
      σ j • (h • B₁) = h • B₂ := by
    intro j hj
    have hZmem : σ j • (h • B₁) ∈ h • S := by
      have hm : σ j • (h • B₁) ∈ σ j • (h • S) :=
        Finset.mem_smul_finset.2 ⟨h • B₁, hXmem, rfl⟩
      rwa [hfixS j hj] at hm
    by_cases hZX : σ j • (h • B₁) = h • B₁
    · exact Or.inl hZX
    · right
      by_contra hZY
      have hZcard : (σ j • (h • B₁)).card = 4 := hSsext.2.1 _ hZmem
      obtain ⟨z, hzZ⟩ := Finset.card_pos.1 (by rw [hZcard]; norm_num)
      have hZsub : σ j • (h • B₁) ⊆ o2F := by
        intro w hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hw
        have hx2 : x ∈ o2F := hXsub hx
        have hx3 : σ j • x ∈ σ j • o2F := Finset.smul_mem_smul_finset hx2
        rwa [hfixo2 j hj] at hx3
      have hzXY : z ∈ (h • B₁) ∪ (h • B₂) := by
        rw [hXYunion]
        exact hZsub hzZ
      have hdX : Disjoint (σ j • (h • B₁)) (h • B₁) :=
        hSsext.2.2.1 _ hZmem _ hXmem (fun heq => hZX heq)
      have hdY : Disjoint (σ j • (h • B₁)) (h • B₂) :=
        hSsext.2.2.1 _ hZmem _ hYmem hZY
      rcases Finset.mem_union.1 hzXY with hz | hz
      · exact (Finset.disjoint_left.1 hdX hzZ) hz
      · exact (Finset.disjoint_left.1 hdY hzZ) hz
  have hcheck : ∀ j ∈ [0, 1, 2, 3], gimgSet j (h • B₁) = h • B₁ ∨
      gimgSet j (h • B₁) = o2F \ (h • B₁) := by
    intro j hj
    have hgj : gimgSet j (h • B₁) = σ j • (h • B₁) :=
      gimgSet_eq_smul σ (fun j hj x => (hσ j hj).2 x) j hj _
    rcases hZeq j hj with hz | hz
    · left
      rw [hgj, hz]
    · right
      rw [hgj, hz, hYeq]
  have hXpow : h • B₁ ∈ Finset.powersetCard 4 o2F := by
    rw [Finset.mem_powersetCard]
    exact ⟨hXsub, by rw [Finset.card_smul_finset, hS.2.1 B₁ hB₁]⟩
  have hS_std : h • S = stdS := by
    rcases tets_check (h • B₁) hXpow hcheck with hstd | hstd
    · have hstdB_mem : stdB ∈ h • S := hstd ▸ hXmem
      exact (sextet_eq_of_mem isSextet_stdS hSsext (by decide) hstdB_mem).symm
    · have hstdB'_mem : stdB' ∈ h • S := hstd ▸ hXmem
      exact (sextet_eq_of_mem isSextet_stdS hSsext (by decide) hstdB'_mem).symm
  exact ⟨h, hhA, ha, hO2, hTr_lab, hS_std⟩

end CFSG.Quasithin.AppendixH.H14
