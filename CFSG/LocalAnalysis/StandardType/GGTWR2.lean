module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Count
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame
public import CFSG.LocalAnalysis.StandardType.GGTWR3
import CFSG.LocalAnalysis.StandardType.GGIntCartanDet
import CFSG.Mathlib.LinearAlgebra.Matrix.DetDualKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWR2_xdatumA_K
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labL => ggRowTwoNodeSmallJA q labJ labL ∧
      Nat.card ↥Bs ≠ q ^ (labL.rank + 1)) p J L)
    (hxL : x ∉ L) (hK : GGResTwoNodeSideDatum p Bs K J) :
    ∃ n : ℕ, GGResXDatumA p Bs K n := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  obtain ⟨labJ0, labX0, hJΛ0, hXΛ0, hJl0, hXl0, hrowJA0, hcard0⟩ := hrow
  have hrowA : GGResRowAt ggRowTwoNodeSmallJA p J L :=
    ⟨labJ0, labX0, hJΛ0, hXΛ0, hJl0, hXl0, hrowJA0⟩
  have hrow' := ggTWSmallA_row_narrow hp2 hrowA
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, _hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw)
      hH hrow' hxL
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  have h4X : 4 ≤ labX.rank := ggTWSmallA_rank_ge Fact.out hp2 hJΛ hJtag hrow2
  have hiso : GGLabelIso labX0 labX := hRig labX0 labX _ hXΛ0 hXΛ hXl0 hXl
  have hEq : labX0 = labX := ggTWR_iso_eq hiso hAtag h4X
  have hne : Nat.card ↥Bs ≠ p ^ N := by
    rw [hEq, hXrank] at hcard0
    exact hcard0
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hfixL := hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
    hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  have hle : Nat.card ↥Bs ≤ p ^ N :=
    ggLE3_card_le_of_fix (N := N) (by omega) hdatL hxp hfixL
  have hLd : GGResTwoNodeSideDatum p Bs L J :=
    (hJ2S G p B Bs x L D J y K hH).1 (l6a_xdatum_of_A hdatL) hrowA
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcardΛa, hWML, hIntL, hWMK, hIntK, hlin, hrefl, hpairL, hpairK, hfLex, hfKex,
    hclosL, hclosK, hdel, _hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hLd hK
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨ΛL, i1L, i2L, ML0, CL0, VL, i3L, i4L, ιL, φL0, hL0, αL0, eL, hMLeqL, hWML0,
    hIntL0, hlinL0, hreflL0, hpairL0, hfL0ex, _hclosL0⟩ := hdatL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL0, hfL0⟩ := hfL0ex
  have hN2 : 2 ≤ N - 1 := by omega
  obtain ⟨e, hMLeq⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 hN2 hBs (ggAutomizer L Bs)
      (Λ₁ := ΛL) (M₁ := ML0) eL hMLeqL hWML0 fL0 φL0 hfL0 hreflL0
      (Λ₂ := Λ) (M₂ := ML) hWML fL (fun i => φ (Sum.inl i)) (fun i => hfL i)
      (fun i => hrefl (Sum.inl i))
  let Λ' : Type := {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa
  let φ' : Λ' → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  let h' : Λ' → V := fun o => h (o.map Subtype.val id)
  let α' : Λ' → Module.Dual (ZMod p) V := fun o => α (o.map Subtype.val id)
  have hcardΛ : Fintype.card Λ = N - 1 := by
    rw [← Fintype.card_fin (N - 1), Fintype.card_congr e]
  have hcardΛaF : Fintype.card Λa = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardΛa
  have hcardSub : Fintype.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} = N - 3 := by
    rw [Fintype.card_of_subtype
      (Finset.univ.filter (fun i : Λ => i ≠ b₁ ∧ i ≠ b₂)) (by intro i; simp)]
    have hfilter : Finset.univ.filter (fun i : Λ => i ≠ b₁ ∧ i ≠ b₂) =
        (Finset.univ.erase b₁).erase b₂ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [hfilter]
    have h1 : b₂ ∈ Finset.univ.erase b₁ := Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ b₂⟩
    rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ b₁),
      Finset.card_univ]
    omega
  have hcardΛ' : Fintype.card Λ' = N - 1 := by
    change Fintype.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) = N - 1
    rw [Fintype.card_sum, hcardSub, hcardΛaF]
    omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at h
  have hcardV : Nat.card V = Nat.card ↥Bs := by
    rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
    exact (Nat.card_congr ι.toEquiv).symm
  have hpow_le : p ^ Module.finrank (ZMod p) V ≤ p ^ N := by
    rw [← hVcard, hcardV]; exact hle
  have hpow_ne : p ^ Module.finrank (ZMod p) V ≠ p ^ N := by
    rw [← hVcard, hcardV]; exact hne
  have hfinrank_le : Module.finrank (ZMod p) V ≤ N :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hpow_le
  have hfinrank_lt : Module.finrank (ZMod p) V < N := by
    rcases lt_or_eq_of_le hfinrank_le with hlt | heq
    · exact hlt
    · exfalso
      exact hpow_ne (by rw [heq])
  have hfinrank : Module.finrank (ZMod p) V ≤ Fintype.card Λ' := by
    rw [hcardΛ']; omega
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hfixy := ggRC_automizer_fixes_y hyBs hKy
  have hyV0' : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (by simpa using h0))
    exact hy1 (by simpa using Subtype.ext_iff.mp h1)
  let yV : V := ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
  have hyV0 : yV ≠ 0 := hyV0'
  have hαy : ∀ o : Λ', α' o yV = 0 := by
    intro o
    have hmemK : φ' o ∈ ggAutomizer K Bs := by
      rw [hclosK]
      apply Subgroup.subset_closure
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    have hfixo : φ' o ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := hfixy (φ' o) hmemK
    have hlin_fix : ggLin (p := p) ι (φ' o) yV = yV :=
      (ggLin_fix_iff (p := p) ι (φ' o) (⟨y, hyBs⟩ : ↥Bs)).mp hfixo
    have hsmul : α' o yV • h' o = 0 := by
      have h1 := hlin (o.map Subtype.val id) yV
      rw [hlin_fix] at h1
      exact sub_eq_self.mp h1.symm
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro hzero
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hdvd)
    have hpair_oo : α' o (h' o) = (2 : ZMod p) := by
      have hh := hpairK o o
      rw [hIntK.1 o] at hh
      simpa using hh
    have hh' : h' o ≠ 0 := by
      intro h0
      have hzero : α' o (h' o) = 0 := by rw [h0, map_zero]
      rw [hpair_oo] at hzero
      exact h2 hzero
    exact (smul_eq_zero.mp hsmul).resolve_right hh'
  have hdet0 : (CK.map (Int.cast : ℤ → ZMod p)).det = 0 :=
    Matrix.det_eq_zero_of_dual_apply_eq_zero α' h'
      (C := CK.map (Int.cast : ℤ → ZMod p))
      (fun i j => by simpa using hpairK i j) hyV0 hαy hfinrank
  have hA : ∃ (n : ℕ) (e' : Fin n ≃ Λ'), MK = (CoxeterMatrix.A n).reindex e' := by
    by_contra hnA
    have hE6 : p = 3 → ¬ ∃ e : Fin 6 ≃ Λ', MK = CoxeterMatrix.E₆.reindex e := by
      intro hp3 he
      obtain ⟨e6, _⟩ := he
      have hcard6 : Fintype.card Λ' = 6 := by
        rw [← Fintype.card_fin 6, Fintype.card_congr e6]
      rw [hcardΛ'] at hcard6
      rcases hcell with ⟨hp5, hN5'⟩ | ⟨hp3', hN6⟩ | ⟨hp7, hN7⟩ | ⟨hp3'', hN9⟩ | ⟨hp5', hN10⟩
      all_goals omega
    exact (hIntK.det_map_ne_zero_of_not_A hWMK hnA hp2 hE6) hdet0
  obtain ⟨n, e', hMKeq⟩ := hA
  have hrange : Set.range φ' =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
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
  have hclosK' : ggAutomizer K Bs = Subgroup.closure (Set.range φ') := by
    rw [hclosK, hrange]
  exact ⟨n, Λ', inferInstance, inferInstance, MK, CK, V, i3, i4, ι, φ', h', α', e',
    hMKeq, hWMK, hIntK, (fun o w => hlin (o.map Subtype.val id) w),
    (fun o => hrefl (o.map Subtype.val id)), hpairK, hfKex, hclosK'⟩

theorem ggTWR2_xdatumA_L
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open) (hJ2S : GGTBJTwoNodeSmallInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧
      Nat.card ↥Bs = q ^ labK.rank) p J K)
    (hL : GGResTwoNodeSideDatum p Bs L J) :
    ∃ n : ℕ, GGResXDatumA p Bs L n := by
  classical
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA, hc⟩ := hrow
  have hrowSmall : ggRowTwoNodeSmall p labJ labK := hrowJA.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hrow2 : ggRowTwoNode p labJ labK := hrowSmall.1
  have hKle9 : labK.rank ≤ 9 := hrowSmall.2
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hrow2 h4K
  have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
      labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
    rcases l05nQD_cell hp hp2 h4K hKle9 hdvdK with h | h | h | h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr (Or.inl h.2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h.2)))
  have hrowK : GGResRowAt ggRowTwoNode p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2⟩
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJA p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA⟩
  have hKdatum : GGResXDatumA p Bs K labK.rank :=
    ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
      (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hJtag (by omega) hrowK
  have hKside : GGResTwoNodeSideDatum p Bs K J :=
    (hJ2S G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hKdatum) hrowK0
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcardΛa, hWML, hIntL, hWMK, hIntK, hlin, hrefl, hpairL, hpairK, hfLex, hfKex,
    hclosL, hclosK, hdel, _hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hKside hL
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨ΛK, i1K, i2K, MK0, CK0, VK, i3K, i4K, ιK, φK0, hK0, αK0, eK, hMKeqK, hWMK0,
    hIntK0, hlinK0, hreflK0, hpairK0, hfK0ex, _hclosK0⟩ := hKdatum
  letI := i1K; letI := i2K; letI := i3K; letI := i4K
  obtain ⟨fK0, hfK0⟩ := hfK0ex
  have hN2 : 2 ≤ labK.rank := by omega
  obtain ⟨e, hMLeq⟩ :=
    ggTW_typeA_of_datum (p := p) (n := labK.rank) hp2 hN2 hBs (ggAutomizer K Bs)
      (Λ₁ := ΛK) (M₁ := MK0) eK hMKeqK hWMK0 fK0 φK0 hfK0 hreflK0
      (Λ₂ := Λ) (M₂ := ML) hWML fL (fun i => φ (Sum.inl i)) (fun i => hfL i)
      (fun i => hrefl (Sum.inl i))
  let Λ' : Type := {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa
  let φ' : Λ' → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  let h' : Λ' → V := fun o => h (o.map Subtype.val id)
  let α' : Λ' → Module.Dual (ZMod p) V := fun o => α (o.map Subtype.val id)
  have hcardΛ : Fintype.card Λ = labK.rank := by
    rw [← Fintype.card_fin labK.rank, Fintype.card_congr e]
  have hcardΛaF : Fintype.card Λa = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardΛa
  have hcardSub : Fintype.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} = labK.rank - 2 := by
    rw [Fintype.card_of_subtype
      (Finset.univ.filter (fun i : Λ => i ≠ b₁ ∧ i ≠ b₂)) (by intro i; simp)]
    have hfilter : Finset.univ.filter (fun i : Λ => i ≠ b₁ ∧ i ≠ b₂) =
        (Finset.univ.erase b₁).erase b₂ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [hfilter]
    have h1 : b₂ ∈ Finset.univ.erase b₁ := Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ b₂⟩
    rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ b₁),
      Finset.card_univ]
    omega
  have hcardΛ' : Fintype.card Λ' = labK.rank := by
    change Fintype.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) = labK.rank
    rw [Fintype.card_sum, hcardSub, hcardΛaF]
    omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at h
  have hcardV : Nat.card V = Nat.card ↥Bs := by
    rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
    exact (Nat.card_congr ι.toEquiv).symm
  have hpow_eq : p ^ Module.finrank (ZMod p) V = p ^ labK.rank := by
    rw [← hVcard, hcardV, hc]
  have hfinrank_eq : Module.finrank (ZMod p) V = labK.rank :=
    Nat.pow_right_injective hp.two_le hpow_eq
  have hfinrank : Module.finrank (ZMod p) V ≤ Fintype.card Λ' := by
    rw [hfinrank_eq, hcardΛ']
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hH.1.orderOf_x
    rw [h1, orderOf_one] at h
    exact (Fact.out : p.Prime).one_lt.ne' h.symm
  have hfixx := ggRC_automizer_fixes_y hxBs hLx
  have hxV0' : ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (by simpa using h0))
    exact hx1 (by simpa using Subtype.ext_iff.mp h1)
  let xV : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hxV0 : xV ≠ 0 := hxV0'
  have hαx : ∀ o : Λ', α' o xV = 0 := by
    intro o
    have hmemL : φ' o ∈ ggAutomizer L Bs := by
      rw [hclosK]
      apply Subgroup.subset_closure
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    have hfixo : φ' o ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := hfixx (φ' o) hmemL
    have hlin_fix : ggLin (p := p) ι (φ' o) xV = xV :=
      (ggLin_fix_iff (p := p) ι (φ' o) (⟨x, hxBs⟩ : ↥Bs)).mp hfixo
    have hsmul : α' o xV • h' o = 0 := by
      have h1 := hlin (o.map Subtype.val id) xV
      rw [hlin_fix] at h1
      exact sub_eq_self.mp h1.symm
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro hzero
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hdvd)
    have hpair_oo : α' o (h' o) = (2 : ZMod p) := by
      have hh := hpairK o o
      rw [hIntK.1 o] at hh
      simpa using hh
    have hh' : h' o ≠ 0 := by
      intro h0
      have hzero : α' o (h' o) = 0 := by rw [h0, map_zero]
      rw [hpair_oo] at hzero
      exact h2 hzero
    exact (smul_eq_zero.mp hsmul).resolve_right hh'
  have hdet0 : (CK.map (Int.cast : ℤ → ZMod p)).det = 0 :=
    Matrix.det_eq_zero_of_dual_apply_eq_zero α' h'
      (C := CK.map (Int.cast : ℤ → ZMod p))
      (fun i j => by simpa using hpairK i j) hxV0 hαx hfinrank
  have hA : ∃ (n : ℕ) (e' : Fin n ≃ Λ'), MK = (CoxeterMatrix.A n).reindex e' := by
    by_contra hnA
    have hE6 : p = 3 → ¬ ∃ e : Fin 6 ≃ Λ', MK = CoxeterMatrix.E₆.reindex e := by
      intro hp3 he
      obtain ⟨e6, _⟩ := he
      have hcard6 : Fintype.card Λ' = 6 := by
        rw [← Fintype.card_fin 6, Fintype.card_congr e6]
      rw [hcardΛ'] at hcard6
      have h7 : (3 : ℕ) ∣ 7 := by rw [hp3, hcard6] at hdvdK; exact hdvdK
      norm_num at h7
    exact (hIntK.det_map_ne_zero_of_not_A hWMK hnA hp2 hE6) hdet0
  obtain ⟨n, e', hMKeq⟩ := hA
  have hrange : Set.range φ' =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
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
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φ') := by
    rw [hclosK, hrange]
  exact ⟨n, Λ', inferInstance, inferInstance, MK, CK, V, i3, i4, ι, φ', h', α', e',
    hMKeq, hWMK, hIntK, (fun o w => hlin (o.map Subtype.val id) w),
    (fun o => hrefl (o.map Subtype.val id)), hpairK, hfKex, hclosL'⟩

theorem ggTWR23_K_typeA_or
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hC : GGTWSmallCells) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallJA p J L)
    (hxL : x ∉ L) (hK : GGResTwoNodeSideDatum p Bs K J) :
    (∃ n : ℕ, GGResXDatumA p Bs K n) ∨
      (p = 3 ∧ Nat.card ↥Bs = 3 ^ 6 ∧
        GGResRowAt (fun q labJ labL => ggRowTwoNodeSmallJA q labJ labL ∧ labL.rank = 5) p J L) := by
  classical
  obtain ⟨labJ, labL, hJΛ, hLΛ, hJl, hLl, hr⟩ := hrow
  by_cases hc : Nat.card ↥Bs = p ^ (labL.rank + 1)
  · by_cases h5 : labL.rank = 5
    ·
      have hp3 : p = 3 := by
        have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
        have h4 : 4 ≤ labL.rank := ggTWSmallA_rank_ge Fact.out hp2 hJΛ hr.2 hr.1.1
        obtain ⟨-, -, -, hdvdL, -⟩ := l05nQD_row_facts hr.1.1 h4
        have h6 : p ∣ 6 := by
          rw [h5] at hdvdL
          simpa using hdvdL
        have h23 : p ∣ 2 * 3 := by rwa [show (2 : ℕ) * 3 = 6 by norm_num]
        rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h23 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h) hp2
        · exact (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num : Nat.Prime 3)).1 h
      exact Or.inr ⟨hp3, by norm_num [hc, hp3, h5],
        ⟨labJ, labL, hJΛ, hLΛ, hJl, hLl, hr, h5⟩⟩
    · exact (ggTWR3_false hRig hT hLift hW hR hTw hJ2S hFix hFixK hC hH
        ⟨labJ, labL, hJΛ, hLΛ, hJl, hLl, hr, hc, h5⟩ hxL hK).elim
  · exact Or.inl (ggTWR2_xdatumA_K hRig hT hLift hW hR hTw hJ2S hFix hH
      ⟨labJ, labL, hJΛ, hLΛ, hJl, hLl, hr, hc⟩ hxL hK)

end CFSG.StandardType

end
