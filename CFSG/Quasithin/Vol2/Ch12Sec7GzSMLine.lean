module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSCode
public import CFSG.Quasithin.Vol2.Ch12Sec7GzLem1b
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10D
public import Certificates.Certificate589101

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277MLine
open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.S127 S127.I77 S127.L5
open scoped IsMulCommutative

section Aux

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [IsMulCommutative ↥V]

theorem ncard_le_length' {α : Type*} {S : Set α} (hS : S.Finite) {l : List α}
    (hsub : ∀ x ∈ S, x ∈ l) : S.ncard ≤ l.length := by
  classical
  calc S.ncard ≤ (↑(l.toFinset) : Set α).ncard :=
        Set.ncard_le_ncard (fun x hx => List.mem_toFinset.2 (hsub x hx)) (Set.toFinite _)
    _ = l.toFinset.card := Set.ncard_coe_finset _
    _ ≤ l.length := List.toFinset_card_le _

theorem length_le_ncard' {α : Type*} {S : Set α} (hS : S.Finite) {l : List α} (hl : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ S) : l.length ≤ S.ncard := by
  classical
  have h1 : l.length = (↑(l.toFinset) : Set α).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]
  rw [h1]
  exact Set.ncard_le_ncard (fun x hx => hsub x (List.mem_toFinset.1 hx)) hS

theorem ncard_codes (C : Coding ↥V) (K : Subgroup ↥V) :
    (C.cd '' (K : Set ↥V)).ncard = Nat.card K := by
  rw [Set.ncard_image_of_injective _ C.cd_injective]
  exact (Nat.card_coe_set_eq _).symm

theorem conjAct_eq_one_of_mem {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (hgV : g ∈ V) :
    conjAct V ⟨g, hg⟩ = 1 := by
  ext x
  show (((conjAct V ⟨g, hg⟩) x : ↥V) : G) = ((x : ↥V) : G)
  rw [conjAct_val]
  have hc : g * (x : G) = (x : G) * g :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨g, hgV⟩ x)
  rw [hc]
  group

theorem conjAct_sq_one {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (h2 : g * g = 1) :
    conjAct V ⟨g, hg⟩ * conjAct V ⟨g, hg⟩ = 1 := by
  rw [← map_mul]
  have : (⟨g, hg⟩ * ⟨g, hg⟩ : Subgroup.normalizer (V : Set G)) = 1 := Subtype.ext h2
  rw [this, map_one]

theorem conjAct_ne_one {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (hgV : g ∉ V)
    (hCV : Subgroup.centralizer (V : Set G) = V) : conjAct V ⟨g, hg⟩ ≠ 1 := by
  intro h
  apply hgV
  rw [← hCV]
  exact A4.conjAct_eq_one_iff.1 h

theorem autOn_sq {W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hWV : W ≤ Subgroup.normalizer (V : Set G)) {a : MulAut ↥V} (ha : a ∈ autOn W V) :
    a * a = 1 := by
  obtain ⟨h, rfl⟩ := (A4.mem_autOn_iff hWV).1 ha
  rw [← map_mul]
  have h2 : (h : G) * (h : G) = 1 := by
    rw [← pow_two]
    exact hW.2 _ h.2
  have : h * h = 1 := Subtype.ext h2
  rw [this, map_one]

theorem card_autOn_four {W : Subgroup G} (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hCV : Subgroup.centralizer (V : Set G) = V) (hW64 : Nat.card W = 64)
    (hWV16 : Nat.card ↥(W ⊓ V) = 16) : Nat.card (autOn W V) = 4 := by
  rw [card_autOn_eq_relIndex hWV, hCV]
  have h := Subgroup.relIndex_mul_card (H := W ⊓ V) (K := W)
  rw [inf_eq_left.2 (inf_le_left : W ⊓ V ≤ W), hWV16, hW64] at h
  omega

theorem fix_mem_of_mem {H W : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hW : IsElemAbelian 2 W) (hWH : W ≤ H) (hWV16 : Nat.card ↥(W ⊓ V) = 16)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    {C : Coding ↥V} {Γ : List B6} (hΓ : mCheck Γ () = true)
    (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ)
    {w : G} (hwW : w ∈ W) (hwV : w ∉ V) :
    ∀ x : ↥V, conjAct V ⟨w, hH (hWH hwW)⟩ x = x → (x : G) ∈ W ⊓ V := by
  have hAH : conjAct V ⟨w, hH (hWH hwW)⟩ ∈ autOn H V :=
    (A4.mem_autOn_iff hH).2 ⟨⟨w, hWH hwW⟩, rfl⟩
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact hW.2 w hwW
  have hlen : (fixList (C.cB (conjAct V ⟨w, hH (hWH hwW)⟩))).length ≤ 16 :=
    mCheck_fix hΓ (hΓ1 _ hAH)
      (isInv_cB C (conjAct_sq_one _ hww) (conjAct_ne_one _ hwV hCV))
  have hK : Nat.card ((W ⊓ V : Subgroup G).subgroupOf V) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : W ⊓ V ≤ V)).toEquiv, hWV16]
  have hfix : ∀ x ∈ (W ⊓ V : Subgroup G).subgroupOf V,
      conjAct V ⟨w, hH (hWH hwW)⟩ x = x := by
    intro x hx
    have hxW : (x : G) ∈ W := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
    apply Subtype.ext
    rw [conjAct_val]
    have hc : w * (x : G) = (x : G) * w := comm_of_isElemAbelian hW hwW hxW
    rw [hc]
    group
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (mem_of_fix hK hfix hlen x hx)

theorem codes_fixList {H W : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hW : IsElemAbelian 2 W) (hWH : W ≤ H) (hWV16 : Nat.card ↥(W ⊓ V) = 16)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    {C : Coding ↥V} {Γ : List B6} (hΓ : mCheck Γ () = true)
    (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ)
    {w : G} (hwW : w ∈ W) (hwV : w ∉ V) :
    (∀ x : ↥V, (x : G) ∈ W ⊓ V ↔
        C.cd x ∈ fixList (C.cB (conjAct V ⟨w, hH (hWH hwW)⟩))) ∧
      (fixList (C.cB (conjAct V ⟨w, hH (hWH hwW)⟩))).length = 16 := by
  classical
  set A : MulAut ↥V := conjAct V ⟨w, hH (hWH hwW)⟩ with hA
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact hW.2 w hwW
  have hlen : (fixList (C.cB A)).length ≤ 16 :=
    mCheck_fix hΓ (hΓ1 _ ((A4.mem_autOn_iff hH).2 ⟨⟨w, hWH hwW⟩, rfl⟩))
      (isInv_cB C (conjAct_sq_one _ hww) (conjAct_ne_one _ hwV hCV))
  have hiff : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ fixList (C.cB A) := by
    intro x
    constructor
    · intro hx
      have hxW : (x : G) ∈ W := (Subgroup.mem_inf.1 hx).1
      have hAx : A x = x := by
        apply Subtype.ext
        rw [hA, conjAct_val]
        have hc : w * (x : G) = (x : G) * w := comm_of_isElemAbelian hW hwW hxW
        rw [hc]
        group
      rw [mem_fixList]
      refine ⟨C.cd_lt x, ?_⟩
      rw [← C.cd_apply, hAx]
    · intro hx
      rw [mem_fixList] at hx
      have hAx : A x = x := by
        apply C.cd_injective
        rw [C.cd_apply, hx.2]
      exact (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (fix_mem_of_mem hH hW hWH hWV16 hCV hΓ hΓ1
        hwW hwV x (by rw [← hA]; exact hAx))).1, (Subgroup.mem_inf.1 (fix_mem_of_mem hH hW hWH
        hWV16 hCV hΓ hΓ1 hwW hwV x (by rw [← hA]; exact hAx))).2⟩)
  refine ⟨hiff, le_antisymm hlen ?_⟩
  have hS : (C.cd '' ((W ⊓ V : Subgroup G).subgroupOf V : Set ↥V)).ncard = 16 := by
    rw [ncard_codes, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : W ⊓ V ≤ V)).toEquiv, hWV16]
  have hsub : ∀ c ∈ C.cd '' ((W ⊓ V : Subgroup G).subgroupOf V : Set ↥V),
      c ∈ fixList (C.cB A) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hiff x).1 (Subgroup.mem_subgroupOf.1 hx)
  have hfin : (C.cd '' ((W ⊓ V : Subgroup G).subgroupOf V : Set ↥V)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hS]; norm_num)
  have := ncard_le_length' hfin hsub
  omega

theorem invs_mem {H W W' : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hW' : IsElemAbelian 2 W') (hW'H : W' ≤ H)
    {C : Coding ↥V} {Γ : List B6} (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ) {Dl : List ℕ}
    (hDl : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ Dl) (hDlt : ∀ d ∈ Dl, d < 64)
    (hWC : ∀ y ∈ W', ∀ z ∈ W ⊓ V, z * y = y * z)
    {a : MulAut ↥V} (ha : a ∈ autOn W' V) (ha1 : a ≠ 1) : C.cB a ∈ invsD Γ Dl := by
  have hW'V : W' ≤ Subgroup.normalizer (V : Set G) := hW'H.trans hH
  rw [mem_invsD]
  refine ⟨hΓ1 a (A4.autOn_mono hW'H ha), isInv_cB C (autOn_sq hW' hW'V ha) ha1, fun d hd => ?_⟩
  obtain ⟨h, rfl⟩ := (A4.mem_autOn_iff hW'V).1 ha
  have hxW : (C.dc d : G) ∈ W ⊓ V := (hDl (C.dc d)).2 (by rw [C.cd_dc d (hDlt d hd)]; exact hd)
  have hfixx : A4.actionOn V W' hW'V h (C.dc d) = C.dc d := by
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    have hc : (h : G) * (C.dc d : G) = (C.dc d : G) * (h : G) := (hWC h.1 h.2 _ hxW).symm
    rw [hc]
    group
  calc (C.cB (A4.actionOn V W' hW'V h)).app d
      = (C.cB (A4.actionOn V W' hW'V h)).app (C.cd (C.dc d)) := by rw [C.cd_dc d (hDlt d hd)]
    _ = C.cd (A4.actionOn V W' hW'V h (C.dc d)) := (C.cd_apply _ _).symm
    _ = C.cd (C.dc d) := by rw [hfixx]
    _ = d := C.cd_dc d (hDlt d hd)

theorem invs_three {H W : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hW : IsElemAbelian 2 W) (hWH : W ≤ H) (hWV16 : Nat.card ↥(W ⊓ V) = 16)
    (hW64 : Nat.card W = 64) (hCV : Subgroup.centralizer (V : Set G) = V)
    {C : Coding ↥V} {Γ : List B6} (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ) {Dl : List ℕ}
    (hDl : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ Dl) (hDlt : ∀ d ∈ Dl, d < 64)
    (hle3 : (invsD Γ Dl).length ≤ 3) :
    (invsD Γ Dl).length = 3 ∧ ∀ B ∈ invsD Γ Dl, ∃ a ∈ autOn W V, a ≠ 1 ∧ C.cB a = B := by
  classical
  have hWC : ∀ y ∈ W, ∀ z ∈ W ⊓ V, z * y = y * z := fun y hy z hz =>
    comm_of_isElemAbelian hW (Subgroup.mem_inf.1 hz).1 hy
  have hcardA : Nat.card (autOn W V) = 4 := card_autOn_four (hWH.trans hH) hCV hW64 hWV16
  have hncA : (autOn W V : Set (MulAut ↥V)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcardA
  have hfinA : (autOn W V : Set (MulAut ↥V)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncA]; norm_num)
  have h1A : (1 : MulAut ↥V) ∈ (autOn W V : Set (MulAut ↥V)) := (autOn W V).one_mem
  have hdiff : ((autOn W V : Set (MulAut ↥V)) \ {1}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem h1A, hncA]
  have hT₀card : (C.cB '' ((autOn W V : Set (MulAut ↥V)) \ {1})).ncard = 3 := by
    rw [Set.ncard_image_of_injective _ C.cB_injective, hdiff]
  have hT₀fin : (C.cB '' ((autOn W V : Set (MulAut ↥V)) \ {1})).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hT₀card]; norm_num)
  have hT₀sub : ∀ B ∈ C.cB '' ((autOn W V : Set (MulAut ↥V)) \ {1}), B ∈ invsD Γ Dl := by
    rintro B ⟨a, ⟨ha, ha1⟩, rfl⟩
    exact invs_mem hH hW hWH hΓ1 hDl hDlt hWC ha (by simpa using ha1)
  have hinv_sub : ∀ B ∈ invsD Γ Dl, B ∈ C.cB '' ((autOn W V : Set (MulAut ↥V)) \ {1}) :=
    fun B hB => eq_of_mem_invsD hle3 hT₀sub hT₀card hT₀fin hB
  have hlen3 : (invsD Γ Dl).length = 3 := by
    apply le_antisymm hle3
    have := ncard_le_length' hT₀fin hT₀sub
    omega
  refine ⟨hlen3, fun B hB => ?_⟩
  obtain ⟨a, ⟨ha, ha1⟩, hBa⟩ := hinv_sub B hB
  exact ⟨a, ha, by simpa using ha1, hBa⟩

theorem M1_part {H W : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hW : IsElemAbelian 2 W) (hWH : W ≤ H) (hW64 : Nat.card W = 64)
    (hWV16 : Nat.card ↥(W ⊓ V) = 16) (hV64 : Nat.card ↥V = 64)
    (hCV : Subgroup.centralizer (V : Set G) = V) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    {C : Coding ↥V} {Γ : List B6} (hΓ : mCheck Γ () = true)
    (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ) {Dl : List ℕ}
    (hDl : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ Dl) (hDlt : ∀ d ∈ Dl, d < 64)
    (hT : ∀ B ∈ invsD Γ Dl, ∃ a ∈ autOn W V, a ≠ 1 ∧ C.cB a = B)
    (hwV : ∃ w ∈ W, w ∉ V) :
    ∀ W' : Subgroup G, W' ≤ H ⊓ Subgroup.centralizer ((W ⊓ V : Subgroup G) : Set G) →
      IsElemAbelian 2 W' → Nat.card W' = 64 → W' = V ∨ W' = W := by
  intro W' hW'N hW'el hW'64
  by_cases hW'V : W' = V
  · exact Or.inl hW'V
  right
  have hW'H : W' ≤ H := hW'N.trans inf_le_left
  have hW'V' : W' ≤ Subgroup.normalizer (V : Set G) := hW'H.trans hH
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := hWH.trans hH
  have hWC : ∀ y ∈ W', ∀ z ∈ W ⊓ V, z * y = y * z := fun y hy z hz =>
    (Subgroup.mem_centralizer_iff.1 (hW'N hy).2) z hz
  have hexW' : ∃ w' ∈ W', w' ∉ V := by
    by_contra hno
    push Not at hno
    exact hW'V (Subgroup.eq_of_le_of_card_ge (fun x hx => hno x hx)
      (le_of_eq (by rw [hV64, hW'64])))
  have hc : ∀ a ∈ autOn W' V, a ≠ 1 → a ∈ autOn W V := by
    intro a ha ha1
    obtain ⟨b, hb1, -, hb⟩ := hT (C.cB a) (invs_mem hH hW'el hW'H hΓ1 hDl hDlt hWC ha ha1)
    have hab : a = b := C.cB_injective hb.symm
    rw [hab]
    exact hb1
  obtain ⟨w', hw'W', hw'V⟩ := hexW'
  have hw'N : w' ∈ Subgroup.normalizer (V : Set G) := hW'V' hw'W'
  have hconj_ne : conjAct V ⟨w', hw'N⟩ ≠ 1 := conjAct_ne_one hw'N hw'V hCV
  have he : ∀ x ∈ W', x ∈ V → x ∈ W := by
    intro x hxW' hxV
    have hmem : conjAct V ⟨w', hw'N⟩ ∈ autOn W' V :=
      (A4.mem_autOn_iff hW'V').2 ⟨⟨w', hw'W'⟩, rfl⟩
    obtain ⟨⟨w, hwW⟩, hwa⟩ := (A4.mem_autOn_iff hWN).1 (hc _ hmem hconj_ne)
    have hwV : w ∉ V := by
      intro hwV
      apply hconj_ne
      rw [← hwa]
      exact conjAct_eq_one_of_mem (hWN hwW) hwV
    have hx : conjAct V ⟨w, hWN hwW⟩ ⟨x, hxV⟩ = ⟨x, hxV⟩ := by
      have hc2 : conjAct V ⟨w, hWN hwW⟩ = conjAct V ⟨w', hw'N⟩ := hwa
      rw [hc2]
      apply Subtype.ext
      rw [conjAct_val]
      change w' * x * w'⁻¹ = x
      have hcm : w' * x = x * w' := comm_of_isElemAbelian hW'el hw'W' hxW'
      rw [hcm]
      group
    exact (Subgroup.mem_inf.1 (fix_mem_of_mem hH hW hWH hWV16 hCV hΓ hΓ1 hwW hwV ⟨x, hxV⟩ hx)).1
  have hf : ∀ y ∈ W', y ∉ V → y ∈ W := by
    intro y hyW' hyV
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hW'V' hyW'
    have hymem : conjAct V ⟨y, hyN⟩ ∈ autOn W' V :=
      (A4.mem_autOn_iff hW'V').2 ⟨⟨y, hyW'⟩, rfl⟩
    obtain ⟨⟨w, hwW⟩, hwa⟩ := (A4.mem_autOn_iff hWN).1 (hc _ hymem (conjAct_ne_one hyN hyV hCV))
    have hwV : w ∉ V := by
      intro hwV
      apply conjAct_ne_one hyN hyV hCV
      rw [← hwa]
      exact conjAct_eq_one_of_mem (hWN hwW) hwV
    have hwconj : ∀ v : ↥V, w * (v : G) * w⁻¹ = y * (v : G) * y⁻¹ := fun v =>
      congrArg (fun φ : MulAut ↥V => ((φ v : ↥V) : G)) hwa
    have hpv : ∀ v ∈ V, (y⁻¹ * w) * v = v * (y⁻¹ * w) := by
      intro v hv
      have hv' := hwconj ⟨v, hv⟩
      calc (y⁻¹ * w) * v = y⁻¹ * (w * v * w⁻¹) * w := by group
        _ = y⁻¹ * (y * v * y⁻¹) * w := by rw [hv']
        _ = v * (y⁻¹ * w) := by group
    obtain ⟨u, hu⟩ : ∃ u : G, u = w⁻¹ * y := ⟨_, rfl⟩
    have hu_comm : ∀ v ∈ V, u * v = v * u := by
      intro v hv
      have hp := hpv v hv
      calc u * v = (y⁻¹ * w)⁻¹ * v := by rw [hu]; group
        _ = (y⁻¹ * w)⁻¹ * (v * (y⁻¹ * w)) * (y⁻¹ * w)⁻¹ := by group
        _ = (y⁻¹ * w)⁻¹ * ((y⁻¹ * w) * v) * (y⁻¹ * w)⁻¹ := by rw [hp]
        _ = v * u := by rw [hu]; group
    have huV : u ∈ V := by
      rw [← hCV]
      exact Subgroup.mem_centralizer_iff.2 (fun v hv => (hu_comm v hv).symm)
    have hyy : y * y = 1 := by
      rw [← pow_two]
      exact hW'el.2 y hyW'
    have hww : w * w = 1 := by
      rw [← pow_two]
      exact hW.2 w hwW
    have huu : u * u = 1 := by
      rw [← pow_two]
      exact hV2 u huV
    have hy_eq : y = w * u := by rw [hu]; group
    have hwu : w * u * w⁻¹ = u := by
      have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
      have h1 : w * u * w * u = 1 := by
        have hyy' := hyy
        rw [hy_eq] at hyy'
        calc w * u * w * u = w * u * (w * u) := by group
          _ = 1 := hyy'
      have h2 : w * u * w = u⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
      rw [hw_inv, h2, h3]
    have hfix_u : conjAct V ⟨w, hWN hwW⟩ ⟨u, huV⟩ = ⟨u, huV⟩ := by
      apply Subtype.ext
      rw [conjAct_val]
      exact hwu
    have huW : u ∈ W :=
      (Subgroup.mem_inf.1 (fix_mem_of_mem hH hW hWH hWV16 hCV hΓ hΓ1 hwW hwV ⟨u, huV⟩ hfix_u)).1
    rw [hy_eq]
    exact W.mul_mem hwW huW
  have hle : W' ≤ W := by
    intro y hy
    by_cases hyV : y ∈ V
    · exact he y hy hyV
    · exact hf y hy hyV
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hW64, hW'64]))

theorem M2_part {H W L : Subgroup G} {t : G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Coding ↥V} {Γ : List B6}
    (hC : IdentL C (autOn L V)) (htV : t ∈ V) (htVt : t ∈ Vt L t)
    (hVtW : Vt L t ≤ W ⊓ V) (hVtV : Vt L t ≤ V) (hVtcard : Nat.card ↥(Vt L t) = 4)
    (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18)
    (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn H V, C.cB a = B)
    {Dl : List ℕ} (hDl : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ Dl) (hDlnd : Dl.Nodup)
    (hperd : 4 ≤ (orbD Dl 18).length ∧
      ∀ t' ∈ orbD Dl 18, ∀ s ∈ orbD Dl 18, ∃ B' ∈ stabD Γ Dl, B'.app t' = s) :
    ∃ g ∈ H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G),
      g * t * g⁻¹ ∈ W ⊓ V ∧ g * t * g⁻¹ ∉ Vt L t := by
  classical
  have ht' : (⟨t, htV⟩ : ↥V) = ⟨t, htV⟩ := rfl
  have hct : C.cd (⟨t, htV⟩ : ↥V) ∈ Dl := (hDl ⟨t, htV⟩).1 (hVtW htVt)
  have hot : orbitSize gm6 (C.cd (⟨t, htV⟩ : ↥V)) = 18 := by
    have h1 := card_orbitIn_autOn hLV (⟨t, htV⟩ : ↥V)
    rw [card_orbitIn_eq_orbitSize hC] at h1
    rw [h1]
    exact h18
  have hT18 : C.cd (⟨t, htV⟩ : ↥V) ∈ orbD Dl 18 := mem_orbD.2 ⟨hct, hot⟩
  have hOrbNd : (orbD Dl 18).Nodup := hDlnd.filter _
  have hVtVcodes : (C.cd '' ((Vt L t).subgroupOf V : Set ↥V)).ncard = 4 := by
    rw [ncard_codes, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVtV).toEquiv, hVtcard]
  have hfinVt : (C.cd '' ((Vt L t).subgroupOf V : Set ↥V)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hVtVcodes]; norm_num)
  have h0C : (0 : ℕ) ∈ C.cd '' ((Vt L t).subgroupOf V : Set ↥V) :=
    ⟨1, Subgroup.one_mem _, C.cd_one⟩
  have hzero : (0 : ℕ) ∉ orbD Dl 18 := by
    intro h0
    have h1 := (mem_orbD.1 h0).2
    rw [orbitSize_gm6_zero hC] at h1
    omega
  obtain ⟨s, hsT, hsV⟩ : ∃ s ∈ orbD Dl 18,
      s ∉ C.cd '' ((Vt L t).subgroupOf V : Set ↥V) := by
    by_contra hno
    push Not at hno
    have hfin3 : ((C.cd '' ((Vt L t).subgroupOf V : Set ↥V)) \ {0}).Finite :=
      hfinVt.diff
    have hsub : ∀ x ∈ orbD Dl 18, x ∈ (C.cd '' ((Vt L t).subgroupOf V : Set ↥V)) \ {0} := by
      intro x hx
      refine ⟨hno x hx, fun h => ?_⟩
      rw [Set.mem_singleton_iff] at h
      exact hzero (h ▸ hx)
    have hle := length_le_ncard' hfin3 hOrbNd hsub
    have hdiff : ((C.cd '' ((Vt L t).subgroupOf V : Set ↥V)) \ {0}).ncard = 3 := by
      rw [Set.ncard_diff_singleton_of_mem h0C, hVtVcodes]
    omega
  obtain ⟨B', hB'st, hB's⟩ := hperd.2 _ hT18 s hsT
  obtain ⟨g, hgH, hgN, hg, hgB⟩ := exists_normalizes_of_stabD hH hΓ2 inf_le_right hDl hB'st
  have hcj : cj C ⟨g, hg⟩ = B' := hgB
  have hcd : C.cd (conjAct V ⟨g, hg⟩ (⟨t, htV⟩ : ↥V)) = s := by
    rw [cd_conj, hcj]
    exact hB's
  refine ⟨g, ⟨hgH, hgN⟩, ?_, ?_⟩
  · exact (hDl _).2 (by rw [hcd]; exact (mem_orbD.1 hsT).1)
  · intro hmem
    apply hsV
    refine ⟨conjAct V ⟨g, hg⟩ (⟨t, htV⟩ : ↥V), ?_, hcd⟩
    exact Subgroup.mem_subgroupOf.2 hmem

theorem M3_part {H W L : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Coding ↥V} {Γ : List B6}
    (hC : IdentL C (autOn L V)) (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn H V, C.cB a = B)
    {Dl : List ℕ} (hDl : ∀ x : ↥V, (x : G) ∈ W ⊓ V ↔ C.cd x ∈ Dl) (hDlt : ∀ d ∈ Dl, d < 64)
    (hperd : ∃ c ∈ orbD Dl 45, 9 ≤ (dedupN ((stabD Γ Dl).map fun B' => B'.app c)).length) :
    ∃ z₀ ∈ W ⊓ V, (Subgroup.centralizer ({z₀} : Set G)).relIndex L = 45 ∧
      9 ≤ (Subgroup.centralizer ({z₀} : Set G)).relIndex
        (H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G)) := by
  classical
  obtain ⟨c, hc45, h9⟩ := hperd
  obtain ⟨hcDl, hc45'⟩ := mem_orbD.1 hc45
  have hcl : c < 64 := hDlt c hcDl
  have hzD : (C.dc c : G) ∈ W ⊓ V := (hDl (C.dc c)).2 (by rw [C.cd_dc c hcl]; exact hcDl)
  refine ⟨(C.dc c : G), hzD, ?_, ?_⟩
  · have h1 := card_orbitIn_autOn hLV (C.dc c)
    rw [card_orbitIn_eq_orbitSize hC (C.dc c), C.cd_dc c hcl, hc45'] at h1
    exact h1.symm
  · have hNV : H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G) ≤
        Subgroup.normalizer (V : Set G) := inf_le_left.trans hH
    rw [← card_orbitIn_autOn hNV (C.dc c)]
    have hsub : ∀ x ∈ dedupN ((stabD Γ Dl).map fun B' => B'.app c),
        x ∈ C.cd '' Orbit.orbitIn (autOn (H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G)) V)
          (C.dc c) := by
      intro x hx
      rw [mem_dedupN, List.mem_map] at hx
      obtain ⟨B', hB'st, hB'x⟩ := hx
      obtain ⟨g, hgH, hgN, hg, hgB⟩ := exists_normalizes_of_stabD hH hΓ2 inf_le_right hDl hB'st
      have hcj : cj C ⟨g, hg⟩ = B' := hgB
      have hmemN : conjAct V ⟨g, hg⟩ ∈
          autOn (H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G)) V :=
        (A4.mem_autOn_iff hNV).2 ⟨⟨g, ⟨hgH, hgN⟩⟩, rfl⟩
      refine ⟨conjAct V ⟨g, hg⟩ (C.dc c), ⟨conjAct V ⟨g, hg⟩, hmemN, rfl⟩, ?_⟩
      rw [cd_conj, hcj, C.cd_dc c hcl]
      exact hB'x
    have hfinO : (Orbit.orbitIn (autOn (H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G)) V)
        (C.dc c)).Finite := Set.toFinite _
    have hfinC : (C.cd '' Orbit.orbitIn (autOn (H ⊓ Subgroup.normalizer
        ((W ⊓ V : Subgroup G) : Set G)) V) (C.dc c)).Finite := hfinO.image _
    have h2 := length_le_ncard' hfinC (dedupN_nodup _) hsub
    have h3 : (C.cd '' Orbit.orbitIn (autOn (H ⊓ Subgroup.normalizer
        ((W ⊓ V : Subgroup G) : Set G)) V) (C.dc c)).ncard ≤
        Nat.card ↥(Orbit.orbitIn (autOn (H ⊓ Subgroup.normalizer
        ((W ⊓ V : Subgroup G) : Set G)) V) (C.dc c)) := by
      rw [Nat.card_coe_set_eq]
      exact Set.ncard_image_le hfinO
    omega

theorem relIndex18_of_set77
    {T L V : Subgroup G} {t : G} (s : Set77 G T L V t)
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) :
    (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 := by
  classical
  have hyp := s.d.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer hyp
  have hCV : Subgroup.centralizer (V : Set G) = V := s.centralizer_V_eq h1222 h1226 h331
  have hVL : V ≤ L := s.d.v_le_lt.trans (Set77.lt_le_L : Lt L t ≤ L)
  have hcardV : Nat.card ↥V = 2 ^ 6 := (S127.card_eq_of_1222 h1222 hyp).2.1
  have h1080 : Nat.card (autOn L V) = 1080 := S127.card_autOn_L hyp.hatA6 hLV
  have hrel : V.relIndex L = 1080 := by
    have h := card_autOn_eq_relIndex hLV
    rw [hCV, inf_eq_right.2 hVL, h1080] at h
    exact h.symm
  have hL : Nat.card ↥L = 69120 := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := L)
    rw [inf_eq_left.2 hVL, hrel, hcardV] at h
    rw [← h]
    norm_num
  have hLt : Lt L t ≤ Subgroup.centralizer ({t} : Set G) ⊓ L := by
    refine le_inf ?_ (Set77.lt_le_L : Lt L t ≤ L)
    exact s.d.lt_le.trans (inf_le_right.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 s.d.mem_vt)))
  have hcard : 3840 ≤ Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ L) := by
    rw [← s.card_Lt]
    exact Subgroup.card_le_of_le hLt
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({t} : Set G)) (K := L)
  have hle18 : (Subgroup.centralizer ({t} : Set G)).relIndex L ≤ 18 := by
    have h1 := Nat.mul_le_mul_left ((Subgroup.centralizer ({t} : Set G)).relIndex L) hcard
    omega
  obtain ⟨z, -, t₀, -, h45, h18, horb⟩ := S127.orbits_of_1222 h1222 hyp
  rcases horb t s.d.mem s.d.ne_one with ⟨l, hl, hlt⟩ | ⟨l, hl, hlt⟩
  · exfalso
    have h := relIndex_centralizer_conj hl (x := t)
    rw [hlt, h45] at h
    omega
  · have h := relIndex_centralizer_conj hl (x := t)
    rw [hlt, h18] at h
    omega

theorem mLine_codes {L : Subgroup G} {t : G} {W H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (V : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCV : Subgroup.centralizer (V : Set G) = V) (hV64 : Nat.card ↥V = 64)
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {Γ : List B6} (hΓ : mCheck Γ () = true)
    (hΓ1 : ∀ a ∈ autOn H V, C.cB a ∈ Γ) (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn H V, C.cB a = B)
    (hWH : W ≤ H) (hW : IsElemAbelian 2 W) (hW64 : Nat.card W = 64) (hWV : W ≠ V)
    (hWV16 : Nat.card ↥(W ⊓ V) = 16) (hVtW : Vt L t ≤ W ⊓ V) (htV : t ∈ V)
    (htVt : t ∈ Vt L t) (hVtV : Vt L t ≤ V) (hVtcard : Nat.card ↥(Vt L t) = 4)
    (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    (∀ W' : Subgroup G, W' ≤ H ⊓ Subgroup.centralizer ((W ⊓ V : Subgroup G) : Set G) →
      IsElemAbelian 2 W' → Nat.card W' = 64 → W' = V ∨ W' = W) ∧
    (∃ g ∈ H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G),
      g * t * g⁻¹ ∈ W ⊓ V ∧ g * t * g⁻¹ ∉ Vt L t) ∧
    ∃ z₀ ∈ W ⊓ V, (Subgroup.centralizer ({z₀} : Set G)).relIndex L = 45 ∧
      9 ≤ (Subgroup.centralizer ({z₀} : Set G)).relIndex
        (H ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G)) := by
  classical
  obtain ⟨w₀, hw₀W, hw₀V⟩ : ∃ w ∈ W, w ∉ V := by
    by_contra hno
    push Not at hno
    exact hWV (Subgroup.eq_of_le_of_card_ge (fun x hx => hno x hx)
      (le_of_eq (by rw [hV64, hW64])))
  have hww₀ : w₀ * w₀ = 1 := by
    rw [← pow_two]
    exact hW.2 w₀ hw₀W
  obtain ⟨hDl, hDllen⟩ := codes_fixList hH hW hWH hWV16 hCV hΓ hΓ1 hw₀W hw₀V
  have hDlt : ∀ d ∈ fixList (C.cB (conjAct V ⟨w₀, hH (hWH hw₀W)⟩)), d < 64 :=
    fun d hd => (mem_fixList.1 hd).1
  have hB₀Γ : C.cB (conjAct V ⟨w₀, hH (hWH hw₀W)⟩) ∈ Γ :=
    hΓ1 _ ((A4.mem_autOn_iff hH).2 ⟨⟨w₀, hWH hw₀W⟩, rfl⟩)
  have hB₀inv : isInv (C.cB (conjAct V ⟨w₀, hH (hWH hw₀W)⟩)) = true :=
    isInv_cB C (conjAct_sq_one _ hww₀) (conjAct_ne_one _ hw₀V hCV)
  have hperd := mCheck_perD hΓ hB₀Γ hB₀inv hDllen
  have hle3 := hperd.1
  obtain ⟨hlen3, hT⟩ := invs_three hH hW hWH hWV16 hW64 hCV hΓ1 hDl hDlt hle3
  have hperd2 := hperd.2 hlen3
  refine ⟨M1_part hH hW hWH hW64 hWV16 hV64 hCV hV2 hΓ hΓ1 hDl hDlt hT ⟨w₀, hw₀W, hw₀V⟩,
    M2_part hH hLV hC htV htVt hVtW hVtV hVtcard h18 hΓ2 hDl (nodup_fixList _)
      ⟨hperd2.1, hperd2.2.1⟩, ?_⟩
  exact M3_part hH hLV hC hΓ2 hDl hDlt hperd2.2.2

end Aux

theorem mLine1277_holds
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) :
    MLine1277 := by
  intro G _ _ T L V t s W hW hW64 hWN hWV hWV16 hVtW
  have hyp := s.d.hyp
  haveI : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (s.d.comm a a.2 b b.2)⟩⟩
  have hNLV : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) :=
    mEqNormV1277_of h331 h1222 h1226 G T L V t s
  have hH : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNLV.le
  have hCV : Subgroup.centralizer (V : Set G) = V := s.centralizer_V_eq h1222 h1226 h331
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hH
  have hV64 : Nat.card ↥V = 64 := s.d.card_V.trans (by norm_num)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => S127.sq_eq_one_of_mem hyp.hyp hx
  have h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 :=
    relIndex18_of_set77 s h331 h1222 h1226
  obtain ⟨C, hC⟩ : ∃ C : Coding ↥V, IdentL C (autOn L V) := exists_identL_G h1222 hyp
  have hMV : hyp.hyp.MVbar = autOn (Subgroup.normalizer (L : Set G)) V := by
    show autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = _
    rw [inf_eq_left.2 hH]
  obtain ⟨hgm, hnm⟩ := Certificates.certificate589101
  have hVtV : Vt L t ≤ V := s.d.vt_le
  have hVtcard : Nat.card ↥(Vt L t) = 4 := s.d.card_Vt
  have htV : t ∈ V := s.d.mem
  have htVt : t ∈ Vt L t := s.d.mem_vt
  by_cases hM : hyp.hyp.MVbar = autOn L V
  ·
    have hAut : autOn (Subgroup.normalizer (L : Set G)) V = autOn L V := hMV.symm.trans hM
    exact mLine_codes hH hLV hCV hV64 hV2 hC hgm
      (fun a ha => by
        rw [hAut] at ha
        exact (hC.1 a).1 ha)
      (fun B hB => by
        obtain ⟨a, ha⟩ := hC.2 B hB
        exact ⟨a, by rw [hAut]; exact (hC.1 a).2 (by rw [ha]; exact hB), ha⟩)
      hWN hW hW64 hWV hWV16 hVtW htV htVt hVtV hVtcard h18
  ·
    exact mLine_codes hH hLV hCV hV64 hV2 hC hnm
      (fun a ha => by
        rw [← hMV] at ha
        exact (MVbar_code hyp hC ha).1)
      (fun B hB => by
        obtain ⟨a, ha, hBa⟩ := MVbar_surj hyp hC hM B hB
        exact ⟨a, by rw [← hMV]; exact ha, hBa⟩)
      hWN hW hW64 hWV hWV16 hVtW htV htVt hVtV hVtcard h18

end CFSG.Quasithin.H13.I1277

end
