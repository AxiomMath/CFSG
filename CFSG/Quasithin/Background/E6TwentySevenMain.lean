module

public import CFSG.Quasithin.Background.E6TwentySeven
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E3Nprime

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ParabolicTorusFact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H S MH : Subgroup Γ), IsSimpleGroup Γ →
    (∃ a b : Γ, a * b ≠ b * a) → quasithinIsQTKECat Γ → pCoreOf 2 H ≠ ⊥ →
    MinParabolic H S MH → ¬ Group.IsSolvable ↥H → 1 < E1.nParam H →
      Group.IsSolvable ↥MH ∧ ∃ (c : ℕ) (B Y : Subgroup Γ), E1.nParam H ≤ c ∧ Y ≤ B ∧ B ≤ MH ∧
        (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧
        (B : Set Γ) * (S : Set Γ) = (S : Set Γ) * (B : Set Γ) ∧ IsCyclic ↥Y ∧
        Nat.card Y = 2 ^ c - 1 ∧
        ∀ A : Subgroup Γ, A ≤ Y → A ≠ ⊥ → ¬ H ⊓ Subgroup.normalizer (A : Set Γ) ≤ MH

section Images

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem card_autI {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autI hV K) = (K ⊓ Subgroup.centralizer (V : Set G)).relIndex K := by
  rw [autI_eq_autOn]
  exact card_autOn_eq_relIndex hK

theorem isSylowIn_autI {S X : Subgroup G} (hS : IsSylowTwoOf S X)
    (hX : X ≤ Subgroup.normalizer (V : Set G)) : IsSylowIn 2 (autI hV S) (autI hV X) := by
  have hSX := hS.1
  set C := Subgroup.centralizer (V : Set G) with hCdef
  refine ⟨autI_mono hV hSX, E3.isPGroup_autI hV (hSX.trans hX) hS.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (autI hV S) (autI hV X)
  rw [inf_eq_left.2 (autI_mono hV hSX), card_autI hV hX, card_autI hV (hSX.trans hX)] at h1
  have e1 := Subgroup.relIndex_mul_relIndex (S ⊓ C) (X ⊓ C) X (inf_le_inf_right _ hSX)
    inf_le_left
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ C) S X inf_le_left hSX
  have h2 : (X ⊓ C).relIndex X * (S ⊓ C).relIndex (X ⊓ C) =
      (S ⊓ C).relIndex S * S.relIndex X := by
    rw [mul_comm, e1, e2]
  have hdvd : (autI hV S).relIndex (autI hV X) ∣ S.relIndex X := by
    refine ⟨(S ⊓ C).relIndex (X ⊓ C), ?_⟩
    have hpos : 0 < (S ⊓ C).relIndex S := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' _ _)
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc (S ⊓ C).relIndex S * S.relIndex X = (X ⊓ C).relIndex X * (S ⊓ C).relIndex (X ⊓ C) :=
          h2.symm
      _ = (autI hV S).relIndex (autI hV X) * (S ⊓ C).relIndex S * (S ⊓ C).relIndex (X ⊓ C) := by
          rw [h1]
      _ = (S ⊓ C).relIndex S *
          ((autI hV S).relIndex (autI hV X) * (S ⊓ C).relIndex (X ⊓ C)) := by ring
  exact fun h => hS.2.2 (h.trans hdvd)

omit [Finite G] in
theorem autI_mul_comm {B S : Subgroup G} (hB : B ≤ Subgroup.normalizer (V : Set G))
    (hS : S ≤ Subgroup.normalizer (V : Set G))
    (hBS : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) :
    (autI hV B : Set (MulAut (IntMod V hV))) * (autI hV S : Set _) =
      (autI hV S : Set _) * (autI hV B : Set _) := by
  set N := Subgroup.normalizer (V : Set G)
  have himg : ∀ X : Subgroup G, X ≤ N →
      ((X.subgroupOf N : Subgroup ↥N) : Set ↥N).image N.subtype = (X : Set G) := by
    intro X hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hX hx⟩, hx, rfl⟩
  have hBS' : ((B.subgroupOf N : Subgroup ↥N) : Set ↥N) * (S.subgroupOf N : Subgroup ↥N) =
      ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) * (B.subgroupOf N : Subgroup ↥N) := by
    apply Set.image_injective.2 N.subtype_injective
    rw [Set.image_mul, Set.image_mul, himg B hB, himg S hS, hBS]
  have e : ∀ X : Subgroup G, (autI hV X : Set (MulAut (IntMod V hV))) =
      (convI hV) '' ((X.subgroupOf N : Subgroup ↥N) : Set ↥N) := fun X => by
    rw [autI, Subgroup.coe_map]
  rw [e B, e S, ← Set.image_mul, ← Set.image_mul, hBS']

omit [Finite G] in
theorem autI_cyclic {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V : Set G))
    (hYV : Y ⊓ Subgroup.centralizer (V : Set G) = ⊥) (hYc : IsCyclic ↥Y) :
    IsCyclic ↥(autI hV Y) ∧ Nat.card ↥(autI hV Y) = Nat.card Y := by
  refine ⟨?_, by rw [card_autI hV hY, hYV, Subgroup.relIndex_bot_left]⟩
  set N := Subgroup.normalizer (V : Set G)
  have hYc' : IsCyclic ↥(Y.subgroupOf N) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hY).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hY).symm.surjective
  let f : ↥(Y.subgroupOf N) →* ↥(autI hV Y) :=
    ((convI hV).comp (Y.subgroupOf N).subtype).codRestrict (autI hV Y)
      (fun y => Subgroup.mem_map_of_mem _ y.2)
  refine isCyclic_of_surjective f ?_
  rintro ⟨φ, ⟨y, hy, rfl⟩⟩
  exact ⟨⟨y, hy⟩, rfl⟩

end Images

theorem le_of_parabolics {X S M : Subgroup G} (hSX : IsSylowTwoOf S X) (hSM : S ≤ M)
    (hNS : Subgroup.normalizer (S : Set G) ≤ M)
    (hpar : ∀ P ∈ uFamHat (conjClosure S X) S, P ≤ M) : X ≤ M := by
  set K₁ := conjClosure S X with hK₁def
  have hK₁X : K₁ ≤ X :=
    conjClosure_le fun k hk s hs => X.mul_mem (X.mul_mem hk (hSX.1 hs)) (X.inv_mem hk)
  have hSK₁ : S ≤ K₁ := le_conjClosure S X
  have hSsyl : IsSylowTwoOf S K₁ := A4.isSylowTwoOf_mono hSX hSK₁ hK₁X
  have hXN : X ≤ Subgroup.normalizer (K₁ : Set G) := le_normalizer_conjClosure S X
  have hfrat : X ≤ K₁ ⊔ (X ⊓ Subgroup.normalizer (S : Set G)) :=
    le_sup_normalizer_of_isSylowTwoOf hSsyl hK₁X hXN
  have hK₁M : K₁ ≤ M := by
    rcases eq_or_lt_of_le hSK₁ with heq | hlt
    · exact heq ▸ hSM
    · have hcl : conjClosure S K₁ = K₁ := by
        refine le_antisymm (conjClosure_le fun k hk s hs =>
          K₁.mul_mem (K₁.mul_mem hk (hSK₁ hs)) (K₁.inv_mem hk)) ?_
        refine conjClosure_le fun k hk s hs => ?_
        have hk' := hfrat hk
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K₁ _
          (inf_le_left.trans hXN)] at hk'
        obtain ⟨a, ha, b, hb, rfl⟩ := hk'
        have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hb.2 s).1 hs
        have e : a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
        rw [e]
        exact mem_conjClosure ha hbs
      have hgen := uHat_eq_of_conjClosure_eq hSK₁ (by rw [hcl]; exact hlt) hcl
      rw [← hgen]
      exact iSup₂_le fun P hP => hpar P hP
  calc X ≤ K₁ ⊔ (X ⊓ Subgroup.normalizer (S : Set G)) := hfrat
    _ ≤ M := sup_le hK₁M (inf_le_right.trans hNS)

theorem inf_centralizer_le_normalizer_of_le {T M V U : Subgroup G} (h : HypE61 T M V)
    (hU1 : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rintro g ⟨hgM, hgU⟩
  by_contra hgN
  apply hU1
  rw [eq_bot_iff, ← h.tiSet.2 g hgM hgN]
  intro u hu
  refine ⟨hUV hu, ?_⟩
  show u ∈ conjSubgroup V g
  rw [mem_conjSubgroup_iff]
  have hc : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hgU u hu).symm
  have : g * u * g⁻¹ = u := by rw [hc, mul_inv_cancel_right]
  rw [this]
  exact hUV hu

theorem e6_27 (hPT : ParabolicTorusFact) {T M V U : Subgroup G} (h : HypE61 T M V)
    (hU1 : U ≠ ⊥) (hUV : U ≤ V) {j : ℕ} (hj : 0 < j) (hr : (j : ℕ∞) < E3.rParam V)
    (h2 : H13.thompsonJk j (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G))
    (h3 : E3.nPrime (autI h.isElemAbelian (M ⊓ Subgroup.centralizer (U : Set G))) ≤ j)
    (h4 : ∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer (V : Set G) → X ≠ ⊥ →
      (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) → Odd (Nat.card X) →
        Subgroup.normalizer (X : Set G) ≤ M) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hV := h.isElemAbelian
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set CMU := M ⊓ Subgroup.centralizer (U : Set G) with hCMUdef
  set MV := M ⊓ Subgroup.normalizer (V : Set G) with hMVdef
  have hQsyl : IsSylowIn 2 Q (M ⊓ Subgroup.centralizer (V : Set G)) := h.isSylowIn_centralizer
  have hCVU : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.centralizer_le hUV
  have hQCMU : Q ≤ CMU := le_inf (inf_le_left.trans h.inM.2) (inf_le_right.trans hCVU)
  obtain ⟨S, hS, hQS⟩ := A4.exists_isSylowTwoOf_ge hQCMU (h.isPGroup_Q)
  have hCN : CMU ≤ Subgroup.normalizer (V : Set G) := inf_centralizer_le_normalizer_of_le h hU1 hUV
  have hSMV : S ≤ MV := le_inf (hS.1.trans inf_le_left) (hS.1.trans hCN)
  have hTMV : IsSylowTwoOf T MV :=
    A4.isSylowTwoOf_mono h.isSylowIn_normalizer (le_inf h.inM.2 h.normal) inf_le_right
  obtain ⟨T', hT', hST'⟩ := A4.exists_isSylowTwoOf_ge hSMV hS.2.1
  obtain ⟨g, hgMV, hgT⟩ := B6.isSylowTwoOf_exists_conj hTMV hT'
  have hT'syl : quasithinIsSylowTwo T' := by
    refine ⟨hT'.2.1, ?_⟩
    have e : T'.index = T.index := by
      rw [hgT]
      exact Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).bijective T
    rw [e]
    exact h.sylow.2
  have hVMV : V ≤ MV := le_inf h.tiSet.1 Subgroup.le_normalizer
  have hVT' : V ≤ T' := IsSylowIn.le_of_normal (p := 2) hT' hVMV
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVMV).2 inf_le_right) h.isPGroup_V
  have hT'Q : T' ⊓ Subgroup.centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf (hQS.trans hST') inf_le_right)
    have h1 : T' ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
      inf_le_inf_right _ (hT'.1.trans inf_le_left)
    exact (A4.isSylowTwoOf_iff_maximal.1 hQsyl).2.2 _ h1 (hT'.2.1.to_le inf_le_left)
      (le_inf (hQS.trans hST') inf_le_right)
  have h' : HypE61 T' M V :=
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := h.qtke
      sylow := hT'syl
      inM := ⟨h.inM.1, hT'.1.trans inf_le_left⟩
      ne_bot := h.ne_bot
      isElemAbelian := h.isElemAbelian
      le := hVT'
      normal := hT'.1.trans inf_le_right
      tiSet := h.tiSet
      unique := by rw [hT'Q]; exact h.unique }
  have hSeq : T' ⊓ Subgroup.centralizer (U : Set G) = S := by
    refine le_antisymm ?_ (le_inf hST' (hS.1.trans inf_le_right))
    exact (A4.isSylowTwoOf_iff_maximal.1 hS).2.2 _
      (le_inf (inf_le_left.trans (hT'.1.trans inf_le_left)) inf_le_right)
      (hT'.2.1.to_le inf_le_left) (le_inf hST' (hS.1.trans inf_le_right))
  have hS' : IsSylowTwoOf (T' ⊓ Subgroup.centralizer (U : Set G)) CMU := by rw [hSeq]; exact hS
  have hJS : H13.thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (E5.thompsonJk_le j S)
      ((thompsonJk_le_of_isSylowTwoOf hS).trans (h2.trans inf_le_right))
  have hS2 : IsPGroup 2 S := hS.2.1
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := by
    have hJQ : thompsonJ S ≤ Q :=
      (thompsonJ_le_thompsonJk j S).trans (hJS.trans (le_inf (inf_le_left.trans
        (hST'.trans' le_rfl)) inf_le_right |>.trans (by rw [← hT'Q])))
    have hJ1 : thompsonJ S ≠ ⊥ := thompsonJ_ne_bot (hVQ.trans hQS) h.isElemAbelian h.ne_bot
    have hNJ := normalizer_thompsonJ_le h.isUniqueM_normalizer_Q hJQ hQS hS2 hJ1
    exact fun x hx => hNJ (E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hx))
  have hSM : S ≤ M := hS.1.trans inf_le_left
  have hSK : IsSylowTwoOf S (Subgroup.centralizer (U : Set G)) :=
    isSylowTwoOf_of_normalizer_le hS (hS.1.trans inf_le_right) hSM hNS
  have hQ'S : T' ⊓ Subgroup.centralizer (V : Set G) ≤ S := hT'Q ▸ hQS
  refine e6_27_of_parabolics h' hUV hj hr hS' h2 ?_
  rw [hSeq]
  intro H hH hn
  by_contra hHM
  obtain ⟨⟨hHK, hSH, hmax⟩, hHN⟩ := hH
  obtain ⟨MH, hMH⟩ := Set.ncard_eq_one.1 hmax
  have hHC : H ≤ Subgroup.centralizer (U : Set G) := by
    refine hHK.trans ?_
    rw [← conjClosure_eq_twoPrimeResidual hSK]
    exact conjClosure_le fun k hk s hs => Subgroup.mul_mem _ (Subgroup.mul_mem _ hk
      (hSK.1 hs)) (Subgroup.inv_mem _ hk)
  have hSHsyl : IsSylowTwoOf S H := A4.isSylowTwoOf_mono hSK hSH.le hHC
  have hmin : MinParabolic H S MH := ⟨hSHsyl, hHN, hMH⟩
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    have hUH : U ≤ H := (hUV.trans (hVQ.trans hQS)).trans hSH.le
    have hUO : U ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf 2 hUH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).2
        (hHC.trans (Subgroup.centralizer_le_normalizer _)))
      (h.isPGroup_V.to_le hUV)
    exact fun hb => hU1 (le_bot_iff.1 (hb ▸ hUO))
  have hn1 : 1 < E1.nParam H := lt_of_le_of_lt (by exact_mod_cast hj) hn
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd (E1.solvable_nParam_le_one hs) (not_le.2 hn1)
  obtain ⟨hMHs, c, B, Y, hc, hYB, hBMH, hBab, hBodd, hBS, hYcyc, hYcard, hNA⟩ :=
    hPT G H S MH h.simple h.nonabelian h.qtke hO2 hmin hns hn1
  have hMHH : MH ≤ H := (hMH ▸ Set.mem_singleton MH : MH ∈ maxOver H S).1.le
  have hSMH : S ≤ MH := (hMH ▸ Set.mem_singleton MH : MH ∈ maxOver H S).2
  have hMHM : MH ≤ M := by
    refine le_of_parabolics (A4.isSylowTwoOf_mono hSHsyl hSMH hMHH) hSM hNS fun P hP => ?_
    have hPMH : P ≤ MH := hP.1.1.trans (conjClosure_le fun k hk s hs =>
      MH.mul_mem (MH.mul_mem hk (hSMH hs)) (MH.inv_mem hk))
    have hPs : Group.IsSolvable ↥P := by
      have := hMHs
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPMH)
    have hSP : IsSylowTwoOf S P := A4.isSylowTwoOf_mono hSHsyl hP.1.2.1.le (hPMH.trans hMHH)
    exact (e6_26 h'.sylow.1 h.ne_bot h.isElemAbelian hVT' h.normalizer_le
      (by rw [hT'Q]; exact h.isUniqueM_normalizer_Q) hj
      ((E1.solvable_nParam_le_one hPs).trans (by exact_mod_cast hj)) hSP hQ'S hST' hr hJS).1
  have hMHle : M ⊓ H ≤ MH := by
    have hlt : M ⊓ H < H := lt_of_le_of_ne inf_le_right fun he => hHM (he ▸ inf_le_left)
    obtain ⟨N, hN, hMN⟩ := exists_isMaxSubgroupIn hlt
    have hNmem : N ∈ maxOver H S := ⟨hN, le_inf hSM hSH.le |>.trans hMN⟩
    rw [hMH] at hNmem
    exact (Set.mem_singleton_iff.1 hNmem) ▸ hMN
  have hBM : B ≤ CMU := le_inf (hBMH.trans hMHM) ((hBMH.trans hMHH).trans hHC)
  by_cases hYV : Y ⊓ Subgroup.centralizer (V : Set G) = ⊥
  ·
    have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBM.trans hCN
    obtain ⟨hYc', hYcard'⟩ := autI_cyclic hV ((hYB.trans hBN)) hYV hYcyc
    have hle := E3.le_nPrime (Y := autI hV Y) (B := autI hV B) (S := autI hV S) (c := c)
      (autI_mono hV hYB) (autI_mono hV hBM) hYc' (hYcard'.trans hYcard)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hBab _ hx _ hy))
      (by
        have h1 := Subgroup.card_map_dvd (B.subgroupOf (Subgroup.normalizer (V : Set G)))
          (convI hV)
        have h2 : Nat.card ↥(B.subgroupOf (Subgroup.normalizer (V : Set G))) = Nat.card B :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
        rw [h2] at h1
        exact Odd.of_dvd_nat hBodd h1)
      (isSylowIn_autI hV hS hCN)
      (autI_mul_comm hV hBN (hS.1.trans hCN) hBS)
    have hcj : c ≤ j := by exact_mod_cast hle.trans h3
    have hjc : (j : ℕ∞) < c := lt_of_lt_of_le hn hc
    exact absurd hcj (not_le.2 (by exact_mod_cast hjc))
  ·
    set A := Y ⊓ Subgroup.centralizer (V : Set G) with hAdef
    have hAM : A ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
      inf_le_inf_right _ ((hYB.trans hBMH).trans hMHM)
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
      hBab a (hYB ha.1) b (hYB hb.1)
    have hAodd : Odd (Nat.card A) :=
      Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le (inf_le_left.trans hYB))
    have hNAM := h4 A hAM hYV hAab hAodd
    exact hNA A inf_le_left hYV (le_trans (le_inf (inf_le_right.trans hNAM) inf_le_left) hMHle)

end E6
end CFSG.Quasithin
