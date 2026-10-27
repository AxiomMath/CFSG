module

public import CFSG.Quasithin.Background.E6TenBlock
public import CFSG.Quasithin.Background.E6SixSeven
public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.Quasithin.EmptyFaithful.T1515cB
public import CFSG.Quasithin.H13.VolIC129Holds

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_centralizer_of {U : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (U : Set G)) :
    s ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  have key : ∀ t ∈ Subgroup.normalizer (U : Set G), ∀ x ∈ Subgroup.centralizer (U : Set G),
      t * x * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro t ht x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hu' : t⁻¹ * u * t ∈ U := (Subgroup.mem_normalizer_iff''.1 ht u).1 hu
    have h1 := hx _ hu'
    calc u * (t * x * t⁻¹) = t * ((t⁻¹ * u * t) * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * u * t)) * t⁻¹ := by rw [h1]
      _ = t * x * t⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key s hs x, fun hx => ?_⟩
  have := key s⁻¹ (Subgroup.inv_mem _ hs) _ hx
  simpa [mul_assoc] using this

theorem inf_centerOf_ne_bot {T W : Subgroup G} (hT : IsPGroup 2 T) (hWT : W ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) : W ⊓ centerOf T ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (W.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTW
  have hne : W.subgroupOf T ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro h0
  apply hy1
  have hyW : (y : G) ∈ W := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have : (y : G) ∈ W ⊓ centerOf T := ⟨hyW, y.2, hyC⟩
  rw [h0, Subgroup.mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

omit [Finite G] in
theorem eq_one_of_mem_closure_blockU {𝓑 : Set (Subgroup G)}
    (hcomm : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → ⁅B₁, B₂⁆ = ⊥) (hZ : ∀ B ∈ 𝓑, blockZ B = ⊥)
    (hU : ∀ B ∈ 𝓑, blockU B ≤ B) {A : Set (Subgroup G)} (hA : A.Finite) :
    A ⊆ 𝓑 → ∀ w ∈ Subgroup.closure {x | ∃ B ∈ A, x ∈ blockU B},
      (∀ B ∈ A, w ∈ Subgroup.centralizer (B : Set G)) → w = 1 := by
  refine Set.Finite.induction_on (motive := fun A _ => A ⊆ 𝓑 →
    ∀ w ∈ Subgroup.closure {x | ∃ B ∈ A, x ∈ blockU B},
      (∀ B ∈ A, w ∈ Subgroup.centralizer (B : Set G)) → w = 1) A hA ?_ ?_
  · intro _ w hw _
    have h0 : {x : G | ∃ B ∈ (∅ : Set (Subgroup G)), x ∈ blockU B} = ∅ := by
      ext x
      simp
    rw [h0, Subgroup.closure_empty, Subgroup.mem_bot] at hw
    exact hw
  · intro B₁ A₀ hB₁ _ ih hsub w hw hwc
    have hB₁𝓑 : B₁ ∈ 𝓑 := hsub (Set.mem_insert _ _)
    have hA₀𝓑 : A₀ ⊆ 𝓑 := fun B hB => hsub (Set.mem_insert_of_mem _ hB)
    set Y := Subgroup.closure {x : G | ∃ B ∈ A₀, x ∈ blockU B} with hYdef
    have hgen : {x : G | ∃ B ∈ insert B₁ A₀, x ∈ blockU B} =
        (blockU B₁ : Set G) ∪ {x : G | ∃ B ∈ A₀, x ∈ blockU B} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_union, SetLike.mem_coe]
      constructor
      · rintro ⟨B, rfl | hB, hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨B, hB, hx⟩
      · rintro (hx | ⟨B, hB, hx⟩)
        · exact ⟨B₁, Or.inl rfl, hx⟩
        · exact ⟨B, Or.inr hB, hx⟩
    rw [hgen, Subgroup.closure_union, Subgroup.closure_eq] at hw
    have hYC : Y ≤ Subgroup.centralizer (B₁ : Set G) := by
      rw [Subgroup.closure_le]
      rintro x ⟨B, hB, hx⟩
      have hne : B₁ ≠ B := fun he => hB₁ (he ▸ hB)
      have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer).1
        (hcomm B₁ hB₁𝓑 B (hA₀𝓑 hB) hne)
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.1 (h1 hb) x (hU B (hA₀𝓑 hB) hx)).symm
    have hBN : blockU B₁ ≤ Subgroup.normalizer (Y : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hYC hy) u (hU B₁ hB₁𝓑 hu)).symm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hw
    obtain ⟨u, hu, y, hy, huy⟩ := hw
    have huy' : u * y = w := huy
    have hyc : y ∈ Subgroup.centralizer (B₁ : Set G) := hYC hy
    have huc : u ∈ Subgroup.centralizer (B₁ : Set G) := by
      have h1 := Subgroup.mul_mem _ (hwc B₁ (Set.mem_insert _ _)) (Subgroup.inv_mem _ hyc)
      rwa [← huy', mul_inv_cancel_right] at h1
    have hu1 : u = 1 := by
      have : u ∈ blockZ B₁ := ⟨hu, huc⟩
      rw [hZ B₁ hB₁𝓑, Subgroup.mem_bot] at this
      exact this
    have hwy : w = y := by rw [← huy', hu1, one_mul]
    subst hwy
    exact ih hA₀𝓑 w hy fun B hB => hwc B (Set.mem_insert_of_mem _ hB)

end E6

namespace H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E6

theorem ch6InE610Four_proved
    : Ch6InE610Four := by
  intro G _ _ T M V U h hU hm hor
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  obtain ⟨hUV, hU1, hHM, hres⟩ := hU
  have hU' : U ∈ gammaE64 V M := ⟨hUV, hU1, hHM, hres⟩
  have hH : QuasithinUnique.CharTwo H := by
    rcases hor with hZ | hC
    · refine as_E_6_6_four_proved G T M V U h ⟨hU1, hUV, hHM, hres⟩ ?_
      rwa [inf_comm] at hZ
    · exact hC
  have hQsyl : IsSylowTwoOf Q H := e6_5_one h hU'
  have hcgs : cgsIn H Q ≤ H ⊓ M := (e6_5_two h hU').1
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hH
    unfold QuasithinUnique.CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQsyl.1.trans h1)
  have hsq : IsSQTKIn H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ :=
    H13.VolI.asc129Statement_holds G H Q (H ⊓ M) hsq hH hQsyl hcgs inf_le_left
  obtain ⟨i, hiM⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hHM
    intro x hx
    obtain ⟨m, hm, y, hy, rfl⟩ := hprod x hx
    refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hall j (hy j)
  set L := Lb i with hLdef
  have hLblock : IsBlock2 H L := (hLb i).1.1
  have hLH : L ≤ H := hLblock.2.1
  have hKN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU').2
  have hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 := by
    have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
    have hUi : U.relIndex V = 2 := by
      have := E3.relIndex_eq_two_pow h.isPGroup_V U
      rw [hm, pow_one] at this
      exact this
    rw [← hUi]
    exact Subgroup.relIndex_le_of_le_left hUC (by rw [hUi]; norm_num)
  have hZL : blockZ L = ⊥ := by
    rcases (hLb i).1.2 with ⟨n, hn, hlin⟩ | h3 | h5
    · exfalso
      apply hiM
      have hc := centralizes_of_lin2_block h.isElemAbelian h.le hQsyl
        (inf_le_left.trans h.inM.2) hKN hH hLblock hn hlin (hLb i).2.1 hidx
      intro l hl
      exact h.centralizer_le (Subgroup.mem_centralizer_iff.2 fun v hv => hc v hv l hl)
    · obtain ⟨-, -, -, -, -, hZc, -⟩ := IsShort2.alt3_structure hLblock.1 h3
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      refine hZc z (((C1.blockU_le_blockQ hLblock.1).trans (C1.blockQ_le L)) hz.1) fun l hl => ?_
      exact (Subgroup.mem_centralizer_iff.1 hz.2 l hl).symm
    · exact AppC.blockZ_eq_bot_of_alt5 hLblock.1 h5
  set S := T ⊓ Subgroup.normalizer (U : Set G) with hSdef
  have hSH : S ≤ Subgroup.normalizer (H : Set G) := fun s hs =>
    mem_normalizer_centralizer_of hs.2
  set 𝓑 : Set (Subgroup G) := (fun s => conjByElt s L) '' (S : Set G) with h𝓑def
  have h𝓑fin : 𝓑.Finite := Set.toFinite _
  have h𝓑blk : ∀ B ∈ 𝓑, IsBlock2 H B := by
    rintro _ ⟨s, hs, rfl⟩
    exact isBlock2_conjByElt_of_normalizer1515c hLblock (hSH hs)
  have h𝓑Z : ∀ B ∈ 𝓑, blockZ B = ⊥ := by
    rintro _ ⟨s, -, rfl⟩
    show blockZ (L.map (MulAut.conj s).toMonoidHom) = ⊥
    rw [Lin2.blockZ_map_equiv, hZL, Subgroup.map_bot]
  have h𝓑comm : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → ⁅B₁, B₂⁆ = ⊥ := fun B₁ h₁ B₂ h₂ hne =>
    distinctBlocksCommuteStatement H B₁ B₂ hH (h𝓑blk B₁ h₁) (h𝓑blk B₂ h₂) hne
  have h𝓑U : ∀ B ∈ 𝓑, blockU B ≤ B := fun B hB =>
    (C1.blockU_le_blockQ (h𝓑blk B hB).1).trans (C1.blockQ_le B)
  have hL𝓑 : L ∈ 𝓑 := ⟨1, S.one_mem, Subgroup.ext fun x => by rw [mem_conjByElt]; simp⟩
  set W := Subgroup.closure {x : G | ∃ B ∈ 𝓑, x ∈ blockU B} with hWdef
  have hUW : blockU L ≤ W := fun x hx => Subgroup.subset_closure ⟨L, hL𝓑, hx⟩
  have hW1 : W ≠ ⊥ := by
    intro h0
    have hlt := hLblock.1.2.2.2.2.1
    rw [show blockU L = ⊥ from le_bot_iff.1 (h0 ▸ hUW)] at hlt
    exact absurd hlt not_lt_bot
  have hQS : Q ≤ S := le_inf inf_le_left
    (inf_le_right.trans ((Subgroup.centralizer_le hUV).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hWS : W ≤ S := by
    rw [Subgroup.closure_le]
    rintro x ⟨B, hB, hx⟩
    have hb := h𝓑blk B hB
    have h1 : blockQ B ≤ pCoreOf 2 H :=
      Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hb.2.1 hb.2.2
    have h2 : pCoreOf 2 H ≤ Q := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQsyl
    exact hQS (h2 (h1 (C1.blockU_le_blockQ hb.1 hx)))
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ t ∈ S, ∀ x ∈ W, t * x * t⁻¹ ∈ W := by
      intro t ht x hx
      have hle : W ≤ W.comap (MulAut.conj t).toMonoidHom := by
        rw [hWdef, Subgroup.closure_le]
        rintro y ⟨B, ⟨s, hs, rfl⟩, hy⟩
        show (MulAut.conj t).toMonoidHom y ∈ W
        apply Subgroup.subset_closure
        refine ⟨conjByElt (t * s) L, ⟨t * s, S.mul_mem ht hs, rfl⟩, ?_⟩
        have e : conjByElt (t * s) L = (conjByElt s L).map (MulAut.conj t).toMonoidHom := by
          unfold conjByElt
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
        rw [e, Lin2.blockU_map_equiv]
        exact Subgroup.mem_map_of_mem _ hy
      have := hle hx
      simpa [MulAut.conj_apply] using this
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (S.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hWel : IsElemAbelian 2 W := by
    refine B2F.isElemAbelian_closure ?_ ?_
    · rintro a ⟨B₁, hB₁, ha⟩ b ⟨B₂, hB₂, hb⟩
      by_cases he : B₁ = B₂
      · subst he
        exact C1.blockU_comm (h𝓑blk B₁ hB₁).1 a ha b (C1.blockU_le_blockQ (h𝓑blk B₁ hB₁).1 hb)
      · have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (h𝓑comm B₁ hB₁ B₂ hB₂ he)
        exact (Subgroup.mem_centralizer_iff.1 (h1 (h𝓑U B₁ hB₁ ha)) b (h𝓑U B₂ hB₂ hb)).symm
    · rintro a ⟨B, hB, ha⟩
      exact C1.blockU_sq (h𝓑blk B hB).1 a ha
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le inf_le_left
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centerOf_ne_bot hS2 hWS hSW hW1)
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hwΩ : w ∈ omegaOneCenterOf S := Subgroup.subset_closure ⟨hw.2, hWel.2 w hw.1⟩
  intro hle
  have hwU := hle hwΩ
  apply hw1'
  refine eq_one_of_mem_closure_blockU h𝓑comm h𝓑Z h𝓑U h𝓑fin le_rfl w hw.1 fun B hB => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.1 ((h𝓑blk B hB).2.1 hb) w hwU).symm

end H13

end CFSG.Quasithin
