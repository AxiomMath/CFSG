module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Family
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6F4
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Lv
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Loc
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Grp
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Props
import CFSG.RankThree.PartTwo.Sec21.FF81Sec52C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81F4Fusion
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec21.FF81.F4 (card_model_sp6)

section G

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem orderOf_b₁ (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) : orderOf b₁ = 3 := by
  have hne : b₁ ≠ 1 := fun h => by
    have := h5.ε_eq_one (h5.ε_e1.trans h)
    exact absurd (congrFun this 1) (by decide)
  exact orderOf_eq_prime h5.basis.b_facts.1 hne

theorem closure_le_nor_A₁ (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {t₁ : G} (ht₁L : t₁ ∈ L)
    (ht₁b : t₁ * b₁ * t₁⁻¹ = b₁⁻¹) (hc : t₁ * (b₂ * b₃) = (b₂ * b₃) * t₁) :
    Subgroup.closure ({b₁, t₁} : Set G) ≤ Nor (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)) := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    refine mem_nor_of_forall fun z hz => ?_
    have hle : Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) ≤
        (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hg with rfl | rfl | rfl
      · have : y * g = g * y :=
          (Subgroup.mem_centralizer_singleton_iff.1 (h5.basis.hyp.hLC ht₁L))
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.subset_closure (by simp)
      · rw [ht₁b]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.subset_closure (by simp)
    exact hle hz

omit [Finite G] in
theorem cen_le_range_of_card {F : Type} [Group F] (ψ : F →* G) (hψ : Function.Injective ψ)
    (x : F) [Finite G]
    (h : Nat.card ↥(Cen (ψ x)) ≤ Nat.card ↥(Cen x)) : Cen (ψ x) ≤ ψ.range := by
  have h1 : (Cen x).map ψ ≤ Cen (ψ x) ⊓ ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, ⟨y, rfl⟩⟩
    have hy' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hy'])
  have h2 : Nat.card ↥((Cen x).map ψ) = Nat.card ↥(Cen x) :=
    Subgroup.card_map_of_injective hψ
  have h3 : Cen (ψ x) ⊓ ψ.range = Cen (ψ x) := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    calc Nat.card ↥(Cen (ψ x)) ≤ Nat.card ↥(Cen x) := h
      _ = Nat.card ↥((Cen x).map ψ) := h2.symm
      _ ≤ Nat.card ↥(Cen (ψ x) ⊓ ψ.range) := Subgroup.card_le_of_le h1
  rw [← h3]
  exact inf_le_right

end G

section F


local instance am6NeZeroRankM : NeZero Tag.F4.rank := ⟨by decide⟩

local notation "𝔽₂" => GaloisField 2 1

theorem card_gf2 : Nat.card (GaloisField 2 1) = 2 := by
  have := GaloisField.card 2 1 (by norm_num)
  simpa using this

theorem card_Lv_single (j : Fin (Tag.rank .F4)) : Nat.card ↥(Lv 𝔽₂ {j}) = 6 := by
  rw [Lv_eq_rootSL2]
  exact card_rootSL2 card_gf2 (isRoot_single _ j)

theorem pimg_mono {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    {A A' : Subgroup ↥(adjointGroup .F4 𝔽₂)} (h : A ≤ A') : pimg 𝔽₂ θP A ≤ pimg 𝔽₂ θP A' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem pimg_le_range {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    (A : Subgroup ↥(adjointGroup .F4 𝔽₂)) : pimg 𝔽₂ θP A ≤ θP.range :=
  Subgroup.map_le_range _ _

theorem mem_pimg_iff {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    (A : Subgroup ↥(adjointGroup .F4 𝔽₂)) {y : G} :
    y ∈ pimg 𝔽₂ θP A ↔ ∃ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ B3Levi 𝔽₂), x ∈ A ∧
      θP ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1, z.2, hz, rfl⟩
  · rintro ⟨x, hx, hxA, rfl⟩
    exact ⟨⟨x, hx⟩, hxA, rfl⟩

theorem mem_pimg_of_mem {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    {A : Subgroup ↥(adjointGroup .F4 𝔽₂)} {x : ↥(adjointGroup .F4 𝔽₂)} (hx : x ∈ B3Levi 𝔽₂)
    (hxA : x ∈ A) : θP ⟨x, hx⟩ ∈ pimg 𝔽₂ θP A :=
  (mem_pimg_iff θP A).2 ⟨x, hx, hxA, rfl⟩

noncomputable def pimgEquiv {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    (hθ : Function.Injective θP) {A : Subgroup ↥(adjointGroup .F4 𝔽₂)} (hA : A ≤ B3Levi 𝔽₂) :
    ↥A ≃* ↥(pimg 𝔽₂ θP A) :=
  (Subgroup.subgroupOfEquivOfLe hA).symm.trans (Subgroup.equivMapOfInjective _ θP hθ)

theorem card_pimg {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G)
    (hθ : Function.Injective θP) {A : Subgroup ↥(adjointGroup .F4 𝔽₂)} (hA : A ≤ B3Levi 𝔽₂) :
    Nat.card ↥(pimg 𝔽₂ θP A) = Nat.card ↥A :=
  (Nat.card_congr (pimgEquiv θP hθ hA).toEquiv).symm

noncomputable def zeta2 : GaloisField 2 1 ≃+* ZMod 2 :=
  letI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  (ZMod.ringEquivOfPrime (GaloisField 2 1) Nat.prime_two
    (by rw [← Nat.card_eq_fintype_card]; exact card_gf2)).symm

theorem Lv_zero_le_zero_one : Lv 𝔽₂ {0} ≤ Lv 𝔽₂ {0, 1} :=
  CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 (by simp))

theorem Lv_one_le_zero_one : Lv 𝔽₂ {1} ≤ Lv 𝔽₂ {0, 1} :=
  CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 (by simp))

theorem Lv_zero_one_le_P : Lv 𝔽₂ {0, 1} ≤ B3Levi 𝔽₂ := Lv_le_B3Levi (by decide)

theorem ff81_6_amalgam'_of (hA : A2Piece (GaloisField 2 1)) (hL : LSide) :
    FF81_6_amalgam' := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 h526 M hM7 h58 h59
  obtain ⟨θP, hθinj, hθrange, hK4, ⟨t₁, hK₂eq, ht₁b, ht₁c⟩, hcardLK4, hcardK₂'⟩ :=
    hL G b L B b₁ b₂ b₃ t₀ s₀ h5
  have hB := h5.basis
  have h0 := h5.opp_eq_bot
  have hbord : orderOf b = 3 := hB.hyp.ord
  have hβord : orderOf (β' b₂ b₃) = 3 := h5.β_orderOf
  have hLmodel : StatedClassicalModel L .PSp 3 2 1 := hB.hyp.model
  have hMmodel : StatedClassicalModel M .PSp 3 2 1 := hM7.2.1
  have hcensK4 : CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G)) = M := cenS_K4_eq h5 hM7
  have hcensK0 : CenS (Subgroup.closure ({b, t₀} : Set G)) = L := cenS_K0_eq h5
  have hRL : pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) ≤ L := hθrange ▸ pimg_le_range θP _
  have hK4R : Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ≤ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) := by
    rw [← hK4]
    exact pimg_mono θP Lv_zero_le_zero_one
  have hRmodel : IsLnq 3 2 1 (pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1})) :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (pimgEquiv θP hθinj Lv_zero_one_le_P) (statedClassicalModel_Lv_zero_one card_gf2)
  have hX := h59 _ hRL hRmodel hK4R
  have hXM := cenS_le_M h5 hM7 hK4R
  have hK0X := K0_le_cenS h5 hRL
  have hK0M : Subgroup.closure ({b, t₀} : Set G) ≤ M := hK0X.trans hXM
  have hbM : b ∈ M := hK0M (Subgroup.subset_closure (by simp))
  have hK2le : pimg 𝔽₂ θP (Lv 𝔽₂ {2}) ≤ L := hθrange ▸ pimg_le_range θP _
  have hK2card : Nat.card ↥(pimg 𝔽₂ θP (Lv 𝔽₂ {2})) = 6 := by
    rw [card_pimg θP hθinj Lv_two_le_P, card_Lv_single]
  have hK2comm4 : ∀ z ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}), ∀ y ∈ Subgroup.closure ({β' b₂ b₃, s₀} : Set G),
      y * z = z * y := by
    intro z hz y hy
    rw [← hK4] at hy
    obtain ⟨v, hv, hvL, hvz⟩ := (mem_pimg_iff θP _).1 hz
    obtain ⟨u, hu, huL, huy⟩ := (mem_pimg_iff θP _).1 hy
    rw [← hvz, ← huy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_levi_zero_two u huL v hvL).eq
  have ht₁L : t₁ ∈ L := hK2le (hK₂eq ▸ Subgroup.subset_closure (by simp))
  have hb₁K₂ : b₁ ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}) := hK₂eq ▸ Subgroup.subset_closure (by simp)
  have hK2M : pimg 𝔽₂ θP (Lv 𝔽₂ {2}) ≤ M := by
    intro z hz
    have hz4 : z ∈ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hK2comm4 z hz y hy
    have hzA := closure_le_nor_A₁ h5 ht₁L ht₁b ht₁c (hK₂eq ▸ hz)
    exact hM7.2.2.2.2.2 ⟨hz4, hzA⟩
  have hK0iso : Nonempty (↥(Subgroup.closure ({b, t₀} : Set G)) ≃* Equiv.Perm (Fin 3)) :=
    nonempty_perm_three_closure hbord h5.ht₀ h5.ht₀b
  have hK0K2 : ∀ x ∈ Subgroup.closure ({b, t₀} : Set G), ∀ y ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}),
      Commute x y := by
    intro x hx y hy
    have hxL : x ∈ CenS L := K0_le_cenS h5 (le_refl L) hx
    exact (Subgroup.mem_centralizer_iff.1 hxL y (hK2le hy)).symm
  have hcard36 : Nat.card ↥(M ⊓ CenS (Subgroup.closure ({b, t₀} : Set G))) = 36 :=
    (card_M_inf_cenS_K0 h5 hM7).trans hcardLK4
  have hb₁ord : orderOf b₁ = 3 := orderOf_b₁ h5
  obtain ⟨m, hmM, hmb⟩ := exists_mem_M_conj_b h5 hM7
  have hML : Nat.card ↥(M ⊓ L) = 36 := by
    have h := hcard36
    rwa [hcensK0] at h
  have hcardb₁ : Nat.card ↥(M ⊓ Cen b₁) = 108 := by
    rw [← hmb, card_M_inf_cen_conj hmM, card_M_inf_cen_b h5 hbM, hML]
  have hK2'M : L ⊓ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ⊔
      pimg 𝔽₂ θP (Lv 𝔽₂ {2})) ≤ M := by
    intro w hw
    rw [← hcensK4]
    intro y hy
    exact Subgroup.mem_centralizer_iff.1 hw.2 y (Subgroup.mem_sup_left hy)
  have hK2'comm : ∀ z ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}), ∀ w ∈ L ⊓ CenS (Subgroup.closure
      ({β' b₂ b₃, s₀} : Set G) ⊔ pimg 𝔽₂ θP (Lv 𝔽₂ {2})), z * w = w * z := fun z hz w hw =>
    Subgroup.mem_centralizer_iff.1 hw.2 z (Subgroup.mem_sup_right hz)
  have hK0card : Nat.card ↥(Subgroup.closure ({b, t₀} : Set G)) = 6 := by
    have ht₀sq : t₀ * t₀ = 1 := by rw [← sq, ← h5.ht₀]; exact pow_orderOf_eq_one t₀
    exact card_closure_dihedral hbord ht₀sq h5.ht₀b
  have hK2card36 : Nat.card ↥(M ⊓ CenS (pimg 𝔽₂ θP (Lv 𝔽₂ {2}))) = 36 :=
    card_M_inf_cenS_K2 h5 hK₂eq ht₁b hK2le hK2M inf_le_left hK2'M hcardK₂' hK2'comm hK0M
      hK0card hb₁ord hcardb₁
  have hMcomm : ∀ m ∈ M, ∀ x ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0}), Commute m x := by
    intro m hm x hx
    rw [hK4] at hx
    have hm' : m ∈ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G)) := hM7.1 hm
    exact (Subgroup.mem_centralizer_iff.1 hm' x hx).symm
  obtain ⟨θA, hagree, hX3, hθAM⟩ := hA G θP hθinj M _ hMmodel hMcomm hK2M hX hXM hK0X hK0iso
    hK0K2 hcard36 hK2card36
  have hcomm0 : ∀ (a : ↥(Lv 𝔽₂ {0})) (c : ↥(Lv 𝔽₂ {3})),
      Commute (θP ⟨a.1, Lv_zero_le_P a.2⟩) (θA ⟨c.1, Lv_three_le_A c.2⟩) := by
    intro a c
    have h2 : θP ⟨a.1, Lv_zero_le_P a.2⟩ ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) :=
      mem_pimg_of_mem θP (Lv_zero_le_P a.2) (Lv_zero_le_zero_one a.2)
    exact Subgroup.mem_centralizer_iff.1 (hX3 c.1 c.2) _ h2
  have hcomm1 : ∀ (a : ↥(Lv 𝔽₂ {1})) (c : ↥(Lv 𝔽₂ {3})),
      Commute (θP ⟨a.1, Lv_one_le_P a.2⟩) (θA ⟨c.1, Lv_three_le_A c.2⟩) := by
    intro a c
    have h2 : θP ⟨a.1, Lv_one_le_P a.2⟩ ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) :=
      mem_pimg_of_mem θP (Lv_one_le_P a.2) (Lv_one_le_zero_one a.2)
    exact Subgroup.mem_centralizer_iff.1 (hX3 c.1 c.2) _ h2
  let D : FamilyData 𝔽₂ G := ⟨θP, θA, hagree, hcomm0, hcomm1⟩
  obtain ⟨ψ, hψinj, hψP, hψA, hψrange⟩ := D.exists_injective hθinj
  have hLY : L ≤ ψ.range := by
    rw [← hθrange]
    rintro _ ⟨z, rfl⟩
    exact ⟨z.1, hψP z.1 z.2⟩
  have hMβ : M ≤ Cen (β' b₂ b₃) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hM7.1 hm)
      (β' b₂ b₃) (Subgroup.subset_closure (by simp))).symm
  have hβmem : β' b₂ b₃ ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0}) := by
    rw [hK4]; exact Subgroup.subset_closure (by simp)
  obtain ⟨xβ, hxβB, hxβLv, hxβ⟩ := (mem_pimg_iff θP _).1 hβmem
  have hψxβ : ψ xβ = β' b₂ b₃ := by rw [hψP xβ hxβB]; exact hxβ
  have hxβ3 : orderOf xβ = 3 := by rw [← orderOf_injective ψ hψinj xβ, hψxβ, hβord]
  have hCenβ : Cen (β' b₂ b₃) ≤ ψ.range := by
    have h1 : Nat.card ↥(Cen (ψ xβ)) ≤ Nat.card ↥(Cen xβ) := by
      rw [hψxβ, card_cen_beta h5 hM7, card_model_sp6 hMmodel]
      refine card_cen_ge_of_mem_rootSL2 card_gf2 (isRoot_single _ 0) ?_ hxβ3
      rw [← Lv_eq_rootSL2]
      exact hxβLv
    have := cen_le_range_of_card ψ hψinj xβ h1
    rwa [hψxβ] at this
  have hMY : M ≤ ψ.range := fun m hm => hCenβ (hMβ hm)
  have hbY : b ∈ ψ.range := hMY hbM
  have hs₀mem : s₀ ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0}) := by
    rw [hK4]; exact Subgroup.subset_closure (by simp)
  obtain ⟨xs, hxsB, hxsLv, hxs⟩ := (mem_pimg_iff θP _).1 hs₀mem
  have hψxs : ψ xs = s₀ := by rw [hψP xs hxsB]; exact hxs
  have hxs2 : orderOf xs = 2 := by rw [← orderOf_injective ψ hψinj xs, hψxs, h5.hs₀]
  have hCens₀ : Cen s₀ ≤ ψ.range := by
    obtain ⟨-, -, -, ⟨S₀, S₁, hS₀, hS₁, hsup, hinf, hc⟩, -⟩ := h526
    have hMs₀ : M ≤ Cen s₀ := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hM7.1 hm) s₀
        (Subgroup.subset_closure (by simp))).symm
    have hcs := card_cen_of_decomp hMmodel hMs₀ hM7.2.2.1 hS₀ hS₁ hsup hinf hc
    have h1 : Nat.card ↥(Cen (ψ xs)) ≤ Nat.card ↥(Cen xs) := by
      rw [hψxs, hcs, card_cen_involution_of_mem_Lv zeta2 card_gf2 hxsLv hxs2]
    have := cen_le_range_of_card ψ hψinj xs h1
    rwa [hψxs] at this
  have hCent₀ : Cen t₀ ≤ ψ.range := by
    obtain ⟨hdec, T₀, T₁, hT₀, hT₁, hsup, hinf, hc⟩ := h58
    have hLt₀ : L ≤ Cen t₀ := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h5.ht₀L l hl)
    have hcardt₀ := card_cen_of_decomp hLmodel hLt₀ hdec hT₀ hT₁ hsup hinf hc
    have hK1X : (Lv 𝔽₂ {3}).map ψ ≤ CenS (pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1})) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hψA x (Lv_three_le_A hx)]
      exact hX3 x hx
    have hK1card : Nat.card ↥((Lv 𝔽₂ {3}).map ψ) = 6 := by
      rw [Subgroup.card_map_of_injective hψinj, card_Lv_single]
    have ht₀sq : t₀ * t₀ = 1 := by rw [← sq, ← h5.ht₀]; exact pow_orderOf_eq_one t₀
    have hK0card : Nat.card ↥(Subgroup.closure ({b, t₀} : Set G)) = 6 :=
      card_closure_dihedral hbord ht₀sq h5.ht₀b
    obtain ⟨g, hgX, hg⟩ := exists_conj_of_card_six hX hK0X hK1X hK0card hK1card
    have ht₀K1 : g * t₀ * g⁻¹ ∈ (Lv 𝔽₂ {3}).map ψ := by
      rw [← hg]
      exact ⟨t₀, Subgroup.subset_closure (by simp), by simp [MulAut.conj_apply]⟩
    obtain ⟨xt, hxtLv, hψxt⟩ := Subgroup.mem_map.1 ht₀K1
    have hxt2 : orderOf xt = 2 := by
      rw [← orderOf_injective ψ hψinj xt, hψxt]
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t₀
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this, h5.ht₀]
    have h1 : Nat.card ↥(Cen (ψ xt)) ≤ Nat.card ↥(Cen xt) := by
      rw [hψxt, show Nat.card ↥(Cen (g * t₀ * g⁻¹)) = Nat.card ↥(Cen t₀) from
        card_cen_equiv (MulAut.conj g) t₀, hcardt₀,
        card_cen_involution_of_mem_Lv zeta2 card_gf2 hxtLv hxt2]
    have h2 := cen_le_range_of_card ψ hψinj xt h1
    rw [hψxt] at h2
    have hgY : g ∈ ψ.range := hMY (hXM hgX)
    intro y hy
    have hy' : g * y * g⁻¹ ∈ Cen (g * t₀ * g⁻¹) := by
      have hy2 : y * t₀ = t₀ * y := Subgroup.mem_centralizer_singleton_iff.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * y * g⁻¹ * (g * t₀ * g⁻¹) = g * (y * t₀) * g⁻¹ := by group
        _ = g * (t₀ * y) * g⁻¹ := by rw [hy2]
        _ = g * t₀ * g⁻¹ * (g * y * g⁻¹) := by group
    have h3 := h2 hy'
    have hyeq : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [hyeq]
    exact ψ.range.mul_mem (ψ.range.mul_mem (ψ.range.inv_mem hgY) h3) hgY
  have hCenb : Cen b ≤ ψ.range := by
    intro x hx
    obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h0 hx
    exact ψ.range.mul_mem (ψ.range.zpow_mem hbY i) (hLY hl)
  have hBY : B ≤ ψ.range := by
    rw [h5.hcl, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl | rfl | hy
    · exact hbY
    · exact hLY hB.hb₁
    · exact hLY hB.hb₂
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hLY hB.hb₃
  have hYsup : ψ.range ≤ Cen b ⊔ Cen (β' b₂ b₃) := by
    rw [hψrange]
    refine sup_le ?_ ?_
    · exact (hθrange ▸ hB.hyp.hLC).trans le_sup_left
    · exact (hθAM.trans hMβ).trans le_sup_right
  exact ⟨ψ.range, hasLeviAmalgam_of_injective ψ hψinj, hCent₀, hCens₀, hCenb, hCenβ, hBY,
    le_antisymm (sup_le hCenb hCenβ) hYsup⟩

end F

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
