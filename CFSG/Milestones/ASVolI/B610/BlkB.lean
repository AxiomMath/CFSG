module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B19Final
public import CFSG.Quasithin.Background.E2SolvBlocks

public section

namespace CFSG.Quasithin.B610T.TwoBlk

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_le_normalizer_preI {V H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : ∀ g ∈ autI hV H, g ∈ Subgroup.normalizer (B : Set (MulAut (IntMod V hV)))) :
    H ≤ Subgroup.normalizer (preI hV H hHN B : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ preI hV H hHN B, g * x * g⁻¹ ∈ preI hV H hHN B := by
    intro g hg x hx
    obtain ⟨hxH, hxB⟩ := (mem_preI hV).1 hx
    have hgxH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg)
    refine (mem_preI hV).2 ⟨hgxH, ?_⟩
    have hgB := hB _ (convI_mem_autI hV hg (hHN hg))
    have h1 := (Subgroup.mem_normalizer_iff.mp hgB _).mp hxB
    have h2 : convHom hV H hHN ⟨g * x * g⁻¹, hgxH⟩ =
        convHom hV H hHN ⟨g, hg⟩ * convHom hV H hHN ⟨x, hxH⟩ * (convHom hV H hHN ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (H.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem burnsideB610_ffJP_le {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) :
    ffJP {A | IsFFStarMin X A} X ≤ X :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hAX => hAX

theorem burnsideB610_mem_normalizer_ffJP {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    (hstab : IsStableFF X {A | IsFFStarMin X A}) :
    ∀ g ∈ X, g ∈ Subgroup.normalizer
      (ffJP {A | IsFFStarMin X A} X : Set (MulAut W)) := by
  refine B19.mem_normalizer_of_map_conj_le fun g hg => ?_
  rw [ffJP, Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hAX => ?_
  refine B19.le_ffJP (hstab.2.2.1 A hA g hg) ?_
  rintro _ ⟨a, ha, rfl⟩
  have := X.mul_mem (X.mul_mem hg (hAX ha)) (X.inv_mem hg)
  simpa [MulAut.conj_apply] using this

theorem burnsideB610_not_mem_centralizer_ffJP [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    {x : MulAut (IntMod V hV)} (hxK : x ∈ autI hV (twoResidual H)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1)
    (hcard : Nat.card (commSub (⊤ : Subgroup (IntMod V hV)) (Subgroup.zpowers x)) = 4) :
    x ∉ Subgroup.centralizer
      (ffJP {A | IsFFStarMin (autI hV H) A} (autI hV H) : Set (MulAut (IntMod V hV))) := by
  intro hxC
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hFF : IsFFModule (autI hV H) :=
    hMP.isFFModule_autOn_of_not_commutator_eq_bot hred (E2.commutator_ne_bot hJ)
  have hstab := B1_7 hW hFF
  set J := ffJP {A | IsFFStarMin (autI hV H) A} (autI hV H) with hJdef
  have hJfix : J ≤ centSub (commSub ⊤ (Subgroup.zpowers x)) := by
    refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAX => ?_
    intro a ha
    have haJ : a ∈ J := B19.le_ffJP hA hAX ha
    have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a haJ
    have ha2 : a * a = 1 := by
      rw [← pow_two]
      exact hA.1.2.2.1.2 a ha
    exact B19.fix_of_comm_sq hW hx3 hx1 hcard ha2 hcomm.symm
  have hJX : J ≤ autI hV H := burnsideB610_ffJP_le _
  set Y := preI hV H hHN J with hY
  have hYH : Y ≤ H := preI_le hV
  have hYJ : autI hV Y = J := autI_preI hV hJX
  have hYn : H ≤ Subgroup.normalizer (Y : Set G) :=
    burnsideB610_le_normalizer_preI hV hHN (burnsideB610_mem_normalizer_ffJP hstab)
  rcases hMP.le_kerIn_or_twoResidual_le hYH hYn with hYk | hKY
  ·
    have hJk : J ≤ autI hV (kerIn M H) := by
      rw [← hYJ]
      exact autI_mono hV hYk
    obtain ⟨A₀, hA₀⟩ := hstab.1
    have hA₀J : A₀ ≤ J := B19.le_ffJP hA₀ hA₀.1.1
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA₀.1.2.1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha2 : a * a = 1 := by
      rw [← pow_two]
      exact hA₀.1.2.2.1.2 a haA
    exact ha1' (B19.eq_one_of_sq_of_odd (E2.odd_card_autI_kerIn hMP hred) (hJk (hA₀J haA)) ha2)
  ·
    have hxJ : x ∈ J := by
      rw [← hYJ]
      exact autI_mono hV hKY hxK
    have hfix := hJfix hxJ
    obtain ⟨-, -, -, hfpf, -⟩ := B19.zpowers_three_decomp hW hx3
    have hbot : commSub (⊤ : Subgroup (IntMod V hV)) (Subgroup.zpowers x) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 fun m hm => hfpf m hm (hfix m hm)
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard

theorem burnsideB610_exists_tv {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X Φ : Subgroup (MulAut W)} (hS : B19.Setting X Φ) {x : MulAut W} (hxΦ : x ∈ Φ)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcard : Nat.card (commSub (⊤ : Subgroup W) (Subgroup.zpowers x)) = 4)
    (hxJ : x ∉ Subgroup.centralizer (ffJP {A | IsFFStarMin X A} X : Set (MulAut W))) :
    ∃ t ∈ B19.tvSet X Φ, x ∈ B19.FOf Φ t := by
  by_contra hno
  push Not at hno
  have hfixF : ∀ t ∈ B19.tvSet X Φ, ∀ m ∈ commV (B19.FOf Φ t), x m = m := by
    intro t ht
    obtain ⟨y, w, h⟩ := hS.exists_tvBlock hW ht
    have hnot : x ∉ Subgroup.zpowers y := by
      rw [← h.FOf_eq]
      exact hno t ht
    rw [h.FOf_eq, commV_eq_commSub]
    exact (B1.commuting_fixes hW (h.central x hxΦ).symm h.x3 hx3 h.x1 hx1 h.card_commSub hcard
      hnot).1
  have hfixW : ∀ m ∈ commV (B19.FAll X Φ), x m = m := by
    have hle : commV (B19.FAll X Φ) ≤ fixV (Subgroup.zpowers x) := by
      rw [B19.commV_FAll]
      exact iSup₂_le fun t ht m hm => B1.zpowers_fix (hfixF t ht m hm)
    exact fun m hm => hle hm x (Subgroup.mem_zpowers x)
  set J := ffJP {A | IsFFStarMin X A} X with hJdef
  have hN : Φ ⊓ Subgroup.centralizer (J : Set (MulAut W)) ≤
      Subgroup.normalizer (B19.FAll X Φ : Set (MulAut W)) := by
    intro g hg
    have hgX : g ∈ X := hS.le hg.1
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => hS.conj_mem_FAll hgX hf, fun hf => ?_⟩
    have := hS.conj_mem_FAll (X.inv_mem hgX) hf
    simpa [mul_assoc] using this
  have hxmem : x ∈ ((B19.FAll X Φ ⊔ (Φ ⊓ Subgroup.centralizer (J : Set (MulAut W))) :
      Subgroup (MulAut W)) : Set (MulAut W)) := hS.le_FAll_sup hW hxΦ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hxmem
  obtain ⟨f, hf, c, hc, hfc⟩ := hxmem
  replace hfc : f * c = x := hfc
  have hcfix : ∀ m ∈ commV (B19.FAll X Φ), c m = m := by
    have hle : commV (B19.FAll X Φ) ≤ fixV (Subgroup.zpowers c) := by
      rw [B19.commV_FAll]
      refine iSup₂_le fun t ht m hm => B1.zpowers_fix ?_
      refine hS.fix_of_comm hW ht (fun z hz => ?_) ?_ m hm
      · exact (hS.FOf_central hW ht z hz c hc.1).symm
      · exact (Subgroup.mem_centralizer_iff.mp hc.2 t (hS.GOf_le_ffJP hW ht B19.mem_GOf)).symm
    exact fun m hm => hle hm c (Subgroup.mem_zpowers c)
  have hf1 : f = 1 := by
    obtain ⟨hsup, -⟩ := hS.decomp_FAll hW
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV (B19.FAll X Φ) ⊔ commV (B19.FAll X Φ) := by
      rw [hsup]
      trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
    have hfw : f w = w := by
      have h1 : x w = f (c w) := by rw [← hfc, MulAut.mul_apply]
      rw [hcfix w hw, hfixW w hw] at h1
      exact h1.symm
    rw [map_mul, hu f hf, hfw]
    rfl
  apply hxJ
  rw [← hfc, hf1, one_mul]
  exact hc.2

end CFSG.Quasithin.B610T.TwoBlk
