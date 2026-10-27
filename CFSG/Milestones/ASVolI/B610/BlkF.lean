module

public import CFSG.Milestones.ASVolI.B610.BlkE
public import CFSG.Milestones.ASVolI.B610.BlkB
public import CFSG.Milestones.ASVolI.B610.Targets

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace TwoBlk

variable {G : Type} [Group G]

theorem burnsideB610_le_of_isSubnormal {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B := by
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM _ _ ih => exact hAM.trans ih

variable [Finite G]

theorem burnsideB610_exists_FOf_eq {H T M V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hsub : IsSubnormal L H)
    (hnat : IsNaturalL2Prime 1 L V) :
    ∃ t ∈ B19.tvSet (autI hV H) (pCoreOf 3 (autI hV H)),
      autI hV L = B19.FOf (pCoreOf 3 (autI hV H)) t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hLH : L ≤ H := burnsideB610_le_of_isSubnormal hsub
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hred.2.1
  have hS := burnsideB610_setting (autI hV H)
  have hL3 := burnsideB610_card_autI_eq_three hV hLN hnat
  obtain ⟨x, hxL, hx3, hx1, hLx⟩ := burnsideB610_exists_gen hL3
  have hLΦ : autI hV L ≤ pCoreOf 3 (autI hV H) :=
    burnsideB610_le_pCoreOf_of_isSubnormal 3 (burnsideB610_isSubnormal_autI hV hsub)
      (IsPGroup.of_card (n := 1) (by rw [hL3]; norm_num))
  have hcf : commV (autI hV L) ⊓ fixV (autI hV L) = ⊥ := by
    rw [hLx, commV_eq_commSub, inf_comm]
    exact (B19.zpowers_three_decomp hW hx3).2.1
  have hinf := burnsideB610_inf_centralizer_eq_bot hV hLN hcf
  have h4 := burnsideB610_card_commutator_eq_four hnat hinf
  have hcard : Nat.card (commSub (⊤ : Subgroup (IntMod V hV)) (Subgroup.zpowers x)) = 4 := by
    rw [← commV_eq_commSub, ← hLx, ← burnsideB610_card_commutator hV hLN]
    exact h4
  have hxK : x ∈ autI hV (twoResidual H) :=
    burnsideB610_le_autI_twoResidual hV (autI_mono hV hLH) (by rw [hL3]; decide) hxL
  have hxJ := burnsideB610_not_mem_centralizer_ffJP hV hMP hred hJ hxK hx3 hx1 hcard
  obtain ⟨t, ht, hxt⟩ := burnsideB610_exists_tv hW hS (hLΦ hxL) hx3 hx1 hcard hxJ
  refine ⟨t, ht, ?_⟩
  rw [hLx]
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxt) (le_of_eq ?_)
  rw [hS.card_FOf hW ht, ← hLx, hL3]

section Family

variable {V : Subgroup G} (hV : IsElemAbelian 2 V) (H : Subgroup G)
  (hHN : H ≤ Subgroup.normalizer (V : Set G))

abbrev burnsideB610_Idx : Type := ↥(burnsideB610_blocks (autI hV H) (pCoreOf 3 (autI hV H)))

noncomputable abbrev burnsideB610_famX (b : burnsideB610_Idx hV H) : Subgroup G :=
  preI hV H hHN b.1

@[expose] noncomputable def burnsideB610_famD (b : burnsideB610_Idx hV H) :
    NatData (burnsideB610_famX hV H hHN b) V (ZMod 2) :=
  burnsideB610_natOfActs hV hHN
    (burnsideB610_block_le (fun w => IntMod.sq_eq_one w) (burnsideB610_setting _) b.2)
    (burnsideB610_actsAsNatural (fun w => IntMod.sq_eq_one w) (burnsideB610_setting _) b.2)
    (burnsideB610_commV_inf_fixV (fun w => IntMod.sq_eq_one w) (burnsideB610_setting _) b.2)

@[expose] noncomputable def burnsideB610_famS (t₀ : MulAut (IntMod V hV)) :
    Finset (burnsideB610_Idx hV H) :=
  (Set.toFinite {b : burnsideB610_Idx hV H | ∃ g ∈ autI hV H,
    b.1 = (B19.GOf (pCoreOf 3 (autI hV H)) t₀).map (MulAut.conj g).toMonoidHom}).toFinset

variable {hV H}

theorem burnsideB610_mem_famS {t₀ : MulAut (IntMod V hV)} {b : burnsideB610_Idx hV H} :
    b ∈ burnsideB610_famS hV H t₀ ↔ ∃ g ∈ autI hV H,
      b.1 = (B19.GOf (pCoreOf 3 (autI hV H)) t₀).map (MulAut.conj g).toMonoidHom :=
  Set.Finite.mem_toFinset _

theorem burnsideB610_famX_inj (i j : burnsideB610_Idx hV H)
    (h : burnsideB610_famX hV H hHN i = burnsideB610_famX hV H hHN j) : i = j := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  apply Subtype.ext
  have h1 := congrArg (autI hV) h
  rwa [autI_preI hV (burnsideB610_block_le hW hS i.2),
    autI_preI hV (burnsideB610_block_le hW hS j.2)] at h1

theorem burnsideB610_famX_comm {i j : burnsideB610_Idx hV H} (hij : i ≠ j) :
    ∀ x ∈ burnsideB610_famX hV H hHN i, ∀ y ∈ burnsideB610_famX hV H hHN j,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  intro x hx y hy
  obtain ⟨hxH, hxB⟩ := (mem_preI hV).1 hx
  obtain ⟨hyH, hyB⟩ := (mem_preI hV).1 hy
  have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hc : convI hV ⟨x, hHN hxH⟩ * convI hV ⟨y, hHN hyH⟩ =
      convI hV ⟨y, hHN hyH⟩ * convI hV ⟨x, hHN hxH⟩ :=
    burnsideB610_block_comm hW hS i.2 j.2 hne _ hxB _ hyB
  have hN : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    H.mul_mem (H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)) (H.inv_mem hyH) |> hHN
  rw [← convI_eq_one_iff hV ⟨_, hN⟩]
  have e : convI hV ⟨x * y * x⁻¹ * y⁻¹, hN⟩ = convI hV ⟨x, hHN hxH⟩ * convI hV ⟨y, hHN hyH⟩ *
      (convI hV ⟨x, hHN hxH⟩)⁻¹ * (convI hV ⟨y, hHN hyH⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e, hc]
  group

theorem burnsideB610_famX_triv {i j : burnsideB610_Idx hV H} (hij : i ≠ j) :
    burnsideB610_famX hV H hHN j ≤
      Subgroup.centralizer ((⁅V, burnsideB610_famX hV H hHN i⁆ : Subgroup G) : Set G) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  intro y hy
  obtain ⟨hyH, hyB⟩ := (mem_preI hV).1 hy
  have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hcent := burnsideB610_block_centSub hW hS i.2 j.2 hne hyB
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hYN := burnsideB610_preI_le_normalizer hV hHN (B := i.1)
  have hwV : w ∈ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYN hw
  have hm := burnsideB610_mk_mem_commV hV hYN hw hwV
  rw [autI_preI hV (burnsideB610_block_le hW hS i.2)] at hm
  have h1 := hcent _ hm
  have h2 := congrArg IntMod.val h1
  rw [show convHom hV H hHN ⟨y, hyH⟩ = convI hV ⟨y, hHN hyH⟩ from rfl, convI_apply_val] at h2
  calc w * y = (y * w * y⁻¹) * y := by rw [show y * w * y⁻¹ = w from h2]
    _ = y * w := by group

theorem burnsideB610_famD_beta_injective (i : burnsideB610_Idx hV H) :
    Function.Injective (burnsideB610_famD hV H hHN i).β := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  exact burnsideB610_beta_injective _ (burnsideB610_preI_inf_centralizer hV hHN
    (burnsideB610_block_le hW hS i.2) (burnsideB610_commV_inf_fixV hW hS i.2))

theorem burnsideB610_famS_conj {t₀ : MulAut (IntMod V hV)} :
    ∀ i ∈ burnsideB610_famS hV H t₀, ∀ h ∈ H, ∃ j ∈ burnsideB610_famS hV H t₀,
      cjSub h (burnsideB610_famX hV H hHN i) = burnsideB610_famX hV H hHN j := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  intro i hi h hh
  obtain ⟨g, hg, hig⟩ := burnsideB610_mem_famS.1 hi
  have hhX : convI hV ⟨h, hHN hh⟩ ∈ autI hV H := convI_mem_autI hV hh (hHN hh)
  refine ⟨⟨i.1.map (MulAut.conj (convI hV ⟨h, hHN hh⟩)).toMonoidHom,
    burnsideB610_map_conj_mem_blocks hW hS i.2 hhX⟩, ?_, ?_⟩
  · refine burnsideB610_mem_famS.2 ⟨convI hV ⟨h, hHN hh⟩ * g, Subgroup.mul_mem _ hhX hg, ?_⟩
    show i.1.map (MulAut.conj (convI hV ⟨h, hHN hh⟩)).toMonoidHom = _
    rw [hig, B19.map_conj_map_conj]
  · exact burnsideB610_cjSub_preI hV hHN hh i.1

theorem burnsideB610_famS_orbit {t₀ : MulAut (IntMod V hV)} :
    ∀ i ∈ burnsideB610_famS hV H t₀, ∀ j ∈ burnsideB610_famS hV H t₀, ∃ h ∈ H,
      cjSub h (burnsideB610_famX hV H hHN i) = burnsideB610_famX hV H hHN j := by
  intro i hi j hj
  obtain ⟨g, hg, hig⟩ := burnsideB610_mem_famS.1 hi
  obtain ⟨g', hg', hjg⟩ := burnsideB610_mem_famS.1 hj
  obtain ⟨n, hnH, hn⟩ := (mem_autI hV).1 (Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg))
  refine ⟨n, hnH, ?_⟩
  rw [burnsideB610_cjSub_preI hV hHN hnH i.1]
  show preI hV H hHN _ = preI hV H hHN j.1
  congr 1
  have hn' : convI hV ⟨(n : G), hHN hnH⟩ = g' * g⁻¹ := hn
  rw [hn', hig, hjg, B19.map_conj_map_conj, inv_mul_cancel_right]

end Family

end TwoBlk

open TwoBlk in
theorem burnsideB610_twoFamTarget_holds : burnsideB610_TwoFamTarget := by
  intro G _ _ H T M V L hMP hred hJ hsub hnat
  classical
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hS := burnsideB610_setting (autI hV H)
  have hLH : L ≤ H := burnsideB610_le_of_isSubnormal hsub
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hHN
  obtain ⟨t₀, ht₀, hLF⟩ := burnsideB610_exists_FOf_eq hV hMP hred hJ hsub hnat
  set Φ := pCoreOf 3 (autI hV H) with hΦ
  have hB₀ : B19.GOf Φ t₀ ∈ burnsideB610_blocks (autI hV H) Φ := ⟨t₀, ht₀, rfl⟩
  set b₀ : burnsideB610_Idx hV H := ⟨B19.GOf Φ t₀, hB₀⟩ with hb₀
  have hb₀S : b₀ ∈ burnsideB610_famS hV H t₀ := by
    refine burnsideB610_mem_famS.2 ⟨1, Subgroup.one_mem _, ?_⟩
    show B19.GOf Φ t₀ = (B19.GOf Φ t₀).map (MulAut.conj (1 : MulAut (IntMod V hV))).toMonoidHom
    ext x
    rw [B19.mem_map_conj]
    simp
  have hB₀H : B19.GOf Φ t₀ ≤ autI hV H := burnsideB610_block_le hW hS hB₀
  have hY₀ : autI hV (burnsideB610_famX hV H hHN b₀) = B19.GOf Φ t₀ := autI_preI hV hB₀H
  have hY₀N : burnsideB610_famX hV H hHN b₀ ≤ Subgroup.normalizer (V : Set G) :=
    burnsideB610_preI_le_normalizer hV hHN
  refine ⟨burnsideB610_Idx hV H, burnsideB610_famS hV H t₀, burnsideB610_famX hV H hHN,
    burnsideB610_famD hV H hHN, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, b₀, hb₀S, ?_,
    ?_, ?_⟩
  · exact fun i _ j _ h => burnsideB610_famX_inj hHN i j h
  · exact fun i _ => preI_le hV
  · exact fun i _ => inf_centralizer_le_preI hV
  · exact fun i _ j _ hij => burnsideB610_famX_comm hHN hij
  · exact fun i _ j _ hij => burnsideB610_famX_triv hHN hij
  · exact fun i _ a ha => burnsideB610_mem_centralizer_of_act_eq_one _
      (burnsideB610_famD_beta_injective hHN i) a ha
  · exact burnsideB610_famS_conj hHN
  · exact burnsideB610_famS_orbit hHN
  · refine burnsideB610_res hV hMP hred _ _ (fun i _ => preI_le hV) (burnsideB610_famS_conj hHN)
      hb₀S ?_
    rw [hY₀, burnsideB610_card_block hW hS hB₀]
    decide
  · exact fun i _ => burnsideB610_block_fix' hV hHN hS i.2 _
  · exact fun i _ P hPX hP2 hcard =>
      burnsideB610_block_gen' hV hHN hS i.2 (by simp) _ P hPX hP2 hcard
  · exact fun i _ => burnsideB610_block_thomp' hV hred hMP.isSylow hS i.2
  · intro l hl
    refine (mem_preI hV).2 ⟨hLH hl, ?_⟩
    have h1 : convI hV ⟨l, hHN (hLH hl)⟩ ∈ autI hV L := convI_mem_autI hV hl (hHN (hLH hl))
    rw [hLF] at h1
    exact B19.FOf_le_GOf h1
  · rw [burnsideB610_commutator_eq_map hV hY₀N, burnsideB610_commutator_eq_map hV hLN, hY₀,
      hLF, hS.commV_GOf hW ht₀]
  · intro g hg hgX
    have h1 := burnsideB610_convI_mem_normalizer_autI hV hg hgX
    rw [hY₀] at h1
    rw [hLF]
    exact burnsideB610_mem_normalizer_FOf hW hS ht₀ h1

end CFSG.Quasithin.B610T
