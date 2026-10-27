module

public import CFSG.Quasithin.H13.A6S1372L74p
public import CFSG.Quasithin.H13.A6S1372L74r
public import CFSG.Quasithin.H13.A6S1372L74t

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_of_le {X U : Subgroup G} (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hUe : IsElemAbelian 2 U)
    (hC : X ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 X)
    (hO : pCoreOf 2 X ≤ Subgroup.centralizer (U : Set G)) : IsTwoReducedIn X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hUX, hXU, hUe, fun D hDX hXD hD => ?_⟩
  have hD2 : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := hD d hd
    obtain ⟨f, hf⟩ := pCoreOf_isPGroup 2 X ⟨d ^ 2 ^ k, hC ⟨X.pow_mem (hDX hd) _, hk⟩⟩
    refine ⟨k + f, Subtype.ext ?_⟩
    have := congrArg Subtype.val hf
    simpa [pow_add, pow_mul] using this
  exact (le_pCoreOf_of_le_normalizer 2 hDX hXD hD2).trans hO

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section FinalZ3

variable {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
  (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)

include hH hKH hHK hKL1 in
theorem commute_convI_cL1 (hhat : ¬ IsHatA6 L)
    {U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hcU : (S.cL1 hhat : G) ∈ Subgroup.normalizer (U : Set G))
    (hXU : K ⊔ pCoreOf 2 (S.L1 ⊔ T) ≤ Subgroup.normalizer (U : Set G))
    (hOK : pCoreOf 2 K ≤ Subgroup.centralizer (U : Set G))
    (hOX : pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) ≤ Subgroup.centralizer (U : Set G))
    {φ : MulAut (IntMod U hUe)} (hφ : φ ∈ autI hUe (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) :
    convI hUe ⟨(S.cL1 hhat : G), hcU⟩ * φ = φ * convI hUe ⟨(S.cL1 hhat : G), hcU⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hcL : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have key : ∀ g : ↥(Subgroup.normalizer (U : Set G)),
      (S.cL1 hhat : G) * g * (S.cL1 hhat : G)⁻¹ * (g : G)⁻¹ ∈
        Subgroup.centralizer (U : Set G) →
      convI hUe ⟨(S.cL1 hhat : G), hcU⟩ * convI hUe g =
        convI hUe g * convI hUe ⟨(S.cL1 hhat : G), hcU⟩ := by
    intro g hg
    have h1 : convI hUe (⟨(S.cL1 hhat : G), hcU⟩ * g * ⟨(S.cL1 hhat : G), hcU⟩⁻¹ * g⁻¹) = 1 := by
      rw [convI_eq_one_iff]
      simpa using hg
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hφ
  have hgX := hg
  rw [sup_comm] at hgX
  obtain ⟨r, hr, k, hk, hrk⟩ := (A6L19.mem_sup_iff hRK).1 hgX
  have hrU : r ∈ Subgroup.normalizer (U : Set G) := hXU (Subgroup.mem_sup_right hr)
  have hkU : k ∈ Subgroup.normalizer (U : Set G) := hXU (Subgroup.mem_sup_left hk)
  have e : g = ⟨r, hrU⟩ * ⟨k, hkU⟩ := Subtype.ext hrk.symm
  have hcr := key ⟨r, hrU⟩ (by
    have h := (pCoreOf 2 S.L1).inv_mem (comm_R1_L1 hr hcL)
    have e : (r * (S.cL1 hhat : G) * r⁻¹ * (S.cL1 hhat : G)⁻¹)⁻¹ =
        (S.cL1 hhat : G) * r * (S.cL1 hhat : G)⁻¹ * r⁻¹ := by group
    rw [e] at h
    exact hOX (pCoreOf_L1_le_X hH hKH hHK hKL1 h))
  have hck := key ⟨k, hkU⟩ (by
    have h := (pCoreOf 2 K).inv_mem (hKL1 k hk _ hcL)
    have e : (k * (S.cL1 hhat : G) * k⁻¹ * (S.cL1 hhat : G)⁻¹)⁻¹ =
        (S.cL1 hhat : G) * k * (S.cL1 hhat : G)⁻¹ * k⁻¹ := by group
    rw [e] at h
    exact hOK h)
  rw [e, map_mul, ← mul_assoc, hcr, mul_assoc, hck, ← mul_assoc]

end FinalZ3

section Final

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G}
  (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)
include hNS h13315 h1356two hH hab hKH hHK hKL1

theorem false_of_card_three (h1227 : U3.Stmt13_2_2_7)
    (hhat : ¬ IsHatA6 L) (hB : ¬ H13.IsA6Block L) (hK2 : oTwoRes K = K)
    (hKC : ∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
      k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hexp, hcomm⟩ := A6L74.exp_comm_of_card_three h3
  obtain ⟨hOR, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hR2 : IsPGroup 2 (pCoreOf 2 (S.L1 ⊔ T)) := pCoreOf_isPGroup 2 _
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set X := K ⊔ R with hX
  have hcL : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hH.1.1
  have hL1K : S.L1 ≤ Subgroup.normalizer (K : Set G) := hL1H.trans hHK
  have hKL := K_le_normalizer_L1 hH hKH hHK hKL1
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  obtain ⟨W, hWU₀, hW1, hWN, hKfix, hcfix⟩ :=
    exists_W hNS h13315 h1356two hH hab hKH hHK hKL1 hhat hK2 hKC hKM h3
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hL1X : S.L1 ≤ Subgroup.normalizer (X : Set G) := fun l hl =>
    A6L74.mem_normalizer_sup hRK (hL1K hl) (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
  have hX'X : X ⊔ S.L1 ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hL1X
  have hX'H : X ⊔ S.L1 ≤ H := sup_le (sup_le hKH hRH) hL1H
  have hX'L : X ⊔ S.L1 ≤ Subgroup.normalizer (S.L1 : Set G) :=
    sup_le (sup_le hKL R1_le_normalizer_L1) Subgroup.le_normalizer
  have hX'K : X ⊔ S.L1 ≤ Subgroup.normalizer (K : Set G) := sup_le hXK hL1K
  have hX'W : X ⊔ S.L1 ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    hWN g (hX'H hg) (hX'L hg) (hX'K hg)
  have hWe : IsElemAbelian 2 W := A1b.isElemAbelian_of_le (hWU₀.trans inf_le_left) hab
  have hOW : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G) := fun o ho => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWU₀ hw).2 o (hOQ ho)).symm
  obtain ⟨k₀, hk₀, hk₀O⟩ := A6L74.exists_not_mem_pCoreOf_of_card_three h3
  have hfpf : ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ → X ⊔ S.L1 ≤ Subgroup.normalizer (U : Set G) →
      K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K := by
    intro U hUW hU1 _
    refine le_antisymm (fun k hk => ?_) (le_inf (pCoreOf_le 2 K) fun o ho =>
      Subgroup.centralizer_le hUW (hOW ho))
    by_contra hkO
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    refine hKfix u (hUW hu) fun g hg => ?_
    obtain ⟨i, hi⟩ := A6L74.exists_pow_of_card_three h3 hk.1 hkO hg
    have hgC : g ∈ Subgroup.centralizer (U : Set G) := by
      have e : g = k ^ i * ((k ^ i)⁻¹ * g) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hk.2 i) (Subgroup.centralizer_le hUW (hOW hi))
    rw [← Subgroup.mem_centralizer_iff.mp hgC u hu]
    group
  obtain ⟨U, hUW, hU1, hX'U, hOXU⟩ := A6L74.exists_minimal_reduced le_sup_left hXK le_sup_left
    hX'X hX'W hWe hW1 (fun h => hk₀O (h hk₀)) hfpf
  have hUe : IsElemAbelian 2 U := A1b.isElemAbelian_of_le hUW hWe
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hX'U
  have hcU : (S.cL1 hhat : G) ∈ Subgroup.normalizer (U : Set G) :=
    hX'U (Subgroup.mem_sup_right hcL)
  have hUR : U ≤ R := hUW.trans (hWU₀.trans (inf_le_left.trans
    (hF.conjClosure_Vp_le_pCoreOf.trans (QH_le_R1 hH))))
  have hCK : K ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 K := (hfpf U hUW hU1 hX'U).le
  have hCX := A6L74.inf_centralizer_le_pCoreOf hR2 hRK hXU hCK
  have hred : IsTwoReducedIn X U :=
    A6L74.isTwoReducedIn_of_le (hUR.trans le_sup_right) hXU hUe hCX hOXU
  have hsyl : IsSylowTwoOf R X :=
    A6L74.isSylowTwoOf_sup Nat.prime_three (by norm_num) hexp hR2 hRK hOR
  have hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (U : Set G) := by
    intro hJ
    have hRC : R ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 X :=
      le_antisymm (fun r hr => hCX ⟨Subgroup.mem_sup_right hr.1, hr.2⟩)
        (le_inf (pCoreOf_le_of_isSylowTwoOf hsyl) hOXU)
    have hbaum : baum R = baum (pCoreOf 2 X) := by
      rw [← hRC]
      exact baum_eq_baum_centralizer hUe hUR (le_inf (thompsonJ_le_self _) hJ)
    have hRM : Subgroup.normalizer (baum R : Set G) ≤ Subgroup.normalizer (L : Set G) := by
      rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
        with h | h
      · exact normalizer_baum_R1_le_M h
      · exact absurd h hB
    apply hKM
    intro k hk
    apply hRM
    rw [hbaum]
    exact normalizer_le_normalizer_baum _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk))
  have hsolv : Group.IsSolvable ↥(autI hUe X) := by
    rw [← range_convHom hUe X hXU]
    have := A6L74.isSolvable_sup hcomm hR2 hRK
    exact Group.isSolvable_of_surjective (f := (convHom hUe X hXU).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨I, -, hJX, -, -, hnat, -⟩ := B2F.structure_of_not_le_of_quot hUe hred hsolv hsyl hJ
  have hI : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hI
    subst hI
    have hbot : autI hUe (thompsonJ X) = ⊥ := by
      rw [hJX]
      simp
    rw [autI_eq_bot_iff hUe ((thompsonJ_le_self X).trans hXU)] at hbot
    exact hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl).trans hbot)
  obtain ⟨Lb, hLb⟩ := hI
  have hLbX : Lb ≤ autI hUe X := by
    refine (le_iSup₂_of_le Lb hLb le_rfl : Lb ≤ ⨆ L' ∈ I, L').trans ?_
    rw [← hJX]
    exact autI_mono hUe (thompsonJ_le_self X)
  have hcc : ∀ l ∈ Lb, convI hUe ⟨(S.cL1 hhat : G), hcU⟩ * l =
      l * convI hUe ⟨(S.cL1 hhat : G), hcU⟩ := fun l hl =>
    commute_convI_cL1 hH hKH hHK hKL1 hhat hUe hcU hXU (hOW.trans (Subgroup.centralizer_le hUW))
      hOXU (hLbX hl)
  have hzc : ∀ a ∈ Subgroup.zpowers (convI hUe ⟨(S.cL1 hhat : G), hcU⟩), ∀ b ∈ Lb,
      a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.zpowers (convI hUe ⟨(S.cL1 hhat : G), hcU⟩) ≤
        Subgroup.centralizer (Lb : Set (MulAut (IntMod U hUe))) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl => (hcc l hl).symm)
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hst : convI hUe ⟨(S.cL1 hhat : G), hcU⟩ ∈ CFSG.Quasithin.stabSub (commV Lb) :=
    S1417.mem_stabSub_of_forall
      (fun u hu => S1417.commV_stable_of_commute hzc (Subgroup.mem_zpowers _) hu)
      (fun u hu => S1417.commV_stable_of_commute hzc
        ((Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)) hu)
  have hfix := S1417.apply_eq_of_commute (hnat Lb hLb) (fun l hl u hu => commV_stable Lb hl hu)
    hst hcc
  obtain ⟨-, φ, -⟩ := hnat Lb hLb
  have hw1 : ((φ.symm (Multiplicative.ofAdd ![1, 0]) : ↥(commV Lb)) : IntMod U hUe) ≠ 1 := by
    intro h
    have h2 := congrArg φ (Subtype.ext h : φ.symm (Multiplicative.ofAdd ![1, 0]) = 1)
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    have h3 := congrArg (fun x : Multiplicative (Fin 2 → ZMod 2) => Multiplicative.toAdd x 0) h2
    simp at h3
  have hcw := hfix _ (φ.symm (Multiplicative.ofAdd ![1, 0])).2
  have hval := congrArg IntMod.val hcw
  rw [convI_apply_val] at hval
  have h1 := hcfix _ (hUW (IntMod.val_mem _)) hval
  exact hw1 (IntMod.val_injective (by rw [h1, IntMod.val_one]))

end Final

end Setting4

theorem lem1374OneFinalZ3_of (h1227 : U3.Stmt13_2_2_7)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) : Lem1374OneFinalZ3 := by
  intro G _ _ T L V S hNS _ hhat H hH hab hB K hKH hHK hK2 hKC _ _ hKM _ hKL1 h3
  exact Setting4.false_of_card_three hNS h13315 h1356two hH hab hKH hHK hKL1 h1227 hhat hB hK2
    hKC hKM h3

end CFSG.Quasithin.H13.A6
