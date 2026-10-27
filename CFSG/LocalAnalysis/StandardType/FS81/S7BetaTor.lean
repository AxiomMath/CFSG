module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SeitzReduction CFSG.Blueprint.Chevalley

private theorem betaTor_exists_rebase
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y) :
    ∃ ι' : adjointGroup .E8 (GaloisField 2 1) →* G,
      Function.Injective ι' ∧ ι'.range = Y ∧
        ι' (rootThree .E8 (GaloisField 2 1) (highRoot .E8)) = b₀ * B.b 1 := by
  have hK2 : Nat.card (GaloisField 2 1) = 2 := natCard_galoisField_two_one
  have hA : E8AutAt Row.twD7 := e8AutAt_twD7
  obtain ⟨ι, hι_inj, hι_range⟩ := exists_injective_hom_range_eq_of_isEm_eight h.isEm
  have h120 : (normalizerLines ι.range E (b₀ * B.b 1)).ncard = 120 := by
    rw [hι_range]
    exact ncard_normalizerLines_eq_120_twD7 h (hA G b₀ K E B Y h)
  have hEY : E ≤ ι.range := by
    rw [hι_range]
    exact RootSetting.torus_le h
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by
      rw [← h.adapted.2.1]
      exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hordβ : orderOf (b₀ * B.b 1) = 3 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    refine orderOf_eq_prime ?_ ?_
    · rw [← hvec]
      exact hEab.2 _ (h.adapted.1 ▸ B.vec_mem_span _)
    · intro h1
      have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
        rw [hvec, h1]
      have he0 := B.indep _ h1'
      have h0 := congrFun he0 0
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
        Pi.zero_apply, add_zero] at h0
      exact one_ne_zero h0
  have hβ1 : b₀ * B.b 1 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordβ
    norm_num at hordβ
  obtain ⟨ι', hι'_inj, hι'_range, hι'_sθ⟩ :=
    exists_hom_range_eq_apply_rootThree_eq hK2 ι hι_inj hEY hEab hEcard hβE hβ1 h120
  exact ⟨ι', hι'_inj, hι'_range.trans hι_range, hι'_sθ⟩

private theorem betaTor_comap_card_of_le_range
    {G : Type} [Group G] (ι' : adjointGroup .E8 (GaloisField 2 1) →* G)
    (hι' : Function.Injective ι') {X : Subgroup G} (hX : X ≤ ι'.range)
    (hcard : Nat.card X = 3 ^ 8) : Nat.card (X.comap ι') = 3 ^ 8 := by
  rw [← Subgroup.card_map_of_injective (K := X.comap ι') (f := ι') hι',
    Subgroup.map_comap_eq_self hX, hcard]

private theorem betaTor_comap_le_centralizer_rootThree
    {G : Type} [Group G] (ι' : adjointGroup .E8 (GaloisField 2 1) →* G)
    (hι' : Function.Injective ι') {β : G}
    (hCY : Subgroup.centralizer ({β} : Set G) ⊓ ι'.range =
      (Subgroup.centralizer ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
        Set (adjointGroup .E8 (GaloisField 2 1)))).map ι')
    {X : Subgroup G} (hX : X ≤ Subgroup.centralizer ({β} : Set G) ⊓ ι'.range) :
    X.comap ι' ≤ Subgroup.centralizer ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
      Set (adjointGroup .E8 (GaloisField 2 1))) := by
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hx' : ι' x ∈ Subgroup.centralizer ({β} : Set G) ⊓ ι'.range := hX hx
  rw [hCY] at hx'
  obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hx'
  have hxm : x = m := (hι' hmeq).symm
  rw [hxm]
  exact hm

theorem twD7BetaTorAt_holds :
    TwD7BetaTorAt := by
  intro G _ _ b₀ K E B Y h F hF hFab hFcard
  have hK2 : Nat.card (GaloisField 2 1) = 2 := natCard_galoisField_two_one
  obtain ⟨ι', hι'_inj, hι'_rangeY, hι'_sθ⟩ := betaTor_exists_rebase h
  have hβeq : rowRootElt Row.twD7 B b₀ =
      ι' (rootThree .E8 (GaloisField 2 1) (highRoot .E8)) := by
    rw [hι'_sθ]
    rfl
  have hCY' : Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ ι'.range =
      (Subgroup.centralizer ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
        Set (adjointGroup .E8 (GaloisField 2 1)))).map ι' := by
    rw [hβeq]
    exact centralizer_singleton_inf_range_eq_map ι' hι'_inj
      (rootThree .E8 (GaloisField 2 1) (highRoot .E8))
  have hFleY : F ≤ Y := hF.trans inf_le_right
  have hFle_range : F ≤ ι'.range := by
    rw [hι'_rangeY]
    exact hFleY
  have hEY' : E ≤ ι'.range := by
    rw [hι'_rangeY]
    exact RootSetting.torus_le h
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcardEq : Nat.card E = 3 ^ 8 := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  have hβE : rowRootElt Row.twD7 B b₀ ∈ E := by
    have h0 : b₀ ∈ E := by
      rw [← h.adapted.2.1]
      exact h.adapted.1 ▸ B.b_mem_span 0
    have h1 : B.b 1 ∈ E := h.adapted.1 ▸ B.b_mem_span 1
    simpa [rowRootElt] using E.mul_mem h0 h1
  have hEcent : E ≤ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ Y := by
    refine le_inf ?_ (RootSetting.torus_le h)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨_, hβE⟩ ⟨e, he⟩)
  have hF' : F ≤ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ ι'.range := by
    rwa [hι'_rangeY]
  have hEcent' : E ≤ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ ι'.range := by
    rwa [hι'_rangeY]
  have hF₁C : F.comap ι' ≤ Subgroup.centralizer
      ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
        Set (adjointGroup .E8 (GaloisField 2 1))) :=
    betaTor_comap_le_centralizer_rootThree ι' hι'_inj hCY' hF'
  have hE₁C : E.comap ι' ≤ Subgroup.centralizer
      ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
        Set (adjointGroup .E8 (GaloisField 2 1))) :=
    betaTor_comap_le_centralizer_rootThree ι' hι'_inj hCY' hEcent'
  have hF₁ab : IsElemAbelian 3 (F.comap ι') := isElemAbelian_comap ι' hι'_inj hFab
  have hE₁ab : IsElemAbelian 3 (E.comap ι') := isElemAbelian_comap ι' hι'_inj hEab
  have hF₁card : Nat.card (F.comap ι') = 3 ^ 8 :=
    betaTor_comap_card_of_le_range ι' hι'_inj hFle_range (hFcard.trans hEcardEq)
  have hE₁card : Nat.card (E.comap ι') = 3 ^ 8 :=
    betaTor_comap_card_of_le_range ι' hι'_inj hEY' hEcardEq
  obtain ⟨d, hdD, hdmap⟩ :=
    exists_mem_perpLevi_map_conj_eq_of_le_centralizer_rootThree
      (K := GaloisField 2 1) hK2 hF₁C hE₁C hF₁ab hE₁ab hF₁card hE₁card
  let c : G := ι' d
  have hcY : c ∈ Y := by
    rw [← hι'_rangeY]
    exact ⟨d, rfl⟩
  have hdC : d ∈ Subgroup.centralizer
      ({rootThree .E8 (GaloisField 2 1) (highRoot .E8)} :
        Set (adjointGroup .E8 (GaloisField 2 1))) :=
    perpLevi_le_centralizer_rootThree (K := GaloisField 2 1) hdD
  have hcC : c ∈ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, hβeq, ← map_mul, ← map_mul]
    exact congrArg ι' (Subgroup.mem_centralizer_iff.1 hdC _ rfl)
  have hFmap : (F.comap ι').map ι' = F := Subgroup.map_comap_eq_self hFle_range
  have hEmap : (E.comap ι').map ι' = E := Subgroup.map_comap_eq_self hEY'
  have hcomp : (MulAut.conj c).toMonoidHom.comp ι' =
      ι'.comp (MulAut.conj d).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv]
    rfl
  refine ⟨c, ⟨hcC, hcY⟩, ?_⟩
  calc
    F.map (MulAut.conj c).toMonoidHom
        = ((F.comap ι').map ι').map (MulAut.conj c).toMonoidHom := by rw [hFmap]
    _ = (F.comap ι').map ((MulAut.conj c).toMonoidHom.comp ι') := by
      rw [Subgroup.map_map]
    _ = (F.comap ι').map (ι'.comp (MulAut.conj d).toMonoidHom) := by rw [hcomp]
    _ = ((F.comap ι').map (MulAut.conj d).toMonoidHom).map ι' := by
      rw [← Subgroup.map_map]
    _ = (E.comap ι').map ι' := by rw [hdmap]
    _ = E := hEmap


end CFSG.StandardType.FrameRoute.FS81

end
