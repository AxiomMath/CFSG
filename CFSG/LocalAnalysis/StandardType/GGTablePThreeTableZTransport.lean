module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

private theorem tzt_inv_mul_mem_ker {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (δ : MulAut H) (δ' : MulAut U) (hδ' : ∀ x, κ (δ x) = δ' (κ x)) (x : H)
    (hx : δ' (κ x) = κ x) : x⁻¹ * δ x ∈ κ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hδ' x, hx, inv_mul_cancel]

private theorem tzt_isSubnormal_map {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (hκ : Function.Surjective κ) (hker : κ.ker ≤ Subgroup.center H)
    (δ : MulAut H) (δ' : MulAut U) (hδ' : ∀ x, κ (δ x) = δ' (κ x))
    {J : Subgroup H} (hJ : IsSubnormal J (ggAutFixedSubgroup δ)) :
    IsSubnormal (J.map κ) (ggAutFixedSubgroup δ') := by
  let C : Subgroup H := ggAutFixedSubgroup δ
  let P : Subgroup H := (ggAutFixedSubgroup δ').comap κ
  have hPmap : P.map κ = ggAutFixedSubgroup δ' :=
    Subgroup.map_comap_eq_self_of_surjective hκ _
  have hCP : C ≤ P := by
    intro x hx
    change κ x ∈ ggAutFixedSubgroup δ'
    rw [mem_ggAutFixedSubgroup, ← hδ' x, hx]
  have hnorm : (C.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCP]
    intro c g hc hg
    change δ (g * c * g⁻¹) = g * c * g⁻¹
    have hc' : δ c = c := hc
    have hg' : δ' (κ g) = κ g := hg
    set z : H := g⁻¹ * δ g with hzdef
    have hz : z ∈ κ.ker := by
      rw [hzdef]
      exact tzt_inv_mul_mem_ker κ δ δ' hδ' g hg'
    have hzcent : z ∈ Subgroup.center H := hker hz
    have hzc : z * c = c * z := ((Subgroup.mem_center_iff.mp hzcent) c).symm
    have hdg : δ g = g * z := by rw [hzdef]; group
    rw [map_mul, map_mul, map_inv, hc', hdg, mul_assoc g z c, hzc]
    group
  have hsub : IsSubnormal C P := IsSubnormal.step hCP hnorm (IsSubnormal.refl P)
  have hmap := (hJ.trans hsub).map κ
  rwa [hPmap] at hmap

private theorem tzt_injective_on {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (J : Subgroup H) (h : J ⊓ κ.ker = ⊥) : Function.Injective (κ.subgroupMap J) := by
  intro a b hab
  have h1 : κ (a : H) = κ (b : H) := by
    have := congrArg Subtype.val hab
    simpa only [MonoidHom.subgroupMap_apply_coe] using this
  have h2 : (a : H)⁻¹ * b ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : (a : H)⁻¹ * b ∈ J := J.mul_mem (J.inv_mem a.2) b.2
  have h4 : (a : H)⁻¹ * b = 1 := by
    have hmem : (a : H)⁻¹ * b ∈ J ⊓ κ.ker := ⟨h3, h2⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact Subtype.ext (inv_mul_eq_one.mp h4)

private noncomputable def tzt_equivMap {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (J : Subgroup H) (h : J ⊓ κ.ker = ⊥) : J ≃* J.map κ :=
  MulEquiv.ofBijective (κ.subgroupMap J) ⟨tzt_injective_on κ J h, by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa only [MonoidHom.subgroupMap_apply_coe] using hxy)⟩⟩

theorem tableZ_transport {H U : Type} [Group H] [Group U] [Finite H] (κ : H →* U)
    (hκ : Function.Surjective κ) (hker : κ.ker ≤ Subgroup.center H)
    (hker2 : ∀ x ∈ κ.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (δ : MulAut H) (hδ3 : δ ^ 3 = 1) (δ' : MulAut U) (hδ' : ∀ x, κ (δ x) = δ' (κ x))
    (J : Subgroup H) (hJ : IsComponentOf J (ggAutFixedSubgroup δ))
    (hZ : Nat.card (Subgroup.center J) ∣ 3) :
    IsComponentOf (J.map κ) (ggAutFixedSubgroup δ') ∧ J ⊓ κ.ker = ⊥ := by
  let A : Subgroup H := J ⊓ κ.ker
  have hAJ : A ≤ J := inf_le_left
  have hAK : A ≤ κ.ker := inf_le_right
  have hAcen : A.subgroupOf J ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxK : (x : H) ∈ κ.ker := hAK (Subgroup.mem_subgroupOf.mp hx)
    have hxc : (x : H) ∈ Subgroup.center H := hker hxK
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : H))
  have hcard_eq : Nat.card A = Nat.card (A.subgroupOf J) := by
    rw [← Subgroup.card_subtype J (A.subgroupOf J), Subgroup.map_subgroupOf_eq_of_le hAJ]
  have hcardA : Nat.card A ∣ Nat.card (Subgroup.center ↥J) := by
    rw [hcard_eq]
    exact Subgroup.card_dvd_of_le hAcen
  have hbot : J ⊓ κ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨k, hk⟩ := hker2 x hx.2
    have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hdvdA : orderOf x ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hx
    have hdvd3 : orderOf x ∣ 3 := (hdvdA.trans hcardA).trans hZ
    have hcop : Nat.Coprime (2 ^ k) 3 := by
      simpa using Nat.coprime_pow_primes k 1 Nat.prime_two Nat.prime_three (by norm_num)
    have hdvd1 : orderOf x ∣ 1 := by
      have hg : orderOf x ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hdvd2 hdvd3
      rwa [Nat.Coprime.gcd_eq_one hcop] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  refine ⟨?_, hbot⟩
  have hsub : IsSubnormal (J.map κ) (ggAutFixedSubgroup δ') :=
    tzt_isSubnormal_map κ hκ hker δ δ' hδ' hJ.2.1
  refine ⟨hsub.le, hsub, ?_⟩
  exact (CFSG.Assembly.IsQuasisimple.congr (tzt_equivMap κ J hbot)).mp hJ.2.2

end CFSG.StandardType.TablePThreeKG

end
