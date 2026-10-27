module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AbelianSylowGL
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.RankThree.S4Free.Stellmacher25
public import CFSG.Quasithin.Background.Asc81cPfTrans1
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16g_le_stabSub_commSub (H : Subgroup (MulAut W)) :
    H ≤ stabSub (commSub ⊤ H) := by
  refine CFSG.RankThree.S4Free.Stell.le_stabSub_of_forall_apply_mem ?_
  intro x hx u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction (p := fun c _ => x c ∈ commSub ⊤ H) ?_ ?_ ?_ ?_ hu
  · rintro c ⟨y, hy, w, -, rfl⟩
    have h1 : x (y w * w⁻¹) = (x * y * x⁻¹) (x w) * (x w)⁻¹ := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [h1]
    exact Subgroup.subset_closure
      ⟨x * y * x⁻¹, H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx), x w, Subgroup.mem_top _, rfl⟩
  · rw [map_one]
    exact (commSub ⊤ H).one_mem
  · intro a b _ _ iha ihb
    rw [map_mul]
    exact (commSub ⊤ H).mul_mem iha ihb
  · intro a _ iha
    rw [map_inv]
    exact (commSub ⊤ H).inv_mem iha

theorem w16g_inf_centSub_commSub_eq_bot (hW : ∀ w : W, w * w = 1) {H : Subgroup (MulAut W)}
    (hH : IsPGroup 3 ↥H) : H ⊓ centSub (commSub ⊤ H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx2 : x * x = 1 := by
    apply MulEquiv.ext
    intro w
    have hcM : x w * w⁻¹ ∈ commSub ⊤ H :=
      Subgroup.subset_closure ⟨x, hx.1, w, Subgroup.mem_top w, rfl⟩
    have hxc : x (x w * w⁻¹) = x w * w⁻¹ := mem_centSub.mp hx.2 _ hcM
    have hw : w⁻¹ = w := inv_eq_of_mul_eq_one_left (hW w)
    calc x (x w) = x ((x w * w⁻¹) * w) := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = x (x w * w⁻¹) * x w := map_mul x _ _
      _ = (x w * w⁻¹) * x w := by rw [hxc]
      _ = w := by
          rw [hw]
          calc (x w * w) * x w = (x w * x w) * w := by ac_rfl
            _ = 1 * w := by rw [hW (x w)]
            _ = w := one_mul w
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 3) (G := ↥H)).mp hH ⟨x, hx.1⟩
  let y : ↥H := ⟨x, hx.1⟩
  have hy2 : y ^ 2 = 1 := by
    rw [show y = ⟨x, hx.1⟩ from rfl]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hx2)
  have h3k : y ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hgcd := pow_gcd_eq_one.mpr ⟨hy2, h3k⟩
  rw [hcop.gcd_eq_one, pow_one] at hgcd
  exact congrArg Subtype.val hgcd

theorem w16g_rank_two_commute (hW : ∀ w : W, w * w = 1) {O R S : Subgroup (MulAut W)}
    (hO : IsPGroup 3 ↥O) (hR : R ≤ O) (hS : S ≤ O) (hrR : rk ↥(commSub ⊤ R) = 2)
    (hrS : rk ↥(commSub ⊤ S) = 2) : ⁅R, S⁆ = ⊥ := by
  let H : Subgroup (MulAut W) := R ⊔ S
  have hHO : H ≤ O := sup_le hR hS
  have hH3 : IsPGroup 3 ↥H := hO.to_le hHO
  have hM : commSub ⊤ H = commSub ⊤ R ⊔ commSub ⊤ S := by
    simp only [H, CFSG.Quasithin.Asc81c.Pf.commSub_sup]
  have hrkM : rk ↥(commSub ⊤ H) ≤ 4 := by
    rw [hM]
    have h := rk_sup_add_rk_inf (commSub ⊤ R) (commSub ⊤ S)
    omega
  have hHstab : H ≤ stabSub (commSub ⊤ H) := w16g_le_stabSub_commSub H
  have hcent : H ⊓ centSub (commSub ⊤ H) = ⊥ := w16g_inf_centSub_commSub_eq_bot hW hH3
  let M : Subgroup W := commSub ⊤ H
  have hrkM' : rk ↥M ≤ 4 := hrkM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥M) (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hW a))
    (n := rk ↥M) (card_eq_two_pow hW2 M)
  let hGL : MulAut ↥M ≃* GL (Fin (rk ↥M)) (ZMod 2) :=
    CFSG.SectionRank.Ccomm.elemAutEquivGL e
  let incl : H →* stabSub M := Subgroup.inclusion hHstab
  let res : H →* MulAut ↥M := (resHom M).comp incl
  let φ : H →* GL (Fin (rk ↥M)) (ZMod 2) := hGL.toMonoidHom.comp res
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : res a = res b := hGL.injective (by simpa [φ] using hab)
    have h2 : res (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : incl (a * b⁻¹) ∈ (resHom M).ker := h2
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h3
    have h4 : ((a * b⁻¹ : H) : MulAut W) ∈ H ⊓ centSub M := ⟨(a * b⁻¹).2, h3⟩
    rw [hcent] at h4
    have h5 : (a * b⁻¹ : H) = 1 := Subtype.ext (Subgroup.mem_bot.mp h4)
    exact mul_inv_eq_one.mp h5
  have hH3top : IsPGroup 3 ↥(⊤ : Subgroup H) :=
    hH3.of_equiv (Subgroup.topEquiv (G := H)).symm
  have hHcomm : IsMulCommutative ↥(⊤ : Subgroup H) :=
    CFSG.AGLEmbeddingD2.AbelianSylowGL.isMulCommutative_of_isPGroup_of_injective_GL
      (X := H) (k := ZMod 2) (r := 3) (m := rk ↥M) (d := 2) (by decide) (by decide)
      (by norm_num) (by intro j hj1 hj2; interval_cases j; norm_num) (by omega) φ hφinj ⊤ hH3top
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hrH : r ∈ H := Subgroup.mem_sup_left hr
  have hsH : s ∈ H := Subgroup.mem_sup_right hs
  have hcomm := hHcomm.is_comm.comm
    (⟨⟨r, hrH⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup H))
    (⟨⟨s, hsH⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup H))
  simpa using hcomm.symm

end CFSG.LocalAnalysis.WeakClosure81
