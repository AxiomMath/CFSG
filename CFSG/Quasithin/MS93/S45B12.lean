module

public import CFSG.Quasithin.MS93.S45Cen
public import CFSG.Quasithin.MS93.S4A431C

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Fix

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem mem_z_of_forall_commutator_mem' {K W Z Lt : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    {dual : Bool} (hd : IsSumOfNaturalModulesVia K W Z ψ dual 1)
    (hLt : ∀ g : SL3 F, ∃ l : ↥K, (l : 𝔾) ∈ Lt ∧ toSL3 ψ l = g) {x : 𝔾} (hx : x ∈ W)
    (hxl : ∀ l ∈ Lt, ⁅x, l⁆ ∈ Z) : x ∈ Z := by
  cases dual with
  | true => exact S46.mem_z_of_forall_commutator_mem hd hLt hx hxl
  | false =>
    set N := NatSec.ofIsSum hd
    rw [← N.coord_eq_zero_iff hx]
    refine S4A.eq_zero_of_forall_mulVec_eq fun g => ?_
    obtain ⟨l, hl, rfl⟩ := hLt g
    have hlx : (l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹ ∈ W := N.conj_mem l (W.inv_mem hx)
    have e : ⁅x, (l : 𝔾)⁆ = x * ((l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h0 := (N.coord_eq_zero_iff (W.mul_mem hx hlx)).mpr (e ▸ hxl l hl)
    rw [N.coord_mul hx hlx, N.coord_conj l (W.inv_mem hx), N.coord_inv hx, natAct_false,
      Matrix.mulVec_neg] at h0
    exact (add_neg_eq_zero.mp h0).symm

theorem mem_of_forall_commutator_eq_one {K X₁ X₂ W Lt : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} {dual : Bool} (h₁ : IsSumOfNaturalModulesVia K X₁ W ψ dual 1)
    (h₂ : IsSumOfNaturalModulesVia K X₂ W ψ dual 1) (hinf : X₁ ⊓ X₂ = W) (hX₁K : X₁ ≤ K)
    (hLtK : Lt ≤ K) (hLt : ∀ g : SL3 F, ∃ l : ↥K, (l : 𝔾) ∈ Lt ∧ toSL3 ψ l = g) {x : 𝔾}
    (hx : x ∈ X₁ ⊔ X₂) (hxl : ∀ l ∈ Lt, ⁅x, l⁆ = 1) : x ∈ W := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X₁ X₂
    (hX₁K.trans h₂.1)] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  have key : ∀ l ∈ Lt, x₁⁻¹ * (l * x₁ * l⁻¹) ∈ W ∧ x₂ * (l * x₂ * l⁻¹)⁻¹ ∈ W := by
    intro l hl
    have hlx₁ : l * x₁ * l⁻¹ ∈ X₁ := (Subgroup.mem_normalizer_iff.mp (h₁.1 (hLtK hl)) _).mp hx₁
    have hlx₂ : l * x₂ * l⁻¹ ∈ X₂ := (Subgroup.mem_normalizer_iff.mp (h₂.1 (hLtK hl)) _).mp hx₂
    have hc := hxl l hl
    rw [commutatorElement_eq_one_iff_commute] at hc
    have e : x₁⁻¹ * (l * x₁ * l⁻¹) = x₂ * (l * x₂ * l⁻¹)⁻¹ := by
      have h1 : l * (x₁ * x₂) * l⁻¹ = x₁ * x₂ := by rw [← hc.eq, mul_inv_cancel_right]
      calc x₁⁻¹ * (l * x₁ * l⁻¹)
          = x₁⁻¹ * (l * (x₁ * x₂) * l⁻¹) * (l * x₂ * l⁻¹)⁻¹ := by group
        _ = x₂ * (l * x₂ * l⁻¹)⁻¹ := by rw [h1]; group
    have hm : x₁⁻¹ * (l * x₁ * l⁻¹) ∈ X₁ ⊓ X₂ := Subgroup.mem_inf.mpr
      ⟨X₁.mul_mem (X₁.inv_mem hx₁) hlx₁, e ▸ X₂.mul_mem hx₂ (X₂.inv_mem hlx₂)⟩
    rw [hinf] at hm
    exact ⟨hm, e ▸ hm⟩
  have hW₁ : x₁⁻¹ ∈ W := mem_z_of_forall_commutator_mem' h₁ hLt (X₁.inv_mem hx₁) fun l hl => by
    have := (key l hl).1
    rwa [show x₁⁻¹ * (l * x₁ * l⁻¹) = ⁅x₁⁻¹, l⁆ by rw [commutatorElement_def, inv_inv]; group]
      at this
  have hW₂ : x₂ ∈ W := mem_z_of_forall_commutator_mem' h₂ hLt hx₂ fun l hl => by
    have := (key l hl).2
    rwa [show x₂ * (l * x₂ * l⁻¹)⁻¹ = ⁅x₂, l⁆ by simp only [commutatorElement_def]; group]
      at this
  exact W.mul_mem (by simpa using W.inv_mem hW₁) hW₂

end Fix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem inf_centralizer_ltil_le (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    (hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a)) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal) ≤
      Hloc c.hyp.le L (p a) := by
  have h := c.hyp
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj (k + 34) (by omega))
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  obtain ⟨hinf3, h₁t, h₂t⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hF7 := c.commutator_qv_ltil_le_top' hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  have hLt := c.exists_ltil_toSL3_eq hα hψs hψ
  have hLs : Ltil h.le L (p (k + 34)) ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) (p (k + 34 + 2)) = 2 := by
    rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega
  have hWhs : whv h (p (k + 34)) (p (k + 34 + 2)) ≤ stab (puAmalgam h.le) (p (k + 34)) :=
    (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans (qv_le_stab _ _)
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxl : ∀ l ∈ Ltil h.le L (p (k + 34)), ⁅x, l⁆ = 1 := fun l hl => by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp hxC l hl).symm
  have hxW : x ∈ whv h (p (k + 34)) (p (k + 34 + 2)) := by
    refine mem_of_forall_commutator_eq_one h₁t h₂t hinf3 ?_ hLs hLt (hF7 hxV) hxl
    refine sup_le ?_ hWhs
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_sup
      (S4A.le_normalizer_conjCl _ _) (S4A.le_normalizer_conjCl _ _))).trans
      ((le_sup_left.trans hXQ).trans (qv_le_stab _ _))
  have hxVh : x ∈ Vcirc h.le L (p (k + 34)) ⊔ ZM _ (p (k + 34)) :=
    mem_of_forall_commutator_eq_one h₁m h₂m hinf2 ((le_sup_left.trans hsup2.le).trans hWhs) hLs
      hLt (hsup2 ▸ hxW) hxl
  have hxZ : x ∈ ZM (puAmalgam h.le) (p (k + 34)) :=
    mem_z_of_forall_commutator_mem' hd hLt hxVh fun l hl => by rw [hxl l hl]; exact one_mem _
  refine hC1 (Subgroup.mem_inf.mpr ⟨hxV, ?_⟩)
  rw [c.zloc_eq_zm_inf_centralizer hα]
  exact Subgroup.mem_inf.mpr ⟨hxZ, hxC⟩

theorem center_le_uloc_sup_hloc (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    (hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a)) :
    centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hZ := c.center_le_zm h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hQs : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hUZ : Uloc h.le L (p a) ≤ ZM _ (p a) := uloc_le_zm h c.full hα
  have hZQ : ZM (puAmalgam h.le) (p a) ≤ Qv _ (p a) :=
    zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUn : Uloc h.le L (p a) ≤ Subgroup.normalizer (Zloc h.le L (p a) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hUL : ⁅Uloc h.le L (p a), Ltil h.le L (p a)⁆ = Uloc h.le L (p a) :=
    c.commutator_uloc_ltil hα
  have hUV : Uloc h.le L (p a) ≤ ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans hZQ) le_rfl
  have hle : centerOf ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ ≤
      ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ ⊓ ZM _ (p a) := le_inf inf_le_left hZ
  rw [zm_eq_uloc_sup_zloc h c.full hα, inf_comm, sup_inf_eq_of_le hUV hUn] at hle
  exact hle.trans (sup_le_sup_left (by rw [inf_comm]; exact hC1) _)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
