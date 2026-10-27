module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace T4213N

theorem autOn_le_of_acts {A B W : Subgroup G} (hB : B ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ a ∈ A, ∃ b ∈ B, ∀ w ∈ W, a * w * a⁻¹ = b * w * b⁻¹) : autOn A W ≤ autOn B W := by
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  obtain ⟨b, hbB, hb⟩ := h g hgA
  refine Setup.mem_autOn_iff.mpr ⟨⟨b, hB hbB⟩, hbB, ?_⟩
  ext w
  rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
  exact (hb w w.2).symm

theorem autOn_eq_of_acts {A B W : Subgroup G} (hA : A ≤ Subgroup.normalizer (W : Set G))
    (hB : B ≤ Subgroup.normalizer (W : Set G))
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w ∈ W, a * w * a⁻¹ = b * w * b⁻¹)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w ∈ W, b * w * b⁻¹ = a * w * a⁻¹) : autOn A W = autOn B W :=
  le_antisymm (autOn_le_of_acts hB hAB) (autOn_le_of_acts hA hBA)

@[expose] noncomputable def rhoAut {A W : Subgroup G} (hAW : A ≤ Subgroup.normalizer (W : Set G)) :
    ↥A →* ↥(autOn A W) where
  toFun a := ⟨conjAct W ⟨a, hAW a.2⟩, Setup.mem_autOn_iff.mpr ⟨⟨a, hAW a.2⟩, a.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext w
    simp [Setup.coe_conjAct_apply]
  map_mul' a b := by
    apply Subtype.ext
    ext w
    simp only [Subgroup.coe_mul, MulAut.mul_apply]
    rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
    simp only [mul_inv_rev]
    group

theorem rhoAut_apply {A W : Subgroup G} (hAW : A ≤ Subgroup.normalizer (W : Set G)) (a : ↥A)
    (w : ↥W) : (((rhoAut hAW a : ↥(autOn A W)) : MulAut ↥W) w : G) = a * w * (a : G)⁻¹ :=
  Setup.coe_conjAct_apply _ _

theorem rhoAut_surjective {A W : Subgroup G} (hAW : A ≤ Subgroup.normalizer (W : Set G)) :
    Function.Surjective (rhoAut hAW) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  exact ⟨⟨g, hg⟩, rfl⟩

theorem realizes_of_equiv {A W : Subgroup G} [IsMulCommutative ↥W]
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (D : FFModel) (hsec : ∀ x, x ∈ D.sec)
    (hker0 : ∀ x, x ∈ D.ker ↔ x = 1) (hact1 : ∀ γ, D.act γ 1 = 1) (α : ↥A →* D.Gam)
    (hα : Function.Surjective α)
    (hker : ∀ a : ↥A, α a = 1 → (a : G) ∈ Subgroup.centralizer (W : Set G))
    (f : ↥W ≃* D.Amb)
    (hf : ∀ (a : ↥A) (w w' : ↥W), (w' : G) = a * w * (a : G)⁻¹ → f w' = D.act (α a) (f w)) :
    D.Realizes (autOn A W) ⊤ ⊥ := by
  set ρ := rhoAut hAW with hρ
  have hle : α.ker ≤ ρ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    apply Subtype.ext
    exact InternalSec.conjAct_eq_one_of_mem_centralizer _ (hker a ha)
  set e := QuotientGroup.quotientKerEquivOfSurjective α hα with he
  set π : D.Gam →* ↥(autOn A W) :=
    (QuotientGroup.lift α.ker ρ hle).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ a : ↥A, π (α a) = ρ a := by
    intro a
    have h1 : e.symm (α a) = (a : ↥A ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro χ
    obtain ⟨a, rfl⟩ := rhoAut_surjective hAW χ
    exact ⟨α a, hπα a⟩
  set β : ↥(⊤ : Subgroup ↥W) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
      ((f.toMonoidHom.codRestrict D.sec fun _ => hsec _).comp (⊤ : Subgroup ↥W).subtype) with hβ
  have hβapp : ∀ u : ↥(⊤ : Subgroup ↥W),
      β u = QuotientGroup.mk (⟨f (u : ↥W), hsec _⟩ : ↥D.sec) := fun _ => rfl
  have hmk : ∀ x y : ↥D.sec, (QuotientGroup.mk x : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
      QuotientGroup.mk y ↔ x = y := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hker0,
      inv_mul_eq_one]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  refine ⟨π, hπs, bot_le, fun x _ => hsec x, fun _ _ _ => trivial, ?_, fun _ x _ => hsec _,
    ?_, β, ?_, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ x hx
    rw [hker0] at hx ⊢
    rw [hx, hact1]
  · intro y
    obtain ⟨⟨y, -⟩, rfl⟩ := QuotientGroup.mk'_surjective (D.ker.subgroupOf D.sec) y
    refine ⟨⟨f.symm y, trivial⟩, ?_⟩
    rw [hβapp, QuotientGroup.mk'_apply]
    congr 1
    exact Subtype.ext (f.apply_symm_apply y)
  · intro u
    rw [hβapp, Subgroup.mem_bot]
    have h1 : (QuotientGroup.mk (⟨f (u : ↥W), hsec _⟩ : ↥D.sec) :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ f (u : ↥W) = 1 := by
      rw [show (1 : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk 1 from rfl, hmk]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, MulEquiv.map_eq_one_iff]
  · intro γ u m hu hm hum
    obtain ⟨a, rfl⟩ := hα γ
    rw [hβapp] at hum
    have hfu : f (u : ↥W) = m := congrArg Subtype.val ((hmk _ _).mp hum)
    rw [hβapp]
    apply (hmk _ _).mpr
    apply Subtype.ext
    show f (((π (α a) : ↥(autOn A W)) : MulAut ↥W) (u : ↥W)) = D.act (α a) m
    rw [← hfu]
    apply hf a (u : ↥W)
    rw [hπα, rhoAut_apply]

end T4213N

end CFSG.Quasithin.H13.Ch4
