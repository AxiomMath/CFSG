module

public import CFSG.Quasithin.MS93.M15LiftGen
public import CFSG.Quasithin.MS93.RedCrit
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement IsMulCommutative Matrix

namespace Sp4L

section Kernel

variable {G : Type} [Group G] {M T L : Subgroup G}

@[expose] def kerM {H : Type*} [Group H] (a : ↥M →* H) : Subgroup G := a.ker.map M.subtype

theorem mem_kerM {H : Type*} [Group H] {a : ↥M →* H} {g : G} :
    g ∈ kerM a ↔ ∃ hg : g ∈ M, a ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem kerM_le {H : Type*} [Group H] (a : ↥M →* H) : kerM a ≤ M := Subgroup.map_subtype_le _

theorem le_normalizer_kerM {H : Type*} [Group H] (a : ↥M →* H) :
    M ≤ Subgroup.normalizer (kerM a : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ kerM a, m * x * m⁻¹ ∈ kerM a := by
    intro m hm x hx
    obtain ⟨hxM, hx1⟩ := mem_kerM.1 hx
    refine mem_kerM.2 ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), ?_⟩
    have e : (⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)⟩ : ↥M) =
        ⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := rfl
    rw [e, map_mul, map_mul, hx1, mul_one, map_inv, mul_inv_cancel]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

variable {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem comm_mem_of_mem_kerM
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      a false 1) {y : G} (hy : y ∈ kerM a) {u : G} (hu : u ∈ Uq M T L) :
    y * u * y⁻¹ * u⁻¹ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hyM, hy1⟩ := mem_kerM.1 hy
  obtain ⟨hMU, -, β, -, hβk, hβeq⟩ := hnat
  have hyu : y * u * y⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hMU hyM) u).1 hu
  have h1 := hβeq ⟨y, hyM⟩ ⟨u, hu⟩ ⟨y * u * y⁻¹, hyu⟩ rfl
  have h2 : β ⟨y * u * y⁻¹, hyu⟩ = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [h1 i, hy1]
    simp [moduleAct]
  have h3 : (⟨y * u * y⁻¹, hyu⟩ : ↥(Uq M T L)) * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at h3
  exact h3

variable [Finite G] (h : PUHyp M T L)
include h

theorem uq_comm {u v : G} (hu : u ∈ Uq M T L) (hv : v ∈ Uq M T L) : u * v = v * u :=
  A4.mul_comm_of_mem_omegaOneCenterOf (h.Uq_le_Xq hu) (h.Uq_le_Xq hv)

theorem uq_sq {u : G} (hu : u ∈ Uq M T L) : u ^ 2 = 1 :=
  A4.sq_eq_one_of_mem_omegaOneCenterOf (h.Uq_le_Xq hu)

theorem isMulCommutative_uq : IsMulCommutative ↥(Uq M T L) :=
  ⟨⟨fun x y => Subtype.ext (uq_comm h x.2 y.2)⟩⟩

theorem exists_pow_mem_L {m : G} (hm : m ∈ M) : ∃ e : ℕ, m ^ 2 ^ e ∈ L := by
  have hTM : T ≤ M := h.le
  set L' : Subgroup ↥M := L.subgroupOf M
  have hL' : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L' ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le hTM, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hmem : (⟨m, hm⟩ : ↥M) ∈ L' ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  obtain ⟨e, he⟩ := h.isPGroup ⟨(t : G), ht⟩
  refine ⟨e, ?_⟩
  have hq : (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ L') = QuotientGroup.mk t := by
    rw [← hlt, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  have h1 : (QuotientGroup.mk ((⟨m, hm⟩ : ↥M) ^ 2 ^ e) : ↥M ⧸ L') = 1 := by
    rw [QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow]
    have ht' : t ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
    rw [ht', QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h1
  simpa [L', Subgroup.mem_subgroupOf] using h1

theorem not_le_kerM
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      a false 1) : ¬ L ≤ kerM a := by
  intro hL
  have hUL : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 := comm_mem_of_mem_kerM hnat (hL hl) (inv_mem hu)
    have hc : l * u⁻¹ * l⁻¹ * u⁻¹⁻¹ ∈ Uq M T L := h1.1
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹ * u⁻¹⁻¹) * u⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, uq_comm h hu hc, mul_inv_cancel_right]
    exact h1.2
  have h2 : Uq M T L = ⊥ := by
    have e1 := h.commutator_uq
    have h3 : ⁅⁅Uq M T L, L⁆, L⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx l hl
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 (hUL hx) l hl).symm
    rw [e1, e1] at h3
    exact h3
  apply h.not_le_centralizer_Z0q
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact h2

theorem kerM_le_centralizer
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      a false 1) : kerM a ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  intro y hy
  have hcomm : ⁅kerM a, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (kerM_le a) (le_normalizer_kerM a) (not_le_kerM h hnat)
  have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) :=
    h.pCoreOf_le_centralizer_Z0q.trans (Subgroup.centralizer_le (Uq_le_Z0q h.L_le))
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have key : ∀ u ∈ Uq M T L, ∀ l ∈ L, y * ⁅u, l⁆ * y⁻¹ = ⁅u, l⁆ := by
    intro u hu l hl
    set c := y * u * y⁻¹ * u⁻¹ with hc
    set n := y * l * y⁻¹ * l⁻¹ with hn
    have hcUL := comm_mem_of_mem_kerM hnat hy hu
    have hnU : n ∈ Subgroup.centralizer (Uq M T L : Set G) := by
      apply hQ
      apply hcomm
      have := Subgroup.commutator_mem_commutator hy hl
      rwa [commutatorElement_def] at this
    have hw : l * u⁻¹ * l⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hMU (h.L_le hl)) _).1 (inv_mem hu)
    have hcl : l * c⁻¹ * l⁻¹ = c⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hcUL.2 l hl
      calc l * c⁻¹ * l⁻¹ = (l * c * l⁻¹)⁻¹ := by group
        _ = c⁻¹ := by rw [this, mul_inv_cancel_right]
    have hnw : ∀ w ∈ Uq M T L, n * w * n⁻¹ = w := fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.1 hnU w hw, mul_inv_cancel_right]
    have hwc : l * u⁻¹ * l⁻¹ * c⁻¹ ∈ Uq M T L := mul_mem hw (inv_mem hcUL.1)
    have e0 : y * ⁅u, l⁆ * y⁻¹ = (c * u) * (n * l) * (c * u)⁻¹ * (n * l)⁻¹ := by
      simp only [hc, hn, commutatorElement_def]
      group
    rw [e0]
    calc (c * u) * (n * l) * (c * u)⁻¹ * (n * l)⁻¹ =
        c * u * (n * ((l * u⁻¹ * l⁻¹) * (l * c⁻¹ * l⁻¹)) * n⁻¹) := by group
      _ = c * u * (n * (l * u⁻¹ * l⁻¹ * c⁻¹) * n⁻¹) := by rw [hcl]
      _ = c * u * (l * u⁻¹ * l⁻¹ * c⁻¹) := by rw [hnw _ hwc]
      _ = u * c * (l * u⁻¹ * l⁻¹ * c⁻¹) := by rw [uq_comm h hcUL.1 hu]
      _ = u * (c * (l * u⁻¹ * l⁻¹)) * c⁻¹ := by group
      _ = u * ((l * u⁻¹ * l⁻¹) * c) * c⁻¹ := by rw [uq_comm h hcUL.1 hw]
      _ = ⁅u, l⁆ := by
          simp only [commutatorElement_def]
          group
  have hle : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    calc y * ⁅u, l⁆ = y * ⁅u, l⁆ * y⁻¹ * y := by group
      _ = ⁅u, l⁆ * y := by rw [key u hu l hl]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rw [← h.commutator_uq] at hu
  exact ((Subgroup.mem_centralizer_iff.1 (hle hu)) y rfl).symm

end Kernel

section Module

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}
  (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
    a false 1)
include h hnat

theorem exists_pi (hsurj : Function.Surjective a) :
    ∃ π : ↥(StatedSp 2 F) →* ↥(autOn M (Uq M T L)), Function.Surjective π ∧
    ∀ m : ↥M, ((π (a m) : ↥(autOn M (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨m, le_normalizer_Uq h.le_normalizer m.2⟩ := by
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  let χ : ↥M →* ↥(autOn M (Uq M T L)) :=
    ((conjAct (Uq M T L)).comp (Subgroup.inclusion hMU)).codRestrict (autOn M (Uq M T L))
      (fun m => Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hMU m, m.2, rfl⟩)
  have hker : a.ker ≤ χ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct (Uq M T L) (Subgroup.inclusion hMU m) = 1
    apply InternalSec.conjAct_eq_one_of_mem_centralizer
    exact kerM_le_centralizer h hnat (mem_kerM.2 ⟨m.2, hm⟩)
  let π := (QuotientGroup.lift a.ker χ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective a hsurj).symm.toMonoidHom
  have hπa : ∀ m, π (a m) = χ m := by
    intro m
    have e : (QuotientGroup.quotientKerEquivOfSurjective a hsurj).symm (a m) =
        QuotientGroup.mk m := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift a.ker χ hker
      ((QuotientGroup.quotientKerEquivOfSurjective a hsurj).symm (a m)) = χ m
    rw [e, QuotientGroup.lift_mk]
  refine ⟨π, fun x => ?_, fun m => by rw [hπa]; rfl⟩
  obtain ⟨g, hgM, hgx⟩ := Setup.mem_autOn_iff.1 x.2
  refine ⟨a ⟨g, hgM⟩, ?_⟩
  rw [hπa]
  apply Subtype.ext
  rw [← hgx]
  rfl

theorem realizesVia_nat (hsurj : Function.Surjective a) [IsMulCommutative ↥(Uq M T L)]
    {π : ↥(StatedSp 2 F) →* ↥(autOn M (Uq M T L))} (hπs : Function.Surjective π)
    (hπa : ∀ m : ↥M, ((π (a m) : ↥(autOn M (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨m, le_normalizer_Uq h.le_normalizer m.2⟩) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia (autOn M (Uq M T L)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) π := by
  obtain ⟨-, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hnat
  let β₁ : ↥(Uq M T L) →* Multiplicative (Fin 2 ⊕ Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0)
      map_one' := by simp
      map_mul' := fun u v => by simp }
  have hβ₁ : ∀ u, β₁ u = Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0) := fun _ => rfl
  have hβ₁s : Function.Surjective β₁ := by
    intro x
    obtain ⟨u, hu⟩ := hβ₀s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd x)
    exact ⟨u, by rw [hβ₁, hu]; rfl⟩
  have hβ₁k : ∀ u, β₁ u = 1 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro u
    have e1 : β₁ u = 1 ↔ β₀ u = 1 := by
      constructor
      · intro h1
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact congrArg Multiplicative.toAdd h1
      · intro h1
        rw [hβ₁, h1]
        rfl
    rw [e1, ← MonoidHom.mem_ker, hβ₀k, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hβ₁e : ∀ (m : ↥M) (u v : ↥(Uq M T L)), (v : G) = m * u * m⁻¹ →
      β₁ v = Multiplicative.ofAdd ((((a m : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β₁ u)) := by
    intro m u v huv
    have := hβ₀e m u v huv 0
    rw [hβ₁, hβ₁, this]
    simp [moduleAct]
  have hY : M ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_centralizer h.le_normalizer)
  have hstab := InternalSec.autOn_le_stabSub hY
  refine ⟨hπs, le_top, bot_le, fun _ _ _ => Subgroup.mem_top _, fun x z hz => (hstab x.2 z).2 hz,
    (FFModel.nat_isActionModel _).sec_inv, (FFModel.nat_isActionModel _).ker_inv, ?_⟩
  let β : ↥(⊤ : Subgroup ↥(Uq M T L)) →* (FFModel.nat (StatedSp 2 F)).Sec :=
    (QuotientGroup.mk' _).comp
      (Subgroup.topEquiv.symm.toMonoidHom.comp (β₁.comp (⊤ : Subgroup ↥(Uq M T L)).subtype))
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥(Uq M T L)),
      β u = QuotientGroup.mk ⟨β₁ u, Subgroup.mem_top _⟩ := fun _ => rfl
  refine ⟨β, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨⟨x, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hβ₁s x
    exact ⟨⟨u, Subgroup.mem_top _⟩, by rw [hβ]; congr 1; exact Subtype.ext hu⟩
  · rw [hβ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show β₁ u ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → F))) ↔ _
    rw [Subgroup.mem_bot, hβ₁k, Subgroup.mem_subgroupOf]
  · rw [hβ] at hum ⊢
    have h3 : (⟨β₁ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat (StatedSp 2 F)).sec) = m := by
      have h1 := QuotientGroup.eq.1 hum
      exact inv_mul_eq_one.1 (Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)))
    subst h3
    congr 1
    apply Subtype.ext
    obtain ⟨m₀, rfl⟩ := hsurj γ
    have hval : ((((π (a m₀) : ↥(autOn M (Uq M T L))) : MulAut ↥(Uq M T L)) (u : ↥(Uq M T L)) :
        ↥(Uq M T L)) : G) = (m₀ : G) * ((u : ↥(Uq M T L)) : G) * (m₀ : G)⁻¹ := by
      rw [hπa]
      exact InternalSec.coe_conjAct_apply _ _
    exact hβ₁e m₀ (u : ↥(Uq M T L)) _ hval

omit hnat in
theorem exists_pow_mem_autOn {x : MulAut ↥(Uq M T L)} (hx : x ∈ autOn M (Uq M T L)) :
    ∃ e : ℕ, x ^ 2 ^ e ∈ autOn L (Uq M T L) := by
  obtain ⟨g, hgM, rfl⟩ := Setup.mem_autOn_iff.1 hx
  obtain ⟨e, he⟩ := exists_pow_mem_L h hgM
  exact ⟨e, Setup.mem_autOn_iff.2 ⟨g ^ 2 ^ e, by simpa using he, by rw [map_pow]⟩⟩

theorem autOn_le_of_four_le (hsurj : Function.Surjective a) [Finite F] (hF : 4 ≤ Nat.card F) :
    autOn M (Uq M T L) ≤ autOn L (Uq M T L) := by
  have : Group.IsPerfect (StatedSp 2 F) := isPerfect_statedSp hF
  have : Finite ↥(StatedSp 2 F) := Subtype.finite
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have : ((L.subgroupOf M).map a).Normal := hLn.map a hsurj
  have htop : (L.subgroupOf M).map a = ⊤ := eq_top_of_isPerfect fun g => by
    obtain ⟨m, rfl⟩ := hsurj g
    obtain ⟨e, he⟩ := exists_pow_mem_L h m.2
    exact ⟨e, ⟨m ^ 2 ^ e, Subgroup.mem_subgroupOf.2 (by simpa using he), map_pow a m _⟩⟩
  intro x hx
  obtain ⟨g, hgM, rfl⟩ := Setup.mem_autOn_iff.1 hx
  have hg : a ⟨g, hgM⟩ ∈ (L.subgroupOf M).map a := htop ▸ Subgroup.mem_top _
  obtain ⟨l, hl, hla⟩ := hg
  have hk : (l : G)⁻¹ * g ∈ kerM a := by
    refine mem_kerM.2 ⟨M.mul_mem (M.inv_mem l.2) hgM, ?_⟩
    have e : (⟨(l : G)⁻¹ * g, M.mul_mem (M.inv_mem l.2) hgM⟩ : ↥M) = l⁻¹ * ⟨g, hgM⟩ := rfl
    rw [e, map_mul, map_inv, hla, inv_mul_cancel]
  have hc := kerM_le_centralizer h hnat hk
  refine Setup.mem_autOn_iff.2 ⟨⟨l, hMU l.2⟩, Subgroup.mem_subgroupOf.1 hl, ?_⟩
  ext u
  rw [InternalSec.coe_conjAct_apply, InternalSec.coe_conjAct_apply]
  have hcu := Subgroup.mem_centralizer_iff.1 hc (u : G) u.2
  calc (l : G) * u * (l : G)⁻¹ =
        (l : G) * ((u : G) * ((l : G)⁻¹ * g)) * ((l : G)⁻¹ * g)⁻¹ * (l : G)⁻¹ := by group
    _ = (l : G) * (((l : G)⁻¹ * g) * u) * ((l : G)⁻¹ * g)⁻¹ * (l : G)⁻¹ := by rw [hcu]
    _ = (g : G) * u * (g : G)⁻¹ := by group

end Module

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem le_fixV_of_card_le_two {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {C : Subgroup V} [Finite C] (hinv : ∀ x ∈ H, ∀ c ∈ C, x c ∈ C) (h2 : Nat.card C ≤ 2) :
    C ≤ fixV H := by
  intro c hc x hx
  by_contra hne
  have hc1 : c ≠ 1 := fun h => hne (by rw [h, map_one])
  have hxc1 : x c ≠ 1 := fun h => hc1 (by
    have := congrArg x.symm h
    rwa [MulEquiv.symm_apply_apply, map_one] at this)
  have hinj : Function.Injective
      (![⟨1, C.one_mem⟩, ⟨c, hc⟩, ⟨x c, hinv x hx c hc⟩] : Fin 3 → ↥C) := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij'.symm hc1
      | exact absurd hij' hc1
      | exact absurd hij'.symm hxc1
      | exact absurd hij' hxc1
      | exact absurd hij'.symm hne
      | exact absurd hij' hne
  have h3 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

theorem sp4Lift_of_nat (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hk : 1 ≤ k) (hF : Fintype.card F = 2 ^ k)
    (hsurj : Function.Surjective a)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      a false 1) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ k ∧
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) =
        Uq M T L ⊓ Subgroup.centralizer (M : Set G) ∧
      ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
        m * u * m⁻¹ = u := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hF]
  have := isMulCommutative_uq h
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨π, hπs, hπa⟩ := exists_pi h hnat hsurj
  have hreal := realizesVia_nat h hnat hsurj hπs hπa
  have hV : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using uq_sq h w.2)
  have hUM : ⁅Uq M T L, M⁆ = Uq M T L :=
    le_antisymm (commutator_le_left_of_le_normalizer hMU)
      (h.commutator_uq.symm.le.trans (Subgroup.commutator_mono le_rfl h.L_le))
  have hcommM : commV (autOn M (Uq M T L)) = ⊤ := InternalSec.commV_autOn_eq_top hMU hUM
  have hCL : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn L (Uq M T L)) := InternalSec.le_fixV_autOn inf_le_right
  have hCM : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn M (Uq M T L)) := by
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    ·
      have hS : SymmetricNatural (autOn M (Uq M T L)) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) 6 :=
        asSp4S6 _ _ _ _ ⟨F, inferInstance, inferInstance, hFn, ⟨π, hreal⟩⟩
      have hder : ⁅autOn M (Uq M T L), autOn M (Uq M T L)⁆ ≤ autOn L (Uq M T L) := by
        obtain ⟨π₆, hπ₆⟩ := hS
        let ψ : Equiv.Perm (Fin 6) →* MulAut ↥(Uq M T L) := (autOn M (Uq M T L)).subtype.comp π₆
        have hrange : ψ.range = autOn M (Uq M T L) := by
          ext x
          constructor
          · rintro ⟨g, rfl⟩
            exact (π₆ g).2
          · intro hx
            obtain ⟨g, hg⟩ := hπ₆.1 ⟨x, hx⟩
            refine ⟨g, ?_⟩
            show ((π₆ g : ↥(autOn M (Uq M T L))) : MulAut ↥(Uq M T L)) = x
            rw [hg]
        have hA : ⁅(⊤ : Subgroup (Equiv.Perm (Fin 6))), ⊤⁆ =
            Subgroup.closure {σ : Equiv.Perm (Fin 6) | σ.IsThreeCycle} := by
          rw [Equiv.Perm.closure_three_cycles_eq_alternating,
            ← alternatingGroup.commutator_perm_eq (by simp)]
          rfl
        rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hA,
          MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨σ, hσ, rfl⟩
        have h3 : ψ σ ^ 3 = 1 := by
          rw [← map_pow, ← hσ.orderOf, pow_orderOf_eq_one, map_one]
        obtain ⟨e, he⟩ := exists_pow_mem_autOn h (show ψ σ ∈ autOn M (Uq M T L) from
          (π₆ σ).2)
        exact mem_of_pow_three h3 he
      have hcard := card_le_two_of_symNatural hV hS
        (fun v hv x hx => hCL hv x (hder hx)) hcommM
      exact le_fixV_of_card_le_two (fun x hx c hc => (hreal.2.2.2.2.1 ⟨x, hx⟩ c hc)) hcard
    ·
      have h4 : 4 ≤ Nat.card F := by
        rw [hFn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have hle := autOn_le_of_four_le h hnat hsurj h4
      exact fun c hc x hx => hCL hc x (hle hx)
  obtain ⟨hcardC, hlift⟩ := lift_of_realizes hFn hk hV hCM hcommM hreal
  refine ⟨?_, ?_, ?_⟩
  · have e : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) =
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective (Uq M T L).subtype_injective]
    rw [← e]
    exact hcardC
  · apply le_antisymm
    · intro c hc
      refine Subgroup.mem_inf.2 ⟨hc.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hfix := hCM (show (⟨c, hc.1⟩ : ↥(Uq M T L)) ∈
          (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) from hc.2)
        (conjAct (Uq M T L) ⟨m, hMU hm⟩) (Setup.mem_autOn_iff.2 ⟨⟨m, hMU hm⟩, hm, rfl⟩)
      have e := congrArg Subtype.val hfix
      rw [InternalSec.coe_conjAct_apply] at e
      calc m * c = m * c * m⁻¹ * m := by group
        _ = c * m := by rw [e]
    · exact inf_le_inf_left _ (Subgroup.centralizer_le h.L_le)
  · intro m hm u hu hmu
    have hx : conjAct (Uq M T L) ⟨m, hMU hm⟩ ∈ autOn M (Uq M T L) :=
      Setup.mem_autOn_iff.2 ⟨⟨m, hMU hm⟩, hm, rfl⟩
    have hval : ((conjAct (Uq M T L) ⟨m, hMU hm⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) = m * u * m⁻¹ :=
      InternalSec.coe_conjAct_apply _ _
    have hxw : conjAct (Uq M T L) ⟨m, hMU hm⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈
        (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
      rw [Subgroup.mem_subgroupOf]
      show ((conjAct (Uq M T L) ⟨m, hMU hm⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) * u⁻¹ ∈ _
      rw [hval]
      exact hmu
    have := hlift _ hx ⟨u, hu⟩ hxw
    rw [← hval, this]

end Main

end Sp4L

theorem sp4Lift_holds :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
        (1 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective a ∧
          IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
            a false 1) →
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ k ∧
        Uq M T L ⊓ Subgroup.centralizer (L : Set G) =
          Uq M T L ⊓ Subgroup.centralizer (M : Set G) ∧
        ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
          m * u * m⁻¹ = u := by
  intro G _ _ M T L h k F _ _ a ⟨hk, hF, hsurj, hnat⟩
  exact Sp4L.sp4Lift_of_nat h hk hF hsurj hnat

end CFSG.Quasithin.MS93
