module

public import CFSG.Quasithin.H13.A6S1372SixteenTilde
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S1384a
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6.L13825

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem isElemAbelian_UH {S : Setting4 G T L V} (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) : IsElemAbelian 2 (conjClosure S.V3 H) := by
  have hUV : conjClosure S.V3 H ≤ conjClosure V S.G1 := conjClosure_mono S.V3_le_V hH.2.1
  have hle : ∀ {k : G}, k ∈ H → conjSub k S.V3 ≤ conjClosure V S.G1 := fun {k} hk x hx =>
    hUV (HypF91.conjSub_le_conjClosure hk hx)
  have hcomm := hS.hab
  refine HypF91.isElemAbelian_conjClosure_of_forall
    (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) fun k hk z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : y ∈ conjClosure V S.G1 := hle hk hy
  have h2 : z ∈ conjClosure V S.G1 := le_conjClosure _ _ (S.V3_le_V hz)
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨y, h1⟩ ⟨z, h2⟩)

theorem card_commV_of_transvectionWith {W : Type} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {t : MulAut W} {w : W} (h : IsTransvectionWith t w) (ht : t ≠ 1) :
    Nat.card ↥(commV (Subgroup.zpowers t)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heq : commV (Subgroup.zpowers t) = Subgroup.zpowers w := by
    rw [commV_zpowers_eq_map]
    apply le_antisymm
    · rintro _ ⟨v, -, rfl⟩
      rw [commHom_apply]
      rcases h.2 v with h1 | h1
      · rw [h1, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h1, mul_comm v w, mul_inv_cancel_right]
        exact Subgroup.mem_zpowers w
    · rw [Subgroup.zpowers_le]
      obtain ⟨v, hv⟩ := CFSG.Quasithin.B1.exists_moved_of_ne_one ht
      have h1 : t v = v * w := (h.2 v).resolve_left hv
      exact ⟨v, Subgroup.mem_top v, by rw [commHom_apply, h1, mul_comm v w, mul_inv_cancel_right]⟩
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime (hW2 w) h.1

section Act

variable {S : Setting4 G T L V} {H : Subgroup G} (hH : H ∈ S.Hz)
  [IsMulCommutative ↥(conjClosure S.V3 H)]

noncomputable abbrev sigmaH : ↥H →* MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
  A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (Setting4.le_normalizer_UV1 hH)

theorem autSec_eq_map {X : Subgroup G} (hXH : X ≤ H) :
    autSec (autOn X (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) =
      (X.subgroupOf H).map (sigmaH hH) := by
  ext ψ
  rw [A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H) (Setting4.le_normalizer_UV1 hH)
    hXH, Subgroup.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩

theorem sigmaH_eq_one_iff (hF : HypF91 T V L (fsuV1 T V) S.V3 H) (x : ↥H) :
    sigmaH hH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [A6Mod.secAct_eq_one_iff, hF.pCoreOf_eq_centralizerMod]
  exact ⟨fun h1 => ⟨x.2, hF.H_normalizes_V₁ x.2, h1⟩, fun h1 => h1.2.2⟩

theorem exists_transvectionWith_sigmaH {h : G} (hh : h ∈ H)
    (htr : InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) :
    sigmaH hH ⟨h, hh⟩ ≠ 1 ∧ ∃ w, IsTransvectionWith (sigmaH hH ⟨h, hh⟩) w := by
  obtain ⟨hnot, c, hc⟩ := htr
  push Not at hnot
  obtain ⟨x₀, hx₀, hd⟩ := hnot
  set U := conjClosure S.V3 H with hU
  have hconj : ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) u).mp hu
  have hcomm : ∀ u ∈ U, h * u * h⁻¹ * u⁻¹ ∈ U := fun u hu => U.mul_mem (hconj u hu) (U.inv_mem hu)
  have hd' := (hc x₀ hx₀).resolve_left hd
  refine ⟨fun h1 => hd ((A6Mod.secAct_eq_one_iff (le_normalizer_conjClosure S.V3 H)
    (Setting4.le_normalizer_UV1 hH) ⟨h, hh⟩).mp h1 x₀ hx₀), ?_⟩
  refine ⟨InternalSec.secMk ((fsuV1 T V).subgroupOf U) ⟨_, hcomm x₀ hx₀⟩,
    fun h1 => hd ((A6Mod.secMk_eq_one_iff _).mp h1), fun v => ?_⟩
  obtain ⟨⟨u, hu⟩, rfl⟩ := InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf U) v
  have hact : sigmaH hH ⟨h, hh⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf U) ⟨u, hu⟩) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf U) ⟨h * u * h⁻¹, hconj u hu⟩ := by
    rw [A6Mod.secAct_secMk]
    congr 1
  rw [hact]
  rcases hc u hu with h1 | h1
  · left
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
    exact h1
  · right
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      mul_right_comm, A6Mod.secMk_eq_one_iff]
    show h * u * h⁻¹ * u⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹)⁻¹ ∈ fsuV1 T V
    have e : h * u * h⁻¹ * u⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹)⁻¹ =
        (h * u * h⁻¹ * u⁻¹ * c⁻¹) * (h * x₀ * h⁻¹ * x₀⁻¹ * c⁻¹)⁻¹ := by group
    rw [e]
    exact (fsuV1 T V).mul_mem h1 ((fsuV1 T V).inv_mem hd')

end Act

end CFSG.Quasithin.H13.A6.L13825
