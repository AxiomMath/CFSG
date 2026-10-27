module

public import CFSG.Quasithin.Background.SmithB51SL3Lin
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section FixSec

variable {V : Type*} [CommGroup V]

@[expose] def fixSec (B : Subgroup (MulAut V)) (W U : Subgroup V) : Subgroup V where
  carrier := {w | w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ U}
  one_mem' := ⟨W.one_mem, fun _ _ => by simp [U.one_mem]⟩
  mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, fun b hb => by
    have : b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [this]
    exact U.mul_mem (hx.2 b hb) (hy.2 b hb)⟩
  inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, fun b hb => by
    have : b x⁻¹ * x⁻¹⁻¹ = (b x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [this]
    exact U.inv_mem (hx.2 b hb)⟩

theorem mem_fixSec {B : Subgroup (MulAut V)} {W U : Subgroup V} {w : V} :
    w ∈ fixSec B W U ↔ w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ U := Iff.rfl

theorem fixSec_le (B : Subgroup (MulAut V)) (W U : Subgroup V) : fixSec B W U ≤ W :=
  fun _ hw => hw.1

theorem le_fixSec {B : Subgroup (MulAut V)} {W U : Subgroup V} (hUW : U ≤ W)
    (hBU : B ≤ stabSub U) : U ≤ fixSec B W U :=
  fun u hu => ⟨hUW hu, fun _ hb => U.mul_mem ((hBU hb u).2 hu) (U.inv_mem hu)⟩

theorem card_fixV_autSec_mul [Finite V] {B : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W) (hBW : B ≤ stabSub W) (hBU : B ≤ stabSub U) :
    Nat.card (fixV (autSec B W U)) * Nat.card U = Nat.card (fixSec B W U) := by
  set F := (fixSec B W U).subgroupOf W with hF
  set q := QuotientGroup.mk' (U.subgroupOf W) with hq
  have h1 := B1More.card_map_mul_card_inf_ker F q
  have hmap : F.map q = fixV (autSec B W U) := by
    ext s
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    constructor
    · rintro ⟨w', hw', hww'⟩
      rw [← hww']
      apply mk_mem_fixV_autQuot.2
      intro g hg _
      obtain ⟨b, hbB, rfl⟩ := mem_autSub.1 hg
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_subgroupOf.1 hw').2 b hbB
    · intro hs
      refine ⟨w, Subgroup.mem_subgroupOf.2 ⟨w.2, fun b hb => ?_⟩, rfl⟩
      have hg : resHom W ⟨b, hBW hb⟩ ∈ autSub B W := mem_autSub.2 ⟨⟨b, hBW hb⟩, hb, rfl⟩
      have := (mk_mem_fixV_autQuot.1 hs) _ hg (autSub_le_stabSub_subgroupOf hBU hg)
      rw [Subgroup.mem_subgroupOf] at this
      simpa [resHom_apply] using this
  have hker : F ⊓ q.ker = U.subgroupOf W := by
    rw [hq, QuotientGroup.ker_mk', inf_eq_right]
    intro w hw
    exact Subgroup.mem_subgroupOf.2 (le_fixSec hUW hBU (Subgroup.mem_subgroupOf.1 hw))
  have hcF : Nat.card F = Nat.card (fixSec B W U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fixSec_le B W U)).toEquiv
  have hcU : Nat.card ↥(U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  rw [hmap, hker, hcF, hcU] at h1
  exact h1

end FixSec

section Coord

variable {V : Type} [CommGroup V] {K : Type} [Field K]

theorem mem_fixSec_iff_nat {L : Subgroup (MulAut V)} {W U : Subgroup V}
    {π : ↥(StatedSL 3 K) →* ↥L} (hπ : Function.Surjective π)
    (f : ↥W →* Multiplicative (Fin 3 → K)) (hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U)
    (hfe : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) w ∈ W),
      f ⟨_, hw⟩ = natAct (StatedSL 3 K) γ (f w))
    (hLW : L ≤ stabSub W) {B : Subgroup (MulAut V)} (hBL : B ≤ L) (w : ↥W) :
    (w : V) ∈ fixSec B W U ↔
      Multiplicative.toAdd (f w) ∈ fixK ((B.subgroupOf L).comap π) := by
  have hkey : ∀ γ : ↥(StatedSL 3 K),
      ((π γ : ↥L) : MulAut V) (w : V) * (w : V)⁻¹ ∈ U ↔
        slAct γ (Multiplicative.toAdd (f w)) = Multiplicative.toAdd (f w) := by
    intro γ
    have hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := ((hLW (π γ).2) w).2 w.2
    have hmem : ((π γ : ↥L) : MulAut V) (w : V) * (w : V)⁻¹ ∈ W := W.mul_mem hw (W.inv_mem w.2)
    have hf : f ⟨_, hmem⟩ = f ⟨_, hw⟩ * (f w)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [← hfk ⟨_, hmem⟩, hf, hfe γ w hw, mul_inv_eq_one]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      exact this
    · intro h
      exact congrArg Multiplicative.ofAdd h
  constructor
  · rintro ⟨-, hB⟩ γ hγ
    exact (hkey γ).1 (hB _ (Subgroup.mem_subgroupOf.1 hγ))
  · intro hfix
    refine ⟨w.2, fun b hb => ?_⟩
    obtain ⟨γ, hγ⟩ := hπ ⟨b, hBL hb⟩
    have hγB : γ ∈ (B.subgroupOf L).comap π := by
      rw [Subgroup.mem_comap, hγ]
      exact hb
    have := (hkey γ).2 (hfix γ hγB)
    rwa [hγ] at this

@[expose] def mulSub (S : Submodule K (Fin 3 → K)) : Subgroup (Multiplicative (Fin 3 → K)) :=
  AddSubgroup.toSubgroup S.toAddSubgroup

theorem mem_mulSub {S : Submodule K (Fin 3 → K)} {x : Multiplicative (Fin 3 → K)} :
    x ∈ mulSub S ↔ Multiplicative.toAdd x ∈ S := Iff.rfl

theorem card_mulSub (S : Submodule K (Fin 3 → K)) : Nat.card (mulSub S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Fin 3 → K)), x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (y : Fin 3 → K), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable [Finite V]

omit [Finite V] in
theorem card_fixSec_nat {L : Subgroup (MulAut V)} {W U : Subgroup V}
    {π : ↥(StatedSL 3 K) →* ↥L} (hπ : Function.Surjective π)
    (f : ↥W →* Multiplicative (Fin 3 → K)) (hfs : Function.Surjective f)
    (hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U)
    (hfe : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) w ∈ W),
      f ⟨_, hw⟩ = natAct (StatedSL 3 K) γ (f w))
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hUW : U ≤ W) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    Nat.card (fixSec B W U) = Nat.card U * Nat.card (fixK ((B.subgroupOf L).comap π)) := by
  set F := (fixSec B W U).subgroupOf W with hF
  have h1 := B1More.card_map_mul_card_inf_ker F f
  have hmap : F.map f = mulSub (fixK ((B.subgroupOf L).comap π)) := by
    ext x
    obtain ⟨w, rfl⟩ := hfs x
    constructor
    · rintro ⟨w', hw', hww'⟩
      rw [← hww', mem_mulSub]
      exact (mem_fixSec_iff_nat hπ f hfk hfe hLW hBL w').1 (Subgroup.mem_subgroupOf.1 hw')
    · intro hx
      exact ⟨w, Subgroup.mem_subgroupOf.2 ((mem_fixSec_iff_nat hπ f hfk hfe hLW hBL w).2 hx),
        rfl⟩
  have hker : F ⊓ f.ker = U.subgroupOf W := by
    have hk : f.ker = U.subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, hfk, Subgroup.mem_subgroupOf]
    rw [hk, inf_eq_right]
    intro w hw
    exact Subgroup.mem_subgroupOf.2
      (le_fixSec hUW (hBL.trans hLU) (Subgroup.mem_subgroupOf.1 hw))
  have hcF : Nat.card F = Nat.card (fixSec B W U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fixSec_le B W U)).toEquiv
  have hcU : Nat.card ↥(U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  rw [hmap, hker, hcF, hcU, card_mulSub] at h1
  rw [← h1, mul_comm]

theorem card_fixV_autSec_nat {L : Subgroup (MulAut V)} {W U : Subgroup V}
    {π : ↥(StatedSL 3 K) →* ↥L} (hπ : Function.Surjective π)
    (f : ↥W →* Multiplicative (Fin 3 → K)) (hfs : Function.Surjective f)
    (hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U)
    (hfe : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) w ∈ W),
      f ⟨_, hw⟩ = natAct (StatedSL 3 K) γ (f w))
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hUW : U ≤ W) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    Nat.card (fixV (autSec B W U)) = Nat.card (fixK ((B.subgroupOf L).comap π)) := by
  have h1 := card_fixV_autSec_mul hUW (hBL.trans hLW) (hBL.trans hLU)
  rw [card_fixSec_nat hπ f hfs hfk hfe hLW hLU hUW hBL, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem card_sec_nat {W U : Subgroup V} (hUW : U ≤ W) (f : ↥W →* Multiplicative (Fin 3 → K))
    (hfs : Function.Surjective f) (hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U) [Finite K] :
    Nat.card (Sec W U) = Nat.card K ^ 3 := by
  have h1 := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥W) f
  have hmap : (⊤ : Subgroup ↥W).map f = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hfs]
  have hk : (⊤ : Subgroup ↥W) ⊓ f.ker = U.subgroupOf W := by
    rw [top_inf_eq]
    ext w
    rw [MonoidHom.mem_ker, hfk, Subgroup.mem_subgroupOf]
  rw [hmap, hk, Subgroup.card_top, Subgroup.card_top] at h1
  have hcU : Nat.card ↥(U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  have h2 := card_sec_mul hUW
  have hK3 : Nat.card (Multiplicative (Fin 3 → K)) = Nat.card K ^ 3 := by
    rw [show Nat.card (Multiplicative (Fin 3 → K)) = Nat.card (Fin 3 → K) from rfl,
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  rw [hcU, hK3] at h1
  rw [← h1] at h2
  have hU : 0 < Nat.card U := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hU h2

theorem rkIdx_fixV_autSec_nat [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {L : Subgroup (MulAut V)} {W U : Subgroup V}
    {π : ↥(StatedSL 3 K) →* ↥L} (hπ : Function.Surjective π)
    (f : ↥W →* Multiplicative (Fin 3 → K)) (hfs : Function.Surjective f)
    (hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U)
    (hfe : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) w ∈ W),
      f ⟨_, hw⟩ = natAct (StatedSL 3 K) γ (f w))
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hUW : U ≤ W) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    rkIdx (fixV (autSec B W U)) =
      n * (3 - Module.finrank K (fixK ((B.subgroupOf L).comap π))) := by
  set d := Module.finrank K (fixK ((B.subgroupOf L).comap π)) with hd
  have hd3 : d ≤ 3 := by
    have := Submodule.finrank_le (fixK ((B.subgroupOf L).comap π))
    rwa [Module.finrank_fin_fun] at this
  have h1 := card_fixV_autSec_nat hπ f hfs hfk hfe hLW hLU hUW hBL
  have hcK : Nat.card ↥(fixK ((B.subgroupOf L).comap π)) = Nat.card K ^ d :=
    Module.natCard_eq_pow_finrank (K := K)
  rw [hcK, hK] at h1
  have h2 := card_sec_nat hUW f hfs hfk
  rw [hK] at h2
  have h3 := (fixV (autSec B W U)).index_mul_card
  rw [h1, h2, ← pow_mul, ← pow_mul] at h3
  have h4 : (fixV (autSec B W U)).index = 2 ^ (n * (3 - d)) := by
    have : 2 ^ (n * 3) = 2 ^ (n * (3 - d)) * 2 ^ (n * d) := by
      rw [← pow_add]
      congr 1
      rw [← Nat.mul_add, Nat.sub_add_cancel hd3]
    rw [this] at h3
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h3
  unfold rkIdx
  rw [h4, padicValNat.prime_pow]

end Coord

end B5

end CFSG.Quasithin
