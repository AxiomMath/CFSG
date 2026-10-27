module

public import CFSG.Quasithin.H13.A6S13827Gj

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem centralizer_QH_le (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (htriv : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V) :
    conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ W := by
  have hF1 := hd.hF.toHypF91
  have hUc : ∀ a ∈ conjClosure S.V3 H, ∀ b ∈ conjClosure S.V3 H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(conjClosure S.V3 H)) ⟨b, hb⟩)
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup G,
      Z = conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := ⟨_, rfl⟩
  rw [← hZ]
  have hV1Z : fsuV1 T V ≤ Z := fun v hv => by
    rw [hZ]
    refine ⟨hV1W.trans hWU.le hv, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hF1.H_le_centralizer (pCoreOf_le 2 H hq)) v hv).symm
  have hZconj : ∀ h ∈ H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z := by
    intro h hh x hx
    rw [hZ] at hx ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) x).mp hx.1,
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have hq' : h⁻¹ * q * h ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hh)) q).mp hq
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ hq'
    calc q * (h * x * h⁻¹) = h * ((h⁻¹ * q * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * q * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * q := by group
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hZconj h hh x, fun hx => ?_⟩
    have := hZconj h⁻¹ (H.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  have hZU : Z ≤ conjClosure S.V3 H := by
    rw [hZ]
    exact inf_le_left
  rcases hmax (Z ⊔ W) le_sup_right (sup_le hZU hWU.le)
      (fun h hh => Subgroup.inf_normalizer_le_normalizer_sup Z W ⟨hHZ hh, hHW hh⟩) with h | h
  · exact le_sup_left.trans h.le
  exfalso
  let P : Subgroup G :=
    { carrier := {u | u ∈ conjClosure S.V3 H ∧ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ Z}
      mul_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨(conjClosure S.V3 H).mul_mem hu hv, fun k hk => ?_⟩
        have hkv : k * v * k⁻¹ * v⁻¹ ∈ conjClosure S.V3 H := hZU (hv' k hk)
        have e : k * (u * v) * k⁻¹ * (u * v)⁻¹ =
            (k * u * k⁻¹ * u⁻¹) * (u * (k * v * k⁻¹ * v⁻¹) * u⁻¹) := by group
        have e2 : u * (k * v * k⁻¹ * v⁻¹) * u⁻¹ = k * v * k⁻¹ * v⁻¹ := by
          rw [hUc u hu _ hkv]
          group
        rw [e, e2]
        exact Z.mul_mem (hu' k hk) (hv' k hk)
      one_mem' := ⟨(conjClosure S.V3 H).one_mem, fun k _ => by
        rw [show k * 1 * k⁻¹ * (1 : G)⁻¹ = 1 by group]
        exact Z.one_mem⟩
      inv_mem' := by
        rintro u ⟨hu, hu'⟩
        refine ⟨(conjClosure S.V3 H).inv_mem hu, fun k hk => ?_⟩
        have hku : k * u * k⁻¹ * u⁻¹ ∈ conjClosure S.V3 H := hZU (hu' k hk)
        have e : k * u⁻¹ * k⁻¹ * u⁻¹⁻¹ = u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ * u := by group
        have e2 : u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ * u = (k * u * k⁻¹ * u⁻¹)⁻¹ := by
          rw [hUc _ ((conjClosure S.V3 H).inv_mem hu) _ ((conjClosure S.V3 H).inv_mem hku)]
          group
        rw [e, e2]
        exact Z.inv_mem (hu' k hk) }
  have hZP : Z ≤ P := fun x hx =>
    ⟨hZU hx, fun k hk => Z.mul_mem (hZconj k (hd.hKH hk) x hx) (Z.inv_mem hx)⟩
  have hWP : W ≤ P := fun w hw => ⟨hWU.le hw, fun k hk => hV1Z (htriv k hk w hw)⟩
  have hUP : conjClosure S.V3 H ≤ P := h ▸ sup_le hZP hWP
  have h1 : ⁅conjClosure S.V3 H, K⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have := Z.inv_mem ((hUP hu).2 k hk)
    have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ := by rw [commutatorElement_def]; group
    rwa [e] at this
  rw [hd.hUK] at h1
  obtain ⟨w, hw, q, hq, hz⟩ := S.exists_z_comm_V3_QH hd.hS.hNS h13315 h1356two hd.hH h13314
  have hwZ := h1 (le_conjClosure S.V3 H hw)
  rw [hZ] at hwZ
  have hc := Subgroup.mem_centralizer_iff.1 hwZ.2 q hq
  apply S.z_ne_one
  rw [hz, hc]
  group

theorem not_Dγ_le_VH_u33 (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (hG1 : S.G1 ≤ H)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G} (hV1W : fsuV1 T V ≤ W)
    (hWU : W < conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (htriv : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hAU : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 H)
    (h8 : 8 ≤ Nat.card (commV (autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H))))) :
    ¬ F8.Dγ S.V3 (fsuV1 T V) H (g : G) ≤ conjClosure V H := by
  intro hDV
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have hUc : ∀ a ∈ conjClosure S.V3 H, ∀ b ∈ conjClosure S.V3 H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(conjClosure S.V3 H)) ⟨b, hb⟩)
  have hZW := hd.centralizer_QH_le h13315 h1356two h13314 hV1W hWU hHW hmax htriv
  have hUγH := hF.Uγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hAW : F8.A₁ (fsuV1 T V) (g : G) ⊔ W ≤ conjClosure S.V3 H := sup_le hAU hWU.le
  obtain ⟨f, hf, v, hv, hc⟩ : ∃ f ∈ F8.Uγ S.V3 H (g : G), ∃ v ∈ conjClosure S.V3 H,
      f * v * f⁻¹ * v⁻¹ ∉ F8.A₁ (fsuV1 T V) (g : G) ⊔ W := by
    by_contra hall
    push Not at hall
    have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    have h1 := hsU.card_commV_le hUγH hAW hall
    have hn : (W.subgroupOf (conjClosure S.V3 H)).Normal := ⟨fun n hn x => by
      have e : x * n * x⁻¹ = n := by
        rw [show x * n = n * x from Subtype.ext (hUc _ x.2 _ n.2)]
        group
      rw [e]
      exact hn⟩
    have h2 : W.relIndex (F8.A₁ (fsuV1 T V) (g : G) ⊔ W) ≤ 2 := by
      rw [← Subgroup.relIndex_subgroupOf hAW, Subgroup.subgroupOf_sup hAU hWU.le,
        Subgroup.relIndex_sup_right]
      calc (W.subgroupOf (conjClosure S.V3 H)).relIndex
            ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure S.V3 H))
          ≤ Nat.card ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure S.V3 H)) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
        _ = Nat.card (F8.A₁ (fsuV1 T V) (g : G)) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAU).toEquiv
        _ = 2 := hF.card_A₁
    omega
  have hfH := hUγH hf
  have hcU : f * v * f⁻¹ * v⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hfH) v).mp hv)
      ((conjClosure S.V3 H).inv_mem hv)
  let _ : CommGroup ↥(conjClosure S.V3 H) := commGroupOfElemAbelian hF.F911_3
  have hE : ∀ w : ↥(conjClosure S.V3 H), w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hF.F911_3.2 w w.2)
  obtain ⟨f₀, hf₀D, hf₀c⟩ := A6G2.exists_hom_two_of_not_mem hE
    (D := (F8.A₁ (fsuV1 T V) (g : G) ⊔ W).subgroupOf (conjClosure S.V3 H))
    (c := ⟨_, hcU⟩) (by rw [Subgroup.mem_subgroupOf]; exact hc)
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let ε : Multiplicative (ZMod 2) ≃* ↥(fsuV1 T V) := mulEquivOfPrimeCardEq h2 hF1.card_V₁
  let φ : ↥(conjClosure S.V3 H) →* ↥(fsuV1 T V) := ε.toMonoidHom.comp f₀
  have hφ1 : ∀ u, φ u = 1 ↔ f₀ u = 1 := fun u => by
    change ε (f₀ u) = 1 ↔ f₀ u = 1
    rw [MulEquiv.map_eq_one_iff]
  obtain ⟨x, hxQ, hxφ⟩ := hF1.F97_surj hF.F911_3 φ fun u hu => by
    rw [hφ1]
    refine hf₀D u (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (hZW ?_)))
    exact ⟨u.2, Subgroup.mem_centralizer_iff.2 fun q hq => hu q hq⟩
  set a := (g : G) * S.z * (g : G)⁻¹ with ha
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have haA : a ∈ F8.A₁ (fsuV1 T V) (g : G) := by
    rw [F8.A₁, mem_conjSub]
    simpa [ha, mul_assoc] using hz
  have hxa : x * a = a * x := by
    have h1 := hxφ ⟨a, hAU haA⟩
    rw [(hφ1 _).2 (hf₀D _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left haA)))] at h1
    have h1' : x * a * x⁻¹ * a⁻¹ = 1 := h1.symm
    calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
      _ = a * x := by rw [h1', one_mul]
  have hxN := hd.mem_normalizer_Uγ_of_comm hG1 s hxa
  set y := x * f * x⁻¹ * f⁻¹ with hy
  have hyU : y ∈ F8.Uγ S.V3 H (g : G) :=
    (F8.Uγ S.V3 H (g : G)).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN f).mp hf)
      ((F8.Uγ S.V3 H (g : G)).inv_mem hf)
  have hfxQ : f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hfH) _).mp
      ((pCoreOf 2 H).inv_mem hxQ)
  have hyQ : y ∈ pCoreOf 2 H := by
    have e : y = x * (f * x⁻¹ * f⁻¹) := by rw [hy]; group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hxQ hfxQ
  have hyD : y ∈ F8.Dγ S.V3 (fsuV1 T V) H (g : G) := by
    rw [hF.Dγ_eq_inf_pCoreOf s]
    exact ⟨hyU, hyQ⟩
  have hyV := hDV hyD
  have hVc : y * v = v * y := isElemAbelian_comm hF.F911_2 hyV
    (conjClosure_mono S.V3_le_V le_rfl hv)
  have hyv : y * v * y⁻¹ * v⁻¹ = 1 := by rw [hVc]; group
  set x' := f * x * f⁻¹ with hx'
  have hx'Q : x' ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hfH) _).mp hxQ
  have hx'iQ : x'⁻¹ ∈ pCoreOf 2 H := (pCoreOf 2 H).inv_mem hx'Q
  have hyx : y = x * x'⁻¹ := by rw [hy, hx']; group
  have e1 := hF1.commutator_mul_left hxQ hx'iQ hv
  have e2 := hF1.commutator_mul_left hx'Q hx'iQ hv
  rw [mul_inv_cancel, one_mul, inv_one, mul_one, mul_inv_cancel] at e2
  have e2' : x'⁻¹ * v * x'⁻¹⁻¹ * v⁻¹ = (x' * v * x'⁻¹ * v⁻¹)⁻¹ :=
    (eq_inv_of_mul_eq_one_right e2.symm)
  set w := f⁻¹ * v * f with hw
  have hwU : w ∈ conjClosure S.V3 H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hfH))
      v).mp hv
    simpa [hw] using this
  have e3 := hF1.commutator_conj hfH hxQ hwU
  have hfw : f * w * f⁻¹ = v := by rw [hw]; group
  rw [hfw, ← hx'] at e3
  have hφv : ((φ ⟨v, hv⟩ : ↥(fsuV1 T V)) : G) = x * v * x⁻¹ * v⁻¹ := hxφ ⟨v, hv⟩
  have hφw : ((φ ⟨w, hwU⟩ : ↥(fsuV1 T V)) : G) = x * w * x⁻¹ * w⁻¹ := hxφ ⟨w, hwU⟩
  have hf2 : f * f = 1 := by
    rw [← pow_two]
    exact hUγel.2 f hf
  have hvw : (⟨v, hv⟩ : ↥(conjClosure S.V3 H)) * (⟨w, hwU⟩ : ↥(conjClosure S.V3 H))⁻¹ =
      (⟨_, hcU⟩ : ↥(conjClosure S.V3 H))⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw]
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
    rw [hfi]
    group
  have key : y * v * y⁻¹ * v⁻¹ = ((φ (⟨_, hcU⟩ : ↥(conjClosure S.V3 H)) : ↥(fsuV1 T V)) : G)⁻¹ := by
    rw [hyx, e1, e2', e3, ← hφv, ← hφw]
    have h4 : φ ⟨v, hv⟩ * (φ ⟨w, hwU⟩)⁻¹ = (φ (⟨_, hcU⟩ : ↥(conjClosure S.V3 H)))⁻¹ := by
      rw [← map_inv, ← map_mul, hvw, map_inv]
    have h5 := congrArg (fun t : ↥(fsuV1 T V) => (t : G)) h4
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h5
  rw [hyv] at key
  have h3 : φ (⟨_, hcU⟩ : ↥(conjClosure S.V3 H)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact (inv_eq_one.1 key.symm)
  exact hf₀c ((hφ1 _).1 h3)

end DK

end Setting4

end CFSG.Quasithin.H13.A6
