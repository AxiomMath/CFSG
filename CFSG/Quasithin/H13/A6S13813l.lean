module

public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.H13.A6S13710c
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

theorem card_subM_le {G : Type} [Group G] [Finite G] (V₁ IH J : Subgroup G) :
    Nat.card ↥(subM V₁ IH J) ≤ Nat.card J := by
  have h1 : Nat.card ↥(subM V₁ IH J) ≤ Nat.card ↥(tildeOf V₁ J) :=
    Nat.card_le_card_of_injective
      (fun x => (⟨((x : ↥(tildeOf V₁ IH)) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁),
        x.2⟩ : ↥(tildeOf V₁ J)))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg
        (fun y : ↥(tildeOf V₁ J) => (y : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) h)))
  have h2 : Nat.card ↥(tildeOf V₁ J) ≤
      Nat.card ↥(J.subgroupOf (Subgroup.normalizer (V₁ : Set G))) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have h3 : Nat.card ↥(J.subgroupOf (Subgroup.normalizer (V₁ : Set G))) ≤ Nat.card J :=
    Nat.card_le_card_of_injective
      (fun x => (⟨((x : ↥(Subgroup.normalizer (V₁ : Set G))) : G), x.2⟩ : ↥J))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : ↥J => (y : G)) h)))
  omega

theorem padicValNat_two_le {n k : ℕ} (hn : 0 < n) (h : n ≤ 2 ^ k) : padicValNat 2 n ≤ k :=
  (Nat.pow_le_pow_iff_right (by norm_num)).1 ((Nat.le_of_dvd hn pow_padicValNat_dvd).trans h)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Amalg

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
include hS hH

theorem card_subM_A₁ :
    Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) (F8.A₁ (fsuV1 T V) (g : G))) ≤ 2 := by
  refine (card_subM_le _ _ _).trans (le_of_eq ?_)
  have hc : Nat.card ↥(F8.A₁ (fsuV1 T V) (g : G)) = Nat.card (fsuV1 T V) :=
    Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
  rw [hc]
  exact (hS.hF H hH).toHypF91.card_V₁

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  {hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G)}
  {hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G)}

theorem actH_mem_A₁ {x : G} (hxH : x ∈ H) (hx : x ∈ F8.Uγ S.V3 H (g : G))
    {w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hw : w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G))) :
    actH hV₁ hIH ⟨x, hxH⟩ w * w⁻¹ ∈
      subM (fsuV1 T V) (conjClosure S.V3 H) (F8.A₁ (fsuV1 T V) (g : G)) := by
  have hF1 := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  obtain ⟨a, haD, haw⟩ := mem_secImg.1 (mem_subM_iff.1 hw)
  have haU : (a : G) ∈ conjClosure S.V3 H := centralizerMod_le_left _ _ _ haD
  have hw' : w = modMk hIHN (a : G) haU := Subtype.ext haw.symm
  have hxa : x * a * x⁻¹ * (a : G)⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
    have := (F8.A₁ (fsuV1 T V) (g : G)).inv_mem (haD.2.2 x hx)
    rwa [show ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ = x * a * x⁻¹ * (a : G)⁻¹ by group] at this
  rw [hw', actH_modMk hV₁ hIHN hIH, ← modMk_inv hIHN, ← modMk_mul hIHN]
  exact secMk_mem_secImg (X := F8.A₁ (fsuV1 T V) (g : G)) hxa

omit [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))] in
theorem card_tilde_le_mul :
    Nat.card ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) ≤
      2 ^ mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) *
        Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G))) := by
  have hF1 := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hF1.H_normalizes_V₁
  set D := F8.DH S.V3 (fsuV1 T V) H (g : G) with hD
  have hDU : D ≤ conjClosure S.V3 H := centralizerMod_le_left _ _ _
  have hmap : (D.subgroupOf (conjClosure S.V3 H)).map (tildeHom hIHN) =
      subM (fsuV1 T V) (conjClosure S.V3 H) D := by
    ext w
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [mem_subM_iff, tildeHom_coe]
      exact secMk_mem_secImg (X := D) (Subgroup.mem_subgroupOf.1 hd)
    · intro hw
      obtain ⟨a, haD, haw⟩ := mem_secImg.1 (mem_subM_iff.1 hw)
      exact ⟨⟨a, hDU haD⟩, Subgroup.mem_subgroupOf.2 haD, Subtype.ext (by
        rw [tildeHom_coe]; exact haw)⟩
  have hdvd := Subgroup.index_map_dvd (D.subgroupOf (conjClosure S.V3 H))
    (tildeHom_surjective hIHN)
  rw [hmap] at hdvd
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
  have hidx : (D.subgroupOf (conjClosure S.V3 H)).index = 2 ^ mIdx (conjClosure S.V3 H) D :=
    HypF98.relIndex_eq_two_pow_mIdx hU2
  rw [hidx] at hdvd
  have h1 := Subgroup.card_mul_index (subM (fsuV1 T V) (conjClosure S.V3 H) D)
  have h2 := Nat.le_of_dvd (by positivity) hdvd
  calc Nat.card ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) =
        Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) D) *
          (subM (fsuV1 T V) (conjClosure S.V3 H) D).index := h1.symm
    _ ≤ Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) D) *
          2 ^ mIdx (conjClosure S.V3 H) D := Nat.mul_le_mul_left _ h2
    _ = _ := mul_comm _ _

omit [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))] in
theorem mIdx_Uγ_le (s : F8Setup T V L H γ γ' g) {k : ℕ}
    (hk : Nat.card (autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ≤ 2 ^ k) :
    mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ≤ k := by
  rw [← (hS.hF H hH).rk_autOn_tilde_Uγ s]
  exact padicValNat_two_le Nat.card_pos hk

theorem actH_mem_A₁_of_fix (s : F8Setup T V L H γ γ' g)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hw : w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)))
    (hfix : ∀ x (hxH : x ∈ H), x ∈ F8.Uγ S.V3 H (g : G) → actH hV₁ hIH ⟨x, hxH⟩ w = w)
    {v : G} (hvH : v ∈ H) (hv : v ∈ F8.Uγ V H (g : G)) :
    actH hV₁ hIH ⟨v, hvH⟩ w * w⁻¹ ∈
      subM (fsuV1 T V) (conjClosure S.V3 H) (F8.A₁ (fsuV1 T V) (g : G)) := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  obtain ⟨a, haD, haw⟩ := mem_secImg.1 (mem_subM_iff.1 hw)
  have haU : (a : G) ∈ conjClosure S.V3 H := centralizerMod_le_left _ _ _ haD
  have hw' : w = modMk hIHN (a : G) haU := Subtype.ext haw.symm
  have hUγH := hF.Uγ_le_H s
  have hca : ∀ x ∈ F8.Uγ S.V3 H (g : G), x * (a : G) = (a : G) * x := by
    intro x hx
    have h1 := hfix x (hUγH hx) hx
    rw [hw', actH_modMk hV₁ hIHN hIH] at h1
    have h2 := secMk_eq_secMk_iff.1 (congrArg Subtype.val h1)
    have h3 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ fsuV1 T V := by
      have := (Subgroup.mem_normalizer_iff.mp (hIHN haU) _).mp h2
      rwa [show (a : G) * ((x * (a : G) * x⁻¹)⁻¹ * (a : G)) * (a : G)⁻¹ =
        (a : G) * x * (a : G)⁻¹ * x⁻¹ by group] at this
    have h5 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) :=
      ⟨h3, haD.2.2 x hx⟩
    rw [hF.F913_5b s, Subgroup.mem_bot] at h5
    calc x * (a : G) = ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ * ((a : G) * x) := by group
      _ = (a : G) * x := by rw [h5, inv_one, one_mul]
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : conjClosure S.V3 H ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hxG : (g : G)⁻¹ * a * (g : G) ∈ H := by
    have := hUst haU
    rw [hstab, mem_conjSub] at this
    exact this
  have hxC : (g : G)⁻¹ * a * (g : G) ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    have e := hca _ (mul_mem_conjSub (g := (g : G)) hu')
    calc u' * ((g : G)⁻¹ * a * (g : G)) =
        (g : G)⁻¹ * (((g : G) * u' * (g : G)⁻¹) * a) * (g : G) := by group
      _ = (g : G)⁻¹ * (a * ((g : G) * u' * (g : G)⁻¹)) * (g : G) := by rw [e]
      _ = ((g : G)⁻¹ * a * (g : G)) * u' := by group
  have hxQ : (g : G)⁻¹ * a * (g : G) ∈ pCoreOf 2 H := by
    rw [hF1.pCoreOf_eq_centralizerMod]
    refine ⟨hxG, hF1.H_normalizes_V₁ hxG, fun u' hu' => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hxC u' hu', mul_inv_cancel_right, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  have hy : (g : G)⁻¹ * v * (g : G) ∈ conjClosure V H := mem_conjSub.mp hv
  have h3 := S.comm_VH_HC hS.hNS h13315 h1356two hH hxQ hxC hy
  have hva : v * a * v⁻¹ * (a : G)⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
    rw [F8.A₁, mem_conjSub]
    have e : (g : G)⁻¹ * (v * a * v⁻¹ * (a : G)⁻¹) * (g : G) =
        ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ * a * (g : G)) * ((g : G)⁻¹ * v * (g : G))⁻¹ *
          ((g : G)⁻¹ * a * (g : G))⁻¹ := by group
    rw [e]
    exact h3
  rw [hw', actH_modMk hV₁ hIHN hIH, ← modMk_inv hIHN, ← modMk_mul hIHN]
  exact secMk_mem_secImg (X := F8.A₁ (fsuV1 T V) (g : G)) hva

end Amalg

end Setting4

end CFSG.Quasithin.H13.A6
