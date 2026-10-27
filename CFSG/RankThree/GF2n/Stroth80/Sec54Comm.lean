module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aUncond
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

noncomputable def sec54_conjAct (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) : ↥F →* MulAut ↥Y :=
  (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hFN)

theorem sec54_conjAct_apply (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) (f : ↥F) (y : ↥Y) :
    ((sec54_conjAct F Y hFN f y : ↥Y) : G) = (f : G) * (y : G) * (f : G)⁻¹ := by
  rw [sec54_conjAct, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

theorem sec54_conjAct_map_subgroupOf (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) :
    ∀ f : ↥F, (Y₀.subgroupOf Y).map ((sec54_conjAct F Y hFN f).toMonoidHom) =
      Y₀.subgroupOf Y := by
  intro f
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    change (z : G) ∈ Y₀ at hz
    have hact : (((sec54_conjAct F Y hFN f) z : ↥Y) : G) =
        (f : G) * (z : G) * (f : G)⁻¹ := sec54_conjAct_apply F Y hFN f z
    rw [← hzy]
    show (((sec54_conjAct F Y hFN f) z : ↥Y) : G) ∈ Y₀
    rw [hact]
    exact hInv (f : G) f.2 (z : G) hz
  · intro hy
    rw [Subgroup.mem_map]
    refine ⟨sec54_conjAct F Y hFN f⁻¹ y, ?_, ?_⟩
    · have hact := sec54_conjAct_apply F Y hFN f⁻¹ y
      change (((sec54_conjAct F Y hFN f⁻¹) y : ↥Y) : G) ∈ Y₀
      rw [hact]
      have hfinv : ((f⁻¹ : ↥F) : G) = (f : G)⁻¹ := rfl
      rw [hfinv]
      exact hInv (f : G)⁻¹ (F.inv_mem f.2) (y : G) (Subgroup.mem_subgroupOf.mp hy)
    · have h1 : sec54_conjAct F Y hFN f * sec54_conjAct F Y hFN f⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change sec54_conjAct F Y hFN f (sec54_conjAct F Y hFN f⁻¹ y) = y
      rw [← MulAut.mul_apply, h1, MulAut.one_apply]

noncomputable def sec54_quotAct (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) :
    ↥F →* MulAut (↥Y ⧸ Y₀.subgroupOf Y) :=
  CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism (sec54_conjAct F Y hFN)
    (Y₀.subgroupOf Y) (sec54_conjAct_map_subgroupOf F Y Y₀ hFN hInv)

theorem sec54_quotAct_apply (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) (f : ↥F) (y : ↥Y) :
    sec54_quotAct F Y Y₀ hFN hInv f (QuotientGroup.mk' (Y₀.subgroupOf Y) y) =
      QuotientGroup.mk' (Y₀.subgroupOf Y) (sec54_conjAct F Y hFN f y) := by
  change CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism
    (sec54_conjAct F Y hFN f) (Y₀.subgroupOf Y)
    (sec54_conjAct_map_subgroupOf F Y Y₀ hFN hInv f)
    (QuotientGroup.mk' (Y₀.subgroupOf Y) y) = _
  rw [CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply]

theorem sec54_quotAct_eq_one_iff (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) (f : ↥F) :
    sec54_quotAct F Y Y₀ hFN hInv f = 1 ↔ ∀ y : ↥Y, ⁅(f : G), (y : G)⁆ ∈ Y₀ := by
  constructor
  · intro hf y
    have h1 : sec54_quotAct F Y Y₀ hFN hInv f
        (QuotientGroup.mk' (Y₀.subgroupOf Y) y) =
        QuotientGroup.mk' (Y₀.subgroupOf Y) y := by
      rw [hf, MulAut.one_apply]
    rw [sec54_quotAct_apply] at h1
    change (QuotientGroup.mk ((sec54_conjAct F Y hFN) f y) :
      ↥Y ⧸ Y₀.subgroupOf Y) = QuotientGroup.mk y at h1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h1
    change ((↑(((sec54_conjAct F Y hFN) f) y) : G) / ↑y : G) ∈ Y₀ at h1
    have h2 : ((↑(((sec54_conjAct F Y hFN) f) y) : G) / ↑y : G) =
        ⁅(f : G), (y : G)⁆ := by
      rw [sec54_conjAct_apply, commutatorElement_def, div_eq_mul_inv]
    rwa [h2] at h1
  · intro hf
    apply MulEquiv.ext
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Y₀.subgroupOf Y) z
    rw [sec54_quotAct_apply, MulAut.one_apply]
    change (QuotientGroup.mk ((sec54_conjAct F Y hFN) f y) :
      ↥Y ⧸ Y₀.subgroupOf Y) = QuotientGroup.mk y
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    change ((↑(((sec54_conjAct F Y hFN) f) y) : G) / ↑y : G) ∈ Y₀
    have h2 : ((↑(((sec54_conjAct F Y hFN) f) y) : G) / ↑y : G) =
        ⁅(f : G), (y : G)⁆ := by
      rw [sec54_conjAct_apply, commutatorElement_def, div_eq_mul_inv]
    rw [h2]
    exact hf y

def sec54_commGroupOfSqOne {H : Type} [Group H] (hH : ∀ x : H, x * x = 1) : CommGroup H :=
  letI : IsMulCommutative H := ⟨⟨fun x y => by
    calc x * y = x⁻¹ * y⁻¹ := by
          rw [inv_eq_of_mul_eq_one_right (hH x), inv_eq_of_mul_eq_one_right (hH y)]
      _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
      _ = y * x := inv_eq_of_mul_eq_one_right (hH (y * x))⟩⟩
  Group.commGroupOfCenterEqTop (Subgroup.center_eq_top (G := H))

theorem sec54_Q_normalizes_Vt (hc : Ctx M Q Z B) {t : G} :
    Q ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (hc.Vt_le_Q t hx)
    have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hc') hx
  · intro hx
    have hc' : ⁅q⁻¹, q * x * q⁻¹⁆ ∈ Z :=
      hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hq) (hc.Vt_le_Q t hx)
    have e : q⁻¹ * (q * x * q⁻¹) * q = ⁅q⁻¹, q * x * q⁻¹⁆ * (q * x * q⁻¹) := by
      rw [commutatorElement_def]; group
    have hmemy : q⁻¹ * (q * x * q⁻¹) * q ∈ Vt M (LB M Q B) B Z t := by
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hc') hx
    have e2 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
    rwa [e2] at hmemy

theorem sec54_Q_normalizes_Vone (hc : Ctx M Q Z B) {t r : G} :
    Q ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
  have key : ∀ q ∈ Q, ∀ x ∈ Sec8V1 M Q Z B t r, q * x * q⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro q hq x hx
    have hxQ : x ∈ Q := sec8_V1_le_Q hc t r hx
    have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq hxQ
    have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact (Sec8V1 M Q Z B t r).mul_mem (sec8_Z_le_V1 hc t r hc') hx
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key q hq x, fun hx => by
    have h1 := key q⁻¹ (Q.inv_mem hq) (q * x * q⁻¹) hx
    have e : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rwa [e] at h1⟩

theorem sec54_conj_Wt_eq {Q V : Subgroup G} {q : G} (hQ : conjSubgroup q Q = Q)
    (hV : conjSubgroup q V = V) : conjSubgroup q (Wt Q V) = Wt Q V := by
  unfold Wt
  rw [conjSubgroup_inf, hQ, conjSubgroup_centralizer, hV]

theorem sec54_comm_W_le_W1 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m) (hs8 : Sec8Hyp hc n t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, x⁆ ∈ Sec8W1 M Q Z B t r := by
  classical
  obtain ⟨K, iK, iFin, hKcard, φ, hrange, hker, hact⟩ := hV
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI hchar : CharP K 2 := charP_two_of_card_eq_two_pow (hKcard.trans hZ2)
  have hsp : SpNat hc t := ⟨K, iK, iFin, hKcard, m, hm, φ, hrange, hker, hact⟩
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Sec8V1 M Q Z B t r with hV1def
  set W : Subgroup G := Wt Q V with hWdef
  set W1 : Subgroup G := Sec8W1 M Q Z B t r with hW1def
  have hV1Q : V1 ≤ Q := hV1def ▸ sec8_V1_le_Q hc t r
  have hVQ : V ≤ Q := hVdef ▸ hc.Vt_le_Q t
  have hZV : Z ≤ V := hVdef ▸ sec39_Z_le_Vt
  have hWQ : W ≤ Q := hWdef ▸ inf_le_left
  have hW1Q : W1 ≤ Q := hW1def ▸ sec8_W1_le_Q M Q Z B t r
  have hVW : V ≤ W := by
    rw [hVdef, hWdef]
    exact sec7ctr_Vt_le_Wt h34 hc hs
  have hV1W1 : V1 ≤ W1 := by
    rw [hV1def, hW1def]
    exact stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane
  have hV1V : V ≤ V1 := le_inf le_sup_right le_sup_right
  have hW1W : W1 ≤ W := by
    rw [hWdef, hW1def]
    refine inf_le_inf_left Q ?_
    apply Subgroup.centralizer_le
    intro x hx
    exact hV1V hx
  have hZW1 : Z ≤ W1 := by
    rw [hW1def]
    change Z ≤ Q ⊓ Subgroup.centralizer ((Sec8V1 M Q Z B t r : Subgroup G) : Set G)
    intro z hz
    exact ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hc.hyp.toHyp79.V_central hz (hV1Q hy)).symm⟩
  have hQnormW : Q ≤ Subgroup.normalizer (W : Set G) := by
    intro q hq
    rw [hWdef, ← conjSubgroup_eq_self_iff]
    exact sec54_conj_Wt_eq (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hq))
      (conjSubgroup_eq_self_iff.mpr ((sec54_Q_normalizes_Vt hc) hq))
  have hQnormW1 : Q ≤ Subgroup.normalizer (W1 : Set G) := by
    intro q hq
    rw [hW1def, ← conjSubgroup_eq_self_iff]
    exact sec54_conj_Wt_eq (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hq))
      (conjSubgroup_eq_self_iff.mpr ((sec54_Q_normalizes_Vone hc) hq))
  haveI hW1n : (W1.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun x hx => hQnormW1 (hWQ hx))
  have hRnormW : Rt M (LB M Q B) t ≤ Subgroup.normalizer (W : Set G) := by
    intro ρ hρ
    rw [hWdef]
    exact sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ))
      (hc.Rt_normalizes_Vt hs.mem hρ)
  have h7A : Sec7A hc t r := sec7A_of_hypPlane h34 hRoot h51 hs8 hr hplane
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs8 r h7A ρ hρ
  have hRnormW1 : Rt M (LB M Q B) t ≤ Subgroup.normalizer (W1 : Set G) := by
    intro ρ hρ
    rw [hW1def]
    exact sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ))
      (conjSubgroup_eq_self_iff.mp (hInv ρ hρ).1)
  have hNcomm : ∀ s ∈ hc.CN t, ∀ x ∈ W, ⁅s, x⁆ ∈ W1 := by
    intro s hsN x hx
    have h1 : ⁅s, x⁆ ∈ Wt Q (Sec8V1 M Q Z B t r) :=
      sec53_sp_comm_Q_le_Wt_vone h34 h51 hc hs hsp hr hplane s hsN x (hWQ hx)
    rw [hW1def]
    exact h1
  let S : Type := ↥W ⧸ W1.subgroupOf W
  haveI hSfin : Finite S := inferInstance
  let ρact : ↥(Rt M (LB M Q B) t) →* MulAut S :=
    sec54_quotAct (Rt M (LB M Q B) t) W W1 hRnormW
      (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormW1 hf) y).mp hy)
  have hNker : (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ≤ ρact.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine (sec54_quotAct_eq_one_iff (Rt M (LB M Q B) t) W W1 hRnormW
      (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormW1 hf) y).mp hy) n).mpr ?_
    intro y
    exact hNcomm (n : G) (Subgroup.mem_subgroupOf.mp hn) (y : G) y.2
  let fsp : ↥(Rt M (LB M Q B) t) →* ↥(StatedSp m K) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp φ.rangeRestrict
  have hfs : Function.Surjective fsp :=
    (MulEquiv.subgroupCongr hrange).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  have hfker : fsp.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    ext r
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (MulEquiv.subgroupCongr hrange) (φ.rangeRestrict r) = 1 ↔ (r : G) ∈ hc.CN t
    rw [map_eq_one_iff _ (MulEquiv.subgroupCongr hrange).injective]
    have h1 : φ.rangeRestrict r = 1 ↔ φ r = 1 := by
      rw [← Subtype.coe_inj]; rfl
    rw [h1, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  let π : ↥(StatedSp m K) →* MulAut S :=
    MonoidHom.liftOfSurjective fsp hfs ⟨ρact, hfker ▸ hNker⟩
  have hπcomp : π.comp fsp = ρact := by
    change (MonoidHom.liftOfRightInverse fsp (Function.surjInv hfs)
      (Function.rightInverse_surjInv hfs) ⟨ρact, hfker ▸ hNker⟩).comp fsp = ρact
    exact MonoidHom.liftOfRightInverse_comp fsp (Function.surjInv hfs)
      (Function.rightInverse_surjInv hfs) ⟨ρact, hfker ▸ hNker⟩
  have hWcard : Nat.card ↥W = Nat.card ↥W1 * Nat.card Z := by
    have h53a := stroth53aStatement_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane
      (conjSubgroup r B) V W V1 (Sec8W1 M Q Z B t r) rfl hVdef.symm hWdef.symm hV1def.symm
      rfl
    exact h53a.2.1
  have hScardZ : Nat.card S = Nat.card Z := by
    have hidx : (W1.subgroupOf W).index = Nat.card S := Subgroup.index_eq_card (W1.subgroupOf W)
    have hmul : (W1.subgroupOf W).index * Nat.card ↥(W1.subgroupOf W) = Nat.card ↥W :=
      Subgroup.index_mul_card (W1.subgroupOf W)
    have hsmall : Nat.card ↥(W1.subgroupOf W) = Nat.card ↥W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv
    rw [hsmall, hWcard] at hmul
    rw [← hidx]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥W1)) ?_
    rw [hmul, Nat.mul_comm (Nat.card ↥W1) (Nat.card Z)]
  have hS2 : ∀ s : S, s * s = 1 := by
    intro s
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (W1.subgroupOf W) s
    have hmem : (y * y : ↥W) ∈ W1.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      have hyy : (((y * y : ↥W) : G)) = (y : G) * (y : G) := rfl
      rw [hyy]
      exact hZW1 (by simpa [pow_two] using hc.hyp.toHyp79.sq_mem_V (hWQ y.2))
    calc s * s = QuotientGroup.mk' (W1.subgroupOf W) (y * y) := by
          rw [← hy, ← map_mul]
      _ = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact hmem
  have hS2pow : ∀ x : S, x ^ 2 = 1 := fun x => by
    rw [pow_two]; exact hS2 x
  letI hScomm : CommGroup S := sec54_commGroupOfSqOne hS2
  have hScard : Nat.card S ≤ Nat.card K := by
    rw [hScardZ, ← hKcard]
  have hptriv : π = 1 := spHomTriv_hom_trivial hS2pow hScard π
  have hρ1 : ρact = 1 := by
    rw [← hπcomp, hptriv, MonoidHom.one_comp]
  intro s hsR x hx
  have h1 : ρact ⟨s, hsR⟩ = 1 := by rw [hρ1]; rfl
  have hcomm := (sec54_quotAct_eq_one_iff (Rt M (LB M Q B) t) W W1 hRnormW
    (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormW1 hf) y).mp hy)
    ⟨s, hsR⟩).mp h1 ⟨x, hx⟩
  exact hcomm

end CFSG.RankThree.GF2n.Stroth80
