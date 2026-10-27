module

public import CFSG.RankThree.GF2n.Stroth80.Sec54Final
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Split
public import CFSG.RankThree.GF2n.Stroth80.Sec53Odd
public import CFSG.RankThree.GF2n.Stroth80.Sec53cFixPair
public import CFSG.RankThree.GF2n.Stroth80.Sec54Vone
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec54D_stroth53a (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53aStatement := by
  have hOdd := stroth53Odd_holds h34 hRoot h51
  have hne := vone_ne_of_odd h34 hRoot h51 hOdd
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixB_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixC_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
  exact stroth53a_of_vone_ne h34 hRoot h51 hne hOdd

noncomputable def sec54D_conjAct (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) : ↥F →* MulAut ↥Y :=
  (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hFN)

theorem sec54D_conjAct_apply (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) (f : ↥F) (y : ↥Y) :
    ((sec54D_conjAct F Y hFN f y : ↥Y) : G) = (f : G) * (y : G) * (f : G)⁻¹ := by
  rw [sec54D_conjAct, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

theorem sec54D_conjAct_map_subgroupOf (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) :
    ∀ f : ↥F, (Y₀.subgroupOf Y).map ((sec54D_conjAct F Y hFN f).toMonoidHom) =
      Y₀.subgroupOf Y := by
  intro f
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    change (z : G) ∈ Y₀ at hz
    have hact : (((sec54D_conjAct F Y hFN f) z : ↥Y) : G) =
        (f : G) * (z : G) * (f : G)⁻¹ := sec54D_conjAct_apply F Y hFN f z
    rw [← hzy]
    show (((sec54D_conjAct F Y hFN f) z : ↥Y) : G) ∈ Y₀
    rw [hact]
    exact hInv (f : G) f.2 (z : G) hz
  · intro hy
    rw [Subgroup.mem_map]
    refine ⟨sec54D_conjAct F Y hFN f⁻¹ y, ?_, ?_⟩
    · have hact := sec54D_conjAct_apply F Y hFN f⁻¹ y
      change (((sec54D_conjAct F Y hFN f⁻¹) y : ↥Y) : G) ∈ Y₀
      rw [hact]
      have hfinv : ((f⁻¹ : ↥F) : G) = (f : G)⁻¹ := rfl
      rw [hfinv]
      exact hInv (f : G)⁻¹ (F.inv_mem f.2) (y : G) (Subgroup.mem_subgroupOf.mp hy)
    · have h1 : sec54D_conjAct F Y hFN f * sec54D_conjAct F Y hFN f⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change sec54D_conjAct F Y hFN f (sec54D_conjAct F Y hFN f⁻¹ y) = y
      rw [← MulAut.mul_apply, h1, MulAut.one_apply]

noncomputable def sec54D_quotAct (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) :
    ↥F →* MulAut (↥Y ⧸ Y₀.subgroupOf Y) :=
  CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism (sec54D_conjAct F Y hFN)
    (Y₀.subgroupOf Y) (sec54D_conjAct_map_subgroupOf F Y Y₀ hFN hInv)

theorem sec54D_quotAct_apply (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) (f : ↥F) (y : ↥Y) :
    sec54D_quotAct F Y Y₀ hFN hInv f (QuotientGroup.mk' (Y₀.subgroupOf Y) y) =
      QuotientGroup.mk' (Y₀.subgroupOf Y) (sec54D_conjAct F Y hFN f y) := by
  change CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism
    (sec54D_conjAct F Y hFN f) (Y₀.subgroupOf Y)
    (sec54D_conjAct_map_subgroupOf F Y Y₀ hFN hInv f)
    (QuotientGroup.mk' (Y₀.subgroupOf Y) y) = _
  rw [CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply]

theorem sec54D_quotAct_eq_one_iff (F Y Y₀ : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [(Y₀.subgroupOf Y).Normal]
    (hInv : ∀ f ∈ F, ∀ y ∈ Y₀, f * y * f⁻¹ ∈ Y₀) (f : ↥F) :
    sec54D_quotAct F Y Y₀ hFN hInv f = 1 ↔ ∀ y : ↥Y, ⁅(f : G), (y : G)⁆ ∈ Y₀ := by
  constructor
  · intro hf y
    have h1 : sec54D_quotAct F Y Y₀ hFN hInv f
        (QuotientGroup.mk' (Y₀.subgroupOf Y) y) =
        QuotientGroup.mk' (Y₀.subgroupOf Y) y := by
      rw [hf, MulAut.one_apply]
    rw [sec54D_quotAct_apply] at h1
    change (QuotientGroup.mk ((sec54D_conjAct F Y hFN) f y) :
      ↥Y ⧸ Y₀.subgroupOf Y) = QuotientGroup.mk y at h1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h1
    change ((↑(((sec54D_conjAct F Y hFN) f) y) : G) / ↑y : G) ∈ Y₀ at h1
    have h2 : ((↑(((sec54D_conjAct F Y hFN) f) y) : G) / ↑y : G) =
        ⁅(f : G), (y : G)⁆ := by
      rw [sec54D_conjAct_apply, commutatorElement_def, div_eq_mul_inv]
    rwa [h2] at h1
  · intro hf
    apply MulEquiv.ext
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Y₀.subgroupOf Y) z
    rw [sec54D_quotAct_apply, MulAut.one_apply]
    change (QuotientGroup.mk ((sec54D_conjAct F Y hFN) f y) :
      ↥Y ⧸ Y₀.subgroupOf Y) = QuotientGroup.mk y
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    change ((↑(((sec54D_conjAct F Y hFN) f) y) : G) / ↑y : G) ∈ Y₀
    have h2 : ((↑(((sec54D_conjAct F Y hFN) f) y) : G) / ↑y : G) =
        ⁅(f : G), (y : G)⁆ := by
      rw [sec54D_conjAct_apply, commutatorElement_def, div_eq_mul_inv]
    rw [h2]
    exact hf y
theorem sec54D_Q_normalizes_Vt (hc : Ctx M Q Z B) {t : G} :
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
    have hmem : q⁻¹ * (q * x * q⁻¹) * q ∈ Vt M (LB M Q B) B Z t := by
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hc') hx
    have e2 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
    rwa [e2] at hmem

theorem sec54D_Q_normalizes_Vone (hc : Ctx M Q Z B) {t r : G} :
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

@[instance_reducible] def sec54D_commGroupOfSqOne {H : Type} [Group H] (hH : ∀ x : H, x * x = 1) : CommGroup H :=
  letI : IsMulCommutative H := ⟨⟨fun x y => by
    calc x * y = x⁻¹ * y⁻¹ := by
          rw [inv_eq_of_mul_eq_one_right (hH x), inv_eq_of_mul_eq_one_right (hH y)]
      _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
      _ = y * x := inv_eq_of_mul_eq_one_right (hH (y * x))⟩⟩
  Group.commGroupOfCenterEqTop (Subgroup.center_eq_top (G := H))

theorem sec54D_conj_Wt_eq {Q V : Subgroup G} {q : G} (hQ : conjSubgroup q Q = Q)
    (hV : conjSubgroup q V = V) : conjSubgroup q (Wt Q V) = Wt Q V := by
  unfold Wt
  rw [conjSubgroup_inf, hQ, conjSubgroup_centralizer, hV]

theorem sec54D_comm_Vone_le_V (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53a : Stroth53aStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m) (hs8 : Sec8Hyp hc n t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r,
      ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨K, iK, iFin, hKcard, φ, hrange, hker, hact⟩ := hV
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI hchar : CharP K 2 := charP_two_of_card_eq_two_pow (hKcard.trans hZ2)
  have hsp : SpNat hc t := ⟨K, iK, iFin, hKcard, m, hm, φ, hrange, hker, hact⟩
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Sec8V1 M Q Z B t r with hV1def
  have hV1Q : V1 ≤ Q := hV1def ▸ sec8_V1_le_Q hc t r
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hZV : Z ≤ V := hVdef ▸ sec39_Z_le_Vt
  have hVQ : V ≤ Q := hVdef ▸ hc.Vt_le_Q t
  have hV1V : V ≤ V1 := by
    rw [hV1def, hVdef]
    exact le_inf le_sup_right le_sup_right
  have hQnormV : Q ≤ Subgroup.normalizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (hVQ hx)
      have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact V.mul_mem (hZV hc') hx
    · intro hx
      have hc' : ⁅q⁻¹, q * x * q⁻¹⁆ ∈ Z :=
        hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hq) (hVQ hx)
      have e : q⁻¹ * (q * x * q⁻¹) * q = ⁅q⁻¹, q * x * q⁻¹⁆ * (q * x * q⁻¹) := by
        rw [commutatorElement_def]; group
      have hmem : q⁻¹ * (q * x * q⁻¹) * q ∈ V := by
        rw [e]
        exact V.mul_mem (hZV hc') hx
      have e2 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
      rwa [e2] at hmem
  have hQnormV1 : Q ≤ Subgroup.normalizer (V1 : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (hV1Q hx)
      have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact V1.mul_mem (hV1V (hZV hc')) hx
    · intro hx
      have hc' : ⁅q⁻¹, q * x * q⁻¹⁆ ∈ Z :=
        hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hq) (hV1Q hx)
      have e : q⁻¹ * (q * x * q⁻¹) * q = ⁅q⁻¹, q * x * q⁻¹⁆ * (q * x * q⁻¹) := by
        rw [commutatorElement_def]; group
      have hmem : q⁻¹ * (q * x * q⁻¹) * q ∈ V1 := by
        rw [e]
        exact V1.mul_mem (hV1V (hZV hc')) hx
      have e2 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
      rwa [e2] at hmem
  haveI hVn : (V.subgroupOf V1).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun x hx => hQnormV (hV1Q hx))
  have hRnormV : Rt M (LB M Q B) t ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]
    exact hc.Rt_normalizes_Vt hs.mem
  have h7A : Sec7A hc t r := sec7A_of_hypPlane h34 hRoot h51 hs8 hr hplane
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs8 r h7A ρ hρ
  have hRnormV1 : Rt M (LB M Q B) t ≤ Subgroup.normalizer (V1 : Set G) :=
    fun ρ hρ => conjSubgroup_eq_self_iff.mp (hInv ρ hρ).1
  have hNcomm : ∀ s ∈ hc.CN t, ∀ x ∈ V1, ⁅s, x⁆ ∈ V := by
    intro s hsN x hx
    have h1 : ⁅s, x⁆ ∈ Z := by
      rw [hV1def] at hx
      exact sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane s hsN x hx
    exact hZV h1
  let S : Type := ↥V1 ⧸ V.subgroupOf V1
  haveI hSfin : Finite S := inferInstance
  let ρact : ↥(Rt M (LB M Q B) t) →* MulAut S :=
    sec54D_quotAct (Rt M (LB M Q B) t) V1 V hRnormV1
      (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormV hf) y).mp hy)
  have hNker : (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ≤ ρact.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine (sec54D_quotAct_eq_one_iff (Rt M (LB M Q B) t) V1 V hRnormV1
      (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormV hf) y).mp hy) n).mpr ?_
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
  have hV1card : Nat.card ↥V1 = Nat.card ↥V * Nat.card Z := by
    have h53a' := h53a G M Q Z B hc n t hs hsp r hr hplane
      (conjSubgroup r B) V (Wt Q V) V1 (Sec8W1 M Q Z B t r) rfl hVdef.symm rfl hV1def.symm
      rfl
    exact h53a'.1
  have hScardZ : Nat.card S = Nat.card Z := by
    have hidx : (V.subgroupOf V1).index = Nat.card S := Subgroup.index_eq_card (V.subgroupOf V1)
    have hmul : (V.subgroupOf V1).index * Nat.card ↥(V.subgroupOf V1) = Nat.card ↥V1 :=
      Subgroup.index_mul_card _
    have hsmall : Nat.card ↥(V.subgroupOf V1) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1V).toEquiv
    rw [hsmall, hV1card] at hmul
    rw [← hidx]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥V)) ?_
    rw [hmul, Nat.mul_comm (Nat.card ↥V) (Nat.card Z)]
  have hS2 : ∀ s : S, s * s = 1 := by
    intro s
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (V.subgroupOf V1) s
    have hmem : (y * y : ↥V1) ∈ V.subgroupOf V1 := by
      rw [Subgroup.mem_subgroupOf]
      have hyy : (((y * y : ↥V1) : G)) = (y : G) * (y : G) := rfl
      rw [hyy]
      exact hZV (by simpa [pow_two] using hc.hyp.toHyp79.sq_mem_V (hV1Q y.2))
    calc s * s = QuotientGroup.mk' (V.subgroupOf V1) (y * y) := by
          rw [← hy, ← map_mul]
      _ = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact hmem
  have hS2pow : ∀ x : S, x ^ 2 = 1 := fun x => by
    rw [pow_two]; exact hS2 x
  letI hScomm : CommGroup S := sec54D_commGroupOfSqOne hS2
  have hScard : Nat.card S ≤ Nat.card K := by
    rw [hScardZ, ← hKcard]
  have hptriv : π = 1 := spHomTriv_hom_trivial (W := S) hS2pow hScard π
  have hρ1 : ρact = 1 := by
    rw [← hπcomp, hptriv, MonoidHom.one_comp]
  intro s hsR x hx
  have h1 : ρact ⟨s, hsR⟩ = 1 := by rw [hρ1]; rfl
  have hcomm := (sec54D_quotAct_eq_one_iff (Rt M (LB M Q B) t) V1 V hRnormV1
    (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormV hf) y).mp hy)
    ⟨s, hsR⟩).mp h1 ⟨x, hx⟩
  exact hcomm
theorem sec54D_comm_W_le_W1 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53a : Stroth53aStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t r : G}
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
    exact sec54D_conj_Wt_eq (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hq))
      (conjSubgroup_eq_self_iff.mpr ((sec54D_Q_normalizes_Vt hc) hq))
  have hQnormW1 : Q ≤ Subgroup.normalizer (W1 : Set G) := by
    intro q hq
    rw [hW1def, ← conjSubgroup_eq_self_iff]
    exact sec54D_conj_Wt_eq (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hq))
      (conjSubgroup_eq_self_iff.mpr ((sec54D_Q_normalizes_Vone hc) hq))
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
    sec54D_quotAct (Rt M (LB M Q B) t) W W1 hRnormW
      (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormW1 hf) y).mp hy)
  have hNker : (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ≤ ρact.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine (sec54D_quotAct_eq_one_iff (Rt M (LB M Q B) t) W W1 hRnormW
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
    have h53a' := h53a G M Q Z B hc n t hs hsp r hr hplane
      (conjSubgroup r B) V W V1 (Sec8W1 M Q Z B t r) rfl hVdef.symm hWdef.symm hV1def.symm
      rfl
    exact h53a'.2.1
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
  letI hScomm : CommGroup S := sec54D_commGroupOfSqOne hS2
  have hScard : Nat.card S ≤ Nat.card K := by
    rw [hScardZ, ← hKcard]
  have hptriv : π = 1 := spHomTriv_hom_trivial (W := S) hS2pow hScard π
  have hρ1 : ρact = 1 := by
    rw [← hπcomp, hptriv, MonoidHom.one_comp]
  intro s hsR x hx
  have h1 : ρact ⟨s, hsR⟩ = 1 := by rw [hρ1]; rfl
  have hcomm := (sec54D_quotAct_eq_one_iff (Rt M (LB M Q B) t) W W1 hRnormW
    (fun f hf y hy => (Subgroup.mem_normalizer_iff.mp (hRnormW1 hf) y).mp hy)
    ⟨s, hsR⟩).mp h1 ⟨x, hx⟩
  exact hcomm
theorem sec54D_vone_eq_Wt (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53a : Stroth53aStatement) (hc : Ctx M Q Z B)
    {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Sec8V1 M Q Z B t r = Sec8W1 M Q Z B t r :=
  sec54_vone_eq_Wt_of_53a h34 hRoot h51 h53a hc hs hm hV hN hr hplane

theorem sec54D_comm_W_le_Vone_of_cardN (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement) (h53a : Stroth53aStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) (hs8 : Sec8Hyp hc n t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, x⁆ ∈ Sec8V1 M Q Z B t r := by
  have hWR := sec54D_comm_W_le_W1 h34 hRoot h51 h53a hc hs hm hV hs8 hr hplane
  have hV1W1 := sec54D_vone_eq_Wt h34 hRoot h51 h53a hc hs hm hV hN hr hplane
  intro s hsR x hx
  have h := hWR s hsR x hx
  rw [← hV1W1] at h
  exact h

private theorem sec54D_comm_mul_left_mul_inv (q x u : G) :
    ⁅q * x, u⁆ * ⁅x, u⁆⁻¹ = ⁅q, x * u * x⁻¹⁆ := by
  simp only [commutatorElement_def]; group

private theorem sec54D_comm_mul_right (x a b : G) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]; group

private theorem sec54D_conj_comm_eq (s x y : G) :
    ⁅s, ⁅x, y⁆⁆ = ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ := by
  simp only [commutatorElement_def]; group

theorem sec54D_hNW (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) :
    ∀ x ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, y⁆ ∈ Z := by
  classical
  have h53a : Stroth53aStatement := sec54D_stroth53a h34 hRoot h51
  have hsp : SpNat hc t := by
    obtain ⟨K, hK, hKf, hKc, hrep⟩ := hV
    exact ⟨K, hK, hKf, hKc, m, hm, hrep⟩
  have hs8 : Sec8Hyp hc n t := ⟨hs, ⟨m, hm, hV⟩⟩
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot hs hsp
  have hs6 : Stroth6Hyp hc n t := ⟨hs, hN⟩
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set W1 : Subgroup G := Sec8W1 M Q Z B t r with hW1def
  have hWQ : W ≤ Q := inf_le_left
  have hW1Q : W1 ≤ Q := inf_le_left
  have hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hc.hyp.toHyp79.comm_mem_V ha hb
  have hRN : ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ⁅s, x⁆ ∈ Q :=
    HS6.central_of_hypPlane h51 hc hs6 (Or.inl hsp) hr hplane
  have hRW : ∀ s ∈ Rt M (LB M Q B) t, ∀ y ∈ W, ⁅s, y⁆ ∈ W1 := by
    intro s hsR y hy
    exact sec54D_comm_W_le_W1 h34 hRoot h51 h53a hc hs hm hV hs8 hr hplane s hsR y hy
  have hNW1 : ∀ x ∈ hc.CN t, ∀ w ∈ W1, ⁅x, w⁆ ∈ Z := by
    intro x hx w hw
    have hw' : w ∈ Sec8V1 M Q Z B t r := by
      rw [sec54D_vone_eq_Wt h34 hRoot h51 h53a hc hs hm hV hN hr hplane]
      exact hw
    exact sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane x hx w hw'
  intro x hx y hy
  have hxR : x ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hx).1
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hxM
  have hxW : x ∈ Subgroup.normalizer (W : Set G) :=
    sec8_Wt_mem_normalizer hxQ (hc.Rt_normalizes_Vt hs.mem hxR)
  have hwW : ⁅x, y⁆ ∈ W := by
    rw [commutatorElement_def]
    exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp hxW y).mp hy) (W.inv_mem hy)
  have hwR : ∀ s ∈ Rt M (LB M Q B) t, ⁅s, ⁅x, y⁆⁆ ∈ Z := by
    intro s hsR
    have hq : ⁅s, x⁆ ∈ Q := hRN s hsR x hx
    have hw1 : ⁅s, y⁆ ∈ W1 := hRW s hsR y hy
    have hu : ⁅s, y⁆ * y ∈ Q := Q.mul_mem (hW1Q hw1) (hWQ hy)
    have hxu : x * (⁅s, y⁆ * y) * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ _).mp hu
    have h1 : ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, ⁅s, y⁆ * y⁆⁻¹ ∈ Z := by
      rw [sec54D_comm_mul_left_mul_inv]
      exact hQQ _ hq _ hxu
    have h2 : ⁅x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ ∈ Z := by
      rw [sec54D_comm_mul_right]
      have h3 : ⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹ * ⁅x, y⁆⁻¹ ∈ Z := by
        have := hQQ _ (hW1Q hw1) _ (hWQ hwW)
        rwa [commutatorElement_def] at this
      have h4 : ⁅x, ⁅s, y⁆⁆ ∈ Z := hNW1 x hx _ hw1
      have e : ⁅x, ⁅s, y⁆⁆ * (⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹) * ⁅x, y⁆⁻¹ =
          ⁅x, ⁅s, y⁆⁆ * (⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹ * ⁅x, y⁆⁻¹) := by group
      rw [e]
      exact Z.mul_mem h4 h3
    rw [sec54D_conj_comm_eq]
    have e : ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ =
        (⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, ⁅s, y⁆ * y⁆⁻¹) * (⁅x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹) := by group
    rw [e]
    exact Z.mul_mem h1 h2
  exact sec54_centralizer_Wt_le_Z h34 hRoot h51 hc hs hm hV hr hplane hwW hwR

theorem sec54FC_hcomm_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  have h53a : Stroth53aStatement := sec54D_stroth53a h34 hRoot h51
  have hV1R : ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r,
      ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t :=
    sec54D_comm_Vone_le_V h34 hRoot h51 h53a hc hs hm hV ⟨hs, ⟨m, hm, hV⟩⟩ hr hplane
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Sec8V1 M Q Z B t r with hV1def
  set W : Subgroup G := Wt Q V with hWdef
  set R : Subgroup G := Rt M (LB M Q B) t with hRdef
  set N : Subgroup G := hc.CN t with hNdef
  have hWR : ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ W, ⁅s, x⁆ ∈ V1 := by
    intro s hsR x hx
    exact sec54D_comm_W_le_Vone_of_cardN h34 hRoot h51 h53a hc hs hm hV hN
      ⟨hs, ⟨m, hm, hV⟩⟩ hr hplane s hsR x (by simpa [hVdef, hWdef] using hx)
  have hV1Q : V1 ≤ Q := by rw [hV1def]; exact sec8_V1_le_Q hc t r
  have hWQ : W ≤ Q := by rw [hWdef]; exact inf_le_left
  have hVV1 : V ≤ V1 := by
    rw [hV1def, hVdef]
    exact le_inf le_sup_right le_sup_right
  have hV1W1 : V1 = Sec8W1 M Q Z B t r :=
    sec54D_vone_eq_Wt h34 hRoot h51 h53a hc hs hm hV hN hr hplane
  have hV1W : V1 ≤ W := by
    rw [hV1W1]
    change Wt Q V1 ≤ Wt Q V
    exact inf_le_inf_left Q (Subgroup.centralizer_le hVV1)
  have hZV : Z ≤ V := by rw [hVdef]; exact sec39_Z_le_Vt
  have hQnormV : Q ≤ Subgroup.normalizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (hc.Vt_le_Q t (by simpa [hVdef] using hx))
      have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact V.mul_mem (hZV hc') hx
    · intro hx
      have hc' : ⁅q⁻¹, q * x * q⁻¹⁆ ∈ Z :=
        hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hq) (hc.Vt_le_Q t (by simpa [hVdef] using hx))
      have e : q⁻¹ * (q * x * q⁻¹) * q = ⁅q⁻¹, q * x * q⁻¹⁆ * (q * x * q⁻¹) := by
        rw [commutatorElement_def]; group
      have hmem : q⁻¹ * (q * x * q⁻¹) * q ∈ V := by
        rw [e]
        exact V.mul_mem (hZV hc') hx
      have e2 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
      rwa [e2] at hmem
  haveI hVn : (V.subgroupOf V1).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun x hx => hQnormV (hV1Q hx))
  have hS2 : ∀ s : ↥V1 ⧸ V.subgroupOf V1, s * s = 1 := by
    intro s
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (V.subgroupOf V1) s
    have hmem : (y * y : ↥V1) ∈ V.subgroupOf V1 := by
      rw [Subgroup.mem_subgroupOf]
      have hyy : (((y * y : ↥V1) : G)) = (y : G) * (y : G) := rfl
      rw [hyy]
      exact hZV (by simpa [pow_two] using hc.hyp.toHyp79.sq_mem_V (hV1Q y.2))
    calc s * s = QuotientGroup.mk' (V.subgroupOf V1) (y * y) := by rw [← hy, ← map_mul]
      _ = 1 := by rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hmem
  have hinvS : ∀ x : ↥V1 ⧸ V.subgroupOf V1, x⁻¹ = x :=
    fun x => inv_eq_of_mul_eq_one_right (hS2 x)
  have hcommS : ∀ a b : (↥V1 ⧸ V.subgroupOf V1), a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (hinvS (a * b)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinvS b, hinvS a]
  have hQnormV1 : Q ≤ Subgroup.normalizer (V1 : Set G) := by
    have key : ∀ q ∈ Q, ∀ x ∈ V1, q * x * q⁻¹ ∈ V1 := by
      intro q hq x hx
      have hc' : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (hV1Q hx)
      have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact V1.mul_mem (hVV1 (hZV hc')) hx
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key q hq x, fun hx => by
      have h1 := key q⁻¹ (Q.inv_mem hq) (q * x * q⁻¹) hx
      have e : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
      rwa [e] at h1⟩
  haveI hV1n : (V1.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun x hx => hQnormV1 (hWQ hx))
  let Φs : ↥R → (↥W →* (↥V1 ⧸ V.subgroupOf V1)) := fun s =>
    { toFun := fun x => QuotientGroup.mk' (V.subgroupOf V1)
        ⟨⁅(s:G), (x:G)⁆, hWR (s:G) s.2 (x:G) (by simpa [hWdef] using x.2)⟩
      map_one' := by
        refine (QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
          (⟨⁅(s:G), (1:G)⁆, hWR (s:G) s.2 (1:G) W.one_mem⟩ : ↥V1)).mpr ?_
        rw [Subgroup.mem_subgroupOf]; simp
      map_mul' := fun x y => by
        have hmem_c : ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ ∈ Z :=
          hc.hyp.toHyp79.comm_mem_V (hWQ x.2) (hV1Q (hWR (s:G) s.2 (y:G) (by simpa using y.2)))
        have hmem_x : ⁅(s:G), (x:G)⁆ ∈ V1 := hWR (s:G) s.2 (x:G) (by simpa using x.2)
        have hmem_y : ⁅(s:G), (y:G)⁆ ∈ V1 := hWR (s:G) s.2 (y:G) (by simpa using y.2)
        have hconj : (x:G) * ⁅(s:G), (y:G)⁆ * (x:G)⁻¹ =
            ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (y:G)⁆ := by
          rw [commutatorElement_def]; group
        have hcomm1 : ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (x:G)⁆ =
            ⁅(s:G), (x:G)⁆ * ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ :=
          hc.hyp.toHyp79.V_central hmem_c (hV1Q hmem_x)
        rw [← map_mul]
        apply (QuotientGroup.eq_iff_div_mem).mpr
        rw [Subgroup.mem_subgroupOf]
        have e : ⁅(s:G), ((x*y : ↥W) : G)⁆ / (⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆) =
            ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ := by
          rw [show ((x*y : ↥W) : G) = (x:G) * (y:G) from rfl]
          rw [commutatorElement_mul_right_eq_mul_conj]
          calc ⁅(s:G), (x:G)⁆ * (x:G) * ⁅(s:G), (y:G)⁆ * (x:G)⁻¹ /
                (⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆)
              = ⁅(s:G), (x:G)⁆ * ((x:G) * ⁅(s:G), (y:G)⁆ * (x:G)⁻¹) /
                (⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆) := by group
            _ = ⁅(s:G), (x:G)⁆ * (⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (y:G)⁆) /
                (⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆) := by rw [hconj]
            _ = ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ := by
                  rw [div_eq_mul_inv, mul_inv_rev]
                  calc ⁅(s:G), (x:G)⁆ * (⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (y:G)⁆) *
                        (⁅(s:G), (y:G)⁆⁻¹ * ⁅(s:G), (x:G)⁆⁻¹)
                      = (⁅(s:G), (x:G)⁆ * ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (y:G)⁆) *
                        (⁅(s:G), (y:G)⁆⁻¹ * ⁅(s:G), (x:G)⁆⁻¹) := by group
                    _ = (⁅(x:G), ⁅(s:G), (y:G)⁆⁆ * ⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆) *
                        (⁅(s:G), (y:G)⁆⁻¹ * ⁅(s:G), (x:G)⁆⁻¹) := by rw [← hcomm1]
                    _ = ⁅(x:G), ⁅(s:G), (y:G)⁆⁆ := by group
        change (⁅(s:G), ((x*y : ↥W) : G)⁆ / (⁅(s:G), (x:G)⁆ * ⁅(s:G), (y:G)⁆) : G) ∈ V
        rw [e]
        exact hZV hmem_c }
  have hkill : ∀ s : ↥R, V1.subgroupOf W ≤ (Φs s).ker := by
    intro s y hy
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
      (⟨⁅(s:G), (y:G)⁆, hWR (s:G) s.2 (y:G) y.2⟩ : ↥V1)).mpr (by
        rw [Subgroup.mem_subgroupOf]
        exact hV1R (s:G) s.2 (y:G) (Subgroup.mem_subgroupOf.mp hy))
  let Φbar : ↥R → (↥W ⧸ V1.subgroupOf W →* (↥V1 ⧸ V.subgroupOf V1)) := fun s =>
    QuotientGroup.lift (V1.subgroupOf W) (Φs s) (hkill s)
  have hmul : ∀ (s t : ↥R) (x : ↥W), Φs (s * t) x = Φs s x * Φs t x := by
    intro s t x
    have hmem_c : ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ ∈ V :=
      hV1R (s:G) s.2 (⁅(t:G),(x:G)⁆) (hWR (t:G) t.2 (x:G) x.2)
    have hmem_s : ⁅(s:G), (x:G)⁆ ∈ V1 := hWR (s:G) s.2 (x:G) x.2
    have hmem_t : ⁅(t:G), (x:G)⁆ ∈ V1 := hWR (t:G) t.2 (x:G) x.2
    have hconj : (s:G) * ⁅(t:G), (x:G)⁆ * (s:G)⁻¹ =
        ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ * ⁅(t:G), (x:G)⁆ := by
      rw [commutatorElement_def]; group
    have hmem_cV1 : ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ ∈ V1 := hVV1 hmem_c
    have hxW : ⁅(s:G), (x:G)⁆ ∈ W := hV1W hmem_s
    have hxW' : ⁅(s:G), (x:G)⁆ ∈ Wt Q V := hxW
    have hxcent : ⁅(s:G), (x:G)⁆ ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_inf.mp hxW').2
    have hcomm1 : ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ * ⁅(s:G), (x:G)⁆ =
        ⁅(s:G), (x:G)⁆ * ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ :=
      Subgroup.mem_centralizer_iff.mp hxcent ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ hmem_c
    have hc1 : QuotientGroup.mk' (V.subgroupOf V1)
        ⟨⁅(s:G), ⁅(t:G), (x:G)⁆⁆, hmem_cV1⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
        ⟨⁅(s:G), ⁅(t:G), (x:G)⁆⁆, hmem_cV1⟩).mpr (by
          rw [Subgroup.mem_subgroupOf]; exact hmem_c)
    have e1 : (⟨⁅((s*t : ↥R) : G), (x:G)⁆,
        hWR ((s*t:↥R):G) (s*t).2 (x:G) x.2⟩ : ↥V1) =
        ⟨⁅(s:G), ⁅(t:G), (x:G)⁆⁆ * ⁅(t:G), (x:G)⁆ * ⁅(s:G), (x:G)⁆,
          V1.mul_mem (V1.mul_mem hmem_cV1 hmem_t) hmem_s⟩ := by
      apply Subtype.ext
      change ⁅((s*t : ↥R) : G), (x:G)⁆ =
        ⁅(s:G), ⁅(t:G), (x:G)⁆⁆ * ⁅(t:G), (x:G)⁆ * ⁅(s:G), (x:G)⁆
      rw [show ((s*t : ↥R) : G) = (s:G) * (t:G) from rfl]
      rw [commutatorElement_mul_left_eq_conj_mul, hconj]
    calc Φs (s * t) x
        = QuotientGroup.mk' (V.subgroupOf V1)
            ⟨⁅(s:G), ⁅(t:G), (x:G)⁆⁆ * ⁅(t:G), (x:G)⁆ * ⁅(s:G), (x:G)⁆,
              V1.mul_mem (V1.mul_mem hmem_cV1 hmem_t) hmem_s⟩ := by
            change QuotientGroup.mk' (V.subgroupOf V1)
              ⟨⁅((s * t : ↥R) : G), (x:G)⁆,
                hWR ((s*t:↥R):G) (s*t).2 (x:G) x.2⟩ = _
            rw [e1]
      _ = QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(s:G), ⁅(t:G), (x:G)⁆⁆, hmem_cV1⟩ *
            QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(t:G), (x:G)⁆, hmem_t⟩ *
            QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(s:G), (x:G)⁆, hmem_s⟩ := by
            rw [← map_mul, ← map_mul]; rfl
      _ = QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(t:G), (x:G)⁆, hmem_t⟩ *
            QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(s:G), (x:G)⁆, hmem_s⟩ := by
            rw [hc1]; congr 1; exact one_mul _
      _ = QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(s:G), (x:G)⁆, hmem_s⟩ *
            QuotientGroup.mk' (V.subgroupOf V1) ⟨⁅(t:G), (x:G)⁆, hmem_t⟩ := by
            rw [hcommS]
      _ = Φs s x * Φs t x := rfl
  let Ψ : ↥R →* ((↥W ⧸ V1.subgroupOf W) → (↥V1 ⧸ V.subgroupOf V1)) :=
    { toFun := fun s => fun q => Φbar s q
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H z =>
          rw [QuotientGroup.lift_mk']
          exact (QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
            (⟨⁅((1 : ↥R) : G), (z:G)⁆,
              hWR _ (1 : ↥R).2 _ z.2⟩ : ↥V1)).mpr (by
                rw [Subgroup.mem_subgroupOf]; simp)
      map_mul' := by
        intro s t
        ext q
        induction q using QuotientGroup.induction_on with
        | H z =>
          rw [QuotientGroup.lift_mk']
          change Φs (s * t) z = Φs s z * Φs t z
          exact hmul s t z }
  have hNle : N.subgroupOf R ≤ Ψ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      change (QuotientGroup.lift (V1.subgroupOf W) (Φs n) (hkill n))
        (QuotientGroup.mk' (V1.subgroupOf W) z) = 1
      rw [show (QuotientGroup.lift (V1.subgroupOf W) (Φs n) (hkill n))
          (QuotientGroup.mk' (V1.subgroupOf W) z) = Φs n z from
        QuotientGroup.lift_mk' (N := V1.subgroupOf W) (φ := Φs n) (hkill n) z]
      exact (QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
        (⟨⁅(n:G), (z:G)⁆, hWR _ n.2 _ z.2⟩ : ↥V1)).mpr (by
          rw [Subgroup.mem_subgroupOf]
          exact hZV (sec54D_hNW h34 hRoot h51 hc hs hm hV hN (n:G)
            (Subgroup.mem_subgroupOf.mp hn) (z:G) (by simpa [hVdef, hWdef] using z.2)))
  obtain ⟨K, iK, iFin, hKcard, φ, hrange, hker, hact⟩ := hV
  let fsp := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp φ.rangeRestrict
  have hfs : Function.Surjective fsp :=
    (MulEquiv.subgroupCongr hrange).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  have hfker : fsp.ker = N.subgroupOf R := by
    ext r
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (MulEquiv.subgroupCongr hrange) (φ.rangeRestrict r) = 1 ↔ (r:G) ∈ N
    rw [map_eq_one_iff _ (MulEquiv.subgroupCongr hrange).injective]
    have h1 : φ.rangeRestrict r = 1 ↔ φ r = 1 := by rw [← Subtype.coe_inj]; rfl
    rw [h1, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  let π := MonoidHom.liftOfSurjective fsp hfs ⟨Ψ, hfker ▸ hNle⟩
  have hπcomp : π.comp fsp = Ψ := by
    change (MonoidHom.liftOfRightInverse fsp (Function.surjInv hfs)
      (Function.rightInverse_surjInv hfs) ⟨Ψ, hfker ▸ hNle⟩).comp fsp = Ψ
    exact MonoidHom.liftOfRightInverse_comp fsp (Function.surjInv hfs)
      (Function.rightInverse_surjInv hfs) ⟨Ψ, hfker ▸ hNle⟩
  letI := iK
  letI := iFin
  have hq4K : 4 ≤ Nat.card K := by rw [hKcard]; exact hc.hyp.q4
  have hperf : Group.IsPerfect (StatedSp m K) := by
    apply isPerfect_statedSp m K
    left
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4) (by simpa using hq4K)
    exact ⟨u, hu⟩
  have htriv : π = 1 := MonoidHom.ext (hom_eq_one_of_perfect_of_comm
    (fun a b : (↥W ⧸ V1.subgroupOf W) → (↥V1 ⧸ V.subgroupOf V1) =>
      funext (fun q => hcommS (a q) (b q))) π)
  have hΨ1 : Ψ = 1 := by rw [← hπcomp, htriv, MonoidHom.one_comp]
  intro s hsR x hx
  have hxval : Ψ ⟨s, hsR⟩ (QuotientGroup.mk' (V1.subgroupOf W) ⟨x, by simpa [hVdef, hWdef] using hx⟩) = 1 := by
    rw [hΨ1]; rfl
  change QuotientGroup.mk' (V.subgroupOf V1)
    (⟨⁅(s:G), (x:G)⁆, hWR (s:G) hsR (x:G) (by simpa [hVdef, hWdef] using hx)⟩ : ↥V1) = 1 at hxval
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := V.subgroupOf V1)
      (⟨⁅(s:G), (x:G)⁆, hWR (s:G) hsR (x:G) (by simpa [hVdef, hWdef] using hx)⟩ : ↥V1)).mp hxval)


end CFSG.RankThree.GF2n.Stroth80
