module

public import CFSG.Quasithin.H13.L32AC40g
public import CFSG.Quasithin.H13.L32AC40i
public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.RuType
open scoped MatrixGroups

attribute [local instance] commGroupOfFact

theorem sl24_center_eq_bot : Subgroup.center SL(2, F4) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have h1 : ∀ s : F4, s ^ 2 = 1 → s = 1 := by decide
  rw [Fintype.card_fin] at hr
  rw [h1 r hr, map_one] at hrg
  exact Subgroup.mem_bot.mpr (Subtype.ext hrg.symm)

theorem nonempty_sl24_equiv_alt5 :
    Nonempty (SL(2, F4) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F4
    (Or.inl (by rw [Nat.card_eq_fintype_card, F4.card]))
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4 ≃* SL(2, F4) :=
    (QuotientGroup.quotientMulEquivOfEq sl24_center_eq_bot).trans QuotientGroup.quotientBot
  exact ⟨(e₂.symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F4)).trans e⟩

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]

theorem isL24Section_of (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h38 : Lemma14_7_38)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHKT : H = K ⊔ T) (hA5 : IsAlt 5 (cStar K))
    (hl1K : l1 T L V ≤ K) :
    IsL24Section K (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) K) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  set Φ := phiU hF with hΦ
  have hker := phiU_eq_one_iff hF
  set X := autIH (fsuV1 T V) V H (conjClosure K T) with hXdef
  have hLb : X = (K.subgroupOf H).map Φ := by
    rw [hXdef, autIH_eq_map hF hF.K₀_le_H, hK₀]
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hmk : ∀ {a b : G} (ha : a ∈ conjClosure V H) (hb : b ∈ conjClosure V H), a = b →
      modMk hUN a ha = modMk hUN b hb := by
    rintro a b ha hb rfl
    rfl
  obtain ⟨-, hcomm, hirr⟩ := isIrrPlus_top h1222 h1332 h1334 h38 S hF hK₀ hHKT hA5 hl1K
  set C := XMod.fixed ↥X (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))) with hC
  have hmemC : ∀ w, w ∈ C ↔ ∀ x ∈ X, x w = w := fun w =>
    ⟨fun h x hx => h.2 ⟨x, hx⟩, fun h => ⟨trivial, fun a => h a a.2⟩⟩
  have hXC : X ≤ stabSub C := by
    intro x hx u
    constructor
    · intro hxu
      have h1 := (hmemC _).mp hxu x⁻¹ (X.inv_mem hx)
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
      rw [h1]
      exact hxu
    · intro hu
      rw [(hmemC u).mp hu x hx]
      exact hu
  obtain ⟨eL⟩ := nonempty_cStar_equiv_map Φ hker hF.K_cComp
  obtain ⟨eA⟩ := hA5
  obtain ⟨eS⟩ := nonempty_sl24_equiv_alt5
  let e : ↥X ≃* SL(2, F4) :=
    (MulEquiv.subgroupCongr hLb).trans ((eL.symm.trans eA).trans eS.symm)
  obtain ⟨-, hRK, hR4⟩ := s5_of h1222 h1332 h1334 S hF hK₀ hHKT ⟨eA⟩ hl1K
  have hRH : pCoreOf 2 (l1 T L V ⊔ T) ≤ H := (Setting147.R1_le_T S).trans hF.T_le_H
  have hPX : ((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Φ ≤ X := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨k, hk, hkr⟩ := hRK _ (Subgroup.mem_subgroupOf.mp hr)
    rw [hLb]
    refine ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    have h1 := (hker (⟨k, hKH hk⟩⁻¹ * r)).mpr (by simpa using hkr)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hP4 : Nat.card ↥(((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Φ) = 4 := by
    rw [card_map_eq_relIndex Φ hker hRH, hR4]
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  have hD4 : Nat.card ↥(subM (fsuV1 T V) (conjClosure V H) V) = 4 := by
    rw [card_subM hUN hV₁V (le_conjClosure V H)]
    have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) V
    rw [inf_eq_left.mpr hV₁V, hV8, hV12] at h1
    omega
  obtain ⟨x, hxL1, -, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hxL1
  have hΦxX : Φ ⟨x, hL1H hxl⟩ ∈ X := by
    rw [hLb]
    exact ⟨⟨x, hL1H hxl⟩, Subgroup.mem_subgroupOf.mpr (hl1K hxl), rfl⟩
  have hDC : subM (fsuV1 T V) (conjClosure V H) V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwD, hwC⟩
    obtain ⟨a, haV, haw⟩ := mem_secImg.mp (show ((w : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
      SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈ tildeOf (fsuV1 T V) V
      from hwD)
    have haU : (a : G) ∈ conjClosure V H := le_conjClosure V H haV
    have hwa : w = modMk hUN (a : G) haU := Subtype.ext haw.symm
    have h1 := (hmemC w).mp hwC _ hΦxX
    rw [hwa, hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
      at h1
    have h3 : (x * (a : G) * x⁻¹)⁻¹ * a ∈ fsuV1 T V :=
      (secMk_eq_secMk_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
        (B := fsuV1 T V)).mp (congrArg Subtype.val h1)
    have h2 : x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ fsuV1 T V := by
      have e2 : x * (a : G) * x⁻¹ * (a : G)⁻¹ =
          ((a : G) * ((x * (a : G) * x⁻¹)⁻¹ * a) * (a : G)⁻¹)⁻¹ := by group
      rw [e2]
      exact (fsuV1 T V).inv_mem ((Subgroup.mem_normalizer_iff.mp a.2 _).mp h3)
    have ha1 := hfpf (a : G) haV h2
    rw [Subgroup.mem_bot, hwa]
    exact Subtype.ext ((secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨(a : G), hUN haU⟩)).mpr ha1)
  have hR1triv : pCoreOf 2 (l1 T L V ⊔ T) ≤ L32NSet14.trivSub V (fsuV1 T V) := by
    rw [← Setting147.T_trivSub_eq S h1222 h1332 h1334]
    exact inf_le_right
  have hPD : ∀ p ∈ ((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Φ,
      ∀ d ∈ subM (fsuV1 T V) (conjClosure V H) V, p d = d := by
    rintro _ ⟨r, hr, rfl⟩ d hd
    obtain ⟨a, haV, had⟩ := mem_secImg.mp (show ((d : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
      SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈ tildeOf (fsuV1 T V) V
      from hd)
    have haU : (a : G) ∈ conjClosure V H := le_conjClosure V H haV
    have hda : d = modMk hUN (a : G) haU := Subtype.ext had.symm
    rw [hda, hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
    apply Subtype.ext
    refine (secMk_eq_secMk_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V)).mpr ?_
    show ((r : G) * a * (r : G)⁻¹)⁻¹ * a ∈ fsuV1 T V
    have h1 := (hR1triv (Subgroup.mem_subgroupOf.mp hr)).2.2 (a : G) haV
    have e2 : ((r : G) * a * (r : G)⁻¹)⁻¹ * a =
        ((a : G)⁻¹ * ((r : G) * a * (r : G)⁻¹ * (a : G)⁻¹) * (a : G)⁻¹⁻¹)⁻¹ := by group
    rw [e2]
    exact (fsuV1 T V).inv_mem ((Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (fsuV1 T V : Set G)).inv_mem a.2) _).mp h1)
  have hU2 : ∀ u : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), u * u = 1 := by
    intro u
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H))).2 u u.2
    simpa [pow_two] using this
  obtain ⟨φ, hφ⟩ := A5Mod.exists_natural_of_fixed hU2 e hcomm hirr hXC hPX hP4 hD4 hDC hPD
  let ιK : ↥K →* ↥X := (Φ.comp (Subgroup.inclusion hKH)).codRestrict X fun k => by
    rw [hLb]
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  let β₀ : ↥(conjClosure V H) →* CFSG.Quasithin.Sec ⊤ C :=
    MonoidHom.mk' (fun u => QuotientGroup.mk ⟨modMk hUN u u.2, Subgroup.mem_top _⟩)
      fun a b => by
        show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [← QuotientGroup.mk_mul]
        congr 1
  refine ⟨fun h hh => le_normalizer_conjClosure V H (hKH hh), e.toMonoidHom.comp ιK,
    φ.toMonoidHom.comp β₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g
    obtain ⟨⟨y, hy⟩, rfl⟩ := e.surjective g
    have hy' := hy
    rw [hLb] at hy'
    obtain ⟨k, hk, hky⟩ := hy'
    refine ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, ?_⟩
    show e (ιK _) = e ⟨y, hy⟩
    congr 1
    exact Subtype.ext hky
  ·
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Subgroup.mem_subgroupOf]
    have e1 : ιK k = 1 ↔ Φ (Subgroup.inclusion hKH k) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e1]
    exact (hker _).trans (mem_pCoreOf_iff_of_mem_cComp hF.K_cComp k.2)
  ·
    intro q
    obtain ⟨⟨w, hw0⟩, hw⟩ := QuotientGroup.mk_surjective (φ.symm q)
    obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
    refine ⟨⟨(a : G), haU⟩, ?_⟩
    have h1 : β₀ ⟨(a : G), haU⟩ = φ.symm q := by
      rw [← hw]
      show QuotientGroup.mk _ = QuotientGroup.mk _
      congr 1
      exact Subtype.ext (Subtype.ext haw)
    show φ (β₀ ⟨(a : G), haU⟩) = q
    rw [h1, MulEquiv.apply_symm_apply]
  ·
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Subgroup.mem_subgroupOf]
    rw [show β₀ u = QuotientGroup.mk ⟨modMk hUN (u : G) u.2, Subgroup.mem_top _⟩ from rfl,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show modMk hUN (u : G) u.2 ∈ C ↔ _
    rw [hmemC, hLb]
    constructor
    · intro h
      refine ⟨u.2, hUN u.2, fun k hk => ?_⟩
      have h1 := h _ ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
        at h1
      have h3 : (k * (u : G) * k⁻¹)⁻¹ * u ∈ fsuV1 T V :=
        (secMk_eq_secMk_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
          (B := fsuV1 T V)).mp (congrArg Subtype.val h1)
      have e2 : (u : G) * k * (u : G)⁻¹ * k⁻¹ =
          (u : G) * ((k * (u : G) * k⁻¹)⁻¹ * u) * (u : G)⁻¹ := by group
      rw [e2]
      exact (Subgroup.mem_normalizer_iff.mp (hUN u.2) _).mp h3
    · rintro ⟨-, -, h⟩ _ ⟨k, hk, rfl⟩
      rw [hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
      apply Subtype.ext
      refine (secMk_eq_secMk_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
        (B := fsuV1 T V)).mpr ?_
      show ((k : G) * u * (k : G)⁻¹)⁻¹ * u ∈ fsuV1 T V
      have h1 := h k (Subgroup.mem_subgroupOf.mp hk)
      have e2 : ((k : G) * u * (k : G)⁻¹)⁻¹ * u =
          (u : G)⁻¹ * ((u : G) * k * (u : G)⁻¹ * (k : G)⁻¹) * (u : G)⁻¹⁻¹ := by group
      rw [e2]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (fsuV1 T V : Set G)).inv_mem (hUN u.2)) _).mp h1
  ·
    intro k x x' hx'
    have hkey : β₀ x' = B5.secHom X (InternalSec.le_stabSub_top X) hXC (ιK k) (β₀ x) := by
      show QuotientGroup.mk _ = B5.secHom X (InternalSec.le_stabSub_top X) hXC (ιK k)
        (QuotientGroup.mk _)
      rw [B5.secHom_mk]
      congr 1
      apply Subtype.ext
      show modMk hUN (x' : G) x'.2 = Φ (Subgroup.inclusion hKH k) (modMk hUN (x : G) x.2)
      rw [hΦ, phiU, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V H)]
      exact hmk _ _ hx'
    show φ (β₀ x') = _
    rw [hkey, hφ]
    rfl

end CFSG.Quasithin.H13.L32A.C
