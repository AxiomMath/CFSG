module

public import CFSG.Quasithin.H13.L32A711b
public import CFSG.Quasithin.H13.L32NLem14413b
public import CFSG.Quasithin.H13.L32A705a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.A6
open scoped Pointwise

@[expose] def sl3Uni (a b c : ZMod 2) : A6.SL3.S :=
  ⟨!![1, a, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]; decide⟩

@[expose] def sl3Inv : Fin 5 → A6.SL3.S :=
  ![sl3Uni 0 1 0, sl3Uni 1 0 0, sl3Uni 1 1 0, sl3Uni 0 0 1, sl3Uni 0 1 1]

theorem sl3Inv_mem : ∀ i : Fin 5, A6.SL3.InX1 (sl3Inv i) ∧ A6.SL3.InX2 (sl3Inv i) := by
  decide +kernel

theorem sl3Inv_sq : ∀ i : Fin 5, sl3Inv i * sl3Inv i = 1 ∧ sl3Inv i ≠ 1 := by
  decide +kernel

theorem sl3_P0_prod : ∀ x : A6.SL3.S, A6.SL3.InX1 x → A6.SL3.InX2 x →
    ∃ i j : Fin 5, x = sl3Inv i * sl3Inv j := by
  decide +kernel

theorem sl3_invol_conj : ∀ b : A6.SL3.S, b * b = 1 → b ≠ 1 →
    ∃ g : A6.SL3.S, g * sl3Uni 1 0 0 * g⁻¹ = b := by
  decide +kernel

@[expose] noncomputable def sl3P0Sylow : Sylow 2 A6.SL3.S :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow (P := A6.SL3.P0) (IsPGroup.of_card (n := 3) (by rw [A6.SL3.card_P0]; norm_num))
    (by rw [index_P0_SL3]; decide)

theorem exists_conj_mem_diff (Tb : Sylow 2 A6.SL3.S) {Rb : Subgroup A6.SL3.S}
    (hRT : Rb ≤ (Tb : Subgroup A6.SL3.S)) (hne : Rb ≠ (Tb : Subgroup A6.SL3.S)) {r : A6.SL3.S}
    (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ c : A6.SL3.S, c * r * c⁻¹ ∈ (Tb : Subgroup A6.SL3.S) ∧ c * r * c⁻¹ ∉ Rb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6.SL3.S sl3P0Sylow Tb
  have hTb : (Tb : Subgroup A6.SL3.S) = MulAut.conj g • (sl3P0Sylow : Subgroup A6.SL3.S) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hP0 : ∀ x : A6.SL3.S, x ∈ (sl3P0Sylow : Subgroup A6.SL3.S) ↔
      A6.SL3.InX1 x ∧ A6.SL3.InX2 x := fun _ => Iff.rfl
  have hmem : ∀ x : A6.SL3.S, A6.SL3.InX1 x → A6.SL3.InX2 x →
      g * x * g⁻¹ ∈ (Tb : Subgroup A6.SL3.S) := by
    intro x h1 h2
    rw [hTb]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g)
      (sl3P0Sylow : Subgroup A6.SL3.S) ((hP0 x).mpr ⟨h1, h2⟩)
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, g * sl3Inv i * g⁻¹ ∉ Rb := by
    by_contra hall
    push Not at hall
    apply hne
    refine le_antisymm hRT fun y hy => ?_
    rw [hTb] at hy
    have hy' := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hy
    rw [MulAut.smul_def, MulAut.conj_inv_apply] at hy'
    obtain ⟨j, k, hjk⟩ := sl3_P0_prod _ ((hP0 _).mp hy').1 ((hP0 _).mp hy').2
    have hy'' : y = (g * sl3Inv j * g⁻¹) * (g * sl3Inv k * g⁻¹) := by
      rw [show (g * sl3Inv j * g⁻¹) * (g * sl3Inv k * g⁻¹) = g * (sl3Inv j * sl3Inv k) * g⁻¹ by
        group, ← hjk]
      group
    rw [hy'']
    exact mul_mem (hall j) (hall k)
  set s := g * sl3Inv i * g⁻¹ with hs
  have hsT : s ∈ (Tb : Subgroup A6.SL3.S) :=
    hmem _ (sl3Inv_mem i).1 (sl3Inv_mem i).2
  have hs2 : s * s = 1 := by
    rw [hs, show g * sl3Inv i * g⁻¹ * (g * sl3Inv i * g⁻¹) = g * (sl3Inv i * sl3Inv i) * g⁻¹ by
      group, (sl3Inv_sq i).1]
    group
  have hs1 : s ≠ 1 := by
    intro h
    apply (sl3Inv_sq i).2
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [hs, mul_assoc] using this
  obtain ⟨g₁, hg₁⟩ := sl3_invol_conj r hr2 hr1
  obtain ⟨g₂, hg₂⟩ := sl3_invol_conj s hs2 hs1
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · have e : g₂ * g₁⁻¹ * r * (g₂ * g₁⁻¹)⁻¹ = s := by
      rw [← hg₁, ← hg₂]
      group
    rw [e]
    exact hsT
  · have e : g₂ * g₁⁻¹ * r * (g₂ * g₁⁻¹)⁻¹ = s := by
      rw [← hg₁, ← hg₂]
      group
    rw [e]
    exact hi

variable {G : Type} [Group G] [Finite G]

namespace Setting147

variable {T L V H : Subgroup G}

omit [Finite G] in
theorem mk_commute_of_mem {H : Subgroup G} (a b : ↥H)
    (h : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) b * QuotientGroup.mk' (CFSG.pCore 2 ↥H) a := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
    simpa using h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a)⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) b)⁻¹) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) b * QuotientGroup.mk' (CFSG.pCore 2 ↥H) a) := by group
    _ = _ := by rw [h1, one_mul]

theorem mem_R1_of_involution (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hinv : ∀ t ∈ T, t * t ∈ pCoreOf 2 H → ∀ l ∈ l1 T L V, t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 H)
    {t : G} (ht : t ∈ T) (ht2 : t * t = 1) : t ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
  have htH : t ∈ H := TH' S ht
  have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ ∈ modO2Image H T ⊓
      Subgroup.centralizer (modO2Image H (l1 T L V) : Set _) := by
    refine ⟨mem_modO2Image'.mpr ⟨⟨t, htH⟩, ht, rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hy
    exact (mk_commute_of_mem ⟨t, htH⟩ l
      (hinv t ht (by rw [ht2]; exact one_mem _) l hl)).symm
  rw [← R1_star_eq S h1222 h1332 h1334 hHL] at hc
  obtain ⟨r, hr, hre⟩ := mem_modO2Image'.mp hc
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf] at hre
  have hq : (r : G)⁻¹ * t ∈ pCoreOf 2 H := by simpa using hre
  rw [show t = r * ((r : G)⁻¹ * t) by group]
  exact mul_mem hr (O2H_le_R1 S hq)

theorem mem_Q_of_involution (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hR1 : ∀ t ∈ T, t * t = 1 → t ∈ pCoreOf 2 (l1 T L V ⊔ T)) {r : G} (hrT : r ∈ T)
    (hr2 : r * r = 1) : r ∈ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have htop : autOn (L ⊔ T) V = ⊤ := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S14.h1281
    rw [eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  obtain ⟨ψ, hψs, hψk⟩ := L14413.quasithinO2QuotientIso_SL3_of (sup_le S14.LV S14.TV)
    (fun v hv => S14.sq_V hv) (by rw [S14.card_V]; norm_num) htop S14.isPGroup_cent_sup
  have hker : ∀ z : ↥(L ⊔ T), ψ z = 1 ↔ (z : G) ∈ pCoreOf 2 (L ⊔ T) := by
    intro z
    rw [← MonoidHom.mem_ker, hψk]
    constructor
    · exact fun h => ⟨z, h, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      rwa [show w = z from Subtype.ext hwz] at hw
  have hTLT : T ≤ L ⊔ T := le_sup_right
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_le S.hyp le_sup_right
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hR1T : pCoreOf 2 (l1 T L V ⊔ T) ≤ T := R1_le_T S
  have hQR : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      ((sup_le_sup_right hl1L T).trans (le_normalizer_pCoreOf 2 (L ⊔ T)))
      (pCoreOf_isPGroup 2 _)
  by_contra hrQ
  set r' : ↥(L ⊔ T) := ⟨r, hTLT hrT⟩ with hr'
  have hψr1 : ψ r' ≠ 1 := fun h => hrQ ((hker r').mp h)
  have hψr2 : ψ r' * ψ r' = 1 := by
    rw [← map_mul]
    have : r' * r' = 1 := Subtype.ext hr2
    rw [this, map_one]
  have hsyl := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTLT
  have hP : IsPGroup 2 ↥(T.subgroupOf (L ⊔ T)) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLT).symm
  set PT : Sylow 2 ↥(L ⊔ T) := IsPGroup.toSylow hP hsyl.2.2 with hPT
  set Tb : Sylow 2 A6.SL3.S := Sylow.mapSurjective hψs PT with hTb
  have hTbc : (Tb : Subgroup A6.SL3.S) = (T.subgroupOf (L ⊔ T)).map ψ := by
    rw [hTb, Sylow.coe_mapSurjective]
    rfl
  set Rb := ((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf (L ⊔ T)).map ψ with hRb
  have hRT : Rb ≤ (Tb : Subgroup A6.SL3.S) := by
    rw [hTbc]
    exact Subgroup.map_mono fun x hx => (hR1T hx : (x : G) ∈ T)
  have hpre : ∀ z : ↥(L ⊔ T), ψ z ∈ (Tb : Subgroup A6.SL3.S) → (z : G) ∈ T := by
    intro z hz
    rw [hTbc] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have h1 : ψ (w⁻¹ * z) = 1 := by rw [map_mul, map_inv, hwz, inv_mul_cancel]
    have h2 := hQT ((hker _).mp h1)
    rw [show (z : G) = w * ((w⁻¹ * z : ↥(L ⊔ T)) : G) by simp]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hw) h2
  have hpreR : ∀ z : ↥(L ⊔ T), ψ z ∈ Rb → (z : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    have h1 : ψ (w⁻¹ * z) = 1 := by rw [map_mul, map_inv, hwz, inv_mul_cancel]
    have h2 := hQR ((hker _).mp h1)
    rw [show (z : G) = w * ((w⁻¹ * z : ↥(L ⊔ T)) : G) by simp]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hw) h2
  have hne : Rb ≠ (Tb : Subgroup A6.SL3.S) := by
    intro he
    have hTR : T ≤ pCoreOf 2 (l1 T L V ⊔ T) := fun t ht => by
      have h1 : ψ ⟨t, hTLT ht⟩ ∈ (Tb : Subgroup A6.SL3.S) := by
        rw [hTbc]
        exact ⟨⟨t, hTLT ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      rw [← he] at h1
      exact hpreR _ h1
    have h2 := S14.index2_eq
    rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _,
      Subgroup.relIndex_eq_one.mpr hTR] at h2
    omega
  obtain ⟨c, hcT, hcR⟩ := exists_conj_mem_diff Tb hRT hne hψr2 hψr1
  obtain ⟨x, rfl⟩ := hψs c
  set z := x * r' * x⁻¹ with hz
  have hψz : ψ z = ψ x * ψ r' * (ψ x)⁻¹ := by rw [hz, map_mul, map_mul, map_inv]
  have hzT : (z : G) ∈ T := hpre z (hψz ▸ hcT)
  have hz2 : (z : G) * z = 1 := by
    have : z * z = 1 := by
      rw [hz, show x * r' * x⁻¹ * (x * r' * x⁻¹) = x * (r' * r') * x⁻¹ by group,
        show r' * r' = 1 from Subtype.ext hr2]
      group
    exact congrArg Subtype.val this
  apply hcR
  rw [← hψz]
  have hzR := hR1 _ hzT hz2
  exact ⟨z, Subgroup.mem_subgroupOf.mpr hzR, rfl⟩

end Setting147

end CFSG.Quasithin.H13.L32A
