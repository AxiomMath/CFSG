module

public import CFSG.Quasithin.Vol2.Ch11SecB25
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G]

theorem le_centralizer_of_le_abelian {A B W : Subgroup G} (hW : IsMulCommutative ↥W)
    (hA : A ≤ W) (hB : B ≤ W) : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hW.is_comm.comm (⟨b, hB hb⟩ : ↥W) ⟨a, hA ha⟩)

theorem isEndStable_conjSub {L V U : Subgroup G} {m : G}
    (hmL : m ∈ Subgroup.normalizer (L : Set G)) (hmV : m ∈ Subgroup.normalizer (V : Set G))
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U) :
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) (conjSub m U) := by
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hmC : m ∈ Subgroup.normalizer (C : Set G) :=
    F7.mem_normalizer_inf hmV (F7.normalizer_le_normalizer_centralizer L hmL)
  have hm' : m⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem hmV
  intro φ hφC hφL u hu
  let ψ : ↥V →* ↥V := (SecA.conjV V m⁻¹ hm').toMonoidHom.comp
    (φ.comp (SecA.conjV V m hmV).toMonoidHom)
  have hψ : ∀ v : ↥V, ((ψ v : ↥V) : G) = m⁻¹ * (φ (SecA.conjV V m hmV v) : G) * m := by
    intro v
    change ((SecA.conjV V m⁻¹ hm' (φ (SecA.conjV V m hmV v)) : ↥V) : G) = _
    rw [SecA.conjV_apply_coe, inv_inv]
  have hψC : ∀ c : ↥V, (c : G) ∈ C → ((ψ c : ↥V) : G) ∈ C := by
    intro c hc
    have h1 : ((SecA.conjV V m hmV c : ↥V) : G) ∈ C := by
      rw [SecA.conjV_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hmC _).mp hc
    have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hmC) _).mp (hφC _ h1)
    rw [hψ]
    simpa using h2
  have hψL : ∀ l ∈ L, ∀ v w : ↥V, (w : G) = l * (v : G) * l⁻¹ →
      ((ψ w : ↥V) : G) * (l * ((ψ v : ↥V) : G) * l⁻¹)⁻¹ ∈ C := by
    intro l hl v w hw
    have hl' : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hmL l).mp hl
    have hw' : ((SecA.conjV V m hmV w : ↥V) : G) =
        (m * l * m⁻¹) * ((SecA.conjV V m hmV v : ↥V) : G) * (m * l * m⁻¹)⁻¹ := by
      rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe, hw]
      group
    have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hmC) _).mp (hφL _ hl' _ _ hw')
    rw [hψ, hψ]
    convert h2 using 1
    group
  have hu₀ : ((SecA.conjV V m⁻¹ hm' u : ↥V) : G) ∈ U := by
    rw [SecA.conjV_apply_coe, inv_inv]
    exact mem_conjSub.mp hu
  have h3 := hU ψ hψC hψL _ hu₀
  have he : SecA.conjV V m hmV (SecA.conjV V m⁻¹ hm' u) = u := by
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe]
    group
  rw [hψ, he] at h3
  exact mem_conjSub.mpr h3

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem kt_le_normalizer {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    KOf L V₁ V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
  sup_le (SecD.kOf_le_normalizer (SecD.lOf_le_normalizer L V₁)) (SecA.IsVi.le_normalizer hV₁)

theorem inH_of_le_kt (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hLT : LOf L V₁ ⊔ T ≤ H₁) (hHK : H₁ ≤ KOf L V₁ V₁ ⊔ T) : InH (LOf L V₁ ⊔ T) H₁ := by
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  exact SecD.inH_of_le hLT (hV₁T.trans (le_sup_right.trans hLT)) (h.fsu.sylow.1.to_le hV₁T)
    (SecA.IsVi.ne_bot h hV₁ le_rfl) (hHK.trans (kt_le_normalizer hV₁))

theorem inH_kt (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    InH (LOf L V₁ ⊔ T) (KOf L V₁ V₁ ⊔ T) :=
  inH_of_le_kt h hV₁ (sup_le_sup_right (le_conjClosure _ _) T) le_rfl

theorem not_kt_le_M (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hne : KOf L V₁ V₁ ≠ LOf L V₁) :
    ¬ KOf L V₁ V₁ ⊔ T ≤ Subgroup.normalizer (L : Set G) := fun hle =>
  hne (SecD.kOf_eq_lOf_of_le (SecD.kOf_cComp h1110 h1112 h hV₁) (SecD.lOf_ne_bot h1110 h hV₁)
    (le_sup_left.trans hle))

theorem oTwoUpper_sup_le (h : Hyp11 G T L I n) {K₁ : Subgroup G}
    (hTK₁ : T ≤ Subgroup.normalizer (K₁ : Set G)) : oTwoUpper (K₁ ⊔ T) ≤ K₁ :=
  SecD.oTwoUpper_le_of_le_sup' le_rfl h.fsu.sylow.1 hTK₁

theorem oTwoUpper_kt_le (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    oTwoUpper (KOf L V₁ V₁ ⊔ T) ≤ KOf L V₁ V₁ :=
  oTwoUpper_sup_le h
    ((SecA.IsVi.le_normalizer hV₁).trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁))

theorem pCoreOf_inf_le_ROf_of_le (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G}
    (hLT : LOf L V₁ ⊔ T ≤ H₁) : pCoreOf 2 ((L ⊔ T) ⊓ H₁) ≤ ROf T L V₁ :=
  F7.pCoreOf_le_pCoreOf_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow
      (le_inf le_sup_right (le_sup_right.trans hLT)))
    le_sup_right
    (le_inf (sup_le_sup_right ((perfectCore_le _).trans inf_le_left) T) hLT)

theorem pCoreOf_inf_le_ROf (h : Hyp11 G T L I n) (V₁ : Subgroup G) :
    pCoreOf 2 ((L ⊔ T) ⊓ (KOf L V₁ V₁ ⊔ T)) ≤ ROf T L V₁ :=
  pCoreOf_inf_le_ROf_of_le h (sup_le_sup_right (le_conjClosure _ _) T)

theorem pCoreOf_le_ROf_of_le (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G}
    (hLT : LOf L V₁ ⊔ T ≤ H₁) : pCoreOf 2 H₁ ≤ ROf T L V₁ :=
  F7.pCoreOf_le_pCoreOf_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_sup_right.trans hLT)) le_sup_right hLT

theorem isElemAbelian_U_of_le (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hHN : H₁ ≤ Subgroup.normalizer (V₁ : Set G)) :
    IsElemAbelian 2 (conjClosure (fsuV T I) H₁) := by
  have hab := h1157 G T L I n V₁ h hV₁
  have hle : conjClosure (fsuV T I) H₁ ≤
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) :=
    conjClosure_mono le_rfl hHN
  have hC := le_centralizer_of_le_abelian hab hle hle
  have hVel := SecA.isElemAbelian_fsuV h
  unfold conjClosure
  refine F7.isElemAbelian_closure _ (fun x hx y hy => ?_) (fun x hx => ?_)
  · exact Subgroup.mem_centralizer_iff.mp (hC (Subgroup.subset_closure hy)) x
      (Subgroup.subset_closure hx)
  · obtain ⟨g, -, z, hz, rfl⟩ := hx
    rw [conj_pow, hVel.2 z hz, mul_one, mul_inv_cancel]

theorem isElemAbelian_U (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    IsElemAbelian 2 (conjClosure (fsuV T I) (KOf L V₁ V₁ ⊔ T)) :=
  isElemAbelian_U_of_le h1157 h hV₁ (kt_le_normalizer hV₁)

theorem fsuV_le_pCoreOf_of_le (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hTH : T ≤ H₁) (hHN : H₁ ≤ Subgroup.normalizer (V₁ : Set G)) :
    fsuV T I ≤ pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUH : conjClosure (fsuV T I) H₁ ≤ H₁ :=
    conjClosure_le fun g hg v hv =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (((SecA.fsuV_le_T h).trans hTH) hv))
        (Subgroup.inv_mem _ hg)
  exact (le_conjClosure _ _).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUH
    (le_normalizer_conjClosure _ _)
    (F7.isPGroup_of_isElemAbelian (isElemAbelian_U_of_le h1157 h hV₁ hHN)))

theorem fsuV_le_pCoreOf_kt (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : fsuV T I ≤ pCoreOf 2 (KOf L V₁ V₁ ⊔ T) :=
  fsuV_le_pCoreOf_of_le h1157 h hV₁ le_sup_right (kt_le_normalizer hV₁)

theorem amalgamHypV_of_inH (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G} (hinH : InH (LOf L V₁ ⊔ T) H₁)
    (hHM : ¬ H₁ ≤ Subgroup.normalizer (L : Set G)) :
    AmalgamHypV (L ⊔ T ⊔ H₁) (L ⊔ T) H₁ T (fsuV T I) :=
  SecB.amalgamHypV_of h331 h3228 h ⟨le_sup_right.trans hinH.1, hinH.2⟩ hHM

theorem amalgamHypV_kt (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hne : KOf L V₁ V₁ ≠ LOf L V₁) :
    AmalgamHypV (L ⊔ T ⊔ (KOf L V₁ V₁ ⊔ T)) (L ⊔ T) (KOf L V₁ V₁ ⊔ T) T (fsuV T I) :=
  amalgamHypV_of_inH h331 h3228 h (inH_kt h hV₁) (not_kt_le_M h1110 h1112 h hV₁ hne)

theorem centralizer_le_normalizer_kOf (hTI : SecD.PointsTIFact) (h1102 : Stmt11_0_2)
    (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {z : G} (hz : z ∈ V₁) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have htrans := (h1141 G T L I n V₁ X h hV₁ hX).1.2
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  obtain ⟨z₀, hz₀, hz₀1, hz₀T⟩ := SecD.exists_z h hV₁
  have hK0 := h1142 G T L I n V₁ h hV₁ z₀ ⟨hV₁V hz₀, hz₀T⟩ hz₀1
  obtain ⟨l, hl, hlz⟩ := htrans z₀ (hV₁V hz₀) z (hV₁V hz) hz₀1 hz1
  have hzl : z ∈ conjSubgroup V₁ l⁻¹ := by
    rw [mem_conjSubgroup_iff, ← hlz]
    simpa [mul_assoc] using hz₀
  have hne : V₁ ⊓ conjSubgroup V₁ l⁻¹ ≠ ⊥ := fun hbot => hz1 (by
    have hz' : z ∈ V₁ ⊓ conjSubgroup V₁ l⁻¹ := ⟨hz, hzl⟩
    rw [hbot] at hz'
    exact Subgroup.mem_bot.mp hz')
  have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) := inv_mem_iff.mp
    (conjSubgroup_eq_iff_mem_normalizer.mp (hTI G T L I n V₁ hset hV₁ l⁻¹ (inv_mem hl) hne))
  have hlK := SecD.normalizer_le_normalizer_kOf L V₁ V₁ hlN
  intro c hc
  have hc' : l⁻¹ * c * l ∈ Subgroup.centralizer ({z₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have e : z₀ = l⁻¹ * z * l := by rw [← hlz]; group
    rw [e]
    calc l⁻¹ * c * l * (l⁻¹ * z * l) = l⁻¹ * (c * z) * l := by group
      _ = l⁻¹ * (z * c) * l := by rw [hc]
      _ = l⁻¹ * z * l * (l⁻¹ * c * l) := by group
  have h1 : l⁻¹ * c * l ∈ Subgroup.normalizer (KOf L V₁ V₁ : Set G) := by
    rw [← hK0]
    exact SecD.normalizer_le_normalizer_kOf L V₁ _
      (SecD.mem_normalizer_zpowers_of_mem_centralizer hc')
  have e : c = l * (l⁻¹ * c * l) * l⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlK h1) (inv_mem hlK)

theorem exists_centralizer_conjSub_eq (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) {z x : G} (hz : z ∈ fsuV T I) (hz1 : z ≠ 1)
    (hzx : z ∈ conjSub x (fsuV T I)) :
    ∃ y ∈ Subgroup.centralizer ({z} : Set G), conjSub x (fsuV T I) = conjSub y (fsuV T I) := by
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have htrans := (h1141 G T L I n V₁ X h hV₁ hX).1.2
  have hw : x⁻¹ * z * x ∈ fsuV T I := mem_conjSub.mp hzx
  have hw1 : x⁻¹ * z * x ≠ 1 := fun h1 => hz1 (by
    have e : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [e, h1]
    group)
  obtain ⟨l, hl, hlw⟩ := htrans _ hw z hz hw1 hz1
  refine ⟨x * l⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * l⁻¹ * z = x * l⁻¹ * (l * (x⁻¹ * z * x) * l⁻¹) := by rw [hlw]
      _ = z * (x * l⁻¹) := by group
  · rw [conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (inv_mem (SecA.L_le_normalizer_fsuV h hl))]

end CFSG.Quasithin.Vol2.Ch11.SecG
