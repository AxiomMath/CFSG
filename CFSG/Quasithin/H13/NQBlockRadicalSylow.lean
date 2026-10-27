module

public import CFSG.Quasithin.H13.NQBlockCcomponentQuotient
public import CFSG.Quasithin.SteinbergBMCComponentLift
public import CFSG.LocalAnalysis.SteinbergCCCComponentOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem isCComponent_map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) {L : Subgroup G} (hL : CFSG.IsCComponent L) :
    CFSG.IsCComponent (L.map e.toMonoidHom) := by
  refine CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mp ?_
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  refine CFSG.Quasithin.map_mem_cComp_top e.toMonoidHom e.surjective ?_
    (CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mpr hL)
  rw [hker]
  infer_instance

theorem isCComponent_top_of_isSimpleGroup {S : Type*} [Group S] [hS : IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.IsCComponent (⊤ : Subgroup S) := by
  have hcomm : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
        commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  refine ⟨(top_ne_bot : (⊤ : Subgroup S) ≠ ⊥), hcomm, IsSubnormal.top,
    fun K hK hK1 _ hKs => ?_⟩
  rcases hKs.eq_bot_or_top_of_isSimpleGroup hS with h | h
  · exact hK1 h
  · exact hK.ne h

theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {K T : Subgroup G}
    (hTK : T ≤ normalizer (K : Set G)) {g : G} (hg : g ∈ K ⊔ T) :
    ∃ k ∈ K, ∃ t ∈ T, k * t = g := by
  rw [sup_eq_closure] at hg
  induction hg using closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    · exact ⟨1, one_mem _, x, hx, one_mul x⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨k₁, hk₁, t₁, ht₁, rfl⟩ := ihx
    obtain ⟨k₂, hk₂, t₂, ht₂, rfl⟩ := ihy
    refine ⟨k₁ * (t₁ * k₂ * t₁⁻¹), mul_mem hk₁ ((mem_normalizer_iff.mp (hTK ht₁) k₂).mp hk₂),
      t₁ * t₂, mul_mem ht₁ ht₂, by group⟩
  | inv x _ ihx =>
    obtain ⟨k, hk, t, ht, rfl⟩ := ihx
    refine ⟨t⁻¹ * k⁻¹ * t⁻¹⁻¹, (mem_normalizer_iff.mp (hTK (inv_mem ht)) k⁻¹).mp (inv_mem hk),
      t⁻¹, inv_mem ht, by group⟩

theorem perfectResidual_top_map_subtype (A : Type*) [Group A] [Finite A] :
    (CFSG.perfectResidual (⊤ : Subgroup A)).map (⊤ : Subgroup A).subtype =
      CFSG.perfectResidual A := by
  have e : (⊤ : Subgroup A).subtype = (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom := by
    ext
    rfl
  rw [e]
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _ topEquiv.surjective

theorem radical_Sylow_normalizer_perfect_residual_supplement {B : Type*} [Group B] [Finite B]
    {r : ℕ} [Fact r.Prime] (L : Subgroup B) [L.Normal] (T : Sylow r B)
    (hBLT : L ⊔ (T : Subgroup B) = ⊤)
    (hsimple : IsSimpleGroup (L ⧸ CFSG.solvableRadical L))
    (hnab : ∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a)
    (N C R A K : Subgroup B) (hN : N = (CFSG.solvableRadical L).map L.subtype)
    (hC : ∀ b : B, b ∈ C ↔ ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ N)
    (hR : R = (T : Subgroup B) ⊓ C) (hA : A = L ⊓ normalizer (R : Set B))
    (hK : K = (CFSG.perfectResidual A).map A.subtype) :
    CFSG.solvableRadical B = C ∧ C = N ⊔ R ∧
      (∃ S : Sylow r (CFSG.solvableRadical B),
        (S : Subgroup (CFSG.solvableRadical B)).map (CFSG.solvableRadical B).subtype = R) ∧
      (R.subgroupOf T).Normal ∧ CFSG.pCore r B ≤ R ∧
      normalizer (R : Set B) = A ⊔ T ∧
      (∀ g ∈ normalizer (R : Set B), ∃ a ∈ A, ∃ t ∈ (T : Subgroup B), a * t = g) ∧
      (A.subgroupOf (normalizer (R : Set B))).Normal ∧ L = N ⊔ A ∧ L = N ⊔ K ∧
      K ≠ ⊥ ∧ ⁅K, K⁆ = K ∧ (CFSG.perfectResidual A).Characteristic ∧
      K ≤ normalizer (R : Set B) ∧ (K.subgroupOf (normalizer (R : Set B))).Normal ∧
      CFSG.IsCComponent (K.subgroupOf (normalizer (R : Set B))) ∧
      (∀ g ∈ K ⊔ (T : Subgroup B), ∃ k ∈ K, ∃ t ∈ (T : Subgroup B), k * t = g) ∧
      CFSG.IsCComponent (K.subgroupOf (K ⊔ T)) ∧ R ≤ K ⊔ T ∧
      (R.subgroupOf (K ⊔ T)).Normal := by
  classical
  have hLn : L.Normal := inferInstance
  obtain ⟨hRLchar, hRLsolv, hRLmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  obtain ⟨hRBchar, -, hRBmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization B
  have hRBn : (CFSG.solvableRadical B).Normal := normal_of_characteristic _
  have hRLn : (CFSG.solvableRadical L).Normal := normal_of_characteristic _
  have hNL : N ≤ L := hN ▸ map_subtype_le _
  have hNmem : ∀ y : L, (y : B) ∈ N ↔ y ∈ CFSG.solvableRadical L := fun y => by
    rw [hN]
    exact mem_map_iff_mem L.subtype_injective
  have hNn : N.Normal := by
    rw [hN]
    refine ⟨fun n hn g => ?_⟩
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.solvableRadical L) (show g ∈ normalizer (L : Set B) by
        rw [normalizer_eq_top_iff.mpr hLn]
        exact mem_top g)
    exact (mem_normalizer_iff.mp h1 n).mp hn
  have hNsolv : Group.IsSolvable N := by
    rw [hN]
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical L).equivMapOfInjective L.subtype
        L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hBL : ∀ b : B, ∃ k : ℕ, b ^ r ^ k ∈ L := by
    intro b
    have hb : b ∈ ((L ⊔ (T : Subgroup B) : Subgroup B) : Set B) := by
      rw [hBLT]
      exact mem_top b
    rw [normal_mul, Set.mem_mul] at hb
    obtain ⟨l, hl, t, ht, rfl⟩ := hb
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    have hk' : t ^ r ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff l).mpr hl, one_mul, ← QuotientGroup.mk_pow, hk',
      QuotientGroup.mk_one]
  have hCn : C.Normal := by
    refine ⟨fun c hc g => (hC _).mpr fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ L := hLn.conj_mem' x hx g
    have h1 := hNn.conj_mem _ ((hC c).mp hc _ hx') g
    have e : x⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) =
        g * ((g⁻¹ * x * g)⁻¹ * (c * (g⁻¹ * x * g) * c⁻¹)) * g⁻¹ := by group
    rw [e]
    exact h1
  have hNC : N ≤ C := fun n hn => (hC n).mpr fun x hx => by
    have e : x⁻¹ * (n * x * n⁻¹) = (x⁻¹ * n * x) * n⁻¹ := by group
    rw [e]
    exact mul_mem (hNn.conj_mem' n hn x) (inv_mem hn)
  have hRadBL : CFSG.solvableRadical B ⊓ L ≤ N := by
    intro y hy
    have hyL : y ∈ L := (mem_inf.mp hy).2
    have hsub : (CFSG.solvableRadical B ⊓ L).subgroupOf L ≤ CFSG.solvableRadical L := by
      refine hRLmax _ inferInstance ?_
      have : Group.IsSolvable (CFSG.solvableRadical B) :=
        (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization B).2.1
      exact Group.isSolvable_of_isSolvable_injective
        (f := (inclusion (inf_le_left : CFSG.solvableRadical B ⊓ L ≤
            CFSG.solvableRadical B)).comp
          (subgroupOfEquivOfLe (inf_le_right : CFSG.solvableRadical B ⊓ L ≤ L)).toMonoidHom)
        ((inclusion_injective inf_le_left).comp (MulEquiv.injective _))
    exact (hNmem ⟨y, hyL⟩).mpr (hsub (mem_subgroupOf.mpr hy))
  have hRadBC : CFSG.solvableRadical B ≤ C := fun b hb => (hC b).mpr fun x hx => by
    refine hRadBL (mem_inf.mpr ⟨?_, ?_⟩)
    · have e : x⁻¹ * (b * x * b⁻¹) = (x⁻¹ * b * x) * b⁻¹ := by group
      rw [e]
      exact mul_mem (hRBn.conj_mem' b hb x) (inv_mem hb)
    · exact mul_mem (inv_mem hx) (hLn.conj_mem x hx b)
  have hZ : center (L ⧸ CFSG.solvableRadical L) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center _) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      exact mem_center_iff.mp (h ▸ mem_top b) a
  have hCL : C ⊓ L ≤ N := by
    intro l hl
    obtain ⟨hlC, hlL⟩ := mem_inf.mp hl
    have hcen : ((⟨l, hlL⟩ : L) : L ⧸ CFSG.solvableRadical L) ∈
        center (L ⧸ CFSG.solvableRadical L) := by
      rw [mem_center_iff]
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h2 : x⁻¹ * (⟨l, hlL⟩ * x * ⟨l, hlL⟩⁻¹) ∈ CFSG.solvableRadical L :=
        (hNmem (x⁻¹ * (⟨l, hlL⟩ * x * ⟨l, hlL⟩⁻¹))).mp ((hC l).mp hlC x x.2)
      have h3 := hRLn.conj_mem' _ h2 ⟨l, hlL⟩
      have e : (x * ⟨l, hlL⟩)⁻¹ * (⟨l, hlL⟩ * x) =
          (⟨l, hlL⟩ : L)⁻¹ * (x⁻¹ * (⟨l, hlL⟩ * x * ⟨l, hlL⟩⁻¹)) * ⟨l, hlL⟩ := by group
      rw [e]
      exact h3
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hcen
    exact (hNmem _).mpr hcen
  have hCpow : ∀ c ∈ C, ∃ k : ℕ, c ^ r ^ k ∈ N := by
    intro c hc
    obtain ⟨k, hk⟩ := hBL c
    exact ⟨k, hCL (mem_inf.mpr ⟨pow_mem hc _, hk⟩)⟩
  set Nc := N.subgroupOf C with hNc
  have hquot : IsPGroup r (C ⧸ Nc) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hCpow c c.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hNc, mem_subgroupOf]
    exact hk
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent (C ⧸ Nc) := hquot.isNilpotent
    refine Group.isSolvable_of_ker_le_range (inclusion hNC) (QuotientGroup.mk' Nc) fun x hx => ?_
    rw [QuotientGroup.ker_mk', hNc, mem_subgroupOf] at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have hRadB : CFSG.solvableRadical B = C := le_antisymm hRadBC (hRBmax C hCn hCsolv)
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal T (N := C)
  have hPR : (P : Subgroup C).map C.subtype = R := by
    rw [hP, hR, map_subgroupOf_eq_of_le inf_le_right]
  have hRC : R ≤ C := hR ▸ inf_le_right
  have hRT : R ≤ T := hR ▸ inf_le_left
  have hCNR : C = N ⊔ R := by
    refine le_antisymm (fun c hc => ?_) (sup_le hNC hRC)
    have hsurj := QuotientGroup.mk'_surjective Nc
    have htop := (P.mapSurjective hsurj).is_maximal' (hquot.to_subgroup ⊤) le_top
    have h1 : QuotientGroup.mk' Nc ⟨c, hc⟩ ∈
        ((P.mapSurjective hsurj : Sylow r _) : Subgroup (C ⧸ Nc)) := by
      rw [← htop]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxc⟩ := h1
    have h2 := QuotientGroup.eq.mp hxc
    rw [hNc, mem_subgroupOf] at h2
    have hxR : (x : B) ∈ R := by
      rw [← hPR]
      exact ⟨x, hx, rfl⟩
    have e : c = (x : B) * ((x : B)⁻¹ * c) := by group
    rw [e]
    exact mul_mem (mem_sup_right hxR) (mem_sup_left (by simpa using h2))
  have hRnT : (R.subgroupOf T).Normal := by
    refine ⟨fun x hx t => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    rw [hR] at hx ⊢
    obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨mul_mem (mul_mem t.2 hxT) (inv_mem t.2), hCn.conj_mem _ hxC t⟩
  have hOr : CFSG.pCore r B ≤ R := by
    rw [hR]
    refine le_inf (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup T) ?_
    rw [← hRadB]
    refine hRBmax _ CFSG.pCore_normal ?_
    have : Group.IsNilpotent (CFSG.pCore r B) := CFSG.pCore_isPGroup.isNilpotent
    infer_instance
  have hTN : (T : Subgroup B) ≤ normalizer (R : Set B) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := hRnT.conj_mem ⟨x, hRT hx⟩ (mem_subgroupOf.mpr hx) ⟨t, ht⟩
      exact mem_subgroupOf.mp h1
    · intro hx
      have h1 := hRnT.conj_mem ⟨t * x * t⁻¹, hRT hx⟩ (mem_subgroupOf.mpr hx) ⟨t, ht⟩⁻¹
      rw [mem_subgroupOf] at h1
      simpa [mul_assoc] using h1
  have hAN : A ≤ normalizer (R : Set B) := hA ▸ inf_le_right
  have hAL : A ≤ L := hA ▸ inf_le_left
  have hNRAT : ∀ g ∈ normalizer (R : Set B), ∃ a ∈ A, ∃ t ∈ (T : Subgroup B), a * t = g := by
    intro g hg
    have hgB : g ∈ ((L ⊔ (T : Subgroup B) : Subgroup B) : Set B) := by
      rw [hBLT]
      exact mem_top g
    rw [normal_mul, Set.mem_mul] at hgB
    obtain ⟨l, hl, t, ht, rfl⟩ := hgB
    refine ⟨l, ?_, t, ht, rfl⟩
    rw [hA]
    refine mem_inf.mpr ⟨hl, ?_⟩
    have h1 := mul_mem hg (inv_mem (hTN ht))
    simpa using h1
  have hNAT : normalizer (R : Set B) = A ⊔ T := by
    refine le_antisymm (fun g hg => ?_) (sup_le hAN hTN)
    obtain ⟨a, ha, t, ht, rfl⟩ := hNRAT g hg
    exact mul_mem_sup ha ht
  have hAnorm : (A.subgroupOf (normalizer (R : Set B))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    rw [hA] at ha ⊢
    obtain ⟨haL, haN⟩ := mem_inf.mp ha
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨hLn.conj_mem _ haL g, mul_mem (mul_mem g.2 haN) (inv_mem g.2)⟩
  have hFrat := Sylow.normalizer_sup_eq_top P
  rw [hPR] at hFrat
  have hLNA : L = N ⊔ A := by
    refine le_antisymm (fun l hl => ?_) (sup_le hNL hAL)
    have hlt : l ∈ ((C ⊔ normalizer (R : Set B) : Subgroup B) : Set B) := by
      rw [sup_comm, hFrat]
      exact mem_top l
    rw [normal_mul, Set.mem_mul] at hlt
    obtain ⟨c, hc, g, hg, rfl⟩ := hlt
    have hc' : c ∈ ((N ⊔ R : Subgroup B) : Set B) := by
      rw [← hCNR]
      exact hc
    rw [normal_mul, Set.mem_mul] at hc'
    obtain ⟨n, hn, x, hx, rfl⟩ := hc'
    have hxg : x * g ∈ A := by
      rw [hA]
      refine mem_inf.mpr ⟨?_, mul_mem (le_normalizer hx) hg⟩
      have e : x * g = n⁻¹ * (n * x * g) := by group
      rw [e]
      exact mul_mem (inv_mem (hNL hn)) hl
    rw [mul_assoc]
    exact mul_mem_sup hn hxg
  set D := N.subgroupOf A with hD
  have hDsolv : Group.IsSolvable D := by
    let f : D →* N :=
      { toFun := fun x => ⟨((x : A) : B), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  let φ : A →* L ⧸ CFSG.solvableRadical L := (QuotientGroup.mk' _).comp (inclusion hAL)
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hy : (y : B) ∈ ((N ⊔ A : Subgroup B) : Set B) := by
      rw [← hLNA]
      exact y.2
    rw [normal_mul, Set.mem_mul] at hy
    obtain ⟨n, hn, a, ha, hna⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    change QuotientGroup.mk' _ (inclusion hAL ⟨a, ha⟩) = QuotientGroup.mk' _ y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hNmem]
    have e : (((inclusion hAL ⟨a, ha⟩)⁻¹ * y : L) : B) = a⁻¹ * n * a := by
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [← hna]
      group
    rw [e]
    exact hNn.conj_mem' n hn a
  have hφker : φ.ker = D := by
    ext a
    rw [MonoidHom.mem_ker, hD, mem_subgroupOf]
    change QuotientGroup.mk' _ (inclusion hAL a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hNmem]
    rfl
  have eAD : (A ⧸ D) ≃* (L ⧸ CFSG.solvableRadical L) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hADs : IsSimpleGroup (A ⧸ D) := MulEquiv.isSimpleGroup eAD
  have hTopC : CFSG.IsCComponent (⊤ : Subgroup (A ⧸ D)) := by
    obtain ⟨a, b, hab⟩ := hnab
    refine isCComponent_top_of_isSimpleGroup ⟨eAD.symm a, eAD.symm b, fun h => hab ?_⟩
    have h1 := congrArg eAD h
    simpa using h1
  obtain ⟨-, hbij⟩ := Ccomponent_solvable_quotient_bijection D hDsolv
  obtain ⟨hK'C, hK'map⟩ := hbij ⊤ hTopC
  rw [comap_top, perfectResidual_top_map_subtype] at hK'C hK'map
  obtain ⟨-, hchar, -, -, -, -⟩ := CFSG.perfect_residual_characterization (G := A)
  have hKA : K ≤ A := hK ▸ map_subtype_le _
  have hLNK : L = N ⊔ K := by
    refine le_antisymm (fun l hl => ?_) (sup_le hNL (hKA.trans hAL))
    have hl' : l ∈ ((N ⊔ A : Subgroup B) : Set B) := by
      rw [← hLNA]
      exact hl
    rw [normal_mul, Set.mem_mul] at hl'
    obtain ⟨n, hn, a, ha, rfl⟩ := hl'
    have h1 : QuotientGroup.mk' D ⟨a, ha⟩ ∈ (CFSG.perfectResidual A).map (QuotientGroup.mk' D) := by
      rw [hK'map]
      exact mem_top _
    obtain ⟨k, hk, hka⟩ := h1
    have h2 := QuotientGroup.eq.mp hka
    rw [hD, mem_subgroupOf] at h2
    have e : n * a = n * (k : B) * ((k : B)⁻¹ * a) := by group
    rw [e]
    refine mul_mem (mul_mem (mem_sup_left hn) (mem_sup_right ?_)) (mem_sup_left ?_)
    · rw [hK]
      exact ⟨k, hk, rfl⟩
    · simpa using h2
  have hKne : K ≠ ⊥ := by
    rw [hK, Ne, map_eq_bot_iff_of_injective _ A.subtype_injective]
    exact hK'C.1
  have hKperf : ⁅K, K⁆ = K := by
    rw [hK, ← map_commutator, hK'C.2.1]
  have hKN : K ≤ normalizer (R : Set B) := hKA.trans hAN
  have hNRnA : normalizer (R : Set B) ≤ normalizer (A : Set B) :=
    (normal_subgroupOf_iff_le_normalizer hAN).mp hAnorm
  have hNRnK : normalizer (R : Set B) ≤ normalizer (K : Set B) := by
    rw [hK]
    exact hNRnA.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hKnorm : (K.subgroupOf (normalizer (R : Set B))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKN).mpr hNRnK
  set M := normalizer (R : Set B) with hM
  have hKM : CFSG.IsCComponent (K.subgroupOf M) := by
    set H := A.subgroupOf M with hH
    have hHs : H.IsSubnormal := hAnorm.isSubnormal
    set eAH : A ≃* H := (subgroupOfEquivOfLe hAN).symm with heAH
    have hL'' := isCComponent_map_mulEquiv eAH hK'C
    have hlift := CFSG.Quasithin.SteinbergBM.Ccomponent_subnormal_lift hHs hL''
    have heq : ((CFSG.perfectResidual A).map eAH.toMonoidHom).map H.subtype = K.subgroupOf M := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        rw [mem_subgroupOf, hK]
        exact ⟨k, hk, rfl⟩
      · intro hx
        rw [mem_subgroupOf, hK] at hx
        obtain ⟨k, hk, hkx⟩ := hx
        refine ⟨eAH k, ⟨k, hk, rfl⟩, Subtype.ext ?_⟩
        exact hkx
    rwa [heq] at hlift
  have hKTN : K ⊔ (T : Subgroup B) ≤ M := sup_le hKN hTN
  have hKT : ∀ g ∈ K ⊔ (T : Subgroup B), ∃ k ∈ K, ∃ t ∈ (T : Subgroup B), k * t = g :=
    fun g hg => exists_mul_of_mem_sup_of_le_normalizer (hTN.trans hNRnK) hg
  have hKTC : CFSG.IsCComponent (K.subgroupOf (K ⊔ T)) := by
    have hover := CFSG.LocalAnalysis.Ccomponent_overgroup hKM
      (show K.subgroupOf M ≤ (K ⊔ (T : Subgroup B)).subgroupOf M from
        fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx)))
    set e2 : (K ⊔ (T : Subgroup B)).subgroupOf M ≃* (K ⊔ (T : Subgroup B) : Subgroup B) :=
      subgroupOfEquivOfLe hKTN with he2
    have hmap := isCComponent_map_mulEquiv e2 hover
    have heq : ((K.subgroupOf M).subgroupOf ((K ⊔ (T : Subgroup B)).subgroupOf M)).map
        e2.toMonoidHom = K.subgroupOf (K ⊔ T) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf] at hy
        exact mem_subgroupOf.mpr hy
      · intro hx
        refine ⟨e2.symm x, ?_, by simp⟩
        rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf]
        exact mem_subgroupOf.mp hx
    rwa [heq] at hmap
  have hRKT : R ≤ K ⊔ T := hRT.trans le_sup_right
  have hRnKT : (R.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRKT).mpr (hKTN.trans le_rfl)
  refine ⟨hRadB, hCNR, ?_, hRnT, hOr, hNAT, hNRAT, hAnorm, hLNA, hLNK, hKne, hKperf, hchar, hKN,
    hKnorm, hKM, hKT, hKTC, hRKT, hRnKT⟩
  rw [hRadB]
  exact ⟨P, hPR⟩

end CFSG.Quasithin.H13.NQBlock
