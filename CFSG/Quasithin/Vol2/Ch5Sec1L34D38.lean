module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38Pair
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsD38
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.EmptyFaithful.A38cD36
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.F918J1
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918L2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Vol2.Ch10.SecA
open scoped commutatorElement

section Orders3

theorem three_dvd_card_of_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    3 ∣ Nat.card X := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
  decide

theorem three_dvd_card_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    3 ∣ Nat.card X :=
  CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two h

end Orders3

section Shape

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem conj_mem_conjAutSub {s l : MulAut W} (hl : l ∈ L) : s * l * s⁻¹ ∈ conjAutSub s L :=
  ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem d38_mp_cases (h38 : A38ForSQTKCat) (hD : D31 M Mp T L V) :
    Mp = L ∨ ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧ Mp = L ⊔ conjAutSub t L := by
  have hTM : T ≤ M := hD.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have hO2 : CFSG.pCore 2 ↥M = ⊥ := by
    have h := D31.pCoreOf_eq_bot hD
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h
  have hLc : L.subgroupOf M ∈ cComp (⊤ : Subgroup ↥M) := subgroupOf_mem_cComp hD.comp
  obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hD.qsqtk hO2 hLc
  obtain ⟨m₀, hm₀, hcl⟩ : ∃ m₀ ∈ M, ∀ s ∈ M, conjAutSub s L ≤ L ⊔ conjAutSub m₀ L := by
    rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨-, t', -, -, -, hcl⟩
    · refine ⟨1, M.one_mem, fun s hs => ?_⟩
      have hLN : (L.subgroupOf M).Normal := hmap ▸ hN.map φ hφ
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_sup_left ?_
      have := hLN.conj_mem ⟨x, hLM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa [MulAut.conj_apply] using this
    · refine ⟨(φ t' : MulAut W), (φ t').2, fun s hs => ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨sh, hsh⟩ := hφ ⟨s, hs⟩
      have hx' : (⟨x, hLM hx⟩ : ↥M) ∈ Lhat.map φ := by
        rw [hmap]
        exact Subgroup.mem_subgroupOf.mpr hx
      obtain ⟨xh, hxh, hxhx⟩ := hx'
      have hmem : sh * xh * sh⁻¹ ∈ Lhat ⊔ Lhat.map (MulAut.conj t').toMonoidHom := by
        rw [← hcl]
        exact mem_conjClosure (Subgroup.mem_top sh) hxh
      have hmem' : φ (sh * xh * sh⁻¹) ∈
          L.subgroupOf M ⊔ (L.subgroupOf M).map (MulAut.conj (φ t')).toMonoidHom := by
        have h1 := Subgroup.mem_map_of_mem φ hmem
        rw [Subgroup.map_sup] at h1
        refine (sup_le_sup (le_of_eq hmap) ?_) h1
        rintro _ ⟨_, ⟨yh, hyh, rfl⟩, rfl⟩
        refine ⟨φ yh, hmap ▸ Subgroup.mem_map_of_mem φ hyh, ?_⟩
        simp [MulAut.conj_apply]
      have hval : ((φ (sh * xh * sh⁻¹) : ↥M) : MulAut W) = (MulAut.conj s).toMonoidHom x := by
        simp [map_mul, map_inv, hsh, hxhx, MulAut.conj_apply]
      rw [← hval]
      have hsub : (L.subgroupOf M ⊔ (L.subgroupOf M).map (MulAut.conj (φ t')).toMonoidHom).map
          M.subtype ≤ L ⊔ conjAutSub (φ t' : MulAut W) L := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLM]
        refine sup_le_sup le_rfl ?_
        rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨(y : MulAut W), Subgroup.mem_subgroupOf.mp hy, ?_⟩
        simp [MulAut.conj_apply]
      exact hsub ⟨_, hmem', rfl⟩
  have hqc : ∀ g : MulAut W, CFSG.IsQuasisimple ↥(conjAutSub g L) := fun g =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      hD.quasi
  have hcases : ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub m₀ L := by
    intro s hs
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hKc : conjAutSub s L ∈ cComp M := conjAutSub_mem_cComp hD.comp (hTM hs)
    have hLtc : conjAutSub m₀ L ∈ cComp M := conjAutSub_mem_cComp hD.comp hm₀
    have h1 : ⁅L, conjAutSub s L⁆ = ⊥ :=
      (cComp_eq_or_commutator_eq_bot_of_isQuasisimple hD.comp hKc hD.quasi (hqc s)).resolve_left
        fun h => hne1 h.symm
    have h2 : ⁅conjAutSub m₀ L, conjAutSub s L⁆ = ⊥ :=
      (cComp_eq_or_commutator_eq_bot_of_isQuasisimple hLtc hKc (hqc m₀) (hqc s)).resolve_left
        fun h => hne2 h.symm
    have hc : L ⊔ conjAutSub m₀ L ≤ Subgroup.centralizer (conjAutSub s L : Set (MulAut W)) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
    have hab : ⁅conjAutSub s L, conjAutSub s L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((hcl s (hTM hs)).trans hc)
    exact ne_bot_of_mem_cComp hKc ((perfect_of_mem_cComp hKc).symm.trans hab)
  by_cases hall : ∀ s ∈ T, conjAutSub s L = L
  · left
    rw [hD.Mp_eq]
    refine le_antisymm (conjClosure_le fun s hs x hx => ?_) (le_conjClosure L T)
    rw [← hall s hs]
    exact conj_mem_conjAutSub hx
  · right
    push Not at hall
    obtain ⟨s, hs, hsL⟩ := hall
    have hsm : conjAutSub s L = conjAutSub m₀ L := (hcases s hs).resolve_left hsL
    refine ⟨s, hs, fun hn => hsL (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn), ?_⟩
    rw [hD.Mp_eq]
    refine le_antisymm (conjClosure_le fun s' hs' x hx => ?_) (sup_le (le_conjClosure L T) ?_)
    · rcases hcases s' hs' with h | h
      · refine Subgroup.mem_sup_left ?_
        rw [← h]
        exact conj_mem_conjAutSub hx
      · refine Subgroup.mem_sup_right ?_
        rw [hsm, ← h]
        exact conj_mem_conjAutSub hx
    · intro y hy
      rw [mem_conjAutSub_iff] at hy
      have := mem_conjClosure (Z := L) (H := T) hs hy
      have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
      rwa [e] at this

theorem d38_center_eq_bot (hD : D31 M Mp T L V)
    (hMp : Mp = L ∨ ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧
      Mp = L ⊔ conjAutSub t L) {n : ℕ}
    (hsz : CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) :
    Subgroup.center ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := hD.quasi.1
  have h2 : IsPGroup 2 ↥(Subgroup.center ↥L) :=
    isPGroup_two_of_isSz (Subgroup.center ↥L) le_rfl hsz
  set Z : Subgroup (MulAut W) := (Subgroup.center ↥L).map L.subtype with hZ
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hLc : L ≤ Subgroup.centralizer (Z : Set (MulAut W)) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    simp only [Subgroup.coe_mul] at h3
    exact h3.symm
  have hMpc : Mp ≤ Subgroup.centralizer (Z : Set (MulAut W)) := by
    rcases hMp with h | ⟨t, htT, htL, h⟩
    · rw [h]
      exact hLc
    · rw [h]
      refine sup_le hLc ?_
      have hLt : conjAutSub t L ∈ cComp M := conjAutSub_mem_cComp hD.comp (hD.sylow.1 htT)
      have hqt : CFSG.IsQuasisimple ↥(conjAutSub t L) := CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)
        hD.quasi
      have hne : L ≠ conjAutSub t L := fun h =>
        htL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
      have hc := (cComp_eq_or_commutator_eq_bot_of_isQuasisimple hD.comp hLt hD.quasi
        hqt).resolve_left hne
      rw [Subgroup.commutator_comm] at hc
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (Subgroup.centralizer_le hZL)
  have hZMp : Z ≤ Mp := hZL.trans (insp5a_sec_L_le_Mp hD)
  have hle : Z ≤ pCoreOf 2 Mp :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZMp
      (hMpc.trans (Subgroup.centralizer_le_normalizer _)) (h2.map L.subtype)
  rw [D31.pCoreOf_Mp_eq_bot hD, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hle

theorem d38_simple_sz (hD : D31 M Mp T L V)
    (hMp : Mp = L ∨ ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧
      Mp = L ⊔ conjAutSub t L)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) :
    IsSimpleGroup ↥L ∧ ∃ n, CFSG.Blueprint.SuzukiModel ↥L 2 n := by
  obtain ⟨n, hn⟩ := hsz
  have hcen := d38_center_eq_bot hD hMp hn
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hL : CFSG.Blueprint.SuzukiModel ↥L 2 n := suzukiModel_congr e.symm hn
  exact ⟨(CFSG.LieType.Simplicity.fam_2b2_simplicity ↥L 2 n hL).2, n, hL⟩

end Shape


section Transport

variable {W : Type} [CommGroup W]

theorem conjAutSub_mul (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

theorem map_commV_conjAutSub (g : MulAut W) (X : Subgroup (MulAut W)) :
    (commV X).map g.toMonoidHom = commV (conjAutSub g X) := by
  rw [commV_eq_commSub, commV_eq_commSub, ← commSub_conjBy, map_top_toMonoidHom]
  rfl

theorem stabSub_map_eq (g : MulAut W) (V : Subgroup W) :
    stabSub (V.map g.toMonoidHom) = conjBy g (stabSub V) := by
  have key : ∀ w : W, w ∈ V.map g.toMonoidHom ↔ g⁻¹ w ∈ V := fun w => by
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro h
      exact ⟨g⁻¹ w, h, by simp⟩
  ext x
  rw [mem_conjBy_iff, mem_stabSub, mem_stabSub]
  constructor
  · intro h u
    have := h (g u)
    rw [key, key] at this
    simpa [MulAut.mul_apply] using this
  · intro h w
    rw [key, key]
    have := h (g⁻¹ w)
    simpa [MulAut.mul_apply] using this

theorem centSub_map_eq (g : MulAut W) (V : Subgroup W) :
    centSub (V.map g.toMonoidHom) = conjBy g (centSub V) := by
  ext x
  rw [mem_conjBy_iff, mem_centSub, mem_centSub]
  constructor
  · intro h v hv
    have := h (g v) ⟨v, hv, rfl⟩
    simp [MulAut.mul_apply, this]
  · rintro h _ ⟨v, hv, rfl⟩
    have h1 : g⁻¹ (x (g v)) = v := by simpa [MulAut.mul_apply] using h v hv
    have h2 := congrArg g h1
    simpa using h2

theorem map_map_inv_aut (g : MulAut W) (V : Subgroup W) :
    (V.map g.toMonoidHom).map g⁻¹.toMonoidHom = V := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id V
  ext v
  simp

variable [Finite W]

theorem two_mul_rk_autSub_le_map {X B : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h2 : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub X V)) (htX : t ∈ X) (hBX : B ≤ X)
    (hBV : B ≤ stabSub (V.map t.toMonoidHom)) (hB : IsElemAbelian2 B) (hB3 : commSeries B 3 = ⊥)
    (hne : commSub (V.map t.toMonoidHom) B ≠ ⊥) :
    2 * rk ↥(autSub B (V.map t.toMonoidHom)) ≤
      rk ↥(V.map t.toMonoidHom) - rk ↥(V.map t.toMonoidHom ⊓ fixV B) := by
  set V' := V.map t.toMonoidHom with hV'
  have hVV : V'.map t⁻¹.toMonoidHom = V := map_map_inv_aut t V
  have hA2 : IsA2 X (conjBy t⁻¹ B) :=
    IsA2.conjBy ⟨hBX, ne_bot_of_commSub_ne_bot hne, hB⟩ (X.inv_mem htX)
  have hB₁V : conjBy t⁻¹ B ≤ stabSub V := by
    rw [← hVV, stabSub_map_eq]
    exact Subgroup.map_mono hBV
  have hB₁3 : commSeries (conjBy t⁻¹ B) 3 = ⊥ := (commSeries_conjBy_eq_bot_iff t⁻¹ B 3).mpr hB3
  have hne₁ : commSub V (conjBy t⁻¹ B) ≠ ⊥ := by
    rw [← hVV, commSub_conjBy]
    exact fun h => hne ((Subgroup.map_eq_bot_iff_of_injective _ t⁻¹.injective).mp h)
  have h := two_mul_rk_autSub_le h2 hA2.1 hB₁V hA2.isElemAbelian2 hB₁3 hne₁
  have hrkAut : ∀ {B' : Subgroup (MulAut W)} {Y : Subgroup W}, B' ≤ stabSub Y →
      rk ↥(autSub B' Y) + rk ↥(B' ⊓ centSub Y) = rk ↥B' := by
    intro B' Y hBY
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_autSub_mul hBY]
  have e1 := hrkAut hB₁V
  have e2 := hrkAut hBV
  have e3 : rk ↥(conjBy t⁻¹ B) = rk ↥B := rk_conjBy t⁻¹ B
  have e4 : rk ↥(conjBy t⁻¹ B ⊓ centSub V) = rk ↥(B ⊓ centSub V') := by
    rw [← hVV, centSub_map_eq]
    unfold conjBy
    rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj t⁻¹).injective]
    exact rk_conjBy t⁻¹ _
  have e5 : rk ↥(V ⊓ fixV (conjBy t⁻¹ B)) = rk ↥(V' ⊓ fixV B) := by
    rw [fixV_conjBy, ← hVV]
    rw [← Subgroup.map_inf_eq _ _ _ t⁻¹.injective]
    exact rk_map_aut_eq _ t⁻¹
  have e6 : rk ↥V = rk ↥V' := (rk_map_aut_eq V t).symm
  omega

end Transport

section Summands

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem two_add_rk_le_of_commSub_eq (hexp : ∀ w : W, w ^ 2 = 1) {C : Subgroup W} (hCV : C ≤ V)
    (hLV : L ≤ stabSub V) (hLC : C ≤ fixV L) (hcomm : commSub V L = V) (hne : ¬ V ≤ C) :
    2 + rk ↥C ≤ rk ↥V := by
  have hlt : rk ↥C < rk ↥V := by
    by_contra h
    push Not at h
    exact hne (eq_of_le_of_rk_le hexp hCV h).symm.le
  by_contra h2
  have hrk : rk ↥V = rk ↥C + 1 := by omega
  have hidx : (C.subgroupOf V).index = 2 := by
    have h1 := (C.subgroupOf V).card_mul_index
    have h2 : Nat.card ↥(C.subgroupOf V) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV).toEquiv
    rw [h2, card_eq_two_pow hexp C, card_eq_two_pow hexp V, hrk, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  apply hne
  rw [← hcomm, commSub, Subgroup.closure_le]
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have hlv : l v ∈ V := (hLV hl v).2 hv
  have key : l v ∈ C ↔ v ∈ C := by
    constructor
    · intro h
      have h1 : l (l v) = l v := hLC h l hl
      rwa [l.injective h1] at h
    · intro h
      rw [hLC h l hl]
      exact h
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨l v, hlv⟩) (b := ⟨v, hv⟩⁻¹)).mpr (by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, key]
    simp)
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem d38_conj_pair (hD : D31 M Mp T L V) {t : MulAut W}
    (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (hL38 : A38Types ↥L) :
    ∀ g ∈ Mp ⊔ T, (conjAutSub g L = L ∧ conjAutSub g (conjAutSub t L) = conjAutSub t L) ∨
      (conjAutSub g L = conjAutSub t L ∧ conjAutSub g (conjAutSub t L) = L) := by
  have hD' : D31 M Mp T (conjAutSub t L) V := hD.conj htT
  have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
    rw [conjAutSub_inv_conjAutSub, sup_comm]
    exact hMp
  have hL38' := a38Types_conjAutSub t hL38
  have htn' := not_mem_normalizer_conjAutSub htn
  have hne : L ≠ conjAutSub t L := fun h =>
    htn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hN := insp5a_Mp_le_normalizer hD htT htn hMp hL38
  have hN' := insp5a_Mp_le_normalizer hD' (T.inv_mem htT) htn' hMp' hL38'
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := insp5a_sec_T_le_normalizer hD
  intro g hg
  have hg' : g ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hg'
  obtain ⟨m, hm, s, hs, rfl⟩ := hg'
  have hmL : conjAutSub m L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hm)
  have hmL' : conjAutSub m (conjAutSub t L) = conjAutSub t L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN' hm)
  have hinj : conjAutSub s L ≠ conjAutSub s (conjAutSub t L) := fun h => by
    apply hne
    have := congrArg (conjAutSub s⁻¹) h
    rwa [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at this
  rw [conjAutSub_mul, conjAutSub_mul]
  rcases insp5a_conj_cases hD htT hMp hL38 s hs with h1 | h1 <;>
    rcases insp5a_conj_cases hD' (T.inv_mem htT) hMp' hL38' s hs with h2 | h2
  · exact Or.inl ⟨by rw [h1, hmL], by rw [h2, hmL']⟩
  · rw [conjAutSub_inv_conjAutSub] at h2
    exact absurd (h1.trans h2.symm) hinj
  · exact absurd (h1.trans h2.symm) hinj
  · rw [conjAutSub_inv_conjAutSub] at h2
    exact Or.inr ⟨by rw [h1, hmL'], by rw [h2, hmL]⟩

end Summands

section Top

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem autSub_top_eq_map (X : Subgroup (MulAut W)) :
    autSub X (⊤ : Subgroup W) = X.map (congrHom (Subgroup.topEquiv (G := W)).symm) := by
  ext φ
  rw [mem_autSub]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, by ext u; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, mem_stabSub_top x⟩, hx, by ext u; rfl⟩

theorem qhatOf_autSub_top (X : Subgroup (MulAut W)) :
    qhatOf (autSub X (⊤ : Subgroup W)) = qhatOf X := by
  rw [autSub_top_eq_map]
  exact kq_map_congr _ X 3

theorem two_le_qhatOf_of_forall {X : Subgroup (MulAut W)}
    (h : ∀ A, IsA2 X A → commSeries A 3 = ⊥ → 2 * rk ↥A ≤ rkIdx (fixV A)) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf X := by
  refine le_kq_iff.mpr fun A hA hA3 => ?_
  have hpos := hA.isElemAbelian2.rk_pos hA.ne_bot
  have h2 := h A hA hA3
  unfold rAV
  rw [le_div_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast h2

end Top


section Cases

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d38_two_le_of_eq
    (h35 : D35) (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1)
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hLs : IsSimpleGroup ↥L)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub (Mp ⊔ T) (orbSup T V)) := by
  have h3 : ¬ 3 ∣ Nat.card ↥L := by
    obtain ⟨n, hn⟩ := hsz
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  have hL38 : A38Types ↥L := Or.inr (Or.inl hsz)
  have hVT : V = orbSup T V := by
    by_contra hne
    have hlt : V < orbSup T V := lt_of_le_of_ne (le_orbSup T V) hne
    have hLV : Mp ≤ stabSub V := insp5a_sec_Mp_le_stabSub hD.hyp
    have hMps : IsSimpleGroup ↥Mp := by rw [hMp]; exact hLs
    have hne' : ¬ Mp ≤ centSub V := fun h => by
      obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp hMp
      exact hlv (h (by rw [hMp]; exact hl) v hv)
    have hfaith : Mp ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hMps hLV hne'
    have hcent : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g := by
      intro g hg hgV x _
      have hg1 : g ∈ Mp ⊓ centSub V := ⟨hg, hgV⟩
      rw [hfaith, Subgroup.mem_bot] at hg1
      rw [hg1, one_mul, mul_one]
    obtain ⟨-, -, -, h5⟩ := h35 W M Mp T L V hD hlt hcent
    exact h3 (three_dvd_card_of_isPSL_three_two (d36A38_holds W L V hL38 h5).1)
  have hT : T ≤ stabSub V := by
    rw [hVT]
    exact CFSG.Quasithin.le_stabSub_orbSup T V
  rw [qhatOf_autSub_congr hVT.symm]
  exact two_le_qhatOf_autSub_of_suzuki_stab hB45 hA21 hF hD hMp hT hLs hsz

theorem d38_two_le_of_concl
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V)
    (htop : orbSup T V = ⊤) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥L 2 n) (hc : D36cConcl Mp T L V t) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub (Mp ⊔ T) (orbSup T V)) := by
  have h3 : ¬ 3 ∣ Nat.card ↥L := by
    obtain ⟨n, hn⟩ := hsz
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  have hL38 : A38Types ↥L := Or.inr (Or.inl hsz)
  obtain ⟨hV0, ⟨hsum0, -⟩, hqU, hU⟩ := hc
  have hUV : commSub (orbSup T V) L = V := hU.resolve_right fun h =>
    h3 (three_dvd_card_of_isPSL_three_two (isPSL_of_autSub_top htop h.1))
  have hcomm : commV L = V := by
    rw [commV_eq_commSub, ← htop]
    exact hUV
  have hN := insp5a_normalizes hD.hyp htT htn hMp hV0 hcomm hL38
  have hQ := insp5a_qsec hD.hyp htT htn hMp hV0 hcomm hL38 hN
  have hS := insp5a_sqtk hA21 hD.hyp hcomm hL38
  obtain ⟨e⟩ := insp5a_equiv hD.hyp hcomm hL38
  have hLs : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hL38
  have hsK : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hszK : ∃ n, CFSG.Blueprint.SuzukiModel ↥(autSub L V) 2 n := by
    obtain ⟨n, hn⟩ := hsz
    exact ⟨n, suzukiModel_congr e.symm hn⟩
  have hexpV : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [← qhatOf_autSub_congr hUV]
    exact hqU
  have h2sec := two_le_qhatOf_autSec_of_suzuki hB45 hF hexpV hQ hS hsK hszK hqV
  have h2V := h2sec.trans (hQ.qhatOf_autSec_le hexpV)
  have hV'c : V.map t.toMonoidHom = commV (conjAutSub t L) := by
    rw [← hcomm, map_commV_conjAutSub]
  have hmapV : ∀ g ∈ Mp ⊔ T, (V.map g.toMonoidHom = V ∧
      (V.map t.toMonoidHom).map g.toMonoidHom = V.map t.toMonoidHom) ∨
      (V.map g.toMonoidHom = V.map t.toMonoidHom ∧
        (V.map t.toMonoidHom).map g.toMonoidHom = V) := by
    intro g hg
    rcases d38_conj_pair hD.hyp htT htn hMp hL38 g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor
      · rw [← hcomm, map_commV_conjAutSub, h1]
      · rw [hV'c, map_commV_conjAutSub, h2]
    · right
      constructor
      · rw [← hcomm, map_commV_conjAutSub, h1, ← hV'c, hcomm]
      · rw [hV'c, map_commV_conjAutSub, h2, hcomm]
  have hsum : V ⊔ V.map t.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine orbSup_le fun s hs => ?_
    rcases hmapV s (Subgroup.mem_sup_right hs) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have hDV : V ⊓ V.map t.toMonoidHom ≤ V ⊓ fixV Mp := by
    rintro x ⟨hxV, hxV'⟩
    rw [hUV] at hsum0
    exact ⟨hxV, (hsum0.2 ⟨Subgroup.mem_sup_left hxV, Subgroup.mem_sup_left hxV'⟩).2⟩
  have hV2 : 2 + rk ↥(V ⊓ fixV Mp) ≤ rk ↥V := by
    have hLMp : L ≤ Mp := insp5a_sec_L_le_Mp hD.hyp
    refine two_add_rk_le_of_commSub_eq hD.hyp.exp inf_le_left (insp5a_le_stabSub hD.hyp)
      (fun x hx l hl => hx.2 l (hLMp hl))
      (insp5a_V_facts hD.hyp htT htn hMp hV0 hL38).2.2 fun h => ?_
    exact (insp5a_sec_lt hD.hyp).ne (Subgroup.subgroupOf_eq_top.mpr h)
  have hbound : ∀ A, IsA2 (Mp ⊔ T) A → commSeries A 3 = ⊥ → 2 * rk ↥A ≤ rkIdx (fixV A) := by
    intro A hA hA3
    have hsub : ∀ B ≤ A, IsElemAbelian2 B ∧ commSeries B 3 = ⊥ ∧ B ≤ Mp ⊔ T := fun B hBA =>
      ⟨⟨fun a ha b hb => hA.isElemAbelian2.1 a (hBA ha) b (hBA hb),
        fun a ha => hA.isElemAbelian2.2 a (hBA ha)⟩,
        le_bot_iff.mp (hA3 ▸ commSeries_mono hBA 3), hBA.trans hA.1⟩
    refine two_mul_rk_le_rkIdx_of_pair hsum hDV hA.isElemAbelian2 (fun a ha => ?_) hV2
      (fun B hBA hBV hne => ?_) (fun B hBA hBV hne => ?_) (fun B hBA hBV hne => ?_)
    · rcases hmapV a (hA.1 ha) with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨mem_stabSub_of_map_eq' h1, mem_stabSub_of_map_eq' h2⟩
      · exact Or.inr h
    · obtain ⟨hBe, hB3, hBX⟩ := hsub B hBA
      exact two_mul_rk_autSub_le h2V hBX hBV hBe hB3 hne
    · obtain ⟨hBe, hB3, hBX⟩ := hsub B hBA
      exact two_mul_rk_autSub_le_map h2V (Subgroup.mem_sup_right htT) hBX hBV hBe hB3 hne
    · obtain ⟨hBe, hB3, hBX⟩ := hsub B hBA
      exact two_mul_rk_autSub_le_sec hQ h2sec hBX hBV hBe hB3 hne
  rw [qhatOf_autSub_congr htop, qhatOf_autSub_top]
  exact two_le_qhatOf_of_forall hbound

end Cases

theorem d38Top_of
    (h38 : A38ForSQTKCat) (h35 : D35) (h36 : D36c) (h37 : D37)
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) : D38Top := by
  intro W _ _ M Mp T L V hD htop hsz
  refine le_antisymm hD.qhat ?_
  have hcases := d38_mp_cases h38 hD.hyp
  obtain ⟨hLs, hszL⟩ := d38_simple_sz hD.hyp hcases hsz
  have h3 : ¬ 3 ∣ Nat.card ↥L := by
    obtain ⟨n, hn⟩ := hszL
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  rcases hcases with hMp | ⟨t, htT, htn, hMp⟩
  · exact d38_two_le_of_eq h35 hB45 hA21 hF hD hMp hLs hszL
  · have hlt : V < orbSup T V := by
      refine lt_of_le_of_ne (le_orbSup T V) fun hVT => ?_
      rcases h37 W M Mp T L V hD hVT t htT htn hMp with ⟨n, hn, -⟩ | ⟨hn, -⟩
      · exact h3 (three_dvd_card_of_isPSL_two_two (isPSL_of_autSub_top (hVT.trans htop) hn))
      · exact h3 (three_dvd_card_of_isPSL_three_two (isPSL_of_autSub_top (hVT.trans htop) hn))
    rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
    · exact d38_two_le_of_concl hB45 hA21 hF hD htop htT htn hMp hszL hc
    ·
      have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
        rw [conjAutSub_inv_conjAutSub, sup_comm]
        exact hMp
      have hstd' : D3Std M Mp T (conjAutSub t L) V := ⟨hD.hyp.conj htT, hD.qhat, hD.irrT⟩
      let e := Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      have hsz' : ∃ n, CFSG.Blueprint.SuzukiModel ↥(conjAutSub t L) 2 n := by
        obtain ⟨n, hn⟩ := hszL
        exact ⟨n, suzukiModel_congr e.symm hn⟩
      exact d38_two_le_of_concl hB45 hA21 hF hstd' htop (T.inv_mem htT)
        (not_mem_normalizer_conjAutSub htn) hMp' hsz' hc

theorem d38Top_of_asB45
    (h38 : A38ForSQTKCat) (h35 : D35) (h36 : D36c) (h37 : D37) (hB45 : AsB45)
    (hF : Facts10_1) : D38Top :=
  d38Top_of h38 h35 h36 h37 hB45 CFSG.Quasithin.asA21SQTKSection hF

end CFSG.Quasithin.H13
