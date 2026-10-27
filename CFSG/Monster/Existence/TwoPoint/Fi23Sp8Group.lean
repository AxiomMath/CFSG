module

public import CFSG.Monster.Existence.TwoPoint.Fi23Sp8Orbit
public import CFSG.Monster.Existence.TwoPoint.Fi23Sp8Polar
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.Alternating.Generation

public section

namespace CFSG.Monster.Existence.Fi23Sp8

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23 CFSG.Sporadic.Th
open CFSG.Monster.Existence.Fi23Sp8.Native
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating
open CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem zmod2_ite_xor (x y : Bool) :
    (if xor x y = true then 1 else 0 : ZMod 2) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem zmod2_ite_and (x y : Bool) :
    (if (x && y) = true then 1 else 0 : ZMod 2) =
      (if x = true then 1 else 0) * (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem zmod2_ite_inj (x y : Bool)
    (h : (if x = true then 1 else 0 : ZMod 2) = if y = true then 1 else 0) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

def vecOf (n : ℕ) : V8 := fun j =>
  match j with
  | Sum.inl i => if n.testBit i.val = true then 1 else 0
  | Sum.inr i => if n.testBit (4 + i.val) = true then 1 else 0

theorem vecOf_zero : vecOf 0 = 0 := by
  funext j
  rcases j with i | i <;> simp [vecOf]

theorem vecOf_xor (a b : ℕ) : vecOf (a ^^^ b) = vecOf a + vecOf b := by
  funext j
  rcases j with i | i
  · simp only [vecOf, Nat.testBit_xor, Pi.add_apply]
    exact zmod2_ite_xor _ _
  · simp only [vecOf, Nat.testBit_xor, Pi.add_apply]
    exact zmod2_ite_xor _ _

theorem vecOf_ite (c : Bool) (a : ℕ) :
    vecOf (if c = true then a else 0) = (if c = true then 1 else 0 : ZMod 2) • vecOf a := by
  cases c <;> simp [vecOf_zero]

theorem vecOf_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : vecOf a = vecOf b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · by_cases hi4 : i < 4
    · have := congrFun h (Sum.inl ⟨i, hi4⟩)
      simp only [vecOf] at this
      exact zmod2_ite_inj _ _ this
    · have := congrFun h (Sum.inr ⟨i - 4, by omega⟩)
      simp only [vecOf] at this
      rw [show 4 + (i - 4) = i by omega] at this
      exact zmod2_ite_inj _ _ this
  · have h8 : (256 : ℕ) ≤ 2 ^ i := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h8),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h8)]

theorem exists_vecOf (v : V8) : ∃ a, a < 256 ∧ vecOf a = v := by
  have hinj : Function.Injective (fun a : Fin 256 => vecOf a.val) := fun a b h =>
    Fin.ext (vecOf_inj a.isLt b.isLt h)
  have hcard : Fintype.card (Fin 256) = Fintype.card V8 := by
    simp [ZMod.card]
  obtain ⟨a, ha⟩ := ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2 v
  exact ⟨a.val, a.isLt, ha⟩

theorem Bf_vecOf
    (a b : ℕ) : Bf (vecOf a) (vecOf b) = if beta a b = true then 1 else 0 := by
  rw [Bf_apply]
  rw [show beta a b = (xor (xor (xor (a.testBit 0 && b.testBit 4) (a.testBit 4 && b.testBit 0))
        (xor (a.testBit 1 && b.testBit 5) (a.testBit 5 && b.testBit 1)))
      (xor (xor (a.testBit 2 && b.testBit 6) (a.testBit 6 && b.testBit 2))
        (xor (a.testBit 3 && b.testBit 7) (a.testBit 7 && b.testBit 3)))) from rfl]
  simp only [zmod2_ite_xor, zmod2_ite_and]
  simp only [vecOf, Fin.sum_univ_four, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceAdd]
  ring

noncomputable def vecV (p : Pt) : V8 := vecOf (vecN p)

theorem vecV_ne_zero
    {p : Pt} (hp : p ∈ Sg) : vecV p ≠ 0 := by
  intro h
  have h1 := (vecN_range hp).1
  have h2 := (vecN_range hp).2
  have := vecOf_inj (by omega : vecN p < 256) (by norm_num : (0 : ℕ) < 256)
    (h.trans vecOf_zero.symm)
  omega

theorem vecV_inj
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) (h : vecV p = vecV q) : p = q :=
  vecN_inj hp hq (vecOf_inj (by have := (vecN_range hp).2; omega)
    (by have := (vecN_range hq).2; omega) h)

theorem exists_vecV
    {v : V8} (hv : v ≠ 0) : ∃ p ∈ Sg, vecV p = v := by
  obtain ⟨a, ha, rfl⟩ := exists_vecOf v
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hv vecOf_zero
  obtain ⟨p, hp, hpa⟩ := exists_vecN (by omega : 1 ≤ a) (by omega : a ≤ 255)
  exact ⟨p, hp, by rw [vecV, hpa]⟩

theorem Bf_vecV (p q : Pt) :
    Bf (vecV p) (vecV q) = if beta (vecN p) (vecN q) = true then 1 else 0 :=
  Bf_vecOf _ _

theorem commute_iff_Bf
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) :
    Commute (tr p) (tr q) ↔ Bf (vecV p) (vecV q) = 0 := by
  rw [commute_iff_beta hp hq, Bf_vecV]
  cases h : beta (vecN p) (vecN q) <;> simp

theorem vecV_trans
    {p q : Pt} (hp : p ∈ Sg) (hq : q ∈ Sg) :
    vecV (tr p • q) = vecV q + Bf (vecV q) (vecV p) • vecV p := by
  have e : vecV (tr p • q) =
      vecOf (vecN q ^^^ (if beta (vecN p) (vecN q) = true then vecN p else 0)) := by
    unfold vecV
    rw [vecN_trans hp hq]
  rw [e, vecOf_xor, vecOf_ite, Bf_comm (vecV q) (vecV p), Bf_vecV p q]
  rfl

open Classical in
noncomputable def ptOfV
    (v : V8) : Pt :=
  if h : ∃ p, p ∈ Sg ∧ vecV p = v then h.choose else piF 0

theorem ptOfV_spec
    {v : V8} (hv : v ≠ 0) : ptOfV v ∈ Sg ∧ vecV (ptOfV v) = v := by
  have h := exists_vecV hv
  unfold ptOfV
  rw [dite_eq_left h]
  exact h.choose_spec

theorem ptOfV_vecV
    {p : Pt} (hp : p ∈ Sg) : ptOfV (vecV p) = p := by
  obtain ⟨h1, h2⟩ := ptOfV_spec (vecV_ne_zero hp)
  exact vecV_inj h1 hp h2

open Classical in
noncomputable def actV
    (n : J) (v : V8) : V8 :=
  if v = 0 then 0 else vecV (n • ptOfV v)

theorem actV_zero
    (n : J) : actV n 0 = 0 := by
  simp [actV]

theorem actV_vecV
    (n : J) {p : Pt} (hp : p ∈ Sg) : actV n (vecV p) = vecV (n • p) := by
  unfold actV
  rw [ite_eq_right (vecV_ne_zero hp), ptOfV_vecV hp]

theorem actV_one
    (v : V8) : actV 1 v = v := by
  by_cases hv : v = 0
  · rw [hv, actV_zero]
  · obtain ⟨p, hp, rfl⟩ := exists_vecV hv
    rw [actV_vecV 1 hp, one_smul]

def MapsSg
    (n : J) : Prop := ∀ p ∈ Sg, n • p ∈ Sg

theorem mapsSg_of_mem
    {l : J} (hl : l ∈ spL) : MapsSg l := fun _ hp => smul_mem_Sg hl hp

theorem actV_mul
    (m : J) {n : J} (hn : MapsSg n) (v : V8) :
    actV (m * n) v = actV m (actV n v) := by
  by_cases hv : v = 0
  · rw [hv, actV_zero, actV_zero, actV_zero]
  · obtain ⟨p, hp, rfl⟩ := exists_vecV hv
    rw [actV_vecV _ hp, actV_vecV _ hp, actV_vecV _ (hn p hp), mul_smul]

theorem actV_ne_zero
    {n : J} (hn : MapsSg n) {v : V8} (hv : v ≠ 0) : actV n v ≠ 0 := by
  obtain ⟨p, hp, rfl⟩ := exists_vecV hv
  rw [actV_vecV _ hp]
  exact vecV_ne_zero (hn p hp)

theorem actV_inj
    {n : J} (hn : MapsSg n) : Function.Injective (actV n) := by
  intro v w h
  by_cases hv : v = 0
  · by_cases hw : w = 0
    · rw [hv, hw]
    · exfalso
      apply actV_ne_zero hn hw
      rw [← h, hv, actV_zero]
  · by_cases hw : w = 0
    · exfalso
      apply actV_ne_zero hn hv
      rw [h, hw, actV_zero]
    · obtain ⟨p, hp, rfl⟩ := exists_vecV hv
      obtain ⟨q, hq, rfl⟩ := exists_vecV hw
      rw [actV_vecV _ hp, actV_vecV _ hq] at h
      have h3 := vecV_inj (hn p hp) (hn q hq) h
      rw [smul_left_cancel n h3]

theorem actV_perp
    {n : J} (hn : MapsSg n) (u v : V8) :
    Bf u v = 0 ↔ Bf (actV n u) (actV n v) = 0 := by
  by_cases hu : u = 0
  · subst hu
    simp [actV_zero]
  by_cases hv : v = 0
  · subst hv
    simp [actV_zero]
  obtain ⟨p, hp, rfl⟩ := exists_vecV hu
  obtain ⟨q, hq, rfl⟩ := exists_vecV hv
  rw [actV_vecV _ hp, actV_vecV _ hq, ← commute_iff_Bf hp hq,
    ← commute_iff_Bf (hn p hp) (hn q hq), tr_smul, tr_smul]
  exact (commute_conj_iff n _ _).symm

theorem exists_isom
    {n : J} (hn : MapsSg n) :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) V8, g ∈ bilinIsometryGroup Bf ∧
      ∀ v, (g : V8 →ₗ[ZMod 2] V8) v = actV n v :=
  polar_aut (actV n) (actV_zero n) (actV_inj hn) (actV_perp hn)

theorem eq_one_of_fix_Sg
    {m : J} (h : ∀ p ∈ Sg, m • p = p) : m = 1 := by
  apply centralizer_trivial
  intro k hk
  have hp := piF_mem_Sg hk
  have := (smul_eq_iff_tr m (piF k) (piF k)).1 (h _ hp)
  rw [← img_eq_tr (gIdx_lt hk), mul_inv_eq_iff_eq_mul] at this
  exact this

noncomputable def rho0
    (l : spL) : LinearMap.GeneralLinearGroup (ZMod 2) V8 :=
  (exists_isom (mapsSg_of_mem l.2)).choose

theorem rho0_mem
    (l : spL) : rho0 l ∈ bilinIsometryGroup Bf :=
  (exists_isom (mapsSg_of_mem l.2)).choose_spec.1

theorem rho0_apply
    (l : spL) (v : V8) :
    (rho0 l : V8 →ₗ[ZMod 2] V8) v = actV l v :=
  (exists_isom (mapsSg_of_mem l.2)).choose_spec.2 v

theorem rho0_mul
    (a b : spL) : rho0 (a * b) = rho0 a * rho0 b := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  rw [Units.val_mul, Module.End.mul_apply, rho0_apply, rho0_apply, rho0_apply]
  exact actV_mul a (mapsSg_of_mem b.2) v

noncomputable def rhoHom :
    spL →* bilinIsometryGroup Bf :=
  MonoidHom.mk' (fun l => ⟨rho0 l, rho0_mem l⟩) fun a b => Subtype.ext (rho0_mul a b)

theorem rhoHom_apply
    (l : spL) (v : V8) :
    ((rhoHom l : LinearMap.GeneralLinearGroup (ZMod 2) V8) : V8 →ₗ[ZMod 2] V8) v = actV l v :=
  rho0_apply l v

theorem rhoHom_injective :
    Function.Injective rhoHom := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hfix : ∀ p ∈ Sg, (l : J) • p = p := by
    intro p hp
    have h1 : actV l (vecV p) = vecV p := by
      rw [← rhoHom_apply, hl]
      rfl
    rw [actV_vecV _ hp] at h1
    exact vecV_inj (smul_mem_Sg l.2 hp) hp h1
  exact Subtype.ext (eq_one_of_fix_Sg hfix)

theorem transvection_eq_rhoHom
    {p : Pt} (hp : p ∈ Sg) :
    rhoHom ⟨tr p, tr_mem_spL hp⟩ =
      ⟨symplecticTransvection Bf Bf_isAlt (vecV p) 1,
        symplecticTransvection_mem_bilinIsometryGroup Bf_isAlt _ _⟩ := by
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  rw [show ((⟨symplecticTransvection Bf Bf_isAlt (vecV p) 1,
        symplecticTransvection_mem_bilinIsometryGroup Bf_isAlt _ _⟩ :
          bilinIsometryGroup Bf) : LinearMap.GeneralLinearGroup (ZMod 2) V8) =
      symplecticTransvection Bf Bf_isAlt (vecV p) 1 from rfl]
  rw [symplecticTransvection_apply Bf_isAlt]
  show ((rhoHom ⟨tr p, tr_mem_spL hp⟩ : LinearMap.GeneralLinearGroup (ZMod 2) V8) :
    V8 →ₗ[ZMod 2] V8) v = _
  rw [rhoHom_apply]
  by_cases hv : v = 0
  · subst hv
    simp [actV_zero]
  · obtain ⟨q, hq, rfl⟩ := exists_vecV hv
    show actV (tr p) (vecV q) = _
    rw [actV_vecV _ hq, vecV_trans hp hq, one_mul]

theorem rhoHom_surjective :
    Function.Surjective rhoHom := by
  intro g
  have hg : (g : LinearMap.GeneralLinearGroup (ZMod 2) V8) ∈ Subgroup.closure
      {t | ∃ (a : V8) (c : ZMod 2), t = symplecticTransvection Bf Bf_isAlt a c} := by
    rw [← alternating_transvection_generation Bf_isAlt Bf_nondegenerate]
    exact g.2
  let R : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V8) :=
    rhoHom.range.map (bilinIsometryGroup Bf).subtype
  have hT : Subgroup.closure
      {t | ∃ (a : V8) (c : ZMod 2), t = symplecticTransvection Bf Bf_isAlt a c} ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    have h1 : symplecticTransvection Bf Bf_isAlt a 1 ∈ R := by
      by_cases ha : a = 0
      · have : symplecticTransvection Bf Bf_isAlt a 1 = 1 := by
          apply Units.ext
          apply LinearMap.ext
          intro x
          rw [symplecticTransvection_apply Bf_isAlt, ha]
          simp
        rw [this]
        exact R.one_mem
      · obtain ⟨p, hp, rfl⟩ := exists_vecV ha
        refine ⟨_, ⟨⟨tr p, tr_mem_spL hp⟩, rfl⟩, ?_⟩
        rw [transvection_eq_rhoHom hp]
        rfl
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · rw [symplecticTransvection_zero Bf_isAlt]
      exact R.one_mem
    · exact h1
  obtain ⟨x, ⟨l, rfl⟩, hx⟩ := hT hg
  exact ⟨l, Subtype.ext hx⟩

noncomputable def spEquiv :
    spL ≃* bilinIsometryGroup Bf :=
  MulEquiv.ofBijective rhoHom ⟨rhoHom_injective, rhoHom_surjective⟩

theorem mem_gIdx_iff {k : ℕ} : k ∈ gIdx ↔ k < 10 ∧ k ≠ 8 := by
  simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_spL_of_mapsSg
    {n : J} (hn : MapsSg n) : n ∈ spL := by
  obtain ⟨g, hg, hgv⟩ := exists_isom hn
  obtain ⟨l, hl⟩ := rhoHom_surjective ⟨g, hg⟩
  have hfix : ∀ p ∈ Sg, ((l : J)⁻¹ * n) • p = p := by
    intro p hp
    have h1 : actV l (vecV p) = actV n (vecV p) := by
      rw [← rhoHom_apply, hl, ← hgv]
    rw [actV_vecV _ hp, actV_vecV _ hp] at h1
    have h2 : (l : J) • p = n • p := vecV_inj (smul_mem_Sg l.2 hp) (hn p hp) h1
    rw [mul_smul, ← h2, inv_smul_smul]
  have h3 := eq_one_of_fix_Sg hfix
  rw [inv_mul_eq_one] at h3
  rw [← h3]
  exact l.2

theorem eq_spL_of_le
    {C : Subgroup J} (hC : spL ≤ C) (h8 : img 8 ∉ C) : C = spL := by
  refine le_antisymm (fun c hc => mem_spL_of_mapsSg fun p hp => ?_) hC
  by_contra hne
  have hx : LbF (c • p) ≠ 0 := hne
  have hxC : tr (c • p) ∈ C := by
    rw [tr_smul]
    exact C.mul_mem (C.mul_mem hc (hC (tr_mem_spL hp))) (C.inv_mem hc)
  exact h8 ((gen_all hC hx hxC) ▸ Subgroup.mem_top _)

theorem piF_eq_smul
    (k : ℕ) : piF k = wordG genG (prefWord k) • (0 : Pt) :=
  Fin.ext (by
    rw [smul_val]
    exact piPt_eq k)

theorem img_eight_not_mem_spL :
    img 8 ∉ spL := by
  intro h8
  have htop : spL = ⊤ := by
    rw [eq_top_iff, ← closure_img_eq_top, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    by_cases h8k : k = 8
    · subst h8k
      exact h8
    · refine img_mem_spL ?_
      simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
      omega
  set n : J := wordG genG (prefWord 8) * (wordG genG (prefWord 0))⁻¹ with hn
  have hnmem : n ∈ spL := by
    rw [htop]
    exact Subgroup.mem_top _
  have hnp : n • piF 0 = piF 8 := by
    rw [hn, piF_eq_smul 0, piF_eq_smul 8, mul_smul, inv_smul_smul]
  have h1 : LbF (piF 0) = 0 := LbF_piF (by simp [gIdx])
  have h2 : LbF (piF 8) = 1 := by
    rw [← rootF_one]
    exact LbF_rootF 1
  have h3 := LbF_smul hnmem (piF 0)
  rw [hnp, h1, h2] at h3
  exact absurd h3 (by decide)

theorem isCoatom_spL :
    IsCoatom spL := by
  refine ⟨fun h => img_eight_not_mem_spL (h ▸ Subgroup.mem_top _), fun C hC => ?_⟩
  by_cases h8 : img 8 ∈ C
  · rw [eq_top_iff, ← closure_img_eq_top, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    by_cases h8k : k = 8
    · subst h8k
      exact h8
    · refine hC.le (img_mem_spL ?_)
      simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
      omega
  · exact absurd (eq_spL_of_le hC.le h8) hC.ne'

noncomputable def bilinEquiv : bilinIsometryGroup Bf ≃* TauCeti.BilinForm.isometryGroup Bf :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V8).subgroupMap
      (bilinIsometryGroup Bf)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact TauCeti.BilinForm.mem_isometryGroup_iff.2 hh
      · intro hg
        refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V8).symm g, ?_,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V8).apply_symm_apply g⟩
        exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg))

theorem Bf_toMatrix :
    LinearMap.BilinForm.toMatrix (Pi.basisFun (ZMod 2) (Fin 4 ⊕ Fin 4)) Bf =
      Matrix.J (Fin 4) (ZMod 2) := by
  rw [Bf, LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']

noncomputable def spEquivStated :
    spL ≃* StatedSp 4 (ZMod 2) :=
  spEquiv.trans (bilinEquiv.trans
    ((CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv
      (Pi.basisFun (ZMod 2) (Fin 4 ⊕ Fin 4)) Bf Bf_toMatrix).trans
      (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)))

theorem lieModel_of_mulEquiv {G : Type} [Group G] (e : G ≃* StatedSp 4 (ZMod 2)) :
    CFSG.Blueprint.LieModel G .PSp 4 2 1 := by
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hscal : (StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf (StatedSp 4 (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  let eP : StatedSp 4 (ZMod 2) ≃* StatedProj (StatedSp 4 (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_⟩,
    ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans eP⟩⟩
  have := congrArg Prod.fst h
  simp only at this
  omega

theorem lieModel_spL :
    CFSG.Blueprint.LieModel ↥spL .PSp 4 2 1 :=
  lieModel_of_mulEquiv spEquivStated

end CFSG.Monster.Existence.Fi23Sp8
