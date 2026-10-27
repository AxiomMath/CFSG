module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.HeringSec94ConjV
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Sylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Helpers

private theorem exists_stab {G : Type} [Group G] {R V : Subgroup G}
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (S : Set G) :
    ∃ C : Subgroup G, ∀ g, g ∈ C ↔ g ∈ R ∧ ∀ a ∈ S, ⁅g, a⁆ ∈ V := by
  refine ⟨{ carrier := {g | g ∈ R ∧ ∀ a ∈ S, ⁅g, a⁆ ∈ V}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro g h ⟨hg, hga⟩ ⟨hh, hha⟩
    refine ⟨R.mul_mem hg hh, fun a ha => ?_⟩
    have e : ⁅g * h, a⁆ = g * ⁅h, a⁆ * g⁻¹ * ⁅g, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRV hg) _).mp (hha a ha)) (hga a ha)
  · exact ⟨R.one_mem, fun a _ => by simp [commutatorElement_def]⟩
  · rintro g ⟨hg, hga⟩
    refine ⟨R.inv_mem hg, fun a ha => ?_⟩
    have e : ⁅g⁻¹, a⁆ = g⁻¹ * ⁅g, a⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hRV (R.inv_mem hg)) _).mp (V.inv_mem (hga a ha))

private theorem sl2_eq_one_of_comm {K : Type} [Field K] [CharP K 2]
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : ∀ h, h * g = g * h) : g = 1 := by
  obtain ⟨c, hc2, hcg⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp (Subgroup.mem_center_iff.mpr hg)
  rw [Fintype.card_fin] at hc2
  have hc1 : c = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : (c - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - c) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hcg, hc1, map_one]

private theorem mem_of_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hP : Nat.card P = Nat.card K)
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg2 : g ^ 2 = 1)
    (hgN : g ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) K))) :
    g ∈ P := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) K) := SL2Grp.sl2_finite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Sylow.ofCard P (hP.trans (SL2Grp.sl2_card_factorization K))
  have hp : IsPGroup 2 (Subgroup.zpowers g) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
  have hmem : g ∈ Subgroup.zpowers g ⊓
      Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    ⟨Subgroup.mem_zpowers g, hgN⟩
  rw [IsPGroup.inf_normalizer_sylow hp S] at hmem
  exact hmem.2

private theorem card_map_eq {G : Type} [Group G] [Finite G] {Y Q S : Subgroup G} {H : Type}
    [Group H] (η : ↥Y →* H) (hηk : ∀ y : ↥Y, η y = 1 ↔ (y : G) ∈ Q) (hQS : Q ≤ S)
    (hSY : S ≤ Y) : Nat.card Q * Nat.card ↥((S.subgroupOf Y).map η) = Nat.card S := by
  have hker : η.ker = Q.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hηk y
  have h := card_inf_mul_card_map hSY η hker
  rwa [inf_eq_right.mpr hQS] at h

private theorem mem_of_map_mem {G : Type} [Group G] {Y Q C : Subgroup G} {H : Type} [Group H]
    (η : ↥Y →* H) (hηk : ∀ y : ↥Y, η y = 1 ↔ (y : G) ∈ Q) (hQC : Q ≤ C) {y : ↥Y}
    (hy : η y ∈ (C.subgroupOf Y).map η) : (y : G) ∈ C := by
  obtain ⟨c, hcC, hcy⟩ := Subgroup.mem_map.mp hy
  have h1 : ((c⁻¹ * y : ↥Y) : G) ∈ Q :=
    (hηk _).mp (by rw [map_mul, map_inv, hcy, inv_mul_cancel])
  have e : (y : G) = (c : G) * ((c⁻¹ * y : ↥Y) : G) := by simp
  rw [e]
  exact C.mul_mem (Subgroup.mem_subgroupOf.mp hcC) (hQC h1)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem comm_mem_Q_of_mem_inf {hc : Ctx M Q Z B} {t r : G} (hr : Sec7A hc t r) {u : G}
    (huB : u ∈ LB M Q B) (huA : u ∈ LB M Q (conjSubgroup r B)) {g : G}
    (hg : g ∈ Rt M (LB M Q B) t) : ⁅u, g⁆ ∈ Q := by
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hQn : ∀ g ∈ M, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) x).mp hx
  let S : Subgroup G :=
    { carrier := {g | g ∈ M ∧ ⁅u, g⁆ ∈ Q}
      mul_mem' := by
        rintro g h ⟨hg, hug⟩ ⟨hh, huh⟩
        refine ⟨M.mul_mem hg hh, ?_⟩
        have e : ⁅u, g * h⁆ = ⁅u, g⁆ * (g * ⁅u, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Q.mul_mem hug (hQn g hg _ huh)
      one_mem' := ⟨M.one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro g ⟨hg, hug⟩
        refine ⟨M.inv_mem hg, ?_⟩
        have e : ⁅u, g⁻¹⁆ = g⁻¹ * ⁅u, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hQn _ (M.inv_mem hg) _ (Q.inv_mem hug) }
  have hBS : LB M Q B ≤ S := fun g hg =>
    ⟨hc.LB_le_M hg, hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator huB hg)⟩
  have huA' : u ∈ conjSubgroup r (LB M Q B) := by rw [← hc.LB_conj hrM]; exact huA
  have hAS : LB M Q (conjSubgroup r B) ≤ S := by
    intro g hg
    rw [hc.LB_conj hrM] at hg
    exact ⟨hc.conj_LB_le_M hrM hg, hc.comm_mem_Q_of_conj hrM huA' hg⟩
  have hRS : Rt M (LB M Q B) t ≤ S := by
    rw [hr.gen]
    exact sup_le hBS hAS
  exact (hRS hg).2

private theorem Rt_le_normalizer_Y {t : G} {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) :
    Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨⟨hQX, -, hQY, -, hXY, -, hcomm⟩, -, -⟩ := hsplit
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  rw [← hXY]
  exact sup_le hXY' Subgroup.le_normalizer

private theorem le_of_LA_u (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) {r : G} (hr : Sec7A hc t r) {u : G}
    (hu : u ∈ LB M Q B ⊓ Y) (huQ : u ∉ Q) {C : Subgroup G} (hQC : Q ≤ C)
    (hAC : LB M Q (conjSubgroup r B) ⊓ Y ≤ C) (huC : u ∈ C) : Y ≤ C := by
  classical
  obtain ⟨K, fK, finK, chK, h4, hKq, η, -, -, hηs, hηk, -, -, -⟩ :=
    sec4_model h34 h311a hs hsplit
  have h4c := sec4_of h34 h311a G M Q Z B hc n t hs X Y hsplit
  have hRY := Rt_le_normalizer_Y hsplit
  have hQY : Q ≤ Y := hsplit.1.2.2.1
  have hYR : Y ≤ Rt M (LB M Q B) t := hsplit.1.2.2.2.1
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨huL, huY⟩ := Subgroup.mem_inf.mp hu
  have hSAeq : LB M Q (conjSubgroup r B) ⊓ Y = conjSubgroup r (LB M Q B ⊓ Y) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr (hRY hrR)]
  have hQSA : Q ≤ LB M Q (conjSubgroup r B) ⊓ Y := le_inf sec39_Q_le_LB hQY
  have hPc : Nat.card ↥(((LB M Q (conjSubgroup r B) ⊓ Y).subgroupOf Y).map η) =
      Nat.card K := by
    have h1 := card_map_eq η hηk hQSA inf_le_right
    have h2 : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ Y) = Nat.card Q * Nat.card Z := by
      rw [hSAeq, card_conjSubgroup]
      have h3 := Subgroup.relIndex_mul_card Q (LB M Q B ⊓ Y)
      rw [h4c.2.1, inf_eq_left.mpr (le_inf sec39_Q_le_LB hQY)] at h3
      rw [← h3, mul_comm]
    rw [h2] at h1
    rw [hKq]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  set P := ((LB M Q (conjSubgroup r B) ⊓ Y).subgroupOf Y).map η with hP
  have hu2 : η ⟨u, huY⟩ ^ 2 = 1 := by
    rw [← map_pow]
    refine (hηk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact hc.sq_mem_Q_of_mem_LB huL
  have huP : η ⟨u, huY⟩ ∉ P := by
    intro hmem
    have huA : u ∈ LB M Q (conjSubgroup r B) := (mem_of_map_mem η hηk hQSA hmem).1
    have hcen : ∀ h, h * η ⟨u, huY⟩ = η ⟨u, huY⟩ * h := by
      intro h
      obtain ⟨y, rfl⟩ := hηs h
      have hc1 : ⁅u, (y : G)⁆ ∈ Q := comm_mem_Q_of_mem_inf hr huL huA (hYR y.2)
      have h2 : η ⁅(⟨u, huY⟩ : ↥Y), y⁆ = 1 :=
        (hηk _).mpr (by simpa [commutatorElement_def] using hc1)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    exact huQ ((hηk _).mp (sl2_eq_one_of_comm hcen))
  have hne : P ≠ P.map (MulAut.conj (η ⟨u, huY⟩)).toMonoidHom := by
    intro heq
    exact huP (mem_of_mem_normalizer hPc hu2
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm))
  have htop := SL2Grp.two_sylow_generate hPc
    ((Subgroup.card_map_of_injective (MulAut.conj (η ⟨u, huY⟩)).injective).trans hPc) hne
  have hPH : P ≤ (C.subgroupOf Y).map η := Subgroup.map_mono fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hAC (Subgroup.mem_subgroupOf.mp hy))
  have huH : η ⟨u, huY⟩ ∈ (C.subgroupOf Y).map η :=
    Subgroup.mem_map.mpr ⟨⟨u, huY⟩, Subgroup.mem_subgroupOf.mpr huC, rfl⟩
  have hPH' : P.map (MulAut.conj (η ⟨u, huY⟩)).toMonoidHom ≤ (C.subgroupOf Y).map η := by
    rintro _ ⟨p, hp, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huH (hPH hp)) (Subgroup.inv_mem _ huH)
  have hHtop : (C.subgroupOf Y).map η = ⊤ := top_le_iff.mp (htop ▸ sup_le hPH hPH')
  intro y hy
  exact mem_of_map_mem (y := ⟨y, hy⟩) η hηk hQC (hHtop ▸ Subgroup.mem_top _)

private theorem inf_le_of_normal (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) {C : Subgroup G} (hQC : Q ≤ C)
    (hCn : ∀ g ∈ Y, ∀ c ∈ C, g * c * g⁻¹ ∈ C) {u : G} (huY : u ∈ Y) (huC : u ∉ C) :
    C ⊓ Y ≤ Q := by
  classical
  obtain ⟨K, fK, finK, chK, h4, -, η, -, -, hηs, hηk, -, -, -⟩ :=
    sec4_model h34 h311a hs hsplit
  haveI : (C.subgroupOf Y).Normal := ⟨fun c hc g =>
    Subgroup.mem_subgroupOf.mpr (hCn g g.2 c (Subgroup.mem_subgroupOf.mp hc))⟩
  haveI := HS9.isSimpleGroup_sl2 h4
  haveI : ((C.subgroupOf Y).map η).Normal := Subgroup.Normal.map inferInstance η hηs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf Y).map η) with hbot | htop
  · intro c hc
    have hmem : η ⟨c, hc.2⟩ ∈ (C.subgroupOf Y).map η :=
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hc.1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hηk _).mp hmem
  · exact (huC (mem_of_map_mem (y := ⟨u, huY⟩) η hηk hQC (htop ▸ Subgroup.mem_top _))).elim

private theorem inf_QA_eq (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) :
    Vt M (LB M Q B) B Z t ⊓ (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))) := by
  rw [conjSubgroup_inf, conjSubgroup_inf, sec9_conj_Vt_eq hc ht hr, sec9_conj_Wt_eq hc ht hr,
    QB_conj]

private theorem card_QA (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G}
    (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r) :
    Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n ∧
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓
        (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) = Nat.card Z ^ 4 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨h1, h2⟩ := sec9_numerics h34 (step91OrderQB_of h34) (step91OrderVQB_of h34) hs
  exact ⟨(sec9_card_X₁ hc ht hr.mem).trans h1,
    by rw [inf_QA_eq hc ht hr.mem, card_conjSubgroup, h2]⟩

private theorem ker_mem (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h91b : Stroth91bStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) {r : G} (hr : Sec7A hc t r)
    {u : G} (hu : u ∈ LB M Q B ⊓ Y) (huQ : u ∉ Q) {a : G}
    (ha : a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))
    (hua : ⁅u, a⁆ ∈ Vt M (LB M Q B) B Z t) : a ∈ Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr := hc.conj_of_mem hrM
  have hXR : X ≤ Rt M (LB M Q B) t := hsplit.1.2.1
  have hYR : Y ≤ Rt M (LB M Q B) t := hsplit.1.2.2.2.1
  have hXY : X ⊔ Y = Rt M (LB M Q B) t := hsplit.1.2.2.2.2.1
  obtain ⟨haA, haW⟩ := Subgroup.mem_inf.mp ha
  have haQ : a ∈ Q := haW.1
  obtain ⟨C, hC⟩ := exists_stab (hc.Rt_normalizes_Vt ht) {a}
  have hCa : ∀ g, g ∈ C ↔ g ∈ Rt M (LB M Q B) t ∧ ⁅g, a⁆ ∈ Vt M (LB M Q B) B Z t := fun g =>
    (hC g).trans (and_congr_right fun _ => ⟨fun h => h a rfl, fun h a' ha' => ha' ▸ h⟩)
  have hQC : Q ≤ C := fun q hq =>
    (hCa q).mpr ⟨hc.Q_le_Rt ht hq, sec39_Z_le_Vt (hc.hyp.toHyp79.comm_mem_V hq haQ)⟩
  have hAC : LB M Q (conjSubgroup r B) ⊓ Y ≤ C := by
    intro g hg
    have hgR : g ∈ Rt M (LB M Q B) t := by
      rw [hr.gen]
      exact Subgroup.mem_sup_right hg.1
    refine (hCa g).mpr ⟨hgR, ?_⟩
    have h1 := hcr.comm_LB_inf_QB_mem_sup hg.1 ⟨haQ, haA⟩
    have h2 : (Z ⊔ conjSubgroup r B : Subgroup G) ≤ Vt M (LB M Q B) B Z t := by
      rw [sup_comm]
      exact hc.conj_Rt_le_Vt ht hrR
    exact h2 h1
  have huC : u ∈ C := (hCa u).mpr ⟨hYR hu.2, hua⟩
  have hYC := le_of_LA_u h34 h311a hs hsplit hr hu huQ hQC hAC huC
  have hXC : X ≤ C := fun x hx => (hCa x).mpr ⟨hXR hx, hsplit.2.2 x hx a haW⟩
  have hRC : Rt M (LB M Q B) t ≤ C := by
    rw [← hXY]
    exact sup_le hXC hYC
  have h1 : ⁅r⁻¹, a⁆ ∈ Vt M (LB M Q B) B Z t :=
    ((hCa r⁻¹).mp (hRC (Subgroup.inv_mem _ hrR))).2
  have ha' : r⁻¹ * a * r ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
    refine ⟨?_, ?_⟩
    · rw [QB_conj] at haA
      exact mem_conjSubgroup.mp haA
    · have := sec9_conj_mem_Wt hc ht (Subgroup.inv_mem _ hrR) haW
      simpa using this
  obtain ⟨⟨-, -, -, -, -, hinf⟩, -⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  rw [← hinf]
  refine ⟨Subgroup.mem_sup_left ha, ?_⟩
  have e : a = ⁅r⁻¹, a⁆⁻¹ * (r⁻¹ * a * r) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    (Subgroup.mem_sup_left ha')

private theorem card_C_mul_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h91b : Stroth91bStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) {r : G} (hr : Sec7A hc t r)
    {u : G} (hu : u ∈ LB M Q B ⊓ Y) (huQ : u ∉ Q) {C : Subgroup G}
    (hC : ∀ x, x ∈ C ↔ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧ ⁅u, x⁆ ∈ Vt M (LB M Q B) B Z t) :
    Nat.card C * Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ≤
      Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t ⊓
        (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) := by
  have huM : u ∈ M := hc.LB_le_M hu.1
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVW := HS6.Vt_le_Wt h34 hc hs.toSec5
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hCW : C ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx => ((hC x).mp hx).1
  have hZC : Z ≤ C := fun z hz =>
    (hC z).mpr ⟨hVW (hZV hz), hZV (comm_left_mem_Z_of_mem_M hc huM hz)⟩
  have hnorm : QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Subgroup.normalizer (C : Set G) :=
    HS9.normalizer_of_commutator_le hZC fun c hc' a ha =>
      HS9.comm_Q91 hc (hWQ (hCW hc')) (hWQ ha.2)
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  have h1 := Subgroup.card_le_of_le (sup_le hCW (inf_le_right :
    QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t)))
  have h2 : Nat.card ↥(C ⊓ (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓
        (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) :=
    Subgroup.card_le_of_le fun x hx =>
      ⟨ker_mem h34 h311a h91b hs hsplit hr hu huQ hx.2 ((hC x).mp hx.1).2, hx.2⟩
  rw [← hcard]
  exact Nat.mul_le_mul h1 h2

private theorem moves_mem (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h91b : Stroth91bStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) {r : G} (hr : Sec7A hc t r)
    (hn5 : 5 ≤ n) {u : G} (hu : u ∈ LB M Q B ⊓ Y) (huQ : u ∉ Q) :
    ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅u, w⁆ ∉ Vt M (LB M Q B) B Z t := by
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨C, hC⟩ := HS9.exists_subgroup_comm_mem_Vt91 hc hZV (hc.Vt_le_Q t)
    (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) u
  have hle := card_C_mul_le h34 h311a h91b hs hsplit hr hu huQ hC
  obtain ⟨hA, hVA⟩ := card_QA h34 hs hr
  by_contra hcon
  push Not at hcon
  have hWC : Wt Q (Vt M (LB M Q B) B Z t) ≤ C := fun w hw => (hC w).mpr ⟨hw, hcon w hw⟩
  have h1 : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ n ≤
      Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 4 := by
    calc Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ n
        ≤ Nat.card C * Nat.card Z ^ n := Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hWC)
      _ ≤ Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 4 := by
          rw [← hA, ← hVA]
          exact hle
  have h2 := Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  have hq2 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have := (Nat.pow_le_pow_iff_right hq2).mp h2
  omega

end Helpers

private theorem h91b_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) : Stroth91bStatement :=
  stroth91b_of_steps h34 h311a (sec9NComm_of_311b h34 h311bComm) (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)

theorem step94MovesW_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q →
        ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅u, w⁆ ∉ Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit hn5 u hu huQ
  obtain ⟨r, hr⟩ :=
    sec9AExists_of h34 h311a (sec9NComm_of_311b h34 h311bComm) G M Q Z B hc n t hs
  exact moves_mem h34 h311a (h91b_of h34 h311a h311bComm) hs hsplit hr hn5 hu huQ

theorem step94CYW_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) : Step94CYWStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit hn5 y hy hyW
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hYR : Y ≤ Rt M (LB M Q B) t := hsplit.1.2.2.2.1
  obtain ⟨u, hu, huQ⟩ :=
    HS9.exists_mem_LB_inf_Y_not_mem hc (sec4_of h34 h311a G M Q Z B hc n t hs X Y hsplit)
  obtain ⟨w₀, hw₀, huw₀⟩ :=
    step94MovesW_holds h34 h311a h311bComm G M Q Z B hc n t hs X Y hsplit hn5 u hu huQ
  obtain ⟨C, hC⟩ := exists_stab (hc.Rt_normalizes_Vt ht)
    (Wt Q (Vt M (LB M Q B) B Z t) : Set G)
  have hQC : Q ≤ C := fun q hq => (hC q).mpr ⟨hc.Q_le_Rt ht hq, fun w hw =>
    sec39_Z_le_Vt (hc.hyp.toHyp79.comm_mem_V hq
      ((inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hw))⟩
  have hCn : ∀ g ∈ Y, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc'
    obtain ⟨hcR, hcW⟩ := (hC c).mp hc'
    have hgR : g ∈ Rt M (LB M Q B) t := hYR hg
    refine (hC _).mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgR hcR)
      (Subgroup.inv_mem _ hgR), fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have := sec9_conj_mem_Wt hc ht (Subgroup.inv_mem _ hgR) hw
      simpa using this
    have e : ⁅g * c * g⁻¹, w⁆ = g * ⁅c, g⁻¹ * w * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hgR) _).mp (hcW _ hw')
  have huC : u ∉ C := fun h => huw₀ (((hC u).mp h).2 w₀ hw₀)
  exact inf_le_of_normal h34 h311a hs hsplit hQC hCn hu.2 huC
    ⟨(hC y).mpr ⟨hYR hy, hyW⟩, hy⟩

theorem step94DimQ_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) : Step94DimQStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs X Y hsplit u hu huQ
  obtain ⟨r, hr⟩ :=
    sec9AExists_of h34 h311a (sec9NComm_of_311b h34 h311bComm) G M Q Z B hc n t hs
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have huL : u ∈ LB M Q B := hu.1
  have huM : u ∈ M := hc.LB_le_M huL
  have huR : u ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht huL
  have huN : u ∉ hc.CN t := by
    intro h
    apply huQ
    rw [← hsplit.1.2.2.2.2.2.1]
    exact ⟨(sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1 h, hu.2⟩
  set V := Vt M (LB M Q B) B Z t with hVdef
  set W := Wt Q V with hWdef
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hVW : V ≤ W := HS6.Vt_le_Wt h34 hc hs5
  have huV : ∀ y ∈ V, u * y * u⁻¹ ∈ V := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht huR) y).mp hy
  have huW : ∀ y ∈ W, u * y * u⁻¹ ∈ W := fun y hy => sec9_conj_mem_Wt hc ht huR hy
  obtain ⟨C, hC⟩ := HS9.exists_subgroup_comm_mem_Vt91 hc hZV hVQ hWQ u
  have hCW : C ≤ W := fun y hy => ((hC y).mp hy).1
  have hVC : V ≤ C := fun v hv => (hC v).mpr ⟨hVW hv, by
    rw [commutatorElement_def]
    exact V.mul_mem (huV v hv) (V.inv_mem hv)⟩
  have hχ := stroth91c_of_34 h34 G M Q Z B hc n t hs (Rt M (LB M Q B) t) V W rfl rfl rfl
  obtain ⟨C₃, hWC₃, hC₃Q, hC₃iff, hC₃card⟩ := HS9.exists_chiTransport91 hc ht hχ huR
  have hfilt := card_Q1_mul_le_filtration hc huM hZV hVW hWQ huV huW hVC hCW
    (fun y hy => ⟨fun h => ((hC y).mp h).2, fun h => (hC y).mpr ⟨hy, h⟩⟩) hWC₃ hC₃Q hC₃iff
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, w, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have h3 : Nat.card ↥(V ⊓ Q1 hc u) = Nat.card Z ^ 3 :=
    HS9.card_Vt_inf_Q1_plus4_91 P ht huL huN
  have hCle := card_C_mul_le h34 h311a (h91b_of h34 h311a h311bComm) hs hsplit hr hu huQ hC
  obtain ⟨hA, hVA⟩ := card_QA h34 hs hr
  haveI : (Z.subgroupOf (Ut Q Z u)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q huM hv)))
  have hQ1U : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc u) * Nat.card ↥(Ut Q Z u) :=
    card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut huL) (fun y hy => hy.1)
      (le_sup_right : Z ≤ Ut Q Z u)
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs5.width
  have hVc : Nat.card V = Nat.card Z ^ 5 := hs.card_V
  have hWc : Nat.card W = Nat.card Z ^ (2 * n - 3) := hs.card_W h34
  have hn3 : 2 < n := hs5.n_gt
  have hq : 0 < Nat.card Z := Nat.card_pos
  have step1 : Nat.card ↥(Q1 hc u) ≤ Nat.card C := by
    have hpos : 0 < Nat.card Z ^ 6 * Nat.card W := Nat.mul_pos (pow_pos hq 6) Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ↥(Q1 hc u) * (Nat.card Z ^ 6 * Nat.card W)
        = Nat.card ↥(Q1 hc u) * Nat.card V * Nat.card W * Nat.card Z := by rw [hVc]; ring
      _ ≤ Nat.card ↥(V ⊓ Q1 hc u) * Nat.card C * Nat.card C₃ * Nat.card Z :=
          Nat.mul_le_mul_right _ hfilt
      _ = Nat.card C * (Nat.card Z ^ 6 * Nat.card W) := by
          rw [mul_assoc _ (Nat.card C₃), hC₃card, h3]; ring
  have step2 : Nat.card C ≤ Nat.card Z ^ (n + 1) := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card Z ^ n) ?_ (pow_pos hq n)
    calc Nat.card C * Nat.card Z ^ n ≤ Nat.card W * Nat.card Z ^ 4 := by
          rw [← hA, ← hVA]; exact hCle
      _ = Nat.card Z ^ (n + 1) * Nat.card Z ^ n := by
          rw [hWc, ← pow_add, ← pow_add]
          congr 1
          omega
  have step3 : Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1) ≤
      Nat.card Z ^ (n + 1) * Nat.card ↥(Ut Q Z u) := by
    calc Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1) = Nat.card Q * Nat.card Z := by
          rw [hQc]; ring
      _ = Nat.card ↥(Q1 hc u) * Nat.card ↥(Ut Q Z u) := hQ1U
      _ ≤ Nat.card Z ^ (n + 1) * Nat.card ↥(Ut Q Z u) :=
          Nat.mul_le_mul_right _ (step1.trans step2)
  exact Nat.le_of_mul_le_mul_left step3 (pow_pos hq (n + 1))

end CFSG.RankThree.GF2n.Stroth80
