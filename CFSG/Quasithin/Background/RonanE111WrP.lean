module

public import CFSG.Quasithin.Background.RonanE111LiftP
public import CFSG.Quasithin.Background.RonanE111WrP4

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X T A J C : Subgroup G} [Fintype ↥C]

theorem pg_le_normalizer {R YR : Subgroup G}
    (hYRn : ∀ r ∈ R, ∀ y ∈ YR, r * y * r⁻¹ ∈ YR) :
    R ≤ Subgroup.normalizer (YR : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hYRn r hr y
  · intro hy
    have h1 := hYRn r⁻¹ (R.inv_mem hr) _ hy
    rwa [show r⁻¹ * (r * y * r⁻¹) * r⁻¹⁻¹ = y by group] at h1

theorem pg_conjSub_A {k : G} (hk : k ∈ actT T A) : A1b.conjSub k A = A :=
  E111R.conjSub_eq_of_mem_normalizer
    (Subgroup.centralizer_le_normalizer _ (mem_actT_iff.mp hk).2)

theorem pg_A_le_actT (h : DiagSetting X T A J C) : A ≤ actT T A := fun a ha =>
  ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm hb ha⟩

theorem pg_actT_le_T : actT T A ≤ T := fun g hg => (mem_actT_iff.mp hg).1

theorem pg_actT_le_normalizer_wrN (h : DiagSetting X T A J C) {R : Subgroup G} :
    actT T A ≤ Subgroup.normalizer (wrN h.diagComm T A R : Set G) := by
  intro g hg
  rw [wrN_eq]
  exact wr_mem_normalizer hg

theorem pg_actT_le_normalizer_wrY (h : DiagSetting X T A J C) {YR : Subgroup G} :
    actT T A ≤ Subgroup.normalizer (wrY h.diagComm T A YR : Set G) := by
  intro g hg
  rw [wrY_eq]
  exact wr_mem_normalizer hg

theorem pg_conjSub_le_of_le {k : G} (hk : k ∈ T) {S : Subgroup G} (hS : S ≤ T) :
    A1b.conjSub k S ≤ T := by
  intro x hx
  rw [A1b.mem_conjSub_iff] at hx
  have h1 := T.mul_mem (T.mul_mem hk (hS hx)) (T.inv_mem hk)
  rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h1

theorem pg_dimg_le_T (h : DiagSetting X T A J C) {U : Subgroup G} (hUT : U ≤ T) :
    dimg h.diagComm U ≤ T := by
  intro d hd
  obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hd
  refine diagHom_mem_of h.diagComm u ?_
  intro c hc
  exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) (hUT hu)) (T.inv_mem (h.AT (h.CA hc)))

theorem pg_wrY_le_T (h : DiagSetting X T A J C) {YR : Subgroup G} (hYT : YR ≤ T) :
    wrY h.diagComm T A YR ≤ T := by
  have hle : (⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm YR)) ≤ T :=
    iSup₂_le fun k hk => pg_conjSub_le_of_le (mem_actT_iff.mp hk).1 (pg_dimg_le_T h hYT)
  exact hle

theorem pg_wrN_le_normalizer_wrY (h : DiagSetting X T A J C) {R YR : Subgroup G}
    (hRJ : R ≤ J) (hYJ : YR ≤ J) (hRN : R ≤ Subgroup.normalizer (YR : Set G))
    (hYE : ∀ e ∈ actE T A J, A1b.conjSub e YR = YR) :
    wrN h.diagComm T A R ≤ Subgroup.normalizer (wrY h.diagComm T A YR : Set G) := by
  have hle : (⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm R)) ≤
      Subgroup.normalizer (wrY h.diagComm T A YR : Set G) :=
    iSup₂_le fun k hk => wr_conj_dimg_le_normalizer h le_rfl hRJ hYJ hRN hYE hk
  exact hle

theorem pg_dimg_le_of_gen (h : DiagSetting X T A J C) {R YR N W : Subgroup G} (hRJ : R ≤ J)
    (hYR : YR ≤ R) (hgen : R ≤ ⁅R, A ⊓ Subgroup.normalizer (J : Set G)⁆ ⊔ YR)
    (hN : dimg h.diagComm R ≤ N) (hYW : dimg h.diagComm YR ≤ W)
    (hcommW : ∀ x ∈ N, ∀ v ∈ A, ⁅x, v⁆ ∈ W) : dimg h.diagComm R ≤ W := by
  have hYJ : YR ≤ J := hYR.trans hRJ
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, ∀ x : G,
      x ∈ M ↔ ∃ u : ↥J, diagHom J C h.diagComm u ∈ W ∧ (u : G) = x := by
    refine ⟨(W.comap (diagHom J C h.diagComm)).map J.subtype, fun x => ?_⟩
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hcomm_part : ⁅R, A ⊓ Subgroup.normalizer (J : Set G)⁆ ≤ M := by
    refine Subgroup.commutator_le.mpr fun r hr v hv => ?_
    obtain ⟨hvA, hvN⟩ := Subgroup.mem_inf.mp hv
    have hrJ : r ∈ J := hRJ hr
    have hvC : ∀ c ∈ C, v * c = c * v := fun c hc => h.comm hvA (h.CA hc)
    have hwJ : v * r⁻¹ * v⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp hvN r⁻¹).mp (J.inv_mem hrJ)
    have hcJ : ⁅r, v⁆ ∈ J := by
      rw [commutatorElement_def, show r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) by group]
      exact J.mul_mem hrJ hwJ
    have hu : (⟨⁅r, v⁆, hcJ⟩ : ↥J) = ⟨r, hrJ⟩ * ⟨v * r⁻¹ * v⁻¹, hwJ⟩ := by
      apply Subtype.ext
      show ⁅r, v⁆ = r * (v * r⁻¹ * v⁻¹)
      rw [commutatorElement_def]
      group
    have hw : diagHom J C h.diagComm ⟨v * r⁻¹ * v⁻¹, hwJ⟩ =
        v * (diagHom J C h.diagComm ⟨r, hrJ⟩)⁻¹ * v⁻¹ := by
      have e := conj_diagHom_of_comm h.diagComm (⟨r, hrJ⟩⁻¹ : ↥J) hvN hvC
      rw [map_inv] at e
      exact e.symm
    have hdelta : diagHom J C h.diagComm ⟨⁅r, v⁆, hcJ⟩ =
        ⁅diagHom J C h.diagComm ⟨r, hrJ⟩, v⁆ := by
      rw [hu, map_mul, hw, commutatorElement_def]
      group
    refine (hM _).mpr ⟨⟨⁅r, v⁆, hcJ⟩, ?_, rfl⟩
    rw [hdelta]
    exact hcommW _ (hN ((mem_dimg_iff h.diagComm).mpr ⟨⟨r, hrJ⟩, hr, rfl⟩)) v hvA
  have hYM : YR ≤ M := by
    intro y hy
    have hyJ : y ∈ J := hYJ hy
    refine (hM y).mpr ⟨⟨y, hyJ⟩, ?_, rfl⟩
    exact hYW ((mem_dimg_iff h.diagComm).mpr ⟨⟨y, hyJ⟩, hy, rfl⟩)
  have hRM : R ≤ M := hgen.trans (sup_le hcomm_part hYM)
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
  obtain ⟨w, hwW, hwu⟩ := (hM _).mp (hRM hu)
  rw [show w = u from Subtype.ext hwu] at hwW
  exact hwW

theorem pg_wrN_le_comm_sup (h : DiagSetting X T A J C) {R YR : Subgroup G} (hRJ : R ≤ J)
    (hYR : YR ≤ R) (hgen : R ≤ ⁅R, A ⊓ Subgroup.normalizer (J : Set G)⁆ ⊔ YR) :
    wrN h.diagComm T A R ≤ ⁅wrN h.diagComm T A R, A⁆ ⊔ wrY h.diagComm T A YR := by
  have hdim : dimg h.diagComm R ≤ ⁅wrN h.diagComm T A R, A⁆ ⊔ wrY h.diagComm T A YR :=
    pg_dimg_le_of_gen h hRJ hYR hgen (wr_dimg_le_wrN h)
      (le_sup_of_le_right (wr_dimg_le_wrY h))
      (fun x hx v hv => Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hv))
  have hle : (⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm R)) ≤
      ⁅wrN h.diagComm T A R, A⁆ ⊔ wrY h.diagComm T A YR := by
    refine iSup₂_le fun k hk => ?_
    have hW : A1b.conjSub k (⁅wrN h.diagComm T A R, A⁆ ⊔ wrY h.diagComm T A YR) =
        ⁅wrN h.diagComm T A R, A⁆ ⊔ wrY h.diagComm T A YR := by
      rw [wr_conjSub_sup, wr_conjSub_commutator, wr_conjSub_wrN h hk, wr_conjSub_wrY h hk,
        pg_conjSub_A hk]
    exact (A1b.conjSub_mono k hdim).trans hW.le
  exact hle

theorem pg_odd_index {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N Q : Subgroup G}
    [(Q.subgroupOf N).Normal] (hpg : ∀ x ∈ N, ∃ m : ℕ, x ^ p ^ m ∈ Q) :
    ¬ 2 ∣ (Q.subgroupOf N).index := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : IsPGroup p (↥N ⧸ Q.subgroupOf N) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf N) g
    obtain ⟨m, hm⟩ := hpg (x : G) x.2
    refine ⟨m, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_pow]; exact hm)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hq
  have hidx : (Q.subgroupOf N).index = p ^ k := hk
  rw [hidx]
  intro h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem pg_isSylowIn_of_odd_index {P Q N : Subgroup G} (hPN : P ≤ N) (hP2 : IsPGroup 2 P)
    (hQP : Q ≤ P) (hodd : ¬ 2 ∣ (Q.subgroupOf N).index) : IsSylowIn 2 P N := by
  refine ⟨hPN, hP2, fun h2 => hodd (h2.trans ?_)⟩
  exact Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono N hQP)

theorem pg_sylow_sup (h : DiagSetting X T A J C) {R : Subgroup G} (hT2 : IsPGroup 2 T)
    (hSylN : IsSylowIn 2 (T ⊓ wrN h.diagComm T A R) (wrN h.diagComm T A R)) :
    IsSylowIn 2 (T ⊓ (wrN h.diagComm T A R ⊔ actT T A)) (wrN h.diagComm T A R ⊔ actT T A) := by
  have hNH : wrN h.diagComm T A R ≤ wrN h.diagComm T A R ⊔ actT T A := le_sup_left
  have hHN : wrN h.diagComm T A R ⊔ actT T A ≤
      Subgroup.normalizer ((wrN h.diagComm T A R : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (pg_actT_le_normalizer_wrN h)
  have hT0T : actT T A ≤ T := fun g hg => (mem_actT_iff.mp hg).1
  have hsup : (T ⊓ (wrN h.diagComm T A R ⊔ actT T A)) ⊔ wrN h.diagComm T A R =
      wrN h.diagComm T A R ⊔ actT T A := by
    apply le_antisymm
    · exact sup_le inf_le_right le_sup_left
    · refine sup_le le_sup_right (fun g hg => ?_)
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hT0T hg, Subgroup.mem_sup_right hg⟩)
  have hSyl : IsSylowIn 2 ((T ⊓ (wrN h.diagComm T A R ⊔ actT T A)) ⊓ wrN h.diagComm T A R)
      (wrN h.diagComm T A R) := by
    have e : (T ⊓ (wrN h.diagComm T A R ⊔ actT T A)) ⊓ wrN h.diagComm T A R =
        T ⊓ wrN h.diagComm T A R := by
      exact le_antisymm (inf_le_inf_right _ inf_le_left)
        (le_inf (le_inf inf_le_left (inf_le_right.trans le_sup_left)) inf_le_right)
    rw [e]
    exact hSylN
  exact wr_sylow_of_normal_sup hNH inf_le_right hHN hsup (hT2.to_le inf_le_left) hSyl

theorem pgroup_diag_cover {n : ℕ} (hn : 1 ≤ n) (h : DiagSetting X T A J C) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {R YR : Subgroup G} (hRJ : R ≤ J) (hYR : YR ≤ R)
    (hYRn : ∀ r ∈ R, ∀ y ∈ YR, r * y * r⁻¹ ∈ YR) (hYT : YR ≤ T)
    (hRE : ∀ e ∈ actE T A J, A1b.conjSub e R = R)
    (hYE : ∀ e ∈ actE T A J, A1b.conjSub e YR = YR)
    (hpq : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ YR)
    (hgen : R ≤ ⁅R, A ⊓ Subgroup.normalizer (J : Set G)⁆ ⊔ YR) :
    dimg h.diagComm R ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K := by
  have hYJ : YR ≤ J := hYR.trans hRJ
  have hRN : R ≤ Subgroup.normalizer (YR : Set G) := pg_le_normalizer hYRn
  have hNY : wrN h.diagComm T A R ≤ Subgroup.normalizer (wrY h.diagComm T A YR : Set G) :=
    pg_wrN_le_normalizer_wrY h hRJ hYJ hRN hYE
  have hYN : wrY h.diagComm T A YR ≤ wrN h.diagComm T A R := wr_wrY_le_wrN h hYR
  have hYT' : wrY h.diagComm T A YR ≤ T := pg_wrY_le_T h hYT
  have hpg := wrP_pgroup h hRJ hRE hpq
  have hgen' := pg_wrN_le_comm_sup h hRJ hYR hgen
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hYn : ((wrY h.diagComm T A YR).subgroupOf (wrN h.diagComm T A R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYN).mpr hNY
  haveI := hYn
  have hodd := pg_odd_index hp hp2 hpg
  have hSylN : IsSylowIn 2 (T ⊓ wrN h.diagComm T A R) (wrN h.diagComm T A R) :=
    pg_isSylowIn_of_odd_index inf_le_right (hT2.to_le inf_le_left) (le_inf hYT' hYN) hodd
  have hSylH := pg_sylow_sup h hT2 hSylN
  have hτ : E1.tauOf ⊤ T A ≤ actT T A :=
    E111R.tauOf_le (E111R.pCoreOf_two_eq_bot h.red) T A
  have hLift := lift_pgroup_sub hp hp2 (T₀ := actT T A) (N := wrN h.diagComm T A R)
    (Y := wrY h.diagComm T A YR) (A := A) hT pg_actT_le_T (pg_A_le_actT h) h.elem
    (pg_actT_le_normalizer_wrN h) (pg_actT_le_normalizer_wrY h) hNY hYN hpg hgen' hSylH hτ
  have hmono : (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K}, K) ≤
      ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K :=
    iSup₂_le fun K hK =>
      le_iSup₂_of_le K (E1.IsE.mono hn (show E1.IsE 1 ⊤ T A K from hK)) le_rfl
  calc dimg h.diagComm R ≤ wrN h.diagComm T A R := wr_dimg_le_wrN h
    _ ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K}, K) ⊔ wrY h.diagComm T A YR := hLift
    _ ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) ⊔ T := sup_le_sup hmono hYT'
    _ = T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K := sup_comm _ _

end CFSG.Quasithin.RonanE111
