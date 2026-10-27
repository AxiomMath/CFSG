module

public import CFSG.Quasithin.Background.OperatorJordanHolderJH1
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316C1
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316O2

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat CFSG.Quasithin.OperatorJH
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL uSL_mul uSL_inv uSL_zero
  uSL_injective)
open scoped MatrixGroups Matrix Pointwise commutatorElement

namespace L4316

section Series

variable {G : Type} [Group G] {Y K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F]
  {α₀ : ↥K →* ↥(StatedSL n F)}

theorem exists_isLabSeries_central [Finite G] {C S : Subgroup G} (hCS : C ≤ S)
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hYC : Y ≤ Subgroup.normalizer (C : Set G))
    (hYS : Y ≤ Subgroup.normalizer (S : Set G))
    (hK : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ C) :
    ∃ l : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l S ∧ ∀ q ∈ l, q.2 = none := by
  obtain ⟨t, ht⟩ := exists_ySeries (Y := Y) _ rfl hCS hSC hYC hYS
  clear hCS hSC hYS
  induction t generalizing S with
  | nil => exact ⟨[], ht, fun q hq => by simp at hq⟩
  | cons S' t ih =>
    obtain ⟨hS', ht'⟩ := ht
    obtain ⟨l, hl, hln⟩ := ih (S := S') (fun k hk s hs => hK k hk s (hS'.1.le hs)) ht'
    have hf : IsLabFactor Y K x α₀ S' S none :=
      ⟨hS'.1, hS'.2.1, hS'.2.2.1, hS'.2.2.2.1, hS'.2.2.2.2,
        fun k hk s hs => IsYSeries.le ht' (hK k hk s hs)⟩
    refine ⟨l ++ [(S, none)], hl.append (isLabSeries_singleton hf), fun q hq => ?_⟩
    rcases List.mem_append.mp hq with h | h
    · exact hln q h
    · rw [List.mem_singleton] at h
      rw [h]

theorem isLabFactor_of_natEig {C S : Subgroup G} {a : F} (h : IsNatEigSection K x α₀ C S a)
    (hCS : C < S) (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) (hYS : Y ≤ Subgroup.normalizer (S : Set G))
    (hKY : K ≤ Y) (hn : 2 ≤ n) (hα : Function.Surjective α₀) :
    IsLabFactor Y K x α₀ C S (some a) :=
  ⟨hCS, hSC, hYC, hYS, fun _ hCJ hJS _ hYJ =>
    h.eq_or_eq hn hα (hKY.trans hYS) hCJ hJS (hKY.trans hYJ), h⟩

theorem IsLabSeries.exists_toK [Finite G] {C D : Subgroup G}
    {l : List (Subgroup G × Option F)} (hl : IsLabSeries Y K x α₀ C l D) (hKY : K ≤ Y)
    (hn : 2 ≤ n) (hα : Function.Surjective α₀) :
    ∃ l' : List (Subgroup G × Option F), IsLabSeries K K 1 α₀ C l' D := by
  induction l generalizing C with
  | nil => exact ⟨[], hl⟩
  | cons p l ih =>
    obtain ⟨hf, hr⟩ := hl
    obtain ⟨l'', hl''⟩ := ih hr
    obtain ⟨S, e⟩ := p
    obtain ⟨hCS, hSC, hYC, hYS, -, he⟩ := hf
    cases e with
    | none =>
      obtain ⟨l₀, hl₀, -⟩ := exists_isLabSeries_central (Y := K) (x := 1) (α₀ := α₀) hCS.le hSC
        (hKY.trans hYC) (hKY.trans hYS) he
      exact ⟨l₀ ++ l'', hl₀.append hl''⟩
    | some a =>
      have h1 : IsNatEigSection K 1 α₀ C S 1 := by
        obtain ⟨β, hβs, hβk, hβK, -⟩ := he
        refine ⟨β, hβs, hβk, hβK, fun c c' hc => ?_⟩
        have : c' = c := Subtype.ext (by rw [hc]; group)
        rw [this, one_smul]
      exact ⟨(S, some 1) :: l'', isLabFactor_of_natEig h1 hCS hSC (hKY.trans hYC)
        (hKY.trans hYS) le_rfl hn hα, hl''⟩

theorem IsLabSeries.exists_factor {C₁ C₂ : Subgroup G} {l : List (Subgroup G × Option F)}
    (hl : IsLabSeries Y K x α₀ C₁ l C₂) (hlt : C₁ < C₂)
    (hirr : ∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → Y ≤ Subgroup.normalizer (J : Set G) →
      J = C₁ ∨ J = C₂) : ∃ e, IsLabFactor Y K x α₀ C₁ C₂ e := by
  cases l with
  | nil => exact absurd (hl : C₁ = C₂) hlt.ne
  | cons p l =>
    obtain ⟨hf, hr⟩ := hl
    have hp : p.1 = C₂ := by
      rcases hirr p.1 hf.1.le hr.le hf.2.2.2.1 with h | h
      · exact absurd h.symm hf.1.ne
      · exact h
    exact ⟨p.2, hp ▸ hf⟩

omit [Field F] in
theorem u4311_comm {I K : Subgroup G} {a b : G} (ha : a ∈ u4311 I K) (hb : b ∈ u4311 I K) :
    a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp hb.2 a ha.1

omit [Field F] in
theorem forall_eq_none_of_labMultiset_eq_zero {l : List (Subgroup G × Option F)}
    (h : labMultiset l = 0) : ∀ q ∈ l, q.2 = none := by
  induction l with
  | nil => intro q hq; simp at hq
  | cons p l ih =>
    rw [labMultiset_cons] at h
    have h1 : (p.2.elim 0 fun a => {a} : Multiset F) = 0 := (add_eq_zero.mp h).1
    have h2 := (add_eq_zero.mp h).2
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨S, e⟩ := q
      cases e with
      | none => rfl
      | some a => simp at h1
    · exact ih h2 q hq

end Series

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}

@[expose] noncomputable def leviS (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ) :
    ↥K₂ →* ↥(StatedSL 2 F) :=
  (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp s.levi

variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem leviS_surjective : Function.Surjective s.leviS :=
  (specialLinearGroupEquivStatedSL 2 F).surjective.comp s.levi_surjective

theorem leviS_ker : s.leviS.ker = (pCoreOf 2 K₂).subgroupOf K₂ := by
  ext k
  rw [MonoidHom.mem_ker, leviS, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, s.ker_levi, Subgroup.mem_subgroupOf,
    mem_pCoreOf_iff']

theorem coe_α_zpow_y (hm : m = 2) (j : ℤ) (hj : y ^ j ∈ K) :
    (((α ⟨y ^ j, hj⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) (((μ ^ j : Fˣ)) : F) := by
  have hμ3 : μ ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, s.μ_order, hm]
    norm_num
  have e : (⟨y ^ j, hj⟩ : ↥K) = (⟨y, s.y_mem⟩ : ↥K) ^ j := rfl
  rw [e, map_zpow, s.α_y, ← map_zpow, ← map_zpow]
  change ((SL3Pt.tor (μ ^ j) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [SL3Pt.coe_tor, SL3Pt.torMat]
  have hν3 : (μ ^ j) ^ 3 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hμ3, one_zpow]
  have hν : ((μ ^ j)⁻¹ : Fˣ) ^ 2 = μ ^ j := by
    calc ((μ ^ j)⁻¹ : Fˣ) ^ 2 = ((μ ^ j)⁻¹) ^ 2 * (μ ^ j) ^ 3 := by rw [hν3, mul_one]
      _ = μ ^ j := by group
  rw [← Units.val_pow_eq_pow_val, hν]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem natEig_U (hm : m = 2) (j : ℤ) :
    IsNatEigSection K₂ (y ^ j) s.leviS ZS (u4311 I K) (((μ ^ j : Fˣ)) : F) := by
  classical
  let p : (Fin 3 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => ![v 1, v 2]
      map_zero' := by ext i; fin_cases i <;> rfl
      map_add' := fun v w => by ext i; fin_cases i <;> rfl }
  refine ⟨(AddMonoidHom.toMultiplicative p).comp β, fun w => ?_, fun u => ?_, fun k u u' hu => ?_,
    fun u u' hu => ?_⟩
  · obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd ![0, w 0, w 1])
    refine ⟨u, ?_⟩
    rw [MonoidHom.comp_apply, hu]
    ext i
    fin_cases i <;> rfl
  · rw [s.ZS_iff]
    change Multiplicative.ofAdd (p (Multiplicative.toAdd (β u))) = 1 ↔ _
    constructor
    · intro h
      have h1 := congrArg (fun w : Multiplicative (Fin 2 → F) => Multiplicative.toAdd w 0) h
      have h2 := congrArg (fun w : Multiplicative (Fin 2 → F) => Multiplicative.toAdd w 1) h
      simp only [toAdd_ofAdd, toAdd_one, Pi.zero_apply] at h1 h2
      refine ⟨Multiplicative.toAdd (β u) 0, ?_⟩
      ext i
      fin_cases i
      · simp
      · simpa [p] using h1
      · simpa [p] using h2
    · rintro ⟨c, hc⟩
      rw [hc]
      ext i
      fin_cases i <;> simp [p]
  · have hkK := s.K₂_le_K k.2
    have h1 := s.β_act ⟨k, hkK⟩ u u' hu
    obtain ⟨h00, h10, h20⟩ := s.α_entries k.2
    have hlev := s.levi_coe k
    change Multiplicative.toAdd (Multiplicative.ofAdd (p (Multiplicative.toAdd (β u')))) =
      ((Matrix.SpecialLinearGroup.toGL (s.levi k) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (Multiplicative.ofAdd (p (Multiplicative.toAdd (β u))))
    rw [toAdd_ofAdd, toAdd_ofAdd, h1, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hlev]
    ext i
    fin_cases i <;>
      simp [p, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, lev, h10, h20]
  · have hjK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
    have h1 := s.β_act ⟨y ^ j, hjK⟩ u u' hu
    change Multiplicative.toAdd (Multiplicative.ofAdd (p (Multiplicative.toAdd (β u')))) =
      ((μ ^ j : Fˣ) : F) •
        Multiplicative.toAdd (Multiplicative.ofAdd (p (Multiplicative.toAdd (β u))))
    rw [toAdd_ofAdd, toAdd_ofAdd, h1, s.coe_α_zpow_y hm j hjK]
    ext i
    fin_cases i <;> simp [p, Matrix.scalar_apply]

theorem ZS_lt_U : ZS < u4311 I K := by
  refine lt_of_le_of_ne s.ZS_le_U fun h => ?_
  obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd ![0, 1, 0])
  have h1 : (u : G) ∈ ZS := h ▸ u.2
  obtain ⟨c, hc⟩ := (s.ZS_iff u).mp h1
  rw [hu, toAdd_ofAdd] at hc
  have := congrFun hc 1
  simp at this

theorem isLabFactor_U (hm : m = 2) (j : ℤ) :
    IsLabFactor (K₂ ⊔ Subgroup.zpowers y) K₂ (y ^ j) s.leviS ZS (u4311 I K)
      (some ((μ ^ j : Fˣ) : F)) := by
  have hXK : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr s.y_mem
  refine L4316.isLabFactor_of_natEig (s.natEig_U hm j) s.ZS_lt_U ?_ ?_ ?_ le_sup_left le_rfl
    s.leviS_surjective
  · intro u hu
    refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun z hz => ?_
    rw [L4316.u4311_comm hu (s.ZS_le_U hz), mul_inv_cancel_right]
    exact hz
  · exact _root_.sup_le (s.K₂_le_KZ.trans s.KZ_cent |>.trans
      (Subgroup.centralizer_le_normalizer _)) s.Y_le_normalizer_ZS
  · exact _root_.sup_le (s.K₂_le_K.trans s.K_U) (hXK.trans s.K_U)

theorem le_normalizer_U :
    K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) :=
  _root_.sup_le (s.K₂_le_K.trans s.K_U) ((Subgroup.zpowers_le.mpr s.y_mem).trans s.K_U)

theorem pCoreOf_KZ_le_normalizer_U :
    pCoreOf 2 KZ ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) :=
  s.pCoreOf_KZ_le.trans (s.R₂_le_K.trans s.K_U)

theorem exists_K₂_U_e1 :
    ∃ c : G, ∃ hc : c ∈ u4311 I K, c ∈ K₂ ∧ Multiplicative.toAdd (β ⟨c, hc⟩) = ![0, 1, 0] := by
  classical
  let A : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hB : specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL A) ∈ stE0 F :=
    ⟨_, SL3Pt.blkSL_mem_stabE0 A, rfl⟩
  obtain ⟨k, hk, hαk⟩ := s.exists_K₂_of_mem_stE0 hB
  have hkK := s.K₂_le_K hk
  obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd ![0, 0, 1])
  have huU : (u : G) ∈ u4311 I K := u.2
  have huK : (u : G) ∈ K := s.q4311_le_K huU.1
  have huC : (u : G) ∈ Subgroup.centralizer (ZS : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subgroup.mem_centralizer_iff.mp huU.2 z (s.ZS_le_U hz).1
  have huN : (u : G) ∈ Subgroup.normalizer (K₂ : Set G) := by
    rw [s.K₂_eq]
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer ⟨huK, huC⟩)
  have hkuU : k * u * k⁻¹ ∈ u4311 I K := (Subgroup.mem_normalizer_iff.mp (s.K_U hkK) u).mp huU
  have hc : k * u * k⁻¹ * (u : G)⁻¹ ∈ u4311 I K :=
    (u4311 I K).mul_mem hkuU ((u4311 I K).inv_mem huU)
  refine ⟨k * u * k⁻¹ * (u : G)⁻¹, hc, ?_, ?_⟩
  · have h1 : (u : G) * k⁻¹ * (u : G)⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp huN k⁻¹).mp (K₂.inv_mem hk)
    have e : k * u * k⁻¹ * (u : G)⁻¹ = k * ((u : G) * k⁻¹ * (u : G)⁻¹) := by group
    rw [e]
    exact K₂.mul_mem hk h1
  · have h2 := s.β_act ⟨k, hkK⟩ u ⟨_, hkuU⟩ rfl
    rw [hαk, specialLinearGroupEquivStatedSL_coe, hu, toAdd_ofAdd] at h2
    have e : (⟨k * u * k⁻¹ * (u : G)⁻¹, hc⟩ : ↥(u4311 I K)) = ⟨_, hkuU⟩ * u⁻¹ := rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, h2, hu, toAdd_ofAdd]
    ext i
    fin_cases i <;> simp [SL3Pt.blkSL, SL3Pt.blk, A]

theorem U_le_K₂ : u4311 I K ≤ K₂ := by
  classical
  obtain ⟨c, hcU, hcK₂, hcβ⟩ := s.exists_K₂_U_e1
  have key : ∀ v : ↥(u4311 I K), (Multiplicative.toAdd (β v) 1 ≠ 0 ∨
      Multiplicative.toAdd (β v) 2 ≠ 0) → (v : G) ∈ K₂ := by
    intro v hv
    obtain ⟨B, hB, hBv⟩ := SL3Pt.stabE0_trans (v := ![0, 1, 0]) (Or.inl (by simp)) hv
    obtain ⟨k, hk, hkα⟩ := s.exists_K₂_of_mem_stE0
      (⟨B, hB, rfl⟩ : specialLinearGroupEquivStatedSL 3 F B ∈ stE0 F)
    have hkK := s.K₂_le_K hk
    have hkcU : k * c * k⁻¹ ∈ u4311 I K := (Subgroup.mem_normalizer_iff.mp (s.K_U hkK) c).mp hcU
    have h1 := s.β_act ⟨k, hkK⟩ ⟨c, hcU⟩ ⟨_, hkcU⟩ rfl
    rw [hkα, specialLinearGroupEquivStatedSL_coe, hcβ, hBv] at h1
    have h2 : (⟨_, hkcU⟩ : ↥(u4311 I K)) = v := s.β_bij.1 (Multiplicative.toAdd.injective h1)
    have h3 : k * c * k⁻¹ = v := congrArg Subtype.val h2
    rw [← h3]
    exact K₂.mul_mem (K₂.mul_mem hk hcK₂) (K₂.inv_mem hk)
  intro v hv
  by_cases hv' : Multiplicative.toAdd (β ⟨v, hv⟩) 1 ≠ 0 ∨ Multiplicative.toAdd (β ⟨v, hv⟩) 2 ≠ 0
  · exact key ⟨v, hv⟩ hv'
  · push Not at hv'
    have hvc : (⟨v, hv⟩ * ⟨c, hcU⟩ : ↥(u4311 I K)) = ⟨v * c, (u4311 I K).mul_mem hv hcU⟩ := rfl
    have h1 : ((⟨v, hv⟩ * ⟨c, hcU⟩ : ↥(u4311 I K)) : G) ∈ K₂ := by
      refine key _ (Or.inl ?_)
      rw [map_mul, toAdd_mul, hcβ, Pi.add_apply, hv'.1]
      simp
    have e : v = v * c * c⁻¹ := by group
    rw [e]
    exact K₂.mul_mem h1 (K₂.inv_mem hcK₂)

theorem U_le_pCoreOf_K₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : u4311 I K ≤ pCoreOf 2 K₂ :=
  fun _ hu => s.R₂_inf_K₂_le ⟨s.q4311_le_R₂ h135 hR hC h37 h38 h39 hu.1, s.U_le_K₂ hu⟩

theorem α_eq_uSL {r : G} (hr : r ∈ R₂) :
    α ⟨r, s.R₂_le_K hr⟩ = specialLinearGroupEquivStatedSL 3 F
      (uSL ((((α ⟨r, s.R₂_le_K hr⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1)
        ((((α ⟨r, s.R₂_le_K hr⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 2) 0) := by
  obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hr)
  conv_rhs => rw [hab]
  rw [specialLinearGroupEquivStatedSL_coe, coe_uSL]
  simp [uMat, hab]

theorem commutator_U_le_ZS : ⁅u4311 I K, pCoreOf 2 K₂⁆ ≤ ZS := by
  rw [Subgroup.commutator_le]
  intro u hu r hr
  have hrR : r ∈ R₂ := s.pCoreOf_K₂_le_R₂ hr
  have hrK := s.R₂_le_K hrR
  have hru : r * u⁻¹ * r⁻¹ ∈ u4311 I K :=
    (Subgroup.mem_normalizer_iff.mp (s.K_U hrK) _).mp ((u4311 I K).inv_mem hu)
  have hmem : ⁅u, r⁆ ∈ u4311 I K := by
    rw [commutatorElement_def, mul_assoc u r, mul_assoc u]
    exact (u4311 I K).mul_mem hu (by simpa [mul_assoc] using hru)
  have e : (⟨⁅u, r⁆, hmem⟩ : ↥(u4311 I K)) = ⟨u, hu⟩ * ⟨r * u⁻¹ * r⁻¹, hru⟩ :=
    Subtype.ext (by simp [commutatorElement_def, mul_assoc])
  have h1 := s.β_act ⟨r, hrK⟩ ⟨u, hu⟩⁻¹ ⟨_, hru⟩ rfl
  rw [s.α_eq_uSL hrR, specialLinearGroupEquivStatedSL_coe, coe_uSL] at h1
  refine (s.ZS_iff ⟨_, hmem⟩).mpr ⟨-(((((α ⟨r, hrK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) 0 1) * Multiplicative.toAdd (β ⟨u, hu⟩) 1 +
      ((((α ⟨r, hrK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) *
        Multiplicative.toAdd (β ⟨u, hu⟩) 2), ?_⟩
  rw [e, map_mul, toAdd_mul, h1, map_inv, toAdd_inv]
  ext i
  fin_cases i
  · simp [uMat, dotProduct, Fin.sum_univ_three]
    ring
  · simp [uMat, dotProduct, Fin.sum_univ_three]
  · simp [uMat, dotProduct, Fin.sum_univ_three]

omit [Finite G] [Fintype F] s in
theorem mul_uMat {B : Matrix (Fin 3) (Fin 3) F} (h00 : B 0 0 = 1) (h10 : B 1 0 = 0)
    (h20 : B 2 0 = 0) (hdet : B 1 1 * B 2 2 - B 1 2 * B 2 1 = 1) (a b : F) :
    B * uMat a b 0 = uMat (a * B 2 2 - b * B 2 1) (-(a * B 1 2) + b * B 1 1) 0 * B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20]
  · linear_combination (-a) * hdet
  · linear_combination (-b) * hdet

@[expose] noncomputable def radM (r : ↥R₂) : Matrix (Fin 3) (Fin 3) F :=
  (((α ⟨r, s.R₂_le_K r.2⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem radM_eq (r : ↥R₂) : s.radM r = uMat (s.radM r 0 1) (s.radM r 0 2) 0 := by
  have h := s.α_eq_uSL r.2
  have h1 := congrArg (fun x : ↥(StatedSL 3 F) =>
    ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [specialLinearGroupEquivStatedSL_coe, coe_uSL] at h1
  exact h1

theorem radM_mul (r r' : ↥R₂) : s.radM (r * r') = s.radM r * s.radM r' := by
  have e : (⟨((r * r' : ↥R₂) : G), s.R₂_le_K (r * r').2⟩ : ↥K) =
      ⟨r, s.R₂_le_K r.2⟩ * ⟨r', s.R₂_le_K r'.2⟩ := rfl
  rw [radM, radM, radM, e, map_mul]
  rfl

theorem radM_mul_entries (r r' : ↥R₂) :
    s.radM (r * r') 0 1 = s.radM r 0 1 + s.radM r' 0 1 ∧
      s.radM (r * r') 0 2 = s.radM r 0 2 + s.radM r' 0 2 := by
  have h1 : s.radM (r * r') = uMat (s.radM r 0 1) (s.radM r 0 2) 0 *
      uMat (s.radM r' 0 1) (s.radM r' 0 2) 0 := by
    rw [s.radM_mul]
    exact congrArg₂ (· * ·) (s.radM_eq r) (s.radM_eq r')
  rw [h1]
  constructor <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem natEig_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) (j : ℤ) :
    IsNatEigSection K₂ (y ^ j) s.leviS (q4311 I K) R₂ 1 := by
  classical
  let β₄ : ↥R₂ →* Multiplicative (Fin 2 → F) :=
    { toFun := fun r => Multiplicative.ofAdd ![-(s.radM r 0 2), s.radM r 0 1]
      map_one' := by
        have h1 : s.radM 1 = 1 := by
          rw [radM]
          have e : (⟨((1 : ↥R₂) : G), s.R₂_le_K (1 : ↥R₂).2⟩ : ↥K) = 1 := rfl
          rw [e, map_one]
          rfl
        rw [h1, ← ofAdd_zero]
        congr 1
        ext i
        fin_cases i <;> simp
      map_mul' := fun r r' => by
        obtain ⟨h1, h2⟩ := s.radM_mul_entries r r'
        rw [h1, h2, ← ofAdd_add]
        congr 1
        ext i
        fin_cases i <;> simp [add_comm] }
  have hβ₄ : ∀ r, Multiplicative.toAdd (β₄ r) = ![-(s.radM r 0 2), s.radM r 0 1] := fun r => rfl
  refine ⟨β₄, fun w => ?_, fun r => ?_, fun k r r' hr => ?_, fun r r' hr => ?_⟩
  ·
    set w' := Multiplicative.toAdd w with hw'
    obtain ⟨k, hk⟩ := s.modO2.1 (specialLinearGroupEquivStatedSL 3 F (uSL (w' 1) (-(w' 0)) 0))
    have hkR : (k : G) ∈ R₂ := s.mem_R₂_of k.2 (hk ▸ SL3Pt.mem_radE0_iff.mpr ⟨_, _, rfl⟩)
    refine ⟨⟨k, hkR⟩, ?_⟩
    have hM : s.radM ⟨k, hkR⟩ = uMat (w' 1) (-(w' 0)) 0 := by
      rw [radM]
      have e : (⟨((⟨k, hkR⟩ : ↥R₂) : G), s.R₂_le_K hkR⟩ : ↥K) = k := rfl
      rw [e, hk, specialLinearGroupEquivStatedSL_coe, coe_uSL]
    apply Multiplicative.toAdd.injective
    rw [hβ₄, hM, ← hw']
    ext i
    fin_cases i <;> simp [uMat]
  ·
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K r.2)]
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (β₄ r) = 0 := by rw [h, toAdd_one]
      rw [hβ₄] at h1
      have ha := congrFun h1 1
      have hb := congrFun h1 0
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, neg_eq_zero] at ha hb
      have h2 := s.α_eq_uSL r.2
      change α ⟨r, s.R₂_le_K r.2⟩ = _ at h2
      rw [h2]
      have h3 : s.radM r 0 1 = 0 := ha
      have h4 : s.radM r 0 2 = 0 := hb
      simp only [radM] at h3 h4
      rw [h3, h4, uSL_zero, map_one]
    · intro h
      have h1 : s.radM r = 1 := by
        rw [radM, h]
        rfl
      apply Multiplicative.toAdd.injective
      rw [hβ₄, h1, toAdd_one]
      ext i
      fin_cases i <;> simp
  ·
    have hkK := s.K₂_le_K k.2
    obtain ⟨h00, h10, h20⟩ := s.α_entries k.2
    set B := (((α ⟨k, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      with hB
    have hlev := s.levi_coe k
    have hdet : B 1 1 * B 2 2 - B 1 2 * B 2 1 = 1 := by
      have := (s.levi k).2
      rw [hlev, Matrix.det_fin_two] at this
      simpa [lev] using this
    have e : (⟨(r' : G), s.R₂_le_K r'.2⟩ : ↥K) = ⟨k, hkK⟩ * ⟨r, s.R₂_le_K r.2⟩ *
        (⟨k, hkK⟩ : ↥K)⁻¹ := Subtype.ext hr
    have hr2 : s.radM r' = B * s.radM r *
        ((((α ⟨k, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      show (((α ⟨(r' : G), s.R₂_le_K r'.2⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = _
      rw [e, map_mul, map_mul, map_inv]
      rfl
    have hBinv : B * ((((α ⟨k, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := Units.mul_inv _
    have hBu := mul_uMat h00 h10 h20 hdet (s.radM r 0 1) (s.radM r 0 2)
    have hr'' : s.radM r' = uMat (s.radM r 0 1 * B 2 2 - s.radM r 0 2 * B 2 1)
        (-(s.radM r 0 1 * B 1 2) + s.radM r 0 2 * B 1 1) 0 := by
      rw [hr2]
      conv_lhs => rw [s.radM_eq r]
      rw [hBu, Matrix.mul_assoc, hBinv, Matrix.mul_one]
    change ![-(s.radM r' 0 2), s.radM r' 0 1] =
      ((Matrix.SpecialLinearGroup.toGL (s.levi k) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ![-(s.radM r 0 2), s.radM r 0 1]
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hlev, hr'']
    ext i
    fin_cases i <;> simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, lev] <;> ring
  ·
    have hjK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
    have e : (⟨(r' : G), s.R₂_le_K r'.2⟩ : ↥K) = ⟨y ^ j, hjK⟩ * ⟨r, s.R₂_le_K r.2⟩ *
        (⟨y ^ j, hjK⟩ : ↥K)⁻¹ := Subtype.ext hr
    have h1 := s.coe_α_zpow_y hm j hjK
    have h2 : ((((α ⟨y ^ j, hjK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (((μ ^ j)⁻¹ : Fˣ) : F) := by
      have e2 : (α ⟨y ^ j, hjK⟩)⁻¹ = α ⟨y ^ (-j), Subgroup.zpow_mem _ s.y_mem (-j)⟩ := by
        rw [← map_inv]
        congr 1
        exact Subtype.ext (zpow_neg y j).symm
      rw [← Subgroup.coe_inv, e2, s.coe_α_zpow_y hm (-j), zpow_neg]
    have hr'' : s.radM r' = s.radM r := by
      show (((α ⟨(r' : G), s.R₂_le_K r'.2⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = _
      rw [e, map_mul, map_mul, map_inv]
      change (((α ⟨y ^ j, hjK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          s.radM r * ((((α ⟨y ^ j, hjK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) = s.radM r
      rw [h1, h2, (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq, Matrix.mul_assoc,
        ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, Matrix.mul_one]
    change ![-(s.radM r' 0 2), s.radM r' 0 1] = (1 : F) • ![-(s.radM r 0 2), s.radM r 0 1]
    rw [hr'', one_smul]

theorem le_normalizer_R₂' :
    K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (R₂ : Set G) :=
  _root_.sup_le (le_sup_left.trans s.le_normalizer_R₂)
    (Subgroup.zpowers_le.mpr (by simpa using s.zpow_y_mem_normalizer_R₂ 1))

theorem le_normalizer_Q (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((q4311 I K : Subgroup G) : Set G) :=
  _root_.sup_le s.K₂_le_K (Subgroup.zpowers_le.mpr s.y_mem) |>.trans
    (s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39)

theorem isLabFactor_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) (j : ℤ) :
    IsLabFactor (K₂ ⊔ Subgroup.zpowers y) K₂ (y ^ j) s.leviS (q4311 I K) R₂ (some 1) := by
  have h := s.natEig_R₂ h135 hR hC h37 h38 h39 hm j
  have hKR : K₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_sup_left.trans s.le_normalizer_R₂
  have hlt : q4311 I K < R₂ := by
    refine lt_of_le_of_ne (s.q4311_le_R₂ h135 hR hC h37 h38 h39) fun hQR => ?_
    apply h.not_centralized le_rfl s.leviS_surjective hKR
    intro k hk r hr
    rw [hQR]
    have h1 : k * r * k⁻¹ ∈ R₂ := (Subgroup.mem_normalizer_iff.mp (hKR hk) r).mp hr
    exact R₂.mul_mem h1 (R₂.inv_mem hr)
  exact L4316.isLabFactor_of_natEig h hlt
    (s.R₂_le_K.trans (s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39))
    (s.le_normalizer_Q h135 hR hC h37 h38 h39) s.le_normalizer_R₂' le_sup_left le_rfl
    s.leviS_surjective

end Setting4315

end CFSG.Quasithin.H13.Ch4
