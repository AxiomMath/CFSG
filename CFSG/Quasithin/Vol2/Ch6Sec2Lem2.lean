module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem6Three
public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Cmp
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem mem_of_odd_orbit_ch6 {R W X : Subgroup G} (hR : IsElemAbelian 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hRX : ∀ r ∈ R, ∀ x ∈ X, x * r * x⁻¹ * r⁻¹ ∈ W)
    (hC : R ⊓ Subgroup.centralizer (X : Set G) = ⊥) {z : G} (hz : z ∈ R)
    (hodd : Odd ((X ⊓ Subgroup.centralizer ({z} : Set G)).relIndex X)) : z ∈ W := by
  classical
  let _ : CommGroup ↥R := commGroupOfElemAbelian hR
  have hconj : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr =>
    (Subgroup.mem_normalizer_iff.mp (hXR hx) r).mp hr
  let _ : MulAction ↥X ↥R :=
    { smul := fun x r => ⟨x * r * x⁻¹, hconj x x.2 r r.2⟩
      one_smul := fun r => Subtype.ext (show ((1 : ↥X) : G) * r * ((1 : ↥X) : G)⁻¹ = r by simp)
      mul_smul := fun x y r => Subtype.ext (show ((x * y : ↥X) : G) * r * ((x * y : ↥X) : G)⁻¹ =
        x * (y * r * (y : G)⁻¹) * (x : G)⁻¹ by simp [mul_assoc]) }
  have hsmul : ∀ (x : ↥X) (r : ↥R), ((x • r : ↥R) : G) = x * r * (x : G)⁻¹ := fun _ _ => rfl
  set z' : ↥R := ⟨z, hz⟩ with hz'
  set O := (Set.toFinite (MulAction.orbit ↥X z')).toFinset with hO
  set w : ↥R := ∏ y ∈ O, y with hw
  have hinv : ∀ x : ↥X, x • w = w := by
    intro x
    let φ : ↥R →* ↥R :=
      { toFun := fun r => x • r
        map_one' := Subtype.ext (by simp [hsmul])
        map_mul' := fun a b => Subtype.ext (by simp only [hsmul, Subgroup.coe_mul]; group) }
    have h1 : x • w = ∏ y ∈ O, x • y := map_prod φ _ _
    rw [h1]
    refine Finset.prod_nbij' (fun y => x • y) (fun y => x⁻¹ • y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rw [hO, Set.Finite.mem_toFinset] at hy ⊢
      obtain ⟨g, rfl⟩ := hy
      exact ⟨x * g, mul_smul _ _ _⟩
    · intro y hy
      rw [hO, Set.Finite.mem_toFinset] at hy ⊢
      obtain ⟨g, rfl⟩ := hy
      exact ⟨x⁻¹ * g, mul_smul _ _ _⟩
    · intro y _
      simp [smul_smul]
    · intro y _
      simp [smul_smul]
    · intro y _
      rfl
  have hw1 : w = 1 := by
    have hwC : (w : G) ∈ R ⊓ Subgroup.centralizer (X : Set G) := by
      refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have := congrArg Subtype.val (hinv ⟨x, hx⟩)
      rw [hsmul] at this
      calc x * (w : G) = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [this]
    rw [hC] at hwC
    exact Subtype.ext (Subgroup.mem_bot.mp hwC)
  have hcard : Odd O.card := by
    have hstab : MulAction.stabilizer ↥X z' =
        (X ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf X := by
      ext x
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        rw [Set.mem_singleton_iff.mp hy]
        have := congrArg Subtype.val hx
        rw [hsmul] at this
        calc z * (x : G) = x * z * (x : G)⁻¹ * x := by rw [this]
          _ = x * z := by group
      · rintro ⟨-, hx⟩
        apply Subtype.ext
        rw [hsmul]
        have := Subgroup.mem_centralizer_iff.mp hx z rfl
        calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [this]
          _ = z := by group
    have h1 := MulAction.index_stabilizer ↥X z'
    rw [hstab] at h1
    have h2 : O.card = Nat.card (MulAction.orbit ↥X z') :=
      (Nat.card_eq_card_finite_toFinset (Set.toFinite _)).symm
    rw [h2, Nat.card_coe_set_eq, ← h1]
    exact hodd
  set W' := W.subgroupOf R with hW'
  have hWn : W'.Normal := Subgroup.normal_of_isMulCommutative W'
  have hmod : ∀ y ∈ O, (QuotientGroup.mk' W' y) = QuotientGroup.mk' W' z' := by
    intro y hy
    rw [hO, Set.Finite.mem_toFinset] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (g • z')⁻¹ * z' = ((g • z') * z'⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
    rw [e]
    refine W'.inv_mem ?_
    rw [hW', Subgroup.mem_subgroupOf]
    simpa [hsmul, hz'] using hRX z hz g g.2
  have hz2 : z' ^ 2 = 1 := Subtype.ext (by simpa using hR.2 z hz)
  have hzW : QuotientGroup.mk' W' z' = 1 := by
    have h1 : QuotientGroup.mk' W' w = QuotientGroup.mk' W' z' ^ O.card := by
      rw [hw, map_prod, Finset.prod_congr rfl hmod, Finset.prod_const]
    rw [hw1, map_one] at h1
    obtain ⟨k, hk⟩ := hcard
    rw [h1, hk, pow_succ, pow_mul, ← map_pow, hz2, map_one, one_pow, one_mul]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hW', Subgroup.mem_subgroupOf] at hzW
  exact hzW

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem omega_le_V (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) : quasithinOmegaOneCenter T ≤ V := by
  have h5 := h.toHyp5_0_1
  have hRred := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hRL : ⁅reducedAggregate (L ⊔ T), L⁆ = V := by
    rw [← h.toHyp611.lemma_6_1_6_three h331 h432 h512 h614 h615, h.comm_eq]
  intro z hz
  refine mem_of_odd_orbit_ch6 hRred.2.2.1 (le_sup_left.trans hRred.2.1) ?_ ?_
    (h5.omega_le_reducedAggregate hz) ?_
  · intro r hr x hx
    have : x * r * x⁻¹ * r⁻¹ ∈ ⁅L, reducedAggregate (L ⊔ T)⁆ :=
      Subgroup.commutator_mem_commutator hx hr
    rwa [Subgroup.commutator_comm, hRL] at this
  · have hT := h.toHyp611.inf_centralizer_eq_bot h331 h432 h615
    refine le_bot_iff.mp fun x hx => ?_
    rw [← hT]
    exact ⟨h5.reducedAggregate_le_T hx.1, hx.2⟩
  · have hsyl : IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal (h5.isSylowTwoOf le_sup_right) le_sup_left
        h5.sup_le_normalizer
    have hle : T ⊓ L ≤ L ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
        refine (Subgroup.closure_le _).mpr ?_ hz
        rintro y ⟨⟨-, hy⟩, -⟩
        exact hy
      exact (Subgroup.mem_centralizer_iff.mp hzT x hx.1).symm
    have hdvd := Subgroup.relIndex_dvd_of_le_left L hle
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    exact hsyl.2.2 (h2.trans hdvd)

theorem not_centralizer_omega_le (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) :
    ¬ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := by
  obtain ⟨H, hH⟩ := h.toHyp5_0_1.exists_isHStar h331
  exact fun hle => hH.2.1 ((h615 G T M L V 2 h.toHyp611 H hH).trans hle)

theorem exists_not_mem_centralizer_ZS (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) :
    ∃ t ∈ T, t ∉ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  by_contra hcon
  push Not at hcon
  apply h.not_centralizer_omega_le h331 h615
  have hZS : ch6ZS T L V ≤ quasithinOmegaOneCenter T := fun z hz =>
    Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hz.1, Subgroup.mem_centralizer_iff.mpr
      fun t ht => (Subgroup.mem_centralizer_iff.mp (hcon t ht) z hz).symm⟩,
      h.toHyp611.isElemAbelian.2 z hz.1⟩
  exact (Subgroup.centralizer_le hZS).trans h.centralizer_le

theorem card_omega (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) : Nat.card (quasithinOmegaOneCenter T) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS h331 h615
  have hZV := h.omega_le_V h331 h432 h512 h614 h615
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  set U := ch6ZS T L V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have hZU : quasithinOmegaOneCenter T ≤ U := fun z hz =>
    ⟨⟨hZV hz, Subgroup.centralizer_le inf_le_left (hZC hz)⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact Subgroup.mem_centralizer_iff.mp (hZC hz) t htT⟩
  have hUne : U ≠ ch6ZS T L V := by
    intro heq
    apply htZ
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    rw [← heq] at hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 t rfl).symm
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by
    rw [h.toHyp611Nat.card_ZS]; norm_num
  have hU2 : Nat.card U ≤ 2 := by
    have hdvd : Nat.card U ∣ 4 := hZS4 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card U ≠ 4 := by
      intro h4
      exact hUne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hZS4]))
    have : Nat.card U ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) ≤ 2 :=
    (Subgroup.card_le_of_le hZU).trans hU2
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1
      (fun hb => h.toHyp611Nat.ZS_ne_bot (le_bot_iff.mp (hb ▸ fun x hx =>
        h.toHyp611.le_T hx.1)))
  have hZ1 : 1 < Nat.card (quasithinOmegaOneCenter T) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
  omega

end Hyp6Sec2

section ProjLine

variable {K : Type} [Field K]

@[expose] def IsSemilinCh6 (f : (Fin 2 → K) ≃+ (Fin 2 → K)) : Prop :=
  ∃ σ : K ≃+* K, ∀ (c : K) (w : Fin 2 → K), f (c • w) = σ c • f w

@[expose] noncomputable def projMapCh6 (f : (Fin 2 → K) ≃+ (Fin 2 → K)) (hf : IsSemilinCh6 f) :
    ℙ K (Fin 2 → K) → ℙ K (Fin 2 → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K (f v) fun h0 => v.2 (f.injective (h0.trans (map_zero f).symm)))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      obtain ⟨σ, hσ⟩ := hf
      simp only at hab ⊢
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨σ t, by rw [hab, hσ]⟩)

theorem exists_eq_smul_of_forall_line_ch6 (f : (Fin 2 → K) ≃+ (Fin 2 → K)) (hf : IsSemilinCh6 f)
    (hline : ∀ w : Fin 2 → K, w ≠ 0 → ∃ a : K, f w = a • w) : ∃ a : K, ∀ w, f w = a • w := by
  obtain ⟨σ, hσ⟩ := hf
  have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  have h01 : (![0, 1] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 1
  obtain ⟨a, ha⟩ := hline _ h10
  obtain ⟨b, hb⟩ := hline _ h01
  have hsum : (![1, 0] : Fin 2 → K) + ![0, 1] = ![1, 1] := by
    funext i; fin_cases i <;> simp
  have h11 : (![1, 1] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  obtain ⟨d, hd⟩ := hline _ h11
  have hab : b = a := by
    have e := hd
    rw [← hsum, map_add, ha, hb] at e
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp at e0 e1
    rw [e1, ← e0]
  have ha0 : a ≠ 0 := by
    intro h0
    apply h10
    apply f.injective
    rw [ha, h0, zero_smul, map_zero]
  have hσ1 : ∀ x : K, σ x = x := by
    intro x
    have hne : (![1, x] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    obtain ⟨c, hc⟩ := hline _ hne
    have hsplit : (![1, x] : Fin 2 → K) = ![1, 0] + x • ![0, 1] := by
      funext i; fin_cases i <;> simp
    have e := hc
    rw [hsplit, map_add, hσ, ha, hb, hab] at e
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp at e0 e1
    have hca : c = a := by rw [e0]
    rw [hca] at e1
    exact mul_right_cancel₀ ha0 (by rw [e1, mul_comm])
  refine ⟨a, fun w => ?_⟩
  have hsplit : w = w 0 • (![1, 0] : Fin 2 → K) + w 1 • ![0, 1] := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, hσ, hσ, ha, hb, hab, hσ1, hσ1]
  conv_rhs => rw [hsplit]
  funext i; fin_cases i <;> simp [mul_comm]

end ProjLine

namespace NatL2Data

variable {n : ℕ} (D : NatL2Data L V n)

@[expose] noncomputable def trAut (φ : MulAut ↥V) : (Fin 2 → D.K) ≃+ (Fin 2 → D.K) :=
  MulEquiv.toAdditive ((D.E.symm.trans φ).trans D.E)

omit [Finite G] in
theorem trAut_apply (φ : MulAut ↥V) (v : ↥V) :
    D.trAut φ (Multiplicative.toAdd (D.E v)) = Multiplicative.toAdd (D.E (φ v)) := by
  change Additive.ofMul (D.E (φ (D.E.symm (D.E v)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [Finite G] in
theorem trAut_conjAct (g : Subgroup.normalizer (V : Set G)) : D.trAut (conjAct V g) = D.conj g :=
  rfl

omit [Finite G] in
theorem trAut_mul (φ ψ : MulAut ↥V) (w : Fin 2 → D.K) :
    D.trAut (φ * ψ) w = D.trAut φ (D.trAut ψ w) := by
  change Additive.ofMul (D.E (φ (ψ (D.E.symm (Additive.toMul w))))) =
    Additive.ofMul (D.E (φ (D.E.symm (D.E (ψ (D.E.symm (Additive.toMul w)))))))
  rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem trAut_one (w : Fin 2 → D.K) : D.trAut 1 w = w := by
  change Additive.ofMul (D.E (D.E.symm (Additive.toMul w))) = w
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
theorem eq_one_of_trAut (φ : MulAut ↥V) (hφ : ∀ w, D.trAut φ w = w) : φ = 1 := by
  ext v
  have h1 := hφ (Multiplicative.toAdd (D.E v))
  rw [D.trAut_apply] at h1
  exact congrArg Subtype.val (D.E.injective (Multiplicative.toAdd.injective h1))

@[expose] def semilinSub : Subgroup (MulAut ↥V) where
  carrier := {φ | IsSemilinCh6 (D.trAut φ)}
  mul_mem' := by
    rintro φ ψ ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨τ.trans σ, fun c w => by
      simp only [D.trAut_mul, hτ, hσ, RingEquiv.coe_trans, Function.comp_apply]⟩
  one_mem' := ⟨RingEquiv.refl _, fun c w => by simp [D.trAut_one]⟩
  inv_mem' := by
    rintro φ ⟨σ, hσ⟩
    refine ⟨σ.symm, fun c w => ?_⟩
    have hinv : ∀ w, D.trAut φ (D.trAut φ⁻¹ w) = w := fun w => by
      rw [← D.trAut_mul, mul_inv_cancel, D.trAut_one]
    apply (D.trAut φ).injective
    rw [hσ, hinv, hinv, RingEquiv.apply_symm_apply]

@[expose, instance_reducible] noncomputable def projAction :
    MulAction ↥D.semilinSub (ℙ D.K (Fin 2 → D.K)) where
  smul φ p := projMapCh6 (D.trAut φ) φ.2 p
  one_smul p := by
    induction p with
    | h v hv =>
      exact (Projectivization.mk_eq_mk_iff' D.K _ _ _ hv).mpr
        ⟨1, by rw [one_smul]; exact (D.trAut_one v).symm⟩
  mul_smul φ ψ p := by
    induction p with
    | h v hv =>
      exact (Projectivization.mk_eq_mk_iff' D.K _ _ _ _).mpr
        ⟨1, by rw [one_smul]; exact (D.trAut_mul φ ψ v).symm⟩

@[expose] noncomputable def projPerm : ↥D.semilinSub →* Equiv.Perm (ℙ D.K (Fin 2 → D.K)) :=
  @MulAction.toPermHom _ _ _ D.projAction

omit [Finite G] in
theorem projPerm_mk (φ : ↥D.semilinSub) (v : Fin 2 → D.K) (hv : v ≠ 0) :
    D.projPerm φ (Projectivization.mk D.K v hv) =
      Projectivization.mk D.K (D.trAut φ v) fun h0 =>
        hv ((D.trAut φ).injective (h0.trans (map_zero _).symm)) :=
  rfl

omit [Finite G] in
theorem conjAct_mem_semilinSub (g : Subgroup.normalizer (V : Set G))
    (hg : (g : G) ∈ Subgroup.normalizer (L : Set G)) : conjAct V g ∈ D.semilinSub :=
  D.exists_semilinear g hg

end NatL2Data

omit [Finite G] in
theorem mul_pow_mul_inv_pow_mem_ch6 {L : Subgroup G} {ℓ t : G} (hℓ : ℓ ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) : (ℓ * t) ^ m * (t ^ m)⁻¹ ∈ L := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (ℓ * t) ^ (m + 1) * (t ^ (m + 1))⁻¹ =
        ((ℓ * t) ^ m * (t ^ m)⁻¹) * (t ^ m * ℓ * (t ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]; group
    rw [e]
    exact L.mul_mem ih ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht m) ℓ).mp hℓ)

namespace Hyp611

variable {n : ℕ}

theorem exists_pow_mem_autOn_L_ch6 (h : Hyp611 G T M L V n) {φ : MulAut ↥V}
    (hφ : φ ∈ autOn (L ⊔ T) V) : ∃ k : ℕ, φ ^ 2 ^ k ∈ autOn L V := by
  obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.mp hφ
  obtain ⟨ℓ, hℓ, t, ht, hgeq⟩ := exists_mul_of_mem_sup_ch6 h.toHyp5_0_1.T_le_normalizer hg
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, mem_autOn_iff.mpr ⟨g ^ 2 ^ k, ?_, by rw [map_pow]⟩⟩
  have := mul_pow_mul_inv_pow_mem_ch6 hℓ (h.toHyp5_0_1.T_le_normalizer ht) (2 ^ k)
  rw [htk, inv_one, mul_one, ← hgeq] at this
  simpa using this

end Hyp611

namespace Hyp611Nat

theorem card_autOn_L_ch6 (h : Hyp611Nat G T M L V 2) : Nat.card ↥(autOn L V) = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := h.toHyp611.L_le_normalizer
  rw [card_autOn_eq_relIndex hLV]
  have heq : (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ :=
        h.toHyp5_0_1.inf_centralizer_le hLV h.module.2.2 (Subgroup.mem_subgroupOf.mp hx)
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, ?_⟩
      have hxO : (x : G) ∈ pCoreOf 2 L := by
        exact ⟨x, hx, rfl⟩
      have hOO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
          (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
            (h.toHyp5_0_1.T_le_normalizer.trans
              (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      have hxQ : (x : G) ∈ ch6Q T V := by rw [h.toHyp611.centralizer_eq]; exact hOO hxO
      exact hxQ.2
  have h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
      (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)).toEquiv]
    exact h.card_oTwoQuot_L
  show ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L).index = 60
  rw [heq, Subgroup.index, h60]

theorem autOn_sup_le_semilinSub (h : Hyp611Nat G T M L V 2) :
    autOn (L ⊔ T) V ≤ h.data.semilinSub := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.mp hφ
  exact h.data.conjAct_mem_semilinSub g (h.toHyp5_0_1.sup_le_normalizer hg)

theorem eq_one_of_projPerm_ch6 (h : Hyp611Nat G T M L V 2) {φ : MulAut ↥V}
    (hφ : φ ∈ autOn (L ⊔ T) V)
    (h1 : h.data.projPerm ⟨φ, h.autOn_sup_le_semilinSub hφ⟩ = 1) : φ = 1 := by
  classical
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  set D := h.data with hD
  have hS : φ ∈ D.semilinSub := h.autOn_sup_le_semilinSub hφ
  have hline : ∀ w : Fin 2 → D.K, w ≠ 0 → ∃ a : D.K, D.trAut φ w = a • w := by
    intro w hw
    have := congrArg (fun π : Equiv.Perm (ℙ D.K (Fin 2 → D.K)) =>
      π (Projectivization.mk D.K w hw)) h1
    simp only [Equiv.Perm.coe_one, id_eq] at this
    rw [D.projPerm_mk] at this
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' D.K _ _ _ hw).mp this
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := exists_eq_smul_of_forall_line_ch6 (D.trAut φ) hS hline
  have ha0 : a ≠ 0 := by
    intro h0
    have e := ha ![1, 0]
    rw [h0, zero_smul] at e
    have := (D.trAut φ).injective (e.trans (map_zero _).symm)
    simpa using congrFun this 0
  have ha3 : a ^ 3 = 1 := by
    have : Fintype D.K := Fintype.ofFinite _
    have hq : Fintype.card D.K = 4 := by rw [← Nat.card_eq_fintype_card, D.card]; norm_num
    have := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [hq] at this
  have hφ3 : φ ^ 3 = 1 := by
    apply D.eq_one_of_trAut
    intro w
    rw [pow_succ, pow_succ, pow_one, D.trAut_mul, D.trAut_mul, ha, ha, ha, smul_smul,
      smul_smul]
    convert one_smul D.K w using 2
    linear_combination ha3
  obtain ⟨k, hk⟩ := h.toHyp611.exists_pow_mem_autOn_L_ch6 hφ
  have hφL : φ ∈ autOn L V := by
    have e : φ = (φ ^ 2 ^ k) ^ 2 ^ k := by
      rw [← pow_mul, ← mul_pow, show (2 * 2 : ℕ) = 4 from rfl]
      have hmod : 4 ^ k % 3 = 1 := by
        rw [Nat.pow_mod]; norm_num
      conv_rhs => rw [← Nat.div_add_mod (4 ^ k) 3, hmod, pow_add, pow_mul, hφ3, one_pow,
        one_mul, pow_one]
    rw [e]
    exact Subgroup.pow_mem _ hk _
  obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp hφL
  obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g hgL
  have hgφ : ∀ w, D.conj g w = a • w := fun w => by rw [← D.trAut_conjAct, hg, ha]
  have hA0 := hA ![1, 0]
  have hA1 := hA ![0, 1]
  rw [hgφ] at hA0 hA1
  have e00 := congrFun hA0 0
  have e10 := congrFun hA0 1
  have e01 := congrFun hA1 0
  have e11 := congrFun hA1 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e10 e01 e11
  have hdet := A.2
  rw [Matrix.det_fin_two, ← e00, ← e11, ← e10, ← e01] at hdet
  have ha1 : a = 1 := by
    have h2 : (2 : D.K) = 0 := CharTwo.two_eq_zero
    have hsq : (a + 1) * (a + 1) = 0 := by
      have : a * a = 1 := by simpa using hdet
      linear_combination this + (a + 1) * h2
    linear_combination mul_self_eq_zero.mp hsq - h2
  apply D.eq_one_of_trAut
  intro w
  rw [ha, ha1, one_smul]

end Hyp611Nat

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_autOn_sup (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) :
    Nat.card ↥(autOn (L ⊔ T) V) = 120 := by
  classical
  set D := h.toHyp611Nat.data with hD
  set f : ↥(autOn (L ⊔ T) V) →* Equiv.Perm (ℙ D.K (Fin 2 → D.K)) :=
    D.projPerm.comp (Subgroup.inclusion h.toHyp611Nat.autOn_sup_le_semilinSub) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    exact Subtype.ext (h.toHyp611Nat.eq_one_of_projPerm_ch6 φ.2 hφ)
  have hP : Nat.card (ℙ D.K (Fin 2 → D.K)) = 5 := by
    rw [Projectivization.card_of_finrank_two D.K (Fin 2 → D.K) (Module.finrank_fin_fun D.K),
      D.card]
    norm_num
  have hle : Nat.card ↥(autOn (L ⊔ T) V) ≤ 120 := by
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_perm, hP] at this
  have hdvd : 60 ∣ Nat.card ↥(autOn (L ⊔ T) V) := by
    rw [← h.toHyp611Nat.card_autOn_L_ch6]
    exact Subgroup.card_dvd_of_le (A4.autOn_mono le_sup_left)
  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS h331 h615
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer htT
  have htX : conjAct V ⟨t, htN⟩ ∈ autOn (L ⊔ T) V :=
    mem_autOn_iff.mpr ⟨⟨t, htN⟩, Subgroup.mem_sup_right htT, rfl⟩
  have htL : conjAct V ⟨t, htN⟩ ∉ autOn L V := by
    intro htL
    obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp htL
    obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g hgL
    obtain ⟨v, hv, hlev⟩ := h.toHyp611Nat.exists_line
    apply htZ
    refine h.toHyp611Nat.mem_centralizer_ZS_of_linear hv hlev htT fun c w => ?_
    have e : ∀ w, D.conj ⟨t, htN⟩ w = (A : Matrix (Fin 2) (Fin 2) D.K).mulVec w := fun w => by
      rw [← D.trAut_conjAct, ← hg, D.trAut_conjAct, hA]
    rw [e, e, Matrix.mulVec_smul]
  have hne : Nat.card ↥(autOn (L ⊔ T) V) ≠ 60 := by
    intro h60
    apply htL
    have heq : autOn L V = autOn (L ⊔ T) V := Subgroup.eq_of_le_of_card_ge
      (A4.autOn_mono le_sup_left) (by rw [h60, h.toHyp611Nat.card_autOn_L_ch6])
    rw [heq]
    exact htX
  have hpos : 0 < Nat.card ↥(autOn (L ⊔ T) V) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

theorem nonempty_autOn_mulEquiv_perm (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) :
    Nonempty (↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) := by
  classical
  set D := h.toHyp611Nat.data with hD
  set f : ↥(autOn (L ⊔ T) V) →* Equiv.Perm (ℙ D.K (Fin 2 → D.K)) :=
    D.projPerm.comp (Subgroup.inclusion h.toHyp611Nat.autOn_sup_le_semilinSub) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    exact Subtype.ext (h.toHyp611Nat.eq_one_of_projPerm_ch6 φ.2 hφ)
  have hP : Nat.card (ℙ D.K (Fin 2 → D.K)) = 5 := by
    rw [Projectivization.card_of_finrank_two D.K (Fin 2 → D.K) (Module.finrank_fin_fun D.K),
      D.card]
    norm_num
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_perm, hP, h.card_autOn_sup h331 h615]; rfl)
  exact ⟨(MulEquiv.ofBijective f hbij).trans (Finite.equivFinOfCardEq hP).permCongrHom⟩

end Hyp6Sec2

theorem stmt6_2_2 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h614 : Stmt6_1_4)
    (h615 : Stmt6_1_5) : Stmt6_2_2 := fun _ _ _ _ _ _ _ h =>
  ⟨h.nonempty_autOn_mulEquiv_perm h331 h615, h.card_omega h331 h432 h512 h614 h615,
    h.not_centralizer_omega_le h331 h615⟩

end CFSG.Quasithin.H13
