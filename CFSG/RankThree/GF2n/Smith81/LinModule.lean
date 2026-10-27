module

public import CFSG.RankThree.GF2n.Smith81.LinModuleLinE
public import CFSG.CGT.Timmesfeld75.TransvectionBasic
public import CFSG.RankThree.GF2n.Smith81.Lin212Cond
public import CFSG.RankThree.GF2n.Smith81.LinTLConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix CFSG.Open

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise

section Steps

variable {G : Type} [Group G] [Finite G]
  {M Q Z B Y : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

private theorem exists_lift_normalizer (hc : Ctx M Q Z B) (hY : Ctx M Q Z Y) {s : G}
    (hs : s ∈ Lgen M (LB M Q B)) (hsYZ : ∀ u ∈ Y ⊔ Z, s * u * s⁻¹ ∈ Y ⊔ Z) :
    ∃ p ∈ Q, conjSubgroup (p⁻¹ * s) Y = Y := by
  have hsM : s ∈ M := (Lgen_le_H0 hc hs).1
  have hYQ : Y ⊔ Z ≤ Q := sup_le hY.le hc.hyp.Z_normal.1
  have hle : conjSubgroup s Y ≤ Y ⊔ Z := by
    intro v hv
    rw [mem_conjSubgroup] at hv
    have h := hsYZ _ (le_sup_left (a := Y) hv)
    simpa [mul_assoc] using h
  have hZs : conjSubgroup s Z = Z := conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hsM)
  have hY' : Ctx M Q Z (conjSubgroup s Y) := by
    obtain ⟨g, hg⟩ := hY.conj
    refine ⟨hc.hyp, ⟨s * g, by rw [hg, conjSubgroup_mul]⟩, hle.trans hYQ, ?_⟩
    intro h
    apply hY.ne
    have h2 : conjSubgroup s⁻¹ (conjSubgroup s Y) = conjSubgroup s⁻¹ (conjSubgroup s Z) := by
      rw [h, hZs]
    rwa [← conjSubgroup_mul, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one,
      conjSubgroup_one] at h2
  obtain ⟨p, hpQ, hp⟩ := hY.exists_conj_of_le_ZB hY' (by rw [sup_comm]; exact hle)
  refine ⟨p, hpQ, ?_⟩
  rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

private theorem step1_of_card (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁)
    (hD : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB Y)) :
    Q ⊓ QB Y ⊓ V₂ = Z ∧ (Q ⊓ QB Y) ⊔ V₂ = Q := by
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, -, -, -, hc₂⟩ := hS.basic
  have hN2 : LB M Q Y ≤ Subgroup.normalizer (V₂ : Set G) := fun t ht =>
    conjSubgroup_eq_self_iff.mp (LinSetup.conj_eq_of_le_V₁ hc hS hn hY hYV ht).2
  have hYZ : (Y ⊔ Z) ⊓ V₂ = Z := by
    refine le_antisymm ?_ (le_inf le_sup_right hZ₂)
    exact (inf_le_inf_right _ (sup_le hYV hZ₁)).trans hint.le
  have h1 : Q ⊓ QB Y ⊓ V₂ = Z := hY.inf_QB_inf_eq_of_sup_inf hZ₂ hN2 hYZ
  refine ⟨h1, ?_⟩
  have hDQ : Q ⊓ QB Y ≤ Q := inf_le_left
  have hN : Q ⊓ QB Y ≤ Subgroup.normalizer (V₂ : Set G) :=
    hDQ.trans (Q_le_normalizer_of_Z_le hc.hyp hZ₂ hV₂Q)
  have hprod := card_sup_mul_card_inf_of_normalizer hN
  have hinf : V₂ ⊓ (Q ⊓ QB Y) = Z := by rw [inf_comm]; exact h1
  rw [hinf, hc₂] at hprod
  have hW := LinSetup.width hc.hyp hS
  unfold Width at hW
  have hle : V₂ ⊔ (Q ⊓ QB Y) ≤ Q := sup_le hV₂Q hDQ
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hge : Nat.card Q ≤ Nat.card ↥(V₂ ⊔ (Q ⊓ QB Y)) := by
    rw [hW]
    have h3 : Nat.card Z ^ (2 * n + 1) * Nat.card Z ≤
        Nat.card ↥(V₂ ⊔ (Q ⊓ QB Y)) * Nat.card Z := by
      rw [hprod]
      calc Nat.card Z ^ (2 * n + 1) * Nat.card Z
          = Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1) := by ring
        _ ≤ Nat.card Z ^ (n + 1) * Nat.card ↥(Q ⊓ QB Y) := Nat.mul_le_mul_left _ hD
    exact Nat.le_of_mul_le_mul_right h3 hZpos
  rw [sup_comm]
  exact Subgroup.eq_of_le_of_card_ge hle hge



private structure CoordProps {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}
    (S Q Z V₁ V₂ : Subgroup G) (ρ : ↥S →* GL (Fin n) F) (ψ₁ ψ₂ : G → Fin n → F) : Prop where
  card : Nat.card F = Nat.card Z
  range : ρ.range = StatedSL n F
  add₁ : ∀ u ∈ V₁, ∀ v ∈ V₁, ψ₁ (u * v) = ψ₁ u + ψ₁ v
  ker₁ : ∀ u ∈ V₁, ψ₁ u = 0 ↔ u ∈ Z
  surj₁ : ∀ x : Fin n → F, ∃ u ∈ V₁, ψ₁ u = x
  add₂ : ∀ u ∈ V₂, ∀ v ∈ V₂, ψ₂ (u * v) = ψ₂ u + ψ₂ v
  ker₂ : ∀ u ∈ V₂, ψ₂ u = 0 ↔ u ∈ Z
  eq₁ : ∀ s : ↥S, ∀ u ∈ V₁,
    ψ₁ ((s : G) * u * (s : G)⁻¹) = (ρ s : Matrix (Fin n) (Fin n) F) *ᵥ ψ₁ u
  eq₂ : ∀ s : ↥S, ∀ v ∈ V₂,
    ψ₂ ((s : G) * v * (s : G)⁻¹) = (tinvGL (ρ s) : Matrix (Fin n) (Fin n) F) *ᵥ ψ₂ v
  one_iff : ∀ s : ↥S, ρ s = 1 ↔ (s : G) ∈ Q

private theorem exists_coordProps {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F)
      (ψ₁ ψ₂ : G → Fin n → F), CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂ := by
  obtain ⟨K, hK, hKfin, hKchar, γ, M₀, φ, F, hF, hFfin, hFchar, ρ', C, hcardK, -, hπ, hφQ,
    -, hrange, hV₁, hV₂, -⟩ := exists_linCoord hc hS hn
  obtain ⟨-, hV₁Q, -, hV₂Q, -⟩ := hS.basic
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hact1 : ∀ (s : ↥(Lgen M (LB M Q B))) (e : M₀.E),
      (C.Ψ (φ ⟨(s : G), hSH s.2⟩ e)).1 = (ρ' s : Matrix (Fin n) (Fin n) F) *ᵥ (C.Ψ e).1 :=
    fun s e => congrArg Prod.fst (C.act s e)
  have hact2 : ∀ (s : ↥(Lgen M (LB M Q B))) (e : M₀.E),
      (C.Ψ (φ ⟨(s : G), hSH s.2⟩ e)).2 =
        (tinvGL (ρ' s) : Matrix (Fin n) (Fin n) F) *ᵥ (C.Ψ e).2 :=
    fun s e => congrArg Prod.snd (C.act s e)
  have hfull : ∀ (s : ↥(Lgen M (LB M Q B))) (e : M₀.E),
      C.Ψ (φ ⟨(s : G), hSH s.2⟩ e) = ((ρ' s : Matrix (Fin n) (Fin n) F) *ᵥ (C.Ψ e).1,
        (tinvGL (ρ' s) : Matrix (Fin n) (Fin n) F) *ᵥ (C.Ψ e).2) :=
    fun s e => C.act s e
  refine ⟨F, hF, hFfin, ρ', fun u => (C.Ψ (M₀.π u)).1, fun u => (C.Ψ (M₀.π u)).2, ?_⟩
  refine ⟨?_, hrange, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Nat.card_congr C.θ₁.toEquiv).symm).trans hcardK
  · intro u hu v hv
    show (C.Ψ (M₀.π (u * v))).1 = (C.Ψ (M₀.π u)).1 + (C.Ψ (M₀.π v)).1
    rw [M₀.π_mul u (hV₁Q hu) v (hV₁Q hv), map_add, Prod.fst_add]
  · intro u hu
    show (C.Ψ (M₀.π u)).1 = 0 ↔ u ∈ Z
    constructor
    · intro h1
      have h2 : (C.Ψ (M₀.π u)).2 = 0 := (hV₁ _).mp (M₀.pi_mem_img hu (hV₁Q hu))
      have h0 : M₀.π u = 0 := C.Ψ.injective (by rw [map_zero]; exact Prod.ext h1 h2)
      exact (M₀.π_ker u (hV₁Q hu)).mp h0
    · intro hz
      have h0 : M₀.π u = 0 := (M₀.π_ker u (hV₁Q hu)).mpr hz
      show (C.Ψ (M₀.π u)).1 = 0
      rw [h0, map_zero]; rfl
  · intro x
    obtain ⟨u, huV, huQ, hu⟩ := M₀.mem_img.mp
      ((hV₁ (C.Ψ.symm (x, 0))).mpr (by rw [C.Ψ.apply_symm_apply]))
    refine ⟨u, huV, ?_⟩
    show (C.Ψ (M₀.π u)).1 = x
    rw [hu, C.Ψ.apply_symm_apply]
  · intro u hu v hv
    show (C.Ψ (M₀.π (u * v))).2 = (C.Ψ (M₀.π u)).2 + (C.Ψ (M₀.π v)).2
    rw [M₀.π_mul u (hV₂Q hu) v (hV₂Q hv), map_add, Prod.snd_add]
  · intro u hu
    show (C.Ψ (M₀.π u)).2 = 0 ↔ u ∈ Z
    constructor
    · intro h2
      have h1 : (C.Ψ (M₀.π u)).1 = 0 := (hV₂ _).mp (M₀.pi_mem_img hu (hV₂Q hu))
      have h0 : M₀.π u = 0 := C.Ψ.injective (by rw [map_zero]; exact Prod.ext h1 h2)
      exact (M₀.π_ker u (hV₂Q hu)).mp h0
    · intro hz
      have h0 : M₀.π u = 0 := (M₀.π_ker u (hV₂Q hu)).mpr hz
      show (C.Ψ (M₀.π u)).2 = 0
      rw [h0, map_zero]; rfl
  · intro s u hu
    have h : M₀.π ((s : G) * u * (s : G)⁻¹) = φ ⟨(s : G), hSH s.2⟩ (M₀.π u) :=
      hπ ⟨(s : G), hSH s.2⟩ u (hV₁Q hu)
    show (C.Ψ (M₀.π ((s : G) * u * (s : G)⁻¹))).1 = _
    rw [h, hact1]
  · intro s v hv
    have h : M₀.π ((s : G) * v * (s : G)⁻¹) = φ ⟨(s : G), hSH s.2⟩ (M₀.π v) :=
      hπ ⟨(s : G), hSH s.2⟩ v (hV₂Q hv)
    show (C.Ψ (M₀.π ((s : G) * v * (s : G)⁻¹))).2 = _
    rw [h, hact2]
  · intro s
    constructor
    · intro h1
      have hφ1 : φ ⟨(s : G), hSH s.2⟩ = 1 := by
        apply LinearEquiv.ext
        intro e
        apply C.Ψ.injective
        show C.Ψ (φ ⟨(s : G), hSH s.2⟩ e) = C.Ψ e
        rw [hfull, h1, Units.val_one, Matrix.one_mulVec, tinvGL_one, Units.val_one,
          Matrix.one_mulVec]
      exact (hφQ ⟨(s : G), hSH s.2⟩).mp hφ1
    · intro hsQ
      have hφ1 : φ ⟨(s : G), hSH s.2⟩ = 1 := (hφQ ⟨(s : G), hSH s.2⟩).mpr hsQ
      have hx : ∀ x : Fin n → F, (ρ' s : Matrix (Fin n) (Fin n) F) *ᵥ x = x := by
        intro x
        have h3 := hfull s (C.Ψ.symm (x, 0))
        rw [hφ1] at h3
        change C.Ψ (C.Ψ.symm (x, 0)) = _ at h3
        rw [C.Ψ.apply_symm_apply] at h3
        exact (congrArg Prod.fst h3).symm
      apply Units.ext
      ext i j
      have hij := congrFun (hx (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using hij


private theorem matrix_eq_one_of_mulVec_eq {F : Type} [Field F] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) F} (h : ∀ x : Fin n → F, M *ᵥ x = x) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply, Pi.single_apply,
    eq_comm] using this

private theorem coord_sub_mem {F : Type} [Field F] {n : ℕ}
    {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F} {ψ₁ ψ₂ : G → Fin n → F}
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) {t : G} (ht : t ∈ LB M Q Y) (x : Fin n → F) :
    ∃ u ∈ Y ⊔ Z, ψ₁ u = x - (ρ ⟨t, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht⟩ :
      Matrix (Fin n) (Fin n) F) *ᵥ x := by
  obtain ⟨-, hV₁Q, -, -, -, -, hN₁, -, -, -⟩ := hS.basic
  have hLt : t ∈ Lgen M (LB M Q B) := LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht
  have htN : t ∈ Subgroup.normalizer (V₁ : Set G) := hN₁ hLt
  obtain ⟨v, hvV, hvx⟩ := hP.surj₁ x
  have hwV : t * v⁻¹ * t⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.mp htN v⁻¹).mp (V₁.inv_mem hvV)
  have hinv : ψ₁ v⁻¹ = -ψ₁ v := by
    have h1 : ψ₁ (v * v⁻¹) = ψ₁ v + ψ₁ v⁻¹ := hP.add₁ v hvV v⁻¹ (V₁.inv_mem hvV)
    have h0 : ψ₁ 1 = 0 := by
      have h2 := hP.add₁ 1 V₁.one_mem 1 V₁.one_mem
      rw [one_mul] at h2
      exact add_left_cancel (by rw [add_zero]; exact h2.symm)
    rw [mul_inv_cancel, h0] at h1
    calc ψ₁ v⁻¹ = -ψ₁ v + (ψ₁ v + ψ₁ v⁻¹) := by abel
      _ = -ψ₁ v := by rw [h1.symm, add_zero]
  have hcomm : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def]; group
  have heq : ψ₁ (t * v⁻¹ * t⁻¹) = (ρ ⟨t, hLt⟩ : Matrix (Fin n) (Fin n) F) *ᵥ ψ₁ v⁻¹ :=
    hP.eq₁ ⟨t, hLt⟩ v⁻¹ (V₁.inv_mem hvV)
  refine ⟨⁅v, t⁆, LinSetup.comm_mem_sup_of_conj_le_V₁ hc hS hn hY hYV ht hvV, ?_⟩
  rw [hcomm, hP.add₁ v hvV _ hwV, heq, hinv, Matrix.mulVec_neg, hvx, sub_eq_add_neg]

private theorem exists_line {F : Type} [Field F] [Finite F] {n : ℕ}
    {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F} {ψ₁ ψ₂ : G → Fin n → F}
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) :
    ∃ c : Fin n → F, c ≠ 0 ∧
      (∀ t (ht : t ∈ LB M Q Y) (x : Fin n → F),
        x - (ρ ⟨t, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht⟩ :
          Matrix (Fin n) (Fin n) F) *ᵥ x ∈ Submodule.span F {c}) ∧
      (∀ u ∈ Y ⊔ Z, ψ₁ u ∈ Submodule.span F {c}) ∧
      (∀ w ∈ Submodule.span F {c}, ∃ u ∈ Y ⊔ Z, ψ₁ u = w) := by
  have hw : Width Q Z n := LinSetup.width hc.hyp hS
  obtain ⟨hZV₁, hV₁Q, -, -, -, -, -, -, -, -⟩ := hS.basic
  have hYVZ : Y ⊔ Z ≤ V₁ := sup_le hYV hZV₁
  obtain ⟨t₀, ht₀, ht₀Q⟩ : ∃ t ∈ LB M Q Y, t ∉ Q := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have h1 : Nat.card ↥(LB M Q Y) ≤ Nat.card ↥Q := Subgroup.card_le_of_le hcon
    have h2 := hY.card_LB_ge hw (by omega : 1 ≤ n)
    have h3 : 2 ≤ Nat.card Z ^ (n - 1) := by
      have := hc.hyp.q4
      exact le_trans (by omega) (Nat.le_self_pow (by omega : n - 1 ≠ 0) _)
    have h4 : Nat.card Q * 2 ≤ Nat.card Q * Nat.card Z ^ (n - 1) := Nat.mul_le_mul_left _ h3
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    omega
  have hρ1 : ρ ⟨t₀, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht₀⟩ ≠ 1 :=
    fun h => ht₀Q ((hP.one_iff _).mp h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin n → F,
      x₀ - (ρ ⟨t₀, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht₀⟩ :
        Matrix (Fin n) (Fin n) F) *ᵥ x₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hρ1
    apply Units.ext
    rw [Units.val_one]
    apply matrix_eq_one_of_mulVec_eq
    intro x
    exact (sub_eq_zero.mp (hcon x)).symm
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n → F, c = x₀ - (ρ ⟨t₀, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY
      hYV ht₀⟩ : Matrix (Fin n) (Fin n) F) *ᵥ x₀ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hcdef]; exact hx₀
  have hac : ∀ a : F, a • c = (a • x₀) - (ρ ⟨t₀, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht₀⟩ :
      Matrix (Fin n) (Fin n) F) *ᵥ (a • x₀) := by
    intro a
    rw [hcdef, Matrix.mulVec_smul, smul_sub]
  have hcover : ∀ w ∈ Submodule.span F {c}, ∃ u ∈ Y ⊔ Z, ψ₁ u = w := by
    intro w hw'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    obtain ⟨u, hu, hψ⟩ := coord_sub_mem hc hS hn hP hY hYV ht₀ (a • x₀)
    exact ⟨u, hu, hψ.trans (hac a).symm⟩
  have hsub : ∀ u ∈ Y ⊔ Z, ψ₁ u ∈ Submodule.span F {c} := by
    let χ : ↥(Y ⊔ Z) →* Multiplicative (Fin n → F) :=
      MonoidHom.mk' (fun u : ↥(Y ⊔ Z) => Multiplicative.ofAdd (ψ₁ (u : G)))
        (fun u v : ↥(Y ⊔ Z) => by
          exact congrArg Multiplicative.ofAdd (hP.add₁ (u : G) (hYVZ u.2) (v : G) (hYVZ v.2)))
    have hcardH : Nat.card ↥(Y ⊔ Z) = Nat.card Z * Nat.card Z := by
      rw [hY.card_sup_Z, IsZConjugate.card_eq (show IsZConjugate Z Y from hY.conj)]
    have hZYZ : Z ≤ Y ⊔ Z := le_sup_right
    have hkerZ : Nat.card Z ≤ Nat.card χ.ker := by
      have hinj : Function.Injective (fun z : ↥Z => (⟨⟨(z : G), hZYZ z.2⟩,
          MonoidHom.mem_ker.mpr (by
            show Multiplicative.ofAdd (ψ₁ (z : G)) = 1
            rw [(hP.ker₁ (z : G) (hZV₁ z.2)).mpr z.2]
            rfl)⟩ : ↥χ.ker)) := by
        intro z₁ z₂ h
        apply Subtype.ext
        exact congrArg (fun y : ↥χ.ker => ((y : ↥(Y ⊔ Z)) : G)) h
      exact Nat.card_le_card_of_injective _ hinj
    have hprod := Subgroup.card_ker_mul_card_range χ
    rw [hcardH] at hprod
    have hrange : Nat.card χ.range ≤ Nat.card Z := by
      have hqpos : 0 < Nat.card Z := Nat.card_pos
      have h1 : Nat.card Z * Nat.card χ.range ≤ Nat.card χ.ker * Nat.card χ.range :=
        Nat.mul_le_mul_right _ hkerZ
      rw [hprod] at h1
      exact Nat.le_of_mul_le_mul_left h1 hqpos
    let A : Set (Multiplicative (Fin n → F)) :=
      Set.range (fun a : F => Multiplicative.ofAdd (a • c))
    have hinjA : Function.Injective (fun a : F => Multiplicative.ofAdd (a • c)) := by
      intro a b hab
      exact smul_left_injective F hc0 (Multiplicative.ofAdd.injective hab)
    have hAcard : Nat.card A = Nat.card F := Nat.card_range_of_injective hinjA
    have hAB : A ⊆ (χ.range : Set (Multiplicative (Fin n → F))) := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨u, hu, hψ⟩ := hcover (a • c)
        (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self c))
      refine ⟨⟨u, hu⟩, ?_⟩
      show Multiplicative.ofAdd (ψ₁ u) = Multiplicative.ofAdd (a • c)
      rw [hψ]
    have hB : (χ.range : Set (Multiplicative (Fin n → F))).ncard = Nat.card χ.range :=
      (Nat.card_coe_set_eq _).symm
    have hA' : A.ncard = Nat.card F := by rw [← Nat.card_coe_set_eq, hAcard]
    have hEq : A = (χ.range : Set (Multiplicative (Fin n → F))) :=
      Set.eq_of_subset_of_ncard_le hAB (by rw [hB, hA', hP.card]; exact hrange |>.trans_eq' rfl)
        (Set.toFinite _)
    intro u hu
    have hmem : Multiplicative.ofAdd (ψ₁ u) ∈ (χ.range : Set (Multiplicative (Fin n → F))) :=
      ⟨⟨u, hu⟩, rfl⟩
    rw [← hEq] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact Submodule.mem_span_singleton.mpr ⟨a, Multiplicative.ofAdd.injective ha⟩
  refine ⟨c, hc0, ?_, hsub, hcover⟩
  intro t ht x
  obtain ⟨u, hu, hψ⟩ := coord_sub_mem hc hS hn hP hY hYV ht x
  rw [← hψ]
  exact hsub u hu


private theorem coord_inv {F : Type} [Field F] {n : ℕ} {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F}
    {ψ₁ ψ₂ : G → Fin n → F} (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    {v : G} (hv : v ∈ V₁) : ψ₁ v⁻¹ = -ψ₁ v := by
  have h1 : ψ₁ (v * v⁻¹) = ψ₁ v + ψ₁ v⁻¹ := hP.add₁ v hv v⁻¹ (V₁.inv_mem hv)
  have h0 : ψ₁ 1 = 0 := by
    have h2 := hP.add₁ 1 V₁.one_mem 1 V₁.one_mem
    rw [one_mul] at h2
    exact add_left_cancel (by rw [add_zero]; exact h2.symm)
  rw [mul_inv_cancel, h0] at h1
  calc ψ₁ v⁻¹ = -ψ₁ v + (ψ₁ v + ψ₁ v⁻¹) := by abel
    _ = -ψ₁ v := by rw [h1.symm, add_zero]

private theorem mem_sup_of_coord {F : Type} [Field F] {n : ℕ}
    {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F}
    {ψ₁ ψ₂ : G → Fin n → F} (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    (hYV₁ : Y ⊔ Z ≤ V₁) {c : Fin n → F}
    (hcover : ∀ w ∈ Submodule.span F {c}, ∃ u ∈ Y ⊔ Z, ψ₁ u = w)
    {v : G} (hv : v ∈ V₁) (hvc : ψ₁ v ∈ Submodule.span F {c}) : v ∈ Y ⊔ Z := by
  obtain ⟨u, hu, huv⟩ := hcover (ψ₁ v) hvc
  have huV : u ∈ V₁ := hYV₁ hu
  have hz : v * u⁻¹ ∈ Z := by
    rw [← hP.ker₁ (v * u⁻¹) (V₁.mul_mem hv (V₁.inv_mem huV)), hP.add₁ v hv u⁻¹ (V₁.inv_mem huV),
      coord_inv hP huV, huv, add_neg_cancel]
  have hve : v = (v * u⁻¹) * u := by group
  rw [hve]
  have hZYZ : Z ≤ Y ⊔ Z := le_sup_right
  exact (Y ⊔ Z).mul_mem (hZYZ hz) hu

private theorem card_LB_le_of_line {F : Type} [Field F] [Finite F] {n : ℕ}
    {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F} {ψ₁ ψ₂ : G → Fin n → F}
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) {c : Fin n → F} (hc0 : c ≠ 0)
    (hline : ∀ t (ht : t ∈ LB M Q Y) (x : Fin n → F),
      x - (ρ ⟨t, LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV ht⟩ :
        Matrix (Fin n) (Fin n) F) *ᵥ x ∈ Submodule.span F {c}) :
    Nat.card ↥(LB M Q Y) ≤ Nat.card Q * Nat.card F ^ (n - 1) := by
  have hLYS : LB M Q Y ≤ Lgen M (LB M Q B) := LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hY hYV
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hc0 (funext h)
  let f : ↥(LB M Q Y) →* GL (Fin n) F := ρ.comp (Subgroup.inclusion hLYS)
  let β : GL (Fin n) F → Fin n → F := fun g j =>
    (1 - (g : Matrix (Fin n) (Fin n) F)) i₀ j / c i₀
  have hmat : ∀ (t : ↥(LB M Q Y)) (i j : Fin n),
      (1 - (f t : Matrix (Fin n) (Fin n) F)) i j = c i * β (f t) j := by
    intro t i j
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hline t.1 t.2 (Pi.single j 1))
    have hk : (1 - (f t : Matrix (Fin n) (Fin n) F)) *ᵥ Pi.single j 1 = a • c := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact ha.symm
    have hcol : ∀ k, (1 - (f t : Matrix (Fin n) (Fin n) F)) k j = a * c k := by
      intro k
      have hk' := congrFun hk k
      rw [Matrix.mulVec_single_one] at hk'
      simpa using hk'
    have hb : β (f t) j = a := by
      show (1 - (f t : Matrix (Fin n) (Fin n) F)) i₀ j / c i₀ = a
      rw [hcol i₀, mul_div_cancel_right₀ _ hi₀]
    rw [hb, hcol i, mul_comm]
  have hdot : ∀ t : ↥(LB M Q Y), β (f t) ⬝ᵥ c = 0 := by
    intro t
    have hdet : (f t : Matrix (Fin n) (Fin n) F).det = 1 := by
      have hmemS : f t ∈ StatedSL n F := by
        rw [← hP.range]
        exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hLYS t, rfl⟩
      exact StatedAPI.det_of_mem_statedSL hmemS
    have hM : (f t : Matrix (Fin n) (Fin n) F) =
        1 + replicateCol Unit (-c) * replicateRow Unit (β (f t)) := by
      ext i j
      have h1 := hmat t i j
      rw [Matrix.sub_apply, Matrix.one_apply] at h1
      simp [Matrix.mul_apply, replicateCol, replicateRow, Matrix.one_apply]
      linear_combination -h1
    have hdetX := det_one_add_replicateCol_mul_replicateRow (ι := Unit) (-c) (β (f t))
    rw [← hM, hdet, dotProduct_neg] at hdetX
    linear_combination hdetX
  have hΦ : ∀ g ∈ f.range, β g ⬝ᵥ c = 0 := by
    intro g hg
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hg
    exact hdot t
  let Φ : f.range → LinearMap.ker (dotLK c) := fun g =>
    ⟨β g.1, LinearMap.mem_ker.mpr (by
      show c ⬝ᵥ β g.1 = 0
      rw [dotProduct_comm]
      exact hΦ g.1 g.2)⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    have hβ : β g = β g' := congrArg Subtype.val h
    apply Subtype.ext
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨t', rfl⟩ := MonoidHom.mem_range.mp hg'
    apply Units.ext
    ext i j
    have e1 := hmat t i j
    have e2 := hmat t' i j
    rw [hβ] at e1
    have key := e1.trans e2.symm
    simp only [Matrix.sub_apply, Matrix.one_apply] at key
    linear_combination -key
  have hinj : Nat.card f.range ≤ Nat.card (LinearMap.ker (dotLK c)) :=
    Nat.card_le_card_of_injective Φ hΦinj
  have hΛ : Nat.card (LinearMap.ker (dotLK c)) ≤ Nat.card F ^ (n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    apply Nat.pow_le_pow_right Nat.card_pos
    have hdim := finrank_ker_dotLK hc0
    omega
  have hkerQ : Nat.card f.ker ≤ Nat.card Q := by
    have hmemQ : ∀ g : f.ker, (g : ↥(LB M Q Y)).1 ∈ Q := by
      intro g
      have hg : f g = 1 := MonoidHom.mem_ker.mp g.2
      exact (hP.one_iff ⟨(g : ↥(LB M Q Y)).1, hLYS (g : ↥(LB M Q Y)).2⟩).mp hg
    have hinjQ : Function.Injective
        (fun g : f.ker => (⟨(g : ↥(LB M Q Y)).1, hmemQ g⟩ : ↥Q)) := by
      intro g₁ g₂ h
      have h' := congrArg Subtype.val h
      dsimp only at h'
      exact Subtype.ext (Subtype.ext h')
    exact Nat.card_le_card_of_injective _ hinjQ
  have hprod := Subgroup.card_ker_mul_card_range f
  calc Nat.card ↥(LB M Q Y) = Nat.card f.ker * Nat.card f.range := hprod.symm
    _ ≤ Nat.card Q * Nat.card F ^ (n - 1) := Nat.mul_le_mul hkerQ (hinj.trans hΛ)

private theorem card_inf_ge_of_count (q Qn L D n : ℕ) (hq : 0 < q) (hQ : 0 < Qn) (hn : 1 ≤ n)
    (hLD : L * D = Qn * q ^ (2 * n)) (hL : L ≤ Qn * q ^ (n - 1)) : q ^ (n + 1) ≤ D := by
  have h1 : Qn * q ^ (2 * n) ≤ Qn * (q ^ (n - 1) * D) := by
    calc Qn * q ^ (2 * n) = L * D := hLD.symm
      _ ≤ Qn * q ^ (n - 1) * D := Nat.mul_le_mul_right _ hL
      _ = Qn * (q ^ (n - 1) * D) := by ring
  have h2 : q ^ (2 * n) ≤ q ^ (n - 1) * D := Nat.le_of_mul_le_mul_left h1 hQ
  have h3 : q ^ (n + 1) * q ^ (n - 1) ≤ D * q ^ (n - 1) := by
    calc q ^ (n + 1) * q ^ (n - 1) = q ^ (2 * n) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ q ^ (n - 1) * D := h2
      _ = D * q ^ (n - 1) := by ring
  exact Nat.le_of_mul_le_mul_right h3 (pow_pos hq _)

private theorem exists_mu_of_card {F : Type} [Field F] [Finite F] (h : 3 ≤ Nat.card F) :
    ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hsub : (Set.univ : Set F) ⊆ ({0, 1} : Set F) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 : ({0, 1} : Set F).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega


private theorem exists_lift_coord {F : Type} [Field F] [Finite F] {n : ℕ}
    {ρ : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F} {ψ₁ ψ₂ : G → Fin n → F}
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hP : CoordProps (Lgen M (LB M Q B)) Q Z V₁ V₂ ρ ψ₁ ψ₂)
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) {c : Fin n → F}
    (hYline : ∀ u ∈ Y ⊔ Z, ψ₁ u ∈ Submodule.span F {c})
    (hcover : ∀ w ∈ Submodule.span F {c}, ∃ u ∈ Y ⊔ Z, ψ₁ u = w)
    {s : ↥(Lgen M (LB M Q B))}
    (hsc : (ρ s : Matrix (Fin n) (Fin n) F) *ᵥ c ∈ Submodule.span F {c}) :
    ∃ s' : ↥(Lgen M (LB M Q B)), ρ s' = ρ s ∧ conjSubgroup (s' : G) Y = Y := by
  obtain ⟨hZV₁, -, -, -, -, -, hN₁, -, -, -⟩ := hS.basic
  have hYZV₁ : Y ⊔ Z ≤ V₁ := sup_le hYV hZV₁
  have hsN : (s : G) ∈ Subgroup.normalizer (V₁ : Set G) := hN₁ s.2
  have hsYZ : ∀ u ∈ Y ⊔ Z, (s : G) * u * (s : G)⁻¹ ∈ Y ⊔ Z := by
    intro u hu
    have huV : u ∈ V₁ := hYZV₁ hu
    have hsuV : (s : G) * u * (s : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp hsN u).mp huV
    apply mem_sup_of_coord hP hYZV₁ hcover hsuV
    rw [hP.eq₁ s u huV]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hYline u hu)
    rw [← ha, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hsc
  obtain ⟨p, hpQ, hp⟩ := exists_lift_normalizer hc hY s.2 hsYZ
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQLg : Q ≤ Lgen M (LB M Q B) := fun x hx => le_Lgen_self M (LB M Q B) (hQLB hx)
  have hpLg : p⁻¹ ∈ Lgen M (LB M Q B) := Subgroup.inv_mem _ (hQLg hpQ)
  have hρp : ρ ⟨p⁻¹, hpLg⟩ = 1 := (hP.one_iff _).mpr (Subgroup.inv_mem _ hpQ)
  refine ⟨⟨p⁻¹ * s, Subgroup.mul_mem _ hpLg s.2⟩, ?_, hp⟩
  have hs'eq : (⟨p⁻¹ * s, Subgroup.mul_mem _ hpLg s.2⟩ : ↥(Lgen M (LB M Q B))) =
      ⟨p⁻¹, hpLg⟩ * s := Subtype.ext rfl
  rw [hs'eq, map_mul, hρp, one_mul]

private theorem le_QB_of_LinSetup (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) : V₁ ≤ QB Y := by
  obtain ⟨F, hF, hFfin, ρ, ψ₁, ψ₂, hP⟩ := exists_coordProps hc hS hn
  obtain ⟨c, hc0, hLine, hYline, hcover⟩ := exists_line hc hS hn hP hY hYV
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, -, hN₁, hN₂, -, -⟩ := hS.basic
  have hYZV₁ : Y ⊔ Z ≤ V₁ := sup_le hYV hZV₁
  have hw : Width Q Z n := LinSetup.width hc.hyp hS
  have hcount := card_LB_le_of_line hc hS hn hP hY hYV hc0 hLine
  rw [hP.card] at hcount
  have hLB := hY.card_LB_mul hw
  have hD : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB Y) :=
    card_inf_ge_of_count (Nat.card Z) (Nat.card Q) (Nat.card ↥(LB M Q Y))
      (Nat.card ↥(Q ⊓ QB Y)) n Nat.card_pos Nat.card_pos (by omega) hLB hcount
  obtain ⟨hDV₂, hDsup⟩ := step1_of_card hc hS hn hY hYV hD
  have hN : Q ⊓ QB Y ≤ Subgroup.normalizer (V₂ : Set G) :=
    inf_le_left.trans (Q_le_normalizer_of_Z_le hc.hyp hZV₂ hV₂Q)
  have hZD : Z ≤ Q ⊓ QB Y := le_inf hc.Z_le_Q hY.Z_le_QB.1
  have hYQB : Y ⊔ Z ≤ QB Y := sup_le hY.B_le_QB hY.Z_le_QB.1
  intro a ha
  have haQ : a ∈ Q := hV₁Q ha
  have hsup : a ∈ (Q ⊓ QB Y) ⊔ V₂ := by rw [hDsup]; exact haQ
  have hmem : a ∈ ((Q ⊓ QB Y : Subgroup G) : Set G) * ((V₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]
    exact hsup
  obtain ⟨d, hd, b₀, hb₀, hdb⟩ := hmem
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = b₀⁻¹ := ⟨_, rfl⟩
  have hbV : b ∈ V₂ := by rw [hbdef]; exact V₂.inv_mem hb₀
  have hab : a * b ∈ Q ⊓ QB Y := by
    have e : a * b = d := by rw [← hdb, hbdef]; group
    rw [e]; exact hd
  by_cases hx : ψ₁ a ∈ Submodule.span F {c}
  · exact hYQB (mem_sup_of_coord hP hYZV₁ hcover ha hx)
  · have hcx : LinearIndependent F ![c, ψ₁ a] :=
      (LinearIndependent.pair_iff' hc0).mpr
        (fun r hr => hx (Submodule.mem_span_singleton.mpr ⟨r, hr⟩))
    have hE : ∀ g : GL (Fin n) F, g ∈ StatedSL n F →
        (g : Matrix (Fin n) (Fin n) F) *ᵥ c ∈ Submodule.span F {c} →
        (g : Matrix (Fin n) (Fin n) F) *ᵥ ψ₁ a = ψ₁ a →
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ ψ₂ b = ψ₂ b := by
      intro g hgS hgc hgx
      have hg : g ∈ ρ.range := by rw [hP.range]; exact hgS
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hg
      obtain ⟨s', hs'ρ, hs'Y⟩ := exists_lift_coord hc hS hn hP hY hYV hYline hcover
        (s := s) (by rw [hs]; exact hgc)
      have hsg : ρ s' = g := hs'ρ.trans hs
      have hσM : (s' : G) ∈ M := (Lgen_le_H0 hc s'.2).1
      have hσQ : ∀ u ∈ Q, (s' : G) * u * (s' : G)⁻¹ ∈ Q := fun u hu =>
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hσM) u).mp hu
      have hQBeq : conjSubgroup (s' : G) (QB Y) = QB Y := by
        have h := QB_conj (s' : G) Y
        rw [hs'Y] at h
        exact h.symm
      have hσQB : ∀ u ∈ QB Y, (s' : G) * u * (s' : G)⁻¹ ∈ QB Y := by
        intro u hu
        rw [← hQBeq, mem_conjSubgroup]
        have e : (s' : G)⁻¹ * ((s' : G) * u * (s' : G)⁻¹) * (s' : G) = u := by group
        rw [e]; exact hu
      have hσD : ∀ u ∈ Q ⊓ QB Y, (s' : G) * u * (s' : G)⁻¹ ∈ Q ⊓ QB Y := fun u hu =>
        ⟨hσQ u hu.1, hσQB u hu.2⟩
      have hσV₁ : ∀ v ∈ V₁, (s' : G) * v * (s' : G)⁻¹ ∈ V₁ := fun v hv =>
        (Subgroup.mem_normalizer_iff.mp (hN₁ s'.2) v).mp hv
      have hσV₂ : ∀ v ∈ V₂, (s' : G) * v * (s' : G)⁻¹ ∈ V₂ := fun v hv =>
        (Subgroup.mem_normalizer_iff.mp (hN₂ s'.2) v).mp hv
      have haV : a ∈ V₁ := ha
      have hbQ : b ∈ Q := hV₂Q hbV
      have ha' : ψ₁ ((s' : G) * a * (s' : G)⁻¹) = ψ₁ a := by
        rw [hP.eq₁ s' a haV, hsg, hgx]
      have hz : a⁻¹ * ((s' : G) * a * (s' : G)⁻¹) ∈ Z := by
        refine (hP.ker₁ _ (V₁.mul_mem (V₁.inv_mem haV) (hσV₁ a haV))).mp ?_
        rw [hP.add₁ _ (V₁.inv_mem haV) _ (hσV₁ a haV), coord_inv hP haV, ha', neg_add_cancel]
      have hb'V₂ : (s' : G) * b * (s' : G)⁻¹ ∈ V₂ := hσV₂ b hbV
      have hb'Q : (s' : G) * b * (s' : G)⁻¹ ∈ Q := hV₂Q hb'V₂
      have hDab : ((s' : G) * a * (s' : G)⁻¹) * ((s' : G) * b * (s' : G)⁻¹) ∈ Q ⊓ QB Y := by
        have e : ((s' : G) * a * (s' : G)⁻¹) * ((s' : G) * b * (s' : G)⁻¹) =
            (s' : G) * (a * b) * (s' : G)⁻¹ := by group
        rw [e]; exact hσD _ hab
      obtain ⟨z, hzZ, hzeq⟩ : ∃ z ∈ Z, (s' : G) * a * (s' : G)⁻¹ = a * z :=
        ⟨a⁻¹ * ((s' : G) * a * (s' : G)⁻¹), hz, by group⟩
      rw [hzeq] at hDab
      have hcomm : z * ((s' : G) * b * (s' : G)⁻¹) = ((s' : G) * b * (s' : G)⁻¹) * z :=
        Z_central hc.hyp hzZ hb'Q
      have hab'D : a * ((s' : G) * b * (s' : G)⁻¹) ∈ Q ⊓ QB Y := by
        have e : a * ((s' : G) * b * (s' : G)⁻¹) =
            (a * z * ((s' : G) * b * (s' : G)⁻¹)) * z⁻¹ := by
          calc a * ((s' : G) * b * (s' : G)⁻¹)
              = a * (((s' : G) * b * (s' : G)⁻¹) * z) * z⁻¹ := by group
            _ = a * (z * ((s' : G) * b * (s' : G)⁻¹)) * z⁻¹ := by rw [hcomm]
            _ = (a * z * ((s' : G) * b * (s' : G)⁻¹)) * z⁻¹ := by group
        rw [e]
        exact (Q ⊓ QB Y).mul_mem hDab (hZD (Z.inv_mem hzZ))
      have hbb' : b⁻¹ * ((s' : G) * b * (s' : G)⁻¹) ∈ Z := by
        have hmem : b⁻¹ * ((s' : G) * b * (s' : G)⁻¹) ∈ (Q ⊓ QB Y) ⊓ V₂ := by
          refine ⟨?_, V₂.mul_mem (V₂.inv_mem hbV) hb'V₂⟩
          have e : b⁻¹ * ((s' : G) * b * (s' : G)⁻¹) =
              (a * b)⁻¹ * (a * ((s' : G) * b * (s' : G)⁻¹)) := by group
          rw [e]
          exact (Q ⊓ QB Y).mul_mem ((Q ⊓ QB Y).inv_mem hab) hab'D
        rw [hDV₂] at hmem
        exact hmem
      have hb' : ψ₂ ((s' : G) * b * (s' : G)⁻¹) = ψ₂ b := by
        have e : (s' : G) * b * (s' : G)⁻¹ = b * (b⁻¹ * ((s' : G) * b * (s' : G)⁻¹)) := by group
        rw [e, hP.add₂ b hbV _ (V₂.mul_mem (V₂.inv_mem hbV) hb'V₂),
          (hP.ker₂ _ (V₂.mul_mem (V₂.inv_mem hbV) hb'V₂)).mpr hbb', add_zero]
      have hfinal := hP.eq₂ s' b hbV
      rw [hsg, hb'] at hfinal
      rw [coe_tinvGL] at hfinal
      exact hfinal.symm
    have hw0 : ψ₂ b = 0 :=
      eq_zero_of_fixed_dual_stab hn (exists_mu_of_card (by rw [hP.card]; have := hc.hyp.q4; omega))
        hcx hE
    have hbZ : b ∈ Z := (hP.ker₂ b hbV).mp hw0
    have hfin : a ∈ Q ⊓ QB Y := by
      have e : a = (a * b) * b⁻¹ := by group
      rw [e]
      exact (Q ⊓ QB Y).mul_mem hab (hZD (Z.inv_mem hbZ))
    exact hfin.2

end Steps

theorem linModuleStatement_holds : LinModuleStatement := by
  intro G _ _ M Q Z B n V₁ V₂ _ hc hS hn Y hYc hYZ
  refine ⟨fun hYV => ?_, fun hYV => ?_⟩
  · obtain ⟨-, hV₁Q, -, -, -, -, -, -, -, -⟩ := hS.basic
    exact le_QB_of_LinSetup hc hS hn ⟨hc.hyp, hYc, hYV.trans hV₁Q, hYZ⟩ hYV
  · obtain ⟨-, -, -, hV₂Q, -, -, -, -, -, -⟩ := hS.basic
    exact le_QB_of_LinSetup hc hS.symm hn ⟨hc.hyp, hYc, hYV.trans hV₂Q, hYZ⟩ hYV

end CFSG.RankThree.GF2n.Smith81
