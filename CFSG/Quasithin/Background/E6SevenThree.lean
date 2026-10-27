module

public import CFSG.Quasithin.Background.E6TenBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.SBc5SL2 CFSG.Quasithin.SBc5
open scoped commutatorElement IsMulCommutative

section SL2

variable {F : Type} [Field F]

theorem coe_dm' (c : Fˣ) :
    ((dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

theorem coe_xm' (t : F) : ((xm t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem dm_mul' (c c' : Fˣ) : dm c * dm c' = dm (c * c') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dm', coe_dm', coe_dm']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dm_one' : dm (1 : Fˣ) = (1 : SL2 F) := by
  apply Subtype.ext
  rw [coe_dm']
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dm_pow' (c : Fˣ) (j : ℕ) : dm c ^ j = dm (c ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, dm_one']
  | succ j ih => rw [pow_succ, ih, dm_mul', pow_succ]

theorem dm_mulVec_zero (c : Fˣ) (w : Fin 2 → F) :
    ((dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w 0 = (c : F) * w 0 := by
  rw [coe_dm']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_zero_of_xm_one_fixed {w : Fin 2 → F}
    (h : ((xm (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : w 1 = 0 := by
  have h0 := congrFun h 0
  rw [coe_xm'] at h0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  exact h0

theorem sl2_mul_self_eq_one_of_mulVec [CharP F 2] {A : Matrix.SpecialLinearGroup (Fin 2) F}
    {w : Fin 2 → F} (hw : w ≠ 0) (hA : (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w) :
    A * A = 1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have htr : a + d = 0 := by
    have hk0 : ((a - 1) * (d - 1) - b * c) * w 0 = 0 := by
      linear_combination (d - 1) * h0 - b * h1
    have hk1 : ((a - 1) * (d - 1) - b * c) * w 1 = 0 := by
      linear_combination (a - 1) * h1 - c * h0
    have hdet0 : (a - 1) * (d - 1) - b * c = 0 := by
      by_contra hne
      apply hw
      funext i
      fin_cases i
      · exact (mul_eq_zero.1 hk0).resolve_left hne
      · exact (mul_eq_zero.1 hk1).resolve_left hne
    linear_combination -hdet0 + hdet + h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination a * htr - hdet - h2
  · linear_combination b * htr
  · linear_combination c * htr
  · linear_combination d * htr - hdet - h2

end SL2

variable {G : Type} [Group G] [Finite G]

theorem lin2_block_torus'' {T M V K L : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hQK : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K)
    (hQM : T ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hK : CharTwo K) (hL : IsBlock2 K L)
    {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) (hBor : IsBorelOfBlock L (L ⊓ (K ⊓ M)))
    (hVL : ¬ V ≤ Subgroup.centralizer (L : Set G)) :
    (∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)) ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ n ∧
      ∃ x ∈ L ⊓ (K ⊓ M), (∀ j : ℕ,
          x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ n - 1) ∣ j) ∧
        (∀ m ∈ L ⊓ (K ⊓ M), ∃ j : ℕ, m * (x ^ j)⁻¹ ∈ Subgroup.centralizer (V : Set G)) ∧
        (∀ m ∈ L ⊓ (K ⊓ M), m ∈ Subgroup.centralizer (V : Set G) → ∃ k : ℕ, m ^ 2 ^ k = 1) ∧
        ∀ v ∈ V, v ∉ Subgroup.centralizer (L : Set G) → ∀ l ∈ L, v * l = l * v →
          ∃ k : ℕ, l ^ 2 ^ k = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQKM : IsSylowTwoOf Q (K ⊓ M) := A4.isSylowTwoOf_mono hQK (le_inf hQK.1 hQM) inf_le_left
  have hVQ : V ≤ Q := fun v hv => ⟨hVT hv, Subgroup.mem_centralizer_iff.2 fun w hw => by
    have := hV.1
    exact setLike_mul_comm hw hv⟩
  have hLK : L ≤ K := hL.2.1
  have hLs : IsShort2 L := hL.1
  unfold IsBorelOfBlock at hBor
  split_ifs at hBor with h3
  · exact absurd h3 (card_quot_ne_three_of_lin2 hn hlin)
  obtain ⟨P, hP, hBP⟩ := hBor
  have hPL : P ≤ L := hP.1
  have hOL : pCoreOf 2 L ≤ K ⊓ M := by
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 K :=
      Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hLK hL.2.2
    have h2 : pCoreOf 2 K ≤ Q := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQK
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLK) ((h1.trans h2).trans hQM)
  have hNKM : L ⊓ Subgroup.normalizer (P : Set G) ≤ K ⊓ M := by
    rw [← hBP]
    exact sup_le inf_le_right hOL
  have hPKM : P ≤ K ⊓ M := (le_inf hPL Subgroup.le_normalizer).trans hNKM
  have hVP : ∀ v ∈ V, ∀ p ∈ P, v * p = p * v :=
    commute_of_le_of_isPGroup hQKM hKN hPKM hP.2.1
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv =>
    mem_normalizer_of_commute_sylow hK hL hP (hQK.1 (hVQ hv)) (hVP v hv)
  have hQP : pCoreOf 2 L ≤ P := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hUP : blockU L ≤ P := (C1.blockU_le_blockQ hLs).trans hQP
  have hVU : ∀ v ∈ V, ∀ u ∈ blockU L, v * u = u * v := fun v hv u hu => hVP v hv u (hUP hu)
  have hUc : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hLs).1
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  obtain ⟨F, hFfield, hFfin, hFcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hFfinite : Finite F := Finite.of_fintype F
  have hcardF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFcard]
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hcardF
  have hker : ∀ x : ↥L, x ∈ α.ker ↔ (x : G) ∈ pCoreOf 2 L := fun x => by
    rw [hαk]
    exact AppC.mem_pCore_iff_mem_blockQ x
  have hσmem : ∀ v ∈ V, ∀ l : ↥L, v * (l : G) * v⁻¹ ∈ L := fun v hv l =>
    (Subgroup.mem_normalizer_iff.mp (hVN v hv) l).1 l.2
  have hαv : ∀ v (hv : v ∈ V) (l : ↥L), α ⟨v * l * v⁻¹, hσmem v hv l⟩ = α l := by
    intro v hv l
    set l' : ↥L := ⟨v * l * v⁻¹, hσmem v hv l⟩ with hl'
    have hmv : ∀ w : Fin 2 → F, ((α l' : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w =
        ((α l : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w := by
      intro w
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
      have hlu : (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (hLU l.2) u).1 u.2
      have h1 := hβe l u ⟨_, hlu⟩ rfl
      have hvu : v⁻¹ * (u : G) * v = u := by
        rw [mul_assoc, ← hVU v hv u u.2, inv_mul_cancel_left]
      have hvlu : v * ((l : G) * u * (l : G)⁻¹) * v⁻¹ = (l : G) * u * (l : G)⁻¹ := by
        rw [hVU v hv _ hlu, mul_inv_cancel_right]
      have h2 := hβe l' u ⟨_, hlu⟩ (by
        show (l : G) * u * (l : G)⁻¹ = v * l * v⁻¹ * u * (v * l * v⁻¹)⁻¹
        calc (l : G) * u * (l : G)⁻¹ = v * ((l : G) * u * (l : G)⁻¹) * v⁻¹ := hvlu.symm
          _ = v * l * (v⁻¹ * (u : G) * v) * (l : G)⁻¹ * v⁻¹ := by rw [hvu]; group
          _ = v * l * v⁻¹ * u * (v * l * v⁻¹)⁻¹ := by group)
      rw [hu, toAdd_ofAdd] at h1 h2
      rw [← h1, ← h2]
    apply Subtype.ext
    ext i j
    have := congrFun (hmv (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  have hzU : ∀ v ∈ V, ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ blockU L := by
    intro v hv
    refine C1.commutator_mem_blockU_of_mem_blockQ hLs fun l hl => ?_
    have h1 : (⟨v * l * v⁻¹, hσmem v hv ⟨l, hl⟩⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαv v hv ⟨l, hl⟩, mul_inv_cancel]
    exact (hker _).1 h1
  have hinner : ∀ v ∈ V, ∃ b ∈ blockU L, ∀ l ∈ L, v * l * v⁻¹ = b * l * b⁻¹ := by
    intro v hv
    set A := blockU L with hAdef
    have hAc : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hUc a a.2 b b.2)⟩⟩
    let ρ : ↥L →* MulAut A := (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hLU)
    have hρ : ∀ (x : ↥L) (a : A), ((ρ x a : A) : G) = x * a * (x : G)⁻¹ := fun x a => rfl
    let d : ↥L → A := fun x => ⟨v * x * v⁻¹ * (x : G)⁻¹, hzU v hv x x.2⟩
    have hd : ∀ x y, d (x * y) = d x * ρ x (d y) := by
      intro x y
      apply Subtype.ext
      change v * ((x : G) * y) * v⁻¹ * ((x : G) * y)⁻¹ =
        (v * x * v⁻¹ * (x : G)⁻¹) * ((x : G) * (v * y * v⁻¹ * (y : G)⁻¹) * (x : G)⁻¹)
      group
    have hS : ∀ x, ∀ s ∈ P.subgroupOf L, d (x * s) = d x := by
      intro x s hs
      apply Subtype.ext
      have hsP : (s : G) ∈ P := hs
      change v * ((x : G) * s) * v⁻¹ * ((x : G) * s)⁻¹ = v * x * v⁻¹ * (x : G)⁻¹
      have hvs : v * (s : G) * v⁻¹ = s := by rw [hVP v hv s hsP, mul_inv_cancel_right]
      calc v * ((x : G) * s) * v⁻¹ * ((x : G) * s)⁻¹
          = v * x * v⁻¹ * (v * (s : G) * v⁻¹) * (s : G)⁻¹ * (x : G)⁻¹ := by group
        _ = v * x * v⁻¹ * (x : G)⁻¹ := by rw [hvs]; group
    have hA2 : IsPGroup 2 A := (C1.blockQ_isPGroup L).to_le (C1.blockU_le_blockQ hLs)
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    have hcop : Nat.Coprime (Nat.card A) (P.subgroupOf L).index := by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hP.2.2)
    obtain ⟨b, hb⟩ := Ch1.SporAut.cocycle_coboundary_of_coprime ρ (P.subgroupOf L) hcop d hd hS
    refine ⟨b, b.2, fun l hl => ?_⟩
    have h := congrArg (fun a : A => (a : G)) (hb ⟨l, hl⟩)
    simp only [d, Subgroup.coe_mul, Subgroup.coe_inv, hρ] at h
    calc v * l * v⁻¹ = (v * l * v⁻¹ * l⁻¹) * l := by group
      _ = (b : G) * (l * (b : G) * l⁻¹)⁻¹ * l := by rw [h]
      _ = (b : G) * l * (b : G)⁻¹ := by group
  set P' : Subgroup ↥L := P.subgroupOf L with hP'def
  have hP' : IsSylowTwoOf P' (⊤ : Subgroup ↥L) := isSylowTwoOf_subgroupOf_top hP
  have hkerP' : α.ker ≤ P' := fun x hx => hQP ((hker x).1 hx)
  have hPbar : IsSylowTwoOf (P'.map α) (⊤ : Subgroup (SL2 F)) :=
    isSylowTwoOf_map_surjective α hαs hP'
  have hUp : IsSylowTwoOf (Uplus F) (⊤ : Subgroup (SL2 F)) := isSylowTwoOf_Uplus (by omega) hcardF
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hUp hPbar
  let c : SL2 F →* SL2 F := (MulAut.conj g⁻¹).toMonoidHom
  have hc_apply : ∀ x : SL2 F, c x = g⁻¹ * x * g := fun x => by
    simp [c]
  let α₁ : ↥L →* SL2 F := c.comp α
  have hα₁s : Function.Surjective α₁ := (MulAut.conj g⁻¹).surjective.comp hαs
  have hα₁k : α₁.ker = α.ker := by
    ext x
    simp only [MonoidHom.mem_ker, α₁, MonoidHom.comp_apply, hc_apply]
    constructor
    · intro h
      have := congrArg (fun y => g * y * g⁻¹) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  have hα₁P : P'.map α₁ = Uplus F := by
    have e : P'.map α₁ = (P'.map α).map c := (Subgroup.map_map _ _ _).symm
    rw [e, hg]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hc_apply]
      exact B6.mem_conjSub.mp hx
    · intro hy
      refine ⟨g * y * g⁻¹, B6.mem_conjSub.mpr (by
        have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rw [e]
        exact hy), ?_⟩
      rw [hc_apply]
      group
  have hα₁B : (Subgroup.normalizer (P' : Set ↥L)).map α₁ = Tplus F := by
    have := map_normalizer_eq_of_ker_le α₁ hα₁s (hα₁k ▸ hkerP')
    rw [this, hα₁P, normalizer_Uplus]
  have hgg : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have hα₁coe : ∀ l : ↥L, ((α₁ l : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) := fun l => by
    show ((c (α l) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hc_apply]
    simp [Matrix.SpecialLinearGroup.coe_mul]
  let β₁ : ↥(blockU L) → (Fin 2 → F) := fun u =>
    ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))
  have hβ₁mul : ∀ u u' : ↥(blockU L), β₁ (u * u') = β₁ u + β₁ u' := by
    intro u u'
    simp only [β₁, map_mul, toAdd_mul, Matrix.mulVec_add]
  have hβ₁e : ∀ (l : ↥L) (u u' : ↥(blockU L)), (u' : G) = l * u * (l : G)⁻¹ →
      β₁ u' = ((α₁ l : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (β₁ u) := by
    intro l u u' h
    have e : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.mul_assoc _ ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F), hgg, Matrix.mul_one]
    simp only [β₁]
    rw [hβe l u u' h, hα₁coe, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  have hβ₁zero : ∀ u : ↥(blockU L), β₁ u = 0 → (u : G) ∈ blockZ L := by
    intro u hu
    have h1 : Multiplicative.toAdd (β u) = 0 := by
      have := congrArg (fun w => ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w) hu
      simp only [β₁, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    have h2 : u ∈ β.ker := toAdd_eq_zero.mp h1
    rw [hβk] at h2
    exact h2
  obtain ⟨p₁, hp₁, hp₁e⟩ : ∃ p ∈ P', α₁ p = xm (1 : F) := by
    have : xm (1 : F) ∈ P'.map α₁ := hα₁P ▸ xm_mem_Uplus 1
    obtain ⟨p, hp, e⟩ := this
    exact ⟨p, hp, e⟩
  have hfix : ∀ b : ↥(blockU L), (∀ p ∈ P, (b : G) * p = p * b) → β₁ b 1 = 0 := by
    intro b hb
    apply eq_zero_of_xm_one_fixed
    rw [← hp₁e]
    refine (hβ₁e p₁ b b ?_).symm
    have hpP : (p₁ : G) ∈ P := hp₁
    rw [← hb p₁ hpP, mul_inv_cancel_right]
  set R : G → ↥(blockU L) → Prop := fun v b => ∀ l ∈ L, v * l * v⁻¹ = (b : G) * l * (b : G)⁻¹
    with hRdef
  have hR1 : ∀ v ∈ V, ∃ b, R v b := fun v hv => by
    obtain ⟨b, hb, hbl⟩ := hinner v hv
    exact ⟨⟨b, hb⟩, hbl⟩
  have hRP : ∀ v ∈ V, ∀ b, R v b → ∀ p ∈ P, (b : G) * p = p * b := by
    intro v hv b hb p hp
    have h1 := hb p (hPL hp)
    have h2 : v * p * v⁻¹ = p := by rw [hVP v hv p hp, mul_inv_cancel_right]
    rw [h2] at h1
    calc (b : G) * p = ((b : G) * p * (b : G)⁻¹) * b := by group
      _ = p * b := by rw [← h1]
  have hRuniq : ∀ v b b', R v b → R v b' → β₁ b = β₁ b' := by
    intro v b b' hb hb'
    have hz : ((b⁻¹ * b' : ↥(blockU L)) : G) ∈ blockZ L := by
      refine ⟨(b⁻¹ * b').2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := hb l hl
      have h2 := hb' l hl
      show l * ((b : G)⁻¹ * b') = (b : G)⁻¹ * b' * l
      have h3 : (b : G) * l * (b : G)⁻¹ = (b' : G) * l * (b' : G)⁻¹ := h1.symm.trans h2
      calc l * ((b : G)⁻¹ * b') = (b : G)⁻¹ * ((b : G) * l * (b : G)⁻¹) * b' := by group
        _ = (b : G)⁻¹ * ((b' : G) * l * (b' : G)⁻¹) * b' := by rw [h3]
        _ = (b : G)⁻¹ * b' * l := by group
    have h1 : β (b⁻¹ * b') = 1 := by
      have : (b⁻¹ * b') ∈ (blockZ L).subgroupOf (blockU L) := hz
      rw [← hβk] at this
      exact this
    have h2 : β₁ (b⁻¹ * b') = 0 := by
      simp only [β₁, h1, toAdd_one, Matrix.mulVec_zero]
    have h3 := hβ₁mul b (b⁻¹ * b')
    rw [mul_inv_cancel_left, h2, add_zero] at h3
    exact h3.symm
  have hRmul : ∀ v ∈ V, ∀ w ∈ V, ∀ b b', R v b → R w b' → R (v * w) (b' * b) := by
    intro v hv w hw b b' hb hb' l hl
    have hb'v : v * (b' : G) * v⁻¹ = b' := by rw [hVU v hv b' b'.2, mul_inv_cancel_right]
    have hw' := hb' l hl
    calc v * w * l * (v * w)⁻¹ = v * (w * l * w⁻¹) * v⁻¹ := by group
      _ = v * ((b' : G) * l * (b' : G)⁻¹) * v⁻¹ := by rw [hw']
      _ = (v * (b' : G) * v⁻¹) * (v * l * v⁻¹) * (v * (b' : G) * v⁻¹)⁻¹ := by group
      _ = (b' : G) * ((b : G) * l * (b : G)⁻¹) * (b' : G)⁻¹ := by rw [hb'v, hb l hl]
      _ = ((b' * b : ↥(blockU L)) : G) * l * ((b' * b : ↥(blockU L)) : G)⁻¹ := by
        simp only [Subgroup.coe_mul]; group
  have hRcent : ∀ v b, R v b → (β₁ b = 0 ↔ v ∈ Subgroup.centralizer (L : Set G)) := by
    intro v b hb
    constructor
    · intro h0
      have hz := hβ₁zero b h0
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hb l hl
      have hbl : (b : G) * l * (b : G)⁻¹ = l := by
        rw [← (Subgroup.mem_centralizer_iff.1 hz.2 l hl), mul_inv_cancel_right]
      rw [hbl] at h1
      calc l * v = (v * l * v⁻¹) * v := by rw [h1]
        _ = v * l := by group
    · intro hvC
      have hbz : (b : G) ∈ blockZ L := ⟨b.2, Subgroup.mem_centralizer_iff.2 fun l hl => by
        have h1 := hb l hl
        have h2 : v * l * v⁻¹ = l := by
          rw [← Subgroup.mem_centralizer_iff.1 hvC l hl, mul_inv_cancel_right]
        rw [h2] at h1
        calc l * (b : G) = ((b : G) * l * (b : G)⁻¹) * b := by rw [← h1]
          _ = (b : G) * l := by group⟩
      have h1 : β b = 1 := by
        have : b ∈ (blockZ L).subgroupOf (blockU L) := hbz
        rw [← hβk] at this
        exact this
      simp only [β₁, h1, toAdd_one, Matrix.mulVec_zero]
  have hRconj : ∀ v b, R v b → ∀ m : ↥L,
      R ((m : G) * v * (m : G)⁻¹) ⟨(m : G) * b * (m : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLU m.2) b).1 b.2⟩ := by
    intro v b hb m l hl
    have hml : (m : G)⁻¹ * l * m ∈ L := L.mul_mem (L.mul_mem (L.inv_mem m.2) hl) m.2
    have h1 := hb _ hml
    calc (m : G) * v * (m : G)⁻¹ * l * ((m : G) * v * (m : G)⁻¹)⁻¹
        = m * (v * ((m : G)⁻¹ * l * m) * v⁻¹) * (m : G)⁻¹ := by group
      _ = m * ((b : G) * ((m : G)⁻¹ * l * m) * (b : G)⁻¹) * (m : G)⁻¹ := by rw [h1]
      _ = ((m : G) * b * (m : G)⁻¹) * l * ((m : G) * b * (m : G)⁻¹)⁻¹ := by group
  choose! bv hbv using hR1
  let σ : ↥V →* Multiplicative F :=
    { toFun := fun v => Multiplicative.ofAdd (β₁ (bv v) 0)
      map_one' := by
        have h1 : R 1 1 := fun l _ => by simp
        show Multiplicative.ofAdd (β₁ (bv (1 : G)) 0) = 1
        rw [hRuniq 1 _ _ (hbv 1 V.one_mem) h1]
        simp [β₁]
      map_mul' := fun v w => by
        have h1 := hRmul v v.2 w w.2 _ _ (hbv v v.2) (hbv w w.2)
        rw [← ofAdd_add]
        congr 1
        show β₁ (bv ((v : G) * w)) 0 = β₁ (bv v) 0 + β₁ (bv w) 0
        rw [hRuniq _ _ _ (hbv _ (V.mul_mem v.2 w.2)) h1, hβ₁mul, add_comm]
        rfl }
  have hσ : ∀ v : ↥V, Multiplicative.toAdd (σ v) = β₁ (bv v) 0 := fun v => rfl
  have hσker : ∀ v : ↥V, σ v = 1 ↔ (v : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro v
    rw [← hRcent v _ (hbv v v.2)]
    constructor
    · intro h
      have h0 : β₁ (bv v) 0 = 0 := by rw [← hσ v, h, toAdd_one]
      funext i
      fin_cases i
      · exact h0
      · exact hfix _ (hRP v v.2 _ (hbv v v.2))
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hσ v, h, toAdd_one]
      rfl
  have hσconj : ∀ v : ↥V, ∀ m : ↥L, (m : G) ∈ Subgroup.normalizer (V : Set G) →
      ∀ c' : Fˣ, α₁ m = dm c' →
        β₁ (bv ((m : G) * v * (m : G)⁻¹)) 0 = (c' : F) * β₁ (bv v) 0 := by
    intro v m hmN c' hm
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmN v).1 v.2
    have h1 := hRconj v _ (hbv v v.2) m
    rw [hRuniq _ _ _ (hbv _ hmv) h1, hβ₁e m (bv v) _ rfl, hm, dm_mulVec_zero]
  have hdiag : ∀ c' : Fˣ, ∃ m : ↥L, (m : G) ∈ K ⊓ M ∧ α₁ m = dm c' := by
    intro c'
    have : dm c' ∈ (Subgroup.normalizer (P' : Set ↥L)).map α₁ := hα₁B ▸ dm_mem_Tplus c'
    obtain ⟨y, hy, hye⟩ := this
    have hyN : (y : G) ∈ L ⊓ Subgroup.normalizer (P : Set G) :=
      ⟨y.2, (mem_normalizer_subgroupOf_iff hPL).1 hy⟩
    rw [← hBP] at hyN
    have hLKMN : L ⊓ (K ⊓ M) ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
      inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLKMN] at hyN
    obtain ⟨m, hm, o, ho, hmo⟩ := hyN
    have hoL : o ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L ho
    refine ⟨⟨m, hm.1⟩, hm.2, ?_⟩
    have hyo : y = ⟨m, hm.1⟩ * ⟨o, hoL⟩ := Subtype.ext hmo.symm
    have hok : (⟨o, hoL⟩ : ↥L) ∈ α₁.ker := by rw [hα₁k, hker]; exact ho
    rw [hyo, map_mul, MonoidHom.mem_ker.1 hok, mul_one] at hye
    exact hye
  obtain ⟨v₁, hv₁, hv₁C⟩ := Set.not_subset.1 hVL
  have hs₁ : β₁ (bv v₁) 0 ≠ 0 := by
    intro h0
    apply hv₁C
    have := (hσker ⟨v₁, hv₁⟩).1 (by
      apply Multiplicative.toAdd.injective
      rw [hσ, toAdd_one]
      exact h0)
    exact this
  have hσsurj : Function.Surjective σ := by
    intro f
    by_cases hf : Multiplicative.toAdd f = 0
    · refine ⟨1, ?_⟩
      rw [map_one]
      apply Multiplicative.toAdd.injective
      rw [hf, toAdd_one]
    · set c' : Fˣ := Units.mk0 (Multiplicative.toAdd f / β₁ (bv v₁) 0) (div_ne_zero hf hs₁)
      obtain ⟨m, hmKM, hm⟩ := hdiag c'
      have hmN : (m : G) ∈ Subgroup.normalizer (V : Set G) := hKN hmKM
      have hmv : (m : G) * v₁ * (m : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmN v₁).1 hv₁
      refine ⟨⟨_, hmv⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hσ]
      have := hσconj ⟨v₁, hv₁⟩ m hmN c' hm
      simp only at this
      rw [this]
      simp only [c', Units.val_mk0]
      field_simp
  have hkerσ : σ.ker = (V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, hσker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ n := by
    rw [Subgroup.relIndex, ← hkerσ, Subgroup.index_ker, MonoidHom.range_eq_top.2 hσsurj,
      Subgroup.card_top]
    exact hcardF
  refine ⟨hVN, hidx, ?_⟩
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hc₀ord : orderOf c₀ = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc₀, Nat.card_units, hcardF]
  obtain ⟨m₀, hm₀KM, hm₀⟩ := hdiag c₀
  have hm₀N : (m₀ : G) ∈ Subgroup.normalizer (V : Set G) := hKN hm₀KM
  have hpow : ∀ j : ℕ, α₁ (m₀ ^ j) = dm (c₀ ^ j) := fun j => by rw [map_pow, hm₀, dm_pow']
  have hxj : ∀ j : ℕ, (m₀ : G) ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ n - 1) ∣ j := by
    intro j
    constructor
    · intro hj
      have hjN : ((m₀ ^ j : ↥L) : G) ∈ Subgroup.normalizer (V : Set G) := by
        rw [Subgroup.coe_pow]
        exact Subgroup.pow_mem _ hm₀N j
      have h1 := hσconj ⟨v₁, hv₁⟩ (m₀ ^ j) hjN (c₀ ^ j) (hpow j)
      have hfixv : ((m₀ ^ j : ↥L) : G) * v₁ * ((m₀ ^ j : ↥L) : G)⁻¹ = v₁ := by
        rw [Subgroup.coe_pow]
        have := Subgroup.mem_centralizer_iff.1 hj v₁ hv₁
        rw [← this, mul_inv_cancel_right]
      simp only at h1
      rw [hfixv] at h1
      have h2 : ((c₀ ^ j : Fˣ) : F) = 1 := by
        have h3 : (1 : F) * β₁ (bv v₁) 0 = ((c₀ ^ j : Fˣ) : F) * β₁ (bv v₁) 0 := by
          rw [one_mul]; exact h1
        exact (mul_right_cancel₀ hs₁ h3).symm
      have h4 : c₀ ^ j = 1 := Units.ext h2
      rw [← hc₀ord]
      exact orderOf_dvd_of_pow_eq_one h4
    · intro hj
      have h1 : c₀ ^ j = 1 := by
        rw [← hc₀ord] at hj
        exact orderOf_dvd_iff_pow_eq_one.1 hj
      have h2 : m₀ ^ j ∈ α₁.ker := by rw [MonoidHom.mem_ker, hpow j, h1, dm_one']
      rw [hα₁k, hker] at h2
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := hVP v hv _ (hQP h2)
      rwa [Subgroup.coe_pow] at this
  have hallP : ∀ m ∈ L ⊓ (K ⊓ M), ∃ j : ℕ, m * ((m₀ : G) ^ j)⁻¹ ∈ P := by
    intro m hm
    have hmB : m ∈ L ⊓ Subgroup.normalizer (P : Set G) := by
      rw [← hBP]
      exact Subgroup.mem_sup_left hm
    have hm'N : (⟨m, hm.1⟩ : ↥L) ∈ Subgroup.normalizer (P' : Set ↥L) :=
      (mem_normalizer_subgroupOf_iff hPL).2 hmB.2
    have hT : α₁ ⟨m, hm.1⟩ ∈ Tplus F := by
      rw [← hα₁B]
      exact Subgroup.mem_map_of_mem α₁ hm'N
    obtain ⟨t, c, hc⟩ := mem_Tplus_iff.1 hT
    obtain ⟨j, hj⟩ : ∃ j : ℕ, c₀ ^ j = c := by
      have hcz : c ∈ Subgroup.zpowers c₀ := hc₀ c
      rw [← mem_powers_iff_mem_zpowers] at hcz
      exact (Submonoid.mem_powers_iff c c₀).1 hcz
    refine ⟨j, ?_⟩
    have hu : α₁ (⟨m, hm.1⟩ * (m₀ ^ j)⁻¹) ∈ Uplus F := by
      rw [map_mul, map_inv, hpow j, hj, hc, mul_inv_cancel_right]
      exact xm_mem_Uplus t
    rw [← hα₁P] at hu
    obtain ⟨p, hp, hpe⟩ := hu
    have hk : p⁻¹ * (⟨m, hm.1⟩ * (m₀ ^ j)⁻¹) ∈ α₁.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpe, inv_mul_cancel]
    rw [hα₁k] at hk
    have hmP : (⟨m, hm.1⟩ : ↥L) * (m₀ ^ j)⁻¹ ∈ P' := by
      have := P'.mul_mem hp (hkerP' hk)
      rwa [mul_inv_cancel_left] at this
    have : (((⟨m, hm.1⟩ : ↥L) * (m₀ ^ j)⁻¹ : ↥L) : G) ∈ P := hmP
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using this
  refine ⟨m₀, ⟨m₀.2, hm₀KM⟩, hxj, fun m hm => ?_, fun m hm hmC => ?_, fun v hv hvC l hl hvl => ?_⟩
  ·
    obtain ⟨j, hj⟩ := hallP m hm
    refine ⟨j, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hVP v hv _ hj
  ·
    obtain ⟨j, hj⟩ := hallP m hm
    have hjC' : m * ((m₀ : G) ^ j)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun v hv => hVP v hv _ hj
    have hjC : (m₀ : G) ^ j ∈ Subgroup.centralizer (V : Set G) := by
      have he : (m₀ : G) ^ j = (m * ((m₀ : G) ^ j)⁻¹)⁻¹ * m := by group
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjC') hmC
    have hdvd := (hxj j).1 hjC
    have h1 : c₀ ^ j = 1 := by
      rw [← hc₀ord] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    have h2 : m₀ ^ j ∈ α₁.ker := by rw [MonoidHom.mem_ker, hpow j, h1, dm_one']
    rw [hα₁k, hker] at h2
    have h3 : (m₀ : G) ^ j ∈ P := by
      have := hQP h2
      rwa [Subgroup.coe_pow] at this
    have hmP : m ∈ P := by
      have he : m = (m * ((m₀ : G) ^ j)⁻¹) * (m₀ : G) ^ j := by group
      rw [he]
      exact P.mul_mem hj h3
    obtain ⟨k, hk⟩ := hP.2.1 ⟨m, hmP⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  ·
    have hb := hbv v hv
    have hb0 : β₁ (bv v) ≠ 0 := fun h0 => hvC ((hRcent v (bv v) hb).1 h0)
    have hlb : ((bv v : ↥(blockU L)) : G) * l * ((bv v : ↥(blockU L)) : G)⁻¹ = l := by
      rw [← hb l hl, hvl, mul_inv_cancel_right]
    have hlb' : l * ((bv v : ↥(blockU L)) : G) * l⁻¹ = (bv v : ↥(blockU L)) := by
      have h1 : ((bv v : ↥(blockU L)) : G) * l = l * (bv v : ↥(blockU L)) := by
        calc ((bv v : ↥(blockU L)) : G) * l
            = (((bv v : ↥(blockU L)) : G) * l * ((bv v : ↥(blockU L)) : G)⁻¹) *
                (bv v : ↥(blockU L)) := by group
          _ = l * (bv v : ↥(blockU L)) := by rw [hlb]
      rw [← h1, mul_inv_cancel_right]
    have hfixw : ((α₁ ⟨l, hl⟩ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (β₁ (bv v)) =
        β₁ (bv v) := (hβ₁e ⟨l, hl⟩ (bv v) (bv v) hlb'.symm).symm
    have hsq := sl2_mul_self_eq_one_of_mulVec hb0 hfixw
    have h2 : (⟨l, hl⟩ : ↥L) ^ 2 ∈ α₁.ker := by
      rw [MonoidHom.mem_ker, pow_two, map_mul, hsq]
    rw [hα₁k, hker] at h2
    obtain ⟨k, hk⟩ := hP.2.1 ⟨_, hQP h2⟩
    refine ⟨k + 1, ?_⟩
    have h3 := congrArg Subtype.val hk
    simp only [SubmonoidClass.mk_pow, Subgroup.coe_one, Subgroup.coe_mk] at h3
    rw [pow_succ', pow_mul]
    exact h3

theorem lin2_block_torus' {T M V K L : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hQK : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K)
    (hQM : T ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hK : CharTwo K) (hL : IsBlock2 K L)
    {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) (hBor : IsBorelOfBlock L (L ⊓ (K ⊓ M)))
    (hVL : ¬ V ≤ Subgroup.centralizer (L : Set G)) :
    (∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)) ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ n ∧
      ∃ x ∈ L ⊓ (K ⊓ M), (∀ j : ℕ,
          x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ n - 1) ∣ j) ∧
        ∀ m ∈ L ⊓ (K ⊓ M), ∃ j : ℕ, m * (x ^ j)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hVN, hidx, x, hx, hxj, hall, -⟩ :=
    lin2_block_torus'' hV hVT hQK hQM hKN hK hL hn hlin hBor hVL
  exact ⟨hVN, hidx, x, hx, hxj, hall⟩

theorem lin2_block_torus {T M V K L : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hQK : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K)
    (hQM : T ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hK : CharTwo K) (hL : IsBlock2 K L)
    {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) (hBor : IsBorelOfBlock L (L ⊓ (K ⊓ M)))
    (hVL : ¬ V ≤ Subgroup.centralizer (L : Set G)) :
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ n ∧
      ∃ x ∈ L ⊓ (K ⊓ M), ∀ j : ℕ,
        x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ n - 1) ∣ j := by
  obtain ⟨-, hidx, x, hx, hxj, -⟩ :=
    lin2_block_torus' hV hVT hQK hQM hKN hK hL hn hlin hBor hVL
  exact ⟨hidx, x, hx, hxj⟩

end E6
end CFSG.Quasithin
