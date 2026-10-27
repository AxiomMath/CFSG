module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.G2SixCore
public import CFSG.Quasithin.Background.G13Two
import CFSG.Open.MatrixFixedVectors
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Vol2.Ch5ModulesFFGrp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups

theorem card_fixed_mulVec_le {F : Type} [Field F] [Finite F] {M : Matrix (Fin 2) (Fin 2) F}
    (hM : M ≠ 1) : Nat.card {w : Fin 2 → F // M.mulVec w = w} ≤ Nat.card F :=
  CFSG.Open.StatedAPI.card_mulVec_fixed_le hM

theorem card_eq_card_range_mul_card_ker {C Q : Type*} [Group C] [Group Q] [Finite C]
    (f : C →* Q) : Nat.card C = Nat.card f.range * Nat.card f.ker := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem card_natSec (F : Type) [Field F] [Finite F] (d : ℕ) :
    Nat.card (↥(FFModel.nat (StatedSL d F)).sec ⧸
      (FFModel.nat (StatedSL d F)).ker.subgroupOf (FFModel.nat (StatedSL d F)).sec) =
      Nat.card F ^ d := by
  show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin d → F))) ⧸
    (⊥ : Subgroup (Multiplicative (Fin d → F))).subgroupOf ⊤) = _
  rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
    Subgroup.card_top]
  show Nat.card (Fin d → F) = _
  rw [Nat.card_fun, Nat.card_fin]

section Natural

variable {V : Type} [CommGroup V] [Finite V]

theorem card_sec_of_binaryNaturalSL {H : Subgroup (MulAut V)} {U Z : Subgroup V} {d a : ℕ}
    (h : BinaryNaturalSL H U Z d a) : Nat.card U = (2 ^ a) ^ d * Nat.card Z := by
  obtain ⟨F, _, _, hF, π, -, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have h1 := card_eq_card_range_mul_card_ker β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top] at h1
  have hk : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, card_natSec, hF] at h1
  exact h1

theorem card_le_of_fixed_natural {K : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSL K U Z 2 n) {a : MulAut V} (haK : a ∈ K) (ha1 : a ≠ 1)
    {C : Subgroup V} (hCU : C ≤ U) (hCa : ∀ c ∈ C, a c = c) :
    Nat.card C ≤ 2 ^ n * Nat.card ↥(C ⊓ Z) := by
  obtain ⟨F, _, _, hF, π, hπs, -, -, hUinv, -, -, -, β, -, hβk, hβe⟩ := h
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 2 F), π γ = ⟨a, haK⟩ := hπs ⟨a, haK⟩
  have hγa : ((π γ : ↥K) : MulAut V) = a := congrArg Subtype.val hγ
  set M : Matrix (Fin 2) (Fin 2) F := ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hM1 : M ≠ 1 := by
    intro h1
    apply ha1
    have hγ1 : γ = 1 := Subtype.ext (Units.ext h1)
    rw [← hγa, hγ1]
    exact congrArg Subtype.val (map_one π)
  have hmk : ∀ m₁ m₂ : ↥(FFModel.nat (StatedSL 2 F)).sec,
      (QuotientGroup.mk m₁ : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
        (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec) =
        QuotientGroup.mk m₂ → m₁ = m₂ := by
    intro m₁ m₂ h12
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h12
    exact inv_mul_eq_one.mp (Subtype.ext (Subgroup.mem_bot.mp h12))
  let f := β.comp (Subgroup.inclusion hCU)
  have hfix : ∀ (c : ↥C) (m : ↥(FFModel.nat (StatedSL 2 F)).sec), f c = QuotientGroup.mk m →
      M.mulVec (Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1)) =
        Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1) := by
    intro c m hm
    have hu : ((π γ : ↥K) : MulAut V) ((Subgroup.inclusion hCU c : ↥U) : V) ∈ U :=
      hUinv (π γ) _ (Subgroup.inclusion hCU c).2
    have key := hβe γ (Subgroup.inclusion hCU c) m hu (Subgroup.mem_top _) hm
    have hac : (⟨((π γ : ↥K) : MulAut V) ((Subgroup.inclusion hCU c : ↥U) : V), hu⟩ : ↥U) =
        Subgroup.inclusion hCU c := by
      apply Subtype.ext
      show ((π γ : ↥K) : MulAut V) (c : V) = c
      rw [hγa]
      exact hCa c c.2
    rw [hac] at key
    have h2 := hmk _ _ (hm.symm.trans key)
    have h3 := congrArg
      (fun x : ↥(FFModel.nat (StatedSL 2 F)).sec =>
        Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from x.1)) h2
    exact h3.symm
  have hker : f.ker = Z.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk _
  have hrange : Nat.card f.range ≤ 2 ^ n := by
    classical
    have hsel : ∀ q : ↥f.range, ∃ w : {w : Fin 2 → F // M.mulVec w = w},
        (q : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
          (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec) =
          QuotientGroup.mk (⟨Multiplicative.ofAdd w.1, Subgroup.mem_top _⟩ :
            ↥(FFModel.nat (StatedSL 2 F)).sec) := by
      rintro ⟨q, c, rfl⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (f c)
      refine ⟨⟨Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1),
        hfix c m hm.symm⟩, ?_⟩
      show f c = _
      exact hm.symm.trans rfl
    choose g hg using hsel
    have hginj : Function.Injective g := by
      intro q₁ q₂ h12
      apply Subtype.ext
      rw [hg q₁, hg q₂, h12]
    calc Nat.card f.range ≤ Nat.card {w : Fin 2 → F // M.mulVec w = w} :=
          Nat.card_le_card_of_injective g hginj
      _ ≤ Nat.card F := card_fixed_mulVec_le hM1
      _ = 2 ^ n := hF
  have hZC : Nat.card ↥(Z.subgroupOf C) = Nat.card ↥(C ⊓ Z) := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  calc Nat.card C = Nat.card f.range * Nat.card f.ker := card_eq_card_range_mul_card_ker f
    _ ≤ 2 ^ n * Nat.card ↥(C ⊓ Z) := by
      rw [hker, hZC]
      exact Nat.mul_le_mul_right _ hrange

theorem inv_mul_e12_mul_mem_Rg {F : Type} [Field F] (k : SL(2, F)) (hk : k.1 1 0 = 0) (c : F) :
    k⁻¹ * e12 c * k ∈ Rg F := by
  have hdet : k.1 0 0 * k.1 1 1 = 1 := by
    have := det_eq_one' k
    rw [hk, mul_zero, sub_zero] at this
    exact this
  refine mem_Rg.2 ⟨c * k.1 1 1 ^ 2, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, e12_coe]
  rw [Matrix.eta_fin_two (k.1), Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hk] <;>
    first | linear_combination hdet | linear_combination (-1 : F) * hdet | ring

omit [Finite V] in
theorem apply_comm_eq_of_sq {a : MulAut V} (hV : ∀ v : V, v ^ 2 = 1) (ha : a ^ 2 = 1) (v : V) :
    a (a v * v⁻¹) = a v * v⁻¹ := by
  have ha2 : a * a = 1 := by rwa [pow_two] at ha
  have haa : a (a v) = v := by rw [← MulAut.mul_apply, ha2, MulAut.one_apply]
  have hinv2 : ∀ w : V, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV w)
  calc a (a v * v⁻¹) = a (a v) * (a v)⁻¹ := by rw [map_mul, map_inv]
    _ = v * (a v)⁻¹ := by rw [haa]
    _ = (a v * v⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    _ = a v * v⁻¹ := hinv2 _

omit [Finite V] in
theorem mem_fixV_zpowers_iff {a : MulAut V} {w : V} :
    w ∈ fixV (Subgroup.zpowers a) ↔ a w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite V] in
theorem binaryNaturalSL_of_equivariant {K : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (σ' : SL(2, F) →* ↥K) (hσ' : Function.Surjective σ')
    (Θ : (Fin 2 → Fin 2 → F) ≃+ Additive V)
    (hΘ : ∀ (h : SL(2, F)) (x : Fin 2 → Fin 2 → F),
      Θ (fun j => (h : Matrix (Fin 2) (Fin 2) F).mulVec (x j)) =
        Additive.ofMul (((σ' h : ↥K) : MulAut V) (Additive.toMul (Θ x))))
    (i : Fin 2) (W : Subgroup V)
    (hW : ∀ v : V, v ∈ W ↔ ∃ x : Fin 2 → F, Additive.ofMul v = Θ (Pi.single i x)) :
    BinaryNaturalSL K W ⊥ 2 n := by
  classical
  set eS := specialLinearGroupEquivStatedSL 2 F with heS
  let π' : ↥(StatedSL 2 F) →* ↥K := σ'.comp eS.symm.toMonoidHom
  have hcoord : ∀ v ∈ W,
      Additive.ofMul v = Θ (Pi.single i ((Θ.symm (Additive.ofMul v)) i)) := by
    intro v hv
    obtain ⟨x, hx⟩ := (hW v).1 hv
    rw [hx, AddEquiv.symm_apply_apply, Pi.single_eq_same]
  have hact : ∀ (h : SL(2, F)) (v : V),
      Θ.symm (Additive.ofMul (((σ' h : ↥K) : MulAut V) v)) =
        fun j => (h : Matrix (Fin 2) (Fin 2) F).mulVec ((Θ.symm (Additive.ofMul v)) j) := by
    intro h v
    apply Θ.injective
    rw [AddEquiv.apply_symm_apply, hΘ, AddEquiv.apply_symm_apply]
    rfl
  have hsingle : ∀ (M : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F),
      (fun j => M.mulVec (Pi.single (M := fun _ : Fin 2 => Fin 2 → F) i x j)) =
        Pi.single i (M.mulVec x) := by
    intro M x
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have hWinv : ∀ k : ↥K, ∀ v ∈ W, (k : MulAut V) v ∈ W := by
    intro k v hv
    obtain ⟨h, rfl⟩ := hσ' k
    obtain ⟨x, hx⟩ := (hW v).1 hv
    refine (hW _).2 ⟨(h : Matrix (Fin 2) (Fin 2) F).mulVec x, ?_⟩
    have h1 := hΘ h (Pi.single i x)
    rw [← hx, toMul_ofMul, hsingle] at h1
    exact h1.symm
  have hmk : ∀ m₁ m₂ : ↥(FFModel.nat (StatedSL 2 F)).sec,
      (QuotientGroup.mk m₁ : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
        (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec) =
        QuotientGroup.mk m₂ → m₁ = m₂ := by
    intro m₁ m₂ h12
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h12
    exact inv_mul_eq_one.mp (Subtype.ext (Subgroup.mem_bot.mp h12))
  let βraw : ↥W →* ↥(FFModel.nat (StatedSL 2 F)).sec :=
    { toFun := fun v =>
        ⟨Multiplicative.ofAdd ((Θ.symm (Additive.ofMul (v : V))) i), Subgroup.mem_top _⟩
      map_one' := by
        apply Subtype.ext
        show Multiplicative.ofAdd ((Θ.symm (Additive.ofMul (1 : V))) i) = 1
        rw [ofMul_one, map_zero]
        rfl
      map_mul' := fun v v' => by
        apply Subtype.ext
        show Multiplicative.ofAdd ((Θ.symm (Additive.ofMul ((v : V) * v'))) i) =
          Multiplicative.ofAdd ((Θ.symm (Additive.ofMul (v : V))) i) *
            Multiplicative.ofAdd ((Θ.symm (Additive.ofMul (v' : V))) i)
        rw [ofMul_mul, map_add, Pi.add_apply, ofAdd_add] }
  let β := (QuotientGroup.mk' ((FFModel.nat (StatedSL 2 F)).ker.subgroupOf
    (FFModel.nat (StatedSL 2 F)).sec)).comp βraw
  refine ⟨F, inferInstance, inferInstance, hF, π', hσ'.comp eS.symm.surjective, bot_le,
    fun _ _ => Subgroup.mem_top _, hWinv, ?_, fun _ _ _ => Subgroup.mem_top _, ?_, β, ?_, ?_,
    ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro (γ : ↥(StatedSL 2 F)) (m : Multiplicative (Fin 2 → F)) hm
    have hm' : m = 1 := Subgroup.mem_bot.mp hm
    subst hm'
    show Multiplicative.ofAdd (((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (1 : Multiplicative (Fin 2 → F)))) ∈
        (⊥ : Subgroup (Multiplicative (Fin 2 → F)))
    rw [toAdd_one, Matrix.mulVec_zero, ofAdd_zero]
    exact Subgroup.one_mem _
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    set y : Fin 2 → F := Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1) with hy
    have hv : Additive.toMul (Θ (Pi.single i y)) ∈ W :=
      (hW _).2 ⟨y, by rw [ofMul_toMul]⟩
    refine ⟨⟨_, hv⟩, ?_⟩
    show QuotientGroup.mk (βraw ⟨_, hv⟩) = _
    congr 1
    apply Subtype.ext
    show Multiplicative.ofAdd ((Θ.symm (Additive.ofMul
      (Additive.toMul (Θ (Pi.single i y))))) i) = m.1
    rw [ofMul_toMul, AddEquiv.symm_apply_apply, Pi.single_eq_same, hy, ofAdd_toAdd]
  · intro u
    constructor
    · intro h1
      rw [Subgroup.mem_bot]
      have h2 : βraw u ∈ (FFModel.nat (StatedSL 2 F)).ker.subgroupOf
          (FFModel.nat (StatedSL 2 F)).sec := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_subgroupOf] at h2
      have h3 : Multiplicative.ofAdd ((Θ.symm (Additive.ofMul (u : V))) i) = 1 :=
        Subgroup.mem_bot.mp h2
      have h4 : (Θ.symm (Additive.ofMul (u : V))) i = 0 := by
        have := congrArg Multiplicative.toAdd h3
        simpa using this
      apply Additive.ofMul.injective
      rw [hcoord _ u.2, h4, Pi.single_zero, map_zero]
      rfl
    · intro h1
      rw [Subgroup.mem_bot] at h1
      have hu : u = 1 := Subtype.ext h1
      rw [hu, map_one]
  · intro (γ : ↥(StatedSL 2 F)) u m hu hm hum
    have hm' : m = βraw u := hmk _ _ hum.symm
    set h := eS.symm γ with hh
    have hγ : γ = eS h := by rw [hh, MulEquiv.apply_symm_apply]
    have hγM : ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (h : Matrix (Fin 2) (Fin 2) F) := by
      rw [hγ]
      exact specialLinearGroupEquivStatedSL_coe 2 F h
    show QuotientGroup.mk (βraw ⟨_, hu⟩) = _
    congr 1
    apply Subtype.ext
    show Multiplicative.ofAdd ((Θ.symm (Additive.ofMul
      (((σ' h : ↥K) : MulAut V) (u : V)))) i) =
      Multiplicative.ofAdd (((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1)))
    rw [hact, hγM, hm']
    rfl

theorem nat_sum_of_nat_nat {K A : Subgroup (MulAut V)} {I : Subgroup V} {n : ℕ}
    (hV : ∀ v : V, v ^ 2 = 1) (hn : 1 ≤ n) (hfix : fixV K = ⊥) (hAK : A ≤ K)
    (hA2 : IsElemAbelian2 A) (hAc : Nat.card A = 2 ^ n) (hr : rkIdx (fixV A) ≤ 2 * n)
    (hI : BinaryNaturalSL K I ⊥ 2 n) (hQ : BinaryNaturalSL K ⊤ I 2 n) :
    ∃ W₁ W₂ : Subgroup V, (∀ k ∈ K, ∀ w ∈ W₁, k w ∈ W₁) ∧ (∀ k ∈ K, ∀ w ∈ W₂, k w ∈ W₂) ∧
      W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧ BinaryNaturalSL K W₁ ⊥ 2 n ∧
        BinaryNaturalSL K W₂ ⊥ 2 n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIc : Nat.card I = (2 ^ n) ^ 2 := by
    have := card_sec_of_binaryNaturalSL hI
    rwa [Subgroup.card_bot, mul_one] at this
  have hVc : Nat.card V = (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := by
    have := card_sec_of_binaryNaturalSL hQ
    rwa [Subgroup.card_top, hIc] at this
  have hrkV : rk V = 4 * n := by
    unfold rk
    rw [hVc, ← pow_mul, ← pow_add, padicValNat.prime_pow]
    ring
  have hCA : (2 ^ n) ^ 2 ≤ Nat.card (fixV A) := by
    have h1 := rk_add_rkIdx (fixV A)
    rw [hrkV] at h1
    rw [card_eq_two_pow hV (fixV A), ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hCa : ∀ a ∈ A, a ≠ 1 → Nat.card (fixV (Subgroup.zpowers a)) ≤ (2 ^ n) ^ 2 := by
    intro a ha ha1
    have haK := hAK ha
    have hfa : ∀ c ∈ fixV (Subgroup.zpowers a), a c = c := fun c hc =>
      mem_fixV_zpowers_iff.1 hc
    have h1 := card_le_of_fixed_natural hQ haK ha1 le_top hfa
    have h2 := card_le_of_fixed_natural hI haK ha1
      (inf_le_right : fixV (Subgroup.zpowers a) ⊓ I ≤ I) (fun c hc => hfa c hc.1)
    rw [inf_bot_eq, Subgroup.card_bot, mul_one] at h2
    calc Nat.card (fixV (Subgroup.zpowers a))
        ≤ 2 ^ n * Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) := h1
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ h2
      _ = (2 ^ n) ^ 2 := by ring
  have hAa : ∀ a ∈ A, a ≠ 1 → fixV A = fixV (Subgroup.zpowers a) := by
    intro a ha ha1
    exact Subgroup.eq_of_le_of_card_ge (B1.fixV_le_fixV ((Subgroup.zpowers_le).2 ha))
      ((hCa a ha ha1).trans hCA)
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ : ∃ a : ↥A, a ≠ 1 := by
    refine (Subgroup.ne_bot_iff_exists_ne_one).mp fun hA0 => ?_
    rw [hA0, Subgroup.card_bot] at hAc
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have ha₀1' : a₀ ≠ 1 := fun h1 => ha₀1 (Subtype.ext h1)
  have hCAeq : Nat.card (fixV A) = (2 ^ n) ^ 2 :=
    le_antisymm (hAa a₀ ha₀ ha₀1' ▸ hCa a₀ ha₀ ha₀1') hCA
  have hcommA : ∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ fixV A := by
    intro a ha v
    by_cases ha1 : a = 1
    · rw [ha1, MulAut.one_apply, mul_inv_cancel]
      exact (fixV A).one_mem
    rw [hAa a ha ha1, mem_fixV_zpowers_iff]
    exact apply_comm_eq_of_sq hV (hA2.2 a ha) v
  obtain ⟨F, _, _, hF, πI, hπI⟩ := hI
  have hchar : CharP F 2 := charP_two_of_card hF
  have hπIinj : Function.Injective πI :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπI
  set eS := specialLinearGroupEquivStatedSL 2 F
  let σ₀ : SL(2, F) →* ↥K := πI.comp eS.toMonoidHom
  have hσ₀inj : Function.Injective σ₀ := hπIinj.comp eS.injective
  have hσ₀surj : Function.Surjective σ₀ := hπI.1.comp eS.surjective
  set B : Subgroup SL(2, F) := (A.subgroupOf K).comap σ₀
  have hBmap : B.map σ₀ = A.subgroupOf K := Subgroup.map_comap_eq_self_of_surjective hσ₀surj _
  have hBc : Nat.card B = 2 ^ n := by
    rw [← Subgroup.card_map_of_injective hσ₀inj, hBmap,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAc]
  have hBp : IsPGroup 2 B := IsPGroup.of_card hBc
  have hBidx : ¬ 2 ∣ B.index := by
    have h1 := B.card_mul_index
    rw [hBc, card_SL2, hF] at h1
    have h2 : B.index = (2 ^ n) ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    exact (odd_two_pow_pow_sub_one hn (by norm_num)).not_two_dvd_nat
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq SL(2, F)
    ((Rg_isPGroup (F := F)).toSylow Rg_index_odd) (hBp.toSylow hBidx)
  have hBR : B = (Rg F).map (MulAut.conj g₀).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 SL(2, F) => (P : Subgroup SL(2, F))) hg₀
    simp only [IsPGroup.toSylow_coe] at h1
    rw [← h1, Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map_equiv]
    simp [MulAut.smul_def]
  let σ' : SL(2, F) →* ↥K := σ₀.comp (MulAut.conj g₀).toMonoidHom
  have hσ'surj : Function.Surjective σ' := hσ₀surj.comp (MulAut.conj g₀).surjective
  let σ : SL(2, F) →* MulAut V := K.subtype.comp σ'
  have hσK : ∀ k ∈ K, ∃ h : SL(2, F), σ h = k := by
    intro k hk
    obtain ⟨h, hh⟩ := hσ'surj ⟨k, hk⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  have hσR : ∀ t ∈ Rg F, σ t ∈ A := by
    intro t ht
    have h1 : (MulAut.conj g₀) t ∈ B := by
      rw [hBR]
      exact ⟨t, ht, rfl⟩
    exact h1
  have hσA : ∀ a ∈ A, ∃ t ∈ Rg F, σ t = a := by
    intro a ha
    obtain ⟨b, hb⟩ := hσ₀surj ⟨a, hAK ha⟩
    have hbB : b ∈ B := by
      show σ₀ b ∈ A.subgroupOf K
      rw [hb, Subgroup.mem_subgroupOf]
      exact ha
    rw [hBR] at hbB
    obtain ⟨t, ht, htb⟩ := hbB
    refine ⟨t, ht, ?_⟩
    show ((σ₀ ((MulAut.conj g₀) t) : ↥K) : MulAut V) = a
    rw [show (MulAut.conj g₀) t = b from htb, hb]
  let _ : DistribMulAction SL(2, F) (Additive V) := distribMulActionAdditive σ
  have hsmul : ∀ (h : SL(2, F)) (v : V), h • Additive.ofMul v = Additive.ofMul (σ h v) :=
    fun _ _ => rfl
  let Y : AddSubgroup (Additive V) := Subgroup.toAddSubgroup (fixV A)
  have hY : ∀ v : V, Additive.ofMul v ∈ Y ↔ v ∈ fixV A := fun _ => Iff.rfl
  have hinvA : ∀ k : SL(2, F), k.1 1 0 = 0 → ∀ v ∈ fixV A, σ k v ∈ fixV A := by
    intro k hk v hv a ha
    obtain ⟨t, ht, rfl⟩ := hσA a ha
    obtain ⟨c, rfl⟩ := mem_Rg.1 ht
    have h1 : σ (k⁻¹ * e12 c * k) v = v := hv _ (hσR _ (inv_mul_e12_mul_mem_Rg k hk c))
    calc σ (e12 c) (σ k v) = σ k (σ (k⁻¹ * e12 c * k) v) := by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, ← mul_assoc,
            ← mul_assoc, mul_inv_cancel, one_mul]
      _ = σ k v := by rw [h1]
  set w₀ : SL(2, F) := e21 1 with hw₀
  have hw₀10 : w₀.1 1 0 ≠ 0 := by
    show (e21 (1 : F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0
    simp
  have hw₀inv : (w₀⁻¹).1 1 0 ≠ 0 := by
    have h1 : w₀⁻¹ = e21 (-1) := by
      rw [hw₀, inv_eq_of_mul_eq_one_right]
      rw [← e21_add, add_neg_cancel]
      apply Subtype.ext
      simp [Matrix.one_fin_two]
    rw [h1]
    show (e21 (-1 : F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0
    simp
  set Y' : Subgroup V := (fixV A).map (σ w₀ : V ≃* V).toMonoidHom
  have hm3 : Y.map (actU w₀) = Subgroup.toAddSubgroup Y' := by
    ext z
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    show Additive.ofMul a ∈ Y.map (actU w₀) ↔ a ∈ Y'
    constructor
    · rintro ⟨y, hy, hya⟩
      obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
      refine ⟨b, (hY b).1 hy, ?_⟩
      have := congrArg Additive.toMul hya
      exact this
    · rintro ⟨b, hb, rfl⟩
      exact ⟨Additive.ofMul b, (hY b).2 hb, rfl⟩
  have hY'c : Nat.card Y' = Nat.card (fixV A) :=
    Subgroup.card_map_of_injective (σ w₀ : V ≃* V).injective
  have hdisj₀ : fixV A ⊓ Y' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvY'⟩
    obtain ⟨y, hyA, rfl⟩ := Subgroup.mem_map.mp hvY'
    set St : Subgroup SL(2, F) :=
      (MulAction.stabilizer (MulAut V) ((σ w₀ : V ≃* V).toMonoidHom y)).comap σ
    have hR : Rg F ≤ St := fun t ht => by
      show σ t • ((σ w₀ : V ≃* V).toMonoidHom y) = _
      exact hvA _ (hσR t ht)
    have hR' : (Rg F).map (MulAut.conj (w₀⁻¹)⁻¹).toMonoidHom ≤ St := by
      rintro _ ⟨t, ht, rfl⟩
      show σ ((MulAut.conj (w₀⁻¹)⁻¹) t) • ((σ w₀ : V ≃* V).toMonoidHom y) = _
      rw [inv_inv, MulAut.conj_apply, MulAut.smul_def, map_mul, map_mul, MulAut.mul_apply,
        MulAut.mul_apply, map_inv]
      show σ w₀ (σ t ((σ w₀)⁻¹ (σ w₀ y))) = σ w₀ y
      have hy' : (σ w₀)⁻¹ (σ w₀ y) = y := by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rw [hy', hyA _ (hσR t ht)]
    have htop : St = ⊤ := top_le_iff.mp ((Rg_sup_conj_eq_top w₀⁻¹ hw₀inv) ▸ sup_le hR hR')
    have hvK : (σ w₀ : V ≃* V).toMonoidHom y ∈ fixV K := by
      intro k hk
      obtain ⟨h, rfl⟩ := hσK k hk
      have : h ∈ St := htop ▸ Subgroup.mem_top h
      exact this
    rw [hfix] at hvK
    exact hvK
  have hsup₀ : fixV A ⊔ Y' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := card_sup_mul_card_inf (fixV A) Y'
    rw [hdisj₀, Subgroup.card_bot, mul_one, hY'c, hCAeq] at h1
    rw [h1, hVc]
  have hdisj : Y ⊓ Y.map (actU w₀) = ⊥ := by
    rw [hm3, eq_bot_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    have h1 : a ∈ fixV A ⊓ Y' :=
      Subgroup.mem_inf.2 ⟨(AddSubgroup.mem_inf.1 hz).1, (AddSubgroup.mem_inf.1 hz).2⟩
    rw [hdisj₀] at h1
    rw [Subgroup.mem_bot.1 h1]
    exact AddSubgroup.mem_bot.2 rfl
  have hsup : Y ⊔ Y.map (actU w₀) = ⊤ := by
    rw [hm3, eq_top_iff]
    intro z _
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    have ha : a ∈ fixV A ⊔ Y' := by
      rw [hsup₀]
      exact Subgroup.mem_top a
    have h1 : Additive.ofMul a ∈ Subgroup.toAddSubgroup (fixV A ⊔ Y') := ha
    rwa [OrderIso.map_sup] at h1
  have hinv : ∀ k : SL(2, F), k.1 1 0 = 0 → ∀ y ∈ Y, k • y ∈ Y := by
    intro k hk y hy
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
    rw [hsmul]
    exact (hY _).2 (hinvA k hk b ((hY b).1 hy))
  have hcomm : ∀ t ∈ Rg F, ∀ u : Additive V, t • u - u ∈ Y := by
    intro t ht u
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective u
    rw [hsmul, ← ofMul_div, div_eq_mul_inv]
    exact (hY _).2 (hcommA _ (hσR t ht) b)
  have hfix' : ∀ t ∈ Rg F, ∀ y ∈ Y, t • y = y := by
    intro t ht y hy
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
    rw [hsmul]
    exact congrArg Additive.ofMul (((hY b).1 hy) _ (hσR t ht))
  have hsq : ∀ u : Additive V, u + u = 0 := fun u => by
    show Additive.ofMul (Additive.toMul u * Additive.toMul u) = Additive.ofMul 1
    rw [← pow_two, hV]
  obtain ⟨s, Θ, hΘ, hYs, -⟩ := exists_equiv_of_halves (U := Additive V) theorem_G_1_3_two hsq Y
    w₀ hw₀10 hinv hcomm hfix' hdisj hsup
  have hYc : Nat.card Y = Nat.card (fixV A) := Nat.card_congr
    { toFun := fun y => ⟨Additive.toMul (y : Additive V), y.2⟩
      invFun := fun x => ⟨Additive.ofMul (x : V), x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : s = 2 := by
    rw [hYc, hCAeq, hF] at hYs
    exact (Nat.pow_right_injective (Nat.le_self_pow (by omega) 2) hYs).symm
  subst hs
  have hsingle : ∀ (k : SL(2, F)) (i : Fin 2) (x : Fin 2 → F),
      (fun j => k • Pi.single (M := fun _ : Fin 2 => Fin 2 → F) i x j) = Pi.single i (k • x) := by
    intro k i x
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  let W : Fin 2 → Subgroup V := fun i =>
    { carrier := {v | ∃ x : Fin 2 → F, Additive.ofMul v = Θ (Pi.single i x)}
      one_mem' := ⟨0, by rw [Pi.single_zero, map_zero]; rfl⟩
      mul_mem' := by
        rintro v v' ⟨x, hx⟩ ⟨x', hx'⟩
        exact ⟨x + x', by rw [ofMul_mul, hx, hx', ← map_add, Pi.single_add]⟩
      inv_mem' := by
        rintro v ⟨x, hx⟩
        exact ⟨-x, by rw [ofMul_inv, hx, ← map_neg, Pi.single_neg]⟩ }
  have hWmem : ∀ i v, v ∈ W i ↔ ∃ x : Fin 2 → F, Additive.ofMul v = Θ (Pi.single i x) :=
    fun _ _ => Iff.rfl
  have hWinv : ∀ i, ∀ k ∈ K, ∀ v ∈ W i, k v ∈ W i := by
    rintro i k hk v ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := hσK k hk
    refine ⟨h • x, ?_⟩
    rw [← hsmul, hx, ← hsingle, hΘ]
  refine ⟨W 0, W 1, hWinv 0, hWinv 1, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro v ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have h1 : Pi.single (M := fun _ : Fin 2 => Fin 2 → F) 0 x = Pi.single 1 y :=
      Θ.injective (hx.symm.trans hy)
    have h2 : x = 0 := by
      have := congrFun h1 0
      simpa using this
    rw [Subgroup.mem_bot]
    apply Additive.ofMul.injective
    rw [hx, h2, Pi.single_zero, map_zero]
    rfl
  · rw [eq_top_iff]
    intro v _
    set z := Θ.symm (Additive.ofMul v) with hz
    have hdec : z = Pi.single 0 (z 0) + Pi.single 1 (z 1) := by
      funext j
      fin_cases j <;> simp
    have hv : v = Additive.toMul (Θ (Pi.single 0 (z 0))) *
        Additive.toMul (Θ (Pi.single 1 (z 1))) := by
      apply Additive.ofMul.injective
      rw [ofMul_mul, ofMul_toMul, ofMul_toMul, ← map_add, ← hdec, hz,
        AddEquiv.apply_symm_apply]
    rw [hv]
    exact Subgroup.mul_mem_sup ⟨z 0, rfl⟩ ⟨z 1, rfl⟩
  · have hΘ' : ∀ (h : SL(2, F)) (x : Fin 2 → Fin 2 → F),
        Θ (fun j => (h : Matrix (Fin 2) (Fin 2) F).mulVec (x j)) =
          Additive.ofMul (((σ' h : ↥K) : MulAut V) (Additive.toMul (Θ x))) :=
      fun h x => hΘ h x
    exact binaryNaturalSL_of_equivariant hF σ' hσ'surj Θ hΘ' 0 (W 0) (hWmem 0)
  · have hΘ' : ∀ (h : SL(2, F)) (x : Fin 2 → Fin 2 → F),
        Θ (fun j => (h : Matrix (Fin 2) (Fin 2) F).mulVec (x j)) =
          Additive.ofMul (((σ' h : ↥K) : MulAut V) (Additive.toMul (Θ x))) :=
      fun h x => hΘ h x
    exact binaryNaturalSL_of_equivariant hF σ' hσ'surj Θ hΘ' 1 (W 1) (hWmem 1)

end Natural

end CFSG.Quasithin.H13
