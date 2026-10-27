module

public import CFSG.Quasithin.H13.A5W1620L32a
public import CFSG.Quasithin.H13.A5W1620L32c
public import CFSG.Quasithin.H13.A5W1622a
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.SteinbergCCPerfectCentralization

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix commutatorElement

namespace L32

section General

variable {G : Type*} [Group G]

theorem commutator_le_left_of_le_normalizer {W K : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) : ⁅W, K⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have h1 : k * w⁻¹ * k⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW hk) _).mp (W.inv_mem hw)
  have e : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact W.mul_mem hw h1

theorem conj_mem_commutator_left {W K : Subgroup G} (hKW : K ≤ Subgroup.normalizer (W : Set G))
    {k : G} (hk : k ∈ K) : ∀ u ∈ ⁅W, K⁆, k * u * k⁻¹ ∈ ⁅W, K⁆ := fun _ hu =>
  SteinbergCC.conj_mem_commutator
    (fun w hw => (Subgroup.mem_normalizer_iff.mp (hKW hk) w).mp hw)
    (fun _ hk' => K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) hu

theorem commutator_le_commutator_commutator {W K : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hKp : ⁅K, K⁆ = K) : ⁅W, K⁆ ≤ ⁅⁅W, K⁆, K⁆ := by
  set N := ⁅⁅W, K⁆, K⁆ with hNdef
  have hNW : N ≤ W := (commutator_le_left_of_le_normalizer
    (SteinbergCC.le_normalizer_of_conj_mem fun k hk => conj_mem_commutator_left hKW hk)).trans
    (commutator_le_left_of_le_normalizer hKW)
  have hNK : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn =>
    SteinbergCC.conj_mem_commutator (conj_mem_commutator_left hKW hk)
      (fun _ hk' => K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) hn
  have hle : K ⊔ W ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (SteinbergCC.le_normalizer_of_conj_mem hNK)
      (SteinbergCC.le_normalizer_of_conj_mem fun w hw n hn => by
        rw [hWc w hw n (hNW hn), mul_inv_cancel_right]
        exact hn)
  have h := SteinbergCC.commutator_le_of_perfect_mod (P := K) (A := W) (N := N) (K := K ⊔ W)
    le_sup_left le_sup_right
    (fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (hle hg) n).mp hn)
    (Subgroup.isPerfect_iff.mpr hKp) (by rw [Subgroup.commutator_comm K W])
  rwa [Subgroup.commutator_comm K W] at h

theorem conj_eq_of_mem_commutator {M K : Subgroup G} {y : G}
    (hMc : ∀ u ∈ M, ∀ w ∈ M, u * w = w * u) (hKM : ∀ k ∈ K, ∀ u ∈ M, k * u * k⁻¹ ∈ M)
    (hyM : ∀ u ∈ M, y * u * y⁻¹ ∈ M)
    (hcomm : ∀ k ∈ K, ∀ u ∈ M, k * (y * u * y⁻¹) * k⁻¹ = y * (k * u * k⁻¹) * y⁻¹)
    (hmod : ∀ u ∈ M, ∀ k ∈ K, k * (y * u * y⁻¹ * u⁻¹) * k⁻¹ = y * u * y⁻¹ * u⁻¹) :
    ∀ x ∈ ⁅M, K⁆, y * x * y⁻¹ = x := by
  have hle : ⁅M, K⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    set d := y * u * y⁻¹ * u⁻¹ with hd
    have hdM : d ∈ M := M.mul_mem (hyM u hu) (M.inv_mem hu)
    have hdu : y * u * y⁻¹ = d * u := by rw [hd]; group
    have h1 : y * (k * u⁻¹ * k⁻¹) * y⁻¹ = k * (y * u⁻¹ * y⁻¹) * k⁻¹ :=
      (hcomm k hk u⁻¹ (M.inv_mem hu)).symm
    have h2 : y * u⁻¹ * y⁻¹ = u⁻¹ * d⁻¹ := by rw [hd]; group
    have h3 : k * d⁻¹ * k⁻¹ = d⁻¹ := by
      have := hmod u hu k hk
      rw [← hd] at this
      calc k * d⁻¹ * k⁻¹ = (k * d * k⁻¹)⁻¹ := by group
        _ = d⁻¹ := by rw [this]
    have hcm : ⁅u, k⁆ ∈ M := by
      have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact M.mul_mem hu (hKM k hk _ (M.inv_mem hu))
    have hdc : d * ⁅u, k⁆ = ⁅u, k⁆ * d := hMc _ hdM _ hcm
    have key : y * ⁅u, k⁆ * y⁻¹ = ⁅u, k⁆ := by
      calc y * ⁅u, k⁆ * y⁻¹ = (y * u * y⁻¹) * (y * (k * u⁻¹ * k⁻¹) * y⁻¹) := by
            rw [commutatorElement_def]; group
        _ = (d * u) * (k * (u⁻¹ * d⁻¹) * k⁻¹) := by rw [h1, h2, hdu]
        _ = d * (u * (k * u⁻¹ * k⁻¹)) * (k * d⁻¹ * k⁻¹) := by group
        _ = d * ⁅u, k⁆ * d⁻¹ := by rw [h3, commutatorElement_def]; group
        _ = ⁅u, k⁆ := by rw [hdc]; group
    calc ⁅u, k⁆ * y = (y * ⁅u, k⁆ * y⁻¹) * y := by rw [key]
      _ = y * ⁅u, k⁆ := by group
  intro x hx
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [h]
    _ = x := by group

theorem conj_eq_of_natural {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {K W X Z : Subgroup G} {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥X →* Multiplicative (Fin 3 → F)} (hβk : β.ker = Z.subgroupOf X)
    (hβe : ∀ (a : ↥K) (u v : ↥X), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hKp : ⁅K, K⁆ = K) (hMX : ⁅W, K⁆ ≤ X) (hMZ : ¬ ⁅W, K⁆ ≤ Z)
    (hZK : Z ≤ Subgroup.centralizer (K : Set G)) {y : G}
    (hyM : ∀ u ∈ ⁅W, K⁆, y * u * y⁻¹ ∈ ⁅W, K⁆)
    (hcomm : ∀ k ∈ K, ∀ u ∈ ⁅W, K⁆, k * (y * u * y⁻¹) * k⁻¹ = y * (k * u * k⁻¹) * y⁻¹) :
    ∀ u ∈ ⁅W, K⁆, y * u * y⁻¹ = u := by
  set M := ⁅W, K⁆ with hMdef
  have hMW : M ≤ W := commutator_le_left_of_le_normalizer hKW
  have hMc : ∀ u ∈ M, ∀ w ∈ M, u * w = w * u := fun u hu w hw => hWc u (hMW hu) w (hMW hw)
  have hKM : ∀ k ∈ K, ∀ u ∈ M, k * u * k⁻¹ ∈ M := fun k hk => conj_mem_commutator_left hKW hk
  have hZfix : ∀ u ∈ Z, ∀ k ∈ K, k * u * k⁻¹ = u := by
    intro u hu k hk
    rw [Subgroup.mem_centralizer_iff.mp (hZK hu) k hk, mul_inv_cancel_right]
  have hfixZ : ∀ u ∈ M, (∀ k ∈ K, k * u * k⁻¹ = u) → u ∈ Z := fun u hu h =>
    mem_of_forall_conj_eq hF hα hβk hβe (hMX hu) h
  have hyZ : ∀ u ∈ M, u ∈ Z → y * u * y⁻¹ ∈ Z := fun u hu huZ =>
    hfixZ _ (hyM u hu) fun k hk => by rw [hcomm k hk u hu, hZfix u huZ k hk]
  have hyZ' : ∀ u ∈ M, y * u * y⁻¹ ∈ Z → u ∈ Z := by
    intro u hu h
    refine hfixZ u hu fun k hk => ?_
    have h1 := hZfix _ h k hk
    rw [hcomm k hk u hu] at h1
    calc k * u * k⁻¹ = y⁻¹ * (y * (k * u * k⁻¹) * y⁻¹) * y := by group
      _ = u := by rw [h1]; group
  have hmod := conj_mul_inv_mem_of_commute hF hα hβk hβe hMX hKM hMZ hyM hyZ hyZ' hcomm
  have hfix := conj_eq_of_mem_commutator hMc hKM hyM hcomm fun u hu k hk =>
    hZfix _ (hmod u hu) k hk
  exact fun u hu => hfix u (commutator_le_commutator_commutator hKW hWc hKp hu)

end General

section Cores

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCoreOf_eq_blockU {H K₀ : Subgroup G} (hK₀H : K₀ ≤ H)
    (hHK₀ : H ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀p : ⁅K₀, K₀⁆ = K₀) :
    ⁅pCoreOf 2 H, K₀⁆ = blockU K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx k hk
    have hxN : x ∈ Subgroup.normalizer (K₀ : Set G) :=
      hHK₀ (CFSG.LieType.BorelTits.pCoreOf_le 2 H hx)
    have h := comm_mem_blockU_of_mem_pCoreOf hK₀H hK₀p hx hxN k⁻¹ (K₀.inv_mem hk)
    have e : ⁅x, k⁆ = (k⁻¹⁻¹ * x * k⁻¹ * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (blockU K₀).inv_mem h
  · refine Subgroup.commutator_mono ?_ le_rfl
    refine le_pCoreOf_of_normalizes ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀H)
      (hHK₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)

theorem conj_mem_commutator_pCoreOf {H K₀ : Subgroup G} (hK₀H : K₀ ≤ H)
    (hHK₀ : H ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀p : ⁅K₀, K₀⁆ = K₀) {y : G}
    (hy : y ∈ Subgroup.normalizer (K₀ : Set G)) :
    ∀ q ∈ ⁅pCoreOf 2 H, K₀⁆, y * q * y⁻¹ ∈ ⁅pCoreOf 2 H, K₀⁆ := by
  rw [commutator_pCoreOf_eq_blockU hK₀H hHK₀ hK₀p]
  intro q hq
  have hyO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀ hy
  exact SteinbergCC.conj_mem_commutator
    (fun x hx => (Subgroup.mem_normalizer_iff.mp hyO x).mp hx)
    (fun x hx => (Subgroup.mem_normalizer_iff.mp hy x).mp hx) hq

end Cores

section Fields

theorem card_eq_two_of_card_statedSL {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (h : Nat.card ↥(StatedSL 3 K) = 168) : Nat.card K = 2 := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK] at h
  rcases m with _ | _ | m
  · simp at hK
    exact absurd hK (by
      have := Finite.one_lt_card (α := K)
      omega)
  · simpa using hK
  · exfalso
    have h4 : 4 ≤ 2 ^ (m + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set q := 2 ^ (m + 2) with hq
    have h1 : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h4 3
    have h2 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left h4 2
      omega
    have h3 : 63 ≤ q ^ 3 - 1 := by omega
    have : 64 * 15 * 63 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

variable {G : Type} [Group G]

theorem natCard_eq_two_of_isModO2Surj {K₀ : Subgroup G} {F F' : Type} [Field F] [Finite F]
    [Field F'] [Finite F'] (hF' : Nat.card F' = 2) {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {α : ↥K₀ →* ↥(StatedSL 3 F)} (hα : IsModO2Surj K₀ α) {α' : ↥K₀ →* ↥(StatedSL 3 F')}
    (hα' : IsModO2Surj K₀ α') : Nat.card F = 2 := by
  refine card_eq_two_of_card_statedSL hF ?_
  have hker : α.ker = α'.ker := hα.2.trans hα'.2.symm
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α' hα'.1).toEquiv,
    CFSG.SectionRank.OddCover.card_statedSL_three, hF']
  norm_num

end Fields

section Sums

variable {G : Type} [Group G] {F : Type} [Field F]

theorem coord_natural {A V : Subgroup G} {α : ↥A →* ↥(StatedSL 3 F)} {k : ℕ}
    {β : ↥V →* Multiplicative (Fin k → Fin 3 → F)}
    (hβe : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i)) (i : Fin k) :
    ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd
          (((Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i).toMultiplicative.comp β) v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd
          (((Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i).toMultiplicative.comp β) u) :=
  fun a u v huv => hβe a u v huv i

theorem natural_of_sum_one {A V Z : Subgroup G} {α : ↥A →* ↥(StatedSL 3 F)}
    (h : IsSumOfNaturalModulesVia A V Z α false 1) :
    A ≤ Subgroup.normalizer (V : Set G) ∧ Z ≤ V ∧
      ∃ β : ↥V →* Multiplicative (Fin 3 → F), Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
        ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
          Multiplicative.toAdd (β v) =
            ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) := by
  obtain ⟨hAV, hZV, β, hβs, hβk, hβe⟩ := h
  refine ⟨hAV, hZV, (Pi.evalAddMonoidHom (fun _ : Fin 1 => Fin 3 → F) 0).toMultiplicative.comp β,
    ?_, ?_, coord_natural hβe 0⟩
  · intro x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun _ => x)
    refine ⟨u, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, hu]
    rfl
  · ext u
    rw [MonoidHom.mem_ker, ← hβk, MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : Multiplicative.toAdd (β u) 0 = 0 := congrArg Multiplicative.toAdd h1
      refine toAdd_eq_zero.mp (funext fun i => ?_)
      rw [Subsingleton.elim i 0, h2]
      rfl
    · intro h1
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rfl

end Sums

end L32

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_commute_of_fix_red (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G))
    (y : ↥(Subgroup.normalizer (V : Set G))) (hyρ : S.frame.ρ y = c234 ∨ S.frame.ρ y = c234⁻¹)
    (hyW : (y : G) ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))
    (hcomm : ∀ k ∈ K₀, ∀ w ∈ S.WK K,
      k * ((y : G) * w * (y : G)⁻¹) * k⁻¹ = (y : G) * (k * w * k⁻¹) * (y : G)⁻¹)
    (hfix : ∀ k ∈ K₀, (y : G) * (k * S.z * k⁻¹ * S.z⁻¹) * (y : G)⁻¹ = k * S.z * k⁻¹ * S.z⁻¹) :
    False := by
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hW2 : ∀ x ∈ S.WK K, x * x = 1 := fun x hx => by rw [← pow_two]; exact hR.2.2.1.2 x hx
  have hKW : K₀ ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    hK₀K.trans ((le_sup_left.trans le_sup_left).trans hR.2.1)
  set W := S.WK K with hWdef
  have hzW : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  set y' : G := (y : G) with hy'
  have hyiW : y'⁻¹ ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := Subgroup.inv_mem _ hyW
  have hmemW : ∀ g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G), ∀ w ∈ W,
      g * w * g⁻¹ ∈ W := fun g hg w hw => (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  have hcomm' : ∀ k ∈ K₀, ∀ w ∈ W, k * (y'⁻¹ * w * y') * k⁻¹ = y'⁻¹ * (k * w * k⁻¹) * y' := by
    intro k hk w hw
    have hw' : y'⁻¹ * w * y' ∈ W := by simpa using hmemW _ hyiW w hw
    have h1 := hcomm k hk _ hw'
    have e1 : y' * (y'⁻¹ * w * y') * y'⁻¹ = w := by group
    rw [e1] at h1
    calc k * (y'⁻¹ * w * y') * k⁻¹ = y'⁻¹ * (y' * (k * (y'⁻¹ * w * y') * k⁻¹) * y'⁻¹) * y' := by
          group
      _ = y'⁻¹ * (k * w * k⁻¹) * y' := by rw [h1]
  have hfix' : ∀ k ∈ K₀, y'⁻¹ * (k * S.z * k⁻¹ * S.z⁻¹) * y' = k * S.z * k⁻¹ * S.z⁻¹ := by
    intro k hk
    have h1 := hfix k hk
    calc y'⁻¹ * (k * S.z * k⁻¹ * S.z⁻¹) * y' =
        y'⁻¹ * (y' * (k * S.z * k⁻¹ * S.z⁻¹) * y'⁻¹) * y' := by rw [h1]
      _ = k * S.z * k⁻¹ * S.z⁻¹ := by group
  apply hz
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w := k * S.z * k⁻¹ * S.z⁻¹ with hwdef
  have hkz : k * S.z * k⁻¹ = w * S.z := by rw [hwdef]; group
  have hwW : w ∈ W := W.mul_mem (hmemW k (hKW hk) _ hzW) (W.inv_mem hzW)
  have hzyW : y' * S.z * y'⁻¹ ∈ W := hmemW _ hyW _ hzW
  have hzyiW : y'⁻¹ * S.z * y' ∈ W := by simpa using hmemW _ hyiW _ hzW
  have hv : S.v12 = S.z * (y' * S.z * y'⁻¹) * (y'⁻¹ * S.z * y') := S.v12_eq_mul y hyρ
  have h1 : k * (y' * S.z * y'⁻¹) * k⁻¹ = w * (y' * S.z * y'⁻¹) := by
    rw [hcomm k hk _ hzW, hkz]
    calc y' * (w * S.z) * y'⁻¹ = (y' * w * y'⁻¹) * (y' * S.z * y'⁻¹) := by group
      _ = w * (y' * S.z * y'⁻¹) := by
        rw [show y' * w * y'⁻¹ = w from hfix k hk]
  have h2 : k * (y'⁻¹ * S.z * y') * k⁻¹ = w * (y'⁻¹ * S.z * y') := by
    rw [hcomm' k hk _ hzW, hkz]
    calc y'⁻¹ * (w * S.z) * y' = (y'⁻¹ * w * y') * (y'⁻¹ * S.z * y') := by group
      _ = w * (y'⁻¹ * S.z * y') := by
        rw [show y'⁻¹ * w * y' = w from hfix' k hk]
  have hvk : k * S.v12 * k⁻¹ = w * S.v12 := by
    have e1 : k * S.v12 * k⁻¹ = (k * S.z * k⁻¹) * (k * (y' * S.z * y'⁻¹) * k⁻¹) *
        (k * (y'⁻¹ * S.z * y') * k⁻¹) := by rw [hv]; group
    rw [e1, hkz, h1, h2, hv]
    have key := L32.mul_three_of_sq (⟨w, hwW⟩ : ↥W) ⟨S.z, hzW⟩ ⟨_, hzyW⟩ ⟨_, hzyiW⟩
      (Subtype.ext (hW2 w hwW))
    exact congrArg Subtype.val key
  have hvc : k * S.v12 * k⁻¹ = S.v12 := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hK.1 (hK₀K hk))
    rw [hc, mul_inv_cancel_right]
  have hw1 : w = 1 := by
    have h3 : w * S.v12 = S.v12 := hvk.symm.trans hvc
    exact mul_eq_right.mp h3
  have h4 : k * S.z * k⁻¹ = S.z := by rw [hkz, hw1, one_mul]
  calc k * S.z = k * S.z * k⁻¹ * k := by group
    _ = S.z * k := by rw [h4]

end Setting

end CFSG.Quasithin.H13.A5
