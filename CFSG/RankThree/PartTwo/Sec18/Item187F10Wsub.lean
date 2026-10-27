module

public import CFSG.RankThree.PartTwo.Sec18.Item187Frattini
public import CFSG.RankThree.PartTwo.Sec18.Item187Triple
public import CFSG.RankThree.PartTwo.Sec18.Item187F0Basic
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.RankThree.PartTwo.Sec18.Item187Syl
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centerOf tripleOf)

variable {G : Type} [Group G] [Finite G]

private theorem auto_eq_of_odd_pow {W : Type} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hW : IsPGroup 2 W) (β : MulAut W) {k : ℕ}
    (hk : Odd k) (hβk : β ^ k = 1) (h : ∀ w : W, w ^ 2 = 1 → β w = w) (w : W) : β w = w := by
  letI : CommGroup W := { toGroup := inferInstance, mul_comm := hcomm }
  obtain ⟨q, rfl⟩ := hk
  obtain ⟨P, hP⟩ : ∃ P : W →* W, ∀ x, P x = ∏ i ∈ Finset.range (2 * q + 1), (β ^ i) x :=
    ⟨{ toFun := fun x => ∏ i ∈ Finset.range (2 * q + 1), (β ^ i) x
       map_one' := by simp
       map_mul' := fun a b => by simp [map_mul, Finset.prod_mul_distrib] }, fun x => rfl⟩
  have key : ∀ (f : ℕ → W) (n : ℕ), (∏ i ∈ Finset.range (n + 1), f (i + 1)) * f 0 =
      (∏ i ∈ Finset.range (n + 1), f i) * f (n + 1) := fun f n =>
    (Finset.prod_range_succ' f (n + 1)).symm.trans (Finset.prod_range_succ f (n + 1))
  have hPβ : ∀ x : W, P (β x) = P x := by
    intro x
    have hβx : (β ^ (2 * q + 1)) x = x := by simp [hβk]
    have h0 : (β ^ 0) x = x := by simp
    have hk' := key (fun i => (β ^ i) x) (2 * q)
    simp only [h0, hβx] at hk'
    have e2 : ∏ i ∈ Finset.range (2 * q + 1), (β ^ i) (β x) =
        ∏ i ∈ Finset.range (2 * q + 1), (β ^ (i + 1)) x :=
      Finset.prod_congr rfl fun i _ => by rw [pow_succ]; rfl
    rw [hP, hP, e2]
    exact mul_right_cancel hk'
  have hPinv : ∀ y : W, β y = y → y ^ 2 = 1 → P y = y := by
    intro y hy hy2
    have hi : ∀ i : ℕ, (β ^ i) y = y := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ]
        show (β ^ i) (β y) = y
        rw [hy, ih]
    rw [hP]
    simp only [hi, Finset.prod_const, Finset.card_range]
    rw [pow_succ, pow_mul, hy2, one_pow, one_mul]
  have hker : ∀ n : ℕ, ∀ u : W, u ^ 2 ^ n = 1 → P u = 1 → u = 1 := by
    intro n
    induction n with
    | zero => intro u hu _; simpa using hu
    | succ n ih =>
      intro u hu hPu
      have hv : (u ^ 2) ^ 2 ^ n = 1 := by
        rw [← pow_mul, ← pow_succ']
        exact hu
      have hPv : P (u ^ 2) = 1 := by rw [map_pow, hPu, one_pow]
      have hu2 : u ^ 2 = 1 := ih (u ^ 2) hv hPv
      exact ((hPinv u (h u hu2) hu2).symm).trans hPu
  obtain ⟨n, hn⟩ := hW (w⁻¹ * β w)
  have hPu : P (w⁻¹ * β w) = 1 := by
    rw [map_mul, map_inv, hPβ, inv_mul_cancel]
  exact (inv_mul_eq_one.mp (hker n _ hn hPu)).symm

theorem orderOf_pow_two_of_fixes_omega {W : Type} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hW : IsPGroup 2 W) (α : MulAut W)
    (h : ∀ w : W, w ^ 2 = 1 → α w = w) : ∃ n : ℕ, orderOf α = 2 ^ n := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun α : MulAut W => (α : W → W)) DFunLike.coe_injective
  have hpos : orderOf α ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite α)).ne'
  obtain ⟨a, k, hk, hm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hfix : ∀ j : ℕ, ∀ w : W, w ^ 2 = 1 → (α ^ j) w = w := by
    intro j w hw
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      show (α ^ j) (α w) = w
      rw [h w hw, ih]
  have hβk : (α ^ 2 ^ a) ^ k = 1 := by
    rw [← pow_mul, ← hm, pow_orderOf_eq_one]
  have hβ1 : α ^ 2 ^ a = 1 := by
    ext w
    show (α ^ 2 ^ a) w = w
    exact auto_eq_of_odd_pow hcomm hW (α ^ 2 ^ a) hk hβk (fun w hw => hfix _ w hw) w
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hβ1)
  exact ⟨i, hi⟩

@[expose] def Wsub (X S : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | ∃ x ∈ X, ∃ z ∈ centerOf S, y = x * z * x⁻¹}

abbrev W1 (X S : Subgroup G) : Subgroup G := Sec3.omegaG (Wsub X S)

@[expose] def BadCase (A M H : Subgroup G) (X : Subgroup G) : Prop :=
  2 ≤ CFSG.pRank 2 ↥(CFSG.Open.pCoreOf 2 (H ⊓ M)) ∧
    ¬ X ≤ Subgroup.normalizer (tripleOf (CFSG.Open.pCoreOf 2 (H ⊓ M)) 1 : Set G) ∧
    ¬ X ≤ Subgroup.normalizer (tripleOf (CFSG.Open.pCoreOf 2 (H ⊓ M)) 2 : Set G)

private theorem wsub_mem_of_gen (X S : Subgroup G) {x z : G} (hx : x ∈ X)
    (hz : z ∈ centerOf S) : x * z * x⁻¹ ∈ Wsub X S := by
  unfold Wsub
  exact Subgroup.subset_closure ⟨x, hx, z, hz, rfl⟩

private theorem wsub_centerOf_le (X S : Subgroup G) : centerOf S ≤ Wsub X S := by
  intro z hz
  simpa using wsub_mem_of_gen X S (Subgroup.one_mem X) hz

private theorem conj_mem_closure_gen {K : Set G} {g : G}
    (hK : ∀ y ∈ K, g * y * g⁻¹ ∈ Subgroup.closure K) {y : G} (hy : y ∈ Subgroup.closure K) :
    g * y * g⁻¹ ∈ Subgroup.closure K := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hK x hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

private theorem wsub_conj_mem (X S : Subgroup G) {g : G} (hg : g ∈ X) {y : G}
    (hy : y ∈ Wsub X S) : g * y * g⁻¹ ∈ Wsub X S := by
  unfold Wsub at hy ⊢
  refine conj_mem_closure_gen ?_ hy
  intro y' hy'
  obtain ⟨a, ha, z, hz, rfl⟩ := hy'
  exact Subgroup.subset_closure ⟨g * a, mul_mem hg ha, z, hz, by group⟩

private theorem centerOf_conj_mem_of_normalizes {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) {z : G} (hz : z ∈ centerOf S) :
    g * z * g⁻¹ ∈ centerOf S := by
  obtain ⟨hzS, hzc⟩ := mem_centerOf_iff.mp hz
  have hconj : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * s * g)).mpr (by
      rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
      exact hs)
  rw [mem_centerOf_iff]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzS, fun y hy => ?_⟩
  have h1 := hzc _ (hconj y hy)
  calc g * z * g⁻¹ * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [h1]
    _ = y * (g * z * g⁻¹) := by group

private theorem wsub_conj_mem_of_normalizes {X S : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgS : g ∈ Subgroup.normalizer (S : Set G))
    {y : G} (hy : y ∈ Wsub X S) : g * y * g⁻¹ ∈ Wsub X S := by
  unfold Wsub at hy ⊢
  refine conj_mem_closure_gen ?_ hy
  intro y' hy'
  obtain ⟨a, ha, z, hz, rfl⟩ := hy'
  have hga : g * a * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgX a).mp ha
  have hgz : g * z * g⁻¹ ∈ centerOf S := centerOf_conj_mem_of_normalizes hgS hz
  exact Subgroup.subset_closure ⟨g * a * g⁻¹, hga, g * z * g⁻¹, hgz, by group⟩

private theorem wsub_le_normalizer_X (X S : Subgroup G) :
    X ≤ Subgroup.normalizer (Wsub X S : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => wsub_conj_mem X S hg hh, fun hh => ?_⟩
  have h2 := wsub_conj_mem X S (inv_mem hg) hh
  rw [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h2
  exact h2

private theorem wsub_mem_normalizer_of_normalizes {X S : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgS : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (Wsub X S : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => wsub_conj_mem_of_normalizes hgX hgS hh, fun hh => ?_⟩
  have h2 := wsub_conj_mem_of_normalizes (inv_mem hgX) (inv_mem hgS) hh
  rw [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h2
  exact h2

private theorem cent_conj_iff {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {h : G} :
    h ∈ Subgroup.centralizer (T : Set G) ↔ g * h * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  have hT : ∀ t, t ∈ T ↔ g * t * g⁻¹ ∈ T := fun t => Subgroup.mem_normalizer_iff.mp hg t
  have hT' : ∀ t ∈ T, g⁻¹ * t * g ∈ T := fun t ht =>
    (hT (g⁻¹ * t * g)).mpr (by
      rw [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact ht)
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc t ht
    have h1 := hc _ (hT' t ht)
    calc t * (g * h * g⁻¹) = g * ((g⁻¹ * t * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * t := by group
  · intro hc t ht
    have h1 := hc _ ((hT t).mp ht)
    calc t * h = g⁻¹ * (g * t * g⁻¹ * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * h * g⁻¹ * (g * t * g⁻¹)) * g := by rw [h1]
      _ = h * t := by group

private theorem cent_inf_normalizer {K X T : Subgroup G}
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hKT : K ≤ Subgroup.normalizer (T : Set G)) :
    K ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  have hX' := Subgroup.mem_normalizer_iff.mp (hKX hg) h
  have hC' := cent_conj_iff (hKT hg) (h := h)
  constructor
  · intro hh
    have hh' : h ∈ X ⊓ Subgroup.centralizer (T : Set G) := hh
    have h1 := Subgroup.mem_inf.mp hh'
    exact Subgroup.mem_inf.mpr ⟨hX'.mp h1.1, hC'.mp h1.2⟩
  · intro hh
    have hh' : g * h * g⁻¹ ∈ X ⊓ Subgroup.centralizer (T : Set G) := hh
    have h1 := Subgroup.mem_inf.mp hh'
    exact Subgroup.mem_inf.mpr ⟨hX'.mpr h1.1, hC'.mpr h1.2⟩

private theorem cent_le_normalizer {K T W : Subgroup G} (hTW : T ≤ W)
    (hKW : K ≤ Subgroup.centralizer (W : Set G)) : K ≤ Subgroup.normalizer (T : Set G) := by
  intro v hv
  have hvT : v ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp (hKW hv) t (hTW ht)
  exact Subgroup.centralizer_le_normalizer (T : Set G) hvT

private theorem cent_conj_eq_of_hom_eq_one {W : Subgroup G}
    {g : Subgroup.normalizer (W : Set G)}
    (h : Subgroup.normalizerMonoidHom W g = 1) (t : G) (ht : t ∈ W) :
    (g : G) * t * (g : G)⁻¹ = t := by
  have key : (((Subgroup.normalizerMonoidHom W g) ⟨t, ht⟩ : ↥W) : G) =
      (((1 : MulAut ↥W) ⟨t, ht⟩ : ↥W) : G) := by
    rw [h]
  exact key

private theorem omegaG_le_centerOf' (S : Subgroup G) : Sec3.omegaG S ≤ centerOf S := by
  intro t ht
  exact mem_centerOf_iff.mpr ⟨(Sec3.mem_omegaG.mp ht).1, (Sec3.mem_omegaG.mp ht).2.1⟩

private theorem omegaG_le_Wsub' (X S : Subgroup G) : Sec3.omegaG S ≤ Wsub X S :=
  (omegaG_le_centerOf' S).trans (wsub_centerOf_le X S)

private theorem le_centralizer_centerOf (S : Subgroup G) :
    S ≤ Subgroup.centralizer (centerOf S : Set G) := by
  intro s hs
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (mem_centerOf_iff.mp hz).2 s hs

private theorem tripleOf_two_eq_omegaG' (S : Subgroup G) : tripleOf S 2 = Sec3.omegaG S :=
  (tripleOf_two_eq S).trans (Item181ThreeProof.fourChar_zero S)

private theorem eq_of_isSylowOf_of_le {T C U : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T U) (hCU : C ≤ U) (hTC : T ≤ C)
    (hn : ∃ n : ℕ, Nat.card U = Nat.card C * 2 ^ n) : C = U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hn
  have hodd : ¬ 2 ∣ T.relIndex U := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
  have h1 := Subgroup.relIndex_mul_card C U
  rw [inf_eq_left.mpr hCU, hn] at h1
  have hCi : C.relIndex U = 2 ^ n := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    have h2 : C.relIndex U * Nat.card C = 2 ^ n * Nat.card C := by
      rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hrel := Subgroup.relIndex_mul_relIndex T C U hTC hCU
  rw [hCi] at hrel
  have hn0 : n = 0 := by
    by_contra hne
    apply hodd
    rw [← hrel]
    exact (dvd_pow_self 2 hne).mul_left _
  rw [hn0, pow_zero] at hCi
  exact le_antisymm hCU (Subgroup.relIndex_eq_one.mp hCi)

private theorem le_of_two_power_centralizer {X S U C : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S X) (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hCU : C ≤ U)
    (hUN : U ≤ Subgroup.normalizer (C : Set G)) (hTC : S ⊓ U ≤ C)
    (hcentral : ∀ u ∈ U, ∃ n : ℕ, u ^ 2 ^ n ∈ C) : U ≤ C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ U) U := hS.inf_of_le_normalizer hUX hXU
  obtain ⟨n, hn⟩ :=
    (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux.twoMod_iff hCU hUN).mpr hcentral
  exact (eq_of_isSylowOf_of_le hT hCU hTC ⟨n, hn⟩).symm.le

variable {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.Wsub_le (h186 : Item186H) (hX : MinCex A M H c X) :
    Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) ≤ centerOf (CFSG.Open.pCoreOf 2 X) := by
  unfold Wsub
  rw [Subgroup.closure_le]
  rintro y ⟨x, hx, z, hz, rfl⟩
  have hzS : z ∈ CFSG.Open.pCoreOf 2 (H ⊓ M) := (mem_centerOf_iff.mp hz).1
  have hzc := (mem_centerOf_iff.mp hz).2
  have hxzX : x * z * x⁻¹ ∈ X := mul_mem (mul_mem hx (hX.pCoreOf_le hzS)) (inv_mem hx)
  have hxzC : x * z * x⁻¹ ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqN : x⁻¹ * q * x ∈ CFSG.Open.pCoreOf 2 X := by
      refine (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) (x⁻¹ * q * x)).mpr ?_
      rw [show x * (x⁻¹ * q * x) * x⁻¹ = q by group]
      exact hq
    have h1 := hzc _ (MinCex.pCoreOf_le_S h186 hX hqN)
    calc q * (x * z * x⁻¹) = x * (z * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]; group
      _ = x * z * x⁻¹ * q := by group
  have hxzQ : x * z * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    MinCex.centralizer_pCoreOf_le h186 hX (Subgroup.mem_inf.mpr ⟨hxzX, hxzC⟩)
  exact mem_centerOf_iff.mpr
    ⟨hxzQ, fun q hq => ((Subgroup.mem_centralizer_iff.mp hxzC) q hq).symm⟩

private theorem MinCex.Wsub_comm (h186 : Item186H) (hX : MinCex A M H c X) {a b : G}
    (ha : a ∈ Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)))
    (hb : b ∈ Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))) : a * b = b * a :=
  (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX ha)).2 b
    (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hb)).1

private theorem MinCex.pCoreOf_le_centralizer_Wsub (h186 : Item186H) (hX : MinCex A M H c X) :
    CFSG.Open.pCoreOf 2 X ≤
      Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hw)).2 q hq

private theorem MinCex.pCoreOf_le_inf_centralizer (h186 : Item186H) (hX : MinCex A M H c X) :
    CFSG.Open.pCoreOf 2 X ≤
      X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  intro q hq
  exact Subgroup.mem_inf.mpr
    ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 X hq, MinCex.pCoreOf_le_centralizer_Wsub h186 hX hq⟩

private theorem MinCex.isPGroup_Wsub (h186 : Item186H) (hX : MinCex A M H c X) :
    IsPGroup 2 ↥(Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))) :=
  IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) (by
    intro w hw
    exact (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hw)).1)

theorem MinCex.le_normalizer_Wsub (hX : MinCex A M H c X) :
    X ≤ Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ∧
      A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
        Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  have hSX : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X := hX.pCoreOf_le
  have hXW := wsub_le_normalizer_X X (CFSG.Open.pCoreOf 2 (H ⊓ M))
  refine ⟨hXW, sup_le ?_ (hSX.trans hXW)⟩
  intro a ha
  have haA : a ∈ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
    (le_sup_left : A ≤ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) ha
  exact wsub_mem_normalizer_of_normalizes (hX.le_normalizer haA)
    (le_normalizer_pCoreOf hX.sec18H haA)

theorem MinCex.sup_zpowers_le_normalizer_W1 (hX : MinCex A M H c X) :
    X ⊔ Subgroup.zpowers c ≤
      Subgroup.normalizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hW := MinCex.le_normalizer_Wsub hX
  have hcW : c ∈ Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    hW.2 ((le_sup_left : A ≤ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) hcA)
  exact (sup_le hW.1 (Subgroup.zpowers_le.mpr hcW)).trans
    (Item181ThreeProof.normalizer_le_normalizer_omegaG _)

private theorem MinCex.omegaG_le_W1 (h186 : Item186H) (hX : MinCex A M H c X) :
    Sec3.omegaG (CFSG.Open.pCoreOf 2 (H ⊓ M)) ≤ W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) := by
  intro t ht
  have htW : t ∈ Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) := omegaG_le_Wsub' X _ ht
  exact Sec3.mem_omegaG.mpr
    ⟨htW, fun w hw => MinCex.Wsub_comm h186 hX htW hw, (Sec3.mem_omegaG.mp ht).2.2⟩

private theorem MinCex.exists_pow_two_pow_mem (h186 : Item186H) (hX : MinCex A M H c X) {u : G}
    (hu : u ∈ X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) :
    ∃ n : ℕ, u ^ 2 ^ n ∈
      X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  obtain ⟨huX, huC⟩ := Subgroup.mem_inf.mp hu
  have huN : u ∈ Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    wsub_le_normalizer_X X _ huX
  have hcommW : ∀ a b : ↥(Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))), a * b = b * a :=
    fun a b => Subtype.ext (MinCex.Wsub_comm h186 hX a.2 b.2)
  have hWp : IsPGroup 2 ↥(Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))) :=
    MinCex.isPGroup_Wsub h186 hX
  have hfix : ∀ w : ↥(Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))), w ^ 2 = 1 →
      Subgroup.normalizerMonoidHom (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))) ⟨u, huN⟩ w = w := by
    intro w hw
    apply Subtype.ext
    have hw1 : (w : G) ∈ W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) := by
      refine Sec3.mem_omegaG.mpr ⟨w.2, fun x hx => ?_, ?_⟩
      · exact congrArg Subtype.val (hcommW w ⟨x, hx⟩)
      · simpa [pow_two] using congrArg Subtype.val hw
    have hcw := Subgroup.mem_centralizer_iff.mp huC (w : G) hw1
    show u * (w : G) * u⁻¹ = (w : G)
    rw [← hcw, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := orderOf_pow_two_of_fixes_omega hcommW hWp _ hfix
  have hαn : (Subgroup.normalizerMonoidHom (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M))) ⟨u, huN⟩) ^
      2 ^ n = 1 := by
    rw [← hn]
    exact pow_orderOf_eq_one _
  have hpow : Subgroup.normalizerMonoidHom (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)))
      (⟨u, huN⟩ ^ 2 ^ n) = 1 := by
    rw [map_pow]
    exact hαn
  refine ⟨n, Subgroup.mem_inf.mpr ⟨pow_mem huX _,
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩⟩
  have hconj : u ^ 2 ^ n * t * (u ^ 2 ^ n)⁻¹ = t := cent_conj_eq_of_hom_eq_one hpow t ht
  rw [mul_inv_eq_iff_eq_mul] at hconj
  exact hconj.symm

theorem MinCex.inf_centralizer_Wsub_inf_S (h186 : Item186H) (hX : MinCex A M H c X)
    (hbad : BadCase A M H X) :
    (X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ⊓
      CFSG.Open.pCoreOf 2 (H ⊓ M) = CFSG.Open.pCoreOf 2 X := by
  unfold BadCase at hbad
  obtain ⟨-, -, hbad2⟩ := hbad
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hXW : X ≤ Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (MinCex.le_normalizer_Wsub hX).1
  have hAW : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
      Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (MinCex.le_normalizer_Wsub hX).2
  have hAA : A ≤ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) := le_sup_left
  have hVX : X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ≤ X :=
    inf_le_left
  have hXV := cent_inf_normalizer (K := X) Subgroup.le_normalizer hXW
  have hAV := cent_inf_normalizer (K := A) (hAA.trans hX.le_normalizer) (hAA.trans hAW)
  rcases hX.sup_eq_or_inf_le hS hVX hXV hAV with hsup | hinf
  · exfalso
    apply hbad2
    rw [tripleOf_two_eq_omegaG']
    have hle : (X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ⊔
        CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
          Subgroup.normalizer (Sec3.omegaG (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
      sup_le (cent_le_normalizer (omegaG_le_Wsub' X (CFSG.Open.pCoreOf 2 (H ⊓ M))) inf_le_right)
        (cent_le_normalizer (omegaG_le_centerOf' (CFSG.Open.pCoreOf 2 (H ⊓ M)))
          (le_centralizer_centerOf _))
    rw [hsup] at hle
    exact hle
  · exact le_antisymm hinf
      (le_inf (MinCex.pCoreOf_le_inf_centralizer h186 hX) (MinCex.pCoreOf_le_S h186 hX))

theorem MinCex.centralizer_W1 (h186 : Item186H) (hX : MinCex A M H c X)
    (hbad : BadCase A M H X) :
    X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) =
      X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  unfold BadCase at hbad
  obtain ⟨-, -, hbad2⟩ := hbad
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hXW : X ≤ Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (MinCex.le_normalizer_Wsub hX).1
  have hAW : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
      Subgroup.normalizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (MinCex.le_normalizer_Wsub hX).2
  have hAA : A ≤ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) := le_sup_left
  have hXW1 : X ≤ Subgroup.normalizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    hXW.trans (Item181ThreeProof.normalizer_le_normalizer_omegaG _)
  have hAW1 : A ≤ Subgroup.normalizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (hAA.trans hAW).trans (Item181ThreeProof.normalizer_le_normalizer_omegaG _)
  have hUX : X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ≤ X :=
    inf_le_left
  have hXU := cent_inf_normalizer (K := X) Subgroup.le_normalizer hXW1
  have hAU := cent_inf_normalizer (K := A) (hAA.trans hX.le_normalizer) hAW1
  have hCU : X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ≤
      X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    inf_le_inf_left X (Subgroup.centralizer_le fun w hw => Sec3.omegaG_le _ hw)
  refine le_antisymm ?_ hCU
  rcases hX.sup_eq_or_inf_le hS hUX hXU hAU with hsup | hinf
  · exfalso
    apply hbad2
    rw [tripleOf_two_eq_omegaG']
    have hle : (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ⊔
        CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
          Subgroup.normalizer (Sec3.omegaG (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
      sup_le (cent_le_normalizer (MinCex.omegaG_le_W1 h186 hX) inf_le_right)
        (cent_le_normalizer (omegaG_le_centerOf' (CFSG.Open.pCoreOf 2 (H ⊓ M)))
          (le_centralizer_centerOf _))
    rw [hsup] at hle
    exact hle
  · have hUN := cent_inf_normalizer (hUX.trans Subgroup.le_normalizer) (hUX.trans hXW)
    have hTC : CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓
        (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ≤
          X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
      ((le_of_eq (inf_comm _ _)).trans hinf).trans
        (MinCex.pCoreOf_le_inf_centralizer h186 hX)
    exact le_of_two_power_centralizer hS hUX hXU hCU hUN hTC
      (fun u hu => MinCex.exists_pow_two_pow_mem h186 hX hu)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
