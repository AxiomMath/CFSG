module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Ch3z

section Abstract

variable {Γ : Type*} [Group Γ]

theorem comm_eq_one_of_odd {k u : Γ} {r : ℕ} (hr : Odd r) (hkr : k ^ r = 1)
    (hw2 : (k * u * k⁻¹ * u⁻¹) * (k * u * k⁻¹ * u⁻¹) = 1)
    (hkw : k * (k * u * k⁻¹ * u⁻¹) * k⁻¹ = k * u * k⁻¹ * u⁻¹) : k * u * k⁻¹ * u⁻¹ = 1 := by
  set w := k * u * k⁻¹ * u⁻¹ with hw
  have hku : k * u * k⁻¹ = w * u := by rw [hw]; group
  have hj : ∀ j : ℕ, k ^ j * u * (k ^ j)⁻¹ = w ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : k ^ (j + 1) * u * (k ^ (j + 1))⁻¹ = k * (k ^ j * u * (k ^ j)⁻¹) * k⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e, ih, pow_succ]
      have e2 : k * (w ^ j * u) * k⁻¹ = (k * w * k⁻¹) ^ j * (k * u * k⁻¹) := by
        rw [conj_pow]; group
      rw [e2, hkw, hku]
      group
  have h1 := hj r
  rw [hkr, inv_one, one_mul, mul_one] at h1
  have h2 : w ^ r = 1 := by
    have : w ^ r * u = 1 * u := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel this
  obtain ⟨m, hm⟩ := hr
  have hsq : w ^ 2 = 1 := by rw [sq]; exact hw2
  rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h2
  exact h2

variable {Ĥ : Type*} [Group Ĥ]

theorem norm_mem_commutator [Finite Ĥ] (ρ : Ĥ →* Γ) {X : Subgroup Γ}
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX2 : ∀ x ∈ X, x * x = 1)
    (hnorm : ∀ h : Ĥ, ∀ x ∈ X, ρ h * x * (ρ h)⁻¹ ∈ X)
    {K R : Subgroup Ĥ} (hKR : ∀ h : Ĥ, ∃ k ∈ K, ∃ r ∈ R, h = k * r) (hodd : Odd R.index)
    (hC : ∀ x ∈ X, (∀ k ∈ K, ρ k * x * (ρ k)⁻¹ = x) → x = 1)
    {v : Γ} (hv : v ∈ X) (hvR : ∀ r ∈ R, ρ r * v * (ρ r)⁻¹ = v) :
    v ∈ Subgroup.closure {y | ∃ k ∈ K, ∃ x ∈ X, y = ρ k * x * (ρ k)⁻¹ * x⁻¹} := by
  let _ : CommGroup ↥X :=
    { (inferInstance : Group ↥X) with mul_comm := fun a b => Subtype.ext (hXab _ a.2 _ b.2) }
  have : Fintype (Ĥ ⧸ R) := Fintype.ofFinite _
  let F : (Ĥ ⧸ R) → ↥X := fun c => Quotient.liftOn' c
    (fun c : Ĥ => (⟨ρ c * v * (ρ c)⁻¹, hnorm c v hv⟩ : ↥X))
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ R := QuotientGroup.leftRel_apply.mp hab
      have h1 := hvR _ hab'
      apply Subtype.ext
      have e1 : ρ b * v * (ρ b)⁻¹ = ρ a * (ρ (a⁻¹ * b) * v * (ρ (a⁻¹ * b))⁻¹) * (ρ a)⁻¹ := by
        simp only [map_mul, map_inv]; group
      show ρ a * v * (ρ a)⁻¹ = ρ b * v * (ρ b)⁻¹
      rw [e1, h1])
  have hF : ∀ c : Ĥ, F (QuotientGroup.mk c) = ⟨ρ c * v * (ρ c)⁻¹, hnorm c v hv⟩ := fun c => rfl
  let Φ : Ĥ → ↥X →* ↥X := fun q =>
    { toFun := fun x => ⟨ρ q * (x : Γ) * (ρ q)⁻¹, hnorm q _ x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hΦF : ∀ (q : Ĥ) (a : Ĥ ⧸ R), Φ q (F a) = F (q • a) := by
    intro q a
    induction a using QuotientGroup.induction_on with
    | H c =>
      rw [MulAction.Quotient.smul_mk, hF, hF]
      apply Subtype.ext
      show ρ q * (ρ c * v * (ρ c)⁻¹) * (ρ q)⁻¹ = ρ (q • c) * v * (ρ (q • c))⁻¹
      simp only [smul_eq_mul, map_mul]
      group
  let N : ↥X := ∏ a : Ĥ ⧸ R, F a
  have hNinv : ∀ q : Ĥ, Φ q N = N := by
    intro q
    simp only [N, map_prod]
    simp only [hΦF]
    exact Fintype.prod_equiv (MulAction.toPerm q) _ _ (fun a => rfl)
  have hN1 : N = 1 := by
    apply Subtype.ext
    apply hC _ N.2
    intro k hk
    exact congrArg Subtype.val (hNinv k)
  let v' : ↥X := ⟨v, hv⟩
  let Y' : Subgroup ↥X :=
    (Subgroup.closure {y | ∃ k ∈ K, ∃ x ∈ X, y = ρ k * x * (ρ k)⁻¹ * x⁻¹}).subgroupOf X
  have hy : ∀ a : Ĥ ⧸ R, F a * v'⁻¹ ∈ Y' := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨k, hk, r, hr, hc⟩ := hKR c
      rw [hF]
      show (ρ c * v * (ρ c)⁻¹) * v⁻¹ ∈ Subgroup.closure
        {y | ∃ k ∈ K, ∃ x ∈ X, y = ρ k * x * (ρ k)⁻¹ * x⁻¹}
      have h1 : ρ c * v * (ρ c)⁻¹ = ρ k * v * (ρ k)⁻¹ := by
        rw [hc]
        have := hvR r hr
        simp only [map_mul]
        calc ρ k * ρ r * v * (ρ k * ρ r)⁻¹ = ρ k * (ρ r * v * (ρ r)⁻¹) * (ρ k)⁻¹ := by group
          _ = ρ k * v * (ρ k)⁻¹ := by rw [this]
      rw [h1]
      exact Subgroup.subset_closure ⟨k, hk, v, hv, rfl⟩
  have hprod : N = (∏ a : Ĥ ⧸ R, (F a * v'⁻¹)) * v' ^ (Fintype.card (Ĥ ⧸ R)) := by
    have : ∀ a : Ĥ ⧸ R, F a = (F a * v'⁻¹) * v' := fun a => by simp
    calc N = ∏ a : Ĥ ⧸ R, ((F a * v'⁻¹) * v') := Finset.prod_congr rfl fun a _ => this a
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card (Ĥ ⧸ R) = R.index := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hv'2 : v' * v' = 1 := Subtype.ext (hX2 v hv)
  have hpow : v' ^ (Fintype.card (Ĥ ⧸ R)) = v' := by
    obtain ⟨m, hm⟩ := hodd
    have hsq : v' ^ 2 = 1 := by rw [sq]; exact hv'2
    rw [hcard, hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [hpow, hN1] at hprod
  have hP : (∏ a : Ĥ ⧸ R, (F a * v'⁻¹)) ∈ Y' := Subgroup.prod_mem _ fun a _ => hy a
  have hv'Y : v' ∈ Y' := by
    have : v' = (∏ a : Ĥ ⧸ R, (F a * v'⁻¹))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, mul_comm]
      exact hprod.symm
    rw [this]
    exact Y'.inv_mem hP
  exact Subgroup.mem_subgroupOf.mp hv'Y

end Abstract

section Good

variable {G : Type} [Group G]

theorem commutator_le_of_comm_le {H U W : Subgroup G} (hUH : U ≤ H) (hUe : IsElemAbelian 2 U)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hWU : IsNormalIn H U W)
    (hZ : ∀ k ∈ oTwoUpper H, ∀ y ∈ ⁅U, oTwoUpper H⁆, k * y * k⁻¹ * y⁻¹ ∈ W) :
    ⁅U, oTwoUpper H⁆ ≤ W := by
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := D14.le_normalizer_of_isNormalIn hWU
  have hodd : ∀ x ∈ H, Odd (orderOf x) → x ∈ centralizerMod W H U := by
    intro x hxH hxodd
    refine ⟨hxH, hHW hxH, fun u hu => ?_⟩
    have hxA : x ∈ Subgroup.normalizer (W : Set G) := hHW hxH
    have huA : u ∈ Subgroup.normalizer (W : Set G) := hHW (hUH hu)
    set w := x * u * x⁻¹ * u⁻¹ with hw
    have hxuU : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU hxH) u).mp hu
    have hwU : w ∈ U := U.mul_mem hxuU (U.inv_mem hu)
    have hwA : w ∈ Subgroup.normalizer (W : Set G) := hHW (hUH hwU)
    have hwK : w ∈ ⁅U, oTwoUpper H⁆ := by
      have := Subgroup.commutator_mem_commutator (mem_oTwoUpper_of_odd hxH hxodd) hu
      rw [Subgroup.commutator_comm] at this
      simpa [commutatorElement_def] using this
    have hZw := hZ x (mem_oTwoUpper_of_odd hxH hxodd) w hwK
    have hw2 : w * w = 1 := by
      have := hUe.2 w hwU
      rwa [sq] at this
    let xa : ↥(Subgroup.normalizer (W : Set G)) := ⟨x, hxA⟩
    let ua : ↥(Subgroup.normalizer (W : Set G)) := ⟨u, huA⟩
    let wa : ↥(Subgroup.normalizer (W : Set G)) := ⟨w, hwA⟩
    have hwa : wa = xa * ua * xa⁻¹ * ua⁻¹ := Subtype.ext rfl
    have hwbar : secMk (Subgroup.normalizer (W : Set G)) W wa =
        secMk _ W xa * secMk _ W ua * (secMk _ W xa)⁻¹ * (secMk _ W ua)⁻¹ := by
      rw [hwa]; simp only [map_mul, map_inv]
    have hxwa : secMk (Subgroup.normalizer (W : Set G)) W (xa * wa * xa⁻¹ * wa⁻¹) = 1 :=
      secMk_eq_one_iff.mpr hZw
    have hkr : (secMk (Subgroup.normalizer (W : Set G)) W xa) ^ (orderOf x) = 1 := by
      rw [← map_pow]
      have : xa ^ (orderOf x) = 1 := Subtype.ext (pow_orderOf_eq_one x)
      rw [this, map_one]
    have hww : secMk (Subgroup.normalizer (W : Set G)) W wa * secMk _ W wa = 1 := by
      rw [← map_mul]
      have : wa * wa = 1 := Subtype.ext hw2
      rw [this, map_one]
    have hkw : secMk (Subgroup.normalizer (W : Set G)) W xa * secMk _ W wa * (secMk _ W xa)⁻¹ =
        secMk _ W wa := by
      simp only [map_mul, map_inv] at hxwa
      exact mul_inv_eq_one.mp hxwa
    rw [hwbar] at hww hkw
    have key := comm_eq_one_of_odd hxodd hkr hww hkw
    exact secMk_eq_one_iff.mp (hwbar.trans key)
  have hKS : oTwoUpper H ≤ centralizerMod W H U := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxodd⟩
    exact hodd x hxH hxodd
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have h1 := (hKS hk).2.2 u hu
  have h2 := W.inv_mem h1
  rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ by rw [commutatorElement_def]; group] at h2

end Good

section GoodStep

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isNormalIn_sup_aux {H U A B : Subgroup G} (hA : IsNormalIn H U A) (hB : IsNormalIn H U B) :
    IsNormalIn H U (A ⊔ B) := by
  refine ⟨sup_le hA.1 hB.1, fun g hg x hx => ?_⟩
  rw [Subgroup.sup_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Or.inl (hA.2 g hg y hy))
    · exact Subgroup.subset_closure (Or.inr (hB.2 g hg y hy))
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ ih =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

omit [Finite G] in
theorem isNormalIn_commutator {H U K : Subgroup G} (hKH : K ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    IsNormalIn H U ⁅U, K⁆ := by
  refine ⟨?_, fun g hg x hx => ?_⟩
  · rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u⁻¹ * k⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hk)) u⁻¹).mp (U.inv_mem hu)
    have h2 := U.mul_mem hu h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using h2
  · induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      have h1 : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU hg) u).mp hu
      have h2 : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK hg) k).mp hk
      have h3 := Subgroup.commutator_mem_commutator h1 h2
      have e : g * ⁅u, k⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * k * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact h3
    | one => simp
    | mul a b _ _ iha ihb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ ih =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ih

theorem exists_good_step {H T U V : Subgroup G} (hT : IsSylowTwoOf T H) (hUT : U ≤ T)
    (hUe : IsElemAbelian 2 U) (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hVU : V ≤ U)
    (hgen : ∀ W : Subgroup G, IsNormalIn H U W → V ≤ W → U ≤ W)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hnc : ∃ L N : Subgroup G, IsChiefStep H U L N ∧ ¬ IsCentralStep H L N) :
    ∃ L N : Subgroup G, IsChiefStep H U L N ∧ ¬ IsCentralStep H L N ∧
      ∃ z ∈ V, z ∈ N ∧ z ∉ L ∧ ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ L := by
  classical
  obtain ⟨L₀, N₀, hstep₀, hnc₀⟩ := hnc
  have hTH : T ≤ H := hT.1
  have hUH : U ≤ H := hUT.trans hTH
  set K := oTwoUpper H with hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  set U₀ : Subgroup G := ⁅U, K⁆ with hU₀
  have hU₀N : IsNormalIn H U U₀ := isNormalIn_commutator hKH hHU hHK
  have hU₀ne : ¬ U₀ ≤ ⊥ := by
    intro hle
    apply hnc₀
    refine D15Proof.isCentralStep_of_commutator_le hT hUH (hstep₀.1.1.trans hUT) hstep₀ ?_
    exact (Subgroup.commutator_mono hstep₀.1.1 le_rfl).trans (hle.trans bot_le)
  let 𝒲 : Set (Subgroup G) := {W | IsNormalIn H U W ∧ ¬ U₀ ≤ W}
  have hbot : (⊥ : Subgroup G) ∈ 𝒲 :=
    ⟨⟨bot_le, fun g _ x hx => by rw [Subgroup.mem_bot.mp hx]; simp⟩, hU₀ne⟩
  obtain ⟨W, ⟨hWn, hWU₀⟩, hWmax⟩ := Set.Finite.exists_maximal (Set.toFinite 𝒲) ⟨⊥, hbot⟩
  have hmaxprop : ∀ W' : Subgroup G, IsNormalIn H U W' → W ≤ W' → W' ≠ W → U₀ ≤ W' := by
    intro W' hW' hWW' hne
    by_contra hcon
    exact hne (le_antisymm (hWmax ⟨hW', hcon⟩ hWW') hWW')
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := D14.le_normalizer_of_isNormalIn hWn
  have hN₁ : IsNormalIn H U (U₀ ⊔ W) := isNormalIn_sup_aux hU₀N hWn
  have hstep : IsChiefStep H U W (U₀ ⊔ W) := by
    refine ⟨hN₁, hWn, ?_, fun K' hK' hWK' hK'N => ?_⟩
    · exact lt_of_le_of_ne le_sup_right fun h => hWU₀ (h ▸ le_sup_left)
    · by_cases heq : K' = W
      · exact Or.inl heq
      · exact Or.inr (le_antisymm hK'N (sup_le (hmaxprop K' hK' hWK' heq) hWK'))
  have hnc₁ : ¬ IsCentralStep H W (U₀ ⊔ W) := by
    intro hcen
    apply hWU₀
    refine commutator_le_of_comm_le hUH hUe hHU hWn ?_
    intro k hk y hy
    exact hcen k (hKH hk) y ((le_sup_left : U₀ ≤ U₀ ⊔ W) hy)
  refine ⟨W, U₀ ⊔ W, hstep, hnc₁, ?_⟩
  have hVW : ¬ V ≤ W := fun h => hWU₀ (hU₀N.1.trans (hgen W hWn h))
  have hlt : V ⊓ W < V := lt_of_le_of_ne inf_le_left fun h => hVW (by rw [← h]; exact inf_le_right)
  have hTVW : T ≤ Subgroup.normalizer ((V ⊓ W : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hTV ht) x, Subgroup.mem_normalizer_iff.mp (hHW (hTH ht)) x]
  obtain ⟨z, hzV, hzW', hz⟩ := exists_fixed_mod hT.2.1 (hVU.trans hUT) hlt hTV hTVW
  have hzW : z ∉ W := fun h => hzW' ⟨hzV, h⟩
  have hzTW : ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ W := fun t ht => (hz t ht).2
  refine ⟨z, hzV, ?_, hzW, hzTW⟩
  have hHA : H ≤ Subgroup.normalizer (W : Set G) := hHW
  have hUA : U ≤ Subgroup.normalizer (W : Set G) := hUH.trans hHA
  let ρ : ↥H →* SecQuot (Subgroup.normalizer (W : Set G)) W :=
    (secMk (Subgroup.normalizer (W : Set G)) W).comp (Subgroup.inclusion hHA)
  let X : Subgroup (SecQuot (Subgroup.normalizer (W : Set G)) W) :=
    secImg (Subgroup.normalizer (W : Set G)) W U
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU2 : ∀ x ∈ U, x * x = 1 := fun x hx => by
    have := hUe.2 x hx
    rwa [sq] at this
  have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_secImg.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hUcomm _ ha _ hb)
  have hX2 : ∀ x ∈ X, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hx
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hU2 _ ha)
    rw [this, map_one]
  have hnorm : ∀ h : ↥H, ∀ x ∈ X, ρ h * x * (ρ h)⁻¹ ∈ X := by
    intro h x hx
    exact secMk_conj_mem_secImg (a := Subgroup.inclusion hHA h) (hHU h.2) hx
  have : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have hKT : K ⊔ T = H := by
    rw [sup_comm, hK, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hT
  have hKR : ∀ h : ↥H, ∃ k ∈ K.subgroupOf H, ∃ r ∈ T.subgroupOf H, h = k * r := by
    intro h
    have hsup : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, hKT, Subgroup.subgroupOf_self]
    have hh : h ∈ K.subgroupOf H ⊔ T.subgroupOf H := by rw [hsup]; exact Subgroup.mem_top h
    obtain ⟨k, hk, r, hr, hkr⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    exact ⟨k, hk, r, hr, hkr.symm⟩
  have hodd : Odd (T.subgroupOf H).index :=
    Nat.not_even_iff_odd.mp fun h => hT.2.2 (even_iff_two_dvd.mp h)
  have hCW : ∀ a : U, (∀ k ∈ K, a.1 * k * a.1⁻¹ * k⁻¹ ∈ W) → a.1 ∈ W := by
    intro a ha
    set C := centralizerMod W U K with hCdef
    have hCn : IsNormalIn H U C := by
      refine ⟨centralizerMod_le_left W U K, fun g hg x hx => ?_⟩
      have := le_normalizer_centralizerMod hHW hHU hHK hg
      exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
    have hWC : W ≤ C := by
      intro w hw
      refine ⟨hWn.1 hw, Subgroup.le_normalizer hw, fun k hk => ?_⟩
      have h1 : k * w⁻¹ * k⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hHW (hKH hk)) w⁻¹).mp (W.inv_mem hw)
      have h2 := W.mul_mem hw h1
      simpa [mul_assoc] using h2
    have haC : a.1 ∈ C := ⟨a.2, hHW (hUH a.2), ha⟩
    by_contra hna
    have hne : C ≠ W := fun h => hna (h ▸ haC)
    have hU₀C : U₀ ≤ C := hmaxprop C hCn hWC hne
    apply hWU₀
    refine commutator_le_of_comm_le hUH hUe hHU hWn ?_
    intro k hk y hy
    have h1 := (hU₀C hy).2.2 k hk
    have h2 := W.inv_mem h1
    rwa [show (y * k * y⁻¹ * k⁻¹)⁻¹ = k * y * k⁻¹ * y⁻¹ by group] at h2
  have hC : ∀ x ∈ X, (∀ k ∈ K.subgroupOf H, ρ k * x * (ρ k)⁻¹ = x) → x = 1 := by
    intro x hx hfix
    obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hx
    rw [secMk_eq_one_iff]
    refine hCW ⟨a, ha⟩ fun k hk => ?_
    have hkH : k ∈ H := hKH hk
    have hcomm := hfix ⟨k, hkH⟩ hk
    have hcomm' : ρ ⟨k, hkH⟩ * secMk _ W a = secMk _ W a * ρ ⟨k, hkH⟩ := by
      rw [mul_inv_eq_iff_eq_mul] at hcomm
      exact hcomm
    have h1 := commutator_mem_of_secMk_commute (A := Subgroup.normalizer (W : Set G)) (B := W)
      (x := a) (y := Subgroup.inclusion hHA ⟨k, hkH⟩) hcomm'.symm
    exact h1
  have hzA : z ∈ Subgroup.normalizer (W : Set G) := hUA (hVU hzV)
  have hv : secMk (Subgroup.normalizer (W : Set G)) W ⟨z, hzA⟩ ∈ X :=
    secMk_mem_secImg (hVU hzV)
  have hvR : ∀ r ∈ T.subgroupOf H, ρ r * secMk (Subgroup.normalizer (W : Set G)) W ⟨z, hzA⟩ *
      (ρ r)⁻¹ = secMk (Subgroup.normalizer (W : Set G)) W ⟨z, hzA⟩ := by
    intro r hr
    have hrT : (r : G) ∈ T := hr
    have hcomm := secMk_comm_of_commutator_mem (A := Subgroup.normalizer (W : Set G)) (K := W)
      (x := Subgroup.inclusion hHA r) (y := ⟨z, hzA⟩) (hzTW r hrT)
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  have hcl := norm_mem_commutator ρ hXab hX2 hnorm hKR hodd hC hv hvR
  have hle : Subgroup.closure {y | ∃ k ∈ K.subgroupOf H, ∃ x ∈ X, y = ρ k * x * (ρ k)⁻¹ * x⁻¹} ≤
      secImg (Subgroup.normalizer (W : Set G)) W U₀ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨k, hk, x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hx
    have hkK : (k : G) ∈ K := hk
    have hmem : ((Subgroup.inclusion hHA k * a * (Subgroup.inclusion hHA k)⁻¹ * a⁻¹ :
        ↥(Subgroup.normalizer (W : Set G))) : G) ∈ U₀ := by
      have := Subgroup.commutator_mem_commutator hkK ha
      rw [Subgroup.commutator_comm] at this
      simpa [commutatorElement_def] using this
    have := secMk_mem_secImg (A := Subgroup.normalizer (W : Set G)) (B := W) (X := U₀) hmem
    simpa [ρ, map_mul, map_inv] using this
  obtain ⟨x, hxU₀, hxz⟩ := mem_secImg.mp (hle hcl)
  have hxW := secMk_eq_secMk_iff.mp hxz
  have hzeq : z = (x : G) * ((x : G)⁻¹ * z) := by group
  rw [hzeq]
  exact Subgroup.mul_mem_sup hxU₀ hxW

end GoodStep

end Ch3z

end CFSG.Quasithin
