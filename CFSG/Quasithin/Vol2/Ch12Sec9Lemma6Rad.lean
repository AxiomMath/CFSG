module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Irr
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9W0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

namespace L1296

variable {G : Type} [Group G]

theorem commutator_lt_self [Finite G] {T V : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) : ⁅V, T⁆ < V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine lt_of_le_of_ne (Subgroup.le_normalizer_iff_commutator_le_left.1 hTV) fun h => hV ?_
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries T).mp hnil
  have key : ∀ k, V ≤ T.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hVT
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact Subgroup.commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hm]
  exact key m

theorem commutator_lt [Finite G] {T V D : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hDT : D ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) : ⁅V, D⁆ < V :=
  lt_of_le_of_lt (Subgroup.commutator_mono le_rfl hDT) (commutator_lt_self hT hVT hTV hV)

theorem le_normalizer_commutator {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  refine LinearS3.le_normalizer_of_conj_mem fun k hk x hx => ?_
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : k * ⁅a, b⁆ * k⁻¹ = ⁅k * a * k⁻¹, k * b * k⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨_, (Subgroup.mem_normalizer_iff.1 (hA hk) a).1 ha, _,
      (Subgroup.mem_normalizer_iff.1 (hB hk) b).1 hb, rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem le_of_isPGroup [Finite G] {T P : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hP : IsPGroup 2 P) (hTP : T ≤ Subgroup.normalizer (P : Set G)) : P ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 ↥(P ⊔ T) := IsPGroup.to_sup_of_normal_left' hP hT.1 hTP
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hk ▸ Subgroup.relIndex_dvd_card T (P ⊔ T))
  have h1 := Subgroup.relIndex_dvd_index_of_le (le_sup_right : T ≤ P ⊔ T)
  rw [hj] at h1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hT.2 ((dvd_pow_self 2 hj0).trans h1)
  rw [hj0, pow_zero] at hj
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 hj)

theorem le_normalizer_centralizerMod {V₁ X U Y : Subgroup G}
    (hX : Y ≤ Subgroup.normalizer (X : Set G)) (hV₁ : Y ≤ Subgroup.normalizer (V₁ : Set G))
    (hU : Y ≤ Subgroup.normalizer (U : Set G)) :
    Y ≤ Subgroup.normalizer (centralizerMod V₁ X U : Set G) := by
  refine LinearS3.le_normalizer_of_conj_mem fun k hk x hx => ?_
  obtain ⟨hxX, hxN, hxc⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 (hX hk) x).1 hxX,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hV₁ hk) hxN) (Subgroup.inv_mem _ (hV₁ hk)),
    fun u hu => ?_⟩
  have hu' : k⁻¹ * u * k ∈ U := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hU hk)) u).1 hu
    rwa [inv_inv] at h1
  have h2 := (Subgroup.mem_normalizer_iff.1 (hV₁ hk) _).1 (hxc _ hu')
  rwa [show k * (x * (k⁻¹ * u * k) * x⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ =
    k * x * k⁻¹ * u * (k * x * k⁻¹)⁻¹ * u⁻¹ by group] at h2

@[expose] noncomputable def ind (a : G) : ZMod 2 := by
  classical
  exact if a = 1 then 0 else 1

theorem ind_mul [Finite G] {D : Subgroup G} (hD : Nat.card D = 2) (hsq : ∀ d ∈ D, d ^ 2 = 1)
    {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) : ind (a * b) = ind a + ind b := by
  classical
  unfold ind
  by_cases ha1 : a = 1
  · subst ha1
    simp
  by_cases hb1 : b = 1
  · subst hb1
    simp
  have e := SteinbergBS.eq_of_card_le_two hD.le ha hb ha1 hb1
  subst e
  have h1 : a * a = 1 := by rw [← sq]; exact hsq a ha
  rw [h1, ite_eq_left rfl, ite_eq_right ha1]
  decide

theorem card_le_of_commutator_mem [Finite G] {V V₁ R : Subgroup G} {n : ℕ}
    (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (h2 : ∀ v ∈ V, v ^ 2 = 1) (hVn : Nat.card V = 2 ^ n)
    (hV₁V : V₁ ≤ V) (hV₁2 : Nat.card V₁ = 2) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hRc : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ * v⁻¹ ∈ V₁)
    (hRV₁ : ∀ r ∈ R, ∀ x ∈ V₁, r * x * r⁻¹ = x) :
    Nat.card R ≤ 2 ^ (n - 1) * Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
  let _ := zmodModuleOf h2
  have hsq₁ : ∀ d ∈ V₁, d ^ 2 = 1 := fun d hd => h2 d (hV₁V hd)
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ V₁, z ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    rw [hbot, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  set c : G → G → G := fun r v => r * v * r⁻¹ * v⁻¹ with hcdef
  have hcmul : ∀ r ∈ R, ∀ v ∈ V, ∀ w ∈ V, c r (v * w) = c r v * c r w := by
    intro r hr v hv w hw
    have hA : r * v * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hRV hr) v).1 hv
    have hB : r * w * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hRV hr) w).1 hw
    have e1 : v⁻¹ * (r * w * r⁻¹) = (r * w * r⁻¹) * v⁻¹ := hab _ (V.inv_mem hv) _ hB
    have e2 : v⁻¹ * w⁻¹ = w⁻¹ * v⁻¹ := hab _ (V.inv_mem hv) _ (V.inv_mem hw)
    calc c r (v * w) = (r * v * r⁻¹) * (r * w * r⁻¹) * (w⁻¹ * v⁻¹) := by
          simp only [hcdef]; group
      _ = (r * v * r⁻¹) * (r * w * r⁻¹) * (v⁻¹ * w⁻¹) := by rw [e2]
      _ = (r * v * r⁻¹) * (v⁻¹ * (r * w * r⁻¹)) * w⁻¹ := by rw [e1]; group
      _ = c r v * c r w := by simp only [hcdef]; group
  let f : ↥R → (Additive ↥V →+ ZMod 2) := fun r =>
    { toFun := fun x => ind (c (r : G) ((Additive.toMul x : ↥V) : G))
      map_zero' := by
        show ind ((r : G) * ((1 : ↥V) : G) * (r : G)⁻¹ * ((1 : ↥V) : G)⁻¹) = 0
        simp [ind]
      map_add' := fun x y => by
        show ind (c (r : G) (((Additive.toMul x * Additive.toMul y : ↥V)) : G)) = _
        rw [Subgroup.coe_mul, hcmul r r.2 _ (Additive.toMul x).2 _ (Additive.toMul y).2]
        exact ind_mul hV₁2 hsq₁ (hRc r r.2 _ (Additive.toMul x).2)
          (hRc r r.2 _ (Additive.toMul y).2) }
  have hf : ∀ r x, f r x = ind (c (r : G) ((Additive.toMul x : ↥V) : G)) := fun _ _ => rfl
  have hcrs : ∀ r ∈ R, ∀ s ∈ R, ∀ v ∈ V, c (r * s) v = c s v * c r v := by
    intro r hr s hs v hv
    have h1 : r * c s v * r⁻¹ = c s v := hRV₁ r hr _ (hRc s hs v hv)
    calc c (r * s) v = (r * c s v * r⁻¹) * c r v := by simp only [hcdef]; group
      _ = c s v * c r v := by rw [h1]
  let ψ : ↥R →* Multiplicative (Additive ↥V →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun r => Multiplicative.ofAdd (AddMonoidHom.toZModLinearMap 2 (f r))
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply LinearMap.ext
        intro x
        show f 1 x = 0
        rw [hf]
        simp [hcdef, ind]
      map_mul' := fun r s => by
        apply Multiplicative.toAdd.injective
        apply LinearMap.ext
        intro x
        show f (r * s) x = f r x + f s x
        rw [hf, hf, hf, Subgroup.coe_mul, hcrs r r.2 s s.2 _ (Additive.toMul x).2,
          ind_mul hV₁2 hsq₁ (hRc s s.2 _ (Additive.toMul x).2) (hRc r r.2 _ (Additive.toMul x).2),
          add_comm] }
  have hψ : ∀ r x, (Multiplicative.toAdd (ψ r)) x = ind (c (r : G) ((Additive.toMul x : ↥V) : G)) :=
    fun _ _ => rfl
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun r => ⟨((r : ↥R) : G), (r : ↥R).2, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩)
      (fun r s hrs => by
        have h1 := congrArg Subtype.val hrs
        exact Subtype.ext (Subtype.ext h1))
    have h1 := LinearMap.congr_fun (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 r.2))
      (Additive.ofMul (⟨v, hv⟩ : ↥V))
    rw [hψ] at h1
    simp only [toMul_ofMul, toAdd_one, LinearMap.zero_apply] at h1
    have h2 : c ((r : ↥R) : G) v = 1 := by
      by_contra hne
      simp [ind, hne] at h1
    simp only [hcdef] at h2
    calc v * ((r : ↥R) : G) = (((r : ↥R) : G) * v * ((r : ↥R) : G)⁻¹ * v⁻¹)⁻¹ *
          (((r : ↥R) : G) * v) := by group
      _ = ((r : ↥R) : G) * v := by rw [h2, inv_one, one_mul]
  have : Finite (Additive ↥V →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f : Additive ↥V →ₗ[ZMod 2] ZMod 2 => (f : Additive ↥V → ZMod 2))
      DFunLike.coe_injective
  set ev := LinearMap.applyₗ (R := ZMod 2) (M₂ := ZMod 2)
    (Additive.ofMul (⟨z, hV₁V hz⟩ : ↥V)) with hev
  have hrange : Nat.card ψ.range ≤ Nat.card ↥(LinearMap.ker ev) := by
    refine Nat.card_le_card_of_injective
      (fun y => ⟨Multiplicative.toAdd (y : Multiplicative (Additive ↥V →ₗ[ZMod 2] ZMod 2)), ?_⟩)
      (fun y y' hyy => by
        have h1 := congrArg Subtype.val hyy
        exact Subtype.ext (Multiplicative.toAdd.injective h1))
    obtain ⟨r, hr⟩ := y.2
    rw [LinearMap.mem_ker, hev, LinearMap.applyₗ_apply_apply, ← hr, hψ, toMul_ofMul]
    have h1 : c ((r : ↥R) : G) z = 1 := by
      simp only [hcdef]
      rw [hRV₁ _ r.2 z hz, mul_inv_cancel]
    rw [h1]
    simp [ind]
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive ↥V) = 2 ^ n := hVn
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h3)
  have hdual : Module.finrank (ZMod 2) (Additive ↥V →ₗ[ZMod 2] ZMod 2) = n := by
    rw [Module.finrank_linearMap, hrank, Module.finrank_self, mul_one]
  have hz0 : Additive.ofMul (⟨z, hV₁V hz⟩ : ↥V) ∉ (⊥ : Submodule (ZMod 2) (Additive ↥V)) := by
    rw [Submodule.mem_bot]
    intro h0
    apply hz1
    have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) h0
    simpa using this
  obtain ⟨φ, hφ, -⟩ := Submodule.exists_le_ker_of_notMem hz0
  have hevne : LinearMap.range ev ≠ ⊥ := by
    intro hb
    apply hφ
    have h1 : ev φ ∈ LinearMap.range ev := LinearMap.mem_range_self ev φ
    rw [hb, Submodule.mem_bot, hev, LinearMap.applyₗ_apply_apply] at h1
    exact h1
  have hr1 : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range ev) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hevne)
  have hk := LinearMap.finrank_range_add_finrank_ker ev
  rw [hdual] at hk
  have hcardk : Nat.card ↥(LinearMap.ker ev) ≤ 2 ^ (n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [← hmul, mul_comm]
  exact Nat.mul_le_mul (hrange.trans hcardk) hker

variable [Finite G]

theorem le_of_tinv_of_lOne (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ W : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hWV : W ≤ V)
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hLW : lOne L V₁ ≤ Subgroup.normalizer (W : Set G)) (hne : W ≠ V) : W ≤ V₁ := by
  rcases tinv_comparable_of_hyp1281One h1222 h hWV hV₁.1 hTW hV₁.2.2 with hle | hle
  · exact hle
  · rcases eq_or_eq_of_lOne_le_normalizer h hV₁ hle hWV hLW with heq | heq
    · exact heq.le
    · exact absurd heq hne

theorem lOne_le_normalizer {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    (V₁ : Subgroup G) : lOne L V₁ ≤ Subgroup.normalizer (V : Set G) :=
  (oTwoUpper_le _).trans (inf_le_left.trans h.hyp.irrPlus.2.2.1)

theorem le_centralizer_of_le_T (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ Y : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hYT : Y ≤ T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hLY : lOne L V₁ ≤ Subgroup.normalizer (Y : Set G))
    (hLYc : ∀ l ∈ lOne L V₁, ∀ y ∈ Y, l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    Y ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hW : ⁅V, Y⁆ ≤ V₁ :=
    le_of_tinv_of_lOne h1222 h hV₁ (Subgroup.le_normalizer_iff_commutator_le_left.1
      (hYT.trans hTV)) (le_normalizer_commutator hTV hTY)
      (le_normalizer_commutator (lOne_le_normalizer h V₁) hLY)
      (commutator_lt h.hyp.sylow.1 hVT hYT hTV h.hyp.irrPlus.2.1).ne
  refine L1299.le_centralizer_of_commutator_le_lOne h hV₁ (hYT.trans hV₁.2.2)
    (fun v hv y hy => ?_) hLYc
  have h1 := V₁.inv_mem (hW (Subgroup.commutator_mem_commutator hv hy))
  rwa [commutatorElement_def, show (v * y * v⁻¹ * y⁻¹)⁻¹ = y * v * y⁻¹ * v⁻¹ by group] at h1

theorem pCoreOf_le_T {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n) (V₁ : Subgroup G) :
    pCoreOf 2 (lOne L V₁ ⊔ T) ≤ T :=
  le_of_isPGroup h.hyp.sylow (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (le_sup_right.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem commutator_pCoreOf_le (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ⁅V, pCoreOf 2 (lOne L V₁ ⊔ T)⁆ ≤ V₁ := by
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hRT := pCoreOf_le_T h V₁
  have hN := LieType.BorelTits.le_normalizer_pCoreOf 2 (lOne L V₁ ⊔ T)
  exact le_of_tinv_of_lOne h1222 h hV₁
    (Subgroup.le_normalizer_iff_commutator_le_left.1 (hRT.trans hTV))
    (le_normalizer_commutator hTV (le_sup_right.trans hN))
    (le_normalizer_commutator (lOne_le_normalizer h V₁) (le_sup_left.trans hN))
    (commutator_lt h.hyp.sylow.1 hVT hRT hTV h.hyp.irrPlus.2.1).ne

theorem inf_centralizer_le_pCoreOf (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (V₁ : Subgroup G) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (lOne L V₁ ⊔ T) := by
  have hN := (inf_centralizer_eq_sup_inf_centralizer h1222 h).2
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    ((sup_le_sup_right hL₁L T).trans hN) (h.hyp.sylow.1.to_le inf_le_left)

theorem card_pCoreOf_le (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    Nat.card ↥(pCoreOf 2 (lOne L V₁ ⊔ T)) ≤
      2 ^ (n - 1) * Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hRT := pCoreOf_le_T h V₁
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hc := commutator_pCoreOf_le h1222 h hV₁
  have h1 := card_le_of_commutator_mem hab hsq hcard hV₁.1 hV₁2 (hRT.trans hTV)
    (fun r hr v hv => by
      have h2 := V₁.inv_mem (hc (Subgroup.commutator_mem_commutator hv hr))
      rwa [commutatorElement_def, show (v * r * v⁻¹ * r⁻¹)⁻¹ = r * v * r⁻¹ * v⁻¹ by group] at h2)
    (fun r hr x hx => by
      have h2 := Subgroup.mem_centralizer_iff.1
        (le_centralizer_normalizer_of_card_eq_two hV₁2 hx) r (hV₁.2.2 (hRT hr))
      rw [h2, mul_inv_cancel_right])
  exact h1.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (inf_le_inf_right _ hRT)))

theorem inf_centralizer_lt_pCoreOf (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    T ⊓ Subgroup.centralizer (V : Set G) < pCoreOf 2 (lOne L V₁ ⊔ T) := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hn2 : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one hT2 hsq hab hTV hcard hn2 hV₁
  obtain ⟨v₁, hv₁, hv₁1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    rw [hbot, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  obtain ⟨v₂, hv₂, hv₂1⟩ : ∃ v ∈ V₂, v ∉ V₁ := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from hne)
    rw [hV₂.2.1, hV₁.2.1] at h1
    norm_num at h1
  have hv₁V := hV₁.1 hv₁
  have hv₂V := hV₂.1 hv₂
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨v₁, hv₁V⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨v₂, hv₂V⟩ with ha₂
  have ha : a₂ ∉ (ZMod 2) ∙ a₁ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₂, toMul_ofMul, toMul_zero, OneMemClass.coe_one] at this
      rw [← this]
      exact V₁.one_mem
    · rw [one_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [← this]
      exact hv₁
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₁ : f a₁ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₁))
  have hfa₂ : f a₂ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₁
  have hτ0 : ∀ x, τ0 x = x + f x • a₁ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₁, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * v₁ := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₁) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₁, toMul_ofMul]
  have hα₂ : ((α ⟨v₂, hv₂V⟩ : ↥V) : G) = v₂ * v₁ := by
    show ((Additive.toMul (τ0 a₂) : ↥V) : G) = _
    rw [hτ0, hfa₂, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]
  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hgL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl
  have hgV₁ : ∀ x ∈ V₁, g * x * g⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      group
    have e := SteinbergBS.eq_of_card_le_two hV₁2.le hx hv₁ hx1 hv₁1
    subst e
    rw [hconj x hv₁V]
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = x
    rw [hτ0, hfa₁, zero_smul, add_zero, ha₁, toMul_ofMul]
  have hgN₁ : g ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => by
      have := hgV₁ x hx
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group)
  set E := centralizerMod V₁ (L ⊔ T) V with hEdef
  have hgE : g ∈ E := by
    refine ⟨Subgroup.mem_sup_left hgL, hgN₁, fun u hu => ?_⟩
    rw [hconj u hu]
    rcases hα ⟨u, hu⟩ with e | e
    · rw [e, mul_inv_cancel]
      exact V₁.one_mem
    · rw [e, show u * v₁ * u⁻¹ = v₁ from by
        rw [hab u hu v₁ hv₁V]; group]
      exact hv₁
  have hQ := (inf_centralizer_eq_sup_inf_centralizer h1222 h).1
  have hEp : IsPGroup 2 E := by
    intro x
    obtain ⟨hxX, hxN, hxc⟩ := x.2
    have hx2 : (x : G) * (x : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
      rw [hQ]
      refine ⟨Subgroup.mul_mem _ hxX hxX, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      set c := (x : G) * u * (x : G)⁻¹ * u⁻¹ with hcdef
      have hd : c ∈ V₁ := hxc u hu
      have hxc' : (x : G) * c * (x : G)⁻¹ = c := by
        have h1 := Subgroup.mem_centralizer_iff.1
          (le_centralizer_normalizer_of_card_eq_two hV₁2 hd) _ hxN
        rw [h1, mul_inv_cancel_right]
      have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hd)
      have hxu : (x : G) * u * (x : G)⁻¹ = c * u := by rw [hcdef]; group
      have key : (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ = u := by
        calc (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ =
              (x : G) * ((x : G) * u * (x : G)⁻¹) * (x : G)⁻¹ := by group
          _ = (x : G) * (c * u) * (x : G)⁻¹ := by rw [hxu]
          _ = ((x : G) * c * (x : G)⁻¹) * ((x : G) * u * (x : G)⁻¹) := by group
          _ = c * (c * u) := by rw [hxc', hxu]
          _ = u := by rw [← mul_assoc, hcc, one_mul]
      calc u * ((x : G) * (x : G)) =
            ((x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹) * ((x : G) * (x : G)) := by
            rw [key]
        _ = (x : G) * (x : G) * u := by group
    obtain ⟨k, hk⟩ := (hT2.to_le inf_le_left) ⟨_, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hTE : T ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_centralizerMod (le_sup_right.trans Subgroup.le_normalizer) hV₁.2.2 hTV
  have hET : E ≤ T := le_of_isPGroup h.hyp.sylow hEp hTE
  have hL₁E : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (E : Set G) := by
    refine sup_le (le_normalizer_centralizerMod ?_ ?_ (lOne_le_normalizer h V₁)) hTE
    · exact ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)).trans Subgroup.le_normalizer
    · exact (oTwoUpper_le _).trans inf_le_right
  have hER : E ≤ pCoreOf 2 (lOne L V₁ ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hET.trans le_sup_right) hL₁E hEp
  refine lt_of_le_of_ne (inf_centralizer_le_pCoreOf h1222 h V₁) fun heq => ?_
  have hgQ : g ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [heq]
    exact hER hgE
  have h1 := Subgroup.mem_centralizer_iff.1 hgQ.2 v₂ hv₂V
  have h2 : g * v₂ * g⁻¹ = v₂ := by rw [← h1]; group
  rw [hconj v₂ hv₂V, hα₂] at h2
  apply hv₁1
  calc v₁ = v₂⁻¹ * (v₂ * v₁) := by group
    _ = 1 := by rw [h2, inv_mul_cancel]

end L1296

end CFSG.Quasithin.H13
