module

public import CFSG.Quasithin.H13.A5Setting
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.F9Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

theorem eq_one_of_fix_W3 : ∀ σ : Equiv.Perm (Fin 5),
    (∀ x : W5, c4 x = 1 → pact σ x = x) → σ = 1 := by
  decide +kernel

theorem K4_not_quadratic : ∀ σ τ : Equiv.Perm (Fin 5), InK4 σ → InK4 τ → σ ≠ 1 → τ ≠ 1 →
    σ ≠ τ → ∃ x : W5, pact τ (pact σ x * x⁻¹) ≠ pact σ x * x⁻¹ := by
  decide +kernel

theorem card_fix_K4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ ≠ 1 →
    Fintype.card {x : W5 // pact σ x = x} = 4 := by
  decide +kernel

theorem InK4_of_comm : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 →
    (∀ x : W5, c4 x = 1 → pact σ x * x⁻¹ = 1 ∨ pact σ x * x⁻¹ = W4) → InK4 σ := by
  decide +kernel

section General

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_oTwoRes_eq_bot {K : Subgroup G} (h : oTwoRes K = ⊥) : IsPGroup 2 K := by
  intro x
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  have hx : (x : G) ^ (2 ^ a) ∈ oTwoRes K := by
    refine Subgroup.subset_closure ⟨K.pow_mem x.2 _, m, hm, ?_⟩
    rw [← pow_mul]
    have : (x : G) ^ (2 ^ a * m) = 1 := by
      rw [← hnm, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    exact this
  rw [h, Subgroup.mem_bot] at hx
  exact Subtype.ext (by simpa using hx)

omit [Finite G] in
theorem conj_eq_of_odd_of_comm {U V₁ : Subgroup G} (hU : IsElemAbelian 2 U) (hV₁U : V₁ ≤ U)
    {g : G} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) (hgV₁ : ∀ c ∈ V₁, g * c * g⁻¹ = c)
    (hg : ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ V₁) {u : G} (hu : u ∈ U) : g * u * g⁻¹ = u := by
  set c := g * u * g⁻¹ * u⁻¹ with hc
  have hcV : c ∈ V₁ := hg u hu
  have h1 : g * u * g⁻¹ = c * u := by rw [hc]; group
  have h2 : g ^ 2 * u * (g ^ 2)⁻¹ = u := by
    have hc2 : c * c = 1 := by
      have := hU.2 c (hV₁U hcV)
      rwa [pow_two] at this
    calc g ^ 2 * u * (g ^ 2)⁻¹ = g * (g * u * g⁻¹) * g⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = g * (c * u) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * (g * u * g⁻¹) := by group
      _ = c * (c * u) := by rw [hgV₁ c hcV, h1]
      _ = u := by rw [← mul_assoc, hc2, one_mul]
  obtain ⟨k, rfl⟩ := hm
  have hcomm : Commute (g ^ 2) u := by
    rw [Commute, SemiconjBy]
    calc g ^ 2 * u = g ^ 2 * u * (g ^ 2)⁻¹ * g ^ 2 := by group
      _ = u * g ^ 2 := by rw [h2]
  have hg' : g = (g ^ 2) ^ (k + 1) := by
    calc g = g * g ^ (2 * k + 1) := by rw [hgm, mul_one]
      _ = (g ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ']; ring_nf
  have : Commute g u := by
    rw [hg']
    exact hcomm.pow_left _
  calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [this.eq]
    _ = u := by group

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {Y P : Subgroup G} (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hx : x ∈ Y ⊔ P) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) : x ∈ Y := by
  have hYn : (Y.subgroupOf (Y ⊔ P)).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hb : (b : G) ∈ Subgroup.normalizer (Y : Set G) :=
      (sup_le Subgroup.le_normalizer hPY) b.2
    simpa using (Subgroup.mem_normalizer_iff.mp hb a).mp ha
  let π := QuotientGroup.mk' (Y.subgroupOf (Y ⊔ P))
  have hPle : P ≤ Y ⊔ P := le_sup_right
  have hsurj : ∀ q : ↥(Y ⊔ P) ⧸ Y.subgroupOf (Y ⊔ P), ∃ p : P, π ⟨p, hPle p.2⟩ = q := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hw' : w ∈ (Y : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y P hPY]
      exact hw
    obtain ⟨y, hy, p, hp, rfl⟩ := Set.mem_mul.1 hw'
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp (hPY (P.inv_mem hp)) y).mp hy
    simpa [mul_assoc] using this
  obtain ⟨p, hp⟩ := hsurj (π ⟨x, hx⟩)
  obtain ⟨k, hk⟩ := hP p
  have h2 : (π ⟨x, hx⟩) ^ (2 ^ k) = 1 := by
    rw [← hp, ← map_pow]
    have : (⟨(p : G), hPle p.2⟩ : ↥(Y ⊔ P)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hodd : (π ⟨x, hx⟩) ^ m = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(Y ⊔ P)) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have h1 : π ⟨x, hx⟩ = 1 := by
    have := pow_gcd_eq_one.2 ⟨h2, hodd⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite G] in
theorem card_conjSub' (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {l y : G}
    (hl : l ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have hv' : l⁻¹ * v * l ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hl) v).mp hv
    simpa using this
  have key := hy _ hv'
  calc v * (l * y * l⁻¹) = l * ((l⁻¹ * v * l) * y) * l⁻¹ := by group
    _ = l * (y * (l⁻¹ * v * l)) * l⁻¹ := by rw [key]
    _ = l * y * l⁻¹ * v := by group

omit [Finite G] in
theorem le_normalizer_of_forall_conj_mem {X Y : Subgroup G}
    (h : ∀ l ∈ X, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) : X ≤ Subgroup.normalizer (Y : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h l hl y, fun hy => ?_⟩
  have := h l⁻¹ (X.inv_mem hl) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_oTwoRes_of_gen {X K : Subgroup G}
    (h : ∀ l ∈ X, ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) → l * y * l⁻¹ ∈ oTwoRes K) :
    X ≤ Subgroup.normalizer (oTwoRes K : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun l hl y hy => ?_
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h l hl y hy.1 hy.2
  | one => simp
  | mul a b _ _ ha hb =>
    have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
    rw [e]
    exact (oTwoRes K).mul_mem ha hb
  | inv a _ ha =>
    have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
    rw [e]
    exact (oTwoRes K).inv_mem ha

omit [Finite G] in
theorem le_normalizer_oTwoRes_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) : H ≤ Subgroup.normalizer (oTwoRes K : Set G) := by
  refine le_normalizer_oTwoRes_of_gen fun l hl y hy ⟨m, hm, hym⟩ => ?_
  refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (h hl) y).mp hy, m, hm, ?_⟩
  rw [conj_pow, hym]
  group

omit [Finite G] in
theorem conjSub_self_of_mem {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g X = X := by
  ext x
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x
  rw [inv_inv] at this
  exact this.symm

end General

@[expose] def Input1323Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

@[expose] noncomputable def G1 : Subgroup G := Subgroup.centralizer ({S.z} : Set G)

@[expose] def Hz : Set (Subgroup G) :=
  {H | InH (S.L1 ⊔ T) H ∧ H ≤ S.G1 ∧ ¬ H ≤ Subgroup.normalizer (L : Set G)}

theorem G1_eq_normalizer : S.G1 = Subgroup.normalizer (S.V1 : Set G) := S.normalizer_V1.symm

theorem centralizer_V1 : Subgroup.centralizer (S.V1 : Set G) = S.G1 := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact S.mem_V1.2 (Or.inr rfl))
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases S.mem_V1.1 hx with rfl | rfl
    · simp
    · exact ((Subgroup.mem_centralizer_singleton_iff.mp hg)).symm

theorem o2_eq_bot_of_not_le {X : Subgroup G} (hLT : L ⊔ T ≤ X)
    (hX : ¬ X ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 X = ⊥ := by
  by_contra h
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, h, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hXM' : X ≤ M' := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans hle
  have := S.uniqueM.2 M' ⟨hM', hLT.trans hXM'⟩
  exact hX (this ▸ hXM')

theorem mem_centralizer_V_of_V3 {x : G} (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.centralizer (S.V3 : Set G)) : x ∈ Subgroup.centralizer (V : Set G) := by
  have hρ : S.frame.ρ ⟨x, hxN⟩ = 1 := by
    refine eq_one_of_fix_W3 _ fun w hw => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective w
    have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by simpa using mem_W3.2 hw⟩
    have := (S.conj_eq_iff ⟨x, hxN⟩ v).1 (by
      have := Subgroup.mem_centralizer_iff.mp hx v hv3
      calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [this]
        _ = v := by group)
    exact this
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := (S.conj_eq_iff ⟨x, hxN⟩ ⟨v, hv⟩).2 (by rw [hρ, map_one, MulAut.one_apply])
  calc v * x = x * v * x⁻¹ * x := by rw [this]
    _ = x * v := by group

theorem coreIn_le_pCoreOf (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    coreIn (centralizerMod S.V1 H S.V3) H ≤ pCoreOf 2 H := by
  set K := coreIn (centralizerMod S.V1 H S.V3) H with hKdef
  have hKH : K ≤ H := coreIn_le_left _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_coreIn _ _
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG1 : H ≤ S.G1 := hH.2.1
  have hgenV3 : ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) →
      y ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rintro y hyK ⟨m, hm, hym⟩
    have hyC : y ∈ centralizerMod S.V1 H S.V3 := coreIn_le_right _ _ hyK
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyz : ∀ c ∈ S.V1, y * c * y⁻¹ = c := by
      intro c hc
      have hyG1 := hHG1 (hKH hyK)
      rw [← S.centralizer_V1] at hyG1
      have := Subgroup.mem_centralizer_iff.mp hyG1 c hc
      calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [this]
        _ = c := by group
    have := conj_eq_of_odd_of_comm (U := S.V3) (V₁ := S.V1)
      (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) S.V1_le_V3 hm hym hyz hyC.2.2 hu
    calc u * y = y * u * y⁻¹ * y := by rw [this]
      _ = y * u := by group
  have hgenV : ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) → y ∈ Subgroup.centralizer (V : Set G) := by
    intro y hyK hy
    have hy3 := hgenV3 y hyK hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
      h1323 G T L V S (Subgroup.centralizer_le_normalizer (S.V3 : Set G) hy3)
    exact S.mem_centralizer_V_of_V3 hyN hy3
  have hYV : oTwoRes K ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.closure_le _).2 fun y hy => hgenV y hy.1 hy.2
  have hYH : H ≤ Subgroup.normalizer (oTwoRes K : Set G) :=
    le_normalizer_oTwoRes_of_le_normalizer hHK
  have hLY : L ≤ Subgroup.normalizer (oTwoRes K : Set G) := by
    refine le_normalizer_oTwoRes_of_gen fun l hl y hyK ⟨m, hm, hym⟩ => ?_
    have hyY : y ∈ oTwoRes K := Subgroup.subset_closure ⟨hyK, m, hm, hym⟩
    have hyCV : y ∈ Subgroup.centralizer (V : Set G) := hYV hyY
    have hyM : y ∈ Subgroup.normalizer (L : Set G) :=
      S.NV_le_M (Subgroup.centralizer_le_normalizer (V : Set G) hyCV)
    have hcomm : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
      rw [← S.cLT]
      refine ⟨le_sup_left (a := L) ?_, ?_⟩
      · have : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyM _).mp (L.inv_mem hl)
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact L.mul_mem hl this
      · have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hl
        have h1 : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          conj_mem_centralizer_of_mem_normalizer hlN hyCV
        exact (Subgroup.centralizer (V : Set G)).mul_mem h1
          ((Subgroup.centralizer (V : Set G)).inv_mem hyCV)
    have hmem : l * y * l⁻¹ ∈ oTwoRes K ⊔ pCoreOf 2 (L ⊔ T) := by
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem _ (le_sup_right (a := oTwoRes K) hcomm)
        (le_sup_left (a := oTwoRes K) hyY)
    refine mem_of_odd_of_mem_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      ((S.pCoreOf_LT_le_T.trans hTH).trans hYH) hmem hm ?_
    rw [conj_pow, hym]
    group
  have hY : oTwoRes K = ⊥ := by
    by_contra hY
    have hchar : CharTwo (oTwoRes K) :=
      A4.charTwo_of_normal ((oTwoRes_le K).trans hKH) hYH
        (S.charTwo_of_inH ⟨hTH, hH.1.2⟩)
    have hO2 : pCoreOf 2 (oTwoRes K) ≠ ⊥ := by
      intro h0
      apply hY
      have hle : oTwoRes K ≤ oTwoRes K ⊓
          Subgroup.centralizer (pCoreOf 2 (oTwoRes K) : Set G) := by
        intro x hx
        refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [h0] at hy
        rw [show y = 1 from hy]
        simp
      have := hle.trans hchar
      rw [h0] at this
      exact le_bot_iff.mp this
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (oTwoRes K) : Set G)) :=
      ⟨_, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoRes K)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hLTM' : L ⊔ T ≤ M' := sup_le (hLY.trans (hN.trans hle))
      ((hTH.trans hYH).trans (hN.trans hle))
    have := S.uniqueM.2 M' ⟨hM', hLTM'⟩
    exact hH.2.2 (this ▸ (hYH.trans (hN.trans hle)))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hHK
    (isPGroup_of_oTwoRes_eq_bot hY)


theorem weak_e_core {g : G} (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ S.V1) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G),
      (∀ (a : G) (ha : a ∈ conjSub g⁻¹ V), InK4 (S.frame.ρ ⟨a, hN ha⟩)) ∧
      ∀ (a b : G) (ha : a ∈ conjSub g⁻¹ V) (hb : b ∈ conjSub g⁻¹ V) (x : W5),
        pact (S.frame.ρ ⟨b, hN hb⟩) (pact (S.frame.ρ ⟨a, hN ha⟩) x * x⁻¹) =
          pact (S.frame.ρ ⟨a, hN ha⟩) x * x⁻¹ := by
  have hVg : IsElemAbelian 2 (conjSub g⁻¹ V) := F7.isElemAbelian_conjSub S.elemAbelian_V
  have hcomm : ∀ a ∈ conjSub g⁻¹ V, ∀ b ∈ conjSub g⁻¹ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVg.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hva : ∀ v ∈ V, ∀ a ∈ conjSub g⁻¹ V, v * a * v⁻¹ * a⁻¹ ∈ V ⊓ conjSub g⁻¹ V :=
    fun v hv a ha => h1 (Subgroup.commutator_mem_commutator hv ha)
  have hfwd : ∀ a ∈ conjSub g⁻¹ V, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    have h := (hva v hv a ha).1
    have e : a * v * a⁻¹ = (v * a * v⁻¹ * a⁻¹)⁻¹ * v := by group
    rw [e]
    exact V.mul_mem (V.inv_mem h) hv
  have hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hfwd a ha v, fun hv => ?_⟩
    have ha2 : a⁻¹ = a := by
      have := hVg.2 a ha
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_left this
    have haa : a * a = 1 := by
      have := hVg.2 a ha
      rwa [pow_two] at this
    have := hfwd a ha _ hv
    rwa [ha2, show a * (a * v * a) * a = (a * a) * v * (a * a) by group, haa, one_mul,
      mul_one] at this
  refine ⟨hN, ?_, ?_⟩
  · intro a ha
    have hza : a * S.z * a⁻¹ = S.z := by
      have hzg : S.z ∈ conjSub g⁻¹ V := by
        rw [mem_conjSub, inv_inv]
        have : g * S.z * g⁻¹ = S.z := by
          have := Subgroup.mem_centralizer_singleton_iff.mp hg
          calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [this]
            _ = S.z := by group
        rw [this]
        exact S.z_mem_V
      rw [hcomm a ha _ hzg]
      group
    refine InK4_of_comm _ (S.rho_four_of_conj_z _ hza) fun x hx => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by simpa using mem_W3.2 hx⟩
    rw [← S.psi_conj ⟨a, hN ha⟩ v, ← map_inv, ← map_mul]
    have hc : (a * v * a⁻¹ * (v : G)⁻¹) ∈ S.V1 := by
      have := h2 (Subgroup.commutator_mem_commutator hv3 ha)
      have e : a * v * a⁻¹ * (v : G)⁻¹ = (v * a * (v : G)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]
      exact S.V1.inv_mem this
    rcases S.mem_V1.1 hc with h | h
    · left
      have : (⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN ha) v).mp v.2⟩ * v⁻¹ : ↥V) = 1 :=
        Subtype.ext (by simpa using h)
      rw [this, map_one]
    · right
      have : (⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN ha) v).mp v.2⟩ * v⁻¹ : ↥V) =
          ⟨S.z, S.z_mem_V⟩ := Subtype.ext (by simpa using h)
      rw [this, S.psi_z]
  · intro a b ha hb x
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    rw [← S.psi_conj ⟨a, hN ha⟩ v, ← map_inv, ← map_mul, ← S.psi_conj ⟨b, hN hb⟩]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hmem : a * v * a⁻¹ * (v : G)⁻¹ ∈ conjSub g⁻¹ V := by
      have := (hva v v.2 a ha).2
      have e : a * v * a⁻¹ * (v : G)⁻¹ = (v * a * (v : G)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]
      exact (conjSub g⁻¹ V).inv_mem this
    rw [hcomm b hb _ hmem]
    group


theorem weak_e_two {g : G} (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ S.V1) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G), ∃ σ : Equiv.Perm (Fin 5),
      (InK4 σ ∧ σ ≠ 1) ∧ ∀ (a : G) (ha : a ∈ conjSub g⁻¹ V),
        S.frame.ρ ⟨a, hN ha⟩ = 1 ∨ S.frame.ρ ⟨a, hN ha⟩ = σ ∨
          ∀ (b : G) (hb : b ∈ conjSub g⁻¹ V), S.frame.ρ ⟨b, hN hb⟩ = 1 := by
  obtain ⟨hN, hK4, hquad⟩ := S.weak_e_core hg h1 h2
  refine ⟨hN, ?_⟩
  by_cases hex : ∃ (a : G) (ha : a ∈ conjSub g⁻¹ V), S.frame.ρ ⟨a, hN ha⟩ ≠ 1
  · obtain ⟨a₀, ha₀, hne⟩ := hex
    refine ⟨S.frame.ρ ⟨a₀, hN ha₀⟩, ⟨hK4 a₀ ha₀, hne⟩, fun b hb => ?_⟩
    by_cases hb1 : S.frame.ρ ⟨b, hN hb⟩ = 1
    · exact Or.inl hb1
    by_cases hbσ : S.frame.ρ ⟨b, hN hb⟩ = S.frame.ρ ⟨a₀, hN ha₀⟩
    · exact Or.inr (Or.inl hbσ)
    exfalso
    obtain ⟨x, hx⟩ := K4_not_quadratic _ _ (hK4 a₀ ha₀) (hK4 b hb) hne hb1 (Ne.symm hbσ)
    exact hx (hquad a₀ b ha₀ hb x)
  · simp only [not_exists, not_not] at hex
    exact ⟨pa, ⟨Or.inr (Or.inl rfl), by decide⟩, fun a ha => Or.inr (Or.inr hex)⟩

theorem weak_e_card {g : G} (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ S.V1) :
    Nat.card (conjSub g⁻¹ V) ≤
      2 * Nat.card ↥(conjSub g⁻¹ V ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨hN, σ, -, hσ⟩ := S.weak_e_two hg h1 h2
  set A := conjSub g⁻¹ V
  let φ : ↥A →* Equiv.Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion hN)
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := (S.conj_eq_iff ⟨a, hN a.2⟩ ⟨v, hv⟩).2 (by
        show pact (φ a) _ = _
        rw [h, map_one, MulAut.one_apply])
      calc v * a = a * v * (a : G)⁻¹ * a := by rw [this]
        _ = a * v := by group
    · intro h
      apply pact_injective
      refine MulEquiv.ext fun x => ?_
      obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
      have := (S.conj_eq_iff ⟨a, hN a.2⟩ v).1 (by
        have := Subgroup.mem_centralizer_iff.mp h v v.2
        calc (a : G) * v * (a : G)⁻¹ = v * a * (a : G)⁻¹ := by rw [this]
          _ = v := by group)
      rw [map_one, MulAut.one_apply]
      exact this
  have hrange : Nat.card φ.range ≤ 2 := by
    have hsub : (φ.range : Set (Equiv.Perm (Fin 5))) ⊆ {1, σ} := by
      rintro _ ⟨a, rfl⟩
      rcases hσ a a.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl (h a a.2)
    calc Nat.card φ.range = Nat.card ((φ.range : Set (Equiv.Perm (Fin 5)))) := rfl
      _ ≤ Nat.card (({1, σ} : Set (Equiv.Perm (Fin 5)))) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by simp)
  have hkcard : Nat.card φ.ker = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_congr ⟨fun a => ⟨a.1, a.1.2, (hker a.1).1 a.2⟩,
      fun b => ⟨⟨b.1, b.2.1⟩, (hker ⟨b.1, b.2.1⟩).2 b.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have h := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hkcard] at h
  calc Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card φ.range := h.symm
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring

theorem card_inf_centralizer_le_four {a : G} (haN : a ∈ Subgroup.normalizer (V : Set G))
    (hK4 : InK4 (S.frame.ρ ⟨a, haN⟩)) (hne : S.frame.ρ ⟨a, haN⟩ ≠ 1) {A : Subgroup G}
    (haA : a ∈ A) : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
  rw [← card_fix_K4 _ hK4 hne, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective
    (fun v => ⟨S.frame.ψ ⟨v.1, (Subgroup.mem_inf.1 v.2).1⟩, ?_⟩) ?_
  · refine (S.conj_eq_iff ⟨a, haN⟩ ⟨v.1, (Subgroup.mem_inf.1 v.2).1⟩).1 ?_
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 v.2).2 a haA
    calc a * v.1 * a⁻¹ = v.1 * a * a⁻¹ := by rw [this]
      _ = v.1 := by group
  · intro v w h
    have := S.frame.ψ.injective (congrArg Subtype.val h)
    exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem weak_e {g : G} (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ S.V1) (h3 : ⁅conjSub g⁻¹ S.V3, V⁆ ≤ S.V1) :
    ⁅S.V3, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ S.V3, V⁆ = ⊥ := by
  have hgN1 : g ∈ Subgroup.normalizer (S.V1 : Set G) := S.G1_eq_normalizer ▸ hg
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have h1' : ⁅V, conjSub g⁻¹⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := conjSub_mono g h1
    rw [← conjSub_commutator, conjSub_inv_conjSub, conjSub_inf, conjSub_inv_conjSub,
      Subgroup.commutator_comm] at this
    rwa [inf_comm]
  have h2' : ⁅S.V3, conjSub g⁻¹⁻¹ V⁆ ≤ S.V1 := by
    rw [inv_inv]
    have := conjSub_mono g h3
    rwa [← conjSub_commutator, conjSub_inv_conjSub, conjSub_self_of_mem hgN1] at this
  have hcardV : Nat.card (conjSub g V) = 16 := by
    rw [card_conjSub', S.card_V]
  have hF1 := S.weak_e_card hginv h1' h2'
  rw [inv_inv, hcardV] at hF1
  have htrans : Nat.card ↥(conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G)) := by
    have e : conjSub g⁻¹ (conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
        V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G) := by
      rw [conjSub_inf, conjSub_conjSub_inv, conjSub_centralizer]
    rw [← e, card_conjSub']
  rw [htrans] at hF1
  obtain ⟨hN, σ, ⟨hσK4, hσ1⟩, hσ⟩ := S.weak_e_two hg h1 h2
  have hall : ∀ (a : G) (ha : a ∈ conjSub g⁻¹ V), S.frame.ρ ⟨a, hN ha⟩ = 1 := by
    intro a ha
    by_contra hne
    rcases hσ a ha with h | h | h
    · exact hne h
    · have h4 := S.card_inf_centralizer_le_four (hN ha) (h ▸ hσK4) hne ha
      omega
    · exact hne (h a ha)
  have hcent : conjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (S.conj_eq_iff ⟨a, hN ha⟩ ⟨v, hv⟩).2 (by rw [hall a ha, map_one, MulAut.one_apply])
    calc v * a = a * v * a⁻¹ * a := by rw [this]
      _ = a * v := by group
  have hVV : ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcent
  constructor
  · exact le_bot_iff.mp (hVV ▸ Subgroup.commutator_mono S.V3_le_V le_rfl)
  · refine le_bot_iff.mp ?_
    rw [Subgroup.commutator_comm, ← hVV]
    exact Subgroup.commutator_mono le_rfl (conjSub_mono _ S.V3_le_V)


theorem hypF91 (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF91 T V L S.V1 S.V3 H where
  sylow := S.sylow_top
  elemAbelian := S.elemAbelian_V
  normalizes_L := S.T_le_NL
  oTwoRes_eq := S.oTwoRes_L
  charTwo_L := S.charTwo_L
  reduced := S.reduced
  cT := S.cT
  card_V₁ := S.card_V1
  V₁_lt_Vp := S.V1_lt_V3
  Vp_le_V := S.V3_le_V
  T_normalizes_V₁ := S.T_le_NV1
  H_le_centralizer := S.centralizer_V1 ▸ hH.2.1
  L₁T_le_H := hH.1.1
  charTwo_H := S.charTwo_of_inH ⟨le_sup_right.trans hH.1.1, hH.1.2⟩
  ker_le := S.coreIn_le_pCoreOf h1323 hH
  L₁T_normalizes_Vp := S.L1T_le_NV3
  irred := S.irred_V3
  normalizer_le := fun _ hx => h1323 G T L V S hx.2
  o2_trivial := S.o2_eq_bot_of_not_le le_sup_left fun h => hH.2.2 (le_sup_right.trans h)
  weak_e := fun _ hg h1 h2 h3 => S.weak_e (hH.2.1 hg) h1 h2 h3

end Setting

end CFSG.Quasithin.H13.A5
