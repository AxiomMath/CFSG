module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Wreath
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547One

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

theorem card_mul_le_card_sup [Finite G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  let f : A × B → ↥(A ⊔ B) := fun p =>
    ⟨p.1 * p.2, (A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h']
        _ = b' * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot] at h2
    have ha : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    have hb : (b : G) = b' := by
      rw [ha] at h'
      exact mul_left_cancel h'
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem cjSub_le_centralizer {X U : Subgroup G} (h : X ≤ Subgroup.centralizer (U : Set G))
    (g : G) : cjSub g X ≤ Subgroup.centralizer (cjSub g U : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ cjSub g U := hu
  rw [mem_cjSub] at hx hu'
  have := Subgroup.mem_centralizer_iff.mp (h hx) _ hu'
  calc u * x = g * ((g⁻¹ * u * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * x * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
    _ = x * u := by group

theorem mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.centralizer (A : Set G))
    (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hB b hb))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

variable [Finite G]

theorem two_core (S : Sylow 2 G) {M : Subgroup G} (hSM : (S : Subgroup G) ≤ M) (hF : CharTwo M)
    {V₁ V₂ : Subgroup G} (hV₁V : V₁ ≤ VZ (S : Subgroup G) M) (hV₂V : V₂ ≤ VZ (S : Subgroup G) M)
    (hV₁4 : Nat.card V₁ = 4) (hV₂4 : Nat.card V₂ = 4) (hV12 : V₁ ⊓ V₂ = ⊥)
    (hV12' : V₁ ⊔ V₂ = VZ (S : Subgroup G) M)
    (hperm : ∀ m ∈ M, (cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂) ∨ (cjSub m V₁ = V₂ ∧ cjSub m V₂ = V₁))
    (hodd : ∀ m ∈ M, ∀ k : ℕ, Odd k →
      m ^ k ∈ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) →
      cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂)
    {t₀ : G} (ht₀M : t₀ ∈ M) (ht₁ : cjSub t₀ V₁ = V₂) (ht₂ : cjSub t₀ V₂ = V₁)
    {X : Subgroup G} (hX : IsA4 X (pCoreOf 2 X)) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) (hQ : pCoreOf 2 X = V₁) :
    X ≤ Subgroup.centralizer (V₂ : Set G) ∧
    cjSub t₀ X ≤ Subgroup.centralizer (V₁ : Set G) ∧
    X ⊓ cjSub t₀ X = ⊥ ∧
    M ≤ Subgroup.normalizer ((X ⊔ cjSub t₀ X : Subgroup G) : Set G) ∧
    Nat.card ↥(X ⊔ cjSub t₀ X) = 144 ∧
    (∀ m ∈ M, cjSub m V₁ = V₁ → cjSub m X = X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := VZ (S : Subgroup G) M with hVdef
  have hred : IsTwoReducedIn M V := isTwoReducedIn_conjClosure M S hSM hF le_rfl
  have hVM : V ≤ M := hred.1
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVab : IsElemAbelian 2 V := hred.2.2.1
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_of_isElemAbelian hVab
  have hV₁C : V ≤ Subgroup.centralizer (V₁ : Set G) := hVC.trans (Subgroup.centralizer_le hV₁V)
  have hV₂C : V ≤ Subgroup.centralizer (V₂ : Set G) := hVC.trans (Subgroup.centralizer_le hV₂V)
  have hV2 : ∀ v ∈ V₂, v ^ 2 = 1 := fun v hv => hVab.2 v (hV₂V hv)
  have hoddmem : ∀ y ∈ X, Odd (orderOf y) → y ∈ Subgroup.normalizer (V₁ : Set G) ⊓
      Subgroup.normalizer (V₂ : Set G) := by
    intro y hy hyo
    have h := hodd y (hXM hy) (orderOf y) hyo (by
      rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _)
    exact ⟨mem_normalizer_of_cjSub_eq h.1, mem_normalizer_of_cjSub_eq h.2⟩
  have hXN : X ≤ Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) := by
    refine hX.le_of_forall_syl3_le fun P hP y hy => hoddmem y (hP.1 hy) ?_
    have h3 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard P hy
      rwa [hP.2] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h <;> rw [h] <;> decide
  have hVS : V ≤ (S : Subgroup G) :=
    (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_two_le_sylow M S hSM)
  have hV2grp : IsPGroup 2 V := S.isPGroup'.to_le hVS
  have hVX : V ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_isSubnormal hX hXM hXs hVM hMV hV2grp
  have hXV : X ⊓ V ≤ V₁ := by
    rw [← hQ]
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hMV (hXM hx)⟩)
      (hV2grp.to_le inf_le_right)
  have hXV₂b : X ⊓ V₂ = ⊥ := by
    refine le_bot_iff.mp (le_trans (le_inf ((inf_le_inf_left X hV₂V).trans hXV) inf_le_right) ?_)
    rw [hV12]
  have hXV₂ : X ≤ Subgroup.centralizer (V₂ : Set G) := by
    have hle : ⁅V₂, X⁆ ≤ X ⊓ V₂ := by
      refine le_inf ?_ (commutator_le_left (hXN.trans inf_le_right))
      rw [Subgroup.commutator_le]
      intro v hv x hx
      rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVX (hV₂V hv)) x).mp hx) (X.inv_mem hx)
    rw [hXV₂b, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hle
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) x hx).symm
  set X' : Subgroup G := cjSub t₀ X with hX'def
  have hX' : IsA4 X' V₂ := by
    have := hX.cjSub' t₀
    rwa [hQ, ht₁] at this
  have hX'V₁ : X' ≤ Subgroup.centralizer (V₁ : Set G) := by
    have := cjSub_le_centralizer hXV₂ t₀
    rwa [ht₂] at this
  have hXX' : X ⊓ X' = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot]
    have hy3 : y ^ 3 = 1 := by
      have h1 : y ^ 3 ∈ V₁ := hQ ▸ hX.cube y hy.1
      have h2 : y ^ 3 ∈ V₂ := hX'.cube y hy.2
      have : y ^ 3 ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
      rwa [hV12, Subgroup.mem_bot] at this
    by_contra hy1
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨w, hwV₁, hw1, -⟩ := exists_ne_of_card_eq_four hV₁4 1
    exact hw1 (hX.fpf y hy.1 hord w (hQ ▸ hwV₁)
      (Subgroup.mem_centralizer_iff.mp (hX'V₁ hy.2) w hwV₁).symm)
  have h144 : 144 ≤ Nat.card ↥(X ⊔ X') := by
    have := card_mul_le_card_sup hXX'
    rwa [hX.card, hX'.card] at this
  obtain ⟨R, hVR, hRM, hMR, hR3, hRC, hRsub⟩ := exists_rhat hVM hMV hVC hF
  have hXR : X ≤ R := hRsub X hXM hXs fun x hx => ⟨1, by
    rw [pow_one]
    exact hV₁V (hQ ▸ hX.cube x hx)⟩
  have hX'R : X' ≤ R := cjSub_le (hMR ht₀M) hXR
  have hRN : ∀ r ∈ R, cjSub r V₁ = V₁ ∧ cjSub r V₂ = V₂ := fun r hr => by
    obtain ⟨k, hk⟩ := hR3 r hr
    exact hodd r (hRM hr) (3 ^ k) (Odd.pow (by decide)) (hVC hk)
  have hV16 : Nat.card V = 16 := by
    have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hVC (hV₂V hb)) a (hV₁V ha)
    have := B2F.card_sup_mul_card_inf_of_commute hc
    rw [hV12', hV12, Subgroup.card_bot, mul_one, hV₁4, hV₂4] at this
    exact this
  have hK₂ : Nat.card ↥(R ⊓ Subgroup.centralizer (V₂ : Set G)) ≤ 48 := by
    have h3 := relIndex_le_three_of_card_eq_four hV₁4
      (H := R ⊓ Subgroup.centralizer (V₂ : Set G))
      (fun r hr => mem_normalizer_of_cjSub_eq (hRN r hr.1).1)
      (fun r hr => by
        obtain ⟨k, hk⟩ := hR3 r hr.1
        exact ⟨k, hV₁C hk⟩)
    have hle : (R ⊓ Subgroup.centralizer (V₂ : Set G)) ⊓ Subgroup.centralizer (V₁ : Set G) ≤ V := by
      intro x hx
      refine hRC ⟨hx.1.1, ?_⟩
      rw [← hV12']
      exact mem_centralizer_sup hx.2 hx.1.2
    have h16 : Nat.card ↥((R ⊓ Subgroup.centralizer (V₂ : Set G)) ⊓
        Subgroup.centralizer (V₁ : Set G)) ≤ 16 := hV16 ▸ Subgroup.card_le_of_le hle
    have hmul := Subgroup.relIndex_mul_card ((R ⊓ Subgroup.centralizer (V₂ : Set G)) ⊓
      Subgroup.centralizer (V₁ : Set G)) (R ⊓ Subgroup.centralizer (V₂ : Set G))
    rw [inf_eq_left.mpr (inf_le_left : (R ⊓ Subgroup.centralizer (V₂ : Set G)) ⊓
      Subgroup.centralizer (V₁ : Set G) ≤ R ⊓ Subgroup.centralizer (V₂ : Set G))] at hmul
    rw [← hmul]
    calc _ ≤ 3 * 16 := Nat.mul_le_mul h3 h16
      _ = 48 := by norm_num
  have hR144 : Nat.card R ≤ 144 := by
    have h3 := relIndex_le_three_of_card_eq_four hV₂4 (H := R)
      (fun r hr => mem_normalizer_of_cjSub_eq (hRN r hr).2)
      (fun r hr => by
        obtain ⟨k, hk⟩ := hR3 r hr
        exact ⟨k, hV₂C hk⟩)
    have hmul := Subgroup.relIndex_mul_card (R ⊓ Subgroup.centralizer (V₂ : Set G)) R
    rw [inf_eq_left.mpr (inf_le_left : R ⊓ Subgroup.centralizer (V₂ : Set G) ≤ R)] at hmul
    rw [← hmul]
    calc _ ≤ 3 * 48 := Nat.mul_le_mul h3 hK₂
      _ = 144 := by norm_num
  have hReq : X ⊔ X' = R := Subgroup.eq_of_le_of_card_ge (sup_le hXR hX'R) (hR144.trans h144)
  have huniq : ∀ m ∈ M, cjSub m V₁ = V₁ → cjSub m X = X := by
    intro m hm hmV
    have hmV₂ : cjSub m V₂ = V₂ := by
      rcases hperm m hm with h | h
      · exact h.2
      · exfalso
        have h12 : V₁ = V₂ := hmV.symm.trans h.1
        have h1 : V₁ = ⊥ := by rw [← hV12, ← h12, inf_idem]
        rw [h1, Subgroup.card_bot] at hV₁4
        norm_num at hV₁4
    have hY : IsA4 (cjSub m X) (cjSub m (pCoreOf 2 X)) := hX.cjSub' m
    have hYR : cjSub m X ≤ R := cjSub_le (hMR hm) hXR
    have hYV₂ : cjSub m X ≤ Subgroup.centralizer (V₂ : Set G) := by
      have := cjSub_le_centralizer hXV₂ m
      rwa [hmV₂] at this
    have hXV₂K : X ⊔ V₂ ≤ R ⊓ Subgroup.centralizer (V₂ : Set G) :=
      sup_le (le_inf hXR hXV₂) (le_inf (hV₂V.trans hVR) (hV₂V.trans hV₂C))
    have h48 : 48 ≤ Nat.card ↥(X ⊔ V₂) := by
      have := card_mul_le_card_sup hXV₂b
      rwa [hX.card, hV₂4] at this
    have hK₂eq : X ⊔ V₂ = R ⊓ Subgroup.centralizer (V₂ : Set G) :=
      Subgroup.eq_of_le_of_card_ge hXV₂K (hK₂.trans h48)
    have hYX : cjSub m X ≤ X := by
      refine hY.le_of_forall_syl3_le fun P hP y hy => ?_
      have hyY := hP.1 hy
      have hyK : y ∈ X ⊔ V₂ := hK₂eq ▸ ⟨hYR hyY, hYV₂ hyY⟩
      have hV₂N : V₂ ≤ Subgroup.normalizer (X : Set G) := hV₂V.trans hVX
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X V₂ hV₂N] at hyK
      obtain ⟨x, hx, v, hv, hxv⟩ := hyK
      have hxv' : x * v = y := hxv
      have hy3 : y ^ 3 = 1 := by
        have := Subgroup.orderOf_dvd_natCard P hy
        rw [hP.2] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have hxvc : x * v = v * x := (Subgroup.mem_centralizer_iff.mp (hXV₂ hx) v hv).symm
      have hpow : (x * v) ^ 3 = x ^ 3 * v ^ 3 := Commute.mul_pow hxvc 3
      have hv3 : v ^ 3 = v := by
        rw [pow_succ, hV2 v hv, one_mul]
      rw [← hxv', hpow, hv3] at hy3
      have hvX : v ∈ X := by
        rw [eq_inv_of_mul_eq_one_right hy3]
        exact X.inv_mem (X.pow_mem hx 3)
      have hv1 : v = 1 := by
        have : v ∈ X ⊓ V₂ := ⟨hvX, hv⟩
        rwa [hXV₂b, Subgroup.mem_bot] at this
      rw [← hxv', hv1, mul_one]
      exact hx
    exact Subgroup.eq_of_le_of_card_ge hYX (by rw [card_cjSub])
  refine ⟨hXV₂, hX'V₁, hXX', hReq ▸ hMR, le_antisymm (by rw [hReq]; exact hR144) h144, huniq⟩

theorem le_normalizer_map_ker {M : Subgroup G} {H : Type*} [Group H] (f : M →* H) :
    M ≤ Subgroup.normalizer ((f.ker.map M.subtype : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, f.normal_ker.conj_mem k hk _, rfl⟩

theorem mem_normalizer_of_conjPerm_eq_one {M : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : ∀ m ∈ M, ∀ P ∈ Ω, cjSub m P ∈ Ω) {m : M} (hm : conjPerm M Ω hΩ m = 1)
    {P : Subgroup G} (hP : P ∈ Ω) : (m : G) ∈ Subgroup.normalizer (P : Set G) := by
  refine mem_normalizer_of_cjSub_eq ?_
  have := congrArg (fun π : Equiv.Perm Ω => ((π ⟨P, hP⟩ : Ω) : Subgroup G)) hm
  simpa [conjPerm_apply] using this

theorem div_four_eq_iff (k l : Fin 8) :
    k.val / 4 = l.val / 4 ↔ (k.val / 4 = 0 ↔ l.val / 4 = 0) := by
  have h1 : k.val / 4 < 2 := by omega
  have h2 : l.val / 4 < 2 := by omega
  constructor
  · intro h
    rw [h]
  · intro h
    by_cases hk : k.val / 4 = 0
    · rw [hk, eq_comm]
      exact h.mp hk
    · have hl : l.val / 4 ≠ 0 := fun hl => hk (h.mpr hl)
      omega

theorem union_equiv_block {α : Type*} {Ω₁ Ω₂ : Set α} [DecidablePred (· ∈ Ω₁)]
    (hdisj : Disjoint Ω₁ Ω₂) (e₁ : Ω₁ ≃ Fin 4) (e₂ : Ω₂ ≃ Fin 4) (P : ↥(Ω₁ ∪ Ω₂)) :
    ((((Equiv.Set.union hdisj).trans ((Equiv.sumCongr e₁ e₂).trans finSumFinEquiv)) P :
      Fin (4 + 4)).val / 4 = 0 ↔ (P : α) ∈ Ω₁) := by
  by_cases hP : (P : α) ∈ Ω₁
  · rw [Equiv.trans_apply, Equiv.Set.union_apply_left hdisj hP, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
    simp only [hP, iff_true]
    have := (e₁ ⟨_, hP⟩).2
    omega
  · have hP₂ : (P : α) ∈ Ω₂ := P.2.resolve_left hP
    rw [Equiv.trans_apply, Equiv.Set.union_apply_right hdisj hP₂, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
    simp only [hP, iff_false]
    have := (e₂ ⟨_, hP₂⟩).2
    omega

theorem permCongr_mem_wreath {Ω : Type*} (p : Ω → Prop) (e : Ω ≃ Fin 8)
    (he : ∀ P, (e P).val / 4 = 0 ↔ p P) (π : Equiv.Perm Ω) (c : Prop)
    (hπ : ∀ P, p (π P) ↔ (p P ↔ c)) : e.permCongr π ∈ wreathSFourTwo := by
  intro i j
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, div_four_eq_iff, div_four_eq_iff, he, he]
  have hi := he (e.symm i)
  have hj := he (e.symm j)
  rw [Equiv.apply_symm_apply] at hi hj
  rw [hi, hj, hπ, hπ]
  tauto

theorem card_sup_mul_card_inf {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := relIndex_sup_eq_relIndex hHK
  have e1 := Subgroup.relIndex_mul_card H (H ⊔ K)
  have e2 := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr (le_sup_left : H ≤ H ⊔ K), h1] at e1
  rw [← e1, ← e2]
  ring

theorem false_of_wreath_aux (h1391 : Input1391) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    (S : Sylow 2 G) {M : Subgroup G} (hM : InM (S : Subgroup G) M) (hF : CharTwo M)
    (hZ2 : Nat.card (quasithinOmegaOneCenter (S : Subgroup G)) = 2)
    {V₁ V₂ : Subgroup G} (hV₁V : V₁ ≤ VZ (S : Subgroup G) M) (hV₂V : V₂ ≤ VZ (S : Subgroup G) M)
    (hV₁4 : Nat.card V₁ = 4) (hV₂4 : Nat.card V₂ = 4) (hV12 : V₁ ⊓ V₂ = ⊥)
    (hV12' : V₁ ⊔ V₂ = VZ (S : Subgroup G) M)
    (hswap : ∃ t ∈ (S : Subgroup G), cjSub t V₁ = V₂ ∧ cjSub t V₂ = V₁)
    (hperm : ∀ m ∈ M, (cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂) ∨ (cjSub m V₁ = V₂ ∧ cjSub m V₂ = V₁))
    (hodd : ∀ m ∈ M, ∀ k : ℕ, Odd k →
      m ^ k ∈ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) →
      cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂)
    (h8 : 8 ≤ ((S : Subgroup G) ⊓
      Subgroup.centralizer (VZ (S : Subgroup G) M : Set G)).relIndex (S : Subgroup G))
    {X : Subgroup G} (hX : IsA4 X (pCoreOf 2 X)) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) (hQ : pCoreOf 2 X = V₁) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := VZ (S : Subgroup G) M with hVdef
  have hSM : (S : Subgroup G) ≤ M := hM.2
  have hred : IsTwoReducedIn M V := isTwoReducedIn_conjClosure M S hSM hF le_rfl
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVab : IsElemAbelian 2 V := hred.2.2.1
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_of_isElemAbelian hVab
  have hVS : V ≤ (S : Subgroup G) :=
    (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_two_le_sylow M S hSM)
  obtain ⟨t₀, ht₀S, ht₁, ht₂⟩ := hswap
  have ht₀M : t₀ ∈ M := hSM ht₀S
  obtain ⟨hXV₂, hX'V₁, hXX', hMR, hcardR, huniq⟩ := two_core S hSM hF hV₁V hV₂V hV₁4 hV₂4 hV12
    hV12' hperm hodd ht₀M ht₁ ht₂ hX hXM hXs hQ
  set X' : Subgroup G := cjSub t₀ X with hX'def
  have hX' : IsA4 X' V₂ := by
    have := hX.cjSub' t₀
    rwa [hQ, ht₁] at this
  set R : Subgroup G := X ⊔ X' with hRdef
  have hinv₁ : cjSub t₀⁻¹ V₂ = V₁ := by rw [← ht₁, cjSub_inv_cjSub]
  have hinv₂ : cjSub t₀⁻¹ V₁ = V₂ := by rw [← ht₂, cjSub_inv_cjSub]
  have hswapX : ∀ m ∈ M, (cjSub m X = X ∧ cjSub m X' = X') ∨ (cjSub m X = X' ∧ cjSub m X' = X) := by
    intro m hm
    rcases hperm m hm with h | h
    · left
      refine ⟨huniq m hm h.1, ?_⟩
      have h1 : cjSub (t₀⁻¹ * m * t₀) V₁ = V₁ := by
        rw [cjSub_mul, cjSub_mul, ht₁, h.2, hinv₁]
      have h2 := huniq _ (M.mul_mem (M.mul_mem (M.inv_mem ht₀M) hm) ht₀M) h1
      rw [hX'def, ← cjSub_mul]
      rw [show m * t₀ = t₀ * (t₀⁻¹ * m * t₀) by group, cjSub_mul, h2]
    · right
      constructor
      · have h1 : cjSub (t₀⁻¹ * m) V₁ = V₁ := by rw [cjSub_mul, h.1, hinv₁]
        have h2 := huniq _ (M.mul_mem (M.inv_mem ht₀M) hm) h1
        rw [show m = t₀ * (t₀⁻¹ * m) by group, cjSub_mul, h2]
      · have h1 : cjSub (m * t₀) V₁ = V₁ := by rw [cjSub_mul, ht₁, h.2]
        have h2 := huniq _ (M.mul_mem hm ht₀M) h1
        rw [hX'def, ← cjSub_mul, h2]
  obtain ⟨z, hzZ, hz1, -, hZ⟩ := exists_eq_of_card_eq_two hZ2
  have hzV : z ∈ V := le_conjClosure _ M hzZ
  have hV₂N₁ : V₂ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (hV₂V.trans (hVC.trans (Subgroup.centralizer_le hV₁V))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzR : z ∉ Subgroup.centralizer (R : Set G) := by
    intro hzC
    have hzV' : z ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by rw [hV12']; exact hzV
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V₁ V₂ hV₂N₁] at hzV'
    obtain ⟨a, ha, b, hb, hab'⟩ := hzV'
    have hab : a * b = z := hab'
    have hcomm : ∀ c ∈ V₁, ∀ d ∈ V₂, c * d = d * c := fun c hc d hd =>
      Subgroup.mem_centralizer_iff.mp (hVC (hV₂V hd)) c (hV₁V hc)
    obtain ⟨p, hpX, hp⟩ := hX.exists_orderOf_eq_three
    have hpz : p * z = z * p := (Subgroup.mem_centralizer_iff.mp hzC p (Subgroup.mem_sup_left hpX))
    have hpN : p ∈ Subgroup.normalizer (V₁ : Set G) := by
      have := hX.normal hpX
      rwa [hQ] at this
    have hpa : p * a * p⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hpN a).mp ha
    have hpb : p * b * p⁻¹ = b := by
      rw [(Subgroup.mem_centralizer_iff.mp (hXV₂ hpX) b hb).symm, mul_inv_cancel_right]
    have hdec : (p * a * p⁻¹) * b = a * b := by
      calc (p * a * p⁻¹) * b = p * (a * b) * p⁻¹ := by
            rw [show p * (a * b) * p⁻¹ = (p * a * p⁻¹) * (p * b * p⁻¹) by group, hpb]
        _ = a * b := by rw [hab, hpz, mul_inv_cancel_right]
    have ha1 : a = 1 := by
      have heq : p * a * p⁻¹ = a := mul_right_cancel hdec
      refine hX.fpf p hpX hp a (hQ ▸ ha) ?_
      calc p * a = p * a * p⁻¹ * p := by group
        _ = a * p := by rw [heq]
    obtain ⟨p', hpX', hp'⟩ := hX'.exists_orderOf_eq_three
    have hpz' : p' * z = z * p' :=
      Subgroup.mem_centralizer_iff.mp hzC p' (Subgroup.mem_sup_right hpX')
    have hpa' : p' * a * p'⁻¹ = a := by
      rw [(Subgroup.mem_centralizer_iff.mp (hX'V₁ hpX') a ha).symm, mul_inv_cancel_right]
    have hpb' : p' * b * p'⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hX'.normal hpX') b).mp hb
    have hdec' : a * (p' * b * p'⁻¹) = a * b := by
      calc a * (p' * b * p'⁻¹) = p' * (a * b) * p'⁻¹ := by
            rw [show p' * (a * b) * p'⁻¹ = (p' * a * p'⁻¹) * (p' * b * p'⁻¹) by group, hpa']
        _ = a * b := by rw [hab, hpz', mul_inv_cancel_right]
    have hb1 : b = 1 := by
      have heq : p' * b * p'⁻¹ = b := mul_left_cancel hdec'
      refine hX'.fpf p' hpX' hp' b hb ?_
      calc p' * b = p' * b * p'⁻¹ * p' := by group
        _ = b * p' := by rw [heq]
    exact hz1 (by rw [← hab, ha1, hb1, one_mul])
  have hT1 := eq_one_of_mem_centralizer S (hSM.trans hMR) hZ hzR
  have hCM := inf_centralizer_eq_bot S hSM hF hMR hT1
  set Ω₁ : Set (Subgroup G) := syl3 X with hΩ₁
  set Ω₂ : Set (Subgroup G) := syl3 X' with hΩ₂
  have hdisj : Disjoint Ω₁ Ω₂ := by
    rw [Set.disjoint_left]
    intro P hP₁ hP₂
    have hle : P ≤ X ⊓ X' := le_inf hP₁.1 hP₂.1
    rw [hXX', le_bot_iff] at hle
    have := hP₁.2
    rw [hle, Subgroup.card_bot] at this
    norm_num at this
  have hΩ : ∀ m ∈ M, ∀ P ∈ Ω₁ ∪ Ω₂, cjSub m P ∈ Ω₁ ∪ Ω₂ := by
    intro m hm P hP
    rcases hswapX m hm with h | h
    · rcases hP with hP | hP
      · left
        have := IsA4.cjSub_mem_syl3 hP m
        rwa [h.1] at this
      · right
        have := IsA4.cjSub_mem_syl3 hP m
        rwa [h.2] at this
    · rcases hP with hP | hP
      · right
        have := IsA4.cjSub_mem_syl3 hP m
        rwa [h.1] at this
      · left
        have := IsA4.cjSub_mem_syl3 hP m
        rwa [h.2] at this
  have hψi : Function.Injective (conjPerm M (Ω₁ ∪ Ω₂) hΩ) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hMK := le_normalizer_map_ker (conjPerm M (Ω₁ ∪ Ω₂) hΩ)
    have hKP : ∀ k ∈ ((conjPerm M (Ω₁ ∪ Ω₂) hΩ).ker.map M.subtype : Subgroup G),
        ∀ P ∈ Ω₁ ∪ Ω₂, k ∈ Subgroup.normalizer (P : Set G) := by
      rintro _ ⟨k, hk, rfl⟩ P hP
      exact mem_normalizer_of_conjPerm_eq_one hΩ (MonoidHom.mem_ker.mp hk) hP
    have hc₁ := commute_of_forall_mem_normalizer hX hXM hMK
      (fun k hk P hP => hKP k hk P (Or.inl hP))
    have hc₂ := commute_of_forall_mem_normalizer hX' (cjSub_le (Subgroup.le_normalizer ht₀M) hXM)
      hMK (fun k hk P hP => hKP k hk P (Or.inr hP))
    have hmK : (m : G) ∈ ((conjPerm M (Ω₁ ∪ Ω₂) hΩ).ker.map M.subtype : Subgroup G) :=
      ⟨m, hm, rfl⟩
    have hmC : (m : G) ∈ M ⊓ Subgroup.centralizer (R : Set G) := by
      refine ⟨m.2, mem_centralizer_sup ?_ ?_⟩
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc₁ m hmK x hx).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc₂ m hmK x hx).symm
    rw [hCM, Subgroup.mem_bot] at hmC
    exact Subtype.ext hmC
  have hc₁ : Nat.card Ω₁ = 4 := hX.card_syl3
  have hc₂ : Nat.card Ω₂ = 4 := hX'.card_syl3
  set e : ↥(Ω₁ ∪ Ω₂) ≃ Fin 8 := (Equiv.Set.union hdisj).trans
    ((Equiv.sumCongr (Finite.equivFinOfCardEq hc₁) (Finite.equivFinOfCardEq hc₂)).trans
      finSumFinEquiv) with he_def
  have he : ∀ P : ↥(Ω₁ ∪ Ω₂), ((e P).val / 4 = 0 ↔ (P : Subgroup G) ∈ Ω₁) :=
    union_equiv_block hdisj _ _
  set ψ := conjPerm M (Ω₁ ∪ Ω₂) hΩ with hψ_def
  have hXne : X' ≠ X := by
    intro hXX
    have h1 := hXX'
    rw [hXX, inf_idem] at h1
    have := hX.card
    rw [h1, Subgroup.card_bot] at this
    norm_num at this
  have hπ : ∀ m : M, ∀ P : ↥(Ω₁ ∪ Ω₂),
      (((ψ m P : ↥(Ω₁ ∪ Ω₂)) : Subgroup G) ∈ Ω₁ ↔
        ((P : Subgroup G) ∈ Ω₁ ↔ cjSub (m : G) X = X)) := by
    intro m P
    have hPm : ((ψ m P : ↥(Ω₁ ∪ Ω₂)) : Subgroup G) = cjSub (m : G) P := rfl
    rw [hPm]
    rcases hswapX m m.2 with h | h
    · simp only [h.1, iff_true]
      constructor
      · intro hmP
        by_contra hP
        have hP₂ : (P : Subgroup G) ∈ Ω₂ := P.2.resolve_left hP
        have := IsA4.cjSub_mem_syl3 hP₂ (m : G)
        rw [h.2] at this
        exact Set.disjoint_left.mp hdisj hmP this
      · intro hP
        have := IsA4.cjSub_mem_syl3 hP (m : G)
        rwa [h.1] at this
    · have hne : cjSub (m : G) X ≠ X := by rw [h.1]; exact hXne
      simp only [hne, iff_false]
      constructor
      · intro hmP hP
        have := IsA4.cjSub_mem_syl3 hP (m : G)
        rw [h.1] at this
        exact Set.disjoint_left.mp hdisj hmP this
      · intro hP
        have hP₂ : (P : Subgroup G) ∈ Ω₂ := P.2.resolve_left hP
        have := IsA4.cjSub_mem_syl3 hP₂ (m : G)
        rwa [h.2] at this
  set θ : M →* Equiv.Perm (Fin 8) := (Equiv.permCongrHom e).toMonoidHom.comp ψ with hθ_def
  have hθmem : ∀ m : M, θ m ∈ wreathSFourTwo := fun m =>
    permCongr_mem_wreath (fun P : ↥(Ω₁ ∪ Ω₂) => (P : Subgroup G) ∈ Ω₁) e he (ψ m) _ (hπ m)
  have hθi : Function.Injective θ :=
    (Equiv.permCongrHom e).injective.comp hψi
  have hT128 : 128 ≤ Nat.card (S : Subgroup G) := by
    have hmul := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓
      Subgroup.centralizer (V : Set G)) (S : Subgroup G)
    rw [inf_eq_left.mpr (inf_le_left : (S : Subgroup G) ⊓
      Subgroup.centralizer (V : Set G) ≤ S)] at hmul
    have hV16 : Nat.card V = 16 := by
      have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
        Subgroup.mem_centralizer_iff.mp (hVC (hV₂V hb)) a (hV₁V ha)
      have := B2F.card_sup_mul_card_inf_of_commute hc
      rw [hV12', hV12, Subgroup.card_bot, mul_one, hV₁4, hV₂4] at this
      exact this
    have h16 : 16 ≤ Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) :=
      hV16 ▸ Subgroup.card_le_of_le (le_inf hVS hVC)
    rw [← hmul]
    calc 128 = 8 * 16 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h8 h16
  have hRT16 : Nat.card ↥(R ⊓ (S : Subgroup G)) ≤ 16 := by
    have hdvd : Nat.card ↥(R ⊓ (S : Subgroup G)) ∣ 144 :=
      hcardR ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨n, hn⟩ := (S.isPGroup'.to_le (inf_le_right : R ⊓ (S : Subgroup G) ≤ S)).exists_card_eq
    rw [hn] at hdvd ⊢
    have h16 : 2 ^ n ∣ 2 ^ 4 := by
      have hcop : Nat.Coprime (2 ^ n) 9 := Nat.Coprime.pow_left n (by norm_num)
      exact hcop.dvd_of_dvd_mul_right (by rw [show 2 ^ 4 * 9 = 144 by norm_num]; exact hdvd)
    exact Nat.le_of_dvd (by norm_num) h16
  have hM1152 : 1152 ≤ Nat.card M := by
    have hSR : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := hSM.trans hMR
    have hprod := card_sup_mul_card_inf hSR
    rw [inf_comm, hcardR] at hprod
    have hle : Nat.card ↥((S : Subgroup G) ⊔ R) ≤ Nat.card M :=
      Subgroup.card_le_of_le (sup_le hSM (sup_le hXM (cjSub_le (Subgroup.le_normalizer ht₀M) hXM)))
    have hpos : 0 < Nat.card ↥(R ⊓ (S : Subgroup G)) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card (S : Subgroup G) * 144 < 128 * 144 := by
      calc Nat.card (S : Subgroup G) * 144 = Nat.card ↥((S : Subgroup G) ⊔ R) *
            Nat.card ↥(R ⊓ (S : Subgroup G)) := hprod.symm
        _ ≤ Nat.card M * 16 := Nat.mul_le_mul hle hRT16
        _ < 1152 * 16 := Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
        _ = 128 * 144 := by norm_num
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  set θ' : M →* wreathSFourTwo := θ.codRestrict wreathSFourTwo hθmem with hθ'_def
  have hθ'i : Function.Injective θ' := by
    intro a b hab
    exact hθi (congrArg Subtype.val hab)
  have hθ'b : Function.Bijective θ' := by
    refine (Nat.bijective_iff_injective_and_card θ').mpr ⟨hθ'i, ?_⟩
    exact le_antisymm (Nat.card_le_card_of_injective θ' hθ'i)
      (card_wreathSFourTwo_le.trans hM1152)
  exact (h1391 G (S : Subgroup G) ‹_› hnonab hqtke ⟨S.isPGroup', S.not_dvd_index⟩ M hM).false
    (MulEquiv.ofBijective θ' hθ'b)

theorem false_of_wreath (h1391 : Input1391) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    (S : Sylow 2 G) {M : Subgroup G} (hM : InM (S : Subgroup G) M) (hF : CharTwo M)
    (hZ2 : Nat.card (quasithinOmegaOneCenter (S : Subgroup G)) = 2)
    {V₁ V₂ : Subgroup G} (hV₁V : V₁ ≤ VZ (S : Subgroup G) M) (hV₂V : V₂ ≤ VZ (S : Subgroup G) M)
    (hV₁4 : Nat.card V₁ = 4) (hV₂4 : Nat.card V₂ = 4) (hV12 : V₁ ⊓ V₂ = ⊥)
    (hV12' : V₁ ⊔ V₂ = VZ (S : Subgroup G) M)
    (hswap : ∃ t ∈ (S : Subgroup G), cjSub t V₁ = V₂ ∧ cjSub t V₂ = V₁)
    (hperm : ∀ m ∈ M, (cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂) ∨ (cjSub m V₁ = V₂ ∧ cjSub m V₂ = V₁))
    (hodd : ∀ m ∈ M, ∀ k : ℕ, Odd k →
      m ^ k ∈ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) →
      cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂)
    (h8 : 8 ≤ ((S : Subgroup G) ⊓
      Subgroup.centralizer (VZ (S : Subgroup G) M : Set G)).relIndex (S : Subgroup G))
    {X : Subgroup G} (hX : IsA4 X (pCoreOf 2 X)) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal)
    (hXV : ¬ X ≤ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := VZ (S : Subgroup G) M with hVdef
  set Q : Subgroup G := pCoreOf 2 X with hQdef
  have hSM : (S : Subgroup G) ≤ M := hM.2
  have hred : IsTwoReducedIn M V := isTwoReducedIn_conjClosure M S hSM hF le_rfl
  have hVM : V ≤ M := hred.1
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVS : V ≤ (S : Subgroup G) :=
    (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_two_le_sylow M S hSM)
  have hcomm := commutator_eq_of_isSubnormal hX rfl hXM hXs hVM hMV (S.isPGroup'.to_le hVS) hXV
  have hXN : X ≤ Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) := by
    refine hX.le_of_forall_syl3_le fun P hP y hy => ?_
    have h3 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard P hy
      rwa [hP.2] at this
    have hyo : Odd (orderOf y) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h <;> rw [h] <;> decide
    have h := hodd y (hXM (hP.1 hy)) (orderOf y) hyo (by
      rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _)
    exact ⟨mem_normalizer_of_cjSub_eq h.1, mem_normalizer_of_cjSub_eq h.2⟩
  have hXi : ∀ {U : Subgroup G}, X ≤ Subgroup.normalizer (U : Set G) →
      X ≤ Subgroup.normalizer ((Q ⊓ U : Subgroup G) : Set G) := fun hU x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hX.normal hx, hU hx⟩
  have hcent : ∀ {U : Subgroup G}, U ≤ V → X ≤ Subgroup.normalizer (U : Set G) → Q ⊓ U = ⊥ →
      X ≤ Subgroup.centralizer (U : Set G) := by
    intro U hUV hXU hQU
    have hle : ⁅U, X⁆ ≤ Q ⊓ U :=
      le_inf (hcomm ▸ Subgroup.commutator_mono hUV le_rfl) (commutator_le_left hXU)
    rw [hQU, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hle
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) x hx).symm
  rcases hX.eq_bot_or_eq (inf_le_left : Q ⊓ V₁ ≤ Q) (hXi (hXN.trans inf_le_left)) with h1 | h1
  · rcases hX.eq_bot_or_eq (inf_le_left : Q ⊓ V₂ ≤ Q) (hXi (hXN.trans inf_le_right)) with
      h2 | h2
    · apply hXV
      intro x hx
      rw [← hV12']
      exact mem_centralizer_sup (hcent hV₁V (hXN.trans inf_le_left) h1 hx)
        (hcent hV₂V (hXN.trans inf_le_right) h2 hx)
    · have hQ : Q = V₂ := Subgroup.eq_of_le_of_card_ge (h2 ▸ inf_le_right)
        (by rw [hV₂4, hX.card_Q])
      obtain ⟨t, ht, ht1, ht2⟩ := hswap
      exact false_of_wreath_aux h1391 hnonab hqtke S hM hF hZ2 hV₂V hV₁V hV₂4 hV₁4
        (by rw [inf_comm]; exact hV12) (by rw [sup_comm]; exact hV12') ⟨t, ht, ht2, ht1⟩
        (fun m hm => (hperm m hm).imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩))
        (fun m hm k hk hmk => (hodd m hm k hk hmk).symm) h8 hX hXM hXs hQ
  · have hQ : Q = V₁ := Subgroup.eq_of_le_of_card_ge (h1 ▸ inf_le_right)
      (by rw [hV₁4, hX.card_Q])
    exact false_of_wreath_aux h1391 hnonab hqtke S hM hF hZ2 hV₁V hV₂V hV₁4 hV₂4 hV12 hV12'
      hswap hperm hodd h8 hX hXM hXs hQ

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
