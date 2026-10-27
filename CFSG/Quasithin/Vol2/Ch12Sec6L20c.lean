module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20b
public import CFSG.Quasithin.Background.E3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19b S126L19d S126L20 S126L20a S126L20b Equiv
open scoped IsMulCommutative commutatorElement

namespace S126L20c

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_of_commutator_le {A B : Subgroup G} (h : ⁅A, B⁆ ≤ A) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  have key : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have h1 : ⁅a⁻¹, b⁆ ∈ A := h (Subgroup.commutator_mem_commutator (A.inv_mem ha) hb)
    have h2 : b * a * b⁻¹ = a * ⁅a⁻¹, b⁆ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact A.mul_mem ha h1
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key b hb a, fun ha => ?_⟩
  have h1 := key b⁻¹ (B.inv_mem hb) _ ha
  rwa [show b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a by group] at h1

omit [IsMulCommutative ↥V] in
theorem normalizer_V_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  obtain ⟨hVT, hTV, -, -⟩ := facts h1222 hH
  have hP2 : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hP1 : V ≠ ⊥ := by
    intro h
    have h1 := card_V F
    have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
    have h2 : Nat.card V = 1 := by
      rw [h]
      exact Subgroup.card_bot
    omega
  have hLT : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hyp.irrPlus.2.2.1 hTV
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨V, hP1, hP2, rfl⟩ : IsTwoLocal _)
  exact hle.trans (huniq M' hM' (hLT.trans hle)).le

omit [IsMulCommutative ↥V] in
theorem mul_self_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    v * v = 1 := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  rw [← pow_two]
  exact hVe.2 v hv

omit [IsMulCommutative ↥V] in
theorem mul_self_conj (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {g y : G}
    (hy : y ∈ conjSubgroup V g) : y * y = 1 := by
  have h1 := mul_self_V h1222 hH (mem_conjSubgroup_iff.1 hy)
  have h2 : g * (y * y) * g⁻¹ = 1 := by
    rw [show g * (y * y) * g⁻¹ = g * y * g⁻¹ * (g * y * g⁻¹) by group, h1]
  calc y * y = g⁻¹ * (g * (y * y) * g⁻¹) * g := by group
    _ = 1 := by rw [h2]; group

omit [Finite G] [IsMulCommutative ↥V] in
theorem conj_comm {g x y : G} (hx : x ∈ conjSubgroup V g) (hy : y ∈ conjSubgroup V g)
    [IsMulCommutative ↥V] : x * y = y * x := by
  have h1 : (⟨g * x * g⁻¹, mem_conjSubgroup_iff.1 hx⟩ : ↥V) * ⟨g * y * g⁻¹,
      mem_conjSubgroup_iff.1 hy⟩ = ⟨g * y * g⁻¹, mem_conjSubgroup_iff.1 hy⟩ *
      ⟨g * x * g⁻¹, mem_conjSubgroup_iff.1 hx⟩ := mul_comm _ _
  have h2 : g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := congrArg Subtype.val h1
  calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h2]
    _ = y * x := by group

structure Hyp4 (V : Subgroup G) (g : G) : Prop where
  notN : g ∉ Subgroup.normalizer (V : Set G)
  ne : ⁅V, conjSubgroup V g⁆ ≠ ⊥
  le : ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g

omit [Finite G] [IsMulCommutative ↥V] in
theorem commutator_conj_inv (g : G) :
    ⁅V, conjSubgroup V g⁻¹⁆ = conjSubgroup ⁅V, conjSubgroup V g⁆ g⁻¹ := by
  rw [E3.conjSubgroup_commutator, E3.conjSubgroup_conj_inv, Subgroup.commutator_comm]

omit [Finite G] [IsMulCommutative ↥V] in
theorem Hyp4.inv {g : G} (h : Hyp4 V g) : Hyp4 V g⁻¹ where
  notN := fun h' => h.notN (by simpa using Subgroup.inv_mem _ h')
  ne := by
    intro h'
    apply h.ne
    rw [commutator_conj_inv] at h'
    have h2 := congrArg (fun A => conjSubgroup A g) h'
    simpa only [E3.conjSubgroup_inv_conj, E3.conjSubgroup_bot] using h2
  le := by
    rw [commutator_conj_inv]
    calc conjSubgroup ⁅V, conjSubgroup V g⁆ g⁻¹ ≤ conjSubgroup (V ⊓ conjSubgroup V g) g⁻¹ :=
          E3.conjSubgroup_mono_left _ h.le
      _ = V ⊓ conjSubgroup V g⁻¹ := by rw [E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv, inf_comm]

omit [Finite G] [IsMulCommutative ↥V] in
theorem Hyp4.le_normalizer {g : G} (h : Hyp4 V g) :
    conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) :=
  le_normalizer_of_commutator_le (h.le.trans inf_le_left)

theorem Hyp4.le_M (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {g : G} (h : Hyp4 V g) :
    conjSubgroup V g ≤ Subgroup.normalizer (L : Set G) :=
  h.le_normalizer.trans (normalizer_V_le h331 h1222 F hH)

theorem fpf_of_hyp4 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) {y : G} (hy : y ∈ conjSubgroup V g) {σ : Perm (Fin 8)}
    (hσ : ActsAs F y σ) (hσ1 : σ ≠ 1) : ∀ k, σ k ≠ k := by
  intro k hk
  obtain ⟨i, hi⟩ := exists_moved hσ1
  obtain ⟨v, hv⟩ := F.β_surj (QuotientGroup.mk (pe i k))
  have hyN := hg.le_normalizer hy
  set w : ↥V := ⟨y * v * y⁻¹, conj_mem hyN v⟩ with hw
  have hcG : ((v * w⁻¹ : ↥V) : G) = v * y * v⁻¹ * y⁻¹ := by
    simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcU : ((v * w⁻¹ : ↥V) : G) ∈ V ⊓ conjSubgroup V g := by
    rw [hcG]
    exact hg.le (Subgroup.commutator_mem_commutator v.2 hy)
  have hβ : F.β (v * w⁻¹) = (QuotientGroup.mk (pe i k) : D8) *
      (dAct σ (QuotientGroup.mk (pe i k)))⁻¹ := by
    rw [map_mul, map_inv, hσ v w rfl, hv]
  have hn : IsNonsing (F.β (v * w⁻¹)) := by
    rw [hβ]
    exact nonsing_comm σ hk hi
  have hc1 : ((v * w⁻¹ : ↥V) : G) ≠ 1 := fun h =>
    ne_one_of_nonsing hn (by rw [show v * w⁻¹ = 1 from Subtype.ext h, map_one])
  obtain ⟨hcV, h4⟩ := wt4_of_mem_inter h331 h1222 h1262 F hH hfus hg.notN hcU hc1
  exact not_nonsing_and_wt4 hn h4

theorem bot_of_hyp4 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hZ
  obtain ⟨E⟩ := exists_frame126E h1222 F hH hZ
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  apply hg.ne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  have hyN := hg.le_normalizer hy
  have hyL := hg.le_M h331 h1222 F hH hy
  obtain ⟨σ, hσ⟩ := exists_actsAs F hH hyL hyN
  by_cases hσ1 : σ = 1
  · rw [hσ1] at hσ
    exact mem_centralizer_of_actsAs_one F hVL hLV hyL hyN hσ
  exfalso
  have hfpf := fpf_of_hyp4 h331 h1222 h1262 F hH hfus hg hy hσ hσ1
  have hσ2 : σ ^ 2 = 1 :=
    pow_eq_one_of_actsAs hσ hyN (by rw [pow_two]; exact mul_self_conj h1222 hH hy)
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    rw [← Perm.mul_apply, ← pow_two, hσ2, Perm.one_apply]
  obtain ⟨m, hm⟩ := exists_mul_inv_coreAct_eq_eOm σ hfpf hinv
  set v : ↥V := E.γ.symm m with hv
  set w : ↥V := ⟨y * v * y⁻¹, conj_mem hyN v⟩ with hw
  have hcG : ((v * w⁻¹ : ↥V) : G) = v * y * v⁻¹ * y⁻¹ := by
    simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcU : ((v * w⁻¹ : ↥V) : G) ∈ V ⊓ conjSubgroup V g := by
    rw [hcG]
    exact hg.le (Subgroup.commutator_mem_commutator v.2 hy)
  have hcz : v * w⁻¹ = z0 E := by
    apply E.γ.injective
    rw [map_mul, map_inv, E.act y hyL hyN σ hσ v w rfl, hv, MulEquiv.apply_symm_apply, hm,
      gamma_z0]
  have hc1 : ((v * w⁻¹ : ↥V) : G) ≠ 1 := by
    rw [hcz]
    exact z0_ne_one' E
  obtain ⟨hcV, h4⟩ := wt4_of_mem_inter h331 h1222 h1262 F hH hfus hg.notN hcU hc1
  have e : (⟨((v * w⁻¹ : ↥V) : G), hcV⟩ : ↥V) = z0 E := by
    rw [← hcz]
  rw [e, beta_z0] at h4
  exact not_hasWt4_one h4

@[expose] noncomputable def perm8 (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    Perm (Fin 8) :=
  Classical.choose (exists_actsAs F hH hxL hxV)

theorem actsAs_perm8 (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    ActsAs F x (perm8 F hH hxL hxV) :=
  Classical.choose_spec (exists_actsAs F hH hxL hxV)

@[expose] noncomputable def nu (F : Frame126 T L V) (hH : Hyp126 G T L V) {X : Subgroup G}
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    ↥X →* Perm (Fin 8) where
  toFun x := perm8 F hH (hXL x.2) (hXV x.2)
  map_one' := (actsAs_perm8 F hH (hXL X.one_mem) (hXV X.one_mem)).unique (ActsAs.one F)
    (Subgroup.one_mem _)
  map_mul' x y := (actsAs_perm8 F hH (hXL (x * y).2) (hXV (x * y).2)).unique
    ((actsAs_perm8 F hH (hXL x.2) (hXV x.2)).mul (actsAs_perm8 F hH (hXL y.2) (hXV y.2))
      (hXV y.2)) (hXV (x * y).2)

section Nu

variable (F : Frame126 T L V) (hH : Hyp126 G T L V) {X : Subgroup G}
  (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hXV : X ≤ Subgroup.normalizer (V : Set G))

theorem actsAs_nu (x : ↥X) : ActsAs F x (nu F hH hXL hXV x) :=
  actsAs_perm8 F hH (hXL x.2) (hXV x.2)

theorem nu_eq {x : ↥X} {σ : Perm (Fin 8)} (h : ActsAs F x σ) : nu F hH hXL hXV x = σ :=
  (actsAs_nu F hH hXL hXV x).unique h (hXV x.2)

theorem mem_range_nu {σ : Perm (Fin 8)} :
    σ ∈ (nu F hH hXL hXV).range ↔ ∃ y ∈ X, ActsAs F y σ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, actsAs_nu F hH hXL hXV x⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, nu_eq F hH hXL hXV h⟩

theorem nu_eq_one_iff (x : ↥X) :
    nu F hH hXL hXV x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    have h1 := actsAs_nu F hH hXL hXV x
    rw [h] at h1
    exact mem_centralizer_of_actsAs_one F hH.hyp.irrPlus.2.2.2.1 hH.hyp.irrPlus.2.2.1 (hXL x.2)
      (hXV x.2) h1
  · intro h
    apply nu_eq
    intro v w hw
    have : w = v := Subtype.ext (by
      rw [hw, ← Subgroup.mem_centralizer_iff.1 h v v.2]
      group)
    rw [this, dAct_one]

theorem card_eq_mul :
    Nat.card X = Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) *
      Nat.card (nu F hH hXL hXV).range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (nu F hH hXL hXV).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (nu F hH hXL hXV)).toEquiv, mul_comm]
  congr 1
  exact Nat.card_congr
    { toFun := fun x => ⟨((x : ↥X) : G), (x : ↥X).2, (nu_eq_one_iff F hH hXL hXV _).1 x.2⟩
      invFun := fun y => ⟨⟨y, y.2.1⟩, (nu_eq_one_iff F hH hXL hXV ⟨y, y.2.1⟩).2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem mem_centralizer_iff (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (v : ↥V) :
    (v : G) ∈ Subgroup.centralizer (X : Set G) ↔ F.β v ∈ fixD (nu F hH hXL hXV).range := by
  constructor
  · intro h
    rw [mem_fixD]
    rintro _ ⟨x, rfl⟩
    have h1 := actsAs_nu F hH hXL hXV x
    have hw : (v : G) = (x : G) * v * (x : G)⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.1 h x x.2]
      group
    exact (h1 v v hw).symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := (mem_fixD.1 h) _ ⟨⟨x, hx⟩, rfl⟩
    set w : ↥V := ⟨x * v * x⁻¹, conj_mem (hXV hx) v⟩ with hw
    have h2 := actsAs_nu F hH hXL hXV ⟨x, hx⟩ v w rfl
    rw [h1] at h2
    have h3 : w = v := beta_inj F hZ h2
    have h4 : x * v * x⁻¹ = v := congrArg Subtype.val h3
    calc x * v = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [h4]

theorem card_centralizer_eq (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) = Nat.card (fixD (nu F hH hXL hXV).range) := by
  refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨F.β ⟨v, v.2.1⟩,
    (mem_centralizer_iff F hH hXL hXV hZ ⟨v, v.2.1⟩).1 v.2.2⟩) ⟨fun v v' h => ?_, fun y => ?_⟩)
  · have h1 : F.β ⟨v, v.2.1⟩ = F.β ⟨v', v'.2.1⟩ := congrArg Subtype.val h
    have h2 := beta_inj F hZ h1
    apply Subtype.ext
    exact congrArg (fun w : ↥V => (w : G)) h2
  · obtain ⟨v, hv⟩ := F.β_surj y
    have hvC := (mem_centralizer_iff F hH hXL hXV hZ v).2 (hv ▸ y.2)
    exact ⟨⟨v, v.2, hvC⟩, Subtype.ext hv⟩

end Nu

end S126L20c

end CFSG.Quasithin.H13
