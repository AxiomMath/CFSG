module

public import CFSG.Sporadic.Schreier.Co1LiftCheck
public import CFSG.Sporadic.Schreier.Co1AutTrivial
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_xor toVecD_injective)
open CFSG.Sporadic.SmallF2.Native Matrix CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2

attribute [local instance] xAct

theorem card_stabH :
    Nat.card stabH = 42305421312000 := by
  have hpre := xAct_pretransitive
  have horb : Nat.card (MulAction.orbit GA xz) * Nat.card (MulAction.stabilizer GA xz) =
      Nat.card GA := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup GA xz)
  have horbit : Nat.card (MulAction.orbit GA xz) = 98280 := by
    rw [MulAction.orbit_eq_univ GA xz, Nat.card_coe_set_eq, Set.ncard_univ, card_co1X_type]
  rw [horbit, card_GA_eq, stabilizer_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe stabH_le_GA).toEquiv] at horb
  omega

abbrev liftR : Array ℕ := Data.liftReps.toArray

theorem lift_facts :
    liftR.size = 2300 ∧ (∀ m < 4600, Native.clsVal liftR m < 2 ^ 24) ∧
    Native.vSorted (((List.range 4600).map (Native.clsVal liftR)).mergeSort
      fun a b => decide (a ≤ b)) = true ∧
    ∀ j < 2300,
      Native.inCls liftR (Native.act Native.hRows0 liftR[j]!) (co2OrigArrs[0]!)[j]! = true ∧
      Native.inCls liftR (Native.act Native.hRows1 liftR[j]!) (co2OrigArrs[1]!)[j]! = true := by
  have h := lift_check
  simp only [Native.liftCheck, Native.liftCheckOf, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

@[expose] noncomputable def clsV (m : ℕ) : Vec24 := toVecD 24 (Native.clsVal liftR m)

theorem clsV_lt {k : ℕ} (hk : k < 2300) : clsV k = toVecD 24 liftR[k]! := by
  unfold clsV Native.clsVal
  simp only [hk, ↓reduceIte]

theorem clsV_add {k : ℕ} (hk : k < 2300) : clsV (k + 2300) = stabVecOf 0 + clsV k := by
  unfold clsV Native.clsVal
  simp only [show ¬k + 2300 < 2300 by omega, hk, ↓reduceIte, Nat.add_sub_cancel]
  rw [toVecD_xor]
  rfl

theorem clsV_inj
    {m m' : ℕ} (hm : m < 4600) (hm' : m' < 4600) (h : clsV m = clsV m') :
    m = m' := by
  obtain ⟨-, hlt, hsort, -⟩ := lift_facts
  have hnodup : ((List.range 4600).map (Native.clsVal liftR)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mp ((vSorted_pairwise _ hsort).imp ne_of_lt)
  exact List.inj_on_of_nodup_map hnodup (List.mem_range.mpr hm) (List.mem_range.mpr hm')
    (toVecD_injective (hlt m hm) (hlt m' hm') h)

@[expose] def InCls (u : Vec24) (k : ℕ) : Prop := u = clsV k ∨ u = clsV (k + 2300)

theorem cls_unique
    {u : Vec24} {k k' : ℕ} (hk : k < 2300) (hk' : k' < 2300) (h : InCls u k)
    (h' : InCls u k') : k = k' := by
  rcases h with rfl | rfl <;> rcases h' with h' | h'
  · exact clsV_inj (by omega) (by omega) h'
  · have := clsV_inj (by omega) (by omega) h'
    omega
  · have := clsV_inj (by omega) (by omega) h'
    omega
  · have := clsV_inj (by omega) (by omega) h'
    omega

theorem inCls_mulVec {g : GL24}
    (hg : (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0) {u : Vec24}
    {k k' : ℕ} (hk : k < 2300) (hk' : k' < 2300) (hu : InCls u k)
    (hgk : InCls ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) k') :
    InCls ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u) k' := by
  unfold InCls at hu hgk ⊢
  rw [clsV_add hk'] at hgk ⊢
  rcases hu with rfl | rfl
  · exact hgk
  · rw [clsV_add hk, mulVec_add, hg]
    rcases hgk with h | h
    · right
      rw [h]
    · left
      rw [h, ← add_assoc, vec24_add_self, zero_add]

theorem inv_mulVec_mulVec (g : GL24) (v : Vec24) :
    ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem inCls_inv {g : GL24}
    (hg : (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0) {j k : ℕ}
    (hj : j < 2300) (hk : k < 2300)
    (h : InCls ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV j) k) :
    InCls (((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) j := by
  have hz : ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0 := by
    conv_lhs => rw [← hg]
    exact inv_mulVec_mulVec g _
  unfold InCls at h ⊢
  rw [clsV_add hk] at h
  rw [clsV_add hj]
  rcases h with h | h
  · left
    rw [← h, inv_mulVec_mulVec]
  · right
    have h' : clsV k = stabVecOf 0 + (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV j := by
      rw [h, ← add_assoc, vec24_add_self, zero_add]
    rw [h', mulVec_add, hz, inv_mulVec_mulVec]

theorem inCls_of_check {g : GL24} {X : Native.Rows} (hX : MRep X g) {a : Array ℕ} {k : ℕ}
    (hk : k < 2300) (h : Native.inCls liftR (Native.act X liftR[k]!) a[k]! = true) :
    InCls ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) a[k]! := by
  simp only [Native.inCls, Bool.or_eq_true, beq_iff_eq] at h
  unfold InCls clsV
  rw [← clsV, clsV_lt hk, MRep.mulVec hX]
  rcases h with h | h
  · left
    rw [h]
  · right
    rw [h]

theorem gen_inCls
    {i : ℕ} (hi : i < 2) {k : ℕ} (hk : k < 2300) :
    InCls ((((if i = 0 then stabH0 else stabH1) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      clsV k) (co2Gen i ⟨k, hk⟩) := by
  have hrep : (co2OrigArrs[i]!)[k]! = (co2Gen i ⟨k, hk⟩ : ℕ) := rep_co2Gen hi ⟨k, hk⟩
  rw [← hrep]
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact inCls_of_check stabH0_rep hk (lift_facts.2.2.2 k hk).1
  · exact inCls_of_check stabH1_rep hk (lift_facts.2.2.2 k hk).2

theorem gen_inCls_inv
    {i : ℕ} (hi : i < 2) {k : ℕ} (hk : k < 2300) :
    InCls (((((if i = 0 then stabH0 else stabH1) : GL24)⁻¹ : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) ((co2Gen i)⁻¹ ⟨k, hk⟩) := by
  have hg : (((if i = 0 then stabH0 else stabH1) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      stabVecOf 0 = stabVecOf 0 := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact stabH_fix_z stabH0_mem
    · exact stabH_fix_z stabH1_mem
  have h := gen_inCls hi ((co2Gen i)⁻¹ ⟨k, hk⟩).2
  have he : (co2Gen i ⟨((co2Gen i)⁻¹ ⟨k, hk⟩ : ℕ), ((co2Gen i)⁻¹ ⟨k, hk⟩).2⟩ : ℕ) = k :=
    congrArg Fin.val (Equiv.Perm.eq_inv_iff_eq.mp rfl)
  rw [he] at h
  exact inCls_inv hg ((co2Gen i)⁻¹ ⟨k, hk⟩).2 hk h

theorem exists_inCls_of_mem
    {g : GL24} (hg : g ∈ Subgroup.closure ({stabH0, stabH1} : Set GL24)) :
    ∀ {k : ℕ}, k < 2300 →
      ∃ k' < 2300, InCls ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) k' := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨_, (co2Gen 0 ⟨k, hk⟩).2, gen_inCls (i := 0) (by norm_num) hk⟩
    · rw [hx]
      exact ⟨_, (co2Gen 1 ⟨k, hk⟩).2, gen_inCls (i := 1) (by norm_num) hk⟩
  | inv_mem x hx =>
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨_, ((co2Gen 0)⁻¹ ⟨k, hk⟩).2, gen_inCls_inv (i := 0) (by norm_num) hk⟩
    · rw [hx]
      exact ⟨_, ((co2Gen 1)⁻¹ ⟨k, hk⟩).2, gen_inCls_inv (i := 1) (by norm_num) hk⟩
  | one =>
    intro k hk
    refine ⟨k, hk, Or.inl ?_⟩
    rw [Units.val_one, one_mulVec]
  | mul x y hx hy ihx ihy =>
    intro k hk
    obtain ⟨k₁, hk₁, h₁⟩ := ihy hk
    obtain ⟨k₂, hk₂, h₂⟩ := ihx hk₁
    refine ⟨k₂, hk₂, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec]
    exact inCls_mulVec (stabH_fix_z hx) hk₁ hk₂ h₁ h₂

theorem exists_cls
    (g : stabH) (k : Fin 2300) :
    ∃ k' : Fin 2300, InCls (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) k' := by
  obtain ⟨k', hk', h⟩ := exists_inCls_of_mem g.2 k.2
  exact ⟨⟨k', hk'⟩, h⟩

@[expose] noncomputable def clsAct
    (g : stabH) (k : Fin 2300) : Fin 2300 :=
  (exists_cls g k).choose

theorem clsAct_spec
    (g : stabH) (k : Fin 2300) :
    InCls (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) (clsAct g k) :=
  (exists_cls g k).choose_spec

theorem clsAct_eq
    {g : stabH} {k k' : Fin 2300}
    (h : InCls (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) k') :
    clsAct g k = k' :=
  Fin.ext (cls_unique (clsAct g k).2 k'.2 (clsAct_spec g k) h)

@[expose, instance_reducible] noncomputable def clsMulAction :
    MulAction stabH (Fin 2300) where
  smul := clsAct
  one_smul k := clsAct_eq (by
    show InCls (((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ clsV k) k
    rw [Units.val_one, one_mulVec]
    exact Or.inl rfl)
  mul_smul g h k := clsAct_eq (by
    show InCls ((((g : GL24) * (h : GL24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      clsV k) (clsAct g (clsAct h k))
    rw [Units.val_mul, ← mulVec_mulVec]
    exact inCls_mulVec (stabH_fix_z g.2) (clsAct h k).2 (clsAct g (clsAct h k)).2
      (clsAct_spec h k) (clsAct_spec g (clsAct h k)))

attribute [local instance] clsMulAction

@[expose] noncomputable def clsHom :
    stabH →* Equiv.Perm (Fin 2300) :=
  MulAction.toPermHom stabH (Fin 2300)

theorem clsHom_apply
    (g : stabH) (k : Fin 2300) : clsHom g k = clsAct g k := rfl

theorem clsHom_gen
    {i : ℕ} (hi : i < 2) :
    clsHom ⟨if i = 0 then stabH0 else stabH1, by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact stabH0_mem
      · exact stabH1_mem⟩ = co2Gen i :=
  Equiv.ext fun k => by
    rw [clsHom_apply]
    exact clsAct_eq (gen_inCls hi k.2)

theorem clsHom_gen0 :
    clsHom ⟨stabH0, stabH0_mem⟩ = co2Gen 0 := clsHom_gen (i := 0) (by norm_num)

theorem clsHom_gen1 :
    clsHom ⟨stabH1, stabH1_mem⟩ = co2Gen 1 := clsHom_gen (i := 1) (by norm_num)

theorem stab_mk_eq {g h : GL24} (hg : g ∈ stabH) (hh : h ∈ stabH) (e : g = h) :
    (⟨g, hg⟩ : stabH) = ⟨h, hh⟩ :=
  Subtype.ext e

theorem clsHom_mem_co2P
    {g : GL24} (hg' : g ∈ Subgroup.closure ({stabH0, stabH1} : Set GL24)) :
    ∀ hg : g ∈ stabH, clsHom ⟨g, hg⟩ ∈ co2P := by
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [stab_mk_eq hg stabH0_mem hx, clsHom_gen0]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [stab_mk_eq hg stabH1_mem hx, clsHom_gen1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | one =>
    intro hg
    rw [show (⟨1, hg⟩ : stabH) = 1 from rfl, map_one]
    exact co2P.one_mem
  | mul x y hx hy ihx ihy =>
    intro hg
    have hx' : x ∈ stabH := hx
    have hy' : y ∈ stabH := hy
    rw [show (⟨x * y, hg⟩ : stabH) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl, map_mul]
    exact co2P.mul_mem (ihx hx') (ihy hy')
  | inv x hx ih =>
    intro hg
    have hx' : x ∈ stabH := hx
    rw [show (⟨x⁻¹, hg⟩ : stabH) = (⟨x, hx'⟩ : stabH)⁻¹ from rfl, map_inv]
    exact co2P.inv_mem (ih hx')

theorem clsHom_range :
    clsHom.range = co2P := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact clsHom_mem_co2P hg hg
  · rw [co2P, Subgroup.closure_le]
    rintro _ (h | h)
    · rw [h]
      exact ⟨_, clsHom_gen0⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨_, clsHom_gen1⟩

theorem clsHom_rangeRestrict_bijective :
    Function.Bijective clsHom.rangeRestrict := by
  have : Finite stabH := Nat.finite_of_card_ne_zero (by rw [card_stabH]; norm_num)
  refine clsHom.rangeRestrict_surjective.bijective_of_nat_card_le ?_
  rw [card_stabH, clsHom_range, card_co2P]

@[expose] noncomputable def stabPermEquiv :
    stabH ≃* co2P :=
  (MulEquiv.ofBijective clsHom.rangeRestrict clsHom_rangeRestrict_bijective).trans
    (MulEquiv.subgroupCongr clsHom_range)

theorem stabPermEquiv_apply
    (g : stabH) : (stabPermEquiv g : Equiv.Perm (Fin 2300)) = clsHom g :=
  rfl

@[expose] noncomputable def stabCo2Equiv :
    stabH ≃* Blueprint.NativeSporadic.Co2 :=
  stabPermEquiv.trans co2PermEquiv.symm

end CFSG.Sporadic.Co1Schreier
