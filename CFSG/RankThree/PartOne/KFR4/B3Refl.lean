module

public import CFSG.RankThree.PartOne.KFCL.Core
public import CFSG.RankThree.PartOne.KFR4.B3Comb

public section

namespace CFSG.RankThree.PartOne.KFR4

open Subgroup CFSG.RankThree.PartOne.KFCL

section Coord

variable {p : ℕ} {Γ : Type*} [Group Γ] {T : Subgroup Γ}

@[expose] def lin (c : ↥T ≃* Multiplicative (Vec p)) (x : ↥T) : Vec p :=
  Multiplicative.toAdd (c x)

theorem lin_mul (c : ↥T ≃* Multiplicative (Vec p)) (x y : ↥T) :
    lin c (x * y) = lin c x + lin c y := by
  simp [lin]

theorem lin_one (c : ↥T ≃* Multiplicative (Vec p)) : lin c 1 = 0 := by
  simp [lin]

theorem lin_inv (c : ↥T ≃* Multiplicative (Vec p)) (x : ↥T) : lin c x⁻¹ = - lin c x := by
  simp [lin]

theorem lin_injective (c : ↥T ≃* Multiplicative (Vec p)) : Function.Injective (lin c) := by
  intro x y h
  exact c.injective (Multiplicative.toAdd.injective h)

theorem lin_surjective (c : ↥T ≃* Multiplicative (Vec p)) : Function.Surjective (lin c) := by
  intro v
  obtain ⟨x, hx⟩ := c.surjective (Multiplicative.ofAdd v)
  exact ⟨x, by simp [lin, hx]⟩

@[expose] def hypT (c : ↥T ≃* Multiplicative (Vec p)) (ρ : Root) : Subgroup ↥T where
  carrier := {x | ρ.vecp p ⬝ᵥ lin c x = 0}
  mul_mem' := fun {x y} hx hy => by
    have hx' : ρ.vecp p ⬝ᵥ lin c x = 0 := hx
    have hy' : ρ.vecp p ⬝ᵥ lin c y = 0 := hy
    show ρ.vecp p ⬝ᵥ lin c (x * y) = 0
    rw [lin_mul, dotProduct_add, hx', hy', add_zero]
  one_mem' := by
    show ρ.vecp p ⬝ᵥ lin c 1 = 0
    rw [lin_one, dotProduct_zero]
  inv_mem' := fun {x} hx => by
    have hx' : ρ.vecp p ⬝ᵥ lin c x = 0 := hx
    show ρ.vecp p ⬝ᵥ lin c x⁻¹ = 0
    rw [lin_inv, dotProduct_neg, hx', neg_zero]

@[expose] def hypS (c : ↥T ≃* Multiplicative (Vec p)) (ρ : Root) : Subgroup Γ :=
  (hypT c ρ).map T.subtype

theorem mem_hypT {c : ↥T ≃* Multiplicative (Vec p)} {ρ : Root} {x : ↥T} :
    x ∈ hypT c ρ ↔ ρ.vecp p ⬝ᵥ lin c x = 0 := Iff.rfl

theorem mem_hypS {c : ↥T ≃* Multiplicative (Vec p)} {ρ : Root} {x : Γ} :
    x ∈ hypS c ρ ↔ ∃ h : x ∈ T, ρ.vecp p ⬝ᵥ lin c ⟨x, h⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem hypS_le (c : ↥T ≃* Multiplicative (Vec p)) (ρ : Root) : hypS c ρ ≤ T := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end Coord

section Arith

variable (p : ℕ)

@[expose] def Root.idx : Root → Fin 3
  | .s1 => 0 | .s2 => 1 | .s3 => 2
  | .m12 => 0 | .m13 => 0 | .m23 => 1
  | .p12 => 0 | .p13 => 0 | .p23 => 1

theorem vecp_idx (ρ : Root) : ρ.vecp p ρ.idx = 1 := by
  cases ρ <;> simp [Root.vecp, Root.vec, Root.idx]

theorem dot_vecp_single (ρ : Root) (k : Fin 3) (a : ZMod p) :
    ρ.vecp p ⬝ᵥ (a • (Pi.single k 1 : Vec p)) = a * ρ.vecp p k := by
  rw [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]

theorem nsq_smul_corp (ρ : Root) : ((ρ.nsq : ℤ) : ZMod p) • ρ.corp p = (2 : ZMod p) • ρ.vecp p := by
  cases ρ <;> funext k <;> fin_cases k <;> simp [Root.nsq, Root.corp, Root.vecp, Root.cor, Root.vec]

theorem dot_vecp_vecp_self (ρ : Root) : ρ.vecp p ⬝ᵥ ρ.vecp p = ((ρ.nsq : ℤ) : ZMod p) := by
  rw [dot_vecp_vecp, dotZ_vec_vec]

theorem two_mul_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {a : ZMod p} (h : 2 * a = 0) :
    a = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases mul_eq_zero.1 h with h2 | h2
  · exfalso
    have : ((2 : ℕ) : ZMod p) = 0 := by simpa using h2
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · exact h2

theorem nsq_mul_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (ρ : Root) {a : ZMod p}
    (h : ((ρ.nsq : ℤ) : ZMod p) * a = 0) : a = 0 := by
  cases ρ
  all_goals first
    | exact two_mul_eq_zero hp hp3 (by simpa [Root.nsq] using h)
    | simpa [Root.nsq] using h

end Arith

section Hyp

variable {p : ℕ} {Γ : Type*} [Group Γ] {T : Subgroup Γ} (c : ↥T ≃* Multiplicative (Vec p))

@[expose] def actT (g : Vec p ≃ₗ[ZMod p] Vec p) : MulAut ↥T :=
  (c.trans (AddEquiv.toMultiplicative g.toAddEquiv)).trans c.symm

theorem lin_actT (g : Vec p ≃ₗ[ZMod p] Vec p) (x : ↥T) : lin c (actT c g x) = g (lin c x) := by
  have : c (actT c g x) = (AddEquiv.toMultiplicative g.toAddEquiv) (c x) := by
    simp [actT]
  rw [lin, this]
  rfl

@[expose] def reflT (ρ : Root) : MulAut ↥T := actT c (reflLin p ρ)

theorem lin_reflT (ρ : Root) (x : ↥T) : lin c (reflT c ρ x) = reflLin p ρ (lin c x) :=
  lin_actT c _ x

theorem relIndex_hypS (hp : p.Prime) (ρ : Root) : (hypS c ρ).relIndex T = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let f : ↥T →* Multiplicative (ZMod p) :=
    { toFun := fun x => Multiplicative.ofAdd (ρ.vecp p ⬝ᵥ lin c x)
      map_one' := by simp [lin_one]
      map_mul' := fun x y => by simp [lin_mul, dotProduct_add, ofAdd_add] }
  have hker : f.ker = hypT c ρ := by
    ext x
    simp [f, MonoidHom.mem_ker, mem_hypT]
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := lin_surjective c ((Multiplicative.toAdd a) • (Pi.single ρ.idx 1 : Vec p))
    refine ⟨x, ?_⟩
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hx, dot_vecp_single, vecp_idx, mul_one]
    rfl
  have hidx : (hypT c ρ).index = p := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hmap : (hypS c ρ).relIndex T = (hypT c ρ).relIndex ⊤ := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := T.subtype) (hypT c ρ) ⊤
      T.subtype_injective
    have h2 : (⊤ : Subgroup ↥T).map T.subtype = T := by
      rw [← MonoidHom.range_eq_map]
      exact T.range_subtype
    rw [h2] at h1
    exact h1
  rw [hmap, Subgroup.relIndex_top_right]
  exact hidx

theorem mem_hypS_coe {ρ : Root} {x : ↥T} : (x : Γ) ∈ hypS c ρ ↔ ρ.vecp p ⬝ᵥ lin c x = 0 := by
  rw [mem_hypS]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem hypS_injective (hp5 : 5 ≤ p) : Function.Injective (hypS c : Root → _) := by
  intro ρ ρ' h
  by_contra hne
  have hg := gram_cast_ne_zero (p := p) hp5 hne
  have hcomm : ρ'.vecp p ⬝ᵥ ρ.vecp p = ((dotZ ρ.vec ρ'.vec : ℤ) : ZMod p) := by
    rw [dotProduct_comm, dot_vecp_vecp]
  obtain ⟨x, hx⟩ := lin_surjective c (((ρ.nsq : ℤ) : ZMod p) • ρ'.vecp p -
    ((dotZ ρ.vec ρ'.vec : ℤ) : ZMod p) • ρ.vecp p)
  have h1 : (x : Γ) ∈ hypS c ρ := by
    rw [mem_hypS_coe, hx, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dot_vecp_vecp_self, dot_vecp_vecp]
    ring
  have h2 : (x : Γ) ∈ hypS c ρ' := by
    rw [← h]
    exact h1
  rw [mem_hypS_coe, hx, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dot_vecp_vecp_self p ρ', hcomm] at h2
  apply hg
  push_cast
  linear_combination h2

@[expose] def lineT (ρ : Root) : Subgroup ↥T where
  carrier := {x | ∃ a : ZMod p, lin c x = a • ρ.vecp p}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [lin_mul, ha, hb, add_smul]⟩
  one_mem' := ⟨0, by rw [lin_one, zero_smul]⟩
  inv_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨-a, by rw [lin_inv, ha, neg_smul]⟩

theorem mem_lineT {ρ : Root} {x : ↥T} : x ∈ lineT c ρ ↔ ∃ a : ZMod p, lin c x = a • ρ.vecp p :=
  Iff.rfl

theorem lin_symm (v : Vec p) : lin c (c.symm (Multiplicative.ofAdd v)) = v := by
  simp [lin]

theorem card_lineT (ρ : Root) : Nat.card (lineT c ρ) = p := by
  have hbij : Function.Bijective (fun a : ZMod p =>
      (⟨c.symm (Multiplicative.ofAdd (a • ρ.vecp p)), ⟨a, lin_symm c _⟩⟩ : lineT c ρ)) := by
    refine ⟨fun a b hab => ?_, fun ⟨x, a, ha⟩ => ⟨a, ?_⟩⟩
    · have h := congrArg (fun z : lineT c ρ => lin c z.1) hab
      simp only [lin_symm] at h
      have := congrFun h ρ.idx
      simpa [vecp_idx] using this
    · apply Subtype.ext
      apply lin_injective c
      show lin c (c.symm _) = lin c x
      rw [lin_symm, ha]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm.trans (Nat.card_zmod p)

theorem inf_eq_map_lineT {ρ : Root} {B : Subgroup Γ}
    (hB : ∀ x : ↥T, (x : Γ) ∈ B ↔ x ∈ lineT c ρ) : T ⊓ B = (lineT c ρ).map T.subtype := by
  ext y
  constructor
  · rintro ⟨hyT, hyB⟩
    exact ⟨⟨y, hyT⟩, (hB ⟨y, hyT⟩).1 hyB, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (hB x).2 hx⟩

theorem card_inf_block {ρ : Root} {B : Subgroup Γ}
    (hB : ∀ x : ↥T, (x : Γ) ∈ B ↔ x ∈ lineT c ρ) : Nat.card ↥(T ⊓ B) = p := by
  rw [inf_eq_map_lineT c hB, Subgroup.card_map_of_injective T.subtype_injective, card_lineT]

theorem hypS_inf_line (hp : p.Prime) (hp3 : 3 ≤ p) {ρ : Root} {B : Subgroup Γ}
    (hB : ∀ x : ↥T, (x : Γ) ∈ B ↔ x ∈ lineT c ρ) : hypS c ρ ⊓ (T ⊓ B) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro y ⟨hy1, hyT, hyB⟩
  obtain ⟨a, ha⟩ := (hB ⟨y, hyT⟩).1 hyB
  have h0 : ρ.vecp p ⬝ᵥ lin c ⟨y, hyT⟩ = 0 := (mem_hypS_coe c (x := ⟨y, hyT⟩)).1 hy1
  rw [ha, dotProduct_smul, smul_eq_mul, dot_vecp_vecp_self] at h0
  have ha0 : a = 0 := nsq_mul_eq_zero hp hp3 ρ (by rw [mul_comm]; exact h0)
  have h1 : (⟨y, hyT⟩ : ↥T) = 1 :=
    lin_injective c (by rw [ha, ha0, zero_smul, lin_one])
  exact congrArg Subtype.val h1

theorem hypS_sup_line (hp : p.Prime) (hp3 : 3 ≤ p) {ρ : Root} {B : Subgroup Γ}
    (hB : ∀ x : ↥T, (x : Γ) ∈ B ↔ x ∈ lineT c ρ) : hypS c ρ ⊔ (T ⊓ B) = T := by
  have : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · exact sup_le (hypS_le c ρ) inf_le_left
  · intro y hyT
    have hn : ((ρ.nsq : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      exact one_ne_zero (nsq_mul_eq_zero hp hp3 ρ (a := 1) (by rw [h0, zero_mul]))
    obtain ⟨r, hr⟩ := lin_surjective c
      ((((ρ.nsq : ℤ) : ZMod p)⁻¹ * (ρ.vecp p ⬝ᵥ lin c ⟨y, hyT⟩)) • ρ.vecp p)
    have hrB : (r : Γ) ∈ T ⊓ B := ⟨r.2, (hB r).2 ⟨_, hr⟩⟩
    have hz : (⟨y, hyT⟩ * r⁻¹ : ↥T) ∈ hypT c ρ := by
      rw [mem_hypT, lin_mul, lin_inv, hr, dotProduct_add, dotProduct_neg, dotProduct_smul,
        smul_eq_mul, dot_vecp_vecp_self]
      have : ((ρ.nsq : ℤ) : ZMod p)⁻¹ * (ρ.vecp p ⬝ᵥ lin c ⟨y, hyT⟩) * ((ρ.nsq : ℤ) : ZMod p) =
          ρ.vecp p ⬝ᵥ lin c ⟨y, hyT⟩ := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      rw [this, add_neg_cancel]
    have hyz : y = ((⟨y, hyT⟩ * r⁻¹ : ↥T) : Γ) * (r : Γ) := by simp
    rw [hyz]
    exact Subgroup.mul_mem_sup ((mem_hypS_coe c).2 hz) hrB

theorem reflT_fix {ρ : Root} {x : ↥T} (hx : (x : Γ) ∈ hypS c ρ) : reflT c ρ x = x := by
  apply lin_injective c
  rw [lin_reflT, reflLin_apply, (mem_hypS_coe c).1 hx, zero_smul, sub_zero]

theorem reflT_inv {ρ : Root} {x : ↥T} (hx : x ∈ lineT c ρ) : reflT c ρ x = x⁻¹ := by
  obtain ⟨a, ha⟩ := hx
  apply lin_injective c
  rw [lin_reflT, lin_inv, reflLin_apply, ha, dotProduct_smul, smul_eq_mul, dot_vecp_vecp_self]
  funext k
  have hk := congrFun (nsq_smul_corp p ρ) k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hk ⊢
  linear_combination (-a) * hk

@[expose] def actTHom : (Vec p ≃ₗ[ZMod p] Vec p) →* MulAut ↥T where
  toFun := actT c
  map_one' := MulEquiv.ext fun x => lin_injective c (by rw [lin_actT]; rfl)
  map_mul' g h := MulEquiv.ext fun x => lin_injective c (by
    rw [lin_actT, MulAut.mul_apply, lin_actT, lin_actT]
    rfl)

theorem actT_injective : Function.Injective (actT c : (Vec p ≃ₗ[ZMod p] Vec p) → MulAut ↥T) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := lin_surjective c v
  have := congrArg (fun φ : MulAut ↥T => lin c (φ x)) hgh
  simpa [lin_actT] using this

theorem card_closure_reflT_le [NeZero p] (hp3 : 3 ≤ p) :
    Nat.card ↥(Subgroup.closure (Set.range (reflT c))) ≤ 48 := by
  have hrange : Set.range (reflT c) = (actTHom c) '' Set.range (reflLin p) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← MonoidHom.map_closure, Subgroup.card_map_of_injective (actT_injective c)]
  exact card_closure_refl_le p hp3

theorem sg_cases (σ ρ : Root) : Root.sg σ ρ = 1 ∨ Root.sg σ ρ = -1 := by
  cases σ <;> cases ρ <;> simp [Root.sg]

theorem sg_cast_mul_self (σ ρ : Root) :
    ((Root.sg σ ρ : ℤ) : ZMod p) * ((Root.sg σ ρ : ℤ) : ZMod p) = 1 := by
  rcases sg_cases σ ρ with h | h <;> rw [h] <;> simp

theorem reflLin_reflLin (σ : Root) (v : Vec p) : reflLin p σ (reflLin p σ v) = v :=
  reflEnd_involutive p σ v

theorem dot_act_reflLin (σ ρ : Root) (v : Vec p) :
    (Root.act σ ρ).vecp p ⬝ᵥ reflLin p σ v = ((Root.sg σ ρ : ℤ) : ZMod p) * (ρ.vecp p ⬝ᵥ v) := by
  have h1 := dot_reflLin p σ (ρ.vecp p) v
  rw [reflLin_vecp, smul_dotProduct, smul_eq_mul] at h1
  rw [← h1, ← mul_assoc, sg_cast_mul_self, one_mul]

theorem dot_act_reflLin_eq_zero (σ ρ : Root) (v : Vec p) :
    (Root.act σ ρ).vecp p ⬝ᵥ reflLin p σ v = 0 ↔ ρ.vecp p ⬝ᵥ v = 0 := by
  rw [dot_act_reflLin]
  constructor
  · intro h
    have := congrArg (fun z => ((Root.sg σ ρ : ℤ) : ZMod p) * z) h
    simpa only [← mul_assoc, sg_cast_mul_self, one_mul, mul_zero] using this
  · intro h
    rw [h, mul_zero]

theorem map_hypS_conj {σ : Root} {w : Γ} (hw : ∀ x : ↥T, w * x * w⁻¹ = (reflT c σ x : Γ))
    (ρ : Root) : (hypS c ρ).map (MulAut.conj w).toMonoidHom = hypS c (Root.act σ ρ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxT, hx0⟩ := mem_hypS.1 hx
    have h1 : (MulAut.conj w).toMonoidHom x = ((reflT c σ ⟨x, hxT⟩ : ↥T) : Γ) := hw ⟨x, hxT⟩
    rw [h1, mem_hypS_coe, lin_reflT, dot_act_reflLin_eq_zero]
    exact hx0
  · intro hy
    obtain ⟨hyT, hy0⟩ := mem_hypS.1 hy
    have h3 : reflT c σ (reflT c σ ⟨y, hyT⟩) = ⟨y, hyT⟩ := by
      apply lin_injective c
      rw [lin_reflT, lin_reflT, reflLin_reflLin]
    have h2 : (MulAut.conj w).toMonoidHom ((reflT c σ ⟨y, hyT⟩ : ↥T) : Γ) =
        ((reflT c σ (reflT c σ ⟨y, hyT⟩) : ↥T) : Γ) := hw (reflT c σ ⟨y, hyT⟩)
    refine ⟨((reflT c σ ⟨y, hyT⟩ : ↥T) : Γ), (mem_hypS_coe c).2 ?_, ?_⟩
    · rw [lin_reflT, ← dot_act_reflLin_eq_zero σ ρ, reflLin_reflLin]
      exact hy0
    · rw [h2, h3]

end Hyp

section Data

structure B3Data (p : ℕ) {Γ : Type*} [Group Γ] (T : Subgroup Γ) where
  c : ↥T ≃* Multiplicative (Vec p)
  block : Root → Subgroup Γ
  block_simple : ∀ (ρ : Root) (N : Subgroup Γ), N ≤ block ρ →
    (N.subgroupOf (block ρ)).Normal → N = ⊥ ∨ N = block ρ
  block_perfect : ∀ ρ, ⁅block ρ, block ρ⁆ = block ρ
  block_cent : ∀ ρ, block ρ ≤ Subgroup.centralizer (hypS c ρ : Set Γ)
  block_T : ∀ (ρ : Root) (x : ↥T), (x : Γ) ∈ block ρ ↔ x ∈ lineT c ρ
  derived_le : ∀ S : Subgroup Γ, S ≤ T →
    (S.relIndex T = p ∨ ∃ e : Γ, e ∈ T ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) →
    ⁅Subgroup.centralizer (S : Set Γ), Subgroup.centralizer (S : Set Γ)⁆ ≤
      ⨆ i : {i : Root // S ≤ hypS c i}, block i.1
  realize : ∀ ρ : Root, ∃ w ∈ Subgroup.normalizer (T : Set Γ),
    ∀ x : ↥T, w * x * w⁻¹ = (reflT c ρ x : Γ)

namespace B3Data

variable {p : ℕ} {Γ : Type*} [Group Γ] {T : Subgroup Γ} (D : B3Data p T)

theorem eq_hypS_of_le (hp : p.Prime) {S : Subgroup Γ} (hS : S.relIndex T = p) {i : Root}
    (h : S ≤ hypS D.c i) : S = hypS D.c i := by
  have h1 := Subgroup.relIndex_mul_relIndex S (hypS D.c i) T h (hypS_le D.c i)
  rw [relIndex_hypS D.c hp i, hS] at h1
  have h2 : S.relIndex (hypS D.c i) = 1 :=
    Nat.eq_of_mul_eq_mul_right hp.pos (h1.trans (one_mul p).symm)
  exact le_antisymm h (Subgroup.relIndex_eq_one.1 h2)

theorem derived_hyp (hp : p.Prime) (hp5 : 5 ≤ p) (i : Root) :
    ⁅Subgroup.centralizer (hypS D.c i : Set Γ), Subgroup.centralizer (hypS D.c i : Set Γ)⁆ =
      D.block i := by
  apply le_antisymm
  · refine (D.derived_le _ (hypS_le D.c i) (Or.inl (relIndex_hypS D.c hp i))).trans ?_
    refine iSup_le fun j => ?_
    have hij : i = j.1 :=
      hypS_injective D.c hp5 (D.eq_hypS_of_le hp (relIndex_hypS D.c hp i) j.2)
    rw [← hij]
  · calc D.block i = ⁅D.block i, D.block i⁆ := (D.block_perfect i).symm
      _ ≤ _ := Subgroup.commutator_mono (D.block_cent i) (D.block_cent i)

theorem block_ne_bot (hp : p.Prime) (ρ : Root) : D.block ρ ≠ ⊥ := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨x, hx⟩ := lin_surjective D.c (ρ.vecp p)
  intro hbot
  have hxB : (x : Γ) ∈ D.block ρ := (D.block_T ρ x).2 ⟨1, by rw [hx, one_smul]⟩
  rw [hbot, Subgroup.mem_bot] at hxB
  have hx1 : x = 1 := Subtype.ext hxB
  have h0 : lin D.c x = 0 := by rw [hx1, lin_one]
  have := congrFun (hx.symm.trans h0) ρ.idx
  rw [vecp_idx] at this
  exact one_ne_zero this

theorem map_conj_eq_of_mem_normalizer {w : Γ} (hw : w ∈ Subgroup.normalizer (T : Set Γ)) :
    T.map (MulAut.conj w).toMonoidHom = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hw x).1 hx
  · intro hy
    have hyy : w * (w⁻¹ * y * w) * w⁻¹ = y := by group
    refine ⟨w⁻¹ * y * w, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hw (w⁻¹ * y * w)).2 (by rw [hyy]; exact hy)
    · show w * (w⁻¹ * y * w) * w⁻¹ = y
      exact hyy

theorem exists_map_eq (hp : p.Prime) (hp5 : 5 ≤ p) {φ : Γ ≃* Γ} (hφ : T.map φ.toMonoidHom = T)
    (i : Root) : ∃ j : Root, (D.block i).map φ.toMonoidHom = D.block j ∧
      (hypS D.c i).map φ.toMonoidHom = hypS D.c j := by
  have hle : (hypS D.c i).map φ.toMonoidHom ≤ T :=
    le_of_le_of_eq (Subgroup.map_mono (hypS_le D.c i)) hφ
  have hidx : ((hypS D.c i).map φ.toMonoidHom).relIndex T = p := by
    have := Subgroup.relIndex_map_map_of_injective (f := φ.toMonoidHom) (hypS D.c i) T φ.injective
    rw [hφ, relIndex_hypS D.c hp i] at this
    exact this
  have hcomm : ⁅Subgroup.centralizer (((hypS D.c i).map φ.toMonoidHom : Subgroup Γ) : Set Γ),
      Subgroup.centralizer (((hypS D.c i).map φ.toMonoidHom : Subgroup Γ) : Set Γ)⁆ =
        (D.block i).map φ.toMonoidHom := by
    rw [← map_centralizer_equiv, ← Subgroup.map_commutator, D.derived_hyp hp hp5 i]
  have hder := D.derived_le _ hle (Or.inl hidx)
  rw [hcomm] at hder
  have hex : ∃ j : Root, (hypS D.c i).map φ.toMonoidHom ≤ hypS D.c j := by
    by_contra hno
    push Not at hno
    have : IsEmpty {j : Root // (hypS D.c i).map φ.toMonoidHom ≤ hypS D.c j} :=
      ⟨fun j => hno j.1 j.2⟩
    rw [iSup_of_empty, le_bot_iff] at hder
    apply D.block_ne_bot hp i
    exact (Subgroup.map_eq_bot_iff_of_injective (f := φ.toMonoidHom) _ φ.injective).1 hder
  obtain ⟨j, hj⟩ := hex
  have hjeq := D.eq_hypS_of_le hp hidx hj
  refine ⟨j, ?_, hjeq⟩
  rw [← hcomm, hjeq, D.derived_hyp hp hp5 j]

@[expose] noncomputable def rootData (hp : p.Prime) (hp5 : 5 ≤ p) : RootData p T where
  ι := Root
  block := D.block
  hyp := hypS D.c
  W := Subgroup.normalizer (T : Set Γ)
  W_le := le_rfl
  hyp_le := hypS_le D.c
  hyp_ne i := fun h => by
    have := relIndex_hypS D.c hp i
    rw [h, Subgroup.relIndex_self] at this
    exact hp.one_lt.ne this
  hyp_inj := hypS_injective D.c hp5
  block_le := D.block_cent
  block_simple := D.block_simple
  derived_le := D.derived_le
  weyl w hw i := D.exists_map_eq hp hp5 (map_conj_eq_of_mem_normalizer hw) i

theorem gen_aux (hp : p.Prime) (hp5 : 5 ≤ p) (J : Set Root)
    (hJ : (D.rootData hp hp5).WStable J)
    (hcl : Subgroup.closure (reflT D.c '' J) = Subgroup.closure (Set.range (reflT D.c))) :
    J = Set.univ := by
  have hcl' : Subgroup.closure (reflLin p '' J) = Subgroup.closure (Set.range (reflLin p)) := by
    have hΦ : Function.Injective (actTHom D.c) := actT_injective D.c
    apply Subgroup.map_injective hΦ
    have e1 : (actTHom D.c) '' (reflLin p '' J) = reflT D.c '' J := by
      rw [Set.image_image]
      rfl
    have e2 : (actTHom D.c) '' Set.range (reflLin p) = Set.range (reflT D.c) := by
      rw [← Set.range_comp]
      rfl
    show (Subgroup.closure (reflLin p '' J)).map (actTHom D.c) =
      (Subgroup.closure (Set.range (reflLin p))).map (actTHom D.c)
    rw [MonoidHom.map_closure, MonoidHom.map_closure, e1, e2]
    exact hcl
  obtain ⟨ρs, hρsJ, hρs⟩ := exists_short_of_closure_eq p (by omega) hcl'
  obtain ⟨ρl, hρlJ, hρl⟩ := exists_long_of_closure_eq p (by omega) hcl'
  have hact : ∀ σ : Root, ∀ i ∈ J, Root.act σ i ∈ J := by
    intro σ i hi
    obtain ⟨w, hw, hwσ⟩ := D.realize σ
    obtain ⟨j, hjJ, -, hjh⟩ := hJ w hw i hi
    have hjh' : (hypS D.c i).map (MulAut.conj w).toMonoidHom = hypS D.c j := hjh
    have : hypS D.c j = hypS D.c (Root.act σ i) := by
      rw [← hjh']
      exact map_hypS_conj D.c hwσ i
    rw [← hypS_injective D.c hp5 this]
    exact hjJ
  rw [Set.eq_univ_iff_forall]
  intro ρ
  by_cases hs : ρ.IsShort
  · obtain ⟨σ, τ, h⟩ := act_transitive ρs ρ (iff_of_true hρs hs)
    rw [← h]
    exact hact σ _ (hact τ _ hρsJ)
  · obtain ⟨σ, τ, h⟩ := act_transitive ρl ρ (iff_of_false hρl hs)
    rw [← h]
    exact hact σ _ (hact τ _ hρlJ)

@[expose] noncomputable def reflData (hp : p.Prime) (hp5 : 5 ≤ p) :
    (D.rootData hp hp5).ReflData 48 :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  { Tblock_card := fun i => card_inf_block D.c (D.block_T i)
    hyp_inf := fun i => hypS_inf_line D.c hp (by omega) (D.block_T i)
    hyp_sup := fun i => hypS_sup_line D.c hp (by omega) (D.block_T i)
    refl := reflT D.c
    refl_fix := fun i x hx => reflT_fix D.c hx
    refl_inv := fun i x hx => reflT_inv D.c ((D.block_T i x).1 hx)
    weyl_card := card_closure_reflT_le D.c (by omega)
    gen := fun J hJ hcl => D.gen_aux hp hp5 J hJ hcl }

include D in
theorem exists_rootData (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ R : RootData p T, Nonempty (R.ReflData 48) :=
  ⟨D.rootData hp hp5, ⟨D.reflData hp hp5⟩⟩

end B3Data

end Data

end CFSG.RankThree.PartOne.KFR4
