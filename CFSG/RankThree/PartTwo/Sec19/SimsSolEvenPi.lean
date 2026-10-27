module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCfg
public import CFSG.HardMathSupport.RichardWeiss.Proving.HeartCohomology

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.HardMathSupport.RichardWeiss.Proving
  Equiv Equiv.Perm
open scoped commutatorElement

@[instance_reducible] private def permBarAddCommGroup (n : ℕ) : AddCommGroup (permBar n) :=
  { (inferInstance : AddGroup (permBar n)) with
    add_comm := fun x y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm] }

section Bar

variable {n : ℕ}

theorem permBar_add_self (v : permBar n) : v + v = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [← QuotientAddGroup.mk_add]
  have h : x + x = 0 := by
    funext i
    exact (show ∀ c : ZMod 2, c + c = 0 by decide) (x i)
  rw [h]
  rfl

theorem permBar_neg_eq (v : permBar n) : -v = v :=
  neg_eq_of_add_eq_zero_right (permBar_add_self v)

theorem permBar_sub_eq_add (u v : permBar n) : u - v = u + v := by
  rw [sub_eq_add_neg, permBar_neg_eq]

theorem vecPerm_single (σ : Perm (Fin n)) (a : Fin n) :
    vecPerm σ (Pi.single a (1 : ZMod 2)) = Pi.single (σ a) 1 := by
  funext i
  rw [vecPerm_apply, Pi.single_apply, Pi.single_apply]
  simp only [Perm.inv_eq_iff_eq]

theorem barAct_single (σ : Perm (Fin n)) (a : Fin n) :
    barAct σ ((Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) : permBar n) =
      ((Pi.single (σ a) (1 : ZMod 2) : Fin n → ZMod 2) : permBar n) := by
  rw [barAct_mk, vecPerm_single]

theorem heartToBar_pairEW (a b : Fin n) :
    heartToBar (pairEW a b : altHeart n) =
      ((Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) : permBar n) +
        ((Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) : permBar n) := by
  rw [heartToBar_mk, ← QuotientAddGroup.mk_add]
  congr 1
  funext p
  rw [pairEW_apply, Pi.add_apply, Pi.single_apply, Pi.single_apply]

private theorem zmod2_aux1 : ∀ p q c : ZMod 2, -p + q = c → p = q + c := by decide

private theorem zmod2_aux2 : ∀ p c : ZMod 2, p = p + c + c + c → c = 0 := by decide

theorem exists_forall_eq_of_mem_zmultiples {z : Fin n → ZMod 2}
    (hz : z ∈ AddSubgroup.zmultiples (allOnes n)) : ∃ c : ZMod 2, ∀ i, z i = c := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
  exact ⟨(k : ZMod 2), fun i => by rw [← hk]; simp [allOnes]⟩

theorem exists_threeCycle_apply_eq (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ σ : Perm (Fin n), σ.IsThreeCycle ∧ σ j = i := by
  obtain ⟨k, hki, hkj⟩ := exists_ne_pair_heart hn i j
  refine ⟨swap j k * swap j i, isThreeCycle_swap_mul_swap_same hkj.symm hij.symm hki, ?_⟩
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hij (Ne.symm hki)]

theorem permBar_fixed_eq_zero (hn : 3 ≤ n) (d : permBar n)
    (hd : ∀ σ ∈ alternatingGroup (Fin n), barAct σ d = d) : d = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective d
  have hσ : ∀ σ ∈ alternatingGroup (Fin n), ∃ c : ZMod 2, ∀ i, x (σ⁻¹ i) = x i + c := by
    intro σ hσ
    have h := hd σ hσ
    rw [barAct_mk, QuotientAddGroup.eq] at h
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_zmultiples h
    refine ⟨c, fun i => ?_⟩
    have := hc i
    simp only [Pi.add_apply, Pi.neg_apply, vecPerm_apply] at this
    exact zmod2_aux1 _ _ _ this
  have h3 : ∀ σ : Perm (Fin n), σ.IsThreeCycle → ∀ i, x (σ⁻¹ i) = x i := by
    intro σ hσ3 i
    obtain ⟨c, hc⟩ := hσ σ (mem_alternatingGroup.2 hσ3.sign)
    have hpow : σ⁻¹ * σ⁻¹ * σ⁻¹ = 1 := by
      have h1 : σ ^ 3 = 1 := by
        rw [← hσ3.orderOf]
        exact pow_orderOf_eq_one σ
      have h2 : σ⁻¹ ^ 3 = 1 := by rw [inv_pow, h1, inv_one]
      simpa [pow_succ] using h2
    have e3 : σ⁻¹ (σ⁻¹ (σ⁻¹ i)) = i := by
      have := congrArg (fun p : Perm (Fin n) => p i) hpow
      simpa [Perm.mul_apply] using this
    have h4 : x i = x i + c + c + c := by
      calc x i = x (σ⁻¹ (σ⁻¹ (σ⁻¹ i))) := by rw [e3]
        _ = x i + c + c + c := by rw [hc, hc, hc]
    have hc0 : c = 0 := zmod2_aux2 _ _ h4
    rw [hc, hc0, add_zero]
  have hconst : ∀ i j, x i = x j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨σ, hσ3, hσj⟩ := exists_threeCycle_apply_eq hn hij
    have := h3 σ hσ3 i
    rw [show σ⁻¹ i = j by rw [Perm.inv_eq_iff_eq, hσj]] at this
    exact this.symm
  have hi0 : 0 < n := by omega
  rw [QuotientAddGroup.eq_zero_iff, mem_zmultiples_allOnes_iff]
  rcases zmod_two_cases' (x ⟨0, hi0⟩) with h | h
  · left
    funext i
    rw [hconst i ⟨0, hi0⟩, h]
    rfl
  · right
    funext i
    rw [hconst i ⟨0, hi0⟩, h]
    rfl

end Bar

open CFSG.CGT.PushingUpLit.SolK (commutator_inv' commutator_mul_right conj_eq_commutator_mul
  commutator_eq_one_of_comm isPGroup_pCoreOf' isPGroup_of_le mem_map_subtype_iff pCoreOf_eq_map)

theorem hom_eq_one_of_isShort {G : Type*} [Group G] {L : Subgroup G} (hL : IsShort L)
    {B : Type*} [Group B] (hB : IsPGroup 2 B) (f : ↥L →* B) : f = 1 := by
  have hq : IsPGroup 2 (↥L ⧸ f.ker) :=
    (hB.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk : f.ker = ⊤ := hL.eq_twoResidual f.ker hq
  ext l
  have : l ∈ f.ker := by rw [hk]; exact Subgroup.mem_top l
  simpa using this

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

include C in
theorem six_le : 6 ≤ n := by
  rcases C.S.n_mem with h | h | h <;> omega

include C in
theorem even_n : Even n := by
  rcases C.S.n_mem with h | h | h
  · exact ⟨3, by omega⟩
  · exact ⟨4, by omega⟩
  · exact ⟨5, by omega⟩

theorem θ_K (k : ↥C.K) : C.θ ⟨(k : G), C.K_le k.2⟩ = 1 := (C.mem_K.1 k.2).choose_spec

theorem β_conj_K (k : ↥C.K) (u v : ↥(blockU X)) (h : (v : G) = (k : G) * (u : G) * (k : G)⁻¹) :
    Multiplicative.toAdd (C.β v) = Multiplicative.toAdd (C.β u) := by
  have := C.θ_spec ⟨(k : G), C.K_le k.2⟩ u v h
  rwa [C.θ_K k, altAct_one] at this

theorem β_conj_X (x : ↥X) (u v : ↥(blockU X)) (h : (v : G) = (x : G) * (u : G) * (x : G)⁻¹) :
    Multiplicative.toAdd (C.β v) =
      altAct (C.α x : Perm (Fin n)) (Multiplicative.toAdd (C.β u)) := by
  have := C.θ_spec ⟨(x : G), C.S.le x.2⟩ u v h
  rwa [C.θ_X x] at this

theorem α_eq_one_iff (x : ↥X) : C.α x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 X := by
  rw [← MonoidHom.mem_ker, C.α_ker, pCoreOf_eq_map, mem_map_subtype_iff]

theorem blockU_le_K : blockU X ≤ C.K := by
  intro u hu
  have huX : u ∈ X := blockU_le_self X hu
  rw [C.mem_K]
  refine ⟨C.S.le huX, ?_⟩
  rw [C.θ_X ⟨u, huX⟩, (C.α_eq_one_iff ⟨u, huX⟩).2 (C.S.W_le_Y hu)]
  rfl

theorem comm_mem_Y (k : ↥C.K) {x : G} (hx : x ∈ X) :
    ⁅(k : G), x⁆ ∈ CFSG.Open.pCoreOf 2 X := by
  have hkM : (k : G) ∈ M := C.K_le k.2
  have hy : (k : G) * x * (k : G)⁻¹ ∈ X := C.S.normal hkM hx
  have hθ : C.α ⟨(k : G) * x * (k : G)⁻¹, hy⟩ = C.α ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [← C.θ_X, ← C.θ_X]
    have e : (⟨(k : G) * x * (k : G)⁻¹, C.S.le hy⟩ : ↥M) =
        ⟨(k : G), hkM⟩ * ⟨x, C.S.le hx⟩ * ⟨(k : G), hkM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, C.θ_K k]
    simp
  have h1 : C.α (⟨(k : G) * x * (k : G)⁻¹, hy⟩ * (⟨x, hx⟩ : ↥X)⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ, mul_inv_cancel]
  have h2 := (C.α_eq_one_iff _).1 h1
  simpa [commutatorElement_def] using h2

theorem comm_mem_W (k : ↥C.K) {x : G} (hx : x ∈ X) : ⁅(k : G), x⁆ ∈ blockU X := by
  classical
  have hX : IsShort X := C.S.block.1
  have hWc : ∀ w ∈ blockU X, ∀ y ∈ CFSG.Open.pCoreOf 2 X, w * y = y * w := fun w hw y hy =>
    (Subgroup.mem_centralizer_iff.1 (hX.blockU_le_center hw).2 y hy).symm
  have hnorm : ((blockU X).subgroupOf (CFSG.Open.pCoreOf 2 X)).Normal := ⟨fun w hw g => by
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have h1 : (g : G) * (w : G) * (g : G)⁻¹ = (w : G) := by
      rw [← hWc _ hw _ g.2]
      group
    show (g : G) * (w : G) * (g : G)⁻¹ ∈ blockU X
    rw [h1]
    exact hw⟩
  have hq2 : IsPGroup 2
      (↥(CFSG.Open.pCoreOf 2 X) ⧸ (blockU X).subgroupOf (CFSG.Open.pCoreOf 2 X)) :=
    (isPGroup_pCoreOf' X).to_quotient _
  have hY : ∀ x' : ↥X, ⁅(k : G), (x' : G)⁆ ∈ CFSG.Open.pCoreOf 2 X := fun x' =>
    C.comm_mem_Y k x'.2
  let f : ↥X →* (↥(CFSG.Open.pCoreOf 2 X) ⧸ (blockU X).subgroupOf (CFSG.Open.pCoreOf 2 X)) :=
    { toFun := fun x' => QuotientGroup.mk ⟨⁅(k : G), (x' : G)⁆, hY x'⟩
      map_one' := by
        have : (⟨⁅(k : G), ((1 : ↥X) : G)⁆, hY 1⟩ : ↥(CFSG.Open.pCoreOf 2 X)) = 1 :=
          Subtype.ext (by simp)
        rw [this]
        exact QuotientGroup.mk_one _
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        set y : G := ⁅(k : G), (b : G)⁆ with hy
        have hyY : y ∈ CFSG.Open.pCoreOf 2 X := hY b
        have hxy : ⁅(a : G), y⁆ ∈ blockU X := by
          rw [← commutator_inv']
          refine (blockU X).inv_mem ?_
          exact Subgroup.commutator_mem_commutator hyY a.2
        have hcalc : (⁅(k : G), (a : G)⁆ * ⁅(k : G), (b : G)⁆)⁻¹ *
            ⁅(k : G), ((a * b : ↥X) : G)⁆ = ⁅(a : G), y⁆ := by
          have e1 : ⁅(k : G), ((a * b : ↥X) : G)⁆ =
              ⁅(k : G), (a : G)⁆ * ((a : G) * y * (a : G)⁻¹) := by
            rw [Subgroup.coe_mul, CFSG.CGT.PushingUpLit.SolK.commutator_mul_right]
          have e2 : (a : G) * y * (a : G)⁻¹ = ⁅(a : G), y⁆ * y := conj_eq_commutator_mul _ _
          rw [e1, e2]
          have hc := hWc _ hxy _ hyY
          calc (⁅(k : G), (a : G)⁆ * y)⁻¹ * (⁅(k : G), (a : G)⁆ * (⁅(a : G), y⁆ * y))
              = y⁻¹ * (⁅(a : G), y⁆ * y) := by group
            _ = ⁅(a : G), y⁆ := by rw [hc]; group
        have hmem : (⁅(k : G), (a : G)⁆ * ⁅(k : G), (b : G)⁆)⁻¹ *
            ⁅(k : G), ((a * b : ↥X) : G)⁆ ∈ blockU X := by
          rw [hcalc]
          exact hxy
        have hmem' := (blockU X).inv_mem hmem
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at hmem' ⊢
        exact hmem' }
  have h1 := hom_eq_one_of_isShort hX hq2 f
  have h2 : f ⟨x, hx⟩ = 1 := DFunLike.congr_fun h1 ⟨x, hx⟩
  have h3 : (⟨⁅(k : G), x⁆, hY ⟨x, hx⟩⟩ : ↥(CFSG.Open.pCoreOf 2 X)) ∈
      (blockU X).subgroupOf (CFSG.Open.pCoreOf 2 X) := (QuotientGroup.eq_one_iff _).1 h2
  exact h3

@[expose] noncomputable def cobound (k : ↥C.K) (x : ↥X) : altHeart n :=
  Multiplicative.toAdd (C.β ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩)

theorem toAdd_β_eq_cobound (k : ↥C.K) (x : ↥X) (u : ↥(blockU X))
    (hu : (u : G) = ⁅(k : G), (x : G)⁆) : Multiplicative.toAdd (C.β u) = C.cobound k x := by
  have : u = ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ := Subtype.ext hu
  rw [this]
  rfl

theorem cobound_mul (k : ↥C.K) (x y : ↥X) :
    C.cobound k (x * y) = C.cobound k x + altAct (C.α x : Perm (Fin n)) (C.cobound k y) := by
  have hxM : (x : G) ∈ M := C.S.le x.2
  have h1 : ⁅(k : G), ((x * y : ↥X) : G)⁆ =
      ⁅(k : G), (x : G)⁆ * ((x : G) * ⁅(k : G), (y : G)⁆ * (x : G)⁻¹) := by
    rw [Subgroup.coe_mul, CFSG.CGT.PushingUpLit.SolK.commutator_mul_right]
  have hW2 : (x : G) * ⁅(k : G), (y : G)⁆ * (x : G)⁻¹ ∈ blockU X :=
    C.S.W_normalized hxM (C.comm_mem_W k y.2)
  have h2 : (⟨⁅(k : G), ((x * y : ↥X) : G)⁆, C.comm_mem_W k (x * y).2⟩ : ↥(blockU X)) =
      ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ *
        ⟨(x : G) * ⁅(k : G), (y : G)⁆ * (x : G)⁻¹, hW2⟩ := Subtype.ext h1
  unfold cobound
  rw [h2, map_mul, toAdd_mul]
  congr 1
  exact C.β_conj_X x ⟨⁅(k : G), (y : G)⁆, C.comm_mem_W k y.2⟩ ⟨_, hW2⟩ rfl

theorem cobound_of_mem_W (k : ↥C.K) (w : ↥X) (hw : (w : G) ∈ blockU X) : C.cobound k w = 0 := by
  have hkM : (k : G) ∈ M := C.K_le k.2
  have hk : (k : G) * (w : G) * (k : G)⁻¹ ∈ blockU X := C.S.W_normalized hkM hw
  have h2 : (⟨⁅(k : G), (w : G)⁆, C.comm_mem_W k w.2⟩ : ↥(blockU X)) =
      ⟨(k : G) * (w : G) * (k : G)⁻¹, hk⟩ * (⟨(w : G), hw⟩ : ↥(blockU X))⁻¹ := Subtype.ext rfl
  unfold cobound
  rw [h2, map_mul, map_inv, toAdd_mul, toAdd_inv, C.β_conj_K k ⟨(w : G), hw⟩ ⟨_, hk⟩ rfl]
  exact add_neg_cancel _

theorem cobound_of_α_eq_one (k : ↥C.K) (y : ↥X) (hy : C.α y = 1) : C.cobound k y = 0 := by
  have hyY : (y : G) ∈ CFSG.Open.pCoreOf 2 X := (C.α_eq_one_iff y).1 hy
  have hfix : ∀ x : ↥X, altAct (C.α x : Perm (Fin n)) (C.cobound k y) = C.cobound k y := by
    intro x
    have hyx : C.α (x * y * x⁻¹) = 1 := by
      rw [map_mul, map_mul, hy, mul_one, map_inv, mul_inv_cancel]
    have e1 := C.cobound_mul k x y
    have e2 := C.cobound_mul k (x * y * x⁻¹) x
    rw [hyx, mul_assoc (x * y), inv_mul_cancel, mul_one] at e2
    simp only [Subgroup.coe_one, altAct_one] at e2
    have e3 := C.cobound_mul k ⁅x, y⁆ y
    have hcomm : ((⁅x, y⁆ : ↥X) : G) ∈ blockU X := by
      have : ((⁅x, y⁆ : ↥X) : G) = ⁅(x : G), (y : G)⁆ := rfl
      rw [this, ← commutator_inv']
      exact (blockU X).inv_mem (Subgroup.commutator_mem_commutator hyY x.2)
    have hα1 : C.α ⁅x, y⁆ = 1 := (C.α_eq_one_iff _).2 (C.S.W_le_Y hcomm)
    rw [C.cobound_of_mem_W k _ hcomm, hα1] at e3
    simp only [Subgroup.coe_one, altAct_one, zero_add] at e3
    have e4 : ⁅x, y⁆ * y = x * y * x⁻¹ := (conj_eq_commutator_mul x y).symm
    rw [e4] at e3
    have e5 : C.cobound k x + altAct (C.α x : Perm (Fin n)) (C.cobound k y) =
        C.cobound k (x * y * x⁻¹) + C.cobound k x := by rw [← e1, ← e2]
    rw [e3] at e5
    exact add_left_cancel (a := C.cobound k x) (by rw [e5, add_comm])
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (C.cobound k y)
  rw [← hz]
  refine altHeart_fixed_eq_zero (by have := C.six_le; omega) z fun σ hσ => ?_
  obtain ⟨x, hx⟩ := C.α_surj ⟨σ, hσ⟩
  have hxσ : (C.α x : Perm (Fin n)) = σ := congrArg Subtype.val hx
  have := hfix x
  rw [← hz, hxσ, altAct_mk] at this
  exact this

theorem cobound_eq_of_α_eq (k : ↥C.K) {x x' : ↥X} (h : C.α x = C.α x') :
    C.cobound k x = C.cobound k x' := by
  have hy : C.α (x⁻¹ * x') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have := C.cobound_mul k x (x⁻¹ * x')
  rw [mul_inv_cancel_left, C.cobound_of_α_eq_one k _ hy, map_zero, add_zero] at this
  exact this.symm

theorem exists_cocycle (k : ↥C.K) :
    ∃ f : alternatingGroup (Fin n) → altHeart n,
      (∀ x : ↥X, f (C.α x) = C.cobound k x) ∧
      ∀ g h, f (g * h) = f g + altAct (g : Perm (Fin n)) (f h) := by
  classical
  have hfx : ∀ x : ↥X, C.cobound k (Function.surjInv C.α_surj (C.α x)) = C.cobound k x :=
    fun x => C.cobound_eq_of_α_eq k (Function.surjInv_eq C.α_surj (C.α x))
  refine ⟨fun g => C.cobound k (Function.surjInv C.α_surj g), hfx, fun g h => ?_⟩
  obtain ⟨x, rfl⟩ := C.α_surj g
  obtain ⟨y, rfl⟩ := C.α_surj h
  show C.cobound k (Function.surjInv C.α_surj (C.α x * C.α y)) =
    C.cobound k (Function.surjInv C.α_surj (C.α x)) +
      altAct (C.α x : Perm (Fin n)) (C.cobound k (Function.surjInv C.α_surj (C.α y)))
  rw [← map_mul, hfx, hfx, hfx, C.cobound_mul]

@[expose] def IsPi (k : ↥C.K) (v : permBar n) : Prop :=
  ∀ (x : ↥X) (u : ↥(blockU X)), (u : G) = (k : G) * (x : G) * (k : G)⁻¹ * (x : G)⁻¹ →
    heartToBar (Multiplicative.toAdd (C.β u)) = v - barAct (C.α x : Perm (Fin n)) v

variable {C}

theorem IsPi.unique {k : ↥C.K} {v v' : permBar n} (h : C.IsPi k v) (h' : C.IsPi k v') : v = v' := by
  have hd : ∀ σ ∈ alternatingGroup (Fin n), barAct σ (v - v') = v - v' := by
    intro σ hσ
    obtain ⟨x, hx⟩ := C.α_surj ⟨σ, hσ⟩
    have hxσ : (C.α x : Perm (Fin n)) = σ := congrArg Subtype.val hx
    have e1 := h x ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ rfl
    have e2 := h' x ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ rfl
    rw [hxσ] at e1 e2
    have h0 : (v - v') - barAct σ (v - v') = 0 := by
      rw [map_sub]
      calc (v - v') - (barAct σ v - barAct σ v') = (v - barAct σ v) - (v' - barAct σ v') := by
            letI := permBarAddCommGroup n
            abel
        _ = 0 := by rw [← e1, ← e2]; exact sub_self _
    exact (sub_eq_zero.1 h0).symm
  exact sub_eq_zero.1 (permBar_fixed_eq_zero (by have := C.six_le; omega) _ hd)

theorem IsPi.one : C.IsPi 1 0 := by
  intro x u hu
  have h1 : u = 1 := by
    apply Subtype.ext
    rw [hu]
    simp
  rw [h1, map_one, toAdd_one, map_zero, map_zero, sub_zero]

theorem IsPi.mul {k k' : ↥C.K} {v v' : permBar n} (h : C.IsPi k v) (h' : C.IsPi k' v') :
    C.IsPi (k * k') (v + v') := by
  intro x u hu
  have hkM : (k : G) ∈ M := C.K_le k.2
  have hu₁ : ⁅(k : G), (x : G)⁆ ∈ blockU X := C.comm_mem_W k x.2
  have hu₂ : ⁅(k' : G), (x : G)⁆ ∈ blockU X := C.comm_mem_W k' x.2
  have hu₂' : (k : G) * ⁅(k' : G), (x : G)⁆ * (k : G)⁻¹ ∈ blockU X :=
    C.S.W_normalized hkM hu₂
  have e : (u : G) = ((k : G) * ⁅(k' : G), (x : G)⁆ * (k : G)⁻¹) * ⁅(k : G), (x : G)⁆ := by
    rw [hu, Subgroup.coe_mul]
    simp only [commutatorElement_def]
    group
  have e' : u = ⟨_, hu₂'⟩ * ⟨_, hu₁⟩ := Subtype.ext e
  rw [e', map_mul, toAdd_mul, C.β_conj_K k ⟨_, hu₂⟩ ⟨_, hu₂'⟩ rfl, map_add, h' x ⟨_, hu₂⟩ rfl,
    h x ⟨_, hu₁⟩ rfl, map_add]
  letI := permBarAddCommGroup n
  abel

theorem IsPi.of_centralizes {k : ↥C.K} (hk : (k : G) ∈ Subgroup.centralizer (X : Set G)) :
    C.IsPi k 0 := by
  intro x u hu
  have hxk : (x : G) * (k : G) = (k : G) * (x : G) :=
    Subgroup.mem_centralizer_iff.1 hk (x : G) x.2
  have h2 : (k : G) * (x : G) * (k : G)⁻¹ * (x : G)⁻¹ = 1 :=
    commutator_eq_one_of_comm hxk.symm
  have h1 : u = 1 := Subtype.ext (hu.trans h2)
  rw [h1, map_one, toAdd_one, map_zero, map_zero, sub_zero]

theorem IsPi.conj {k k' : ↥C.K} {v : permBar n} (m : ↥M)
    (hk' : (k' : G) = (m : G) * (k : G) * (m : G)⁻¹) (h : C.IsPi k v) :
    C.IsPi k' (barAct (C.θ m) v) := by
  intro x u hu
  have hmx : (m : G)⁻¹ * (x : G) * (m : G) ∈ X := by
    have := C.S.normal (M.inv_mem m.2) x.2
    simpa using this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥X, (x₀ : G) = (m : G)⁻¹ * (x : G) * (m : G) := ⟨⟨_, hmx⟩, rfl⟩
  have hu₀ : ⁅(k : G), (x₀ : G)⁆ ∈ blockU X := C.comm_mem_W k x₀.2
  have hu_eq : (u : G) = (m : G) * ⁅(k : G), (x₀ : G)⁆ * (m : G)⁻¹ := by
    rw [hu, hk', hx₀]
    simp only [commutatorElement_def]
    group
  have e1 := C.θ_spec m ⟨⁅(k : G), (x₀ : G)⁆, hu₀⟩ u hu_eq
  have e2 := h x₀ ⟨⁅(k : G), (x₀ : G)⁆, hu₀⟩ rfl
  have hperm : C.θ m * (C.α x₀ : Perm (Fin n)) = (C.α x : Perm (Fin n)) * C.θ m := by
    rw [← C.θ_X x₀, ← C.θ_X x, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (m : G) * (x₀ : G) = (x : G) * (m : G)
    rw [hx₀]
    group
  have e3 : barAct (C.θ m) (barAct (C.α x₀ : Perm (Fin n)) v) =
      barAct (C.α x : Perm (Fin n)) (barAct (C.θ m) v) := by
    rw [← barAct_mul, ← barAct_mul, hperm]
  rw [e1, heartToBar_altAct, e2, map_sub, e3]

theorem IsPi.of_blockU (k : ↥C.K) (u : ↥(blockU X)) (h : (k : G) = u) :
    C.IsPi k (heartToBar (Multiplicative.toAdd (C.β u))) := by
  intro x u' hu'
  have hxM : (x : G) ∈ M := C.S.le x.2
  have hxu : (x : G) * (u : G) * (x : G)⁻¹ ∈ blockU X := C.S.W_normalized hxM u.2
  have e : u' = u * (⟨(x : G) * (u : G) * (x : G)⁻¹, hxu⟩ : ↥(blockU X))⁻¹ := by
    apply Subtype.ext
    rw [hu', h]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, C.β_conj_X x u ⟨_, hxu⟩ rfl, map_add, map_neg,
    heartToBar_altAct, sub_eq_add_neg]

theorem exists_isPi (hn : 6 ≤ n) (hev : Even n) (k : ↥C.K) : ∃ v, C.IsPi k v := by
  classical
  obtain ⟨f, hfα, hf⟩ := C.exists_cocycle k
  have hn0 : 0 < n := by omega
  obtain ⟨w, b, hfw⟩ := cocycle_heart_decomp hn hev ⟨0, hn0⟩ f hf
  refine ⟨(if b then (((Pi.single (⟨0, hn0⟩ : Fin n) (1 : ZMod 2) : Fin n → ZMod 2)) :
    permBar n) else 0) + heartToBar w, ?_⟩
  intro x u hu
  rw [C.toAdd_β_eq_cobound k x u hu, ← hfα x, hfw (C.α x)]
  cases b
  · simp only [Bool.false_eq_true, if_false, zero_add, map_sub, heartToBar_altAct,
      permBar_sub_eq_add]
    letI := permBarAddCommGroup n
    abel
  · simp only [if_true, map_add, map_sub, heartToBar_altAct, heartToBar_pairEW, barAct_single,
      permBar_sub_eq_add]
    letI := permBarAddCommGroup n
    abel

theorem centralizes_of_isPi_zero {k : ↥C.K} (h : C.IsPi k 0) :
    (k : G) ∈ Subgroup.centralizer (X : Set G) := by
  have hX : IsShort X := C.S.block.1
  have hZ : ∀ x : ↥X, ⁅(k : G), (x : G)⁆ ∈ blockZ X := by
    intro x
    have e := h x ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ rfl
    rw [map_zero, sub_zero] at e
    have e1 : Multiplicative.toAdd (C.β ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩) = 0 :=
      heartToBar_injective (e.trans (map_zero heartToBar).symm)
    have e2 : C.β ⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ = 1 :=
      Multiplicative.toAdd.injective (e1.trans toAdd_one.symm)
    have e3 : (⟨⁅(k : G), (x : G)⁆, C.comm_mem_W k x.2⟩ : ↥(blockU X)) ∈ C.β.ker := e2
    rw [C.β_ker, Subgroup.mem_subgroupOf] at e3
    exact e3
  have hZ2 : IsPGroup 2 ↥(blockZ X) :=
    isPGroup_of_le (isPGroup_pCoreOf' X) (inf_le_left.trans C.S.W_le_Y)
  let f : ↥X →* ↥(blockZ X) :=
    { toFun := fun x => ⟨⁅(k : G), (x : G)⁆, hZ x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hZb : ⁅(k : G), (b : G)⁆ ∈ blockU X ⊓ Subgroup.centralizer (X : Set G) := hZ b
        have hc : (a : G) * ⁅(k : G), (b : G)⁆ = ⁅(k : G), (b : G)⁆ * (a : G) :=
          Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hZb).2 (a : G) a.2
        show ⁅(k : G), ((a * b : ↥X) : G)⁆ = ⁅(k : G), (a : G)⁆ * ⁅(k : G), (b : G)⁆
        rw [Subgroup.coe_mul, CFSG.CGT.PushingUpLit.SolK.commutator_mul_right, hc, mul_inv_cancel_right] }
  have h1 := hom_eq_one_of_isShort hX hZ2 f
  refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
  have h2 : f ⟨x, hx⟩ = 1 := DFunLike.congr_fun h1 ⟨x, hx⟩
  have h3 : ⁅(k : G), x⁆ = 1 := congrArg Subtype.val h2
  exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm

variable (C)

theorem exists_piData (hn : 6 ≤ n) (hev : Even n) : Nonempty C.PiData := by
  classical
  choose p hp using C.exists_isPi hn hev
  have hp1 : p 1 = 0 := (hp 1).unique IsPi.one
  have hpm : ∀ k k', p (k * k') = p k + p k' := fun k k' =>
    (hp (k * k')).unique ((hp k).mul (hp k'))
  refine ⟨{ π := { toFun := fun k => Multiplicative.ofAdd (p k)
                   map_one' := by rw [hp1]; rfl
                   map_mul' := fun k k' => by rw [hpm]; rfl }
            comm_mem := fun k x hx => C.comm_mem_W k hx
            spec := fun k x u hu => hp k x u hu
            ker := fun k => ⟨fun h => ?_, fun h => ?_⟩
            equivar := fun m k k' hk' => (hp k').unique ((hp k).conj m hk') }⟩
  · have h0 : p k = 0 := congrArg Multiplicative.toAdd h
    have := hp k
    rw [h0] at this
    exact centralizes_of_isPi_zero this
  · have h0 : p k = 0 := (hp k).unique (IsPi.of_centralizes h)
    show Multiplicative.ofAdd (p k) = 1
    rw [h0]
    rfl

variable {C}

theorem PiData.π_W (D : C.PiData) (k : ↥C.K) (u : ↥(blockU X)) (h : (k : G) = u) :
    Multiplicative.toAdd (D.π k) = heartToBar (Multiplicative.toAdd (C.β u)) :=
  IsPi.unique (fun x u' hu' => D.spec k x u' hu') (IsPi.of_blockU k u h)

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
