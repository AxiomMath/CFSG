module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod
import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.GroupTheory.SuzukiTwoGroupsQuadratic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.H13.NFa2
open CFSG.GroupTheory.SuzukiTwoGroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X N₀ N₁ : Subgroup G} {W W₀ : Type}
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W₀] [Module (ZMod 2) W₀]

theorem SecRep.normal_subgroupOf (s : SecRep X N₀ N₁ W) : (N₀.subgroupOf N₁).Normal := by
  have h : N₀.subgroupOf N₁ = s.cls.ker := by
    refine Subgroup.ext fun n => ?_
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (s.ker n).symm
  rw [h]
  exact MonoidHom.normal_ker s.cls

noncomputable def SecRep.quotEquiv (s : SecRep X N₀ N₁ W) [(N₀.subgroupOf N₁).Normal] :
    ↥N₁ ⧸ N₀.subgroupOf N₁ ≃* Multiplicative W :=
  QuotientGroup.liftEquiv (N₀.subgroupOf N₁) s.surj (by
    refine Subgroup.ext fun n => ?_
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (s.ker n).symm)

theorem SecRep.quotEquiv_mk (s : SecRep X N₀ N₁ W) [(N₀.subgroupOf N₁).Normal] (n : ↥N₁) :
    SecRep.quotEquiv s (QuotientGroup.mk n) = s.cls n := by
  rw [SecRep.quotEquiv]
  exact QuotientGroup.liftEquiv_mk (N₀.subgroupOf N₁) s.surj _ n

noncomputable def SecRep.equivOfBot (s : SecRep X ⊥ N₁ W) : ↥N₁ ≃* Multiplicative W :=
  (QuotientGroup.quotientBot (G := ↥N₁)).symm.trans
    (QuotientGroup.liftEquiv (⊥ : Subgroup ↥N₁) s.surj (by
      refine Subgroup.ext fun n => ?_
      rw [Subgroup.mem_bot, MonoidHom.mem_ker]
      exact ⟨fun h => by rw [h, map_one], fun h =>
        Subtype.ext (by simpa using Subgroup.mem_bot.mp ((s.ker n).mp h))⟩))

theorem SecRep.equivOfBot_apply (s : SecRep X ⊥ N₁ W) (n : ↥N₁) :
    SecRep.equivOfBot s n = s.cls n := by
  rw [SecRep.equivOfBot, MulEquiv.trans_apply, QuotientGroup.quotientBot_symm_apply]
  exact QuotientGroup.liftEquiv_mk (⊥ : Subgroup ↥N₁) s.surj _ n

private def commElem (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (a b : ↥N₁) : ↥N₀ :=
  ⟨⁅(a : G), (b : G)⁆, hcomm a a.2 b b.2⟩

private theorem commElem_left (s : SecRep X N₀ N₁ W)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) {a a' b : ↥N₁}
    (ha : s.cl a = s.cl a') : commElem hcomm a b = commElem hcomm a' b := by
  apply Subtype.ext
  have hzN : ((a : G)⁻¹ * (a' : G)) ∈ N₀ := (s.cl_eq_iff a a').mp ha.symm
  have hza : (a' : G) = (a : G) * ((a : G)⁻¹ * (a' : G)) := by group
  have hz1 : ⁅((a : G)⁻¹ * (a' : G)), (b : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hc _ hzN (b : G) b.2)
  have h := commutatorElement_mul_left_of_commute (x := (a : G))
    (x' := (a : G)⁻¹ * (a' : G)) (y := (b : G)) (by rw [hz1]; simp)
  show ⁅(a : G), (b : G)⁆ = ⁅(a' : G), (b : G)⁆
  rw [hza, h, hz1, one_mul]

private theorem commElem_right (s : SecRep X N₀ N₁ W)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (a : ↥N₁) {b b' : ↥N₁}
    (hb : s.cl b = s.cl b') : commElem hcomm a b = commElem hcomm a b' := by
  apply Subtype.ext
  have hzN : ((b : G)⁻¹ * (b' : G)) ∈ N₀ := (s.cl_eq_iff b b').mp hb.symm
  have hzb : (b' : G) = (b : G) * ((b : G)⁻¹ * (b' : G)) := by group
  have hz1 : ⁅(a : G), ((b : G)⁻¹ * (b' : G))⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hc _ hzN (a : G) a.2).symm
  have h := commutatorElement_mul_right_of_commute (x := (a : G)) (y := (b : G))
    (y' := (b : G)⁻¹ * (b' : G)) (by rw [hz1]; simp)
  show ⁅(a : G), (b : G)⁆ = ⁅(a : G), (b' : G)⁆
  rw [hzb, h, hz1, one_mul]

private theorem commVal_mul_left (s₀ : SecRep X ⊥ N₀ W₀) (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (a a' b : ↥N₁) :
    s₀.cl (commElem hcomm (a * a') b) =
      s₀.cl (commElem hcomm a b) + s₀.cl (commElem hcomm a' b) := by
  have hcommute : Commute (a : G) ⁅(a' : G), (b : G)⁆ :=
    (hc ⁅(a' : G), (b : G)⁆ (hcomm a' a'.2 b b.2) (a : G) a.2).symm
  have h := commutatorElement_mul_left_of_commute (x := (a : G)) (x' := (a' : G))
    (y := (b : G)) hcommute
  have he : commElem hcomm (a * a') b = commElem hcomm a' b * commElem hcomm a b := by
    apply Subtype.ext
    simpa only [commElem, Subgroup.coe_mul] using h
  rw [he, SecRep.cl_mul, add_comm]

private theorem commVal_mul_right (s₀ : SecRep X ⊥ N₀ W₀) (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (a b b' : ↥N₁) :
    s₀.cl (commElem hcomm a (b * b')) =
      s₀.cl (commElem hcomm a b) + s₀.cl (commElem hcomm a b') := by
  have hmem : ((a : G) * (b : G) * (a : G)⁻¹) ∈ N₁ :=
    N₁.mul_mem (N₁.mul_mem a.2 b.2) (N₁.inv_mem a.2)
  have hcommute : Commute ((a : G) * (b : G) * (a : G)⁻¹) ⁅(a : G), (b' : G)⁆ :=
    (hc ⁅(a : G), (b' : G)⁆ (hcomm a a.2 b' b'.2) _ hmem).symm
  have h := commutatorElement_mul_right_of_commute (x := (a : G)) (y := (b : G))
    (y' := (b' : G)) hcommute
  have he : commElem hcomm a (b * b') = commElem hcomm a b' * commElem hcomm a b := by
    apply Subtype.ext
    simpa only [commElem, Subgroup.coe_mul] using h
  rw [he, SecRep.cl_mul, add_comm]

noncomputable def SecRep.commForm (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) :
    W →ₗ[ZMod 2] W →ₗ[ZMod 2] W₀ := by
  classical
  let f : W → W → W₀ := fun v w =>
    s₀.cl (commElem hcomm (s.exists_cl v).choose (s.exists_cl w).choose)
  have hadd_left : ∀ v v' w, f (v + v') w = f v w + f v' w := by
    intro v v' w
    let a : ↥N₁ := (s.exists_cl v).choose
    let a' : ↥N₁ := (s.exists_cl v').choose
    let b : ↥N₁ := (s.exists_cl w).choose
    have ha : s.cl a = v := (s.exists_cl v).choose_spec
    have ha' : s.cl a' = v' := (s.exists_cl v').choose_spec
    have hrep : s.cl (s.exists_cl (v + v')).choose = s.cl (a * a') := by
      rw [(s.exists_cl (v + v')).choose_spec, ← ha, ← ha', ← SecRep.cl_mul]
    have h1 : f (v + v') w = s₀.cl (commElem hcomm (a * a') b) := by
      change s₀.cl (commElem hcomm (s.exists_cl (v + v')).choose b) = _
      rw [commElem_left s hc hcomm hrep]
    have h2 : f v w + f v' w =
        s₀.cl (commElem hcomm a b) + s₀.cl (commElem hcomm a' b) := rfl
    rw [h1, h2, commVal_mul_left s₀ hc hcomm a a' b]
  have hadd_right : ∀ v w w', f v (w + w') = f v w + f v w' := by
    intro v w w'
    let a : ↥N₁ := (s.exists_cl v).choose
    let b : ↥N₁ := (s.exists_cl w).choose
    let b' : ↥N₁ := (s.exists_cl w').choose
    have hb : s.cl b = w := (s.exists_cl w).choose_spec
    have hb' : s.cl b' = w' := (s.exists_cl w').choose_spec
    have hrep : s.cl (s.exists_cl (w + w')).choose = s.cl (b * b') := by
      rw [(s.exists_cl (w + w')).choose_spec, ← hb, ← hb', ← SecRep.cl_mul]
    have h1 : f v (w + w') = s₀.cl (commElem hcomm a (b * b')) := by
      change s₀.cl (commElem hcomm a (s.exists_cl (w + w')).choose) = _
      rw [commElem_right s hc hcomm a hrep]
    have h2 : f v w + f v w' =
        s₀.cl (commElem hcomm a b) + s₀.cl (commElem hcomm a b') := rfl
    rw [h1, h2, commVal_mul_right s₀ hc hcomm a b b']
  have hzero_left : ∀ w, f 0 w = 0 := by
    intro w
    have h := hadd_left 0 0 w
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hzero_right : ∀ v, f v 0 = 0 := by
    intro v
    have h := hadd_right v 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hsmul_left : ∀ (c : ZMod 2) v w, f (c • v) w = c • f v w := by
    intro c v w
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    generalize c.val = k
    induction k with
    | zero => rw [zero_nsmul, zero_nsmul, hzero_left]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd_left, ih]
  have hsmul_right : ∀ (c : ZMod 2) v w, f v (c • w) = c • f v w := by
    intro c v w
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    generalize c.val = k
    induction k with
    | zero => rw [zero_nsmul, zero_nsmul, hzero_right]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd_right, ih]
  exact LinearMap.mk₂ (ZMod 2) f hadd_left hsmul_left hadd_right hsmul_right

theorem SecRep.commForm_cl (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (a b : ↥N₁) :
    SecRep.commForm s s₀ hc hcomm (s.cl a) (s.cl b) =
      s₀.cl ⟨⁅(a : G), (b : G)⁆, hcomm a a.2 b b.2⟩ := by
  rw [SecRep.commForm]
  change s₀.cl (commElem hcomm (s.exists_cl (s.cl a)).choose
    (s.exists_cl (s.cl b)).choose) = _
  rw [commElem_left s hc hcomm (s.exists_cl (s.cl a)).choose_spec]
  exact congrArg s₀.cl (commElem_right s hc hcomm a (s.exists_cl (s.cl b)).choose_spec)

theorem SecRep.commForm_ρ (h : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W)
    (s₀ : SecRep X ⊥ N₀ W₀) (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (x : ↥X) (v w : W) :
    SecRep.commForm s s₀ hc hcomm (s.ρ x v) (s.ρ x w) =
      s₀.ρ x (SecRep.commForm s s₀ hc hcomm v w) := by
  obtain ⟨a, ha⟩ := s.exists_cl v
  obtain ⟨b, hb⟩ := s.exists_cl w
  rw [← ha, ← hb]
  let a' : ↥N₁ := ⟨(x : G) * (a : G) * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.norm₁ x.2) (a : G)).mp a.2⟩
  let b' : ↥N₁ := ⟨(x : G) * (b : G) * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.norm₁ x.2) (b : G)).mp b.2⟩
  let c' : ↥N₀ := ⟨(x : G) * ⁅(a : G), (b : G)⁆ * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.norm₀ x.2) ⁅(a : G), (b : G)⁆).mp
      (hcomm a a.2 b b.2)⟩
  have hact : s.ρ x (s.cl a) = s.cl a' := s.act x a a' rfl
  have hact' : s.ρ x (s.cl b) = s.cl b' := s.act x b b' rfl
  have hact₀ : s₀.ρ x (s₀.cl (commElem hcomm a b)) = s₀.cl c' :=
    s₀.act x (commElem hcomm a b) c' rfl
  rw [hact, hact', SecRep.commForm_cl s s₀ hc hcomm a' b',
    SecRep.commForm_cl s s₀ hc hcomm a b]
  change s₀.cl (commElem hcomm a' b') = s₀.ρ x (s₀.cl (commElem hcomm a b))
  rw [hact₀]
  apply congrArg s₀.cl
  apply Subtype.ext
  show ⁅(x : G) * (a : G) * (x : G)⁻¹, (x : G) * (b : G) * (x : G)⁻¹⁆ =
    (x : G) * ⁅(a : G), (b : G)⁆ * (x : G)⁻¹
  simp only [commutatorElement_def]
  group

theorem SecRep.span_range_commForm (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (hgen : ⁅N₁, N₁⁆ = N₀) :
    Submodule.span (ZMod 2) (Set.range fun p : W × W =>
      SecRep.commForm s s₀ hc hcomm p.1 p.2) = ⊤ := by
  classical
  let T : Submodule (ZMod 2) W₀ :=
    Submodule.span (ZMod 2) (Set.range fun p : W × W =>
      SecRep.commForm s s₀ hc hcomm p.1 p.2)
  let S : Set ↥N₀ := Set.range fun p : ↥N₁ × ↥N₁ =>
    (⟨⁅(p.1 : G), (p.2 : G)⁆, hcomm p.1 p.1.2 p.2 p.2.2⟩ : ↥N₀)
  let R : Subgroup ↥N₀ :=
    { carrier := {n | s₀.cl n ∈ T}
      one_mem' := by
        change s₀.cl (1 : ↥N₀) ∈ T
        rw [show s₀.cl (1 : ↥N₀) = 0 from by
          change Multiplicative.toAdd (s₀.cls 1) = 0
          rw [map_one]
          rfl]
        exact T.zero_mem
      mul_mem' := by
        intro a b ha hb
        change s₀.cl (a * b) ∈ T
        rw [SecRep.cl_mul]
        exact T.add_mem ha hb
      inv_mem' := by
        intro a ha
        change s₀.cl a⁻¹ ∈ T
        rw [SecRep.cl_inv]
        exact T.neg_mem ha }
  have hSR : S ⊆ R := by
    rintro n ⟨⟨a, b⟩, rfl⟩
    change s₀.cl ⟨⁅(a : G), (b : G)⁆, hcomm a a.2 b b.2⟩ ∈ T
    rw [← SecRep.commForm_cl s s₀ hc hcomm a b]
    exact Submodule.mem_span_of_mem (Set.mem_range_self (s.cl a, s.cl b))
  have hgenK : ∀ K : Subgroup ↥N₀, S ⊆ K → ∀ n : ↥N₀, n ∈ K := by
    intro K hSK n
    let S_G : Set G := {g | ∃ a ∈ N₁, ∃ b ∈ N₁, ⁅a, b⁆ = g}
    have hmem : (n : G) ∈ Subgroup.closure S_G := by
      rw [← Subgroup.commutator_def, hgen]
      exact n.2
    have hle : S_G ⊆ (K.map N₀.subtype : Set G) := by
      rintro g ⟨a, ha, b, hb, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨⁅a, b⁆, hcomm a ha b hb⟩, ?_, rfl⟩
      exact hSK ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have hn : (n : G) ∈ K.map N₀.subtype := (Subgroup.mem_closure.mp hmem) _ hle
    obtain ⟨m, hmK, hmn⟩ := Subgroup.mem_map.mp hn
    have hmn' : m = n := Subtype.ext hmn
    rwa [hmn'] at hmK
  have hclosure : Subgroup.closure S ≤ R := (Subgroup.closure_le R).mpr hSR
  have htop : R = ⊤ := by
    rw [eq_top_iff]
    intro n _
    exact hclosure (Subgroup.mem_closure.mpr fun K hK => hgenK K hK n)
  rw [show Submodule.span (ZMod 2) (Set.range fun p : W × W =>
      SecRep.commForm s s₀ hc hcomm p.1 p.2) = T from rfl]
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, hn⟩ := s₀.surj (Multiplicative.ofAdd w)
  have hcl : s₀.cl n = w := by
    have := congrArg Multiplicative.toAdd hn
    simpa [SecRep.cl] using this
  have hnR : n ∈ R := by rw [htop]; exact Subgroup.mem_top n
  change s₀.cl n ∈ T at hnR
  rwa [hcl] at hnR

private theorem sqVal_eq (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hsq : ∀ a ∈ N₁, a ^ 2 ∈ N₀) (h2 : ∀ z ∈ N₀, z ^ 2 = 1) {a a' : ↥N₁}
    (ha : s.cl a = s.cl a') :
    s₀.cl ⟨(a : G) ^ 2, hsq a a.2⟩ = s₀.cl ⟨(a' : G) ^ 2, hsq a' a'.2⟩ := by
  have hzN : ((a : G)⁻¹ * (a' : G)) ∈ N₀ := by
    simpa using (s.cl_eq_iff a a').mp ha.symm
  have hza : (a' : G) = (a : G) * ((a : G)⁻¹ * (a' : G)) := by group
  have hz2 : ((a : G)⁻¹ * (a' : G)) ^ 2 = 1 := h2 _ hzN
  have hzc : Commute (a : G) ((a : G)⁻¹ * (a' : G)) :=
    (hc _ hzN (a : G) a.2).symm
  have helem : (⟨(a : G) ^ 2, hsq a a.2⟩ : ↥N₀) =
      ⟨(a' : G) ^ 2, hsq a' a'.2⟩ := by
    apply Subtype.ext
    change (a : G) ^ 2 = (a' : G) ^ 2
    rw [hza, hzc.mul_pow, hz2, mul_one]
  exact congrArg s₀.cl helem

noncomputable def SecRep.sqMap (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hsq : ∀ a ∈ N₁, a ^ 2 ∈ N₀) (h2 : ∀ z ∈ N₀, z ^ 2 = 1) :
    W → W₀ :=
  fun v => s₀.cl ⟨((s.exists_cl v).choose : G) ^ 2,
    hsq ((s.exists_cl v).choose) ((s.exists_cl v).choose).2⟩

theorem SecRep.sqMap_cl (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hsq : ∀ a ∈ N₁, a ^ 2 ∈ N₀) (h2 : ∀ z ∈ N₀, z ^ 2 = 1) (a : ↥N₁) :
    SecRep.sqMap s s₀ hc hsq h2 (s.cl a) = s₀.cl ⟨(a : G) ^ 2, hsq a a.2⟩ :=
  sqVal_eq s s₀ hc hsq h2 (s.exists_cl (s.cl a)).choose_spec

theorem SecRep.sqMap_add (s : SecRep X N₀ N₁ W) (s₀ : SecRep X ⊥ N₀ W₀)
    (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hsq : ∀ a ∈ N₁, a ^ 2 ∈ N₀) (h2 : ∀ z ∈ N₀, z ^ 2 = 1)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₁, ⁅a, b⁆ ∈ N₀) (v w : W) :
    SecRep.sqMap s s₀ hc hsq h2 (v + w) =
      SecRep.sqMap s s₀ hc hsq h2 v + SecRep.sqMap s s₀ hc hsq h2 w +
        SecRep.commForm s s₀ hc hcomm v w := by
  obtain ⟨a, ha⟩ := s.exists_cl v
  obtain ⟨b, hb⟩ := s.exists_cl w
  rw [← ha, ← hb, ← SecRep.cl_mul]
  rw [SecRep.sqMap_cl s s₀ hc hsq h2 (a * b), SecRep.sqMap_cl s s₀ hc hsq h2 a,
    SecRep.sqMap_cl s s₀ hc hsq h2 b, SecRep.commForm_cl s s₀ hc hcomm a b]
  rw [← SecRep.cl_mul, ← SecRep.cl_mul]
  have hZ : ∀ z ∈ N₀.subgroupOf N₁, ∀ g : ↥N₁, g * z = z * g := by
    intro z hz g
    apply Subtype.ext
    exact (hc (z : G) (Subgroup.mem_subgroupOf.mp hz) (g : G) g.2).symm
  have hsq_sub : (a * b : ↥N₁) ^ 2 = a ^ 2 * b ^ 2 * ⁅(b : ↥N₁), (a : ↥N₁)⁆ := by
    refine CFSG.Quasithin.St84.sq_mul_of_central (Z := N₀.subgroupOf N₁) hZ ?_ ?_ ?_
    · rw [Subgroup.mem_subgroupOf]; exact hsq a a.2
    · rw [Subgroup.mem_subgroupOf]; exact hsq b b.2
    · rw [Subgroup.mem_subgroupOf]; exact hcomm b b.2 a a.2
  have hsqG : ((a * b : ↥N₁) : G) ^ 2 =
      (a : G) ^ 2 * (b : G) ^ 2 * ⁅(b : G), (a : G)⁆ := by
    have := congrArg (fun x : ↥N₁ => (x : G)) hsq_sub
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def] using this
  have hsym : ⁅(b : G), (a : G)⁆ = ⁅(a : G), (b : G)⁆ := by
    rw [← commutatorElement_inv]
    have hg : ⁅(a : G), (b : G)⁆ * ⁅(a : G), (b : G)⁆ = 1 := by
      simpa [pow_two] using h2 _ (hcomm a a.2 b b.2)
    exact inv_eq_of_mul_eq_one_right hg
  have helem : (⟨((a * b : ↥N₁) : G) ^ 2, hsq (a * b) (a * b).2⟩ : ↥N₀) =
      (⟨(a : G) ^ 2, hsq a a.2⟩ : ↥N₀) * ⟨(b : G) ^ 2, hsq b b.2⟩ *
        commElem hcomm a b := by
    apply Subtype.ext
    show ((a * b : ↥N₁) : G) ^ 2 =
      (a : G) ^ 2 * (b : G) ^ 2 * ⁅(a : G), (b : G)⁆
    rw [hsqG, hsym]
  exact congrArg s₀.cl helem

theorem SecRep.sqMap_ρ (h : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W)
    (s₀ : SecRep X ⊥ N₀ W₀) (hc : ∀ z ∈ N₀, ∀ x ∈ N₁, z * x = x * z)
    (hsq : ∀ a ∈ N₁, a ^ 2 ∈ N₀) (h2 : ∀ z ∈ N₀, z ^ 2 = 1)
    (x : ↥X) (v : W) :
    SecRep.sqMap s s₀ hc hsq h2 (s.ρ x v) =
      s₀.ρ x (SecRep.sqMap s s₀ hc hsq h2 v) := by
  obtain ⟨a, ha⟩ := s.exists_cl v
  rw [← ha, SecRep.sqMap_cl s s₀ hc hsq h2 a]
  let a' : ↥N₁ := ⟨(x : G) * (a : G) * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.norm₁ x.2) (a : G)).mp a.2⟩
  let c' : ↥N₀ := ⟨(x : G) * (a : G) ^ 2 * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.norm₀ x.2) ((a : G) ^ 2)).mp (hsq a a.2)⟩
  have hact : s.ρ x (s.cl a) = s.cl a' := s.act x a a' rfl
  have hact₀ : s₀.ρ x (s₀.cl ⟨(a : G) ^ 2, hsq a a.2⟩) = s₀.cl c' :=
    s₀.act x ⟨(a : G) ^ 2, hsq a a.2⟩ c' rfl
  rw [hact, SecRep.sqMap_cl s s₀ hc hsq h2 a', hact₀]
  apply congrArg s₀.cl
  apply Subtype.ext
  show ((x : G) * (a : G) * (x : G)⁻¹) ^ 2 = (x : G) * (a : G) ^ 2 * (x : G)⁻¹
  rw [pow_two, pow_two]
  group

end CFSG.Quasithin.F112R.St84

end
