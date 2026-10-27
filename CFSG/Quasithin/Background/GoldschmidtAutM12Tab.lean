module

public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Quasithin.Background.GoldschmidtAutM12Core

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Quasithin

namespace AutM12Recog

namespace Tab

structure Rep (G D : Type) [Group G] where
  rel : G → D → Prop
  mulD : D → D → D
  oneD : D
  rel_inj : ∀ (x y : G) (d : D), rel x d → rel y d → x = y
  rel_uniq : ∀ (x : G) (d e : D), rel x d → rel x e → d = e
  rel_mul : ∀ (x y : G) (d e : D), rel x d → rel y e → rel (x * y) (mulD d e)
  rel_one : rel 1 oneD

@[expose] def permSubRep (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Rep ↥H (List ℕ) where
  rel x l := RepL l (x : Equiv.Perm (Fin n))
  mulD := compL
  oneD := List.range n
  rel_inj := fun _ _ _ h h' => Subtype.ext (eq_of_repL h h')
  rel_uniq := fun _ _ _ h h' => repL_unique h h'
  rel_mul := fun _ _ _ _ h h' => repL_mul h h'
  rel_one := repL_one n

section Valid

variable {G D : Type} [Group G]

@[expose] def ValidD [DecidableEq D] (mulD : D → D → D) (oneD : D) (gd els : List D)
    (par lab : List ℕ) (rm : List (List ℕ)) : Prop :=
  0 < els.length ∧ els.getD 0 oneD = oneD ∧ els.Nodup ∧
    (∀ j, 1 ≤ j → j < els.length → par.getD j 0 < j ∧ lab.getD j 0 < gd.length ∧
      mulD (els.getD (par.getD j 0) oneD) (gd.getD (lab.getD j 0) oneD) = els.getD j oneD) ∧
    (∀ i, i < els.length → ∀ a, a < gd.length →
      (rm.getD i []).getD a 0 < els.length ∧
        mulD (els.getD i oneD) (gd.getD a oneD) = els.getD ((rm.getD i []).getD a 0) oneD)

instance [DecidableEq D] (mulD : D → D → D) (oneD : D) (gd els : List D) (par lab : List ℕ)
    (rm : List (List ℕ)) : Decidable (ValidD mulD oneD gd els par lab rm) := by
  unfold ValidD
  infer_instance

@[expose] def Valid [DecidableEq D] (R : Rep G D) (gd els : List D) (par lab : List ℕ)
    (rm : List (List ℕ)) : Prop :=
  ValidD R.mulD R.oneD gd els par lab rm

variable {R : Rep G D} [DecidableEq D] {gd els : List D} {par lab : List ℕ} {rm : List (List ℕ)}

theorem card_closure_of_valid (gens : ℕ → G) (k : ℕ) (hk : gd.length = k)
    (hgd : ∀ a, a < k → R.rel (gens a) (gd.getD a R.oneD))
    (hv : Valid R gd els par lab rm) :
    (∀ x ∈ Subgroup.closure (gens '' {a | a < k}), ∃ j, j < els.length ∧
        R.rel x (els.getD j R.oneD)) ∧
      (∀ j, j < els.length → ∃ x ∈ Subgroup.closure (gens '' {a | a < k}),
        R.rel x (els.getD j R.oneD)) ∧
      Nat.card (Subgroup.closure (gens '' {a | a < k})) = els.length := by
  obtain ⟨hpos, h0, hnd, hpar, hrm⟩ := hv
  set H := Subgroup.closure (gens '' {a | a < k}) with hH
  have hgen : ∀ a, a < k → gens a ∈ H := fun a ha => Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hreach : ∀ j, j < els.length → ∃ x ∈ H, R.rel x (els.getD j R.oneD) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact ⟨1, H.one_mem, by rw [h0]; exact R.rel_one⟩
      · obtain ⟨hp, hl, he⟩ := hpar j hj0 hj
        obtain ⟨x, hx, hrx⟩ := ih _ hp (lt_trans hp hj)
        refine ⟨x * gens (lab.getD j 0), H.mul_mem hx (hgen _ (hk ▸ hl)), ?_⟩
        rw [← he]
        exact R.rel_mul _ _ _ _ hrx (hgd _ (hk ▸ hl))
  have hstep : ∀ x : G, ∀ j, j < els.length → R.rel x (els.getD j R.oneD) → ∀ a, a < k →
      R.rel (x * gens a) (els.getD ((rm.getD j []).getD a 0) R.oneD) := by
    intro x j hj hx a ha
    rw [← (hrm j hj a (hk ▸ ha)).2]
    exact R.rel_mul _ _ _ _ hx (hgd a ha)
  have hmem : ∀ x ∈ H, ∃ j, j < els.length ∧ R.rel x (els.getD j R.oneD) := by
    intro x hx
    refine Subgroup.closure_induction_right (p := fun x _ => ∃ j, j < els.length ∧
      R.rel x (els.getD j R.oneD)) ⟨0, hpos, by rw [h0]; exact R.rel_one⟩ ?_ ?_ hx
    · rintro x hx' y ⟨a, ha, rfl⟩ ⟨j, hj, hjx⟩
      exact ⟨_, (hrm j hj a (hk ▸ ha)).1, hstep x j hj hjx a ha⟩
    · rintro x hx' y ⟨a, ha, rfl⟩ ⟨j, hj, hjx⟩
      have hinj : ∀ i, i < els.length → ∀ i', i' < els.length →
          (rm.getD i []).getD a 0 = (rm.getD i' []).getD a 0 → i = i' := by
        intro i hi i' hi' h
        obtain ⟨xi, -, hxi⟩ := hreach i hi
        obtain ⟨xi', -, hxi'⟩ := hreach i' hi'
        have e1 := hstep xi i hi hxi a ha
        have e2 := hstep xi' i' hi' hxi' a ha
        rw [← h] at e2
        have e4 : xi = xi' := mul_right_cancel (R.rel_inj _ _ _ e1 e2)
        have e5 : els.getD i R.oneD = els.getD i' R.oneD := by
          rw [e4] at hxi
          exact R.rel_uniq _ _ _ hxi hxi'
        exact (List.Nodup.getElem_inj_iff hnd).mp
          (by rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e5)
      let f : Fin els.length → Fin els.length := fun i =>
        ⟨(rm.getD i []).getD a 0, (hrm i i.2 a (hk ▸ ha)).1⟩
      have hf : Function.Injective f := fun i i' h =>
        Fin.ext (hinj i i.2 i' i'.2 (congrArg Fin.val h))
      obtain ⟨i0, hi0⟩ := (Finite.injective_iff_surjective.mp hf) ⟨j, hj⟩
      obtain ⟨xi, -, hxi⟩ := hreach i0 i0.2
      have e1 := hstep xi i0 i0.2 hxi a ha
      have e2 : (rm.getD i0 []).getD a 0 = j := congrArg Fin.val hi0
      rw [e2] at e1
      have e4 : x = xi * gens a := R.rel_inj _ _ _ hjx e1
      refine ⟨i0, i0.2, ?_⟩
      have : x * (gens a)⁻¹ = xi := by rw [e4]; group
      rw [this]
      exact hxi
  refine ⟨hmem, hreach, ?_⟩
  choose! x hxH hxr using hreach
  have hbij : Function.Bijective (fun j : Fin els.length => (⟨x j, hxH j j.2⟩ : H)) := by
    constructor
    · intro i j h
      have h1 : x i = x j := congrArg Subtype.val h
      have h2 : els.getD i R.oneD = els.getD j R.oneD := by
        have hi := hxr i i.2
        rw [h1] at hi
        exact R.rel_uniq _ _ _ hi (hxr j j.2)
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp
        (by rwa [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2] at h2))
    · rintro ⟨y, hy⟩
      obtain ⟨j, hj, hjy⟩ := hmem y hy
      refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
      exact R.rel_inj _ _ _ (hxr j hj) hjy
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fin]

theorem isElemAbelian_of_valid (gens : ℕ → G) (k : ℕ) (hk : gd.length = k)
    (hgd : ∀ a, a < k → R.rel (gens a) (gd.getD a R.oneD))
    (hv : Valid R gd els par lab rm)
    (hcomm : ∀ i, i < els.length → ∀ j, j < els.length →
      R.mulD (els.getD i R.oneD) (els.getD j R.oneD) =
        R.mulD (els.getD j R.oneD) (els.getD i R.oneD))
    (hsq : ∀ i, i < els.length → R.mulD (els.getD i R.oneD) (els.getD i R.oneD) = R.oneD) :
    IsElemAbelian 2 (Subgroup.closure (gens '' {a | a < k})) := by
  obtain ⟨hmem, -, -⟩ := card_closure_of_valid gens k hk hgd hv
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨i, hi, hxi⟩ := hmem x hx
    obtain ⟨j, hj, hyj⟩ := hmem y hy
    apply Subtype.ext
    show x * y = y * x
    exact R.rel_inj _ _ _ (R.rel_mul _ _ _ _ hxi hyj)
      (hcomm i hi j hj ▸ R.rel_mul _ _ _ _ hyj hxi)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := hmem x hx
    rw [pow_two]
    exact R.rel_inj _ _ _ (R.rel_mul _ _ _ _ hxi hxi) (by rw [hsq i hi]; exact R.rel_one)

end Valid

end Tab

@[expose] def HasTwoE16 (Q : Type) [Group Q] : Prop :=
  ∃ B B' : Subgroup Q, IsElemAbelian 2 B ∧ IsElemAbelian 2 B' ∧ Nat.card B = 16 ∧
    Nat.card B' = 16 ∧ B ≠ B'

theorem HasTwoE16.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : HasTwoE16 Q) : HasTwoE16 Q' := by
  obtain ⟨B, B', hB, hB', c, c', hne⟩ := h
  have key : ∀ C : Subgroup Q, IsElemAbelian 2 C → IsElemAbelian 2 (C.map e.toMonoidHom) := by
    intro C hC
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show e a * e b = e b * e a
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hC.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hC.2 a ha, map_one]
  refine ⟨B.map e.toMonoidHom, B'.map e.toMonoidHom, key B hB, key B' hB', ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (B.equivMapOfInjective e.toMonoidHom e.injective).toEquiv, c]
  · rw [← Nat.card_congr (B'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv, c']
  · exact fun h => hne (Subgroup.map_injective e.injective h)

theorem hasTwoE16_sylow {G : Type} [Group G] [Finite G] {H E E' : Subgroup G}
    (hH : IsPGroup 2 H) (hE : E ≤ H) (hE' : E' ≤ H) (hEa : IsElemAbelian 2 E)
    (hEa' : IsElemAbelian 2 E') (hc : Nat.card E = 16) (hc' : Nat.card E' = 16) (hne : E ≠ E')
    (Q : Sylow 2 G) : HasTwoE16 ↥(Q : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0, hHQ0⟩ := hH.exists_le_sylow
  have key : ∀ C : Subgroup G, C ≤ (Q0 : Subgroup G) → IsElemAbelian 2 C →
      IsElemAbelian 2 (C.subgroupOf (Q0 : Subgroup G)) := by
    intro C hC hCa
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
      apply Subtype.ext
      apply Subtype.ext
      show a * b = b * a
      exact congrArg Subtype.val (hCa.1.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)
    · rintro ⟨a, ha⟩ ha'
      apply Subtype.ext
      exact hCa.2 a ha'
  have hE0 : E ≤ (Q0 : Subgroup G) := hE.trans hHQ0
  have hE0' : E' ≤ (Q0 : Subgroup G) := hE'.trans hHQ0
  have h0 : HasTwoE16 ↥(Q0 : Subgroup G) := by
    refine ⟨E.subgroupOf Q0, E'.subgroupOf Q0, key E hE0 hEa, key E' hE0' hEa', ?_, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0).toEquiv, hc]
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0').toEquiv, hc']
    · intro h
      apply hne
      have := congrArg (Subgroup.map (Q0 : Subgroup G).subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hE0, Subgroup.map_subgroupOf_eq_of_le hE0'] at this
  exact h0.of_mulEquiv (Sylow.equiv Q0 Q)

namespace TProps

variable {T : Type} [Group T] (hT : TProps T)
include hT

theorem not_hasTwoE16 {Q : Type} [Group Q] (f : Q →* T) (hf : Function.Injective f) :
    ¬ HasTwoE16 Q := by
  rintro ⟨B, B', hB, hB', c, c', hne⟩
  exact hT.false_of_two_E16 f hf B B' hB hB' c c' hne

end TProps

end AutM12Recog

end CFSG.Quasithin.F6
