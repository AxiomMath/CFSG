module

public import CFSG.RankThree.PartOne.SLB4A.ExcOdd
public import CFSG.RankThree.PartOne.SLB4A.WeylWord3

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

@[expose] def e6i (k : Fin 6) : Fin TwistTag.E6.tag.rank := Fin.cast (by decide) k

@[expose] def orbL : Fin 4 → List (Fin TwistTag.E6.tag.rank) :=
  ![[e6i 0, e6i 5], [e6i 2, e6i 4], [e6i 3], [e6i 1]]

@[expose] def wordF4 : List (Fin 4) :=
  [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

@[expose] def omega6 : List (Fin TwistTag.E6.tag.rank) := wordF4.flatMap orbL

theorem wsq_omega6 : WSq TwistTag.E6.tag omega6 := by
  unfold WSq
  decide +kernel

theorem walk_omega6_zero : (walk TwistTag.E6.tag omega6 0).1 ≠ 0 := by
  decide +kernel

@[expose] def orbPar (τ : Tag) (l : List (Fin τ.rank)) (α : Fin τ.rank → ℤ) : ℤ :=
  (l.map fun i => ∑ j, τ.cartan i j * α j).sum

theorem hpar_omega6 : ∀ a : Fin 4, ∀ k < TwistTag.E6.tag.rootCertificate.roots.length,
    orbPar TwistTag.E6.tag (orbL a) (TwistTag.E6.tag.rootCertificate.root k) % 2 =
      orbPar TwistTag.E6.tag (orbL a) (TwistTag.E6.tag.rootCertificate.root (walk TwistTag.E6.tag omega6 k).1) % 2 := by
  decide +kernel

@[expose] def sgl (τ : Tag) (l : List (Fin τ.rank)) (j : Fin τ.rank) : C2 :=
  (l.map fun i => if τ.cartan i j % 2 = 0 then (1 : C2) else c2gen).prod

theorem hcomb_E6 : ∀ v : V2 5, (∀ j : Fin TwistTag.E6.tag.rank,
    sgl TwistTag.E6.tag (orbL 0) j ^ ex (v 0) * sgl TwistTag.E6.tag (orbL 1) j ^ ex (v 1) *
      sgl TwistTag.E6.tag (orbL 2) j ^ ex (v 2) * sgl TwistTag.E6.tag (orbL 3) j ^ ex (v 3) = 1) →
    v 0 = 1 ∧ v 1 = 1 ∧ v 2 = 1 ∧ v 3 = 1 := by
  decide +kernel

section TT

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def tprod (l : List (Fin τ.rank)) : adjointGroup τ K :=
  (l.map fun i => dElt i (-1 : Kˣ)).prod

theorem tprod_nil : (tprod [] : adjointGroup τ K) = 1 := rfl

theorem tprod_cons (i : Fin τ.rank) (l : List (Fin τ.rank)) :
    (tprod (i :: l) : adjointGroup τ K) = dElt i (-1 : Kˣ) * tprod l := by
  simp [tprod]

theorem coe_tprod (l : List (Fin τ.rank)) :
    ((tprod l : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) =
      (l.map fun j => torusElt τ K j (-1 : Kˣ)).prod := by
  rw [tprod, Subgroup.val_list_prod, List.map_map]
  rfl

theorem tprod_comm (l l' : List (Fin τ.rank)) :
    (tprod l * tprod l' : adjointGroup τ K) = tprod l' * tprod l := by
  have h : Commute (tprod l : adjointGroup τ K) (tprod l') := by
    refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
    exact dElt_mul_comm' i j _ _
  exact h.eq

theorem tprod_sq (l : List (Fin τ.rank)) : (tprod l * tprod l : adjointGroup τ K) = 1 := by
  induction l with
  | nil => simp [tprod_nil]
  | cons i l ih =>
    rw [tprod_cons]
    have hc : tprod l * dElt i (-1 : Kˣ) = dElt i (-1 : Kˣ) * (tprod l : adjointGroup τ K) := by
      have := tprod_comm (K := K) [i] l
      simpa [tprod_cons, tprod_nil] using this.symm
    calc dElt i (-1 : Kˣ) * tprod l * (dElt i (-1 : Kˣ) * tprod l)
        = dElt i (-1 : Kˣ) * (tprod l * dElt i (-1 : Kˣ)) * tprod l := by group
      _ = dElt i (-1 : Kˣ) * (dElt i (-1 : Kˣ) * tprod l) * tprod l := by rw [hc]
      _ = (dElt i (-1 : Kˣ) * dElt i (-1 : Kˣ)) * (tprod l * tprod l) := by group
      _ = 1 := by rw [dElt_neg_one_sq, ih, one_mul]

theorem tprod_hVec (l : List (Fin τ.rank)) (j : Fin τ.rank) :
    opOf (tprod l : adjointGroup τ K) (hVec τ K j) = hVec τ K j := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [tprod_cons, opOf_mul, Module.End.mul_apply, ih, opOf_dElt, torusElt_hVec]

theorem tprod_rootVec (l : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    opOf (tprod l : adjointGroup τ K) (rootVec τ K α) =
      ((((-1 : Kˣ) ^ orbPar τ l α : Kˣ) : K)) • rootVec τ K α := by
  induction l with
  | nil => simp [tprod_nil, orbPar, opOf_one]
  | cons i l ih =>
    rw [tprod_cons, opOf_mul, Module.End.mul_apply, ih, map_smul, opOf_dElt,
      torusElt_rootVec i (-1) hα, smul_smul]
    have : orbPar τ (i :: l) α = (∑ j, τ.cartan i j * α j) + orbPar τ l α := by
      simp [orbPar]
    rw [this, zpow_add, Units.val_mul, mul_comm]

theorem wElt_comm_tprod (ω : List (Fin τ.rank)) (l : List (Fin τ.rank))
    (hpar : ∀ k < τ.rootCertificate.roots.length,
      orbPar τ l (τ.rootCertificate.root k) % 2 =
        orbPar τ l (τ.rootCertificate.root (walk τ ω k).1) % 2) :
    (wElt ω * tprod l : adjointGroup τ K) = tprod l * wElt ω := by
  refine Subtype.ext (Units.ext (end_ext' (fun j => ?_) (fun k hk => ?_)))
  · have h1 := prod_weylElt_hVecSum K ω (Pi.single j 1)
    rw [hVecSum_single] at h1
    have h2 : opOf (wElt ω : adjointGroup τ K) (hVec τ K j) =
        hVecSum K (ω.foldr (hStep τ) (Pi.single j 1)) := h1
    have hD : ∀ c : Fin τ.rank → ℤ, opOf (tprod l : adjointGroup τ K) (hVecSum K c) =
        hVecSum K c := fun c => by
      simp only [hVecSum, map_sum, map_smul, tprod_hVec]
    show opOf (wElt ω * tprod l) (hVec τ K j) = opOf (tprod l * wElt ω) (hVec τ K j)
    rw [opOf_mul, opOf_mul, Module.End.mul_apply, Module.End.mul_apply, tprod_hVec, h2, hD]
  · have hr := isRoot_rootCertificate_root (τ := τ) hk
    have hr' := isRoot_rootCertificate_root (τ := τ) (walk_fst_lt ω hk)
    have h1 : opOf (wElt ω : adjointGroup τ K) (rootVec τ K (τ.rootCertificate.root k)) =
        ((-1 : K) ^ (walk τ ω k).2) • rootVec τ K (τ.rootCertificate.root (walk τ ω k).1) :=
      prod_weylElt_rootVec_root K ω hk
    show opOf (wElt ω * tprod l) (rootVec τ K (τ.rootCertificate.root k)) =
      opOf (tprod l * wElt ω) (rootVec τ K (τ.rootCertificate.root k))
    rw [opOf_mul, opOf_mul, Module.End.mul_apply, Module.End.mul_apply, tprod_rootVec l hr,
      map_smul, h1, map_smul, tprod_rootVec l hr', smul_smul, smul_smul,
      neg_one_zpow_parity (hpar k hk), mul_comm]

theorem tprod_hasEig (l : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    HasEig (opOf (tprod l : adjointGroup τ K)) (rootVec τ K α) := by
  induction l with
  | nil => rw [tprod_nil, opOf_one]; exact HasEig.one _
  | cons i l ih =>
    rw [tprod_cons, opOf_mul]
    refine HasEig.mul ?_ ih
    simpa using dElt_pow_hasEig (K := K) i (-1 : Kˣ) 1 hα

theorem tprod_pow_hasEig (l : List (Fin τ.rank)) (n : ℕ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    HasEig (opOf ((tprod l : adjointGroup τ K) ^ n)) (rootVec τ K α) := by
  rw [opOf_pow]
  exact HasEig.pow (tprod_hasEig l hα) n

theorem Mult_pow {j : Fin τ.rank} {Q : adjointGroup τ K} {m : K} (h : Mult j Q m) (n : ℕ) :
    Mult j (Q ^ n) (m ^ n) := by
  induction n with
  | zero => simpa using Mult_one j
  | succ n ih => rw [pow_succ, pow_succ]; exact Mult_mul ih h

theorem Mult_tprod (l : List (Fin τ.rank)) (j : Fin τ.rank) :
    Mult j (tprod l : adjointGroup τ K) (eps K (sgl τ l j)) := by
  induction l with
  | nil => simpa [tprod_nil, sgl, eps_one] using Mult_one j
  | cons i l ih =>
    rw [tprod_cons]
    have h1 : Mult j (dElt i (-1 : Kˣ) : adjointGroup τ K)
        (((((-1 : Kˣ) ^ τ.cartan i j : Kˣ)) : K)) := by
      simpa using Mult_dElt_pow i j (-1 : Kˣ) 1
    have h2 : sgl τ (i :: l) j = (if τ.cartan i j % 2 = 0 then (1 : C2) else c2gen) * sgl τ l j := by
      simp [sgl]
    rw [h2, eps_mul]
    have h3 := Mult_mul h1 ih
    rwa [neg_one_zpow_eq_eps] at h3

end TT

section Gens

variable {K : Type} [Field K]

noncomputable def gT (k : Fin 5) : adjointGroup TwistTag.E6.tag K :=
  if h : k.1 < 4 then tprod (orbL ⟨k.1, h⟩) else wElt omega6

theorem gT_lt {k : Fin 5} (h : k.1 < 4) : (gT k : adjointGroup TwistTag.E6.tag K) = tprod (orbL ⟨k.1, h⟩) := by
  simp [gT, h]

theorem gT_four : (gT 4 : adjointGroup TwistTag.E6.tag K) = wElt omega6 := by
  simp [gT]

theorem gT_comm (i j : Fin 5) : (gT i * gT j : adjointGroup TwistTag.E6.tag K) = gT j * gT i := by
  by_cases hi : i.1 < 4 <;> by_cases hj : j.1 < 4
  · rw [gT_lt hi, gT_lt hj]
    exact tprod_comm _ _
  · rw [gT_lt hi, show j = 4 from Fin.ext (by omega), gT_four]
    exact (wElt_comm_tprod omega6 _ (hpar_omega6 _)).symm
  · rw [gT_lt hj, show i = 4 from Fin.ext (by omega), gT_four]
    exact wElt_comm_tprod omega6 _ (hpar_omega6 _)
  · rw [show i = 4 from Fin.ext (by omega), show j = 4 from Fin.ext (by omega)]

theorem gT_sq (k : Fin 5) : (gT k * gT k : adjointGroup TwistTag.E6.tag K) = 1 := by
  by_cases hk : k.1 < 4
  · rw [gT_lt hk]
    exact tprod_sq _
  · rw [show k = 4 from Fin.ext (by omega), gT_four]
    exact wElt_mul_wElt_eq_one wsq_omega6

theorem gT_ind (hneg : (-1 : K) ≠ 1) (v : V2 5)
    (hv : (gT 0 : adjointGroup TwistTag.E6.tag K) ^ ex (v 0) * gT 1 ^ ex (v 1) * gT 2 ^ ex (v 2) *
      gT 3 ^ ex (v 3) * gT 4 ^ ex (v 4) = 1) : v = 1 := by
  have e0 : (gT 0 : adjointGroup TwistTag.E6.tag K) = tprod (orbL 0) := gT_lt (by decide)
  have e1 : (gT 1 : adjointGroup TwistTag.E6.tag K) = tprod (orbL 1) := gT_lt (by decide)
  have e2 : (gT 2 : adjointGroup TwistTag.E6.tag K) = tprod (orbL 2) := gT_lt (by decide)
  have e3 : (gT 3 : adjointGroup TwistTag.E6.tag K) = tprod (orbL 3) := gT_lt (by decide)
  rw [e0, e1, e2, e3, gT_four] at hv
  rcases ex_cases (v 4) with h4 | h4
  · rw [h4, pow_zero, mul_one] at hv
    have hall := hcomb_E6 v fun j => by
      have hM := Mult_mul (Mult_mul (Mult_mul (Mult_pow (Mult_tprod (K := K) (orbL 0) j) (ex (v 0)))
        (Mult_pow (Mult_tprod (K := K) (orbL 1) j) (ex (v 1))))
        (Mult_pow (Mult_tprod (K := K) (orbL 2) j) (ex (v 2))))
        (Mult_pow (Mult_tprod (K := K) (orbL 3) j) (ex (v 3)))
      rw [hv] at hM
      have h1 := eq_of_Mult_one hM
      simp only [eps_pow, ← eps_mul] at h1
      exact eps_inj hneg (h1.trans (eps_one K).symm)
    obtain ⟨a0, a1, a2, a3⟩ := hall
    funext k
    fin_cases k
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact eq_one_of_ex_eq_zero h4
  · rw [h4, pow_one] at hv
    have hr := isRoot_rootCertificate_root (τ := TwistTag.E6.tag) (walk_fst_lt omega6 (k := 0) (by decide))
    have hD : HasEig (opOf (tprod (orbL 0) ^ ex (v 0) * tprod (orbL 1) ^ ex (v 1) *
        tprod (orbL 2) ^ ex (v 2) * tprod (orbL 3) ^ ex (v 3) : adjointGroup TwistTag.E6.tag K))
        (rootVec TwistTag.E6.tag K (TwistTag.E6.tag.rootCertificate.root (walk TwistTag.E6.tag omega6 0).1)) := by
      simp only [opOf_mul]
      exact (((tprod_pow_hasEig _ _ hr).mul (tprod_pow_hasEig _ _ hr)).mul
        (tprod_pow_hasEig _ _ hr)).mul (tprod_pow_hasEig _ _ hr)
    exact absurd hv (no_torus_mul_wElt _ omega6 (k := 0) (by decide) walk_omega6_zero hD)

end Gens

end CFSG.RankThree.PartOne.SLB4A
