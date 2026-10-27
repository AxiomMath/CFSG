module

public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.GroupActions.PrimitiveCoprimeSimplicity
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem rawInvs_getElem! {n : ℕ} {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (rawInvs n S)[j]! = invCand n S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem wordA_mem' {n m : ℕ} {S Sinv : Array (Array ℕ)} {K : Subgroup (Equiv.Perm (Fin n))}
    (P : ℕ → Prop) (hS : ∀ h < m, Rep n S[h]! (permOfArr n S[h]!))
    (hSinv : ∀ h < m, Rep n Sinv[h]! (permOfArr n S[h]!)⁻¹)
    (hK : ∀ h < m, P h → permOfArr n S[h]! ∈ K) :
    ∀ w : List ℤ, lettersOK m w = true → (∀ l ∈ w, P (l.natAbs - 1)) →
      ∃ g ∈ K, Rep n (wordA n S Sinv w) g
  | [], _, _ => ⟨1, K.one_mem, rep_idA⟩
  | l :: w, hw, hP => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK m w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g, hgK, hg⟩ := wordA_mem' P hS hSinv hK w hw'
      (fun l' hl' => hP l' (List.mem_cons_of_mem _ hl'))
    have hlet := rep_letterA (gs := fun h => permOfArr n S[h]!) hS hSinv ⟨hl0, hlj⟩
    refine ⟨_, K.mul_mem ?_ hgK, rep_compA hlet hg⟩
    have hPl := hP l List.mem_cons_self
    by_cases hpos : decide (0 < l) = true
    · rw [ite_eq_left hpos]
      exact hK _ (by omega) hPl
    · rw [ite_eq_right hpos]
      exact K.inv_mem (hK _ (by omega) hPl)

theorem strong_mem_closure {n : ℕ} {O S : Array (Array ℕ)} {W : Array (List ℤ)} {base : Array ℕ}
    {chunks : ℕ} (hOS : O.size ≤ S.size) (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (h : rawChainOK n (S.extract 0 O.size) S base W chunks = true) :
    ∀ j < S.size, permOfArr n S[j]! ∈
      Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} := by
  have hF := chainCheckFacts h
  have hosz : (S.extract 0 O.size).size = O.size := by simp [Nat.min_eq_left hOS]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hk : j < O.size
    · rw [hSO j hk]
      exact Subgroup.subset_closure ⟨j, hk, rfl⟩
    · obtain ⟨hl, he⟩ := hF.words j hj (by rw [hosz]; omega)
      have hjj : ∀ h < j, h < S.size := fun h hh => lt_trans hh hj
      obtain ⟨g, hgK, hg⟩ := wordA_mem' (K := Subgroup.closure {g | ∃ k < O.size,
        permOfArr n O[k]! = g}) (m := j) (fun _ => True)
        (fun h hh => (rep_permOfArr (hF.strong_inv h (hjj h hh))).1)
        (fun h hh => (rep_permOfArr (hF.strong_inv h (hjj h hh))).2)
        (fun h hh _ => ih h hh (hjj h hh)) _ hl (fun _ _ => trivial)
      have hrepS := (rep_permOfArr (hF.strong_inv j hj)).1
      have := (eqA_iff hrepS hg).1 he
      rw [this]
      exact hgK

@[expose] def fixLetters (S : Array (Array ℕ)) (x : ℕ) (w : List ℤ) : Bool :=
  w.all fun l => (S[l.natAbs - 1]!)[x]! == x

@[expose] def primCheck (n : ℕ) (S : Array (Array ℕ)) (x : ℕ) (labels roots : Array ℕ) (k : ℕ)
    (tw hw : Array (List ℤ)) : Bool :=
  let Sinv := rawInvs n S
  decide (x < n) && decide (tw.size = n) && decide (hw.size = n) &&
    allLt n fun p =>
      lettersOK S.size tw[p]! && ((wordA n S Sinv tw[p]!)[x]! == p) &&
      lettersOK S.size hw[p]! && fixLetters S x hw[p]! && decide (labels[p]! < k) &&
      decide (roots[labels[p]!]! < n) &&
      ((wordA n S Sinv hw[p]!)[roots[labels[p]!]!]! == p)

theorem primCheck_spec {n k : ℕ} {S : Array (Array ℕ)} {J : Subgroup (Equiv.Perm (Fin n))}
    {x : ℕ} {labels roots : Array ℕ} {tw hw : Array (List ℤ)}
    (hSinvA : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true)
    (hSJ : ∀ j < S.size, permOfArr n S[j]! ∈ J)
    (h : primCheck n S x labels roots k tw hw = true) :
    ∃ hx : x < n, (∀ p : Fin n, ∃ g ∈ J, g ⟨x, hx⟩ = p) ∧
      ∀ p : Fin n, labels[(p : ℕ)]! < k ∧ ∃ r : Fin n, (r : ℕ) = roots[labels[(p : ℕ)]!]! ∧
        ∃ g ∈ J ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n), g r = p := by
  simp only [primCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hx, -⟩, -⟩, hall⟩ := h
  refine ⟨hx, fun p => ?_, fun p => ?_⟩
  · have hp := allLt_spec hall p.2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨htl, htp⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hp
    obtain ⟨g, hgJ, hg⟩ := wordA_mem' (K := J) (m := S.size) (fun _ => True)
      (fun j hj => (rep_permOfArr (hSinvA j hj)).1) (fun j hj => (rep_permOfArr (hSinvA j hj)).2)
      (fun j hj _ => hSJ j hj) _ htl (fun _ _ => trivial)
    refine ⟨g, hgJ, Fin.ext ?_⟩
    rw [← hg.apply hx, htp]
  · have hp := allLt_spec hall p.2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hhl⟩, hfix⟩, hlab⟩, hroot⟩, hhp⟩ := hp
    refine ⟨hlab, ⟨roots[labels[(p : ℕ)]!]!, hroot⟩, rfl, ?_⟩
    have hfix' : ∀ l ∈ hw[(p : ℕ)]!, (S[l.natAbs - 1]!)[x]! = x := by
      intro l hl
      have := List.all_eq_true.1 hfix l hl
      simpa using this
    have hstab : ∀ j < S.size, (S[j]!)[x]! = x →
        permOfArr n S[j]! ∈ J ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n) := by
      intro j hj hxj
      refine ⟨hSJ j hj, ?_⟩
      show permOfArr n S[j]! ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n)
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      apply Fin.ext
      rw [← (rep_permOfArr (hSinvA j hj)).1.apply hx, hxj]
    obtain ⟨g, hgK, hg⟩ := wordA_mem' (K := J ⊓ MulAction.stabilizer (Equiv.Perm (Fin n))
      (⟨x, hx⟩ : Fin n)) (m := S.size) (fun j => (S[j]!)[x]! = x)
      (fun j hj => (rep_permOfArr (hSinvA j hj)).1) (fun j hj => (rep_permOfArr (hSinvA j hj)).2)
      (fun j hj hxj => hstab j hj hxj) _ hhl hfix'
    refine ⟨g, hgK, Fin.ext ?_⟩
    rw [← hg.apply hroot, hhp]

theorem isPreprimitive_of_suborbit_labels' {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X →
      S = {lab x} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive G X := by
  classical
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclosed : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by
      rw [hH h hh]
      exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin k) := (Finset.univ.filter (· ∈ B)).image lab
  have hmemS : ∀ p, lab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem lab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => lab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS,
      ← Nat.card_eq_fintype_card]
    exact hB.ncard_dvd_card ⟨x, hxB⟩
  rcases hdiv S ((hmemS x).mpr hxB) hdvd with hS | hS
  · left
    have hx : ∀ r ∈ B, r = x := by
      intro r hr
      have hr' : lab r ∈ S := (hmemS r).mpr hr
      rw [hS, Finset.mem_singleton] at hr'
      obtain ⟨h, hh, hhr⟩ := horb x r hr'.symm
      rw [← hhr, hH h hh]
    intro p hp q hq
    rw [hx p hp, hx q hq]
  · right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (lab p)

@[expose] def labFin (n k : ℕ) (hk : 0 < k) (labels : Array ℕ) (p : Fin n) : Fin k :=
  ⟨labels[(p : ℕ)]! % k, Nat.mod_lt _ hk⟩

@[expose] def LabelsDivisorOK (n k : ℕ) (hk : 0 < k) (labels : Array ℕ) (x : Fin n) : Prop :=
  ∀ T : Finset (Fin k), labFin n k hk labels x ∈ T →
    (∑ i ∈ T, (Finset.univ.filter (fun p : Fin n => labFin n k hk labels p = i)).card) ∣
        Fintype.card (Fin n) →
    T = {labFin n k hk labels x} ∨ T = Finset.univ

instance (n k : ℕ) (hk : 0 < k) (labels : Array ℕ) (x : Fin n) :
    Decidable (LabelsDivisorOK n k hk labels x) := by
  unfold LabelsDivisorOK
  infer_instance

theorem isSimpleGroup_of_chain_primitive {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    {O S : Array (Array ℕ)} {W : Array (List ℤ)} {base : List (Fin n)} (hbn : base.Nodup)
    {chunks : ℕ} (hc : 0 < chunks) (hO2 : O.size = 2) (hOS : O.size ≤ S.size)
    (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (hchain : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W chunks = true)
    {x : ℕ} {labels roots : Array ℕ} {tw hw : Array (List ℤ)}
    (hprim : primCheck n S x labels roots k tw hw = true)
    (hdiv : ∀ hx : x < n, LabelsDivisorOK n k hk labels ⟨x, hx⟩)
    {m pa pb pc : ℕ} (hm : (rawOrbitSizes n S (base.map Fin.val).toArray).prod = n * m)
    (ha : orderOf (permOfArr n O[0]!) = pa) (hb : orderOf (permOfArr n O[1]!) = pb)
    (hab : orderOf (permOfArr n O[0]! * permOfArr n O[1]!) = pc)
    (hpq : Nat.Coprime pa pb) (hcm : Nat.Coprime pc m) :
    IsSimpleGroup ↥(Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g}) := by
  set J := Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} with hJ
  have hF := chainCheckFacts hchain
  have hSJ := strong_mem_closure hOS hSO hchain
  obtain ⟨hx, hreach, hroots⟩ := primCheck_spec (J := J) hF.strong_inv hSJ hprim
  have hpt : MulAction.IsPretransitive ↥J (Fin n) := by
    refine ⟨fun p q => ?_⟩
    obtain ⟨g, hg, hgp⟩ := hreach p
    obtain ⟨g', hg', hgq⟩ := hreach q
    refine ⟨⟨g' * g⁻¹, J.mul_mem hg' (J.inv_mem hg)⟩, ?_⟩
    show (g' * g⁻¹) p = q
    rw [Equiv.Perm.mul_apply, ← hgp]
    simpa using hgq
  have hprimitive : MulAction.IsPreprimitive ↥J (Fin n) := by
    refine isPreprimitive_of_suborbit_labels' (G := ↥J) (X := Fin n) (⟨x, hx⟩ : Fin n)
      (MulAction.stabilizer ↥J (⟨x, hx⟩ : Fin n)) (fun h hh => hh) (labFin n k hk labels) ?_
      (hdiv hx)
    intro p q hpq
    obtain ⟨hlp, r, hr, g, hg, hgp⟩ := hroots p
    obtain ⟨hlq, r', hr', g', hg', hgq⟩ := hroots q
    have hl : labels[(p : ℕ)]! = labels[(q : ℕ)]! := by
      have h1 : labels[(p : ℕ)]! % k = labels[(q : ℕ)]! % k := congrArg Fin.val hpq
      rwa [Nat.mod_eq_of_lt hlp, Nat.mod_eq_of_lt hlq] at h1
    have hrr : r = r' := Fin.ext (by rw [hr, hr', hl])
    subst hrr
    obtain ⟨hgJ, hgs⟩ := hg
    obtain ⟨hgJ', hgs'⟩ := hg'
    refine ⟨⟨g' * g⁻¹, J.mul_mem hgJ' (J.inv_mem hgJ)⟩, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      show (g' * g⁻¹) ⟨x, hx⟩ = ⟨x, hx⟩
      have h1 : g ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have h := hgs
        change g ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n) at h
        rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      have h2 : g' ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have h := hgs'
        change g' ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n) at h
        rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      rw [Equiv.Perm.mul_apply]
      have h3 : g⁻¹ ⟨x, hx⟩ = ⟨x, hx⟩ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact h1.symm
      rw [h3, h2]
    · show (g' * g⁻¹) p = q
      rw [Equiv.Perm.mul_apply, ← hgp]
      simpa using hgq
  have hO0 : 0 < O.size := by omega
  have hO1 : 1 < O.size := by omega
  let a : ↥J := ⟨permOfArr n O[0]!, Subgroup.subset_closure ⟨0, hO0, rfl⟩⟩
  let b : ↥J := ⟨permOfArr n O[1]!, Subgroup.subset_closure ⟨1, hO1, rfl⟩⟩
  have hgen : Subgroup.closure ({a, b} : Set ↥J) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := {g | ∃ k < O.size,
      permOfArr n O[k]! = g})]
    refine Subgroup.closure_mono ?_
    rintro y ⟨k', hk', hy⟩
    rw [hO2] at hk'
    interval_cases k'
    · exact Or.inl (Subtype.ext hy.symm)
    · exact Or.inr (Subtype.ext hy.symm)
  have hJcard : Nat.card ↥J = n * m := by
    have := card_closure_permOfArr_of_rawChainOK (n := n) (by omega) (O := O) (S := S) (W := W)
      hbn hc hOS hSO hchain
    rw [hm] at this
    exact this
  have hstab : Nat.card (MulAction.stabilizer ↥J (⟨x, hx⟩ : Fin n)) = m := by
    have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥J (⟨x, hx⟩ : Fin n))
    rw [Nat.card_prod, MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, hJcard] at h1
    have hnpos : 0 < n := by omega
    exact Nat.eq_of_mul_eq_mul_left hnpos h1
  have hoa : orderOf a = pa := by rw [← ha]; exact Subgroup.orderOf_mk _ _
  have hob : orderOf b = pb := by rw [← hb]; exact Subgroup.orderOf_mk _ _
  have hoab : orderOf (a * b) = pc := by
    rw [← hab, ← Subgroup.orderOf_coe]
    rfl
  exact CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    (by rw [Nat.card_fin]; exact hn) a b hgen (⟨x, hx⟩ : Fin n) (by rw [hoa, hob]; exact hpq)
    (by rw [hoab, hstab]; exact hcm)

@[expose] def powA (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => compA n t (powA n t k)

theorem rep_powA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    ∀ k : ℕ, Rep n (powA n t k) (g ^ k)
  | 0 => by simpa [powA] using (rep_idA (n := n))
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (rep_powA h k)

theorem orderOf_eq_prime_of_rep {n p : ℕ} [Fact p.Prime] {t : Array ℕ}
    {g : Equiv.Perm (Fin n)} (hg : Rep n t g) (h1 : eqA n (powA n t p) (idA n) = true)
    (h2 : eqA n t (idA n) = false) : orderOf g = p := by
  refine orderOf_eq_prime ((eqA_iff (rep_powA hg p) rep_idA).1 h1) ?_
  intro h
  have : eqA n t (idA n) = true := (eqA_iff hg rep_idA).2 h
  rw [h2] at this
  exact Bool.false_ne_true this

end CFSG.Quasithin
