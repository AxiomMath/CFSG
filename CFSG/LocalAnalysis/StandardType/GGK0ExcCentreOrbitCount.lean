module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreDefs
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreOrbits
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

private def lk0xpa4_orbit {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Set (Fin n) :=
  Set.range (fun k : ℤ => (σ ^ k) i)

private lemma lk0xpa4_orbit_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (i x : Fin n) :
    x ∈ lk0xpa4_orbit σ i ↔ σ.SameCycle i x := by
  constructor
  · rintro ⟨k, hk⟩
    exact Equiv.Perm.SameCycle.of_zpow (f := σ) (n := k) ⟨1, by simpa using hk⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : ℤ), by simpa using hm⟩

private lemma lk0xpa4_orbit_eq_sameCycle {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    lk0xpa4_orbit σ i = lk0xpa4_orbit σ j ↔ σ.SameCycle i j := by
  have heq : Equivalence (σ.SameCycle) := Equiv.Perm.SameCycle.equivalence σ
  constructor
  · intro h
    have : j ∈ lk0xpa4_orbit σ i := by
      rw [h]
      exact ⟨0, by simp⟩
    exact (lk0xpa4_orbit_mem σ i j).mp this
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      exact (lk0xpa4_orbit_mem σ j x).mpr (heq.trans h.symm ((lk0xpa4_orbit_mem σ i x).mp hx))
    · intro x hx
      exact (lk0xpa4_orbit_mem σ i x).mpr (heq.trans h ((lk0xpa4_orbit_mem σ j x).mp hx))

private lemma lk0xpa4_go_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} {rho : List ℕ}
    (hlen : rho.length = n) (happly : ∀ i : Fin n, rho.getD i.val 0 = (σ i).val)
    (i : Fin n) :
    ∀ (m t fuel : ℕ), t + m = Function.minimalPeriod σ i → 1 ≤ t → m + 1 ≤ fuel →
      k0NodeOrbit.go rho i.val fuel ((fun s => ((σ ^ s) i).val) t)
          ((List.range t).map (fun s => ((σ ^ s) i).val))
        = (List.range (Function.minimalPeriod σ i)).map (fun s => ((σ ^ s) i).val) := by
  intro m
  induction m with
  | zero =>
      intro t fuel ht ht1 hfuel
      have htk : t = Function.minimalPeriod σ i := by omega
      have hfix : (fun s => ((σ ^ s) i).val) (Function.minimalPeriod σ i) = i.val := by
        have h := Function.iterate_minimalPeriod (f := σ) (x := i)
        simpa [Equiv.Perm.coe_pow] using congrArg Fin.val h
      rw [htk]
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      rw [k0NodeOrbit.go.eq_2, if_pos hfix]
  | succ m ih =>
      intro t fuel ht ht1 hfuel
      have hlt : t < Function.minimalPeriod σ i := by omega
      have hne : (fun s => ((σ ^ s) i).val) t ≠ i.val := by
        intro heq
        have hpow : (σ ^ t) i = i := Fin.ext heq
        have hper : Function.IsPeriodicPt σ t i := by
          rw [Function.IsPeriodicPt, Function.IsFixedPt]
          simpa [Equiv.Perm.coe_pow] using hpow
        exact (Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega : t ≠ 0) hlt) hper
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      rw [k0NodeOrbit.go.eq_2, if_neg hne]
      have hstep : (fun s => ((σ ^ s) i).val) (t + 1)
          = rho.getD ((fun s => ((σ ^ s) i).val) t) 0 := by
        change ((σ ^ (t + 1)) i).val = rho.getD ((σ ^ t) i).val 0
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (happly ((σ ^ t) i)).symm
      rw [← hstep]
      have hacc : (List.range t).map (fun s => ((σ ^ s) i).val)
            ++ [(fun s => ((σ ^ s) i).val) t]
          = (List.range (t + 1)).map (fun s => ((σ ^ s) i).val) := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [hacc]
      exact ih (t + 1) f (by omega) (by omega) (by omega)

private lemma lk0xpa4_nodeOrbit_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} {rho : List ℕ}
    (hlen : rho.length = n) (happly : ∀ i : Fin n, rho.getD i.val 0 = (σ i).val)
    (i : Fin n) :
    k0NodeOrbit rho i.val
      = (List.range (Function.minimalPeriod σ i)).map (fun s => ((σ ^ s) i).val) := by
  have hkpos : 1 ≤ Function.minimalPeriod σ i :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.Injective.mem_periodicPts σ.injective i)
  have hkle : Function.minimalPeriod σ i ≤ n := by
    simpa using Function.minimalPeriod_le_card (f := σ) (x := i)
  have hfuel : (Function.minimalPeriod σ i - 1) + 1 ≤ rho.length + 1 := by
    rw [hlen]; omega
  have hx1 : (fun s => ((σ ^ s) i).val) 1 = rho.getD i.val 0 := by
    show ((σ ^ 1) i).val = rho.getD i.val 0
    rw [pow_one]
    exact (happly i).symm
  have hx0 : (List.range 1).map (fun s => ((σ ^ s) i).val) = [i.val] := by simp
  have h := lk0xpa4_go_eq hlen happly i (Function.minimalPeriod σ i - 1) 1 (rho.length + 1)
      (by omega) (by omega) hfuel
  rw [hx1, hx0] at h
  rw [k0NodeOrbit]
  exact h

private lemma lk0xpa4_zpow_eq_pow_mod {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (t : ℤ) :
    ∃ s : ℕ, s < Function.minimalPeriod σ i ∧ (σ ^ s) i = (σ ^ t) i := by
  have hN : (0 : ℤ) < (orderOf σ : ℤ) := by exact_mod_cast orderOf_pos σ
  set r : ℤ := t % (orderOf σ : ℤ) with hr
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg t (by omega)
  have hz : (σ ^ r) i = (σ ^ t) i := by
    rw [hr, zpow_mod_orderOf]
  have hkpos : 0 < Function.minimalPeriod σ i :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.Injective.mem_periodicPts σ.injective i)
  refine ⟨r.toNat % Function.minimalPeriod σ i, Nat.mod_lt _ hkpos, ?_⟩
  have hiter : (σ ^ (r.toNat % Function.minimalPeriod σ i)) i = (σ ^ r.toNat) i := by
    simpa [Equiv.Perm.coe_pow] using
      (Function.iterate_mod_minimalPeriod_eq (f := σ) (x := i) (n := r.toNat))
  have hcast : (σ ^ r.toNat) i = (σ ^ r) i := by
    conv_rhs => rw [← Int.toNat_of_nonneg hr_nonneg]
    rfl
  rw [hiter, hcast, hz]

private lemma lk0xpa4_nodeOrbit_mem {n : ℕ} {σ : Equiv.Perm (Fin n)} {rho : List ℕ}
    (hlen : rho.length = n) (happly : ∀ i : Fin n, rho.getD i.val 0 = (σ i).val)
    (i j : Fin n) : j.val ∈ k0NodeOrbit rho i.val ↔ σ.SameCycle i j := by
  rw [lk0xpa4_nodeOrbit_eq hlen happly i, List.mem_map]
  constructor
  · rintro ⟨s, _, hsj⟩
    exact ⟨(s : ℤ), Fin.ext hsj⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s, hs, hst⟩ := lk0xpa4_zpow_eq_pow_mod σ i t
    exact ⟨s, by rw [List.mem_range]; exact hs, by
      show ((σ ^ s) i).val = j.val
      rw [hst, ht]⟩

private noncomputable def lk0xpa4_numOrb {n : ℕ} (σ : Equiv.Perm (Fin n))
    (P : Finset (Fin n)) : ℕ :=
  (P.image (fun i => lk0xpa4_orbit σ i)).card

private lemma lk0xpa4_numOrb_eq_numOrbitsOn {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : lk0xpa4_numOrb σ S = numOrbitsOn σ S := by
  classical
  unfold lk0xpa4_numOrb numOrbitsOn lk0xpa4_orbit
  rw [show {O : Set (Fin n) | ∃ i ∈ S, O = Set.range (fun k : ℤ => (σ ^ k) i)}
        = (↑(S.image (fun i => Set.range (fun k : ℤ => (σ ^ k) i))) : Set (Set (Fin n))) by
      ext O
      simp only [Finset.mem_coe, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, h⟩; exact ⟨i, hi, h.symm⟩
      · rintro ⟨i, hi, h⟩; exact ⟨i, hi, h.symm⟩]
  exact (Set.ncard_coe_finset _).symm

private lemma lk0xpa4_numOrb_insert_of_mem {n : ℕ} (σ : Equiv.Perm (Fin n))
    {P : Finset (Fin n)} {i : Fin n} (h : ∃ p ∈ P, σ.SameCycle p i) :
    lk0xpa4_numOrb σ (insert i P) = lk0xpa4_numOrb σ P := by
  classical
  obtain ⟨p, hp, hsp⟩ := h
  have hmem : lk0xpa4_orbit σ i ∈ P.image (fun x => lk0xpa4_orbit σ x) :=
    Finset.mem_image.mpr ⟨p, hp, (lk0xpa4_orbit_eq_sameCycle σ p i).mpr hsp⟩
  unfold lk0xpa4_numOrb
  rw [Finset.image_insert, Finset.card_insert_of_mem hmem]

private lemma lk0xpa4_numOrb_insert_of_notMem {n : ℕ} (σ : Equiv.Perm (Fin n))
    {P : Finset (Fin n)} {i : Fin n} (h : ∀ p ∈ P, ¬ σ.SameCycle p i) :
    lk0xpa4_numOrb σ (insert i P) = lk0xpa4_numOrb σ P + 1 := by
  classical
  have hmem : lk0xpa4_orbit σ i ∉ P.image (fun x => lk0xpa4_orbit σ x) := by
    rw [Finset.mem_image]
    rintro ⟨p, hp, hp'⟩
    exact h p hp ((lk0xpa4_orbit_eq_sameCycle σ p i).mp hp')
  unfold lk0xpa4_numOrb
  rw [Finset.image_insert, Finset.card_insert_of_notMem hmem]

private def lk0xpa4_nf {n : ℕ} (nodes : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ nodes)

private lemma lk0xpa4_nf_nil {n : ℕ} : lk0xpa4_nf (n := n) [] = ∅ := by
  ext i; simp [lk0xpa4_nf]

private lemma lk0xpa4_nf_cons {n : ℕ} {i : ℕ} {rest : List ℕ} (hi : i < n) :
    lk0xpa4_nf (n := n) (i :: rest) = insert ⟨i, hi⟩ (lk0xpa4_nf (n := n) rest) := by
  ext j
  simp only [lk0xpa4_nf, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
    Finset.mem_insert, Fin.ext_iff]

private lemma lk0xpa4_go_count {n : ℕ} (σ : Equiv.Perm (Fin n)) (rho : List ℕ)
    (hlen : rho.length = n) (happly : ∀ i : Fin n, rho.getD i.val 0 = (σ i).val) :
    ∀ (nodes : List ℕ), (∀ i ∈ nodes, i < n) →
      ∀ (P : Finset (Fin n)) (seen : List ℕ) (count : ℕ),
        (∀ j : Fin n, j.val ∈ seen ↔ ∃ p ∈ P, σ.SameCycle p j) →
        count = lk0xpa4_numOrb σ P →
        k0NumRhoOrbits.go rho nodes seen count
          = lk0xpa4_numOrb σ (P ∪ lk0xpa4_nf (n := n) nodes) := by
  intro nodes
  induction nodes with
  | nil =>
      intro hnodes P seen count hseen hcount
      rw [k0NumRhoOrbits.go.eq_1]
      simp only [lk0xpa4_nf_nil, Finset.union_empty]
      exact hcount
  | cons i rest ih =>
      intro hnodes P seen count hseen hcount
      have hi : i < n := hnodes i (by simp)
      have hrest : ∀ j ∈ rest, j < n := fun j hj => hnodes j (by simp [hj])
      rw [k0NumRhoOrbits.go.eq_2]
      by_cases hmem : i ∈ seen
      · rw [if_pos hmem]
        have hwit : ∃ p ∈ P, σ.SameCycle p ⟨i, hi⟩ := (hseen ⟨i, hi⟩).mp hmem
        have hseen' : ∀ j : Fin n, j.val ∈ seen ↔
            ∃ p ∈ insert ⟨i, hi⟩ P, σ.SameCycle p j := by
          intro j
          rw [hseen j]
          constructor
          · rintro ⟨p, hp, hsp⟩
            exact ⟨p, Finset.mem_insert_of_mem hp, hsp⟩
          · rintro ⟨p, hp, hsp⟩
            rcases Finset.mem_insert.mp hp with rfl | hp
            · obtain ⟨q, hq, hsq⟩ := hwit
              exact ⟨q, hq, (Equiv.Perm.SameCycle.equivalence σ).trans hsq hsp⟩
            · exact ⟨p, hp, hsp⟩
        have hcount' : count = lk0xpa4_numOrb σ (insert ⟨i, hi⟩ P) := by
          rw [hcount, lk0xpa4_numOrb_insert_of_mem σ hwit]
        rw [ih hrest (insert ⟨i, hi⟩ P) seen count hseen' hcount']
        congr 1
        rw [lk0xpa4_nf_cons hi]
        ext j; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      · rw [if_neg hmem]
        have hnot : ∀ p ∈ P, ¬ σ.SameCycle p ⟨i, hi⟩ := by
          intro p hp hsp
          exact hmem ((hseen ⟨i, hi⟩).mpr ⟨p, hp, hsp⟩)
        have hseen' : ∀ j : Fin n, j.val ∈ seen ++ k0NodeOrbit rho i ↔
            ∃ p ∈ insert ⟨i, hi⟩ P, σ.SameCycle p j := by
          intro j
          rw [List.mem_append, hseen j]
          constructor
          · rintro (h | h)
            · obtain ⟨p, hp, hsp⟩ := h
              exact ⟨p, Finset.mem_insert_of_mem hp, hsp⟩
            · exact ⟨⟨i, hi⟩, Finset.mem_insert_self _ _,
                (lk0xpa4_nodeOrbit_mem hlen happly ⟨i, hi⟩ j).mp h⟩
          · rintro ⟨p, hp, hsp⟩
            rcases Finset.mem_insert.mp hp with rfl | hp
            · exact Or.inr ((lk0xpa4_nodeOrbit_mem hlen happly ⟨i, hi⟩ j).mpr hsp)
            · exact Or.inl ⟨p, hp, hsp⟩
        have hcount' : count + 1 = lk0xpa4_numOrb σ (insert ⟨i, hi⟩ P) := by
          rw [hcount, lk0xpa4_numOrb_insert_of_notMem σ hnot]
        rw [ih hrest (insert ⟨i, hi⟩ P) (seen ++ k0NodeOrbit rho i) (count + 1)
          hseen' hcount']
        congr 1
        rw [lk0xpa4_nf_cons hi]
        ext j; simp only [Finset.mem_union, Finset.mem_insert]; tauto

private lemma lk0xpa4_numRhoOrbits_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (rho : List ℕ)
    (removed : List ℕ) (s : List ℕ)
    (hlen : rho.length = n) (happly : ∀ i : Fin n, rho.getD i.val 0 = (σ i).val)
    (hnodes : ∀ i ∈ removed, i < n)
    (hrem : ∀ i : Fin n, i.val ∈ removed ↔ 0 < s.getD i.val 0) :
    k0NumRhoOrbits rho removed
      = numOrbitsOn σ (Finset.univ.filter (fun i : Fin n => 0 < s.getD i.val 0)) := by
  classical
  have hgo := lk0xpa4_go_count σ rho hlen happly removed hnodes (∅ : Finset (Fin n)) [] 0
      (by intro j; simp)
      (by simp [lk0xpa4_numOrb])
  rw [k0NumRhoOrbits, hgo, lk0xpa4_numOrb_eq_numOrbitsOn]
  congr 1
  rw [Finset.empty_union]
  ext i
  simp only [lk0xpa4_nf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hrem i

theorem PA4_rZ_eq_numOrbits
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    ρ.row.D.rZ + 1 = numOrbitsOn ρ.row.nodePerm (posNodes ρ) := by
  classical
  have hlabn : 1 ≤ lab.n := by
    by_contra h
    have h0 : lab.n = 0 := by omega
    have hq1 : ρ.setup.D.q = 1 := by rw [ρ.q_eq, h0, pow_zero]
    exact not_isPrimePow_one (hq1 ▸ ρ.setup.hqpow.1)
  have hp_ne : p ≠ 0 := by
    intro hp0
    obtain ⟨T', tw', _, hmem⟩ := ρ.row.valid
    subst p
    have h1 : ¬ 0 ∣ 2 ^ lab.n - 1 := by
      rw [zero_dvd_iff]
      have := Nat.one_lt_two_pow (by omega : lab.n ≠ 0)
      omega
    have h2 : ¬ 0 ∣ 2 ^ lab.n + 1 := by
      rw [zero_dvd_iff]
      have := Nat.two_pow_pos lab.n
      omega
    rw [k0shape_table_branch0 T' tw' 0 lab.n h1 h2] at hmem
    exact List.not_mem_nil hmem
  have hweight : (∑ i : Fin (k0DiagOf ρ.row.T).marks.length,
      (k0DiagOf ρ.row.T).marks.getD i 0 * ρ.row.s.getD i 0) = p :=
    ggKacShVecs_sum _ _ _ ρ.row.s_mem
  have hSnonempty : (posNodes ρ).Nonempty := by
    by_contra hemp
    have hall : ∀ i : Fin (k0DiagOf ρ.row.T).marks.length, ρ.row.s.getD i.val 0 = 0 := by
      intro i
      have hi : i ∉ posNodes ρ := fun hmem => hemp ⟨i, hmem⟩
      have hz : ¬ 0 < ρ.row.s.getD i.val 0 := by simpa [posNodes] using hi
      omega
    have hp0 : p = 0 := by
      rw [← hweight]
      exact Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])
    exact hp_ne hp0
  have hcount : k0NumRhoOrbits ρ.row.rho
        ((List.range (k0DiagOf ρ.row.T).marks.length).filter
          (fun i => decide (ρ.row.s.getD i 0 > 0)))
      = numOrbitsOn ρ.row.nodePerm (posNodes ρ) := by
    have hrem : ∀ i : Fin (k0DiagOf ρ.row.T).marks.length,
        i.val ∈ (List.range (k0DiagOf ρ.row.T).marks.length).filter
            (fun i => decide (ρ.row.s.getD i 0 > 0)) ↔ 0 < ρ.row.s.getD i.val 0 := by
      intro i
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨i.isLt, h⟩⟩
    have hnodes : ∀ i ∈ (List.range (k0DiagOf ρ.row.T).marks.length).filter
          (fun i => decide (ρ.row.s.getD i 0 > 0)), i < (k0DiagOf ρ.row.T).marks.length :=
      fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
    have := lk0xpa4_numRhoOrbits_eq ρ.row.nodePerm ρ.row.rho _ ρ.row.s ρ.row.rho_length
      ρ.row.rho_apply hnodes hrem
    simpa [posNodes] using this
  have hpos : 0 < numOrbitsOn ρ.row.nodePerm (posNodes ρ) := by
    rw [← lk0xpa4_numOrb_eq_numOrbitsOn]
    obtain ⟨i, hi⟩ := hSnonempty
    exact Finset.card_pos.mpr ⟨lk0xpa4_orbit ρ.row.nodePerm i,
      Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hD : ρ.row.D.rZ = k0NumRhoOrbits ρ.row.rho
        ((List.range (k0DiagOf ρ.row.T).marks.length).filter
          (fun i => decide (ρ.row.s.getD i 0 > 0))) - 1 := by
    rw [ρ.row.D_eq]
    rfl
  rw [hD, hcount]
  omega

end CFSG.StandardType.GGK0ExcCentreU

end
