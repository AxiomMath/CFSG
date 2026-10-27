module

public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.ChainArrays

theorem card_le_of_orbit_subset {G α : Type*} [Group G] [MulAction G α] [Finite G]
    (K : Subgroup G) (b : α) (L : List α) (hL : ∀ g ∈ K, g • b ∈ L) :
    Nat.card K ≤ L.length * Nat.card (K ⊓ MulAction.stabilizer G b : Subgroup G) := by
  classical
  have h1 := (MulAction.stabilizer K b).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have horb : (MulAction.orbit K b).ncard ≤ L.length := by
    calc (MulAction.orbit K b).ncard ≤ ((L.toFinset : Set α)).ncard := by
          apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
          rintro _ ⟨g, rfl⟩
          rw [Finset.mem_coe, List.mem_toFinset]
          exact hL g g.2
      _ = L.toFinset.card := Set.ncard_coe_finset _
      _ ≤ L.length := List.toFinset_card_le L
  have hstab : Nat.card (MulAction.stabilizer K b) ≤
      Nat.card (K ⊓ MulAction.stabilizer G b : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun s => ⟨((s : K) : G), (s : K).2, MulAction.mem_stabilizer_iff.2 ?_⟩) ?_
    · exact MulAction.mem_stabilizer_iff.1 s.2
    · intro s t hst
      have h' : ((s : K) : G) = ((t : K) : G) :=
        congrArg (fun y : (K ⊓ MulAction.stabilizer G b : Subgroup G) => (y : G)) hst
      exact Subtype.ext (Subtype.ext h')
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul horb hstab

theorem card_centralizer_inf_conj {G : Type*} [Group G] (P : Subgroup G) {g x y : G}
    (hg : g ∈ P) (h : g * y * g⁻¹ = x) :
    Nat.card (Subgroup.centralizer {y} ⊓ P : Subgroup G) =
      Nat.card (Subgroup.centralizer {x} ⊓ P : Subgroup G) := by
  subst h
  refine Nat.card_congr
    { toFun := fun c => ⟨g * c * g⁻¹,
        Subgroup.mem_inf.2 ⟨?_, P.mul_mem (P.mul_mem hg (Subgroup.mem_inf.1 c.2).2)
          (P.inv_mem hg)⟩⟩
      invFun := fun c => ⟨g⁻¹ * c * g,
        Subgroup.mem_inf.2 ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hg)
          (Subgroup.mem_inf.1 c.2).2) hg⟩⟩
      left_inv := fun c => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc]) }
  · have hc : (c : G) * y = y * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group
  · have hc : (c : G) * (g * y * g⁻¹) = g * y * g⁻¹ * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * c) * g := by rw [hc]
      _ = y * (g⁻¹ * c * g) := by group

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem exists_levT_inv_mul_mem {i : ℕ} (hi : i < Q.baseCount) {h : Equiv.Perm (Fin n)}
    (hh : h ∈ Q.levelSubgroup i) :
    ∃ k < (lev n S base i).pts.size,
      (lev n S base i).pts[k]! = (h (Q.base.get ⟨i, hi⟩) : ℕ) ∧
      (levT n S base i k)⁻¹ * h ∈ Q.levelSubgroup (i + 1) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  have hx : h b ∈ Q.orbitPoints ⟨i, hi⟩ := by
    rw [Q.orbitPoints_eq_orbit]
    exact ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨hk, hpts, ht⟩ := hA.orbitPoints_spec hF hi hx
  obtain ⟨-, hmem, hval⟩ := Q.transversal_getD_spec ⟨i, hi⟩ (h b) hx
  rw [ht] at hmem hval
  have hptsv := hA.levPts_val hF hi hk
  rw [hpts] at hptsv
  set t := levT n S base i (lev n S base i).pos[((h b : Fin n) : ℕ)]! with htdef
  refine ⟨_, hk, hptsv.symm, ?_⟩
  rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩]
  refine Subgroup.mem_inf.2
    ⟨(Q.levelSubgroup i).mul_mem ((Q.levelSubgroup i).inv_mem hmem) hh, ?_⟩
  have htb : t b = h b := hval
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
  change t⁻¹ (h b) = b
  rw [← htb]
  simp

end Facts

@[expose] def commA (n : ℕ) (p x : Array ℕ) : Bool := eqA n (compA n p x) (compA n x p)

theorem commA_iff {p x : Array ℕ} {P X : Equiv.Perm (Fin n)} (hp : Rep n p P) (hx : Rep n x X) :
    commA n p x = true ↔ P * X = X * P :=
  eqA_iff (rep_compA hp hx) (rep_compA hx hp)

@[expose] def tailOK (n : ℕ) (L : Array Level) (x : Array ℕ) (E : List (Array ℕ)) :
    ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => !(commA n acc x) || E.any (eqA n acc)
  | fuel + 1, i, acc =>
    allLt (L[i]!).pts.size fun k => tailOK n L x E fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem tailOK_spec {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {E : List (Array ℕ)} :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      tailOK n (rawLevels n S base) x E fuel i acc = true →
      ∀ h ∈ Q.levelSubgroup i, A * h * X = X * (A * h) → ∃ e ∈ E, Rep n e (A * h) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc A hacc htail h hh hcomm
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot] at hh
    subst hh
    rw [mul_one] at hcomm ⊢
    have hc : commA n acc x = true := (commA_iff hacc hx).2 hcomm
    simp only [tailOK, hc, Bool.not_true, Bool.false_or, List.any_eq_true] at htail
    obtain ⟨e, he, heq⟩ := htail
    exact ⟨e, he, rep_of_eqA hacc heq⟩
  | succ fuel ih =>
    intro i hi acc A hacc htail h hh hcomm
    have hib : i < Q.baseCount := by omega
    obtain ⟨k, hk, -, hk'⟩ := exists_levT_inv_mul_mem hA hF hQ hib hh
    have hstep := allLt_spec htail hk
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have e : A * h = A * levT n S base i k * ((levT n S base i k)⁻¹ * h) := by group
    rw [e] at hcomm ⊢
    exact ih (i + 1) (by omega) _ _ hrep hstep _ hk' hcomm

theorem card_centralizer_inf_levelSubgroup_le_of_tailOK {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {m : ℕ} (hm : m ≤ Q.baseCount) {E : List (Array ℕ)}
    (htail : tailOK n (rawLevels n S base) x E (Q.baseCount - m) m (idA n) = true) :
    Nat.card (Subgroup.centralizer {X} ⊓ Q.levelSubgroup m : Subgroup (Equiv.Perm (Fin n))) ≤
      E.length := by
  classical
  set K := (Subgroup.centralizer {X} ⊓ Q.levelSubgroup m : Subgroup (Equiv.Perm (Fin n)))
  have hsub : (K : Set (Equiv.Perm (Fin n))) ⊆ (permOfArr n) '' (E.toFinset : Set (Array ℕ)) := by
    intro g hg
    obtain ⟨hgc, hgm⟩ := hg
    have hcomm : 1 * g * X = X * (1 * g) := by
      rw [one_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgc
    obtain ⟨e, he, hre⟩ := tailOK_spec hA hF hQ hx (Q.baseCount - m) m (by omega) (idA n) 1
      rep_idA htail g hgm hcomm
    rw [one_mul] at hre
    exact ⟨e, by simpa using he, permOfArr_eq_of_rep hre⟩
  calc Nat.card K = (K : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ((permOfArr n) '' (E.toFinset : Set (Array ℕ))).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (E.toFinset : Set (Array ℕ)).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = E.toFinset.card := Set.ncard_coe_finset _
    _ ≤ E.length := List.toFinset_card_le E

end Facts

@[expose] def fixLevList (n : ℕ) (L : Array Level) (x : Array ℕ) (i : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun q =>
    x[(q : ℕ)]! == (q : ℕ) && decide ((L[i]!).pos[(q : ℕ)]! < (L[i]!).pts.size)

@[expose] def fixLevCount (n : ℕ) (L : Array Level) (x : Array ℕ) (i : ℕ) : ℕ :=
  (fixLevList n L x i).length

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem card_centralizer_inf_levelSubgroup_le {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {i : ℕ} (hi : i < Q.baseCount)
    (hfix : X (Q.base.get ⟨i, hi⟩) = Q.base.get ⟨i, hi⟩) :
    Nat.card (Subgroup.centralizer {X} ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n))) ≤
      fixLevCount n (rawLevels n S base) x i *
        Nat.card (Subgroup.centralizer {X} ⊓ Q.levelSubgroup (i + 1) :
          Subgroup (Equiv.Perm (Fin n))) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  set K := (Subgroup.centralizer {X} ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n)))
  have hL : ∀ g ∈ K, g • b ∈ fixLevList n (rawLevels n S base) x i := by
    intro g hg
    obtain ⟨hgc, hgi⟩ := hg
    rw [fixLevList, List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    rw [Equiv.Perm.smul_def, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    have hcomm : g * X = X * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    have horb : g b ∈ Q.orbitPoints ⟨i, hi⟩ := by
      rw [Q.orbitPoints_eq_orbit]
      exact ⟨⟨g, hgi⟩, rfl⟩
    refine ⟨?_, (hA.orbitPoints_spec hF hi horb).1⟩
    rw [hx (g b)]
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ b) hcomm
    simp only [Equiv.Perm.mul_apply, hfix] at this
    rw [← this]
  have h := card_le_of_orbit_subset K b _ hL
  have hstab : (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b : Subgroup _) =
      Subgroup.centralizer {X} ⊓ Q.levelSubgroup (i + 1) := by
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩, inf_assoc]
  rw [hstab] at h
  exact h

end Facts

@[expose] def relImg (base : Array ℕ) (i : ℕ) (acc : Array ℕ) (q m : ℕ) : ℕ :=
  if m < i then acc[base[m]!]! else acc[q]!

@[expose] def relOK (base : Array ℕ) (xs : Array (Array ℕ)) (rels : List (ℕ × ℕ × ℕ)) (i : ℕ)
    (acc : Array ℕ) (q : ℕ) : Bool :=
  rels.all fun r => !(decide (max r.1 r.2.1 = i)) ||
    relImg base i acc q r.2.1 == (xs[r.2.2]!)[relImg base i acc q r.1]!

@[expose] def ptailOK (n : ℕ) (L : Array Level) (base : Array ℕ) (x : Array ℕ)
    (xs : Array (Array ℕ)) (rels : List (ℕ × ℕ × ℕ)) (E : List (Array ℕ)) :
    ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => !(commA n acc x) || E.any (eqA n acc)
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOK base xs rels i acc (L[i]!).pts[k]!) ||
        ptailOK n L base x xs rels E fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem ptailOK_spec {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    {xs : Array (Array ℕ)} (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e))
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {E : List (Array ℕ)} :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      ptailOK n (rawLevels n S base) base x xs rels E fuel i acc = true →
      ∀ h ∈ Q.levelSubgroup i, A * h * X = X * (A * h) → ∃ e ∈ E, Rep n e (A * h) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc A hacc htail h hh hcomm
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot] at hh
    subst hh
    rw [mul_one] at hcomm ⊢
    have hc : commA n acc x = true := (commA_iff hacc hx).2 hcomm
    simp only [ptailOK, hc, Bool.not_true, Bool.false_or, List.any_eq_true] at htail
    obtain ⟨e, he, heq⟩ := htail
    exact ⟨e, he, rep_of_eqA hacc heq⟩
  | succ fuel ih =>
    intro i hi acc A hacc htail h hh hcomm
    have hib : i < Q.baseCount := by omega
    obtain ⟨k, hk, hpt, hk'⟩ := exists_levT_inv_mul_mem hA hF hQ hib hh
    have hstep := allLt_spec htail hk
    have hcX : Commute (A * h) X := hcomm
    have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
      fun m hm => hA.base_val ⟨m, hm⟩
    have himg : ∀ m (hm : m ≤ i), relImg base i acc ((rawLevels n S base)[i]!).pts[k]! m =
        ((A * h) (Q.base.get ⟨m, by omega⟩) : ℕ) := by
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hlt | rfl
      · rw [relImg, ite_eq_left hlt, ← hbase m (by omega), hacc, Equiv.Perm.mul_apply,
          Q.levelSubgroup_fixes_base_index i h hh ⟨m, by omega⟩ hlt]
      · rw [relImg, ite_eq_right (lt_irrefl _), show ((rawLevels n S base)[m]!).pts[k]! =
          (lev n S base m).pts[k]! from rfl, hpt, hacc, Equiv.Perm.mul_apply]
    have hrel : relOK base xs rels i acc ((rawLevels n S base)[i]!).pts[k]! = true := by
      rw [relOK, List.all_eq_true]
      intro r hr
      obtain ⟨he, hl, hl', hrx⟩ := hrels r hr
      rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
      by_cases hmax : max r.1 r.2.1 = i
      · right
        have hl1 : r.1 ≤ i := hmax ▸ le_max_left _ _
        have hl2 : r.2.1 ≤ i := hmax ▸ le_max_right _ _
        have hbs := hA.base_size
        have hXe : (X ^ r.2.2) (Q.base.get ⟨r.1, by omega⟩) = Q.base.get ⟨r.2.1, by omega⟩ := by
          apply Fin.ext
          rw [← hxs r.2.2 he, hbase r.1 (by omega), hbase r.2.1 (by omega), hrx]
        rw [himg r.2.1 hl2, himg r.1 hl1, hxs r.2.2 he, ← hXe]
        congr 1
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, (hcX.pow_right r.2.2).eq]
      · exact Or.inl hmax
    rw [hrel, Bool.not_true, Bool.false_or] at hstep
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have e : A * h = A * levT n S base i k * ((levT n S base i k)⁻¹ * h) := by group
    rw [e] at hcomm ⊢
    exact ih (i + 1) (by omega) _ _ hrep hstep _ hk' hcomm

theorem centralizer_subset_of_ptailOK {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    {xs : Array (Array ℕ)} (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e))
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {E : List (Array ℕ)}
    (htail : ptailOK n (rawLevels n S base) base x xs rels E Q.baseCount 0 (idA n) = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.centralizer {X} ⊓ Q.originalSubgroup) :
    ∃ e ∈ E, Rep n e g := by
  obtain ⟨hgc, hgP⟩ := Subgroup.mem_inf.1 hg
  rw [← Q.levelSubgroup_zero_eq_original hQ] at hgP
  have hcomm : 1 * g * X = X * (1 * g) := by
    rw [one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hgc
  obtain ⟨e, he, hre⟩ := ptailOK_spec hA hF hQ hx hxs hrels Q.baseCount 0 (by omega) (idA n) 1
    rep_idA htail g hgP hcomm
  rw [one_mul] at hre
  exact ⟨e, he, hre⟩

end Facts

end CFSG.RankThree.Native
