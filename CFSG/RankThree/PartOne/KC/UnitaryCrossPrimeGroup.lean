module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open scoped commutatorElement

section Quasisimple

variable {Q G : Type*} [Group Q] [Group G]

theorem isPerfect_of_surjective (f : Q →* G) (hf : Function.Surjective f) [hP : Group.IsPerfect Q] :
    Group.IsPerfect G := by
  refine ⟨?_⟩
  have h := Subgroup.map_commutator (⊤ : Subgroup Q) ⊤ f
  rw [show ⁅(⊤ : Subgroup Q), ⊤⁆ = ⊤ from hP.commutator_eq_top,
    Subgroup.map_top_of_surjective f hf] at h
  exact h.symm

theorem isQuasisimple_of_perfect_of_simple (hP : Group.IsPerfect Q)
    (hS : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨hP, hS, ?_⟩
  by_contra! hab
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := hab
  have hP' : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    @isPerfect_of_surjective Q (Q ⧸ Subgroup.center Q) _ _ (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) hP
  have h1 : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    refine (Subgroup.commutator_le.mpr fun a _ b _ => ?_).antisymm bot_le
    rw [commutatorElement_def, hcomm a b, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h2 : commutator (Q ⧸ Subgroup.center Q) = ⊤ := hP'.commutator_eq_top
  have := hS.toNontrivial
  have : (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) ≠ ⊤ := bot_ne_top
  exact this (h1.symm.trans h2)

theorem eq_one_of_perfect_of_comm {A : Type*} [Group A] (hP : Group.IsPerfect Q)
    (hA : ∀ a b : A, a * b = b * a) (φ : Q →* A) : ∀ g, φ g = 1 := by
  have hφ : (⊤ : Subgroup Q) ≤ φ.ker := by
    rw [← hP.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hA (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro g
  exact MonoidHom.mem_ker.mp (hφ (Subgroup.mem_top g))

theorem isQuasisimple_range (hQ : CFSG.IsQuasisimple Q) (f : Q →* G)
    (hker : f.ker ≤ Subgroup.center Q) : CFSG.IsQuasisimple f.range := by
  let f' : Q →* f.range := f.rangeRestrict
  have hf' : Function.Surjective f' := f.rangeRestrict_surjective
  have hker' : f'.ker = f.ker := f.ker_rangeRestrict
  have hcen : Subgroup.center f.range = (Subgroup.center Q).map f' := by
    apply le_antisymm
    · intro j hj
      obtain ⟨g, rfl⟩ := hf' j
      refine ⟨g, ?_, rfl⟩
      have hc : ∀ g' : Q, ⁅g, g'⁆ ∈ Subgroup.center Q := fun g' => by
        apply hker
        rw [← hker', MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact (Subgroup.mem_center_iff.mp hj (f' g')).symm
      let φ : Q →* Subgroup.center Q :=
        { toFun := fun g' => ⟨⁅g, g'⁆, hc g'⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by
            change ⁅g, a * b⁆ = ⁅g, a⁆ * ⁅g, b⁆
            have h1 : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
              simp only [commutatorElement_def]; group
            have h2 : a * ⁅g, b⁆ * a⁻¹ = ⁅g, b⁆ := by
              rw [Subgroup.mem_center_iff.mp (hc b) a, mul_inv_cancel_right]
            rw [h1, h2]) }
      have hφ := eq_one_of_perfect_of_comm hQ.1
        (fun a b : Subgroup.center Q => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)) φ
      have h1 : ∀ g' : Q, ⁅g, g'⁆ = 1 := fun g' => congrArg Subtype.val (hφ g')
      show g ∈ Subgroup.center Q
      rw [Subgroup.mem_center_iff]
      intro g'
      exact (commutatorElement_eq_one_iff_commute.mp (h1 g')).symm.eq
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro j
      obtain ⟨g, rfl⟩ := hf' j
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  have hmap : Subgroup.center Q ≤ (Subgroup.center f.range).comap f' := fun z hz => by
    rw [Subgroup.mem_comap, hcen]
    exact Subgroup.mem_map_of_mem _ hz
  let ψ : Q ⧸ Subgroup.center Q →* f.range ⧸ Subgroup.center f.range :=
    QuotientGroup.map (Subgroup.center Q) (Subgroup.center f.range) f' hmap
  have hψ : Function.Bijective ψ := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
      have h1 : f' g ∈ Subgroup.center f.range := (QuotientGroup.eq_one_iff _).mp hu
      rw [hcen] at h1
      obtain ⟨z, hz, hzg⟩ := h1
      have h2 : g ∈ Subgroup.center Q := by
        have h3 : z⁻¹ * g ∈ f'.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzg, inv_mul_cancel]
        have h4 : g = z * (z⁻¹ * g) := by group
        rw [h4]
        exact mul_mem hz (hker (hker' ▸ h3))
      exact (QuotientGroup.eq_one_iff _).mpr h2
    · intro v
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨g, rfl⟩ := hf' j
      exact ⟨g, rfl⟩
  have : Group.IsPerfect Q := hQ.1
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  exact isQuasisimple_of_perfect_of_simple (isPerfect_of_surjective f' hf')
    (MulEquiv.ofBijective ψ hψ).symm.isSimpleGroup

end Quasisimple

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_of_normal_chain {C M J : Subgroup G} (hJM : J ≤ M)
    (hJ : (J.subgroupOf M).Normal) (hM : (M.subgroupOf C).Normal) :
    (J.subgroupOf C).IsSubnormal := by
  refine Subgroup.IsSubnormal.step (J.subgroupOf C) (M.subgroupOf C)
    (fun g hg => hJM hg) hM.isSubnormal ?_
  refine ⟨fun n hn g => ?_⟩
  have hnJ : ((n : C) : G) ∈ J := hn
  have hnM : ((n : C) : G) ∈ M := n.2
  have hgM : ((g : C) : G) ∈ M := g.2
  have h1 := hJ.conj_mem ⟨((n : C) : G), hnM⟩ hnJ ⟨((g : C) : G), hgM⟩
  exact h1

end Subnormal

section Core

variable {G : Type*} [Group G] [Finite G]

theorem commute_of_isComponent_core {p : ℕ} (hp : p.Prime) {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : CFSG.IsComponent (J.subgroupOf C)) {j s : G} (hj : j ∈ J)
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p) C) :
    Commute j s := by
  have hcore := CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := C) hp
  have hsub : (CFSG.RankThree.LocalRank.aschbacherSolvableCore p C).IsSubnormal :=
    (inferInstance : (CFSG.RankThree.LocalRank.aschbacherSolvableCore p C).Normal).isSubnormal
  have h1 := (CFSG.LocalCores.component_solvable_centralizer hcore.1 hsub).1 _ hJ
  obtain ⟨s', hs', rfl⟩ := hs
  have h2 : ⁅(⟨j, hJC hj⟩ : C), s'⁆ = 1 := by
    have := Subgroup.commutator_le.mp h1.le ⟨j, hJC hj⟩ hj s' hs'
    simpa using this
  have h3 := congrArg Subtype.val h2
  exact commutatorElement_eq_one_iff_commute.mp h3

end Core

section Commutators

variable {G : Type*} [Group G]

theorem commutator_eq_of_isPerfect {H : Subgroup G} (hH : Group.IsPerfect H) : ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, hH.commutator_eq_top, Subgroup.map_top,
    Subgroup.range_subtype]

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun _ ha _ hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem conj_mem_commutator_self {H : Subgroup G} {g : G} (hg : g ∈ H) {y : G}
    (hy : y ∈ ⁅H, H⁆) : g * y * g⁻¹ ∈ ⁅H, H⁆ := by
  rw [← Subgroup.map_subtype_commutator] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹,
    (inferInstance : (commutator H).Normal).conj_mem y' hy' ⟨g, hg⟩, rfl⟩

theorem commutator_iSup_commuting {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) :
    ⁅(⨆ i, A i), (⨆ i, A i)⁆ = ⨆ i, ⁅A i, A i⁆ := by
  apply le_antisymm
  · set P : Subgroup G := ⨆ i, ⁅A i, A i⁆ with hP
    have hP1 : ∀ i, ⁅A i, A i⁆ ≤ P := fun i => le_iSup (fun i => ⁅A i, A i⁆) i
    have hconjA : ∀ j, ∀ g ∈ A j, ∀ y ∈ P, g * y * g⁻¹ ∈ P := by
      intro j g hg y hy
      refine Subgroup.iSup_induction (fun i => ⁅A i, A i⁆) (C := fun y => g * y * g⁻¹ ∈ P) hy
        ?_ ?_ ?_
      · intro i y hy
        by_cases hij : j = i
        · subst hij
          exact hP1 j (conj_mem_commutator_self hg hy)
        · have hyA : y ∈ A i := commutator_self_le (A i) hy
          have : g * y * g⁻¹ = y := by
            rw [(hc j i hij g hg y hyA).eq, mul_inv_cancel_right]
          rw [this]
          exact hP1 i hy
      · simp
      · intro u v hu hv
        have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
        rw [this]
        exact mul_mem hu hv
    have hconjM : ∀ m ∈ ⨆ i, A i, ∀ y ∈ P, m * y * m⁻¹ ∈ P := by
      intro m hm
      refine Subgroup.iSup_induction' A (C := fun m _ => ∀ y ∈ P, m * y * m⁻¹ ∈ P) ?_ ?_ ?_ hm
      · intro j g hg y hy
        exact hconjA j g hg y hy
      · intro y hy
        simpa using hy
      · intro u v _ _ hu hv y hy
        have : u * v * y * (u * v)⁻¹ = u * (v * y * v⁻¹) * u⁻¹ := by group
        rw [this]
        exact hu _ (hv y hy)
    refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
    refine Subgroup.iSup_induction' A (C := fun g _ => ∀ g' ∈ ⨆ i, A i, ⁅g, g'⁆ ∈ P) ?_ ?_ ?_
      hg g' hg'
    · intro i g hgi g' hg'
      refine Subgroup.iSup_induction' A (C := fun g' _ => ⁅g, g'⁆ ∈ P) ?_ ?_ ?_ hg'
      · intro j g' hg'j
        by_cases hij : i = j
        · subst hij
          exact hP1 i (Subgroup.commutator_mem_commutator hgi hg'j)
        · have : ⁅g, g'⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_commute]
            exact hc i j hij g hgi g' hg'j
          rw [this]
          exact one_mem _
      · simp
      · intro u v hu _ hPu hPv
        have : ⁅g, u * v⁆ = ⁅g, u⁆ * (u * ⁅g, v⁆ * u⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact mul_mem hPu (hconjM u hu _ hPv)
    · intro g' hg'
      simp
    · intro u v hu hv hPu hPv g' hg'
      have : ⁅u * v, g'⁆ = u * ⁅v, g'⁆ * u⁻¹ * ⁅u, g'⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem (hconjM u hu _ (hPv g' hg')) (hPu g' hg')
  · exact iSup_le fun i => Subgroup.commutator_mono (le_iSup A i) (le_iSup A i)

theorem commutator_eq_one_of_central {F Z : Subgroup G} (Y : G) (hF : Group.IsPerfect F)
    (hZ : ∀ z ∈ Z, ∀ g : G, Commute z g) (h : ∀ g ∈ F, ⁅Y, g⁆ ∈ Z) :
    ∀ g ∈ F, ⁅Y, g⁆ = 1 := by
  let φ : F →* Z :=
    { toFun := fun g => ⟨⁅Y, (g : G)⁆, h g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅Y, ((a * b : F) : G)⁆ = ⁅Y, (a : G)⁆ * ⁅Y, (b : G)⁆
        have h1 : ⁅Y, (a : G) * (b : G)⁆ = ⁅Y, (a : G)⁆ * ((a : G) * ⁅Y, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]; group
        have h2 : (a : G) * ⁅Y, (b : G)⁆ * (a : G)⁻¹ = ⁅Y, (b : G)⁆ := by
          rw [(hZ _ (h b b.2) (a : G)).eq.symm, mul_inv_cancel_right]
        rw [Subgroup.coe_mul, h1, h2]) }
  have hφ := eq_one_of_perfect_of_comm hF
    (fun a b : Z => Subtype.ext (hZ _ a.2 (b : G)).eq) φ
  intro g hg
  exact congrArg Subtype.val (hφ ⟨g, hg⟩)

end Commutators

section OddPart

variable {Γ : Type*} [Group Γ]

@[expose] def oddOrderSubgroup (Q : Subgroup Γ) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, Commute x y) :
    Subgroup Γ where
  carrier := {z | z ∈ Q ∧ Odd (orderOf z)}
  mul_mem' := by
    rintro a b ⟨haQ, hao⟩ ⟨hbQ, hbo⟩
    refine ⟨mul_mem haQ hbQ, ?_⟩
    have hdvd := (hQ a haQ b hbQ).orderOf_mul_dvd_lcm
    exact Odd.of_dvd_nat (Odd.of_dvd_nat (hao.mul hbo) (Nat.lcm_dvd_mul _ _)) hdvd
  one_mem' := ⟨one_mem Q, by simp⟩
  inv_mem' := by
    rintro a ⟨haQ, hao⟩
    exact ⟨inv_mem haQ, by rwa [orderOf_inv]⟩

theorem mem_oddOrderSubgroup {Q : Subgroup Γ} {hQ : ∀ x ∈ Q, ∀ y ∈ Q, Commute x y} {z : Γ} :
    z ∈ oddOrderSubgroup Q hQ ↔ z ∈ Q ∧ Odd (orderOf z) := Iff.rfl

theorem odd_card_of_forall_odd_orderOf (H : Subgroup Γ) [Finite H]
    (h : ∀ z ∈ H, Odd (orderOf z)) : Odd (Nat.card H) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card H := by
    rcases Nat.even_or_odd (Nat.card H) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have := h (z : Γ) z.2
  rw [Subgroup.orderOf_coe, hz] at this
  exact absurd this (by decide)

theorem odd_orderOf_of_fixed_two_part (σ : MulAut Γ) (Q : Subgroup Γ) [Finite Q]
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, Commute x y) (hσQ : ∀ z ∈ Q, σ z ∈ Q)
    (hfix : ∀ z ∈ Q, ∀ k : ℕ, z ^ 2 ^ k = 1 → σ z = z)
    {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1) (s : Γ) (hc : s * (σ s)⁻¹ ∈ Q) :
    Odd (orderOf (s * (σ s)⁻¹)) := by
  set c := s * (σ s)⁻¹ with hcdef
  have hσpowQ : ∀ (k : ℕ), ∀ z ∈ Q, (σ ^ k) z ∈ Q := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hσQ z hz)
  have hfin : IsOfFinOrder (⟨c, hc⟩ : Q) := isOfFinOrder_of_finite _
  have hord : orderOf c ≠ 0 := by
    have h1 := hfin.orderOf_pos
    rw [Subgroup.orderOf_mk] at h1
    exact h1.ne'
  obtain ⟨e, o, ho, hn⟩ := Nat.exists_eq_two_pow_mul_odd hord
  set z := c ^ o with hz
  have hzQ : z ∈ Q := Subgroup.pow_mem Q hc o
  have hz2 : z ^ 2 ^ e = 1 := by
    rw [hz, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hσz : ∀ k : ℕ, (σ ^ k) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hfix z hzQ e hz2, ih]
  set d : ℕ → Γ := fun k => s * ((σ ^ k) s)⁻¹ with hd
  have hd0 : d 0 = 1 := by simp [hd]
  have hdsucc : ∀ k, d (k + 1) = d k * (σ ^ k) c := by
    intro k
    simp only [hd, hcdef, pow_succ, MulAut.mul_apply, map_mul, map_inv]
    group
  have hdQ : ∀ k, d k ∈ Q := by
    intro k
    induction k with
    | zero => rw [hd0]; exact one_mem Q
    | succ k ih => rw [hdsucc]; exact mul_mem ih (hσpowQ k c hc)
  have hdpow : ∀ k, d k ^ o = z ^ k := by
    intro k
    induction k with
    | zero => simp [hd0]
    | succ k ih =>
      rw [hdsucc, (hcomm _ (hdQ k) _ (hσpowQ k c hc)).mul_pow, ih, ← map_pow, ← hz, hσz,
        pow_succ]
  have hdm : d m = 1 := by simp [hd, hσm]
  have hzm : z ^ m = 1 := by rw [← hdpow, hdm, one_pow]
  have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
    have h2 : orderOf z ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hz2
    have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp this
  have hco : c ^ o = 1 := hz1
  exact Odd.of_dvd_nat ho (orderOf_dvd_of_pow_eq_one hco)

end OddPart

end CFSG.RankThree.PartOne.KCUnitary
