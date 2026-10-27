module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG

variable {X : Type*} [Group X]

theorem exists_mul_eq_isPGroup_coprime [Finite X] (g : X) {r : ℕ} (hr : r.Prime) :
    ∃ a b : X, a * b = g ∧ (∃ k : ℕ, a ^ (r ^ k) = 1) ∧ Nat.Coprime (orderOf b) r ∧
      a ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' r hr.one_lt.ne'
  have hcop : Nat.Coprime (r ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hr).mpr hm)
  set u := Nat.gcdA (r ^ e) m
  set v := Nat.gcdB (r ^ e) m
  have hbez : (r ^ e : ℤ) * u + m * v = 1 := by
    have := Nat.gcd_eq_gcd_ab (r ^ e) m
    rw [hcop.gcd_eq_one] at this
    push_cast at this
    linarith
  refine ⟨g ^ ((m : ℤ) * v), g ^ ((r ^ e : ℤ) * u), ?_, ⟨e, ?_⟩, ?_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rw [← zpow_add, add_comm, hbez, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * v * ((r ^ e : ℕ) : ℤ) =
      ((orderOf g : ℕ) : ℤ) * v by rw [hn]; push_cast; ring, zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, one_zpow]
  · have h1 : (g ^ ((r ^ e : ℤ) * u)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show (r ^ e : ℤ) * u * (m : ℤ) =
        ((orderOf g : ℕ) : ℤ) * u by rw [hn]; push_cast; ring, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
      ((Nat.Prime.coprime_iff_not_dvd hr).mpr hm).symm

theorem coprime_orderOf_of_mem_closure [Finite X] {S : Set X} {r : ℕ}
    (hS : S.Pairwise Commute) (hcop : ∀ a ∈ S, Nat.Coprime (orderOf a) r) {g : X}
    (hg : g ∈ Subgroup.closure S) : Nat.Coprime (orderOf g) r := by
  classical
  have hfin : S.Finite := Set.toFinite S
  set m := ∏ a ∈ hfin.toFinset, orderOf a
  have hm : Nat.Coprime m r := Nat.Coprime.prod_left fun a ha =>
    hcop a ((Set.Finite.mem_toFinset hfin).mp ha)
  have hcomm : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  have key : g ^ m = 1 := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      exact orderOf_dvd_iff_pow_eq_one.mp
        (Finset.dvd_prod_of_mem _ ((Set.Finite.mem_toFinset hfin).mpr hx))
    | one => exact one_pow m
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one key) hm

theorem commute_of_coprime_card [Finite X] {r : ℕ} {H : Subgroup X} (hH : H.Normal)
    [Group.IsNilpotent H] (hHr : Nat.Coprime (Nat.card H) r) {g : X}
    (hg : ∀ q : ℕ, q.Prime → q ≠ r → ∀ x ∈ pCore q X, g * x = x * g) :
    ∀ h ∈ H, g * h = h * g := by
  have htop : fittingSubgroup H = ⊤ := fitting_eq_top_of_nilpotent H
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore] at htop
  have hle : (⨆ q : (Nat.card H).primeFactors, pCore (q : ℕ) H) ≤
      (Subgroup.centralizer {g}).subgroupOf H := by
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have : Fact (q : ℕ).Prime := ⟨hq⟩
    have hqr : (q : ℕ) ≠ r := by
      intro h
      have hc : Nat.Coprime (q : ℕ) r :=
        Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors q.2) hHr
      rw [h, Nat.coprime_self] at hc
      exact hq.one_lt.ne' (h.trans hc)
    intro x hx
    have hmap : (pCore (q : ℕ) H).map H.subtype ≤ pCore (q : ℕ) X :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map H.subtype⟩
    have hxq : (x : X) ∈ pCore (q : ℕ) X := hmap ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hg q hq hqr x hxq
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈ (Subgroup.centralizer {g}).subgroupOf H := hle (htop ▸ trivial)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hmem
  exact hmem g rfl

theorem mem_centralizer_fittingSubgroup [Finite X] {y : X}
    (hy : ∀ p : ℕ, p.Prime → ∀ x ∈ pCore p X, y * x = x * y) :
    y ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
  have hle : fittingSubgroup X ≤ Subgroup.centralizer {y} := by
    rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hy p (Nat.prime_of_mem_primeFactors p.2) x hx
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp (hle hx) y rfl
  exact this.symm

theorem mem_pCore_of_mem_fittingSubgroup [Finite X] {p : ℕ} [Fact p.Prime] {y : X}
    (hy : y ∈ fittingSubgroup X) (hyp : ∃ k : ℕ, y ^ (p ^ k) = 1) : y ∈ pCore p X := by
  set F := fittingSubgroup X
  obtain ⟨k, hk⟩ := hyp
  have hk' : (⟨y, hy⟩ : F) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hpg : IsPGroup p (Subgroup.zpowers (⟨y, hy⟩ : F)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change ((⟨y, hy⟩ : F) ^ n) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hmem : y ∈ (P : Subgroup F).map F.subtype :=
    ⟨⟨y, hy⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  exact Sylow.map_le_pCore fittingSubgroup_normal fittingSubgroup_nilpotent p P hmem

section Perfect

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem pCore_le_center_of_not_le (hK : Group.IsSolvable K) (q : ℕ) [Fact q.Prime]
    (h : ¬ Subgroup.centralizer (pCore q X : Set X) ≤ K) : pCore q X ≤ Subgroup.center X := by
  have : (pCore q X).Normal := pCore_normal
  have htop := eq_top_of_not_le hK h
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (pCore q X : Set X) := by
    rw [htop]
    trivial
  exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm

end Perfect

variable [Finite X]

theorem le_fittingSubgroup_of_forall_coprime
    (hF : Subgroup.centralizer (fittingSubgroup X : Set X) ≤ fittingSubgroup X)
    {N : Subgroup X} [hN : N.Normal]
    (hcop : ∀ r : ℕ, r.Prime → ∀ y ∈ N, Nat.Coprime (orderOf y) r →
      ∀ x ∈ pCore r X, y * x = x * y) :
    N ≤ fittingSubgroup X := by
  have stepA : ∀ r : ℕ, r.Prime → ∀ y ∈ N, (∃ k : ℕ, y ^ (r ^ k) = 1) →
      y ∈ fittingSubgroup X := by
    intro r hr y hyN hyr
    have : Fact r.Prime := ⟨hr⟩
    set Sr : Set X := {g | g ∈ N ∧ ∃ k : ℕ, g ^ (r ^ k) = 1} with hSr
    set R := Subgroup.normalClosure Sr with hRdef
    have hRN : R ≤ N := Subgroup.normalClosure_le_normal fun g hg => hg.1
    have hRq : ∀ q : ℕ, q.Prime → q ≠ r → ∀ g ∈ R, ∀ x ∈ pCore q X, g * x = x * g := by
      intro q hq hqr g hg x hx
      have : Fact q.Prime := ⟨hq⟩
      have : (pCore q X).Normal := pCore_normal
      have hle : R ≤ Subgroup.centralizer (pCore q X : Set X) := by
        refine Subgroup.normalClosure_le_normal fun g' hg' => ?_
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro x' hx'
        obtain ⟨k, hk⟩ := hg'.2
        have hco : Nat.Coprime (orderOf g') q :=
          Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
            (Nat.Coprime.pow_left k ((Nat.coprime_primes hr hq).mpr hqr.symm))
        exact (hcop q hq g' hg'.1 hco x' hx').symm
      exact (Subgroup.mem_centralizer_iff.mp (hle hg) x hx).symm
    have hRcop : ∀ g ∈ R, Nat.Coprime (orderOf g) r →
        g ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      intro g hg hgr
      refine mem_centralizer_fittingSubgroup fun p hp x hx => ?_
      by_cases hpr : p = r
      · subst hpr
        exact hcop p hp g (hRN hg) hgr x hx
      · exact hRq p hp hpr g hg x hx
    have hcen : ∀ a ∈ R, Nat.Coprime (orderOf a) r → ∀ g ∈ R, g * a = a * g := by
      intro a ha har g hg
      have haC := hRcop a ha har
      set H := Subgroup.normalClosure ({a} : Set X) with hHdef
      have hHZ : H ≤ Subgroup.centralizer (fittingSubgroup X : Set X) ⊓ fittingSubgroup X :=
        Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ⟨haC, hF haC⟩)
      have hHcomm : ∀ b ∈ H, ∀ c ∈ H, Commute b c := fun b hb c hc =>
        (Subgroup.mem_centralizer_iff.mp (hHZ hb).1 c (hHZ hc).2).symm
      have hconj : ∀ b ∈ Group.conjugatesOfSet ({a} : Set X), Nat.Coprime (orderOf b) r := by
        intro b hb
        rw [Group.mem_conjugatesOfSet_iff] at hb
        obtain ⟨a', ha', hab⟩ := hb
        rw [Set.mem_singleton_iff] at ha'
        subst ha'
        obtain ⟨c, rfl⟩ := isConj_iff.mp hab
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a'
        rw [show (MulAut.conj c).toMonoidHom a' = c * a' * c⁻¹ from rfl] at this
        rw [this]
        exact har
      have hHcop : ∀ b ∈ H, Nat.Coprime (orderOf b) r := fun b hb =>
        coprime_orderOf_of_mem_closure
          (fun b₁ hb₁ b₂ hb₂ _ => hHcomm b₁ (Subgroup.conjugatesOfSet_subset_normalClosure hb₁)
            b₂ (Subgroup.conjugatesOfSet_subset_normalClosure hb₂)) hconj hb
      have hcard : Nat.Coprime (Nat.card H) r := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
        intro hdvd
        obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := H) r hdvd
        have := hHcop b b.2
        rw [Subgroup.orderOf_coe, hb, Nat.coprime_self] at this
        exact hr.one_lt.ne' this
      have hHab : IsMulCommutative H :=
        ⟨⟨fun b c => Subtype.ext (hHcomm b b.2 c c.2)⟩⟩
      have hHnil : Group.IsNilpotent H := by
        have : Subgroup.center H = ⊤ := by
          rw [eq_top_iff]
          intro b _
          rw [Subgroup.mem_center_iff]
          intro c
          exact Subtype.ext (hHcomm c c.2 b b.2)
        exact Subgroup.isNilpotent_of_ker_le_center (1 : H →* Unit)
          (by rw [this]; exact le_top)
      exact commute_of_coprime_card inferInstance hcard
        (fun q hq hqr x hx => hRq q hq hqr g hg x hx) a (Subgroup.subset_normalClosure rfl)
    let Z : Subgroup R := Subgroup.closure {g : R | Nat.Coprime (orderOf g) r}
    have hZcen : Z ≤ Subgroup.center R := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hg' : Nat.Coprime (orderOf (g : X)) r := by rwa [Subgroup.orderOf_coe]
      exact hcen g g.2 hg' h h.2
    have : Z.Normal := Subgroup.normal_of_le_center hZcen
    have hRZ : IsPGroup r (R ⧸ Z) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, b, hab, ⟨k, hk⟩, hb, -, -⟩ := exists_mul_eq_isPGroup_coprime g hr
        refine ⟨k, ?_⟩
        have hbZ : b ∈ Z := Subgroup.subset_closure hb
        rw [← hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).mpr hbZ, mul_one,
          ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    have : Group.IsNilpotent (R ⧸ Z) := hRZ.isNilpotent
    have hRnil : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']; exact hZcen)
    have hRF : R ≤ fittingSubgroup X := le_sSup ⟨inferInstance, hRnil⟩
    exact hRF (Subgroup.subset_normalClosure ⟨hyN, hyr⟩)
  set H := (fittingSubgroup X).subgroupOf N
  have hidx : H.index = 1 := by
    by_contra hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨P⟩ : Nonempty (Sylow r N) := inferInstance
    have hPH : (P : Subgroup N) ≤ H := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      apply stepA r hr g g.2
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using this
    exact P.not_dvd_index (hrd.trans (Subgroup.index_dvd_of_le hPH))
  rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hidx
  exact hidx

theorem centralizer_fittingSubgroup_le {K : Subgroup X} (hK : Group.IsSolvable K) {p : ℕ}
    [Fact p.Prime]
    (hp : Subgroup.centralizer (pCore p X : Set X) ≤ K) :
    Subgroup.centralizer (fittingSubgroup X : Set X) ≤ fittingSubgroup X := by
  set C := Subgroup.centralizer (fittingSubgroup X : Set X) with hC
  have hCK : C ≤ K := (Subgroup.centralizer_le (pCore_le_fitting X p)).trans hp
  have hCsol : Group.IsSolvable C := by
    have := hK
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCK)
  have hCC := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCsol
  have hFC : (fittingSubgroup C).map C.subtype ≤ fittingSubgroup X := by
    refine le_sSup ⟨inferInstance, ?_⟩
    exact Group.nilpotent_of_surjective (C.subtype.subgroupMap (fittingSubgroup C))
      (C.subtype.subgroupMap_surjective _)
  intro c hc
  have hmem : (⟨c, hc⟩ : C) ∈ Subgroup.centralizer (fittingSubgroup C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (f : X) (hFC ⟨f, hf, rfl⟩)
  exact hFC ⟨⟨c, hc⟩, hCC hmem, rfl⟩


end CFSG.RankThree.PartTwo.Sec4.Census
