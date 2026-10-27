module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

section Helpers

variable {X : Type} [Group X] [Finite X]

theorem uc22pws_exists_mul_of_mem_sup {H K : Subgroup X} (hHK : H ≤ normalizer (K : Set X)) {x : X}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := fun h hh k hk =>
    (mem_normalizer_iff.1 (hHK hh) k).1 hk
  let S : Subgroup X :=
    { carrier := {z | ∃ h ∈ H, ∃ k ∈ K, z = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', h'⁻¹ * k * h'⁻¹⁻¹ * k',
          K.mul_mem (hconj h'⁻¹ (H.inv_mem hh') k hk) hk', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, hconj h hh k⁻¹ (K.inv_mem hk), by group⟩ }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩)
  exact hle hx

theorem uc22pws_le_normalizer {E H K : Subgroup X} (hEab : IsMulCommutative E) (hH : H ≤ E)
    (hK : K ≤ E) : H ≤ normalizer (K : Set X) := by
  haveI := hEab
  exact fun h hh => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
    mul_comm_of_mem_isMulCommutative E (hK hk) (hH hh))

theorem uc22pws_isMulCommutative_of_le {E H : Subgroup X} (hEab : IsMulCommutative E) (h : H ≤ E) :
    IsMulCommutative H := by
  haveI := hEab
  exact IsMulCommutative.of_comm fun a b =>
    Subtype.ext (mul_comm_of_mem_isMulCommutative E (h a.2) (h b.2))

theorem uc22pws_pow_card {H : Subgroup X} {x : X} (hx : x ∈ H) : x ^ Nat.card H = 1 :=
  congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))

theorem uc22pws_eq_one_of_mem_inf {U E : Subgroup X} (hU2 : IsPGroup 2 U) (hEodd : Odd (Nat.card E))
    {x : X} (hxE : x ∈ E) (hxU : x ∈ U) : x = 1 := by
  obtain ⟨k, hk⟩ := hU2 ⟨x, hxU⟩
  have h1 : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : x ^ Nat.card E = 1 := uc22pws_pow_card hxE
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hEodd)).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem uc22pws_pow_mul {U : Subgroup X} {y : X} (hy : y ∈ normalizer (U : Set X)) {u : X}
    (hu : u ∈ U) (m : ℕ) : ∃ u' ∈ U, (y * u) ^ m = y ^ m * u' := by
  induction m with
  | zero => exact ⟨1, U.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨u', hu', h⟩ := ih
    have hc : y⁻¹ * u' * y ∈ U := by
      simpa using (mem_normalizer_iff.1 (inv_mem hy) u').1 hu'
    refine ⟨y⁻¹ * u' * y * u, U.mul_mem hc hu, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem uc22pws_isPGroup_zpowers {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {g : G} {k : ℕ}
    (hg : g ^ (p ^ k) = 1) : IsPGroup p (zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem uc22pws_mem_pCoreOf_iff {p : ℕ} (hp : p.Prime) {H : Subgroup X} (hH : IsMulCommutative H)
    {x : X} : x ∈ pCoreOf p H ↔ x ∈ H ∧ ∃ k : ℕ, x ^ (p ^ k) = 1 := by
  haveI := hH
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := H)) ⟨y, hy⟩
    exact ⟨y.2, k, by simpa using congrArg Subtype.val (congrArg Subtype.val hk)⟩
  · rintro ⟨hxH, k, hk⟩
    have hg : (⟨x, hxH⟩ : H) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    have hle : zpowers (⟨x, hxH⟩ : H) ≤ CFSG.pCore p H :=
      le_sSup ⟨inferInstance, uc22pws_isPGroup_zpowers hp hg⟩
    exact ⟨⟨x, hxH⟩, hle (mem_zpowers _), rfl⟩

theorem uc22pws_exists_orderOf {H : Subgroup X} {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card H) :
    ∃ y ∈ H, orderOf y = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem uc22pws_of_orderOf {p : ℕ} (hp : p.Prime) {y : X} (hy : orderOf y = p) :
    y ≠ 1 ∧ y ^ (p ^ 1) = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hy
    exact hp.one_lt.ne hy
  · rw [pow_one, ← hy]
    exact pow_orderOf_eq_one y

@[expose] def uc22pwsInv (U : Subgroup X) (Φ : Set (MulAut X)) (W : Subgroup X) : Prop :=
  ∀ φ ∈ Φ, ∀ x ∈ W, φ x ∈ W ⊔ U

theorem uc22pws_inv_bot (U : Subgroup X) (Φ : Set (MulAut X)) : uc22pwsInv U Φ ⊥ := by
  intro φ _ x hx
  rw [Subgroup.mem_bot.1 hx, map_one]
  exact one_mem _

theorem uc22pws_inv_biSup {U : Subgroup X} {Φ : Set (MulAut X)} (S : Finset ℕ) (F : ℕ → Subgroup X)
    (h : ∀ q ∈ S, uc22pwsInv U Φ (F q)) : uc22pwsInv U Φ (⨆ q ∈ S, F q) := by
  intro φ hφ x hx
  have hle : (⨆ q ∈ S, F q) ≤ ((⨆ q ∈ S, F q) ⊔ U).comap φ.toMonoidHom := by
    refine iSup₂_le fun q hq y hy => ?_
    exact Subgroup.mem_comap.2
      (sup_le_sup_right (le_iSup₂ (f := fun q _ => F q) q hq) U (h q hq φ hφ y hy))
  exact Subgroup.mem_comap.1 (hle hx)

theorem uc22pws_inv_pCoreOf {U E : Subgroup X} (hEU : E ≤ normalizer (U : Set X)) (hU2 : IsPGroup 2 U)
    (hEab : IsMulCommutative E) (hEodd : Odd (Nat.card E)) {Φ : Set (MulAut X)}
    (hΦE : ∀ φ ∈ Φ, ∀ x ∈ E, φ x ∈ E ⊔ U) {p : ℕ} (hp : p.Prime) :
    uc22pwsInv U Φ (pCoreOf p E) := by
  intro φ hφ x hx
  obtain ⟨hxE, k, hk⟩ := (uc22pws_mem_pCoreOf_iff hp hEab).1 hx
  obtain ⟨y, hy, u, hu, hyu⟩ := uc22pws_exists_mul_of_mem_sup hEU (hΦE φ hφ x hxE)
  have h1 : (y * u) ^ (p ^ k) = 1 := by rw [← hyu, ← map_pow, hk, map_one]
  obtain ⟨u', hu', h2⟩ := uc22pws_pow_mul (hEU hy) hu (p ^ k)
  rw [h2] at h1
  have h3 : y ^ (p ^ k) = 1 :=
    uc22pws_eq_one_of_mem_inf hU2 hEodd (E.pow_mem hy _)
      (by rw [eq_inv_of_mul_eq_one_left h1]; exact U.inv_mem hu')
  have hyp : y ∈ pCoreOf p E := (uc22pws_mem_pCoreOf_iff hp hEab).2 ⟨hy, k, h3⟩
  rw [hyu]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyp) (Subgroup.mem_sup_right hu)

theorem uc22pws_exists_min {U : Subgroup X} {Φ : Set (MulAut X)} {A : Subgroup X}
    (hA : uc22pwsInv U Φ A) :
    ∃ F : Subgroup X, F ≤ A ∧ uc22pwsInv U Φ F ∧ (A ≠ ⊥ → F ≠ ⊥) ∧
      ∀ W : Subgroup X, W ≤ F → uc22pwsInv U Φ W → W = ⊥ ∨ W = F := by
  by_cases hA0 : A = ⊥
  · exact ⟨⊥, bot_le, uc22pws_inv_bot U Φ, fun h => absurd hA0 h,
      fun W hW _ => Or.inl (le_bot_iff.1 hW)⟩
  · have hne : {W : Subgroup X | W ≤ A ∧ W ≠ ⊥ ∧ uc22pwsInv U Φ W}.Nonempty := ⟨A, le_rfl, hA0, hA⟩
    obtain ⟨F, ⟨hFA, hF0, hFi⟩, hmin⟩ :=
      (InvImage.wf (fun W : Subgroup X => Nat.card W) wellFounded_lt).has_min _ hne
    refine ⟨F, hFA, hFi, fun _ => hF0, fun W hWF hWi => ?_⟩
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · exact Or.inr (eq_of_le_of_card_ge hWF
        (not_lt.1 (hmin W ⟨hWF.trans hFA, hW0, hWi⟩)))

@[expose] def uc22pwsFam (E : Subgroup X) (F : ℕ → Subgroup X) (S : Finset ℕ) : Prop :=
  ∀ q ∈ S, q.Prime ∧ F q ≤ E ∧ ∀ x ∈ F q, ∃ k : ℕ, x ^ (q ^ k) = 1

theorem uc22pws_torsion {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    (S : Finset ℕ) (hS : uc22pwsFam E F S) {p : ℕ} (hp : p.Prime) {x : X}
    (hx : x ∈ ⨆ q ∈ S, F q) {k : ℕ} (hk : x ^ (p ^ k) = 1) :
    (p ∈ S → x ∈ F p) ∧ (p ∉ S → x = 1) := by
  suffices H : ∀ S : Finset ℕ, uc22pwsFam E F S → ∀ p : ℕ, p.Prime → ∀ x : X,
      x ∈ ⨆ q ∈ S, F q → ∀ k : ℕ, x ^ (p ^ k) = 1 → (p ∈ S → x ∈ F p) ∧ (p ∉ S → x = 1) from
    H S hS p hp x hx k hk
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ p _ x hx k _
    have hx1 : x = 1 := by simpa using hx
    exact ⟨fun h => absurd h (Finset.notMem_empty _), fun _ => hx1⟩
  | insert q S hqS ih =>
    intro hS p hp x hx k hk
    obtain ⟨hqp, hqE, hqg⟩ := hS q (Finset.mem_insert_self q S)
    have hS' : uc22pwsFam E F S := fun q' hq' => hS q' (Finset.mem_insert_of_mem hq')
    have hJE : (⨆ q' ∈ S, F q') ≤ E := iSup₂_le fun q' hq' => (hS' q' hq').2.1
    rw [Finset.iSup_insert] at hx
    obtain ⟨f, hf, a, ha, rfl⟩ :=
      uc22pws_exists_mul_of_mem_sup (uc22pws_le_normalizer hEab hqE hJE) hx
    haveI := hEab
    have hcomm : Commute f a := mul_comm_of_mem_isMulCommutative E (hqE hf) (hJE ha)
    have hk' : f ^ (p ^ k) * a ^ (p ^ k) = 1 := by rw [← hcomm.mul_pow]; exact hk
    obtain ⟨j, hj⟩ := hqg f hf
    by_cases hpq : p = q
    · subst hpq
      have h1 : a ^ (p ^ k) = (f ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk'
      have h2 : a ^ (p ^ (k + j)) = 1 := by
        rw [pow_add, pow_mul, h1, inv_pow, ← pow_mul, Nat.mul_comm, pow_mul, hj, one_pow, inv_one]
      rw [(ih hS' p hqp a ha (k + j) h2).2 hqS, mul_one]
      exact ⟨fun _ => hf, fun h => absurd (Finset.mem_insert_self _ _) h⟩
    · have hmem : p ∈ insert q S ↔ p ∈ S := by simp [Finset.mem_insert, hpq]
      have hg : f ^ (p ^ k) = (a ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk'
      have hgJ : f ^ (p ^ k) ∈ ⨆ q' ∈ S, F q' := by
        rw [hg]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ha _)
      have hgq : (f ^ (p ^ k)) ^ (q ^ j) = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hj, one_pow]
      have hf1 : f ^ (p ^ k) = 1 := (ih hS' q hqp _ hgJ j hgq).2 hqS
      have hcop : Nat.Coprime (p ^ k) (q ^ j) :=
        Nat.Coprime.pow k j ((Nat.coprime_primes hp hqp).2 hpq)
      have hf2 : f = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1
        (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf1) (orderOf_dvd_of_pow_eq_one hj)))
      subst hf2
      have ha1 : a ^ (p ^ k) = 1 := by simpa using hk
      have := ih hS' p hp a ha k ha1
      rw [one_mul]
      exact ⟨fun h => this.1 (hmem.1 h), fun h => this.2 fun h' => h (hmem.2 h')⟩

theorem uc22pws_mem_of_dvd {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S : Finset ℕ} (hS : uc22pwsFam E F S) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card ↥(⨆ q ∈ S, F q)) : p ∈ S := by
  obtain ⟨y, hy, hyo⟩ := uc22pws_exists_orderOf hp hd
  obtain ⟨hy1, hyp⟩ := uc22pws_of_orderOf hp hyo
  by_contra h
  exact hy1 ((uc22pws_torsion hEab S hS hp hy hyp).2 h)

theorem uc22pws_disjoint {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S₁ S₂ : Finset ℕ} (h₁ : uc22pwsFam E F S₁) (h₂ : uc22pwsFam E F S₂) (hd : Disjoint S₁ S₂) :
    Disjoint (⨆ q ∈ S₁, F q) (⨆ q ∈ S₂, F q) := by
  rw [disjoint_iff]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (fun h => hne (Subgroup.eq_bot_of_card_eq _ h) :
      Nat.card ↥((⨆ q ∈ S₁, F q) ⊓ (⨆ q ∈ S₂, F q)) ≠ 1)
  obtain ⟨y, hy, hyo⟩ := uc22pws_exists_orderOf hp hpd
  obtain ⟨hy1, hyp⟩ := uc22pws_of_orderOf hp hyo
  have hp1 : p ∈ S₁ := by
    by_contra h
    exact hy1 ((uc22pws_torsion hEab S₁ h₁ hp hy.1 hyp).2 h)
  have hp2 : p ∈ S₂ := by
    by_contra h
    exact hy1 ((uc22pws_torsion hEab S₂ h₂ hp hy.2 hyp).2 h)
  exact Finset.disjoint_left.1 hd hp1 hp2

theorem uc22pws_squarefree {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S : Finset ℕ} (hS : uc22pwsFam E F S) (hc : ∀ q ∈ S, Nat.card (F q) = q) :
    Squarefree (Nat.card ↥(⨆ q ∈ S, F q)) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(⨆ q ∈ S, F q)) p (n := 2)
    (by rw [pow_two]; exact hpp)
  have hK' : Nat.card (K.map (⨆ q ∈ S, F q).subtype) = p ^ 2 := by
    rw [card_map_of_injective (Subgroup.subtype_injective _)]; exact hK
  have hKJ : ∀ x ∈ K.map (⨆ q ∈ S, F q).subtype, x ∈ ⨆ q ∈ S, F q :=
    fun x hx => map_subtype_le K hx
  have hKp : ∀ x ∈ K.map (⨆ q ∈ S, F q).subtype, x ^ (p ^ 2) = 1 :=
    fun x hx => hK' ▸ uc22pws_pow_card hx
  have h2 := hp.two_le
  by_cases hpS : p ∈ S
  · have hle : K.map (⨆ q ∈ S, F q).subtype ≤ F p := fun x hx =>
      (uc22pws_torsion hEab S hS hp (hKJ x hx) (hKp x hx)).1 hpS
    have := Subgroup.card_le_of_le hle
    rw [hK', hc p hpS] at this
    nlinarith
  · have hle : K.map (⨆ q ∈ S, F q).subtype ≤ ⊥ := fun x hx =>
      Subgroup.mem_bot.2 ((uc22pws_torsion hEab S hS hp (hKJ x hx) (hKp x hx)).2 hpS)
    have := Subgroup.card_le_of_le hle
    rw [hK', Subgroup.card_bot] at this
    nlinarith

theorem uc22pws_isCyclic {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S : Finset ℕ} (hS : uc22pwsFam E F S) (hc : ∀ q ∈ S, Nat.card (F q) = q) :
    IsCyclic ↥(⨆ q ∈ S, F q) := by
  haveI : IsMulCommutative ↥(⨆ q ∈ S, F q) :=
    uc22pws_isMulCommutative_of_le hEab (iSup₂_le fun q hq => (hS q hq).2.1)
  haveI : IsZGroup ↥(⨆ q ∈ S, F q) := IsZGroup.of_squarefree (uc22pws_squarefree hEab hS hc)
  infer_instance

theorem uc22pws_sylow {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S : Finset ℕ} (hS : uc22pwsFam E F S) (hc : ∀ q ∈ S, Nat.card (F q) = q ^ 2)
    (he : ∀ q ∈ S, ∀ x ∈ F q, x ^ q = 1) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card ↥(⨆ q ∈ S, F q)) :
    ∃ P : Sylow p ↥(⨆ q ∈ S, F q), Nat.card P = p ^ 2 ∧ ¬ IsCyclic P := by
  have hpS : p ∈ S := uc22pws_mem_of_dvd hEab hS hp hd
  haveI : Fact p.Prime := ⟨hp⟩
  have hFJ : F p ≤ ⨆ q ∈ S, F q := le_iSup₂ (f := fun q _ => F q) p hpS
  have hQ0c : Nat.card ((F p).subgroupOf (⨆ q ∈ S, F q)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFJ).toEquiv]; exact hc p hpS
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hQ0c).exists_le_sylow
  have hQle : (Q : Subgroup ↥(⨆ q ∈ S, F q)).map (⨆ q ∈ S, F q).subtype ≤ F p := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨g, hg⟩
    exact (uc22pws_torsion hEab S hS hp g.2 (k := k)
      (by simpa using congrArg Subtype.val (congrArg Subtype.val hk))).1 hpS
  have hc' : Nat.card Q = p ^ 2 := by
    refine le_antisymm ?_ ?_
    · calc Nat.card Q = Nat.card ((Q : Subgroup ↥(⨆ q ∈ S, F q)).map (⨆ q ∈ S, F q).subtype) :=
            (card_map_of_injective (Subgroup.subtype_injective _)).symm
        _ ≤ Nat.card (F p) := card_le_of_le hQle
        _ = p ^ 2 := hc p hpS
    · rw [← hQ0c]; exact card_le_of_le hQ
  refine ⟨Q, hc', fun hcyc => ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Q)
  have hgp : g ^ p = 1 :=
    Subtype.ext (Subtype.ext (he p hpS _ (hQle ⟨g.1, g.2, rfl⟩)))
  have hg' : orderOf g = p ^ 2 := hg.trans hc'
  have h1 := Nat.le_of_dvd hp.pos (hg' ▸ orderOf_dvd_of_pow_eq_one hgp)
  have h2 := hp.two_le
  nlinarith

theorem uc22pws_pCoreOf_biSup {E : Subgroup X} (hEab : IsMulCommutative E) {F : ℕ → Subgroup X}
    {S : Finset ℕ} (hS : uc22pwsFam E F S) {p : ℕ} (hp : p.Prime) (hpS : p ∈ S) :
    pCoreOf p (⨆ q ∈ S, F q) = F p := by
  haveI : IsMulCommutative ↥(⨆ q ∈ S, F q) :=
    uc22pws_isMulCommutative_of_le hEab (iSup₂_le fun q hq => (hS q hq).2.1)
  ext x
  rw [uc22pws_mem_pCoreOf_iff hp inferInstance]
  constructor
  · rintro ⟨hx, k, hk⟩
    exact (uc22pws_torsion hEab S hS hp hx hk).1 hpS
  · intro hx
    exact ⟨le_iSup₂ (f := fun q _ => F q) p hpS hx, (hS p hpS).2.2 x hx⟩

theorem uc22pws_pCoreOf_elem {E : Subgroup X} (hEab : IsMulCommutative E)
    (hrank : ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2)
    {p : ℕ} (hp : p.Prime) : (∀ x ∈ pCoreOf p E, x ^ p = 1) ∧ Nat.card (pCoreOf p E) ≤ p ^ 2 := by
  haveI := hEab
  obtain ⟨Q, hQe, hQc⟩ := hrank p hp
  have hsub : pCoreOf p E ≤ (Q : Subgroup E).map E.subtype := by
    intro x hx
    obtain ⟨hxE, k, hk⟩ := (uc22pws_mem_pCoreOf_iff hp hEab).1 hx
    have hg : (⟨x, hxE⟩ : E) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    have hgQ : zpowers (⟨x, hxE⟩ : E) ≤ (Q : Subgroup E) :=
      (uc22pws_isPGroup_zpowers hp hg).le_sylow_of_normal Q
    exact ⟨⟨x, hxE⟩, hgQ (mem_zpowers _), rfl⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hsub hx
    simpa using congrArg Subtype.val (hQe.2 g hg)
  · calc Nat.card (pCoreOf p E) ≤ Nat.card ((Q : Subgroup E).map E.subtype) := card_le_of_le hsub
      _ = Nat.card Q := card_map_of_injective E.subtype_injective
      _ ≤ p ^ 2 := hQc

theorem uc22pws_card_cases {p : ℕ} (hp : p.Prime) {E F : Subgroup X} (hE : IsMulCommutative E)
    (hF : F ≤ pCoreOf p E) (hF0 : F ≠ ⊥) (hc : Nat.card (pCoreOf p E) ≤ p ^ 2) :
    Nat.card F = p ∨ Nat.card F = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p F := fun g => by
    obtain ⟨-, k, hk⟩ := (uc22pws_mem_pCoreOf_iff hp hE).1 (hF g.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hle : p ^ n ≤ p ^ 2 := hn ▸ (card_le_of_le hF).trans hc
  have h1 : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have h2 : n ≠ 0 := fun h => hF0 (eq_bot_of_card_eq F (by rw [hn, h, pow_zero]))
  rw [hn]
  interval_cases n
  · exact absurd rfl h2
  · exact Or.inl (pow_one p)
  · exact Or.inr rfl

theorem uc22pws_exists_sel {U E : Subgroup X} (hEU : E ≤ normalizer (U : Set X)) (hU2 : IsPGroup 2 U)
    (hEab : IsMulCommutative E) (hEodd : Odd (Nat.card E)) {Φ : Set (MulAut X)}
    (hΦE : ∀ φ ∈ Φ, ∀ x ∈ E, φ x ∈ E ⊔ U) :
    ∃ F : ℕ → Subgroup X, ∀ p : ℕ, p.Prime → F p ≤ pCoreOf p E ∧ uc22pwsInv U Φ (F p) ∧
      (p ∣ Nat.card E → F p ≠ ⊥) ∧
      ∀ W : Subgroup X, W ≤ F p → uc22pwsInv U Φ W → W = ⊥ ∨ W = F p := by
  have key : ∀ p : ℕ, ∃ Fp : Subgroup X, p.Prime → (Fp ≤ pCoreOf p E ∧ uc22pwsInv U Φ Fp ∧
      (p ∣ Nat.card E → Fp ≠ ⊥) ∧
      ∀ W : Subgroup X, W ≤ Fp → uc22pwsInv U Φ W → W = ⊥ ∨ W = Fp) := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨Fp, h1, h2, h3, h4⟩ :=
        uc22pws_exists_min (uc22pws_inv_pCoreOf hEU hU2 hEab hEodd hΦE hp)
      refine ⟨Fp, fun _ => ⟨h1, h2, fun hd => h3 ?_, h4⟩⟩
      obtain ⟨y, hy, hyo⟩ := uc22pws_exists_orderOf hp hd
      obtain ⟨hy1, hyp⟩ := uc22pws_of_orderOf hp hyo
      intro h
      have hyc : y ∈ pCoreOf p E := (uc22pws_mem_pCoreOf_iff hp hEab).2 ⟨hy, 1, hyp⟩
      rw [h] at hyc
      exact hy1 (Subgroup.mem_bot.1 hyc)
    · exact ⟨⊥, fun h => absurd h hp⟩
  choose F hF using key
  exact ⟨F, hF⟩

end Helpers

theorem uc22pw_select_mod_of {X : Type} [Group X] [Finite X] {U E : Subgroup X} (hEab : IsMulCommutative E)
    (hrank : ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2)
    {Φ : Set (MulAut X)} {F : ℕ → Subgroup X}
    (hF : ∀ p : ℕ, p.Prime → F p ≤ pCoreOf p E ∧ uc22pwsInv U Φ (F p) ∧ (p ∣ Nat.card E → F p ≠ ⊥) ∧
      ∀ W : Subgroup X, W ≤ F p → uc22pwsInv U Φ W → W = ⊥ ∨ W = F p) :
    ∃ B C : Subgroup X, B ≤ E ∧ C ≤ E ∧ Disjoint B C ∧ IsCyclic B ∧ Squarefree (Nat.card B) ∧
      (∀ φ ∈ Φ, ∀ x ∈ B, φ x ∈ B ⊔ U) ∧ (∀ φ ∈ Φ, ∀ x ∈ C, φ x ∈ C ⊔ U) ∧
      piSet (B ⊔ C) = piSet E ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∃ P : Sylow p C, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∀ W : Subgroup X, W ≤ pCoreOf p (B ⊔ C) →
        (∀ φ ∈ Φ, ∀ x ∈ W, φ x ∈ W ⊔ U) → W = ⊥ ∨ W = pCoreOf p (B ⊔ C)) ∧
      B ⊔ C = ⨆ q ∈ (Nat.card E).primeFactors, F q := by
  classical
  have hPmem : ∀ p ∈ (Nat.card E).primeFactors, p.Prime ∧ p ∣ Nat.card E := fun p hp => by
    obtain ⟨h1, h2, -⟩ := Nat.mem_primeFactors.1 hp
    exact ⟨h1, h2⟩
  have hcard : ∀ p ∈ (Nat.card E).primeFactors, Nat.card (F p) = p ∨ Nat.card (F p) = p ^ 2 :=
    fun p hp => by
      obtain ⟨hpp, hpd⟩ := hPmem p hp
      obtain ⟨h1, -, h3, -⟩ := hF p hpp
      exact uc22pws_card_cases hpp hEab h1 (h3 hpd) (uc22pws_pCoreOf_elem hEab hrank hpp).2
  have hfam : uc22pwsFam E F (Nat.card E).primeFactors := fun p hp => by
    obtain ⟨hpp, -⟩ := hPmem p hp
    obtain ⟨h1, -⟩ := hF p hpp
    exact ⟨hpp, h1.trans (map_subtype_le _),
      fun x hx => ((uc22pws_mem_pCoreOf_iff hpp hEab).1 (h1 hx)).2⟩
  have hexp : ∀ p ∈ (Nat.card E).primeFactors, ∀ x ∈ F p, x ^ p = 1 := fun p hp x hx =>
    (uc22pws_pCoreOf_elem hEab hrank (hPmem p hp).1).1 x ((hF p (hPmem p hp).1).1 hx)
  have hJE : ∀ S : Finset ℕ, uc22pwsFam E F S → (⨆ q ∈ S, F q) ≤ E := fun S hS =>
    iSup₂_le fun q hq => (hS q hq).2.1
  set P : Finset ℕ := (Nat.card E).primeFactors with hP
  set P₁ : Finset ℕ := P.filter fun p => Nat.card (F p) = p with hP₁
  set P₂ : Finset ℕ := P.filter fun p => ¬ Nat.card (F p) = p with hP₂
  have hfam₁ : uc22pwsFam E F P₁ := fun p hp => hfam p (Finset.mem_filter.1 hp).1
  have hfam₂ : uc22pwsFam E F P₂ := fun p hp => hfam p (Finset.mem_filter.1 hp).1
  have hc₁ : ∀ q ∈ P₁, Nat.card (F q) = q := fun q hq => (Finset.mem_filter.1 hq).2
  have hc₂ : ∀ q ∈ P₂, Nat.card (F q) = q ^ 2 := fun q hq => by
    obtain ⟨hqP, hne⟩ := Finset.mem_filter.1 hq
    exact (hcard q hqP).resolve_left hne
  have hBC : (⨆ q ∈ P₁, F q) ⊔ (⨆ q ∈ P₂, F q) = ⨆ q ∈ P, F q := by
    rw [← Finset.iSup_union, Finset.filter_union_filter_not_eq]
  refine ⟨⨆ q ∈ P₁, F q, ⨆ q ∈ P₂, F q, hJE _ hfam₁, hJE _ hfam₂,
    uc22pws_disjoint hEab hfam₁ hfam₂ (Finset.disjoint_filter_filter_not P P _),
    uc22pws_isCyclic hEab hfam₁ hc₁, uc22pws_squarefree hEab hfam₁ hc₁,
    uc22pws_inv_biSup _ _ fun q hq => (hF q (hfam₁ q hq).1).2.1,
    uc22pws_inv_biSup _ _ fun q hq => (hF q (hfam₂ q hq).1).2.1, ?_,
    fun p hp hd => uc22pws_sylow hEab hfam₂ hc₂ (fun q hq => hexp q (Finset.mem_filter.1 hq).1) hp hd,
    fun p hp hd W hW hWi => ?_, hBC⟩
  · rw [hBC]
    ext p
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hd.trans (card_dvd_of_le (hJE P hfam))⟩
    · rintro ⟨hp, hd⟩
      have hpP : p ∈ P := Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩
      have hpF : p ∣ Nat.card (F p) := by
        rcases hcard p hpP with h | h
        · rw [h]
        · rw [h]; exact dvd_pow_self p two_ne_zero
      exact ⟨hp, hpF.trans (card_dvd_of_le (le_iSup₂ (f := fun q _ => F q) p hpP))⟩
  · have hpP₂ : p ∈ P₂ := uc22pws_mem_of_dvd hEab hfam₂ hp hd
    have hpP : p ∈ P := (Finset.mem_filter.1 hpP₂).1
    rw [hBC, uc22pws_pCoreOf_biSup hEab hfam hp hpP] at hW ⊢
    exact (hF p hp).2.2.2 W hW hWi


theorem uc22pw_select_mod {X : Type} [Group X] [Finite X] {U E : Subgroup X}
    (hEU : E ≤ normalizer (U : Set X)) (hU2 : IsPGroup 2 U) (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hrank : ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2)
    (Φ : Set (MulAut X)) (hΦU : ∀ φ ∈ Φ, ∀ x : X, x ∈ U ↔ φ x ∈ U)
    (hΦE : ∀ φ ∈ Φ, ∀ x ∈ E, φ x ∈ E ⊔ U) :
    ∃ B C : Subgroup X, B ≤ E ∧ C ≤ E ∧ Disjoint B C ∧ IsCyclic B ∧ Squarefree (Nat.card B) ∧
      (∀ φ ∈ Φ, ∀ x ∈ B, φ x ∈ B ⊔ U) ∧ (∀ φ ∈ Φ, ∀ x ∈ C, φ x ∈ C ⊔ U) ∧
      piSet (B ⊔ C) = piSet E ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∃ P : Sylow p C, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∀ W : Subgroup X, W ≤ pCoreOf p (B ⊔ C) →
        (∀ φ ∈ Φ, ∀ x ∈ W, φ x ∈ W ⊔ U) → W = ⊥ ∨ W = pCoreOf p (B ⊔ C)) := by
  obtain ⟨F, hF⟩ := uc22pws_exists_sel hEU hU2 hEab hEodd hΦE
  obtain ⟨B, C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := uc22pw_select_mod_of hEab hrank hF
  exact ⟨B, C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
