module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Quasithin.Background.B2FactorizationBaumannVar
public import CFSG.Quasithin.Background.E2Frattini

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G]

omit [Group G] in
theorem eq_one_of_odd_orderOf_of_pow_two_pow {M' : Type*} [Monoid M'] {y : M'}
    (hy : Odd (orderOf y)) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : Nat.Coprime (orderOf y) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hy)
  rw [← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd h2 h1

theorem commute_of_odd_of_commutator {y x : G} (hy : Odd (orderOf y))
    (hc : y * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * y)
    (hc2 : ∃ k : ℕ, (y * x * y⁻¹ * x⁻¹) ^ 2 ^ k = 1) : y * x = x * y := by
  set c := y * x * y⁻¹ * x⁻¹ with hcdef
  have hcomm : Commute y c := hc
  have hyc : ∀ n : ℕ, y ^ n * x * (y ^ n)⁻¹ = c ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcy : y * c ^ n = c ^ n * y := (hcomm.pow_right n).eq
      calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = y * (c ^ n * x) * y⁻¹ := by rw [ih]
        _ = (y * c ^ n) * x * y⁻¹ := by group
        _ = (c ^ n * y) * x * y⁻¹ := by rw [hcy]
        _ = c ^ n * (y * x * y⁻¹ * x⁻¹) * x := by group
        _ = c ^ (n + 1) * x := by rw [← hcdef, pow_succ]
  have h1 := hyc (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : c ^ orderOf y = 1 := by
    have := congrArg (· * x⁻¹) h1
    simpa using this.symm
  obtain ⟨k, hk⟩ := hc2
  have h3 : orderOf c ∣ Nat.gcd (orderOf y) (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hk)
  have hcop : Nat.gcd (orderOf y) (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hy)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have h4 : y * x * y⁻¹ * x⁻¹ = 1 := h3
  calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
    _ = x * y := by rw [h4, one_mul]

theorem exists_pow_two_pow_eq_one {T : Subgroup G} (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem cjSub_sup (g : G) (A B : Subgroup G) : cjSub g (A ⊔ B) = cjSub g A ⊔ cjSub g B :=
  Subgroup.map_sup A B _

theorem mem_normalizer_sup_of_comm {V Q : Subgroup G} {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (h1 : ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ Q) (h2 : ∀ v ∈ V, g⁻¹ * v * g * v⁻¹ ∈ Q) :
    g ∈ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ Subgroup.normalizer (Q : Set G) →
      (∀ v ∈ V, g' * v * g'⁻¹ * v⁻¹ ∈ Q) → cjSub g' (V ⊔ Q) ≤ V ⊔ Q := by
    intro g' hg'Q hg'
    rw [cjSub_sup, cjSub_eq_of_mem_normalizer hg'Q]
    refine sup_le (fun w hw => ?_) le_sup_right
    rw [mem_cjSub] at hw
    have e : w = (g' * (g'⁻¹ * w * g') * g'⁻¹ * (g'⁻¹ * w * g')⁻¹) * (g'⁻¹ * w * g') := by
      group
    rw [e]
    exact (V ⊔ Q).mul_mem (Subgroup.mem_sup_right (hg' _ hw)) (Subgroup.mem_sup_left hw)
  refine le_normalizer_of_cjSub_le (key g hgQ h1) (key g⁻¹ (Subgroup.inv_mem _ hgQ) ?_)
  intro v hv
  simpa using h2 v hv

theorem exists_hyperplane_noncomm [Finite G] {A P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hA : IsElemAbelian 2 A) (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hact : ∃ y ∈ P, ∃ a ∈ A, a * y ≠ y * a) :
    ∃ B : Subgroup G, B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      ∃ y ∈ P ⊓ Subgroup.centralizer (B : Set G), ∃ a ∈ A, a * y ≠ y * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyP, a, haA, hne⟩ := hact
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.mem_bot] at haA
    subst haA
    exact hne (by rw [one_mul, mul_one])
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a =>
          Subtype.ext (by simpa using hA.2 a a.2) }
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P (conjAut hAP)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  by_contra hcon
  push Not at hcon
  have hsmul : ∀ (b : A) (x : P), (((b • x : P)) : G) = (b : G) * x * (b : G)⁻¹ :=
    fun b x => rfl
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P) ≤
      CFSG.fixedPointSubgroup A P := by
    refine iSup₂_le fun B hB x hx => ?_
    have hB' : B.map A.subtype ≤ A := by
      rintro _ ⟨b, -, rfl⟩
      exact b.2
    have hcard : Nat.card A = 2 * Nat.card (B.map A.subtype) := by
      have := B.card_mul_index
      rw [hB] at this
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      omega
    have hxc : (x : G) ∈ P ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have h1 : b • x = x := hx ⟨b, hb⟩
      have h2 := congrArg (fun z : P => (z : G)) h1
      simp only [hsmul] at h2
      show (b : G) * x = x * b
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    intro a'
    apply Subtype.ext
    rw [hsmul]
    exact mul_inv_eq_iff_eq_mul.mpr (hcon _ hB' hcard x hxc a' a'.2)
  have hy : (⟨y, hyP⟩ : P) ∈ CFSG.fixedPointSubgroup A P := hle (hgen ▸ Subgroup.mem_top _)
  have h1 : (⟨a, haA⟩ : A) • (⟨y, hyP⟩ : P) = ⟨y, hyP⟩ := hy ⟨a, haA⟩
  have h2 := congrArg (fun z : P => (z : G)) h1
  simp only [hsmul] at h2
  exact hne (mul_inv_eq_iff_eq_mul.mp h2)

theorem conj_commutator_of_mul_self {x y : G} (hx : x * x = 1) :
    x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  calc x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ = x * y * x * y⁻¹ * (x * x)⁻¹ := by group
    _ = x * y * x * y⁻¹ := by rw [hx, inv_one, mul_one]
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h1]
    _ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group

theorem conj_eq_inv_of_mem_zpowers {x z w : G} (hz : x * z * x⁻¹ = z⁻¹)
    (hw : w ∈ Subgroup.zpowers z) : x * w * x⁻¹ = w⁻¹ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have := map_zpow (MulAut.conj x) z m
  simp only [MulAut.conj_apply] at this
  rw [this, hz, inv_zpow]

theorem exists_dihedral_pair [Finite G] {H T M V : Subgroup G} (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) (hVQ : ¬ V ≤ pCoreOf 2 H) :
    ∃ U : Subgroup G, U ≤ V ∧ V ⊓ pCoreOf 2 H ≤ U ∧ ∃ x ∈ V, x ∉ U ∧
      (∀ v ∈ V, v ∈ U ∨ x * v ∈ U) ∧ ∃ z ∈ H, Odd (orderOf z) ∧ z ≠ 1 ∧
        x * z * x⁻¹ = z⁻¹ ∧ ∀ u ∈ U, z * u * z⁻¹ * u⁻¹ ∈ pCoreOf 2 H := by
  classical
  have hT := h.isSylow
  set Q := pCoreOf 2 H with hQdef
  set K := twoResidual H with hKdef
  have hKH : K ≤ H := twoResidual_le H
  have hQT : Q ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hVH : V ≤ H := hVT.trans hT.1
  have hstep : ∃ v ∈ V, ∃ k ∈ K, v * k * v⁻¹ * k⁻¹ ∉ Q := by
    by_contra hcon
    push Not at hcon
    apply hVQ
    have hWT : V ⊔ Q ≤ T := sup_le hVT hQT
    have hWH : V ⊔ Q ≤ H := hWT.trans hT.1
    have hTW : T ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) :=
      B2F.le_normalizer_sup hTV (hT.1.trans hHQ)
    have hKW : K ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
      intro k hk
      refine mem_normalizer_sup_of_comm (hHQ (hKH hk)) (fun v hv => ?_) (fun v hv => ?_)
      · have := Q.inv_mem (hcon v hv k hk)
        simpa [mul_assoc] using this
      · have := Q.inv_mem (hcon v hv k⁻¹ (K.inv_mem hk))
        simpa [mul_assoc] using this
    have hHW : H ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
      rw [← sup_twoResidual_eq hT]
      exact sup_le hTW hKW
    exact le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (V ⊔ Q) H hWH ((Subgroup.normal_subgroupOf_iff_le_normalizer hWH).2 hHW)
      (hT.2.1.to_le hWT))
  obtain ⟨v₀, hv₀, k₀, hk₀, hne₀⟩ := hstep
  obtain ⟨p, hpp, hp2, hpow⟩ := h.exists_prime_pow_mem_pCoreOf hsolv
  have : Fact p.Prime := ⟨hpp⟩
  set Q' : Subgroup H := Q.subgroupOf H with hQ'
  have hQ'n : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hHQ
  set π : H →* H ⧸ Q' := QuotientGroup.mk' Q' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q'
  have hπ1 : ∀ w : H, π w = 1 ↔ (w : G) ∈ Q := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set Vb : Subgroup (H ⧸ Q') := (V.subgroupOf H).map π with hVb
  set Kb : Subgroup (H ⧸ Q') := (K.subgroupOf H).map π with hKb
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 (le_normalizer_twoResidual H)
  have hKbn : Kb.Normal := hKn.map π hπs
  have hKbp : IsPGroup p Kb := by
    rintro ⟨_, k, hk, rfl⟩
    obtain ⟨a, ha⟩ := hpow k (Subgroup.mem_subgroupOf.1 hk)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hπ1]
    simpa using ha
  have hVbel : IsElemAbelian 2 Vb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
      obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
      apply Subtype.ext
      show π a' * π b' = π b' * π a'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (isElemAbelian_comm hV ha' hb')
    · obtain ⟨a', ha', rfl⟩ := ha
      rw [← map_pow]
      have : a' ^ 2 = 1 := Subtype.ext (by simpa using hV.2 _ ha')
      rw [this, map_one]
  have hact : ∃ y ∈ Kb, ∃ a ∈ Vb, a * y ≠ y * a := by
    refine ⟨π ⟨k₀, hKH hk₀⟩, ⟨_, hk₀, rfl⟩, π ⟨v₀, hVH hv₀⟩, ⟨_, hv₀, rfl⟩, fun heq => hne₀ ?_⟩
    have : π (⟨v₀, hVH hv₀⟩ * ⟨k₀, hKH hk₀⟩ * ⟨v₀, hVH hv₀⟩⁻¹ * ⟨k₀, hKH hk₀⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv, heq]
      group
    exact (hπ1 _).1 this
  have hVbN : Vb ≤ Subgroup.normalizer (Kb : Set (H ⧸ Q')) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hKbn]
    exact Subgroup.mem_top g
  obtain ⟨Bb, hBV, hcard, yb, ⟨hybK, hybC⟩, ab, habV, hne⟩ :=
    exists_hyperplane_noncomm hp2 hVbel hKbp hVbN hact
  obtain ⟨a, haV, rfl⟩ := habV
  obtain ⟨y, hyK, rfl⟩ := hybK
  have ha2 : a * a = 1 := Subtype.ext (by simpa [pow_two] using hV.2 _ haV)
  set z₀ : H := y * a * y⁻¹ * a⁻¹ with hz₀
  have hz₀K : z₀ ∈ K.subgroupOf H := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ K.subgroupOf H := hKn.conj_mem _ ((K.subgroupOf H).inv_mem hyK) a
    have e : z₀ = y * (a * y⁻¹ * a⁻¹) := by rw [hz₀]; group
    rw [e]
    exact (K.subgroupOf H).mul_mem hyK h1
  have hz₀inv : a * z₀ * a⁻¹ = z₀⁻¹ := conj_commutator_of_mul_self ha2
  obtain ⟨a₂, b₁, hz₀eq, ha₂, hb₁, ⟨k, hk⟩, hb₁odd⟩ := exists_two_part_odd_part z₀
  have hπa₂ : π a₂ = 1 := by
    have hmem : π a₂ ∈ Kb := ⟨a₂, Subgroup.zpowers_le.2 hz₀K ha₂, rfl⟩
    obtain ⟨n, hn⟩ := hKbp ⟨π a₂, hmem⟩
    have hn' : π a₂ ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hodd : Odd (orderOf (π a₂)) :=
      Odd.of_dvd_nat (Odd.pow (hpp.odd_of_ne_two hp2)) (orderOf_dvd_of_pow_eq_one hn')
    exact eq_one_of_odd_orderOf_of_pow_two_pow hodd (by rw [← map_pow, hk, map_one])
  have hπb₁ : π b₁ = π z₀ := by rw [hz₀eq, map_mul, hπa₂, mul_one]
  have hπz₀ : π z₀ ≠ 1 := by
    intro h1
    apply hne
    have e : π z₀ = π y * π a * (π y)⁻¹ * (π a)⁻¹ := by
      rw [hz₀]
      simp only [map_mul, map_inv]
    rw [e] at h1
    calc π a * π y = (π y * π a * (π y)⁻¹ * (π a)⁻¹)⁻¹ * (π y * π a) := by group
      _ = π y * π a := by rw [h1, inv_one, one_mul]
  set U : Subgroup G := V ⊓ (Bb.comap π).map H.subtype with hU
  have hπaB : π a ∉ Bb := fun hB => hne (Subgroup.mem_centralizer_iff.1 hybC _ hB)
  have hidx : (Bb.subgroupOf Vb).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card Bb Vb
    rw [inf_eq_left.2 hBV, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hdich : ∀ w ∈ Vb, w ∈ Bb ∨ π a * w ∈ Bb := by
    intro w hw
    by_cases hwB : w ∈ Bb
    · exact Or.inl hwB
    · right
      have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨π a, ⟨a, haV, rfl⟩⟩)
        (b := ⟨w, hw⟩)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
      exact key.2 (iff_of_false hπaB hwB)
  have hU2 : ∀ v ∈ V, v ∈ U ∨ (a : G) * v ∈ U := by
    intro v hv
    rcases hdich (π ⟨v, hVH hv⟩) ⟨⟨v, hVH hv⟩, hv, rfl⟩ with hB | hB
    · exact Or.inl ⟨hv, ⟨v, hVH hv⟩, hB, rfl⟩
    · refine Or.inr ⟨V.mul_mem haV hv, a * ⟨v, hVH hv⟩, ?_, rfl⟩
      show π (a * ⟨v, hVH hv⟩) ∈ Bb
      rw [map_mul]
      exact hB
  have hxU : (a : G) ∉ U := by
    rintro ⟨-, w, hw, hwa⟩
    have : w = a := Subtype.ext hwa
    subst this
    exact hπaB hw
  have hVQU : V ⊓ Q ≤ U := fun q hq =>
    ⟨hq.1, ⟨q, hQH hq.2⟩, by
      show π ⟨q, hQH hq.2⟩ ∈ Bb
      rw [(hπ1 _).2 hq.2]
      exact Bb.one_mem, rfl⟩
  refine ⟨U, inf_le_left, hVQU, (a : G), haV, hxU, hU2, (b₁ : G), b₁.2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hb₁odd
  · intro h1
    apply hπz₀
    rw [← hπb₁, show b₁ = 1 from Subtype.ext h1, map_one]
  · have := conj_eq_inv_of_mem_zpowers hz₀inv hb₁
    exact congrArg Subtype.val this
  · rintro _ ⟨huV, w, hw, rfl⟩
    have hwB : π w ∈ Bb := hw
    have c1 : Commute (π y) (π w) := (Subgroup.mem_centralizer_iff.1 hybC _ hwB).symm
    have c2 : Commute (π a) (π w) := isElemAbelian_comm hVbel ⟨a, haV, rfl⟩ (hBV hwB)
    have hcomm : π b₁ * π w = π w * π b₁ := by
      rw [hπb₁, hz₀]
      simp only [map_mul, map_inv]
      exact (((c1.mul_left c2).mul_left c1.inv_left).mul_left c2.inv_left).eq
    have : π (b₁ * w * b₁⁻¹ * w⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    exact (hπ1 _).1 this

theorem conj_mem_normalizer_cjSub {X : Subgroup G} {g : G} (z : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    z * g * z⁻¹ ∈ Subgroup.normalizer (cjSub z X : Set G) := by
  rw [mem_normalizer_iff_cjSub_eq, ← cjSub_mul, show z * g * z⁻¹ * z = z * g by group, cjSub_mul,
    cjSub_eq_of_mem_normalizer hg]

end E2

end CFSG.Quasithin
