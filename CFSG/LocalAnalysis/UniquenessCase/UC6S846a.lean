module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup

theorem coprime_orderOf_of_mem_closure {Q : Type*} [Group Q] [IsCyclic Q] {p : ℕ}
    (S : Set Q) (hS : ∀ x ∈ S, ¬ p ∣ orderOf x) (hp : p.Prime) {y : Q}
    (hy : y ∈ Subgroup.closure S) : ¬ p ∣ orderOf y := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simpa using hp.ne_one
  | mul x y _ _ hx hy =>
    have hxy : Commute x y := IsMulCommutative.is_comm.comm x y
    have hdvd := hxy.orderOf_mul_dvd_lcm
    intro hp'
    have h1 := hp'.trans hdvd
    have := (Nat.Prime.dvd_mul hp).1 (h1.trans (Nat.lcm_dvd_mul _ _))
    rcases this with h | h
    · exact hx h
    · exact hy h
  | inv x _ hx => simpa using hx

theorem mem_inner_of_pPow {Γ : Type*} [Group Γ] (I N H : Subgroup Γ) [N.Normal]
    (hcyc : IsCyclic (Γ ⧸ N)) (hcube : ∀ φ ∈ N, φ ^ 3 ∈ I) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3 ∨ N ≤ I)
    (hgen : Subgroup.closure {x | x ∈ H ∧ ¬ p ∣ orderOf x} = H) {h : Γ} (hh : h ∈ H) {k : ℕ}
    (hk : h ^ (p ^ k) = 1) : h ∈ I := by
  classical
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  set S : Set Γ := {x | x ∈ H ∧ ¬ p ∣ orderOf x} with hSdef
  have hmap : (Subgroup.closure S).map π = Subgroup.closure (π '' S) := MonoidHom.map_closure π S
  have hπh : π h ∈ Subgroup.closure (π '' S) := by
    rw [← hmap, hgen]
    exact ⟨h, hh, rfl⟩
  have hSπ : ∀ x ∈ π '' S, ¬ p ∣ orderOf x := by
    rintro _ ⟨s, hs, rfl⟩ hdvd
    exact hs.2 (hdvd.trans (orderOf_map_dvd π s))
  have hcop := coprime_orderOf_of_mem_closure (π '' S) hSπ hp hπh
  have hπk : (π h) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hπ1 : π h = 1 := by
    have hdvd : orderOf (π h) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hπk
    obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hord
    · exfalso
      apply hcop
      rw [hord]
      exact dvd_pow_self p hjpos.ne'
  have hhN : h ∈ N := by
    have : (QuotientGroup.mk' N) h = 1 := hπ1
    exact (QuotientGroup.eq_one_iff h).1 this
  rcases hp3 with hp3 | hNI
  ·
    have h3 : h ^ 3 ∈ I := hcube h hhN
    have hcopr : Nat.Coprime 3 (p ^ k) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, 3 * a + (p ^ k : ℕ) * b = 1 := by
      have := Nat.gcd_eq_gcd_ab 3 (p ^ k)
      rw [hcopr.gcd_eq_one] at this
      exact ⟨Nat.gcdA 3 (p ^ k), Nat.gcdB 3 (p ^ k), by exact_mod_cast this.symm⟩
    have hpow : h = (h ^ 3) ^ a := by
      have h1 : h ^ (3 * a + ((p ^ k : ℕ) : ℤ) * b) = h := by rw [hab]; simp
      have h2 : h ^ (3 * a + ((p ^ k : ℕ) : ℤ) * b) = (h ^ 3) ^ a := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, hk, one_zpow, mul_one]
        norm_cast
      exact h1.symm.trans h2
    rw [hpow]
    exact I.zpow_mem h3 a
  · exact hNI hhN

theorem exists_lift_pGroup {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (Qb : Subgroup K) (hQb : IsPGroup q Qb) :
    ∃ Q : Subgroup H, IsPGroup q Q ∧ Q.map f = Qb ∧ Disjoint Q f.ker := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite K := Finite.of_surjective f hf
  obtain ⟨S', hS'⟩ := hQb.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf q S'
  have hSmap : (S : Subgroup H).map f = (S' : Subgroup K) := by
    rw [← hS, Sylow.coe_mapSurjective]
  refine ⟨(S : Subgroup H) ⊓ Qb.comap f, S.isPGroup'.to_le inf_le_left, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hyS : y ∈ (S : Subgroup H).map f := by rw [hSmap]; exact hS' hy
      obtain ⟨x, hxS, rfl⟩ := hyS
      exact ⟨x, ⟨hxS, hy⟩, rfl⟩
  · rw [Subgroup.disjoint_def]
    intro x hxQ hxker
    have hxS : x ∈ (S : Subgroup H) := hxQ.1
    obtain ⟨a, ha⟩ := S.isPGroup' ⟨x, hxS⟩
    obtain ⟨b, hb⟩ := hker ⟨x, hxker⟩
    have ha' : x ^ q ^ a = 1 := by simpa using ha
    have hb' : x ^ 2 ^ b = 1 := by simpa using hb
    have hcop : Nat.Coprime (q ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have h1 : orderOf x ∣ Nat.gcd (q ^ a) (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
    rw [hcop.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem exists_fixed_in_coset {G : Type*} [Group G] [Finite G] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (O B E : Subgroup G) (hO : IsPGroup 2 O) (hOB : O ≤ B)
    (hEO : E ≤ Subgroup.normalizer (O : Set G)) (hEB : E ≤ Subgroup.normalizer (B : Set G))
    (hE : IsPGroup ℓ E) (hcommB : ∀ e ∈ E, ∀ b ∈ B, e * b * e⁻¹ * b⁻¹ ∈ O) (b : G) (hb : b ∈ B) :
    ∃ c ∈ B, c ∈ Subgroup.centralizer (E : Set G) ∧ c * b⁻¹ ∈ O := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let α : Type _ := {c : G // c ∈ B ∧ c * b⁻¹ ∈ O}
  have hmem : ∀ e : E, ∀ c : α, (e : G) * c.1 * (e : G)⁻¹ ∈ B ∧
      ((e : G) * c.1 * (e : G)⁻¹) * b⁻¹ ∈ O := by
    intro e c
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hEB e.2) c.1).1 c.2.1, ?_⟩
    have h1 : ((e : G) * c.1 * (e : G)⁻¹) * b⁻¹ =
        ((e : G) * (c.1 * b⁻¹) * (e : G)⁻¹) * ((e : G) * b * (e : G)⁻¹ * b⁻¹) := by group
    rw [h1]
    refine O.mul_mem ?_ (hcommB e e.2 b hb)
    exact (Subgroup.mem_normalizer_iff.1 (hEO e.2) (c.1 * b⁻¹)).1 c.2.2
  letI : MulAction E α :=
    { smul := fun e c => ⟨(e : G) * c.1 * (e : G)⁻¹, hmem e c⟩
      one_smul := fun c => Subtype.ext (by
        change ((1 : E) : G) * c.1 * ((1 : E) : G)⁻¹ = c.1
        simp)
      mul_smul := fun e₁ e₂ c => Subtype.ext (by
        change (((e₁ * e₂ : E)) : G) * c.1 * (((e₁ * e₂ : E)) : G)⁻¹ =
          (e₁ : G) * ((e₂ : G) * c.1 * (e₂ : G)⁻¹) * (e₁ : G)⁻¹
        simp [mul_assoc]) }
  have hfin : Finite α := Finite.of_injective (Subtype.val : α → G) Subtype.val_injective
  have hcard : Nat.card α = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1 * b⁻¹, c.2.2⟩
        invFun := fun o => ⟨o.1 * b, hOB.trans (le_refl B) o.2 |> fun h => B.mul_mem h hb, by simp⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  obtain ⟨k, hk⟩ := hO.exists_card_eq
  have hndvd : ¬ ℓ ∣ Nat.card α := by
    rw [hcard, hk]
    intro hdvd
    have := (Nat.Prime.dvd_of_dvd_pow hℓ hdvd)
    have h2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this
    exact hℓ2 h2
  obtain ⟨c, hc⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card α hndvd
  refine ⟨c.1, c.2.1, ?_, c.2.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hc ⟨e, he⟩)
  change e * c.1 * e⁻¹ = c.1 at h
  calc e * c.1 = (e * c.1 * e⁻¹) * e := by group
    _ = c.1 * e := by rw [h]

theorem exists_sylow_copy {Bg : Type*} [Group Bg] [Finite Bg] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Ob Ab Cb : Subgroup Bg) [Ob.Normal] (hO : IsPGroup 2 Ob) (hA : IsPGroup p Ab)
    (hAO : Ab ⊔ Ob = ⊤) (hCO : ∀ b : Bg, ∃ c ∈ Cb, c * b⁻¹ ∈ Ob) :
    ∃ S : Subgroup Bg, S ≤ Cb ∧ Nonempty (↥S ≃* ↥Ab) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let π : Bg →* Bg ⧸ Ob := QuotientGroup.mk' Ob
  have hcop : ∀ x : Bg, x ∈ Ob → (∃ k, x ^ p ^ k = 1) → x = 1 := by
    intro x hxO ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hO ⟨x, hxO⟩
    have hb' : x ^ 2 ^ b = 1 := by simpa using hb
    have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h1 : orderOf x ∣ Nat.gcd (p ^ a) (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb')
    rw [hcop.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  let φA : ↥Ab →* Bg ⧸ Ob := π.comp Ab.subtype
  have hφAinj : Function.Injective φA := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : (x : Bg) ∈ Ob := (QuotientGroup.eq_one_iff (x : Bg)).1 hx
    obtain ⟨k, hk⟩ := hA x
    have hk' : (x : Bg) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have := hcop (x : Bg) hxO ⟨k, hk'⟩
    exact Subtype.ext this
  have hφAsurj : Function.Surjective φA := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Ob y
    have hb : b ∈ (Ab ⊔ Ob : Subgroup Bg) := by rw [hAO]; exact Subgroup.mem_top b
    obtain ⟨a, ha, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
    refine ⟨⟨a, ha⟩, ?_⟩
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    show π a = π (a * o)
    rw [map_mul, hπo, mul_one]
  have hQp : IsPGroup p (Bg ⧸ Ob) := hA.of_surjective φA hφAsurj
  let φC : ↥Cb →* Bg ⧸ Ob := π.comp Cb.subtype
  have hφCsurj : Function.Surjective φC := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Ob y
    obtain ⟨c, hc, hcb⟩ := hCO b
    refine ⟨⟨c, hc⟩, ?_⟩
    show π c = π b
    have h1 : π (c * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hcb
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 h1
  obtain ⟨S₀⟩ : Nonempty (Sylow p ↥Cb) := inferInstance
  have hS₀map : (S₀ : Subgroup ↥Cb).map φC = ⊤ := by
    have hcoe : ((S₀.mapSurjective hφCsurj : Sylow p (Bg ⧸ Ob)) : Subgroup (Bg ⧸ Ob)) =
        (S₀ : Subgroup ↥Cb).map φC := Sylow.coe_mapSurjective hφCsurj S₀
    rw [← hcoe]
    have hTop : IsPGroup p ↥(⊤ : Subgroup (Bg ⧸ Ob)) := hQp.of_equiv Subgroup.topEquiv.symm
    exact ((S₀.mapSurjective hφCsurj : Sylow p (Bg ⧸ Ob)).is_maximal' hTop le_top).symm
  let ψ : ↥(S₀ : Subgroup ↥Cb) →* Bg ⧸ Ob := φC.comp (S₀ : Subgroup ↥Cb).subtype
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : ((x : ↥Cb) : Bg) ∈ Ob := (QuotientGroup.eq_one_iff ((x : ↥Cb) : Bg)).1 hx
    obtain ⟨k, hk⟩ := S₀.isPGroup' x
    have hk' : ((x : ↥Cb) : Bg) ^ p ^ k = 1 := by
      have := congrArg (fun z : ↥(S₀ : Subgroup ↥Cb) => ((z : ↥Cb) : Bg)) hk
      simpa using this
    have := hcop _ hxO ⟨k, hk'⟩
    exact Subtype.ext (Subtype.ext this)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (S₀ : Subgroup ↥Cb).map φC := by rw [hS₀map]; exact Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨(S₀ : Subgroup ↥Cb).map Cb.subtype, Subgroup.map_subtype_le _, ⟨?_⟩⟩
  exact ((Subgroup.equivMapOfInjective (S₀ : Subgroup ↥Cb) Cb.subtype Cb.subtype_injective).symm.trans
    ((MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (MulEquiv.ofBijective φA ⟨hφAinj, hφAsurj⟩).symm))

theorem exists_centralizing_copy {G : Type*} [Group G] [Finite G] {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (O A E : Subgroup G) (hO : IsPGroup 2 O)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hEO : E ≤ Subgroup.normalizer (O : Set G))
    (hA : IsPGroup p A) (hE : IsPGroup ℓ E)
    (hcomm : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ O) :
    ∃ A' : Subgroup G, A' ≤ Subgroup.centralizer (E : Set G) ∧ A' ≤ A ⊔ O ∧
      Nonempty (↥A' ≃* ↥A) := by
  classical
  set B : Subgroup G := A ⊔ O with hBdef
  have hAB : A ≤ B := le_sup_left
  have hOB : O ≤ B := le_sup_right
  have hBN : B ≤ Subgroup.normalizer (O : Set G) := sup_le hAO Subgroup.le_normalizer
  have hNormOB : (O.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).2 hBN
  have hcommB : ∀ e ∈ E, ∀ b ∈ B, e * b * e⁻¹ * b⁻¹ ∈ O := by
    intro e he b hb
    have hb' : b ∈ Subgroup.closure ((A : Set G) ∪ (O : Set G)) := by
      rw [← Subgroup.sup_eq_closure]; exact hb
    have hcl : Subgroup.closure ((A : Set G) ∪ (O : Set G)) ≤ Subgroup.normalizer (O : Set G) := by
      rw [← Subgroup.sup_eq_closure]; exact hBN
    clear hb
    revert he
    induction hb' using Subgroup.closure_induction with
    | mem x hx =>
      intro he
      rcases hx with hx | hx
      · exact hcomm e he x hx
      · have h1 : e * x * e⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hEO he) x).1 hx
        exact O.mul_mem h1 (O.inv_mem hx)
    | one => intro he; simp
    | mul x y hxm hym ihx ihy =>
      intro he
      have hxN : x ∈ Subgroup.normalizer (O : Set G) := hcl hxm
      have h1 := ihx he
      have h2 := ihy he
      have h3 : x * (e * y * e⁻¹ * y⁻¹) * x⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hxN _).1 h2
      have h4 : e * (x * y) * e⁻¹ * (x * y)⁻¹ =
          (e * x * e⁻¹ * x⁻¹) * (x * (e * y * e⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [h4]
      exact O.mul_mem h1 h3
    | inv x hxm ih =>
      intro he
      have hxN : x ∈ Subgroup.normalizer (O : Set G) := hcl hxm
      have h1 := ih he
      have h2 : x⁻¹ * (e * x * e⁻¹ * x⁻¹)⁻¹ * x ∈ O :=
        (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) _).1 (O.inv_mem h1) |> fun h => by
          simpa [mul_assoc] using h
      have h4 : e * x⁻¹ * e⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (e * x * e⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [h4]
      exact h2
  have hEB : E ≤ Subgroup.normalizer (B : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    have h1 : ∀ e' ∈ E, ∀ b ∈ B, e' * b * e'⁻¹ ∈ B := by
      intro e' he' b hb
      have h2 : e' * b * e'⁻¹ = (e' * b * e'⁻¹ * b⁻¹) * b := by group
      rw [h2]
      exact B.mul_mem (hOB (hcommB e' he' b hb)) hb
    intro b
    constructor
    · exact h1 e he b
    · intro hb
      have := h1 e⁻¹ (E.inv_mem he) _ hb
      simpa [mul_assoc] using this
  have hfix : ∀ b : ↥B, ∃ c ∈ (B ⊓ Subgroup.centralizer (E : Set G)).subgroupOf B,
      c * b⁻¹ ∈ O.subgroupOf B := by
    intro b
    obtain ⟨c, hcB, hcc, hcb⟩ :=
      exists_fixed_in_coset hℓ hℓ2 O B E hO hOB hEO hEB hE hcommB b b.2
    exact ⟨⟨c, hcB⟩, Subgroup.mem_subgroupOf.2 ⟨hcB, hcc⟩, Subgroup.mem_subgroupOf.2 hcb⟩
  haveI := hNormOB
  have hOpg : IsPGroup 2 (O.subgroupOf B) := hO.of_equiv (Subgroup.subgroupOfEquivOfLe hOB).symm
  have hApg : IsPGroup p (A.subgroupOf B) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAB).symm
  have hAO' : A.subgroupOf B ⊔ O.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAB hOB]
    exact Subgroup.subgroupOf_self B
  obtain ⟨S, hSC, ⟨e⟩⟩ := exists_sylow_copy (Bg := ↥B) hp hp2 (O.subgroupOf B) (A.subgroupOf B)
    ((B ⊓ Subgroup.centralizer (E : Set G)).subgroupOf B) hOpg hApg hAO' hfix
  refine ⟨S.map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_subgroupOf.1 (hSC hs)).2
  · rintro _ ⟨s, hs, rfl⟩
    exact s.2
  · exact ⟨((Subgroup.equivMapOfInjective S B.subtype B.subtype_injective).symm.trans e).trans
      (Subgroup.subgroupOfEquivOfLe hAB)⟩

theorem card_map_of_disjoint_ker {H K : Type*} [Group H] [Group K] (f : H →* K) (Q : Subgroup H)
    (hQ : Disjoint Q f.ker) : Nat.card (Q.map f) = Nat.card Q := by
  have hinj : Function.Injective (f.domRestrict Q) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (x : H) ∈ f.ker := hx
    have := Subgroup.disjoint_def.1 hQ x.2 hx1
    exact Subtype.ext this
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h
  exact h.symm

theorem isElemAbelian_of_disjoint_ker {H K : Type*} [Group H] [Group K] (f : H →* K)
    (Q : Subgroup H) (hQ : Disjoint Q f.ker) {p : ℕ} (h : CFSG.Open.IsElemAbelian p (Q.map f)) :
    CFSG.Open.IsElemAbelian p Q := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h1 : f a * f b = f b * f a := by
      have := mul_comm' (⟨f a, ⟨a, a.2, rfl⟩⟩ : ↥(Q.map f)) ⟨f b, ⟨b, b.2, rfl⟩⟩
      exact congrArg Subtype.val this
    apply Subtype.ext
    have hmem : ((a : H) * b)⁻¹ * (b * a) ∈ Q :=
      Q.mul_mem (Q.inv_mem (Q.mul_mem a.2 b.2)) (Q.mul_mem b.2 a.2)
    have hker : ((a : H) * b)⁻¹ * (b * a) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h1, inv_mul_cancel]
    have h2 := Subgroup.disjoint_def.1 hQ hmem hker
    have h3 : (a : H) * b = b * a := inv_mul_eq_one.1 h2
    simpa using h3
  · have h1 : f (x ^ p) = 1 := by rw [map_pow]; exact hp _ ⟨x, hx, rfl⟩
    exact Subgroup.disjoint_def.1 hQ (Q.pow_mem hx p) h1

theorem isElemAbelian_of_mulEquiv {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (e : ↥A ≃* ↥B) (h : CFSG.Open.IsElemAbelian p B) : CFSG.Open.IsElemAbelian p A :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
    (CFSG.IsElementaryAbelian.of_mulEquiv e.symm (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h))

theorem closure_pPrime_map {N Γ : Type*} [Group N] [Group Γ] (ρ : N →* Γ) (Mn : Subgroup N)
    {p : ℕ} (h : Subgroup.closure {x | x ∈ Mn ∧ ¬ p ∣ orderOf x} = Mn) :
    Subgroup.closure {y | y ∈ Mn.map ρ ∧ ¬ p ∣ orderOf y} = Mn.map ρ := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 (fun y hy => hy.1)
  · calc Mn.map ρ = (Subgroup.closure {x | x ∈ Mn ∧ ¬ p ∣ orderOf x}).map ρ := by rw [h]
      _ = Subgroup.closure (ρ '' {x | x ∈ Mn ∧ ¬ p ∣ orderOf x}) := MonoidHom.map_closure ρ _
      _ ≤ _ := by
        apply Subgroup.closure_mono
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.1, rfl⟩, fun hd => hx.2 (hd.trans (orderOf_map_dvd ρ x))⟩

theorem closure_pPrime_subgroupOf {G : Type*} [Group G] {N M : Subgroup G} (hMN : M ≤ N) {p : ℕ}
    (h : Subgroup.closure {x : G | x ∈ M ∧ ¬ p ∣ orderOf x} = M) :
    Subgroup.closure {y : ↥N | y ∈ M.subgroupOf N ∧ ¬ p ∣ orderOf y} = M.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  have h1 : (Subgroup.closure {y : ↥N | y ∈ M.subgroupOf N ∧ ¬ p ∣ orderOf y}).map N.subtype =
      Subgroup.closure {x : G | x ∈ M ∧ ¬ p ∣ orderOf x} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, by
        show ¬ p ∣ orderOf (y : G)
        rwa [Subgroup.orderOf_coe]⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hMN hx1⟩, ⟨hx1, ?_⟩, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact hx2
  rw [h1, h, Subgroup.map_subgroupOf_eq_of_le hMN]

theorem eq_one_of_mem_isPGroup_of_mem_isPGroup {G : Type*} [Group G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {P O : Subgroup G} (hP : IsPGroup q P) (hO : IsPGroup 2 O) {x : G} (hxP : x ∈ P)
    (hxO : x ∈ O) : x = 1 := by
  obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
  obtain ⟨b, hb⟩ := hO ⟨x, hxO⟩
  have ha' : x ^ q ^ a = 1 := by simpa using ha
  have hb' : x ^ 2 ^ b = 1 := by simpa using hb
  have hcop : Nat.Coprime (q ^ a) (2 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have h1 : orderOf x ∣ Nat.gcd (q ^ a) (2 ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
  rw [hcop.gcd_eq_one] at h1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
