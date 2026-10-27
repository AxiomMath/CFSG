module

public import CFSG.Quasithin.H13.A7HyperplaneBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Module Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem hammingNorm_pair : ∀ i k : Fin 7, i ≠ k →
    hammingNorm (Pi.single i 1 + Pi.single k 1 : Fin 7 → ZMod 2) = 2 := by
  decide +kernel

theorem exists_fixed_of_mul_self_eq_one {σ : Perm (Fin 7)} (h : σ * σ = 1) : ∃ j, σ j = j := by
  have hσ : σ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, h]
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  by_contra hcon
  push Not at hcon
  have hempty : σ.supportᶜ = ∅ := by
    ext j
    simp [Equiv.Perm.mem_support, hcon j]
  rw [hempty, Finset.card_empty, Fintype.card_fin] at hmod
  exact absurd hmod (by decide)

theorem zmodTwo_sub_eq_add : ∀ a b : ZMod 2, a - b = a + b := by
  decide

theorem fun_sub_eq_add (u v : Fin 7 → ZMod 2) : u - v = u + v :=
  funext fun i => zmodTwo_sub_eq_add (u i) (v i)

theorem commutator_mem_of_mem_normalizer {P : Subgroup G} {a : G}
    (ha : a ∈ normalizer (P : Set G)) (x : P) : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ P := by
  have h : (x : G) * a * (x : G)⁻¹ * a⁻¹ = x * (a * (x : G)⁻¹ * a⁻¹) := by group
  rw [h]
  exact P.mul_mem x.2 ((mem_normalizer_iff.1 ha _).1 (P.inv_mem x.2))

theorem vec_commutator {P : Subgroup G} (ψ : P ≃* Multiplicative (evenWeight 7)) {a : G}
    (ha : a ∈ normalizer (P : Set G)) {σ : Perm (Fin 7)} (hσ : IsCoordAct ψ a σ) (x : P) :
    vec ψ ⟨(x : G) * a * (x : G)⁻¹ * a⁻¹, commutator_mem_of_mem_normalizer ha x⟩ =
      vec ψ x + permAct7 σ (vec ψ x) := by
  have hy : a * (x : G) * a⁻¹ ∈ P := (mem_normalizer_iff.1 ha x).1 x.2
  have he : (⟨(x : G) * a * (x : G)⁻¹ * a⁻¹, commutator_mem_of_mem_normalizer ha x⟩ : P) =
      x * (⟨a * x * a⁻¹, hy⟩ : P)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he, vec_mul, vec_inv, hσ x ⟨a * x * a⁻¹, hy⟩ rfl]

theorem eq_thirtyTwo_of_pow {k : ℕ} (hk : k ≤ 6) (h1 : 32 ≤ 2 ^ k) (h3 : 2 ^ k ≠ 64) :
    2 ^ k = 32 := by
  interval_cases k <;> simp_all

theorem nat_card_hyperplaneStd : Nat.card hyperplaneStd = 32 := by
  have h : (Finset.univ.filter fun x : Fin 7 → ZMod 2 =>
      ∑ i, x i = 0 ∧ x 0 + x 1 + x 2 + x 3 = 0).card = 32 := by
    decide +kernel
  rw [← h, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

theorem hyperplane_claim {P Q : Subgroup G}
    (ψP : P ≃* Multiplicative (evenWeight 7)) (ψQ : Q ≃* Multiplicative (evenWeight 7))
    (hPact : ∀ n ∈ normalizer (P : Set G), ∃ σ, IsCoordAct ψP n σ)
    (hQ4 : ∀ H : Subgroup G, H ≤ Q → 16 ≤ Nat.card H →
      centralizer (H : Set G) ≤ normalizer (Q : Set G))
    (hPQ : P ≠ Q → ∀ x : P, (x : G) ∈ Q → x ≠ 1 → hammingNorm (vec ψP x) = 4)
    (hA : 32 ≤ Nat.card (Q ⊓ normalizer (P : Set G) : Subgroup G))
    (hPA : ⁅P, Q ⊓ normalizer (P : Set G)⁆ ≠ ⊥) :
    Nat.card (Q ⊓ normalizer (P : Set G) : Subgroup G) = 32 ∧
      Nat.card (P ⊓ normalizer (Q : Set G) : Subgroup G) = 32 ∧
      ⁅P ⊓ normalizer (Q : Set G), Q ⊓ normalizer (P : Set G)⁆ ≠ ⊥ ∧
      (∀ a ∈ Q ⊓ normalizer (P : Set G), a ∉ centralizer (P : Set G) →
        Nat.card (Set.range fun x : P => (x : G) * a * (x : G)⁻¹ * a⁻¹) = 4) ∧
      P ⊓ centralizer ((Q ⊓ normalizer (P : Set G) : Subgroup G) : Set G) ≤
        normalizer (Q : Set G) ∧
      ∃ u : P, (u : G) ∈ centralizer ((Q ⊓ normalizer (P : Set G) : Subgroup G) : Set G) ∧
        hammingNorm (vec ψP u) = 2 := by
  classical
  set A := Q ⊓ normalizer (P : Set G) with hAdef
  set R := P ⊓ normalizer (Q : Set G) with hRdef
  have hAN : A ≤ normalizer (P : Set G) := inf_le_right
  have hAQ : A ≤ Q := inf_le_left
  have hAact : ∀ a ∈ A, ∃ σ, IsCoordAct ψP a σ := fun a ha => hPact a (hAN ha)
  set ρ := coordRep ψP hAN hAact with hρdef
  have hspec := coordRep_spec ψP hAN hAact
  have hρ1 := coordRep_eq_one_iff ψP hAN hAact
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_vec ψP ⟨x, hx⟩ ⟨y, hy⟩)
  have hPsq : ∀ x ∈ P, x * x = 1 := fun x hx => congrArg Subtype.val (sq_eq_one_of_vec ψP ⟨x, hx⟩)
  have hQsq : ∀ q ∈ Q, q * q = 1 := fun q hq => congrArg Subtype.val (sq_eq_one_of_vec ψQ ⟨q, hq⟩)
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_vec ψQ ⟨x, hx⟩ ⟨y, hy⟩)
  have hP64 : Nat.card P = 64 := nat_card_of_vec ψP
  have hQ64 : Nat.card Q = 64 := nat_card_of_vec ψQ
  have hPfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP64]; norm_num)
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ64]; norm_num)
  have hconjP : ∀ a ∈ normalizer (P : Set G), ∀ x : P, a * (x : G) * a⁻¹ ∈ P :=
    fun a ha x => (mem_normalizer_iff.1 ha x).1 x.2
  have hmove : ∃ a ∈ A, a ∉ centralizer (P : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hPA
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_iff.1 (hcon a ha) x hx).symm
  have hPneQ : P ≠ Q := by
    intro h
    obtain ⟨a, haA, haP⟩ := hmove
    apply haP
    rw [mem_centralizer_iff]
    intro x hx
    exact hPcomm x hx a (h ▸ hAQ haA)
  have hwt4 := hPQ hPneQ
  have hcommQ : ∀ x : P, (x : G) ∈ normalizer (Q : Set G) → ∀ a ∈ A,
      (x : G) * (a * x * a⁻¹) ∈ Q := by
    intro x hx a ha
    have h1 : (x : G) * (a * x * a⁻¹) = (x * a * (x : G)⁻¹) * a⁻¹ := by
      have : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (hPsq x x.2)
      rw [this]
      group
    rw [h1]
    exact Q.mul_mem ((mem_normalizer_iff.1 hx a).1 (hAQ ha)) (Q.inv_mem (hAQ ha))
  have hvec_comm : ∀ (x : P) (a : A),
      vec ψP (x * ⟨(a : G) * x * (a : G)⁻¹, hconjP a (hAN a.2) x⟩) =
        vec ψP x + permAct7 (ρ a) (vec ψP x) := by
    intro x a
    rw [vec_mul, hspec a x ⟨(a : G) * x * (a : G)⁻¹, hconjP a (hAN a.2) x⟩ rfl]
  have hPnotN : ¬ P ≤ normalizer (Q : Set G) := by
    intro hPN
    obtain ⟨a, haA, haP⟩ := hmove
    set σ := ρ ⟨a, haA⟩ with hσdef
    have hσ1 : σ ≠ 1 := fun h => haP ((hρ1 _).1 h)
    have hσ2 : σ * σ = 1 := by
      rw [hσdef, ← map_mul]
      apply (hρ1 _).2
      have : ((⟨a, haA⟩ * ⟨a, haA⟩ : A) : G) = 1 := hQsq a (hAQ haA)
      rw [this]
      exact one_mem _
    obtain ⟨j, hj⟩ := exists_fixed_of_mul_self_eq_one hσ2
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hcon
      push Not at hcon
      exact hσ1 (Perm.ext hcon)
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    obtain ⟨x, hx⟩ := exists_vec_eq ψP (pair_mem_evenWeight i j)
    have hc := hvec_comm x ⟨a, haA⟩
    rw [hx, map_add, permAct7_single, permAct7_single, hj] at hc
    have hc' : vec ψP (x * ⟨a * x * a⁻¹, hconjP a (hAN haA) x⟩) =
        Pi.single i 1 + Pi.single (σ i) 1 := by
      rw [hc]
      have h2 := fun_add_self_eq_zero (Pi.single j 1 : Fin 7 → ZMod 2)
      calc Pi.single i 1 + Pi.single j 1 + (Pi.single (σ i) 1 + Pi.single j 1)
          = Pi.single i 1 + Pi.single (σ i) 1 + (Pi.single j 1 + Pi.single j 1) := by abel
        _ = _ := by rw [h2, add_zero]
    have hne1 : x * ⟨a * x * a⁻¹, hconjP a (hAN haA) x⟩ ≠ 1 := by
      intro h1
      rw [h1, vec_one] at hc'
      have h3 := congrFun hc' i
      simp only [Pi.zero_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hi)] at h3
      exact absurd h3 (by decide)
    have h4 := hwt4 _ (hcommQ x (hPN x.2) a haA) hne1
    rw [hc', hammingNorm_pair i (σ i) (Ne.symm hi)] at h4
    exact absurd h4 (by norm_num)
  have hC16 : Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) < 16 := by
    by_contra h
    push Not at h
    apply hPnotN
    have h1 := hQ4 (A ⊓ centralizer (P : Set G)) (inf_le_left.trans hAQ) h
    intro x hx
    apply h1
    rw [mem_centralizer_iff]
    intro c hc
    exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 x hx).symm
  have hC8 : Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) ≤ 8 := by
    have hdvd : Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hQ64]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans hAQ)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hk'] at hC16 ⊢
    have : k ≤ 3 := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      _ = 8 := by norm_num
  set B : Subgroup (Perm (Fin 7)) := ρ.range with hBdef
  have hρker : ρ.ker = (centralizer (P : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hρ1 a
  have hcardker : Nat.card ρ.ker = Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) := by
    rw [hρker, ← Subgroup.card_map_of_injective A.subtype_injective, subgroupOf_map_subtype,
      inf_comm]
  have hcardA : Nat.card A = Nat.card B * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hBel : CFSG.IsElementaryAbelian 2 B :=
    { is_comm := ⟨fun x y => by
        obtain ⟨a, ha⟩ := x.2
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← ha, ← hb, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hQcomm a (hAQ a.2) b (hAQ b.2))⟩
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_of_forall_pow_eq_one
        intro x
        obtain ⟨a, ha⟩ := x.2
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← ha, ← map_pow, pow_two]
        have : a * a = 1 := Subtype.ext (hQsq a (hAQ a.2))
        rw [this, map_one] }
  have hB4 : 4 ≤ Nat.card B := by
    have h1 := hcardA
    rw [hcardker] at h1
    by_contra h
    push Not at h
    have : Nat.card A ≤ 3 * 8 := h1 ▸ Nat.mul_le_mul (by omega) hC8
    omega
  have hWR : hyperplaneSum B ≤ imgSub ψP (normalizer (Q : Set G)) := by
    refine iSup₂_le fun X hX => ?_
    obtain ⟨hXB, hXidx⟩ := hX
    intro e he
    obtain ⟨heE, hefix⟩ := mem_fixedEven.1 he
    obtain ⟨x, rfl⟩ := exists_vec_eq ψP heE
    set AX : Subgroup A := X.comap ρ with hAXdef
    have hAXidx : AX.index = 2 := by
      rw [hAXdef, Subgroup.index_comap]
      exact hXidx
    have hAX16 : 16 ≤ Nat.card (AX.map A.subtype) := by
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      have h := Subgroup.card_mul_index AX
      rw [hAXidx] at h
      omega
    refine ⟨x, hQ4 _ ((Subgroup.map_subtype_le AX).trans hAQ) hAX16 ?_, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hspec a x ⟨(a : G) * x * (a : G)⁻¹, hconjP a (hAN a.2) x⟩ rfl
    rw [hefix (ρ a) ha] at h1
    have h2 : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val (vec_injective ψP h1)
    calc (A.subtype a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by simp
      _ = x * a := by rw [h2]
  have hCQ : commSpan B ≤ imgSub ψP Q := by
    rw [commSpan, Submodule.span_le]
    rintro _ ⟨w, hw, _, ⟨a, rfl⟩, rfl⟩
    obtain ⟨x, hxN, rfl⟩ := hWR hw
    exact ⟨x * ⟨(a : G) * x * (a : G)⁻¹, hconjP a (hAN a.2) x⟩, hcommQ x hxN a a.2,
      hvec_comm x a⟩
  have hW4 : ∀ v ∈ commSpan B, v ≠ 0 → hammingNorm v = 4 := by
    intro v hv hv0
    obtain ⟨c, hcQ, rfl⟩ := hCQ hv
    exact hwt4 c hcQ (fun h => hv0 (by rw [h, vec_one]))
  obtain ⟨σ₀, hσB, -, hσW, hσC, hσF, hFW, hrank⟩ :=
    A7_even_weight_hyperplane_centralizer_geometry hBel hB4 hW4
  have hB4' : Nat.card B = 4 := by
    rw [← nat_card_kleinStd, ← hσB,
      Subgroup.card_map_of_injective (MulAut.conj σ₀).injective]
  have hAcard : Nat.card A = 32 := by
    have h1 := hcardA
    rw [hcardker, hB4'] at h1
    omega
  have hpermInj : Function.Injective (permAct7 σ₀) := fun u v h => by
    have := congrArg (permAct7 σ₀⁻¹) h
    rwa [permAct7_inv_apply, permAct7_inv_apply] at this
  have hW32 : Nat.card (hyperplaneSum B) = 32 := by
    rw [← nat_card_hyperplaneStd, ← hσW]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hpermInj _).toEquiv
  have hRcard : Nat.card R = 32 := by
    have h1 : 32 ≤ Nat.card R := by
      rw [← hW32, hRdef, ← nat_card_imgSub ψP (normalizer (Q : Set G))]
      exact Nat.card_le_card_of_injective (Submodule.inclusion hWR)
        (Submodule.inclusion_injective hWR)
    have h2 : Nat.card R ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hP64]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card R ≠ 64 := by
      intro h
      apply hPnotN
      have : R = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hP64])
      rw [← this]
      exact inf_le_right
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rw [hk'] at h1 h3 ⊢
    exact eq_thirtyTwo_of_pow hk h1 h3
  have hRA : ⁅R, A⁆ ≠ ⊥ := by
    have hne : commSpan B ≠ ⊥ := by
      intro h
      have h1 := hσC
      rw [h, Submodule.map_bot] at h1
      have h2 : vecFirstFour ∈ (⊥ : Submodule (ZMod 2) (Fin 7 → ZMod 2)) :=
        h1 ▸ Submodule.subset_span rfl
      rw [Submodule.mem_bot] at h2
      exact absurd (congrFun h2 0) (by decide)
    obtain ⟨w, hw, b, hb, hwb⟩ : ∃ w ∈ hyperplaneSum B, ∃ b ∈ B, w + permAct7 b w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [commSpan, Submodule.span_eq_bot]
      rintro _ ⟨w, hw, b, hb, rfl⟩
      exact hcon w hw b hb
    obtain ⟨a, rfl⟩ := hb
    obtain ⟨x, hxN, rfl⟩ := hWR hw
    intro hbot
    apply hwb
    have hmem : ⁅(x : G), (a : G)⁆ ∈ ⁅R, A⁆ := commutator_mem_commutator ⟨x.2, hxN⟩ a.2
    rw [hbot, mem_bot, commutatorElement_def] at hmem
    rw [← vec_commutator ψP (hAN a.2) (hspec a) x, vec_eq_zero_iff]
    exact Subtype.ext hmem
  have hcomm4 : ∀ a ∈ A, a ∉ centralizer (P : Set G) →
      Nat.card (Set.range fun x : P => (x : G) * a * (x : G)⁻¹ * a⁻¹) = 4 := by
    intro a ha haP
    have hb : ρ ⟨a, ha⟩ ≠ 1 := fun h => haP ((hρ1 _).1 h)
    have hr := hrank (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ hb
    have h4 : Nat.card ((evenWeight 7).map (permAct7 (ρ ⟨a, ha⟩) - LinearMap.id)) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hr]
      norm_num
    rw [← h4]
    have hmemP : ∀ x : P, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ P :=
      commutator_mem_of_mem_normalizer (hAN ha)
    have hvc := vec_commutator ψP (hAN ha) (hspec ⟨a, ha⟩)
    let F : (Set.range fun x : P => (x : G) * a * (x : G)⁻¹ * a⁻¹) →
        (evenWeight 7).map (permAct7 (ρ ⟨a, ha⟩) - LinearMap.id) := fun s =>
      ⟨vec ψP ⟨s.1, by obtain ⟨x, hx⟩ := s.2; rw [← hx]; exact hmemP x⟩, by
        obtain ⟨x, hx⟩ := s.2
        refine ⟨vec ψP x, vec_mem ψP x, ?_⟩
        have : (⟨s.1, by obtain ⟨x, hx⟩ := s.2; rw [← hx]; exact hmemP x⟩ : P) =
            ⟨(x : G) * a * (x : G)⁻¹ * a⁻¹, hmemP x⟩ := Subtype.ext hx.symm
        rw [this, hvc x, LinearMap.sub_apply, LinearMap.id_apply, fun_sub_eq_add, add_comm]⟩
    have hF : Function.Bijective F := by
      refine ⟨fun s t h => ?_, fun m => ?_⟩
      · have h1 := congrArg (fun e : (evenWeight 7).map (permAct7 (ρ ⟨a, ha⟩) - LinearMap.id) =>
          (e : Fin 7 → ZMod 2)) h
        have h2 := vec_injective ψP h1
        exact Subtype.ext (congrArg (fun z : P => (z : G)) h2)
      · obtain ⟨e, he, hem⟩ := m.2
        obtain ⟨x, rfl⟩ := exists_vec_eq ψP he
        refine ⟨⟨_, x, rfl⟩, Subtype.ext ?_⟩
        change vec ψP ⟨(x : G) * a * (x : G)⁻¹ * a⁻¹, _⟩ = m
        rw [hvc x, ← hem, LinearMap.sub_apply, LinearMap.id_apply, fun_sub_eq_add, add_comm]
    exact Nat.card_congr (Equiv.ofBijective F hF)
  have hfixC : ∀ x : P, (x : G) ∈ centralizer (A : Set G) → vec ψP x ∈ fixedEven B := by
    intro x hx
    refine ⟨vec_mem ψP x, ?_⟩
    rintro _ ⟨a, rfl⟩
    have h1 : (x : G) = a * x * (a : G)⁻¹ := by
      rw [mem_centralizer_iff.1 hx a a.2]
      group
    exact (hspec a x x h1).symm
  have hCPA : P ⊓ centralizer (A : Set G) ≤ normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨hxP, hxA⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨x', hx'N, hx'⟩ := hWR (hFW (hfixC ⟨x, hxP⟩ hxA))
    have : x' = ⟨x, hxP⟩ := vec_injective ψP hx'
    rw [this] at hx'N
    exact hx'N
  obtain ⟨u, hu⟩ : ∃ u : P, (u : G) ∈ centralizer (A : Set G) ∧
      hammingNorm (vec ψP u) = 2 := by
    have h1 : (Pi.single 4 1 + Pi.single 5 1 : Fin 7 → ZMod 2) ∈
        (fixedEven B).map (permAct7 σ₀) := by
      rw [hσF]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨v, hv, hve⟩ := h1
    obtain ⟨u, rfl⟩ := exists_vec_eq ψP (mem_fixedEven.1 hv).1
    refine ⟨u, ?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro a ha
      have h2 := hspec ⟨a, ha⟩ u ⟨a * u * a⁻¹, hconjP a (hAN ha) u⟩ rfl
      rw [(mem_fixedEven.1 hv).2 (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩] at h2
      have h3 : a * (u : G) * a⁻¹ = u := congrArg Subtype.val (vec_injective ψP h2)
      calc a * (u : G) = a * u * a⁻¹ * a := by group
        _ = u * a := by rw [h3]
    · rw [← hammingNorm_permAct7 σ₀, hve]
      exact hammingNorm_pair 4 5 (by decide)
  exact ⟨hAcard, hRcard, hRA, hcomm4, hCPA, u, hu⟩

theorem mem_conj_smul_iff {V : Subgroup G} {g x : G} :
    x ∈ MulAut.conj g⁻¹ • V ↔ g * x * g⁻¹ ∈ V := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
    MulAut.conj_apply]

theorem conj_smul_eq_self_iff {V : Subgroup G} {g : G} :
    MulAut.conj g⁻¹ • V = V ↔ g ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    rw [← mem_conj_smul_iff, h]
  · intro h
    ext x
    rw [mem_conj_smul_iff, ← h]

theorem mem_normalizer_conj_smul_iff {V : Subgroup G} {g x : G} :
    x ∈ normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g⁻¹ * y * g)
    rw [mem_conj_smul_iff, mem_conj_smul_iff] at this
    convert this using 2 <;> group
  · intro h y
    rw [mem_conj_smul_iff, mem_conj_smul_iff]
    convert h (g * y * g⁻¹) using 2
    group

@[expose] noncomputable def conjIso (V : Subgroup G) (g : G) :
    (MulAut.conj g⁻¹ • V : Subgroup G) ≃* V where
  toFun x := ⟨g * x * g⁻¹, mem_conj_smul_iff.1 x.2⟩
  invFun v := ⟨g⁻¹ * v * g, mem_conj_smul_iff.2 (by
    rw [show g * (g⁻¹ * (v : G) * g) * g⁻¹ = v by group]
    exact v.2)⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv v := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjIso (V : Subgroup G) (g : G) (x : (MulAut.conj g⁻¹ • V : Subgroup G)) :
    ((conjIso V g x : V) : G) = g * x * g⁻¹ :=
  rfl

theorem card_range_commutator_eq_relIndex {V : Subgroup G}
    (hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {a : G} (ha : a ∈ normalizer (V : Set G)) :
    Nat.card (Set.range fun v : V => (v : G) * a * (v : G)⁻¹ * a⁻¹) =
      (centralizer ({a} : Set G)).relIndex V := by
  have hmem : ∀ v : V, (v : G) * a * (v : G)⁻¹ * a⁻¹ ∈ V :=
    commutator_mem_of_mem_normalizer ha
  have hconj : ∀ v : V, a * (v : G)⁻¹ * a⁻¹ ∈ V := fun v =>
    (mem_normalizer_iff.1 ha _).1 (V.inv_mem v.2)
  let δ : V →* V :=
    { toFun := fun v => ⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hmem v⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have h1 : (a * (x : G)⁻¹ * a⁻¹) * ((y : G) * (a * (y : G)⁻¹ * a⁻¹)) =
            ((y : G) * (a * (y : G)⁻¹ * a⁻¹)) * (a * (x : G)⁻¹ * a⁻¹) :=
          hVcomm _ (hconj x) _ (V.mul_mem y.2 (hconj y))
        simp only [Subgroup.coe_mul]
        calc (x : G) * y * a * ((x : G) * y)⁻¹ * a⁻¹
            = x * (((y : G) * (a * (y : G)⁻¹ * a⁻¹)) * (a * (x : G)⁻¹ * a⁻¹)) := by group
          _ = x * ((a * (x : G)⁻¹ * a⁻¹) * ((y : G) * (a * (y : G)⁻¹ * a⁻¹))) := by rw [h1]
          _ = x * a * (x : G)⁻¹ * a⁻¹ * (y * a * (y : G)⁻¹ * a⁻¹) := by group) }
  have hker : δ.ker = (centralizer ({a} : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (v : G) * a * (v : G)⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h
      calc (v : G) * a = ((v : G) * a * (v : G)⁻¹ * a⁻¹) * (a * v) := by group
        _ = a * v := by rw [h1, one_mul]
    · intro h
      apply Subtype.ext
      change (v : G) * a * (v : G)⁻¹ * a⁻¹ = 1
      rw [h]
      group
  have hsub := Set.range_subset_iff.2 hmem
  have hrange : Nat.card δ.range =
      Nat.card (Set.range fun v : V => (v : G) * a * (v : G)⁻¹ * a⁻¹) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨((w : V) : G), by
          obtain ⟨v, hv⟩ := w.2
          exact ⟨v, congrArg Subtype.val hv⟩⟩
        invFun := fun y => ⟨⟨y.1, hsub y.2⟩, by
          obtain ⟨v, hv⟩ := y.2
          exact ⟨v, Subtype.ext hv⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem A7_no_noncentral_normalizing_hyperplane {V M : Subgroup G}
    (_hV : CFSG.IsElementaryAbelian 2 V) (_hV64 : Nat.card V = 64)
    (_hNM : normalizer (V : Set G) ≤ M) (φ : V ≃* Multiplicative (evenWeight 7))
    (hact : ∀ n ∈ normalizer (V : Set G), ∃ σ : Perm (Fin 7), ∀ v w : V,
      (w : G) = n * v * n⁻¹ →
        ((Multiplicative.toAdd (φ w) : evenWeight 7) : Fin 7 → ZMod 2) =
          permAct7 σ ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2))
    (hTI : ∀ m ∈ M, MulAut.conj m⁻¹ • V = V ∨ V ⊓ (MulAut.conj m⁻¹ • V) = ⊥)
    (hwt2 : ∀ v : V,
      hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 2 →
        centralizer ({(v : G)} : Set G) ≤ M)
    (hwt4 : ∀ g : G, MulAut.conj g⁻¹ • V ≠ V → ∀ v : V,
      (v : G) ∈ MulAut.conj g⁻¹ • V → v ≠ 1 →
        hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 4) :
    (∀ g : G, ((MulAut.conj g⁻¹ • V) ⊓ normalizer (V : Set G)).relIndex
        (MulAut.conj g⁻¹ • V) ≤ 2 →
      ⁅V, (MulAut.conj g⁻¹ • V) ⊓ normalizer (V : Set G)⁆ = ⊥) ∧
      ∀ H : Subgroup G, H ≤ V → 16 ≤ Nat.card H →
        centralizer (H : Set G) ≤ normalizer (V : Set G) := by
  classical
  have hact' : ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct φ n σ := hact
  have hV64' : Nat.card V = 64 := nat_card_of_vec φ
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV64']; norm_num)
  have hF2 : ∀ H : Subgroup G, H ≤ V → 16 ≤ Nat.card H →
      centralizer (H : Set G) ≤ normalizer (V : Set G) := by
    intro H hHV hH x hx
    rw [← conj_smul_eq_self_iff]
    by_contra hne
    have h8 := card_inf_le_eight φ (S := MulAut.conj x⁻¹ • V) (hwt4 x hne)
    have hle : H ≤ V ⊓ (MulAut.conj x⁻¹ • V) := fun h hh => Subgroup.mem_inf.2 ⟨hHV hh, by
      rw [mem_conj_smul_iff, ← mem_centralizer_iff.1 hx h hh, mul_inv_cancel_right]
      exact hHV hh⟩
    have : Finite (V ⊓ (MulAut.conj x⁻¹ • V) : Subgroup G) :=
      Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    have h9 := Subgroup.card_le_of_le hle
    omega
  have hF2g : ∀ g : G, ∀ H : Subgroup G, H ≤ MulAut.conj g⁻¹ • V → 16 ≤ Nat.card H →
      centralizer (H : Set G) ≤ normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G) := by
    intro g H hHV hH x hx
    rw [mem_normalizer_conj_smul_iff]
    have hH'V : H.map (MulAut.conj g).toMonoidHom ≤ V := by
      rintro _ ⟨h, hh, rfl⟩
      exact mem_conj_smul_iff.1 (hHV hh)
    have hH' : 16 ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hH
    apply hF2 _ hH'V hH'
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have h1 := mem_centralizer_iff.1 hx h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * x * g⁻¹) = g * (h * x) * g⁻¹ := by group
      _ = g * (x * h) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * h * g⁻¹) := by group
  have hactg : ∀ g : G, ∀ n ∈ normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G),
      ∃ σ, IsCoordAct ((conjIso V g).trans φ) n σ := by
    intro g n hn
    obtain ⟨σ, hσ⟩ := hact' (g * n * g⁻¹) (mem_normalizer_conj_smul_iff.1 hn)
    refine ⟨σ, fun x y hxy => ?_⟩
    change vec φ (conjIso V g y) = permAct7 σ (vec φ (conjIso V g x))
    apply hσ
    rw [coe_conjIso, coe_conjIso, hxy]
    group
  have hPQ2 : ∀ g : G, MulAut.conj g⁻¹ • V ≠ V → ∀ x : (MulAut.conj g⁻¹ • V : Subgroup G),
      (x : G) ∈ V → x ≠ 1 → hammingNorm (vec ((conjIso V g).trans φ) x) = 4 := by
    intro g hne x hxV hx1
    change hammingNorm (vec φ (conjIso V g x)) = 4
    have hne' : MulAut.conj g⁻¹⁻¹ • V ≠ V := by
      rw [Ne, conj_smul_eq_self_iff, Subgroup.inv_mem_iff, ← conj_smul_eq_self_iff]
      exact hne
    refine hwt4 g⁻¹ hne' _ ?_ ?_
    · rw [mem_conj_smul_iff, coe_conjIso]
      rw [show g⁻¹ * (g * (x : G) * g⁻¹) * g⁻¹⁻¹ = x by group]
      exact hxV
    · intro h
      apply hx1
      exact (conjIso V g).injective (h.trans (map_one _).symm)
  refine ⟨fun g hidx => ?_, hF2⟩
  set Q := MulAut.conj g⁻¹ • V with hQdef
  set A := Q ⊓ normalizer (V : Set G) with hAdef
  by_contra hVA
  have hQ64 : Nat.card Q = 64 := nat_card_of_vec ((conjIso V g).trans φ)
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ64]; norm_num)
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_vec ((conjIso V g).trans φ) ⟨x, hx⟩ ⟨y, hy⟩)
  have hA32 : 32 ≤ Nat.card A := by
    have h := Subgroup.card_mul_index (A.subgroupOf Q)
    have h2 : Nat.card (A.subgroupOf Q) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2, hQ64] at h
    have h3 : (A.subgroupOf Q).index ≤ 2 := hidx
    have h4 : Nat.card A * (A.subgroupOf Q).index ≤ Nat.card A * 2 :=
      Nat.mul_le_mul_left _ h3
    omega
  obtain ⟨hA32', hR32, hRA, -, hCPA, u, huA, hu2⟩ :=
    hyperplane_claim φ ((conjIso V g).trans φ) hact' (hF2g g) (fun hne => hwt4 g (Ne.symm hne))
      hA32 hVA
  have hQRA : ⁅Q, V ⊓ normalizer (Q : Set G)⁆ ≠ ⊥ := by
    intro h
    apply hRA
    rw [commutator_comm]
    exact le_bot_iff.1 (h ▸ commutator_mono inf_le_left le_rfl)
  obtain ⟨-, -, -, hcomm4, -, -⟩ :=
    hyperplane_claim ((conjIso V g).trans φ) φ (hactg g) hF2 (hPQ2 g) (hR32 ▸ le_rfl) hQRA
  have huR : (u : G) ∈ V ⊓ normalizer (Q : Set G) := ⟨u.2, hCPA ⟨u.2, huA⟩⟩
  have huQ : (u : G) ∈ centralizer (Q : Set G) := by
    by_contra hnot
    have h4 := hcomm4 u huR hnot
    rw [card_range_commutator_eq_relIndex hQcomm huR.2] at h4
    have hAu : A ≤ centralizer ({(u : G)} : Set G) := fun a ha =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 huA a ha)
    have h5 := Subgroup.relIndex_dvd_of_le_left Q hAu
    have h6 : A.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h7 := Nat.le_of_dvd (Nat.pos_of_ne_zero h6) h5
    have h8 : A.relIndex Q ≤ 2 := hidx
    omega
  have hQM : Q ≤ M := fun q hq =>
    hwt2 u hu2 (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 huQ q hq))
  have hIV : ⁅V ⊓ normalizer (Q : Set G), A⁆ ≤ V := by
    rw [commutator_le]
    intro r hr a ha
    rw [commutatorElement_def, show r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) by group]
    exact V.mul_mem hr.1 ((mem_normalizer_iff.1 ha.2 _).1 (V.inv_mem hr.1))
  have hIQ : ⁅V ⊓ normalizer (Q : Set G), A⁆ ≤ Q := by
    rw [commutator_le]
    intro r hr a ha
    rw [commutatorElement_def]
    exact Q.mul_mem ((mem_normalizer_iff.1 hr.2 a).1 ha.1) (Q.inv_mem ha.1)
  have hQN : Q ≤ normalizer (V : Set G) := by
    intro q hq
    rw [← conj_smul_eq_self_iff]
    rcases hTI q (hQM hq) with h | h
    · exact h
    · exfalso
      apply hRA
      rw [eq_bot_iff]
      intro y hy
      have hy' : y ∈ V ⊓ (MulAut.conj q⁻¹ • V) := Subgroup.mem_inf.2 ⟨hIV hy, by
        rw [mem_conj_smul_iff, hQcomm q hq y (hIQ hy), mul_inv_cancel_right]
        exact hIV hy⟩
      rw [h] at hy'
      exact hy'
  have hAQ : A = Q := le_antisymm inf_le_left (le_inf le_rfl hQN)
  have hA32'' : Nat.card A = 32 := hA32'
  rw [hAQ, hQ64] at hA32''
  omega

end CFSG.Quasithin.H13.A7
