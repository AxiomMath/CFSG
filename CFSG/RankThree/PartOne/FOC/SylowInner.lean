module

public import CFSG.RankThree.PartOne.FOCD.RankInner
public import CFSG.RankThree.PartOne.FOC.CompGroup
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankTwoLocal

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

section LemmaZ

open scoped IsMulCommutative in
theorem central_eq_one_of_perfect_abelian_sylow {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (S : Sylow p E)
    (hS : ∀ x ∈ (S : Subgroup E), ∀ y ∈ (S : Subgroup E), x * y = y * x)
    {z : E} (hz : z ∈ Subgroup.center E) (hzp : z ^ p = 1) : z = 1 := by
  have : IsMulCommutative (S : Subgroup E) :=
    ⟨⟨fun a b => Subtype.ext (hS a a.2 b b.2)⟩⟩
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup E) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := mul_assoc _ _ _
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [this]
      _ = z ^ k := inv_mul_cancel_left _ _
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup E)) z key
  have h2 : MonoidHom.transfer (MonoidHom.id (S : Subgroup E)) z = 1 := by
    set f := MonoidHom.transfer (MonoidHom.id (S : Subgroup E)) with hf
    have hperf : Group.IsPerfect f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    have hsub : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    have := Subsingleton.elim (⟨f z, ⟨z, rfl⟩⟩ : f.range) ⟨1, one_mem _⟩
    exact congrArg Subtype.val this
  rw [h2] at h1
  have h4 : z ^ (S : Subgroup E).index = 1 := by
    have := congrArg Subtype.val h1.symm
    simpa using this
  have h5 : Nat.Coprime p (S : Subgroup E).index :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 S.not_dvd_index
  have h6 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h7 : orderOf z ∣ (S : Subgroup E).index := orderOf_dvd_of_pow_eq_one h4
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h5 h6 h7)

theorem no_central_of_isQuasisimple {p : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime)
    (hab : ∀ P : Sylow p T, ∀ x ∈ (P : Subgroup T), ∀ y ∈ (P : Subgroup T), x * y = y * x)
    {E : Subgroup T} (hE : CFSG.IsQuasisimple ↥E) :
    ∀ z ∈ E ⊓ Subgroup.centralizer (E : Set T), z ^ p = 1 → z = 1 := by
  intro z hz hzp
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥E := hE.1
  obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨S⟩ : Nonempty (Sylow p ↥E) := inferInstance
  obtain ⟨Q, hQ⟩ := (S.isPGroup'.map E.subtype).exists_le_sylow
  have hSab : ∀ x ∈ (S : Subgroup ↥E), ∀ y ∈ (S : Subgroup ↥E), x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hab Q _ (hQ ⟨x, hx, rfl⟩) _ (hQ ⟨y, hy, rfl⟩)
  have hzc : (⟨z, hzE⟩ : ↥E) ∈ Subgroup.center ↥E := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC y y.2)
  have hzp' : (⟨z, hzE⟩ : ↥E) ^ p = 1 := Subtype.ext (by simpa using hzp)
  have := central_eq_one_of_perfect_abelian_sylow S hSab hzc hzp'
  exact congrArg Subtype.val this

end LemmaZ

section SylowFixed

theorem exists_normalized_sylow {T : Type*} [Group T] [Finite T] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] {E : Subgroup T} {y : T} (hyp : y ^ p = 1)
    (hyN : y ∈ Subgroup.normalizer (E : Set T)) (hpE : ¬ p ∣ Nat.card E) :
    ∃ U : Sylow r E, ∀ x ∈ (U : Subgroup E),
      y * (x : T) * y⁻¹ ∈ (U : Subgroup E).map E.subtype ∧
      y⁻¹ * (x : T) * y ∈ (U : Subgroup E).map E.subtype := by
  have hy : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set T) := Subgroup.zpowers_le.2 hyN
  let φ : Subgroup.zpowers y →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hy)
  let _ : MulDistribMulAction (Subgroup.zpowers y) E := MulDistribMulAction.compHom E φ
  have hP : IsPGroup p (Subgroup.zpowers y) := by
    have h1 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    rcases (Nat.dvd_prime Fact.out).1 h1 with h2 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h2, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints (Sylow r E)
  have hdvd : Nat.card (Sylow r E) ∣ Nat.card E := by
    obtain ⟨P⟩ : Nonempty (Sylow r E) := inferInstance
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.index_dvd_card _
  have hpS : ¬ p ∣ Nat.card (Sylow r E) := fun h => hpE (h.trans hdvd)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (Sylow r E)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hpS ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨U, hU⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix)).1
  refine ⟨U, fun x hx => ?_⟩
  have hconj : ∀ g : Subgroup.zpowers y, ∀ x ∈ (U : Subgroup E),
      ∃ u ∈ (U : Subgroup E), (u : T) = (g : T) * (x : T) * (g : T)⁻¹ := by
    intro g x hx
    have h1 : g • U = U := MulAction.mem_fixedPoints.1 hU g
    have h2 : (φ g • x : E) ∈ ((g • U : Sylow r E) : Subgroup E) :=
      Subgroup.smul_mem_pointwise_smul x g (U : Subgroup E) hx
    rw [h1] at h2
    exact ⟨φ g • x, h2, rfl⟩
  constructor
  · obtain ⟨u, hu, hux⟩ := hconj ⟨y, Subgroup.mem_zpowers y⟩ x hx
    exact ⟨u, hu, hux⟩
  · obtain ⟨u, hu, hux⟩ := hconj ⟨y⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers y)⟩ x hx
    refine ⟨u, hu, ?_⟩
    show (u : T) = _
    rw [hux]
    simp

end SylowFixed

section Inner

variable {p : ℕ} {T : Type} [Group T] [Finite T]

theorem inner_of_dvd_card (hp : p.Prime) (hA : PRankLeTwo p T) {b y : T} (hb1 : b ≠ 1)
    (hbp : b ^ p = 1) (hyp : y ^ p = 1) (hby : b * y = y * b) {E : Subgroup T}
    (hbE : ∀ e ∈ E, b * e = e * b) (hyN : y ∈ Subgroup.normalizer (E : Set T))
    (hpE : p ∣ Nat.card E)
    (hEZ : ∀ z ∈ E ⊓ Subgroup.centralizer (E : Set T), z ^ p = 1 → z = 1) :
    y ∈ E ⊔ Subgroup.centralizer (E : Set T) := by
  classical
  by_contra hyE
  have : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hbC : b ∈ Subgroup.centralizer (E : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hbE e he).symm
  have hyb : y ∉ Subgroup.zpowers b := fun h =>
    hyE (Subgroup.mem_sup_right ((Subgroup.zpowers_le.2 hbC) h))
  have hynorm : ∀ h : T, h ∈ E ↔ y * h * y⁻¹ ∈ E := Subgroup.mem_normalizer_iff.1 hyN
  have : Fintype E := Fintype.ofFinite E
  let f : Function.End ↥E := fun e => ⟨y * (e : T) * y⁻¹, (hynorm e).1 e.2⟩
  have hfpow : ∀ (n : ℕ) (e : ↥E), (((f ^ n) e : ↥E) : T) = y ^ n * (e : T) * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e; change (e : T) = y ^ 0 * (e : T) * (y ^ 0)⁻¹; simp
    | succ n ih =>
      intro e
      rw [pow_succ]
      change (((f ^ n) (f e) : ↥E) : T) = _
      rw [ih]
      change y ^ n * (y * (e : T) * y⁻¹) * (y ^ n)⁻¹ = y ^ (n + 1) * (e : T) * (y ^ (n + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
  have hf1 : f ^ p ^ 1 = 1 := by
    funext e
    apply Subtype.ext
    rw [pow_one]
    change (((f ^ p) e : ↥E) : T) = (e : T)
    rw [hfpow p e, hyp]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf1
  have hpcard : p ∣ Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    exact hpE
  have hpfix : p ∣ Fintype.card (Function.fixedPoints f) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpcard)))
  let CE : Subgroup T := E ⊓ Subgroup.centralizer ({y} : Set T)
  have hCEcard : Nat.card CE = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card (α := (Function.fixedPoints f : Set ↥E))]
    refine Nat.card_congr ⟨fun z => ⟨⟨z.1, (Subgroup.mem_inf.1 z.2).1⟩, ?_⟩,
      fun e => ⟨(e.1 : T), Subgroup.mem_inf.2 ⟨e.1.2, ?_⟩⟩, ?_, ?_⟩
    · apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).2
      change y * (z : T) * y⁻¹ = (z : T)
      calc y * (z : T) * y⁻¹ = ((z : T) * y) * y⁻¹ := by rw [h]
        _ = (z : T) := by group
    · have h : f e.1 = e.1 := e.2
      have h' : y * (e.1 : T) * y⁻¹ = (e.1 : T) := congrArg Subtype.val h
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (e.1 : T) * y = (y * (e.1 : T) * y⁻¹) * y := by rw [h']
        _ = y * (e.1 : T) := by group
    · intro z; rfl
    · intro e; rfl
  have hpCE : p ∣ Nat.card CE := hCEcard ▸ hpfix
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := CE) p hpCE
  set z' : T := (z : T) with hz'
  have hz'E : z' ∈ E := (Subgroup.mem_inf.1 z.2).1
  have hz'y : y * z' = z' * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).2).symm
  have hz'ord : orderOf z' = p := by
    rw [hz', Subgroup.orderOf_coe]
    exact hz
  have hz'p : z' ^ p = 1 := hz'ord ▸ pow_orderOf_eq_one z'
  have hz'b : b * z' = z' * b := hbE z' hz'E
  have h21 : y * b = b * y := hby.symm
  have h31 : z' * b = b * z' := hz'b.symm
  have h32 : z' * y = y * z' := hz'y.symm
  have hcomm₂ : ∀ a ∈ ({b, y} : Set T), ∀ c ∈ ({b, y} : Set T), a * c = c * a := by
    intro a ha c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> first | rfl | assumption
  have hpow₂ : ∀ a ∈ ({b, y} : Set T), a ^ p = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hbp
    · exact hyp
  have hcomm₃ : ∀ a ∈ ({b, y, z'} : Set T), ∀ c ∈ ({b, y, z'} : Set T), a * c = c * a := by
    intro a ha c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
    rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
      first | rfl | assumption
  have hpow₃ : ∀ a ∈ ({b, y, z'} : Set T), a ^ p = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hbp
    · exact hyp
    · exact hz'p
  set A₁ : Subgroup T := Subgroup.zpowers b with hA₁
  set A₂ : Subgroup T := Subgroup.closure {b, y} with hA₂
  set A₃ : Subgroup T := Subgroup.closure {b, y, z'} with hA₃
  have hA₁₂ : A₁ ≤ A₂ := by
    rw [hA₁, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hA₂₃ : A₂ ≤ A₃ := by
    rw [hA₂, Subgroup.closure_le]
    intro a ha
    exact Subgroup.subset_closure (by rcases ha with rfl | rfl <;> simp)
  have hyA₂ : y ∈ A₂ := Subgroup.subset_closure (by simp)
  have hz'A₃ : z' ∈ A₃ := Subgroup.subset_closure (by simp)
  have hP₂ : IsPGroup p A₂ := isPGroup_closure hp hcomm₂ hpow₂
  have hP₃ : IsPGroup p A₃ := isPGroup_closure hp hcomm₃ hpow₃
  have hcardA₁ : Nat.card A₁ = p := by rw [hA₁, Nat.card_zpowers, hbord]
  have h12 : p * p ≤ Nat.card A₂ := by
    have := p_mul_card_le_of_not_mem hp hA₁₂ hP₂ hyA₂ hyb
    rwa [hcardA₁] at this
  have hA₂le : Nat.card A₂ ≤ p ^ 2 :=
    hA (A₂) (fun r hr => pow_eq_one_of_mem_closure hcomm₂ hpow₂ r hr)
      (fun r hr s hs => commute_of_mem_closure hcomm₂ r hr s hs)
  have hA₂card : Nat.card A₂ = p ^ 2 := by nlinarith
  set N : Subgroup T := E ⊔ Subgroup.centralizer (E : Set T) with hN
  have hA₁N : A₁ ≤ A₂ ⊓ N := le_inf hA₁₂ ((Subgroup.zpowers_le.2 hbC).trans le_sup_right)
  have hyN' : y ∉ A₂ ⊓ N := fun h => hyE (Subgroup.mem_inf.1 h).2
  have hp₂N : p * Nat.card ↥(A₂ ⊓ N) ≤ Nat.card A₂ :=
    p_mul_card_le_of_not_mem hp (inf_le_left : A₂ ⊓ N ≤ A₂) hP₂ hyA₂ hyN'
  have hcardAN : Nat.card A₁ ≤ Nat.card ↥(A₂ ⊓ N) := Subgroup.card_le_of_le hA₁N
  have hAN : A₂ ⊓ N = A₁ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hA₁N ?_
    rw [hcardA₁]
    have : p * Nat.card ↥(A₂ ⊓ N) ≤ p * p := by rw [hA₂card] at hp₂N; nlinarith
    exact Nat.le_of_mul_le_mul_left this hp.pos
  have hz'A₂ : z' ∉ A₂ := by
    intro h
    have h1 : z' ∈ A₂ ⊓ N := Subgroup.mem_inf.2 ⟨h, Subgroup.mem_sup_left hz'E⟩
    rw [hAN] at h1
    have h2 : z' ∈ Subgroup.centralizer (E : Set T) := (Subgroup.zpowers_le.2 hbC) h1
    have h3 : z' ∈ E ⊓ Subgroup.centralizer (E : Set T) := Subgroup.mem_inf.2 ⟨hz'E, h2⟩
    have h4 := hEZ z' h3 hz'p
    rw [h4, orderOf_one] at hz'ord
    exact hp.one_lt.ne hz'ord
  have h23 : p * Nat.card A₂ ≤ Nat.card A₃ := p_mul_card_le_of_not_mem hp hA₂₃ hP₃ hz'A₃ hz'A₂
  have hA₃le : Nat.card A₃ ≤ p ^ 2 :=
    hA A₃ (fun r hr => pow_eq_one_of_mem_closure hcomm₃ hpow₃ r hr)
      (fun r hr s hs => commute_of_mem_closure hcomm₃ r hr s hs)
  rw [hA₂card] at h23
  have : p * p ^ 2 ≤ p ^ 2 := h23.trans hA₃le
  have hp2 : 2 ≤ p := hp.two_le
  nlinarith [pow_pos hp.pos 2]

theorem two_le_localRank_of_not_dvd_card (hp : p.Prime) (hA : PRankLeTwo p T) {b y : T}
    (hb1 : b ≠ 1) (hbp : b ^ p = 1) (hyp : y ^ p = 1) (hby : b * y = y * b) {E : Subgroup T}
    (hbE : ∀ e ∈ E, b * e = e * b) (hyN : y ∈ Subgroup.normalizer (E : Set T))
    (hpE : ¬ p ∣ Nat.card E) (hE2 : 2 ∣ Nat.card E) (hyb : y ∉ Subgroup.zpowers b) :
    2 ≤ localRank p T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_normalized_sylow (r := 2) (p := p) hyp hyN hpE
  set U' : Subgroup T := (U : Subgroup E).map E.subtype with hU'
  have hU2 : IsPGroup 2 U' := U.isPGroup'.map E.subtype
  have hU0 : U' ≠ ⊥ := by
    intro h
    have h1 : (U : Subgroup E) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 h
    have h2 := Sylow.card_eq_multiplicity U
    have hne : Nat.card E ≠ 0 := Nat.card_pos.ne'
    have h3 : 1 ≤ (Nat.card E).factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hne).1 hE2
    rw [h1, Subgroup.card_bot] at h2
    have h4 : 2 ^ 1 ≤ 2 ^ (Nat.card E).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcomm₂ : ∀ a ∈ ({b, y} : Set T), ∀ c ∈ ({b, y} : Set T), a * c = c * a := by
    intro a ha c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
      first | rfl | assumption | exact hby.symm
  have hpow₂ : ∀ a ∈ ({b, y} : Set T), a ^ p = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hbp
    · exact hyp
  set A₁ : Subgroup T := Subgroup.zpowers b with hA₁
  set A₂ : Subgroup T := Subgroup.closure {b, y} with hA₂
  have hA₁₂ : A₁ ≤ A₂ := by
    rw [hA₁, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hyA₂ : y ∈ A₂ := Subgroup.subset_closure (by simp)
  have hP₂ : IsPGroup p A₂ := isPGroup_closure hp hcomm₂ hpow₂
  have hcardA₁ : Nat.card A₁ = p := by rw [hA₁, Nat.card_zpowers, hbord]
  have h12 : p * p ≤ Nat.card A₂ := by
    have := p_mul_card_le_of_not_mem hp hA₁₂ hP₂ hyA₂ hyb
    rwa [hcardA₁] at this
  have hA₂le : Nat.card A₂ ≤ p ^ 2 :=
    hA A₂ (fun r hr => pow_eq_one_of_mem_closure hcomm₂ hpow₂ r hr)
      (fun r hr s hs => commute_of_mem_closure hcomm₂ r hr s hs)
  have hA₂card : Nat.card A₂ = p ^ 2 := by nlinarith
  have hel : IsElementaryAbelian p A₂ :=
    { is_comm := ⟨fun a c => Subtype.ext (commute_of_mem_closure hcomm₂ a.1 a.2 c.1 c.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun g =>
        Subtype.ext (by simpa using pow_eq_one_of_mem_closure hcomm₂ hpow₂ g.1 g.2)) }
  have hbN : b ∈ Subgroup.normalizer (U' : Set T) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact (hbE x x.2).symm
  have hyN' : y ∈ Subgroup.normalizer (U' : Set T) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hU x hx).1
    · intro hh
      obtain ⟨x, hx, hxh⟩ := hh
      have h1 := (hU x hx).2
      have h2 : y⁻¹ * (x : T) * y = h := by
        have : (x : T) = y * h * y⁻¹ := hxh
        rw [this]
        group
      rwa [h2] at h1
  have hA₂N : A₂ ≤ Subgroup.normalizer (U' : Set T) := by
    rw [hA₂, Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hbN
    · exact hyN'
  exact (SourceSixThirteen.le_localRank_iff_exists hp (by norm_num : 1 ≤ 2)).2
    ⟨U', hU2, hU0, A₂, hA₂N, hel, hA₂card⟩

theorem innerCompN_of_sylow [IsSimpleGroup T] (hp : p.Prime)
    (hab : ∀ P : Sylow p T, ∀ x ∈ (P : Subgroup T), ∀ y ∈ (P : Subgroup T), x * y = y * x)
    (hA : PRankLeTwo p T)
    (hB : localRank p T ≤ 1 ∨ ∀ b : T, b ≠ 1 → b ^ p = 1 → ∀ E : Subgroup T,
      IsComponentOf (Subgroup.centralizer ({b} : Set T)) E → p ∣ Nat.card E) :
    InnerCompN p T := by
  classical
  intro _ b y hbp hyp hby E hE hyN
  by_cases hb1 : b = 1
  · subst hb1
    rw [centralizer_one_eq_top] at hE
    have hs : IsSimpleGroup ↥(⊤ : Subgroup T) := Subgroup.topEquiv.isSimpleGroup
    have hEtop : E = ⊤ := @eq_of_isComponentOf_simple T _ ⊤ E hs hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top y)
  have hbE : ∀ e ∈ E, b * e = e * b := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hE.1 he)).symm
  by_cases hpE : p ∣ Nat.card E
  · exact inner_of_dvd_card hp hA hb1 hbp hyp hby hbE hyN hpE
      (no_central_of_isQuasisimple hp hab hE.2.1)
  · by_contra hyE
    have hbC : b ∈ Subgroup.centralizer (E : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (hbE e he).symm
    have hyb : y ∉ Subgroup.zpowers b := fun h =>
      hyE (Subgroup.mem_sup_right ((Subgroup.zpowers_le.2 hbC) h))
    rcases hB with hloc | hall
    · obtain ⟨t, ht⟩ := exists_involution_of_isQuasisimple hE.2.1
      have hE2 : 2 ∣ Nat.card E := ht ▸ orderOf_dvd_natCard t
      have h2 := two_le_localRank_of_not_dvd_card hp hA hb1 hbp hyp hby hbE hyN hpE hE2 hyb
      omega
    · exact hpE (hall b hb1 hbp E hE)

end Inner

end CFSG.RankThree.PartOne.FOC
