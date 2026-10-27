module

public import CFSG.RankThree.OddKernel.HuppertCyclicNormal
public import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension
public import CFSG.RankThree.Coprime.SmallPrimeTorsionQuotient
public import CFSG.RankThree.SubgroupLists.ExtraspecialCore

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open scoped commutatorElement Pointwise

universe u

section Helpers

variable {p : ℕ}

theorem pRank_le_of_card_omega₁_le (hp : p.Prime) {G : Type*} [Group G] [Finite G] {k : ℕ}
    (h : Nat.card (omega₁ G (p := p)) ≤ p ^ k) : pRank p G ≤ k := by
  rw [pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA => ?_
  have hle : A ≤ omega₁ G (p := p) := fun x hx =>
    subset_closure (show x ^ (p ^ 1) = 1 by rw [pow_one]; exact hA.2 x hx)
  exact (card_le_of_le hle).trans h

theorem isElemAbelian_inf_left {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) (K : Subgroup G) :
    CFSG.Open.IsElemAbelian p (A ⊓ K) := by
  have := hA.1
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hA.2 x hx.1⟩
  change (a : G) * b = b * a
  exact congrArg Subtype.val (mul_comm' (⟨a, a.2.1⟩ : A) ⟨b, b.2.1⟩)

theorem card_le_of_isCyclic_quotient (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] [IsCyclic (G ⧸ K)] {r : ℕ}
    (hK : ∀ B : Subgroup G, B ≤ K → CFSG.Open.IsElemAbelian p B → Nat.card B ≤ p ^ r)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) : Nat.card A ≤ p ^ (r + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker
    (QuotientGroup.mk' K) A
  rw [QuotientGroup.ker_mk'] at hcard
  have h1 : Nat.card (A.map (QuotientGroup.mk' K)) ≤ p := by
    refine CFSG.RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic fun c => ?_
    obtain ⟨a, ha, hac⟩ := mem_map.1 c.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hac, ← map_pow, hA.2 a ha, map_one]
    rfl
  have h2 : Nat.card (A ⊓ K : Subgroup G) ≤ p ^ r :=
    hK _ inf_le_right (isElemAbelian_inf_left hA K)
  rw [hcard, pow_succ, mul_comm]
  exact Nat.mul_le_mul h2 h1

theorem card_le_of_le_map_of_nonabelian (hp : p.Prime) {P G : Type*} [Group P] [Group G]
    [Finite P] [Finite G] {E : Subgroup P} (hE : Nat.card E = p ^ 3)
    (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (π : P →* G) {B : Subgroup G}
    (hB : B ≤ E.map π) (hBc : IsMulCommutative B) : Nat.card B ≤ p ^ 2 := by
  have hmapdvd : Nat.card (E.map π) ∣ p ^ 3 := hE ▸ card_map_dvd E π
  have hdvd : Nat.card B ∣ p ^ 3 := (card_dvd_of_le hB).trans hmapdvd
  obtain ⟨j, hj, hBj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases (show j ≤ 2 ∨ j = 3 by omega) with h | rfl
  · rw [hBj]
    exact Nat.pow_le_pow_right hp.pos h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hmap_le : Nat.card (E.map π) ≤ p ^ 3 := Nat.le_of_dvd (pow_pos hp.pos 3) hmapdvd
    have hBeq : B = E.map π := eq_of_le_of_card_ge hB (by rw [hBj]; exact hmap_le)
    have hcard := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker π E
    have hmapcard : Nat.card (E.map π) = p ^ 3 := by rw [← hBeq, hBj]
    rw [hE, hmapcard] at hcard
    have h1 : Nat.card (E ⊓ π.ker : Subgroup P) = 1 := by
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 3) (hcard.symm.trans (mul_one _).symm)
    have hbot : E ⊓ π.ker = ⊥ := card_eq_one.1 h1
    apply hxy
    have hxB : π x ∈ B := hBeq ▸ mem_map_of_mem π hx
    have hyB : π y ∈ B := hBeq ▸ mem_map_of_mem π hy
    have hc : π x * π y = π y * π x :=
      congrArg Subtype.val (mul_comm' (⟨π x, hxB⟩ : B) ⟨π y, hyB⟩)
    have hker : ⁅x, y⁆ ∈ E ⊓ π.ker := by
      refine mem_inf.2 ⟨?_, MonoidHom.mem_ker.2 ?_⟩
      · rw [commutatorElement_def]
        exact E.mul_mem (E.mul_mem (E.mul_mem hx hy) (E.inv_mem hx)) (E.inv_mem hy)
      · rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [hbot, mem_bot] at hker
    exact commutatorElement_eq_one_iff_mul_comm.1 hker

theorem mem_map_center_iff {P : Type*} [Group P] (E : Subgroup P) (z : P) :
    z ∈ (center E).map E.subtype ↔ z ∈ E ∧ ∀ e ∈ E, e * z = z * e := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun e he => congrArg Subtype.val (mem_center_iff.1 hw ⟨e, he⟩)⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

theorem map_center_normal {P : Type*} [Group P] (E : Subgroup P) [hE : E.Normal] :
    ((center E).map E.subtype).Normal := by
  refine ⟨fun z hz g => ?_⟩
  rw [mem_map_center_iff] at hz ⊢
  refine ⟨hE.conj_mem z hz.1 g, fun e he => ?_⟩
  have h := hz.2 (g⁻¹ * e * g) (by simpa using hE.conj_mem e he g⁻¹)
  calc e * (g * z * g⁻¹) = g * ((g⁻¹ * e * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * e * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * e := by group

theorem map_center_le_center_of_card_eq (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (E : Subgroup P) [E.Normal] (hZ : Nat.card (center E) = p) :
    (center E).map E.subtype ≤ center P := by
  have : Fact p.Prime := ⟨hp⟩
  have := hP.isNilpotent
  have := map_center_normal E
  set Z := (center E).map E.subtype with hZdef
  have hZcard : Nat.card Z = p := by
    rw [hZdef, card_map_of_injective E.subtype_injective, hZ]
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hZcard
    exact hp.one_lt.ne hZcard
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hZne
  have hdvd : Nat.card (Z ⊓ center P : Subgroup P) ∣ p := hZcard ▸ card_dvd_of_le inf_le_left
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpc
  · exact absurd (card_eq_one.1 h1) hne
  · have heq : Z ⊓ center P = Z := eq_of_le_of_card_ge inf_le_left (by rw [hZcard, hpc])
    exact inf_eq_left.1 heq

end Helpers

section Cube

variable {p : ℕ}

theorem exists_cyclic_supplement (hp : p.Prime) (hp2 : p ≠ 2) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hScard : Nat.card (omega₁ P (p := p)) = p ^ 3)
    (hSexp : ∀ x ∈ omega₁ P (p := p), x ^ p = 1)
    (hSnc : ∃ x ∈ omega₁ P (p := p), ∃ y ∈ omega₁ P (p := p), x * y ≠ y * x) :
    IsCyclic (centralizer (omega₁ P (p := p) : Set P)) ∧
      ∃ X : Subgroup P, IsCyclic X ∧ (omega₁ P (p := p) : Set P) * (X : Set P) = Set.univ ∧
        ⁅⁅omega₁ P (p := p), (⊤ : Subgroup P)⁆, X⁆ = ⊥ := by
  let : MulDistribMulAction Unit P := MulDistribMulAction.compHom P (1 : Unit →* MulAut P)
  have hA : Nat.Coprime (Nat.card Unit) p := by simp
  have h := CFSG.RankThree.Coprime.prime_cube_torsion_cyclic_extension_alternative hp hp2 hP
    (A := Unit) hA hScard hSexp hSnc
  obtain ⟨⟨hCc, -⟩, halt⟩ := h
  refine ⟨hCc, ?_⟩
  rcases halt with hSC | ⟨X, -, hXc, -, -, -, -, -, -, hSX, hTX, -⟩
  · refine ⟨centralizer (omega₁ P (p := p) : Set P), hCc, hSC, ?_⟩
    have := omega₁_characteristic P (p := p)
    refine le_bot_iff.1 ((commutator_mono (commutator_le_left _ _) le_rfl).trans ?_)
    rw [commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.2 le_rfl).le
  · exact ⟨X, hXc, hSX, hTX⟩

theorem commutator_le_and_lowerCentralSeries_three {P : Type*} [Group P] (E X Z : Subgroup P)
    [E.Normal] (hZ : Z ≤ center P) (hEE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Z)
    (hEX : (E : Set P) * (X : Set P) = Set.univ) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hTX : ⁅⁅E, (⊤ : Subgroup P)⁆, X⁆ = ⊥) :
    commutator P ≤ ⁅E, (⊤ : Subgroup P)⁆ ∧ (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ := by
  have hdec : ∀ g : P, ∃ e ∈ E, ∃ x ∈ X, e * x = g := fun g => by
    have hg : g ∈ (E : Set P) * (X : Set P) := hEX ▸ Set.mem_univ g
    obtain ⟨e, he, x, hx, hex⟩ := Set.mem_mul.1 hg
    exact ⟨e, he, x, hx, hex⟩
  have hcomm : commutator P ≤ ⁅E, (⊤ : Subgroup P)⁆ := by
    have := commutator_normal E ⊤
    rw [_root_.commutator_def, commutator_le]
    intro g _ h _
    obtain ⟨e₁, he₁, x₁, hx₁, rfl⟩ := hdec g
    obtain ⟨e₂, he₂, x₂, hx₂, rfl⟩ := hdec h
    let π := QuotientGroup.mk' ⁅E, (⊤ : Subgroup P)⁆
    have hcE : ∀ e ∈ E, ∀ k : P, Commute (π e) (π k) := fun e he k => by
      have hk : ⁅e, k⁆ ∈ ⁅E, (⊤ : Subgroup P)⁆ := commutator_mem_commutator he (mem_top k)
      have : π ⁅e, k⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hk
      rw [map_commutatorElement] at this
      exact commutatorElement_eq_one_iff_commute.1 this
    have hcX : Commute (π x₁) (π x₂) := by
      change π x₁ * π x₂ = π x₂ * π x₁
      rw [← map_mul, ← map_mul, hX x₁ hx₁ x₂ hx₂]
    have hc : Commute (π (e₁ * x₁)) (π (e₂ * x₂)) := by
      rw [map_mul, map_mul]
      exact (((hcE e₁ he₁ e₂).mul_right (hcE e₁ he₁ x₂)).mul_left
        (((hcE e₂ he₂ x₁).symm).mul_right hcX))
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hc
  refine ⟨hcomm, ?_⟩
  have hT : ⁅⁅E, (⊤ : Subgroup P)⁆, (⊤ : Subgroup P)⁆ ≤ Z := by
    rw [commutator_le]
    intro t ht g _
    obtain ⟨e, he, x, hx, rfl⟩ := hdec g
    have htE : t ∈ E := commutator_le_left E ⊤ ht
    have h1 : ⁅t, x⁆ = 1 := by
      have : ⁅t, x⁆ ∈ ⁅⁅E, (⊤ : Subgroup P)⁆, X⁆ := commutator_mem_commutator ht hx
      rwa [hTX, mem_bot] at this
    have h2 : x * t⁻¹ * x⁻¹ = t⁻¹ := by
      calc x * t⁻¹ * x⁻¹ = t⁻¹ * ⁅t, x⁆ := by rw [commutatorElement_def]; group
        _ = t⁻¹ := by rw [h1, mul_one]
    have h3 : ⁅t, e * x⁆ = ⁅t, e⁆ := by
      calc ⁅t, e * x⁆ = t * e * (x * t⁻¹ * x⁻¹) * e⁻¹ := by
            rw [commutatorElement_def]; group
        _ = ⁅t, e⁆ := by rw [h2, commutatorElement_def]
    rw [h3]
    exact hEE t htE e he
  have hZ' : ⁅Z, (⊤ : Subgroup P)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 (hZ.trans (center_le_centralizer _))
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  refine le_bot_iff.1 ?_
  rw [← hZ']
  exact commutator_mono (commutator_mono hcomm le_rfl |>.trans hT) le_rfl

theorem powHom_range_isCyclic_le_center {P : Type*} [Group P] (θ : P →* P)
    (hθ : ⇑θ = fun x => x ^ p) (E X : Subgroup P) (hE : ∀ e ∈ E, e ^ p = 1)
    (hEX : (E : Set P) * (X : Set P) = Set.univ) [IsCyclic X] :
    IsCyclic θ.range ∧ θ.range ≤ center P := by
  have h : ∀ a : P, θ a = a ^ p := fun a => congrFun hθ a
  have hθE : ∀ e ∈ E, θ e = 1 := fun e he => by rw [h]; exact hE e he
  have hdec : ∀ g : P, ∃ e ∈ E, ∃ x ∈ X, e * x = g := fun g => by
    have hg : g ∈ (E : Set P) * (X : Set P) := hEX ▸ Set.mem_univ g
    obtain ⟨e, he, x, hx, hex⟩ := Set.mem_mul.1 hg
    exact ⟨e, he, x, hx, hex⟩
  have hrange : ∀ g : P, ∃ x ∈ X, θ g = θ x := fun g => by
    obtain ⟨e, he, x, hx, rfl⟩ := hdec g
    exact ⟨x, hx, by rw [map_mul, hθE e he, one_mul]⟩
  have hle : θ.range ≤ X.map θ := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨x, hx, hgx⟩ := hrange g
    exact ⟨x, hx, hgx.symm⟩
  have hXc : IsCyclic (X.map θ) :=
    isCyclic_of_surjective (θ.subgroupMap X) (θ.subgroupMap_surjective X)
  refine ⟨Subgroup.isCyclic_of_le hle, ?_⟩
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    let _ := IsCyclic.commGroup (α := X)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X) ⟨b, hb⟩)
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx, hgx⟩ := hrange g
  rw [hgx, mem_center_iff]
  intro k
  obtain ⟨e, he, y, hy, rfl⟩ := hdec k
  have hxX : θ x ∈ X := by rw [h]; exact X.pow_mem hx p
  have hcy : y * θ x = θ x * y := hXcomm y hy _ hxX
  have hce : e * θ x = θ x * e := by
    have h1 : θ (e * x * e⁻¹) = θ x := by
      rw [map_mul, map_mul, map_inv, hθE e he, inv_one, one_mul, mul_one]
    have h2 : θ (e * x * e⁻¹) = e * θ x * e⁻¹ := by rw [h, h]; exact conj_pow
    calc e * θ x = (e * θ x * e⁻¹) * e := by group
      _ = θ x * e := by rw [← h2, h1]
  calc e * y * θ x = e * (y * θ x) := mul_assoc _ _ _
    _ = e * (θ x * y) := by rw [hcy]
    _ = e * θ x * y := (mul_assoc _ _ _).symm
    _ = θ x * e * y := by rw [hce]
    _ = θ x * (e * y) := mul_assoc _ _ _

theorem exists_pow_prime_pow_hom {P : Type*} [Group P] (θ : P →* P)
    (hθ : ⇑θ = fun x => x ^ p) (n : ℕ) : ∃ lam : P →* P, ⇑lam = fun x => x ^ p ^ n := by
  have h : ∀ a : P, θ a = a ^ p := fun a => congrFun hθ a
  have hmul : ∀ n : ℕ, ∀ x y : P, (x * y) ^ p ^ n = x ^ p ^ n * y ^ p ^ n := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      calc (x * y) ^ p ^ (n + 1) = θ ((x * y) ^ p ^ n) := by rw [h, pow_succ, pow_mul]
        _ = θ (x ^ p ^ n) * θ (y ^ p ^ n) := by rw [ih, map_mul]
        _ = x ^ p ^ (n + 1) * y ^ p ^ (n + 1) := by rw [h, h, pow_succ, pow_mul, pow_mul]
  exact ⟨MonoidHom.mk' (fun x => x ^ p ^ n) (hmul n), rfl⟩

theorem rank_two_large_prime_cube_torsion_structure {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P) (hrank : pRank p P ≤ 2)
    (hE : Nat.card (omega₁ P (p := p)) = p ^ 3) :
    let E := omega₁ P (p := p)
    (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
      IsCyclic (centralizer (E : Set P)) ∧ IsCyclic (center P) ∧
      (∃ X : Subgroup P, IsCyclic X ∧ (E : Set P) * (X : Set P) = Set.univ) ∧
      commutator P ≤ E ∧ (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧
      (∃ θ : P →* P, (⇑θ = fun x => x ^ p) ∧ IsCyclic θ.range ∧ θ.range ≤ center P) ∧
      (∃ k : ℕ, Monoid.exponent P = p ^ k) ∧
      ∀ k : ℕ, Monoid.exponent P = p ^ k → 1 ≤ k ∧
        (2 ≤ k → (∃ lam : P →* P, (⇑lam = fun x => x ^ p ^ (k - 1)) ∧
            lam.range = (center E).map E.subtype) ∧ Nat.card (center E) = p) ∧
        (k = 1 → E = ⊤) := by
  intro E
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hEchar : E.Characteristic := omega₁_characteristic P (p := p)
  have hEn : E.Normal := normal_of_characteristic E
  have htors := CFSG.RankThree.PGroups.rank_two_large_prime_torsion_exponent hp hp3 hP hrank
  have hexp : ∀ x ∈ E, x ^ p = 1 := htors.2.1
  have hmemE : ∀ x : P, x ^ p = 1 → x ∈ E := fun x hx =>
    subset_closure (show x ^ (p ^ 1) = 1 by rw [pow_one]; exact hx)
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩
    have h3 : 3 ≤ pRank p P := by
      rw [pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.le_pRank hp.one_lt le_top ⟨hcomm, hexp⟩ hE
    omega
  have hsupp := exists_cyclic_supplement hp hp2 hP hE hexp hnc
  obtain ⟨hCc, X, hXc, hEX, hTX⟩ := hsupp
  have hnc' : ∃ a b : E, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hcube := CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (S := E) hE hnc'
  have hcommE : commutator E = center E := hcube.1
  have hZcard : Nat.card (center E) = p := hcube.2.1
  have hZ : (center E).map E.subtype ≤ center P := map_center_le_center_of_card_eq hp hP E hZcard
  have hEE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ (center E).map E.subtype := fun x hx y hy => by
    have hc : ⁅(⟨x, hx⟩ : E), ⟨y, hy⟩⁆ ∈ center E :=
      hcommE ▸ commutator_mem_commutator (mem_top _) (mem_top _)
    exact ⟨_, hc, map_commutatorElement E.subtype _ _⟩
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    let _ := IsCyclic.commGroup (α := X)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X) ⟨b, hb⟩)
  have hcls := commutator_le_and_lowerCentralSeries_three E X _ hZ hEE hEX hXcomm hTX
  have hcommP : commutator P ≤ E := hcls.1.trans (commutator_le_left E ⊤)
  have hγ : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ := hcls.2
  have hθex := (CFSG.RankThree.omega_one_eq_torsion_and_powHom_of_class_three hp hp3 hP hγ).2.2
    hcommP
  obtain ⟨θ, hθ⟩ := hθex
  have hθr := powHom_range_isCyclic_le_center θ hθ E X hexp hEX
  have hZPc : IsCyclic (center P) := Subgroup.isCyclic_of_le (center_le_centralizer (E : Set P))
  refine ⟨hnc, hCc, hZPc, ⟨X, hXc, hEX⟩, hcommP, hγ, ⟨θ, hθ, hθr⟩, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hdvd : Monoid.exponent P ∣ p ^ n := hn ▸ Group.exponent_dvd_nat_card
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨k, hk⟩
  intro k hk
  have hpowk : ∀ x : P, x ^ p ^ k = 1 := fun x => hk ▸ Monoid.pow_exponent_eq_one x
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have hsub : Subsingleton P := Monoid.exp_eq_one_iff.1 (by rw [hk, hk0', pow_zero])
    have hle : Nat.card E ≤ 1 :=
      (card_le_card_group E).trans (Finite.card_le_one_iff_subsingleton.2 hsub)
    rw [hE] at hle
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  refine ⟨hk1, fun hk2 => ⟨?_, hZcard⟩, fun hk1' => ?_⟩
  · obtain ⟨lam, hlam⟩ := exists_pow_prime_pow_hom θ hθ (k - 1)
    have hlamx : ∀ x : P, lam x = x ^ p ^ (k - 1) := fun x => congrFun hlam x
    refine ⟨lam, hlam, ?_⟩
    have hle : lam.range ≤ (center E).map E.subtype := by
      rintro _ ⟨x, rfl⟩
      rw [mem_map_center_iff]
      have hcen : lam x ∈ center P := by
        have hθx : θ (x ^ p ^ (k - 2)) = lam x := by
          rw [hlamx, congrFun hθ, ← pow_mul, ← pow_succ]
          congr 2
          omega
        exact hθr.2 ⟨_, hθx⟩
      refine ⟨hmemE _ ?_, fun e _ => mem_center_iff.1 hcen e⟩
      rw [hlamx, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hk1]
      exact hpowk x
    have hne : lam.range ≠ ⊥ := by
      intro hbot
      have hall : ∀ x : P, x ^ p ^ (k - 1) = 1 := fun x => by
        rw [← hlamx]
        exact (MonoidHom.range_eq_bot_iff.1 hbot) ▸ rfl
      have hdvd : p ^ k ∣ p ^ (k - 1) := hk ▸ Monoid.exponent_dvd_of_forall_pow_eq_one hall
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
      omega
    have hZc : Nat.card ((center E).map E.subtype) = p := by
      rw [card_map_of_injective E.subtype_injective, hZcard]
    have hdvd : Nat.card lam.range ∣ p := hZc ▸ card_dvd_of_le hle
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpc
    · exact absurd (card_eq_one.1 h1) hne
    · exact eq_of_le_of_card_ge hle (by rw [hZc, hpc])
  · refine eq_top_iff.2 fun x _ => hmemE x ?_
    have := hpowk x
    rwa [hk1', pow_one] at this

end Cube

section Main

theorem rank_two_large_prime_small_torsion_structure {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P)
    (hE : Nat.card (omega₁ P (p := p)) ≤ p ^ 2) :
    IsCyclic (commutator P) ∧ ∀ (N : Subgroup P) [N.Normal], pRank p (P ⧸ N) ≤ 2 :=
  ⟨(huppert_small_prime_torsion_cyclic_normal_structure hp hp3 hP hE).2, fun N _ =>
    pRank_le_of_card_omega₁_le hp
      (CFSG.RankThree.Coprime.small_prime_torsion_quotient_bound hp hp3 hP hE N)⟩

theorem rank_two_large_prime_quotient_pRank_le_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P) (hrank : pRank p P ≤ 2)
    (N : Subgroup P) [N.Normal] : pRank p (P ⧸ N) ≤ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have htors := CFSG.RankThree.PGroups.rank_two_large_prime_torsion_exponent hp hp3 hP hrank
  obtain ⟨j, hj⟩ := (hP.to_subgroup (omega₁ P (p := p))).exists_card_eq
  have hj3 : j ≤ 3 := by
    have h := htors.2.2
    rw [hj] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  rcases (show j ≤ 2 ∨ j = 3 by omega) with hj2 | rfl
  · have hE2 : Nat.card (omega₁ P (p := p)) ≤ p ^ 2 := hj ▸ Nat.pow_le_pow_right hp.pos hj2
    exact ((rank_two_large_prime_small_torsion_structure hp hp3 hP hE2).2 N).trans
      (by norm_num)
  have hcube := rank_two_large_prime_cube_torsion_structure hp hp3 hP hrank hj
  obtain ⟨hnc, -, -, ⟨X, hXc, hEX⟩, -⟩ := hcube
  have hEn : (omega₁ P (p := p)).Normal :=
    @normal_of_characteristic _ _ _ (omega₁_characteristic P (p := p))
  have hKn : ((omega₁ P (p := p)).map (QuotientGroup.mk' N)).Normal :=
    hEn.map _ (QuotientGroup.mk'_surjective N)
  have hKc : IsCyclic ((P ⧸ N) ⧸ (omega₁ P (p := p)).map (QuotientGroup.mk' N)) := by
    let ρ : P →* (P ⧸ N) ⧸ (omega₁ P (p := p)).map (QuotientGroup.mk' N) :=
      (QuotientGroup.mk' _).comp (QuotientGroup.mk' N)
    have hρ : Function.Surjective ρ :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective N)
    refine isCyclic_of_surjective (ρ.comp X.subtype) fun q => ?_
    obtain ⟨g, rfl⟩ := hρ q
    have hg : g ∈ ((omega₁ P (p := p) : Set P) * (X : Set P)) := hEX ▸ Set.mem_univ g
    obtain ⟨e, he, x, hx, rfl⟩ := Set.mem_mul.1 hg
    refine ⟨⟨x, hx⟩, ?_⟩
    have hρe : ρ e = 1 := (QuotientGroup.eq_one_iff _).2 (mem_map_of_mem _ he)
    change ρ x = ρ (e * x)
    rw [map_mul, hρe, one_mul]
  rw [pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA => ?_
  exact card_le_of_isCyclic_quotient hp ((omega₁ P (p := p)).map (QuotientGroup.mk' N)) (r := 2)
    (fun B hB hBe => card_le_of_le_map_of_nonabelian hp hj hnc _ hB hBe.1) hA

theorem rank_two_large_prime_section_pRank_le_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P) (hrank : pRank p P ≤ 2)
    (U : Subgroup P) (V : Subgroup U) [V.Normal] : pRank p (U ⧸ V) ≤ 3 := by
  have hU : pRank p U ≤ pRank p P := by
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt U.subtype U.subtype_injective
  exact rank_two_large_prime_quotient_pRank_le_three hp hp3 (hP.to_subgroup U) (hU.trans hrank) V

theorem rank_two_large_prime_power_structure_and_section_bound {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P)
    (hrank : pRank p P ≤ 2) :
    let E := omega₁ P (p := p)
    ((∀ x ∈ E, x ^ p = 1) ∧ Nat.card E ≤ p ^ 3) ∧
    (Nat.card E ≤ p ^ 2 →
      IsCyclic (commutator P) ∧ ∀ (N : Subgroup P) [N.Normal], pRank p (P ⧸ N) ≤ 2) ∧
    (Nat.card E = p ^ 3 →
      (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
      IsCyclic (centralizer (E : Set P)) ∧ IsCyclic (center P) ∧
      (∃ X : Subgroup P, IsCyclic X ∧ (E : Set P) * (X : Set P) = Set.univ) ∧
      commutator P ≤ E ∧ (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧
      (∃ θ : P →* P, (⇑θ = fun x => x ^ p) ∧ IsCyclic θ.range ∧ θ.range ≤ center P) ∧
      (∃ k : ℕ, Monoid.exponent P = p ^ k) ∧
      ∀ k : ℕ, Monoid.exponent P = p ^ k → 1 ≤ k ∧
        (2 ≤ k → (∃ lam : P →* P, (⇑lam = fun x => x ^ p ^ (k - 1)) ∧
            lam.range = (center E).map E.subtype) ∧ Nat.card (center E) = p) ∧
        (k = 1 → E = ⊤)) ∧
    (∀ (N : Subgroup P) [N.Normal], pRank p (P ⧸ N) ≤ 3) ∧
    ∀ (U : Subgroup P) (V : Subgroup U) [V.Normal], pRank p (U ⧸ V) ≤ 3 := by
  intro E
  have htors := CFSG.RankThree.PGroups.rank_two_large_prime_torsion_exponent hp hp3 hP hrank
  exact ⟨⟨htors.2.1, htors.2.2⟩, rank_two_large_prime_small_torsion_structure hp hp3 hP,
    rank_two_large_prime_cube_torsion_structure hp hp3 hP hrank,
    fun N _ => rank_two_large_prime_quotient_pRank_le_three hp hp3 hP hrank N,
    fun U V _ => rank_two_large_prime_section_pRank_le_three hp hp3 hP hrank U V⟩

end Main

end CFSG.RankThree.OddKernel
