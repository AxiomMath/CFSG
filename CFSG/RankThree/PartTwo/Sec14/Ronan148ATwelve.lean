module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveQuot
import CFSG.RankThree.PartTwo.Sec14.Ronan148AConjComp
import CFSG.RankThree.PartTwo.Sec14.Ronan148HInc
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] def IsTwelveType (F : Type*) [Group F] : Prop :=
  IsQuasisimple F ∧ IsPGroup 3 (Subgroup.center F) ∧
    (∃ x : F, x ^ 3 = 1 ∧ x ∉ Subgroup.center F) ∧ 5 ∣ Nat.card (F ⧸ Subgroup.center F)

section Frame

variable {Q : Type} [Group Q] [Finite Q]

theorem isElemAbelian_zpowers_of_pow_three {u : Q} (hu3 : u ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers u) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change (a : Q) * b = b * a
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]

theorem inf_centralizer_eq_map_center (K : Subgroup Q) :
    K ⊓ Subgroup.centralizer (K : Set Q) = (Subgroup.center ↥K).map K.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)


theorem mem_of_pow_three_of_mem_centralizer_ON (hQ : NoE81TwoLocal Q) {K : Subgroup Q}
    (hK : IsComponent K) (hKON : Sec4.IsTripleCover ↥K CFSG.Blueprint.NativeSporadic.ON)
    {u : Q} (hu3 : u ^ 3 = 1) (huC : u ∈ Subgroup.centralizer (K : Set Q)) : u ∈ K := by
  by_contra hu
  obtain ⟨T, E, hT, hT2, hE, hEc, hET⟩ :=
    exists_twoLocal_rank_three_of_tripleCover_ON hKON hK.1.1
  have hinj : Function.Injective K.subtype := K.subtype_injective
  have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ K.one_mem)
  have hUc : Nat.card (Subgroup.zpowers u) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
  have hEK : E.map K.subtype ≤ K := Subgroup.map_subtype_le E
  have hint : E.map K.subtype ⊓ Subgroup.zpowers u = ⊥ := by
    have hdvd : Nat.card ↥(E.map K.subtype ⊓ Subgroup.zpowers u) ∣ 3 :=
      hUc ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
        E.map K.subtype ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers u) (by rw [hUc, h1])
      have hmem : u ∈ E.map K.subtype ⊓ Subgroup.zpowers u := by
        rw [heq]
        exact Subgroup.mem_zpowers u
      exact hu (hEK hmem.1)
  exact false_of_commuting_twoLocal_quot hQ (J := K)
    ((Subgroup.map_eq_bot_iff_of_injective T hinj).not.mpr hT) (hT2.map _)
    (Subgroup.map_subtype_le T) hEK ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
    (CFSG.SectionRank.isElemAbelian_map hE _) (Subgroup.zpowers_le.mpr huC)
    (isElemAbelian_zpowers_of_pow_three hu3) hint
    (by rw [Subgroup.card_map_of_injective hinj, hEc, hUc])

theorem pow_not_mem_center_of_coprime {F : Type*} [Group F] {f : F} (hf3 : f ^ 3 = 1)
    (hfZ : f ∉ Subgroup.center F) {r : ℕ} (hr : ¬ 3 ∣ r) : f ^ r ∉ Subgroup.center F := by
  have hfr : f ^ r = f ^ (r % 3) := by
    conv_lhs => rw [← Nat.div_add_mod r 3, pow_add, pow_mul, hf3, one_pow, one_mul]
  have hr3 : r % 3 = 1 ∨ r % 3 = 2 := by omega
  rw [hfr]
  rcases hr3 with h | h
  · rw [h, pow_one]
    exact hfZ
  · rw [h]
    intro hc
    apply hfZ
    have : (f ^ 2) ^ 2 = f := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hf3, one_mul, pow_one]
    rw [← this]
    exact Subgroup.pow_mem _ hc 2

theorem map_mem_center_of_mem_centralizer_ON (hQ : NoE81TwoLocal Q) {K : Subgroup Q}
    (hK : IsComponent K) (hKON : Sec4.IsTripleCover ↥K CFSG.Blueprint.NativeSporadic.ON)
    [hKn : K.Normal] {P F : Type} [Group P] [Finite P] [Group F] [Finite F] (ι : P →* Q)
    (hι3 : ¬ 3 ∣ Nat.card ι.ker) (φ : P →* F) (hφ : Function.Surjective φ)
    (hφ3 : ¬ 3 ∣ Nat.card φ.ker) (hF : IsTwelveType F) {p : P}
    (hp : ι p ∈ Subgroup.centralizer (K : Set Q)) : φ p ∈ Subgroup.center F := by
  obtain ⟨hFq, hFZ3, ⟨f, hf3, hfZ⟩, -⟩ := hF
  set M := (Subgroup.centralizer (K : Set Q)).comap ι with hM
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance ι
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq (hMn.map φ hφ) with htop | hcen
  swap
  · exact hcen ⟨p, hp, rfl⟩
  exfalso
  obtain ⟨m, hmM, hmf⟩ : f ∈ M.map φ := htop ▸ Subgroup.mem_top f
  have hm3 : m ^ 3 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hmf, hf3]
  set r := orderOf (m ^ 3) with hr
  have hrdvd : r ∣ Nat.card φ.ker := by
    rw [hr, ← Subgroup.orderOf_mk (m ^ 3) hm3]
    exact orderOf_dvd_natCard _
  have hr3 : ¬ 3 ∣ r := fun h => hφ3 (h.trans hrdvd)
  set x := m ^ r with hx
  have hxM : x ∈ M := M.pow_mem hmM r
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, hr, pow_orderOf_eq_one]
  have hφx : φ x ∉ Subgroup.center F := by
    rw [hx, map_pow, hmf]
    exact pow_not_mem_center_of_coprime hf3 hfZ hr3
  have hx1 : x ≠ 1 := fun h1 => hφx (by rw [h1, map_one]; exact Subgroup.one_mem _)
  have hιx3 : ι x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hιxK : ι x ∈ K := mem_of_pow_three_of_mem_centralizer_ON hQ hK hKON hιx3 hxM
  have hιx1 : ι x ≠ 1 := by
    intro h1
    have hxk : x ∈ ι.ker := h1
    have hord : orderOf (⟨x, hxk⟩ : ι.ker) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hx3 hx1
    exact hι3 (hord ▸ orderOf_dvd_natCard _)
  set Z := K ⊓ Subgroup.centralizer (K : Set Q) with hZ
  have hZc : Nat.card Z = 3 := by
    rw [hZ, inf_centralizer_eq_map_center, Subgroup.card_map_of_injective K.subtype_injective]
    exact hKON.1
  have hZu : Z = Subgroup.zpowers (ι x) := by
    refine (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hιxK, hxM⟩)) ?_).symm
    rw [hZc, Nat.card_zpowers, orderOf_eq_prime hιx3 hιx1]
  have hker : ∀ y ∈ ι.ker, φ y = 1 := by
    have hkn : ι.ker.Normal := MonoidHom.normal_ker ι
    have hcop : Nat.Coprime 3 (Nat.card ι.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hι3
    have hdk : ∀ y ∈ ι.ker, orderOf (φ y) ∣ Nat.card ι.ker := fun y hy =>
      (orderOf_map_dvd φ y).trans (by
        rw [← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq (hkn.map φ hφ) with htop' | hcen'
    · exfalso
      obtain ⟨k, hk, hkf⟩ : f ∈ ι.ker.map φ := htop' ▸ Subgroup.mem_top f
      have hf1 : f ≠ 1 := fun h1 => hfZ (h1 ▸ Subgroup.one_mem _)
      have hof : orderOf f = 3 := orderOf_eq_prime hf3 hf1
      have hdvd := hdk k hk
      rw [hkf, hof] at hdvd
      exact hι3 hdvd
    · intro y hy
      obtain ⟨n, hn⟩ := hFZ3 ⟨φ y, hcen' ⟨y, hy, rfl⟩⟩
      have h1 : (φ y) ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have hd1 : orderOf (φ y) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
      have hc : Nat.Coprime (orderOf (φ y)) (Nat.card ι.ker) :=
        Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left n hcop)
      exact orderOf_eq_one_iff.mp (hc.eq_one_of_dvd (hdk y hy))
  have hconj : ∀ p' : P, ∃ j : ℤ, φ p' * φ x * (φ p')⁻¹ = φ x ^ j := by
    intro p'
    have hmem : ι p' * ι x * (ι p')⁻¹ ∈ Z :=
      Subgroup.mem_inf.mpr ⟨hKn.conj_mem _ hιxK _,
        (Subgroup.normal_centralizer (H := K)).conj_mem _ hxM _⟩
    rw [hZu] at hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨j, ?_⟩
    have hk : p' * x * p'⁻¹ * (x ^ j)⁻¹ ∈ ι.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_zpow]
      rw [← hj]
      group
    have := hker _ hk
    simp only [map_mul, map_inv, map_zpow] at this
    calc φ p' * φ x * (φ p')⁻¹ = φ p' * φ x * (φ p')⁻¹ * (φ x ^ j)⁻¹ * φ x ^ j := by group
      _ = φ x ^ j := by rw [this, one_mul]
  have hnorm : (Subgroup.zpowers (φ x)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    obtain ⟨p', rfl⟩ := hφ g
    obtain ⟨j, hj⟩ := hconj p'
    rw [← conj_zpow, hj, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq hnorm with htop'' | hcen''
  · apply hφx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop'' ▸ Subgroup.mem_top g)
    rw [← hk]
    exact (Commute.zpow_left (Commute.refl (φ x)) k).eq
  · exact hφx (hcen'' (Subgroup.mem_zpowers _))


theorem false_of_commuting_ON_quot (hQ : NoE81TwoLocal Q) {K : Subgroup Q} (hK : IsComponent K)
    (hKON : Sec4.IsTripleCover ↥K CFSG.Blueprint.NativeSporadic.ON)
    {P₁ P₂ F₁ F₂ : Type} [Group P₁] [Finite P₁] [Group P₂] [Finite P₂] [Group F₁] [Finite F₁]
    [Group F₂] [Finite F₂] (ι₁ : P₁ →* Q) (ι₂ : P₂ →* Q) (hι₁ : ¬ 3 ∣ Nat.card ι₁.ker)
    (hι₂ : ¬ 3 ∣ Nat.card ι₂.ker) (φ₁ : P₁ →* F₁) (φ₂ : P₂ →* F₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hφ₁3 : ¬ 3 ∣ Nat.card φ₁.ker) (hφ₂3 : ¬ 3 ∣ Nat.card φ₂.ker)
    (hF₁ : IsTwelveType F₁) (hF₂ : IsTwelveType F₂) {W : Subgroup Q} (hW3 : ¬ 3 ∣ Nat.card W)
    (hW₁ : ι₁.range ≤ Subgroup.normalizer (W : Set Q))
    (hW₂ : ι₂.range ≤ Subgroup.normalizer (W : Set Q))
    (hW : ∀ p q, ι₁ p * ι₂ q * (ι₁ p)⁻¹ * (ι₂ q)⁻¹ ∈ W) : False := by
  haveI hKn : K.Normal :=
    normal_of_forall_map_conj_eq (map_conj_eq_of_tripleCover_ON_quot hQ hK hKON)
  set ρ : Q →* MulAut ↥K := MulAut.conjNormal with hρ
  have hρ1 : ∀ q : Q, ρ q = 1 → q ∈ Subgroup.centralizer (K : Set Q) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : Q)) hq
    simp only [hρ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * q = q * k * q⁻¹ * q := by rw [this]
      _ = q * k := by group
  have hSdata : ∀ {F : Type} [Group F] [Finite F], IsTwelveType F →
      IsSimpleGroup (F ⧸ Subgroup.center F) ∧ 3 ∣ Nat.card (F ⧸ Subgroup.center F) ∧
        5 ∣ Nat.card (F ⧸ Subgroup.center F) ∧
        ∃ a b : F ⧸ Subgroup.center F, a * b ≠ b * a := by
    intro F _ _ hF
    obtain ⟨⟨-, hs, hab⟩, -, ⟨f, hf3, hfZ⟩, h5⟩ := hF
    refine ⟨hs, ?_, h5, hab⟩
    have hf1 : (f : F ⧸ Subgroup.center F) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff]
      exact hfZ
    have hof : orderOf (f : F ⧸ Subgroup.center F) = 3 :=
      orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hf3, QuotientGroup.mk_one]) hf1
    exact hof ▸ orderOf_dvd_natCard _
  obtain ⟨hS₁s, hS₁3, hS₁5, hS₁ab⟩ := hSdata hF₁
  obtain ⟨hS₂s, hS₂3, hS₂5, hS₂ab⟩ := hSdata hF₂
  have hker : ∀ {P F : Type} [Group P] [Finite P] [Group F] [Finite F] (ι : P →* Q)
      (φ : P →* F), ¬ 3 ∣ Nat.card ι.ker → Function.Surjective φ → ¬ 3 ∣ Nat.card φ.ker →
      IsTwelveType F → (ρ.comp ι).ker ≤ ((QuotientGroup.mk' (Subgroup.center F)).comp φ).ker := by
    intro P F _ _ _ _ ι φ hι hφ hφ3 hF p hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact map_mem_center_of_mem_centralizer_ON hQ hK hKON ι hι φ hφ hφ3 hF (hρ1 _ hp)
  obtain ⟨f₁, hf₁, -⟩ := exists_lift_range (ρ.comp ι₁)
    ((QuotientGroup.mk' (Subgroup.center F₁)).comp φ₁)
    ((QuotientGroup.mk'_surjective _).comp hφ₁) (hker ι₁ φ₁ hι₁ hφ₁ hφ₁3 hF₁)
  obtain ⟨f₂, hf₂, -⟩ := exists_lift_range (ρ.comp ι₂)
    ((QuotientGroup.mk' (Subgroup.center F₂)).comp φ₂)
    ((QuotientGroup.mk'_surjective _).comp hφ₂) (hker ι₂ φ₂ hι₂ hφ₂ hφ₂3 hF₂)
  have hNW : ∀ {P : Type} [Group P] (ι : P →* Q), ι.range ≤ Subgroup.normalizer (W : Set Q) →
      (ρ.comp ι).range ≤ Subgroup.normalizer ((W.map ρ : Subgroup (MulAut ↥K)) : Set _) := by
    intro P _ ι hι
    rintro _ ⟨p, rfl⟩
    rw [MonoidHom.comp_apply]
    exact Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ (hι ⟨p, rfl⟩))
  have hcomm : ⁅(ρ.comp ι₁).range, (ρ.comp ι₂).range⁆ ≤ W.map ρ := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [commutatorElement_def]
    refine ⟨ι₁ p * ι₂ q * (ι₁ p)⁻¹ * (ι₂ q)⁻¹, hW p q, ?_⟩
    simp only [map_mul, map_inv, MonoidHom.comp_apply]
  have hW3' : ¬ 3 ∣ Nat.card (W.map ρ) := fun h => hW3 (h.trans (Subgroup.card_map_dvd _ _))
  have hdvd := card_mul_card_dvd_of_commutator_le (hNW ι₁ hW₁) (hNW ι₂ hW₂) hcomm hW3' hS₁s hS₂s
    hS₁3 hS₂3 hS₁ab hS₂ab f₁ hf₁ f₂ hf₂
  have h25 : 25 ∣ Nat.card (MulAut ↥K) := by
    refine (Nat.mul_dvd_mul hS₁5 hS₂5).trans (hdvd.trans ?_)
    exact Subgroup.card_subgroup_dvd_card _
  exact not_twentyfive_dvd_card_mulAut_of_tripleCover_ON hKON hK.1.1 h25

end Frame

variable {G : Type} [Group G] [Finite G]


theorem false_of_commuting_of_tripleCover_ON {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {d : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hKON : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON)
    {P₁ P₂ N : Subgroup G} (hP₁ : P₁ ≤ Subgroup.centralizer ({d} : Set G))
    (hP₂ : P₂ ≤ Subgroup.centralizer ({d} : Set G)) (hN : N ≤ Subgroup.centralizer ({d} : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) (hP₁N : P₁ ≤ Subgroup.normalizer (N : Set G))
    (hP₂N : P₂ ≤ Subgroup.normalizer (N : Set G)) (hcomm : ⁅P₁, P₂⁆ ≤ N)
    {F₁ F₂ : Type} [Group F₁] [Finite F₁] [Group F₂] [Finite F₂] (φ₁ : ↥P₁ →* F₁)
    (φ₂ : ↥P₂ →* F₂) (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hφ₁3 : ¬ 3 ∣ Nat.card φ₁.ker) (hφ₂3 : ¬ 3 ∣ Nat.card φ₂.ker) (hF₁ : IsTwelveType F₁)
    (hF₂ : IsTwelveType F₂) : False := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  obtain ⟨-, hθc, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥C).Normal := by haveI := hθc; infer_instance
  set θ := aschbacherSolvableCore 3 ↥C with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hQ : NoE81TwoLocal (↥C ⧸ θ) := noE81TwoLocal_quot h hθ3
  obtain ⟨L', hL', rfl⟩ := hK
  have hKb : IsComponent (L'.map π) := isComponent_map_of_mem_thetaComponents Nat.prime_three hL'
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hL'.2.1
  have e : ↥L' ≃* ↥(L'.map C.subtype) := L'.equivMapOfInjective C.subtype C.subtype_injective
  have hKbON : Sec4.IsTripleCover ↥(L'.map π) CFSG.Blueprint.NativeSporadic.ON :=
    KFacts.KS14.isTripleCover_congr η
      (KFacts.KS14.isTripleCover_congr (Ronan148H.thetaQuotEquiv e).symm hKON)
  have hι : ∀ {P : Subgroup G} (hP : P ≤ C),
      ¬ 3 ∣ Nat.card (π.comp (Subgroup.inclusion hP)).ker := by
    intro P hP h3
    have hk : (π.comp (Subgroup.inclusion hP)).ker = θ.comap (Subgroup.inclusion hP) := by
      rw [← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rw [hk] at h3
    exact hθ3 (h3.trans (Subgroup.card_comap_dvd_of_injective θ _
      (Subgroup.inclusion_injective hP)))
  set W := (N.subgroupOf C).map π with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    have := h3.trans (Subgroup.card_map_dvd (N.subgroupOf C) π)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv] at this
    exact hN3 this
  have hWn : ∀ {P : Subgroup G} (hP : P ≤ C), P ≤ Subgroup.normalizer (N : Set G) →
      (π.comp (Subgroup.inclusion hP)).range ≤ Subgroup.normalizer (W : Set (↥C ⧸ θ)) := by
    intro P hP hPN
    rintro _ ⟨p, rfl⟩
    refine Subgroup.le_normalizer_map π ⟨Subgroup.inclusion hP p, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hPN p.2) n
  have hWc : ∀ (p : ↥P₁) (q : ↥P₂), π (Subgroup.inclusion hP₁ p) * π (Subgroup.inclusion hP₂ q) *
      (π (Subgroup.inclusion hP₁ p))⁻¹ * (π (Subgroup.inclusion hP₂ q))⁻¹ ∈ W := by
    intro p q
    refine ⟨Subgroup.inclusion hP₁ p * Subgroup.inclusion hP₂ q * (Subgroup.inclusion hP₁ p)⁻¹ *
      (Subgroup.inclusion hP₂ q)⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have := hcomm (Subgroup.commutator_mem_commutator p.2 q.2)
    rw [commutatorElement_def] at this
    simpa using this
  exact false_of_commuting_ON_quot hQ hKb hKbON (π.comp (Subgroup.inclusion hP₁))
    (π.comp (Subgroup.inclusion hP₂)) (hι hP₁) (hι hP₂) φ₁ φ₂ hφ₁ hφ₂ hφ₁3 hφ₂3 hF₁ hF₂ hW3
    (hWn hP₁ hP₁N) (hWn hP₂ hP₂N) hWc

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
