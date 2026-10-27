module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.Factors
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

@[expose] def IsASimple (A K : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (K : Set G) ∧ (∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) ∧
    ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → A ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = K

@[expose] def simpleComponents (K : Subgroup G) : Set (Subgroup G) :=
  {T | T ≤ K ∧ (T.subgroupOf K).Normal ∧ IsSimpleGroup T ∧ ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x}

variable [Finite G] {A K : Subgroup G}

omit [Finite G] in
private theorem simpleComponents_conj_mem {T : Subgroup G} (hT : T ∈ simpleComponents K) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) : k * t * k⁻¹ ∈ T :=
  (Subgroup.normal_subgroupOf_iff hT.1).mp hT.2.1 t k ht hk

omit [Finite G] in
private theorem simpleComponents_inf_eq_bot {T T' : Subgroup G} (hT : T ∈ simpleComponents K)
    (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') : T ⊓ T' = ⊥ := by
  have hTK := hT.1
  have hT'K := hT'.1
  have hTs : IsSimpleGroup T := hT.2.2.1
  have hT's : IsSimpleGroup T' := hT'.2.2.1
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hT.2.2.2
  have hD : ((T ⊓ T').subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro u v hu hv
    obtain ⟨huT, huT'⟩ := Subgroup.mem_inf.mp hu
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hv huT) (inv_mem hv),
      simpleComponents_conj_mem hT' huT' (hTK hv)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ T').subgroupOf T) with h | h
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : T) ∈ (T ⊓ T').subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    have hle : T ≤ T' := fun x hx => by
      have hmem : (⟨x, hx⟩ : T) ∈ (T ⊓ T').subgroupOf T := by rw [h]; trivial
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    have hN : (T.subgroupOf T').Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro u v hu hv
      exact simpleComponents_conj_mem hT hu (hT'K hv)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf T') with h' | h'
    · have hx₀1 : x₀ = 1 := by
        have hmem : (⟨x₀, hle hx₀⟩ : T') ∈ T.subgroupOf T' := hx₀
        rw [h', Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      exact hxy₀ (by rw [hx₀1, one_mul, mul_one])
    · refine hne (le_antisymm hle fun x hx => ?_)
      have hmem : (⟨x, hx⟩ : T') ∈ T.subgroupOf T' := by rw [h']; trivial
      exact hmem

omit [Finite G] in
private theorem simpleComponents_commute_elem {T T' : Subgroup G} (hT : T ∈ simpleComponents K)
    (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') {x y : G} (hx : x ∈ T) (hy : y ∈ T') :
    x * y = y * x := by
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ T' := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := simpleComponents_conj_mem hT (inv_mem hx) (hT'.1 hy)
      simpa [mul_assoc] using mul_mem hx this
    · exact mul_mem (simpleComponents_conj_mem hT' hy (hT.1 hx)) (inv_mem hy)
  rw [simpleComponents_inf_eq_bot hT hT' hne, Subgroup.mem_bot, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul] at hmem
  exact hmem

private theorem IsASimple.exists_factors (hK : IsASimple A K) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ (∀ i, S i ∈ simpleComponents K) ∧
      (∀ T ∈ simpleComponents K, ∃ i, T = S i) ∧
      (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) ∧
      (∀ i j, ∃ a ∈ A, S j = (S i).map (MulAut.conj a).toMonoidHom) ∧ (⨆ i, S i) = K := by
  obtain ⟨hA, hnc, hmin⟩ := hK
  obtain ⟨r, S, hr, hSK, hSn, hSs, hSnc, hSc, hSt, hSg⟩ := exists_aSimple_factors hA hnc hmin
  have hS : ∀ i, S i ∈ simpleComponents K := fun i => ⟨hSK i, hSn i, hSs i, hSnc i⟩
  refine ⟨r, S, hr, hS, fun T hT => ?_, hSc, hSt, hSg⟩
  by_contra hcon
  push Not at hcon
  have hKle : K ≤ Subgroup.centralizer (T : Set G) :=
    calc K = ⨆ i, S i := hSg.symm
      _ ≤ _ := iSup_le fun i y hy => by
        rw [Subgroup.mem_centralizer_iff]
        exact fun x hx => simpleComponents_commute_elem hT (hS i) (hcon i) hx hy
  have hTK : T ≤ K := hT.1
  obtain ⟨-, -, -, x, hx, y, hy, hxy⟩ := hT
  exact hxy (Subgroup.mem_centralizer_iff.mp (hKle (hTK hy)) x hx)

theorem IsASimple.simpleComponents_nonempty (hK : IsASimple A K) :
    (simpleComponents K).Nonempty := by
  obtain ⟨r, S, hr, hS, -⟩ := hK.exists_factors
  exact ⟨S ⟨0, hr⟩, hS _⟩

theorem IsASimple.components_commute (hK : IsASimple A K) {T T' : Subgroup G}
    (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') :
    T ≤ Subgroup.centralizer (T' : Set G) ∧ T ⊓ T' = ⊥ := by
  obtain ⟨r, S, -, -, hSall, hSc, -⟩ := hK.exists_factors
  obtain ⟨i, rfl⟩ := hSall T hT
  obtain ⟨j, rfl⟩ := hSall T' hT'
  refine ⟨fun x hx => ?_, simpleComponents_inf_eq_bot hT hT' hne⟩
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => (hSc i j (fun h => hne (by rw [h])) x hx y hy).symm

theorem IsASimple.iSup_components (hK : IsASimple A K) :
    (⨆ T ∈ simpleComponents K, T) = K := by
  obtain ⟨r, S, -, hS, -, -, -, hSg⟩ := hK.exists_factors
  refine le_antisymm (iSup₂_le fun T hT => hT.1) ?_
  calc K = ⨆ i, S i := hSg.symm
    _ ≤ _ := iSup_le fun i => le_iSup₂_of_le (S i) (hS i) le_rfl

theorem IsASimple.components_transitive (hK : IsASimple A K) {T T' : Subgroup G}
    (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) :
    ∃ a ∈ A, T' = T.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨r, S, -, -, hSall, -, hSt, -⟩ := hK.exists_factors
  obtain ⟨i, rfl⟩ := hSall T hT
  obtain ⟨j, rfl⟩ := hSall T' hT'
  exact hSt i j

theorem IsASimple.normalizes_component_iff (hK : IsASimple A K) (hA : IsMulCommutative A)
    {T T' : Subgroup G} (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) {a : G}
    (ha : a ∈ A) : T.map (MulAut.conj a).toMonoidHom = T ↔
      T'.map (MulAut.conj a).toMonoidHom = T' := by
  have key : ∀ {T T' : Subgroup G}, T ∈ simpleComponents K → T' ∈ simpleComponents K →
      T.map (MulAut.conj a).toMonoidHom = T → T'.map (MulAut.conj a).toMonoidHom = T' := by
    intro T T' hT hT' h
    obtain ⟨b, hb, rfl⟩ := hK.components_transitive hT hT'
    have hab : a * b = b * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
    have hcomp : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
      ext x
      change a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹
      calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
        _ = (b * a) * x * (b * a)⁻¹ := by rw [hab]
        _ = b * (a * x * a⁻¹) * b⁻¹ := by group
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h]
  exact ⟨key hT hT', key hT' hT⟩

theorem IsASimple.exists_diagonal (hK : IsASimple A K) {p : ℕ} (hp : p.Prime)
    {T : Subgroup G} (hT : T ∈ simpleComponents K) {a : G}
    (ha : a ∈ A) (hap : a ^ p = 1) (hmove : T.map (MulAut.conj a).toMonoidHom ≠ T) :
    ∃ φ : T →* G, Function.Injective φ ∧ (∀ t, φ t ∈ K) ∧ ∀ t, a * φ t * a⁻¹ = φ t := by
  obtain ⟨hAK, -, -⟩ := hK
  obtain ⟨hTK, hTn, hTs, x₀, hx₀, y₀, hy₀, hxy₀⟩ := hT
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = A ⊔ K := ⟨_, rfl⟩
  have hAH : A ≤ H := hH ▸ le_sup_left
  have hKH : K ≤ H := hH ▸ le_sup_right
  have hTH : T ≤ H := hTK.trans hKH
  have hNnormal : (K.subgroupOf H).Normal :=
    hH ▸ Subgroup.normal_subgroupOf_sup_of_le_normalizer hAK
  let eT : T.subgroupOf H ≃* T := Subgroup.subgroupOfEquivOfLe hTH
  have hTs' : IsSimpleGroup (T.subgroupOf H) := eT.isSimpleGroup
  have hmove' : (⟨a, hAH ha⟩ : H) ∉
      Subgroup.normalizer ((T.subgroupOf H : Subgroup H) : Set H) := by
    intro hmem
    refine hmove (Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => (Subgroup.mem_normalizer_iff.mp hmem ⟨g, hTH hg⟩).mp hg, fun hg => ?_⟩
    have hgH : g ∈ H := by
      have h1 : a * g * a⁻¹ ∈ H := hTH hg
      have h2 : g = a⁻¹ * (a * g * a⁻¹) * a := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem (hAH ha)) h1) (hAH ha)
    exact (Subgroup.mem_normalizer_iff.mp hmem ⟨g, hgH⟩).mpr hg
  obtain ⟨φ, hφinj, hφN, hφfix⟩ := CFSG.SignalizerFunctorTheorem.exists_diagonal (H := H) hp
    (a := ⟨a, hAH ha⟩) (Subtype.ext (by simpa using hap)) (N := K.subgroupOf H)
    (T := T.subgroupOf H) (fun x hx => hTK hx)
    (fun n hn t ht => (Subgroup.normal_subgroupOf_iff hTK).mp hTn (t : G) (n : G) ht hn)
    ⟨⟨⟨x₀, hTH hx₀⟩, hx₀⟩, ⟨⟨y₀, hTH hy₀⟩, hy₀⟩, fun h =>
      hxy₀ (congrArg (fun z : T.subgroupOf H => ((z : H) : G)) h)⟩ hmove'
  refine ⟨H.subtype.comp (φ.comp eT.symm.toMonoidHom),
    H.subtype_injective.comp (hφinj.comp eT.symm.injective), fun t => hφN _, fun t => ?_⟩
  simpa using congrArg Subtype.val (hφfix (eT.symm t))

theorem IsASimple.exists_centralizing_of_normalizing (hK : IsASimple A K) {p : ℕ} (hp : p.Prime)
    (hA : IsElemAbelian p A)
    (hcyc : ∀ T ∈ simpleComponents K, ∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P)
    {B : Subgroup G} (hBA : B ≤ A) (hB : p ^ 2 ≤ Nat.card B)
    (hnorm : ∀ b ∈ B, ∀ T ∈ simpleComponents K, T.map (MulAut.conj b).toMonoidHom = T) :
    ∃ b ∈ B, b ≠ 1 ∧ ∀ x ∈ K, b * x * b⁻¹ = x := by
  have := hA.1
  obtain ⟨T₁, hT₁⟩ := hK.simpleComponents_nonempty
  have hBN : B ≤ Subgroup.normalizer (T₁ : Set G) := fun b hb =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hnorm b hb T₁ hT₁)
  let ρ : B →* MulAut T₁ := T₁.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hρ : ∀ (b : B) (t : T₁), ((ρ b t : T₁) : G) = b * t * (b : G)⁻¹ := fun b t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe T₁ (Subgroup.inclusion hBN b) t
  have hpow : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hA.2 b (hBA b.2))
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective (fun b : B => ⟨1, by simpa using hpow b⟩) ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := (hcyc T₁ hT₁ ρ.range hRp).exists_ofOrder_eq_natCard
  have hgp : g ^ p = 1 := by
    obtain ⟨b, hb⟩ := g.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← hb, ← map_pow, hpow b, map_one]
    rfl
  have hcardle : Nat.card ρ.range ≤ p :=
    Nat.le_of_dvd hp.pos (hg ▸ orderOf_dvd_of_pow_eq_one hgp)
  have hnotinj : ¬ Function.Injective ρ := by
    intro hinj
    have h1 : Nat.card B = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨b, hb1, hbne⟩ := hnotinj
  have hT₁c : ∀ t ∈ T₁, (b : G) * t * (b : G)⁻¹ = t := by
    intro t ht
    simpa [hb1] using (hρ b ⟨t, ht⟩).symm
  have hcomp : ∀ T ∈ simpleComponents K, T ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    intro T hT x hx
    obtain ⟨c, hc, hTeq⟩ := hK.components_transitive hT₁ hT
    rw [hTeq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcb : Commute c (b : G) :=
      congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : A) ⟨b, hBA b.2⟩)
    have htb : Commute t (b : G) := by
      have := hT₁c t ht
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    exact ((hcb.mul_left htb).mul_left hcb.inv_left).eq
  refine ⟨b, b.2, fun h => hbne (Subtype.ext h), fun x hx => ?_⟩
  have hKc : K ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    rw [← hK.iSup_components]
    exact iSup₂_le hcomp
  rw [mul_inv_eq_iff_eq_mul]
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hKc hx)).symm

end CFSG.SignalizerFunctorTheorem.Nonsolvable
