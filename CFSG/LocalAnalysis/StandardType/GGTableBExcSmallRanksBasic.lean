module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBExcSmallRanks

theorem card_le_sq_of_prod_units {K₁ K₂ : Type*} [Field K₁] [Finite K₁] [Field K₂] [Finite K₂]
    {p : ℕ} (hp : 0 < p) (A : Subgroup (K₁ˣ × K₂ˣ)) (hA : ∀ x ∈ A, x ^ p = 1) :
    Nat.card A ≤ p ^ 2 := by
  have h1 : Nat.card (A.map (MonoidHom.fst _ _)) ≤ p :=
    TableB.card_le_of_isCyclic hp inferInstance (by
      rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Prod.fst (hA x hx))
  have h2 : Nat.card (A.map (MonoidHom.snd _ _)) ≤ p :=
    TableB.card_le_of_isCyclic hp inferInstance (by
      rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Prod.snd (hA x hx))
  have : Finite (A.map (MonoidHom.fst K₁ˣ K₂ˣ)) := Subtype.finite
  have : Finite (A.map (MonoidHom.snd K₁ˣ K₂ˣ)) := Subtype.finite
  have hinj : Function.Injective (fun a : A =>
      ((⟨a.1.1, Subgroup.mem_map_of_mem _ a.2⟩ : A.map (MonoidHom.fst _ _)),
        (⟨a.1.2, Subgroup.mem_map_of_mem _ a.2⟩ : A.map (MonoidHom.snd _ _)))) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hxy.1) (congrArg Subtype.val hxy.2))
  calc Nat.card A ≤ Nat.card (A.map (MonoidHom.fst _ _) × A.map (MonoidHom.snd _ _)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (A.map (MonoidHom.fst _ _)) * Nat.card (A.map (MonoidHom.snd _ _)) :=
        Nat.card_prod _ _
    _ ≤ p * p := Nat.mul_le_mul h1 h2
    _ = p ^ 2 := (sq p).symm

theorem card_le_sq_of_le_range {K₁ K₂ G : Type*} [Field K₁] [Finite K₁] [Field K₂] [Finite K₂]
    [Group G] {p : ℕ} (hp : 0 < p) (ι : K₁ˣ × K₂ˣ →* G) (hι : Function.Injective ι)
    {A : Subgroup G} (hAι : A ≤ ι.range) (hA : ∀ x ∈ A, x ^ p = 1) : Nat.card A ≤ p ^ 2 := by
  have hmap : (A.comap ι).map ι = A := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hAι]
  rw [← hmap, Subgroup.card_map_of_injective hι]
  refine card_le_sq_of_prod_units hp _ fun x hx => hι ?_
  rw [map_pow, map_one]
  exact hA _ hx

section Normalizer

variable {G : Type*} [Group G]

@[expose] def omegaSub (T : Subgroup G) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (p : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ T ∧ x ^ p = 1}
  mul_mem' {x y} hx hy := ⟨T.mul_mem hx.1 hy.1, by
    rw [(Commute.mul_pow (hTc x hx.1 y hy.1) p), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨T.one_mem, one_pow p⟩
  inv_mem' {x} hx := ⟨T.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_omegaSub {T : Subgroup G} {hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x} {p : ℕ} {x : G} :
    x ∈ omegaSub T hTc p ↔ x ∈ T ∧ x ^ p = 1 :=
  Iff.rfl

theorem commute_of_zpow {p : ℕ} (hp : p.Prime) {n h : G} {i : ℤ} (hi : ¬ (p : ℤ) ∣ i)
    (h1 : Commute (n ^ i) h) (h2 : Commute (n ^ p) h) : Commute n h := by
  have hcop : IsCoprime (p : ℤ) i := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    have : ¬ p ∣ i.natAbs := fun hd => hi (Int.natCast_dvd.mpr hd)
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  obtain ⟨u, v, huv⟩ := hcop
  have e : n = (n ^ p) ^ u * (n ^ i) ^ v := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (p : ℤ) u, mul_comm i v,
      huv, zpow_one]
  rw [e]
  exact (h2.zpow_left u).mul_left (h1.zpow_left v)

variable [Finite G]

theorem card_lt_of_normalizer_pow_mem {p k : ℕ} (hp : p.Prime) {T : Subgroup G}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT : ∀ A : Subgroup G, A ≤ T → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ k)
    {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) (hnp : n ^ p ∈ T)
    {h₀ : G} (hh₀ : h₀ ∈ T) (hh₀p : h₀ ^ p = 1) (hnh : n * h₀ ≠ h₀ * n)
    (hord : (Nat.card G).factorization p ≤ (Nat.card T).factorization p + 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) : Nat.card E < p ^ (k + 1) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  set N := Subgroup.normalizer (T : Set G) with hNdef
  have hTN : T ≤ N := Subgroup.le_normalizer
  set T' : Subgroup N := T.subgroupOf N with hT'
  have hT'n : T'.Normal := Subgroup.normal_in_normalizer
  set π : N →* N ⧸ T' := QuotientGroup.mk' T' with hπ
  have hπker : ∀ x : N, π x = 1 ↔ (x : G) ∈ T := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hT', Subgroup.mem_subgroupOf]
  set n' : N := ⟨n, hn⟩ with hn'
  have hnT : n ∉ T := fun h => hnh (hTc n h h₀ hh₀)
  have hπp : π n' ^ p = 1 := by
    rw [← map_pow, hπker]
    exact hnp
  have hπ1 : π n' ≠ 1 := by
    rw [Ne, hπker]
    exact hnT
  have hordn : orderOf (π n') = p := orderOf_eq_prime hπp hπ1
  set Z := Subgroup.zpowers (π n') with hZ
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hordn]
  set M : Subgroup N := Z.comap π with hM
  have hTM : T' ≤ M := fun x hx => by
    show π x ∈ Z
    rw [(hπker x).mpr (Subgroup.mem_subgroupOf.mp hx)]
    exact Z.one_mem
  have hMcard : Nat.card M = p * Nat.card T := by
    let f : M →* N ⧸ T' := π.comp M.subtype
    have hrange : f.range = Z := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hM,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T')]
    have hker : f.ker = T'.subgroupOf M := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show π (x : N) = 1 ↔ (x : N) ∈ T.subgroupOf N
      rw [Subgroup.mem_subgroupOf]
      exact hπker x
    have h1 := TableB.card_range_mul_card_ker f
    rw [hrange, hZcard, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv,
      hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv] at h1
    exact h1.symm
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hMfac : (Nat.card M).factorization p = (Nat.card T).factorization p + 1 := by
    rw [hMcard, Nat.factorization_mul hp.ne_zero hT0, Finsupp.add_apply, hp.factorization_self,
      add_comm]
  obtain SM : Sylow p M := default
  set SG : Subgroup G := ((SM : Subgroup M).map M.subtype).map N.subtype with hSG
  have hSGcard : Nat.card SG = p ^ (Nat.card M).factorization p := by
    rw [hSG, Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity]
  have hMG : (Nat.card M).factorization p ≤ (Nat.card G).factorization p := by
    have hdvd : Nat.card M ∣ Nat.card G := by
      have h1 : Nat.card ((M.map N.subtype : Subgroup G)) = Nat.card M :=
        Subgroup.card_map_of_injective N.subtype_injective
      rw [← h1]
      exact Subgroup.card_subgroup_dvd_card _
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hG0).mpr hdvd p
  let S : Sylow p G := Sylow.ofCard SG (by rw [hSGcard]; congr 1; omega)
  obtain ⟨Q, hEQ⟩ := (TableB.isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hmem : ∀ e ∈ E, g * e * g⁻¹ ∈ SG := by
    intro e he
    have h1 : g * e * g⁻¹ ∈ ((g • Q : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (Q : Subgroup G) (hEQ he)
    rw [hg] at h1
    exact h1
  set E₁ := E.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE₁ab : IsElemAbelian p E₁ := TableB.isElemAbelian_map hE _
  have hE₁S : ∀ x ∈ E₁, ∃ y : N, y ∈ M ∧ (y : G) = x := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hmem e he)
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨y, hzy ▸ z.2, hyx⟩
  by_contra hlt
  push Not at hlt
  have hE₁N : E₁ ≤ N := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hE₁S x hx
    exact y.2
  set E₂ : Subgroup N := E₁.subgroupOf N with hE₂
  have hE₂M : E₂ ≤ M := fun y hy => by
    obtain ⟨y', hy'M, hy'⟩ := hE₁S y (Subgroup.mem_subgroupOf.mp hy)
    have hyy : y' = y := Subtype.ext hy'
    rw [← hyy]
    exact hy'M
  have hE₂card : Nat.card E₂ = Nat.card E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁N).toEquiv
  have hidx : Nat.card E₁ ≤ p * Nat.card (E₁ ⊓ T : Subgroup G) := by
    let f : E₂ →* N ⧸ T' := π.comp E₂.subtype
    have hrange : f.range ≤ Z := by
      rintro _ ⟨x, rfl⟩
      exact hE₂M x.2
    have hker : Nat.card f.ker = Nat.card (E₁ ⊓ T : Subgroup G) := by
      have hmap : (f.ker.map E₂.subtype).map N.subtype = E₁ ⊓ T := by
        ext x
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨Subgroup.mem_subgroupOf.mp z.2, (hπker (z : N)).mp hz⟩
        · rintro ⟨hx1, hx2⟩
          exact ⟨⟨x, hE₁N hx1⟩, ⟨⟨⟨x, hE₁N hx1⟩, Subgroup.mem_subgroupOf.mpr hx1⟩,
            (hπker _).mpr hx2, rfl⟩, rfl⟩
      rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective,
        Subgroup.card_map_of_injective E₂.subtype_injective]
    have h1 := TableB.card_range_mul_card_ker f
    have h2 : Nat.card f.range ≤ p := hZcard ▸ Subgroup.card_le_of_le hrange
    rw [hE₂card, hker] at h1
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hAle : Nat.card (E₁ ⊓ T : Subgroup G) ≤ p ^ k :=
    hT _ inf_le_right (fun x hx => hE₁ab.2 x hx.1)
  have hAeq : p ^ k ≤ Nat.card (E₁ ⊓ T : Subgroup G) := by
    have h1 : p * p ^ k ≤ p * Nat.card (E₁ ⊓ T : Subgroup G) := by
      rw [← pow_succ']
      exact hlt.trans (hE₁card ▸ hidx)
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  set Ω := omegaSub T hTc p with hΩdef
  have hΩ : Nat.card Ω ≤ p ^ k := hT Ω (fun x hx => hx.1) (fun x hx => hx.2)
  have hAΩ : (E₁ ⊓ T : Subgroup G) ≤ Ω := fun x hx => ⟨hx.2, hE₁ab.2 x hx.1⟩
  have hAΩeq : (E₁ ⊓ T : Subgroup G) = Ω := Subgroup.eq_of_le_of_card_ge hAΩ (by omega)
  have hh₀E : h₀ ∈ E₁ := by
    have h1 : h₀ ∈ Ω := ⟨hh₀, hh₀p⟩
    rw [← hAΩeq] at h1
    exact h1.1
  obtain ⟨e, heE, heT⟩ : ∃ e ∈ E₁, e ∉ T := by
    by_contra hcon
    push Not at hcon
    have hle : E₁ ≤ E₁ ⊓ T := fun x hx => ⟨hx, hcon x hx⟩
    have h1 := Subgroup.card_le_of_le hle
    have h3 : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)
    omega
  obtain ⟨y, hyM, rfl⟩ := hE₁S e heE
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (show π y ∈ Z from hyM)
  set t : G := (((n' ^ i)⁻¹ * y : N) : G) with ht_def
  have ht : t ∈ T := by
    rw [ht_def, ← hπker, map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
  have hy_eq : (y : G) = n ^ i * t := by
    rw [ht_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, mul_inv_cancel_left]
  have hpi : ¬ (p : ℤ) ∣ i := by
    rintro ⟨j, rfl⟩
    apply heT
    rw [hy_eq, zpow_mul, zpow_natCast]
    exact T.mul_mem (T.zpow_mem hnp j) ht
  have hcomm_e : (y : G) * h₀ = h₀ * y := TableB.IsElemAbelian.comm hE₁ab heE hh₀E
  have hct : t * h₀ = h₀ * t := hTc t ht h₀ hh₀
  have hni : Commute (n ^ i) h₀ := by
    have h2 : n ^ i * h₀ * t = h₀ * n ^ i * t := by
      calc n ^ i * h₀ * t = n ^ i * (t * h₀) := by rw [mul_assoc, hct]
        _ = (y : G) * h₀ := by rw [hy_eq, mul_assoc]
        _ = h₀ * y := hcomm_e
        _ = h₀ * n ^ i * t := by rw [hy_eq, mul_assoc]
    exact mul_right_cancel h2
  exact hnh (commute_of_zpow hp hpi hni (hTc _ hnp h₀ hh₀)).eq

end Normalizer

end TableBExcSmallRanks

end CFSG.StandardType
