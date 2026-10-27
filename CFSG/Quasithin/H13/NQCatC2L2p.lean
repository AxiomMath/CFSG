module

public import CFSG.Quasithin.H13.NQCatC2B
public import CFSG.Quasithin.H13.NQCatC2JH
public import CFSG.Quasithin.H13.NQCatT513PSL2

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513 CFSG.GorensteinWalter

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

section Transport

variable {A : Type} [Group A] {Q : Subgroup A} {P : Type} [Group P] (e : ↥Q ≃* P)

@[expose] noncomputable def tr (X : Subgroup A) : Subgroup P := (X.subgroupOf Q).map e.toMonoidHom

theorem mem_tr {X : Subgroup A} {y : P} : y ∈ tr e X ↔ ((e.symm y : ↥Q) : A) ∈ X := by
  rw [tr, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

theorem apply_mem_tr {X : Subgroup A} {a : A} (ha : a ∈ Q) : e ⟨a, ha⟩ ∈ tr e X ↔ a ∈ X := by
  rw [mem_tr, MulEquiv.symm_apply_apply]

theorem card_tr {X : Subgroup A} (hX : X ≤ Q) : Nat.card (tr e X) = Nat.card X := by
  rw [tr, Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

theorem isCyclic_tr {X : Subgroup A} (hX : X ≤ Q) (hc : IsCyclic ↥X) : IsCyclic ↥(tr e X) := by
  have : IsCyclic ↥(X.subgroupOf Q) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hX).symm.surjective
  exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap _)
    (e.toMonoidHom.subgroupMap_surjective _)

theorem tr_mono {X Y : Subgroup A} (hXY : X ≤ Y) : tr e X ≤ tr e Y := by
  intro y hy
  rw [mem_tr] at hy ⊢
  exact hXY hy

theorem mem_normalizer_tr {X : Subgroup A} {a : A} (ha : a ∈ Q)
    (haN : a ∈ Subgroup.normalizer (X : Set A)) :
    e ⟨a, ha⟩ ∈ Subgroup.normalizer (tr e X : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_tr, mem_tr, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  exact Subgroup.mem_normalizer_iff.mp haN _

theorem mem_normalizer_of_tr [Finite A] {X : Subgroup A} (hX : X ≤ Q) {a : A} (ha : a ∈ Q)
    (haN : e ⟨a, ha⟩ ∈ Subgroup.normalizer (tr e X : Set P)) :
    a ∈ Subgroup.normalizer (X : Set A) := by
  apply mem_normalizer_of_conj_mem'
  intro x hx
  have h1 := (Subgroup.mem_normalizer_iff.mp haN (e ⟨x, hX hx⟩)).mp
    ((apply_mem_tr e (hX hx)).mpr hx)
  rw [mem_tr, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply] at h1
  exact h1

end Transport

variable {A : Type} [Group A] [Finite A]

theorem nonempty_l24_of_le {Q R : Subgroup A} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (e : ↥Q ≃* PSL2 K)
    (hRQ : R ≤ Q) (hL : CFSG.Blueprint.LieModel (ModO2 R) .PSL 2 2 2) :
    Nonempty (↥R ≃* L24) := by
  obtain ⟨eX⟩ := exists_l24_of_lieModel hL
  obtain ⟨u, hu, hPu, -⟩ := psl2_card_four_mul hp hK hp8
  have hQ : Nat.card ↥Q = 4 * u := by rw [Nat.card_congr e.toEquiv, hPu]
  refine nonempty_equiv_l24_of_surjective eX (MonoidHom.id _) (fun x => ⟨x, rfl⟩) ?_ ?_
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr (fun x y hxy => hxy)]
    exact IsPGroup.of_bot
  · intro X hX
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hRQ)]
    exact card_le_four_of_isPGroup hu hQ _ (hX.map _)

theorem psl2_img_le
    {Q R T C : Subgroup A} {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p)
    (e : ↥Q ≃* PSL2 K) (hT : IsSylowTwoOf T Q) (hCQ : C ≤ Q) (hCc : IsCyclic ↥C)
    (hCo : Odd (Nat.card C)) (hperm : ∀ t ∈ T, ∀ x ∈ C, ∃ x' ∈ C, ∃ t' ∈ T, t * x = x' * t')
    (hRQ : R ≤ Q) (eR : ↥R ≃* L24) (hTR : T ≤ R) {b : A} (hbR : b ∈ R) (hb3 : orderOf b = 3)
    (hbC : b ∈ Subgroup.normalizer (C : Set A)) (hbT : b ∈ Subgroup.normalizer (T : Set A)) :
    C ≤ R ⊓ Subgroup.normalizer (T : Set A) := by
  let T' : Sylow 2 (PSL2 K) := (sylowOf hT).mapSurjective (f := e.toMonoidHom) e.surjective
  have hT' : (T' : Subgroup (PSL2 K)) = tr e T := rfl
  let eR' : ↥(tr e R) ≃* L24 :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hRQ).trans eR)
  have hperm' : ∀ t ∈ (T' : Subgroup (PSL2 K)), ∀ x ∈ tr e C, ∃ x' ∈ tr e C,
      ∃ t' ∈ (T' : Subgroup (PSL2 K)), t * x = x' * t' := by
    rw [hT']
    intro t ht x hx
    rw [mem_tr] at ht hx
    obtain ⟨x', hx', t'', ht'', he⟩ := hperm _ ht _ hx
    refine ⟨e ⟨x', hCQ hx'⟩, (apply_mem_tr e _).mpr hx', e ⟨t'', hT.1 ht''⟩,
      (apply_mem_tr e _).mpr ht'', ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact Subtype.ext he
  have hle := core_psl2_prime_le hK hp8 hp11 (D₁ := tr e C) (R₁ := tr e R) T'
    (isCyclic_tr e hCQ hCc) (by rw [card_tr e hCQ]; exact hCo) hperm' eR'
    (by rw [hT']; exact tr_mono e hTR) ((apply_mem_tr e (hRQ hbR)).mpr hbR)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hb3]) (mem_normalizer_tr e (hRQ hbR) hbC)
    (by rw [hT']; exact mem_normalizer_tr e (hRQ hbR) hbT)
  intro c hc
  have h1 := Subgroup.mem_inf.mp (hle ((apply_mem_tr e (hCQ hc)).mpr hc))
  refine Subgroup.mem_inf.mpr ⟨(apply_mem_tr e (hCQ hc)).mp h1.1,
    mem_normalizer_of_tr e hT.1 (hCQ hc) ?_⟩
  rw [← hT']
  exact h1.2

theorem psl2_factor
    {Q R S C X : Subgroup A} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p)
    (e : ↥Q ≃* PSL2 K) (hSQ : IsSylowTwoOf (S ⊓ Q) Q) (hRQ : R ≤ Q) (eR : ↥R ≃* L24)
    (hSR : IsSylowTwoOf (S ⊓ R) R) (hCQ : C ≤ Q) (hCc : IsCyclic ↥C) (hCo : Odd (Nat.card C))
    (hperm : ∀ t ∈ S ⊓ Q, ∀ x ∈ C, ∃ x' ∈ C, ∃ t' ∈ S ⊓ Q, t * x = x' * t')
    (hX : X ≤ R ⊓ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A)) (hX3 : Nat.card X = 3)
    (hXC : X ≤ Subgroup.normalizer (C : Set A)) :
    C ≤ R ⊓ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, hPu, -⟩ := psl2_card_four_mul hp hK hp8
  have hQc : Nat.card ↥Q = 4 * u := by rw [Nat.card_congr e.toEquiv, hPu]
  have h4Q : Nat.card ↥(S ⊓ Q) ≤ 4 := by
    have := card_le_four_of_isPGroup hu hQc ((S ⊓ Q).subgroupOf Q) hSQ.2.1.comap_subtype
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSQ.1).toEquiv] at this
  have h4R : Nat.card ↥(S ⊓ R) = 4 := by
    have := CFSG.Walter.JT.card_sylow_of_psl24 eR (sylowOf hSR)
    rwa [coe_sylowOf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR.1).toEquiv] at this
  have hSRQ : S ⊓ R = S ⊓ Q :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_left S hRQ) (by rw [h4R]; exact h4Q)
  rw [hSRQ] at hX ⊢
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hX3])
  have hbX := hX b.2
  exact psl2_img_le hK hp8 hp11 e hSQ hCQ hCc hCo hperm hRQ eR (hSRQ ▸ inf_le_right)
    (Subgroup.mem_inf.mp hbX).1 (by rw [Subgroup.orderOf_coe, hb3]) (hXC b.2)
    (Subgroup.mem_inf.mp hbX).2

end CFSG.Quasithin.H13.NQCat.C2
