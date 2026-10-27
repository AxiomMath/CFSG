module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126e
public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P F126 Equiv
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Star

variable {H : Subgroup G}

theorem isSolvable_ker_mk : Group.IsSolvable ↥(QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
  rw [QuotientGroup.ker_mk']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
  infer_instance

theorem star_mem_cComp {K : Subgroup G} (hK : K ∈ cComp H) :
    S126.star H K ∈ cComp (⊤ : Subgroup (S126.HStar H)) :=
  map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) isSolvable_ker_mk (subgroupOf_mem_cComp hK)

theorem star_injOn {K K' : Subgroup G} (hK : K ∈ cComp H) (hK' : K' ∈ cComp H)
    (h : S126.star H K = S126.star H K') : K = K' := by
  have h1 := map_injOn_cComp_top _ isSolvable_ker_mk (subgroupOf_mem_cComp hK)
    (subgroupOf_mem_cComp hK') h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left (le_of_mem_cComp hK),
    inf_of_le_left (le_of_mem_cComp hK')] at h1
  exact h1

theorem isComponent_star {K : Subgroup G} (hK : K ∈ cComp H)
    (hs : IsSimpleGroup ↥(S126.star H K)) : CFSG.IsComponent (S126.star H K) := by
  have hL := star_mem_cComp hK
  have hnonab : ∃ a b : ↥(S126.star H K), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    exact not_isSolvable_of_mem_cComp hL (Group.isSolvable_of_comm hcomm)
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1,
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)⟩

theorem commute_star {K K' : Subgroup G} (hK : K ∈ cComp H) (hK' : K' ∈ cComp H)
    (hne : K ≠ K') (hs : IsSimpleGroup ↥(S126.star H K))
    (hs' : IsSimpleGroup ↥(S126.star H K')) :
    ∀ x ∈ S126.star H K, ∀ y ∈ S126.star H K', x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_star hK hs)
      (isComponent_star hK' hs') with h | h
  · exact absurd (star_injOn hK hK' h) hne
  · intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx
    exact (Subgroup.mem_centralizer_iff.1 h1 y hy).symm

omit [Finite G] in
theorem star_conjSub {X : Subgroup G} {g : G} (hg : g ∈ H) :
    S126.star H (conjSub g X) =
      (S126.star H X).map (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : S126.HStar H)).toMonoidHom := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (g : G)⁻¹ * z * g ∈ X := mem_conjSub.1 (Subgroup.mem_subgroupOf.1 hz)
    have hxH : (g : G)⁻¹ * z * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) z.2) hg
    refine ⟨QuotientGroup.mk ⟨_, hxH⟩, ⟨⟨_, hxH⟩, Subgroup.mem_subgroupOf.2 hz', rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hz : (g : G) * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg x.2) (H.inv_mem hg)
    refine ⟨⟨_, hz⟩, Subgroup.mem_subgroupOf.2 (mul_mem_conjSub (Subgroup.mem_subgroupOf.1 hx)), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

end Star

section Commute

universe u

variable {Q : Type u} [Group Q] [Finite Q]

omit [Finite Q] in
@[expose] def mulHom (A B : Subgroup Q) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ↥A × ↥B →* Q :=
  A.subtype.noncommCoprod B.subtype fun a b =>
    show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2

omit [Finite Q] in
theorem mulHom_apply (A B : Subgroup Q) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (p : ↥A × ↥B) :
    mulHom A B hc p = (p.1 : Q) * p.2 := rfl

omit [Finite Q] in
theorem mulHom_injective {A B : Subgroup Q} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) : Function.Injective (mulHom A B hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [MonoidHom.mem_ker, mulHom_apply] at hab
  have ha : (a : Q) = (b : Q)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have hm : (a : Q) ∈ A ⊓ B := ⟨a.2, by rw [ha]; exact B.inv_mem b.2⟩
  rw [hi, Subgroup.mem_bot] at hm
  have hb : (b : Q) = 1 := by rw [hm, one_mul] at hab; exact hab
  rw [Subgroup.mem_bot]
  exact Prod.ext (Subtype.ext hm) (Subtype.ext hb)

omit [Finite Q] in
theorem range_mulHom (A B : Subgroup Q) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (mulHom A B hc).range = A ⊔ B := by
  rw [mulHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

omit [Finite Q] in
theorem card_sup_of_commute {A B : Subgroup Q} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← range_mulHom A B hc, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofInjective _ (mulHom_injective hc hi))).symm

omit [Finite Q] in
theorem card_eq_card_map_mul {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (S : Subgroup X) :
    Nat.card S = Nat.card (S.map f) * Nat.card ↥(S ⊓ f.ker) := by
  let g : ↥S →* Y := f.comp S.subtype
  have hr : g.range = S.map f := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card g.ker = Nat.card ↥(S ⊓ f.ker) := by
    refine Nat.card_congr ⟨fun x => ⟨((x : ↥S) : X), (x : ↥S).2, x.2⟩,
      fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩, fun x => rfl, fun y => rfl⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hr, hk]

theorem exists_mul_of_le_sup {A B P : Subgroup Q} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) (hPAB : P ≤ A ⊔ B) (hP : Nat.card P = 9) (hA : ¬ 9 ∣ Nat.card A)
    (hB : ¬ 9 ∣ Nat.card B) : ∀ p ∈ P, ∃ a ∈ P ⊓ A, ∃ b ∈ P ⊓ B, p = a * b := by
  set μ := mulHom A B hc with hμ
  have hμi : Function.Injective μ := mulHom_injective hc hi
  set P' := P.comap μ with hP'
  have hPr : P'.map μ = P := by
    rw [hP', Subgroup.map_comap_eq, range_mulHom]
    exact inf_eq_right.2 hPAB
  have hP'9 : Nat.card P' = 9 := by
    rw [← hP, ← hPr, Subgroup.card_map_of_injective hμi]
  have hsmall : ∀ (Z : Type u) [Group Z] (f : ↥A × ↥B →* Z) (S : Subgroup Z),
      P'.map f ≤ S → ¬ 9 ∣ Nat.card S → 3 ≤ Nat.card ↥(P' ⊓ f.ker) := by
    intro Z _ f S hle h9
    have h1 := card_eq_card_map_mul f P'
    rw [hP'9] at h1
    have hd1 : Nat.card (P'.map f) ∣ 9 := ⟨_, h1⟩
    have hd2 : Nat.card (P'.map f) ∣ Nat.card S := Subgroup.card_dvd_of_le hle
    have h3 : Nat.card (P'.map f) ≤ 3 := by
      rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 (show Nat.card (P'.map f) ∣ 3 ^ 2
        from hd1) with ⟨k, hk, hk'⟩
      interval_cases k
      · rw [hk']; norm_num
      · rw [hk']; norm_num
      · exfalso
        rw [hk'] at hd2
        exact h9 (by simpa using hd2)
    have hpos : 0 < Nat.card ↥(P' ⊓ f.ker) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card (P'.map f) * Nat.card ↥(P' ⊓ f.ker) ≤ 3 * 2 :=
      Nat.mul_le_mul h3 (by omega)
    omega
  have hfst := hsmall ↥A (MonoidHom.fst _ _) ⊤ (le_top) (by rwa [Subgroup.card_top])
  have hsnd := hsmall ↥B (MonoidHom.snd _ _) ⊤ (le_top) (by rwa [Subgroup.card_top])
  set S₁ := (P' ⊓ (MonoidHom.snd ↥A ↥B).ker).map (MonoidHom.fst _ _) with hS₁
  set S₂ := (P' ⊓ (MonoidHom.fst ↥A ↥B).ker).map (MonoidHom.snd _ _) with hS₂
  have hc₁ : Nat.card S₁ = Nat.card ↥(P' ⊓ (MonoidHom.snd ↥A ↥B).ker) := by
    have h := card_eq_card_map_mul (MonoidHom.fst ↥A ↥B) (P' ⊓ (MonoidHom.snd ↥A ↥B).ker)
    have hb : P' ⊓ (MonoidHom.snd ↥A ↥B).ker ⊓ (MonoidHom.fst ↥A ↥B).ker = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨a, b⟩ ⟨⟨-, hb⟩, ha⟩
      exact Prod.ext ha hb
    rw [hb, Subgroup.card_bot, mul_one] at h
    exact h.symm
  have hc₂ : Nat.card S₂ = Nat.card ↥(P' ⊓ (MonoidHom.fst ↥A ↥B).ker) := by
    have h := card_eq_card_map_mul (MonoidHom.snd ↥A ↥B) (P' ⊓ (MonoidHom.fst ↥A ↥B).ker)
    have hb : P' ⊓ (MonoidHom.fst ↥A ↥B).ker ⊓ (MonoidHom.snd ↥A ↥B).ker = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨a, b⟩ ⟨⟨-, ha⟩, hb⟩
      exact Prod.ext ha hb
    rw [hb, Subgroup.card_bot, mul_one] at h
    exact h.symm
  have hprod : S₁.prod S₂ ≤ P' := by
    rintro ⟨a, b⟩ ⟨⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩, ⟨⟨a₂, b₂⟩, ⟨ha₂, hb₂⟩, rfl⟩⟩
    have hb₁' : b₁ = 1 := hb₁
    have ha₂' : a₂ = 1 := hb₂
    have : ((a₁, b₁) * (a₂, b₂) : ↥A × ↥B) = (a₁, b₂) := by
      rw [Prod.mk_mul_mk, hb₁', ha₂', one_mul, mul_one]
    show (a₁, b₂) ∈ P'
    rw [← this]
    exact P'.mul_mem ha₁ ha₂
  have hcardprod : Nat.card ↥(S₁.prod S₂) = Nat.card S₁ * Nat.card S₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv S₁ S₂).toEquiv, Nat.card_prod]
  have heq : S₁.prod S₂ = P' := Subgroup.eq_of_le_of_card_ge hprod (by
    rw [hcardprod, hc₁, hc₂, hP'9]
    calc 9 = 3 * 3 := rfl
      _ ≤ _ := Nat.mul_le_mul hsnd hfst)
  intro p hp
  rw [← hPr] at hp
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
  rw [← heq] at hx
  obtain ⟨⟨y, ⟨hyP, hy2⟩, hy1⟩, ⟨z, ⟨hzP, hz1⟩, hz2⟩⟩ := hx
  have hy2' : y.2 = 1 := hy2
  have hz1' : z.1 = 1 := hz1
  have hy : y = (x.1, 1) := Prod.ext hy1 hy2'
  have hz : z = (1, x.2) := Prod.ext hz1' hz2
  refine ⟨(x.1 : Q), ⟨?_, x.1.2⟩, (x.2 : Q), ⟨?_, x.2.2⟩, rfl⟩
  · have h1 : μ y ∈ P := hyP
    rw [hy, hμ, mulHom_apply] at h1
    simpa using h1
  · have h1 : μ z ∈ P := hzP
    rw [hz, hμ, mulHom_apply] at h1
    simpa using h1

end Commute

end CFSG.Quasithin.H13.L1233
