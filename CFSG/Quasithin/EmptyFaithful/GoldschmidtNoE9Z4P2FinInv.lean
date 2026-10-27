module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.E9P2.FinInv

open CFSG.QuasithinUnique Subgroup

section Basic

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_pow_three {U : Subgroup G} (hU : IsPGroup 2 U) {x : G} (hx : x ∈ U)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have hd : 2 ^ k ∣ 3 := hk ▸ orderOf_dvd_of_pow_eq_one h3
  have hk0 : k = 0 := by
    by_contra hne
    exact absurd ((dvd_pow_self 2 hne).trans hd) (by decide)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem isSylowTwoOf_top_of_sylow [Finite G] (P : Sylow 2 G) : IsSylowTwoOf (P : Subgroup G) ⊤ :=
  ⟨le_top, P.isPGroup', by
    rw [show ((P : Subgroup G).subgroupOf ⊤).index = (P : Subgroup G).index from
      Subgroup.relIndex_top_right _]
    exact P.not_dvd_index⟩

theorem normalizer_eq_of_conj {U U₀ : Subgroup G} (g : G)
    (hU : U = U₀.map (MulAut.conj g).toMonoidHom) (h0 : normalizer (U₀ : Set G) = U₀) :
    normalizer (U : Set G) = U := by
  subst hU
  rw [← Subgroup.map_equiv_normalizer_eq, h0]

theorem normalizer_eq_of_isSylowTwoOf [Finite G] {U U₀ : Subgroup G} (hU : IsSylowTwoOf U ⊤)
    (hU₀ : IsSylowTwoOf U₀ ⊤) (h0 : normalizer (U₀ : Set G) = U₀) :
    normalizer (U : Set G) = U := by
  obtain ⟨g, -, hg⟩ := hU₀.exists_conj hU
  exact normalizer_eq_of_conj g hg h0

theorem eq_one_of_mem_normalizer_of_pow_three {U : Subgroup G} (hU : IsPGroup 2 U)
    (hN : normalizer (U : Set G) = U) {x : G} (hx : x ∈ normalizer (U : Set G)) (h3 : x ^ 3 = 1) :
    x = 1 :=
  eq_one_of_mem_of_pow_three hU (hN ▸ hx) h3

end Basic

section Prod

variable {A B : Type*} [Group A] [Group B]

theorem isPGroup_prod {H : Subgroup A} {K : Subgroup B} (hH : IsPGroup 2 H) (hK : IsPGroup 2 K) :
    IsPGroup 2 (H.prod K) := by
  intro x
  obtain ⟨i, hi⟩ := hH ⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩
  obtain ⟨j, hj⟩ := hK ⟨x.1.2, (Subgroup.mem_prod.1 x.2).2⟩
  have hi' : x.1.1 ^ 2 ^ i = 1 := congrArg Subtype.val hi
  have hj' : x.1.2 ^ 2 ^ j = 1 := congrArg Subtype.val hj
  refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change x.1.1 ^ 2 ^ (i + j) = 1
    rw [pow_add, pow_mul, hi', one_pow]
  · change x.1.2 ^ 2 ^ (i + j) = 1
    rw [add_comm, pow_add, pow_mul, hj', one_pow]

theorem card_prod (H : Subgroup A) (K : Subgroup B) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

theorem isSylowTwoOf_map_fst {U : Subgroup (A × B)} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map (MonoidHom.fst A B)) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  rw [show ((U.map (MonoidHom.fst A B)).subgroupOf ⊤).index = (U.map (MonoidHom.fst A B)).index from
    Subgroup.relIndex_top_right _]
  have hU' : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  exact fun h => hU' (h.trans (Subgroup.index_map_dvd U (fun a => ⟨(a, 1), rfl⟩)))

theorem isSylowTwoOf_map_snd {U : Subgroup (A × B)} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map (MonoidHom.snd A B)) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  rw [show ((U.map (MonoidHom.snd A B)).subgroupOf ⊤).index = (U.map (MonoidHom.snd A B)).index from
    Subgroup.relIndex_top_right _]
  have hU' : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  exact fun h => hU' (h.trans (Subgroup.index_map_dvd U (fun b => ⟨(1, b), rfl⟩)))

theorem eq_prod_map [Finite A] [Finite B] {U : Subgroup (A × B)} (hU : IsSylowTwoOf U ⊤) :
    U = (U.map (MonoidHom.fst A B)).prod (U.map (MonoidHom.snd A B)) := by
  have hle : U ≤ (U.map (MonoidHom.fst A B)).prod (U.map (MonoidHom.snd A B)) := fun x hx =>
    Subgroup.mem_prod.2 ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  exact (hU.eq_of_le hle le_top
    (isPGroup_prod (isSylowTwoOf_map_fst hU).isPGroup (isSylowTwoOf_map_snd hU).isPGroup)).symm

theorem closure_involutions_prod {H : Subgroup A} {K : Subgroup B}
    (hH : closure {x | x ∈ H ∧ x * x = 1} = H) (hK : closure {x | x ∈ K ∧ x * x = 1} = K) :
    closure {x : A × B | x ∈ H.prod K ∧ x * x = 1} = H.prod K := by
  refine le_antisymm ((closure_le _).2 fun x hx => hx.1) ?_
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
  have h1 : ((a, 1) : A × B) ∈ closure {x : A × B | x ∈ H.prod K ∧ x * x = 1} := by
    rw [← hH] at ha
    refine Subgroup.closure_induction (p := fun y _ =>
      ((y, 1) : A × B) ∈ closure {x : A × B | x ∈ H.prod K ∧ x * x = 1}) ?_ ?_ ?_ ?_ ha
    · intro y hy
      exact subset_closure ⟨Subgroup.mem_prod.2 ⟨hy.1, one_mem _⟩, by simp [hy.2]⟩
    · exact one_mem _
    · intro y z _ _ hy hz
      simpa using mul_mem hy hz
    · intro y _ hy
      simpa using inv_mem hy
  have h2 : ((1, b) : A × B) ∈ closure {x : A × B | x ∈ H.prod K ∧ x * x = 1} := by
    rw [← hK] at hb
    refine Subgroup.closure_induction (p := fun y _ =>
      ((1, y) : A × B) ∈ closure {x : A × B | x ∈ H.prod K ∧ x * x = 1}) ?_ ?_ ?_ ?_ hb
    · intro y hy
      exact subset_closure ⟨Subgroup.mem_prod.2 ⟨one_mem _, hy.1⟩, by simp [hy.2]⟩
    · exact one_mem _
    · intro y z _ _ hy hz
      simpa using mul_mem hy hz
    · intro y _ hy
      simpa using inv_mem hy
  simpa using mul_mem h1 h2

theorem mem_normalizer_prod {H : Subgroup A} {K : Subgroup B} {x : A × B}
    (hx : x ∈ normalizer ((H.prod K : Subgroup (A × B)) : Set (A × B))) :
    x.1 ∈ normalizer (H : Set A) ∧ x.2 ∈ normalizer (K : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at hx
  refine ⟨Subgroup.mem_normalizer_iff.2 fun h => ?_, Subgroup.mem_normalizer_iff.2 fun h => ?_⟩
  · simpa [Subgroup.mem_prod] using hx (h, 1)
  · simpa [Subgroup.mem_prod] using hx (1, h)

theorem eq_one_of_mem_normalizer_prod {H : Subgroup A} {K : Subgroup B} (hH : IsPGroup 2 H)
    (hK : IsPGroup 2 K) (hNH : normalizer (H : Set A) = H) (hNK : normalizer (K : Set B) = K)
    {x : A × B} (hx : x ∈ normalizer ((H.prod K : Subgroup (A × B)) : Set (A × B)))
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨h1, h2⟩ := mem_normalizer_prod hx
  exact Prod.ext (eq_one_of_mem_normalizer_of_pow_three hH hNH h1 (congrArg Prod.fst h3))
    (eq_one_of_mem_normalizer_of_pow_three hK hNK h2 (congrArg Prod.snd h3))

end Prod

section Commute

theorem exists_ne_one_map_eq_one {E C : Type*} [Group E] [Group C] (f : E →* C)
    (hE : Nat.card E = 9) (hC : ¬ 9 ∣ Nat.card C) : ∃ x : E, x ≠ 1 ∧ f x = 1 := by
  by_contra hne
  have hinj : Function.Injective f := (injective_iff_map_eq_one f).2 fun x hx => by
    by_contra h
    exact hne ⟨x, h, hx⟩
  exact hC (hE ▸ Subgroup.card_dvd_of_injective f hinj)

variable {A B : Type*} [Group A] [Group B]

theorem eq_one_of_commute_prod
    (hA : ¬ 9 ∣ Nat.card A) (hB : ¬ 9 ∣ Nat.card B)
    (cA : ∀ a z : A, a ≠ 1 → a ^ 3 = 1 → z * z = 1 → z * a = a * z → z = 1)
    (cB : ∀ b z : B, b ≠ 1 → b ^ 3 = 1 → z * z = 1 → z * b = b * z → z = 1)
    {E : Subgroup (A × B)} (hE9 : Nat.card E = 9) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    {z : A × B} (hz : z * z = 1) (hc : ∀ e ∈ E, z * e = e * z) : z = 1 := by
  obtain ⟨x, hx1, hx⟩ := exists_ne_one_map_eq_one ((MonoidHom.snd A B).comp E.subtype) hE9 hB
  obtain ⟨y, hy1, hy⟩ := exists_ne_one_map_eq_one ((MonoidHom.fst A B).comp E.subtype) hE9 hA
  have hx2 : (x : A × B).2 = 1 := hx
  have hy2 : (y : A × B).1 = 1 := hy
  have hxa : (x : A × B).1 ≠ 1 := fun h => hx1 (Subtype.ext (Prod.ext h hx2))
  have hyb : (y : A × B).2 ≠ 1 := fun h => hy1 (Subtype.ext (Prod.ext hy2 h))
  have hz1 : z.1 * z.1 = 1 := congrArg Prod.fst hz
  have hz2 : z.2 * z.2 = 1 := congrArg Prod.snd hz
  refine Prod.ext (cA _ _ hxa (congrArg Prod.fst (hE3 x x.2)) hz1
    (congrArg Prod.fst (hc x x.2))) (cB _ _ hyb (congrArg Prod.snd (hE3 y y.2)) hz2
    (congrArg Prod.snd (hc y y.2)))

end Commute

end CFSG.Quasithin.E9P2.FinInv
