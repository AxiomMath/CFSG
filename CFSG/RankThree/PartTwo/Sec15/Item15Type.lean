module

public import CFSG.RankThree.PartTwo.KFacts.KS15Basic

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace CFSG.RankThree.PartTwo.Sec15

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

theorem pCore_two_le_pPrimeCore_three : CFSG.pCore 2 Y ≤ CFSG.pPrimeCore 3 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨CFSG.pCore_normal (p := 2) (G := Y), ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := Y))
  rw [hn]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem pPrimeCore_three_eq_pCore_two
    (h : CFSG.pPrimeCore 3 (Y ⧸ CFSG.pCore 2 Y) = ⊥) :
    CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y := by
  refine le_antisymm ?_ pCore_two_le_pPrimeCore_three
  have hN : ((CFSG.pPrimeCore 3 Y).map (QuotientGroup.mk' (CFSG.pCore 2 Y))).Normal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := Y)).map _ (QuotientGroup.mk'_surjective _)
  have hcop : Nat.Coprime 3
      (Nat.card ((CFSG.pPrimeCore 3 Y).map (QuotientGroup.mk' (CFSG.pCore 2 Y)))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := Y))
  have hle : (CFSG.pPrimeCore 3 Y).map (QuotientGroup.mk' (CFSG.pCore 2 Y)) ≤
      CFSG.pPrimeCore 3 (Y ⧸ CFSG.pCore 2 Y) := le_sSup ⟨hN, hcop⟩
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
  exact hle

theorem pPrimeCore_three_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsSimpleGroup Q) (h3 : 3 ∣ Nat.card Q) : CFSG.pPrimeCore 3 Q = ⊥ := by
  rcases (CFSG.pPrimeCore_normal (p := 3) (G := Q)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := Q)
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc h3

end Generic

section Image

variable {G : Type} [Group G]

theorem nonempty_img148_equiv {A Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    letI := ker148_normal hY
    Nonempty (↥(img148 A Y Y) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
  let := ker148_normal hY
  let φ : ↥Y →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion le_sup_left)
  have hrange : φ.range = img148 A Y Y := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : φ.ker = CFSG.pPrimeCore 3 ↥Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (ker148 A Y) (Subgroup.inclusion le_sup_left y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker148, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion, pPrimeCoreOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange) |>.symm⟩

end Image

section Simple

variable {K : Type*} [Group K]

theorem center_eq_bot_of_isSimpleGroup (hK : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    Subgroup.center K = ⊥ := by
  rcases (inferInstance : (Subgroup.center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem not_isTripleCover_of_isSimpleGroup (hK : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {Y : Type*} [Group Y] : ¬ Sec4.IsTripleCover K Y := by
  rintro ⟨h3, -⟩
  rw [center_eq_bot_of_isSimpleGroup hK hnab, Subgroup.card_bot] at h3
  norm_num at h3

theorem isEmpty_mulEquiv_prod_of_isSimpleGroup (hK : IsSimpleGroup K) {H₁ H₂ : Type*}
    [Group H₁] [Group H₂] [Nontrivial H₁] [Nontrivial H₂] : IsEmpty (K ≃* H₁ × H₂) := by
  refine ⟨fun e => ?_⟩
  let f : K →* H₁ := (MonoidHom.fst H₁ H₂).comp e.toMonoidHom
  have hf : Function.Surjective f := fun h => ⟨e.symm (h, 1), by simp [f]⟩
  rcases f.normal_ker.eq_bot_or_eq_top with h | h
  · obtain ⟨y, hy⟩ := exists_ne (1 : H₂)
    have hmem : e.symm (1, y) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp [f]
    rw [h, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hmem
    exact hy (congrArg Prod.snd hmem)
  · obtain ⟨x, hx⟩ := exists_ne (1 : H₁)
    obtain ⟨k, rfl⟩ := hf x
    exact hx ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top k))

theorem isEmpty_mulEquiv_prod_of_isSimpleGroup' (hK : IsSimpleGroup K) {H₁ H₂ : Type*}
    [Group H₁] [Group H₂] [Nontrivial H₁] (hne : IsEmpty (K ≃* H₁)) :
    IsEmpty (K ≃* H₁ × H₂) := by
  refine ⟨fun e => ?_⟩
  let f : K →* H₁ := (MonoidHom.fst H₁ H₂).comp e.toMonoidHom
  have hf : Function.Surjective f := fun h => ⟨e.symm (h, 1), by simp [f]⟩
  rcases f.normal_ker.eq_bot_or_eq_top with h | h
  · exact hne.false (MulEquiv.ofBijective f
      ⟨(MonoidHom.ker_eq_bot_iff f).mp h, hf⟩)
  · obtain ⟨x, hx⟩ := exists_ne (1 : H₁)
    obtain ⟨k, rfl⟩ := hf x
    exact hx ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top k))

theorem not_isCentralProductA6Covers_of_isSimpleGroup (hK : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : ¬ IsCentralProductA6Covers K := by
  rintro ⟨U, V, hU, hV, -, -, h3, hU6, hV6⟩
  have hne : ∀ W : Subgroup K, Sec4.IsTripleCover ↥W (alternatingGroup (Fin 6)) → W ≠ ⊥ := by
    rintro W ⟨hW3, -⟩ rfl
    have hle : Nat.card (Subgroup.center (⊥ : Subgroup K)) ≤ 1 := by
      rw [← Nat.card_unique (α := (⊥ : Subgroup K))]
      exact Subgroup.card_le_card_group _
    omega
  have hUt := (hU.eq_bot_or_eq_top).resolve_left (hne U hU6)
  have hVt := (hV.eq_bot_or_eq_top).resolve_left (hne V hV6)
  rw [hUt, hVt, inf_top_eq, Subgroup.card_top] at h3
  obtain ⟨a, b, hab⟩ := hnab
  have : IsCyclic K := isCyclic_of_prime_card (p := 3) (hp := ⟨Nat.prime_three⟩) h3
  exact hab (IsCyclic.commGroup.mul_comm a b)

theorem not_isA6CoverTimesA5_of_isSimpleGroup (hK : IsSimpleGroup K) : ¬ IsA6CoverTimesA5 K := by
  rintro ⟨U, V, hU, hV, hUV, -, ⟨hU3, -⟩, ⟨eV⟩⟩
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    have hle : Nat.card (Subgroup.center (⊥ : Subgroup K)) ≤ 1 := by
      rw [← Nat.card_unique (α := (⊥ : Subgroup K))]
      exact Subgroup.card_le_card_group _
    omega
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    have := eV.symm.injective.nontrivial
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  rw [(hU.eq_bot_or_eq_top).resolve_left hU1, (hV.eq_bot_or_eq_top).resolve_left hV1,
    inf_top_eq] at hUV
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  exact hx ((Subgroup.mem_bot).mp (hUV ▸ Subgroup.mem_top x))

end Simple


section Img

variable {G : Type} [Group G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_eq_bot_of_le {X : Subgroup G} (hX : X ≤ pPrimeCoreOf 3 Y) :
    img148 A Y X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (hX (Subgroup.mem_subgroupOf.mp hx))

theorem img148_sup {X X' : Subgroup G} (hX : X ≤ Y ⊔ A) (hX' : X' ≤ Y ⊔ A) :
    img148 A Y (X ⊔ X') = img148 A Y X ⊔ img148 A Y X' := by
  unfold img148
  rw [← Subgroup.map_sup]
  congr 1
  apply Subgroup.map_injective (Y ⊔ A).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX, inf_eq_left.mpr hX',
    inf_eq_left.mpr (sup_le hX hX')]

theorem img148_comm (hAab : IsMulCommutative A) (x y : ↥(img148 A Y A)) : x * y = y * x := by
  obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
  obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
  apply Subtype.ext
  change QuotientGroup.mk' _ a * QuotientGroup.mk' _ b =
    QuotientGroup.mk' _ b * QuotientGroup.mk' _ a
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (show (a : G) * b = b * a from congrArg Subtype.val
    (hAab.is_comm.comm ⟨a, Subgroup.mem_subgroupOf.mp ha⟩ ⟨b, Subgroup.mem_subgroupOf.mp hb⟩))

end Img

section Transport

theorem IsLThreeEpsAt.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p f : ℕ}
    [Fact p.Prime] (h : IsLThreeEpsAt X p f) : IsLThreeEpsAt X' p f := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl ⟨e.symm.trans φ⟩
  · exact Or.inr ⟨hq, ⟨e.symm.trans φ⟩⟩

theorem isLThreeEpsAt_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hq : 2 < p ^ e) (h : Sec4.IsoLThreePi X p e) : IsLThreeEpsAt X p e := by
  rcases h with ⟨-, φ⟩ | ⟨-, φ⟩
  · exact Or.inl φ
  · exact Or.inr ⟨hq, φ⟩

end Transport


section Case148

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem exists_lA_of_isSimpleGroup_img148 (h148 : Item148 A LB) {Y : Subgroup G}
    (hY : Y ∈ scriptY A) (hAab : IsMulCommutative A) (hPGL : KFacts.KS15Z3PGLNonabelian)
    {K : Type} [Group K] (hKs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (he : letI := ker148_normal hY.2
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* K))
    (hA5 : IsEmpty (K ≃* alternatingGroup (Fin 5)))
    (hA7 : IsEmpty (K ≃* alternatingGroup (Fin 7)))
    (hA10 : IsEmpty (K ≃* alternatingGroup (Fin 10)))
    (hL3 : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt K p f) :
    ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      ∃ L' ∈ lA A c', Nonempty (K ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') := by
  let := ker148_normal hY.2
  obtain ⟨e⟩ := he
  set X := img148 A Y (deltaZero A LB Y) with hX
  have hXs : IsSimpleGroup ↥X := e.isSimpleGroup
  have hXnab : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hXnt : Nontrivial ↥X := hXs.toNontrivial
  rcases (h148 Y hY).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hX1 : X = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hX1 ▸ x.2)))
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e', hp, -, -, -, hL3'⟩ | ⟨-, h3A6 | hφ⟩
    · obtain ⟨φ⟩ := hφ
      exact ⟨c', hc', L', hL', ⟨e.symm.trans φ⟩⟩
    · obtain ⟨φ⟩ := hφ
      exact (hA7.false (e.symm.trans φ)).elim
    · exact (hL3 p f (IsLThreeEpsAt.of_mulEquiv e hL3')).elim
    · exact (not_isTripleCover_of_isSimpleGroup hXs hXnab h3A6).elim
    · obtain ⟨φ⟩ := hφ
      exact (hA5.false (e.symm.trans φ)).elim
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := h3
    rcases h with hON | hCP | hA6A5 | hφ | hφ | ⟨_, hφ⟩
    · exact not_isTripleCover_of_isSimpleGroup hXs hXnab hON
    · exact not_isCentralProductA6Covers_of_isSimpleGroup hXs hXnab hCP
    · exact not_isA6CoverTimesA5_of_isSimpleGroup hXs hA6A5
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_prod_of_isSimpleGroup hXs).false φ
    · obtain ⟨φ⟩ := hφ
      exact hA7.false (e.symm.trans φ)
    · obtain ⟨φ⟩ := hφ
      exact hL3 7 1 (Or.inl ⟨e.symm.trans φ⟩)
  ·
    obtain ⟨hφ, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact (hA10.false (e.symm.trans φ)).elim
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have hq : 2 < 2 ^ (3 * n) := by
      calc 2 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (hL3 2 (3 * n) (IsLThreeEpsAt.of_mulEquiv e (isLThreeEpsAt_of_isoLThreePi hq hiso))).elim
  ·
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact ((isEmpty_mulEquiv_prod_of_isSimpleGroup' hXs
      ⟨fun ψ => hA5.false (e.symm.trans ψ)⟩).false φ).elim
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    rw [← hX] at hsup
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hN : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      refine sup_le Subgroup.le_normalizer ?_
      have hC : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hcomm
      exact hC.trans (Subgroup.centralizer_le_normalizer _)
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases hN.eq_bot_or_eq_top with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_top] at h
        have := le_inf (hJ₂le.trans h) le_rfl
        rwa [hinf, le_bot_iff] at this
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := hPGL _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂
end Case148

end CFSG.RankThree.PartTwo.Sec15
