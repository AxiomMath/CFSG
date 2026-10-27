module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

variable (p : ℕ) (G : Type*) [Group G]

section pPrimeCore_properties

variable {G} {p}

lemma CFSG.normalPPrimeSubgroups_nonempty : (normalPPrimeSubgroups p G).Nonempty := by
  refine ⟨⊥, ?_⟩
  constructor
  · infer_instance
  · simp

lemma CFSG.directedOn_normal_pPrimeSubgroups :
    DirectedOn (· ≤ ·) (normalPPrimeSubgroups p G) := by
  classical
  intro A hA B hB
  rcases hA with ⟨hA_normal, hA_coprime⟩
  rcases hB with ⟨hB_normal, hB_coprime⟩
  refine ⟨A ⊔ B, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · have : A.Normal := hA_normal
    have : B.Normal := hB_normal
    exact Subgroup.sup_normal A B
  · -- Show `Nat.Coprime p (Nat.card (A ⊔ B))` using the cardinality formula for `A ⊔ B = A * B`.
    have : B.Normal := hB_normal
    have hmul : (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) := by
      simpa using (Subgroup.mul_normal A B)
    have hcard_sup_set :
        Nat.card (↑(A ⊔ B) : Set G) = Nat.card ((A : Set G) * (B : Set G) : Set G) :=
      Nat.card_congr (Set.equivOfEq hmul)
    have hcard_sup : Nat.card (↥(A ⊔ B)) = Nat.card ((A : Set G) * (B : Set G) : Set G) := by
      simpa using hcard_sup_set
    have hcard_mul :
        Nat.card ((A : Set G) * (B : Set G) : Set G) =
          Nat.card B * Nat.card ((A : Set G).image (↑) : Set (G ⧸ B)) := by
      simpa using
        (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := B) (t := (A : Set G)))
    have hset_image :
        ((A : Set G).image (↑) : Set (G ⧸ B)) =
          (A.map (QuotientGroup.mk' B) : Set (G ⧸ B)) := by
      -- `Subgroup.coe_map` and `QuotientGroup.coe_mk'` identify the set image with the subgroup map.
      simp [Subgroup.coe_map]
    have hcard_image_set :
        Nat.card ((A : Set G).image (↑) : Set (G ⧸ B)) =
          Nat.card (A.map (QuotientGroup.mk' B) : Set (G ⧸ B)) :=
      Nat.card_congr (Set.equivOfEq hset_image)
    have hcard_image_subgroup :
        Nat.card ((A : Set G).image (↑) : Set (G ⧸ B)) = Nat.card (A.map (QuotientGroup.mk' B)) := by
      have hcard_coe :
          Nat.card (A.map (QuotientGroup.mk' B) : Set (G ⧸ B)) =
            Nat.card (A.map (QuotientGroup.mk' B)) := rfl
      exact hcard_image_set.trans hcard_coe
    have hcard_image_dvd :
        Nat.card (A.map (QuotientGroup.mk' B)) ∣ Nat.card A :=
      Subgroup.card_map_dvd (H := A) (QuotientGroup.mk' B)
    have hcoprime_image :
        Nat.Coprime p (Nat.card ((A : Set G).image (↑) : Set (G ⧸ B))) := by
      have : Nat.Coprime p (Nat.card (A.map (QuotientGroup.mk' B))) :=
        Nat.Coprime.of_dvd_right hcard_image_dvd hA_coprime
      simpa [hcard_image_subgroup] using this
    have hcoprime_prod :
        Nat.Coprime p (Nat.card B * Nat.card ((A : Set G).image (↑) : Set (G ⧸ B))) :=
      Nat.Coprime.mul_right hB_coprime hcoprime_image
    have hcoprime_mul : Nat.Coprime p (Nat.card ((A : Set G) * (B : Set G) : Set G)) := by
      simpa [hcard_mul] using hcoprime_prod
    -- Rewrite along `hcard_sup` to finish.
    -- `Nat.card (A ⊔ B)` means `Nat.card ↥(A ⊔ B)`.
    simpa using (show Nat.Coprime p (Nat.card (↥(A ⊔ B))) by
      rw [hcard_sup]
      exact hcoprime_mul)

public theorem CFSG.pPrimeCore_eq_bot_iff : pPrimeCore p G = ⊥ ↔ ∀ (K : Subgroup G), K.Normal → Nat.Coprime p (Nat.card K) → K = ⊥ := by
  constructor
  · intro h K hK_normal hK_coprime
    exact (sSup_eq_bot.mp h) K ⟨hK_normal, hK_coprime⟩
  · intro h
    rw [pPrimeCore, sSup_eq_bot]
    intro K ⟨hK_normal, hK_coprime⟩
    exact h K hK_normal hK_coprime

/-- The `p'`-core is preserved under group isomorphisms. -/
public theorem CFSG.pPrimeCore_map_iso {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G ≃* G') : (pPrimeCore p G).map f.toMonoidHom = pPrimeCore p G' := by
  -- Let S be the set of normal subgroups of G with order coprime to p
  let S : Set (Subgroup G) := {K | K.Normal ∧ Nat.Coprime p (Nat.card K)}
  let S' : Set (Subgroup G') := {K' | K'.Normal ∧ Nat.Coprime p (Nat.card K')}
  -- The order isomorphism induced by f on subgroup lattices
  let F : Subgroup G ≃o Subgroup G' := MulEquiv.mapSubgroup f
  -- Show that F maps S to S' bijectively
  have h_image : F '' S = S' := by
    ext K'
    constructor
    · rintro ⟨K, ⟨hK_normal, hK_coprime⟩, h⟩
      have : F K = K.map f.toMonoidHom := rfl
      rw [this] at h
      subst h
      constructor
      · -- K.map f is normal because f is surjective
        exact Subgroup.Normal.map hK_normal f.toMonoidHom f.surjective
      · -- Cardinality preserved under isomorphism
        have : K ≃* K.map f.toMonoidHom := MulEquiv.subgroupMap f K
        have hcard : Nat.card K = Nat.card (K.map f.toMonoidHom) :=
          Nat.card_congr this.toEquiv
        rwa [← hcard]
    · intro ⟨hK'_normal, hK'_coprime⟩
      -- The preimage under F.symm = map f.symm
      have h_symm_normal : (F.symm K').Normal := by
        dsimp [F]
        exact Subgroup.Normal.map hK'_normal f.symm.toMonoidHom f.symm.surjective
      have h_symm_coprime : Nat.Coprime p (Nat.card (F.symm K')) := by
        have : F.symm K' ≃* K' := (MulEquiv.subgroupMap f.symm K').symm
        have hcard : Nat.card (F.symm K') = Nat.card K' := Nat.card_congr this.toEquiv
        rw [hcard]
        exact hK'_coprime
      refine ⟨F.symm K', ⟨h_symm_normal, h_symm_coprime⟩, ?_⟩
      simp [F, Subgroup.map_map]
  -- Now compute using OrderIso.map_sSup
  calc
    (pPrimeCore p G).map f.toMonoidHom = (sSup S).map f.toMonoidHom := rfl
    _ = F (sSup S) := rfl
    _ = ⨆ K ∈ S, F K := OrderIso.map_sSup F S
    _ = sSup (F '' S) := by simp [sSup_image]
    _ = sSup S' := by rw [h_image]
    _ = pPrimeCore p G' := rfl

/-- The `p'`-core is characteristic. -/
public instance CFSG.pPrimeCore_characteristic : (pPrimeCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  simpa using (pPrimeCore_map_iso (G := G) (G' := G) (p := p) (f := φ))


/-- The `p'`-core is normal. -/
@[instance]
public theorem CFSG.pPrimeCore_normal : (pPrimeCore p G).Normal := by
  classical
  refine ⟨?_⟩
  intro n hn g
  dsimp [pPrimeCore] at hn
  have hdir := directedOn_normal_pPrimeSubgroups (G := G) (p := p)
  have hne := normalPPrimeSubgroups_nonempty (G := G) (p := p)
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hn) with ⟨K, hK, hnK⟩
  exact Subgroup.mem_sSup_of_mem hK (hK.1.conj_mem n hnK g)

variable [Finite G] [Fact p.Prime]

/-- The order of the `p'`-core is coprime to `p`. -/
public theorem CFSG.pPrimeCore_coprime_card : Nat.Coprime p (Nat.card (pPrimeCore p G)) := by
  classical
  have hp : Nat.Prime p := Fact.out
  refine (hp.coprime_iff_not_dvd).2 ?_
  intro hpdvd
  have : Fintype (pPrimeCore p G) := Fintype.ofFinite (pPrimeCore p G)
  have hpdvd' : p ∣ Fintype.card (pPrimeCore p G) := by
    simpa [Nat.card_eq_fintype_card] using hpdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := pPrimeCore p G) p hpdvd'
  have hxmem : (x : G) ∈ pPrimeCore p G := x.property
  have hxmem' :
      (x : G) ∈ sSup {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} := by
    exact hxmem
  have hdir := directedOn_normal_pPrimeSubgroups (G := G) (p := p)
  have hne := normalPPrimeSubgroups_nonempty (G := G) (p := p)
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hxmem') with ⟨K, hK, hxK⟩
  have hp_dvd : p ∣ Nat.card K := by
    have horder_dvd : orderOf (x : G) ∣ Nat.card K :=
      Subgroup.orderOf_dvd_natCard K hxK
    have horder : orderOf (x : G) = p := by
      simpa [Subgroup.orderOf_coe] using hx
    simpa [horder] using horder_dvd
  have hnot : ¬ p ∣ Nat.card K := (hp.coprime_iff_not_dvd).1 hK.2
  exact (hnot hp_dvd).elim

lemma CFSG.coprime_prime_pow_of_ne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) (n : ℕ) :
    Nat.Coprime p (q ^ n) := (Nat.coprime_primes hp hq).mpr hne |>.pow_right n

lemma CFSG.exists_prime_dvd_ne_of_not_prime_power {m p : ℕ} (hm0 : m ≠ 0)
    (hm_not : ∀ n, m ≠ p ^ n) : ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := by
  by_contra! h
  have h' : ∀ {d}, Nat.Prime d → d ∣ m → d = p := by
    intro d hprime hdvd
    exact h d hprime hdvd
  apply hm_not (Nat.primeFactorsList m).length
  exact Nat.eq_prime_pow_of_unique_prime_dvd hm0 h'

public theorem CFSG.isPGroup_of_nilpotent_normal (N : Subgroup G) (hN_normal : N.Normal) (hN_nilpotent : Group.IsNilpotent (↥N))
    (hcore : pPrimeCore p G = ⊥) : IsPGroup p N := by
  by_contra h_not
  rw [IsPGroup.iff_card] at h_not
  have h_card_ne_zero : Nat.card (↥N) ≠ 0 := by
    have : Finite N := inferInstance
    have hpos : 0 < Nat.card (↥N) := by
      rw [Finite.card_pos_iff (α := ↥N)]
      exact ⟨⟨1, N.one_mem⟩⟩
    linarith
  have h_not' : ∀ n, Nat.card (↥N) ≠ p ^ n := by
    simpa using h_not
  have hp_prime : Nat.Prime p := Fact.out
  rcases exists_prime_dvd_ne_of_not_prime_power h_card_ne_zero h_not' with
    ⟨q, hq_prime, hq_dvd, hq_ne⟩
  have : Fact q.Prime := ⟨hq_prime⟩
  let Q : Sylow q N := Classical.choice Sylow.nonempty
  have hQ_ne_bot : (Q : Subgroup N) ≠ ⊥ := by
    apply Sylow.ne_bot_of_dvd_card Q hq_dvd
  have : Group.IsNilpotent (↥N) := hN_nilpotent
  have h_normcond : NormalizerCondition N := Group.normalizerCondition_of_isNilpotent
  have hQ_normal : (Q : Subgroup N).Normal :=
    Sylow.normal_of_normalizerCondition h_normcond Q
  have hQ_char : (Q : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal Q hQ_normal
  have : N.Normal := hN_normal
  have : (Q : Subgroup N).Characteristic := hQ_char
  have : ((Q : Subgroup N).map N.subtype).Normal := inferInstance
  have hQ_pgroup : IsPGroup q (Q : Subgroup N) := Q.isPGroup'
  have hQ_map_pgroup : IsPGroup q ((Q : Subgroup N).map N.subtype) :=
    IsPGroup.map hQ_pgroup N.subtype
  rcases (IsPGroup.iff_card.mp hQ_map_pgroup) with ⟨n, hcard⟩
  have hcoprime : Nat.Coprime p (Nat.card ((Q : Subgroup N).map N.subtype)) := by
    rw [hcard]
    exact coprime_prime_pow_of_ne hp_prime hq_prime hq_ne.symm n
  have hQ_eq_bot := (pPrimeCore_eq_bot_iff.mp hcore ((Q : Subgroup N).map N.subtype) inferInstance hcoprime)
  apply hQ_ne_bot
  have hQ_eq_bot' : (Q : Subgroup N) = ⊥ :=
    Subgroup.map_injective Subtype.coe_injective (by
      simpa [Subgroup.map_bot] using hQ_eq_bot)
  exact hQ_eq_bot'

end pPrimeCore_properties
