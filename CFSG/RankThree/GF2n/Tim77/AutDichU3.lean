module

public import CFSG.CGT.T75B.Lemma21Wire
public import CFSG.Goldschmidt.Steps.StrongEmb

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.T75B (rootGroup mem_rootGroup)

theorem sylow_eq_of_involution_mem {L : Type} [Group L] [Finite L]
    (hK : CFSG.BenderSuzuki.IsBenderGroup L) (S S' : Sylow 2 L) {c : L} (hc : orderOf c = 2)
    (hcS : c ∈ (S : Subgroup L)) (hcS' : c ∈ (S' : Subgroup L)) : S = S' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK S
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L S S'
  have hgc : g⁻¹ * c * g ∈ (S : Subgroup L) := CFSG.CGT.T75B.mem_smul_sylow.mp hcS'
  have hgN : g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
    CFSG.Goldschmidt.mem_of_involution_conj_mem hN hc (Subgroup.le_normalizer hcS)
      (Subgroup.le_normalizer hgc)
  apply Sylow.ext
  ext x
  rw [CFSG.CGT.T75B.mem_smul_sylow]
  have h := (Subgroup.mem_normalizer_iff.mp hgN) (g⁻¹ * x * g)
  rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h
  exact h.symm

theorem involution_mem_sylow_of_normalizer {L : Type} [Group L] (S : Sylow 2 L) {c : L}
    (hc : orderOf c = 2) (hcN : c ∈ Subgroup.normalizer ((S : Subgroup L) : Set L)) :
    c ∈ (S : Subgroup L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have h2 := S.isPGroup'.to_sup_of_normal_left' hp (Subgroup.zpowers_le.mpr hcN)
  have heq := S.is_maximal' h2 le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem autDich_u3 {L : Type} [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* CFSG.Theory.Comparator.PSU3Model f) (σ : MulAut L) (hσ : σ * σ = 1) {ā : L}
    (hā : orderOf ā = 2) (hfix : σ ā = ā) :
    (∃ τ : L, τ * τ = 1 ∧ τ * ā = ā * τ ∧ ∀ z : L, σ z = τ * z * τ⁻¹) ∨
      (∃ t : L, orderOf t = 2 ∧ σ t = t ∧ ¬ Commute ā t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : CFSG.BenderSuzuki.IsBenderGroup L := CFSG.BenderSuzuki.IsBenderGroup.isPSU3 f hf e
  have hI : CFSG.CGT.T75B.Lemma21Input L := CFSG.CGT.T75B.lemma21Input_of_mulEquiv hf e
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rw [hā, pow_two] at h
    exact h
  obtain ⟨S, hāS⟩ : ∃ S : Sylow 2 L, ā ∈ (S : Subgroup L) := by
    have hp : IsPGroup 2 (Subgroup.zpowers ā) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hā, pow_one])
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers ā)⟩
  have hN := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK S
  have hāN : ā ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) := Subgroup.le_normalizer hāS
  have hāc : ∀ y ∈ (S : Subgroup L), Commute ā y :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK S hāS hā2
  have hāR : ā ∈ rootGroup S := mem_rootGroup.mpr ⟨hāS, fun s hs => (hāc s hs).symm.eq⟩
  have hσσ : ∀ g : L, σ (σ g) = g := fun g => congrArg (fun f : MulAut L => f g) hσ
  have hσN : (S : Subgroup L).map σ.toMonoidHom ≤
      Subgroup.normalizer ((S : Subgroup L) : Set L) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hc : σ s ∈ Subgroup.centralizer ({ā} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := (hāc s hs).map σ
      rw [hfix] at h1
      exact h1.symm.eq
    exact CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hN hā hāN hc
  have hσS : (S : Subgroup L).map σ.toMonoidHom ≤ (S : Subgroup L) := by
    have h2 := S.isPGroup'.to_sup_of_normal_left' (S.isPGroup'.map σ.toMonoidHom) hσN
    have heq := S.is_maximal' h2 le_sup_left
    exact le_sup_right.trans heq.le
  have hpres : ∀ x ∈ rootGroup S, σ x ∈ rootGroup S := by
    intro x hx
    obtain ⟨hxS, hxc⟩ := mem_rootGroup.mp hx
    refine mem_rootGroup.mpr ⟨hσS (Subgroup.mem_map.mpr ⟨x, hxS, rfl⟩), fun s hs => ?_⟩
    have hσsS : σ s ∈ (S : Subgroup L) := hσS (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
    have h2 := congrArg σ (hxc (σ s) hσsS)
    simpa only [map_mul, hσσ] using h2
  by_cases hin : σ ∈ (MulAut.conj : L →* MulAut L).range
  ·
    obtain ⟨t, htR, hσt⟩ := hI.inner S σ hσ hin hpres
    have htm := mem_rootGroup.mp htR
    have htt : t * t = 1 :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hK S htm.1
        (fun y hy => (htm.2 y hy).symm)
    refine Or.inl ⟨t, htt, (htm.2 ā hāS).symm, fun z => ?_⟩
    rw [hσt, MulAut.conj_apply]
  ·
    obtain ⟨-, S', hne, hfixS'⟩ := hI.outer S σ hσ hin hpres
    have h4 : 4 ≤ Nat.card (Subgroup.center (S' : Subgroup L)) :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.four_le_card_center hK S'
    have hcen1 : Subgroup.center (S' : Subgroup L) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at h4
      omega
    obtain ⟨⟨⟨c, hcS'⟩, hcen⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcen1
    have hcR : c ∈ rootGroup S' :=
      Subgroup.mem_map.mpr ⟨⟨c, hcS'⟩, hcen, rfl⟩
    have hc1' : c ≠ 1 := by
      rintro rfl
      exact hc1 rfl
    obtain ⟨hcS'', hcc⟩ := mem_rootGroup.mp hcR
    have hcc2 : c * c = 1 :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hK S' hcS''
        (fun y hy => (hcc y hy).symm)
    have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc2) hc1'
    have hσc : σ c = c := hfixS' c hcR
    refine Or.inr ⟨c, hord, hσc, fun hcom => ?_⟩
    have hcN : c ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
      CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hN hā hāN
        (Subgroup.mem_centralizer_singleton_iff.mpr hcom.symm.eq)
    have hcS : c ∈ (S : Subgroup L) := involution_mem_sylow_of_normalizer S hord hcN
    exact hne (congrArg rootGroup (sylow_eq_of_involution_mem hK S S' hord hcS hcS'').symm)

end CFSG.RankThree.GF2n.Tim77
