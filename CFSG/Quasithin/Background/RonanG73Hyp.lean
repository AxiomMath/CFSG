module

public import CFSG.Quasithin.Background.RonanG73Setup
public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.Foundations.KCoreClosure
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoprimeCentralizer

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

theorem isElemAbelian_subgroupOf {M : Type*} [Group M] {A : Subgroup M} (hA : IsElemAbelian 2 A)
    (K : Subgroup M) : IsElemAbelian 2 (A.subgroupOf K) := by
  obtain ⟨hcomm, hpow⟩ := hA
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have := hcomm.is_comm.comm ⟨(a : ↥K).1, a.2⟩ ⟨(b : ↥K).1, b.2⟩
    exact congrArg (fun z : ↥A => (z : M)) this
  · apply Subtype.ext
    have := hpow (x : M) hx
    simpa using this

theorem isSQTKCat_of_sup_elemAbelian {X : Type} [Group X] [Finite X] (L A : Subgroup X)
    [L.Normal] (hA : IsElemAbelian 2 A) (hX : L ⊔ A = ⊤)
    (hL : CFSG.SectionRank.IsSQTKCat ↥L) : CFSG.SectionRank.IsSQTKCat X := by
  have hmemA : ∀ y : X ⧸ L, ∃ a ∈ A, (QuotientGroup.mk' L) a = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ L ⊔ A := by rw [hX]; trivial
    obtain ⟨l, hl, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨a, ha, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).2 hl,
      one_mul]
  have hsq : ∀ y : X ⧸ L, y * y = 1 := by
    intro y
    obtain ⟨a, ha, rfl⟩ := hmemA y
    rw [← map_mul]
    have : a * a = 1 := by
      have := hA.2 a ha
      rwa [pow_two] at this
    rw [this, map_one]
  refine ⟨?_, ?_⟩
  ·
    intro p hp hp2
    have hp1 : 1 < p := hp.one_lt
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p X]
    obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup X)
    have hEL : E ≤ L := by
      intro x hx
      have h1 : (QuotientGroup.mk' L x) ^ p = 1 := by rw [← map_pow, hE.2 x hx, map_one]
      have h2 : (QuotientGroup.mk' L x) ^ 2 = 1 := by rw [pow_two, hsq]
      have h3 : orderOf (QuotientGroup.mk' L x) ∣ Nat.gcd p 2 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
      have hcop : Nat.gcd p 2 = 1 := by
        have : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
        exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
          (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm)))
      rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact (QuotientGroup.eq_one_iff x).1 h3
    have hE' : IsElemAbelian p (E.subgroupOf L) := by
      obtain ⟨hcomm, hpow⟩ := hE
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have := hcomm.is_comm.comm ⟨(a : ↥L).1, a.2⟩ ⟨(b : ↥L).1, b.2⟩
        exact congrArg (fun z : ↥E => (z : X)) this
      · apply Subtype.ext
        have := hpow (x : X) hx
        simpa using this
    have hcard' : Nat.card (E.subgroupOf L) = p ^ CFSG.Open.pRank p (⊤ : Subgroup X) := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    have hle : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
      CFSG.SectionRank.le_pRank hp1 le_top hE' hcard'
    have hL2 := hL.1 p hp hp2
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥L] at hL2
    exact hle.trans hL2
  ·
    have hk : CFSG.SectionRank.IsKGroupCat ↥(QuotientGroup.mk' L).ker :=
      hL.2.of_mulEquiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' L))
    have hq : CFSG.KCore.KGroupAllSimple CFSG.Blueprint.Catalog (X ⧸ L) := by
      refine CFSG.KCore.KGroupAllSimple.of_commutative
        CFSG.SectionRank.catalog_containsAbelianSimple fun a b => ?_
      obtain ⟨a', ha', rfl⟩ := hmemA a
      obtain ⟨b', hb', rfl⟩ := hmemA b
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg (fun z : ↥A => (z : X)) (hA.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    exact CFSG.KCore.KGroupAllSimple.of_ker CFSG.SectionRank.catalog_isoInvariant
      (QuotientGroup.mk' L) hk hq

theorem isQuotientOfSQTKTauCeti_sup {M : Type} [Group M] [Finite M] {L A : Subgroup M}
    (hLn : ∀ g ∈ L ⊔ A, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hA : IsElemAbelian 2 A)
    (hL : CFSG.SectionRank.IsSQTKCat ↥L) : IsQuotientOfSQTKTauCeti ↥(L ⊔ A) := by
  set Γ : Subgroup M := L ⊔ A with hΓ
  have hLΓ : L ≤ Γ := le_sup_left
  have hAΓ : A ≤ Γ := le_sup_right
  have hLn' : (L.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff hLΓ).2 fun l γ hl hγ => hLn γ hγ l hl
  have hsup : L.subgroupOf Γ ⊔ A.subgroupOf Γ = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Γ)
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLΓ,
      Subgroup.map_subgroupOf_eq_of_le hAΓ, Subgroup.map_top, Subgroup.range_subtype]
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥Γ := by
    refine isSQTKCat_of_sup_elemAbelian (L.subgroupOf Γ) (A.subgroupOf Γ)
      (isElemAbelian_subgroupOf hA Γ) hsup ?_
    exact hL.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLΓ)
  exact ⟨↥Γ, inferInstance, inferInstance, tc_of_isStronglyQuasithin hSQTK.1, hSQTK.2,
    MonoidHom.id _, Function.surjective_id⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_g93Hyp {G L : Subgroup (GLV V)} [Finite ↥G] (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L)
    (hS : CFSG.SectionRank.IsSQTKCat ↥L) (hirr : IsIrr L ⊤)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (twoRank ↥G + 1)) :
    ∃ Γ A : Subgroup (GLV V), Γ ≤ G ∧ G93Hyp Γ A L L (twoRank ↥G) := by
  haveI : Finite (GLV V) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.finite_GLV_of_finite (V := V)
  obtain ⟨A, hAG, hAel, hAcard⟩ := exists_elemAbelian_twoRank G
  have hΓG : L ⊔ A ≤ G := sup_le hLG hAG
  have hLΓ : L ≤ L ⊔ A := le_sup_left
  have hΓnorm : ∀ γ ∈ L ⊔ A, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L := fun γ hγ => hnorm γ (hΓG hγ)
  have hm1 : 1 ≤ twoRank ↥G := by
    have h2 := two_lt_finrank_of_quasisimple (V := V) hq
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    have : 2 ^ 1 ≤ 2 ^ twoRank ↥G := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  have hn : (L.subgroupOf (L ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff hLΓ).2 fun l γ hl hγ => hΓnorm γ hγ l hl
  have hq' : CFSG.Open.IsQuasisimple ↥L := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hA2 : IsPGroup 2 ↥A :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.isPGroup_two_of_isElemAbelian hAel
  refine ⟨L ⊔ A, A, hΓG, ?_⟩
  exact
  { quotient := isQuotientOfSQTKTauCeti_sup hΓnorm hAel hS
    A_le := le_sup_right
    A_elem := hAel
    A_card := hAcard
    bound := hd
    L_comp := ⟨hLΓ, IsSubnormal.step hLΓ hn (IsSubnormal.refl _), hq'⟩
    L_comm := by
      by_contra hcon
      push Not at hcon
      have hAle : A ≤ (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
        intro a ha
        refine Subgroup.mem_inf.2 ⟨(le_sup_right : A ≤ L ⊔ A) ha, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro l hl
        exact (hcon a ha l hl).symm
      have hbot :=
        CFSG.Quasithin.Background.Harris.OrdinaryProofs.inf_centralizer_eq_bot_of_two_group
          hirr (L ⊔ A) hA2
      apply hAne
      rw [eq_bot_iff, ← hbot]
      exact le_inf le_rfl hAle
    H_le := hLΓ
    H_normal := hΓnorm
    H_irr := hirr
    H_eq := Or.inl rfl }

end CFSG.Quasithin.RonanG73
