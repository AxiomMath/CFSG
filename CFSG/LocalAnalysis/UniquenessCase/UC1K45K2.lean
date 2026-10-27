module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private lemma uc45_kof_isSolvable (c : Pre45 p G D) : Group.IsSolvable ↥(Kof G) := by
  have hpos : Nat.card ↥(Kof G) ≠ 0 := Nat.card_pos.ne'
  have hsupp : (Nat.card ↥(Kof G)).factorization.support ⊆ ({2, p} : Finset ℕ) := by
    intro r hr
    rw [Nat.support_factorization] at hr
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact c.K22p r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  refine TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow (G := ↥(Kof G))
    (p := 2) (q := p) (a := (Nat.card ↥(Kof G)).factorization 2)
    (b := (Nat.card ↥(Kof G)).factorization p) Nat.prime_two c.prime ?_
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (ne_of_lt c.odd)]

private lemma uc45_kof_map_isSolvable (c : Pre45 p G D) :
    Group.IsSolvable ↥((Kof G).map (QuotientGroup.mk' (Wker G))) := by
  haveI : Group.IsSolvable ↥(Kof G) := uc45_kof_isSolvable c
  let ψ : ↥(Kof G) →* ↥((Kof G).map (QuotientGroup.mk' (Wker G))) :=
    { toFun := fun x => ⟨QuotientGroup.mk' (Wker G) x.1,
        Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  exact Group.isSolvable_of_surjective (f := ψ) fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private lemma uc45_kof_map_normalClosure (c : Pre45 p G D) :
    Subgroup.normalClosure
      ((D.map (QuotientGroup.mk' (Wker G)) : Subgroup (G ⧸ Wker G)) :
        Set (G ⧸ Wker G)) = ⊤ := by
  rw [Subgroup.coe_map, ← Subgroup.map_normalClosure (D : Set G)
    (QuotientGroup.mk' (Wker G)) (QuotientGroup.mk'_surjective _), c.gen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private lemma uc45_kof_map_coprime (c : Pre45 p G D) :
    Nat.Coprime 3 (Nat.card ↥((Kof G).map (QuotientGroup.mk' (Wker G)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (CFSG.pPrimeCore_coprime_card (p := 3) (G := G)).coprime_dvd_right ?_
  refine (Subgroup.card_map_dvd (Kof G) (QuotientGroup.mk' (Wker G))).trans ?_
  exact Subgroup.card_dvd_of_le (Subgroup.commutator_le_left (H₁ := CFSG.pPrimeCore 3 G)
    (H₂ := (⊤ : Subgroup G)))

private lemma uc45_kof_map_commutator (c : Pre45 p G D) :
    ⁅(Kof G).map (QuotientGroup.mk' (Wker G)), (⊤ : Subgroup (G ⧸ Wker G))⁆ =
      (Kof G).map (QuotientGroup.mk' (Wker G)) := by
  rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' (Wker G))
      (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_commutator (QuotientGroup.mk' (Wker G)) (H₁ := Kof G)
      (H₂ := (⊤ : Subgroup G)),
    kof_commutator_top c.card_three c.gen]

private lemma uc45_kof_map_pair (hPair : PairX) (c : Pre45 p G D) :
    ∀ k ∈ (Kof G).map (QuotientGroup.mk' (Wker G)),
      Z3E9A5Mod2 ((D.map (QuotientGroup.mk' (Wker G))) ⊔
        (D.map (QuotientGroup.mk' (Wker G))).map (MulAut.conj k).toMonoidHom) := by
  intro k hk
  obtain ⟨k₀, _hk₀, hk₀eq⟩ := Subgroup.mem_map.1 hk
  have hconj : (MulAut.conj k).toMonoidHom.comp (QuotientGroup.mk' (Wker G)) =
      (QuotientGroup.mk' (Wker G)).comp (MulAut.conj k₀).toMonoidHom := by
    ext x
    change k * QuotientGroup.mk' (Wker G) x * k⁻¹ =
      QuotientGroup.mk' (Wker G) (k₀ * x * k₀⁻¹)
    rw [map_mul, map_mul, map_inv, hk₀eq]
  have hsup : D.map (QuotientGroup.mk' (Wker G)) ⊔
      (D.map (QuotientGroup.mk' (Wker G))).map (MulAut.conj k).toMonoidHom =
      (D ⊔ D.map (MulAut.conj k₀).toMonoidHom).map (QuotientGroup.mk' (Wker G)) := by
    rw [Subgroup.map_map, hconj, ← Subgroup.map_map, ← Subgroup.map_sup]
  rw [hsup]
  exact uc45_pair_shape hPair c (Wker G) rfl k₀

private lemma uc45_kof_map_isPGroup (hCore : Core2) (hPair : PairX) (c : Pre45 p G D) :
    IsPGroup 2 ((Kof G).map (QuotientGroup.mk' (Wker G))) := by
  haveI : ((Kof G).map (QuotientGroup.mk' (Wker G))).Normal :=
    (kof_normal (G := G)).map (QuotientGroup.mk' (Wker G)) (QuotientGroup.mk'_surjective _)
  exact hCore (G ⧸ Wker G) (D.map (QuotientGroup.mk' (Wker G)))
    ((Kof G).map (QuotientGroup.mk' (Wker G))) (uc45_card_D_map c)
    (uc45_kof_map_normalClosure c) (uc45_kof_map_isSolvable c)
    (uc45_kof_map_coprime c) (uc45_kof_map_commutator c) (uc45_kof_map_pair hPair c)

private lemma uc45_odd_prime_order_not_mem_inf_wker (c : Pre45 p G D)
    {x : G} (hxK : x ∈ Kof G) (hxW : x ∈ Wker G)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hxq : orderOf x = q) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hPX : ⁅Subgroup.zpowers x, Xof G⁆ ≤ ZXof G := by
    refine Subgroup.commutator_le.mpr fun a ha y hy => ?_
    exact (mem_wker.mp (Subgroup.zpowers_le.mpr hxW ha)) y hy
  have hRZX : ⁅Xof G, Subgroup.zpowers x⁆ ≤ ZXof G := by
    rw [Subgroup.commutator_comm (Xof G) (Subgroup.zpowers x)]
    exact hPX
  have hRZ : ⁅Xof G, Subgroup.zpowers x⁆ ≤ Subgroup.center G := hRZX.trans c.ZX_le
  have hcommbot : ⁅⁅Xof G, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro p _
    exact Subgroup.mem_center_iff.mp (hRZ hr) p
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card ↥(Xof G)) := by
    rw [Nat.card_zpowers, hxq]
    refine (hq.coprime_iff_not_dvd).mpr fun hdvd => ?_
    obtain ⟨k, hk⟩ := (xof_isPGroup (G := G)).exists_card_eq
    rw [hk] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  have hidem : ⁅⁅Xof G, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ =
      ⁅Xof G, Subgroup.zpowers x⁆ :=
    CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime (Xof G)
      (Subgroup.zpowers x) hcop
      (Subgroup.le_normalizer_of_normal : Subgroup.zpowers x ≤
        Subgroup.normalizer (Xof G : Set G))
  have hRbot : ⁅Xof G, Subgroup.zpowers x⁆ = ⊥ := by rw [← hidem, hcommbot]
  have hxcentX : x ∈ Subgroup.centralizer (Xof G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hycent : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Xof G)
        (H₂ := Subgroup.zpowers x)).mp hRbot hy
    exact (Subgroup.mem_centralizer_iff.mp hycent x (Subgroup.mem_zpowers x)).symm
  have hxX : x ∈ Xof G := uc45_centralizer_X_le c.toBase45 c.K22p ⟨hxK, hxcentX⟩
  have hdvd : orderOf x ∣ Nat.card ↥(Xof G) := Subgroup.orderOf_dvd_natCard (Xof G) hxX
  obtain ⟨k, hk⟩ := (xof_isPGroup (G := G)).exists_card_eq
  rw [hxq, hk] at hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))

private lemma uc45_inf_wker_isPGroup (c : Pre45 p G D) :
    IsPGroup 2 ↥(Kof G ⊓ Wker G) := by
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Kof G ⊓ Wker G) → r = 2 := by
    intro r hr hrdvd
    rcases c.K22p r hr (hrdvd.trans
      (Subgroup.card_dvd_of_le (inf_le_left : Kof G ⊓ Wker G ≤ Kof G))) with h2 | hp
    · exact h2
    · exfalso
      haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨x, hxq⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Kof G ⊓ Wker G)) r hrdvd
      exact uc45_odd_prime_order_not_mem_inf_wker c x.2.1 x.2.2 hr
        (by rw [hp]; exact ne_of_gt c.odd) (by rw [Subgroup.orderOf_coe, hxq])
  exact IsPGroup.of_card (n := (Nat.card ↥(Kof G ⊓ Wker G)).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥(Kof G ⊓ Wker G))).ne'
      (fun {r} hr hrdvd => hprime r hr hrdvd))

private lemma uc45_kof_isPGroup_of_map
    (hKmap : IsPGroup 2 ((Kof G).map (QuotientGroup.mk' (Wker G))))
    (hKinf : IsPGroup 2 ↥(Kof G ⊓ Wker G)) : IsPGroup 2 (Kof G) := by
  let ψ : ↥(Kof G) →* G ⧸ Wker G :=
    (QuotientGroup.mk' (Wker G)).comp (Kof G).subtype
  have hker : ψ.ker = (Kof G ⊓ Wker G).subgroupOf (Kof G) := by
    show ((QuotientGroup.mk' (Wker G)).comp (Kof G).subtype).ker =
      (Kof G ⊓ Wker G).subgroupOf (Kof G)
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx' : (x : G) ∈ (QuotientGroup.mk' (Wker G)).ker := MonoidHom.mem_ker.mpr hx
      rwa [QuotientGroup.ker_mk'] at hx'
    · rintro ⟨-, hxW⟩
      exact (MonoidHom.mem_ker (f := QuotientGroup.mk' (Wker G))).mp
        (by rw [QuotientGroup.ker_mk']; exact hxW)
  have hker2 : IsPGroup 2 ψ.ker := by
    rw [hker]
    exact hKinf.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Kof G ⊓ Wker G ≤ Kof G)).symm
  have hrange : ψ.range = (Kof G).map (QuotientGroup.mk' (Wker G)) := by
    show ((QuotientGroup.mk' (Wker G)).comp (Kof G).subtype).range =
      (Kof G).map (QuotientGroup.mk' (Wker G))
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hrange2 : IsPGroup 2 ψ.range := by rw [hrange]; exact hKmap
  have htop : IsPGroup 2 (⊤ : Subgroup ↥(Kof G)) := by
    have h := hrange2.comap_of_ker_isPGroup ψ hker2
    rwa [MonoidHom.comap_range_self] at h
  exact htop.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup ↥(Kof G)) ≃* ↥(Kof G))

theorem uc45_K_eq_X (hCore : Core2) (hPair : PairX) (c : Pre45 p G D) : Kof G = Xof G := by
  have hKmap : IsPGroup 2 ((Kof G).map (QuotientGroup.mk' (Wker G))) :=
    uc45_kof_map_isPGroup hCore hPair c
  have hKinf : IsPGroup 2 ↥(Kof G ⊓ Wker G) := uc45_inf_wker_isPGroup c
  have hK2 : IsPGroup 2 (Kof G) := uc45_kof_isPGroup_of_map hKmap hKinf
  have htopmap : (⊤ : Subgroup ↥(Kof G)).map (Kof G).subtype = Kof G := by
    apply le_antisymm (Subgroup.map_subtype_le _)
    intro x hx
    exact Subgroup.mem_map_of_mem (Kof G).subtype (Subgroup.mem_top (⟨x, hx⟩ : ↥(Kof G)))
  have hKleX : Kof G ≤ Xof G := by
    have htop : (⊤ : Subgroup ↥(Kof G)) ≤ CFSG.pCore 2 ↥(Kof G) :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance
        (hK2.to_subgroup (⊤ : Subgroup ↥(Kof G)))
    calc Kof G = (⊤ : Subgroup ↥(Kof G)).map (Kof G).subtype := htopmap.symm
      _ ≤ (CFSG.pCore 2 ↥(Kof G)).map (Kof G).subtype := Subgroup.map_mono htop
      _ = Xof G := (CFSG.openPCoreOf_eq_map_pCore 2 (Kof G)).symm
  exact le_antisymm hKleX (CFSG.openPCoreOf_le 2 (Kof G))

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
