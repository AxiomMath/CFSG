module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G10

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.mem_J_of_orderOf_three' (c : Conf T L I t w J)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hE : Ch11.SecA.FactA318ExclTwo) {S : Type} [Group S] [Finite S]
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S) (hQS : CFSG.IsQuasisimple S)
    (hZS : Subgroup.center S = ⊥) (h3S : 3 ∣ Nat.card S)
    (hrkS : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S))
    (hK7S : ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
      ∀ f : X →* S, ¬ Function.Surjective f)
    {y : G} (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hy3 : orderOf y = 3) : y ∈ J := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hS : SQTKGroup ↥(Subgroup.centralizer ({w} : Set G)) :=
    InternalSec.sqtkGroup_of_localSQTK hK (pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq)
  have hSQ := SQTKHyp.of_sqtkGroup _ hS
  have hJc := subgroupOf_mem_cComp c.mem
  obtain ⟨e₀⟩ := Ch11.SecA.quotPCore_subgroupOf_equiv (L := J) c.J_le
  set e := e₀.trans eJ with he
  have hQ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQS
  have hrank : 1 < CFSG.Open.pRank 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))) := by
    rw [Ch11.SecA.pRank_subgroupOf_eq c.J_le Nat.prime_three (by norm_num),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eJ]
    omega
  have hconc := a318 h318 hS (h36' _ hSQ) (a38ForSQTK_of_cat h38 _ hSQ) hJc hQ Nat.prime_three
    (by norm_num) hrank
  set y' : ↥(Subgroup.centralizer ({w} : Set G)) := ⟨y, hy⟩
  have hy'3 : orderOf y' = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  suffices hy' : y' ∈ J.subgroupOf (Subgroup.centralizer ({w} : Set G)) from
    Subgroup.mem_subgroupOf.mp hy'
  have hZ' : Subgroup.center (↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G))) ⧸
      CFSG.pCore 2 ↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G)))) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hZS] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have h3 : 3 ∣ Nat.card (↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G))) ⧸
      CFSG.pCore 2 ↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G)))) := by
    rw [Nat.card_congr e.toEquiv]
    exact h3S
  obtain ⟨ψ, hψ, hψk⟩ := Ch11.SecA.exists_starHom hQ hZ' h3
  set ψ' := e.toMonoidHom.comp ψ with hψ'
  have hψ's : Function.Surjective ψ' := e.surjective.comp hψ
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3', -⟩
  · rw [h1]
    exact Subgroup.subset_closure ⟨trivial, 1, by rw [pow_one]; exact hy'3⟩
  · exfalso
    obtain ⟨s, q, -, ⟨r, k, -, -, -, hPSL⟩, -⟩ := h2
    exact hK7S _ s r k hPSL ψ' hψ's
  · exfalso
    have hc := hE _ h3'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center
      ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G)))))) 3 (by rw [hc])
    have hzc : ψ' (z : ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))))) ∈
        Subgroup.center S :=
      Subgroup.map_center_le_center hψ's ⟨_, z.2, rfl⟩
    rw [hZS, Subgroup.mem_bot] at hzc
    have h1 : ψ z = 1 := by
      have := congrArg e.symm hzc
      rwa [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        map_one] at this
    obtain ⟨k, hk⟩ := hψk _ h1
    have h2 : orderOf (z : ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))))) ∣
        2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_coe, hz] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

theorem Conf.exists_y_of_case3 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) :
    ∃ y ∈ CFSG.conjugate L t, orderOf y = 3 ∧ y ∈ Subgroup.centralizer ({w} : Set G) := by
  have hwt : t * w * t⁻¹ ∈ fsuUL T L I := by
    have h1 := c.claim.1
    rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L c.ht),
      SecA.mem_conjugate_iff] at h1
    exact h1
  obtain ⟨l, hl, hl3, hlc⟩ := exists_three_comm_of_case3 h37 h38 h1011 c.hyp h3 hwt
  refine ⟨t⁻¹ * l * t, ?_, ?_, ?_⟩
  · rw [SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hl
  · have := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective l
    rw [← hl3, ← this]
    simp
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc t⁻¹ * l * t * w = t⁻¹ * (l * (t * w * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * w * t⁻¹) * l) * t := by rw [hlc]
      _ = w * (t⁻¹ * l * t) := by group

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
