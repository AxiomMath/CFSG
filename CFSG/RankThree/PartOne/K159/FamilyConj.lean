module

public import CFSG.RankThree.PartOne.K159.BorelConj
import CFSG.RankThree.PartOne.HNB.Tools
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartOne.K159

open scoped Pointwise commutatorElement

@[expose] def FamilyFactsGrp (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∃ Pi : Set (Subgroup H), ¬ p ∣ Nat.card ↥Pi ∧
    (∀ α : MulAut H, ∀ M ∈ Pi, M.map α.toMonoidHom ∈ Pi) ∧
    ∀ M ∈ Pi, p ∣ Nat.card ↥M ∧
      ∃ S : Subgroup H, S ≤ M ∧ IsPGroup 2 ↥S ∧
        (∀ α : MulAut H, M.map α.toMonoidHom = M → S.map α.toMonoidHom = S) ∧
        ∀ x ∈ M, orderOf x = p → ∃ t ∈ S, x * t ≠ t * x

theorem map_map_transport {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') (α' : MulAut H')
    (N : Subgroup H) :
    (N.map e.toMonoidHom).map α'.toMonoidHom =
      (N.map (e.trans (α'.trans e.symm)).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem FamilyFactsGrp.of_mulEquiv {p : ℕ} {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : FamilyFactsGrp p H) : FamilyFactsGrp p H' := by
  obtain ⟨Pi, hcard, hstab, hM⟩ := h
  have hinj : Function.Injective (fun M : Subgroup H => M.map e.toMonoidHom) :=
    Subgroup.map_injective e.injective
  refine ⟨(fun M : Subgroup H => M.map e.toMonoidHom) '' Pi, ?_, ?_, ?_⟩
  · rw [Nat.card_image_of_injective hinj]
    exact hcard
  · rintro α' _ ⟨M, hMPi, rfl⟩
    refine ⟨M.map (e.trans (α'.trans e.symm)).toMonoidHom,
      hstab (e.trans (α'.trans e.symm)) M hMPi, ?_⟩
    exact (map_map_transport e α' M).symm
  · rintro _ ⟨M, hMPi, rfl⟩
    obtain ⟨hpM, S, hSM, hS2, hSinv, hScent⟩ := hM M hMPi
    refine ⟨?_, S.map e.toMonoidHom, Subgroup.map_mono hSM, hS2.map e.toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hpM
    · intro α' hα'
      rw [map_map_transport] at hα' ⊢
      have h1 : M.map (e.trans (α'.trans e.symm)).toMonoidHom = M := by
        apply hinj
        exact hα'
      rw [hSinv _ h1]
    · rintro x hx hxo
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hyo : orderOf y = p := by
        rw [← hxo]
        exact (MulEquiv.orderOf_eq e y).symm
      obtain ⟨t, htS, hne⟩ := hScent y hy hyo
      refine ⟨e t, Subgroup.mem_map_of_mem _ htS, fun hc => hne ?_⟩
      apply e.injective
      rw [map_mul, map_mul]
      exact hc

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_two_subgroup_of_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E Y M S : Subgroup G}
    [hE : IsElementaryAbelian p ↥E]
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hMY : M ≤ Y) (hSM : S ≤ M) (hS2 : IsPGroup 2 ↥S)
    (hEM : E ≤ Subgroup.normalizer (M : Set G)) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hpM : p ∣ Nat.card ↥M) (hcent : ∀ x ∈ M, orderOf x = p → ∃ t ∈ S, x * t ≠ t * x) :
    ∃ S₀ : Subgroup G, S₀ ≤ Y ∧ S₀ ≠ ⊥ ∧ IsPGroup 2 ↥S₀ ∧ E ≤ Subgroup.normalizer (S₀ : Set G) ∧
      S₀ = ⁅S₀, E⁆ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := IsElementaryAbelian.isPGroup p ↥E
  have hSinv : ∀ e ∈ E, ∀ x ∈ S, e * x * e⁻¹ ∈ S := fun e he x hx =>
    (Subgroup.mem_normalizer_iff.1 (hES he) x).1 hx
  obtain ⟨x, hxM, hxo, hxc⟩ := exists_orderOf_eq_of_isPGroup_normalizes hp hEM hEp hpM
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hxE : x ∈ E := by
    have hz : IsElementaryAbelian p ↥(Subgroup.zpowers x) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hcentz : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro e he
      exact hxc e he
    have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hcentz
    have hF : E ⊔ Subgroup.zpowers x = E := hEmax _ hsup le_sup_left
    rw [← hF]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨t, htS, hxt⟩ := hcent x hxM hxo
  have hcomm : ⁅t, x⁆ ≠ 1 := fun h => hxt ((commutatorElement_eq_one_iff_mul_comm.1 h).symm)
  refine ⟨⁅S, E⁆, ?_, ?_, ?_, ?_, ?_⟩
  · exact (commutator_le_of_forall_conj_mem hSinv).trans (hSM.trans hMY)
  · intro h
    apply hcomm
    have := Subgroup.commutator_mem_commutator htS hxE
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · exact hS2.to_le (commutator_le_of_forall_conj_mem hSinv)
  ·
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : S.map (MulAut.conj e).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hES he)
    have h2 : E.map (MulAut.conj e).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer he)
    have h3 := Subgroup.map_commutator S E (MulAut.conj e).toMonoidHom
    have h4 : (⁅S, E⁆).map (MulAut.conj e).toMonoidHom = ⁅S, E⁆ := by
      rw [h3]
      exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆) h1 h2
    exact h4
  ·
    have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥S) := by
      obtain ⟨a, ha⟩ := hEp.exists_card_eq
      obtain ⟨b, hb⟩ := hS2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hsolv : Group.IsSolvable ↥S := by
      have : Group.IsNilpotent ↥S := hS2.isNilpotent
      infer_instance
    exact (HNB.commutator_double_eq_self_of_coprime_solvable E S
      (le_normalizer_of_forall_conj_mem hSinv) hcop hsolv).symm

@[expose] def FamilyFacts (p : ℕ) (Y : Subgroup G) : Prop := FamilyFactsGrp p ↥Y

theorem exists_two_subgroup_of_family {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E Y : Subgroup G}
    [hE : IsElementaryAbelian p ↥E]
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) (hF : FamilyFacts p Y) :
    ∃ S : Subgroup G, S ≤ Y ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, E⁆ := by
  classical
  obtain ⟨Pi, hcard, hstab, hM⟩ := hF
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := IsElementaryAbelian.isPGroup p ↥E
  let : MulDistribMulAction ↥E ↥Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  let αe : ↥E → MulAut ↥Y := fun e => MulDistribMulAction.toMulEquiv ↥Y e
  have hα : ∀ (e : ↥E) (M : Subgroup ↥Y), e • M = M.map (αe e).toMonoidHom := fun e M => rfl
  let sub : SubMulAction ↥E (Subgroup ↥Y) :=
    { carrier := Pi
      smul_mem' := fun e M hM' => by
        rw [hα]
        exact hstab _ M hM' }
  have hcard' : ¬ p ∣ Nat.card ↥sub := hcard
  obtain ⟨Mfix, hMfix⟩ := hEp.nonempty_fixed_point_of_prime_not_dvd_card ↥sub hcard'
  set M : Subgroup ↥Y := (Mfix : Subgroup ↥Y) with hMdef
  have hMPi : M ∈ Pi := Mfix.2
  have hMe : ∀ e : ↥E, M.map (αe e).toMonoidHom = M := fun e => by
    have h1 : e • Mfix = Mfix := MulAction.mem_fixedPoints.1 hMfix e
    have h2 : e • M = M := congrArg (fun P : ↥sub => (P : Subgroup ↥Y)) h1
    rw [← hα]
    exact h2
  obtain ⟨hpM, S, hSM, hS2, hSinv, hScent⟩ := hM M hMPi
  have hSe : ∀ e : ↥E, S.map (αe e).toMonoidHom = S := fun e => hSinv _ (hMe e)
  set M' : Subgroup G := M.map Y.subtype with hM'
  set S' : Subgroup G := S.map Y.subtype with hS'
  have hM'Y : M' ≤ Y := Subgroup.map_subtype_le _
  have hS'M' : S' ≤ M' := Subgroup.map_mono hSM
  have hM'inv : ∀ e ∈ E, ∀ x ∈ M', e * x * e⁻¹ ∈ M' := by
    intro e he x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 : (αe ⟨e, he⟩) t ∈ M := by
      rw [← hMe ⟨e, he⟩]
      exact Subgroup.mem_map_of_mem _ ht
    exact Subgroup.mem_map.2 ⟨_, h1, rfl⟩
  have hS'inv : ∀ e ∈ E, ∀ x ∈ S', e * x * e⁻¹ ∈ S' := by
    intro e he x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 : (αe ⟨e, he⟩) t ∈ S := by
      rw [← hSe ⟨e, he⟩]
      exact Subgroup.mem_map_of_mem _ ht
    exact Subgroup.mem_map.2 ⟨_, h1, rfl⟩
  have hpM' : p ∣ Nat.card ↥M' := by
    rw [hM', Subgroup.card_map_of_injective Y.subtype_injective]
    exact hpM
  have hS'2 : IsPGroup 2 ↥S' := hS2.map Y.subtype
  have hcent' : ∀ x ∈ M', orderOf x = p → ∃ t ∈ S', x * t ≠ t * x := by
    intro x hx hxo
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyo : orderOf y = p := by
      rw [← hxo]
      exact (Subgroup.orderOf_coe y).symm
    obtain ⟨t, htS, hne⟩ := hScent y hy hyo
    refine ⟨(t : G), Subgroup.mem_map_of_mem _ htS, fun h => hne ?_⟩
    exact Subtype.ext h
  exact exists_two_subgroup_of_fixed hp hp2 hEmax hM'Y hS'M' hS'2
    (le_normalizer_of_forall_conj_mem hM'inv) (le_normalizer_of_forall_conj_mem hS'inv) hpM' hcent'

end Fixed

end CFSG.RankThree.PartOne.K159
