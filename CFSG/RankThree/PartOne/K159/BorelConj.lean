module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.RankThree.PartOne.HNB.Tools
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartOne.K159

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def BorelFactsGrp (p : ℕ) (H : Type*) [Group H] : Prop :=
  p ∣ Nat.card H ∧ ¬ p ∣ Nat.card (Sylow 2 H) ∧
    ∀ (T : Sylow 2 H) (x : H), orderOf x = p → ∃ t ∈ (T : Subgroup H), x * t ≠ t * x

@[expose] def BorelFacts (p : ℕ) (Y : Subgroup G) : Prop := BorelFactsGrp p ↥Y

theorem card_sylow_le_of_surjective {H H' : Type*} [Group H] [Group H'] [Finite H] {f : H →* H'}
    (hf : Function.Surjective f) (q : ℕ) [Fact q.Prime] :
    Nat.card (Sylow q H') ≤ Nat.card (Sylow q H) :=
  Nat.card_le_card_of_surjective _ (Sylow.mapSurjective_surjective hf q)

theorem BorelFactsGrp.of_mulEquiv {p : ℕ} {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') (h : BorelFactsGrp p H) : BorelFactsGrp p H' := by
  obtain ⟨h0, h1, h3⟩ := h
  have hcard : Nat.card (Sylow 2 H') = Nat.card (Sylow 2 H) :=
    le_antisymm (card_sylow_le_of_surjective (f := e.toMonoidHom) e.surjective 2)
      (card_sylow_le_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact h0
  · rw [hcard]
    exact h1
  · intro T' x' hx'
    obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective 2 T'
    have hxo : orderOf (e.symm x') = p := by
      rw [MulEquiv.orderOf_eq]
      exact hx'
    obtain ⟨t, htT, hne⟩ := h3 T (e.symm x') hxo
    refine ⟨e t, ?_, fun hcomm => hne ?_⟩
    · rw [← hT]
      exact Subgroup.mem_map_of_mem e.toMonoidHom htT
    · apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hcomm

theorem BorelFacts.of_mulEquiv {p : ℕ} {Y Y' : Subgroup G} (e : ↥Y ≃* ↥Y') (h : BorelFacts p Y) :
    BorelFacts p Y' :=
  BorelFactsGrp.of_mulEquiv e h

theorem not_dvd_card_sylow_two_of_torus {p : ℕ} {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    {D : Subgroup H} (hD : D ≤ Subgroup.normalizer (T : Subgroup H)) (hodd : Odd (Nat.card D))
    {m : ℕ} (hm : Nat.card H = Nat.card T * Nat.card D * m) (hpm : ¬ p ∣ m) :
    ¬ p ∣ Nat.card (Sylow 2 H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := Subgroup.normalizer (T : Subgroup H) with hN
  have hTN : (T : Subgroup H) ≤ N := Subgroup.le_normalizer
  have hcop : Nat.Coprime (Nat.card T) (Nat.card D) := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.coprime_two_left).2 hodd)
  have h1 : Nat.card T ∣ Nat.card N := Subgroup.card_dvd_of_le hTN
  have h2 : Nat.card D ∣ Nat.card N := Subgroup.card_dvd_of_le hD
  obtain ⟨k, hk⟩ := hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have h4 : Nat.card N * N.index = Nat.card H := Subgroup.card_mul_index N
  have hpos : 0 < Nat.card T * Nat.card D := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h5 : m = k * N.index := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card T * Nat.card D * m = Nat.card H := hm.symm
      _ = Nat.card N * N.index := h4.symm
      _ = Nat.card T * Nat.card D * (k * N.index) := by rw [hk, mul_assoc]
  rw [Sylow.card_eq_index_normalizer T]
  intro hdvd
  exact hpm (h5 ▸ Dvd.dvd.mul_left hdvd k)

theorem exists_noncomm_of_sylow {p : ℕ} {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    (h : ∀ x : H, orderOf x = p → ∃ t ∈ (T : Subgroup H), x * t ≠ t * x) (T' : Sylow 2 H) :
    ∀ x : H, orderOf x = p → ∃ t ∈ (T' : Subgroup H), x * t ≠ t * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T T'
  intro x hx
  have hy : orderOf (g⁻¹ * x * g) = p := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
    simpa [MulAut.conj_apply] using this.trans hx
  obtain ⟨t, ht, hne⟩ := h (g⁻¹ * x * g) hy
  refine ⟨g * t * g⁻¹, ?_, fun hcomm => hne ?_⟩
  · have h2 : (MulAut.conj g) • t ∈ (MulAut.conj g) • (T : Subgroup H) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨t, ht, rfl⟩
    have h3 : ((g • T : Sylow 2 H) : Subgroup H) = (T' : Subgroup H) :=
      congrArg (fun P : Sylow 2 H => (P : Subgroup H)) hg
    rw [← h3]
    exact h2
  · calc (g⁻¹ * x * g) * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hcomm]
      _ = t * (g⁻¹ * x * g) := by group

theorem BorelFactsGrp.of_torus {p : ℕ} {H : Type*} [Group H] [Finite H] (hpH : p ∣ Nat.card H)
    (T : Sylow 2 H) {D : Subgroup H} (hD : D ≤ Subgroup.normalizer (T : Subgroup H))
    (hodd : Odd (Nat.card D)) {m : ℕ} (hm : Nat.card H = Nat.card T * Nat.card D * m) (hpm : ¬ p ∣ m)
    (hcent : ∀ x : H, orderOf x = p → ∃ t ∈ (T : Subgroup H), x * t ≠ t * x) : BorelFactsGrp p H :=
  ⟨hpH, not_dvd_card_sylow_two_of_torus T hD hodd hm hpm, fun T' => exists_noncomm_of_sylow T hcent T'⟩

theorem not_dvd_card_sylow_two_of_borel {p : ℕ} {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    {B : Subgroup H} (hB : B ≤ Subgroup.normalizer (T : Subgroup H)) (hidx : ¬ p ∣ B.index) :
    ¬ p ∣ Nat.card (Sylow 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_index_normalizer T]
  exact fun hdvd => hidx (hdvd.trans (Subgroup.index_dvd_of_le hB))

theorem BorelFactsGrp.of_borel {p : ℕ} {H : Type*} [Group H] [Finite H] (hpH : p ∣ Nat.card H)
    (T : Sylow 2 H) {B : Subgroup H} (hB : B ≤ Subgroup.normalizer (T : Subgroup H))
    (hidx : ¬ p ∣ B.index)
    (hcent : ∀ x : H, orderOf x = p → ∃ t ∈ (T : Subgroup H), x * t ≠ t * x) : BorelFactsGrp p H :=
  ⟨hpH, not_dvd_card_sylow_two_of_borel T hB hidx, fun T' => exists_noncomm_of_sylow T hcent T'⟩

theorem exists_orderOf_eq_of_isPGroup_normalizes {p : ℕ} (hp : p.Prime) {B E : Subgroup G}
    (hEB : E ≤ Subgroup.normalizer (B : Set G)) (hE : IsPGroup p ↥E) (hpB : p ∣ Nat.card ↥B) :
    ∃ x ∈ B, orderOf x = p ∧ ∀ e ∈ E, e * x = x * e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : MulDistribMulAction ↥E ↥B := Subgroup.conjMulDistribMulActionOfLeNormalizer E B hEB
  let C : Subgroup G := B ⊓ Subgroup.centralizer (E : Set G)
  have hcard : Nat.card (MulAction.fixedPoints ↥E ↥B) = Nat.card ↥C := by
    refine Nat.card_congr
      { toFun := fun b => ⟨(b.1 : G), b.1.2, ?_⟩
        invFun := fun c => ⟨⟨(c : G), c.2.1⟩, ?_⟩
        left_inv := fun b => rfl
        right_inv := fun c => rfl }
    · show (b.1 : G) ∈ Subgroup.centralizer (E : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h := MulAction.mem_fixedPoints.1 b.2 ⟨e, he⟩
      have h' := congrArg Subtype.val h
      change (e : G) * (b.1 : G) * (e : G)⁻¹ = (b.1 : G) at h'
      calc e * (b.1 : G) = (e * (b.1 : G) * e⁻¹) * e := by group
        _ = (b.1 : G) * e := by rw [h']
    · refine MulAction.mem_fixedPoints.2 fun e => ?_
      apply Subtype.ext
      change (e : G) * (c : G) * (e : G)⁻¹ = (c : G)
      have h := Subgroup.mem_centralizer_iff.1 c.2.2 e e.2
      calc (e : G) * (c : G) * (e : G)⁻¹ = ((c : G) * e) * (e : G)⁻¹ := by rw [h]
        _ = (c : G) := by group
  have hmod := hE.card_modEq_card_fixedPoints ↥B
  rw [hcard] at hmod
  have hpC : p ∣ Nat.card ↥C := by
    have h1 : Nat.card ↥B ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hpB
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h1)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hpC
  refine ⟨(x : G), x.2.1, ?_, fun e he => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hx
  · exact Subgroup.mem_centralizer_iff.1 x.2.2 e he

omit [Finite G] in
theorem le_normalizer_of_forall_conj_mem {E T : Subgroup G}
    (h : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) : E ≤ Subgroup.normalizer (T : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h e he x hx, fun hx => ?_⟩
  have := h e⁻¹ (E.inv_mem he) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem commutator_le_of_forall_conj_mem {E T : Subgroup G}
    (h : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) : ⁅T, E⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro g hg e he
  rw [commutatorElement_def]
  have := h e he g⁻¹ (T.inv_mem hg)
  have h2 : g * e * g⁻¹ * e⁻¹ = g * (e * g⁻¹ * e⁻¹) := by group
  rw [h2]
  exact T.mul_mem hg this

theorem exists_two_subgroup_of_borel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E Y : Subgroup G}
    [hE : IsElementaryAbelian p ↥E]
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) (hB : BorelFacts p Y) :
    ∃ S : Subgroup G, S ≤ Y ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, E⁆ := by
  classical
  obtain ⟨hpY, hM1, hM3⟩ := hB
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := IsElementaryAbelian.isPGroup p ↥E
  let : MulDistribMulAction ↥E ↥Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  obtain ⟨T, hT⟩ := hEp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥Y) hM1
  have hTinv : ∀ e ∈ E, ∀ t : ↥Y, t ∈ (T : Subgroup ↥Y) →
      ∃ t' : ↥Y, t' ∈ (T : Subgroup ↥Y) ∧ (t' : G) = e * t * e⁻¹ := by
    intro e he t ht
    have h1 : (⟨e, he⟩ : ↥E) • T = T := MulAction.mem_fixedPoints.1 hT ⟨e, he⟩
    have h2 : (⟨e, he⟩ : ↥E) • (T : Subgroup ↥Y) = (T : Subgroup ↥Y) :=
      congrArg (fun P : Sylow 2 ↥Y => (P : Subgroup ↥Y)) h1
    have h3 : (⟨e, he⟩ : ↥E) • t ∈ (⟨e, he⟩ : ↥E) • (T : Subgroup ↥Y) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨t, ht, rfl⟩
    rw [h2] at h3
    exact ⟨_, h3, rfl⟩
  set T' : Subgroup G := (T : Subgroup ↥Y).map Y.subtype with hT'
  have hT'Y : T' ≤ Y := Subgroup.map_subtype_le _
  have hT'inv : ∀ e ∈ E, ∀ x ∈ T', e * x * e⁻¹ ∈ T' := by
    intro e he x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨t', ht', h⟩ := hTinv e he t ht
    exact Subgroup.mem_map.2 ⟨t', ht', h⟩
  have hET' : E ≤ Subgroup.normalizer (T' : Set G) := le_normalizer_of_forall_conj_mem hT'inv
  have hT'2 : IsPGroup 2 ↥T' := (T.isPGroup').map Y.subtype
  obtain ⟨x, hxY, hxo, hxc⟩ :=
    exists_orderOf_eq_of_isPGroup_normalizes hp hEY hEp hpY
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hxE : x ∈ E := by
    have hz : IsElementaryAbelian p ↥(Subgroup.zpowers x) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro e he
      exact hxc e he
    have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hcent
    have hF : E ⊔ Subgroup.zpowers x = E := hEmax _ hsup le_sup_left
    rw [← hF]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxo' : orderOf (⟨x, hxY⟩ : ↥Y) = p := by
    rw [← hxo, Subgroup.orderOf_mk]
  obtain ⟨t, htT, hxt⟩ := hM3 T ⟨x, hxY⟩ hxo'
  have htG : (t : G) ∈ T' := Subgroup.mem_map.2 ⟨t, htT, rfl⟩
  have hcomm : ⁅(t : G), x⁆ ≠ 1 := by
    intro h
    apply hxt
    apply Subtype.ext
    have := (commutatorElement_eq_one_iff_mul_comm).1 h
    exact this.symm
  refine ⟨⁅T', E⁆, ?_, ?_, ?_, ?_, ?_⟩
  · exact (commutator_le_of_forall_conj_mem hT'inv).trans hT'Y
  · intro h
    apply hcomm
    have := Subgroup.commutator_mem_commutator htG hxE
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · exact hT'2.to_le (commutator_le_of_forall_conj_mem hT'inv)
  ·
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : T'.map (MulAut.conj e).toMonoidHom = T' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hET' he)
    have h2 : E.map (MulAut.conj e).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer he)
    have h3 := Subgroup.map_commutator T' E (MulAut.conj e).toMonoidHom
    have h4 : (⁅T', E⁆).map (MulAut.conj e).toMonoidHom = ⁅T', E⁆ := by
      rw [h3]
      exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆) h1 h2
    exact h4
  ·
    have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥T') := by
      obtain ⟨a, ha⟩ := hEp.exists_card_eq
      obtain ⟨b, hb⟩ := hT'2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hsolv : Group.IsSolvable ↥T' := by
      have : Group.IsNilpotent ↥T' := hT'2.isNilpotent
      infer_instance
    exact (HNB.commutator_double_eq_self_of_coprime_solvable E T' hET' hcop hsolv).symm

end CFSG.RankThree.PartOne.K159
