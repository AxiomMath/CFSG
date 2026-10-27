module

public import CFSG.GroupTheory.WielandtProductFinal
public import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin

namespace H

namespace Tri

open scoped Pointwise

variable {G : Type*} [Group G]

theorem coe_sup_eq_mul {H L : Subgroup G} (h : (H : Set G) * L = L * H) :
    ((H ⊔ L : Subgroup G) : Set G) = (H : Set G) * L := by
  rw [Subgroup.sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) Subgroup.subset_closure
  induction hx using Subgroup.closure_induction'' with
  | one => exact ⟨1, H.one_mem, 1, L.one_mem, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    have : y⁻¹ * x⁻¹ ∈ (L : Set G) * H := Set.mul_mem_mul (L.inv_mem hy) (H.inv_mem hx)
    rw [← h] at this
    simpa using this
  | mul x' x'' _ _ hx hx' =>
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hx
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hx'
    have : y₁ * x₂ ∈ (L : Set G) * H := Set.mul_mem_mul hy₁ hx₂
    rw [← h] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    have hab' : a * b = y₁ * x₂ := hab
    refine ⟨x₁ * a, H.mul_mem hx₁ ha, b * y₂, L.mul_mem hb hy₂, ?_⟩
    calc x₁ * a * (b * y₂) = x₁ * (a * b) * y₂ := by group
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [hab']
      _ = x₁ * y₁ * (x₂ * y₂) := by group

theorem card_sup_eq_mul {H L : Subgroup G} (h : (H : Set G) * L = L * H) (hinf : H ⊓ L = ⊥) :
    Nat.card ↥(H ⊔ L) = Nat.card H * Nat.card L := by
  have hsup := coe_sup_eq_mul h
  let f : ↥H × ↥L → ↥(H ⊔ L) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have e : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have hmem : (q.1 : G)⁻¹ * p.1 ∈ H ⊓ L := by
        refine ⟨H.mul_mem (H.inv_mem q.1.2) p.1.2, ?_⟩
        have : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
        rw [this]
        exact L.mul_mem q.2.2 (L.inv_mem p.2.2)
      rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h1 : p.1 = q.1 := Subtype.ext hmem.symm
      have h2 : p.2 = q.2 := by
        apply Subtype.ext
        rw [h1] at e
        exact mul_left_cancel e
      exact Prod.ext h1 h2
    · have hx : (x : G) ∈ ((H ⊔ L : Subgroup G) : Set G) := x.2
      rw [hsup] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem subgroupOf_mul_comm {Q H L : Subgroup G} (hH : H ≤ Q) (hL : L ≤ Q)
    (h : (H : Set G) * L = L * H) :
    ((H.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) * (L.subgroupOf Q : Subgroup ↥Q) =
      (L.subgroupOf Q : Subgroup ↥Q) * (H.subgroupOf Q : Subgroup ↥Q) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have : (a : G) * b ∈ (L : Set G) * H := h ▸ Set.mul_mem_mul ha hb
    obtain ⟨c, hc, d, hd, hcd⟩ := this
    exact ⟨⟨c, hL hc⟩, hc, ⟨d, hH hd⟩, hd, Subtype.ext hcd⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    have : (a : G) * b ∈ (H : Set G) * L := h.symm ▸ Set.mul_mem_mul ha hb
    obtain ⟨c, hc, d, hd, hcd⟩ := this
    exact ⟨⟨c, hH hc⟩, hc, ⟨d, hL hd⟩, hd, Subtype.ext hcd⟩

theorem exists_normal_or_le_normalizer [Finite G] {B U : Subgroup G}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hU : IsPGroup 2 U)
    (hBU : (B : Set G) * U = U * B) :
    (∃ O : Subgroup G, O ≠ ⊥ ∧ O ≤ U ∧ B ⊔ U ≤ Subgroup.normalizer (O : Set G)) ∨
      U ≤ Subgroup.normalizer (B : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := B ⊔ U with hQ
  have hBQ : B ≤ Q := le_sup_left
  have hUQ : U ≤ Q := le_sup_right
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card U) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
  have hinf : B ⊓ U = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcardQ : Nat.card Q = Nat.card B * Nat.card U := card_sup_eq_mul hBU hinf
  set B' := B.subgroupOf Q with hB'
  set U' := U.subgroupOf Q with hU'
  have hB'card : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
  have hU'p : IsPGroup 2 U' := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUQ).symm
  have hB'comm : IsMulCommutative ↥B' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hBab _ a.2 _ b.2))⟩⟩
  have hsolv : Group.IsSolvable ↥Q := by
    refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product B' U'
      (CommGroup.isNilpotent) hU'p.isNilpotent (by rw [hB'card, hU'card]; exact hcop) ?_
    intro g
    have hg : (g : G) ∈ ((B ⊔ U : Subgroup G) : Set G) := g.2
    rw [coe_sup_eq_mul hBU] at hg
    obtain ⟨b, hb, u, hu, hbu⟩ := hg
    exact ⟨⟨b, hBQ hb⟩, hb, ⟨u, hUQ hu⟩, hu, Subtype.ext hbu.symm⟩
  have hidx : U'.index = Nat.card B := by
    have h := U'.card_mul_index
    rw [hU'card, hcardQ, mul_comm (Nat.card B)] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥U)) h
  have hidx2 : ¬ 2 ∣ U'.index := by
    rw [hidx, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hBodd
  let Usyl : Sylow 2 ↥Q := hU'p.toSylow hidx2
  by_cases hP : CFSG.pCore 2 ↥Q = ⊥
  ·
    right
    set F := CFSG.fittingSubgroup ↥Q with hF
    have hFodd : ¬ 2 ∣ Nat.card F := by
      intro h2
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥F))
      have hle := Sylow.map_le_pCore (CFSG.fittingSubgroup_normal) (CFSG.fittingSubgroup_nilpotent)
        2 P
      rw [hP, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective] at hle
      have h1 : Nat.card ↥(P : Subgroup ↥F) = 1 := by rw [hle, Subgroup.card_bot]
      rw [Sylow.card_eq_multiplicity] at h1
      have h0 : (Nat.card ↥F).factorization 2 = 0 := by
        by_contra hne
        have : 2 ≤ 2 ^ (Nat.card ↥F).factorization 2 :=
          Nat.le_self_pow hne 2
        omega
      have h3 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
      omega
    have hB'odd : Odd (Nat.card B') := hB'card ▸ hBodd
    have hFB : F ≤ B' := by
      have h1 : F.relIndex (B' ⊔ F) * Nat.card ↥(F ⊓ (B' ⊔ F)) = Nat.card ↥(B' ⊔ F) :=
        Subgroup.relIndex_mul_card F (B' ⊔ F)
      rw [Subgroup.relIndex_sup_right, inf_of_le_left le_sup_right] at h1
      have h2 : F.relIndex B' * Nat.card ↥(F ⊓ B') = Nat.card B' :=
        Subgroup.relIndex_mul_card F B'
      have hodd1 : Odd (F.relIndex B') := by
        rw [← h2] at hB'odd
        exact Nat.Odd.of_mul_left hB'odd
      have hodd2 : Odd (Nat.card ↥(B' ⊔ F)) := by
        rw [← h1]
        exact hodd1.mul (Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd]))
      have hdvd : Nat.card ↥(B' ⊔ F) ∣ Nat.card B' * 2 ^ k := by
        rw [hB'card, ← hk, ← hcardQ]
        exact Subgroup.card_subgroup_dvd_card _
      have hdvd' : Nat.card ↥(B' ⊔ F) ∣ Nat.card B' :=
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd2)).dvd_of_dvd_mul_right hdvd
      have heq : B' = B' ⊔ F :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (Nat.le_of_dvd Nat.card_pos hdvd')
      rw [heq]
      exact le_sup_right
    have hB'C : B' ≤ Subgroup.centralizer (F : Set ↥Q) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact Subtype.ext (hBab _ (hFB hf) _ hb)
    have hB'F : B' = F :=
      le_antisymm (hB'C.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
        hsolv)) hFB
    have hnorm : B'.Normal := by rw [hB'F]; infer_instance
    exact hUQ.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hBQ).mp hnorm)
  ·
    left
    set O := (CFSG.pCore 2 ↥Q).map Q.subtype with hO
    have hOQ : O ≤ Q := Subgroup.map_subtype_le _
    have hPU : CFSG.pCore 2 ↥Q ≤ U' :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Q)).le_sylow_of_normal Usyl
    refine ⟨O, ?_, ?_, ?_⟩
    · rw [hO, Ne, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]
      exact hP
    · rintro _ ⟨x, hx, rfl⟩
      exact hPU hx
    · have hOsub : O.subgroupOf Q = CFSG.pCore 2 ↥Q :=
        Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
      have hnorm : (O.subgroupOf Q).Normal := by rw [hOsub]; infer_instance
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOQ).mp hnorm

theorem le_of_commute [Finite G] {B E P : Subgroup G} (hE : E ≤ Subgroup.normalizer (B : Set G))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : 4 ≤ Nat.card E)
    (hBodd : Odd (Nat.card B)) (h : ∀ e ∈ E, e ≠ 1 → ∀ b ∈ B, e * b = b * e → b ∈ P) :
    B ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥E :=
    { is_comm := ⟨fun a b => Subtype.ext (hEab _ a.2 _ b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hE2 _ g.2) }
  let _ : MulDistribMulAction ↥E ↥B := MulDistribMulAction.compHom ↥B (Subgroup.inclusion hE)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := ↥E) (H := ↥B)
    (by norm_num; exact hE4) (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hBodd)
  have hle : (⨆ (a : ↥E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥B) ≤
      P.comap B.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have hc : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    refine h a a.2 ha1 x x.2 ?_
    calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
      _ = x * a := by rw [hc]
  intro b hb
  have hmem : (⟨b, hb⟩ : ↥B) ∈
      ⨆ (a : ↥E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥B := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

end Tri

end H

end CFSG.Quasithin
