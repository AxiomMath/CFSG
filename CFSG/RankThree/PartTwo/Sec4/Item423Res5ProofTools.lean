module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaFunctor
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

namespace Res423Five

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Abstract

variable {G : Type} [Group G]

theorem commutator_eq_bot_of_normalizes {S N Θ : Subgroup G} (hS : IsQuasisimple S)
    (hSN : S ≤ N) (hNS : N ≤ Subgroup.normalizer (S : Set G))
    (hNΘ : N ≤ Subgroup.normalizer (Θ : Set G)) (hΘN : Θ ≤ Subgroup.normalizer (N : Set G))
    (hΘ : Group.IsSolvable Θ) : ⁅S, Θ⁆ = ⊥ := by
  have hSp : Group.IsPerfect S := hS.1
  have hNM : ∀ n ∈ N, ∀ m ∈ Θ ⊓ N, n * m * n⁻¹ ∈ Θ ⊓ N := fun n hn m hm =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hNΘ hn) m).mp hm.1,
      N.mul_mem (N.mul_mem hn hm.2) (N.inv_mem hn)⟩
  have h1 : ⁅S, Θ ⊓ N⁆ ≤ S ⊓ (Θ ⊓ N) := by
    rw [Subgroup.commutator_le]
    intro s hs m hm
    rw [commutatorElement_def]
    refine ⟨?_, (Θ ⊓ N).mul_mem (hNM s (hSN hs) m hm) ((Θ ⊓ N).inv_mem hm)⟩
    have h2 : m * s⁻¹ * m⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hNS hm.2) s⁻¹).mp (S.inv_mem hs)
    have h3 := S.mul_mem hs h2
    simpa [mul_assoc] using h3
  have h2 : S ⊓ (Θ ⊓ N) ≤ Subgroup.centralizer (S : Set G) := by
    have hnorm : ((Θ ⊓ N).subgroupOf S).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using hNM g (hSN g.2) x hx⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hS hnorm with htop | hcen
    · exfalso
      have hSΘ : S ≤ Θ := fun s hs => by
        have hmem : (⟨s, hs⟩ : S) ∈ (Θ ⊓ N).subgroupOf S := htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hmem).1
      have : Group.IsSolvable S :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hSΘ)
      have : Nontrivial S := CFSG.LocalCores.isQuasisimple_nontrivial hS
      exact Group.IsPerfect.not_isSolvable (G := S) inferInstance
    · rintro x ⟨hxS, hxM⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hx : (⟨x, hxS⟩ : S) ∈ (Θ ⊓ N).subgroupOf S := Subgroup.mem_subgroupOf.mpr hxM
      have h4 := Subgroup.mem_center_iff.mp (hcen hx) ⟨s, hs⟩
      exact congrArg Subtype.val h4
  have h3 : ⁅S, Θ ⊓ N⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator hSp
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h1.trans h2
  have h4 : ⁅S, Θ⁆ ≤ Θ ⊓ N := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [commutatorElement_def]
    refine ⟨Θ.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNΘ (hSN hs)) t).mp ht) (Θ.inv_mem ht),
      ?_⟩
    have h5 : t * s⁻¹ * t⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hΘN ht) s⁻¹).mp (N.inv_mem (hSN hs))
    have h6 := N.mul_mem (hSN hs) h5
    simpa [mul_assoc] using h6
  apply CFSG.LocalCores.perfect_double_commutator hSp
  rw [eq_bot_iff, ← h3, Subgroup.commutator_comm S (Θ ⊓ N)]
  exact Subgroup.commutator_mono h4 le_rfl

theorem commutator_eq_bot_of_coprime {Q B I : Subgroup G}
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime (Nat.card B) (Nat.card Q))
    (hI : ⁅Q, B⁆ ≤ I) (hQI : Q ⊓ I ≤ Subgroup.centralizer (B : Set G)) : ⁅Q, B⁆ = ⊥ := by
  have h1 : ⁅Q, B⁆ ≤ Q ⊓ I := by
    refine le_inf ?_ hI
    rw [Subgroup.commutator_le]
    intro x hx b hb
    rw [commutatorElement_def]
    have h2 : b * x⁻¹ * b⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hBQ hb) x⁻¹).mp (Q.inv_mem hx)
    have h3 := Q.mul_mem hx h2
    simpa [mul_assoc] using h3
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq' hBQ hcop,
    eq_bot_iff]
  calc ⁅⁅Q, B⁆, B⁆ ≤ ⁅Q ⊓ I, B⁆ := Subgroup.commutator_mono h1 le_rfl
    _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQI

end Abstract

section Types

variable {G : Type} [Group G]

@[expose] def TypeOneAt (Δ B : Subgroup G) (b : G) : Prop :=
  ∀ d ∈ Δ, d * b = b * d → Nat.Coprime 3 (orderOf d) → ∀ x ∈ B, d * x = x * d

@[expose] def TypeTwoAt (I B : Subgroup G) (b : G) (S : Subgroup G) : Prop :=
  IsQuasisimple S ∧ S ≤ I ∧ S ≤ Subgroup.centralizer {b} ∧
    (∀ x ∈ I, x * b = b * x → x ∈ Subgroup.normalizer (S : Set G)) ∧
      B ≤ Subgroup.zpowers b ⊔ S

variable [Finite G]

theorem theta_le_centralizer_of_typeTwoAt {I B S : Subgroup G} {b : G} (hI : I.Normal)
    (hS : TypeTwoAt I B b S) :
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.centralizer (S : Set G) := by
  obtain ⟨hSq, hSI, hSb, hnorm, -⟩ := hS
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set U := inSubgroup (aschbacherSolvableCore 3) C with hU
  have hUC : U ≤ C := Res423Two.inSubgroup_theta_le C
  have hCU : C ≤ Subgroup.normalizer (U : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun hu => Res423Two.conj_mem_inSubgroup_theta' hc hu
    · intro hu
      have := Res423Two.conj_mem_inSubgroup_theta' (C.inv_mem hc) hu
      simpa [mul_assoc] using this
  have hcomm : ⁅S, U⁆ = ⊥ := by
    refine commutator_eq_bot_of_normalizes hSq (le_inf hSI hSb) (fun x hx => ?_)
      (fun x hx => hCU hx.2) (fun u hu => ?_) (Res423Two.isSolvable_inSubgroup_theta C)
    · exact hnorm x hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact ⟨hI.conj_mem y hy.1 u, C.mul_mem (C.mul_mem (hUC hu) hy.2) (C.inv_mem (hUC hu))⟩
      · intro hy
        refine ⟨?_, ?_⟩
        · have := hI.conj_mem _ hy.1 u⁻¹
          simpa [mul_assoc] using this
        · have := C.mul_mem (C.mul_mem (C.inv_mem (hUC hu)) hy.2) (hUC hu)
          simpa [mul_assoc] using this
  rw [Subgroup.commutator_comm] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem le_zpowers_sup {B : Subgroup G} (hB3 : ∀ x ∈ B, x ^ 3 = 1) (hB9 : Nat.card B = 9)
    {b b' : G} (hb : b ∈ B) (hb1 : b ≠ 1) (hb'B : b' ∈ B) (hb' : b' ∉ Subgroup.zpowers b) :
    B ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers b' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.zpowers b ⊔ Subgroup.zpowers b' with hH
  have hHB : H ≤ B := sup_le (Subgroup.zpowers_le.mpr hb) (Subgroup.zpowers_le.mpr hb'B)
  have hob : orderOf b = 3 := orderOf_eq_prime (hB3 b hb) hb1
  have h3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have hdvd : Nat.card H ∣ 9 := hB9 ▸ Subgroup.card_dvd_of_le hHB
  have h3H : 3 ∣ Nat.card H := h3 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card H ≠ 3 := by
    intro h
    apply hb'
    have heq : Subgroup.zpowers b = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, h3])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
  have h9 : Nat.card H = 9 := by
    have hle : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card H <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hHB (by rw [h9, hB9])).ge

theorem commutator_theta_eq_bot_of_typeTwoAt {I B S : Subgroup G} {b : G} (hI : I.Normal)
    (hS : TypeTwoAt I B b S) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)), B⁆ = ⊥ := by
  have hle := theta_le_centralizer_of_typeTwoAt hI hS
  obtain ⟨-, -, -, -, hBle⟩ := hS
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  have hub : u ∈ Subgroup.centralizer ({b} : Set G) := Res423Two.inSubgroup_theta_le _ hu
  have hcen : Subgroup.zpowers b ⊔ S ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun s hs => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hub).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hle hu) s hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcen (hBle hx))

theorem commutator_theta_eq_bot_of_typeOneAt {Δ B : Subgroup G} {b : G} (hΔ : Δ.Normal)
    (hBΔ : B ≤ Δ) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : IsPGroup 3 B) (hb : b ∈ B)
    (h1 : TypeOneAt Δ B b) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)), B⁆ = ⊥ := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set U := inSubgroup (aschbacherSolvableCore 3) C with hU
  have hBC : B ≤ C := fun x hx => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (hBc b hb x hx).symm
  have hU3 := Res423Two.not_three_dvd_card_inSubgroup_theta C
  refine commutator_eq_bot_of_coprime (I := Δ) (fun x hx => ?_) ?_ ?_ ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun hu => Res423Two.conj_mem_inSubgroup_theta' (hBC hx) hu
    · intro hu
      have := Res423Two.conj_mem_inSubgroup_theta' (C.inv_mem (hBC hx)) hu
      simpa [mul_assoc] using this
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU3)
  · rw [Subgroup.commutator_le]
    intro u _ x hx
    rw [commutatorElement_def]
    exact Δ.mul_mem (hΔ.conj_mem x (hBΔ hx) u) (Δ.inv_mem (hBΔ hx))
  · rintro d ⟨hdU, hdΔ⟩
    have hdb : d * b = b * d := Subgroup.mem_centralizer_singleton_iff.mp
      (Res423Two.inSubgroup_theta_le C hdU)
    have hcop : Nat.Coprime 3 (orderOf d) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro h3
      exact hU3 (h3.trans (Subgroup.orderOf_dvd_natCard U hdU))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h1 d hdΔ hdb hcop x hx).symm

theorem thetaAlpha_eq_bot_of_types {I Δ B : Subgroup G} (hI : I.Normal) (hΔ : Δ.Normal)
    (hBΔ : B ≤ Δ) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : IsPGroup 3 B)
    (hcases : ∀ b ∈ B, b ≠ 1 → TypeOneAt Δ B b ∨ ∃ S, TypeTwoAt I B b S)
    (hT : ∀ y : G, (∀ b ∈ B, b ≠ 1 → ∀ S, TypeTwoAt I B b S → ∀ s ∈ S, y * s = s * y) →
      y = 1) :
    thetaAlpha 3 B = ⊥ := by
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    rcases hcases b hb hb1 with h1 | ⟨S, hS⟩
    · rw [commutator_theta_eq_bot_of_typeOneAt hΔ hBΔ hBc hBp hb h1]
    · rw [commutator_theta_eq_bot_of_typeTwoAt hI hS]
  have hTb : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine hT y fun b hb hb1 S hS s hs => ?_
    have hyb : y ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hy b) hb) hb1
    exact (Subgroup.mem_centralizer_iff.mp (theta_le_centralizer_of_typeTwoAt hI hS hyb) s
      hs).symm
  rw [thetaAlpha, hJ, hTb, sup_bot_eq]

end Types

theorem thetaAlpha_subgroupOf_eq_bot_of_map {M M' : Type} [Group M] [Group M'] [Finite M]
    (ρ : M →* M') (hρ : Function.Injective ρ) (B Y : Subgroup M)
    (h : thetaAlpha 3 ((B.map ρ).subgroupOf (Y.map ρ)) = ⊥) :
    thetaAlpha 3 (B.subgroupOf Y) = ⊥ := by
  let ψ := Y.equivMapOfInjective ρ hρ
  have : Finite ↥(Y.map ρ) := Finite.of_equiv _ ψ.toEquiv
  have hψ : (B.subgroupOf Y).map ψ.toMonoidHom = (B.map ρ).subgroupOf (Y.map ρ) := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
    · intro hz
      obtain ⟨y, rfl⟩ := ψ.surjective z
      refine ⟨y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hz
      have : x = y := hρ hxy
      exact this ▸ hx
  have h1 := thetaAlpha_map_equiv Nat.prime_three ψ (B.subgroupOf Y)
  rw [hψ, h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp h1

section Fix

variable {X : Type} [Group X]

theorem fix_of_mul_conj_eq (hZ : Subgroup.center X = ⊥) {t : MulAut X} {x : X}
    (h : t * MulAut.conj x = MulAut.conj x * t) : t x = x := by
  apply Res423Two.conj_injective_of_center hZ
  rw [← Res423Two.mulAut_mul_conj_mul_inv, h]
  group

end Fix

end Res423Five

end CFSG.RankThree.PartTwo.Sec4
