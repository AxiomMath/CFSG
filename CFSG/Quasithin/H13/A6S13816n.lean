module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoA
import CFSG.Quasithin.H13.NQRigidWMGroups

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

namespace FFTwo

open scoped commutatorElement

section Generic

variable {Ω : Type} [Group Ω]

private theorem ff_eq_of_normal_of_isQuasisimple {K E : Subgroup Ω} (hKE : K ≤ E)
    (hn : ∀ x ∈ E, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hE : CFSG.IsQuasisimple ↥E) : K = E := by
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn g g.2 k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hE) (K.subgroupOf E) with hc | htop
  · exfalso
    refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm hKE (fun e he => ?_)
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

private theorem ff_eq_or_eq_of_normal [Finite Ω] {J L₁ L₂ K : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hL₁J : L₁ ≤ J) (hL₂J : L₂ ≤ J) (h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hKJ : K ≤ J) (hKn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K = L₁ ∨ K = L₂ := by
  have hKL : K ≤ L₁ ⊔ L₂ :=
    (B1Red.perfect_le_oTwoUpper' hKJ hK.1).trans (oTwoUpper_le_of_pow_mem h2)
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le hL₁J hL₂J
  rcases InternalSec.le_or_le_of_sup_eq rfl hcomm hKL
    (fun x hx k hk => hKn x (hLJ hx) k hk) hK with h | h
  · exact Or.inl
      (ff_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₁J hx) k hk) hK hq₁)
  · exact Or.inr
      (ff_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₂J hx) k hk) hK hq₂)

private theorem ff_le_of_perfect_of_isSolvable {A B P : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPAB : P ≤ A ⊔ B) (hP : Group.IsPerfect ↥P)
    (hB : Group.IsSolvable ↥B) : P ≤ A := by
  set H := A ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  set N : Subgroup ↥H := A.subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc g g.2 n hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion hBH)) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hc)).1 hh
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' N ⟨b, hBH hb⟩ = QuotientGroup.mk' N ⟨a * b, hh⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    show (b⁻¹ * (a * b) : Ω) ∈ A
    rw [hc a ha b hb, inv_mul_cancel_left]
    exact ha
  have : Group.IsSolvable (↥H ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hPH : P ≤ H := hPAB
  let φ : ↥P →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hPH)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro p hp
  have h1 : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hr, Subgroup.mem_bot] at h1
  have h2 : (⟨p, hPH hp⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

private theorem ff_isSolvable_of_card_six {H : Type*} [Group H] (h : Nat.card H = 6) :
    Group.IsSolvable H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num : 3 ∣ Nat.card H)
  set P := Subgroup.zpowers x with hP
  have hPc : Nat.card ↥P = 3 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 2 := by
    have := P.card_mul_index
    rw [hPc, h] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  have hQc : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcyc : IsCyclic (H ⧸ P) := isCyclic_of_prime_card hQc
  exact Group.isSolvable_of_subgroup_quotient P

end Generic

section Orders

private theorem ff_card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

private theorem ff_card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

end Orders

section Factors

variable {Ω : Type} [Group Ω]

private theorem ff_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

private theorem ff_isQuasisimple_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : CFSG.IsQuasisimple Q := by
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := h }
    exact hp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect Q)

private theorem ff_fac_of_simple [Finite Ω] {G : Subgroup Ω} (hs : IsSimpleGroup ↥G)
    (hp : ¬ (Nat.card ↥G).Prime) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5))) :=
  ⟨G, le_rfl, fun _ hg _ hk => G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg),
    ff_isQuasisimple_of_simple hp, Or.inl rfl⟩

private theorem ff_fac_of_perm_five {G : Subgroup Ω} (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5))) := by
  set f : Equiv.Perm (Fin 5) →* Ω := G.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := G.subtype_injective.comp e.symm.injective
  have hcard : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hA5 : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    ff_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have e' := (alternatingGroup (Fin 5)).equivMapOfInjective f hfinj
  refine ⟨(alternatingGroup (Fin 5)).map f, ?_, ?_, ?_, Or.inr ⟨e⟩⟩
  · rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  · rintro g hg _ ⟨a, ha, rfl⟩
    have hg' : f (e ⟨g, hg⟩) = g := by simp [hf]
    refine ⟨e ⟨g, hg⟩ * a * (e ⟨g, hg⟩)⁻¹, Subgroup.Normal.conj_mem inferInstance a ha _, ?_⟩
    rw [map_mul, map_mul, map_inv, hg']
  · exact B1Red.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e'.symm
        (B1Red.isQuasisimple_to_open hA5))

private theorem ff_fac_of_factorList [Finite Ω] {G : Subgroup Ω} (h : B56FactorList ↥G) :
    (∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
        (K = G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5)))) ∨
      (Group.IsSolvable ↥G ∧ 3 ∣ Nat.card ↥G) := by
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm, hmodd, hF, ⟨e⟩⟩
  · have hcard : Nat.card ↥G = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, ff_card_statedSL_two]
    by_cases hn1 : n = 1
    · subst hn1
      right
      have h6 : Nat.card ↥G = 6 := by rw [hcard, hF]; norm_num
      exact ⟨ff_isSolvable_of_card_six h6, by rw [h6]; norm_num⟩
    · left
      have : CharP F 2 := ff_charP_two hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hs : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      have : IsSimpleGroup ↥G := e.isSimpleGroup
      refine ff_fac_of_simple this ?_
      rw [hcard]
      have h16 : 16 ≤ Nat.card F ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h4 2
      exact Nat.not_prime_mul (by omega) (by omega)
  · obtain ⟨e⟩ := he
    exact Or.inl (ff_fac_of_perm_five e)
  · left
    have hcard : Nat.card ↥G =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, ff_card_statedSL_three]
    have hs : IsSimpleGroup ↥(StatedSL 3 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hmodd
    have : IsSimpleGroup ↥G := e.isSimpleGroup
    refine ff_fac_of_simple this ?_
    rw [hcard]
    have hq : 2 ≤ Nat.card F := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h8 : 8 ≤ Nat.card F ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    have h4 : 4 ≤ Nat.card F ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
    exact Nat.not_prime_mul (by omega) (by
      have : 3 * 7 ≤ (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)

end Factors
section Cases

variable {V : Type} [CommGroup V] [Finite V]

private structure CompData (J L₁ L₂ : Subgroup (MulAut V)) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  le₁ : L₁ ≤ J
  le₂ : L₂ ≤ J
  norm : ∀ x ∈ J, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂
  two : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂
  inf : L₁ ⊓ L₂ = ⊥
  ne₁ : Nat.card ↥L₁ ≠ 168
  ne₂ : Nat.card ↥L₂ ≠ 168
  big : 360 < Nat.card ↥L₁ * Nat.card ↥L₂

variable {J L₁ L₂ : Subgroup (MulAut V)}

omit [Finite V] in
private theorem card_mul_le_card_sup (hinf : L₁ ⊓ L₂ = ⊥) [Finite ↥(L₁ ⊔ L₂)] :
    Nat.card ↥L₁ * Nat.card ↥L₂ ≤ Nat.card ↥(L₁ ⊔ L₂) := by
  rw [← Nat.card_prod]
  let f : ↥L₁ × ↥L₂ → ↥(L₁ ⊔ L₂) := fun p =>
    ⟨(p.1 : MulAut V) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  refine Nat.card_le_card_of_injective f fun p q h => ?_
  have h1 : (p.1 : MulAut V) * p.2 = q.1 * q.2 := congrArg Subtype.val h
  have h2 : (q.1 : MulAut V)⁻¹ * p.1 = q.2 * (p.2 : MulAut V)⁻¹ := by
    calc (q.1 : MulAut V)⁻¹ * p.1 = (q.1 : MulAut V)⁻¹ * (p.1 * p.2) * (p.2 : MulAut V)⁻¹ := by
          group
      _ = (q.1 : MulAut V)⁻¹ * (q.1 * q.2) * (p.2 : MulAut V)⁻¹ := by rw [h1]
      _ = q.2 * (p.2 : MulAut V)⁻¹ := by group
  have h3 : (q.1 : MulAut V)⁻¹ * p.1 ∈ L₁ ⊓ L₂ :=
    ⟨L₁.mul_mem (L₁.inv_mem q.1.2) p.1.2, h2 ▸ L₂.mul_mem q.2.2 (L₂.inv_mem p.2.2)⟩
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h3
  have h4 : (p.2 : MulAut V) = q.2 := by
    rw [← h3] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)

omit [Finite V] in
private theorem CompData.false_of_case1 (P : CompData J L₁ L₂)
    (hF : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : False := by
  set F := quasithinGenFitting J with hFdef
  have hFJ : F ≤ J := quasithinGenFitting_le J
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le P.le₁ P.le₂
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute P.comm
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hLJn : ((L₁ ⊔ L₂).subgroupOf J).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g g.2 n hn⟩
  have hcomp : ∀ {A : Subgroup (MulAut V)}, A ≤ L₁ ⊔ L₂ →
      (∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ A, x * k * x⁻¹ ∈ A) → CFSG.IsQuasisimple ↥A → A ≤ F := by
    intro A hAL hAn hAq
    have hA : (A.subgroupOf (L₁ ⊔ L₂)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hAn g g.2 n hn⟩
    have hsub : CFSG.Open.IsSubnormal A J :=
      CFSG.Open.IsSubnormal.step hAL hA
        (CFSG.Open.IsSubnormal.step hLJ hLJn (CFSG.Open.IsSubnormal.refl J))
    have hc : CFSG.Open.IsComponentOf A J :=
      ⟨hAL.trans hLJ, hsub, B1Red.isQuasisimple_to_open hAq⟩
    exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right
  have hL₁F : L₁ ≤ F := hcomp le_sup_left hL₁n P.q₁
  have hL₂F : L₂ ≤ F := hcomp le_sup_right hL₂n P.q₂
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hFJ g.2) n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hF) ((L₁ ⊔ L₂).subgroupOf F) with hcen | htop
  · refine InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb => ?_
    have h1 : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      hcen (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hL₁F hb⟩
    exact (congrArg Subtype.val h2).symm
  · have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := htop ▸ Subgroup.mem_top _
      exact this
    have h1 : L₁ = F := ff_eq_of_normal_of_isQuasisimple hL₁F
      (fun x hx k hk => hL₁n x (hFL hx) k hk) P.q₁ hF
    have h2 : L₂ = F := ff_eq_of_normal_of_isQuasisimple hL₂F
      (fun x hx k hk => hL₂n x (hFL hx) k hk) P.q₂ hF
    have h12 : L₁ = L₂ := h1.trans h2.symm
    exact InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb =>
      P.comm a ha b (h12 ▸ hb)

private theorem CompData.false_of_case4 (P : CompData J L₁ L₂) (h4 : B56Case4 J) : False := by
  obtain ⟨G₁, G₂, t, hJt, -, hcomm, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN := InternalSec.mem_normalizer_sup ht₁ ht₂
  have hsol : Group.IsSolvable ↥G₂ := by
    have := isCyclic_of_prime_card hc₂
    infer_instance
  have hle : ∀ {L : Subgroup (MulAut V)}, L ≤ J → CFSG.IsQuasisimple ↥L → L ≤ G₁ := by
    intro L hLJ hL
    have h1 : L ≤ ⁅J, J⁆ := InternalSec.le_commutator_of_perfect hLJ hL.1
    rw [hJt] at h1
    exact ff_le_of_perfect_of_isSolvable hcomm (h1.trans
      (InternalSec.commutator_le_of_zpowers htN)) hL.1 hsol
  have hLG : L₁ ⊔ L₂ ≤ G₁ := sup_le (hle P.le₁ P.q₁) (hle P.le₂ P.q₂)
  have h1 := card_mul_le_card_sup P.inf
  have h2 := Subgroup.card_le_of_le hLG
  have hcard : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have := P.big
  omega

private theorem CompData.false_of_case5 (P : CompData J L₁ L₂) (h5 : B56Case5 J) : False := by
  obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, -⟩ := h5
  have hs : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have hs' : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
  have hcard : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e₁.toEquiv, ff_card_statedSL_three, Nat.card_zmod]
    norm_num
  have hq : CFSG.IsQuasisimple ↥G₁ := ff_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hn₁ : ∀ x ∈ J, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := fun x hx g hg =>
    InternalSec.conj_mem_of_mem_sup_of_commute hc x (by rw [hsup]; exact hx) g hg
  rcases ff_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hG₁J hn₁ hq with h | h
  · exact P.ne₁ (by rw [← h, hcard])
  · exact P.ne₂ (by rw [← h, hcard])

omit [Finite V] in
private theorem ne_bot_of_isQuasisimple {L : Subgroup (MulAut V)} (hL : CFSG.IsQuasisimple ↥L) :
    L ≠ ⊥ := by
  intro hbot
  have : Nontrivial ↥L :=
    CFSG.ComponentClassification.Quasisimple.nontrivial (B1Red.isQuasisimple_to_open hL)
  have : Subsingleton ↥L := by rw [hbot]; infer_instance
  exact not_subsingleton ↥L ‹_›

private theorem CompData.case3 (P : CompData J L₁ L₂) (h3 : B56Case3 J) :
    ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V), L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧
      (∀ g ∈ G₁, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁) ∧ (∀ g ∈ G₂, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂) ∧
      G₁ ⊔ G₂ = J ∧
      G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ B56FactorList ↥G₁ ∧
      B56FactorList ↥G₂ ∧ fixV J ≤ W₁ ∧ fixV J ≤ W₂ ∧ XMod.IsInv ↥J W₁ ∧ XMod.IsInv ↥J W₂ ∧
      W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV J ∧ B56Piece G₁ W₁ (fixV J) ∧ B56Piece G₂ W₂ (fixV J) := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, hW₁, hW₂, hI₁, hI₂, hWsup, hWinf, hp₁,
    hp₂⟩ := h3
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have key : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → A ⊓ B = ⊥ →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B56FactorList ↥A →
      (L₁ ≤ A ∧ ∀ g ∈ A, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁) ∨
        (L₂ ≤ A ∧ ∀ g ∈ A, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂) := by
    intro A B hsupAB hinfAB hcAB hfA
    have hcBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcAB a ha b hb).symm
    have hAJ : A ≤ J := by rw [← hsupAB]; exact le_sup_left
    rcases ff_fac_of_factorList hfA with ⟨K, hKA, hKn, hKq, -⟩ | ⟨hsol, h3dvd⟩
    · have hKJn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
        intro x hx k hk
        have hx' : x ∈ A ⊔ B := by rw [hsupAB]; exact hx
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          (B19Aux.mem_sup_iff_of_le_normalizer
            (InternalSec.le_normalizer_of_commute hcAB)).1 hx'
        have hbk : b * k = k * b := (hcAB k (hKA hk) b hb).symm
        have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
          calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
            _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
            _ = a * k * a⁻¹ := by group
        rw [e]
        exact hKn a ha k hk
      rcases ff_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two (hKA.trans hAJ) hKJn
        hKq with h | h
      · subst h
        exact Or.inl ⟨hKA, hKn⟩
      · subst h
        exact Or.inr ⟨hKA, hKn⟩
    · exfalso
      have hJBA : J = B ⊔ A := by rw [← hsupAB, sup_comm]
      have hL₁B : L₁ ≤ B :=
        ff_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₁) P.q₁.1 hsol
      have hL₂B : L₂ ≤ B :=
        ff_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₂) P.q₂.1 hsol
      have hLB : L₁ ⊔ L₂ ≤ B := sup_le hL₁B hL₂B
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
      obtain ⟨e, he⟩ := P.two (x : MulAut V) (hAJ x.2)
      have hxe : (x : MulAut V) ^ 2 ^ e ∈ A ⊓ B := ⟨A.pow_mem x.2 _, hLB he⟩
      rw [hinfAB, Subgroup.mem_bot] at hxe
      have hord : orderOf (x : MulAut V) = 3 := by rw [Subgroup.orderOf_coe, hx]
      have hdvd : 3 ∣ 2 ^ e := hord ▸ orderOf_dvd_of_pow_eq_one hxe
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
  have hG₁ := key hsup hinf hc hf₁
  have hG₂ := key ((sup_comm _ _).trans hsup) ((inf_comm _ _).trans hinf) hc' hf₂
  rcases hG₁ with ⟨h1, n1⟩ | ⟨h1, n1⟩ <;> rcases hG₂ with ⟨h2, n2⟩ | ⟨h2, n2⟩
  · exfalso
    exact ne_bot_of_isQuasisimple P.q₁ (le_bot_iff.mp (hinf ▸ le_inf h1 h2))
  · exact ⟨G₁, G₂, W₁, W₂, h1, h2, n1, n2, hsup, hinf, hc, hf₁, hf₂, hW₁, hW₂, hI₁, hI₂, hWsup,
      hWinf, hp₁, hp₂⟩
  · exact ⟨G₂, G₁, W₂, W₁, h2, h1, n2, n1, (sup_comm _ _).trans hsup, (inf_comm _ _).trans hinf,
      hc', hf₂, hf₁, hW₂, hW₁, hI₂, hI₁, (sup_comm _ _).trans hWsup, (inf_comm _ _).trans hWinf,
      hp₂, hp₁⟩
  · exfalso
    exact ne_bot_of_isQuasisimple P.q₂ (le_bot_iff.mp (hinf ▸ le_inf h1 h2))

end Cases

section Main

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def TwoB56Gen (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V), L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧
    (∀ g ∈ G₁, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁) ∧ (∀ g ∈ G₂, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂) ∧
    G₁ ⊔ G₂ = ffJ X ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
    B56FactorList ↥G₁ ∧ B56FactorList ↥G₂ ∧ fixV (ffJ X) ≤ W₁ ∧ fixV (ffJ X) ≤ W₂ ∧
    XMod.IsInv ↥(ffJ X) W₁ ∧ XMod.IsInv ↥(ffJ X) W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧
    W₁ ⊓ W₂ = fixV (ffJ X) ∧ B56Piece G₁ W₁ (fixV (ffJ X)) ∧ B56Piece G₂ W₂ (fixV (ffJ X))

theorem twoB56Gen_of_ffModule (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (hτX : τ ∈ X) (hL₁X : L₁ ≤ X) (hL₂X : L₂ ≤ X)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂) (hinf : L₁ ⊓ L₂ = ⊥)
    (hne₁ : Nat.card ↥L₁ ≠ 168) (hne₂ : Nat.card ↥L₂ ≠ 168)
    (hbig : 360 < Nat.card ↥L₁ * Nat.card ↥L₂)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) (hB53 : B53Hyp (ffJ X)) :
    TwoB56Gen X L₁ L₂ := by
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hcomm hn hτ h2 hq₁ hq₂ hO2 hFF
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have P : CompData (ffJ X) L₁ L₂ :=
    ⟨hcomm, hq₁, hq₂, hL₁J, hL₂J, fun x hx l hl => hn x (hJX hx) l hl,
      fun x hx => h2 x (hJX hx), hinf, hne₁, hne₂, hbig⟩
  have hcases := h56 V hV (ffJ X) (InternalSec.ffJ_ne_bot_of_isFFModule hV hFF) hB53
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | h3 | h4 | h5
  · exact (P.false_of_case1 h1.1).elim
  · exact (InternalSec.not_le_perm_three hq₁ hL₁J e).elim
  · exact P.case3 h3
  · exact (P.false_of_case4 h4).elim
  · exact (P.false_of_case5 h5).elim

omit [Finite V] in
theorem commV_le_of_b56Piece {G : Subgroup (MulAut V)} {W C : Subgroup V}
    (h : B56Piece G W C) : commV G ≤ W := by
  rcases h with ⟨hW, -⟩ | ⟨hW, -⟩ | ⟨-, hc, -⟩
  · exact hW ▸ le_sup_left
  · exact hW ▸ le_sup_left
  · exact hc

omit [Finite V] in
theorem le_fixV_of_perfect {J G₂ L₂ : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
    (hperf : Group.IsPerfect ↥L₂) (hLG : L₂ ≤ G₂) (hGJ : G₂ ≤ J)
    (hI₁ : XMod.IsInv ↥J W₁) (hW₂ : commV G₂ ≤ W₂) (hWW : W₁ ⊓ W₂ ≤ fixV J) :
    W₁ ≤ fixV L₂ := by
  intro u hu
  have hmem : ∀ b ∈ L₂, (b : MulAut V) u * u⁻¹ ∈ fixV J := by
    intro b hb
    refine hWW ⟨W₁.mul_mem (hI₁ ⟨b, hGJ (hLG hb)⟩ u hu) (W₁.inv_mem hu), hW₂ ?_⟩
    exact Subgroup.subset_closure ⟨b, hLG hb, u, rfl⟩
  have hfix : ∀ b ∈ L₂, ∀ c ∈ fixV J, (b : MulAut V) c = c := fun b hb c hc =>
    hc b (hGJ (hLG hb))
  let f : ↥L₂ →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have h1 := hfix b b.2 _ (hmem b' b'.2)
        have e : ((b * b' : ↥L₂) : MulAut V) u * u⁻¹ =
            (b : MulAut V) ((b' : MulAut V) u * u⁻¹) * ((b : MulAut V) u * u⁻¹) := by
          rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e, h1, mul_comm] }
  have hf : f = 1 := by
    have hperf' : Group.IsPerfect ↥L₂ := hperf
    ext b
    obtain ⟨h1⟩ := hperf'
    have hb : b ∈ commutator ↥L₂ := h1 ▸ Subgroup.mem_top b
    have : f.ker = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← h1]
      exact Abelianization.commutator_subset_ker f
    have hk : b ∈ f.ker := this ▸ Subgroup.mem_top b
    exact hk
  intro b hb
  have h1 : f ⟨b, hb⟩ = 1 := by rw [hf]; rfl
  have h2 : (b : MulAut V) u * u⁻¹ = 1 := h1
  exact mul_inv_eq_one.mp h2

omit [Finite V] in
theorem TwoB56Gen.commV_le_fixV {X L₁ L₂ : Subgroup (MulAut V)} (h : TwoB56Gen X L₁ L₂)
    (hperf : Group.IsPerfect ↥L₂) : commV L₁ ≤ fixV L₂ := by
  obtain ⟨G₁, G₂, W₁, W₂, hL₁, hL₂, -, -, hsup, -, -, -, -, -, -, hI₁, -, -, hinf, hp₁, hp₂⟩ := h
  have hG₂J : G₂ ≤ ffJ X := hsup ▸ le_sup_right
  exact (commV_mono hL₁).trans ((commV_le_of_b56Piece hp₁).trans
    (le_fixV_of_perfect hperf hL₂ hG₂J hI₁ (commV_le_of_b56Piece hp₂) hinf.le))

end Main

end FFTwo

end CFSG.Quasithin.H13.A6
