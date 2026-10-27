module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Red
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.A5.G3
open scoped commutatorElement

section Abstract

variable {Y : Type} [Group Y]

theorem delta5_pCore_le_of_map_eq_top {P : Subgroup Y} (hP : P.Normal)
    {α : Y →* alternatingGroup (Fin 5)} {β : ↥(CFSG.pCore 2 Y) →* Multiplicative (evenWeight 5)}
    (hβb : Function.Bijective β)
    (hβe : ∀ (x : Y) (u v : ↥(CFSG.pCore 2 Y)), (v : Y) = x * u * x⁻¹ → ∀ i : Fin 5,
      ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
          (((α x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i))
    (htop : P.map α = ⊤) : CFSG.pCore 2 Y ≤ P := by
  intro u hu
  set u' : ↥(CFSG.pCore 2 Y) := ⟨u, hu⟩ with hu'
  set w : Fin 5 → ZMod 2 := ((Multiplicative.toAdd (β u') : evenWeight 5) : Fin 5 → ZMod 2)
    with hw
  have hwe : ∑ i, w i = 0 := (Multiplicative.toAdd (β u')).2
  obtain ⟨v, hve, τ, hτs, hvτ⟩ := exists_commutator_decomp w hwe
  obtain ⟨q, hq⟩ := hβb.2 (Multiplicative.ofAdd
    (⟨v, (A5.Delta5.mem_evenWeight_iff v).2 hve⟩ : evenWeight 5))
  have hτ : (⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτs⟩ : alternatingGroup (Fin 5)) ∈ P.map α :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨p, hpP, hp⟩ := hτ
  have hq' : p * (q : Y) * p⁻¹ ∈ CFSG.pCore 2 Y :=
    (CFSG.pCore_normal (G := Y) (p := 2)).conj_mem _ q.2 p
  set q' : ↥(CFSG.pCore 2 Y) := ⟨p * (q : Y) * p⁻¹, hq'⟩ with hq'def
  have hβq' : ∀ i, ((Multiplicative.toAdd (β q') : evenWeight 5) : Fin 5 → ZMod 2) i =
      v (τ⁻¹ i) := by
    intro i
    have := hβe p q q' rfl i
    rw [hq, hp] at this
    simpa using this
  have hkey : q⁻¹ * q' = u' := by
    apply hβb.1
    rw [map_mul, map_inv, hq]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, AddSubgroup.coe_add, AddSubgroup.coe_neg,
      Pi.add_apply, Pi.neg_apply]
    rw [hβq' i, ← hw, hvτ i]
    simp
  have hu2 : u = (q : Y)⁻¹ * (p * (q : Y) * p⁻¹) := by
    have := congrArg Subtype.val hkey
    simpa using this.symm
  rw [hu2]
  have h1 : (q : Y)⁻¹ * p * (q : Y) ∈ P := by
    have := hP.conj_mem p hpP (q : Y)⁻¹
    simpa using this
  have := P.mul_mem h1 (P.inv_mem hpP)
  simpa [mul_assoc] using this

theorem delta5_le_pCore_of_normal (hD : IsDelta5Group Y) {P : Subgroup Y} (hP : P.Normal)
    (hne : P ≠ ⊤) : P ≤ CFSG.pCore 2 Y := by
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := hD
  have hA : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hPm : (P.map α).Normal := hP.map α hαs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map α) with h | h
  · intro x hx
    rw [← hαk, MonoidHom.mem_ker]
    have : α x ∈ P.map α := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · exfalso
    apply hne
    have hQP := delta5_pCore_le_of_map_eq_top hP hβb hβe h
    rw [eq_top_iff]
    intro y _
    have hy : α y ∈ P.map α := h ▸ Subgroup.mem_top _
    obtain ⟨p, hpP, hp⟩ := hy
    have hpy : p⁻¹ * y ∈ CFSG.pCore 2 Y := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]
    have := P.mul_mem hpP (hQP hpy)
    simpa using this

theorem delta5_commutator_eq_top (hD : IsDelta5Group Y) :
    ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
  by_contra hne
  have hle := delta5_le_pCore_of_normal hD (Subgroup.commutator_normal ⊤ ⊤) hne
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := hD
  apply not_solvable_alt5
  apply Group.isSolvable_of_comm
  intro a b
  obtain ⟨x, rfl⟩ := hαs a
  obtain ⟨y, rfl⟩ := hαs b
  have hxy : ⁅x, y⁆ ∈ CFSG.pCore 2 Y :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  rw [← hαk, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
    map_inv] at hxy
  calc α x * α y = α x * α y * (α x)⁻¹ * (α y)⁻¹ * (α y * α x) := by group
    _ = α y * α x := by rw [hxy, one_mul]

theorem map_eq_bot_of_two {N' : Type} [Group N'] {P : Subgroup N'} (hP : P.Normal)
    (hP2 : IsPGroup 2 ↥P) (α : N' →* alternatingGroup (Fin 5)) (hα : Function.Surjective α) :
    P.map α = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hPm : (P.map α).Normal := hP.map α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map α) with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 ↥(P.map α) := hP2.map α
    rw [h] at h2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [Subgroup.card_top, A5.Delta5.a5_card] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
    have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h4

theorem isDelta5Group_of_surj {N' : Type} [Group N'] [Finite Y] (φ : N' →* Y)
    (hφ : Function.Surjective φ) (hker2 : IsPGroup 2 ↥φ.ker) {U : Subgroup N'} (hUn : U.Normal)
    (hU2 : IsPGroup 2 ↥U) (α₀ : N' →* alternatingGroup (Fin 5)) (hα₀ : Function.Surjective α₀)
    (hα₀k : α₀.ker = U) (β₀ : ↥U →* Multiplicative (evenWeight 5))
    (hβ₀ : Function.Surjective β₀) (hβ₀k : ∀ u : ↥U, β₀ u = 1 ↔ φ u = 1)
    (hcomp : ∀ (n : N') (u v : ↥U), (v : N') = n * u * n⁻¹ → ∀ j : Fin 5,
      ((Multiplicative.toAdd (β₀ v) : evenWeight 5) : Fin 5 → ZMod 2) j =
        ((Multiplicative.toAdd (β₀ u) : evenWeight 5) : Fin 5 → ZMod 2)
          (((α₀ n : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ j)) :
    IsDelta5Group Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerU : φ.ker ≤ U := by
    have h := map_eq_bot_of_two (MonoidHom.normal_ker φ) hker2 α₀ hα₀
    intro x hx
    rw [← hα₀k, MonoidHom.mem_ker]
    have : α₀ x ∈ φ.ker.map α₀ := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  set α : Y →* alternatingGroup (Fin 5) := φ.liftOfSurjective hφ ⟨α₀, hα₀k ▸ hkerU⟩ with hαdef
  have hαφ : ∀ n, α (φ n) = α₀ n := fun n =>
    MonoidHom.liftOfRightInverse_comp_apply φ _ _ ⟨α₀, hα₀k ▸ hkerU⟩ n
  have hαs : Function.Surjective α := fun a => by
    obtain ⟨n, rfl⟩ := hα₀ a
    exact ⟨φ n, hαφ n⟩
  set M : Subgroup Y := U.map φ with hM
  have hMk : α.ker = M := by
    ext y
    obtain ⟨n, rfl⟩ := hφ y
    rw [MonoidHom.mem_ker, hαφ, ← MonoidHom.mem_ker, hα₀k]
    constructor
    · intro hn
      exact ⟨n, hn, rfl⟩
    · rintro ⟨u, hu, huv⟩
      have h1 : u⁻¹ * n ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
      have := U.mul_mem hu (hkerU h1)
      simpa using this
  have hMn : M.Normal := hUn.map φ hφ
  have hM2 : IsPGroup 2 ↥M := hU2.map φ
  have hMO : M = CFSG.pCore 2 Y := by
    refine le_antisymm (le_sSup ⟨hMn, hM2⟩) ?_
    have h := map_eq_bot_of_two (CFSG.pCore_normal (G := Y) (p := 2)) CFSG.pCore_isPGroup α hαs
    intro y hy
    rw [← hMk, MonoidHom.mem_ker]
    have : α y ∈ (CFSG.pCore 2 Y).map α := ⟨y, hy, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  set ψ : ↥U →* ↥(CFSG.pCore 2 Y) :=
    (φ.comp U.subtype).codRestrict (CFSG.pCore 2 Y) (fun u => hMO ▸ ⟨u, u.2, rfl⟩) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hMO] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨⟨u, hu⟩, rfl⟩
  have hψk : ψ.ker ≤ β₀.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (hβ₀k u).mpr (congrArg Subtype.val hu)
  set β : ↥(CFSG.pCore 2 Y) →* Multiplicative (evenWeight 5) := ψ.liftOfSurjective hψs ⟨β₀, hψk⟩
    with hβdef
  have hβψ : ∀ u, β (ψ u) = β₀ u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨β₀, hψk⟩ u
  have hβb : Function.Bijective β := by
    refine ⟨?_, fun w => ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro m hm
      obtain ⟨u, rfl⟩ := hψs m
      rw [MonoidHom.mem_ker, hβψ, hβ₀k] at hm
      exact Subgroup.mem_bot.mpr (Subtype.ext hm)
    · obtain ⟨u, rfl⟩ := hβ₀ w
      exact ⟨ψ u, hβψ u⟩
  refine ⟨α, β, hαs, hMk.trans hMO, hβb, fun y m m' hmm' j => ?_⟩
  obtain ⟨n, rfl⟩ := hφ y
  obtain ⟨u, rfl⟩ := hψs m
  obtain ⟨u', rfl⟩ := hψs m'
  have hnu : n * (u : N') * n⁻¹ ∈ U := hUn.conj_mem _ u.2 n
  have h1 : β₀ u' = β₀ ⟨n * u * n⁻¹, hnu⟩ := by
    have h2 : φ ((u' : N')⁻¹ * (n * u * n⁻¹)) = 1 := by
      have h3 : φ u' = φ (n * u * n⁻¹) := by
        have := hmm'
        simp only [hψ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
          at this
        rw [this, map_mul, map_mul, map_inv]
      rw [map_mul, map_inv, h3, inv_mul_cancel]
    have h4 := (hβ₀k ⟨(u' : N')⁻¹ * (n * u * n⁻¹), U.mul_mem (U.inv_mem u'.2) hnu⟩).mpr h2
    have h5 : (⟨n * u * n⁻¹, hnu⟩ : ↥U) = u' * ⟨(u' : N')⁻¹ * (n * u * n⁻¹),
        U.mul_mem (U.inv_mem u'.2) hnu⟩ := Subtype.ext (by simp)
    rw [h5, map_mul, h4, mul_one]
  rw [hβψ, hβψ, hαφ, h1]
  exact hcomp n u ⟨n * u * n⁻¹, hnu⟩ rfl j

end Abstract

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_cComp_of_delta5 {B X : Subgroup Q} (hD : IsDelta5Group ↥B) (hsub : IsSubnormal B X) :
    B ∈ cComp X := by
  have hcard := hD.card
  have hperf : ⁅B, B⁆ = B := by
    have h := congrArg (Subgroup.map B.subtype) (delta5_commutator_eq_top hD)
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  refine ⟨fun h => ?_, hperf, hsub, fun K hKB hK hKp hKsub => ?_⟩
  · rw [h] at hcard
    simp at hcard
  · have hKB' : IsSubnormal K B := A3.subnormal_of_le_of_le hKsub hKB.le (A3.subnormal_le hsub)
    obtain ⟨P, hPB, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKB' hKB
    have hne : P.subgroupOf B ≠ ⊤ := by
      intro htop
      apply (lt_iff_le_not_ge.mp hPB).2
      intro x hx
      have : (⟨x, hx⟩ : ↥B) ∈ P.subgroupOf B := htop ▸ Subgroup.mem_top _
      exact this
    have hPQ := delta5_le_pCore_of_normal hD hPn hne
    have hab := hD.isElemAbelian_pCore
    apply hK
    rw [← hKp, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have ha' : (⟨a, hKB.le ha⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := hPQ (Subgroup.mem_subgroupOf.mpr (hKP ha))
    have hb' : (⟨b, hKB.le hb⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := hPQ (Subgroup.mem_subgroupOf.mpr (hKP hb))
    have hc := hab.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have hc' : a * b = b * a := by
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥B) => ((x : ↥B) : Q)) hc
      simpa using this
    rw [Subgroup.mem_bot, commutatorElement_def, hc']
    group

theorem mem_lFamily_of_delta5 {S B : Subgroup Q} (hD : IsDelta5Group ↥B)
    (hSB : S ≤ Subgroup.normalizer (B : Set Q)) : B ∈ lFamily S := by
  have hNorm : (B.subgroupOf (B ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  exact mem_cComp_of_delta5 hD (A3.subnormal_of_normal le_sup_left hNorm)

theorem false_of_delta5 (hQ : SQTKHypCat Q) (hcore : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h39 : A39ForSQTKCat)
    (hΔ : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      CFSG.SectionRank.IsSQTKCat X → CFSG.pCore 2 X = ⊥ → NoDelta5In X)
    {S B : Subgroup Q} (hS : IsSylowTwoOf S ⊤) (hSB : S ≤ Subgroup.normalizer (B : Set Q))
    (hD : IsDelta5Group ↥B) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : B ∈ lFamily S := mem_lFamily_of_delta5 hD hSB
  have hQS := hQ.isSQTKCat
  have hQq : SQTKHypCat (Q ⧸ CFSG.pCore 2 Q) := SQTKHypCat.quotient_pCore Q hQS
  have hNS : CFSG.pCore 2 Q ≤ S := by rw [hQ.o2]; exact bot_le
  obtain ⟨Λ, hΛ, hBΛ⟩ := exists_cComp_ge_of_lFamily (CFSG.pCore 2 Q)
    (isSolvable_pCore_two_group Q) (h37 _ hQq) (h39 _ hQq) hS hNS hB
  have hΛsub : IsSubnormal Λ ⊤ := subnormal_of_mem_cComp hΛ
  have hΛ' : SQTKHypCat ↥Λ := hQ.of_subnormal hΛsub
  have hZΛ : pCoreOf 2 Λ ≤ centerOf Λ := by
    rw [hQ.pCoreOf_two_of_subnormal hΛsub]
    exact bot_le
  have hE := hD.isElemAbelian_pCore
  have hEcard : Nat.card ↥((CFSG.pCore 2 ↥B).map B.subtype) = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hD.card_pCore]
    norm_num
  have hEab : IsElemAbelian 2 ((CFSG.pCore 2 ↥B).map B.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      have hc := hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      apply Subtype.ext
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥B) => ((x : ↥B) : Q)) hc
      simp only [Subgroup.coe_mul] at this ⊢
      rw [← ha, ← hb]
      simpa using this
    · obtain ⟨x', hx', rfl⟩ := hx
      have := hE.2 x' hx'
      simpa using congrArg Subtype.val this
  have hm : 1 < CFSG.Open.pRank 2 Λ :=
    lt_of_lt_of_le (by norm_num : 1 < 4)
      (CFSG.SectionRank.le_pRank (by norm_num)
        ((Subgroup.map_subtype_le _).trans hBΛ) hEab hEcard)
  have hcoreΛ : A36CoreCat (modO2Image ⊤ Λ) :=
    hcore _ (SQTKHypCat.quotient_pCore ↥(⊤ : Subgroup Q) (hQ.subgroup ⊤)) _
      (modO2Image_mem_cComp hΛ)
  have hΛq : CFSG.IsQuasisimple ↥Λ :=
    lemma_1_2_1_five_of_core CFSG.Quasithin.l2MultiplierFact hΛ hcoreΛ hZΛ hm
  obtain ⟨hT', hB'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hS hΛ hBΛ hB
  have hne : B.subgroupOf Λ ≠ ⊤ := by
    intro h
    apply hD.not_isQuasisimple
    have hBeq : B = Λ := by
      refine le_antisymm hBΛ fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Λ) ∈ B.subgroupOf Λ := h ▸ Subgroup.mem_top _
      exact this
    subst hBeq
    exact hΛq
  have hTN : (S ⊓ Λ).subgroupOf Λ ≤
      Subgroup.normalizer ((B.subgroupOf Λ : Subgroup ↥Λ) : Set ↥Λ) :=
    subgroupOf_le_normalizer (inf_le_left.trans hSB)
  have hD' : IsDelta5Group ↥(B.subgroupOf Λ) := hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBΛ).symm
  exact hΔ ↥Λ hΛq hΛ'.isSQTKCat hΛ'.o2 _ hT' _ hB' hne hTN hD'

end CFSG.Quasithin.H13.L1449
