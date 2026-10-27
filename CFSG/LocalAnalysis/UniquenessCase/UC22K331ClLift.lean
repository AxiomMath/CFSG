module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open Subgroup

theorem k331c_exists_perfect {X Y : Type*} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hY : commutator Y = ⊤) :
    ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ P.map π = ⊤ := by
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image {P : Subgroup X | P.map π = ⊤}
    (fun P => Nat.card P) (Set.toFinite _)
    ⟨⊤, by
      show Subgroup.map π ⊤ = ⊤
      rwa [Subgroup.map_top, MonoidHom.range_eq_top]⟩
  have hP' : P.map π = ⊤ := hP
  have hc : (⁅P, P⁆ : Subgroup X).map π = ⊤ := by
    rw [Subgroup.map_commutator, hP']
    exact hY
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  exact ⟨P, Subgroup.eq_of_le_of_card_ge hle (hmin _ hc), hP'⟩

theorem k331c_isPGroup_ker {Γ K' : Type*} [Group Γ] [Finite Γ] [Group K'] [Finite K']
    [Group.IsPerfect Γ] (α : Γ →* K') (hα : α.ker ≤ center Γ)
    (β : K' →* alternatingGroup (Fin 8)) (hβ : IsPGroup 2 β.ker)
    (hχ : Function.Surjective (β.comp α)) : IsPGroup 2 (β.comp α).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set χ : Γ →* alternatingGroup (Fin 8) := β.comp α with hχdef
  set N : Subgroup Γ := χ.ker with hN
  haveI : Group.IsNilpotent β.ker := hβ.isNilpotent
  let f : N →* β.ker := (α.comp N.subtype).codRestrict β.ker fun n =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp n.2)
  have hf : f.ker ≤ center N := by
    intro n hn
    have h1 : α (n : Γ) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    rw [mem_center_iff]
    intro m
    exact Subtype.ext (mem_center_iff.mp (hα (MonoidHom.mem_ker.mpr h1)) (m : Γ))
  haveI : Group.IsNilpotent N := Subgroup.isNilpotent_of_ker_le_center f hf
  obtain ⟨P⟩ : Nonempty (Sylow 2 N) := Sylow.nonempty
  haveI hPn : (P : Subgroup N).Normal := inferInstance
  haveI : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P hPn
  set S : Subgroup Γ := (P : Subgroup N).map N.subtype with hS
  haveI : S.Normal := inferInstance
  have hSN : S ≤ N := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hS2 : IsPGroup 2 S := P.isPGroup'.map N.subtype
  obtain ⟨T, hT⟩ := Subgroup.exists_right_complement'_of_coprime (Sylow.card_coprime_index P)
  have hTcop : Nat.Coprime 2 (Nat.card T) := by
    rw [← hT.symm.index_eq_card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index
  have hTker : ∀ t : T, α ((t : N) : Γ) = 1 := by
    intro t
    have hmem : α ((t : N) : Γ) ∈ β.ker := (f (t : N)).2
    obtain ⟨k, hk⟩ := hβ ⟨_, hmem⟩
    have hk' : (α ((t : N) : Γ)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hT' : (α ((t : N) : Γ)) ^ Nat.card T = 1 := by
      have h1 : t ^ Nat.card T = 1 := pow_card_eq_one'
      have h2 : ((t : N) : Γ) ^ Nat.card T = 1 := by
        have e1 : (((t ^ Nat.card T : T) : N) : Γ) = 1 := by
          rw [h1]
          rfl
        rwa [Subgroup.coe_pow, Subgroup.coe_pow] at e1
      rw [← map_pow, h2, map_one]
    have h3 : orderOf (α ((t : N) : Γ)) ∣ Nat.gcd (2 ^ k) (Nat.card T) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hT')
    rw [(Nat.Coprime.pow_left k hTcop).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hTc : ∀ t : T, ((t : N) : Γ) ∈ center Γ := fun t =>
    hα (MonoidHom.mem_ker.mpr (hTker t))
  haveI : Group.IsPerfect (Γ ⧸ S) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective S)
  let χ' : Γ ⧸ S →* alternatingGroup (Fin (6 + 2)) := QuotientGroup.lift S χ hSN
  have hχ' : Function.Surjective χ' := fun y => by
    obtain ⟨x, rfl⟩ := hχ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hdec : ∀ x : Γ, x ∈ N →
      ∃ t : T, (QuotientGroup.mk x : Γ ⧸ S) = QuotientGroup.mk ((t : N) : Γ) := by
    intro x hx
    obtain ⟨⟨p, t⟩, hpt⟩ := hT.2 ⟨x, hx⟩
    have hx' : (p : Γ) * ((t : N) : Γ) = x := congrArg Subtype.val hpt
    refine ⟨t, ?_⟩
    rw [← hx', QuotientGroup.mk_mul]
    have hp : (p : Γ) ∈ S := ⟨p, p.2, rfl⟩
    rw [(QuotientGroup.eq_one_iff (p : Γ)).mpr hp, one_mul]
  have hcen : χ'.ker ≤ center (Γ ⧸ S) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨t, ht⟩ := hdec x (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hq))
    rw [ht, mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (mem_center_iff.mp (hTc t) g)
  have hodd : Odd (Nat.card χ'.ker) := by
    let g : T →* χ'.ker := ((QuotientGroup.mk' S).comp (N.subtype.comp T.subtype)).codRestrict
      χ'.ker fun t => MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (t : N).2)
    have hg : Function.Surjective g := by
      rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨t, ht⟩ := hdec x (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hq))
      exact ⟨t, Subtype.ext ht.symm⟩
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp hTcop) (Subgroup.card_dvd_of_surjective hg)
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 6) (by norm_num) χ' hχ'
    hcen hodd
  have hbot : χ'.ker = ⊥ := Subgroup.card_eq_one.mp h1
  have hNS : N ≤ S := by
    intro x hx
    have : (QuotientGroup.mk x : Γ ⧸ S) ∈ χ'.ker :=
      MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)
    rwa [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
  exact hS2.of_injective (Subgroup.inclusion hNS) (Subgroup.inclusion_injective hNS)

theorem k331c_lift {H L : Type} [Group H] [Finite H] [Group L] [Finite L] (φ : H →* L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center H) {K : Subgroup L}
    (hK : IsAlt (Bar2 K) 8) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* H) (χ : Γ →* alternatingGroup (Fin 8)),
      Function.Injective ρ ∧ Function.Surjective χ ∧ IsPGroup 2 χ.ker := by
  obtain ⟨e8⟩ := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ₀ : ↥K →* alternatingGroup (Fin 8) :=
    e8.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := e8.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψ₀k : ψ₀.ker = CFSG.pCore 2 ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    show e8 (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψ₀2 : IsPGroup 2 ψ₀.ker := by
    rw [hψ₀k]
    exact CFSG.pCore_isPGroup
  set X : Subgroup H := K.comap φ with hX
  let φ' : X →* K := φ.subgroupComap K
  have hφ' : Function.Surjective φ' := φ.subgroupComap_surjective_of_surjective K hφ
  let ψ₁ : X →* alternatingGroup (Fin 8) := ψ₀.comp φ'
  have hψ₁ : Function.Surjective ψ₁ := hψ₀s.comp hφ'
  have hA8 : commutator (alternatingGroup (Fin 8)) = ⊤ :=
    commutator_alternatingGroup_eq_top
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  obtain ⟨Γ₀, hΓ₀, hΓ₀m⟩ := k331c_exists_perfect ψ₁ hψ₁ hA8
  haveI : Group.IsPerfect Γ₀ := Subgroup.isPerfect_iff.mpr hΓ₀
  let α : Γ₀ →* K := φ'.comp Γ₀.subtype
  have hαker : α.ker ≤ center Γ₀ := by
    intro x hx
    have h1 : φ ((x : X) : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : ((x : X) : H) ∈ center H := hker (MonoidHom.mem_ker.mpr h1)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (mem_center_iff.mp h2 ((y : X) : H)))
  have hsurj : Function.Surjective (ψ₀.comp α) := by
    have : (ψ₀.comp α).range = ⊤ := by
      show (ψ₁.comp Γ₀.subtype).range = ⊤
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hΓ₀m]
    exact MonoidHom.range_eq_top.mp this
  exact ⟨Γ₀, inferInstance, inferInstance, X.subtype.comp Γ₀.subtype, ψ₀.comp α,
    X.subtype_injective.comp Γ₀.subtype_injective, hsurj,
    k331c_isPGroup_ker α hαker ψ₀ hψ₀2 hsurj⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
