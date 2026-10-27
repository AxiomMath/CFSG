module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18S3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Nat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl
public import CFSG.Quasithin.Recognition.GoldschmidtF112B2Trio
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Quot
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModM10

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F53Push
  CFSG.Quasithin.F53Mod CFSG.QuasithinUnique.Setup.Campbell Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

theorem relCent_eq_fixSecIn {E Z A : Subgroup G} [(Z.subgroupOf E).Normal] (hZE : Z ≤ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) : relCent E Z A = fixSecIn A Z E := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_relCent hEZ] at hx
    refine (CFSG.Quasithin.X1512.mem_fixSecIn hZE).mpr ⟨hx.1, fun a ha => ?_⟩
    have h := hx.2 a ha
    have e : a * x * a⁻¹ * x⁻¹ = ⁅x, a⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Z.inv_mem h
  · intro x hx
    rw [CFSG.Quasithin.X1512.mem_fixSecIn hZE] at hx
    rw [mem_relCent hEZ]
    refine ⟨hx.1, fun a ha => ?_⟩
    have h := hx.2 a ha
    have e : ⁅x, a⁆ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Z.inv_mem h

section Dictionary

variable {n : ℕ} {M : Model n} {K Z E : Subgroup G} [(Z.subgroupOf E).Normal]
  {Ψ : ↥K →* Perm (Fin n)} {β : M.W →* ↥E ⧸ Z.subgroupOf E}

theorem comap_fixSecIn (h : SecData M K Z E Ψ β) {A : Subgroup G} (hZE : Z ≤ E)
    (hAK : A ≤ K) :
    (fixSecIn A Z E).subgroupOf E =
      ((fixW M ((A.subgroupOf K).map Ψ)).map β).comap
        (QuotientGroup.mk' (Z.subgroupOf E)) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_map, X1512.mem_fixSecIn hZE]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨u, hu⟩ := h.surj (QuotientGroup.mk x)
    refine ⟨u, ?_, hu⟩
    rintro σ ⟨a', ha', rfl⟩
    obtain ⟨hax, h'⟩ := h.equiv a' u x hu
    apply h.inj
    rw [h', hu]
    exact ((X1512.mk_eq_iff hZE).mpr (hx a' (Subgroup.mem_subgroupOf.mp ha'))).symm
  · rintro ⟨u, hu, hux⟩
    refine ⟨x.2, fun a ha => ?_⟩
    have haK : a ∈ K := hAK ha
    have hux' : β u = QuotientGroup.mk x := hux
    obtain ⟨hax, h'⟩ := h.equiv ⟨a, haK⟩ u x hux'
    have hfix := hu (Ψ ⟨a, haK⟩) ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [hfix, hux'] at h'
    exact (X1512.mk_eq_iff hZE).mp h'

end Dictionary

private theorem nat3_eq_of_fixes {σ τ : Perm (Fin 3)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) {u : nat3.W} (hu : u ≠ 1)
    (hσu : nat3.act σ u = u) (hτu : nat3.act τ u = u) : σ = τ := by
  by_contra hne
  obtain ⟨h3, hne1⟩ := F112B2.perm_fin3_mul_involutions σ τ hσ1 hσ hτ1 hτ hne
  have hfixH : ∀ x ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 3))), nat3.act x u = u := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases (by simpa using hy : y = σ ∨ y = τ) with rfl | rfl
      · exact hσu
      · exact hτu
    | one => simp
    | mul a b _ _ ha hb => rw [act_mul_apply, hb, ha]
    | inv a _ ha =>
      calc nat3.act a⁻¹ u = nat3.act a⁻¹ (nat3.act a u) := by rw [ha]
        _ = u := by rw [← act_mul_apply, inv_mul_cancel]; simp
  have hmem : σ * τ ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 3))) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hfix : u ∈ fixW nat3 (Subgroup.zpowers (σ * τ)) := by
    rw [mem_fixW]
    intro y hy
    exact hfixH y ((Subgroup.zpowers_le.mpr hmem) hy)
  rw [nat3_fixW_eq_bot_of_order_three hne1 h3] at hfix
  exact hu (Subgroup.mem_bot.mp hfix)

private theorem nat3_fixW_zpowers_inj {σ τ : Perm (Fin 3)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (h : fixW nat3 (Subgroup.zpowers σ) = fixW nat3 (Subgroup.zpowers τ)) : σ = τ := by
  have hcard : Nat.card (fixW nat3 (Subgroup.zpowers σ)) = 2 := by
    have hidx : idx nat3 σ = 2 := by
      have h0 := idx_nat3 σ
      rw [if_neg hσ1, if_pos (by simpa [pow_two] using hσ)] at h0
      exact h0
    have hf := idx_mul_card nat3 σ
    rw [card_nat3, ← card_fixW_zpowers nat3 σ, hidx] at hf
    omega
  have hne : fixW nat3 (Subgroup.zpowers σ) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu : (u : nat3.W) ≠ 1 := by
    intro h1
    exact hu1 (Subtype.ext h1)
  have hσu : nat3.act σ (u : nat3.W) = (u : nat3.W) :=
    (mem_fixW.mp u.2) σ (Subgroup.mem_zpowers σ)
  have huW' : (u : nat3.W) ∈ fixW nat3 (Subgroup.zpowers τ) := by
    rw [← h]
    exact u.2
  have hτu : nat3.act τ (u : nat3.W) = (u : nat3.W) :=
    (mem_fixW.mp huW') τ (Subgroup.mem_zpowers τ)
  exact nat3_eq_of_fixes hσ hτ hσ1 hτ1 hu hσu hτu

theorem natQuot_of_isNat3Sec {L E Z : Subgroup G} (h : IsNat3Sec L Z E) (hZE : Z ≤ E)
    (hEL : E ≤ L)
    (hSyl : ∀ A : Subgroup G, IsSylowTwoOf A L → E ≤ A ∧ E.relIndex A = 2)
    (hcSec : cSecIn L Z E = E) : NatQuot L E Z 1 := by
  have hmodel : IsModelSec nat3 L Z E := h
  have hNat3 : IsNat3Sec L Z E := h
  have hmodel' : IsModelSec nat3 L Z E := hmodel
  obtain ⟨hZn, θ, β, hθs, hθk, hsd⟩ := hmodel
  letI : (Z.subgroupOf E).Normal := hZn
  have hsec : IsSec L Z E := IsModelSec.isSec hmodel' hZE
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := hEL.trans hsec.normL
  have hker : ∀ x : ↥L, θ x = 1 ↔ (x : G) ∈ E := by
    intro x
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf, hcSec]
  have hdata : ∀ A : Subgroup G, IsSylowTwoOf A L →
      ∃ σ : Perm (Fin 3), σ * σ = 1 ∧ σ ≠ 1 ∧
        (A.subgroupOf L).map θ = Subgroup.zpowers σ ∧
        (fixW nat3 ((A.subgroupOf L).map θ)).index = 2 ∧
        Nat.card (commW nat3 ((A.subgroupOf L).map θ) ⊤) = 2 := by
    intro A hA
    obtain ⟨hEA, hErel⟩ := hSyl A hA
    let B : Subgroup (Perm (Fin 3)) := (A.subgroupOf L).map θ
    have hBcard : Nat.card B = 2 := by
      rw [show Nat.card B = E.relIndex A from
        card_map_subgroupOf_eq_relIndex θ hker hA.1, hErel]
    have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hBcard
      omega
    obtain ⟨σ, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hσB : (σ : Perm (Fin 3)) ∈ B := σ.2
    have hdvd : orderOf (σ : Perm (Fin 3)) ∣ 2 := by
      have h := orderOf_dvd_natCard (⟨(σ : Perm (Fin 3)), hσB⟩ : ↥B)
      rwa [Subgroup.orderOf_mk, hBcard] at h
    have hord : orderOf (σ : Perm (Fin 3)) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exfalso
        exact hσ1 (Subtype.ext (orderOf_eq_one_iff.mp h))
      · exact h
    have hBσ : B = Subgroup.zpowers (σ : Perm (Fin 3)) := by
      refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hσB) ?_).symm
      rw [hBcard, Nat.card_zpowers, hord]
    have hσsq : (σ : Perm (Fin 3)) * σ = 1 := by
      rw [← pow_two, ← hord, pow_orderOf_eq_one]
    have hσ1' : (σ : Perm (Fin 3)) ≠ 1 := fun h => hσ1 (Subtype.ext h)
    have hidx : (fixW nat3 B).index = 2 := by
      have h0 : idx nat3 (σ : Perm (Fin 3)) = 2 := by
        have h := idx_nat3 (σ : Perm (Fin 3))
        rw [if_neg hσ1', if_pos (by simpa [pow_two] using hσsq)] at h
        exact h
      rw [hBσ]
      simpa [idx] using h0
    have hcomm : Nat.card (commW nat3 B ⊤) = 2 := by
      have h0 : Nat.card (commW nat3 (Subgroup.zpowers (σ : Perm (Fin 3))) ⊤) = 2 := by
        rw [← bf1 nat3 (σ : Perm (Fin 3))]
        simpa [hBσ, idx] using hidx
      simpa [hBσ] using h0
    exact ⟨σ, hσsq, hσ1', hBσ, hidx, hcomm⟩
  have hZrel : ∀ A : Subgroup G, IsSylowTwoOf A L → Z ≤ relCent E Z A := by
    intro A hA
    rw [relCent_eq_fixSecIn hZE hEZ]
    intro z hz
    rw [mem_fixSecIn_iff hEZ]
    refine ⟨hZE hz, fun a ha => ?_⟩
    have h1 : a * z⁻¹ * a⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hsec.normL (hA.1 ha)) z⁻¹).mp (Z.inv_mem hz)
    have e : ⁅z, a⁆ = z * (a * z⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    have hza : ⁅z, a⁆ ∈ Z := by
      rw [e]
      exact Z.mul_mem hz h1
    have e2 : a * z * a⁻¹ * z⁻¹ = ⁅z, a⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e2]
    exact Z.inv_mem hza
  refine ⟨hZE, hEL, le_inf hsec.normN hsec.normL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsNat3Sec.relIndex_eq hNat3]
    norm_num
  · intro A hA
    obtain ⟨σ, hσsq, hσ1, hBσ, hidx, hcomm⟩ := hdata A hA
    have hZEindex : Z.relIndex E = 4 := by
      simpa using IsNat3Sec.relIndex_eq hNat3
    have hrelE : (relCent E Z A).relIndex E = 2 := by
      rw [relCent_eq_fixSecIn hZE hEZ, hsd.relIndex_fixSecIn hZE hA.1]
      exact hidx
    have hrelE' : relCent E Z A ≤ E := fun x hx => hx.1
    have hm := Subgroup.relIndex_mul_relIndex (H := Z) (K := relCent E Z A) (L := E)
      (hZrel A hA) hrelE'
    rw [hZEindex, hrelE] at hm
    omega
  · intro A hA
    obtain ⟨σ, hσsq, hσ1, hBσ, hidx, hcomm⟩ := hdata A hA
    have hquad : ⁅commSec A Z E, A⁆ ≤ Z := by
      rw [hsd.quadratic_iff hZE hA.1]
      rw [hBσ]
      exact commW_commW_eq_bot_of_sq nat3 hσsq
    have hcommE : ⁅E, A⁆ ≤ E := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      have haN : a ∈ Subgroup.normalizer (E : Set G) := hsec.normN (hA.1 ha)
      have h1 : a * x⁻¹ * a⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp haN x⁻¹).mp (E.inv_mem hx)
      have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact E.mul_mem hx h1
    have hcommE' : commSec A Z E ≤ E := sup_le hcommE hZE
    have hle : commSec A Z E ≤ relCent E Z A := by
      rw [relCent_eq_fixSecIn hZE hEZ]
      intro x hx
      rw [mem_fixSecIn_iff hEZ]
      refine ⟨hcommE' hx, fun a ha => ?_⟩
      have hxZ : ⁅x, a⁆ ∈ Z := Subgroup.commutator_le.mp hquad x hx a ha
      have e : a * x * a⁻¹ * x⁻¹ = ⁅x, a⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Z.inv_mem hxZ
    have hZle : Z ≤ commSec A Z E := le_sup_right
    have hD2 : Z.relIndex (commSec A Z E) = 2 := by
      rw [hsd.card_commSec hZE hA.1]
      exact hcomm
    have hline : Z.relIndex (relCent E Z A) = 2 := by
      have hZEindex : Z.relIndex E = 4 := by
        simpa using IsNat3Sec.relIndex_eq hNat3
      have hrelE : (relCent E Z A).relIndex E = 2 := by
        rw [relCent_eq_fixSecIn hZE hEZ, hsd.relIndex_fixSecIn hZE hA.1]
        exact hidx
      have hrelE' : relCent E Z A ≤ E := fun x hx => hx.1
      have hm := Subgroup.relIndex_mul_relIndex (H := Z) (K := relCent E Z A) (L := E)
        (hZrel A hA) hrelE'
      rw [hZEindex, hrelE] at hm
      omega
    have hmul := Subgroup.relIndex_mul_relIndex (H := Z) (K := commSec A Z E)
      (L := relCent E Z A) hZle hle
    rw [hD2, hline] at hmul
    have hone : (commSec A Z E).relIndex (relCent E Z A) = 1 := by omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)
  · intro A A' hA hA' hnot
    obtain ⟨σ, hσsq, hσ1, hBσ, hidx, hcomm⟩ := hdata A hA
    obtain ⟨τ, hτsq, hτ1, hBτ, hidx', hcomm'⟩ := hdata A' hA'
    set B : Subgroup (Perm (Fin 3)) := (A.subgroupOf L).map θ with hBdef
    set B' : Subgroup (Perm (Fin 3)) := (A'.subgroupOf L).map θ with hB'def
    have hBσ' : B = Subgroup.zpowers σ := by simpa [hBdef] using hBσ
    have hBτ' : B' = Subgroup.zpowers τ := by simpa [hB'def] using hBτ
    have hidxB : (fixW nat3 B).index = 2 := by simpa [hBdef] using hidx
    have hidxB' : (fixW nat3 B').index = 2 := by simpa [hB'def] using hidx'
    have hBne : B ≠ B' := by
      intro hBB
      apply hnot
      intro a ha
      have haL : a ∈ L := hA.1 ha
      have hθa : θ ⟨a, haL⟩ ∈ B' := by
        rw [← hBB]
        exact ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      obtain ⟨a', ha'B', hθa'⟩ := hθa
      have ha'G : (a' : G) ∈ A' := by
        simpa using (Subgroup.mem_subgroupOf.mp ha'B')
      have hdiff : θ (⟨a, haL⟩ * a'⁻¹) = 1 := by
        rw [map_mul, map_inv, hθa']
        simp
      have hE : a * (a' : G)⁻¹ ∈ E := by
        have h := (hker (⟨a, haL⟩ * a'⁻¹)).mp hdiff
        simpa using h
      have h1 : a * (a' : G)⁻¹ * (a' : G) ∈ E ⊔ A' :=
        Subgroup.mul_mem_sup hE ha'G
      have h2 : a = a * (a' : G)⁻¹ * (a' : G) := by group
      rw [h2, sup_comm]
      exact h1
    have hfixne : fixW nat3 B ≠ fixW nat3 B' := by
      intro hfix
      apply hBne
      have hστ : σ = τ := by
        refine nat3_fixW_zpowers_inj hσsq hτsq hσ1 hτ1 ?_
        rw [← hBσ', ← hBτ']
        exact hfix
      calc B = Subgroup.zpowers σ := hBσ'
        _ = Subgroup.zpowers τ := by rw [hστ]
        _ = B' := hBτ'.symm
    have hcardB : Nat.card (fixW nat3 B) = 2 := by
      have h := Subgroup.card_mul_index (fixW nat3 B)
      rw [card_nat3, hidxB] at h
      omega
    have hcardB' : Nat.card (fixW nat3 B') = 2 := by
      have h := Subgroup.card_mul_index (fixW nat3 B')
      rw [card_nat3, hidxB'] at h
      omega
    have hdisj : fixW nat3 B ⊓ fixW nat3 B' = ⊥ := by
      by_contra hne
      have hge : 2 ≤ Nat.card ↥(fixW nat3 B ⊓ fixW nat3 B') := by
        have h1 : 1 < Nat.card ↥(fixW nat3 B ⊓ fixW nat3 B') :=
          (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
        omega
      have hle : Nat.card ↥(fixW nat3 B ⊓ fixW nat3 B') ≤ 2 := by
        calc Nat.card ↥(fixW nat3 B ⊓ fixW nat3 B') ≤ Nat.card (fixW nat3 B) :=
              Subgroup.card_le_of_le inf_le_left
          _ = 2 := hcardB
      have hcard : Nat.card ↥(fixW nat3 B ⊓ fixW nat3 B') = 2 := le_antisymm hle hge
      have heq : fixW nat3 B ⊓ fixW nat3 B' = fixW nat3 B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hcardB])
      have hleFB : fixW nat3 B ≤ fixW nat3 B' := by
        rw [← heq]
        exact inf_le_right
      have hFB : fixW nat3 B = fixW nat3 B' :=
        Subgroup.eq_of_le_of_card_ge hleFB (by rw [hcardB', hcardB])
      exact hfixne hFB
    have hsupB : fixW nat3 B ⊔ fixW nat3 B' = ⊤ := by
      have hnorm : fixW nat3 B' ≤ Subgroup.normalizer (fixW nat3 B : Set nat3.W) := by
        rw [CommGroup.normalizer_eq_top]
        exact le_top
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (fixW nat3 B) (fixW nat3 B') hnorm (disjoint_iff.mpr hdisj)
      have hcard4 : Nat.card ↥(fixW nat3 B ⊔ fixW nat3 B') = 4 := by
        rw [hcard, hcardB, hcardB']
      refine Subgroup.eq_top_of_card_eq (H := fixW nat3 B ⊔ fixW nat3 B') ?_
      rw [hcard4, card_nat3]
    let π : ↥E →* ↥E ⧸ Z.subgroupOf E := QuotientGroup.mk' (Z.subgroupOf E)
    have hcomapA : (fixSecIn A Z E).subgroupOf E =
        ((fixW nat3 B).map β).comap π := by
      simpa [π, hBdef] using comap_fixSecIn hsd hZE hA.1
    have hcomapA' : (fixSecIn A' Z E).subgroupOf E =
        ((fixW nat3 B').map β).comap π := by
      simpa [π, hB'def] using comap_fixSecIn hsd hZE hA'.1
    have hmapA : ((fixSecIn A Z E).subgroupOf E).map π = (fixW nat3 B).map β := by
      rw [hcomapA]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hmapA' : ((fixSecIn A' Z E).subgroupOf E).map π = (fixW nat3 B').map β := by
      rw [hcomapA']
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hfixA_le_E : fixSecIn A Z E ≤ E :=
      fun x hx => (mem_fixSecIn_iff hEZ).mp hx |>.1
    have hfixA'_le_E : fixSecIn A' Z E ≤ E :=
      fun x hx => (mem_fixSecIn_iff hEZ).mp hx |>.1
    have hsub : (fixSecIn A Z E ⊓ fixSecIn A' Z E).subgroupOf E = Z.subgroupOf E := by
      calc
        (fixSecIn A Z E ⊓ fixSecIn A' Z E).subgroupOf E
            = (fixSecIn A Z E).subgroupOf E ⊓ (fixSecIn A' Z E).subgroupOf E := by
              change (fixSecIn A Z E ⊓ fixSecIn A' Z E).comap E.subtype =
                (fixSecIn A Z E).comap E.subtype ⊓ (fixSecIn A' Z E).comap E.subtype
              rw [Subgroup.comap_inf]
        _ = ((fixW nat3 B).map β).comap π ⊓ ((fixW nat3 B').map β).comap π := by
              rw [hcomapA, hcomapA']
        _ = (((fixW nat3 B).map β) ⊓ ((fixW nat3 B').map β)).comap π := by
              rw [Subgroup.comap_inf]
        _ = (((fixW nat3 B) ⊓ (fixW nat3 B')).map β).comap π := by
              rw [← Subgroup.map_inf (fixW nat3 B) (fixW nat3 B') β hsd.inj]
        _ = ((⊥ : Subgroup nat3.W).map β).comap π := by rw [hdisj]
        _ = (⊥ : Subgroup (↥E ⧸ Z.subgroupOf E)).comap π := by rw [Subgroup.map_bot]
        _ = Z.subgroupOf E := by
              ext x
              rw [Subgroup.mem_comap, Subgroup.mem_bot]
              change (QuotientGroup.mk' (Z.subgroupOf E)) x = 1 ↔ x ∈ Z.subgroupOf E
              rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hfixZ : fixSecIn A Z E ⊓ fixSecIn A' Z E = Z := by
      have h := Subgroup.subgroupOf_inj.mp hsub
      have hle : fixSecIn A Z E ⊓ fixSecIn A' Z E ≤ E :=
        fun x hx => (mem_fixSecIn_iff hEZ).mp (Subgroup.mem_inf.mp hx).1 |>.1
      rwa [inf_of_le_left hle, inf_of_le_left hZE] at h
    have hsupmap : ((fixSecIn A Z E ⊔ fixSecIn A' Z E).subgroupOf E).map π = ⊤ := by
      rw [Subgroup.subgroupOf_sup hfixA_le_E hfixA'_le_E,
        Subgroup.map_sup, hmapA, hmapA', ← Subgroup.map_sup, hsupB,
        Subgroup.map_top_of_surjective β hsd.surj]
    have hsupE : fixSecIn A Z E ⊔ fixSecIn A' Z E = E := by
      have hsupLe : fixSecIn A Z E ⊔ fixSecIn A' Z E ≤ E :=
        sup_le hfixA_le_E hfixA'_le_E
      refine le_antisymm hsupLe ?_
      intro x hxE
      have hxmap : π ⟨x, hxE⟩ ∈ ((fixSecIn A Z E ⊔ fixSecIn A' Z E).subgroupOf E).map π := by
        rw [hsupmap]
        exact Subgroup.mem_top _
      obtain ⟨u, hu, hux⟩ := hxmap
      have hxZ : x * (u : G)⁻¹ ∈ Z := by
        have hker : π (⟨x, hxE⟩ * u⁻¹) = 1 := by
          rw [map_mul, map_inv, hux]
          simp
        have hker' : QuotientGroup.mk (⟨x, hxE⟩ * u⁻¹) = (1 : ↥E ⧸ Z.subgroupOf E) := by
          simpa [π, QuotientGroup.mk'_apply] using hker
        have hmem : (⟨x, hxE⟩ * u⁻¹) ∈ Z.subgroupOf E :=
          (QuotientGroup.eq_one_iff (N := Z.subgroupOf E) (⟨x, hxE⟩ * u⁻¹)).mp hker'
        simpa using Subgroup.mem_subgroupOf.mp hmem
      have hZsup : Z ≤ fixSecIn A Z E ⊔ fixSecIn A' Z E := by
        have hZA : Z ≤ fixSecIn A Z E := by
          rw [← relCent_eq_fixSecIn hZE hEZ]
          exact hZrel A hA
        exact hZA.trans le_sup_left
      have huG : (u : G) ∈ fixSecIn A Z E ⊔ fixSecIn A' Z E :=
        Subgroup.mem_subgroupOf.mp hu
      have hx : x = (x * (u : G)⁻¹) * (u : G) := by group
      rw [hx]
      exact (fixSecIn A Z E ⊔ fixSecIn A' Z E).mul_mem (hZsup hxZ) huG
    rw [relCent_eq_fixSecIn hZE hEZ, relCent_eq_fixSecIn hZE hEZ]
    exact ⟨hfixZ, hsupE⟩
  · intro g hgL hodd hgE e heE hcomm
    have hgθ : θ ⟨g, hgL⟩ ≠ 1 := by
      intro h1
      exact hgE ((hker ⟨g, hgL⟩).mp h1)
    have hoddθ : Odd (orderOf (θ ⟨g, hgL⟩)) :=
      Odd.of_dvd_nat hodd (by
        simpa [Subgroup.orderOf_mk] using orderOf_map_dvd θ ⟨g, hgL⟩)
    have hsign : Perm.sign (θ ⟨g, hgL⟩) = 1 :=
      CFSG.Quasithin.sign_eq_one_of_odd_orderOf' hoddθ
    have h3 : (θ ⟨g, hgL⟩) ^ 3 = 1 := perm3_pow_three_of_sign _ hsign
    have hfixbot : fixW nat3 (Subgroup.zpowers (θ ⟨g, hgL⟩)) = ⊥ :=
      nat3_fixW_eq_bot_of_order_three hgθ h3
    have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := hsec.normL hgL
    have hcomm' : g * e * g⁻¹ * e⁻¹ ∈ Z := by
      have h := Z.inv_mem hcomm
      simpa [commutatorElement_def, mul_assoc] using h
    have hefix : e ∈ fixSecIn (Subgroup.zpowers g) Z E := by
      rw [mem_fixSecIn_zpowers_iff hEZ hgZ]
      exact ⟨heE, hcomm'⟩
    have hA : Subgroup.zpowers g ≤ L := Subgroup.zpowers_le.mpr hgL
    have heSub : (⟨e, heE⟩ : ↥E) ∈ (fixSecIn (Subgroup.zpowers g) Z E).subgroupOf E :=
      Subgroup.mem_subgroupOf.mpr hefix
    rw [comap_fixSecIn hsd hZE hA, map_zpowers_subgroupOf θ hgL, hfixbot,
      Subgroup.map_bot, Subgroup.mem_comap, Subgroup.mem_bot] at heSub
    have hmem : (⟨e, heE⟩ : ↥E) ∈ Z.subgroupOf E :=
      (QuotientGroup.eq_one_iff (⟨e, heE⟩ : ↥E)).mp heSub
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro A hZA hAE hnorm
    refine IsModelSec.irred_of hmodel' ?_ hZA hAE hnorm
    intro Y hY
    exact X1512.coreMod_irreducible (Or.inl rfl) Y hY

theorem card_commutator_zpowers_le_relIndex {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hEab : IsMulCommutative E) (hE2 : ∀ x ∈ E, x ^ 2 = 1) {a : H}
    (haN : a ∈ Subgroup.normalizer (E : Set H)) (ha2 : a ^ 2 ∈ E) :
    Nat.card ↥⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ≤
      (E ⊓ Subgroup.centralizer ({a} : Set H)).relIndex E := by
  classical
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun x y => hEab.is_comm.comm x y }
  let α : ↥E →* ↥E := Subgroup.normalizerMonoidHom E ⟨a, haN⟩
  let β : ↥E →* ↥E :=
    { toFun := fun x => (α x)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        show (α (x * y))⁻¹ = (α x)⁻¹ * (α y)⁻¹
        rw [map_mul, mul_inv_rev]
        exact mul_comm _ _ }
  let φ : ↥E →* ↥E := (MonoidHom.id ↥E) * β
  let φ' : ↥E →* H := E.subtype.comp φ
  have hφapply : ∀ x : ↥E, (φ x : H) = (x : H) * (a * (x : H)⁻¹ * a⁻¹) := by
    intro x
    show (x : H) * ((α x)⁻¹ : ↥E) = _
    have hα : ((α x : ↥E) : H) = a * (x : H) * a⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨a, haN⟩ x
    rw [Subgroup.coe_inv, hα]
    group
  have hker : φ.ker = (E ⊓ Subgroup.centralizer ({a} : Set H)).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hx1 : (x : H) * (a * (x : H)⁻¹ * a⁻¹) = 1 := by
        have := congrArg Subtype.val hx
        simpa [hφapply] using this
      have h1 : (x : H) * a * (x : H)⁻¹ = a := by
        have := congrArg (fun t => t * a) hx1
        simpa [mul_assoc] using this
      have h2 : (x : H) * a = a * (x : H) := by
        have := congrArg (fun t => t * (x : H)) h1
        simpa [mul_assoc] using this
      exact ⟨x.2, h2⟩
    · intro hx
      apply Subtype.ext
      rw [show (φ x : H) = (x : H) * (a * (x : H)⁻¹ * a⁻¹) from hφapply x]
      have hxinv : a * (x : H)⁻¹ = (x : H)⁻¹ * a := by
        have := congrArg (fun t => (x : H)⁻¹ * t * (x : H)⁻¹) hx.2
        simpa [mul_assoc] using this
      rw [hxinv]
      group
      rfl
  have hle : ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ≤ φ'.range := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hdecomp : a ^ k = a ^ (k % 2) * (a ^ (2 : ℤ)) ^ (k / 2) := by
      rw [← zpow_mul, ← zpow_add]
      congr 1
      omega
    have heE : (a ^ 2) ^ (k / 2) ∈ E := Subgroup.zpow_mem E ha2 (k / 2)
    have hmod := Int.emod_two_eq_zero_or_one k
    rcases hmod with hk0 | hk1
    ·
      have hyE : a ^ k ∈ E := by
        rw [hdecomp, hk0]
        simpa using heE
      have h1 : ⁅x, a ^ k⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hEab.is_comm.comm ⟨x, hx⟩ ⟨a ^ k, hyE⟩)
      rw [h1]
      exact φ'.range.one_mem
    ·
      have hk : a ^ k = a * (a ^ 2) ^ (k / 2) := by
        rw [hdecomp, hk1]
        simp
      have hcomm : ⁅x, a ^ k⁆ = ⁅x, a⁆ := by
        rw [hk, commutatorElement_def, commutatorElement_def]
        have hxe : (a ^ 2) ^ (k / 2) * (x : H) = (x : H) * (a ^ 2) ^ (k / 2) :=
          congrArg Subtype.val (hEab.is_comm.comm ⟨(a ^ 2) ^ (k / 2), heE⟩ ⟨x, hx⟩)
        have hxe' : (a ^ 2) ^ (k / 2) * (x : H)⁻¹ = (x : H)⁻¹ * (a ^ 2) ^ (k / 2) := by
          have h1 : (x : H)⁻¹ * ((a ^ 2) ^ (k / 2) * (x : H)) * (x : H)⁻¹ =
              (x : H)⁻¹ * ((x : H) * (a ^ 2) ^ (k / 2)) * (x : H)⁻¹ := by rw [hxe]
          have h2 : (x : H)⁻¹ * (a ^ 2) ^ (k / 2) = (a ^ 2) ^ (k / 2) * (x : H)⁻¹ := by
            simpa [mul_assoc] using h1
          exact h2.symm
        calc
          x * (a * (a ^ 2) ^ (k / 2)) * x⁻¹ * (a * (a ^ 2) ^ (k / 2))⁻¹
              = x * a * ((a ^ 2) ^ (k / 2) * x⁻¹) * ((a ^ 2) ^ (k / 2))⁻¹ * a⁻¹ := by group
          _ = x * a * (x⁻¹ * (a ^ 2) ^ (k / 2)) * ((a ^ 2) ^ (k / 2))⁻¹ * a⁻¹ := by rw [hxe']
          _ = x * a * x⁻¹ * a⁻¹ := by group
      rw [hcomm]
      refine ⟨⟨x, hx⟩, ?_⟩
      show (φ' ⟨x, hx⟩ : H) = ⁅x, a⁆
      rw [show (φ' ⟨x, hx⟩ : H) = (φ ⟨x, hx⟩ : H) from rfl, hφapply ⟨x, hx⟩]
      rw [commutatorElement_def]
      group
  have hker' : φ'.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      simpa [φ'] using h
    · intro h
      simpa [φ'] using congrArg Subtype.val h
  have hcard : Nat.card φ'.range = (E ⊓ Subgroup.centralizer ({a} : Set H)).relIndex E := by
    rw [← Subgroup.index_ker φ', hker', hker]
    rfl
  exact (Subgroup.card_le_of_le hle).trans_eq hcard

theorem le_normalizer_subgroupOf_of_le_normalizer {A H : Subgroup G} (hAH : A ≤ H)
    (hH : H ≤ Subgroup.normalizer (A : Set G)) :
    ⊤ ≤ Subgroup.normalizer (A.subgroupOf H : Set ↥H) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hmem : (x : ↥H) * a * x⁻¹ ∈ A.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hH x.2) (a : G)).mp (Subgroup.mem_subgroupOf.mp ha))
    exact hmem
  · intro ha
    have haA : (x : G) * (a : G) * (x : G)⁻¹ ∈ A := Subgroup.mem_subgroupOf.mp ha
    have := (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem x.2))
      ((x : G) * (a : G) * (x : G)⁻¹)).mp haA
    have haA' : (a : G) ∈ A := by
      simpa [mul_assoc] using this
    simpa using (Subgroup.mem_subgroupOf.mpr haA')

theorem le_normalizer_of_le_normalizer_subgroupOf {A H : Subgroup G} (hAH : A ≤ H)
    (h : ⊤ ≤ Subgroup.normalizer (A.subgroupOf H : Set ↥H)) :
    H ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hmem : (⟨g, hg⟩ : ↥H) * ⟨a, hAH ha⟩ * (⟨g, hg⟩ : ↥H)⁻¹ ∈ A.subgroupOf H :=
      (Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_top _)) ⟨a, hAH ha⟩).mp
        (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro ha
    have haH : a ∈ H := by
      have h1 : g * a * g⁻¹ ∈ H := hAH ha
      have h2 : g⁻¹ * (g * a * g⁻¹) * g ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg
      have h2' : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rwa [h2'] at h2
    have hprod : (⟨g, hg⟩ : ↥H) * ⟨a, haH⟩ * (⟨g, hg⟩ : ↥H)⁻¹ ∈ A.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simpa using ha
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_top ⟨g, hg⟩)) ⟨a, haH⟩).mpr hprod)

theorem relCent_subgroupOf {E Z A H : Subgroup G} (hEH : E ≤ H) (hZH : Z ≤ H)
    (hAH : A ≤ H) (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hEZH : E.subgroupOf H ≤ Subgroup.normalizer (Z.subgroupOf H : Set ↥H)) :
    (relCent E Z A).subgroupOf H =
      relCent (E.subgroupOf H) (Z.subgroupOf H) (A.subgroupOf H) := by
  ext x
  constructor
  · intro hx
    have hx' : (x : G) ∈ relCent E Z A := Subgroup.mem_subgroupOf.mp hx
    rw [mem_relCent hEZ] at hx'
    rw [mem_relCent hEZH]
    refine ⟨Subgroup.mem_subgroupOf.mpr hx'.1, fun a ha => ?_⟩
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    exact Subgroup.mem_subgroupOf.mpr (hx'.2 a ha')
  · intro hx
    rw [mem_relCent hEZH] at hx
    rw [Subgroup.mem_subgroupOf, mem_relCent hEZ]
    refine ⟨Subgroup.mem_subgroupOf.mp hx.1, fun a ha => ?_⟩
    have haH : a ∈ H := hAH ha
    have hcomm := hx.2 ⟨a, haH⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp hcomm

theorem natQuot_subgroupOf {H E Z : Subgroup G} {n : ℕ} (hEH : E ≤ H) (hZH : Z ≤ H)
    (h : NatQuot (⊤ : Subgroup ↥H) (E.subgroupOf H) (Z.subgroupOf H) n) :
    NatQuot H E Z n := by
  have hZE : Z ≤ E := by
    intro z hz
    have hz' : (⟨z, hZH hz⟩ : ↥H) ∈ Z.subgroupOf H := Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp (h.Z_le hz')
  have hEZH : E.subgroupOf H ≤ Subgroup.normalizer (Z.subgroupOf H : Set ↥H) :=
    fun x _ => (h.normal (Subgroup.mem_top x)).2
  have hNE : H ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_le_normalizer_subgroupOf hEH (h.normal.trans inf_le_left)
  have hNZ : H ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_le_normalizer_subgroupOf hZH (h.normal.trans inf_le_right)
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := hEH.trans hNZ
  have hrelH : Z ≤ H := hZH
  refine ⟨?_, hEH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : (⟨z, hZH hz⟩ : ↥H) ∈ Z.subgroupOf H := Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp (h.Z_le hz')
  · intro g hg
    exact Subgroup.mem_inf.mpr ⟨hNE hg, hNZ hg⟩
  · rw [← Subgroup.relIndex_subgroupOf hEH, h.index]
  · intro A hA
    have hA' : IsSylowTwoOf (A.subgroupOf H) (⊤ : Subgroup ↥H) :=
      CFSG.Quasithin.X1512.sylow_subgroupOf_top hA
    have hrc : (relCent E Z A).subgroupOf H =
        relCent (E.subgroupOf H) (Z.subgroupOf H) (A.subgroupOf H) :=
      relCent_subgroupOf hEH hZH hA.1 hEZ hEZH
    have hrel_le : relCent E Z A ≤ H := fun x hx => hEH hx.1
    rw [← Subgroup.relIndex_subgroupOf hrel_le, hrc, h.line (A.subgroupOf H) hA']
  · intro A hA
    have hA' : IsSylowTwoOf (A.subgroupOf H) (⊤ : Subgroup ↥H) :=
      CFSG.Quasithin.X1512.sylow_subgroupOf_top hA
    have hcommH : ⁅E, A⁆ ≤ H := Subgroup.commutator_le_of_le hEH hA.1
    have hrel_le : relCent E Z A ≤ H := fun x hx => hEH hx.1
    have hsub : ((⁅E, A⁆ ⊔ Z).subgroupOf H) = (relCent E Z A).subgroupOf H := by
      rw [Subgroup.subgroupOf_sup hcommH hZH,
        ← CFSG.GroupTheory.commutator_subgroupOf_eq hEH hA.1,
        relCent_subgroupOf hEH hZH hA.1 hEZ hEZH,
        h.comm_eq (A.subgroupOf H) hA']
    have hinf := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_of_le_left (sup_le hcommH hZH), inf_of_le_left hrel_le] at hinf
  · intro A A' hA hA' hnot
    have hA'' : IsSylowTwoOf (A.subgroupOf H) (⊤ : Subgroup ↥H) :=
      CFSG.Quasithin.X1512.sylow_subgroupOf_top hA
    have hB'' : IsSylowTwoOf (A'.subgroupOf H) (⊤ : Subgroup ↥H) :=
      CFSG.Quasithin.X1512.sylow_subgroupOf_top hA'
    have hnot' : ¬ A.subgroupOf H ≤ (A'.subgroupOf H) ⊔ E.subgroupOf H := by
      intro hle
      apply hnot
      intro a ha
      have haH : a ∈ H := hA.1 ha
      have hmem : (⟨a, haH⟩ : ↥H) ∈ (A'.subgroupOf H) ⊔ E.subgroupOf H :=
        hle (Subgroup.mem_subgroupOf.mpr ha)
      have hmemG : (⟨a, haH⟩ : ↥H) ∈ ((A' ⊔ E).subgroupOf H) := by
        rwa [Subgroup.subgroupOf_sup hA'.1 hEH]
      exact Subgroup.mem_subgroupOf.mp hmemG
    have hres := h.lines_inf (A.subgroupOf H) (A'.subgroupOf H) hA'' hB'' hnot'
    have hrelA_le : relCent E Z A ≤ H := fun x hx => hEH hx.1
    have hrelA'_le : relCent E Z A' ≤ H := fun x hx => hEH hx.1
    have hrcA : (relCent E Z A).subgroupOf H =
        relCent (E.subgroupOf H) (Z.subgroupOf H) (A.subgroupOf H) :=
      relCent_subgroupOf hEH hZH hA.1 hEZ hEZH
    have hrcA' : (relCent E Z A').subgroupOf H =
        relCent (E.subgroupOf H) (Z.subgroupOf H) (A'.subgroupOf H) :=
      relCent_subgroupOf hEH hZH hA'.1 hEZ hEZH
    refine ⟨?_, ?_⟩
    · have hinfEq : ((relCent E Z A ⊓ relCent E Z A').subgroupOf H) =
          (Z.subgroupOf H) := by
        calc
          ((relCent E Z A ⊓ relCent E Z A').subgroupOf H)
              = (relCent E Z A).subgroupOf H ⊓ (relCent E Z A').subgroupOf H := by
                change (relCent E Z A ⊓ relCent E Z A').comap H.subtype =
                  (relCent E Z A).comap H.subtype ⊓ (relCent E Z A').comap H.subtype
                rw [Subgroup.comap_inf]
          _ = relCent (E.subgroupOf H) (Z.subgroupOf H) (A.subgroupOf H) ⊓
                relCent (E.subgroupOf H) (Z.subgroupOf H) (A'.subgroupOf H) := by
                rw [hrcA, hrcA']
          _ = Z.subgroupOf H := hres.1
      have h := Subgroup.subgroupOf_inj.mp hinfEq
      have hle : relCent E Z A ⊓ relCent E Z A' ≤ H := fun x hx => hEH (Subgroup.mem_inf.mp hx).1.1
      rwa [inf_of_le_left hle, inf_of_le_left hZH] at h
    · have hsupEq : ((relCent E Z A ⊔ relCent E Z A').subgroupOf H) =
          (E.subgroupOf H) := by
        rw [Subgroup.subgroupOf_sup hrelA_le hrelA'_le, hrcA, hrcA', hres.2]
      have h := Subgroup.subgroupOf_inj.mp hsupEq
      have hle : relCent E Z A ⊔ relCent E Z A' ≤ H := sup_le hrelA_le hrelA'_le
      rwa [inf_of_le_left hle, inf_of_le_left hEH] at h
  · intro g hg hodd hgE e heE hcomm
    have hgH : (⟨g, hg⟩ : ↥H) ∉ E.subgroupOf H := by
      intro hmem
      exact hgE (Subgroup.mem_subgroupOf.mp hmem)
    have hodd' : Odd (orderOf (⟨g, hg⟩ : ↥H)) := by
      simpa [Subgroup.orderOf_mk] using hodd
    have heH : e ∈ H := hEH heE
    have heE' : (⟨e, heH⟩ : ↥H) ∈ E.subgroupOf H := Subgroup.mem_subgroupOf.mpr heE
    have hcomm' : ⁅(⟨e, heH⟩ : ↥H), (⟨g, hg⟩ : ↥H)⁆ ∈ Z.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hcomm
    exact Subgroup.mem_subgroupOf.mp
      (h.fpf ⟨g, hg⟩ (Subgroup.mem_top _) hodd' hgH ⟨e, heH⟩ heE' hcomm')
  · intro A hZA hAE hnorm
    have hA_le_H : A ≤ H := hAE.trans hEH
    have hZ' : Z.subgroupOf H ≤ A.subgroupOf H :=
      fun x hx => Subgroup.mem_subgroupOf.mpr (hZA (Subgroup.mem_subgroupOf.mp hx))
    have hA' : A.subgroupOf H ≤ E.subgroupOf H :=
      fun x hx => Subgroup.mem_subgroupOf.mpr (hAE (Subgroup.mem_subgroupOf.mp hx))
    have hnorm' : ⊤ ≤ Subgroup.normalizer (A.subgroupOf H : Set ↥H) :=
      le_normalizer_subgroupOf_of_le_normalizer hA_le_H hnorm
    rcases h.irred (A.subgroupOf H) hZ' hA' hnorm' with hres | hres
    · left
      have h := Subgroup.subgroupOf_inj.mp hres
      rwa [inf_of_le_left hA_le_H, inf_of_le_left hZH] at h
    · right
      have h := Subgroup.subgroupOf_inj.mp hres
      rwa [inf_of_le_left hA_le_H, inf_of_le_left hEH] at h

theorem natQuot_of_baumann_one_top {H : Type} [Group H] [Finite H] {P : Subgroup H}
    (hc : CharTwo (⊤ : Subgroup H)) (hq : IsL2Quot 1 (oTwoQuot ↥(⊤ : Subgroup H)))
    (hP : IsSylowTwoOf P (⊤ : Subgroup H)) (hnc : NoCharNormal P (⊤ : Subgroup H))
    (he : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup H))) :
    NatQuot (⊤ : Subgroup H) (pCoreOf 2 (⊤ : Subgroup H)) (centerOf (⊤ : Subgroup H)) 1 ∧
      ⁅pCoreOf 2 (⊤ : Subgroup H), oTwoRes (⊤ : Subgroup H)⁆ ≠ ⊥ := by
  classical
  let E : Subgroup H := pCoreOf 2 (⊤ : Subgroup H)
  let Z0 : Subgroup H := zZero (⊤ : Subgroup H) E
  have hCE : Subgroup.centralizer (E : Set H) ≤ E := by
    intro x hx
    exact hc ⟨Subgroup.mem_top x, hx⟩
  have hEcent : E ≤ Subgroup.centralizer (E : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (he.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)).symm
  have hcent_eq : (⊤ : Subgroup H) ⊓ Subgroup.centralizer (E : Set H) = E := by
    rw [top_inf_eq]
    exact le_antisymm hCE hEcent
  have hPush : PushHyp (⊤ : Subgroup H) P E :=
    ⟨hP, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup H), he, le_rfl, hcent_eq⟩
  have hqPerm : Nonempty (OTwoQuot (⊤ : Subgroup H) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := hq
    exact ⟨e.trans permThreeEquivPSL.symm⟩
  have hJ : ¬ thompsonJ P ≤ E :=
    not_thompsonJ_le_pCoreOf (Or.inl rfl) hq hP hnc
  have hinat : IsNat3Sec (⊤ : Subgroup H) Z0 E :=
    hss18S3_holds H (⊤ : Subgroup H) P E hPush hqPerm hJ
  have hinat0 : IsNat3Sec (⊤ : Subgroup H) Z0 E := hinat
  have hmodel : IsModelSec nat3 (⊤ : Subgroup H) Z0 E := hinat
  have hmodel' : IsModelSec nat3 (⊤ : Subgroup H) Z0 E := hmodel
  obtain ⟨hZnθ, θ, β, hθs, hθk, hsd⟩ := hmodel
  letI : (Z0.subgroupOf E).Normal := hZnθ
  have hZ0le : Z0 ≤ E := inf_le_left
  have hsec : IsSec (⊤ : Subgroup H) Z0 E := IsModelSec.isSec hmodel' hZ0le
  have hZ0rel : Z0.relIndex E = 4 := by
    simpa using IsNat3Sec.relIndex_eq hinat0
  let e : OTwoQuot (⊤ : Subgroup H) ≃* Equiv.Perm (Fin 3) := Classical.choice hqPerm
  have hcSec : cSecIn (⊤ : Subgroup H) Z0 E = E := by
    have hEc : E ≤ cSecIn (⊤ : Subgroup H) Z0 E := by
      intro x hx
      rw [mem_cSecIn_iff hsec.normL]
      refine ⟨Subgroup.mem_top x, fun y hy => ?_⟩
      have hxy : x * y = y * x :=
        congrArg Subtype.val (he.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [hxy]
        group
      rw [h1]
      exact Z0.one_mem
    have hErel : E.relIndex (⊤ : Subgroup H) = 6 := by
      rw [show E = pCoreOf 2 (⊤ : Subgroup H) from rfl]
      exact relIndex_core_eq_six e
    have hcSecRel : (cSecIn (⊤ : Subgroup H) Z0 E).relIndex (⊤ : Subgroup H) = 6 := by
      change ((cSecIn (⊤ : Subgroup H) Z0 E).subgroupOf (⊤ : Subgroup H)).index = 6
      rw [← hθk]
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθs, Subgroup.card_top]
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num
    have hmul := Subgroup.relIndex_mul_relIndex E (cSecIn (⊤ : Subgroup H) Z0 E)
      (⊤ : Subgroup H) hEc le_top
    rw [hErel, hcSecRel] at hmul
    have hone : E.relIndex (cSecIn (⊤ : Subgroup H) Z0 E) = 1 := by omega
    have hle : cSecIn (⊤ : Subgroup H) Z0 E ≤ E :=
      (Subgroup.relIndex_eq_one (H := E) (K := cSecIn (⊤ : Subgroup H) Z0 E)).mp hone
    exact le_antisymm hle hEc
  have hAE : ∀ A : Subgroup H, IsSylowTwoOf A (⊤ : Subgroup H) →
      E ≤ A ∧ E.relIndex A = 2 := by
    intro A hA
    have hPushA : PushHyp (⊤ : Subgroup H) A E :=
      ⟨hA, hPush.normal, he, hPush.le_core, hPush.cent_eq⟩
    exact ⟨pCoreOf_le_of_isSylowTwoOf hA, by
      rw [show E = pCoreOf 2 (⊤ : Subgroup H) from rfl]
      exact relIndex_core_sylow hPushA e⟩
  have hnat : NatQuot (⊤ : Subgroup H) E Z0 1 :=
    natQuot_of_isNat3Sec hinat0 hZ0le le_top hAE hcSec
  have hcenter : Z0 = centerOf (⊤ : Subgroup H) := by
    have hZ0_eq : Z0 = E ⊓ Subgroup.centralizer (pResidualOf 2 (⊤ : Subgroup H) : Set H) := by
      change zZero (⊤ : Subgroup H) E = _
      rw [zZero_eq, pResidualOf_eq_oTwoRes]
    have hZ0_C_R : Z0 ≤ Subgroup.centralizer (pResidualOf 2 (⊤ : Subgroup H) : Set H) := by
      rw [hZ0_eq]
      exact inf_le_right
    obtain ⟨A, hA, hAQ⟩ := exists_offender (S := P) (Q := E) hJ
    obtain ⟨hArel, hAPsup⟩ := offender_s3_aux hPush e hA hAQ
    obtain ⟨a, haA, haE⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have haP : a ∈ P := hA.1 haA
    have ha2 : a ^ 2 ∈ E := by
      have h1 : a ^ 2 = 1 := hA.2.1.2 a haA
      rw [h1]
      exact E.one_mem
    have hidx_Ca : (E ⊓ Subgroup.centralizer ({a} : Set H)).relIndex E ≤ 2 := by
      have hCA_le : E ⊓ Subgroup.centralizer (A : Set H) ≤
          E ⊓ Subgroup.centralizer ({a} : Set H) := by
        refine inf_le_inf_left _ ?_
        intro x hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        have hya : y = a := by simpa using hy
        simpa [hya] using hx a haA
      have h1 := relIndex_le_of_le (L := E) hCA_le
      have h2 := offender_count hPush hA
      omega
    have hEa_bound : Nat.card ↥⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ≤ 2 :=
      (card_commutator_zpowers_le_relIndex he.1 he.2
        (hPush.normal (Subgroup.mem_top a)) ha2).trans hidx_Ca
    have hErelP : E.relIndex P = 2 := by
      rw [show E = pCoreOf 2 (⊤ : Subgroup H) from rfl]
      exact relIndex_core_sylow hPush e
    have hnot_le : ¬ ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ≤ Z0 := by
      intro hle
      apply haE
      have haC : a ∈ cSecIn (⊤ : Subgroup H) Z0 E := by
        refine Subgroup.subset_closure ⟨Subgroup.mem_top a, fun x hx => ?_⟩
        have hcomm : ⁅x, a⁆ ∈ Z0 :=
          hle (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a))
        have := Z0.inv_mem hcomm
        have e' : a * x * a⁻¹ * x⁻¹ = ⁅x, a⁆⁻¹ := by
          rw [commutatorElement_def]
          group
        simpa [e'] using this
      rwa [hcSec] at haC
    have hcomm_ne_bot : ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ≠ ⊥ := by
      intro hbot
      exact hnot_le (by rw [hbot]; exact bot_le)
    have hcard_comm : Nat.card ↥⁅E, (Subgroup.zpowers a : Subgroup H)⁆ = 2 := by
      have hge : 1 < Nat.card ↥⁅E, (Subgroup.zpowers a : Subgroup H)⁆ :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hcomm_ne_bot
      omega
    have hinter_bot : ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0 = ⊥ := by
      by_contra hne
      have hge : 2 ≤ Nat.card ↥(⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0) := by
        have h1 : 1 < Nat.card ↥(⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0) :=
          (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
        omega
      have hle : Nat.card ↥(⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0) ≤ 2 := by
        calc Nat.card ↥(⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0)
            ≤ Nat.card ↥⁅E, (Subgroup.zpowers a : Subgroup H)⁆ :=
              Subgroup.card_le_of_le inf_le_left
          _ = 2 := hcard_comm
      have hcard : Nat.card ↥(⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0) = 2 :=
        le_antisymm hle hge
      have heq : ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0 =
          ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hcard_comm])
      exact hnot_le (by rw [← heq]; exact inf_le_right)
    have hcenter_le : centerOf (⊤ : Subgroup H) ≤ Z0 := by
      intro y hy
      rw [hZ0_eq, Subgroup.mem_inf]
      refine ⟨hCE ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        rw [centerOf, Subgroup.mem_inf] at hy
        exact Subgroup.mem_centralizer_iff.mp hy.2 e (Subgroup.mem_top e)
      · rw [Subgroup.mem_centralizer_iff]
        intro r hr
        rw [centerOf, Subgroup.mem_inf] at hy
        exact Subgroup.mem_centralizer_iff.mp hy.2 r (Subgroup.mem_top r)
    refine le_antisymm ?_ hcenter_le
    intro z hzZ0
    have hzE : z ∈ E := hZ0le hzZ0
    have hZa : a ∈ Subgroup.normalizer (Z0 : Set H) := hsec.normL (Subgroup.mem_top a)
    have hE_comm_z : ∀ x ∈ E, x * z = z * x := by
      intro x hx
      exact congrArg Subtype.val (he.1.is_comm.comm ⟨x, hx⟩ ⟨z, hzE⟩)
    have hza_comm : a * z = z * a := by
      have hw : ⁅z, a⁆ = 1 := by
        have hwZ : ⁅z, a⁆ ∈ Z0 := by
          have h1 : a * z⁻¹ * a⁻¹ ∈ Z0 :=
            (Subgroup.mem_normalizer_iff.mp hZa z⁻¹).mp (Z0.inv_mem hzZ0)
          have e' : ⁅z, a⁆ = z * (a * z⁻¹ * a⁻¹) := by
            rw [commutatorElement_def]
            group
          rw [e']
          exact Z0.mul_mem hzZ0 h1
        have hwE : ⁅z, a⁆ ∈ ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ :=
          Subgroup.commutator_mem_commutator hzE (Subgroup.mem_zpowers a)
        have hmem : ⁅z, a⁆ ∈ ⁅E, (Subgroup.zpowers a : Subgroup H)⁆ ⊓ Z0 :=
          Subgroup.mem_inf.mpr ⟨hwE, hwZ⟩
        rwa [hinter_bot, Subgroup.mem_bot] at hmem
      have := commutatorElement_eq_one_iff_mul_comm.mp hw
      exact this.symm
    have hP_central : P ≤ Subgroup.centralizer ({z} : Set H) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hpE : p ∈ E
      · exact hE_comm_z p hpE
      · have hidx : (E.subgroupOf P).index = 2 := by
          change E.relIndex P = 2
          exact hErelP
        have hpa : p * a⁻¹ ∈ E := by
          have hmem : (⟨p, hp⟩ : ↥P) * (⟨a, haP⟩ : ↥P)⁻¹ ∈ E.subgroupOf P :=
            (Subgroup.mul_mem_iff_of_index_two hidx).2 (by
              constructor
              · intro h
                exact False.elim (hpE (Subgroup.mem_subgroupOf.mp h))
              · intro h
                have haInv : a⁻¹ ∈ E := by simpa using Subgroup.mem_subgroupOf.mp h
                exact False.elim (haE (by simpa using E.inv_mem haInv)))
          exact Subgroup.mem_subgroupOf.mp hmem
        have hp_eq : p = (p * a⁻¹) * a := by group
        calc p * z = ((p * a⁻¹) * a) * z := by conv_lhs => rw [hp_eq]
          _ = (p * a⁻¹) * (a * z) := by group
          _ = (p * a⁻¹) * (z * a) := by rw [hza_comm]
          _ = ((p * a⁻¹) * z) * a := by group
          _ = (z * (p * a⁻¹)) * a := by rw [hE_comm_z (p * a⁻¹) hpa]
          _ = z * ((p * a⁻¹) * a) := by group
          _ = z * p := by conv_lhs => rw [← hp_eq]
    have htop_central : (⊤ : Subgroup H) ≤ Subgroup.centralizer ({z} : Set H) := by
      rw [← pResidualOf_sup_eq_of_sylow hP]
      exact sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hZ0_C_R hzZ0) r hr)) hP_central
    have hz_center : z ∈ centerOf (⊤ : Subgroup H) := by
      rw [centerOf, Subgroup.mem_inf]
      refine ⟨Subgroup.mem_top z, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hy := htop_central (Subgroup.mem_top y)
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      exact hy
    exact hz_center

  refine ⟨?_, ?_⟩
  · simpa [E, hcenter] using hnat
  · change ⁅E, oTwoRes (⊤ : Subgroup H)⁆ ≠ ⊥
    intro hcomm_bot
    obtain ⟨d, hdR, hdX, k, hdk⟩ := exists_odd_elt (X := (⊤ : Subgroup H)) θ hθs (c := c3)
    have hc3ord : orderOf c3 = 3 := orderOf_eq_prime c3_pow_three c3_ne_one
    have hc3odd : Odd (orderOf c3) := by rw [hc3ord]; decide
    obtain ⟨-, hne⟩ := odd_orderOf_pow_two_pow (c := c3) hc3odd k
    have hd1 : θ ⟨d, hdX⟩ ≠ 1 := by
      intro h1
      apply c3_ne_one
      apply hne
      rwa [hdk] at h1
    have hd3 : (θ ⟨d, hdX⟩) ^ 3 = 1 := by
      rw [hdk, ← pow_mul, mul_comm (2 ^ k) 3, pow_mul, c3_pow_three, one_pow]
    have hfixbot : fixW nat3 (Subgroup.zpowers (θ ⟨d, hdX⟩)) = ⊥ :=
      nat3_fixW_eq_bot_of_order_three hd1 hd3
    have hfixTop : fixW nat3 (Subgroup.zpowers (θ ⟨d, hdX⟩)) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rw [mem_fixW_zpowers_iff]
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Z0.subgroupOf E) (β u)
      have hcomm1 : ⁅(x : H), (d : H)⁆ = 1 := by
        have hmem := Subgroup.commutator_mem_commutator x.2 hdR
        rwa [hcomm_bot, Subgroup.mem_bot] at hmem
      have hcommute : (d : H) * (x : H) = (x : H) * (d : H) := by
        have := commutatorElement_eq_one_iff_mul_comm.mp hcomm1
        exact this.symm
      have hdx : (d : H) * (x : H) * (d : H)⁻¹ = (x : H) := by
        rw [hcommute]
        group
      obtain ⟨hkx, heq⟩ := hsd.equiv ⟨d, hdX⟩ u x hx.symm
      have hxsub : (⟨(d : H) * (x : H) * (d : H)⁻¹, hkx⟩ : ↥E) = x :=
        Subtype.ext hdx
      rw [hxsub] at heq
      have hx' : (QuotientGroup.mk x : ↥E ⧸ Z0.subgroupOf E) = β u := by
        simpa [QuotientGroup.mk'_apply] using hx
      rw [hx'] at heq
      exact hsd.inj heq
    have htopbot : (⊤ : Subgroup nat3.W) = ⊥ := hfixTop.symm.trans hfixbot
    have hne_top : (⊤ : Subgroup nat3.W) ≠ ⊥ := by
      intro h
      have h1 : Nat.card (⊤ : Subgroup nat3.W) = Nat.card (⊥ : Subgroup nat3.W) := by rw [h]
      rw [Subgroup.card_top, Subgroup.card_bot, card_nat3] at h1
      norm_num at h1
    exact hne_top htopbot

theorem oTwoUpper_top_subgroupOf (L : Subgroup G) :
    oTwoUpper (⊤ : Subgroup ↥L) = (oTwoUpper L).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le L), oTwoUpper, oTwoUpper,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy.2⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, ⟨Subgroup.mem_top _, by simpa using hx.2⟩, rfl⟩

theorem oTwoUpper_le_pResidualOf (X : Subgroup G) : oTwoUpper X ≤ pResidualOf 2 X := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxX, hxodd⟩
  refine ⟨⟨x, hxX⟩, ?_, rfl⟩
  show (⟨x, hxX⟩ : ↥X) ∈ pResidual 2 ↥X
  unfold pResidual
  simp only [Subgroup.mem_iInf]
  intro N hN hNk
  obtain ⟨k, hk⟩ := hNk ⟨x, hxX⟩
  have hord : orderOf (⟨x, hxX⟩ : ↥X) = orderOf x := Subgroup.orderOf_mk x hxX
  have hcop : Nat.Coprime (2 ^ k) (orderOf (⟨x, hxX⟩ : ↥X)) := by
    rw [hord]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hxodd)
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem natQuot_of_baumann_one {G : Type} [Group G] {L P : Subgroup G} [Finite ↥L]
    (hc : CharTwo L) (hq : IsL2Quot 1 (oTwoQuot ↥L)) (hP : IsSylowTwoOf P L)
    (hnc : NoCharNormal P L) (he : IsElemAbelian 2 (pCoreOf 2 L)) :
    NatQuot L (pCoreOf 2 L) (centerOf L) 1 ∧
      ⁅pCoreOf 2 L, pResidualOf 2 L⁆ ≠ ⊥ := by
  let E : Subgroup G := pCoreOf 2 L
  let Z : Subgroup G := centerOf L
  have hEtop : pCoreOf 2 (⊤ : Subgroup ↥L) = E.subgroupOf L := by
    ext x
    rw [CFSG.Quasithin.F53Push.pCoreOf_top_eq, ← CFSG.Quasithin.F53Push.mem_pCoreOf_iff x,
      Subgroup.mem_subgroupOf]
  have hZtop : centerOf (⊤ : Subgroup ↥L) = Z.subgroupOf L := by
    ext x
    change x ∈ (⊤ : Subgroup ↥L) ⊓ Subgroup.centralizer (⊤ : Set ↥L) ↔
      x ∈ (L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf L
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hx⟩
      refine ⟨x.2, ?_⟩
      change (x : G) ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simpa using congrArg Subtype.val (hx ⟨y, hy⟩ (Subgroup.mem_top _))
    · rintro ⟨-, hx⟩
      refine ⟨Subgroup.mem_top x, ?_⟩
      change x ∈ Subgroup.centralizer (⊤ : Set ↥L)
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      apply Subtype.ext
      simpa using hx y y.2
  have hctop : CharTwo (⊤ : Subgroup ↥L) := by
    simpa using CFSG.Quasithin.EmptyFaithfulMultiple.L15422.charTwo_subgroupOf
      (X := L) (L := L) le_rfl hc
  have hqtop : IsL2Quot 1 (oTwoQuot ↥(⊤ : Subgroup ↥L)) := by
    obtain ⟨eL⟩ := hq
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr (Subgroup.topEquiv)).trans eL⟩
  have hPtop : IsSylowTwoOf (P.subgroupOf L) (⊤ : Subgroup ↥L) :=
    CFSG.Quasithin.X1512.sylow_subgroupOf_top hP
  have hnctop : NoCharNormal (P.subgroupOf L) (⊤ : Subgroup ↥L) :=
    noCharNormal_subgroupOf hP.1 hnc
  have hetop : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup ↥L)) := by
    have h : IsElemAbelian 2 (E.subgroupOf L) := by
      refine ⟨?_, ?_⟩
      · exact IsMulCommutative.of_comm (fun x y => by
          apply Subtype.ext
          apply Subtype.ext
          simpa using congrArg Subtype.val (he.1.is_comm.comm
            ⟨((x : ↥L) : G), Subgroup.mem_subgroupOf.mp x.2⟩
            ⟨((y : ↥L) : G), Subgroup.mem_subgroupOf.mp y.2⟩))
      · intro x hx
        have hxG : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
        apply Subtype.ext
        simpa using he.2 (x : G) hxG
    simpa [hEtop] using h
  have htop := natQuot_of_baumann_one_top hctop hqtop hPtop hnctop hetop
  have hinput : NatQuot (⊤ : Subgroup ↥L) (E.subgroupOf L) (Z.subgroupOf L) 1 := by
    simpa [hEtop, hZtop] using htop.1
  have hL : NatQuot L E Z 1 :=
    natQuot_subgroupOf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (fun x hx => (Subgroup.mem_inf.mp hx).1) hinput
  have hRtop : oTwoRes (⊤ : Subgroup ↥L) = (oTwoUpper L).subgroupOf L := by
    rw [oTwoRes_eq_oTwoUpper, oTwoUpper_top_subgroupOf]
  refine ⟨?_, ?_⟩
  · simpa [E, Z] using hL
  · intro hbot
    have hbotO : ⁅E, oTwoUpper L⁆ = ⊥ := by
      rw [eq_bot_iff]
      calc ⁅E, oTwoUpper L⁆ ≤ ⁅E, pResidualOf 2 L⁆ :=
            Subgroup.commutator_mono le_rfl (oTwoUpper_le_pResidualOf L)
        _ = ⊥ := hbot
    have hcommSub : ⁅pCoreOf 2 (⊤ : Subgroup ↥L), oTwoRes (⊤ : Subgroup ↥L)⁆ =
        (⁅E, oTwoUpper L⁆).subgroupOf L := by
      rw [hEtop, hRtop,
        CFSG.GroupTheory.commutator_subgroupOf_eq (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
          (oTwoUpper_le L)]
    apply htop.2
    rw [hcommSub, hbotO]
    simp

end CFSG.Quasithin.St84
