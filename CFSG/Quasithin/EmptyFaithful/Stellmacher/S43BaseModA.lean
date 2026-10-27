module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDict

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

@[expose] def commTwoF : Finset orth.W :=
  spanF (commGensF orth S5SylF (spanF (commGensF orth S5SylF Finset.univ)))

set_option maxRecDepth 100000 in
private theorem fix_le_commIterF : ∀ w ∈ (Finset.univ : Finset orth.W),
    (∀ b ∈ S5SylF, orth.act b w = w) → w ∈ commTwoF := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem centralizer_commIterF : ∀ σ ∈ S5SylF,
    ((∀ y ∈ commTwoF, orth.act σ y = y) ↔ σ ∈ S5ThatF) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem normalizer_commIterF : ∀ σ : Perm (Fin 5),
    ((∀ y ∈ commTwoF, orth.act σ y ∈ commTwoF) ↔
      σ ∈ S5SylF) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem comm_That_commIterF : ∀ w : orth.W,
    w ∈ spanF (commGensF orth S5ThatF Finset.univ) ↔ w ∈ commTwoF := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem comm_commTwoF_fixF : ∀ w : orth.W,
    w ∈ spanF (commGensF orth S5SylF commTwoF) ↔ ∀ b ∈ S5SylF, orth.act b w = w := by
  decide +kernel

private theorem S5That_le_S5SylF : ∀ τ ∈ S5ThatF, τ ∈ S5SylF := by decide +kernel

theorem nat_card_S5That : Nat.card S5That = 4 := by
  have h : S5ThatF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

theorem S5That_le_S5Syl : S5That ≤ S5Syl := fun τ hτ =>
  (mem_S5Syl_iff τ).mpr (S5That_le_S5SylF τ ((mem_S5That_iff τ).mp hτ))

theorem commIter_two_eq :
    F53Mod.commIter orth S5Syl 2 = commW orth S5Syl (commW orth S5Syl ⊤) := rfl

theorem mem_commIter_two_iff (w : orth.W) :
    w ∈ F53Mod.commIter orth S5Syl 2 ↔ w ∈ commTwoF := by
  rw [commIter_two_eq]
  exact mem_commW_iff orth mem_S5Syl_iff
    (fun u => mem_commW_iff orth mem_S5Syl_iff (Uf := Finset.univ) (fun u => by simp) u) w

theorem card_commW_S5Syl : Nat.card (commW orth S5Syl ⊤) = 8 :=
  congrArg (fun p => p.1) profile_orth.2.2.2.2.2

theorem card_commIter_two : Nat.card (F53Mod.commIter orth S5Syl 2) = 4 :=
  congrArg (fun p => p.2.2) profile_orth.2.2.2.2.2

theorem fixW_S5Syl_le_commIter_two : fixW orth S5Syl ≤ F53Mod.commIter orth S5Syl 2 := by
  intro w hw
  rw [mem_commIter_two_iff]
  exact fix_le_commIterF w (Finset.mem_univ w) fun b hb => hw b ((mem_S5Syl_iff b).mpr hb)

theorem fix_commIter_two_iff {σ : Perm (Fin 5)} (hσ : σ ∈ S5Syl) :
    (∀ y ∈ F53Mod.commIter orth S5Syl 2, orth.act σ y = y) ↔ σ ∈ S5That := by
  rw [mem_S5That_iff]
  refine Iff.trans ?_ (centralizer_commIterF σ ((mem_S5Syl_iff σ).mp hσ))
  exact forall_congr' fun y => by rw [mem_commIter_two_iff]

theorem invariant_commIter_two_iff (σ : Perm (Fin 5)) :
    (∀ y ∈ F53Mod.commIter orth S5Syl 2, orth.act σ y ∈ F53Mod.commIter orth S5Syl 2) ↔
      σ ∈ S5Syl := by
  rw [mem_S5Syl_iff]
  refine Iff.trans ?_ (normalizer_commIterF σ)
  exact forall_congr' fun y => by rw [mem_commIter_two_iff, mem_commIter_two_iff]

theorem commW_commIter_two_eq_fixW :
    commW orth S5Syl (F53Mod.commIter orth S5Syl 2) = fixW orth S5Syl := by
  ext w
  rw [mem_commW_iff orth mem_S5Syl_iff (Uf := commTwoF) mem_commIter_two_iff w,
    comm_commTwoF_fixF w, mem_fixW]
  exact ⟨fun h b hb => h b ((mem_S5Syl_iff b).mp hb), fun h b hb => h b ((mem_S5Syl_iff b).mpr hb)⟩

theorem commW_S5That_eq_commIter_two : commW orth S5That ⊤ = F53Mod.commIter orth S5Syl 2 := by
  ext w
  rw [mem_commIter_two_iff,
    mem_commW_iff orth mem_S5That_iff (Uf := Finset.univ) (fun u => by simp) w]
  exact comm_That_commIterF w

variable {G : Type} [Group G] {X S Z : Subgroup G}

namespace Dict5

variable (D : Dict5 X S Z)

theorem comm_comm_eq :
    ⁅⁅Z, S⁆, S⁆ = (F53Mod.commIter orth S5Syl 2).map D.φ := by
  rw [← D.map_commW_top D.S_le, ← D.map_commW D.S_le, D.bar_S, commIter_two_eq]

theorem comm_eq : ⁅Z, S⁆ = (commW orth S5Syl ⊤).map D.φ := by
  rw [← D.map_commW_top D.S_le, D.bar_S]

theorem fix_eq : Z ⊓ Subgroup.centralizer (S : Set G) = (fixW orth S5Syl).map D.φ := by
  rw [← D.map_fixW D.S_le, D.bar_S]

theorem mem_centralizer_Y_iff (x : ↥X) :
    (x : G) ∈ S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) ↔ D.ψ x ∈ S5That := by
  rw [Subgroup.mem_inf, D.mem_S_iff, D.comm_comm_eq, D.mem_centralizer_map_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact (fix_commIter_two_iff h1).mp h2
  · intro h
    have h1 : D.ψ x ∈ S5Syl := S5That_le_S5Syl h
    exact ⟨h1, (fix_commIter_two_iff h1).mpr h⟩

end Dict5

theorem card_comm_S [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) : Nat.card ↥⁅Z, S⁆ = 8 := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  rw [D.comm_eq, D.card_map_φ, card_commW_S5Syl]

theorem eq_comm_comm_of_inv [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) :
    ∀ U : Subgroup G, U ≤ Z → S ≤ Subgroup.normalizer (U : Set G) → Nat.card U = 4 →
      U = ⁅⁅Z, S⁆, S⁆ := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  intro U hUZ hSn hU4
  have hinv : IsInvSub orth S5Syl (U.comap D.φ) := by
    rw [← D.bar_S]
    exact (D.invariant_iff D.S_le hUZ).mp fun k hk u hu =>
      ((Subgroup.mem_normalizer_iff.mp (hSn hk)) u).mp hu
  have hcard : Nat.card (U.comap D.φ) = 2 ^ 2 := by
    rw [← D.card_map_φ, D.map_comap_φ hUZ, hU4]
    norm_num
  have hY : Nat.card (F53Mod.commIter orth S5Syl 2) = 2 ^ 2 := by
    rw [card_commIter_two]
    norm_num
  have heq : U.comap D.φ = F53Mod.commIter orth S5Syl 2 :=
    (lemma26 orth (Or.inl rfl) 2 (by norm_num)).unique ⟨hinv, hcard⟩
      ⟨isInvSub_commIter orth S5Syl 2, hY⟩
  rw [D.comm_comm_eq, ← heq, D.map_comap_φ hUZ]

theorem comm_comm_comm_S [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) :
    ⁅⁅⁅Z, S⁆, S⁆, S⁆ = Z ⊓ Subgroup.centralizer (S : Set G) := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  rw [D.comm_comm_eq, ← D.map_commW D.S_le, D.bar_S, D.fix_eq, commW_commIter_two_eq_fixW]

theorem comm_le [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) : ⁅Z, S⁆ ≤ Z := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  exact D.commutator_le D.S_le

theorem comm_comm_le_comm [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) : ⁅⁅Z, S⁆, S⁆ ≤ ⁅Z, S⁆ :=
  Subgroup.commutator_mono (comm_le hq hS hZ) le_rfl

theorem relIndex_centralizer_Y [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) :
    (S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G)).relIndex S = 2 := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  set K := S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) with hK
  have hKS : K ≤ S := inf_le_left
  have hKX : K ≤ X := hKS.trans D.S_le
  have hQK : pCoreOf 2 X ≤ K := fun x hx => by
    have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
    refine (D.mem_centralizer_Y_iff ⟨x, hxX⟩).mpr ?_
    rw [(D.ker_iff ⟨x, hxX⟩).mpr hx]
    exact one_mem _
  have hbar : D.bar K = S5That := D.bar_eq_of_iff D.mem_centralizer_Y_iff
  have h1 := D.card_bar hKX
  have h2 := D.card_bar D.S_le
  rw [hbar, nat_card_S5That, inf_of_le_left hQK] at h1
  rw [D.bar_S, card_S5Syl, inf_of_le_left D.Q_le] at h2
  have h3 := Subgroup.relIndex_mul_relIndex _ _ _ hQK hKS
  rw [← h1, ← h2] at h3
  omega

theorem comm_centralizer_Y [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) :
    ⁅Z, S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G)⁆ = ⁅⁅Z, S⁆, S⁆ := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  have hKX : S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) ≤ X :=
    inf_le_left.trans D.S_le
  have hbar : D.bar (S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G)) = S5That :=
    D.bar_eq_of_iff D.mem_centralizer_Y_iff
  rw [← D.map_commW_top hKX, hbar, commW_S5That_eq_commIter_two, D.comm_comm_eq]

theorem normalizer_Y [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) :
    X ⊓ Subgroup.normalizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) = S := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  ext x
  constructor
  · rintro ⟨hxX, hxN⟩
    rw [D.comm_comm_eq] at hxN
    have := (invariant_commIter_two_iff (D.ψ ⟨x, hxX⟩)).mp
      ((D.mem_normalizer_map_iff _ ⟨x, hxX⟩).mp hxN)
    exact (D.mem_S_iff ⟨x, hxX⟩).mpr this
  · intro hxS
    refine ⟨D.S_le hxS, ?_⟩
    rw [D.comm_comm_eq]
    exact (D.mem_normalizer_map_iff _ ⟨x, D.S_le hxS⟩).mpr
      ((invariant_commIter_two_iff _).mpr (D.ψ_mem_S5Syl hxS))

end CFSG.Quasithin.F53.Stellmacher.S43
