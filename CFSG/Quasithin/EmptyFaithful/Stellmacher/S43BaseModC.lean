module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

@[expose] def fixOrthF (Af : Finset (Perm (Fin 5))) : Finset orth.W :=
  Finset.univ.filter fun w => ∀ b ∈ Af, orth.act b w = w

@[expose] def S5SylE : Fin 8 → Perm (Fin 5) :=
  ![1, S5g, S5g ^ 2, S5g ^ 3, swap 0 2, S5g * swap 0 2, S5g ^ 2 * swap 0 2, S5g ^ 3 * swap 0 2]

@[expose] def OfdMul (Af : Finset (Perm (Fin 5))) : Prop := ∀ a ∈ Af, ∀ b ∈ Af, a * b ∈ Af

instance (Af : Finset (Perm (Fin 5))) : Decidable (OfdMul Af) := by unfold OfdMul; infer_instance

@[expose] def OfdComm (Af : Finset (Perm (Fin 5))) : Prop := ∀ a ∈ Af, ∀ b ∈ Af, a * b = b * a

instance (Af : Finset (Perm (Fin 5))) : Decidable (OfdComm Af) := by unfold OfdComm; infer_instance

@[expose] def OfdSq (Af : Finset (Perm (Fin 5))) : Prop := ∀ a ∈ Af, a * a = 1

instance (Af : Finset (Perm (Fin 5))) : Decidable (OfdSq Af) := by unfold OfdSq; infer_instance

@[expose] def OfdCard (Af : Finset (Perm (Fin 5))) : Prop := Af.card * (fixOrthF Af).card = 16

instance (Af : Finset (Perm (Fin 5))) : Decidable (OfdCard Af) := by unfold OfdCard; infer_instance

@[expose] def OfdConcl (Af : Finset (Perm (Fin 5))) : Prop :=
  Af = {1} ∨ Af = {1, swap 0 2} ∨ Af = {1, swap 1 3} ∨ Af = S5ThatF

instance (Af : Finset (Perm (Fin 5))) : Decidable (OfdConcl Af) := by
  unfold OfdConcl; infer_instance

private theorem image_S5SylE : (Finset.univ : Finset (Fin 8)).image S5SylE = S5SylF := by
  unfold S5SylF; decide +kernel

set_option maxRecDepth 100000 in
private theorem offender_finite : ∀ s ∈ (Finset.univ : Finset (Fin 8)).powerset,
    (1 : Perm (Fin 5)) ∈ s.image S5SylE → OfdMul (s.image S5SylE) → OfdComm (s.image S5SylE) →
      OfdSq (s.image S5SylE) → OfdCard (s.image S5SylE) → OfdConcl (s.image S5SylE) := by
  decide +kernel

theorem offender_perm (A : Subgroup (Perm (Fin 5))) (hA : A ≤ S5Syl)
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1)
    (hidx : Nat.card A = (fixW orth A).index) :
    (∀ σ, σ ∈ A ↔ σ = 1) ∨
      (∃ τ : Perm (Fin 5), (τ = swap 0 2 ∨ τ = swap 1 3) ∧ ∀ σ, σ ∈ A ↔ σ = 1 ∨ σ = τ) ∨
      A = S5That := by
  classical
  set s : Finset (Fin 8) := Finset.univ.filter fun i => S5SylE i ∈ A with hs
  set Af : Finset (Perm (Fin 5)) := s.image S5SylE with hAf
  have hmem : ∀ σ, σ ∈ A ↔ σ ∈ Af := by
    intro σ
    constructor
    · intro hσ
      have h1 : σ ∈ S5SylF := (mem_S5Syl_iff σ).mp (hA hσ)
      rw [← image_S5SylE, Finset.mem_image] at h1
      obtain ⟨i, -, rfl⟩ := h1
      exact Finset.mem_image.mpr ⟨i, by simp [hs, hσ], rfl⟩
    · intro hσ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hσ
      simpa [hs] using hi
  have hcardA : Nat.card A = Af.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  have hcardF : Nat.card (fixW orth A) = (fixOrthF Af).card := card_fixW orth hmem
  have h16 : OfdCard Af := by
    unfold OfdCard
    rw [← hcardA, ← hcardF, hidx, mul_comm]
    have := Subgroup.card_mul_index (fixW orth A)
    rw [card_orth] at this
    omega
  have hone : (1 : Perm (Fin 5)) ∈ Af := (hmem 1).mp A.one_mem
  have hmul : OfdMul Af := fun a ha b hb =>
    (hmem _).mp (A.mul_mem ((hmem a).mpr ha) ((hmem b).mpr hb))
  have hcomm : OfdComm Af := fun a ha b hb => hab a ((hmem a).mpr ha) b ((hmem b).mpr hb)
  have hsqA : OfdSq Af := fun a ha => hsq a ((hmem a).mpr ha)
  have hc := offender_finite s (Finset.mem_powerset.mpr (Finset.subset_univ s)) hone hmul hcomm
    hsqA h16
  rcases hc with h | h | h | h
  · left
    intro σ
    rw [hmem, hAf, h, Finset.mem_singleton]
  · right; left
    refine ⟨swap 0 2, Or.inl rfl, fun σ => ?_⟩
    rw [hmem, hAf, h, Finset.mem_insert, Finset.mem_singleton]
  · right; left
    refine ⟨swap 1 3, Or.inr rfl, fun σ => ?_⟩
    rw [hmem, hAf, h, Finset.mem_insert, Finset.mem_singleton]
  · right; right
    ext σ
    rw [hmem, hAf, h, mem_S5That_iff]

@[expose] def commTauF (τ : Perm (Fin 5)) : Finset orth.W :=
  spanF (commGensF orth {1, τ} Finset.univ)

set_option maxRecDepth 100000 in
private theorem card_commTauF : ∀ τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))),
    (commTauF τ).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem commTauF_not_fix : ∀ τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))),
    ∃ w ∈ commTauF τ, ¬ ∀ b ∈ S5SylF, orth.act b w = w := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem commTwoF_eq_mul : ∀ τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))),
    ∀ w ∈ commTwoF, ∃ r ∈ commTauF τ, ∃ f ∈ fixOrthF S5SylF, r * f = w := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem commTauF_le : ∀ τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))),
    ∀ w ∈ commTauF τ, w ∈ commTwoF := by
  decide +kernel

theorem mem_zpowers_perm_iff_of_sq {τ : Perm (Fin 5)} (h : τ * τ = 1) (σ : Perm (Fin 5)) :
    σ ∈ Subgroup.zpowers τ ↔ σ = 1 ∨ σ = τ := by
  rw [mem_zpowers_iff_of_pow_eq_one (m := 2) (by rw [pow_two]; exact h) (by norm_num)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩

theorem comm_zpowers_facts {τ : Perm (Fin 5)} (hτ : τ = swap 0 2 ∨ τ = swap 1 3) :
    Nat.card (commW orth (Subgroup.zpowers τ) ⊤) = 2 ∧
      commW orth (Subgroup.zpowers τ) ⊤ ≠ fixW orth S5Syl ∧
      commW orth (Subgroup.zpowers τ) ⊤ ⊔ fixW orth S5Syl = F53Mod.commIter orth S5Syl 2 := by
  have hτF : τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))) := by
    rcases hτ with rfl | rfl <;> simp
  have hsq : τ * τ = 1 := by rcases hτ with rfl | rfl <;> decide +kernel
  have hB : ∀ σ, σ ∈ Subgroup.zpowers τ ↔ σ ∈ ({1, τ} : Finset (Perm (Fin 5))) := fun σ => by
    rw [mem_zpowers_perm_iff_of_sq hsq, Finset.mem_insert, Finset.mem_singleton]
  have hTop : ∀ u : orth.W, u ∈ (⊤ : Subgroup orth.W) ↔ u ∈ (Finset.univ : Finset orth.W) := by
    intro u; simp
  have hmemR : ∀ w, w ∈ commW orth (Subgroup.zpowers τ) ⊤ ↔ w ∈ commTauF τ :=
    mem_commW_iff orth hB hTop
  refine ⟨?_, ?_, ?_⟩
  · rw [card_commW orth hB hTop]
    exact card_commTauF τ hτF
  · intro h
    obtain ⟨w, hw, hn⟩ := commTauF_not_fix τ hτF
    apply hn
    intro b hb
    have : w ∈ fixW orth S5Syl := h ▸ (hmemR w).mpr hw
    exact this b ((mem_S5Syl_iff b).mpr hb)
  · apply le_antisymm
    · refine sup_le ?_ fixW_S5Syl_le_commIter_two
      intro w hw
      rw [hmemR] at hw
      exact (mem_commIter_two_iff w).mpr (commTauF_le τ hτF w hw)
    · intro w hw
      rw [mem_commIter_two_iff] at hw
      obtain ⟨r, hr, f, hf, rfl⟩ := commTwoF_eq_mul τ hτF w hw
      refine Subgroup.mul_mem_sup ((hmemR r).mpr hr) ?_
      intro b hb
      exact (Finset.mem_filter.mp hf).2 b ((mem_S5Syl_iff b).mp hb)

variable {G : Type} [Group G] {X S Z : Subgroup G}

namespace Dict5

variable (D : Dict5 X S Z)

theorem relIndex_centralizer_bar {K : Subgroup G} (hK : K ≤ X) :
    (Z ⊓ Subgroup.centralizer (K : Set G)).relIndex Z = (fixW orth (D.bar K)).index := by
  have e := Subgroup.relIndex_map_map_of_injective (fixW orth (D.bar K)) ⊤ D.inj
  rw [D.map_φ_top, Subgroup.relIndex_top_right, D.map_fixW hK] at e
  exact e

end Dict5

theorem swap_mem_That {τ : Perm (Fin 5)} (hτ : τ = swap 0 2 ∨ τ = swap 1 3) :
    τ ∈ S5That := by
  rw [mem_S5That_iff]
  rcases hτ with rfl | rfl <;> decide +kernel

theorem idx_orth_swap {τ : Perm (Fin 5)} (hτ : τ = swap 0 2 ∨ τ = swap 1 3) :
    idx orth τ = 2 := by
  have h1 : τ ≠ 1 := by rcases hτ with rfl | rfl <;> decide +kernel
  refine ((transvections τ h1).2).mpr ?_
  rcases hτ with rfl | rfl
  · exact ⟨0, 2, by decide, rfl⟩
  · exact ⟨1, 3, by decide, rfl⟩

theorem offender_trichotomy [Finite G] (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hS : IsSylowTwoOf S X) (hZ : IsOrthSec X ⊥ Z) {B : Subgroup G} (hBS : B ≤ S)
    (hB : IsElemAbelian 2 B)
    (hidx : (pCoreOf 2 X ⊓ B).relIndex B = (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z) :
    ⁅Z, B⁆ ≤ ⁅⁅Z, S⁆, S⁆ ∧
      (B ≤ pCoreOf 2 X ∨
        ((∃ t ∈ B, t ∉ pCoreOf 2 X ∧ (Z ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Z = 2 ∧
            B ≤ Subgroup.zpowers t ⊔ pCoreOf 2 X) ∧
          (pCoreOf 2 X ⊓ B).relIndex B = 2 ∧ Nat.card ↥⁅Z, B⁆ = 2 ∧
          ⁅Z, B⁆ ≠ Z ⊓ Subgroup.centralizer (S : Set G) ∧
          ⁅Z, B⁆ ⊔ (Z ⊓ Subgroup.centralizer (S : Set G)) = ⁅⁅Z, S⁆, S⁆) ∨
        ((pCoreOf 2 X ⊓ B).relIndex B = 4 ∧
          B ⊔ pCoreOf 2 X = S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) ∧
          ⁅Z, B⁆ = ⁅⁅Z, S⁆, S⁆)) := by
  obtain ⟨D⟩ := nonempty_dict5 hq hS hZ
  have hBX : B ≤ X := hBS.trans D.S_le
  have hAS : D.bar B ≤ S5Syl := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (D.mem_bar_iff σ).mp hσ
    exact (D.mem_S_iff x).mp (hBS hx)
  have hab : ∀ a ∈ D.bar B, ∀ b ∈ D.bar B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (D.mem_bar_iff a).mp ha
    obtain ⟨y, hy, rfl⟩ := (D.mem_bar_iff b).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hB.1.is_comm.comm (⟨(x : G), hx⟩ : ↥B) ⟨(y : G), hy⟩
    exact congrArg (Subtype.val : ↥B → G) this
  have hsq : ∀ a ∈ D.bar B, a * a = 1 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (D.mem_bar_iff a).mp ha
    rw [← map_mul]
    have : (x * x : ↥X) = 1 := Subtype.ext (by simpa [pow_two] using hB.2 _ hx)
    rw [this, map_one]
  have hidx' : Nat.card (D.bar B) = (fixW orth (D.bar B)).index := by
    rw [D.card_bar hBX, hidx, D.relIndex_centralizer_bar hBX]
  have hcommTop : ⁅Z, B⁆ = (commW orth (D.bar B) ⊤).map D.φ := (D.map_commW_top hBX).symm
  have hQ : ∀ x : ↥X, (x : G) ∈ pCoreOf 2 X ↔ D.ψ x = 1 := fun x => (D.ker_iff x).symm
  have key : D.bar B ≤ S5That → ⁅Z, B⁆ ≤ ⁅⁅Z, S⁆, S⁆ := fun hAT => by
    have hBC : B ≤ S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G) := by
      intro x hx
      have hxX : x ∈ X := hBX hx
      exact (D.mem_centralizer_Y_iff ⟨x, hxX⟩).mpr
        (hAT ((D.mem_bar_iff _).mpr ⟨⟨x, hxX⟩, hx, rfl⟩))
    calc ⁅Z, B⁆ ≤ ⁅Z, S ⊓ Subgroup.centralizer ((⁅⁅Z, S⁆, S⁆ : Subgroup G) : Set G)⁆ :=
          Subgroup.commutator_mono le_rfl hBC
      _ = ⁅⁅Z, S⁆, S⁆ := comm_centralizer_Y hq hS hZ
  rcases offender_perm (D.bar B) hAS hab hsq hidx' with h1 | ⟨τ, hτ, hAτ⟩ | h3
  · refine ⟨key fun σ hσ => ?_, Or.inl fun x hx => ?_⟩
    · rw [(h1 σ).mp hσ]; exact one_mem _
    · have hxX : x ∈ X := hBX hx
      exact (hQ ⟨x, hxX⟩).mpr ((h1 _).mp ((D.mem_bar_iff _).mpr ⟨⟨x, hxX⟩, hx, rfl⟩))
  · have hτ1 : τ ≠ 1 := by rcases hτ with rfl | rfl <;> decide +kernel
    have hτA : τ ∈ D.bar B := (hAτ τ).mpr (Or.inr rfl)
    obtain ⟨t, htB, htτ⟩ := (D.mem_bar_iff τ).mp hτA
    have hsqτ : τ * τ = 1 := hsq τ hτA
    have hAz : D.bar B = Subgroup.zpowers τ := by
      ext σ; rw [hAτ, mem_zpowers_perm_iff_of_sq hsqτ]
    have hAT : D.bar B ≤ S5That := fun σ hσ => by
      rcases (hAτ σ).mp hσ with rfl | rfl
      · exact one_mem _
      · exact swap_mem_That hτ
    have hcard2 : (pCoreOf 2 X ⊓ B).relIndex B = 2 := by
      rw [← D.card_bar hBX, hidx', hAz]
      exact idx_orth_swap hτ
    refine ⟨key hAT, Or.inr (Or.inl ⟨⟨(t : G), htB, ?_, ?_, ?_⟩, hcard2, ?_, ?_, ?_⟩)⟩
    · exact fun h => hτ1 (by rw [← htτ]; exact (hQ t).mp h)
    · rw [D.relIndex_centralizer_eq t, htτ]
      exact idx_orth_swap hτ
    · intro x hx
      have hxX : x ∈ X := hBX hx
      have hxA : D.ψ ⟨x, hxX⟩ ∈ D.bar B := (D.mem_bar_iff _).mpr ⟨⟨x, hxX⟩, hx, rfl⟩
      rcases (hAτ _).mp hxA with h | h
      · exact Subgroup.mem_sup_right ((hQ ⟨x, hxX⟩).mpr h)
      · have h2 : ((t⁻¹ * ⟨x, hxX⟩ : ↥X) : G) ∈ pCoreOf 2 X :=
          (D.ker_iff _).mp (by rw [map_mul, map_inv, htτ, h, inv_mul_cancel])
        have h3 : x = (t : G) * ((t⁻¹ * ⟨x, hxX⟩ : ↥X) : G) := by simp
        rw [h3]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) h2
    · rw [hcommTop, hAz, D.card_map_φ]
      exact (comm_zpowers_facts hτ).1
    · rw [hcommTop, D.fix_eq, hAz]
      intro h
      exact (comm_zpowers_facts hτ).2.1 (Subgroup.map_injective D.inj h)
    · rw [hcommTop, D.fix_eq, hAz, ← Subgroup.map_sup, (comm_zpowers_facts hτ).2.2,
        D.comm_comm_eq]
  · refine ⟨key h3.le, Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
    · rw [← D.card_bar hBX, h3, nat_card_S5That]
    · apply le_antisymm
      · refine sup_le ?_ ?_
        · intro x hx
          have hxX : x ∈ X := hBX hx
          exact (D.mem_centralizer_Y_iff ⟨x, hxX⟩).mpr
            (h3.le ((D.mem_bar_iff _).mpr ⟨⟨x, hxX⟩, hx, rfl⟩))
        · intro x hx
          have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
          refine (D.mem_centralizer_Y_iff ⟨x, hxX⟩).mpr ?_
          rw [(D.ker_iff ⟨x, hxX⟩).mpr hx]
          exact one_mem _
      · intro x hx
        have hxX : x ∈ X := D.S_le hx.1
        have hxT : D.ψ ⟨x, hxX⟩ ∈ D.bar B := by
          rw [h3]; exact (D.mem_centralizer_Y_iff ⟨x, hxX⟩).mp hx
        obtain ⟨b, hb, hbx⟩ := (D.mem_bar_iff _).mp hxT
        have h2 : ((b⁻¹ * ⟨x, hxX⟩ : ↥X) : G) ∈ pCoreOf 2 X :=
          (D.ker_iff _).mp (by rw [map_mul, map_inv, hbx, inv_mul_cancel])
        have h4 : x = (b : G) * ((b⁻¹ * ⟨x, hxX⟩ : ↥X) : G) := by simp
        rw [h4]
        exact Subgroup.mul_mem_sup hb h2
    · rw [hcommTop, h3, commW_S5That_eq_commIter_two, D.comm_comm_eq]

end CFSG.Quasithin.F53.Stellmacher.S43
