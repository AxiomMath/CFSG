module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_ten_second_noncyclic (D : Data G) (h1110 : R1110Core D) {V₀ V : Subgroup G}
    (h11 : F11.Hyp11 D V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) {n : ℕ} (hn : 1 < n)
    (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) (hXn : Xbar.Normal) (hXe : IsElemAbelian p Xbar)
    (hXc : Nat.card Xbar = p ^ n) (hXd : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆)
    {v : G} (hv : v ∈ V)
    (hrk : 1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))) :
    ∃ B : Subgroup G,
      B ≤ F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ∧
        B ≤ F11.CElt D.M V₀ v ∧ ¬ IsCyclic ↥B := by
  haveI hXnI : Xbar.Normal := hXn
  have hcore := h1110 V₀ V h11 p hp hp2 P hP
  have h1 := hcore.1
  have hcyc := hcore.2.1.1
  have hcent := hcore.2.1.2
  have hPM : P ≤ D.M := (uc22p22u_sylow_O2p hp hp2 hP).1
  have hPp : IsPGroup p ↥P := hP.isPGroup
  set T : Subgroup G := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar with hT
  set Z : Subgroup G := T ⊓ F11.CTilde D.M V₀ V with hZ
  have hTP : T ≤ P := by rw [hT]; exact inf_le_left.trans inf_le_left
  have hTQ : T ≤ P ⊓ ⁅D.M, D.M⁆ := by rw [hT]; exact inf_le_left
  have hTM : T ≤ D.M := hTP.trans hPM
  have hZT : Z ≤ T := by rw [hZ]; exact inf_le_left
  have hZP : Z ≤ P ⊓ F11.CTilde D.M V₀ V := by
    rw [hZ]
    exact le_inf (inf_le_left.trans hTP) inf_le_right
  have hZc : IsCyclic ↥Z := by
    haveI := hcyc
    exact isCyclic_of_injective (Subgroup.inclusion hZP) (Subgroup.inclusion_injective hZP)
  have hmemT : ∀ t ∈ T, ∃ h : t ∈ D.M,
      (QuotientGroup.mk ⟨t, h⟩ : F11.MBar11 D.M V₀ V) ∈ Xbar := by
    intro t ht
    rw [hT] at ht
    exact uc22p22u_mem_barPreimage11.1 ht.2
  have hbar : F11.barImage11 D.M V₀ V T = Xbar := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      obtain ⟨hmM, hm'⟩ := hmemT _ hm
      exact hm'
    · intro q hq
      have hq1 : q ∈ pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ :=
        uc22p22u_le_pCoreOf Xbar _ (CFSG.Open.IsElemAbelian.isPGroup hXe) hXd hq
      rw [h1] at hq1
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq1
      refine uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩
      rw [hT]
      exact ⟨hm, uc22p22u_mem_barPreimage11.2 ⟨m.2, hq⟩⟩
  have hCS : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ v := by
    rw [F11.CTilde]
    exact iInf₂_le v hv
  set S : Subgroup G := T ⊓ F11.CElt D.M V₀ v with hS
  have hST : S ≤ T := inf_le_left
  have hZS : Z ≤ S := by
    rw [hZ, hS]
    exact le_inf inf_le_left (inf_le_right.trans hCS)
  have hSp : IsPGroup p ↥S := hPp.to_le (hST.trans hTP)
  have hTT : ⁅T, T⁆ ≤ Z := by
    rw [hZ]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨haM, ha'⟩ := hmemT a ha
    obtain ⟨hbM, hb'⟩ := hmemT b hb
    have hc := hXe.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have hc' : (QuotientGroup.mk ⟨a, haM⟩ : F11.MBar11 D.M V₀ V) *
        QuotientGroup.mk ⟨b, hbM⟩ =
        QuotientGroup.mk ⟨b, hbM⟩ * QuotientGroup.mk ⟨a, haM⟩ := congrArg Subtype.val hc
    have h2 : (QuotientGroup.mk ⁅(⟨a, haM⟩ : ↥D.M), ⟨b, hbM⟩⁆ : F11.MBar11 D.M V₀ V) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      exact commutatorElement_eq_one_iff_commute.2 hc'
    have h3 : ⁅a, b⁆ ∈ F11.CTilde D.M V₀ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this
    refine ⟨?_, h3⟩
    have : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [this]
    exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)
  have hScomm : ⁅S, S⁆ ≤ Z := (Subgroup.commutator_mono hST hST).trans hTT
  have hScent : ⁅S, Z⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono (hST.trans hTQ) hZP).trans hcent.le)
  have hSpow : ∀ t ∈ S, t ^ p ∈ Z := by
    intro t ht
    obtain ⟨htT, -⟩ := ht
    obtain ⟨htM, ht'⟩ := hmemT t htT
    have h2 : (QuotientGroup.mk (⟨t, htM⟩ ^ p : ↥D.M) : F11.MBar11 D.M V₀ V) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hXe.2 _ ht'
    have h3 : t ^ p ∈ F11.CTilde D.M V₀ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf] using this
    rw [hZ]
    exact ⟨T.pow_mem htT p, h3⟩
  have hSZ : S ⊓ F11.CTilde D.M V₀ V = Z := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, hx⟩
      exact ⟨hxT, hx⟩
    · rintro ⟨hxT, hx⟩
      exact ⟨⟨hxT, hCS hx⟩, hx⟩
  have hSW : F11.barImage11 D.M V₀ V S =
      Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      exact ⟨hbar ▸ uc22p22u_mem_barImage11.2 ⟨m, hm.1, rfl⟩,
        uc22p22u_mem_barImage11.2 ⟨m, hm.2, rfl⟩⟩
    · rintro q ⟨hqX, hqC⟩
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 (hbar ▸ hqX)
      obtain ⟨m', hm', hmm'⟩ := uc22p22u_mem_barImage11.1 hqC
      have h1' : ((m'⁻¹ * m : ↥D.M) : G) ∈ F11.CTilde D.M V₀ V :=
        uc22p22u_mk_eq_iff.1 hmm'
      refine uc22p22u_mem_barImage11.2 ⟨m, ⟨hm, ?_⟩, rfl⟩
      have h3 : (m : G) = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) := by simp
      rw [h3]
      exact (F11.CElt D.M V₀ v).mul_mem hm' (hCS h1')
  have hcardS := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := V₀) (V := V) (hST.trans hTM)
  rw [hSW, hSZ] at hcardS
  have hS2 : p ^ 2 * Nat.card ↥Z ≤ Nat.card ↥S := by
    obtain ⟨E₀, hE₀W, hE₀e, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))
    have h1' : p ^ 2 ≤ Nat.card ↥(Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) := by
      calc p ^ 2 ≤ p ^ CFSG.Open.pRank p
              (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) :=
            Nat.pow_le_pow_right hp.pos hrk
        _ = Nat.card ↥E₀ := hE₀c.symm
        _ ≤ _ := Subgroup.card_le_of_le hE₀W
    rw [hcardS]
    exact Nat.mul_le_mul_right _ h1'
  obtain ⟨E, hEΩ, hEe, hEc⟩ := uc22p22u_exists_elemAbelian_omega1 hp hp2 hSp hZc hZS hScomm
    hScent hSpow hS2
  have hΩS : F11.Omega1p p S ≤ S := (Subgroup.closure_le S).2 fun x hx => hx.1
  have hΩT : F11.Omega1p p S ≤ F11.Omega1p p T :=
    Subgroup.closure_mono fun x hx => ⟨hST hx.1, hx.2⟩
  exact ⟨E, hEΩ.trans hΩT, hEΩ.trans (hΩS.trans inf_le_right),
    uc22p22u_not_isCyclic_of_card_sq hp hEe hEc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
