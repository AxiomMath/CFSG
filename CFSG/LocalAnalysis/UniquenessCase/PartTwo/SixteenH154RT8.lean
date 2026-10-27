module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Five
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_tdata (D : Data G) (hcore : R1110Core D) {V : Subgroup G}
    (hV : F11.Hyp11 D ⊥ V) [((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M ⊥ V)} (hXn : Xbar.Normal) (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), (⊤ : Subgroup (F11.MBar11 D.M ⊥ V))⁆)
    {T Z : Subgroup G} (hT : T = P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)
    (hZ : Z = T ⊓ F11.CTilde D.M ⊥ V) :
    IsPGroup p ↥T ∧ IsCyclic ↥Z ∧ Z ≤ T ∧ ⁅T, T⁆ ≤ Z ∧ ⁅T, Z⁆ = ⊥ ∧ (∀ t ∈ T, t ^ p ∈ Z) ∧
      T ≤ D.M ∧ F11.barImage11 D.M ⊥ V T = Xbar := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hXn
  obtain ⟨hPM, -, -⟩ := uc22p22u_sylow_O2p hp hp2 hP
  have hPp : IsPGroup p ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.1
  have h1 := (hcore ⊥ V hV p hp hp2 P hP).1
  obtain ⟨hcyc, hcent⟩ := (hcore ⊥ V hV p hp hp2 P hP).2.1
  have hTP : T ≤ P := by rw [hT]; exact inf_le_left.trans inf_le_left
  have hTQ : T ≤ P ⊓ ⁅D.M, D.M⁆ := by rw [hT]; exact inf_le_left
  have hTM : T ≤ D.M := hTP.trans hPM
  have hZT : Z ≤ T := by rw [hZ]; exact inf_le_left
  have hZP : Z ≤ P ⊓ F11.CTilde D.M ⊥ V := by
    rw [hZ]
    exact le_inf (inf_le_left.trans hTP) inf_le_right
  have hmemT : ∀ t ∈ T, ∃ h : t ∈ D.M,
      (QuotientGroup.mk ⟨t, h⟩ : F11.MBar11 D.M ⊥ V) ∈ Xbar := by
    intro t ht
    rw [hT] at ht
    exact uc22p22u_mem_barPreimage11.1 ht.2
  refine ⟨hPp.to_le hTP, ?_, hZT, ?_, ?_, ?_, hTM, ?_⟩
  · haveI := hcyc
    exact isCyclic_of_injective (Subgroup.inclusion hZP) (Subgroup.inclusion_injective hZP)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨haM, ha'⟩ := hmemT a ha
    obtain ⟨hbM, hb'⟩ := hmemT b hb
    have hc := hXe.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have hc' : (QuotientGroup.mk ⟨a, haM⟩ : F11.MBar11 D.M ⊥ V) * QuotientGroup.mk ⟨b, hbM⟩ =
        QuotientGroup.mk ⟨b, hbM⟩ * QuotientGroup.mk ⟨a, haM⟩ := congrArg Subtype.val hc
    have h2 : (QuotientGroup.mk ⁅(⟨a, haM⟩ : ↥D.M), ⟨b, hbM⟩⁆ : F11.MBar11 D.M ⊥ V) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      exact commutatorElement_eq_one_iff_commute.2 hc'
    have h3 : ⁅a, b⁆ ∈ F11.CTilde D.M ⊥ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this
    rw [hZ]
    refine ⟨?_, h3⟩
    have : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [this]
    exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)
  · exact le_bot_iff.1 ((Subgroup.commutator_mono hTQ hZP).trans hcent.le)
  · intro t ht
    obtain ⟨htM, ht'⟩ := hmemT t ht
    have h2 : (QuotientGroup.mk (⟨t, htM⟩ ^ p : ↥D.M) : F11.MBar11 D.M ⊥ V) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hXe.2 _ ht'
    have h3 : t ^ p ∈ F11.CTilde D.M ⊥ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf] using this
    rw [hZ]
    exact ⟨T.pow_mem ht p, h3⟩
  · apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      obtain ⟨hmM, hm'⟩ := hmemT _ hm
      exact hm'
    · intro q hq
      have hq1 : q ∈ pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ :=
        uc22p22u_le_pCoreOf Xbar _ (CFSG.Open.IsElemAbelian.isPGroup hXe) hXle hq
      rw [h1] at hq1
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq1
      refine uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩
      rw [hT]
      exact ⟨hm, uc22p22u_mem_barPreimage11.2 ⟨m.2, hq⟩⟩

@[expose] def s16h_R1110Last (D : Data G) : Prop :=
  ∀ V : Subgroup G, F11.Hyp11 D ⊥ V →
    ∀ [((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M) →
      ∀ n : ℕ, 1 < n → ∀ Xbar : Subgroup (F11.MBar11 D.M ⊥ V), Xbar.Normal →
        IsElemAbelian p Xbar → Nat.card Xbar = p ^ n →
        Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ →
        (D.sig = D.sig1 → ∀ v ∈ V, v ≠ 1 →
          1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) →
            UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)))

theorem s16h_r1110Last_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h63 : UC6.R6_3 D)
    (h77 : F07.R77Eq D) (hcore : R1110Core D) : s16h_R1110Last D := by
  intro V hV hN p hp hp2 P hP n hn Xbar hXn hXe hXc hXle hσ v hv hv1 hrank
  haveI hN' : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := hN
  set T : Subgroup G := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar with hT
  set Z : Subgroup G := T ⊓ F11.CTilde D.M ⊥ V with hZ
  set Y : Subgroup G := F11.Omega1p p T with hYdef
  have hYIn : F11.InP11 D Y := by
    rw [hYdef, hT]
    exact s16e_d3_inP11 D hSg hσ hcore h77 hV hp hp2 hn Xbar hXn hXe hXc hXle hP
  obtain ⟨p', hp'pr, -, -, hYp', -, hYnc, -, hYΓ', -⟩ := hYIn
  have hYexpP : ∀ x ∈ Y, x ^ p = 1 := by
    rw [hYdef, hT]
    exact ((hcore ⊥ V hV p hp hp2 P hP).2.2 n hn Xbar hXn hXe hXc hXle).1
  have hYnebot : Y ≠ ⊥ := by
    intro hbot
    apply hYnc
    rw [hbot]
    exact isCyclic_of_subsingleton
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYnebot
  have hpdvd : orderOf y ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (hYexpP y.1 y.2)
  haveI : Fact p'.Prime := ⟨hp'pr⟩
  have hp'dvd : p' ∣ orderOf y := hYp'.dvd_orderOf hy1
  have horder : orderOf y = p := by
    rcases (Nat.dvd_prime hp).1 hpdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hp'eq : p' = p := (Nat.prime_dvd_prime_iff_eq hp'pr hp).1 (horder ▸ hp'dvd)
  have hYΓ : rankThreeGamma 1 p Y ≤ D.M := by
    rw [← hp'eq]
    exact hYΓ'
  have hVc := uc22p22u_cTilde_bot D.M V
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ :=
    s16h_tdata D hcore hV hp hp2 hP hXn hXe hXle hT hZ
  have hX₀v : F11.CTilde D.M ⊥ V ≤ centralizer ({v} : Set G) := by
    rw [hVc]
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_centralizer_iff.1 hx.2 h hv
  set S : Subgroup G := T ⊓ centralizer ({v} : Set G) with hS
  have hST : S ≤ T := inf_le_left
  have hZS : Z ≤ S := le_inf hZT (inf_le_right.trans hX₀v)
  have hSp : IsPGroup p ↥S := hTp.to_le hST
  have hScomm : ⁅S, S⁆ ≤ Z := (Subgroup.commutator_mono hST hST).trans hcomm
  have hScent : ⁅S, Z⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_mono hST le_rfl).trans hcent.le)
  have hSpow : ∀ t ∈ S, t ^ p ∈ Z := fun t ht => hpow t ht.1
  have hSZ : S ⊓ F11.CTilde D.M ⊥ V = Z := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, hx⟩
      exact ⟨hxT, hx⟩
    · rintro ⟨hxT, hx⟩
      exact ⟨⟨hxT, hX₀v hx⟩, hx⟩
  have hSW : F11.barImage11 D.M ⊥ V S =
      Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      refine ⟨hbar ▸ uc22p22u_mem_barImage11.2 ⟨m, hm.1, rfl⟩,
        uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩⟩
      exact uc22p22u_mem_CElt_bot.2 ⟨m.2, (Subgroup.mem_centralizer_iff.1 hm.2 v rfl).symm⟩
    · rintro q ⟨hqX, hqC⟩
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 (hbar ▸ hqX)
      obtain ⟨m', hm', hmm'⟩ := uc22p22u_mem_barImage11.1 hqC
      obtain ⟨-, hm'c⟩ := uc22p22u_mem_CElt_bot.1 hm'
      have h1 : ((m'⁻¹ * m : ↥D.M) : G) ∈ F11.CTilde D.M ⊥ V := uc22p22u_mk_eq_iff.1 hmm'
      have h2 : ((m'⁻¹ * m : ↥D.M) : G) * v = v * ((m'⁻¹ * m : ↥D.M) : G) :=
        Subgroup.mem_centralizer_iff.1 (hX₀v h1) v rfl |>.symm
      have h3 : (m : G) = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) := by simp
      refine uc22p22u_mem_barImage11.2 ⟨m, ⟨hm, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [h3]
      calc h * ((m' : G) * ((m'⁻¹ * m : ↥D.M) : G)) =
            (h * (m' : G)) * ((m'⁻¹ * m : ↥D.M) : G) := by rw [mul_assoc]
        _ = ((m' : G) * h) * ((m'⁻¹ * m : ↥D.M) : G) := by rw [← hm'c]
        _ = (m' : G) * (h * ((m'⁻¹ * m : ↥D.M) : G)) := by rw [mul_assoc]
        _ = (m' : G) * (((m'⁻¹ * m : ↥D.M) : G) * h) := by rw [← h2]
        _ = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) * h := by rw [mul_assoc]
  have hcardS := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := ⊥) (V := V) (hST.trans hTM)
  rw [hSW, hSZ] at hcardS
  have hS2 : p ^ 2 * Nat.card ↥Z ≤ Nat.card ↥S := by
    obtain ⟨E₀, hE₀W, hE₀e, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v))
    have h1 : p ^ 2 ≤ Nat.card ↥(Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) := by
      calc p ^ 2 ≤ p ^ CFSG.Open.pRank p
              (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) :=
            Nat.pow_le_pow_right hp.pos hrank
        _ = Nat.card ↥E₀ := hE₀c.symm
        _ ≤ _ := Subgroup.card_le_of_le hE₀W
    rw [hcardS]
    exact Nat.mul_le_mul_right _ h1
  obtain ⟨E, hEΩ, hEe, hEc⟩ := uc22p22u_exists_elemAbelian_omega1 hp hp2 hSp hZc hZS hScomm
    hScent hSpow hS2
  have hΩS : F11.Omega1p p S ≤ S := (Subgroup.closure_le S).2 fun x hx => hx.1
  have hΩT : F11.Omega1p p S ≤ F11.Omega1p p T :=
    Subgroup.closure_mono fun x hx => ⟨hST hx.1, hx.2⟩
  have hEY : E ≤ Y := by
    rw [hYdef]
    exact hEΩ.trans hΩT
  have hES : E ≤ S := hEΩ.trans hΩS
  have hEM : E ≤ D.M := hES.trans (hST.trans hTM)
  have hEC : E ≤ D.M ⊓ centralizer ({v} : Set G) := le_inf hEM (hES.trans inf_le_right)
  have hΓ : rankThreeGamma 1 p E ≤ D.M := (uc22p22u_gamma_mono hEY).trans hYΓ
  exact uc22p22u_uniqueMax_mono D hEC inf_le_left (h63 p hp hp2 E hEM hEe hEc hΓ)

theorem s16h_r1110W_of_core_last (D : Data G) (hcore : R1110Core D) (hlast : s16h_R1110Last D) :
    R1110W D := by
  intro V hV hN p hp hp2 P hP
  have hc := @hcore ⊥ V hV hN p hp hp2 P hP
  exact ⟨hc.1, hc.2.1, fun n hn Xbar hXn hXe hXc hXle =>
    ⟨hc.2.2 n hn Xbar hXn hXe hXc hXle,
      @hlast V hV hN p hp hp2 P hP n hn Xbar hXn hXe hXc hXle⟩⟩

theorem s16h_r1110W_holds (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) : R1110W D :=
  s16h_r1110W_of_core_last D (r1110Core_holds D hSig h61 h63 h77 h869 h111 h112 hThin hCyc)
    (s16h_r1110Last_holds D hSig h63 h77
      (r1110Core_holds D hSig h61 h63 h77 h869 h111 h112 hThin hCyc))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
