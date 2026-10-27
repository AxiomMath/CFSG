module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_exists_stable_index {T : Type} [CommGroup T] {ι : Type}
    {Y : ι → Subgroup T} (hinj : Function.Injective Y) {B : Subgroup (MulAut T)}
    (hB : IsPGroup 2 B) (hperm : ∀ b ∈ B, ∀ i, ∃ j, (Y i).map b.toMonoidHom = Y j)
    (hodd : Odd (Nat.card ι)) :
    ∃ i, ∀ b ∈ B, (Y i).map b.toMonoidHom = Y i := by
  have hsmul : ∀ (x : MulAut T) (I : Subgroup T), x • I = I.map x.toMonoidHom := by
    intro x I
    have hf : MulDistribMulAction.toMonoidEnd _ _ x = x.toMonoidHom := by
      ext y
      rfl
    rw [Subgroup.pointwise_smul_def, hf]
  let S : SubMulAction ↥B (Subgroup T) :=
    { carrier := Set.range Y
      smul_mem' := by
        rintro b _ ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := hperm b b.2 i
        exact ⟨j, by rw [← hj, ← hsmul]; rfl⟩ }
  have hcard : Nat.card ↥S = Nat.card ι :=
    (Nat.card_congr (Equiv.ofInjective Y hinj)).symm
  have hndvd : ¬ 2 ∣ Nat.card ↥S := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨s, hs⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card ↥S hndvd
  obtain ⟨i, hi⟩ := s.2
  refine ⟨i, fun b hb => ?_⟩
  have h1 : (⟨b, hb⟩ : ↥B) • s = s := hs ⟨b, hb⟩
  have h2 := congrArg Subtype.val h1
  rw [← hsmul, hi]
  exact h2

theorem s16c13bcA_exists_noncyclic_fixing {T : Type} [CommGroup T] [Finite T] {p : ℕ}
    (hp : p.Prime) {F : Subgroup (MulAut T)} (hF : IsElemAbelian p F)
    (hFc : p ^ 3 ≤ Nat.card F) {Y : Subgroup T}
    (hFY : ∀ f ∈ F, Y.map f.toMonoidHom = Y) (hY : Nat.card Y < p ^ 2) {n : T} (hn : n ∈ Y) :
    ∃ P : Subgroup (MulAut T), P ≤ F ∧ ¬ IsCyclic P ∧ ∀ f ∈ P, f n = n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  set S : Subgroup ↥F := MulAction.stabilizer ↥F n with hS
  have hidx : S.index = (MulAction.orbit ↥F n).ncard := MulAction.index_stabilizer ↥F n
  have horb : MulAction.orbit ↥F n ⊆ (Y : Set T) := by
    rintro _ ⟨f, rfl⟩
    have h1 : (f : MulAut T) n ∈ Y.map (f : MulAut T).toMonoidHom := ⟨n, hn, rfl⟩
    rw [hFY f f.2] at h1
    exact h1
  have hle : S.index ≤ Nat.card Y := by
    rw [hidx]
    have h1 := Set.ncard_le_ncard horb (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq] at h1
  have hdvd : S.index ∣ p ^ k := hk ▸ Dvd.intro _ (Subgroup.index_mul_card S)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj2 : j < 2 := by
    have h1 : p ^ j < p ^ 2 := hj ▸ lt_of_le_of_lt hle hY
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  have hidxp : S.index ≤ p := by
    interval_cases j
    · rw [hj]
      exact hp.one_lt.le.trans' (by simp)
    · rw [hj]
      simp
  have hcardS : p ^ 2 ≤ Nat.card S := by
    have h1 : Nat.card S * S.index = Nat.card F := Subgroup.card_mul_index S
    have h2 : p * p ^ 2 ≤ p * Nat.card S := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card F := hFc
        _ = Nat.card S * S.index := h1.symm
        _ ≤ Nat.card S * p := Nat.mul_le_mul_left _ hidxp
        _ = p * Nat.card S := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  refine ⟨S.map F.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card ↥(S.map F.subtype) :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    have hg1 : g ^ p = 1 := by
      have hgF : (g : MulAut T) ∈ F := Subgroup.map_subtype_le S g.2
      exact Subtype.ext (hF.2 _ hgF)
    have hle2 := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hg1)
    have hcardP : Nat.card ↥(S.map F.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective F.subtype_injective
    have h3 : p < p ^ 2 := by
      calc p < p * p := lt_mul_of_one_lt_left hp.pos hp.one_lt
        _ = p ^ 2 := by ring
    omega
  · rintro f ⟨g, hg, rfl⟩
    exact hg

theorem s16c13bcA_case168_4_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h4 : 3 < CFSG.Open.evenRank G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (h : Case168_4With D ⊥ V hV L 2) :
    Insp1613U D V := by
  classical
  obtain ⟨p, hp37, hL, hS, hpσ⟩ := h
  have hpp : p.Prime := by rcases hp37 with rfl | rfl <;> norm_num
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hrank := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 hpσ
  have hcore := s16n9b_case4_pcore D hV hc hpp (by norm_num : 1 < 2) hL
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  obtain ⟨F, hFX, hFel, hFcard, hFY, -⟩ := s16n9b_case4_kernel
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hp37 (by norm_num) hL hcore hrank hind hinj hsup hcard hrk
    hperm hsurj
  obtain ⟨i₀, hi₀⟩ := s16c13bcA_exists_stable_index hinj (s16c13bcA_wBar_isPGroup D hV)
    (fun b hb i => hperm b (s16c13bcA_wBar_le_mbar D hV hb) i)
    (by rw [Nat.card_eq_fintype_card, hcard]; exact ⟨1, rfl⟩)
  have hY0 : Y i₀ ≠ ⊥ := by
    intro h0
    have h1 := hrk i₀
    rw [h0, rk_bot] at h1
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three] at h1
      omega
    · rw [s16c1610_dParam_seven] at h1
      omega
  obtain ⟨n, hnY, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h125 hY0
    (fun b hb => s16c13bcA_mem_stabSub_of_map_eq (hi₀ b hb))
  have hYcard : Nat.card ↥(Y i₀) < p ^ 2 := by
    have hsq : ∀ v : ↥(Y i₀), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using s15_Infra_vtil_sq_eq_one ⊥ V hV v.1)
    rw [card_eq_two_pow_rk hsq, hrk i₀]
    rcases hp37 with rfl | rfl
    · rw [s16c1610_dParam_three]
      norm_num
    · rw [s16c1610_dParam_seven]
      norm_num
  obtain ⟨P, hPF, hPc, hPfix⟩ := s16c13bcA_exists_noncyclic_fixing hpp hFel hFcard
    (fun f hf => hFY f hf i₀) hYcard hnY
  have hPp : IsPGroup p P := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hFel.2 g (hPF g.2))⟩
  exact s16c13bcA_insp_of_fixing D h125 hpσ hn1 hnfix (hPF.trans hFX) hPp hPc hPfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
