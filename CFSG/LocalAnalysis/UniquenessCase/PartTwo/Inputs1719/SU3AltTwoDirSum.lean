module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IrrSetQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
public import CFSG.Quasithin.Background.B69Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614JFaith
public import CFSG.Quasithin.Background.SmithB51LnSub
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.F918V6BB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W]

theorem fix_commV_of_mem_conjSet_of_ne {Y K X₁ X₂ : Subgroup (MulAut W)}
    (hKcomp : CFSG.Open.IsComponentOf K Y)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W))))
    (h₁ : X₁ ∈ conjSet K Y) (h₂ : X₂ ∈ conjSet K Y) (hne : X₁ ≠ X₂) :
    ∀ x ∈ X₁, ∀ u ∈ commV X₂, x u = u := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  have hc₁ : CFSG.Open.IsComponentOf X₁ Y :=
    e₁ ▸ CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hKcomp hn₁
  have hc₂ : CFSG.Open.IsComponentOf X₂ Y :=
    e₂ ▸ CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hKcomp hn₂
  have hcomm := CFSG.Quasithin.B69.components_mul_comm_of_ne hc₁ hc₂ hne
  have hdisj : Disjoint (commV (autQuot X₁ (⊥ : Subgroup W)))
      (commV (autQuot X₂ (⊥ : Subgroup W))) :=
    hsum.1.pairwiseDisjoint (i := ⟨X₁, ⟨n₁, hn₁, e₁⟩⟩) (j := ⟨X₂, ⟨n₂, hn₂, e₂⟩⟩)
      (fun h => hne (congrArg Subtype.val h))
  intro x hx u hu
  have hxu : x u ∈ commV X₂ := by
    induction hu using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨l, hl, v, rfl⟩ := hw
      refine Subgroup.subset_closure ⟨l, hl, x v, ?_⟩
      have hlx : x * l = l * x := (hcomm l hl x hx).symm
      have : x (l v) = l (x v) := by
        simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f v) hlx
      simp [map_mul, map_inv, this]
    | one => simp
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact (commV X₂).mul_mem ha hb
    | inv a _ ha =>
      rw [map_inv]
      exact (commV X₂).inv_mem ha
  have h1 : x u * u⁻¹ ∈ commV X₁ := Subgroup.subset_closure ⟨x, hx, u, rfl⟩
  have h2 : x u * u⁻¹ ∈ commV X₂ := (commV X₂).mul_mem hxu ((commV X₂).inv_mem hu)
  have hm1 : QuotientGroup.mk' (⊥ : Subgroup W) (x u * u⁻¹) ∈
      commV (autQuot X₁ (⊥ : Subgroup W)) := by
    rw [← map_commV_eq_commV_autQuot X₁ ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le X₁)]
    exact Subgroup.mem_map_of_mem _ h1
  have hm2 : QuotientGroup.mk' (⊥ : Subgroup W) (x u * u⁻¹) ∈
      commV (autQuot X₂ (⊥ : Subgroup W)) := by
    rw [← map_commV_eq_commV_autQuot X₂ ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le X₂)]
    exact Subgroup.mem_map_of_mem _ h2
  have h3 := Subgroup.mem_bot.1 (hdisj.le_bot ⟨hm1, hm2⟩)
  have h4 : x u * u⁻¹ ∈ (⊥ : Subgroup W) := (QuotientGroup.eq_one_iff _).1 h3
  exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h4)

theorem commV_sup_fixV_eq_top_of_isDirSumOver {Y K : Subgroup (MulAut W)}
    (hKcomp : CFSG.Open.IsComponentOf K Y)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W)))) :
    commV K ⊔ fixV K = ⊤ := by
  have hKmem : K ∈ conjSet K Y := ⟨1, Y.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap : ∀ X : Subgroup (MulAut W),
      (commV X).map (QuotientGroup.mk' (⊥ : Subgroup W)) = commV (autQuot X ⊥) :=
    fun X => map_commV_eq_commV_autQuot X ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le X)
  have htop : (⨆ X : conjSet K Y, commV (X : Subgroup (MulAut W))) = ⊤ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    simp only [hmap]
    exact hsum.2
  rw [eq_top_iff, ← htop]
  refine iSup_le fun X => ?_
  by_cases hX : (X : Subgroup (MulAut W)) = K
  · rw [hX]; exact le_sup_left
  · refine le_sup_of_le_right ?_
    intro u hu
    rw [mem_fixV]
    intro k hk
    exact fix_commV_of_mem_conjSet_of_ne hKcomp hsum hKmem X.2 (Ne.symm hX) k hk u hu

theorem commV_inf_fixV_eq_bot_of_isDirSumOver {Y K : Subgroup (MulAut W)}
    (hKcomp : CFSG.Open.IsComponentOf K Y)
    (hfix : fixV (⨆ X ∈ conjSet K Y, X) = ⊥)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W)))) :
    commV K ⊓ fixV K = ⊥ := by
  have hKmem : K ∈ conjSet K Y := ⟨1, Y.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  rw [eq_bot_iff]
  rintro u ⟨hu1, hu2⟩
  have hmem : u ∈ fixV (⨆ X ∈ conjSet K Y, X) := by
    simp only [CFSG.Quasithin.fixV_iSup, Subgroup.mem_iInf]
    intro X hX
    by_cases hXK : X = K
    · subst hXK; exact hu2
    · rw [mem_fixV]
      intro x hx
      exact fix_commV_of_mem_conjSet_of_ne hKcomp hsum hX hKmem hXK x hx u hu1
  rw [hfix] at hmem
  exact hmem

theorem dMinDeg_le_rk_of_hom_ne_one {K A : Type} [Group K] [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a * a = 1)
    (φ : K →* MulAut A) (hφ : φ ≠ 1) : dMinDeg K ≤ rk A := by
  obtain ⟨k, hk, κ, hκ⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614J.exists_injective_gl
      hcomm h2
  have hrk : rk A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  rw [hrk]
  refine Nat.sInf_le ⟨κ.comp φ, fun h => hφ ?_⟩
  ext x a
  have hx : κ (φ x) = κ 1 := by
    simpa using congrArg (fun f => f x) h
  rw [hκ hx]
  rfl

theorem commSub_le_of_rk_lt_dMinDeg (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {U S : Subgroup W} (hUS : U ≤ S)
    (hSK : StableUnder K S) (hUK : StableUnder K U)
    (hrk : rk ↥S < rk ↥U + dMinDeg ↥K) : commSub S K ≤ U := by
  classical
  by_contra hne
  have hgen : ∃ k ∈ K, ∃ s ∈ S, k s * s⁻¹ ∉ U := by
    by_contra hall
    push Not at hall
    exact hne ((Subgroup.closure_le _).2 (by
      rintro _ ⟨k, hk, s, hs, rfl⟩
      exact hall k hk s hs))
  obtain ⟨k, hk, s, hs, hks⟩ := hgen
  have hKS : K ≤ stabSub S := CFSG.Quasithin.B1.le_stabSub_of_invariant hSK
  have hstab : autSub K S ≤ stabSub (U.subgroupOf S) :=
    CFSG.Quasithin.autSub_le_stabSub_subgroupOf (CFSG.Quasithin.B1.le_stabSub_of_invariant hUK)
  let A := ↥S ⧸ U.subgroupOf S
  let φ : ↥K →* MulAut A := (autQuot (autSub K S) (U.subgroupOf S)).subtype.comp
    ((CFSG.Quasithin.D37Lift.toQuot (U.subgroupOf S) (autSub K S) hstab).comp
      (CFSG.Quasithin.F918V6B.resOnto hKS))
  have hφ : φ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun f : ↥K →* MulAut A => f ⟨k, hk⟩ (QuotientGroup.mk ⟨s, hs⟩)) h1
    have h3 : (QuotientGroup.mk ⟨k s, hSK k hk s hs⟩ : A) = QuotientGroup.mk ⟨s, hs⟩ := h2
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h3
    apply hks
    have h4 : (k s)⁻¹ * s ∈ U := by simpa using h3
    have h5 := U.inv_mem h4
    simpa [mul_comm] using h5
  have hcommA : ∀ a b : A, a * b = b * a := fun a b => mul_comm a b
  have h2A : ∀ a : A, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul]
      have : x * x = 1 := Subtype.ext (by simpa [pow_two] using hW (x : W))
      rw [this, QuotientGroup.mk_one]
  have hd := dMinDeg_le_rk_of_hom_ne_one hcommA h2A φ hφ
  have hcard : Nat.card ↥S = Nat.card A * Nat.card ↥(U.subgroupOf S) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf S)
  have hcardU : Nat.card ↥(U.subgroupOf S) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  have hrkS : rk ↥S = rk ↥U + rk A := by
    unfold rk
    rw [hcard, hcardU, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', add_comm]
  omega

theorem fixV_autSub_autQuot_bot_eq_bot {K : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : I ∈ irrSet K) (hinf : commV K ⊓ fixV K = ⊥) :
    fixV (autSub (autQuot K (⊥ : Subgroup W))
      (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) = ⊥ := by
  have hIK : I ≤ commV K := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    calc I = commSub I K := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
  have hIbot : (I ⊓ fixV K).map (QuotientGroup.mk' (⊥ : Subgroup W)) = ⊥ := by
    have h0 : I ⊓ fixV K = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hIK)
    rw [h0, Subgroup.map_bot]
  have hmap := map_subtype_fixV_autSub_autQuot (CFSG.Quasithin.B5.Ln.stabSub_bot_le K)
    bot_le hI
  rw [hIbot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (I.map (QuotientGroup.mk' (⊥ : Subgroup W))).subtype_injective).mp hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
