module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Core
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SH1

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

@[expose] def NoONS427 (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 → ¬ (19 * 31 * 343) ∣ Nat.card (autFix σ)

theorem noONS427_of_card {S : Type} [Group S] [Finite S] (h : ¬ (19 * 31 * 343) ∣ Nat.card S) :
    NoONS427 S :=
  fun σ _ _ hd => h (hd.trans (Subgroup.card_subgroup_dvd_card _))

theorem card_eq_card_map_mk_mul {L : Type} [Group L] [Finite L] (H : Subgroup L) :
    Nat.card H = Nat.card (H.map (QuotientGroup.mk' (Subgroup.center L))) *
      Nat.card (H ⊓ Subgroup.center L : Subgroup L) := by
  set f : H →* L ⧸ Subgroup.center L := (QuotientGroup.mk' (Subgroup.center L)).comp H.subtype
  have hrange : f.range = H.map (QuotientGroup.mk' (Subgroup.center L)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : f.ker = (Subgroup.center L).subgroupOf H := by
    ext x
    simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hker : Nat.card f.ker = Nat.card (H ⊓ Subgroup.center L : Subgroup L) := by
    rw [hk, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker]

section Transfer

theorem row427_of_noCfg'
    {S : Type} [Group S] [Finite S]
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S' ∧ NoONS427 S') :
    Row427 S := by
  intro G _ _ hG A hA _ hθ L hL ⟨e⟩ d hdA hd1 _ hLd K hK htype
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL) hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hσ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hσ1 : descAut L ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hLd
    have hdC := (descAut_eq_one_iff hL.1.1 ⟨d, hdN⟩).mp h1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hle := map_le_autFix hdN (hK'M.trans inf_le_right)
  rcases htype with ⟨⟨φ⟩⟩ | ⟨-, hext⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q
    have hZK : Subgroup.center (K'.subgroupOf L ⧸ CFSG.pCore 2 (K'.subgroupOf L)) = ⊥ := by
      haveI := (isA5Type_quot_congr eKL hT).isSimpleGroup
      haveI : Group.IsPerfect (K'.subgroupOf L) := hK₁q.1
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ :=
      inf_eq_bot_of_center_eq_bot hK₁q hZK le_rfl hZ3
    have eB := equivBar hK'L hinf
    have hsn := isSubnormal_bar hdN hK'M hK'sn
    exact (h (L ⧸ Subgroup.center L) ⟨e⟩).1 _ hσ3 hσ1 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn (isA5Type_quot_congr eB.symm hT)
  ·
    apply (h (L ⧸ Subgroup.center L) ⟨e⟩).2 _ hσ3 hσ1
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
    have hON' : Nat.card ((K ⧸ CFSG.pCore 2 K) ⧸ N) = 460815505920 := by
      rw [Nat.card_congr eQ.toEquiv, CFSG.Sporadic.ON.card_ON]
    have h1 : 19 * 31 * 343 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hON']
      exact Dvd.dvd.mul_right (by norm_num) _
    have h2 : 19 * 31 * 343 ∣ Nat.card (K'.subgroupOf L) := by
      refine (h1.trans (Subgroup.card_quotient_dvd_card _)).trans ?_
      rw [Nat.card_congr eK.toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'L).toEquiv]
    rw [card_eq_card_map_mk_mul] at h2
    have h3 : IsPGroup 3 ((K'.subgroupOf L) ⊓ Subgroup.center L : Subgroup L) :=
      hZ3.to_le inf_le_right
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    rw [hk] at h2
    have h4 := (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime (19 * 31 * 343) 3)).dvd_of_dvd_mul_right
      h2
    exact h4.trans (Subgroup.card_dvd_of_le hle)

theorem row427_of_noCfg
    {S : Type} [Group S] [Finite S]
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S')
    (hON : ¬ (19 * 31 * 343) ∣ Nat.card S) : Row427 S :=
  row427_of_noCfg' fun S' _ _ ⟨e'⟩ => ⟨h S' ⟨e'⟩,
    noONS427_of_card (by rwa [Nat.card_congr e'.toEquiv])⟩

theorem rowOf427_of_noCfg
    {X : Type} [Group X] [Finite X]
    (h : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* X) → NoCfgS427 S)
    (hON : ¬ (19 * 31 * 343) ∣ Nat.card X) : RowOf427 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine row427_of_noCfg (fun S' _ _ ⟨e'⟩ => h S' ⟨e'.trans eSX⟩) ?_
  rwa [Nat.card_congr eSX.toEquiv]

end Transfer

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
