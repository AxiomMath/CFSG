module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKSchurC1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotLarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.Permutation.FiveTransitive.PrimeFreeOrderLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim

public section

namespace CFSG.GroupTheory

theorem exists_mem_orderOf_eq_prime_of_mem_map {L H : Type} [Group L] [Finite L] [Group H]
    {p : ℕ} [Fact p.Prime] (f : L →* H) (hf : Function.Surjective f)
    (hN : ¬ p ∣ Nat.card f.ker) {C : Subgroup L} {x : H}
    (hxC : x ∈ C.map f) (hx : orderOf x = p) :
    ∃ a ∈ C, orderOf a = p ∧ f a = x := by
  obtain ⟨k0, hk0C, rfl⟩ := Subgroup.mem_map.mp hxC
  let fC : C →* ↥(C.map f) := (f.comp C.subtype).codRestrict (C.map f) fun c =>
    Subgroup.mem_map_of_mem f c.2
  have hfC : Function.Surjective fC := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hkerC : ¬ p ∣ Nat.card fC.ker := by
    have hker_le : Nat.card fC.ker ∣ Nat.card f.ker := by
      rw [show fC.ker = (f.comp C.subtype).ker from MonoidHom.ker_codRestrict _ _ _,
        ← MonoidHom.comap_ker f C.subtype]
      exact Subgroup.card_comap_dvd_of_injective f.ker C.subtype C.subtype_injective
    exact fun h => hN (h.trans hker_le)
  obtain ⟨a, haφ, haord⟩ :=
    CFSG.FiveTransitive.PrimeFreeOrderLift.exists_lift fC hfC hkerC
      ⟨f k0, Subgroup.mem_map_of_mem f hk0C⟩ (by simpa using hx)
  exact ⟨a, a.2, (Subgroup.orderOf_coe a).trans haord, congrArg Subtype.val haφ⟩

end CFSG.GroupTheory

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem IsSUn.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSUn X n a) : IsSUn Y n a := by
  obtain ⟨K, hKf, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hKf, hKfin, hcard, ⟨e.symm.trans e'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isL2_and_isL2Square {X : Type} [Group X] [Finite X] {b n : ℕ} (hn : 3 ≤ n)
    (hL2 : IsL2 X b) (hSq : IsL2Square X n) : False := by
  have hb : 1 ≤ b := hL2.admissible.2.1
  have hodd1 : Odd (2 ^ (2 * b) - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hodd2 : Odd ((2 ^ (2 * n) - 1) ^ 2) :=
    (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).pow
  have heq : 2 ^ b * (2 ^ (2 * b) - 1) = 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2 :=
    (S17.card_of_isL2 hL2).symm.trans (S17.card_of_isL2Square_eq hSq)
  have hb2n : b = 2 * n :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd1 hodd2 heq
  have heq2 : 2 ^ (2 * b) - 1 = (2 ^ (2 * n) - 1) ^ 2 := by
    have h := heq
    rw [hb2n] at h ⊢
    exact Nat.mul_left_cancel (n := 2 ^ (2 * n)) (by positivity) h
  have hb4n : 2 * b = 4 * n := by omega
  rw [hb4n] at heq2
  have hqpow : 2 ^ (4 * n) = (2 ^ (2 * n)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hqpow] at heq2
  have hq : 4 ≤ 2 ^ (2 * n) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 ≤ (2 ^ (2 * n)) ^ 2 := by
    have : 0 < (2 ^ (2 * n)) ^ 2 := by positivity
    omega
  have hq2 : 1 ≤ 2 ^ (2 * n) := by
    have : 0 < 2 ^ (2 * n) := by positivity
    omega
  have heqZ : ((2 : ℤ) ^ (2 * n)) ^ 2 - 1 = ((2 : ℤ) ^ (2 * n) - 1) ^ 2 := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) heq2
    simpa only [Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one,
      Nat.cast_ofNat] using h
  have hqZ : (4 : ℤ) ≤ (2 : ℤ) ^ (2 * n) := by
    have h : (4 : ℤ) ≤ (2 ^ (2 * n) : ℤ) := by exact_mod_cast hq
    simpa only [Nat.cast_pow] using h
  nlinarith [heqZ, hqZ]

theorem comap_pCore_eq_of_pCore_eq_bot_of_kSchurC1
    {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hSC : KSchurC1)
    (hshape : (∃ n : ℕ, 3 ≤ n ∧ IsSp4 (Y ⧸ CFSG.pCore 2 Y) n) ∨
      (∃ a : ℕ, 2 ≤ a ∧ IsSUn (Y ⧸ CFSG.pCore 2 Y) 4 a) ∨
      (∃ n : ℕ, 3 ≤ n ∧ IsOmegaMinus (Y ⧸ CFSG.pCore 2 Y) 6 n))
    (hbot : CFSG.pCore 2 Y = ⊥) : f.ker = CFSG.pCore 2 X := by
  have hSchur : ∀ (Xb : Type) [Group Xb] [Finite Xb] (K : Subgroup Xb) [K.Normal],
      ⁅(⊤ : Subgroup Xb), (⊤ : Subgroup Xb)⁆ = ⊤ → K ≤ Subgroup.center Xb →
      Odd (Nat.card ↥K) →
      Nonempty (Xb ⧸ K ≃* Y ⧸ CFSG.pCore 2 Y) → K = ⊥ := by
    intro Xb _ _ K _ hcomm hcenter hodd ⟨e⟩
    refine hSC Xb K hcomm hcenter hodd ?_
    rcases hshape with ⟨n, hn, hSp⟩ | ⟨a, ha, hSU⟩ | ⟨n, hn, hOm⟩
    · exact Or.inl ⟨n, hn, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSp⟩
    · exact Or.inr (Or.inl ⟨a, ha, IsSUn.of_mulEquiv e.symm hSU⟩)
    · exact Or.inr (Or.inr ⟨n, hn, IsOmegaMinus.of_mulEquiv e.symm hOm⟩)
  have hmain := comap_pCore_eq_of_surjective_of_schur f hf hperfect hker hSchur
  rw [← hmain, hbot, MonoidHom.comap_bot]

private theorem thin8_of_mem_calC {D : Data G} {Ch : Choice2011 G} (h8 : S23_8 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {Y : Subgroup G} (hY : Y ∈ calC D.M) :
    F08.Thin8 Y := by
  obtain ⟨-, hshape⟩ := h8 h1930 c Y hY
  rcases hshape with ⟨a, -, hL2 | hSz⟩ | ⟨hrest, -⟩
  · exact thin8_of_isL2_or_isSz (Or.inl hL2)
  · exact thin8_of_isL2_or_isSz (Or.inr hSz)
  · rcases hrest with ⟨q, hq, hq2, hL2odd⟩ | hJ1 | ⟨a, hL2⟩
    · exact thin8_of_isL2Odd_bar2 hq hq2 hL2odd
    · exact thin8_of_isJ1_bar2 hJ1
    · exact thin8_of_isL2_or_isSz (Or.inl hL2)

private theorem exists_component_of_B23 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSp4 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
      (IsOmegaMinus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)))
    (hd : KTab23d) (hB23 : S23_9_B23 D Ch) (h1930 : H1930 D)
    (hK_ne_bot : Hinf (D.M ⊓ c.L) ≠ ⊥) :
    ∃ Y : Subgroup G, Y ∈ calC D.M ∧ Hinf (D.M ⊓ c.L) ≤ Y := by
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let Pℓ : Subgroup ↥(c.H hV) :=
    MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))
  let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
  have hd' := hd (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hL2shape : IsL2 (Bar2 Kstar) n ∨
      (∃ a : ℕ, n = 2 * a ∧ IsL2 (Bar2 Kstar) a) ∨
      IsL2 (Bar2 Kstar) (2 * n) := by
    rcases hline with ⟨hSp, hNatSp⟩ | ⟨a, hn2, hSU, hNatSU⟩ | ⟨hOm, hNatOm⟩
    · exact Or.inl (hd'.2.2.2.1 ⟨hSp, hNatSp⟩)
    · exact Or.inr (Or.inl (hd'.2.2.2.2.2.1 ⟨a, hn2, hSU, hNatSU⟩))
    · exact Or.inr (Or.inr (hd'.2.2.2.2.2.2.1 ⟨hOm, hNatOm⟩))
  have hB := hB23 h1930 c h3
  dsimp only at hB
  rcases hB with hKbot | hKcal | hKthird | hKfourth
  · exact absurd hKbot hK_ne_bot
  · exact ⟨Hinf (D.M ⊓ c.L), hKcal, le_rfl⟩
  · obtain ⟨⟨hV', hOplus, hNatPlus⟩, -⟩ := hKthird
    rw [show hV' = hV from Subsingleton.elim _ _] at hOplus hNatPlus
    have hsq : IsL2Square (Bar2 Kstar) n :=
      hd'.2.2.2.2.2.2.2.2.1 ⟨hOplus, hNatPlus⟩
    rcases hL2shape with hL2 | ⟨a, -, hL2⟩ | hL2
    · exact (not_isL2_and_isL2Square h3 hL2 hsq).elim
    · exact (not_isL2_and_isL2Square h3 hL2 hsq).elim
    · exact (not_isL2_and_isL2Square h3 hL2 hsq).elim
  · obtain ⟨-, X, hXcal, hKX⟩ := hKfourth
    exact ⟨X, hXcal, hKX⟩

namespace Ctx23L

private theorem exists_zpowers_eq_of_prime_card {H : Type} [Group H] (A : Subgroup H)
    [Finite ↥A] {p : ℕ} (hp : p.Prime) (hcard : Nat.card ↥A = p) :
    ∃ x ∈ A, orderOf x = p ∧ A = Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA_nontriv : Nontrivial ↥A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
  obtain ⟨x, hxA, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial A
  have hxorder : orderOf x = p := by
    have hdvd : orderOf x ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A hxA
    rw [hcard] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact hp'
  refine ⟨x, hxA, hxorder, ?_⟩
  have htop : Subgroup.zpowers (⟨x, hxA⟩ : ↥A) = ⊤ :=
    zpowers_eq_top_of_prime_card hcard (by simpa using hx1)
  have hmap := congrArg (Subgroup.map A.subtype) htop
  have htopmap : (⊤ : Subgroup ↥A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [MonoidHom.map_zpowers, htopmap] at hmap
  simpa using hmap.symm

theorem exists_mem_orderOf_eq_prime_of_le_Hinf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {Kstar Astar : Subgroup ↥(c.H hV)}
    (hKstar_eq : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hAstar_le : Astar ≤ Kstar) (hAstar_card : Nat.card ↥Astar = p) :
    ∃ a : ↥c.L, a ∈ (Hinf (D.M ⊓ c.L)).subgroupOf c.L ∧ orderOf a = p ∧
      c.phiL hV a ∈ Astar ∧ Astar = Subgroup.zpowers (c.phiL hV a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxA, hxorder, hAeq⟩ := exists_zpowers_eq_of_prime_card Astar hp hAstar_card
  have hxImage : x ∈ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) := by
    rw [hKstar_eq]
    exact hAstar_le hxA
  have hkerP : IsPGroup 2 (c.phiL hV).ker := by
    rw [hker_eq]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hker_not : ¬ p ∣ Nat.card (c.phiL hV).ker := by
    obtain ⟨k, hk⟩ := hkerP.exists_card_eq
    rw [hk]
    intro h
    have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
  obtain ⟨a, haK, haord, haφ⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_prime_of_mem_map (c.phiL hV)
      (c.phiL_surjective hV) hker_not (C := (Hinf (D.M ⊓ c.L)).subgroupOf c.L)
      (x := x) hxImage hxorder
  refine ⟨a, haK, haord, ?_, ?_⟩
  · rw [haφ]; exact hxA
  · rw [haφ]; exact hAeq

theorem phiL_ker_eq_pCore_of_kSchurC1 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hSC : KSchurC1)
    (hshape : (∃ m : ℕ, 3 ≤ m ∧ IsSp4 ↥(c.H hV) m) ∨
      (∃ a : ℕ, 2 ≤ a ∧ IsSUn ↥(c.H hV) 4 a) ∨
      (∃ m : ℕ, 3 ≤ m ∧ IsOmegaMinus ↥(c.H hV) 6 m)) :
    (c.phiL hV).ker = CFSG.pCore 2 ↥c.L := by
  have hbotH : CFSG.pCore 2 ↥(c.H hV) = ⊥ := hK.1 hnat
  have eY : (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) ≃* ↥(c.H hV) :=
    (QuotientGroup.quotientMulEquivOfEq hbotH).trans QuotientGroup.quotientBot
  have hshapeQ : (∃ m : ℕ, 3 ≤ m ∧
        IsSp4 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) m) ∨
      (∃ a : ℕ, 2 ≤ a ∧
        IsSUn (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) 4 a) ∨
      (∃ m : ℕ, 3 ≤ m ∧
        IsOmegaMinus (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) 6 m) := by
    rcases hshape with ⟨m, hm, hSp⟩ | ⟨a, ha, hSU⟩ | ⟨m, hm, hOm⟩
    · exact Or.inl ⟨m, hm, CFSG.Blueprint.LieModel.of_mulEquiv eY.symm hSp⟩
    · exact Or.inr (Or.inl ⟨a, ha, IsSUn.of_mulEquiv eY.symm hSU⟩)
    · exact Or.inr (Or.inr ⟨m, hm, IsOmegaMinus.of_mulEquiv eY.symm hOm⟩)
  exact comap_pCore_eq_of_pCore_eq_bot_of_kSchurC1 (c.phiL hV) (c.phiL_surjective hV)
    (c.commutator_L_eq_top) (c.phiL_ker_commutator_mem_pCore hV hK hnat) hSC hshapeQ hbotH

private theorem mem_normalizer_of_forall_conj_mem {H : Type} [Group H] [Finite H]
    {A : Subgroup H} {w : H} (hw : ∀ a ∈ A, w * a * w⁻¹ ∈ A) :
    w ∈ Subgroup.normalizer (A : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_le : A.map (MulAut.conj w).toMonoidHom ≤ A := by
    rintro - ⟨x, hx, rfl⟩
    exact hw x hx
  exact Subgroup.eq_of_le_of_card_ge hmap_le
    (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])

private theorem comap_zpowers_eq_ker_sup_and_isSylowOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {a : ↥c.L}
    (haord : orderOf a = p) :
    (Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV) =
        (c.phiL hV).ker ⊔ Subgroup.zpowers a ∧
      CFSG.ABGLocalTools.IsSylowOf p (Subgroup.zpowers a)
        ((Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hR_eq : (Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV) =
      (c.phiL hV).ker ⊔ Subgroup.zpowers a := by
    rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, sup_comm]
  have hkerP : IsPGroup 2 (c.phiL hV).ker := by
    rw [hker_eq]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hcop : Nat.Coprime p (Nat.card (c.phiL hV).ker) := by
    obtain ⟨k, hk⟩ := hkerP.exists_card_eq
    rw [hk]
    exact (hp.coprime_iff_not_dvd.mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)).pow_right k
  have hQsyl : IsPGroup p (Subgroup.zpowers a) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, haord]; norm_num⟩
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p (Subgroup.zpowers a)
      ((Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV)) := by
    have h := CFSG.ABGLocalTools.isSylowOf_sup_of_coprime (p := p)
      (N := (c.phiL hV).ker) (Q := Subgroup.zpowers a) hcop hQsyl
    simpa [← hR_eq] using h
  exact ⟨hR_eq, hRsyl⟩

private theorem zpowers_le_normalizer_comap {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Astar : Subgroup ↥(c.H hV)} {w : ↥(c.H hV)} {g : ↥c.L}
    (hw_norm : w ∈ Subgroup.normalizer (Astar : Set ↥(c.H hV)))
    (hgφ : c.phiL hV g = w) :
    Subgroup.zpowers g ≤
      Subgroup.normalizer (((Astar.comap (c.phiL hV) : Subgroup ↥c.L) : Set ↥c.L)) := by
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_comap] at hx ⊢
    have hφg : c.phiL hV (g * x * g⁻¹) = w * c.phiL hV x * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hgφ]
    rw [hφg]
    exact (Subgroup.mem_normalizer_iff.mp hw_norm (c.phiL hV x)).mp hx
  · intro hx
    rw [Subgroup.mem_comap] at hx ⊢
    have hφg : c.phiL hV (g * x * g⁻¹) = w * c.phiL hV x * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hgφ]
    have hconj : w * c.phiL hV x * w⁻¹ ∈ Astar := by
      rwa [hφg] at hx
    exact (Subgroup.mem_normalizer_iff.mp hw_norm (c.phiL hV x)).mpr hconj

private theorem sup_ker_zpowers_le_inf_subgroupOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    (h1930 : H1930 D) {a : ↥c.L} (haK : (a : G) ∈ Hinf (D.M ⊓ c.L)) :
    (c.phiL hV).ker ⊔ Subgroup.zpowers a ≤ (D.M ⊓ c.L).subgroupOf c.L := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have hxP : x ∈ CFSG.pCore 2 ↥c.L := by rwa [← hker_eq]
    have hxPof : (x : G) ∈ CFSG.Open.pCoreOf 2 c.L :=
      Subgroup.mem_map_of_mem c.L.subtype hxP
    exact s23_9_O2L_of h1930 c hxPof
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have hx' : (x : G) ∈ Subgroup.zpowers (a : G) := by
      simpa [MonoidHom.map_zpowers] using Subgroup.mem_map_of_mem c.L.subtype hx
    exact ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left)
      (Subgroup.zpowers_le.mpr haK hx')

private theorem mem_stabilizer_of_frattini {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {p : ℕ} {Astar Pℓ : Subgroup ↥(c.H hV)}
    {w : ↥(c.H hV)} {a g nL mL : ↥c.L}
    (hN : ∀ a : ↥c.L, (a : G) ∈ Hinf (D.M ⊓ c.L) → orderOf a = p →
      c.phiL hV a ∈ Astar →
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) ≤ D.M)
    (hPℓ : ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ)
    (hR_le_ML : (Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV) ≤
      (D.M ⊓ c.L).subgroupOf c.L)
    (hnLR : nL ∈ (Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV))
    (hmLnorm : mL ∈ Subgroup.normalizer (Subgroup.zpowers a : Set ↥c.L))
    (haK : (a : G) ∈ Hinf (D.M ⊓ c.L)) (haord : orderOf a = p)
    (haφA : c.phiL hV a ∈ Astar)
    (hg_eq : g = nL * mL) (hgφ : c.phiL hV g = w) : w ∈ Pℓ := by
  have hnM : (nL : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp (hR_le_ML hnLR)).1
  have hmLnormG : (mL : G) ∈ Subgroup.normalizer
      (Subgroup.zpowers (c.L.subtype a) : Set G) := by
    have hmMap : (mL : G) ∈ (Subgroup.normalizer
        (Subgroup.zpowers a : Set ↥c.L)).map c.L.subtype :=
      Subgroup.mem_map_of_mem _ hmLnorm
    have hle := Subgroup.le_normalizer_map (f := c.L.subtype)
      (H := Subgroup.zpowers a) hmMap
    simpa only [MonoidHom.map_zpowers] using hle
  have hmM : (mL : G) ∈ D.M := hN a haK haord haφA hmLnormG
  have hgM : (g : G) ∈ D.M := by
    have hval : (g : G) = (nL : G) * (mL : G) := by
      simpa using congrArg Subtype.val hg_eq
    rw [hval]
    exact D.M.mul_mem hnM hmM
  have hg_ML : g ∈ (D.M ⊓ c.L).subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hgM, g.2⟩
  rw [← hPℓ]
  exact Subgroup.mem_map.mpr ⟨g, hg_ML, hgφ⟩

theorem mem_stabilizer_of_forall_normalizer_le_M {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) (h1930 : H1930 D)
    {Kstar Pℓ : Subgroup ↥(c.H hV)}
    (hPℓ : ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ)
    (hKstar_eq : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    {Astar : Subgroup ↥(c.H hV)} (hAstar_le : Astar ≤ Kstar)
    (hAstar_card : Nat.card ↥Astar = p)
    {w : ↥(c.H hV)} (hw_norm : ∀ a ∈ Astar, w * a * w⁻¹ ∈ Astar)
    (hN : ∀ a : ↥c.L, (a : G) ∈ Hinf (D.M ⊓ c.L) → orderOf a = p →
      c.phiL hV a ∈ Astar →
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) ≤ D.M)
    {g : ↥c.L} (hgφ : c.phiL hV g = w) : w ∈ Pℓ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haK, haord, haφA, hAeq⟩ :=
    c.exists_mem_orderOf_eq_prime_of_le_Hinf hV hp hp2 hker_eq hKstar_eq hAstar_le hAstar_card
  have hw_norm_sub : w ∈ Subgroup.normalizer (Astar : Set ↥(c.H hV)) :=
    mem_normalizer_of_forall_conj_mem hw_norm
  obtain ⟨hR_eq, hRsyl⟩ :=
    comap_zpowers_eq_ker_sup_and_isSylowOf c hV hp hp2 hker_eq haord
  have hR_le_ML : (Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV) ≤
      (D.M ⊓ c.L).subgroupOf c.L :=
    hR_eq.symm ▸
      sup_ker_zpowers_le_inf_subgroupOf c hV hker_eq h1930 (Subgroup.mem_subgroupOf.mp haK)
  have hg_norm_R : Subgroup.zpowers g ≤ Subgroup.normalizer
      (((Subgroup.zpowers (c.phiL hV a)).comap (c.phiL hV) : Subgroup ↥c.L) :
        Set ↥c.L) := by
    simpa only [hAeq, hR_eq] using zpowers_le_normalizer_comap c hV hw_norm_sub hgφ
  obtain ⟨nL, hnLR, mL, hmLnorm, hg_eq⟩ :=
    CFSG.RankThree.PartTwo.Sec18.exists_mul_of_isSylowOf hRsyl hg_norm_R
      (Subgroup.mem_zpowers g)
  exact mem_stabilizer_of_frattini c hV hN hPℓ hR_le_ML hnLR hmLnorm
    (Subgroup.mem_subgroupOf.mp haK) haord haφA hg_eq hgφ

end Ctx23L

noncomputable def pointStabilizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(c.H hV) :=
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  MulAction.stabilizer ↥(c.H hV)
    (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
      Set (c.W hV)))

noncomputable def residualPointStabilizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : Subgroup ↥(c.H hV) :=
  Hinf (pointStabilizer c hV)

theorem map_inf_eq_pointStabilizer_and_residual {D : Data G} {Ch : Choice2011 G}
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = pointStabilizer c hV ∧
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) =
        residualPointStabilizer c hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  constructor
  · dsimp only [pointStabilizer]
    simpa only [hℓ] using c.map_inf_eq_stabilizer_Ztil hV h4 h1930
  · dsimp only [residualPointStabilizer, pointStabilizer]
    simpa only [hℓ] using c.map_Hinf_inf_eq hV h4 h1930

private theorem exists_KGen_order_three {D : Data G} {Ch : Choice2011 G}
    (hG : KGen) (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSp4 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
      (IsOmegaMinus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))) :
    ∃ A : Subgroup ↥(c.H hV), A ≤ residualPointStabilizer c hV ∧
      Nat.card ↥A = 3 ∧ ∃ w : ↥(c.H hV), w ∉ pointStabilizer c hV ∧
        ∀ a ∈ A, w * a * w⁻¹ ∈ A := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rcases hline with ⟨hSp, hNatSp⟩ | ⟨a, hn2, hSU, hNatSU⟩ | ⟨hOm, hNatOm⟩
  · simpa only [pointStabilizer, residualPointStabilizer] using
      hG (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
        (c.commutator_H_eq hV) h3 (c.sylowStar hV) |>.1 ⟨hSp, hNatSp⟩
  · simpa only [pointStabilizer, residualPointStabilizer] using
      hG (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
        (c.commutator_H_eq hV) h3 (c.sylowStar hV) |>.2.1 ⟨a, hn2, hSU, hNatSU⟩
  · simpa only [pointStabilizer, residualPointStabilizer] using
      hG (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
        (c.commutator_H_eq hV) h3 (c.sylowStar hV) |>.2.2 ⟨hOm, hNatOm⟩

private theorem exists_KGen_data {D : Data G} {Ch : Choice2011 G}
    (hA : KTab23a) (h4 : S23_4 D Ch) (hG : KGen)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSp4 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
      (IsOmegaMinus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))) :
    ∃ (Pℓ Kstar : Subgroup ↥(c.H hV)) (A : Subgroup ↥(c.H hV)) (w : ↥(c.H hV)),
      ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ ∧
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar ∧
      A ≤ Kstar ∧ Nat.card ↥A = 3 ∧ w ∉ Pℓ ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A := by
  let Pℓ : Subgroup ↥(c.H hV) := pointStabilizer c hV
  let Kstar : Subgroup ↥(c.H hV) := residualPointStabilizer c hV
  obtain ⟨hPℓ, hKstar⟩ :=
    map_inf_eq_pointStabilizer_and_residual hA h4 h1930 c hV hnat
  obtain ⟨A, hA_le, hAcard, w, hw_notPℓ, hw_norm⟩ :=
    exists_KGen_order_three hG c hV h3 hnat hline
  exact ⟨Pℓ, Kstar, A, w, hPℓ, hKstar, hA_le, hAcard, hw_notPℓ, hw_norm⟩

private theorem exists_thin_component_of_order_three {D : Data G} {Ch : Choice2011 G}
    (h8 : S23_8 D Ch) (hd : KTab23d)
    (hB23 : S23_9_B23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSp4 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
      (IsOmegaMinus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)))
    {Kstar A : Subgroup ↥(c.H hV)}
    (hKstar_eq : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hA_le : A ≤ Kstar) (hAcard : Nat.card ↥A = 3) :
    ∃ Y : Subgroup G, Y ∈ calC D.M ∧ Hinf (D.M ⊓ c.L) ≤ Y ∧ F08.Thin8 Y := by
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  have hK_ne_bot : K ≠ ⊥ := by
    intro hKbot
    dsimp only [K] at hKbot
    have hKstar_bot : Kstar = ⊥ := by
      rw [← hKstar_eq, hKbot]
      simp
    have hAle : A ≤ (⊥ : Subgroup ↥(c.H hV)) := hKstar_bot ▸ hA_le
    have hAbot : A = ⊥ := le_bot_iff.mp hAle
    have hcard : Nat.card ↥A = 1 := by rw [hAbot]; simp
    omega
  obtain ⟨Y, hYcal, hKY⟩ :=
    exists_component_of_B23 c hV h3 hnat hline hd hB23 h1930 hK_ne_bot
  exact ⟨Y, hYcal, hKY, thin8_of_mem_calC h8 h1930 c hYcal⟩

private theorem normalizer_zpowers_le_M_of_thin_component {D : Data G} {Ch : Choice2011 G}
    (h4 : S23_4 D Ch) (h847 : R847ThinCZ D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {Y K : Subgroup G}
    (hYcal : Y ∈ calC D.M) (hYthin : F08.Thin8 Y) (hKY : K ≤ Y)
    {A : Subgroup ↥(c.H hV)} :
    ∀ a : ↥c.L, (a : G) ∈ K → orderOf a = 3 → c.phiL hV a ∈ A →
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) ≤ D.M := by
  intro a haK haord _
  have haY : (a : G) ∈ Y := hKY haK
  have haordG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans haord
  exact Ctx23L.normalizer_zpowers_le_M_of_r847ThinCZ c h1930 h4 h847 hYcal
    hYthin haY Nat.prime_three (by norm_num) haordG

theorem s23_9_NotSp4SU4O6m_of (D : Data G) (Ch : Choice2011 G)
    (hA : KTab23a) (hd : KTab23d) (hG : KGen)
    (h4 : S23_4 D Ch) (h8 : S23_8 D Ch) (h847 : R847ThinCZ D)
    (hB23 : S23_9_B23 D Ch) (hK : KOrdNatural) (hSC : KSchurC1) :
    S23_9_NotSp4SU4O6m D Ch := by
  intro h1930 c h3 hV
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  change ¬ ((IsSp4 ↥(c.H hV) n ∧ NatSpn (c.H hV) ⊤ ⊥ 4 n) ∨
    (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧ NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
    (IsOmegaMinus ↥(c.H hV) 6 n ∧ NatOmegaMinus (c.H hV) ⊤ ⊥ 6 n))
  intro hline
  have hnat : IsNaturalClassicalModule (c.H hV) n := by
    rcases hline with ⟨hSp, hNatSp⟩ | ⟨a, hn2, hSU, hNatSU⟩ | ⟨hOm, hNatOm⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨hSp, hNatSp⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨a, hn2, hSU, hNatSU⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨hOm, hNatOm⟩
  obtain ⟨Pℓ, Kstar, A, w, hPℓ_image, hKstar_eq, hA_le, hAcard, hw_notPℓ, hw_norm⟩ :=
    exists_KGen_data hA h4 hG h1930 c hV (by simpa only [n] using h3)
      (by simpa only [n] using hnat) (by simpa only [n] using hline)
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  obtain ⟨Y, hYcal, hKY, hYthin⟩ :=
    exists_thin_component_of_order_three h8 hd hB23 h1930 c hV
      (by simpa only [n] using h3) (by simpa only [n] using hnat)
      (by simpa only [n] using hline) hKstar_eq hA_le hAcard
  have hshape : (∃ m : ℕ, 3 ≤ m ∧ IsSp4 ↥(c.H hV) m) ∨
      (∃ a : ℕ, 2 ≤ a ∧ IsSUn ↥(c.H hV) 4 a) ∨
      (∃ m : ℕ, 3 ≤ m ∧ IsOmegaMinus ↥(c.H hV) 6 m) := by
    rcases hline with ⟨hSp, -⟩ | ⟨a, hn2, hSU, -⟩ | ⟨hOm, -⟩
    · exact Or.inl ⟨n, h3, hSp⟩
    · exact Or.inr (Or.inl ⟨a, by omega, hSU⟩)
    · exact Or.inr (Or.inr ⟨n, h3, hOm⟩)
  have hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L :=
    c.phiL_ker_eq_pCore_of_kSchurC1 hV hK hnat hSC hshape
  have hN : ∀ a : ↥c.L, (a : G) ∈ K → orderOf a = 3 →
      c.phiL hV a ∈ A →
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) ≤ D.M :=
    normalizer_zpowers_le_M_of_thin_component h4 h847 h1930 c hV hYcal hYthin hKY
  obtain ⟨g, hgφ⟩ := c.phiL_surjective hV w
  exact hw_notPℓ (Ctx23L.mem_stabilizer_of_forall_normalizer_le_M c hV
    Nat.prime_three (by norm_num) hker_eq h1930 hPℓ_image hKstar_eq hA_le hAcard
    hw_norm hN hgφ)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
