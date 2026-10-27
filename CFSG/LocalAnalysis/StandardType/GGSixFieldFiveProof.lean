module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerFive
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGFieldFiveNbrTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (ψ : (ggU t n 1).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ →
    ∀ D : Subgroup G, IsElemAbelian 5 D → Nat.card D = 5 ^ 2 →
      D ≤ Subgroup.normalizer (G₀ : Set G) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n 1).D ψ d) →
    ∀ x ∈ D, ∀ L : Subgroup G, IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) →
      GGNbrClauseFiveMarking 5 x L →
    ∀ J : Subgroup G, IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) →
      ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
        IsComponentOf K (G₀ ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
        x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K

@[expose] def GGFieldFiveRankTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (ψ : (ggU t n 1).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    ∀ E : Subgroup G, IsElemAbelian 5 E → E ≤ Subgroup.normalizer (G₀ : Set G) →
      (∀ e ∈ E, GGPsiInnerDiag (ggU t n 1).D ψ e) → Nat.card E < 5 ^ 4

end Inputs

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isComponentOf_of_inf_of_le_normalizer {G₀ C K : Subgroup G}
    (hK : IsComponentOf K (G₀ ⊓ C)) (hC : C ≤ Subgroup.normalizer (G₀ : Set G)) :
    IsComponentOf K C := by
  have hn : ((G₀ ⊓ C).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro g c hg hc
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hC hc) g).mp hg.1,
      C.mul_mem (C.mul_mem hc hg.2) (C.inv_mem hc)⟩
  exact isComponentOf_of_isSubnormal_of_isComponentOf hK
    (IsSubnormal.step inf_le_right hn (IsSubnormal.refl C))

theorem not_mem_zpowers_of_centralizer {p : ℕ} (hp : p.Prime) {x y : G} {K : Subgroup G}
    (hx : x ^ p = 1) (hx1 : x ≠ 1) (hy : y ^ p = 1) (hy1 : y ≠ 1)
    (hyK : y ∈ Subgroup.centralizer (K : Set G)) (hxK : x ∉ Subgroup.centralizer (K : Set G)) :
    y ∉ Subgroup.zpowers x := by
  intro hyx
  have : Fact p.Prime := ⟨hp⟩
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hyx
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx hx1, orderOf_eq_prime hy hy1])
  have hxy : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  exact hxK ((Subgroup.zpowers_le.mpr hyK) hxy)

theorem ggNbr_of_isComponentOf_le {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    {y : G} (hyD : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer {y})) (hJK : J ≤ K) (hpK : p ∣ Nat.card K)
    (hxK : x ∉ Subgroup.centralizer (K : Set G)) : GGNbr p B x D J y K := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hDJ.1.1 hyD
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hDJ.1.2.2.2.2.2.1.2.2
  have hD : D = Subgroup.closure {x, y} :=
    (ggClosure_pair_eq hp hDJ.1.2.2.1 hxD hyD hS.2.2.1 (hS.1.1.2 x hxB) hyx).symm
  have hKO : ¬ K ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)) := by
    intro hle
    have hcop : Nat.Coprime p
        (Nat.card (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)))) := by
      rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map,
        Subgroup.card_map_of_injective (Subgroup.centralizer ({y} : Set G)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (hpK.trans (Subgroup.card_dvd_of_le hle))
  have hA : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    (largeEvenPComponent_iff_lBalance p _ K).mpr
      ⟨hK.1, lBalanceIsPComponent_of_isComponentOf hK hKO⟩
  have hKL : K ≤ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G)) := le_sSup hA
  have hAJ : K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))),
      J.map (MulAut.conj a⁻¹).toMonoidHom := by
    calc K = ⨆ (a : G) (_ : a ∈ K), J.map (MulAut.conj a).toMonoidHom :=
          (eq_iSup_map_conj_of_isQuasisimple hK.2.2 hJq hJK).symm
      _ ≤ _ := by
        refine iSup₂_le fun a ha => ?_
        have h := le_iSup₂ (f := fun (a : G)
          (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))) =>
            J.map (MulAut.conj a⁻¹).toMonoidHom) a⁻¹ (hKL (K.inv_mem ha))
        rwa [inv_inv] at h
  have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcK : ∀ b ∈ Subgroup.normalizer (K : Set G),
      (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K →
        b ∈ Subgroup.centralizer (K : Set G) := fun b hbN h =>
    mem_centralizer_of_commutator_le_coprime hp hK.2.2 hpK hOcop
      (fun k hk => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hk)) hbN h
  have hxA : ¬ (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
    intro h
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
    have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxy
    have hxJ : x ∈ Subgroup.centralizer (J : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun j hj => Subgroup.mem_centralizer_singleton_iff.mp
        (hS.2.2.2.1.1 (hDJ.1.2.2.2.2.2.1.1 hj).1)
    exact hxK (hcK x (mem_normalizer_of_le_component hK hJq hJK hxCy hxJ) h)
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk)
  have hDK : ∀ b ∈ D, b ∈ Subgroup.centralizer (K : Set G) → b ∈ Subgroup.zpowers y := by
    intro b hbD hbK
    have hyH : Subgroup.zpowers y ≤ D ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hyD, hyK⟩
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow hp).mp
      (hDJ.1.2.2.1 ▸ Subgroup.card_dvd_of_le (inf_le_left :
        D ⊓ Subgroup.centralizer (K : Set G) ≤ D))
    have hi2 : i ≠ 2 := by
      rintro rfl
      have hH : D ⊓ Subgroup.centralizer (K : Set G) = D :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hHi, hDJ.1.2.2.1])
      have hxH : x ∈ D ⊓ Subgroup.centralizer (K : Set G) := by
        rw [hH]
        exact hxD
      exact hxK hxH.2
    have hle : Nat.card (D ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤
        Nat.card (Subgroup.zpowers y) := by
      rw [hHi, Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 y hyB) hy1]
      calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    have heq := Subgroup.eq_of_le_of_card_ge hyH hle
    rw [heq]
    exact ⟨hbD, hbK⟩
  refine ⟨⟨hS.1, hyB, hy1, hA.1, hA, fun b => ⟨?_, ?_⟩⟩, hD, hAJ, hxA⟩
  · rintro ⟨hbB, hbN, hbO⟩
    have hbK := hcK b hbN hbO
    have hbD : b ∈ D := by
      rw [hDJ.1.2.2.2.2.2.2]
      exact ⟨hbB, Subgroup.centralizer_le hJK hbK⟩
    exact hDK b hbD hbK
  · intro hb
    have hbA : b ∈ Subgroup.centralizer (K : Set G) := Subgroup.zpowers_le.mpr hyK hb
    refine ⟨Subgroup.zpowers_le.mpr hyB hb, Subgroup.centralizer_le_normalizer _ hbA, ?_⟩
    have hbot : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr hbA
    rw [hbot]
    exact bot_le

end Config

section Main

theorem two_le_of_ggFieldFiveNbrTag {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGFieldFiveNbrTag t) (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp5 : p = 5) : 2 ≤ f := by
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  by_contra hf
  obtain rfl : f = 1 := by omega
  subst hp5
  have hDel : IsElemAbelian 5 D := hctx.d_elem
  have hxD : x ∈ D := hctx.x_mem_d
  have hx1 : x ≠ 1 := hctx.sstar.2.2.1
  have hLmark : GGNbrClauseFiveMarking 5 x L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inl (Or.inl h.1)) hctx.stdType.1
  obtain ⟨y, hyD, hy1, K, hK, hJK, hpK, hxK, hnm⟩ := h G n ψ _ hctx.presents D hDel hctx.card_d
    (fun d hd => hctx.bstar_le_normalizer (hctx.d_le_bstar hd))
    (fun d hd => hctx.2.2.2.2.2.2.1.2 d (hctx.d_le_bstar hd)) x hxD L hctx.l_isComponentOf_inf
    hLmark J hctx.j_comp
  have hKc : IsComponentOf K (Subgroup.centralizer {y}) :=
    isComponentOf_of_inf_of_le_normalizer hK (s1.2.1.centralizer_le hyD hy1)
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKc.1 hk)
  have hyx : y ∉ Subgroup.zpowers x :=
    not_mem_zpowers_of_centralizer (by norm_num) (hDel.2 x hxD) hx1 (hDel.2 y hyD) hy1 hyK hxK
  have hnbr : GGNbr 5 B x D J y K :=
    ggNbr_of_isComponentOf_le hctx.thmI hctx.stdSub hyD hyx hKc hJK hpK hxK
  exact hnm (hctx.stdType.2.2.1 y K (isNeighborOf_of_ggNbr hctx.stdSub hnbr)).2

theorem two_le_of_ggFieldFiveRankTag {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGFieldFiveRankTag t) (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp5 : p = 5) : 2 ≤ f := by
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  by_contra hf
  obtain rfl : f = 1 := by omega
  subst hp5
  have h4 := ggAKF_pow_four_le_card_bstar hctx
  have h5 := h G n ψ _ hctx.presents s1.1 Bs hctx.bstar.2.1 hctx.bstar_le_normalizer
    (fun e he => hctx.2.2.2.2.2.2.1.2 e he)
  omega

theorem ggSixFieldFiveInput_of_tags (h : ∀ t, GGFieldFiveNbrTag t) : GGSixFieldFiveInput :=
  fun _ _ _ _ _ _ _ _ _ _ t _ _ _ hctx s1 hp5 => two_le_of_ggFieldFiveNbrTag (h t) hctx s1 hp5

theorem ggSixFieldFiveInput_of_tags_or_rank
    (h : ∀ t, GGFieldFiveNbrTag t ∨ GGFieldFiveRankTag t) : GGSixFieldFiveInput := by
  intro _ _ _ _ _ _ _ _ _ _ t _ _ _ hctx s1 hp5
  rcases h t with hN | hR
  · exact two_le_of_ggFieldFiveNbrTag hN hctx s1 hp5
  · exact two_le_of_ggFieldFiveRankTag hR hctx s1 hp5

theorem ggFieldFiveNbrTag_of_vacuous (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGFieldFiveNbrTag t := by
  intro G _ _ n ψ G₀ hpres
  rcases ht with h | h | h | h | h | h | rfl
  all_goals first
    | exact absurd hpres not_ggPresentsG0_POmegaOdd
    | exact absurd hpres (not_ggPresentsG0_of_placeholder t (by simp [h]))

theorem ggSixFieldFiveInput_of_genuine (hPSL : GGFieldFiveNbrTag .PSL)
    (hPSU : GGFieldFiveNbrTag .PSU) (hPSp : GGFieldFiveNbrTag .PSp)
    (hPlus : GGFieldFiveNbrTag .POmegaPlus) (hMinus : GGFieldFiveNbrTag .POmegaMinus)
    (hF4 : GGFieldFiveNbrTag .F4) (hE6 : GGFieldFiveNbrTag .E6) (hE7 : GGFieldFiveNbrTag .E7)
    (hE8 : GGFieldFiveNbrTag .E8) (hTwE6 : GGFieldFiveNbrTag .twistedE6) :
    GGSixFieldFiveInput := by
  refine ggSixFieldFiveInput_of_tags fun t => ?_
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | _ => exact ggFieldFiveNbrTag_of_vacuous _ (by simp)

end Main

end CFSG.StandardType
