module

public import CFSG.Quasithin.EmptyFaithful.SBd7Ms
public import CFSG.Quasithin.EmptyFaithful.A38c10MSa
public import CFSG.Quasithin.EmptyFaithful.S153F19

public section

namespace CFSG.Quasithin.A38c10.MS

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.FLc
  CFSG.Quasithin
open scoped commutatorElement Pointwise

section Pair

variable {G : Type} [Group G] [Finite G]

theorem exists_isModO2Surj {P S : Subgroup G} {ψ : ↥P →* SLt 3} (h : PsiData P S ψ) :
    ∃ α : ↥(perfectCore P) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
      IsModO2Surj (perfectCore P) α := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)
  refine ⟨e.toMonoidHom.comp (ψ.comp (Subgroup.inclusion (perfectCore_le P))),
    e.surjective.comp (psiK_surjective h), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective]
  exact ker_psiK h

theorem charTwo_sup_of_le {L P S : Subgroup G} (hL : CharTwo L) (hS : IsPGroup 2 ↥S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hPL : P ≤ L) (hOP : pCoreOf 2 L ≤ P ⊔ S) :
    CharTwo (P ⊔ S) := by
  classical
  set H : Subgroup G := P ⊔ S with hH
  set H₀ : Subgroup G := L ⊔ S with hH₀
  have hHH₀ : H ≤ H₀ := sup_le_sup_right hPL S
  have hH₀N : H₀ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := hHH₀.trans hH₀N
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hprod : (H₀ : Set G) = (L : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L S hSL
  set P' : Subgroup G := pCoreOf 2 H with hP'
  have hOLP : pCoreOf 2 L ≤ P' := by
    have hnorm : H ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
      normalizer_le_normalizer_pCoreOf 2 L (hHN hg)
    exact le_pCoreOf_of_le_normalizer 2 hOP hnorm (pCoreOf_isPGroup 2 L)
  set K' : Subgroup G := H ⊓ Subgroup.centralizer (P' : Set G) with hK'
  have hKN : H ≤ Subgroup.normalizer (K' : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      S153F.mem_normalizer_centralizer_of_mem_normalizer (le_normalizer_pCoreOf 2 H hg)⟩
  have hK2 : IsPGroup 2 ↥K' := by
    rintro ⟨x, hxK⟩
    obtain ⟨hxH, hxC⟩ := hxK
    obtain ⟨a, ha⟩ := SBd7.pow_mem_of_mul_pgroup hLH₀ hH₀N hprod hSH₀ hS x (hHH₀ hxH)
    have hxa : x ^ 2 ^ a ∈ H ⊓ Subgroup.centralizer (P' : Set G) :=
      ⟨H.pow_mem hxH _, Subgroup.pow_mem _ hxC _⟩
    have hmem : x ^ 2 ^ a ∈ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
      ⟨ha, fun p hp => (Subgroup.mem_centralizer_iff.mp hxa.2 p (hOLP hp))⟩
    have hpc : x ^ 2 ^ a ∈ pCoreOf 2 L := hL hmem
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 L) ⟨x ^ 2 ^ a, hpc⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using this
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hKN hK2

open CFSG.Quasithin.S153D in
theorem isMSPair_sup_S_of_K {T Mc M V₁ V₂ Yp I L K : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hKI : K ≤ I)
    (hSK : Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G))
    (hchar : CharTwo (K ⊔ Sgp153 T V₁)) (hcomp : K ∈ cComp (K ⊔ Sgp153 T V₁))
    (hLie : IsRankTwoLie2Derived ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hKM : ¬ K ≤ M) (hV' : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ K)⁆ ≠ ⊥) :
    IsMSPair (K ⊔ Sgp153 T V₁) (Sgp153 T V₁) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hSI : Sgp153 T V₁ ≤ I := c.facts.sylow.1
  have hsqI : SQTKGroup ↥I := (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hKSI : K ⊔ Sgp153 T V₁ ≤ I := sup_le hKI hSI
  have hSp : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hset : ((K ⊔ Sgp153 T V₁ : Subgroup G) : Set G) = (K : Set G) * (Sgp153 T V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K _ hSK
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) (K ⊔ Sgp153 T V₁) :=
    SBd7.isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right hKSI
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (hh.decomp.le₁.trans hyp.VZ_le_T) Subgroup.le_normalizer
  have hS0 : Sgp153 T V₁ ≠ ⊥ := by
    intro hb
    have h1 : V₁ = ⊥ := le_bot_iff.mp (hb ▸ hV₁S)
    have h4 := hh.decomp.card₁
    rw [h1, Subgroup.card_bot] at h4
    omega
  have hno : ∀ C : Subgroup G, C ≤ Sgp153 T V₁ → C ≠ ⊥ →
      (C.subgroupOf (Sgp153 T V₁)).Characteristic →
        ¬ (K ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (C : Set G)) := fun C hCS hC1 hchar =>
    hyp.lemma_15_3_11_twelve hh.decomp hV' hKM hCS hC1 hchar
  have hH'le : (K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) ≤ K ⊔ Sgp153 T V₁ :=
    inf_le_left
  have hSH' : Sgp153 T V₁ ≤ (K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  have hchS : ((Sgp153 T V₁).subgroupOf (Sgp153 T V₁)).Characteristic :=
    ⟨fun φ => by rw [Subgroup.subgroupOf_self]; exact Subgroup.comap_top _⟩
  have hlt : (K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) < K ⊔ Sgp153 T V₁ := by
    refine lt_of_le_of_ne hH'le fun h => hno _ le_rfl hS0 hchS ?_
    calc K ⊔ Sgp153 T V₁
        = (K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G) := h.symm
      _ ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := inf_le_right
  have hodd : ¬ 2 ∣ ((K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)).relIndex
      (K ⊔ Sgp153 T V₁) := by
    intro hdvd
    apply hsyl.2.2
    have h1 := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁)
      ((K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)) (K ⊔ Sgp153 T V₁) hSH' hH'le
    have h2 : 2 ∣ (Sgp153 T V₁).relIndex (K ⊔ Sgp153 T V₁) := by
      rw [← h1]; exact Dvd.dvd.mul_left hdvd _
    exact h2
  have hcore : Sgp153 T V₁ =
      pCoreOf 2 ((K ⊔ Sgp153 T V₁) ⊓ Subgroup.normalizer (Sgp153 T V₁ : Set G)) := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 hSH' (fun g hg => hg.2) hSp
    · exact pCoreOf_le_of_isSylowTwoOf (SBd7.isSylowTwoOf_of_le_of_le' hsyl hSH' hH'le)
  exact ⟨⟨B5.sqtk_of_le hsqI hKSI, hchar, K, hcomp, hset, hLie⟩,
    Or.inl ⟨_, hlt, hodd, hcore⟩, hno⟩

omit [Finite G] in
theorem exists_order_three {Y₁ Y₂ P Yp : Subgroup G} [Finite G] (hY₁ : Y₁ ≤ Yp) (hY₂ : Y₂ ≤ Yp)
    (hc₁ : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3) (hc₂ : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3)
    (hYP : Y₁ ≤ P ∨ Y₂ ≤ P) : ∃ y ∈ Yp, y ∈ P ∧ orderOf y = 3 := by
  have key : ∀ Y : Subgroup G, Y ≤ Yp → (∃ a, Nat.card ↥Y = 2 ^ a * 3) → Y ≤ P →
      ∃ y ∈ Yp, y ∈ P ∧ orderOf y = 3 := by
    rintro Y hYYp ⟨a, ha⟩ hYP'
    have h3 : 3 ∣ Nat.card ↥Y := ⟨2 ^ a, by rw [ha]; ring⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine ⟨x, hYYp x.2, hYP' x.2, ?_⟩
    rw [← Subgroup.orderOf_coe] at hx
    exact hx
  rcases hYP with h | h
  · exact key Y₁ hY₁ hc₁ h
  · exact key Y₂ hY₂ hc₂ h

end Pair

end CFSG.Quasithin.A38c10.MS
