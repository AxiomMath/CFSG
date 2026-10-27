module

public import CFSG.Quasithin.Background.E6TwentyThree
public import CFSG.Quasithin.Background.E6TwentyThreeKG
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.Background.E6OneTwoFour
public import CFSG.Quasithin.Background.C124AsmBlock

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623CCompBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U₀ X : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → U₀ ≤ V → E3.mQuot V U₀ = 2 →
    U₀ ∈ gammaE64 V M → X ∈ cComp (Subgroup.centralizer (U₀ : Set G)) →
    ¬ CFSG.IsQuasisimple ↥X → ¬ X ≤ M → V ⊓ Subgroup.centralizer (X : Set G) = U₀ →
    ∃ K : Subgroup G, T ⊓ Subgroup.centralizer (V : Set G) ≤ K ∧
      K ≤ Subgroup.centralizer (U₀ : Set G) ∧ CharTwo K ∧ IsBlock2 K X ∧ IsLin2Type X 2 ∧
      IsBorelOfBlock X (X ⊓ (K ⊓ M))

section Alt

variable {G : Type} [Group G]

theorem card_quot_eq_sixty_of_altType {L : Subgroup G} (h5 : IsAltType L 5) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
  obtain ⟨α, hαs, hαk, -⟩ := h5
  rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
    Nat.card_eq_fintype_card]
  decide

theorem not_isPGroup_two_of_altType {L : Subgroup G} (h5 : IsAltType L 5) :
    ¬ IsPGroup 2 ↥L := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hαs, -⟩ := h5
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (h2.of_surjective α hαs)
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hcardA] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

end Alt

section Main

variable {G : Type} [Group G] [Finite G]

theorem mem_cComp_of_hyperplane (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h621 : E621Stmt) (h68 : E68Stmt)
    (hKG : E623CentA5Block) (hCC : E623CCompBlock) {T M V U U₀ L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (hm : 2 < E3.mParam (autI hV M)) (hUV : U ≤ V)
    (hU1 : E3.mQuot V U = 1) (hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M)
    (hL : IsBlock2 (Subgroup.centralizer (U : Set G)) L) (h5 : IsAltType L 5) (hLM : ¬ L ≤ M)
    (hU₀U : U₀ ≤ U) (hU₀1 : U₀ ≠ ⊥) (hidx : U₀.relIndex U = 2) :
    L ∈ cComp (Subgroup.centralizer (U₀ : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hU2 : IsPGroup 2 U := hV2.to_le hUV
  have hU₀V : U₀ ≤ V := hU₀U.trans hUV
  have hHH₀ : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (U₀ : Set G) :=
    Subgroup.centralizer_le hU₀U
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hq1 : E3.mQuot U U₀ = 1 := by
    have h1 := E3.relIndex_eq_two_pow hU2 U₀
    rw [hidx] at h1
    have h1' : 2 ^ 1 = 2 ^ E3.mQuot U U₀ := by rw [pow_one]; exact h1
    exact (Nat.pow_right_injective le_rfl h1').symm
  have hq2 : E3.mQuot V U₀ = 2 := by
    have h1 := E3.mQuot_add hU₀U hUV
    omega
  have hH₀M : ¬ Subgroup.centralizer (U₀ : Set G) ≤ M := fun hle => hUM (hHH₀.trans hle)
  have hU₀Γ : U₀ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₀V hU₀1 hH₀M (by omega)
  have hO₀ : oddCoreIn (Subgroup.centralizer (U₀ : Set G)) = ⊥ :=
    h621 G T M V U₀ hV h (Or.inr hm) hU₀V hU₀1
  have h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
    rw [card_quot_eq_sixty_of_altType h5]
    norm_num
  have hLc : L ∈ cComp (Subgroup.centralizer (U : Set G)) := L238.mem_cComp_of_isBlock2 hL h3
  obtain ⟨X, hX, hLX⟩ := exists_cComp_of_le h37 h39 h hU₀Γ hU₀U hUV hLc
  by_cases hXL : X = L
  · exact hXL ▸ hX
  exfalso
  have hXH₀ : X ≤ Subgroup.centralizer (U₀ : Set G) := le_of_mem_cComp hX
  have hCVL : V ⊓ Subgroup.centralizer (L : Set G) = U := by
    have hUCL : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun l hl =>
        (Subgroup.mem_centralizer_iff.1 (hL.2.1 hl) u hu).symm
    rcases eq_or_eq_of_mQuot_eq_one hV2 hUCL inf_le_left hU1 with h1 | h1
    · exact h1
    · exfalso
      apply hLM
      refine le_trans (fun l hl => ?_) h.centralizer_le
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ V ⊓ Subgroup.centralizer (L : Set G) := by rw [h1]; exact hv
      exact (Subgroup.mem_centralizer_iff.1 hv'.2 l hl).symm
  have hpcH : pCoreOf 2 (Subgroup.centralizer (U : Set G)) ≠ ⊥ := by
    intro h0
    apply hU₀1
    have hU1' : U ≤ pCoreOf 2 (Subgroup.centralizer (U : Set G)) :=
      C1.le_pCoreOf_of_normalized (fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' =>
        hVc _ (hUV hw') _ (hUV hw)) (Subgroup.centralizer_le_normalizer _) hU2
    rw [h0] at hU1'
    exact le_bot_iff.1 (hU₀U.trans hU1')
  have hCVX : V ⊓ Subgroup.centralizer (X : Set G) = U₀ := by
    have hle1 : U₀ ≤ V ⊓ Subgroup.centralizer (X : Set G) := le_inf hU₀V fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hXH₀ hx) u hu).symm
    have hle2 : V ⊓ Subgroup.centralizer (X : Set G) ≤ U := by
      rw [← hCVL]
      exact inf_le_inf_left _ (Subgroup.centralizer_le hLX)
    rcases eq_or_eq_of_mQuot_eq_one hU2 hle1 hle2 hq1 with h1 | h1
    · exact h1
    · exfalso
      have hXH : X ≤ Subgroup.centralizer (U : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hu' : u ∈ V ⊓ Subgroup.centralizer (X : Set G) := by rw [h1]; exact hu
        exact (Subgroup.mem_centralizer_iff.1 hu'.2 x hx).symm
      have hXc : X ∈ cComp (Subgroup.centralizer (U : Set G)) := cComp_mem_of_le hX hXH hHH₀
      have hQH : Q ≤ Subgroup.centralizer (U : Set G) :=
        inf_le_right.trans (Subgroup.centralizer_le hUV)
      have hLfam : L ∈ lFamily Q := cComp_subset_lFamily hQH hLc
      exact hXL (Vol2Native.lemma_1_2_4_unique hq.1 h37 hpcH hLfam hXc hLc hLX le_rfl)
  obtain ⟨u, huU, huU₀⟩ : ∃ u ∈ U, u ∉ U₀ := by
    by_contra hall
    push Not at hall
    have h1 : U = U₀ := le_antisymm (fun w hw => hall w hw) hU₀U
    rw [h1, Subgroup.relIndex_self] at hidx
    omega
  have hCU := centralizer_eq_inf_of_relIndex_two hU₀U hidx huU huU₀
  have huV : u ∈ V := hUV huU
  have huC : u ∉ Subgroup.centralizer (X : Set G) := fun huC =>
    huU₀ (by rw [← hCVX]; exact ⟨huV, huC⟩)
  have hLu : ∀ l ∈ L, u * l = l * u := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hL.2.1 hl) u huU
  have hXM : ¬ X ≤ M := fun hle => hLM (hLX.trans hle)
  by_cases hXq : CFSG.IsQuasisimple ↥X
  ·
    have hXc : IsComponentIn X (Subgroup.centralizer (U₀ : Set G)) :=
      Id2519.isComponentIn_of_mem_cComp hX hXq
    obtain ⟨-, hcases⟩ := h68 G T M V U₀ X hV h hU₀Γ hXc
    have hm2 : E3.mQuot V (V ⊓ Subgroup.centralizer (X : Set G)) = 2 := by rw [hCVX, hq2]
    have htype :
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 2 2 2 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 2 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 2 ∨
        Nonempty (↥X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 7)) := by
      rcases hcases with ⟨k, htype, -, -, -, -, hk, -, -⟩ | ⟨k, -, htype, -, -, hb⟩ |
          ⟨-, -, -, h1, -⟩ | ⟨htype, -, -, -⟩ | ⟨-, -, h1, -⟩
      ·
        have hk2 : k = 2 := by omega
        subst hk2
        rcases htype with ⟨-, h⟩ | ⟨-, h3, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · omega
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      ·
        rcases hb with ⟨-, ⟨h2k, -⟩ | ⟨-, h1⟩⟩ | ⟨-, -, -, hk, -⟩
        ·
          have hk1 : k = 1 := by omega
          subst hk1
          rcases htype with ⟨h2, -⟩ | ⟨-, h⟩
          · omega
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · omega
        ·
          have hk2 : k = 2 := by omega
          subst hk2
          rcases htype with ⟨-, h⟩ | ⟨h1, -⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · omega
      · omega
      ·
        rcases htype with h | ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · omega
    have hQH₀ : IsSylowTwoOf Q (Subgroup.centralizer (U₀ : Set G)) := e6_5_one h hU₀Γ
    have hVQ : V ≤ Q := h.le_inf_centralizer
    have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
    have hVH₀ : V ≤ Subgroup.centralizer (U₀ : Set G) := hVQ.trans hQH₀.1
    have hcore : CFSG.pPrimeCore 2 ↥(Subgroup.centralizer (U₀ : Set G)) = ⊥ :=
      pPrimeCore_eq_bot_of_oddCoreIn' hO₀
    have hQ2' : IsPGroup 2 (Q.subgroupOf (Subgroup.centralizer (U₀ : Set G))) :=
      hQH₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH₀.1).symm
    set P : Sylow 2 ↥(Subgroup.centralizer (U₀ : Set G)) := hQ2'.toSylow hQH₀.2.2 with hPdef
    have huN : u ∈ Subgroup.normalizer (X : Set G) := by
      have hvz : (⟨u, hVH₀ huV⟩ : ↥(Subgroup.centralizer (U₀ : Set G))) ∈
          Subgroup.centralizer ((P : Subgroup ↥(Subgroup.centralizer (U₀ : Set G))) :
            Set ↥(Subgroup.centralizer (U₀ : Set G))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subtype.ext
          (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) u huV).symm
      have hvzS : (⟨u, hVH₀ huV⟩ : ↥(Subgroup.centralizer (U₀ : Set G))) ∈
          (P : Subgroup ↥(Subgroup.centralizer (U₀ : Set G))) := show u ∈ Q from hVQ huV
      have hnorm := central_sylow_normalizes_components hcore P hvz hvzS hXc.2
      have h2 : u ∈ (Subgroup.normalizer
          ((X.subgroupOf (Subgroup.centralizer (U₀ : Set G)) :
            Subgroup ↥(Subgroup.centralizer (U₀ : Set G))) :
            Set ↥(Subgroup.centralizer (U₀ : Set G)))).map
          (Subgroup.centralizer (U₀ : Set G)).subtype := ⟨_, hnorm, rfl⟩
      rw [map_subtype_normalizer hXc.1] at h2
      exact h2.2
    have hXuH : X ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (U : Set G) := by
      rw [hCU]
      exact inf_le_inf_right _ hXH₀
    have hLB : IsBlock2 (X ⊓ Subgroup.centralizer ({u} : Set G)) L := by
      refine ⟨hL.1, le_inf hLX fun l hl => Subgroup.mem_centralizer_singleton_iff.2
        (hLu l hl).symm, ?_⟩
      have h1 := hL.2.2.comap (Subgroup.inclusion hXuH)
      convert h1 using 1
      ext x
      simp [Subgroup.mem_subgroupOf]
    exact hKG G X u hXq htype huN (h.isElemAbelian.2 u huV) huC L hLB h5
  ·
    obtain ⟨K, hQK, hKU₀, hK, hXK, hlin, hBor⟩ :=
      hCC G T M V U₀ X hV h hm hU₀V hq2 hU₀Γ hX hXq hXM hCVX
    have hQK' : IsSylowTwoOf Q K := A4.isSylowTwoOf_mono (e6_5_one h hU₀Γ) hQK hKU₀
    have hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
      (e6_5_three h hU₀Γ).2 ⟨hKU₀ hg.1, hg.2⟩
    have hVX : ¬ V ≤ Subgroup.centralizer (X : Set G) := fun hle => huC (hle huV)
    obtain ⟨-, -, -, -, -, -, -, hC2⟩ := lin2_block_torus'' hV h.le hQK'
      (inf_le_left.trans h.inM.2) hKN hK hXK (by norm_num) hlin hBor hVX
    apply not_isPGroup_two_of_altType h5
    intro l
    obtain ⟨k, hk⟩ := hC2 u huV huC l (hLX l.2) (hLu l l.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem e623A5Dichotomy_of (h311 : Theorem311Stmt) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h621 : E621Stmt) (h68 : E68Stmt)
    (hKG : E623CentA5Block) (hCC : E623CCompBlock) : E623A5Dichotomy := by
  intro G _ _ T M V U L hV h hm hr hUV hU1 hUM hH hL h5 hLM t ht
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hU2 : IsPGroup 2 U := hV2.to_le hUV
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.normal ht
  by_cases hUt : CFSG.conjugate U t = U
  ·
    have htH : t ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
      rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_centralizer, hUt]
    have hLt : IsBlock2 (Subgroup.centralizer (U : Set G)) (CFSG.conjugate L t) := by
      have h1 := Setup.Campbell.isBlock2_map_conj hL.1 t⁻¹
      have h2 : (Subgroup.centralizer (U : Set G)).map (MulAut.conj t⁻¹).toMonoidHom =
          Subgroup.centralizer (U : Set G) :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr htH
      rw [h2] at h1
      exact h1
    by_cases he : CFSG.conjugate L t = L
    · exact Or.inl he
    · exact Or.inr (distinctBlocksCommuteStatement _ L _ hH hL.1 hLt (Ne.symm he))
  ·
    have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h (Or.inr hm) hr).2
    have hcorank : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) → CFSG.conjugate U g ≠ U →
        (U ⊓ CFSG.conjugate U g).relIndex U = 2 ∧ U ⊓ CFSG.conjugate U g ≠ ⊥ := by
      intro g hgN hne
      have hgV : CFSG.conjugate U g ≤ V := conjugate_le_of_mem_normalizer hUV hgN
      have hgq : E3.mQuot V (CFSG.conjugate U g) = 1 := (mQuot_conjugate hgN).trans hU1
      have hle := mQuot_inf_left_le (U' := CFSG.conjugate U g) hV2 hUV
      rw [hgq] at hle
      have hne0 : E3.mQuot U (U ⊓ CFSG.conjugate U g) ≠ 0 := by
        intro h0
        have hle' : U ≤ CFSG.conjugate U g :=
          inf_eq_left.1 ((E3.mQuot_eq_zero_iff hU2 inf_le_left).1 h0)
        rcases eq_or_eq_of_mQuot_eq_one hV2 hle' hgV hU1 with h2 | h2
        · exact hne h2
        · rw [h2, E3.mQuot_self] at hgq
          omega
      have hm1 : E3.mQuot U (U ⊓ CFSG.conjugate U g) = 1 := by omega
      refine ⟨by rw [E3.relIndex_eq_two_pow hU2, hm1, pow_one], fun h0 => ?_⟩
      have hadd := E3.mQuot_add (inf_le_left : U ⊓ CFSG.conjugate U g ≤ U) hUV
      rw [hm1, hU1, h0] at hadd
      omega
    obtain ⟨hidx, hU₀1⟩ := hcorank t htN hUt
    have hUt' : CFSG.conjugate U t⁻¹ ≠ U := by
      intro he
      apply hUt
      have h1 := congrArg (fun S => CFSG.conjugate S t) he
      simp only [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one]
        at h1
      exact h1.symm
    obtain ⟨hidx', hU₀1'⟩ := hcorank t⁻¹ (Subgroup.inv_mem _ htN) hUt'
    have hL₀ := mem_cComp_of_hyperplane h37 h39 h621 h68 hKG hCC hV h hm hUV hU1 hUM hL.1 h5
      hLM inf_le_left hU₀1 hidx
    have hL₀' := mem_cComp_of_hyperplane h37 h39 h621 h68 hKG hCC hV h hm hUV hU1 hUM hL.1 h5
      hLM inf_le_left hU₀1' hidx'
    have hLt₀ : CFSG.conjugate L t ∈
        cComp (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G)) := by
      have h1 := cComp_map_mulEquiv (MulAut.conj t⁻¹) hL₀'
      have h2 : (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t⁻¹ : Subgroup G) : Set G)).map
          (MulAut.conj t⁻¹).toMonoidHom =
          Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G) := by
        change CFSG.conjugate
          (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t⁻¹ : Subgroup G) : Set G)) t = _
        rw [BenderBranch.conjugate_centralizer, BenderBranch.conjugate_inf,
          BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one, inf_comm]
      rw [h2] at h1
      exact h1
    have hB : IsBlock2 (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G)) L :=
      C124.isBlock2_of_short_of_mem_cComp hL₀ hL.1.1
    have hBt : IsBlock2 (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G))
        (CFSG.conjugate L t) :=
      C124.isBlock2_of_short_of_mem_cComp hLt₀ (Lin2.IsShort2.map_equiv hL.1.1 (MulAut.conj t⁻¹))
    have h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [card_quot_eq_sixty_of_altType h5]
      norm_num
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hL.1.1.2.2.2.1.resolve_right h3
    by_cases he : CFSG.conjugate L t = L
    · exact Or.inl he
    · exact Or.inr (C1Pack.commutator_eq_bot_of_quasisimple hB hq hBt (Ne.symm he))

end Main

end E6

end CFSG.Quasithin
