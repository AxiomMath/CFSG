module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyThree

variable {M V₀ V : Subgroup G}

theorem le_conjClosure (M L : Subgroup G) : L ≤ UC22.conjClosure M L := by
  intro z hz
  have hle : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ UC22.conjClosure M L :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _ ⟨1, M.one_mem, rfl⟩ le_rfl
  exact hle ⟨z, hz, by simp [MulAut.conj_apply]⟩

theorem conjClosure_le {M L : Subgroup G} (hLM : L ≤ M) : UC22.conjClosure M L ≤ M := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨x, hx, rfl⟩ := hK
  rintro _ ⟨z, hz, rfl⟩
  simpa [MulAut.conj_apply] using M.mul_mem (M.mul_mem hx (hLM hz)) (M.inv_mem hx)

theorem le_normalizer_conjClosure (M L : Subgroup G) :
    M ≤ normalizer (UC22.conjClosure M L : Set G) := by
  have key : ∀ g ∈ M, ∀ w ∈ UC22.conjClosure M L, g * w * g⁻¹ ∈ UC22.conjClosure M L := by
    intro g hg
    have hle : UC22.conjClosure M L ≤
        (UC22.conjClosure M L).comap (MulAut.conj g).toMonoidHom := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨x, hx, rfl⟩ := hK
      rintro _ ⟨z, hz, rfl⟩
      have hmem : (g * x) * z * (g * x)⁻¹ ∈ L.map (MulAut.conj (g * x)).toMonoidHom :=
        ⟨z, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have hK' : L.map (MulAut.conj (g * x)).toMonoidHom ≤ UC22.conjClosure M L :=
        le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _
          ⟨g * x, M.mul_mem hg hx, rfl⟩ le_rfl
      have e : (MulAut.conj g).toMonoidHom ((MulAut.conj x).toMonoidHom z) =
          (g * x) * z * (g * x)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [Subgroup.mem_comap, e]
      exact hK' hmem
    exact fun w hw => hle hw
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key g hg w, fun hw => ?_⟩
  have := key g⁻¹ (M.inv_mem hg) _ hw
  simpa [mul_assoc] using this

theorem barSub_pCoreOf_eq_bot (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V) (hne : V₀ ≠ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hirr : ConjGenerated M V₀ V) : barSub V₀ V hV (pCoreOf 2 M) = ⊥ := by
  haveI : Nontrivial (Vtil V₀ V hV) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h1 : Nat.card (Vtil V₀ V hV) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hnt
    have hc := card_Vtil_eq V₀ V hV hV₀V
    have h2 : Nat.card V ≤ Nat.card V₀ := by
      rw [hc]
      calc Nat.card V₀ * Nat.card (Vtil V₀ V hV)
          ≤ Nat.card V₀ * 1 := Nat.mul_le_mul_left _ h1
        _ = Nat.card V₀ := mul_one _
    exact hne (Subgroup.eq_of_le_of_card_ge hV₀V h2)
  have hP2 : IsPGroup 2 ↥(barSub V₀ V hV (pCoreOf 2 M)) := by
    intro φ
    obtain ⟨a, haP, ha⟩ := (mem_barSub V₀ V hV _ φ).1 φ.2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨(a : G), haP⟩
    have han : a ^ (2 ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← ha, ← map_pow, han, map_one, Subgroup.coe_one]
  exact eq_bot_of_isPGroup_of_stable hV hM hM₀ hirr hP2
    (TwelveEighteen.conj_mem_barSub hV (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))

theorem barSub_pCoreOf_eq_bot_of_isSubnormal (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hL : CFSG.Open.IsSubnormal L M) (h0 : barSub V₀ V hV (pCoreOf 2 M) = ⊥) :
    barSub V₀ V hV (pCoreOf 2 L) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_bot_iff.1 (h0 ▸ barSub_mono V₀ V hV (A4.pCoreOf_le_of_subnormal 2 hL))

theorem isSubnormal_barSub (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hL : CFSG.Open.IsSubnormal L M) :
    CFSG.Open.IsSubnormal (barSub V₀ V hV L) (barSub V₀ V hV M) := by
  exact (hL.comap (stabTil V₀ V).subtype).map (actTil V₀ V hV)

theorem isQuasisimple_barSub (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hLS : L ≤ stabTil V₀ V) (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L))
    (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) (hL1 : barSub V₀ V hV L ≠ ⊥) :
    CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV L) := by
  let φ : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLS)).codRestrict (barSub V₀ V hV L)
      (fun x => actTil_mem_barSub V₀ V hV x.2 (hLS x.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨a, haL, rfl⟩ := (mem_barSub V₀ V hV L ψ).1 hψ
    exact ⟨⟨a, haL⟩, rfl⟩
  have hker : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hLS x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V hV hxP (hLS x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  haveI : Nontrivial ↥(barSub V₀ V hV L) := (Subgroup.nontrivial_iff_ne_bot _).2 hL1
  let ψ : UC22.Bar2 L →* ↥(barSub V₀ V hV L) := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact uc22br4_isQuasisimple_of_surjective hLq ψ hψ

theorem barSub_map_conj (hV : IsElemAbelian 2 V) {L : Subgroup G} (hLS : L ≤ stabTil V₀ V)
    {g : G} (hg : g ∈ stabTil V₀ V) :
    barSub V₀ V hV (L.map (MulAut.conj g).toMonoidHom) =
      (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV ⟨g, hg⟩)).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨a, haK, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
    obtain ⟨l, hl, hla⟩ := haK
    refine ⟨actTil V₀ V hV ⟨l, hLS hl⟩, actTil_mem_barSub V₀ V hV hl (hLS hl), ?_⟩
    have hae : a = ⟨g, hg⟩ * ⟨l, hLS hl⟩ * (⟨g, hg⟩ : ↥(stabTil V₀ V))⁻¹ :=
      Subtype.ext (by simpa [MulAut.conj_apply] using hla.symm)
    rw [hae, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨l, hlL, rfl⟩ := (mem_barSub V₀ V hV L ψ).1 hψ
    refine (mem_barSub V₀ V hV _ _).2
      ⟨⟨g, hg⟩ * l * (⟨g, hg⟩ : ↥(stabTil V₀ V))⁻¹, ⟨l, hlL, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · rw [map_mul, map_mul, map_inv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem rankThreeLayer_barSub_conjClosure (hV : IsElemAbelian 2 V)
    (hMS : M ≤ stabTil V₀ V) {L : Subgroup G} (hL : CFSG.Open.IsSubnormal L M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (h0 : barSub V₀ V hV (pCoreOf 2 M) = ⊥) :
    rankThreeLayer (barSub V₀ V hV (UC22.conjClosure M L)) =
      barSub V₀ V hV (UC22.conjClosure M L) := by
  set X := UC22.conjClosure M L with hX
  refine le_antisymm (sSup_le fun _ hK => hK.1) ?_
  have hLM : L ≤ M := hL.le
  have hXM : X ≤ M := conjClosure_le hLM
  have hK : ∀ K ∈ UC22.conjSetOf M L,
      barSub V₀ V hV K ≤ rankThreeLayer (barSub V₀ V hV X) := by
    rintro K ⟨g, hgM, rfl⟩
    have hconj := barSub_map_conj hV (hLM.trans hMS) (hMS hgM)
    by_cases hL1 : barSub V₀ V hV L = ⊥
    · rw [hconj, hL1, Subgroup.map_bot]
      exact bot_le
    have hq := isQuasisimple_barSub hV (hLM.trans hMS) hLq
      (barSub_pCoreOf_eq_bot_of_isSubnormal hV hL h0) hL1
    have hqK : CFSG.Open.IsQuasisimple
        ↥(barSub V₀ V hV (L.map (MulAut.conj g).toMonoidHom)) := by
      rw [hconj]
      exact CFSG.Open.IsQuasisimple.of_mulEquiv
        ((barSub V₀ V hV L).equivMapOfInjective _ (MulAut.conj _).injective).symm hq
    have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)
    have hKsn : CFSG.Open.IsSubnormal (L.map (MulAut.conj g).toMonoidHom) M := by
      simpa only [hMg] using hL.map (MulAut.conj g).toMonoidHom
    have hsn := isSubnormal_barSub (V₀ := V₀) hV hKsn
    have hKX : barSub V₀ V hV (L.map (MulAut.conj g).toMonoidHom) ≤ barSub V₀ V hV X :=
      barSub_mono V₀ V hV
        (le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _ ⟨g, hgM, rfl⟩ le_rfl)
    have hsnX : CFSG.Open.IsSubnormal (barSub V₀ V hV (L.map (MulAut.conj g).toMonoidHom))
        (barSub V₀ V hV X) := by
      have := hsn.inf_of_le (barSub_mono V₀ V hV hXM)
      rwa [inf_eq_left.2 hKX] at this
    exact le_sSup ⟨hKX, hsnX, hqK⟩
  set E := rankThreeLayer (barSub V₀ V hV X) with hE
  have hXP : X ≤ (E.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype := by
    refine iSup₂_le fun K hK' => ?_
    intro k hk
    have hKM : K ≤ M := by
      obtain ⟨g, hgM, rfl⟩ := hK'
      exact le_trans
        (le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _ ⟨g, hgM, rfl⟩ le_rfl)
        hXM
    have hkS : k ∈ stabTil V₀ V := hMS (hKM hk)
    exact ⟨⟨k, hkS⟩, hK K hK' (actTil_mem_barSub V₀ V hV hk hkS), rfl⟩
  intro φ hφ
  obtain ⟨a, haX, rfl⟩ := (mem_barSub V₀ V hV X φ).1 hφ
  obtain ⟨b, hb, hba⟩ := hXP haX
  have hab : b = a := Subtype.ext hba
  subst hab
  exact hb

theorem ne_and_conjGenerated_of_hyp125 {D : Data G} (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) :
    V₀ ≠ V ∧ ConjGenerated D.M V₀ V := by
  obtain ⟨h0, -, -⟩ : InCalV0 D.M V₀ V ∧ CentralizersUnique D.M D.T ∧
      ∀ W : Subgroup G, ¬ InCalW D.M D.T W := by
    rcases h.1 with ⟨-, h0⟩ | h2
    · exact absurd h0 hV₀
    · exact h2
  obtain ⟨-, -, -, hTI₀, hTI, hgen, -⟩ := h0
  exact ⟨fun e => hTI (e ▸ hTI₀), fun v hv hv0 => (hgen v hv hv0).symm⟩

theorem xCond1218_conjClosure {D : Data G} (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥)
    {L : Subgroup G} (hL : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (j : ℕ) :
    XCond1218 D.M V₀ V h.isElemAbelian j (UC22.conjClosure D.M L) := by
  obtain ⟨hne, hirr⟩ := ne_and_conjGenerated_of_hyp125 h hV₀
  have hP := h.pairFacts
  exact Or.inl (rankThreeLayer_barSub_conjClosure h.isElemAbelian
    (le_stabTil hP.le_normalizer hP.le_normalizer₀) hL hLq
    (barSub_pCoreOf_eq_bot h.isElemAbelian hP.le hne hP.le_normalizer hP.le_normalizer₀ hirr))

theorem barSub_conjClosure_ne_bot (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hL1 : barSub V₀ V hV L ≠ ⊥) : barSub V₀ V hV (UC22.conjClosure M L) ≠ ⊥ := by
  exact fun h0 => hL1 (le_bot_iff.1 (h0 ▸ barSub_mono V₀ V hV (le_conjClosure M L)))

end TwelveTwentyThree

section Certified


theorem twelve_twentyThree_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {Δ : Finset (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H)) (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H) :
    mBar D.M V₀ V h.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + D.k + Δ.sum ι := by
  have h4 := twelve_twentyTwo_four D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀
    (TwelveTwentyThree.conjClosure_le hLM.le)
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
    (TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hL1) hΔ hΔU ι hι
    (TwelveTwentyThree.xCond1218_conjClosure h hV₀ hLM hLq _)
  omega

theorem twelve_twentyThree_three (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {Δ : Finset (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H)) (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) :
    mBar D.M V₀ V h.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + D.k + Δ.sup ι := by
  have h3 := twelve_twentyTwo_three D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀
    (TwelveTwentyThree.conjClosure_le hLM.le)
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
    (TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hL1) hΔ hΔU ι hι hO2
    (TwelveTwentyThree.xCond1218_conjClosure h hV₀ hLM hLq _)
  omega

theorem twelve_twentyThree_three_two (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {L : Subgroup G}
    (hLM : CFSG.Open.IsSubnormal L D.M) (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L))
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) {Δ : Finset (Subgroup G)}
    (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H))
    (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)
    (hmax : Δ.sup ι = 1) (hmk : D.k + 1 < mBar D.M V₀ V h.isElemAbelian) :
    mBar D.M V₀ V h.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + 1 := by
  exact twelve_twentyTwo_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h hV₀
    (TwelveTwentyThree.conjClosure_le hLM.le)
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
    (TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hL1) hΔ hΔU ι hι hO2 hmax
    (TwelveTwentyThree.xCond1218_conjClosure h hV₀ hLM hLq _) (by rw [hmax]; exact hmk)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
