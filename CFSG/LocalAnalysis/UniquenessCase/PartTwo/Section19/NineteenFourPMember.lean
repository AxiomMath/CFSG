module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.Quasithin.H13.L32NLem14325a
public import CFSG.RankThree.PartTwo.Sec6.Item68Tools
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Generic
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sup_tauOf_mem_calP19_4 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) {A J X : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hJ : JChoice19 D L K J) {q : ℕ} (hqp : q.Prime) (hq2 : q ≠ 2) (hX : Nat.card X = q)
    (hXJ : X ≤ J)
    (hτX : E1.tauOf (J ⊔ D.T) D.T A ≤
      normalizer ((X ⊔ pCoreOf 2 (J ⊔ D.T) : Subgroup G) : Set G))
    (ha : ∃ a ∈ A, ∃ x ∈ X, ⁅a, x⁆ ∉ pCoreOf 2 (J ⊔ D.T))
    (hq : q = 5 ∨ (q = 3 ∧ ∃ F : Subgroup G, (F = L ∨ F = K) ∧ X ≤ F ∧
      E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (F : Set G))) :
    X ⊔ E1.tauOf (J ⊔ D.T) D.T A ∈ calP19_4 D L K J A := by
  let H : Subgroup G := J ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  let τ : Subgroup G := E1.tauOf H D.T A
  let XQ : Subgroup G := X ⊔ Q
  let Y : Subgroup G := X ⊔ τ
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTtop : IsSylowIn 2 D.T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG
  have hTH : D.T ≤ H := by dsimp [H]; exact le_sup_right
  have hTsylH : IsSylowIn 2 D.T H := by
    refine ⟨hTH, hTtop.isPGroup, fun hd => hTtop.not_dvd_relIndex ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex D.T H ⊤ hTH le_top]
    exact Dvd.dvd.mul_right hd _
  have hQleH : Q ≤ H := by
    dsimp [Q]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQleT : Q ≤ D.T := by
    dsimp [Q]; exact E1.pCoreOf_two_le_of_isSylowIn hTsylH
  have hQ2 : IsPGroup 2 Q := by
    dsimp [Q]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) := by
    dsimp [Q]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hτleT : τ ≤ D.T := E1.tauOf_le H D.T A
  have hτleH : τ ≤ H := hτleT.trans hTH
  have hτ2 : IsPGroup 2 τ := hTtop.isPGroup.to_le hτleT
  have hτQ : τ ≤ Subgroup.normalizer (Q : Set G) := hτleH.trans hHnormQ
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hneV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV0 : InCalV D.M V₀ := S17.hyp125_inCalV h.hyp.hyp125 hneV0
  have hV0ab : IsElemAbelian 2 V₀ := hV0.2.2.2
  have hAab : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV0ab g)
  have hXp : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hX, pow_one])
  have hXne : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card X = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hX] at h1
    exact hqp.ne_one h1
  have hXQdisj : X ⊓ Q = ⊥ := E1.inf_eq_bot_of_isPGroup hqp hq2 hXp hQ2
  have hq2dvd : ¬ 2 ∣ q := by
    intro hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp hd).symm
  have hQτ : Q ≤ τ := le_sup_right.trans (E1.le_tauOf hTsylH hAT hAab)
  have hAτ : A ≤ τ := le_sup_left.trans (E1.le_tauOf hTsylH hAT hAab)
  have hQXQ : Q ≤ XQ := by dsimp [XQ]; exact le_sup_right
  have hXXQ : X ≤ XQ := by dsimp [XQ]; exact le_sup_left
  have hXQleH : XQ ≤ H := by
    dsimp [XQ]
    exact sup_le (hXJ.trans le_sup_left) hQleH
  have hXQnormQ : XQ ≤ Subgroup.normalizer (Q : Set G) := hXQleH.trans hHnormQ
  have hcardXQ : Nat.card XQ = q * Nat.card Q := by
    have hdisj : Disjoint Q X := disjoint_iff.mpr (by rwa [inf_comm] at hXQdisj)
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q X
      (hXXQ.trans hXQnormQ) hdisj
    rw [sup_comm, hX, mul_comm] at h
    dsimp [XQ]
    exact h
  have hQXQrel : Q.relIndex XQ = q := by
    have hmul := Subgroup.relIndex_mul_card Q XQ
    rw [inf_eq_left.mpr hQXQ, hcardXQ] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hQsylXQ : IsSylowIn 2 Q XQ := by
    refine ⟨hQXQ, hQ2, ?_⟩
    rw [hQXQrel]
    exact hq2dvd
  have hpc : (CFSG.pCore 2 ↥XQ : Subgroup ↥XQ) = Q.subgroupOf XQ := by
    apply le_antisymm
    · intro y hy
      have hy' : (y : G) ∈ pCoreOf 2 XQ := Subgroup.mem_map_of_mem XQ.subtype hy
      exact CFSG.ABGLocalTools.le_of_isPGroup_of_not_dvd_relIndex
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 XQ) (CFSG.LieType.BorelTits.pCoreOf_le 2 XQ)
        hQsylXQ.le hXQnormQ hQsylXQ.not_dvd_relIndex hy'
    · have hQsubn : (Q.subgroupOf XQ).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQXQ).mpr hXQnormQ
      have hQsubp : IsPGroup 2 (Q.subgroupOf XQ) :=
        hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQXQ).symm
      exact CFSG.LieType.BorelTits.le_pCore 2 hQsubn hQsubp
  let C : Subgroup G := CFSG.RankThree.PartTwo.Sec6.centralizerMod τ XQ Q hτX hτQ
  have hCτ : C ≤ τ := fun _ hc => hc.1
  have hC2 : IsPGroup 2 C := hτ2.to_le hCτ
  have hCnormτ : τ ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_normalizer_centralizerMod hτX hτQ
  have hQC : Q ≤ C := by
    intro q hq
    refine ⟨hQτ hq, fun x hx => ?_⟩
    have h1 : q * (x * q⁻¹ * x⁻¹) = q * x * q⁻¹ * x⁻¹ := by group
    rw [← h1]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQnormQ hx) q⁻¹).mp (Q.inv_mem hq))
  have hXleNC : X ≤ Subgroup.normalizer (C : Set G) := by
    have hconj : ∀ s ∈ X, ∀ c : G, c ∈ C → s * c * s⁻¹ ∈ C := by
      intro s hs c hc
      have hcomm : ⁅s, c⁆ ∈ C := by
        have h1 : ⁅s, c⁆ = ⁅c, s⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact hQC (Q.inv_mem (hc.2 s (hXXQ hs)))
      have h2 : s * c * s⁻¹ = ⁅s, c⁆ * c := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact C.mul_mem hcomm hc
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconj x hx c
    · intro hc
      have := hconj x⁻¹ (X.inv_mem hx) (x * c * x⁻¹) hc
      simpa [mul_assoc] using this
  have hQCle : Q ≤ C := hQC
  have hCnormP : X ⊔ C ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hXleNC Subgroup.le_normalizer
  have hcardP : Nat.card (X ⊔ C : Subgroup G) = q * Nat.card C := by
    have hdisj : Disjoint C X := disjoint_iff.mpr (by
      rw [inf_comm]
      refine le_antisymm (fun y hy => ?_) bot_le
      have hyX : y ∈ X := hy.1
      have hyC : y ∈ C := hy.2
      have hyXτ : y ∈ X ⊓ τ := ⟨hyX, hCτ hyC⟩
      rwa [E1.inf_eq_bot_of_isPGroup hqp hq2 hXp hτ2, Subgroup.mem_bot] at hyXτ)
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C X
      hXleNC hdisj
    rw [sup_comm, hX, mul_comm] at h
    exact h
  have hPrel : C.relIndex (X ⊔ C) = q := by
    have hmul := Subgroup.relIndex_mul_card C (X ⊔ C)
    rw [inf_eq_left.mpr le_sup_right, hcardP] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hCsubject : (C.subgroupOf (X ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hCnormP
  have hquotcard : Nat.card (↥(X ⊔ C) ⧸ C.subgroupOf (X ⊔ C)) = q := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf (X ⊔ C))
    have hcardCsub : Nat.card (C.subgroupOf (X ⊔ C)) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : C ≤ X ⊔ C)).toEquiv
    rw [hcardCsub, hcardP] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul.symm
  have hpow : ∀ x ∈ (X ⊔ C : Subgroup G), ∃ k : ℕ, x ^ q ^ k ∈ C := by
    intro x hx
    have hxq : (QuotientGroup.mk' (C.subgroupOf (X ⊔ C)) ⟨x, hx⟩) ^ q = 1 := by
      have h := pow_card_eq_one' (G := ↥(X ⊔ C) ⧸ C.subgroupOf (X ⊔ C))
        (x := QuotientGroup.mk' (C.subgroupOf (X ⊔ C)) ⟨x, hx⟩)
      rwa [hquotcard] at h
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hxq)
  have hτP : τ ≤ Subgroup.normalizer ((X ⊔ C : Subgroup G) : Set G) := by
    have hconj : ∀ s ∈ τ, ∀ y ∈ (X ⊔ C : Subgroup G), s * y * s⁻¹ ∈ X ⊔ C := by
      intro s hs y hy
      have hy' : (MulAut.conj s) y ∈ (X ⊔ C).map (MulAut.conj s).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      have hmap : (X ⊔ C).map (MulAut.conj s).toMonoidHom ≤ X ⊔ C := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro z ⟨x, hx, rfl⟩
          have hxXQ : x ∈ XQ := Subgroup.mem_sup_left hx
          have hmem : (MulAut.conj s) x ∈ XQ := by
            have := (Subgroup.mem_normalizer_iff.mp (hτX hs) x).mp hxXQ
            simpa [MulAut.conj_apply] using this
          exact (sup_le (le_sup_left : X ≤ X ⊔ C) (hQC.trans le_sup_right)) hmem
        · have hCmap : C.map (MulAut.conj s).toMonoidHom = C := by
            ext z
            constructor
            · rintro ⟨c, hc, rfl⟩
              have := (Subgroup.mem_normalizer_iff.mp (hCnormτ hs) c).mp hc
              simpa [MulAut.conj_apply] using this
            · intro hz
              refine ⟨s⁻¹ * z * s, ?_, ?_⟩
              · simpa using (Subgroup.mem_normalizer_iff.mp (hCnormτ (τ.inv_mem hs)) z).mp hz
              · simp [MulAut.conj_apply, mul_assoc]
          rw [hCmap]
          exact le_sup_right
      have hmem' : (MulAut.conj s) y ∈ X ⊔ C := hmap hy'
      simpa [MulAut.conj_apply] using hmem'
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj t ht y
    · intro hy
      have := hconj t⁻¹ (τ.inv_mem ht) (t * y * t⁻¹) hy
      simpa [mul_assoc] using this
  have hcommA : (X ⊔ C : Subgroup G) ≤ ⁅X ⊔ C, A⁆ ⊔ C := by
    obtain ⟨a₀, ha₀A, x₀, hx₀X, hcomm₀⟩ := ha
    have hAXleXQ : ⁅A, X⁆ ≤ XQ := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have h1 : a * x * a⁻¹ ∈ XQ :=
        (Subgroup.mem_normalizer_iff.mp (hτX (hAτ ha)) x).mp (Subgroup.mem_sup_left hx)
      have h2 : x⁻¹ ∈ XQ := XQ.inv_mem (Subgroup.mem_sup_left hx)
      have h3 : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := rfl
      rw [h3]
      exact XQ.mul_mem h1 h2
    have hAXsupQ : ⁅A, X⁆ ⊔ Q = XQ := by
      apply le_antisymm
      · exact sup_le hAXleXQ hQXQ
      · have hle : ⁅A, X⁆ ⊔ Q ≤ XQ := sup_le hAXleXQ hQXQ
        have hqrel := Subgroup.relIndex_mul_relIndex Q (⁅A, X⁆ ⊔ Q) XQ le_sup_right hle
        rw [hQXQrel] at hqrel
        have hne1 : Q.relIndex (⁅A, X⁆ ⊔ Q) ≠ 1 := by
          intro h1
          have hleQ : ⁅A, X⁆ ⊔ Q ≤ Q := Subgroup.relIndex_eq_one.mp h1
          exact hcomm₀ (hleQ (Subgroup.mem_sup_left
            (Subgroup.commutator_mem_commutator ha₀A hx₀X)))
        rcases (Nat.dvd_prime hqp).mp ⟨_, hqrel.symm⟩ with h1 | hq
        · exact absurd h1 hne1
        · have hrelL : (⁅A, X⁆ ⊔ Q).relIndex XQ = 1 := by
            rw [hq] at hqrel
            exact Nat.eq_of_mul_eq_mul_left hqp.pos (by simpa using hqrel)
          exact Subgroup.relIndex_eq_one.mp hrelL
    have hXQleR : XQ ≤ ⁅X ⊔ C, A⁆ ⊔ C := by
      rw [← hAXsupQ]
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono (le_sup_left : X ≤ X ⊔ C) le_rfl).trans le_sup_left
      · exact hQC.trans le_sup_right
    exact sup_le ((le_sup_left : X ≤ XQ).trans hXQleR) le_sup_right
  have hCrelA : C.relIndex A = 2 := by
    obtain ⟨a₀, ha₀A, x₀, hx₀X, hcomm₀⟩ := ha
    have hA_le_NXQ : A ≤ Subgroup.normalizer ((XQ : Subgroup G) : Set G) := hAτ.trans hτX
    let φ : ↥A →* MulAut ↥XQ :=
      (Subgroup.normalizerMonoidHom XQ).comp (Subgroup.inclusion hA_le_NXQ)
    let Qbar := ↥XQ ⧸ CFSG.pCore 2 ↥XQ
    let ρ : ↥A →* MulAut Qbar := (CFSG.pCoreQuotMulAut ↥XQ).comp φ
    have hquotcard : Nat.card Qbar = q := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥XQ)
      rw [hpc] at hmul
      have hcardQsub : Nat.card (Q.subgroupOf XQ) = Nat.card Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQXQ).toEquiv
      rw [hcardQsub, hcardXQ] at hmul
      have hquot : Nat.card (↥XQ ⧸ Q.subgroupOf XQ) = q :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul.symm
      dsimp [Qbar]
      rw [hpc]
      exact hquot
    have : Fact q.Prime := ⟨hqp⟩
    have : IsCyclic Qbar := isCyclic_of_prime_card hquotcard
    have hZ : IsCyclic (ZMod (Nat.card Qbar))ˣ := by
      rw [hquotcard]
      exact ZMod.isCyclic_units_prime hqp
    have : IsCyclic (MulAut Qbar) := (IsCyclic.mulAutMulEquiv Qbar).isCyclic.mpr hZ
    have hker : ρ.ker = C.subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro ha1
        refine ⟨hAτ a.2, fun x hx => ?_⟩
        show ⁅(a : G), x⁆ ∈ Q
        let y : ↥XQ := ⟨x, hx⟩
        have hfix : (ρ a) (QuotientGroup.mk y : Qbar) = (QuotientGroup.mk y : Qbar) := by
          rw [ha1, MulAut.one_apply]
        have hcomp : (ρ a) (QuotientGroup.mk y : Qbar) =
            (QuotientGroup.mk (φ a y) : Qbar) := by
          simpa [ρ] using CFSG.pCoreQuotMulAut_mk (φ a) y
        have h2 : (QuotientGroup.mk (φ a y) : Qbar) = (QuotientGroup.mk y : Qbar) := by
          rw [← hcomp, hfix]
        have hmem : (φ a y)⁻¹ * y ∈ CFSG.pCore 2 ↥XQ :=
          (QuotientGroup.eq (s := CFSG.pCore 2 ↥XQ)).mp h2
        rw [hpc] at hmem
        have hk : ((φ a y)⁻¹ * y : ↥XQ).val ∈ Q := Subgroup.mem_subgroupOf.mp hmem
        have hk' : (a : G) * x⁻¹ * (a : G)⁻¹ * x ∈ Q := by
          simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
            mul_assoc] using hk
        let k : G := (a : G) * x⁻¹ * (a : G)⁻¹ * x
        have hkQ : k ∈ Q := hk'
        have h1 : (a : G) * x * (a : G)⁻¹ = x * k⁻¹ := by
          have hk1 : (a : G) * x⁻¹ * (a : G)⁻¹ = k * x⁻¹ := by
            calc (a : G) * x⁻¹ * (a : G)⁻¹
                = ((a : G) * x⁻¹ * (a : G)⁻¹ * x) * x⁻¹ := by group
              _ = k * x⁻¹ := by rw [show k = (a : G) * x⁻¹ * (a : G)⁻¹ * x from rfl]
          calc (a : G) * x * (a : G)⁻¹ = ((a : G) * x⁻¹ * (a : G)⁻¹)⁻¹ := by group
            _ = (k * x⁻¹)⁻¹ := by rw [hk1]
            _ = x * k⁻¹ := by group
        have hcommax : ⁅(a : G), x⁆ = x * k⁻¹ * x⁻¹ := by
          simp only [commutatorElement_def]
          rw [h1]
        rw [hcommax]
        exact (Subgroup.mem_normalizer_iff.mp (hXQnormQ hx) k⁻¹).mp (Q.inv_mem hkQ)
      · intro hc
        have hcommXQ : ∀ z ∈ XQ, ⁅(a : G), z⁆ ∈ Q := hc.2
        ext z
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective z
        show (ρ a) (QuotientGroup.mk u : Qbar) = (QuotientGroup.mk u : Qbar)
        have hcomp : (ρ a) (QuotientGroup.mk u : Qbar) =
            (QuotientGroup.mk (φ a u) : Qbar) := by
          simpa [ρ] using CFSG.pCoreQuotMulAut_mk (φ a) u
        rw [hcomp, QuotientGroup.eq (s := CFSG.pCore 2 ↥XQ), hpc]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have hu : (a : G) * u.val * (a : G)⁻¹ * u.val⁻¹ ∈ Q := hcommXQ u.val u.2
        have hk : (a : G) * u.val⁻¹ * (a : G)⁻¹ * u.val ∈ Q := by
          have h1 : (a : G) * u.val * (a : G)⁻¹ = ⁅(a : G), u.val⁆ * u.val := by
            simp only [commutatorElement_def]
            group
          have h2 : (a : G) * u.val⁻¹ * (a : G)⁻¹ = u.val⁻¹ * ⁅(a : G), u.val⁆⁻¹ := by
            calc (a : G) * u.val⁻¹ * (a : G)⁻¹
                = ((a : G) * u.val * (a : G)⁻¹)⁻¹ := by group
              _ = (⁅(a : G), u.val⁆ * u.val)⁻¹ := by rw [h1]
              _ = u.val⁻¹ * ⁅(a : G), u.val⁆⁻¹ := by group
          have h3 : (a : G) * u.val⁻¹ * (a : G)⁻¹ * u.val
              = u.val⁻¹ * ⁅(a : G), u.val⁆⁻¹ * u.val := by
            rw [h2]
          rw [h3]
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXQnormQ u.2))
            (⁅(a : G), u.val⁆⁻¹)).mp (Q.inv_mem hu)
        simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
          mul_assoc] using hk
    have hrange_sq : ∀ x ∈ ρ.range, x * x = 1 := by
      rintro x ⟨a, rfl⟩
      have ha2 : (a : ↥A) * (a : ↥A) = 1 := by
        apply Subtype.ext
        show (a : G) * (a : G) = 1
        rw [← pow_two]
        exact hAab.2 a a.2
      calc ρ a * ρ a = ρ (a * a) := (map_mul ρ a a).symm
        _ = ρ 1 := by rw [ha2]
        _ = 1 := map_one ρ
    have hcard_range : Nat.card ρ.range ≤ 2 :=
      CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.card_le_two_of_cyclic_sq
        ρ.range hrange_sq
    have hrange_gt : 1 < Nat.card ρ.range := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      have hmem : ρ ⟨a₀, ha₀A⟩ ∈ ρ.range := ⟨_, rfl⟩
      have h1 : ρ ⟨a₀, ha₀A⟩ = 1 := by
        have hmem' : ρ ⟨a₀, ha₀A⟩ ∈ (⊥ : Subgroup (MulAut Qbar)) := hbot ▸ hmem
        simpa using hmem'
      have h2 : (⟨a₀, ha₀A⟩ : ↥A) ∈ ρ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact hcomm₀ (h2.2 x₀ (hXXQ hx₀X))
    have hcard_two : Nat.card ρ.range = 2 := by omega
    have hrel : C.relIndex A = Nat.card ρ.range := by
      rw [← Subgroup.index_ker ρ, hker]
      rfl
    rw [hrel, hcard_two]
  have hEamb : E1.EOneAmb (X ⊔ τ) A := by
    have h := CFSG.LocalAnalysis.WeakClosure81.eOneAmb_sup_mod hqp hq2
      (O := C) (P₀ := X ⊔ C) (τ := τ) hC2 le_sup_right hCnormP hCnormτ hpow hτ2 hτP (by
        intro hle
        have hXle : X ≤ C := le_sup_left.trans hle
        have hXτ : X ≤ τ := hXle.trans hCτ
        have hXbot : X = ⊥ := by
          have h1 : X ≤ ⊥ := by
            rw [← E1.inf_eq_bot_of_isPGroup hqp hq2 hXp hτ2]
            exact le_inf le_rfl hXτ
          exact le_bot_iff.mp h1
        exact hXne hXbot) hAτ hcommA hCrelA
    rwa [show (X ⊔ C) ⊔ τ = X ⊔ τ by rw [sup_assoc, sup_eq_right.mpr hCτ]] at h
  have hAY : A ≤ Y := by dsimp [Y]; exact hAτ.trans le_sup_right
  have hEone : E1.EOne ↥Y (A.subgroupOf Y) := E1.eOne_of_eOneAmb hAY hEamb
  have hEcard : Nat.card (E1.barO2 ↥Y (A.subgroupOf Y)) ≤ 2 ^ 1 := by
    obtain ⟨-, -, -, -, -, -, hcard⟩ := hEone
    rw [hcard]
    norm_num
  have hcardY : Nat.card Y = q * Nat.card τ := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := τ) (K := XQ) hτX
    have hinf : τ ⊓ XQ = Q := by
      apply le_antisymm
      · exact CFSG.ABGLocalTools.le_of_isPGroup_of_not_dvd_relIndex (hτ2.to_le inf_le_left)
          inf_le_right hQsylXQ.le hXQnormQ hQsylXQ.not_dvd_relIndex
      · exact le_inf hQτ hQXQ
    have hsup : τ ⊔ XQ = Y := by
      dsimp [Y, XQ]
      rw [← sup_assoc, sup_comm τ X, sup_assoc, sup_eq_left.mpr hQτ]
    rw [hinf, hsup, hcardXQ] at h
    have h' : Nat.card Y * Nat.card Q = (q * Nat.card τ) * Nat.card Q := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hτrelY : τ.relIndex Y = q := by
    have hmul := Subgroup.relIndex_mul_card τ Y
    rw [inf_eq_left.mpr (le_sup_right : τ ≤ Y), hcardY] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hτsylY : IsSylowIn 2 τ Y := by
    refine ⟨le_sup_right, hτ2, ?_⟩
    rw [hτrelY]
    exact hq2dvd
  have hTYsyl : IsSylowIn 2 (D.T ⊓ Y) Y := by
    refine ⟨inf_le_right, hTtop.isPGroup.to_le inf_le_left, ?_⟩
    have hle : τ ≤ D.T ⊓ Y := le_inf hτleT le_sup_right
    have hdvd : (D.T ⊓ Y).relIndex Y ∣ τ.relIndex Y :=
      Subgroup.relIndex_dvd_of_le_left Y hle
    rw [hτrelY] at hdvd
    intro h2
    exact hq2dvd (h2.trans hdvd)
  have hτne : τ ≠ ⊥ := by
    obtain ⟨a₀, ha₀, x₀, hx₀, hcomm⟩ := ha
    have ha₀ne : a₀ ≠ 1 := by
      intro h1
      apply hcomm
      rw [h1]
      simp
    intro hbot
    have : a₀ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hAτ ha₀
    exact ha₀ne (Subgroup.mem_bot.mp this)
  obtain ⟨k, hτcard⟩ := hτ2.exists_card_eq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, pow_zero] at hτcard
      exact absurd (Subgroup.card_eq_one.mp hτcard) hτne
    · exact hk
  have hprimefac : (Nat.card Y).primeFactors = {2, q} := by
    rw [hcardY, hτcard,
      Nat.primeFactors_mul hqp.ne_zero (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)),
      hqp.primeFactors, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
    ext r
    simp [eq_comm, or_comm]
  have hqcase : q = 5 ∨ (q = 3 ∧ (Opp 3 Y ≤ L ∨ Opp 3 Y ≤ K)) := by
    rcases hq with h5 | ⟨h3, F, hF, hXF, hτF⟩
    · exact Or.inl h5
    · right
      refine ⟨h3, ?_⟩
      have hYF : Y ≤ Subgroup.normalizer (F : Set G) := by
        dsimp [Y]
        exact sup_le (hXF.trans Subgroup.le_normalizer) hτF
      have hFY : (Y ⊓ F).relIndex Y = (τ ⊓ F).relIndex τ := by
        have h1 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
          (H := Y) (K := F) hYF).2
        have h2 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
          (H := τ) (K := F) hτF).2
        have hsup : Y ⊔ F = τ ⊔ F := by
          dsimp [Y]
          rw [sup_assoc, sup_eq_right.mpr (hXF.trans le_sup_right)]
        rw [hsup] at h1
        exact h1.symm.trans h2
      have hnot3 : ¬ 3 ∣ (Y ⊓ F).relIndex Y := by
        rw [hFY]
        intro h3dvd
        have hdvd : (τ ⊓ F).relIndex τ ∣ Nat.card τ :=
          Subgroup.relIndex_dvd_card (τ ⊓ F) τ
        rw [hτcard] at hdvd
        exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3dvd.trans hdvd)) (by norm_num)
      have hconj : ∀ s ∈ Y, ∀ z ∈ (Y ⊓ F : Subgroup G), s * z * s⁻¹ ∈ Y ⊓ F := by
        intro s hs z hz
        obtain ⟨hzY, hzF⟩ := Subgroup.mem_inf.mp hz
        exact ⟨Y.mul_mem (Y.mul_mem hs hzY) (Y.inv_mem hs),
          (Subgroup.mem_normalizer_iff.mp (hYF hs) z).mp hzF⟩
      have hNnorm : Y ≤ Subgroup.normalizer ((Y ⊓ F : Subgroup G) : Set G) := by
        intro y hy
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · exact hconj y hy z
        · intro hz
          have := hconj y⁻¹ (Y.inv_mem hy) (y * z * y⁻¹) hz
          simpa [mul_assoc] using this
      have hNFnormal : ((Y ⊓ F).subgroupOf Y).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : Y ⊓ F ≤ Y)).mpr hNnorm
      have hOppF : Opp 3 Y ≤ F := by
        refine (Subgroup.closure_le F).mpr ?_
        rintro x ⟨hxY, k, hk⟩
        refine (CFSG.Quasithin.H13.L14325.mem_of_normal_of_not_dvd_relIndex hNFnormal
          Nat.prime_three hnot3 hxY (k := k) ?_).2
        rw [← hk]
        exact pow_orderOf_eq_one x
      rcases hF with hFL | hFK
      · exact Or.inl (hFL ▸ hOppF)
      · exact Or.inr (hFK ▸ hOppF)
  have hYH : Y ≤ H := by
    dsimp [Y]
    exact sup_le (hXJ.trans le_sup_left) hτleH
  have hIsE : E1.IsE 1 H D.T A Y :=
    ⟨hYH, le_inf hτleT le_sup_right, hTYsyl, Or.inl ⟨hEone, hEcard⟩⟩
  exact ⟨by simpa [H] using hIsE, q, hqp, hq2, hprimefac, hqcase⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
