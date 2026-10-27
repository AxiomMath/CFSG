module

public import CFSG.LocalAnalysis.StandardType.GGKGTwTheta

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem map_conj_eq {M N : Type} [Group M] [Group N] (φ : M →* N) (x y : M) :
    φ (MulAut.conj x y) = MulAut.conj (φ x) (φ y) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem mulEquiv_conj_apply {M N : Type} [Group M] [Group N] (e : M ≃* N) (x y : M) :
    e (MulAut.conj x y) = MulAut.conj (e x) (e y) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem conj_mem_normalizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')} [Finite A]
    (m : L') (h : ∀ a : A, ∃ b : A,
      MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ = (b : MulAut L')) :
    MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  let c : MulAut L' := MulAut.conj m
  rw [Subgroup.mem_set_normalizer_iff]
  intro v
  constructor
  · intro hv
    obtain ⟨b, hb⟩ := h ⟨v, hv⟩
    rw [hb]
    exact b.2
  · intro hv
    have hmaple : A.map (MulAut.conj c).toMonoidHom ≤ A := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨b, hb⟩ := h ⟨w, hw⟩
      rw [show (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ from MulAut.conj_apply c w, hb]
      exact b.2
    have hcard : Nat.card (A.map (MulAut.conj c).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hEq : A.map (MulAut.conj c).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)
    have hmem : (MulAut.conj c).toMonoidHom v ∈ A.map (MulAut.conj c).toMonoidHom := by
      rw [hEq]
      exact hv
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 hmem
    have huv' : u = v := (MulAut.conj c).injective huv
    rwa [← huv']


private theorem tw_conjAut_apply {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {R : Type} [Group R] {Θ : R ≃* ↥(twistedE6RootGroup K σ)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ 3 = 1} {L' : Type} [Group L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) {l₀ : L'}
    {j : ↥(twistedE6RootGroup K σ)} (hl₀ : Θ (ψ l₀) = j) (a' : A) (l : L') :
    ((Θ (ψ ((MulAut.conj l₀ * (a' : MulAut L') * (MulAut.conj l₀)⁻¹) l)) :
        ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      (((j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
          (j : ModGL TwistTag.E6.tag K)⁻¹) *
        ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        ((j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
          (j : ModGL TwistTag.E6.tag K)⁻¹)⁻¹) := by
  have harg : (MulAut.conj l₀ * (a' : MulAut L') * (MulAut.conj l₀)⁻¹) l =
      MulAut.conj l₀ ((a' : MulAut L') ((MulAut.conj l₀)⁻¹ l)) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
  have hinv : (MulAut.conj l₀)⁻¹ = MulAut.conj l₀⁻¹ := by
    ext y
    rw [MulAut.conj_inv_apply, MulAut.conj_apply, inv_inv]
  have hw : ((Θ (ψ ((MulAut.conj l₀)⁻¹ l)) : ↥(twistedE6RootGroup K σ)) :
        ModGL TwistTag.E6.tag K) =
      (j : ModGL TwistTag.E6.tag K)⁻¹ *
        ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        (j : ModGL TwistTag.E6.tag K) := by
    rw [hinv, MulAut.conj_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hl₀]
    group
  rw [harg, map_conj_eq ψ, mulEquiv_conj_apply Θ]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hl₀]
  rw [hF.conj a' ((MulAut.conj l₀)⁻¹ l), hw]
  group

theorem kgL1_clause_tw (hCore : TwE6RootAs.TwE6CorootCore) {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {R : Type} [Group R] {Θ : R ≃* ↥(twistedE6RootGroup K σ)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) :
    ∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c →
      ∃ E : Subgroup R, GGLayerOf (ggRFix ψ {(c : MulAut L')}) E := by
  intro c hc
  obtain ⟨β, hβroot, hβ⟩ := hF.aut.corootPt hc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hne : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  have hbase : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (t (Multiplicative.toAdd (κ c))) * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple β ζ) := by
    rw [KGTwFrame.t_coroot hF, hβ, ← corootTuple_eq_zetaVec_kg ζ hζ β]
  obtain ⟨X, D, hCent, hXcyc, -, hXD, hDq, -, -, -, -⟩ :=
    hCore K σ (2 ^ n) hK hσ hchar 3 Nat.prime_three h3 Fr hF.hFr v hF.hv g hF.hg hF.hgF
      (t (Multiplicative.toAdd (κ c))) (hF.ht _).1 β hβroot ζ hζ hne hbase
  have hLayer : GGLayerOf ((Subgroup.centralizer
      ({t (Multiplicative.toAdd (κ c))} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
      (twistedE6RootGroup K σ)) D := by
    have h := ggLayerOf_sup_of_cyclic hXcyc hXD hDq
    rwa [← hCent] at h
  refine ⟨D.comap Θ.toMonoidHom, ?_⟩
  refine layer_of_centralizer_tw Θ ψ hψ {(c : MulAut L')}
    ({t (Multiplicative.toAdd (κ c))} : Set (ModGL TwistTag.E6.tag K)) ?_ ?_ hLayer
  · rintro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨t (Multiplicative.toAdd (κ c)), rfl, fun l => hF.conj c l⟩
  · rintro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exact ⟨(c : MulAut L'), rfl, fun l => hF.conj c l⟩

theorem kgD4_clause_tw (hD4 : GGTwE6D4LayerInput) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {R : Type} [Group R] {Θ : R ≃* ↥(twistedE6RootGroup K σ)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) {a b : ↥A}
    (hab : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∃ Ev : Subgroup R, GGLayerOf (ggRFix ψ {(a : MulAut L') * (b : MulAut L')}) Ev ∧
      ∃ l : L', ψ l ∈ Ev ∧ MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ ≠ (a : MulAut L') := by
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.aut.corootOrth hab
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hne : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  set ta : ModGL TwistTag.E6.tag K := t (Multiplicative.toAdd (κ a)) with hta
  set tt : ModGL TwistTag.E6.tag K := t (Multiplicative.toAdd (κ (a * b))) with htt
  have htamem : ta ∈ twistedE6InndiagGL K σ := by
    rw [hta]; exact (hF.ht _).1
  have httmem : tt ∈ twistedE6InndiagGL K σ := by
    rw [htt]; exact (hF.ht _).1
  have hkey : (Multiplicative.toAdd (κ (a * b)) : Fin Tag.E6.rank → ZMod 3) =
      (kgExpVec α + kgExpVec β : Fin Tag.E6.rank → ZMod 3) := by
    rw [kgKappa_toAdd_mul (K := K) κ a b, ha, hb]
    rfl
  have h1 : zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ (a * b))) =
      zetaVec (τ := Tag.E6) ζ hζ (kgExpVec α + kgExpVec β) :=
    congrArg (zetaVec (τ := Tag.E6) ζ hζ) hkey
  have hzeta : TwE6RootAs.corootTuple α ζ * TwE6RootAs.corootTuple β ζ =
      zetaVec (τ := Tag.E6) ζ hζ (kgExpVec α) * zetaVec (τ := Tag.E6) ζ hζ (kgExpVec β) := by
    rw [corootTuple_eq_zetaVec_kg ζ hζ α, corootTuple_eq_zetaVec_kg ζ hζ β]
    rfl
  have hbase_tt : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) tt * g =
      rootDiagUnit TwistTag.E6.tag
        (TwE6RootAs.corootTuple α ζ * TwE6RootAs.corootTuple β ζ) := by
    rw [htt, KGTwFrame.t_coroot hF]
    exact congrArg (rootDiagUnit TwistTag.E6.tag)
      (h1.trans ((kgZetaE6_add ζ hζ (kgExpVec α) (kgExpVec β)).trans hzeta.symm))
  have hbase_ta : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ta * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) := by
    rw [hta, KGTwFrame.t_coroot hF, ha]
    exact congrArg (rootDiagUnit TwistTag.E6.tag) (corootTuple_eq_zetaVec_kg ζ hζ α).symm
  obtain ⟨E, hE, j, hjE, hjV, hjta⟩ :=
    hD4 n hn h3 K σ hK hσ Fr hF.hFr v hF.hv g hF.hg hF.hgF α β hα hβ hαβ ζ hζ hne
      tt httmem ta htamem hbase_tt hbase_ta
  have hEv : GGLayerOf (ggRFix ψ {(a : MulAut L') * (b : MulAut L')})
      (E.comap Θ.toMonoidHom) := by
    refine layer_of_centralizer_tw Θ ψ hψ {(a : MulAut L') * (b : MulAut L')}
      ({tt} : Set (ModGL TwistTag.E6.tag K)) ?_ ?_ hE
    · rintro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      refine ⟨tt, rfl, fun l => ?_⟩
      rw [← Subgroup.coe_mul]
      exact hF.conj (a * b) l
    · rintro d hd
      rw [Set.mem_singleton_iff] at hd
      subst hd
      refine ⟨(a : MulAut L') * (b : MulAut L'), rfl, fun l => ?_⟩
      rw [← Subgroup.coe_mul]
      exact hF.conj (a * b) l
  obtain ⟨l₀, hl₀ψ⟩ := hψ (Θ.symm j)
  have hl₀ : Θ (ψ l₀) = j := by rw [hl₀ψ, MulEquiv.apply_symm_apply]
  have hexists : ∀ a' : A, ∃ b' : A,
      MulAut.conj l₀ * (a' : MulAut L') * (MulAut.conj l₀)⁻¹ = (b' : MulAut L') := by
    intro a'
    have hx'hyp : Multiplicative.toAdd (κ a') ∈ hypE6 := hF.aut.toAdd_mem_hypE6 a'
    obtain ⟨y, hy, hVy⟩ := hjV (Multiplicative.toAdd (κ a')) hx'hyp
    have h1 := hVy (t (Multiplicative.toAdd (κ a'))) (hF.ht _).1
      (KGTwFrame.t_coroot hF (Multiplicative.toAdd (κ a')))
    have h2 := KGTwFrame.t_coroot hF y
    have hEq : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
          (j : ModGL TwistTag.E6.tag K)⁻¹) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (t y) :=
      mul_left_cancel (mul_right_cancel (h1.trans h2.symm))
    have hjt : (j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
        (j : ModGL TwistTag.E6.tag K)⁻¹ = t y :=
      baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hEq
    obtain ⟨b', hb'⟩ := hF.aut.exists_of_mem_hypE6 hy
    refine ⟨b', ?_⟩
    refine mulAut_eq_of_comp_eq ψ hker hperf (fun l => ?_)
    apply Θ.injective
    apply Subtype.ext
    rw [tw_conjAut_apply hF hl₀ a' l, hF.conj b' l, hb']
    rw [← hjt]
  refine ⟨E.comap Θ.toMonoidHom, hEv, l₀, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    change Θ (ψ l₀) ∈ E
    rw [hl₀]
    exact hjE
  · haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hF.aut.card_eq]; norm_num)
    exact conj_mem_normalizer l₀ hexists
  · intro hcontra
    let m1 : ModGL TwistTag.E6.tag K :=
      (j : ModGL TwistTag.E6.tag K) * ta * (j : ModGL TwistTag.E6.tag K)⁻¹
    have hm1mem : m1 ∈ twistedE6InndiagGL K σ :=
      mul_mem (mul_mem (Subgroup.mem_sup_left j.2) htamem) (inv_mem (Subgroup.mem_sup_left j.2))
    have hconjEq : twistedE6InndiagConj K σ ⟨m1, hm1mem⟩ =
        twistedE6InndiagConj K σ ⟨ta, htamem⟩ := by
      refine MulEquiv.ext (fun c => ?_)
      refine Subtype.ext ?_
      rw [twistedE6InndiagConj_apply, twistedE6InndiagConj_apply]
      obtain ⟨l, hl⟩ := hψ (Θ.symm c)
      have hΘl : Θ (ψ l) = c := by rw [hl, MulEquiv.apply_symm_apply]
      have hL := tw_conjAut_apply hF hl₀ a l
      have hR := hF.conj a l
      rw [hΘl] at hL hR
      have harg : (MulAut.conj l₀ * (a : MulAut L') * (MulAut.conj l₀)⁻¹) l =
          (a : MulAut L') l := by rw [hcontra]
      have key : ((Θ (ψ ((MulAut.conj l₀ * (a : MulAut L') * (MulAut.conj l₀)⁻¹) l)) :
          ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          ((Θ (ψ ((a : MulAut L') l)) : ↥(twistedE6RootGroup K σ)) :
            ModGL TwistTag.E6.tag K) := by rw [harg]
      exact hL.symm.trans (key.trans hR)
    have hm1eq : (j : ModGL TwistTag.E6.tag K) * ta * (j : ModGL TwistTag.E6.tag K)⁻¹ = ta :=
      Subtype.ext_iff.mp (twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ hconjEq)
    exact hjta hm1eq

end CFSG.StandardType.KGL

end
