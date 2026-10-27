module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Cover
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Noncentral
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts2
import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem quotient_center_equiv_and_minimal {Y K : Type} [Group Y] [Finite Y] [Group K]
    [Finite K] (P : Subgroup Y) [hPN : P.Normal] (e : Y ⧸ P ≃* K)
    (hKperf : Group.IsPerfect K) (f : Y →* K) (hf : Function.Surjective f)
    (hf_eq : f = e.toMonoidHom.comp (QuotientGroup.mk' P))
    (Q : Subgroup Y) [hQN : Q.Normal]
    (hQdef : Q = (Subgroup.center K).comap f)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) :
    Nonempty (Y ⧸ Q ≃* K ⧸ Subgroup.center K) ∧
      (∀ M : Subgroup Y, M.map (QuotientGroup.mk' Q) = ⊤ → M = ⊤) := by
  classical
  let φ : Y →* K ⧸ Subgroup.center K :=
    (QuotientGroup.mk' (Subgroup.center K)).comp f
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (Subgroup.center K)).comp hf
  have hφker : φ.ker = Q := by
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' (Subgroup.center K)) f,
      QuotientGroup.ker_mk', ← hQdef]
  let eQ : Y ⧸ Q ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hQmapφ : ∀ x : Y, eQ (QuotientGroup.mk' Q x) = φ x := by
    intro x
    rfl
  have hminQ : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' Q) = ⊤ → M = ⊤ := by
    intro M hM
    have hMφ : M.map φ = ⊤ := by
      have h1 : M.map (eQ.toMonoidHom.comp (QuotientGroup.mk' Q)) = ⊤ := by
        rw [← Subgroup.map_map, hM, Subgroup.map_top_of_surjective _ eQ.surjective]
      rwa [show eQ.toMonoidHom.comp (QuotientGroup.mk' Q) = φ from
        MonoidHom.ext hQmapφ] at h1
    have hMcenter : (M.map f).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
      have h2 : M.map φ = (M.map f).map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [← Subgroup.map_map]
      rwa [← h2]
    have hMf : M.map f = ⊤ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts2.eq_top_of_map_center_eq_top
        (Group.isPerfect_def.mp hKperf) (M := M.map f) hMcenter
    have hMf' : M.map (e.toMonoidHom.comp (QuotientGroup.mk' P)) = ⊤ := by
      rw [← hf_eq]
      exact hMf
    have hMP : M.map (QuotientGroup.mk' P) = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective]
      exact hMf'
    exact hmin M hMP
  exact ⟨⟨eQ⟩, hminQ⟩

theorem exists_central_preimage_minimal_cover {Y K : Type} [Group Y] [Finite Y] [Group K]
    [Finite K] {p : ℕ} (P : Subgroup Y) [hPN : P.Normal] (hP : IsPGroup p P)
    (e : Y ⧸ P ≃* K) (hKperf : Group.IsPerfect K)
    (hZp : IsPGroup p (Subgroup.center K)) (hZn : Subgroup.center K ≠ ⊥)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) :
    ∃ (Q : Subgroup Y) (_ : Q.Normal), P ≤ Q ∧ IsPGroup p Q ∧ Q ≠ ⊥ ∧
      Nonempty (Y ⧸ Q ≃* K ⧸ Subgroup.center K) ∧
      (∀ M : Subgroup Y, M.map (QuotientGroup.mk' Q) = ⊤ → M = ⊤) := by
  classical
  let f : Y →* K := e.toMonoidHom.comp (QuotientGroup.mk' P)
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective P)
  let Q : Subgroup Y := (Subgroup.center K).comap f
  have hQnormal : Q.Normal :=
    Subgroup.Normal.comap (inferInstance : (Subgroup.center K).Normal) f
  have hPQ : P ≤ Q := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' P x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [MonoidHom.comp_apply, hx1, map_one]
    exact Subgroup.one_mem _
  have hfker : f.ker = P := by
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' P) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hQp : IsPGroup p Q := by
    have h := IsPGroup.comap_of_ker_isPGroup (p := p) hZp f (by rw [hfker]; exact hP)
    simpa [Q] using h
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hmapQ : Q.map f = Subgroup.center K := by
      rw [show Q = (Subgroup.center K).comap f from rfl,
        Subgroup.map_comap_eq_self_of_surjective hf]
    rw [hbot, Subgroup.map_bot] at hmapQ
    exact hZn hmapQ.symm
  have hQdef : Q = (Subgroup.center K).comap f := rfl
  obtain ⟨⟨eQ⟩, hminQ⟩ :=
    @quotient_center_equiv_and_minimal Y K _ _ _ _ P hPN e hKperf f hf rfl Q
      hQnormal hQdef hmin
  exact ⟨Q, hQnormal, hPQ, hQp, hQne, ⟨eQ⟩, hminQ⟩

theorem false_of_center_preimage_le_center
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {Y K : Type} [Group Y] [Finite Y] [Group K] [Finite K]
    (hKY : CFSG.Open.IsKGroup Y) (hYperf : Group.IsPerfect Y)
    (Q : Subgroup Y) [hQN : Q.Normal] (hQp : IsPGroup p Q) (hQne : Q ≠ ⊥)
    [hS : IsSimpleGroup (Y ⧸ Q)] (hQle : Q ≤ Subgroup.center Y)
    (hrkY : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) : False := by
  have hcenterY : Subgroup.center Y = Q := by
    have hmapcenter : (Subgroup.center Y).map (QuotientGroup.mk' Q) = ⊥ := by
      have hnorm : ((Subgroup.center Y).map (QuotientGroup.mk' Q)).Normal :=
        (inferInstance : (Subgroup.center Y).Normal).map _
          (QuotientGroup.mk'_surjective Q)
      rcases @Subgroup.Normal.eq_bot_or_eq_top (Y ⧸ Q) _ hS
        ((Subgroup.center Y).map (QuotientGroup.mk' Q)) hnorm with h | h
      · exact h
      · exfalso
        have htop : Subgroup.center (Y ⧸ Q) = ⊤ :=
          top_unique (h ▸ Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Q))
        have hcomm : IsMulCommutative (Y ⧸ Q) :=
          ⟨⟨fun a b =>
            (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm⟩⟩
        have hperf : Group.IsPerfect (Y ⧸ Q) :=
          Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Q)
        exact @Group.IsPerfect.not_isMulCommutative (Y ⧸ Q) _ hS.toNontrivial hperf hcomm
    apply le_antisymm ?_ hQle
    intro z hz
    have hz' : QuotientGroup.mk' Q z ∈ (Subgroup.center Y).map (QuotientGroup.mk' Q) :=
      Subgroup.mem_map_of_mem _ hz
    rw [hmapcenter, Subgroup.mem_bot] at hz'
    exact (QuotientGroup.eq_one_iff z).mp hz'
  have hqY : CFSG.Open.IsQuasisimple Y :=
    ⟨Group.isPerfect_def.mp hYperf,
      (QuotientGroup.quotientMulEquivOfEq hcenterY).isSimpleGroup_congr.mpr hS⟩
  have hperfQ : Group.IsPerfect (Y ⧸ Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Q)
  have hnabY : ∃ a b : Y ⧸ Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact @Group.IsPerfect.not_isMulCommutative (Y ⧸ Q) _ hS.toNontrivial hperfQ
      ⟨⟨fun a b => h a b⟩⟩
  have htop : Function.Surjective ⇑(Subgroup.topEquiv (G := Y)).toMonoidHom :=
    fun y => ⟨(Subgroup.topEquiv (G := Y)).symm y, by simp⟩
  have hcatQ : CFSG.Open.IsCatalogGroup (Y ⧸ Q) :=
    hKY.isCatalogGroup_of_surjective (⊤ : Subgroup Y) hnabY
      ((QuotientGroup.mk' Q).comp (Subgroup.topEquiv (G := Y)).toMonoidHom)
      ((QuotientGroup.mk'_surjective Q).comp htop)
  have hcatY : CFSG.Open.IsCatalogGroup (Y ⧸ Subgroup.center Y) :=
    CFSG.Open.isCatalogGroup_isoInvariant
      (QuotientGroup.quotientMulEquivOfEq hcenterY) hcatQ
  have hZpY : IsPGroup p (Subgroup.center Y) := hcenterY ▸ hQp
  have hZneY : Subgroup.center Y ≠ ⊥ := hcenterY ▸ hQne
  have h4 := hC5 Y hqY hcatY p hp hp5 hZneY hZpY
  omega

theorem false_of_center_preimage_not_le_center
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {Y K : Type} [Group Y] [Finite Y] [Group K] [Finite K]
    [hYperf : Group.IsPerfect Y] (hKq : CFSG.Open.IsQuasisimple K)
    (hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K))
    (Q : Subgroup Y) [hQN : Q.Normal] (hQp : IsPGroup p Q)
    (hS : IsSimpleGroup (Y ⧸ Q))
    (hminQ : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' Q) = ⊤ → M = ⊤)
    (hnc : ¬ Q ≤ Subgroup.center Y)
    (eQ : Y ⧸ Q ≃* K ⧸ Subgroup.center K)
    (hZcard : Nat.card (Subgroup.center K) = p)
    (hrkY : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) : False := by
  have hQrank : CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ Q)) ≤ 2 :=
    pRank_quotient_le_two_of_not_le_center hp (by omega : p ≠ 2) Q hQp hS hminQ
      hnc hrkY
  have hKquot : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 2 := by
    calc
      CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K))
          = CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ Q)) :=
            (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eQ).symm
      _ ≤ 2 := hQrank
  have hZp : IsPGroup p (Subgroup.center K) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hZn : Subgroup.center K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center K) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hZrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(Subgroup.center K)) ≤ 1 :=
    GL83.I713.pRank_top_le_one_of_card_lt hp (by rw [hZcard]; nlinarith [hp.two_le])
  have hAdd := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_add_of_normal
    (G := K) hp (Subgroup.center K)
  have hKrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3 := by
    omega
  have h4 := hC5 K hKq hcat p hp hp5 hZn hZp
  omega

theorem false_of_perfect_cover_data
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive) {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3)
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K))
    (hZcard : Nat.card (Subgroup.center K) = p)
    (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) [hPN : P.Normal]
    (hYperf : Group.IsPerfect Y) (hPp : IsPGroup p P) (e : Y ⧸ P ≃* K)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup G))
    (hKY : CFSG.Open.IsKGroup Y) : False := by
  classical
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.mpr hKq.1
  have hZp : IsPGroup p (Subgroup.center K) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hZn : Subgroup.center K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center K) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hrkY : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 := hrank.trans hrk
  obtain ⟨Q, hQN, hPQ, hQp, hQne, ⟨eQ⟩, hminQ⟩ :=
    @exists_central_preimage_minimal_cover Y K _ _ _ _ p P hPN hPp e hKperf hZp hZn hmin
  have hS : IsSimpleGroup (Y ⧸ Q) := eQ.isSimpleGroup_congr.mpr hKq.2
  by_cases hQle : Q ≤ Subgroup.center Y
  · exact @false_of_center_preimage_le_center hC5 p hp hp5 Y K _ _ _ _ hKY hYperf Q hQN
      hQp hQne hS hQle hrkY
  · exact @false_of_center_preimage_not_le_center hC5 p hp hp5 Y K _ _ _ _ hYperf hKq hcat
      Q hQN hQp hS hminQ hQle eQ hZcard hrkY

theorem false_of_perfect_cover_of_center_card_prime
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {K : Type} [Group K] [Finite K] (π : H →* K) (hπ : Function.Surjective π)
    (hKq : CFSG.Open.IsQuasisimple K)
    (hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K))
    (hZcard : Nat.card (Subgroup.center K) = p) : False := by
  classical
  have hZp : IsPGroup p (Subgroup.center K) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hZn : Subgroup.center K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center K) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.mpr hKq.1
  obtain ⟨Y, hGY, hFinY, P, hPN, hYperf, hPp, ⟨e⟩, hmin, hrank, hKY⟩ :=
    @exists_perfect_pCover_of_surjective G _ _ p hp H K _ hKperf π hπ
  exact @false_of_perfect_cover_data hC5 G _ _ p hp hp5 hrk K _ _ hKq hcat hZcard
    Y hGY hFinY P hPN hYperf hPp e hmin hrank (hKY hK)

theorem center_quotient_quasisimple_card_prime {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hq : CFSG.Open.IsQuasisimple K) (Z₀ : Subgroup K) [hZ0N : Z₀.Normal]
    (hZ0le : Z₀ ≤ Subgroup.center K) {m : ℕ} (hZ0card : Nat.card Z₀ = p ^ m)
    (hZcard : Nat.card (Subgroup.center K) = p ^ (m + 1)) :
    CFSG.Open.IsQuasisimple (K ⧸ Z₀) ∧ Nat.card (Subgroup.center (K ⧸ Z₀)) = p := by
  classical
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  have hperfK : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hnabK : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact @Group.IsPerfect.not_isMulCommutative (K ⧸ Subgroup.center K) _
      hq.2.toNontrivial hperfK ⟨⟨fun a b => h a b⟩⟩
  have hqK : CFSG.IsQuasisimple K := ⟨hKperf, hq.2, hnabK⟩
  obtain ⟨hqK', -, hcenterK'⟩ :=
    CFSG.LocalCores.quasisimple_central_quotient hqK Z₀ hZ0le
  have hK'q : CFSG.Open.IsQuasisimple (K ⧸ Z₀) :=
    ⟨Group.isPerfect_def.mp hqK'.1, hqK'.2.1⟩
  let Z : Subgroup K := Subgroup.center K
  have hfZker : ((QuotientGroup.mk' Z₀).comp Z.subtype).ker = Z₀.subgroupOf Z := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hfZrange : ((QuotientGroup.mk' Z₀).comp Z.subtype).range =
      Subgroup.center (K ⧸ Z₀) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hcenterK']
  have hfZcard := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' Z₀).comp Z.subtype)
  rw [hfZker, hfZrange] at hfZcard
  have hZ0sub : Nat.card ↥(Z₀.subgroupOf Z) = p ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0le).toEquiv, hZ0card]
  rw [hZ0sub] at hfZcard
  have hZcard' : Nat.card ↥Z = p ^ (m + 1) := by
    rw [show Nat.card ↥Z = Nat.card Z from rfl, hZcard]
  rw [hZcard', pow_succ] at hfZcard
  exact ⟨hK'q, Nat.mul_left_cancel (pow_pos hp.pos m) hfZcard⟩

theorem false_of_central_quotient
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {K : Type} [Group K] [Finite K] (π : H →* K) (hπ : Function.Surjective π)
    (hq : CFSG.Open.IsQuasisimple K) (Z₀ : Subgroup K) [hZ0N : Z₀.Normal]
    (hZ0le : Z₀ ≤ Subgroup.center K) {m : ℕ} (hZ0card : Nat.card Z₀ = p ^ m)
    (hZcard : Nat.card (Subgroup.center K) = p ^ (m + 1)) : False := by
  classical
  obtain ⟨hK'q, hcentercard⟩ :=
    @center_quotient_quasisimple_card_prime K _ _ p hp hq Z₀ hZ0N hZ0le m
      hZ0card hZcard
  let π' : H →* (K ⧸ Z₀) := (QuotientGroup.mk' Z₀).comp π
  have hπ' : Function.Surjective π' :=
    (QuotientGroup.mk'_surjective Z₀).comp hπ
  have hperfK' : Group.IsPerfect (K ⧸ Z₀) := Group.isPerfect_def.mpr hK'q.1
  have hperf : Group.IsPerfect ((K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀)) :=
    @Group.IsPerfect.ofSurjective (K ⧸ Z₀)
      ((K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀)) _ _
      (QuotientGroup.mk' (Subgroup.center (K ⧸ Z₀))) hperfK'
      (QuotientGroup.mk'_surjective (Subgroup.center (K ⧸ Z₀)))
  have hnab : ∃ a b : (K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact @Group.IsPerfect.not_isMulCommutative ((K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀)) _
      hK'q.2.toNontrivial hperf ⟨⟨fun a b => h a b⟩⟩
  have hcat : CFSG.Open.IsCatalogGroup ((K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀)) :=
    @CFSG.Open.IsKGroup.isCatalogGroup_of_surjective G _ hK H
      ((K ⧸ Z₀) ⧸ Subgroup.center (K ⧸ Z₀)) _ hK'q.2 hnab
      ((QuotientGroup.mk' (Subgroup.center (K ⧸ Z₀))).comp π')
      ((QuotientGroup.mk'_surjective (Subgroup.center (K ⧸ Z₀))).comp hπ')
  exact @false_of_perfect_cover_of_center_card_prime hC5 G _ _ hK p hp hp5 hrk H
    (K ⧸ Z₀) _ _ π' hπ' hK'q hcat hcentercard

theorem false_of_quasisimple_section (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {K : Type} [Group K] (π : H →* K) (hπ : Function.Surjective π)
    (hKq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) : False := by
  classical
  have hFinK : Finite K := Finite.of_surjective π hπ
  have hcommK : commutator K = ⊤ := hKq.1
  have hsimpleK : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  let Z : Subgroup K := Subgroup.center K
  have hFinZ : Finite ↥Z :=
    @Finite.of_injective ↥Z K hFinK Z.subtype Z.subtype_injective
  obtain ⟨n, hn⟩ :=
    @IsPGroup.exists_card_eq p ↥Z _ ⟨hp⟩ hFinZ (hZp : IsPGroup p Z)
  have hn0 : n ≠ 0 := by
    intro h0
    apply hZ
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, h0, pow_zero]
  let m := n - 1
  have hn_eq : n = m + 1 := by omega
  have hdvd : p ^ m ∣ Nat.card ↥Z := by
    rw [hn, hn_eq, pow_succ]
    exact dvd_mul_right (p ^ m) p
  obtain ⟨Z₁, hZ₁card⟩ :=
    @Sylow.exists_subgroup_card_pow_prime ↥Z _ hFinZ p m ⟨hp⟩ hdvd
  let Z₀ : Subgroup K := Z₁.map Z.subtype
  have hZ₀le : Z₀ ≤ Z := Subgroup.map_subtype_le Z₁
  have hZ₀card : Nat.card Z₀ = p ^ m := by
    change Nat.card (Z₁.map Z.subtype) = p ^ m
    rw [Subgroup.card_map_of_injective Z.subtype_injective, hZ₁card]
  have hZ0N : Z₀.Normal := Subgroup.normal_of_le_center hZ₀le
  have hZcard' : Nat.card ↥Z = p ^ (m + 1) := by
    rw [show Nat.card ↥Z = Nat.card Z from rfl, hn, hn_eq]
  exact @false_of_central_quotient hC5 G _ _ hK p hp hp5 hrk H K _ hFinK π hπ hKq
    Z₀ hZ0N hZ₀le m hZ₀card hZcard'

end CFSG.LocalAnalysis.WeakClosure81.Asch22
