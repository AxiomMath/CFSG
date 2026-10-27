module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped Pointwise commutatorElement

theorem ggRCSKGPiece_of_marking {G : Type} [Group G] {C₀ E J : Subgroup G} (hJC : J ≤ C₀)
    (hJN : C₀ ≤ Subgroup.normalizer (J : Set G)) (hperf : ⁅J, J⁆ = J)
    (hQ1 : pCoreOf 2 C₀ ≤ J ⊔ (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)))
    (hQ2 : pCoreOf 2 C₀ ≤
      ⁅J, pCoreOf 2 C₀⁆ ⊔ (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)))
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) {X : Type} [Group X]
    (hXq : CFSG.Assembly.IsQuasisimple X) (𝒜 : Set (MulAut X))
    (hXm : LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧ ∀ α ∈ 𝒜, ∃ φ ∈ I,
      ∀ x : X, φ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk (α x))))
    (π : ↥J →* X) (hπ : Function.Surjective π) (hker : π.ker = (pCoreOf 2 C₀).subgroupOf J)
    (hact : ∀ ε ∈ E, ∃ α ∈ 𝒜, ∀ s s' : ↥J, (s' : G) = ε⁻¹ * s * ε → π s' = α (π s)) :
    GGRCSKGPiece C₀ E J := by
  refine ⟨hJC, ggIsSubnormal_of_normal hJC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJN), hperf, hQ1, hQ2, hEJ, ?_⟩
  intro hN
  haveI : ((pCoreOf 2 C₀).subgroupOf J).Normal := hN
  let QJ : Type := ↥J ⧸ (pCoreOf 2 C₀).subgroupOf J
  let e : QJ ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he_mk : ∀ s : ↥J, e (QuotientGroup.mk s) = π s := by
    intro s
    change (QuotientGroup.quotientKerEquivOfSurjective π hπ)
      (QuotientGroup.quotientMulEquivOfEq hker.symm (QuotientGroup.mk s)) = π s
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hqs : CFSG.Assembly.IsQuasisimple QJ :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hXq
  refine ⟨hqs, ?_⟩
  refine largeEvenMarking_congr e ?_ hXm
  intro lab R _ I F θX hθ
  refine ⟨hθ.1, ?_⟩
  intro ε hε
  obtain ⟨α, hα, hαact⟩ := hact ε hε
  obtain ⟨φ, hφ, hφact⟩ := hθ.2 α hα
  refine ⟨φ, hφ, fun l l' hrel => ?_⟩
  obtain ⟨s, s', hsl, hsl', hss'⟩ := hrel
  have hθJ : ∀ l : QJ,
      ((centerQuotCongr e).trans θX) (QuotientGroup.mk l) = θX (QuotientGroup.mk (e l)) := by
    intro l
    rw [MulEquiv.trans_apply, centerQuotCongr_mk]
  rw [← hsl, ← hsl', hθJ, hθJ, he_mk s, he_mk s', hαact s s' hss']
  exact hφact (π s)

theorem largeEvenMarking_innAct {X : Type} [Group X]
    (h : LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I)) :
    LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧ ∀ α ∈ LargeEvenInnSet X,
      ∃ φ ∈ I, ∀ x : X, φ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk (α x))) := by
  refine largeEvenMarking_mono ?_ h
  intro lab R _ I F θ hθ
  refine ⟨hθ.1, ?_⟩
  intro α hα
  obtain ⟨y, rfl⟩ := hα
  refine ⟨MulAut.conj (θ (QuotientGroup.mk y)), hθ.2 (Set.mem_range_self _), ?_⟩
  intro x
  simp [MulAut.conj_apply]

theorem le_commutator_sup_of_perfect {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q L : Subgroup G} (hQ : IsPGroup p Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hperf : ⁅Q ⊔ L, Q ⊔ L⁆ = Q ⊔ L) : Q ≤ ⁅Q ⊔ L, Q⁆ ⊔ (Q ⊓ L) := by
  classical
  let H : Subgroup G := Q ⊔ L
  let N : Subgroup G := ⁅H, Q⁆
  let M : Subgroup G := L ⊔ N
  have hQH : Q ≤ H := le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hLQ
  have hNleQ : N ≤ Q := by
    rw [Subgroup.commutator_le]
    intro h hh q hq
    have h1 : h * q * h⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHnormQ hh) q).mp hq
    have h2 : h * q * h⁻¹ * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
    simpa [commutatorElement_def] using h2
  have hNleH : N ≤ H := hNleQ.trans hQH
  have hMleH : M ≤ H := sup_le hLH hNleH
  have hQHnorm : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHnormQ
  have hNnormH : (N.subgroupOf H).Normal := by
    haveI : (Q.subgroupOf H).Normal := hQHnorm
    have hcomm : (⁅(⊤ : Subgroup ↥H), Q.subgroupOf H⁆).Normal :=
      Subgroup.commutator_normal _ _
    have hmapS : Subgroup.map H.subtype ⁅(⊤ : Subgroup ↥H), Q.subgroupOf H⁆ = N := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQH, Subgroup.map_top,
        Subgroup.range_subtype]
    have hmapN : Subgroup.map H.subtype (N.subgroupOf H) = N :=
      Subgroup.map_subgroupOf_eq_of_le hNleH
    have hEq : N.subgroupOf H = ⁅(⊤ : Subgroup ↥H), Q.subgroupOf H⁆ :=
      Subgroup.map_injective H.subtype_injective (hmapN.trans hmapS.symm)
    rw [hEq]
    exact hcomm
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleH).mp hNnormH
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := hLH.trans hHN
  have hLNmul : (M : Set G) = (L : Set G) * (N : Set G) := by
    simpa [M] using Subgroup.coe_mul_of_left_le_normalizer_right L N hLN
  have hLconj : ∀ l ∈ L, ∀ x ∈ M, l * x * l⁻¹ ∈ M := by
    intro l hl x hx
    have hx' : x ∈ (L : Set G) * (N : Set G) := by
      rw [← hLNmul]
      exact hx
    obtain ⟨l', hl', n, hn, hEq⟩ := hx'
    rw [← hEq]
    have h1 : l * l' * l⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) l').mp hl'
    have h2 : l * n * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN (hLH hl)) n).mp hn
    have heq : l * (l' * n) * l⁻¹ = (l * l' * l⁻¹) * (l * n * l⁻¹) := by group
    rw [heq]
    exact M.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hQconj : ∀ q ∈ Q, ∀ x ∈ M, q * x * q⁻¹ ∈ M := by
    intro q hq x hx
    have hx' : x ∈ (L : Set G) * (N : Set G) := by
      rw [← hLNmul]
      exact hx
    obtain ⟨l', hl', n, hn, hEq⟩ := hx'
    rw [← hEq]
    have hNconj : q * n * q⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hHN (hQH hq)) n).mp hn
    have hLconj' : q * l' * q⁻¹ ∈ M := by
      have hcomm : ⁅l', q⁆ ∈ N :=
        (Subgroup.commutator_le.mp le_rfl) l' (hLH hl') q hq
      have hcomm' : ⁅q, l'⁆ ∈ N := by
        have heq : ⁅q, l'⁆ = ⁅l', q⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [heq]
        exact N.inv_mem hcomm
      have heq : q * l' * q⁻¹ = ⁅q, l'⁆ * l' := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact M.mul_mem (Subgroup.mem_sup_right hcomm') (Subgroup.mem_sup_left hl')
    have heq : q * (l' * n) * q⁻¹ =
        (q * l' * q⁻¹) * (q * n * q⁻¹) := by group
    rw [heq]
    exact M.mul_mem hLconj' (Subgroup.mem_sup_right hNconj)
  have hLnormM : L ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hLconj l hl x
    · intro hx
      have h := hLconj l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
      have heq : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
      rw [heq] at h
      exact h
  have hQnormM : Q ≤ Subgroup.normalizer (M : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hQconj q hq x
    · intro hx
      have h := hQconj q⁻¹ (Q.inv_mem hq) (q * x * q⁻¹) hx
      have heq : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
      rw [heq] at h
      exact h
  have hHnormM : H ≤ Subgroup.normalizer (M : Set G) := sup_le hQnormM hLnormM
  have hMnormH : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleH).mpr hHnormM
  let K : Subgroup ↥H := M.subgroupOf H
  haveI : K.Normal := hMnormH
  haveI : Group.IsPerfect ↥H :=
    Subgroup.isPerfect_iff.mpr (by simpa [H] using hperf)
  have hVperf : Group.IsPerfect (↥H ⧸ K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  let f : ↥Q →* (↥H ⧸ K) :=
    (QuotientGroup.mk' K).comp (Subgroup.inclusion hQH)
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective K v
    have hh : (h : G) ∈ (Q : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ]
      exact h.2
    obtain ⟨q, hq, l, hl, hEq⟩ := hh
    refine ⟨⟨q, hq⟩, ?_⟩
    change (QuotientGroup.mk' K) (Subgroup.inclusion hQH ⟨q, hq⟩) =
      (QuotientGroup.mk' K) h
    change (QuotientGroup.mk (Subgroup.inclusion hQH ⟨q, hq⟩) : ↥H ⧸ K) =
      (QuotientGroup.mk h : ↥H ⧸ K)
    rw [QuotientGroup.eq]
    have hEq' : (Subgroup.inclusion hQH ⟨q, hq⟩ : ↥H)⁻¹ * h = ⟨l, hLH hl⟩ := by
      apply Subtype.ext
      change q⁻¹ * (h : G) = l
      rw [← hEq]
      group
    rw [hEq']
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl)
  have hVp : IsPGroup p (↥H ⧸ K) := IsPGroup.of_surjective hQ f hfsurj
  have hKtop : K = ⊤ := by
    by_contra hne
    haveI : Nontrivial (↥H ⧸ K) := QuotientGroup.nontrivial_iff.mpr hne
    haveI : Group.IsPerfect (↥H ⧸ K) := hVperf
    haveI : Group.IsNilpotent (↥H ⧸ K) := hVp.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (↥H ⧸ K) inferInstance
  have hHM : H ≤ M := by
    have h1 : M.subgroupOf H = ⊤ := hKtop
    exact Subgroup.subgroupOf_eq_top.mp h1
  have hQM : Q ≤ M := hQH.trans hHM
  have hgoal : Q ≤ N ⊔ (Q ⊓ L) := by
    intro q hq
    have hq' : q ∈ (L : Set G) * (N : Set G) := by
      rw [← hLNmul]
      exact hQM hq
    obtain ⟨l, hl, n, hn, hEq⟩ := hq'
    have hnQ : n ∈ Q := hNleQ hn
    have hlQ : l ∈ Q := by
      have heq : l = q * n⁻¹ := by rw [← hEq]; group
      rw [heq]
      exact Q.mul_mem hq (Q.inv_mem hnQ)
    rw [← hEq]
    exact (N ⊔ (Q ⊓ L)).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hlQ, hl⟩))
      (Subgroup.mem_sup_left hn)
  simpa [N, H] using hgoal

theorem exists_sup_proj {G : Type} [Group G] {Q L : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hdisj : Q ⊓ L = ⊥) :
    ∃ π : ↥(Q ⊔ L) →* ↥L, Function.Surjective π ∧ π.ker = Q.subgroupOf (Q ⊔ L) ∧
      ∀ (x : ↥(Q ⊔ L)) (l : ↥L), (x : G) * (l : G)⁻¹ ∈ Q → π x = l := by
  classical
  have hex : ∀ x : ↥(Q ⊔ L), ∃ l : ↥L, (x : G) * (l : G)⁻¹ ∈ Q := by
    intro x
    have hx : (x : G) ∈ (Q : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ]
      exact x.2
    obtain ⟨q, hq, l, hl, hEq⟩ := hx
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [← hEq]
    simpa using hq
  let πfun : ↥(Q ⊔ L) → ↥L := fun x => Classical.choose (hex x)
  have hπfun : ∀ x : ↥(Q ⊔ L), (x : G) * (πfun x : G)⁻¹ ∈ Q :=
    fun x => Classical.choose_spec (hex x)
  have huniq : ∀ (x : ↥(Q ⊔ L)) (l : ↥L), (x : G) * (l : G)⁻¹ ∈ Q → πfun x = l := by
    intro x l hxl
    have hq : (πfun x : G) * (l : G)⁻¹ ∈ Q := by
      have h1 : (πfun x : G) * (l : G)⁻¹ =
          ((x : G) * (πfun x : G)⁻¹)⁻¹ * ((x : G) * (l : G)⁻¹) := by group
      rw [h1]
      exact Q.mul_mem (Q.inv_mem (hπfun x)) hxl
    have hl : (πfun x : G) * (l : G)⁻¹ ∈ L :=
      L.mul_mem (πfun x).2 (L.inv_mem l.2)
    have hbot : (πfun x : G) * (l : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hq, hl⟩
    have h1 : (πfun x : G) * (l : G)⁻¹ = 1 := by simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  let π : ↥(Q ⊔ L) →* ↥L :=
    { toFun := πfun
      map_one' := huniq 1 1 (by simp)
      map_mul' := by
        intro x y
        apply huniq
        have hx := hπfun x
        have hy := hπfun y
        have hconj : (πfun x : G) * ((y : G) * (πfun y : G)⁻¹) * (πfun x : G)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hLQ (πfun x).2) _).mp hy
        have hprod : ((x * y : ↥(Q ⊔ L)) : G) * ((πfun x * πfun y : ↥L) : G)⁻¹ ∈ Q := by
          have hm : ((x : G) * (πfun x : G)⁻¹) *
              ((πfun x : G) * ((y : G) * (πfun y : G)⁻¹) * (πfun x : G)⁻¹) ∈ Q :=
            Q.mul_mem hx hconj
          have heq : ((x * y : ↥(Q ⊔ L)) : G) * ((πfun x * πfun y : ↥L) : G)⁻¹ =
              ((x : G) * (πfun x : G)⁻¹) *
                ((πfun x : G) * ((y : G) * (πfun y : G)⁻¹) * (πfun x : G)⁻¹) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [heq]
          exact hm
        exact hprod }
  have hsurj : Function.Surjective π := by
    intro l
    exact ⟨⟨l, Subgroup.mem_sup_right l.2⟩, huniq _ l (by simp)⟩
  have hker : π.ker = Q.subgroupOf (Q ⊔ L) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 := hπfun x
      have hx' : πfun x = 1 := hx
      rw [hx'] at h1
      simpa using h1
    · intro hx
      exact huniq x 1 (by simpa using hx)
  exact ⟨π, hsurj, hker, fun x l hxl => huniq x l hxl⟩

theorem proj_conj_of_eq_mul {G : Type} [Group G] {Q L : Subgroup G} (π : ↥(Q ⊔ L) →* ↥L)
    (hπ : ∀ (x : ↥(Q ⊔ L)) (l : ↥L), (x : G) * (l : G)⁻¹ ∈ Q → π x = l)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) {ε q l m : G} (hq : q ∈ Q)
    (hlQ : l ∈ Subgroup.normalizer (Q : Set G)) (hlL : l ∈ Subgroup.normalizer (L : Set G))
    (hmQ : m ∈ Subgroup.normalizer (Q : Set G)) (hmL : m ∈ Subgroup.centralizer (L : Set G))
    (hε : ε = q * l * m) (s s' : ↥(Q ⊔ L)) (hs : (s' : G) = ε⁻¹ * s * ε) :
    ((π s' : ↥L) : G) = l⁻¹ * (π s : G) * l := by
  have hq₁ : (s : G) * (π s : G)⁻¹ ∈ Q := by
    have hs' : (s : G) ∈ (Q : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ]
      exact s.2
    obtain ⟨q₂, hq₂, l₂, hl₂, hEq⟩ := hs'
    have hπs : π s = ⟨l₂, hl₂⟩ :=
      hπ s ⟨l₂, hl₂⟩ (by rw [← hEq]; simpa using hq₂)
    rw [hπs]
    have hEq' : (s : G) * l₂⁻¹ = q₂ := by rw [← hEq]; group
    rw [hEq']
    exact hq₂
  have hLmem : l⁻¹ * (π s : G) * l ∈ L := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlL) (π s : G)).mp (π s).2
  let lInv : ↥L := ⟨l⁻¹ * (π s : G) * l, hLmem⟩
  set q₁ : G := (s : G) * (π s : G)⁻¹ with hq₁def
  have hq₁' : q₁ ∈ Q := by simpa [hq₁def] using hq₁
  set X : G := q⁻¹ * q₁ * ((π s : G) * q * (π s : G)⁻¹) with hXdef
  have hX : X ∈ Q := by
    rw [hXdef]
    refine Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hq₁') ?_
    exact (Subgroup.mem_normalizer_iff.mp (hLQ (π s).2) q).mp hq
  have hq₁l₁ : q₁ * (π s : G) = (s : G) := by rw [hq₁def]; group
  have hm' : l * m * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzl : l⁻¹ * z * l ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlL) z).mp hz
    have hcomm : (l⁻¹ * z * l) * m = m * (l⁻¹ * z * l) :=
      Subgroup.mem_centralizer_iff.mp hmL _ hzl
    calc
      z * (l * m * l⁻¹) = l * ((l⁻¹ * z * l) * m) * l⁻¹ := by group
      _ = l * (m * (l⁻¹ * z * l)) * l⁻¹ := by rw [hcomm]
      _ = (l * m * l⁻¹) * z := by group
  have hml₁ : (π s : G) * (l * m * l⁻¹) = (l * m * l⁻¹) * (π s : G) :=
    Subgroup.mem_centralizer_iff.mp hm' (π s : G) (π s).2
  have hml₁inv : (l * m * l⁻¹) * (π s : G)⁻¹ = (π s : G)⁻¹ * (l * m * l⁻¹) := by
    have hc : Commute ((π s : G)) (l * m * l⁻¹) := hml₁
    exact (hc.symm.inv_right).eq
  have hXs : (s' : G) * (lInv : G)⁻¹ = (l * m)⁻¹ * X * (l * m) := by
    calc
      (s' : G) * (lInv : G)⁻¹
          = m⁻¹ * l⁻¹ * q⁻¹ * q₁ * (π s : G) * q * (l * m * l⁻¹) *
              (π s : G)⁻¹ * l := by
            rw [hs, hε, ← hq₁l₁]
            dsimp [lInv]
            group
      _ = m⁻¹ * l⁻¹ * q⁻¹ * q₁ * (π s : G) * q *
              ((l * m * l⁻¹) * (π s : G)⁻¹) * l := by group
      _ = m⁻¹ * l⁻¹ * q⁻¹ * q₁ * (π s : G) * q *
              ((π s : G)⁻¹ * (l * m * l⁻¹)) * l := by rw [hml₁inv]
      _ = m⁻¹ * l⁻¹ * q⁻¹ * q₁ * (π s : G) * q * (π s : G)⁻¹ *
              (l * m * l⁻¹) * l := by group
      _ = (l * m)⁻¹ * X * (l * m) := by
            rw [hXdef]
            group
  have hmem : (s' : G) * (lInv : G)⁻¹ ∈ Q := by
    have hB : l * m ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hlQ hmQ
    rw [hXs]
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hB) X).mp hX
  have hπs' : π s' = lInv := hπ s' lInv hmem
  simpa [lInv] using congrArg Subtype.val hπs'

theorem mem_of_mul_mem_centralizer {G : Type} [Group G] {G₀ : Subgroup G}
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {c : G}
    (h : ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G)) : c ∈ G₀ := by
  obtain ⟨g, hg, hcg⟩ := h
  have h1 : c * g = 1 := by
    rw [hC, Subgroup.mem_bot] at hcg
    exact hcg
  rw [eq_inv_of_mul_eq_one_left h1]
  exact G₀.inv_mem hg

end CFSG.StandardType
