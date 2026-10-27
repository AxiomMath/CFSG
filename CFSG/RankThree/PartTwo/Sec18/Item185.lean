module

public import CFSG.RankThree.PartTwo.Sec18.Item185Ctx
import CFSG.RankThree.PartTwo.Sec3.ElemNineAut
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec18.SylowTop
import CFSG.RankThree.PartTwo.Sec18.Item185Irred
import CFSG.RankThree.PartTwo.Sec18.Item185Fstar
import CFSG.RankThree.PartTwo.Sec18.Item185Pcrit
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec18.Item185Quot
import CFSG.RankThree.PartTwo.Sec18.Item185Omega
import CFSG.RankThree.PartTwo.Sec18.Item185Faithful
import CFSG.RankThree.PartTwo.Sec18.Item185Cases
public import CFSG.RankThree.PartTwo.Sec18.Item185LeafF1
import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open Item185Proof

private theorem isElemAbelian_of_ker_trivial {H K : Type} [Group H] [Group K] {p : ℕ}
    (f : H →* K) {F : Subgroup H} (hF : ∀ x ∈ F, f x = 1 → x = 1)
    (h : IsElemAbelian p (F.map f)) : IsElemAbelian p F := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have hcomm : f a * f b = f b * f a :=
      congrArg Subtype.val (h.1.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
        ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
    have hmem : (a : H) * b * ((b : H) * a)⁻¹ ∈ F :=
      F.mul_mem (F.mul_mem a.2 b.2) (F.inv_mem (F.mul_mem b.2 a.2))
    have hker : f ((a : H) * b * ((b : H) * a)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp (hF _ hmem hker))
  · have h1 : f x ^ p = 1 := h.2 (f x) (Subgroup.mem_map_of_mem f hx)
    have h2 : f (x ^ p) = 1 := by rw [map_pow, h1]
    exact hF _ (F.pow_mem hx p) h2

private theorem isElemAbelian_of_le_elemAbelian {G : Type} [Group G] {p : ℕ} {E F : Subgroup G}
    (hFE : F ≤ E) (hE : IsElemAbelian p E) : IsElemAbelian p F := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  have h1 := hE.1.is_comm.comm (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩
  exact Subtype.ext (congrArg (fun x : E => (x : G)) h1)

private theorem exists_elemAbelian_lift {X : Type} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] (hN : IsPGroup 2 N) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup (X ⧸ N)} (hE : IsElemAbelian p E) :
    ∃ F : Subgroup X, IsElemAbelian p F ∧ Nat.card F = Nat.card E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E₀ : Subgroup X := E.comap (QuotientGroup.mk' N)
  have hNE₀ : N ≤ E₀ := fun n hn => by
    show (n : X ⧸ N) ∈ E
    rw [(QuotientGroup.eq_one_iff n).mpr hn]
    exact E.one_mem
  let ψ : E₀ →* X ⧸ N := (QuotientGroup.mk' N).comp E₀.subtype
  have hψrange : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro he
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N e
      exact ⟨⟨m, he⟩, rfl⟩
  have hker : ψ.ker = N.subgroupOf E₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : X)
  have hidx : (N.subgroupOf E₀).index = Nat.card E := by
    rw [← hker, Subgroup.index_ker, hψrange]
  have hNcard : Nat.card (N.subgroupOf E₀) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE₀).toEquiv
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hEp
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf E₀)) (N.subgroupOf E₀).index := by
    rw [hNcard, hidx, hk, hj]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
  obtain ⟨A', hA'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcardA : Nat.card A' = (N.subgroupOf E₀).index := by
    have h1 := hA'.card_mul_card
    have h2 := Subgroup.card_mul_index (N.subgroupOf E₀)
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hFE₀ : A'.map E₀.subtype ≤ E₀ := Subgroup.map_subtype_le A'
  refine ⟨A'.map E₀.subtype, ?_, ?_⟩
  · apply isElemAbelian_of_ker_trivial (QuotientGroup.mk' N)
    · rintro x hx hx1
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      have haN : a ∈ N.subgroupOf E₀ :=
        Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff (a : X)).mp hx1)
      have ha1 : a = 1 := Subgroup.disjoint_def.mp hA'.disjoint haN ha
      rw [ha1, map_one]
    · refine isElemAbelian_of_le_elemAbelian ?_ hE
      rintro _ ⟨x, hx, rfl⟩
      exact hFE₀ hx
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hcardA, hidx]

private theorem exists_conj_of_planeQ8 {G : Type} [Group G] [Finite G] {A B T : Subgroup G}
    {c : G} (hQ : PlaneQ8 A B T c) (hAT : A ⊓ T = B) {x y : G} (hx : x ∈ B) (hy : y ∈ B)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ t ∈ T, t * x * t⁻¹ = y := by
  subst hAT
  have hcomm : ∀ a ∈ A ⊓ T, ∀ b ∈ A ⊓ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.isElemAbelian.1.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
  have h3 : ∀ b : ↥(A ⊓ T), b ^ 3 = 1 := fun b => Subtype.ext (hQ.isElemAbelian.2 (b : G) b.2.1)
  letI : CommGroup ↥(A ⊓ T) :=
    { (inferInstance : Group ↥(A ⊓ T)) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  obtain ⟨f, hf⟩ := hQ.quaternion
  have hc : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hQ.commute k hk
  have hA : A = (A ⊓ T) ⊔ Subgroup.zpowers c := hQ.eq_sup.trans (sup_comm _ _)
  obtain ⟨φ⟩ := Sec4.Res423Four.nonempty_autIn_inf_equiv hc hA
  let g : QuaternionGroup 2 →* MulAut ↥(A ⊓ T) :=
    (Sec4.autIn T (A ⊓ T)).subtype.comp (φ.toMonoidHom.comp f)
  have hg : Function.Injective g :=
    (Subgroup.subtype_injective _).comp (φ.injective.comp hf)
  let e : g.range ≃* QuaternionGroup 2 := (MonoidHom.ofInjective hg).symm
  obtain ⟨σ, hσ, hσxy⟩ := Sec3.exists_apply_eq_of_quaternion h3 hQ.card_plane e
    (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hσ
  obtain ⟨t, hN, hT, hteq⟩ := Sec4.mem_autIn_iff.mp (φ (f q)).2
  have key : (A ⊓ T).normalizerMonoidHom ⟨t, hN⟩ ⟨x, hx⟩ = ⟨y, hy⟩ := by
    rw [hteq]
    exact hσxy
  refine ⟨t, hT, ?_⟩
  have h2 := congrArg Subtype.val key
  rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2

private theorem conj_mem_oTwoP_map {G : Type} [Group G] {M : Subgroup G} {x : G} (hxM : x ∈ M)
    {y : G} (hy : y ∈ (Sec4.oTwoP 3 ↥M).map M.subtype) :
    x * y * x⁻¹ ∈ (Sec4.oTwoP 3 ↥M).map M.subtype := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩ * z * (⟨x, hxM⟩ : ↥M)⁻¹,
    (Sec4.oTwoP_normal 3 ↥M).conj_mem z hz ⟨x, hxM⟩, rfl⟩

private theorem inf_oTwoP_eq_bot {G : Type} [Group G] {A B T M : Subgroup G} {c : G}
    (hQ : PlaneQ8 A B T c) (hWM : Subgroup.normalizer (A : Set G) ≤ M)
    (hnot : ¬ B ≤ (Sec4.oTwoP 3 ↥M).map M.subtype) :
    B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype = ⊥ := by
  have hKV : T ≤ Subgroup.normalizer
      ((B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype : Subgroup G) : Set G) := by
    intro t ht
    have htM : t ∈ M := hWM (hQ.le_normalizer ht)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hB := Subgroup.mem_normalizer_iff.mp (hQ.le_normalizer_plane ht) h
    have hO : h ∈ (Sec4.oTwoP 3 ↥M).map M.subtype ↔
        t * h * t⁻¹ ∈ (Sec4.oTwoP 3 ↥M).map M.subtype := by
      refine ⟨conj_mem_oTwoP_map htM, fun hh => ?_⟩
      have h' := conj_mem_oTwoP_map (M.inv_mem htM) hh
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [e] at h'
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr hB hO
  rcases Sec13.eq_bot_or_eq_of_isIrreducibleOn hQ.irreducible inf_le_left hKV with h | h
  · exact h
  · exact absurd ((le_of_eq h.symm).trans inf_le_right) hnot

private theorem comm_oTwoP_of_planeQ8 {G : Type} [Group G] [Finite G] {A B T M : Subgroup G}
    {c : G} (h : Sec18Std G A M) (hQ : PlaneQ8 A B T c)
    (hWM : Subgroup.normalizer (A : Set G) ≤ M) (hAT : A ⊓ T = B)
    (hBO : B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype = ⊥) :
    ∀ p : ℕ, p.Prime → 3 < p → ∀ b ∈ B, ∀ y ∈ (Sec4.oTwoP p ↥M).map M.subtype,
      b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  intro p hp hp3 b hb y hy
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBA : B ≤ A := by rw [hQ.eq_sup]; exact le_sup_right
  have hAM : A ≤ M := (Subgroup.le_normalizer (H := A)).trans hWM
  have hBM : B ≤ M := hBA.trans hAM
  have hTM : T ≤ M := hQ.le_normalizer.trans hWM
  have hBe : IsElemAbelian 3 B := isElemAbelian_of_le_elemAbelian hBA hQ.isElemAbelian
  have hQO : CFSG.Open.pCoreOf 2 M ≤ (Sec4.oTwoP 3 ↥M).map M.subtype := by
    rintro z ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) w ∈ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    rw [h1]
    exact one_mem _
  have hBker : ∀ x ∈ B.subgroupOf M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) x = 1 → x = 1 := by
    intro x hx hx1
    have hxQ : (x : ↥M) ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff x).mp hx1
    have hxO : (x : G) ∈ B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx,
        hQO (Subgroup.mem_map_of_mem M.subtype hxQ)⟩
    rw [hBO, Subgroup.mem_bot] at hxO
    exact Subtype.ext hxO
  have hBmE : IsElemAbelian 3 (B.subgroupOf M) :=
    isElemAbelian_of_ker_trivial M.subtype (fun x _ hx => Subtype.ext hx)
      (by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBM]; exact hBe)
  have hB₁E : IsElemAbelian 3 ((B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :=
    CFSG.SectionRank.isElemAbelian_map hBmE _
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (B.subgroupOf M).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hBker x.1 x.2 hx)
  have hB₁9 : Nat.card ((B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) = 9 := by
    have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (B.subgroupOf M).subtype).range =
        (B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have e1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have e2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
    rw [← hrange, ← e1, e2, hQ.card_plane]
  have hTmN : T.subgroupOf M ≤ Subgroup.normalizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro s hs
    have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.mp hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hQ.le_normalizer_plane hsT) (x : G)
  have hS₁N : (T.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (((B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.map_mono (f := QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hTmN).trans
      (Subgroup.le_normalizer_map _)
  have htrans : ∀ x ∈ (B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)), x ≠ 1 →
      ∀ y ∈ (B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)), y ≠ 1 →
      ∃ s ∈ (T.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)), s * x * s⁻¹ = y := by
    rintro _ ⟨x', hx', rfl⟩ hx1 _ ⟨y', hy', rfl⟩ hy1
    have hx'1 : (x' : G) ≠ 1 := fun h => hx1 (by rw [show x' = 1 from Subtype.ext h, map_one])
    have hy'1 : (y' : G) ≠ 1 := fun h => hy1 (by rw [show y' = 1 from Subtype.ext h, map_one])
    obtain ⟨t, ht, hty⟩ := exists_conj_of_planeQ8 hQ hAT (Subgroup.mem_subgroupOf.mp hx')
      (Subgroup.mem_subgroupOf.mp hy') hx'1 hy'1
    have hconj : (⟨t, hTM ht⟩ : ↥M) * x' * (⟨t, hTM ht⟩ : ↥M)⁻¹ = y' := Subtype.ext hty
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, hTM ht⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  have hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian p E →
      Nat.card E ≤ p ^ 2 := by
    intro E hE
    obtain ⟨F, hF, hFcard⟩ := exists_elemAbelian_lift (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      (p := p) (by omega) hE
    have hFM : F.map M.subtype ≤ M := Subgroup.map_subtype_le F
    have hF' := card_le_sq_of_le_M h hp hp3 hFM (CFSG.SectionRank.isElemAbelian_map hF M.subtype)
    rw [Subgroup.card_map_of_injective M.subtype_injective, hFcard] at hF'
    exact hF'
  have hc := centralizes_pCore hp3 hrank hB₁E hB₁9 hS₁N htrans
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hb₁ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨b, hBM hb⟩ : ↥M) ∈
      (B.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have hzY : QuotientGroup.mk' (CFSG.pCore 2 ↥M) z ∈ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := hz
  have hcomm := hc _ hb₁ _ hzY
  have hmul : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ((⟨b, hBM hb⟩ : ↥M) * z * (⟨b, hBM hb⟩ : ↥M)⁻¹ * z⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  exact Subgroup.mem_map.mpr ⟨_, (QuotientGroup.eq_one_iff _).mp hmul, rfl⟩

theorem item185_of
    (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) (h1846 : Item184_6)
    (hF1 : LeafF1) (hOut : LeafOuter) (hIn : LeafInner) : Item185 := by
  intro G _ _ A M H c hH
  by_contra hnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.normalizer (A : Set G))
  have hC := ctx_of h1812 h184 h1842 h1846 hH hP
  have hWM : Subgroup.normalizer (A : Set G) ≤ M := Rem187QProof.normalizer_le hH.toSec18Std
  have hA3 : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using hC.planeQ8.isElemAbelian.2 x x.2)⟩
  have hAP : A ≤ P := SylowTop.le_of_isSylowOf (Subgroup.le_normalizer (H := A)) hA3 hP
  have hPM : P ≤ M := hP.le.trans hWM
  have hAM : A ≤ M := (Subgroup.le_normalizer (H := A)).trans hWM
  have hAT : A ⊓ (lc H c ⊓ Subgroup.normalizer (A : Set G)) =
      A ⊓ inSubgroup perfectResidual H := by
    rw [← inf_lc_eq h1812 h184 hH]
    refine le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right ?_))
    exact inf_le_left.trans (Subgroup.le_normalizer (H := A))
  have hBO := inf_oTwoP_eq_bot hC.planeQ8 hWM hnot
  have hcent := comm_oTwoP_of_planeQ8 hH.toSec18Std hC.planeQ8 hWM hAT hBO
  have hBe : IsElemAbelian 3 (A ⊓ inSubgroup perfectResidual H) :=
    isElemAbelian_of_le_elemAbelian inf_le_left hC.planeQ8.isElemAbelian
  have hB9 : Nat.card ↥(A ⊓ inSubgroup perfectResidual H) = 9 := hC.planeQ8.card_plane
  have hB3 : IsPGroup 3 ↥(A ⊓ inSubgroup perfectResidual H) := fun x =>
    ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  have hB1 : A ⊓ inSubgroup perfectResidual H ≠ ⊥ := fun h => hnot (by rw [h]; exact bot_le)
  have hBP : A ⊓ inSubgroup perfectResidual H ≤ P := inf_le_left.trans hAP
  have hBM : A ⊓ inSubgroup perfectResidual H ≤ M := inf_le_left.trans hAM
  have hBn : P ≤ Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) :=
    hP.le.trans hC.normalizer_le
  obtain ⟨K, hK, b, hb, k, hk, hnc⟩ :=
    exists_component hH.toSec18Std hC.sylow_G hBP hPM hB3 hB1 hBn hBO hBM hcent
  have hP3 : IsPGroup 3 P := hC.sylow_G.isPGroup
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_ncard_le_two hK hP3 hPM (ncard_conj_le_two hH.toSec18Std hK)
  have hirr := isIrreducibleOn_normalizer_inf hC hK
  have hnc' : ∃ b ∈ A ⊓ inSubgroup perfectResidual H, ∃ k ∈ K,
      b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := ⟨b, hb, k, hk, hnc⟩
  have hXB : Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) :=
    inf_le_left.trans hC.normalizer_le
  have hBS : A ⊓ inSubgroup perfectResidual H ≤
      Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (inf_le_left.trans (Subgroup.le_normalizer (H := A))) (hBP.trans hPK)
  have hSM : Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤ M :=
    inf_le_left.trans hWM
  obtain ⟨E, hEK, hEa, hE9⟩ := exists_nine_of_leafF1 hF1 hH.toSec18Std hK hBe hB9 hBM
    inf_le_right hXB hSM hBS hirr hnc'
  have h27 : ∀ E' ≤ P, IsElemAbelian 3 E' → Nat.card E' ≤ 27 := fun E' hE'P hE' =>
    card_le_of_le_M hH.toSec18Std (hE'P.trans hPM) hE'
  have hBK : A ⊓ inSubgroup perfectResidual H ≤ K :=
    le_of_pRank_gt_one hC.sylow_G (le_inf hC.sylow_W.le hPK) hBP hBe hB9 hXB hirr inf_le_right
      ⟨E, hEK, hEa, hE9⟩ h27
  have hWK : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) := fun w hw =>
    normalizer_le_normalizer_component hK hBK hnc' ⟨hWM hw, hC.normalizer_le hw⟩
  have hΩ := le_oTwoP_centralizer h1812 h184 h1842 hH
  have hfaith := faithful_P hC hK hWK hBK hnc' hΩ
  by_cases hin : InducesInnerMod c K (CFSG.Open.pCoreOf 2 K)
  · have hcP : c ∈ P := hAP hC.planeQ8.mem
    have hcK : c ∈ K := mem_of_inducesInner hC hK hPK hfaith c hcP hin
    have hAK : A ≤ K := by
      rw [hC.planeQ8.eq_sup]
      exact sup_le (Subgroup.zpowers_le.mpr hcK) hBK
    exact (false_of_inner hC hIn hK hWK hAK hfaith hΩ).elim
  · have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
      hWK (Subgroup.le_normalizer (H := A) hC.planeQ8.mem)
    exact hOut (K ⧸ CFSG.pCore 2 K) (rankHyp_of_mem hH.toSec18Std hK) _ _ _ _
      (outerData_of hC hK hWK hBK hfaith hcN hin hΩ)


section Leaves

theorem item185_of_leaves (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (h1846 : Item184_6) (hOut : LeafOuter) (hIn : LeafInner) : Item185 :=
  item185_of h1812 h184 h1842 h1846 Item185Proof.leafF1_holds hOut hIn

end Leaves

end CFSG.RankThree.PartTwo.Sec18
