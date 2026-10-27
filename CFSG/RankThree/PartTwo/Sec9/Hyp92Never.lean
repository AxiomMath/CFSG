module

public import CFSG.RankThree.PartTwo.Sec9.Item93
public import CFSG.RankThree.PartTwo.Sec10.Item102
public import CFSG.RankThree.PartTwo.Sec11.Item116Points
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
public import CFSG.RankThree.PartTwo.Sec9.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def SLPiInndiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), 1 ≤ n →
    Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) →
    ∃ D : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)),
      (∀ σ τ : MulAut (L ⧸ aschbacherSolvableCore 3 L), σ * τ * σ⁻¹ * τ⁻¹ ∈ D) ∧
      (∀ x : G, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
        KFacts.InducesStdKind L x .inner ∨ KFacts.InducesStdKind L x .diagonal →
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hx⟩) ∈ D) ∧
      (∀ x : G, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
        KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField →
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hx⟩) ∉ D)

@[expose] def SLPiSylowFixed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsSLThreePiAt X (2 ^ (3 * n)) →
    ∀ (T : Sylow 3 X) (ζ : MulAut X), ζ ^ 3 = 1 → (∀ t ∈ (T : Subgroup X), ζ t = t) → ζ = 1

@[expose] def SLPiFieldSylowFixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), 1 ≤ n →
    Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) →
    ∀ (a : G) (haN : a ∈ Subgroup.normalizer (L : Set G)), a ^ 3 = 1 →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) →
      ∀ T : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
        IsSylowOf 3 T (Sec8.barCentralizer (Subgroup.zpowers a) L) →
      ∀ ζ : MulAut (L ⧸ aschbacherSolvableCore 3 L), ζ ^ 3 = 1 → (∀ t ∈ T, ζ t = t) →
        ζ ∈ Subgroup.zpowers (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩))

@[expose] def TransferExtremal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (N : Subgroup G),
    (∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ N) →
    ∀ x ∈ (P : Subgroup G), x ∉ N → x ^ p = 1 →
    (∀ g : G, (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x},
        g⁻¹ * y * g ∈ (P : Subgroup G)) → x⁻¹ * (g⁻¹ * x * g) ∈ N) →
    commutator G ≠ ⊤

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_commute_of_maximal {A : Subgroup G} (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) {z : G}
    (hz3 : z ^ 3 = 1) (hzA : ∀ x ∈ A, z * x = x * z) : z ∈ A := by
  set D := Subgroup.zpowers z with hD
  have hDN : D ≤ Subgroup.normalizer (A : Set G) := by
    rw [hD, Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => (hzA g hg).symm)
  have hdecomp : ∀ y ∈ A ⊔ D, ∃ w ∈ D, ∃ u ∈ A, w * u = y := by
    intro y hy
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D A hDN] at hy
    obtain ⟨w, hw, u, hu, rfl⟩ := hy
    exact ⟨w, hw, u, hu, rfl⟩
  have hcommD : ∀ w ∈ D, ∀ u ∈ A, w * u = u * w := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((show Commute z u from hzA u hu).zpow_left k).eq
  have hDexp : ∀ w ∈ D, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hDcomm : ∀ w ∈ D, ∀ w' ∈ D, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (Commute.zpow_zpow_self z k k').eq
  have hAcomm : ∀ u ∈ A, ∀ u' ∈ A, u * u' = u' * u := fun u hu u' hu' =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
  have hel : CFSG.Assembly.IsElemAbelian 3 (A ⊔ D) := by
    refine ⟨⟨⟨fun y y' => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨w, hw, u, hu, hwu⟩ := hdecomp y y.2
      obtain ⟨w', hw', u', hu', hwu'⟩ := hdecomp y' y'.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hwu, ← hwu']
      have h1 : Commute (w * u) (w' * u') := by
        apply Commute.mul_left
        · exact (show Commute w w' from hDcomm w hw w' hw').mul_right
            (show Commute w u' from hcommD w hw u' hu')
        · exact (show Commute u w' from (hcommD w' hw' u hu).symm).mul_right
            (show Commute u u' from hAcomm u hu u' hu')
      exact h1.eq
    · obtain ⟨w, hw, u, hu, rfl⟩ := hdecomp y hy
      rw [(show Commute w u from hcommD w hw u hu).mul_pow, hDexp w hw, hAel.2 u hu, one_mul]
  have hAD := hAmax _ hel le_sup_left
  rw [← hAD]
  exact (le_sup_right : D ≤ A ⊔ D) (Subgroup.mem_zpowers _)

theorem thetaQuotMulAut_apply_eq_of_commute {L X : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.normalizer (L : Set G)) (hzX : ∀ s ∈ X, z * s = s * z) :
    ∀ t ∈ Sec8.imageModTheta L X, Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨z, hz⟩) t = t := by
  rintro _ ⟨⟨s, hsL⟩, hs, rfl⟩
  rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  change z * s * z⁻¹ = s
  rw [hzX s (Subgroup.mem_subgroupOf.mp hs), mul_inv_cancel_right]

theorem isSylowOf_imageModTheta {L X Y : Subgroup G} (hXY : IsSylowOf 3 X Y) (hYL : Y ≤ L) :
    IsSylowOf 3 (Sec8.imageModTheta L X) (Sec8.imageModTheta L Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXL : X ≤ L := hXY.le.trans hYL
  have h1 : IsSylowOf 3 (X.subgroupOf L) (Y.subgroupOf L) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hXL, inf_of_le_left hYL]
    exact hXY
  exact Sec12.IsSylowOf.map h1 _

theorem exists_sylow_coe_eq {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (h : IsSylowOf p P ⊤) : ∃ Q : Sylow p X, (Q : Subgroup X) = P :=
  ⟨Sylow.ofCard P (by rw [h.card_eq, Subgroup.card_top]), Sylow.coe_ofCard _ _⟩

end General

section Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G} {n : ℕ}

theorem Hyp92.one_le (h : Hyp92 G A c L a R n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    obtain ⟨K, _, _, h1 | h1⟩ := h.isSLThreePiAt
    · have h2 : 1 < Nat.card K := Finite.one_lt_card
      rw [h1.1] at h2
      norm_num at h2
    · norm_num at h1
  · exact hn

theorem Hyp92.mem_zpowers_of_eq_one (h : Hyp92 G A c L a R n) {x : G} (hxA : x ∈ A)
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hx⟩) = 1) :
    x ∈ Subgroup.zpowers c := by
  have hz : x ∈ Sec4.thetaQuotCentralizer L := ⟨⟨x, hx⟩, h1, rfl⟩
  have h2 := Sec11.mem_sectionCentralizer_of_mem_thetaQuotCentralizer hxA hz
  rw [h.sectionCentralizer_eq] at h2
  exact h2

end Hyp

theorem hyp92Never_of (h95 : Item95) (hNL : Hyp92NormalizerL) (hK1 : SLPiInndiag)
    (hK2 : SLPiSylowFixed) (hK3 : SLPiFieldSylowFixed) (hT : TransferExtremal) :
    Hyp92Never := by
  intro G _ _ A c L a R n h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := h.one_le
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hAmax := h.mem_partTwoF.2.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAel.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hcA := h.mem_A
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have haA := h.a_mem
  have ha3 : a ^ 3 = 1 := hexp a haA
  have haN := h.a_mem_normalizer
  have hAR : A ≤ R := Sec10.le_of_hyp91 h.toHyp91
  have hHL := hNL G A c L a R n h
  have hc3 : ∀ g : G, (g * c * g⁻¹) ^ 3 = 1 := fun g => by
    rw [conj_pow, hexp c hcA, mul_one, mul_inv_cancel]
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c)
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := fun x hx => hHL (hCH (hAC hx))
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  obtain ⟨D, hDc, hDin, hDout⟩ := hK1 G L n hn h.isSLThreePiAt
  set α := ρ ⟨a, haN⟩ with hα
  have hαD : α ∉ D := hDout a haN h.inducesStdKind
  have hρ3 : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
      ρ ⟨x, hx⟩ ^ 3 = 1 := by
    intro x hx hx3
    rw [← map_pow]
    have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hα3 : α ^ 3 = 1 := hρ3 a haN ha3
  have hαpow : ∀ ζ ∈ Subgroup.zpowers α, ζ ∈ D → ζ = 1 := by
    intro ζ hζ hζD
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
    have hα3' : α ^ (3 : ℤ) = 1 := by exact_mod_cast hα3
    rw [zpow_eq_zpow_emod k hα3'] at hζD ⊢
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with hk | hk | hk <;> rw [hk] at hζD ⊢
    · rfl
    · exact absurd (by simpa using hζD) hαD
    · exfalso
      apply hαD
      have h1 : α = (α ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hα3', mul_one,
          zpow_one]
      rw [h1]
      exact D.zpow_mem hζD 2
  have hkey : ∀ (g : G) (hgA : g * c * g⁻¹ ∈ A),
      ρ ⟨g * c * g⁻¹, hAL hgA⟩ ∈ Subgroup.zpowers α → g * c * g⁻¹ ∈ Subgroup.zpowers c := by
    intro g hgA hgα
    have hkind := h95 G A c L a R n h g (hAR hgA)
    have hD := hDin _ (hAL hgA) hkind
    exact h.mem_zpowers_of_eq_one hgA (hAL hgA) (hαpow _ hgα hD)
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  have hACa : A ≤ Ca := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a haA)
  have hK : L ⊓ Ca ≤ Ca ⊓ Cc := fun x hx => ⟨hx.2, hLC hx.1⟩
  have hKN : Ca ⊓ Cc ≤ Subgroup.normalizer ((L ⊓ Ca : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxL := hHL (hCH hx.2)
    have hxCa : x ∈ Subgroup.normalizer (Ca : Set G) := Subgroup.le_normalizer hx.1
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxL y).mp hy1,
        (Subgroup.mem_normalizer_iff.mp hxCa y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxL y).mpr hy1,
        (Subgroup.mem_normalizer_iff.mp hxCa y).mpr hy2⟩
  have hbar : ∀ S : Subgroup G, IsSylowOf 3 S (Ca ⊓ Cc) →
      IsSylowOf 3 (Sec8.imageModTheta L (S ⊓ (L ⊓ Ca)))
        (Sec8.barCentralizer (Subgroup.zpowers a) L) := by
    intro S hS
    have h1 := isSylowOf_imageModTheta (hS.inf_of_le_normalizer hK hKN)
      (inf_le_left : L ⊓ Ca ≤ L)
    rwa [KFacts.imageModTheta_centralizer_eq haN ⟨1, by simpa using ha3⟩] at h1
  have hfix3 : ∀ S : Subgroup G, IsSylowOf 3 S (Ca ⊓ Cc) → ∀ (z : G) (hzA : z ∈ A),
      (∀ s ∈ S, z * s = s * z) → ρ ⟨z, hAL hzA⟩ ∈ Subgroup.zpowers α := by
    intro S hS z hzA hzS
    exact hK3 G L n hn h.isSLThreePiAt a haN ha3 h.inducesStdKind _ (hbar S hS) _
      (hρ3 z (hAL hzA) (hexp z hzA))
      (thetaQuotMulAut_apply_eq_of_commute (hAL hzA) (fun s hs => hzS s hs.1))
  obtain ⟨S, hS, hAS⟩ := Sec11.exists_isSylowOf_ge hA3 (le_inf hACa hAC)
  obtain ⟨E, hE, hSE⟩ := Sec11.exists_isSylowOf_ge hS.isPGroup (hS.le.trans inf_le_left)
  have hE3 : IsPGroup 3 E := hE.isPGroup
  have hECc : E ≤ Cc := by
    by_contra hcon
    have hES : E ⊓ Cc = S := hS.eq_of_le (le_inf hSE (hS.le.trans inf_le_right))
      (inf_le_inf_right _ hE.le) (hE3.to_le inf_le_left)
    obtain ⟨y, hyE, hyS, hyc⟩ : ∃ y ∈ E, (∀ s ∈ S, y⁻¹ * s * y ∈ S) ∧ y ∉ Cc := by
      have hnil : Group.IsNilpotent E := hE3.isNilpotent
      have hlt : S.subgroupOf E < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        apply hcon
        intro x hxE
        have hx : (⟨x, hxE⟩ : E) ∈ S.subgroupOf E := htop ▸ Subgroup.mem_top _
        exact (hS.le.trans inf_le_right) (Subgroup.mem_subgroupOf.mp hx)
      have hlt2 := Group.normalizerCondition_of_isNilpotent (G := E) _ hlt
      obtain ⟨y', hy'N, hy'S⟩ := IsConcreteLE.exists_of_lt hlt2
      refine ⟨y', y'.2, fun s hs => ?_, fun hyc => hy'S ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy'N) ⟨s, hSE hs⟩).mp
          (Subgroup.mem_subgroupOf.mpr hs)
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [Subgroup.mem_subgroupOf, ← hES]
        exact ⟨y'.2, hyc⟩
    have hc'S : ∀ s ∈ S, y * c * y⁻¹ * s = s * (y * c * y⁻¹) := by
      intro s hs
      have h2 : (y⁻¹ * s * y) * c = c * (y⁻¹ * s * y) :=
        Subgroup.mem_centralizer_singleton_iff.mp ((hS.le.trans inf_le_right) (hyS s hs))
      calc y * c * y⁻¹ * s = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by rw [h2]
        _ = s * (y * c * y⁻¹) := by group
    have hc'A : y * c * y⁻¹ ∈ A :=
      mem_of_commute_of_maximal hAel hAmax (hc3 y) (fun x hx => hc'S x (hAS hx))
    have hc'c := hkey y hc'A (hfix3 S hS _ hc'A hc'S)
    obtain ⟨k, hk⟩ := hE3 ⟨y, hyE⟩
    have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hyc (Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec12.commute_of_conj_mem_zpowers hco hc'c hk'))
  obtain ⟨P, hP, hEP⟩ := Sec11.exists_isSylowOf_ge hE3 (hECc.trans hCH)
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPC : P ≤ Cc := Sec11.le_centralizer_of_le_normalizer_zpowers hco hP3 hP.le
  have hAP : A ≤ P := hAS.trans (hSE.trans hEP)
  have hcP : c ∈ P := hAP hcA
  have haP : a ∈ P := hAP haA
  have hPL : P ≤ Subgroup.normalizer (L : Set G) := hP.le.trans hHL
  have hcZ : ∀ x ∈ P, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
  have hZP : ∀ z ∈ P, z ^ 3 = 1 → (∀ x ∈ P, z * x = x * z) → z ∈ Subgroup.zpowers c := by
    intro z hzP hz3 hzZ
    have hzA : z ∈ A := mem_of_commute_of_maximal hAel hAmax hz3 (fun x hx => hzZ x (hAP hx))
    apply h.mem_zpowers_of_eq_one hzA (hAL hzA)
    have hPL' : IsSylowOf 3 (P ⊓ L) L := hP.inf_of_le_normalizer (hLC.trans hCH) hHL
    have h1 := isSylowOf_imageModTheta hPL' le_rfl
    have htop : Sec8.imageModTheta L L = ⊤ := by
      rw [Sec8.imageModTheta, Subgroup.subgroupOf_self]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [htop] at h1
    obtain ⟨T, hT⟩ := exists_sylow_coe_eq h1
    refine hK2 _ n hn h.isSLThreePiAt T _ (hρ3 z (hAL hzA) hz3) ?_
    intro t ht
    rw [hT] at ht
    exact thetaQuotMulAut_apply_eq_of_commute (X := P ⊓ L) (hAL hzA)
      (fun s hs => hzZ s (Subgroup.mem_inf.mp hs).1) t ht
  have hPG : IsSylowOf 3 P ⊤ := by
    refine Sec12.isSylowOf_of_normalizer_le hP le_top ?_
    rintro g ⟨-, hg⟩
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    refine hZP _ ((Subgroup.mem_normalizer_iff.mp hg c).mp hcP) (hc3 g) ?_
    intro x hx
    have h1 : g⁻¹ * x * g ∈ P := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using h2
    have h2 := hcZ _ h1
    calc g * c * g⁻¹ * x = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [h2]
      _ = x * (g * c * g⁻¹) := by group
  obtain ⟨PS, hPS⟩ := exists_sylow_coe_eq hPG
  have hCPa : P ⊓ Ca = E := hE.eq_of_le (le_inf hEP hE.le) inf_le_right (hP3.to_le inf_le_left)
  set N : Subgroup G := (D.comap ρ).map (Subgroup.normalizer (L : Set G)).subtype with hN
  have htop : commutator G = ⊤ := by
    have hG := h.toTheoremFourHyp
    have := hG.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h1 | h1
    · obtain ⟨x, y, hxy⟩ := hG.nonabelian
      exact absurd ((commutator_eq_bot_iff G).mp h1) fun hc => hxy (hc.is_comm.comm x y)
    · exact h1
  refine hT G 3 PS N ?_ a (hPS ▸ haP) ?_ ha3 ?_ htop
  · intro y hy z hz
    rw [hPS] at hy hz
    refine ⟨⟨y, hPL hy⟩ * ⟨z, hPL hz⟩ * ⟨y, hPL hy⟩⁻¹ * ⟨z, hPL hz⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hDc _ _
  · rintro ⟨⟨a', ha'⟩, h1, h2⟩
    change a' = a at h2
    subst h2
    exact hαD h1
  · intro g hg
    rw [hPS, hCPa] at hg
    have hbP : g⁻¹ * a * g ∈ P := hg a (hSE (hAS haA))
    have hX'le : (P ⊓ Subgroup.centralizer {g⁻¹ * a * g}).map (MulAut.conj g).toMonoidHom ≤
        Ca := by
      rintro _ ⟨x, hx, rfl⟩
      have hxb := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
      rw [hCa, Subgroup.mem_centralizer_singleton_iff]
      change g * x * g⁻¹ * a = a * (g * x * g⁻¹)
      calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [hxb]
        _ = a * (g * x * g⁻¹) := by group
    have hEX' : E ≤ (P ⊓ Subgroup.centralizer {g⁻¹ * a * g}).map
        (MulAut.conj g).toMonoidHom := by
      intro y hy
      refine ⟨g⁻¹ * y * g, Subgroup.mem_inf.mpr ⟨hg y hy, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hE.le hy)
        calc g⁻¹ * y * g * (g⁻¹ * a * g) = g⁻¹ * (y * a) * g := by group
          _ = g⁻¹ * (a * y) * g := by rw [hya]
          _ = g⁻¹ * a * g * (g⁻¹ * y * g) := by group
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
    have hX'E := hE.eq_of_le hEX' hX'le ((hP3.to_le inf_le_left).map _)
    have hgcE : g * c * g⁻¹ ∈ E := by
      rw [← hX'E]
      refine ⟨c, Subgroup.mem_inf.mpr ⟨hcP, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcZ _ hbP).symm
    have hgcZ : ∀ s ∈ E, g * c * g⁻¹ * s = s * (g * c * g⁻¹) := by
      intro s hs
      have h2 := hcZ _ (hg s hs)
      calc g * c * g⁻¹ * s = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by rw [h2]
        _ = s * (g * c * g⁻¹) := by group
    have hgcA : g * c * g⁻¹ ∈ A :=
      mem_of_commute_of_maximal hAel hAmax (hc3 g) (fun x hx => hgcZ x (hSE (hAS hx)))
    have hEac : IsSylowOf 3 E (Ca ⊓ Cc) := hE.of_le (le_inf hE.le hECc) inf_le_left
    have hgcc := hkey g hgcA (hfix3 E hEac _ hgcA hgcZ)
    have hgL := hHL (Sec10.mem_normalizer_zpowers_of_conj_mem hgcc)
    refine ⟨⟨a, haN⟩⁻¹ * (⟨g, hgL⟩⁻¹ * ⟨a, haN⟩ * ⟨g, hgL⟩), ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := hDc α⁻¹ (ρ ⟨g, hgL⟩)⁻¹
    simpa [mul_assoc] using h1

end CFSG.RankThree.PartTwo.Sec9
