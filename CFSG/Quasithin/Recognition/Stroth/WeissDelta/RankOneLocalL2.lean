module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalL22
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ShultStronglyClosedTI.LinearModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace L2

variable {X Ω : Type} [Group X] [MulAction X Ω] {N : Subgroup X} {m : ℕ}

private theorem natCard_subtype_ne_two {α : Type*} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    Nat.card {x : α // x ≠ a ∧ x ≠ b} = Nat.card α - 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun x : α => x ≠ a ∧ x ≠ b) =
      (Finset.univ.erase a).erase b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [h,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Nat.card_eq_fintype_card]
  omega

private theorem eq_of_isPGroup_of_normal_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H P Q : Subgroup G} (hPleH : P ≤ H)
    (hP2 : IsPGroup p P) (hPnorm : (P.subgroupOf H).Normal)
    (hPnotdvd : ¬ p ∣ P.relIndex H) (hQleH : Q ≤ H)
    (hQ2 : IsPGroup p Q) (hQcard : Nat.card Q = Nat.card P) : Q = P := by
  let P_H : Subgroup H := P.subgroupOf H
  have hP2H : IsPGroup p P_H :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPleH).symm
  let SP : Sylow p H := hP2H.toSylow (by simpa [Subgroup.relIndex] using hPnotdvd)
  have hSPcoe : (SP : Subgroup H) = P_H := IsPGroup.toSylow_coe hP2H _
  have hSPnorm : SP.Normal := by
    change (SP : Subgroup H).Normal
    rw [hSPcoe]
    exact hPnorm
  let Q_H : Subgroup H := Q.subgroupOf H
  have hQ2H : IsPGroup p Q_H :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQleH).symm
  have hHnorm : H ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleH).mp hPnorm
  have hQnormSP : Q_H ≤ Subgroup.normalizer (SP : Subgroup H) := by
    intro q hq
    rw [hSPcoe]
    have hqnorm : q ∈ (Subgroup.normalizer P).subgroupOf H := hHnorm q.2
    rwa [Subgroup.subgroupOf_normalizer_eq hPleH] at hqnorm
  have hQinf : Q_H = Q_H ⊓ (SP : Subgroup H) := by
    calc
      Q_H = Q_H ⊓ Subgroup.normalizer (SP : Subgroup H) :=
        (inf_eq_left.mpr hQnormSP).symm
      _ = Q_H ⊓ (SP : Subgroup H) := IsPGroup.inf_normalizer_sylow hQ2H SP
  have hQleP : Q ≤ P := by
    intro q hq
    let qH : H := ⟨q, hQleH hq⟩
    have hqH : qH ∈ Q_H := hq
    have hqP : qH ∈ P_H := by
      have hqinf : qH ∈ Q_H ⊓ (SP : Subgroup H) := hQinf ▸ hqH
      exact (Subgroup.mem_inf.mp hqinf).2
    exact hqP
  exact Subgroup.eq_of_le_of_card_ge hQleP (by rw [hQcard])



private theorem root_exists (S : L2Setup X Ω N m) (hm : 2 ≤ m) [Finite X] [Fintype Ω]
    [N.Normal] (ω : Ω) :
    ∃ R : Subgroup X, R ≤ MulAction.stabilizer X ω ∧
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal ∧ IsPGroup 2 R ∧
      ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β := by
  classical
  obtain ⟨r, hp, hr⟩ := S.exists_borel_conj ω
  let H : Subgroup ↥N := S.B.map (MulAut.conj r).toMonoidHom
  let R : Subgroup ↥N := S.U.map (MulAut.conj r).toMonoidHom
  have hRleH : R ≤ H := Subgroup.map_mono S.hUleB
  have hR2 : IsPGroup 2 R := S.hU2.map (MulAut.conj r).toMonoidHom
  have hRcard : Nat.card R = 2 ^ m := by
    rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, S.hUcard]
  have hHcard : Nat.card H = 2 ^ m * (2 ^ m - 1) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, S.hBcard]
  have hRnormH : (R.subgroupOf H).Normal := by
    have hconj : ∀ b ∈ H, ∀ q ∈ R, b * q * b⁻¹ ∈ R := by
      intro b hb q hq
      rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
      rcases Subgroup.mem_map.mp hq with ⟨u, hu, rfl⟩
      have hmem : b₀ * u * b₀⁻¹ ∈ S.U :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normal_subgroupOf_iff_le_normalizer S.hUleB).mp S.hUnorm hb₀) u).mp hu
      exact Subgroup.mem_map.mpr ⟨b₀ * u * b₀⁻¹, hmem, by simp [mul_assoc]⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRleH]
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hconj b hb q hq
    · intro hq
      have hq' : b⁻¹ * (b * q * b⁻¹) * (b⁻¹)⁻¹ ∈ R :=
        hconj b⁻¹ (H.inv_mem hb) (b * q * b⁻¹) hq
      simpa [mul_assoc] using hq'
  have hrel : R.relIndex H = 2 ^ m - 1 := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := H)
    rw [inf_eq_left.mpr hRleH, hRcard, hHcard] at h
    have hqpos : 0 < 2 ^ m := pow_pos (by norm_num : (0 : ℕ) < 2) m
    apply Nat.eq_of_mul_eq_mul_right hqpos
    calc
      R.relIndex H * 2 ^ m = 2 ^ m * (2 ^ m - 1) := h
      _ = (2 ^ m - 1) * 2 ^ m := by rw [mul_comm]
  have hodd : Odd (R.relIndex H) := by
    rw [hrel]
    exact mersenne_odd.mpr (by omega)
  have hnotdvd : ¬ 2 ∣ R.relIndex H := fun hdvd =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  let R_X : Subgroup X := R.map N.subtype
  have hR_X2 : IsPGroup 2 R_X := hR2.map N.subtype
  have hRXle : R_X ≤ MulAction.stabilizer X ω := by
    have hRleSub : R ≤ (MulAction.stabilizer X ω).subgroupOf N := by
      rw [hr]
      exact hRleH
    calc
      R_X = R.map N.subtype := rfl
      _ ≤ ((MulAction.stabilizer X ω).subgroupOf N).map N.subtype :=
        Subgroup.map_mono hRleSub
      _ = MulAction.stabilizer X ω ⊓ N := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ MulAction.stabilizer X ω := inf_le_left
  have hsem : ∀ (n : R_X) (x : Ω), x ≠ ω → (n : X) • x = x → n = 1 := by
    intro n x hx hfix
    rcases Subgroup.mem_map.mp n.2 with ⟨nN, hnN, hnEq⟩
    have hfixN : nN • x = x := by
      change (N.subtype nN) • x = x
      rw [hnEq]
      exact hfix
    let p : PSL2MatrixGroup (L2K m) := S.e r
    let a : ℙ (L2K m) (Fin 2 → (L2K m)) := S.theta x
    have ha : a ≠ p • psl2ProjectiveInfinity (L2K m) := by
      intro h
      apply hx
      apply S.theta.injective
      rw [show S.theta x = a from rfl, h, hp]
    have hn_image : S.e nN ∈ (psl2UpperUnipotentSubgroup (L2K m)).map
        (MulAut.conj p).toMonoidHom := by
      rw [← S.map_root r]
      exact Subgroup.mem_map_of_mem S.e.toMonoidHom hnN
    obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hn_image
    have hthetafix : (S.e nN) • a = a := by
      calc
        (S.e nN) • a = S.theta (nN • x) := (S.theta_smul nN x).symm
        _ = S.theta x := by rw [hfixN]
        _ = a := rfl
    have hueq' : p * u * p⁻¹ = S.e nN := by
      simpa [MulAut.conj_apply] using hueq
    have hu_fix : u • (p⁻¹ • a) = p⁻¹ • a := by
      have h := congrArg (fun z => p⁻¹ • z) hthetafix
      rw [← hueq'] at h
      simpa [mul_smul] using h
    have ha' : p⁻¹ • a ≠ psl2ProjectiveInfinity (L2K m) := by
      intro h
      apply ha
      calc
        a = p • (p⁻¹ • a) := by simp
        _ = p • psl2ProjectiveInfinity (L2K m) := by rw [h]
    let u₀ : psl2UpperUnipotentSubgroup (L2K m) := ⟨u, hu⟩
    have hu_fix₀ : u₀ • (p⁻¹ • a) = p⁻¹ • a := hu_fix
    have hone : (1 : psl2UpperUnipotentSubgroup (L2K m)) • (p⁻¹ • a) = p⁻¹ • a :=
      one_smul _ _
    have hu0 : u₀ = 1 :=
      (S.model.regular (p⁻¹ • a) (p⁻¹ • a) ha' ha').unique hu_fix₀ hone
    have hu1 : u = 1 := congrArg Subtype.val hu0
    have he1 : S.e nN = 1 := by
      rw [← hueq, hu1]
      simp
    have hnN1 : nN = 1 := S.e.injective (by simpa using he1)
    apply Subtype.ext
    rw [← hnEq, hnN1]
    rfl
  have hregular : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R_X, (r : X) • α = β := by
    intro α β hα hβ
    have hΩcard : Fintype.card Ω = 2 ^ m + 1 := by
      rw [← Nat.card_eq_fintype_card]
      calc
        Nat.card Ω = Nat.card (ℙ (L2K m) (Fin 2 → (L2K m))) :=
          Nat.card_congr S.theta
        _ = 2 ^ m + 1 := S.model.card_eq
    have hRXcard : Nat.card R_X = 2 ^ m := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, hRcard]
    let f : R_X → Ω := fun n => (n : X) • α
    have hf : Function.Injective f := by
      intro n m h
      have hfix : ((m⁻¹ * n : R_X) : X) • α = α := by
        have h' : (n : X) • α = (m : X) • α := by simpa [f] using h
        calc
          ((m⁻¹ * n : R_X) : X) • α = (m⁻¹ : X) • ((n : X) • α) := by
            simp [Subgroup.coe_mul, mul_smul]
          _ = (m⁻¹ : X) • ((m : X) • α) := by rw [← h']
          _ = α := by simp [← mul_smul]
      have h1 := hsem (m⁻¹ * n) α hα hfix
      have hmul : n = m := by
        calc
          n = m * (m⁻¹ * n) := by group
          _ = m * 1 := by rw [h1]
          _ = m := mul_one m
      exact hmul
    have horbit : (Set.range f).ncard = Nat.card R_X :=
      Set.ncard_range_of_injective hf
    have hcomp : (Set.univ \ {ω} : Set Ω).ncard = Nat.card R_X := by
      rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ ω), Set.ncard_univ,
        Nat.card_eq_fintype_card, hΩcard, hRXcard]
      omega
    have hsubset : Set.range f ⊆ (Set.univ \ {ω} : Set Ω) := by
      rintro _ ⟨n, rfl⟩
      refine ⟨Set.mem_univ _, ?_⟩
      intro hnω
      have hnω' : (n : X) • α = ω := by simpa [f] using hnω
      have hnfix : (n : X) • ω = ω :=
        (MulAction.mem_stabilizer_iff.mp (hRXle n.2))
      have : (n : X) • α = (n : X) • ω := by rw [hnω', hnfix]
      exact hα (MulAction.injective (n : X) this)
    have heq : Set.range f = (Set.univ \ {ω} : Set Ω) :=
      Set.eq_of_subset_of_ncard_le hsubset (by rw [hcomp, horbit])
    have hβmem : β ∈ (Set.univ \ {ω} : Set Ω) := ⟨Set.mem_univ _, hβ⟩
    obtain ⟨n, hn⟩ := Set.mem_range.mp (by rw [heq]; exact hβmem)
    refine ⟨n, by simpa [f] using hn, ?_⟩
    intro m hm
    apply hf
    simpa [f] using hm.trans hn.symm
  have hRXnorm : (R_X.subgroupOf (MulAction.stabilizer X ω)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRXle]
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    let φ := MulAut.conjNormal (H := N) x
    let Q : Subgroup ↥N := R.map φ.toMonoidHom
    have hHinv : ∀ n : ↥N, n ∈ H → φ n ∈ H := by
      intro n hn
      have hH_eq : H = (MulAction.stabilizer X ω).subgroupOf N := hr.symm
      rw [hH_eq] at hn ⊢
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [MulAction.mem_stabilizer_iff] at hn ⊢
      have hxfix : x • ω = ω := MulAction.mem_stabilizer_iff.mp hx
      have hxinv : x⁻¹ • ω = ω := by
        have := congrArg (fun z => x⁻¹ • z) hxfix
        simpa using this.symm
      change (x : X) * (n : X) * x⁻¹ ∈ MulAction.stabilizer X ω
      rw [MulAction.mem_stabilizer_iff]
      calc
        (x * (n : X) * x⁻¹) • ω = (x * (n : X)) • (x⁻¹ • ω) := by
          rw [mul_smul]
        _ = x • ((n : X) • (x⁻¹ • ω)) := by rw [mul_smul]
        _ = x • ((n : X) • ω) := by rw [hxinv]
        _ = x • ω := by rw [hn]
        _ = ω := hxfix
    have hQleH : Q ≤ H := by
      intro q hq
      rcases Subgroup.mem_map.mp hq with ⟨n, hn, rfl⟩
      exact hHinv n (hRleH hn)
    have hQcard : Nat.card Q = Nat.card R :=
      Subgroup.card_map_of_injective φ.injective
    have hQeq : Q = R :=
      eq_of_isPGroup_of_normal_sylow hRleH hR2 hRnormH hnotdvd hQleH
        (hR2.map φ.toMonoidHom) hQcard
    have hcomp : (MulAut.conj x).toMonoidHom.comp N.subtype =
        N.subtype.comp φ.toMonoidHom := by
      ext n
      change x * (n : X) * x⁻¹ = (x * (n : X) * x⁻¹ : X)
      rfl
    have hmap1 : R_X.map (MulAut.conj x).toMonoidHom = Q.map N.subtype := by
      rw [show R_X = R.map N.subtype from rfl, Subgroup.map_map, hcomp,
        show Q = R.map φ.toMonoidHom from rfl, ← Subgroup.map_map]
    have hmap : R_X.map (MulAut.conj x).toMonoidHom = R_X :=
      hmap1.trans (by rw [hQeq])
    exact hmap
  exact ⟨R_X, hRXle, hRXnorm, hR_X2, hregular⟩

private theorem pair_eq_stabilizer_inf (S : L2Setup X Ω N m) {ω ω' : Ω} :
    (N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
      (MulAction.stabilizer ↥N ω ⊓ MulAction.stabilizer ↥N ω').map N.subtype := by
  ext x
  constructor
  · rintro ⟨⟨hxN, hxω⟩, hxω'⟩
    exact ⟨⟨x, hxN⟩, ⟨by simpa using hxω, by simpa using hxω'⟩, rfl⟩
  · rintro ⟨n, ⟨hnω, hnω'⟩, rfl⟩
    exact ⟨⟨n.2, hnω⟩, hnω'⟩

private theorem exists_torus_conj_X (S : L2Setup X Ω N m) {ω ω' : Ω} (hne : ω ≠ ω') :
    ∃ r : ↥N, (N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
      (S.T.map (MulAut.conj r).toMonoidHom).map N.subtype := by
  obtain ⟨r, hr⟩ := S.exists_torus_conj hne
  refine ⟨r, ?_⟩
  rw [pair_eq_stabilizer_inf S, hr]

private theorem odd_closure_aux (S : L2Setup X Ω N m) (hm : 2 ≤ m) [Finite X] [Fintype Ω]
    [N.Normal] (hXNCyc : IsCyclic (X ⧸ N)) {ω ω' : Ω} (hne : ω ≠ ω')
    (Sset : Set X)
    (hSsub : Sset ⊆ ↑(MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'))
    (hSodd : ∀ s ∈ Sset, Odd (orderOf s)) :
    Odd (Nat.card ↥(Subgroup.closure Sset)) := by
  classical
  let Y : Subgroup X := MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  let Tp : Subgroup X := N ⊓ Y
  have hTp_le_Y : Tp ≤ Y := by dsimp [Tp]; exact inf_le_right
  have hTpOdd : Odd (Nat.card (Tp.subgroupOf Y)) := by
    obtain ⟨r, hr⟩ := exists_torus_conj_X S hne
    have hTp_eq : Tp = (S.T.map (MulAut.conj r).toMonoidHom).map N.subtype := by
      simpa [Tp, Y, inf_assoc] using hr
    have hcardTp : Nat.card Tp = 2 ^ m - 1 := by
      rw [hTp_eq, Subgroup.card_map_of_injective N.subtype_injective,
        Subgroup.card_map_of_injective (MulAut.conj r).injective, S.hTcard]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTp_le_Y).toEquiv, hcardTp]
    exact mersenne_odd.mpr (by omega)
  have hTpnorm : (Tp.subgroupOf Y).Normal := by
    have hconj : ∀ y ∈ Y, ∀ x ∈ Tp, y * x * y⁻¹ ∈ Tp := by
      intro y hy x hx
      exact ⟨(inferInstance : N.Normal).conj_mem x hx.1 y,
        Y.mul_mem (Y.mul_mem hy hx.2) (Y.inv_mem hy)⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTp_le_Y]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj y hy x hx
    · intro hx
      have hx' : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ ∈ Tp :=
        hconj y⁻¹ (Y.inv_mem hy) (y * x * y⁻¹) hx
      simpa [mul_assoc] using hx'
  let f : Y →* X ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hker : f.ker = Tp.subgroupOf Y := by
    ext y
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Tp, Y,
      Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨h, y.2.1, y.2.2⟩
    · rintro ⟨h, -, -⟩
      exact h
  have hquot : IsCyclic (Y ⧸ Tp.subgroupOf Y) := by
    haveI : IsCyclic (X ⧸ N) := hXNCyc
    have hYker : IsCyclic (Y ⧸ f.ker) :=
      isCyclic_of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
    exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.mp hYker
  have hcyc : ∀ P : Sylow 2 Y, IsCyclic (P : Subgroup Y) :=
    CFSG.GH74.Uniqueness.Bender.isCyclic_sylow_of_quotient (Tp.subgroupOf Y)
      hTpOdd hquot
  obtain ⟨A, hAodd, hAmem⟩ :=
    CFSG.OddStandard.SmallF3.Omega.exists_subgroup_odd_elems Y hcyc
  have hcl_le : Subgroup.closure Sset ≤ A := by
    rw [Subgroup.closure_le]
    intro s hs
    exact (hAmem s).mpr ⟨hSsub hs, hSodd s hs⟩
  exact Odd.of_dvd_nat hAodd (Subgroup.card_dvd_of_le hcl_le)

private theorem regular_on_complement [Finite Ω] [Fintype Ω] {Tp : Subgroup X}
    {ω ω' : Ω} (hne : ω ≠ ω')
    (hTω : Tp ≤ MulAction.stabilizer X ω)
    (hTω' : Tp ≤ MulAction.stabilizer X ω')
    (hcardT : Nat.card Tp = 2 ^ m - 1)
    (hfix : ∀ t ∈ Tp, t ≠ 1 → ∀ x : Ω, t • x = x → x = ω ∨ x = ω')
    (hΩcard : Fintype.card Ω = 2 ^ m + 1) :
    ∀ x y : Ω, x ≠ ω → x ≠ ω' → y ≠ ω → y ≠ ω' →
      ∃! t : Tp, (t : X) • x = y := by
  classical
  let C := {x : Ω // x ≠ ω ∧ x ≠ ω'}
  haveI : Finite Ω := Finite.of_fintype Ω
  haveI : Fintype C := Fintype.ofFinite C
  have hCcard : Nat.card C = Nat.card Tp := by
    change Nat.card {x : Ω // x ≠ ω ∧ x ≠ ω'} = Nat.card Tp
    rw [natCard_subtype_ne_two hne, Nat.card_eq_fintype_card, hΩcard, hcardT]
    omega
  intro x y hx hx' hy hy'
  let f : Tp → C := fun t =>
    ⟨(t : X) • x, by
      constructor
      · intro h
        apply hx
        have htω : (t : X) • ω = ω := hTω t.2
        calc
          x = (t : X)⁻¹ • ((t : X) • x) := by simp
          _ = (t : X)⁻¹ • ω := by rw [h]
          _ = ω := by
            simpa using (congrArg (fun z => (t : X)⁻¹ • z) htω).symm
      · intro h
        apply hx'
        have htω' : (t : X) • ω' = ω' := hTω' t.2
        calc
          x = (t : X)⁻¹ • ((t : X) • x) := by simp
          _ = (t : X)⁻¹ • ω' := by rw [h]
          _ = ω' := by
            simpa using (congrArg (fun z => (t : X)⁻¹ • z) htω').symm⟩
  have hf : Function.Injective f := by
    intro t s hts
    by_contra htsne
    have hfixpoint : (s⁻¹ * t : Tp) • x = x := by
      have h := congrArg Subtype.val hts
      simp only [f] at h
      calc
        ((s⁻¹ * t : Tp) : X) • x = (s : X)⁻¹ • ((t : X) • x) := by
          simp [Subgroup.coe_mul, mul_smul]
        _ = (s : X)⁻¹ • ((s : X) • x) := by rw [h]
        _ = x := by simp
    have hbad := hfix (s⁻¹ * t) (Tp.mul_mem (Tp.inv_mem s.2) t.2)
      (by
        intro h1
        apply htsne
        have h1' : s⁻¹ * t = 1 := Subtype.ext (by simpa using h1)
        calc
          t = s * (s⁻¹ * t) := by group
          _ = s * 1 := by rw [h1']
          _ = s := mul_one s) x hfixpoint
    rcases hbad with h | h
    · exact hx h
    · exact hx' h
  have hrange : Set.range f = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_range_of_injective hf, Set.ncard_univ, hCcard]
  let xC : C := ⟨x, hx, hx'⟩
  let yC : C := ⟨y, hy, hy'⟩
  have hyrange : yC ∈ Set.range f := by rw [hrange]; exact Set.mem_univ yC
  obtain ⟨t, ht⟩ := hyrange
  refine ⟨t, ?_, ?_⟩
  · simpa [f, xC, yC] using congrArg Subtype.val ht
  · intro s hs
    apply hf
    apply Subtype.ext
    have htval : (t : X) • x = y := congrArg Subtype.val ht
    simpa [f, xC, yC] using hs.trans htval.symm

private theorem rankOneLocal_and_zassenhaus_psl2_core {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* PSL2MatrixGroup (L2K m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    RankOneLocal X Ω N ∧ RankOneZassenhaus X Ω N := by
  classical
  letI : N.Normal := hN
  obtain ⟨S⟩ := exists_l2Setup h2 m hm N hN e hΩ
  have hKcard : Nat.card (L2K m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hq4 : 4 ≤ Nat.card (L2K m) := by
    rw [hKcard]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : IsSimpleGroup (PSL2MatrixGroup (L2K m)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
  have hPperf : Group.IsPerfect (PSL2MatrixGroup (L2K m)) :=
    psl2_isPerfect_of_card_gt_three (L2K m) (by rw [hKcard]; omega)
  have hNperf : Group.IsPerfect ↥N := by
    haveI : Group.IsPerfect (PSL2MatrixGroup (L2K m)) := hPperf
    have hmap : Group.IsPerfect
        ((⊤ : Subgroup (PSL2MatrixGroup (L2K m))).map e.symm.toMonoidHom) :=
      Group.IsPerfect.map _
    rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
    exact Group.IsPerfect.top_iff.mp hmap
  haveI : Nontrivial ↥N := e.toEquiv.nontrivial
  have hNnotcomm : ¬ IsMulCommutative ↥N := Group.IsPerfect.not_isMulCommutative ↥N
  have hcent : Subgroup.centralizer (N : Set X) = ⊥ :=
    centralizer_eq_bot_of_isMultiplyPretransitive hNnotcomm h2
  have hBender : CFSG.GH74.Uniqueness.Bender.BenderType ↥N m 1 1 :=
    CFSG.GH74.Uniqueness.Bender.BenderType.linear m hm e
  have hOutCyc : IsCyclic (Outer ↥N) :=
    (CFSG.GH74.Uniqueness.Bender.BenderType.outer_linear hBender).1
  haveI : IsCyclic (Outer ↥N) := hOutCyc
  let φ : X ⧸ N →* Outer ↥N :=
    QuotientGroup.lift N (CFSG.RankThree.PartOne.CTP.outerHom N)
      (fun _ hg => (MonoidHom.mem_ker
        (f := CFSG.RankThree.PartOne.CTP.outerHom N)).mp
        ((CFSG.RankThree.PartOne.CTP.ker_outerHom N hcent).symm ▸ hg))
  have hφinj : Function.Injective φ :=
    CFSG.RankThree.PartOne.CTP.quotientOuterHom_injective N hcent
  have hXNCyc : IsCyclic (X ⧸ N) := isCyclic_of_injective φ hφinj
  have hperfect : CFSG.perfectResidual X = N := by
    apply le_antisymm
    · haveI : IsCyclic (X ⧸ N) := hXNCyc
      have hSolv : Group.IsSolvable (X ⧸ N) := inferInstance
      open CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension in
      exact perfectResidual_le_of_isSolvable_quotient hSolv
    · exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual N hNperf
  have hTorusCard : ∀ {ω ω' : Ω}, ω ≠ ω' →
      Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
        2 ^ m - 1 := by
    intro ω ω' hne
    obtain ⟨r, hr⟩ := exists_torus_conj_X S hne
    rw [hr, Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj r).injective, S.hTcard]
  have hTorusConj : ∀ {ω ω' : Ω}, ω ≠ ω' →
      ∃ r : ↥N, (N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
        (S.T.map (MulAut.conj r).toMonoidHom).map N.subtype := by
    intro ω ω' hne
    exact exists_torus_conj_X S hne
  have hRoot : ∀ ω : Ω, ∃ R : Subgroup X, R ≤ MulAction.stabilizer X ω ∧
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal ∧ IsPGroup 2 R ∧
      ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β :=
    fun ω => root_exists S hm ω
  have hTorusOdd : ∀ ω ω' : Ω, ω ≠ ω' →
      Odd (Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω')) := by
    intro ω ω' hne
    rw [hTorusCard hne]
    exact mersenne_odd.mpr (by omega)
  have hTorusFix : ∀ ω ω' ω'' : Ω, ω ≠ ω' →
      (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        t • ω'' = ω'') → ω'' = ω ∨ ω'' = ω' := by
    intro ω ω' ω'' hne hall
    let Tp : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
    have hcardTp : Nat.card Tp = 2 ^ m - 1 := hTorusCard hne
    have hTne : Tp ≠ ⊥ := by
      refine (Subgroup.one_lt_card_iff_ne_bot (H := Tp)).mp ?_
      rw [hcardTp]
      have hq4' : 4 ≤ 2 ^ m := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hTne
    have htT : (t : X) ∈ Tp := t.2
    have htN : (t : X) ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT).1).1
    let tN : ↥N := ⟨t, htN⟩
    have htN1 : tN ≠ 1 := by
      intro h
      apply ht1
      have htX : (t : X) = 1 := congrArg Subtype.val h
      exact Subtype.ext htX
    have htω : tN • ω = ω := by
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT).1).2
    have htω' : tN • ω' = ω' := (Subgroup.mem_inf.mp htT).2
    have htfix : tN • ω'' = ω'' := hall t htT
    exact S.eq_two_of_fixed (t := tN) htN1 htω htω' hne ω'' htfix
  have hTorusCyclic : ∀ ω ω' : Ω, ω ≠ ω' →
      IsCyclic ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') := by
    intro ω ω' hne
    obtain ⟨r, hr⟩ := exists_torus_conj_X S hne
    rw [hr]
    haveI : IsCyclic ↥S.T := S.hTcyc
    let e₁ : ↥S.T ≃* ↥(S.T.map (MulAut.conj r).toMonoidHom) :=
      Subgroup.equivMapOfInjective S.T (MulAut.conj r).toMonoidHom
        (MulAut.conj r).injective
    haveI : IsCyclic ↥(S.T.map (MulAut.conj r).toMonoidHom) :=
      isCyclic_of_surjective e₁.toMonoidHom e₁.surjective
    let e₂ : ↥(S.T.map (MulAut.conj r).toMonoidHom) ≃*
        ↥((S.T.map (MulAut.conj r).toMonoidHom).map N.subtype) :=
      Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective
    exact isCyclic_of_surjective e₂.toMonoidHom e₂.surjective
  have hOddClosure : ∀ ω ω' : Ω, ω ≠ ω' → ∀ Sset : Set X,
      Sset ⊆ ↑(MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') →
      (∀ s ∈ Sset, Odd (orderOf s)) →
      Odd (Nat.card ↥(Subgroup.closure Sset)) :=
    fun ω ω' hne => odd_closure_aux S hm hXNCyc hne
  have hFixTwo : ∀ ω ω' : Ω, ω ≠ ω' →
      ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        t ≠ 1 → ∀ ω'', t • ω'' = ω'' → ω'' = ω ∨ ω'' = ω' := by
    intro ω ω' hne t htT ht1 ω'' hfix
    have htN : t ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT).1).1
    let tN : ↥N := ⟨t, htN⟩
    have htN1 : tN ≠ 1 := by
      intro h
      apply ht1
      exact congrArg Subtype.val h
    have htω : tN • ω = ω := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT).1).2
    have htω' : tN • ω' = ω' := (Subgroup.mem_inf.mp htT).2
    exact S.eq_two_of_fixed (t := tN) htN1 htω htω' hne ω'' hfix
  have hCentralizer : ∀ ω ω' : Ω, ω ≠ ω' →
      ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
          g * t = t * g) → g ∈ N := by
    intro ω ω' hne g hg hcomm
    let Tp : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
    have hTleN : Tp ≤ N := by
      intro t ht
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
    have hTω : Tp ≤ MulAction.stabilizer X ω := by
      intro t ht
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).2
    have hTω' : Tp ≤ MulAction.stabilizer X ω' := by
      intro t ht
      exact (Subgroup.mem_inf.mp ht).2
    have hfixT : ∀ t ∈ Tp, t ≠ 1 → ∀ x : Ω, t • x = x → x = ω ∨ x = ω' := by
      intro t htT ht1 x hx
      have htN : t ∈ N := hTleN htT
      let tN : ↥N := ⟨t, htN⟩
      have htN1 : tN ≠ 1 := by
        intro h
        apply ht1
        exact congrArg Subtype.val h
      have htω : tN • ω = ω := hTω htT
      have htω' : tN • ω' = ω' := hTω' htT
      exact S.eq_two_of_fixed (t := tN) htN1 htω htω' hne x hx
    have hreg := regular_on_complement (m := m) hne hTω hTω'
      (hTorusCard hne) hfixT (by
        rw [← Nat.card_eq_fintype_card]
        calc
          Nat.card Ω = Nat.card (ℙ (L2K m) (Fin 2 → (L2K m))) :=
            Nat.card_congr S.theta
          _ = 2 ^ m + 1 := S.model.card_eq)
    haveI : Nonempty {x : Ω // x ≠ ω ∧ x ≠ ω'} := by
      apply Fintype.card_pos_iff.mp
      rw [← Nat.card_eq_fintype_card, natCard_subtype_ne_two hne,
        Nat.card_eq_fintype_card]
      have hΩcard : Fintype.card Ω = 2 ^ m + 1 := by
        rw [← Nat.card_eq_fintype_card]
        calc
          Nat.card Ω = Nat.card (ℙ (L2K m) (Fin 2 → (L2K m))) :=
            Nat.card_congr S.theta
          _ = 2 ^ m + 1 := S.model.card_eq
      rw [hΩcard]
      have hq4' : 4 ≤ 2 ^ m := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    let γ₀ : {x : Ω // x ≠ ω ∧ x ≠ ω'} := Classical.arbitrary _
    have hγ₀ : (γ₀ : Ω) ≠ ω ∧ (γ₀ : Ω) ≠ ω' := γ₀.2
    have hgω : g • ω = ω := hg.1
    have hgω' : g • ω' = ω' := hg.2
    let δ : {x : Ω // x ≠ ω ∧ x ≠ ω'} :=
      ⟨g • γ₀, by
        constructor
        · intro h
          apply hγ₀.1
          calc
            (γ₀ : Ω) = g⁻¹ • (g • γ₀) := by simp
            _ = g⁻¹ • ω := by rw [h]
            _ = ω := by
              simpa using (congrArg (fun z => g⁻¹ • z) hgω).symm
        · intro h
          apply hγ₀.2
          calc
            (γ₀ : Ω) = g⁻¹ • (g • γ₀) := by simp
            _ = g⁻¹ • ω' := by rw [h]
            _ = ω' := by
              simpa using (congrArg (fun z => g⁻¹ • z) hgω').symm⟩
    obtain ⟨t, ht, -⟩ := hreg γ₀ δ hγ₀.1 hγ₀.2 δ.2.1 δ.2.2
    have htT : (t : X) ∈ Tp := t.2
    let h : X := (t : X)⁻¹ * g
    have htδ : (t : X) • (γ₀ : Ω) = g • (γ₀ : Ω) := by
      simpa [δ] using ht
    have hhγ₀ : h • (γ₀ : Ω) = γ₀ := by
      calc
        h • (γ₀ : Ω) = ((t : X)⁻¹ * g) • (γ₀ : Ω) := rfl
        _ = (t : X)⁻¹ • (g • (γ₀ : Ω)) := by rw [mul_smul]
        _ = (t : X)⁻¹ • ((t : X) • (γ₀ : Ω)) := by rw [htδ]
        _ = (γ₀ : Ω) := by simp
    haveI : IsMulCommutative Tp := (hTorusCyclic ω ω' hne).isMulCommutative
    have hcommT : ∀ u ∈ Tp, h * u = u * h := by
      intro u hu
      let uT : Tp := ⟨u, hu⟩
      have htu : (t : X) * u = u * (t : X) := by
        have h := (IsMulCommutative.is_comm (M := Tp)).comm t uT
        exact congrArg Subtype.val h
      have htu_inv : (t : X)⁻¹ * u = u * (t : X)⁻¹ :=
        (show Commute (t : X) u from htu).inv_left.eq
      calc
        h * u = (t : X)⁻¹ * (g * u) := by
          rw [show h = (t : X)⁻¹ * g from rfl]
          group
        _ = (t : X)⁻¹ * (u * g) := by rw [hcomm u hu]
        _ = ((t : X)⁻¹ * u) * g := by group
        _ = (u * (t : X)⁻¹) * g := by rw [htu_inv]
        _ = u * ((t : X)⁻¹ * g) := by group
        _ = u * h := by rw [show h = (t : X)⁻¹ * g from rfl]
    have hfixAll : ∀ x : Ω, h • x = x := by
      intro x
      by_cases hxω : x = ω
      · rw [hxω]
        have htω : (t : X) • ω = ω := hTω htT
        have hgω : g • ω = ω := hg.1
        calc
          h • ω = (t : X)⁻¹ • (g • ω) := by
            rw [show h = (t : X)⁻¹ * g from rfl, mul_smul]
          _ = (t : X)⁻¹ • ω := by rw [hgω]
          _ = ω := by
            simpa using (congrArg (fun z => (t : X)⁻¹ • z) htω).symm
      · by_cases hxω' : x = ω'
        · rw [hxω']
          have htω' : (t : X) • ω' = ω' := hTω' htT
          have hgω' : g • ω' = ω' := hg.2
          calc
            h • ω' = (t : X)⁻¹ • (g • ω') := by
              rw [show h = (t : X)⁻¹ * g from rfl, mul_smul]
            _ = (t : X)⁻¹ • ω' := by rw [hgω']
            _ = ω' := by
              simpa using (congrArg (fun z => (t : X)⁻¹ • z) htω').symm
        · obtain ⟨s, hs, -⟩ := hreg (γ₀ : Ω) x hγ₀.1 hγ₀.2 hxω hxω'
          have hsT : (s : X) ∈ Tp := s.2
          calc
            h • x = h • ((s : X) • (γ₀ : Ω)) := by rw [← hs]
            _ = (h * (s : X)) • (γ₀ : Ω) := by rw [← mul_smul]
            _ = ((s : X) * h) • (γ₀ : Ω) := by rw [hcommT s hsT]
            _ = (s : X) • (h • (γ₀ : Ω)) := by rw [← mul_smul]
            _ = (s : X) • (γ₀ : Ω) := by rw [hhγ₀]
            _ = x := hs
    have hh1 : h = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
      intro x
      rw [hfixAll x, one_smul]
    have hg_eq_t : g = (t : X) := by
      calc
        g = (t : X) * h := by
          rw [show h = (t : X)⁻¹ * g from rfl]
          group
        _ = (t : X) * 1 := by rw [hh1]
        _ = (t : X) := mul_one _
    rw [hg_eq_t]
    exact hTleN htT
  refine ⟨?_, ?_⟩
  · refine ⟨hRoot, hTorusOdd, hTorusFix, hTorusCyclic, hOddClosure, hperfect⟩
  · refine ⟨hFixTwo, hCentralizer⟩

end L2

theorem rankOneLocal_psl2 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    RankOneLocal X Ω N :=
  (L2.rankOneLocal_and_zassenhaus_psl2_core h2 m hm N hN e hΩ).1

theorem rankOneZassenhaus_psl2 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    RankOneZassenhaus X Ω N :=
  (L2.rankOneLocal_and_zassenhaus_psl2_core h2 m hm N hN e hΩ).2

end CFSG.Quasithin.Stroth.WeissDelta
