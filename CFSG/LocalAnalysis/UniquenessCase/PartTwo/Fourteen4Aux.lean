module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Assembly.OrderReductions.PrimePart
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_isSylowOf {X I : Subgroup G} {q : ℕ} (hq : q.Prime) (hX : IsPGroup 3 X)
    (hI3 : ¬ 3 ∣ Nat.card I) (hXI : X ≤ normalizer (I : Set G)) :
    ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q I ∧ X ≤ normalizer (Q : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hbot : IsPGroup q (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hXbot : X ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨S, hS, -, hXS⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three hq hX hI3 hXI
      (bot_le : (⊥ : Subgroup G) ≤ I) hbot hXbot
  exact ⟨S, CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS, hXS⟩

private theorem isSylowOf_map_conj {I Q : Subgroup G} {n : G} {q : ℕ} (hq : q.Prime)
    (hn : n ∈ normalizer (I : Set G)) (hQ : CFSG.ABGLocalTools.IsSylowOf q Q I) :
    CFSG.ABGLocalTools.IsSylowOf q (Q.map (MulAut.conj n).toMonoidHom) I := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hQ ⊢
  obtain ⟨hQI, hQp, hQidx⟩ := hQ
  have hI : I.map (MulAut.conj n).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
  refine ⟨?_, hQp.map _, ?_⟩
  · rw [← hI]
    exact Subgroup.map_mono hQI
  · rw [← hI, Subgroup.relIndex_map_map_of_injective Q I (MulAut.conj n).injective]
    exact hQidx

theorem exists_mem_normalizer_acts_as {H I X Q : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hX : IsPGroup 3 X) (hI3 : ¬ 3 ∣ Nat.card I) (hIH : I ≤ H) (hHI : H ≤ normalizer (I : Set G))
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q I) (hXQ : X ≤ normalizer (Q : Set G)) {n : G}
    (hn : n ∈ H ⊓ normalizer (X : Set G))
    (hXI : X ≤ normalizer (I : Set G)) :
    ∃ m ∈ H ⊓ normalizer (Q : Set G) ⊓ normalizer (X : Set G),
      ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hnH : n ∈ H := hn.1
  have hnX : n ∈ normalizer (X : Set G) := hn.2
  have hnI : n ∈ normalizer (I : Set G) := hHI hnH
  have hQ' : CFSG.ABGLocalTools.IsSylowOf q (Q.map (MulAut.conj n).toMonoidHom) I :=
    isSylowOf_map_conj hq hnI hQ
  have hXQ' : X ≤ normalizer ((Q.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxn : n⁻¹ * x * n ∈ Subgroup.normalizer (Q : Set G) := by
      have hxinv : n⁻¹ * x * n ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1
          ((Subgroup.normalizer (X : Set G)).inv_mem hnX) x).1 hx
        simpa using this
      exact hXQ hxinv
    have h1 : y ∈ Q.map (MulAut.conj n).toMonoidHom ↔ (MulAut.conj n)⁻¹ y ∈ Q := by
      have h := Subgroup.mem_map_iff_mem (K := Q) (f := (MulAut.conj n).toMonoidHom)
        (MulAut.conj n).injective (x := (MulAut.conj n)⁻¹ y)
      rw [show (MulEquiv.toMonoidHom (MulAut.conj n)) ((MulAut.conj n)⁻¹ y) = y by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply]
        group] at h
      exact h
    have h2 : x * y * x⁻¹ ∈ Q.map (MulAut.conj n).toMonoidHom ↔
        (MulAut.conj n)⁻¹ (x * y * x⁻¹) ∈ Q := by
      have h := Subgroup.mem_map_iff_mem (K := Q) (f := (MulAut.conj n).toMonoidHom)
        (MulAut.conj n).injective (x := (MulAut.conj n)⁻¹ (x * y * x⁻¹))
      rw [show (MulEquiv.toMonoidHom (MulAut.conj n)) ((MulAut.conj n)⁻¹ (x * y * x⁻¹))
          = x * y * x⁻¹ by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply]
        group] at h
      exact h
    rw [h1, h2]
    have hkey : (MulAut.conj n)⁻¹ (x * y * x⁻¹) =
        (n⁻¹ * x * n) * ((MulAut.conj n)⁻¹ y) * (n⁻¹ * x * n)⁻¹ := by
      rw [MulAut.conj_inv_apply, MulAut.conj_inv_apply]
      group
    rw [hkey]
    exact Subgroup.mem_normalizer_iff.1 hxn ((MulAut.conj n)⁻¹ y)
  have hS : fusionIsSylowIn q Q I := by
    obtain ⟨S, rfl⟩ := hQ
    exact CFSG.Goldschmidt.G310.fusionIsSylowIn_map S
  have hS' : fusionIsSylowIn q (Q.map (MulAut.conj n).toMonoidHom) I := by
    obtain ⟨S, hS⟩ := hQ'
    rw [← hS]
    exact CFSG.Goldschmidt.G310.fusionIsSylowIn_map S
  obtain ⟨c, hc, hcQ⟩ :=
    CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three hq hX hI3 hXI
      hS hS' hXQ hXQ'
  have hcI : c ∈ I := hc.1
  have hcC : c ∈ Subgroup.centralizer (X : Set G) := hc.2
  have hcX : c ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) hcC
  have hcH : c ∈ H := hIH hcI
  set m : G := c⁻¹ * n with hm
  have hmH : m ∈ H := H.mul_mem (H.inv_mem hcH) hnH
  have hmX : m ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).inv_mem hcX) hnX
  have hmQ : m ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hmul : m * y * m⁻¹ = c⁻¹ * (n * y * n⁻¹) * c := by rw [hm]; group
    rw [hmul]
    have hmem_n : y ∈ Q ↔ n * y * n⁻¹ ∈ Q.map (MulAut.conj n) := by
      have := Subgroup.mem_map_iff_mem (K := Q) (f := (MulAut.conj n : MulAut G).toMonoidHom)
        (MulAut.conj n).injective (x := y)
      simpa [MulAut.conj_apply] using this.symm
    have hmem_c : c⁻¹ * (n * y * n⁻¹) * c ∈ Q ↔
        n * y * n⁻¹ ∈ Q.map (MulAut.conj c) := by
      have := Subgroup.mem_map_iff_mem (K := Q) (f := (MulAut.conj c : MulAut G).toMonoidHom)
        (MulAut.conj c).injective (x := c⁻¹ * (n * y * n⁻¹) * c)
      have hval : (MulEquiv.toMonoidHom (MulAut.conj c)) (c⁻¹ * (n * y * n⁻¹) * c) =
          n * y * n⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hval] at this
      exact this.symm
    rw [hmem_c, hmem_n]
    exact Iff.of_eq (congrArg (fun S : Subgroup G => n * y * n⁻¹ ∈ S) hcQ)
  have hact : ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹ := by
    intro x hx
    have hy : n * x * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hnX x).1 hx
    have hcomm : (n * x * n⁻¹) * c = c * (n * x * n⁻¹) := hcC (n * x * n⁻¹) hy
    calc m * x * m⁻¹
        = c⁻¹ * (n * x * n⁻¹) * c := by rw [hm]; group
      _ = c⁻¹ * ((n * x * n⁻¹) * c) := by group
      _ = c⁻¹ * (c * (n * x * n⁻¹)) := by rw [hcomm]
      _ = n * x * n⁻¹ := by group
  exact ⟨m, ⟨⟨hmH, hmQ⟩, hmX⟩, hact⟩

theorem exists_sylow_not_le {H I M X : Subgroup G} (hIH : I ≤ H) (hHI : H ≤ normalizer (I : Set G))
    (hX : IsPGroup 3 X) (hI3 : ¬ 3 ∣ Nat.card I) (hXI : X ≤ normalizer (I : Set G))
    (hodd : Odd (M.relIndex H)) (hIM : ¬ I ≤ M) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧
      ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q I ∧ X ≤ normalizer (Q : Set G) ∧
        ¬ Q ≤ M := by
  by_contra hcon
  push_neg at hcon
  have hI2 : Odd (M.relIndex I) := by
    have hI'norm : (I.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 hHI
    haveI : (I.subgroupOf H).Normal := hI'norm
    have hdvd : (M.subgroupOf H).relIndex ((I.subgroupOf H) ⊔ (M.subgroupOf H)) ∣ M.relIndex H := by
      have := Subgroup.relIndex_dvd_index_of_le (H := M.subgroupOf H)
        (K := (I.subgroupOf H) ⊔ (M.subgroupOf H)) le_sup_right
      rwa [show (M.subgroupOf H).index = M.relIndex H from rfl] at this
    have heq : M.relIndex I =
        (M.subgroupOf H).relIndex ((I.subgroupOf H) ⊔ (M.subgroupOf H)) := by
      rw [← Subgroup.relIndex_subgroupOf hIH]
      exact (CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (I.subgroupOf H)
        (M.subgroupOf H)).symm
    rw [heq]
    exact Odd.of_dvd_nat hodd hdvd
  have htop : M.subgroupOf I = ⊤ := by
    apply CFSG.OrderReductions.PrimePart.eq_top_of_contains_sylow_for_every_prime
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := ↥I)
      refine ⟨S, ?_⟩
      have hcard : Nat.card S = 1 := by
        rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hI3, pow_zero]
      rw [Subgroup.eq_bot_of_card_eq (S : Subgroup ↥I) hcard]
      exact bot_le
    · by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (I ⊓ M)
        rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS₀
        obtain ⟨hS₀le, hS₀p, hS₀idx⟩ := hS₀
        have hS₀I : CFSG.ABGLocalTools.IsSylowOf 2 S₀ I := by
          rw [CFSG.ABGLocalTools.isSylowOf_iff]
          refine ⟨hS₀le.trans inf_le_left, hS₀p, ?_⟩
          have hrelI : S₀.relIndex I =
              S₀.relIndex (I ⊓ M) * (I ⊓ M).relIndex I :=
            (Subgroup.relIndex_mul_relIndex S₀ (I ⊓ M) I hS₀le inf_le_left).symm
          rw [hrelI, Subgroup.inf_relIndex_left I M]
          have hodd2 : ¬ 2 ∣ M.relIndex I := by
            rintro ⟨k, hk⟩
            obtain ⟨j, hj⟩ := hI2
            omega
          exact Nat.Prime.not_dvd_mul Nat.prime_two hS₀idx hodd2
        obtain ⟨S, hS⟩ := hS₀I
        refine ⟨S, ?_⟩
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        have hyS₀ : (y : G) ∈ S₀ := by
          have : (y : G) ∈ (S : Subgroup ↥I).map I.subtype :=
            Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
          rwa [hS] at this
        exact (hS₀le hyS₀).2
      · obtain ⟨Q, hQ, hXQ⟩ := exists_invariant_isSylowOf hp hX hI3 hXI
        obtain ⟨S, hS⟩ := hQ
        refine ⟨S, ?_⟩
        have hQM : Q ≤ M := hcon p hp hp2 hp3 Q ⟨S, hS⟩ hXQ
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        have hyQ : (y : G) ∈ Q := by
          have : (y : G) ∈ (S : Subgroup ↥I).map I.subtype :=
            Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
          rwa [hS] at this
        exact hQM hyQ
  apply hIM
  intro x hx
  have : (⟨x, hx⟩ : ↥I) ∈ M.subgroupOf I := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_elemAbelian_char {Q : Subgroup G} {q : ℕ} (hq : q.Prime) (hQ : IsPGroup q Q)
    (hQ1 : Q ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ Q ∧ IsElemAbelian q V ∧ V ≠ ⊥ ∧
      ∀ g ∈ normalizer (Q : Set G), g ∈ normalizer (V : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  let V : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ (∀ y ∈ Q, x * y = y * x) ∧ x ^ q = 1}
      one_mem' := by
        refine ⟨Q.one_mem, ?_, one_pow q⟩
        intro y hy
        simp
      mul_mem' := by
        rintro x x' ⟨hxQ, hxc, hxq⟩ ⟨hx'Q, hx'c, hx'q⟩
        refine ⟨Q.mul_mem hxQ hx'Q, ?_, ?_⟩
        · intro y hy
          calc (x * x') * y = x * (x' * y) := by group
            _ = x * (y * x') := by rw [hx'c y hy]
            _ = (x * y) * x' := by group
            _ = (y * x) * x' := by rw [hxc y hy]
            _ = y * (x * x') := by group
        · have hcomm : Commute x x' := (hx'c x hxQ).symm
          rw [hcomm.mul_pow, hxq, hx'q, mul_one]
      inv_mem' := by
        rintro x ⟨hxQ, hxc, hxq⟩
        refine ⟨Q.inv_mem hxQ, ?_, ?_⟩
        · intro y hy
          calc x⁻¹ * y = (y⁻¹ * x)⁻¹ := by group
            _ = (x * y⁻¹)⁻¹ := by rw [hxc y⁻¹ (Q.inv_mem hy)]
            _ = y * x⁻¹ := by group
        · rw [inv_pow, hxq, inv_one] }
  have hVQ : V ≤ Q := fun x hx => hx.1
  have hVea : IsElemAbelian q V := by
    refine ⟨?_, ?_⟩
    · exact ⟨⟨fun a b => Subtype.ext (a.2.2.1 b.1 b.2.1)⟩⟩
    · intro x hx
      exact hx.2.2
  have hVne : V ≠ ⊥ := by
    haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
    let Z : Subgroup ↥Q := Subgroup.center ↥Q
    haveI : Nontrivial ↥Z := hQ.center_nontrivial
    have hZne : Z ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot Z).mp inferInstance
    have hZcard : Nat.card ↥Z ≠ 1 := fun h => hZne (Subgroup.eq_bot_of_card_eq Z h)
    have hZq : IsPGroup q ↥Z := hQ.to_subgroup Z
    have hqZ : q ∣ Nat.card ↥Z := (hZq.card_eq_or_dvd).resolve_left hZcard
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqZ
    let v : G := (z : ↥Q)
    have hvo : orderOf v = q := by
      rw [show v = ((z : ↥Q) : G) from rfl]
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hvV : v ∈ V := by
      refine ⟨z.1.2, ?_, ?_⟩
      · intro y hy
        exact congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp z.2 (⟨y, hy⟩ : ↥Q)).symm)
      · rw [← orderOf_dvd_iff_pow_eq_one, hvo]
    have hv1 : v ≠ 1 := by
      intro h
      have hone : orderOf v = 1 := by rw [h]; exact orderOf_one
      rw [hvo] at hone
      exact hq.ne_one hone
    intro hbot
    have : v ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hvV
    exact hv1 (Subgroup.mem_bot.mp this)
  refine ⟨V, hVQ, hVea, hVne, ?_⟩
  have hconj : ∀ g ∈ normalizer (Q : Set G), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v ⟨hvQ, hvc, hvq⟩
    have hgvQ : g * v * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg v).1 hvQ
    refine ⟨hgvQ, ?_, ?_⟩
    · intro y hy
      have hgyQ : g⁻¹ * y * g ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1
          ((Subgroup.normalizer (Q : Set G)).inv_mem hg) y).1 hy
        simpa using this
      have hcomm := hvc (g⁻¹ * y * g) hgyQ
      calc (g * v * g⁻¹) * y = g * (v * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * v) * g⁻¹ := by rw [hcomm]
        _ = y * (g * v * g⁻¹) := by group
    · rw [← MulAut.conj_apply g v, ← map_pow, hvq, map_one]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact hconj g hg v hv
  · intro hv
    have hginv : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hg
    have := hconj g⁻¹ hginv (g * v * g⁻¹) hv
    simpa [mul_assoc] using this

theorem card_le_pow_of_pRank_le {q r : ℕ} (hq : q.Prime) {V K : Subgroup G}
    (hV : IsElemAbelian q V) (hVK : V ≤ K) (hr : Open.pRank q K ≤ r) : Nat.card V ≤ q ^ r := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hVq : IsPGroup q ↥V := by
    intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hV.2 (g : G) g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hVq
  have hk_le : k ≤ Open.pRank q K := CFSG.SectionRank.le_pRank hq.one_lt hVK hV hk
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos (hk_le.trans hr)

theorem lt_inf_normalizer {q : ℕ} (hq : q.Prime) {Q W : Subgroup G} (hQ : IsPGroup q Q)
    (hWQ : W < Q) : W < Q ⊓ normalizer (W : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have h1 : W.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hWQ.not_ge h
  obtain ⟨⟨y, hyQ⟩, hy1, hy2⟩ :=
    SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (W.subgroupOf Q) h1)
  have hWQ' : W ≤ Q := hWQ.le
  have hy3 : y ∈ normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact (Subgroup.mem_normalizer_iff.1 hy1 ⟨z, hWQ' hz⟩).1 hz
    · intro hz
      have hzQ : z ∈ Q := by
        have h5 : y⁻¹ * (y * z * y⁻¹) * y ∈ Q :=
          Q.mul_mem (Q.mul_mem (Q.inv_mem hyQ) (hWQ' hz)) hyQ
        simpa [mul_assoc] using h5
      exact (Subgroup.mem_normalizer_iff.1 hy1 ⟨z, hzQ⟩).2 hz
  refine lt_of_le_of_ne (le_inf hWQ' Subgroup.le_normalizer) ?_
  intro heq
  apply hy2
  have : y ∈ Q ⊓ normalizer (W : Set G) := ⟨hyQ, hy3⟩
  rw [← heq] at this
  exact this

theorem rankThreePrimeCore_facts (H : Subgroup G) :
    rankThreePrimeCore 3 H ≤ H ∧ H ≤ normalizer ((rankThreePrimeCore 3 H : Subgroup G) : Set G) ∧
      ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 H) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hle : rankThreePrimeCore 3 H ≤ H := relPPrimeCore_le H
  refine ⟨hle, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 (relPPrimeCore_normal hp H)
  · exact (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_relPPrimeCore hp H)

theorem pCoreOf_ne_bot_of_fstar {H : Subgroup G} (hF : Fstar H = pCoreOf 2 H) (hH : H ≠ ⊥) :
    pCoreOf 2 H ≠ ⊥ := by
  intro h0
  rw [h0] at hF
  have h1 : CFSG.Open.genFittingFStar ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 hF
  have h2 := CFSG.Adapters.generalized_fitting_self_centralizing ↥H
  rw [h1] at h2
  apply hH
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥H) ∈ Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y = 1 := hy
    rw [this]; simp
  have := h2 hx'
  have h3 : (⟨x, hx⟩ : ↥H) = 1 := by simpa using this
  have h4 : x = 1 := congrArg Subtype.val h3
  simp [h4]

theorem exists_isMaxTwoLocal_ge_of_fstar {H : Subgroup G} (hF : Fstar H = pCoreOf 2 H)
    (hH : H ≠ ⊥) : ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  have hne : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_fstar hF hH
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  set S : Set (Subgroup G) := {K | IsTwoLocal K ∧ Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ K}
    with hS
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ :=
    Set.exists_max_image S (fun K => Nat.card K) (Set.toFinite S) ⟨_, hloc, le_rfl⟩
  refine ⟨M, ⟨hM, fun K hK hMK => ?_⟩,
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans hHM⟩
  exact (Subgroup.eq_of_le_of_card_ge hMK (hmax K ⟨hK, hHM.trans hMK⟩)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
