module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

private lemma le_sylow_of_le_normalizer {K : Type*} [Group K] {p : ℕ}
    {P : Subgroup K} (hP : IsPGroup p P) (S : Sylow p K)
    (h : P ≤ Subgroup.normalizer (S : Set K)) : P ≤ (S : Subgroup K) := by
  have hinf := hP.inf_normalizer_sylow S
  rw [inf_eq_left.mpr h] at hinf
  exact inf_eq_left.mp hinf.symm

private lemma mem_sylow_of_mem_normalizer {K : Type*} [Group K] {p : ℕ}
    {R S : Sylow p K} {r : K} (hr : r ∈ (R : Subgroup K))
    (hrn : r ∈ Subgroup.normalizer (S : Set K)) : r ∈ (S : Subgroup K) :=
  le_sylow_of_le_normalizer (R.isPGroup'.to_le (Subgroup.zpowers_le.mpr hr)) S
    (Subgroup.zpowers_le.mpr hrn) (Subgroup.mem_zpowers r)

private lemma mem_conj_smul_sylow_iff {K : Type*} [Group K] {p : ℕ} {x g : K}
    {S : Sylow p K} :
    g ∈ ((x • S : Sylow p K) : Subgroup K) ↔ x⁻¹ * g * x ∈ (S : Subgroup K) := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private lemma natCard_sylow_ne {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (T : Sylow p K) (hcount : Nat.card (Sylow p K) = Nat.card (T : Subgroup K) + 1) :
    Nat.card {U : Sylow p K // U ≠ T} = Nat.card (T : Subgroup K) := by
  haveI : Fintype (Sylow p K) := Fintype.ofFinite _
  haveI : Fintype {U : Sylow p K // U ≠ T} := Fintype.ofFinite _
  haveI : Fintype {U : Sylow p K // U = T} := Fintype.ofFinite _
  haveI : Fintype (T : Subgroup K) := Fintype.ofFinite _
  have hc : Fintype.card (Sylow p K) = Fintype.card (T : Subgroup K) + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun U => U = T),
    Fintype.card_subtype_eq, Nat.card_eq_fintype_card, hc]
  exact Nat.add_sub_cancel _ _

private lemma exists_ne_one_smul_eq_self_of_card_lt {Q Ω : Type*} [Group Q] [MulAction Q Ω]
    [Finite Q] [Finite Ω] (ω : Ω) (hcard : Nat.card Ω < Nat.card Q) :
    ∃ q : Q, q ≠ 1 ∧ q • ω = ω := by
  by_contra hcon
  have hfix : ∀ q : Q, q • ω = ω → q = 1 := by
    intro q hq
    by_contra hq1
    exact hcon ⟨q, hq1, hq⟩
  have hinj : Function.Injective (fun q : Q => q • ω) := by
    intro q₁ q₂ hq
    change q₁ • ω = q₂ • ω at hq
    have hq' : (q₁⁻¹ * q₂) • ω = ω := by rw [mul_smul, ← hq, inv_smul_smul]
    have h1 : q₁⁻¹ * q₂ = 1 := hfix _ hq'
    calc q₁ = q₁ * (q₁⁻¹ * q₂) := by rw [h1, mul_one]
      _ = q₂ := by group
  have hle : Nat.card Q ≤ Nat.card Ω := Nat.card_le_card_of_injective _ hinj
  omega

private lemma eq_of_mem_sylow_smul_eq {K : Type*} [Group K] {p : ℕ}
    {R S₀ : Sylow p K} (hinf : (R : Subgroup K) ⊓ (S₀ : Subgroup K) = ⊥)
    {r₁ r₂ : K} (hr₁ : r₁ ∈ (R : Subgroup K)) (hr₂ : r₂ ∈ (R : Subgroup K))
    (h : r₁ • S₀ = r₂ • S₀) : r₁ = r₂ := by
  have hfix : (r₂⁻¹ * r₁) • S₀ = S₀ := by rw [mul_smul, h, inv_smul_smul]
  have hn : r₂⁻¹ * r₁ ∈ Subgroup.normalizer (S₀ : Set K) :=
    (Sylow.smul_eq_iff_mem_normalizer).mp hfix
  have hmemR : r₂⁻¹ * r₁ ∈ (R : Subgroup K) :=
    (R : Subgroup K).mul_mem ((R : Subgroup K).inv_mem hr₂) hr₁
  have hmemS : r₂⁻¹ * r₁ ∈ (S₀ : Subgroup K) :=
    mem_sylow_of_mem_normalizer hmemR hn
  have hmemBot : r₂⁻¹ * r₁ ∈ ((R : Subgroup K) ⊓ (S₀ : Subgroup K)) := ⟨hmemR, hmemS⟩
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmemBot
  exact hmemBot.symm

private lemma exists_mem_sylow_smul_eq {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {R S₀ S : Sylow p K}
    (hinf : (R : Subgroup K) ⊓ (S₀ : Subgroup K) = ⊥)
    (hcount : Nat.card (Sylow p K) = Nat.card (R : Subgroup K) + 1)
    (h₀ : S₀ ≠ R) (hS : S ≠ R) : ∃ r ∈ (R : Subgroup K), r • S₀ = S := by
  haveI : Finite (Sylow p K) := inferInstance
  let Ω := {U : Sylow p K // U ≠ R}
  let f : ↥(R : Subgroup K) → Ω := fun t =>
    ⟨(t : K) • S₀, by
      intro h
      apply h₀
      have hT : ((t : K)⁻¹) • R = R := by
        rw [Sylow.smul_eq_iff_mem_normalizer]
        exact Subgroup.le_normalizer ((R : Subgroup K).inv_mem t.2)
      calc S₀ = ((t : K)⁻¹) • ((t : K) • S₀) := (inv_smul_smul _ _).symm
        _ = ((t : K)⁻¹) • R := by rw [h]
        _ = R := hT⟩
  have hinj : Function.Injective f := by
    intro t t' h
    have h' : (t : K) • S₀ = (t' : K) • S₀ := congrArg Subtype.val h
    exact Subtype.ext (eq_of_mem_sylow_smul_eq hinf t.2 t'.2 h')
  have hcard : Nat.card ↥(R : Subgroup K) = Nat.card Ω := by
    rw [show Nat.card ↥(R : Subgroup K) = Nat.card (R : Subgroup K) from rfl,
      show Nat.card Ω = Nat.card (R : Subgroup K) from natCard_sylow_ne R hcount]
  obtain ⟨e⟩ := Finite.card_eq.mp hcard
  have hsurj : Function.Surjective f := Function.Injective.surjective_of_finite e hinj
  obtain ⟨t, ht⟩ := hsurj ⟨S, hS⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

private lemma map_conjNormal_eq_map_conj {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (g : G) {S : Subgroup ↥K} :
    Subgroup.map K.subtype (Subgroup.map (MulAut.conjNormal (H := K) g).toMonoidHom S) =
      Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map K.subtype S) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma normalizer_sylow_eq_subgroupOf {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hN : IsStronglyPEmbedded p N)
    (hT : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hne : (T : Subgroup ↥K).map K.subtype ≠ ⊥)
    (hKnot : ¬ K ≤ N)
    (hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))) :
    N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) := by
  have hAXp : IsPGroup p ((T : Subgroup ↥K).map K.subtype) := T.isPGroup'.map K.subtype
  have hNK_le : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    have hg' : (g : X) ∈
        Subgroup.normalizer (((T : Subgroup ↥K).map K.subtype) : Set X) :=
      Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hg)
    exact hN.normalizer_le hne hAXp hT hg'
  have hNK_lt : N.subgroupOf K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hKnot
    intro k hk
    have hmem : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by rw [htop]; trivial
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subtype.coe_mk] using hmem
  rcases hmax.le_iff.mp hNK_le with htop | heq
  · exact absurd htop hNK_lt.ne
  · exact heq

private lemma conjNormal_sylow_eq_self {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    {g : X} (hg : g ∈ N) : MulAut.conjNormal (H := K) g • T = T := by
  have hA_le_NK : (T : Subgroup ↥K) ≤ N.subgroupOf K := by
    rw [hNK]
    exact Subgroup.le_normalizer
  let A_NK : Sylow p ↥(N.subgroupOf K) := T.subtype hA_le_NK
  have hA_NK_normal : (A_NK : Subgroup ↥(N.subgroupOf K)).Normal := by
    rw [show (A_NK : Subgroup ↥(N.subgroupOf K)) =
        ((T : Subgroup ↥K).subgroupOf (N.subgroupOf K)) from Sylow.coe_subtype T hA_le_NK]
    rw [hNK]
    exact Subgroup.normal_in_normalizer
  haveI : Unique (Sylow p ↥(N.subgroupOf K)) := Sylow.unique_of_normal A_NK hA_NK_normal
  let T' : Sylow p ↥K := MulAut.conjNormal (H := K) g • T
  have hT'_le : (T' : Subgroup ↥K) ≤ N.subgroupOf K := by
    intro a ha
    rw [Subgroup.mem_subgroupOf]
    have ha' : a ∈ ((MulAut.conjNormal (H := K) g • T : Sylow p ↥K) :
        Subgroup ↥K) := ha
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at ha'
    let φ : ↥K →* ↥K :=
      (MulDistribMulAction.toMonoidEnd (MulAut ↥K) ↥K) (MulAut.conjNormal (H := K) g)
    obtain ⟨t, ht, hta⟩ := (Subgroup.mem_map (f := φ)).mp ha'
    have hφt : (φ t : ↥K) = (MulAut.conjNormal (H := K) g) t := rfl
    rw [← hta, hφt, MulAut.conjNormal_apply (H := K)]
    have htN : (t : X) ∈ N := Subgroup.mem_subgroupOf.mp (hA_le_NK ht)
    exact N.mul_mem (N.mul_mem hg htN) (N.inv_mem hg)
  haveI : (A_NK : Subgroup ↥(N.subgroupOf K)).Normal := hA_NK_normal
  let T'_NK : Sylow p ↥(N.subgroupOf K) := T'.subtype hT'_le
  have hle : (A_NK : Subgroup ↥(N.subgroupOf K)) ≤ (T'_NK : Subgroup ↥(N.subgroupOf K)) :=
    IsPGroup.le_sylow_of_normal (N := (A_NK : Subgroup ↥(N.subgroupOf K)))
      A_NK.isPGroup' T'_NK
  have hmap : (T : Subgroup ↥K) ≤ (T' : Subgroup ↥K) := by
    have h := Subgroup.map_mono (f := (N.subgroupOf K).subtype) hle
    rwa [Sylow.coe_subtype, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hA_le_NK,
      Subgroup.map_subgroupOf_eq_of_le hT'_le] at h
  apply Sylow.ext
  exact (Subgroup.eq_of_le_of_card_ge hmap (by
    rw [Sylow.card_eq_multiplicity T', Sylow.card_eq_multiplicity T])).symm

private lemma normal_subgroupOf_map_sylow {X : Type*} [Group X] {p : ℕ}
    {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T) :
    (((T : Subgroup ↥K).map K.subtype).subgroupOf N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : X) ∈ (T : Subgroup ↥K).map K.subtype := hn
  obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.mp hn'
  have hconj_sub : Subgroup.map (MulAut.conjNormal (H := K) (g : X)).toMonoidHom
      (T : Subgroup ↥K) = (T : Subgroup ↥K) := by
    have h := congrArg (fun S : Sylow p ↥K => (S : Subgroup ↥K)) (hconj (g : X) g.2)
    rwa [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
  have hgt_mem : MulAut.conjNormal (H := K) (g : X) t ∈ (T : Subgroup ↥K) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := K) (g : X)).toMonoidHom ht
    rwa [hconj_sub] at h
  have hgn : (g : X) * (n : X) * (g : X)⁻¹ =
      ((MulAut.conjNormal (H := K) (g : X) t : ↥K) : X) := by
    rw [← htn, MulAut.conjNormal_apply (H := K)]
    rfl
  change (g : X) * (n : X) * (g : X)⁻¹ ∈ Subgroup.map K.subtype (T : Subgroup ↥K)
  rw [hgn]
  exact Subgroup.mem_map_of_mem K.subtype hgt_mem

private lemma exists_sylow_card_lt {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hTNnormal : (((T : Subgroup ↥K).map K.subtype).subgroupOf N).Normal)
    (hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N))
    (hKnot : ¬ K ≤ N) (z : X) (hzN : z ∈ N)
    (hzp : IsPGroup p (Subgroup.zpowers z))
    (hzA : z ∉ (T : Subgroup ↥K).map K.subtype) :
    ∃ (Q : Subgroup ↥N) (g : ↥K) (T' : Sylow p ↥K),
      IsPGroup p Q ∧ Nat.card (T : Subgroup ↥K) < Nat.card Q ∧
      T' = g • T ∧ (g : X) ∉ N := by
  let TN : Subgroup ↥N := ((T : Subgroup ↥K).map K.subtype).subgroupOf N
  let zN : ↥N := ⟨z, hzN⟩
  have hzNp : IsPGroup p (Subgroup.zpowers zN) := by
    obtain ⟨k, hk⟩ := hzp.exists_card_eq
    exact IsPGroup.of_card (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk z hzN, ← Nat.card_zpowers z, hk])
  let Q : Subgroup ↥N := TN ⊔ Subgroup.zpowers zN
  have hQp : IsPGroup p Q := IsPGroup.to_sup_of_normal_left hTNp hzNp
  have hTN_lt_Q : TN < Q := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply hzA
    have hzNQ : zN ∈ Q := (le_sup_right : Subgroup.zpowers zN ≤ Q) (Subgroup.mem_zpowers zN)
    rw [← hEq] at hzNQ
    exact Subgroup.mem_subgroupOf.mp hzNQ
  have hcardQ : Nat.card TN < Nat.card Q := Subgroup.card_lt_of_lt hTN_lt_Q
  have hcardTN : Nat.card TN = Nat.card (T : Subgroup ↥K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAXN).toEquiv,
      Subgroup.card_map_of_injective K.subtype_injective]
  have hcard : Nat.card (T : Subgroup ↥K) < Nat.card Q := by rwa [← hcardTN]
  obtain ⟨gX, hgK, hgN⟩ : ∃ g : X, g ∈ K ∧ g ∉ N := by
    by_contra hcon
    push Not at hcon
    exact hKnot fun k hk => hcon k hk
  let g : ↥K := ⟨gX, hgK⟩
  exact ⟨Q, g, g • T, hQp, hcard, rfl, hgN⟩

private lemma exists_stabilizing_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hTNnormal : (((T : Subgroup ↥K).map K.subtype).subgroupOf N).Normal)
    (hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N))
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hcount : Nat.card (Sylow p ↥K) = Nat.card (T : Subgroup ↥K) + 1)
    (hKnot : ¬ K ≤ N) (z : X) (hzN : z ∈ N)
    (hzp : IsPGroup p (Subgroup.zpowers z))
    (hzA : z ∉ (T : Subgroup ↥K).map K.subtype) :
    ∃ (g : ↥K) (T' : Sylow p ↥K) (x' : X), T' = g • T ∧ (g : X) ∉ N ∧
      x' ∈ N ∧ x' ≠ 1 ∧ IsPGroup p (Subgroup.zpowers x') ∧
      MulAut.conjNormal (H := K) x' • T' = T' := by
  obtain ⟨Q, g, T', hQp, hcard, hgT, hgN⟩ :=
    exists_sylow_card_lt hNK hAXN hTNnormal hTNp hKnot z hzN hzp hzA
  have hT'_ne : T' ≠ T := by
    intro h
    apply hgN
    have hgn : g ∈ Subgroup.normalizer (T : Set ↥K) :=
      (Sylow.smul_eq_iff_mem_normalizer).mp (by rwa [hgT] at h)
    exact Subgroup.mem_subgroupOf.mp (by rw [hNK]; exact hgn)
  letI : MulAction Q (Sylow p ↥K) :=
    MulAction.compHom (Sylow p ↥K)
      ((MulAut.conjNormal (H := K)).comp (N.subtype.comp Q.subtype))
  have hqT : ∀ q : Q, q • T = T := fun q => by
    rw [MulAction.compHom_smul_def]
    exact hconj ((q : Q) : X) ((q : Q) : ↥N).2
  let ΩQ : SubMulAction Q (Sylow p ↥K) :=
    { carrier := {U | U ≠ T}
      smul_mem' := by
        intro q U hU hUT
        exact hU (by
          calc U = q⁻¹ • (q • U) := (inv_smul_smul q U).symm
            _ = q⁻¹ • T := by rw [hUT]
            _ = q⁻¹ • (q • T) := by rw [hqT q]
            _ = T := inv_smul_smul q T) }
  have hcardΩQ : Nat.card ↥ΩQ = Nat.card (T : Subgroup ↥K) := by
    change Nat.card {U : Sylow p ↥K // U ≠ T} = Nat.card (T : Subgroup ↥K)
    rw [natCard_sylow_ne T hcount]
  have hlt : Nat.card ↥ΩQ < Nat.card Q := by rw [hcardΩQ]; exact hcard
  obtain ⟨q, hq1, hqT'Ω⟩ :=
    exists_ne_one_smul_eq_self_of_card_lt (⟨T', hT'_ne⟩ : ↥ΩQ) hlt
  have hqT' : q • T' = T' := congrArg Subtype.val hqT'Ω
  have hconjT' : MulAut.conjNormal (H := K) ((q : Q) : X) • T' = T' := by
    have h := hqT'
    rwa [MulAction.compHom_smul_def] at h
  have hx1 : ((q : Q) : X) ≠ 1 := fun h =>
    hq1 (by apply Subtype.ext; apply Subtype.ext; exact h)
  have hxp : IsPGroup p (Subgroup.zpowers ((q : Q) : X)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQp) q
    exact IsPGroup.of_card (by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn])
  exact ⟨g, T', ((q : Q) : X), hgT, hgN, ((q : Q) : ↥N).2,
    hx1, hxp, hconjT'⟩

private lemma false_of_stabilizing_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hN : IsStronglyPEmbedded p N)
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hAXne : (T : Subgroup ↥K).map K.subtype ≠ ⊥)
    {g : ↥K} {T' : Sylow p ↥K} {x' : X} (hgT : T' = g • T) (hgN : (g : X) ∉ N)
    (hxN : x' ∈ N) (hx1 : x' ≠ 1)
    (hxp : IsPGroup p (Subgroup.zpowers x'))
    (hxT' : MulAut.conjNormal (H := K) x' • T' = T') : False := by
  have hsub : Subgroup.map (MulAut.conjNormal (H := K) x').toMonoidHom
      (T' : Subgroup ↥K) = (T' : Subgroup ↥K) :=
    congrArg (fun S : Sylow p ↥K => (S : Subgroup ↥K)) hxT'
  let T'_X : Subgroup X := (T' : Subgroup ↥K).map K.subtype
  have hmapX : Subgroup.map (MulAut.conj x').toMonoidHom T'_X = T'_X := by
    change Subgroup.map (MulAut.conj x').toMonoidHom
        (Subgroup.map K.subtype (T' : Subgroup ↥K)) =
      Subgroup.map K.subtype (T' : Subgroup ↥K)
    rw [← map_conjNormal_eq_map_conj x' (S := (T' : Subgroup ↥K))]
    rw [hsub]
  have hxnorm : x' ∈ Subgroup.normalizer (T'_X : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapX
  have hT'_le_Ng : T'_X ≤ N.map (MulAut.conj (g : X)).toMonoidHom := by
    rintro y ⟨a, ha, rfl⟩
    have ha' : a ∈ ((g • T : Sylow p ↥K) : Subgroup ↥K) := by
      rw [hgT] at ha
      exact ha
    have hginv : (g : ↥K)⁻¹ * a * g ∈ (T : Subgroup ↥K) :=
      (mem_conj_smul_sylow_iff (x := g) (g := a) (S := T)).mp ha'
    refine (Subgroup.mem_map (f := (MulAut.conj (g : X)).toMonoidHom)).mpr
      ⟨(g : X)⁻¹ * (a : X) * (g : X), ?_, ?_⟩
    · exact hAXN (Subgroup.mem_map_of_mem K.subtype hginv)
    · change (MulAut.conj (g : X)) ((g : X)⁻¹ * (a : X) * (g : X)) = K.subtype a
      rw [MulAut.conj_apply]
      group
      rfl
  have hT'_ne_bot : T'_X ≠ ⊥ := by
    have hcardT'_X : Nat.card T'_X = Nat.card (T : Subgroup ↥K) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective,
        Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hcardAX : Nat.card ((T : Subgroup ↥K).map K.subtype) =
        Nat.card (T : Subgroup ↥K) := Subgroup.card_map_of_injective K.subtype_injective
    have hcardT_ne_one : Nat.card (T : Subgroup ↥K) ≠ 1 := fun h =>
      hAXne (Subgroup.card_eq_one.mp (by rw [hcardAX, h]))
    intro hbot
    have : Nat.card T'_X = 1 := by rw [hbot]; simp
    omega
  have hxNg : x' ∈ N.map (MulAut.conj (g : X)).toMonoidHom :=
    (hN.conj (g : X)).normalizer_le hT'_ne_bot (T'.isPGroup'.map K.subtype)
      hT'_le_Ng hxnorm
  have hxint : x' ∈ N ⊓ N.map (MulAut.conj (g : X)).toMonoidHom := ⟨hxN, hxNg⟩
  have hpdvd : p ∣ Nat.card (N ⊓ N.map (MulAut.conj (g : X)).toMonoidHom : Subgroup X) := by
    have hpdvd' : p ∣ Nat.card (Subgroup.zpowers x') := by
      rcases hxp.card_eq_or_dvd with h1 | h1
      · rw [Subgroup.card_eq_one] at h1
        exact absurd (Subgroup.zpowers_eq_bot.mp h1) hx1
      · exact h1
    exact hpdvd'.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxint))
  exact hN.2.2 (g : X) hgN hpdvd

private lemma pElement_mem_map_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hN : IsStronglyPEmbedded p N)
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hAXne : (T : Subgroup ↥K).map K.subtype ≠ ⊥)
    (hTNnormal : (((T : Subgroup ↥K).map K.subtype).subgroupOf N).Normal)
    (hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N))
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hcount : Nat.card (Sylow p ↥K) = Nat.card (T : Subgroup ↥K) + 1)
    (hKnot : ¬ K ≤ N) :
    ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) →
      z ∈ (T : Subgroup ↥K).map K.subtype := by
  intro z hzN hzp
  by_contra hzA
  obtain ⟨g, T', x', hgT, hgN, hxN, hx1, hxp, hxT'⟩ :=
    exists_stabilizing_sylow hNK hAXN hTNnormal hTNp hconj hcount hKnot z hzN hzp hzA
  exact false_of_stabilizing_sylow hN hAXN hAXne hgT hgN hxN hx1 hxp hxT'

private lemma pPrimeCore_centralizes_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} {T : Sylow p ↥K}
    (hTNnormal : (((T : Subgroup ↥K).map K.subtype).subgroupOf N).Normal)
    (hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N)) :
    CFSG.pPrimeCore p ↥N ≤ Subgroup.centralizer
      ((((T : Subgroup ↥K).map K.subtype).subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  let Y : Subgroup ↥N := CFSG.pPrimeCore p ↥N
  change Y ≤ Subgroup.centralizer
    ((((T : Subgroup ↥K).map K.subtype).subgroupOf N : Subgroup ↥N) : Set ↥N)
  haveI : Y.Normal := CFSG.pPrimeCore_normal
  have hYcop : Nat.Coprime p (Nat.card Y) := CFSG.pPrimeCore_coprime_card
  obtain ⟨n, hn⟩ := hTNp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y)
      (Nat.card (((T : Subgroup ↥K).map K.subtype).subgroupOf N)) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hYcop.symm
  have hYinf : Y ⊓ (((T : Subgroup ↥K).map K.subtype).subgroupOf N) = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime hcop
  have hcomm : ⁅Y, ((T : Subgroup ↥K).map K.subtype).subgroupOf N⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅Y, ((T : Subgroup ↥K).map K.subtype).subgroupOf N⁆ ≤
          Y ⊓ (((T : Subgroup ↥K).map K.subtype).subgroupOf N) :=
          Subgroup.commutator_le_inf Y (((T : Subgroup ↥K).map K.subtype).subgroupOf N)
      _ = ⊥ := hYinf
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

private lemma pPrimeCore_le_subgroupOf_map_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hYcen : CFSG.pPrimeCore p ↥N ≤ Subgroup.centralizer
      ((((T : Subgroup ↥K).map K.subtype).subgroupOf N : Subgroup ↥N) : Set ↥N))
    (hinner : ∀ (T : Sylow p ↥K) (α : MulAut ↥K),
      (∀ u ∈ (T : Subgroup ↥K), α u = u) → ∃ u ∈ (T : Subgroup ↥K), α = MulAut.conj u)
    (hKcent : Subgroup.centralizer ((K : Subgroup X) : Set X) = ⊥) :
    CFSG.pPrimeCore p ↥N ≤ (((T : Subgroup ↥K).map K.subtype).subgroupOf N) := by
  intro y hy
  have hfix : ∀ u ∈ (T : Subgroup ↥K), MulAut.conjNormal (H := K) (y : X) u = u := by
    intro u hu
    have huAX : (u : X) ∈ (T : Subgroup ↥K).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype hu
    let tN : ↥N := ⟨(u : X), hAXN huAX⟩
    have htN : tN ∈ (((T : Subgroup ↥K).map K.subtype).subgroupOf N) :=
      Subgroup.mem_subgroupOf.mpr huAX
    have hc := Subgroup.mem_centralizer_iff.mp (hYcen hy) tN htN
    have hc' : (u : X) * (y : X) = (y : X) * (u : X) := by
      have := congrArg (fun z : ↥N => (z : X)) hc
      simpa only [Subgroup.coe_mul, tN] using this
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hc']
    group
  obtain ⟨u, hu, hα⟩ := hinner T (MulAut.conjNormal (H := K) (y : X)) hfix
  have hcen : (u : X)⁻¹ * (y : X) ∈ Subgroup.centralizer ((K : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkK : k ∈ K := hk
    have hval : ((MulAut.conjNormal (H := K) (y : X)) ⟨k, hkK⟩ : ↥K) =
        (MulAut.conj u ⟨k, hkK⟩) := by rw [hα]
    have hvalX : (y : X) * k * (y : X)⁻¹ = (u : X) * k * (u : X)⁻¹ := by
      have := congrArg (fun z : ↥K => (z : X)) hval
      simpa only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] using this
    calc k * ((u : X)⁻¹ * (y : X))
        = (u : X)⁻¹ * ((u : X) * k * (u : X)⁻¹) * (y : X) := by group
      _ = (u : X)⁻¹ * ((y : X) * k * (y : X)⁻¹) * (y : X) := by rw [hvalX]
      _ = ((u : X)⁻¹ * (y : X)) * k := by group
  have hbot : (u : X)⁻¹ * (y : X) = 1 := by
    have hmem : (u : X)⁻¹ * (y : X) ∈ (⊥ : Subgroup X) := by
      rw [← hKcent]
      exact hcen
    exact Subgroup.mem_bot.mp hmem
  have hyu : (y : X) = (u : X) := by
    calc (y : X) = (u : X) * ((u : X)⁻¹ * (y : X)) := by group
      _ = (u : X) := by rw [hbot, mul_one]
  have hyAX : (y : X) ∈ (T : Subgroup ↥K).map K.subtype := by
    rw [hyu]
    exact Subgroup.mem_map_of_mem K.subtype hu
  exact Subgroup.mem_subgroupOf.mpr hyAX

private lemma pPrimeCore_eq_bot_of_le_subgroupOf_map_sylow {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {N K : Subgroup X} {T : Sylow p ↥K}
    (hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N))
    (hle : CFSG.pPrimeCore p ↥N ≤ (((T : Subgroup ↥K).map K.subtype).subgroupOf N)) :
    CFSG.pPrimeCore p ↥N = ⊥ := by
  let Y : Subgroup ↥N := CFSG.pPrimeCore p ↥N
  change Y = ⊥
  haveI : Y.Normal := CFSG.pPrimeCore_normal
  have hYcop : Nat.Coprime p (Nat.card Y) := CFSG.pPrimeCore_coprime_card
  refine (Subgroup.eq_bot_iff_forall Y).mpr ?_
  intro y hy
  have hyTN : y ∈ (((T : Subgroup ↥K).map K.subtype).subgroupOf N) := hle hy
  have hord_dvd : orderOf y ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hy
  have hnotp : ¬ p ∣ orderOf y := by
    intro hpd
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hYcop) (hpd.trans hord_dvd)
  have hyp : IsPGroup p (Subgroup.zpowers y) :=
    hTNp.to_le (Subgroup.zpowers_le.mpr hyTN)
  by_contra hy1
  obtain ⟨m, hm⟩ := hyp.exists_card_eq
  have hm' : orderOf y = p ^ m := by rw [← Nat.card_zpowers y, hm]
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hy1
    have h1 : orderOf y = 1 := by rw [hm', hm0, pow_zero]
    exact orderOf_eq_one_iff.mp h1
  exact hnotp (by rw [hm']; exact dvd_pow_self p hm0)

private lemma exists_fixed_sylow_ne {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y]
    {p r : ℕ} [Fact p.Prime] [MulAction Y (Sylow p K)]
    (T : Sylow p K) (hcount : Nat.card (Sylow p K) = Nat.card (T : Subgroup K) + 1)
    (hr : r.Prime) (hYp : IsPGroup r Y) (hrp : r ≠ p)
    (hfixT : ∀ y : Y, y • T = T) :
    ∃ T' : Sylow p K, T' ≠ T ∧ ∀ y : Y, y • T' = T' := by
  haveI : Fact r.Prime := ⟨hr⟩
  let Ω : SubMulAction Y (Sylow p K) :=
    { carrier := {U | U ≠ T}
      smul_mem' := by
        intro y U hU hUT
        exact hU (by
          calc U = y⁻¹ • (y • U) := (inv_smul_smul y U).symm
            _ = y⁻¹ • T := by rw [hUT]
            _ = y⁻¹ • (y • T) := by rw [hfixT y]
            _ = T := inv_smul_smul y T) }
  have hcardΩ : Nat.card ↥Ω = Nat.card (T : Subgroup K) := by
    change Nat.card {U : Sylow p K // U ≠ T} = Nat.card (T : Subgroup K)
    rw [natCard_sylow_ne T hcount]
  have hrnotdvd : ¬ r ∣ Nat.card (T : Subgroup K) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    intro hd
    have hdvdp : r ∣ p := Nat.Prime.dvd_of_dvd_pow hr hd
    exact hrp ((Nat.Prime.dvd_iff_eq (p := p) (a := r) Fact.out
      (Nat.Prime.one_lt hr).ne').mp hdvdp).symm
  have hfix_ne : Nat.card (MulAction.fixedPoints Y ↥Ω) ≠ 0 := by
    intro h0
    apply hrnotdvd
    apply Nat.modEq_zero_iff_dvd.mp
    have h := hYp.card_modEq_card_fixedPoints ↥Ω
    rwa [hcardΩ, h0] at h
  obtain ⟨u⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix_ne)).1
  obtain ⟨⟨T', hT'_ne⟩, hT'_fix⟩ := u
  refine ⟨T', hT'_ne, fun y => ?_⟩
  have h := congrArg Subtype.val (hT'_fix y)
  simpa [Ω] using h

private lemma exists_c_of_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N K : Subgroup X} [K.Normal] {T T' : Sylow p ↥K}
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hinf : (T' : Subgroup ↥K) ⊓ (T : Subgroup ↥K) = ⊥)
    (hcountT' : Nat.card (Sylow p ↥K) = Nat.card (T' : Subgroup ↥K) + 1)
    (hT'_ne : T' ≠ T)
    (hpElement_mem_AX : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) →
      z ∈ (T : Subgroup ↥K).map K.subtype)
    {x : X} (hxN : x ∈ N) (hx1 : x ≠ 1)
    (hxp : IsPGroup p (Subgroup.zpowers x)) :
    ∃ c : ↥K, c ∈ (T' : Subgroup ↥K) ∧
      c • T = MulAut.conjNormal (H := K) x • T' ∧ c ≠ 1 := by
  let T'' : Sylow p ↥K := MulAut.conjNormal (H := K) x • T'
  have hxAX : x ∈ (T : Subgroup ↥K).map K.subtype := hpElement_mem_AX x hxN hxp
  obtain ⟨xK, hxKT, hxKx⟩ := (Subgroup.mem_map (f := K.subtype)).mp hxAX
  have hT''_ne' : T'' ≠ T' := by
    intro h
    have hxKn : xK ∈ Subgroup.normalizer (T' : Set ↥K) := by
      refine (Sylow.smul_eq_iff_mem_normalizer (P := T')).mp ?_
      rw [Sylow.smul_def, ← MulAut.conjNormal_val]
      change MulAut.conjNormal (H := K) (xK : X) • T' = T'
      have hxKx' : (xK : X) = x := hxKx
      rw [hxKx']
      exact h
    have hxKT' : xK ∈ (T' : Subgroup ↥K) :=
      mem_sylow_of_mem_normalizer hxKT hxKn
    have hmemBot : xK ∈ ((T : Subgroup ↥K) ⊓ (T' : Subgroup ↥K)) := ⟨hxKT, hxKT'⟩
    rw [inf_comm, hinf, Subgroup.mem_bot] at hmemBot
    apply hx1
    rw [← hxKx, hmemBot]
    rfl
  have hxTfix_inv : MulAut.conjNormal (H := K) x⁻¹ • T = T := by
    have h := hconj x hxN
    calc MulAut.conjNormal (H := K) x⁻¹ • T
        = MulAut.conjNormal (H := K) x⁻¹ •
            (MulAut.conjNormal (H := K) x • T) := by rw [h]
      _ = (MulAut.conjNormal (H := K) x⁻¹ * MulAut.conjNormal (H := K) x) • T := by
            rw [mul_smul]
      _ = (1 : MulAut ↥K) • T := by rw [← map_mul, inv_mul_cancel, map_one]
      _ = T := one_smul _ _
  have hT''_ne : T'' ≠ T := by
    intro h
    apply hT'_ne
    calc T' = MulAut.conjNormal (H := K) x⁻¹ • T'' := by
          rw [show T'' = MulAut.conjNormal (H := K) x • T' from rfl, ← mul_smul,
            ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = MulAut.conjNormal (H := K) x⁻¹ • T := by rw [h]
      _ = T := hxTfix_inv
  obtain ⟨c, hcT', hcT⟩ :=
    exists_mem_sylow_smul_eq (R := T') (S₀ := T) (S := T'')
      hinf hcountT' hT'_ne.symm hT''_ne'
  have hc1 : c ≠ 1 := by
    intro hc
    apply hT''_ne
    rw [← hcT, hc, one_smul]
  exact ⟨c, hcT', hcT, hc1⟩

private lemma c_mem_properties {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N K : Subgroup X} [K.Normal] {T T' : Sylow p ↥K}
    (hinf : (T' : Subgroup ↥K) ⊓ (T : Subgroup ↥K) = ⊥)
    (hpElement_mem_AX : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) →
      z ∈ (T : Subgroup ↥K).map K.subtype)
    {c : ↥K} (hcT' : c ∈ (T' : Subgroup ↥K)) (hc1 : c ≠ 1) :
    IsPGroup p (Subgroup.zpowers (c : X)) ∧ (c : X) ∉ N := by
  have hcpX : IsPGroup p (Subgroup.zpowers (c : X)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp T'.isPGroup') ⟨c, hcT'⟩
    have hck : orderOf c = p ^ k := by
      rw [← Subgroup.orderOf_mk c hcT']
      exact hk
    have hcXk : orderOf (c : X) = p ^ k := by
      rw [Subgroup.orderOf_coe c, hck]
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hcXk])
  refine ⟨hcpX, ?_⟩
  intro hcN
  have hcAX : (c : X) ∈ (T : Subgroup ↥K).map K.subtype :=
    hpElement_mem_AX (c : X) hcN hcpX
  obtain ⟨cK, hcKT, hcKc⟩ := (Subgroup.mem_map (f := K.subtype)).mp hcAX
  have hcK_eq : cK = c := K.subtype_injective hcKc
  have hcT : c ∈ (T : Subgroup ↥K) := hcK_eq ▸ hcKT
  have hmemBot : c ∈ ((T' : Subgroup ↥K) ⊓ (T : Subgroup ↥K)) := ⟨hcT', hcT⟩
  rw [hinf, Subgroup.mem_bot] at hmemBot
  exact hc1 hmemBot

private lemma inf_sylow_eq_bot_of_ne {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hN : IsStronglyPEmbedded p N)
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hAXN : (T : Subgroup ↥K).map K.subtype ≤ N)
    (hAXp : IsPGroup p ((T : Subgroup ↥K).map K.subtype))
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    {T' : Sylow p ↥K} (hT' : T' ≠ T) :
    (T : Subgroup ↥K) ⊓ (T' : Subgroup ↥K) = ⊥ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥K) T T'
  have hgN : (g : X) ∉ N := by
    intro hgN
    apply hT'
    calc T' = g • T := hg.symm
      _ = MulAut.conj g • T := Sylow.smul_def
      _ = MulAut.conjNormal (H := K) (g : X) • T := by rw [← MulAut.conjNormal_val]
      _ = T := hconj (g : X) hgN
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxT : x ∈ (T : Subgroup ↥K) := hx.1
  have hxT' : x ∈ (T' : Subgroup ↥K) := hx.2
  have hxT'g : x ∈ ((g • T : Sylow p ↥K) : Subgroup ↥K) := by rwa [hg]
  have hxg : g⁻¹ * x * g ∈ (T : Subgroup ↥K) :=
    (mem_conj_smul_sylow_iff (x := g) (g := x) (S := T)).mp hxT'g
  have hxAX : (x : X) ∈ (T : Subgroup ↥K).map K.subtype :=
    Subgroup.mem_map_of_mem K.subtype hxT
  have hxN : (x : X) ∈ N := hAXN hxAX
  have hxgN : (g : X)⁻¹ * (x : X) * (g : X) ∈ N := by
    simpa only [Subgroup.coe_subtype, map_mul, map_inv] using
      hAXN (Subgroup.mem_map_of_mem K.subtype hxg)
  have hxmap : (x : X) ∈ N.map (MulAut.conj (g : X)).toMonoidHom := by
    refine (Subgroup.mem_map).mpr ⟨(g : X)⁻¹ * (x : X) * (g : X), hxgN, ?_⟩
    change (MulAut.conj (g : X)) ((g : X)⁻¹ * (x : X) * (g : X)) = (x : X)
    rw [MulAut.conj_apply]
    group
  have hxne : (x : X) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxp : IsPGroup p (Subgroup.zpowers (x : X)) :=
    hAXp.to_le (Subgroup.zpowers_le.mpr hxAX)
  have hpdvd : p ∣ Nat.card (Subgroup.zpowers (x : X)) := by
    rcases hxp.card_eq_or_dvd with h1 | h1
    · rw [Subgroup.card_eq_one] at h1
      exact absurd (Subgroup.zpowers_eq_bot.mp h1) hxne
    · exact h1
  refine hN.2.2 (g : X) hgN ?_
  exact hpdvd.trans (Subgroup.card_dvd_of_le
    (le_inf (Subgroup.zpowers_le.mpr hxN) (Subgroup.zpowers_le.mpr hxmap)))

private lemma commutes_of_c {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N K : Subgroup X} [K.Normal] {T T' : Sylow p ↥K}
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hinf : (T' : Subgroup ↥K) ⊓ (T : Subgroup ↥K) = ⊥)
    {x y : X} (hyN : y ∈ N) (hxy : x * y = y * x)
    (hyT' : MulAut.conjNormal (H := K) y • T' = T')
    {c : ↥K} (hcT' : c ∈ (T' : Subgroup ↥K))
    (hcT : c • T = MulAut.conjNormal (H := K) x • T') :
    (c : X) * y = y * (c : X) := by
  have hyT : MulAut.conjNormal (H := K) y • T = T := hconj y hyN
  have hyT_inv : (MulAut.conjNormal (H := K) y)⁻¹ • T = T := by
    calc (MulAut.conjNormal (H := K) y)⁻¹ • T
        = (MulAut.conjNormal (H := K) y)⁻¹ •
            (MulAut.conjNormal (H := K) y • T) := by rw [hyT]
      _ = ((MulAut.conjNormal (H := K) y)⁻¹ * MulAut.conjNormal (H := K) y) • T := by
            rw [mul_smul]
      _ = (1 : MulAut ↥K) • T := by rw [inv_mul_cancel]
      _ = T := one_smul _ _
  have hyT'' : MulAut.conjNormal (H := K) y •
      (MulAut.conjNormal (H := K) x • T') = MulAut.conjNormal (H := K) x • T' := by
    rw [← mul_smul, ← map_mul, ← hxy, map_mul, mul_smul, hyT']
  let c' : ↥K := (MulAut.conjNormal (H := K) y) c
  have hc'_T' : c' ∈ (T' : Subgroup ↥K) := by
    have h : c' ∈ ((MulAut.conjNormal (H := K) y • T' : Sylow p ↥K) :
        Subgroup ↥K) := by
      rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa only [c', MulAut.smul_def, MulAut.inv_apply, MulEquiv.symm_apply_apply] using hcT'
    rwa [hyT'] at h
  have hc'T : c' • T = MulAut.conjNormal (H := K) x • T' := by
    rw [Sylow.smul_def, ← MulAut.conjNormal_val]
    have hc'X : (c' : X) = y * (c : X) * y⁻¹ := by
      simp only [c', MulAut.conjNormal_apply]
    rw [hc'X, map_mul, map_mul, map_inv, mul_smul, mul_smul, hyT_inv]
    rw [MulAut.conjNormal_val, ← Sylow.smul_def, hcT, hyT'']
  have hc'c : c' = c :=
    (eq_of_mem_sylow_smul_eq hinf hcT' hc'_T' (hcT.trans hc'T.symm)).symm
  have hfix : (MulAut.conjNormal (H := K) y) c = c := hc'c
  have h := congrArg (fun z : ↥K => (z : X)) hfix
  rw [MulAut.conjNormal_apply] at h
  calc (c : X) * y = (y * (c : X) * y⁻¹) * y := by rw [h]
    _ = y * (c : X) := by group

private lemma centralizer_has_pElement_outside {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup X} [K.Normal] {T : Sylow p ↥K}
    (hK : K = CFSG.generalizedFitting X)
    (hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T)
    (hinf_bot : ∀ T' : Sylow p ↥K, T' ≠ T →
      (T : Subgroup ↥K) ⊓ (T' : Subgroup ↥K) = ⊥)
    (hcount : ∀ T : Sylow p ↥K,
      Nat.card (Sylow p ↥K) = Nat.card (T : Subgroup ↥K) + 1)
    (hpElement_mem_AX : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) →
      z ∈ (T : Subgroup ↥K).map K.subtype) :
    ∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) →
      (orderOf y).Prime → orderOf y ≠ p → x * y = y * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧
        c ∉ N := by
  intro x y hxN hyN hx1 hxp hyprime hypne hxy
  have hxAX : x ∈ (T : Subgroup ↥K).map K.subtype := hpElement_mem_AX x hxN hxp
  obtain ⟨xK, hxKT, hxKx⟩ := (Subgroup.mem_map (f := K.subtype)).mp hxAX
  have hyT : MulAut.conjNormal (H := K) y • T = T := hconj y hyN
  let Y : Subgroup X := Subgroup.zpowers y
  have hYleN : Y ≤ N := Subgroup.zpowers_le.mpr hyN
  letI : MulAction Y (Sylow p ↥K) :=
    MulAction.compHom (Sylow p ↥K) ((MulAut.conjNormal (H := K)).comp Y.subtype)
  have hYp : IsPGroup (orderOf y) Y := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
  have hfixT : ∀ z : Y, z • T = T := by
    intro z
    rw [MulAction.compHom_smul_def]
    exact hconj (z : X) (hYleN z.2)
  obtain ⟨T', hT'_ne, hT'_fix⟩ :=
    exists_fixed_sylow_ne (K := ↥K) (Y := Y) T (hcount T) hyprime hYp hypne hfixT
  have hyT' : MulAut.conjNormal (H := K) y • T' = T' :=
    hT'_fix ⟨y, Subgroup.mem_zpowers y⟩
  have hinfT'T : (T' : Subgroup ↥K) ⊓ (T : Subgroup ↥K) = ⊥ := by
    rw [inf_comm]
    exact hinf_bot T' hT'_ne
  obtain ⟨c, hcT', hcT, hc1⟩ :=
    exists_c_of_sylow hconj hinfT'T (hcount T') hT'_ne hpElement_mem_AX hxN hx1 hxp
  obtain ⟨hcpX, hcN⟩ := c_mem_properties hinfT'T hpElement_mem_AX hcT' hc1
  exact ⟨(c : X), hK ▸ c.2, commutes_of_c hconj hinfT'T hyN hxy hyT' hcT' hcT, hcpX, hcN⟩

private lemma exists_sylow_of_rankOne {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N K : Subgroup X} [K.Normal] (hK1 : K ≠ ⊥)
    (hN : IsStronglyPEmbedded p N)
    (hmax : ∀ T : Sylow p ↥K, IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)))
    (hcount : ∀ T : Sylow p ↥K, Nat.card (Sylow p ↥K) = Nat.card (T : Subgroup ↥K) + 1) :
    ∃ T : Sylow p ↥K, (T : Subgroup ↥K).map K.subtype ≤ N ∧
      (∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T) ∧
      (∀ T' : Sylow p ↥K, T' ≠ T → (T : Subgroup ↥K) ⊓ (T' : Subgroup ↥K) = ⊥) ∧
      ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ (T : Subgroup ↥K).map K.subtype := by
  classical
  obtain ⟨P, hPN, hPK, T, hT, -⟩ := exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hnotle : ¬ K ≤ N :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
  have hAXeq : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hAXN : (T : Subgroup ↥K).map K.subtype ≤ N := hAXeq.le.trans (inf_le_left.trans hPN)
  have hAXp : IsPGroup p ((T : Subgroup ↥K).map K.subtype) := T.isPGroup'.map K.subtype
  have hAXne : (T : Subgroup ↥K).map K.subtype ≠ ⊥ := by rw [hAXeq]; exact hPK
  have hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    normalizer_sylow_eq_subgroupOf hN hAXN hAXne hnotle (hmax T)
  have hconj : ∀ g : X, g ∈ N → MulAut.conjNormal (H := K) g • T = T :=
    fun g hg => conjNormal_sylow_eq_self hNK hg
  have hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N) :=
    hAXp.of_equiv (Subgroup.subgroupOfEquivOfLe hAXN).symm
  exact ⟨T, hAXN, hconj, fun T' hT' => inf_sylow_eq_bot_of_ne hN hconj hAXN hAXp hNK hT',
    pElement_mem_map_sylow hN hNK hAXN hAXne (normal_subgroupOf_map_sylow hconj) hTNp hconj
      (hcount T) hnotle⟩

theorem pElements_of_rankOne {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (hmax : ∀ T : Sylow p ↥(CFSG.generalizedFitting X),
      IsCoatom (Subgroup.normalizer ((T : Subgroup ↥(CFSG.generalizedFitting X)) :
        Set ↥(CFSG.generalizedFitting X))))
    (hcount : ∀ T : Sylow p ↥(CFSG.generalizedFitting X),
      Nat.card (Sylow p ↥(CFSG.generalizedFitting X)) =
        Nat.card (T : Subgroup ↥(CFSG.generalizedFitting X)) + 1) :
    (∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) →
      (orderOf y).Prime → orderOf y ≠ p → x * y = y * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧
        c ∉ N) ∧
    ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting X := by
  classical
  obtain ⟨hKsimple, -, hKnormal, -⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (H := X) Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKnormal
  haveI : IsSimpleGroup ↥K := hKsimple
  obtain ⟨T, -, hconj, hinf_bot, hpElement_mem_AX⟩ :=
    exists_sylow_of_rankOne hO ((Subgroup.nontrivial_iff_ne_bot K).1 inferInstance) hN hmax hcount
  exact ⟨centralizer_has_pElement_outside (K := K) (T := T) rfl hconj hinf_bot hcount
      hpElement_mem_AX,
    fun z hz hzp => Subgroup.map_subtype_le _ (hpElement_mem_AX z hz hzp)⟩

theorem good_of_rankOne {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (hmax : ∀ T : Sylow p ↥(CFSG.generalizedFitting X),
      IsCoatom (Subgroup.normalizer ((T : Subgroup ↥(CFSG.generalizedFitting X)) :
        Set ↥(CFSG.generalizedFitting X))))
    (hcount : ∀ T : Sylow p ↥(CFSG.generalizedFitting X),
      Nat.card (Sylow p ↥(CFSG.generalizedFitting X)) =
        Nat.card (T : Subgroup ↥(CFSG.generalizedFitting X)) + 1)
    (hinner : ∀ (T : Sylow p ↥(CFSG.generalizedFitting X))
      (α : MulAut ↥(CFSG.generalizedFitting X)),
      (∀ u ∈ (T : Subgroup ↥(CFSG.generalizedFitting X)), α u = u) →
        ∃ u ∈ (T : Subgroup ↥(CFSG.generalizedFitting X)), α = MulAut.conj u) :
    Good p N := by
  classical
  obtain ⟨hKsimple, -, hKnormal, hKcent⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (H := X) Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKnormal
  haveI : IsSimpleGroup ↥K := hKsimple
  obtain ⟨T, hAXN, hconj, -, -⟩ :=
    exists_sylow_of_rankOne hO ((Subgroup.nontrivial_iff_ne_bot K).1 inferInstance) hN hmax hcount
  have hTNp : IsPGroup p (((T : Subgroup ↥K).map K.subtype).subgroupOf N) :=
    (T.isPGroup'.map K.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hAXN).symm
  refine ⟨pPrimeCore_eq_bot_of_le_subgroupOf_map_sylow hTNp
    (pPrimeCore_le_subgroupOf_map_sylow hAXN
      (pPrimeCore_centralizes_sylow (normal_subgroupOf_map_sylow hconj) hTNp) hinner hKcent), ?_⟩
  intro x y hxN hyN hx1 hxp hyprime _ hypne hxy
  exact (pElements_of_rankOne hO hN hmax hcount).1 x y hxN hyN hx1 hxp hyprime hypne hxy
