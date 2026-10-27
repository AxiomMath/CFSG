module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_a
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Theorem 9.1 from BG Section 9

This file contains the support package and proof of Theorem 9.1 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_coprime_card_of_isPiSubgroup_singleton_compl
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H) :
    Nat.Coprime p (Nat.card H) := by
  refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
  intro hpH
  have hpmem : (⟨p, Fact.out⟩ : Nat.Primes) ∈
      (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) :=
    hH ⟨p, Fact.out⟩ hpH
  have hpmem' :
      ¬ (⟨p, Fact.out⟩ : Nat.Primes) ∈ ({⟨p, Fact.out⟩} : Set Nat.Primes) := hpmem
  exact hpmem' (Set.mem_singleton _)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_isPiSubgroup_singleton_compl_of_coprime_card
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Nat.Coprime p (Nat.card H)) :
    IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H := by
  intro q hq
  rw [Set.mem_compl_iff]
  intro hqp
  have hqval : q.val = p :=
    congrArg (fun r : Nat.Primes => r.val) (Set.mem_singleton_iff.mp hqp)
  exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hH) (by
    simpa [hqval] using hq)

omit [IsMinCE G] in
private theorem CFSG.section9_t91_family_member_le_of_centralizers_le
    {p : ℕ} [Fact p.Prime] {M B K : Subgroup G}
    (hBelem : IsElementaryAbelian p B) (hBnoncyclic : ¬ IsCyclic B)
    (hcentralizers : ∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M)
    (hK : K ∈ section9PPrimeFamily (⊤ : Subgroup G) B p) :
    K ≤ M := by
  classical
  rcases hK with ⟨_hKtop, hKπ, hBnormK⟩
  have hKπ_singleton :
      IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) K := by
    simpa [section9PPrimeSet] using hKπ
  have hKcop : Nat.Coprime p (Nat.card K) :=
    section9_coprime_card_of_isPiSubgroup_singleton_compl hKπ_singleton
  let : IsElementaryAbelian p B := hBelem
  let : CommGroup B := IsMulCommutative.instCommGroup
  have : Subgroup.Normalizes B K := ⟨hBnormK⟩
  let : Fact (IsPGroup p B) := ⟨IsElementaryAbelian.isPGroup p B⟩
  have hBfix_top :
      (⨆ (b : B) (_ : b ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥K) = ⊤ := by
    simpa using proposition_1_16_a (G := ↥K) (A := B) p hKcop hBnoncyclic
  have hfixed_map_le :
      ∀ b : B, ∀ hb_ne : b ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥K).map K.subtype ≤ M := by
    intro b hb_ne
    have hbG_ne : (b : G) ≠ 1 := by
      intro hbG
      exact hb_ne (Subtype.ext hbG)
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥K) =
          (elementCentralizerIn K (b : G)).subgroupOf K := by
      simpa using fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn K B hBnormK b
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥K)).map K.subtype =
          elementCentralizerIn K (b : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥K)).map K.subtype =
            ((elementCentralizerIn K (b : G)).subgroupOf K).map K.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn K (b : G) ⊓ K := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn K (b : G) := inf_eq_left.2 inf_le_left
    calc
      (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥K)).map K.subtype =
          elementCentralizerIn K (b : G) := hfix_map
      _ ≤ Subgroup.centralizer ({(b : G)} : Set G) := inf_le_right
      _ ≤ M := hcentralizers (b : G) b.2 hbG_ne
  have htop_map_K : (⊤ : Subgroup K).map K.subtype = K := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
  calc
    K = (⊤ : Subgroup K).map K.subtype := htop_map_K.symm
    _ =
        (⨆ (b : B) (_ : b ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥K).map
          K.subtype := by
          simp [hBfix_top]
    _ ≤ M := by
          rw [Subgroup.map_iSup]
          refine iSup_le ?_
          intro b
          rw [Subgroup.map_iSup]
          refine iSup_le ?_
          intro hb_ne
          exact hfixed_map_le b hb_ne

omit [IsMinCE G] in
private theorem CFSG.section9_t91_generated_le_of_centralizers_le
    {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hB : B ∈ section9ElementaryAbelianPSubgroupsIn p M)
    (hBnoncyclic : ¬ IsCyclic B)
    (hcentralizers : ∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M) :
    section9GeneratedPPrimeFamily (⊤ : Subgroup G) B p ≤ M := by
  classical
  refine sSup_le ?_
  intro K hK
  exact
    section9_t91_family_member_le_of_centralizers_le
      hB.2 hBnoncyclic hcentralizers hK


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_PPrimeFamily_of_le_normalizer
    {p : ℕ} [Fact p.Prime] {H A P K : Subgroup G}
    (hAP : A ≤ P) (hK : K ∈ section9PPrimeFamily H P p) :
    K ∈ section9PPrimeFamily H A p := by
  exact ⟨hK.1, hK.2.1, hAP.trans hK.2.2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_family_member_le_of_generated_le
    {p : ℕ} [Fact p.Prime] {M A K : Subgroup G}
    (hgen : section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p ≤ M)
    (hK : K ∈ section9PPrimeFamily (⊤ : Subgroup G) A p) :
    K ≤ M :=
  (le_sSup hK).trans hgen

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_family_member_le_of_generated_le_of_le_normalizer
    {p : ℕ} [Fact p.Prime] {M A P K : Subgroup G}
    (hAP : A ≤ P)
    (hgen : section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p ≤ M)
    (hK : K ∈ section9PPrimeFamily (⊤ : Subgroup G) P p) :
    K ≤ M :=
  section9_family_member_le_of_generated_le hgen
    (section9_PPrimeFamily_of_le_normalizer hAP hK)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_pPrimeCore_map_subtype_subgroupOf
    {p : ℕ} (X : Subgroup G) :
    (((pPrimeCore p X).map X.subtype).subgroupOf X) = pPrimeCore p X := by
  change ((pPrimeCore p X).map X.subtype).comap X.subtype = pPrimeCore p X
  exact
    Subgroup.comap_map_eq_self_of_injective
      (H := pPrimeCore p X) (f := X.subtype) X.subtype_injective

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_pPrimeCore_map_subtype_le
    {p : ℕ} (X : Subgroup G) :
    (pPrimeCore p X).map X.subtype ≤ X := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_IsPiSubgroup_map
    {G' : Type*} [Group G'] {π : Set Nat.Primes}
    {H : Subgroup G} (hH : IsPiSubgroup (G := G) π H) (f : G →* G') :
    IsPiSubgroup (G := G') π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))

omit [IsMinCE G] in
private theorem CFSG.section9_pPrimeCore_map_mem_PPrimeFamily_of_le
    {p : ℕ} [Fact p.Prime] {A X : Subgroup G} (hAX : A ≤ X) :
    (pPrimeCore p X).map X.subtype ∈
      section9PPrimeFamily (⊤ : Subgroup G) A p := by
  classical
  let Q : Subgroup G := (pPrimeCore p X).map X.subtype
  have hQ_le_X : Q ≤ X := section9_pPrimeCore_map_subtype_le (p := p) X
  have hQsub_eq : Q.subgroupOf X = pPrimeCore p X := by
    simpa [Q] using section9_pPrimeCore_map_subtype_subgroupOf (G := G) (p := p) X
  have hQsub_norm : (Q.subgroupOf X).Normal := by
    rw [hQsub_eq]
    infer_instance
  have hX_norm_Q : X ≤ Subgroup.normalizer (Q : Set G) := by
    exact Subgroup.le_normalizer_of_normal_subgroupOf (H := Q) (K := X) hQ_le_X
  have hQpiX :
      IsPiSubgroup (G := X) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) (pPrimeCore p X) :=
    section9_isPiSubgroup_singleton_compl_of_coprime_card
      (G := X) (p := p) (H := pPrimeCore p X)
      (pPrimeCore_coprime_card (G := X) (p := p))
  have hQpi : IsPiSubgroup (G := G) (section9PPrimeSet p) Q := by
    simpa [Q, section9PPrimeSet] using section9_IsPiSubgroup_map hQpiX X.subtype
  exact ⟨le_top, hQpi, hAX.trans hX_norm_Q⟩

omit [IsMinCE G] in
private theorem CFSG.section9_pPrimeCore_map_le_of_generated_le
    {p : ℕ} [Fact p.Prime] {M A X : Subgroup G}
    (hAX : A ≤ X)
    (hgen : section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p ≤ M) :
    (pPrimeCore p X).map X.subtype ≤ M :=
  section9_family_member_le_of_generated_le hgen
    (section9_pPrimeCore_map_mem_PPrimeFamily_of_le hAX)

omit [IsMinCE G] in
private theorem CFSG.section9_pPrimeCore_map_le_generatedPPrimeFamily_of_le
    {p : ℕ} [Fact p.Prime] {A X : Subgroup G} (hAX : A ≤ X) :
    (pPrimeCore p X).map X.subtype ≤
      section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p :=
  le_sSup (section9_pPrimeCore_map_mem_PPrimeFamily_of_le hAX)

public theorem CFSG.section9_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (N : Subgroup M) [N.Normal] (hNne : N ≠ ⊥) :
    Subgroup.normalizer (((N : Subgroup M).map M.subtype : Subgroup G) : Set G) = M := by
  classical
  let NG : Subgroup G := (N : Subgroup M).map M.subtype
  have hNG_le_M : NG ≤ M := by
    rintro x ⟨n, _hn, rfl⟩
    exact n.2
  have hM_le_norm : M ≤ Subgroup.normalizer (NG : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases hx with ⟨n, hn, rfl⟩
      refine ⟨(⟨m, hm⟩ : M) * n * (⟨m, hm⟩ : M)⁻¹, ?_, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance n hn ⟨m, hm⟩
      · rfl
    · intro hx
      rcases hx with ⟨n, hn, hnx⟩
      refine ⟨(⟨m, hm⟩ : M)⁻¹ * n * (⟨m, hm⟩ : M), ?_, ?_⟩
      · simpa using
          Subgroup.Normal.conj_mem inferInstance n hn ((⟨m, hm⟩ : M)⁻¹)
      · have hnx' : (n : G) = m * x * m⁻¹ := by
          simpa using hnx
        change m⁻¹ * (n : G) * m = x
        rw [hnx']
        simp [mul_assoc]
  have hnorm_proper : Subgroup.normalizer (NG : Set G) ≠ ⊤ := by
    intro htop
    have hNG_normal : NG.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hNG_normal; IsSimpleGroup.eq_bot_or_eq_top_of_normal NG) with hbot | htopNG
    · apply hNne
      ext n
      constructor
      · intro hn
        have hnG : ((n : M) : G) ∈ NG := ⟨n, hn, rfl⟩
        have hnG_bot : ((n : M) : G) ∈ (⊥ : Subgroup G) := by
          simpa [NG, hbot] using hnG
        have hn_one_G : ((n : M) : G) = 1 := by
          simpa using hnG_bot
        exact Subtype.ext (show (n : G) = 1 by simpa using hn_one_G)
      · intro hn
        rw [Subgroup.mem_bot] at hn
        simp [hn]
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        intro x hx
        have hxNG : x ∈ NG := by
          simp [NG, htopNG]
        exact hNG_le_M hxNG
      exact hM.ne_top (top_le_iff.mp htop_le_M)
  exact (hM.le_iff_eq hnorm_proper).mp hM_le_norm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic
    (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_normalizer_le_normalizer_thompsonSubgroup
    (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup S : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (thompsonSubgroup S)
    (Subgroup.normalizer (S : Set G)) ?_
  intro g x hx
  let cg : G ≃* G := MulAut.conj g
  have hmap_le : (thompsonSubgroup S).map cg.toMonoidHom ≤ thompsonSubgroup S := by
    change (sSup (thompsonAbelianSubgroups S)).map cg.toMonoidHom ≤
      sSup (thompsonAbelianSubgroups S)
    conv_lhs => rw [sSup_eq_iSup' (thompsonAbelianSubgroups S)]
    rw [Subgroup.map_iSup]
    refine iSup_le ?_
    intro A
    rcases A with ⟨A, hA⟩
    have hAmap_le_S : A.map cg.toMonoidHom ≤ S := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp g.property a).1 (hA.1 ha)
    have hAmap_comm : IsMulCommutative (A.map cg.toMonoidHom) := by
      let : IsMulCommutative A := hA.2.1
      simpa [cg] using (Subgroup.map_isMulCommutative (f := cg.toMonoidHom) (H := A))
    have hAmap_max :
        ∀ B : Subgroup G, B ≤ S → IsMulCommutative B →
          Nat.card B ≤ Nat.card (A.map cg.toMonoidHom) := by
      intro B hBS hBcomm
      let cgInv : G ≃* G := MulAut.conj g⁻¹
      have hBmap_le_S : B.map cgInv.toMonoidHom ≤ S := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨b, hb, rfl⟩
        have hgInv : (g : G)⁻¹ ∈ Subgroup.normalizer (S : Set G) := by
          exact (Subgroup.inv_mem_iff (H := Subgroup.normalizer (S : Set G))).2 g.property
        exact (Subgroup.mem_normalizer_iff.mp hgInv b).1 (hBS hb)
      have hBmap_comm : IsMulCommutative (B.map cgInv.toMonoidHom) := by
        let : IsMulCommutative B := hBcomm
        simpa [cgInv] using
          (Subgroup.map_isMulCommutative (f := cgInv.toMonoidHom) (H := B))
      have hcard_le : Nat.card (B.map cgInv.toMonoidHom) ≤ Nat.card A :=
        hA.2.2 (B.map cgInv.toMonoidHom) hBmap_le_S hBmap_comm
      have hcard_Bmap : Nat.card (B.map cgInv.toMonoidHom) = Nat.card B :=
        Subgroup.card_map_of_injective (K := B) (f := cgInv.toMonoidHom) cgInv.injective
      have hcard_Amap : Nat.card (A.map cg.toMonoidHom) = Nat.card A :=
        Subgroup.card_map_of_injective (K := A) (f := cg.toMonoidHom) cg.injective
      calc
        Nat.card B = Nat.card (B.map cgInv.toMonoidHom) := hcard_Bmap.symm
        _ ≤ Nat.card A := hcard_le
        _ = Nat.card (A.map cg.toMonoidHom) := hcard_Amap.symm
    exact le_sSup (show A.map cg.toMonoidHom ∈ thompsonAbelianSubgroups S from
      ⟨hAmap_le_S, hAmap_comm, hAmap_max⟩)
  have hxmap : g * x * g⁻¹ ∈ (thompsonSubgroup S).map cg.toMonoidHom := by
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [cg, MulAut.conj_apply]⟩
  exact hmap_le hxmap

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_normalizer_le_normalizer_centerIn
    (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((centerIn (G := G) H : Subgroup G) : Set G) := by
  have h :=
    section9_normalizer_le_normalizer_map_subtype_of_characteristic
      (G := G) H (Subgroup.center H)
  simpa [centerIn_eq_map_center_local] using h

omit [Finite G] [IsMinCE G] in
private lemma CFSG.section9_mem_PPrimeFamily_top_conjBy_of_mem_normalizer
    {p : ℕ} [Fact p.Prime] {A Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hQ : Q ∈ section9PPrimeFamily (⊤ : Subgroup G) A p) :
    Q.conjBy g ∈ section9PPrimeFamily (⊤ : Subgroup G) A p := by
  rcases hQ with ⟨_, hQπ, hAnormQ⟩
  have hg_inv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem hg
  refine ⟨le_top, ?_, ?_⟩
  · simpa [Subgroup.conjBy, section9PPrimeFamily] using
      section9_IsPiSubgroup_map
        (G := G) (G' := G) (π := section9PPrimeSet p)
        hQπ (MulAut.conj g).toMonoidHom
  · refine subgroup_le_normalizer_of_conj_mem (Q.conjBy g) A ?_
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hgaA : g⁻¹ * a * g ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp hg_inv (a : G)).1 a.property
    have hy' : (g⁻¹ * a * g) * y * (g⁻¹ * a * g)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAnormQ hgaA) y).1 hy
    exact Subgroup.mem_map.mpr ⟨_, hy', by
      simp [mul_assoc]⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_normalizer_le_normalizer_generatedPPrimeFamily
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer
        ((section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem
    (section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p)
    (Subgroup.normalizer (A : Set G)) ?_
  intro g x hx
  let cg : G ≃* G := MulAut.conj g
  have hmap_le :
      (section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p).map cg.toMonoidHom ≤
        section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p := by
    change (sSup (section9PPrimeFamily (⊤ : Subgroup G) A p)).map cg.toMonoidHom ≤
      sSup (section9PPrimeFamily (⊤ : Subgroup G) A p)
    conv_lhs => rw [sSup_eq_iSup' (section9PPrimeFamily (⊤ : Subgroup G) A p)]
    rw [Subgroup.map_iSup]
    refine iSup_le ?_
    intro Q
    rcases Q with ⟨Q, hQ⟩
    exact le_sSup
      (show Q.conjBy g ∈ section9PPrimeFamily (⊤ : Subgroup G) A p from
        section9_mem_PPrimeFamily_top_conjBy_of_mem_normalizer g.property hQ)
  have hxmap :
      g * x * g⁻¹ ∈
        (section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p).map cg.toMonoidHom := by
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [cg, MulAut.conj_apply]⟩
  exact hmap_le hxmap

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_normalizer_le_of_generatedPPrimeFamily_eq_pPrimeCore_map
    {p : ℕ} [Fact p.Prime] {M A : Subgroup G}
    (hNormCore :
      pPrimeCore p M ≠ ⊥ →
        Subgroup.normalizer
          ((((pPrimeCore p M : Subgroup M).map M.subtype : Subgroup G)) : Set G) = M)
    (hgen_eq :
      section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p =
        (pPrimeCore p M).map M.subtype)
    (hOpM_ne_bot : pPrimeCore p M ≠ ⊥) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hNorm_gen :
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer
          (((pPrimeCore p M).map M.subtype : Subgroup G) : Set G) := by
    simpa [hgen_eq] using section9_normalizer_le_normalizer_generatedPPrimeFamily (G := G) (p := p) A
  exact hNorm_gen.trans (le_of_eq (hNormCore hOpM_ne_bot))

omit [IsMinCE G] in
public theorem CFSG.section9_sylow_map_subtype_of_normalizer_le
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p M)
    (hN : Subgroup.normalizer
        ((((P : Subgroup M).map M.subtype : Subgroup G)) : Set G) ≤ M) :
    ∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = (P : Subgroup M).map M.subtype := by
  classical
  let PG : Subgroup G := (P : Subgroup M).map M.subtype
  have hPGp : IsPGroup p PG := by
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  suffices hnot : ¬ p ∣ PG.index by
    exact ⟨hPGp.toSylow hnot, rfl⟩
  intro hpidx
  rcases hPGp.exists_card_eq with ⟨n, hPGcard⟩
  have hdvdG : p ^ (n + 1) ∣ Nat.card G := by
    rcases hpidx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      Nat.card G = Nat.card PG * PG.index := by rw [PG.card_mul_index]
      _ = p ^ n * (p * a) := by rw [hPGcard, ha]
      _ = p ^ (n + 1) * a := by rw [pow_succ']; ac_rfl
  have hdvd_norm :
      p ^ (n + 1) ∣ Nat.card (Subgroup.normalizer (PG : Set G)) := by
    exact Sylow.prime_pow_dvd_card_normalizer (G := G) (p := p) (n := n)
      (H := PG) hdvdG hPGcard
  have hnorm_card_dvd_M :
      Nat.card (Subgroup.normalizer (PG : Set G)) ∣ Nat.card M := by
    let N : Subgroup G := Subgroup.normalizer (PG : Set G)
    have hcard_eq : Nat.card N = Nat.card (N.subgroupOf M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := N) (K := M) (by
        simpa [N, PG] using hN)).toEquiv.symm
    rw [hcard_eq]
    exact Subgroup.card_subgroup_dvd_card (N.subgroupOf M)
  have hdvdM : p ^ (n + 1) ∣ Nat.card M := hdvd_norm.trans hnorm_card_dvd_M
  have hPGcard_eq_P : Nat.card PG = Nat.card (P : Subgroup M) := by
    simpa [PG] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup M)) (f := M.subtype) M.subtype_injective)
  have hPcard : Nat.card (P : Subgroup M) = p ^ n := by
    rw [← hPGcard_eq_P]
    exact hPGcard
  have hp_dvd_P_index : p ∣ (P : Subgroup M).index := by
    have hdvd' : p ^ n * p ∣ p ^ n * (P : Subgroup M).index := by
      have hMcard : Nat.card M = p ^ n * (P : Subgroup M).index := by
        rw [← (P : Subgroup M).card_mul_index, hPcard]
      simpa [hMcard, pow_succ] using hdvdM
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (Fact.out : Nat.Prime p).pos n) hdvd'
  exact P.not_dvd_index hp_dvd_P_index

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_thompsonSubgroup_map_injective
    {G' : Type*} [Group G'] (S : Subgroup G) (f : G →* G')
    (hf : Function.Injective f) :
    thompsonSubgroup (S.map f) = (thompsonSubgroup S).map f := by
  classical
  apply le_antisymm
  · rw [thompsonSubgroup]
    refine sSup_le ?_
    intro B hB
    let A : Subgroup G := B.comap f ⊓ S
    have hA_le_S : A ≤ S := inf_le_right
    have hAcomm : IsMulCommutative A := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have hxB : f (x : G) ∈ B := x.2.1
      have hyB : f (y : G) ∈ B := y.2.1
      let : IsMulCommutative B := hB.2.1
      have hcomm := setLike_mul_comm (s := B) hxB hyB
      apply Subtype.ext
      exact hf (by simpa using hcomm)
    have hB_eq_Amap : B = A.map f := by
      apply le_antisymm
      · intro b hb
        have hbSmap : b ∈ S.map f := hB.1 hb
        rcases Subgroup.mem_map.mp hbSmap with ⟨s, hs, hsb⟩
        refine Subgroup.mem_map.mpr ?_
        refine ⟨s, ?_, hsb⟩
        exact ⟨by simpa [hsb] using hb, hs⟩
      · intro b hb
        rcases Subgroup.mem_map.mp hb with ⟨a, ha, rfl⟩
        exact ha.1
    have hA_mem : A ∈ thompsonAbelianSubgroups S := by
      refine ⟨hA_le_S, hAcomm, ?_⟩
      intro C hCS hCcomm
      have hCmap_le_Smap : C.map f ≤ S.map f := Subgroup.map_mono hCS
      have hCmap_comm : IsMulCommutative (C.map f) := by
        let : IsMulCommutative C := hCcomm
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := C))
      have hcard_le : Nat.card (C.map f) ≤ Nat.card B :=
        hB.2.2 (C.map f) hCmap_le_Smap hCmap_comm
      have hcard_Cmap : Nat.card (C.map f) = Nat.card C :=
        Subgroup.card_map_of_injective (K := C) (f := f) hf
      have hcard_Amap : Nat.card (A.map f) = Nat.card A :=
        Subgroup.card_map_of_injective (K := A) (f := f) hf
      calc
        Nat.card C = Nat.card (C.map f) := hcard_Cmap.symm
        _ ≤ Nat.card B := hcard_le
        _ = Nat.card (A.map f) := by rw [← hB_eq_Amap]
        _ = Nat.card A := hcard_Amap
    have hA_le_J : A ≤ thompsonSubgroup S := le_sSup hA_mem
    calc
      B = A.map f := hB_eq_Amap
      _ ≤ (thompsonSubgroup S).map f := Subgroup.map_mono hA_le_J
  · change (sSup (thompsonAbelianSubgroups S)).map f ≤
      sSup (thompsonAbelianSubgroups (S.map f))
    conv_lhs => rw [sSup_eq_iSup' (thompsonAbelianSubgroups S)]
    rw [Subgroup.map_iSup]
    refine iSup_le ?_
    intro A
    rcases A with ⟨A, hA⟩
    have hAmap_mem : A.map f ∈ thompsonAbelianSubgroups (S.map f) := by
      refine ⟨Subgroup.map_mono hA.1, ?_, ?_⟩
      · let : IsMulCommutative A := hA.2.1
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      · intro B hB_le_Smap hBcomm
        let C : Subgroup G := B.comap f ⊓ S
        have hC_le_S : C ≤ S := inf_le_right
        have hCcomm : IsMulCommutative C := by
          refine ⟨⟨fun x y => ?_⟩⟩
          have hxB : f (x : G) ∈ B := x.2.1
          have hyB : f (y : G) ∈ B := y.2.1
          let : IsMulCommutative B := hBcomm
          have hcomm := setLike_mul_comm (s := B) hxB hyB
          apply Subtype.ext
          exact hf (by simpa using hcomm)
        have hB_eq_Cmap : B = C.map f := by
          apply le_antisymm
          · intro b hb
            have hbSmap : b ∈ S.map f := hB_le_Smap hb
            rcases Subgroup.mem_map.mp hbSmap with ⟨s, hs, hsb⟩
            refine Subgroup.mem_map.mpr ?_
            refine ⟨s, ?_, hsb⟩
            exact ⟨by simpa [hsb] using hb, hs⟩
          · intro b hb
            rcases Subgroup.mem_map.mp hb with ⟨c, hc, rfl⟩
            exact hc.1
        have hcard_le : Nat.card C ≤ Nat.card A := hA.2.2 C hC_le_S hCcomm
        have hcard_Cmap : Nat.card (C.map f) = Nat.card C :=
          Subgroup.card_map_of_injective (K := C) (f := f) hf
        have hcard_Amap : Nat.card (A.map f) = Nat.card A :=
          Subgroup.card_map_of_injective (K := A) (f := f) hf
        calc
          Nat.card B = Nat.card (C.map f) := by rw [hB_eq_Cmap]
          _ = Nat.card C := hcard_Cmap
          _ ≤ Nat.card A := hcard_le
          _ = Nat.card (A.map f) := hcard_Amap.symm
    exact le_sSup hAmap_mem

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_centerIn_map_injective
    {G' : Type*} [Group G'] (H : Subgroup G) (f : G →* G')
    (hf : Function.Injective f) :
    centerIn (G := G') (H.map f) = (centerIn (G := G) H).map f := by
  ext y
  constructor
  · intro hy
    rcases hy.1 with ⟨h, hh, hfy⟩
    refine ⟨h, ?_, hfy⟩
    refine ⟨hh, ?_⟩
    change h ∈ Subgroup.centralizer (H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hycent : y ∈ Subgroup.centralizer ((H.map f : Subgroup G') : Set G') := hy.2
    have hcent :=
      (Subgroup.mem_centralizer_iff.mp hycent) (f k)
        (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    rw [← hfy] at hcent
    exact hf (by simpa using hcent)
  · intro hy
    rcases hy with ⟨h, hhcenter, hfy⟩
    refine ⟨?_, ?_⟩
    · exact ⟨h, hhcenter.1, hfy⟩
    · change y ∈ Subgroup.centralizer ((H.map f : Subgroup G') : Set G')
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with ⟨k, hk, hfkz⟩
      rw [← hfy, ← hfkz]
      have hhcent : h ∈ Subgroup.centralizer (H : Set G) := hhcenter.2
      have hcomm := (Subgroup.mem_centralizer_iff.mp hhcent) k hk
      simpa using congrArg f hcomm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_sup_ne_bot_of_left_ne_bot
    {A B : Subgroup G} (hA : A ≠ ⊥) :
    A ⊔ B ≠ ⊥ := by
  intro hsup
  apply hA
  exact le_bot_iff.mp (le_sup_left.trans (le_of_eq hsup))


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_sup_isMulCommutative_of_le_centralizer
    {A B : Subgroup G} (hAcomm : IsMulCommutative A)
    (hBcomm : IsMulCommutative B) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  have hcomm :
      ∀ x ∈ ((A : Set G) ∪ (B : Set G)), ∀ y ∈ ((A : Set G) ∪ (B : Set G)),
        x * y = y * x := by
    intro x hx y hy
    rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
    · exact setLike_mul_comm (s := A) hxA hyA
    · exact ((Subgroup.mem_centralizer_iff.mp (hAB hxA)) y hyB).symm
    · exact (Subgroup.mem_centralizer_iff.mp (hAB hyA)) x hxB
    · exact setLike_mul_comm (s := B) hxB hyB
  exact Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm x hx y hy)

omit [IsMinCE G] in
private theorem CFSG.section9_exists_mem_thompsonAbelianSubgroups
    (S : Subgroup G) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups S := by
  classical
  let s : Set (Subgroup G) := {A | A ≤ S ∧ IsMulCommutative A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    exact ⟨bot_le, inferInstance⟩
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximalFor (fun A : Subgroup G => Nat.card A) s hsne
  refine ⟨A, ?_⟩
  refine ⟨hAmax.1.1, hAmax.1.2, ?_⟩
  intro B hBS hBcomm
  exact hAmax.le ⟨hBS, hBcomm⟩

omit [IsMinCE G] in
private theorem CFSG.section9_centerIn_le_thompsonSubgroup
    (S : Subgroup G) :
    centerIn (G := G) S ≤ thompsonSubgroup S := by
  classical
  intro z hz
  obtain ⟨A, hA⟩ := section9_exists_mem_thompsonAbelianSubgroups (G := G) S
  let Z : Subgroup G := A ⊔ centerIn (G := G) S
  have hZ_le_S : Z ≤ S := by
    exact sup_le hA.1 inf_le_left
  have hcenter_comm : IsMulCommutative (centerIn (G := G) S) := by
    refine (Subgroup.le_centralizer_iff_isMulCommutative
      (K := centerIn (G := G) S)).1 ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2) y hy.1
  have hA_center : A ≤ Subgroup.centralizer ((centerIn (G := G) S : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hy.2) a (hA.1 ha)).symm
  have hZcomm : IsMulCommutative Z := by
    simpa [Z] using
      section9_sup_isMulCommutative_of_le_centralizer hA.2.1 hcenter_comm hA_center
  have hZcard_le_A : Nat.card Z ≤ Nat.card A :=
    hA.2.2 Z hZ_le_S hZcomm
  have hA_le_Z : A ≤ Z := le_sup_left
  have hA_eq_Z : A = Z := Subgroup.eq_of_le_of_card_ge hA_le_Z hZcard_le_A
  have hzA : z ∈ A := by
    have hzZ : z ∈ Z := (show centerIn (G := G) S ≤ Z from le_sup_right) hz
    simpa [hA_eq_Z] using hzZ
  exact (le_sSup hA) hzA

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_thompsonSubgroup_le
    (S : Subgroup G) :
    thompsonSubgroup S ≤ S := by
  rw [thompsonSubgroup]
  exact sSup_le (fun A hA => hA.1)

omit [IsMinCE G] in
private theorem CFSG.section9_centerIn_ne_bot_of_isPGroup_ne_bot
    {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hSp : IsPGroup p S) (hSne : S ≠ ⊥) :
    centerIn (G := G) S ≠ ⊥ := by
  classical
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  have hcenter_ne_bot : Subgroup.center S ≠ ⊥ :=
    (ne_of_gt (IsPGroup.bot_lt_center (p := p) (G := S) hSp))
  intro hcenterIn_bot
  apply hcenter_ne_bot
  ext z
  constructor
  · intro hz
    have hzMap : ((z : S) : G) ∈ (Subgroup.center S).map S.subtype := ⟨z, hz, rfl⟩
    have hzCenterIn : ((z : S) : G) ∈ centerIn (G := G) S := by
      simpa [centerIn_eq_map_center_local] using hzMap
    have hzBot : ((z : S) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hcenterIn_bot] using hzCenterIn
    have hz_one : ((z : S) : G) = 1 := by simpa using hzBot
    exact Subtype.ext hz_one
  · intro hz
    rw [Subgroup.mem_bot] at hz
    simp [hz]

omit [IsMinCE G] in
private theorem CFSG.section9_centerIn_thompsonSubgroup_ne_bot_of_isPGroup_ne_bot
    {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hSp : IsPGroup p S) (hSne : S ≠ ⊥) :
    centerIn (G := G) (thompsonSubgroup S) ≠ ⊥ := by
  classical
  have hcenterS_ne_bot : centerIn (G := G) S ≠ ⊥ :=
    section9_centerIn_ne_bot_of_isPGroup_ne_bot (G := G) (p := p) hSp hSne
  have hJ_le_S : thompsonSubgroup S ≤ S :=
    section9_thompsonSubgroup_le (G := G) S
  have hcenterS_le_centerJ :
      centerIn (G := G) S ≤ centerIn (G := G) (thompsonSubgroup S) := by
    intro z hz
    refine ⟨section9_centerIn_le_thompsonSubgroup (G := G) S hz, ?_⟩
    exact (Subgroup.mem_centralizer_iff
      (g := z) (s := ((thompsonSubgroup S : Subgroup G) : Set G))).2 <| by
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hz.2) y (hJ_le_S hy)
  intro hcenterJ_bot
  exact hcenterS_ne_bot
    (le_bot_iff.mp (hcenterS_le_centerJ.trans (le_of_eq hcenterJ_bot)))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_inf_eq_bot_of_isPGroup_and_coprime_card
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hHp : IsPGroup p H) (hKcop : Nat.Coprime p (Nat.card K)) :
    H ⊓ K = ⊥ := by
  have hHKsub_p : IsPGroup p ((H ⊓ K).subgroupOf H) :=
    IsPGroup.to_subgroup (H := (H ⊓ K).subgroupOf H) hHp
  have hHKp : IsPGroup p ↥(H ⊓ K) := by
    exact hHKsub_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := H) inf_le_left)
  have hHKcard_dvd : Nat.card ↥(H ⊓ K) ∣ Nat.card K := by
    have hsub_dvd : Nat.card ((H ⊓ K).subgroupOf K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card ((H ⊓ K).subgroupOf K)
    have hcard_eq : Nat.card ((H ⊓ K).subgroupOf K) = Nat.card ↥(H ⊓ K) := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
    rwa [hcard_eq] at hsub_dvd
  have hHKcop : Nat.Coprime p (Nat.card ↥(H ⊓ K)) :=
    Nat.Coprime.of_dvd_right hHKcard_dvd hKcop
  have hcard_one : Nat.card ↥(H ⊓ K) = 1 := by
    rcases hHKp.card_eq_or_dvd with h1 | hpdiv
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHKcop) hpdiv
  exact Subgroup.card_eq_one.mp hcard_one

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_pCore_le_sylow
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    pCore p G ≤ (S : Subgroup G) := by
  have hsup_p : IsPGroup p (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) := by
    exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup G)) (K := pCore p G)
      S.isPGroup' (pCore_isPGroup (G := G) (p := p))
  have hEq : (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) = (S : Subgroup G) :=
    S.3 hsup_p le_sup_left
  exact sup_eq_left.mp hEq

omit [IsMinCE G] in
public theorem CFSG.section9_fitting_le_pCore_sup_pPrimeCore
    {p : ℕ} [Fact p.Prime] :
    fittingSubgroup G ≤ pCore p G ⊔ pPrimeCore p G := by
  have hnilF : Group.IsNilpotent (fittingSubgroup G) := by infer_instance
  have hF_le_iSup :
      fittingSubgroup G ≤ ⨆ q : (Nat.card G).primeFactors.attach, pCore q.1 G :=
    normal_nilpotent_le_sup_pCore
      (G := G) (N := fittingSubgroup G) (hN := inferInstance) hnilF
  refine hF_le_iSup.trans ?_
  refine iSup_le ?_
  intro q
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := G) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 G)) := by
      rw [hn]
      have hpq : p ≠ q.1 := by
        intro hpq'
        exact hqp hpq'.symm
      exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact
      (le_sSup (show pCore q.1 G ∈ {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
        ⟨inferInstance, hcop⟩)).trans le_sup_right

omit [IsMinCE G] in
private theorem CFSG.section9_pPrime_subgroup_le_pPrimeCore_of_sylow_normalizes
    {p : ℕ} [Fact p.Prime] (hsolv : Group.IsSolvable G) (P : Sylow p G)
    {K : Subgroup G} (hKcop : Nat.Coprime p (Nat.card K))
    (hPnorm : (P : Subgroup G) ≤ Subgroup.normalizer (K : Set G)) :
    K ≤ pPrimeCore p G := by
  classical
  let M : Subgroup G := pPrimeCore p G
  have : M.Normal := by
    dsimp [M]
    infer_instance
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Kbar : Subgroup (G ⧸ M) := K.map q
  let Pbar : Sylow p (G ⧸ M) := P.mapSurjective (QuotientGroup.mk'_surjective M)
  have hKbar_cop : Nat.Coprime p (Nat.card Kbar) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := K) q) hKcop
  have hpCore_inf_Kbar : pCore p (G ⧸ M) ⊓ Kbar = ⊥ := by
    exact section9_inf_eq_bot_of_isPGroup_and_coprime_card
      (G := G ⧸ M) (p := p) (pCore_isPGroup (G := G ⧸ M) (p := p)) hKbar_cop
  have hPbar_norm_Kbar :
      (Pbar : Subgroup (G ⧸ M)) ≤ Subgroup.normalizer (Kbar : Set (G ⧸ M)) := by
    intro x hx
    have hxPmap : x ∈ (P : Subgroup G).map q := by
      rw [Sylow.coe_mapSurjective] at hx
      exact hx
    rcases Subgroup.mem_map.mp hxPmap with ⟨x₀, hx₀P, rfl⟩
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y₀, hy₀K, rfl⟩
    have hconj : x₀ * y₀ * x₀⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm hx₀P) y₀).1 hy₀K
    exact Subgroup.mem_map.mpr ⟨x₀ * y₀ * x₀⁻¹, hconj, by simp [q, mul_assoc]⟩
  have hpCore_le_Pbar : pCore p (G ⧸ M) ≤ (Pbar : Subgroup (G ⧸ M)) :=
    section9_pCore_le_sylow Pbar
  have hKbar_le_cent_pCore :
      Kbar ≤ Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htPbar : t ∈ (Pbar : Subgroup (G ⧸ M)) := hpCore_le_Pbar ht
    have htNorm : t ∈ Subgroup.normalizer (Kbar : Set (G ⧸ M)) :=
      hPbar_norm_Kbar htPbar
    have hcomm_Kbar : ⁅t, k⁆ ∈ Kbar := by
      have hconj : t * k * t⁻¹ ∈ Kbar :=
        (Subgroup.mem_normalizer_iff.mp htNorm k).1 hk
      change t * k * t⁻¹ * k⁻¹ ∈ Kbar
      exact Kbar.mul_mem hconj (Kbar.inv_mem hk)
    have hcomm_pCore : ⁅t, k⁆ ∈ pCore p (G ⧸ M) := by
      exact
        (Subgroup.commutator_le_left (H₁ := pCore p (G ⧸ M)) (H₂ := Kbar))
          (Subgroup.commutator_mem_commutator ht hk)
    have hcomm_bot : ⁅t, k⁆ ∈ (⊥ : Subgroup (G ⧸ M)) := by
      rw [← hpCore_inf_Kbar]
      exact ⟨hcomm_pCore, hcomm_Kbar⟩
    exact (commutatorElement_eq_one_iff_mul_comm).1 (by simpa using hcomm_bot)
  have hsolvQ : Group.IsSolvable (G ⧸ M) := by infer_instance
  have hcore_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hcent_pCore_le :
      Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    have hOp_eq : Op_p'p p (G ⧸ M) = pCore p (G ⧸ M) :=
      Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hcore_bot
    let T : Sylow p (Op_p'p p (G ⧸ M)) := by
      have htop_p : IsPGroup p (⊤ : Subgroup (Op_p'p p (G ⧸ M))) := by
        rw [hOp_eq]
        simpa using
          (pCore_isPGroup (G := G ⧸ M) (p := p)).to_subgroup
            (⊤ : Subgroup (pCore p (G ⧸ M)))
      exact IsPGroup.toSylow (p := p) htop_p (by
        simpa using (Fact.out : Nat.Prime p).not_dvd_one)
    have htop_p : IsPGroup p (⊤ : Subgroup (Op_p'p p (G ⧸ M))) := by
      rw [hOp_eq]
      simpa using
        (pCore_isPGroup (G := G ⧸ M) (p := p)).to_subgroup
          (⊤ : Subgroup (pCore p (G ⧸ M)))
    have hcent :
        Subgroup.centralizer ((T.1.map (Op_p'p p (G ⧸ M)).subtype :
            Subgroup (G ⧸ M)) : Set (G ⧸ M)) ≤ Op_p'p p (G ⧸ M) :=
      proposition_1_15_a (G := G ⧸ M) (p := p) hsolvQ T
    have hTtop : (T : Subgroup (Op_p'p p (G ⧸ M))) = ⊤ :=
      T.3 htop_p le_top
    have hTmap_eq :
        (T.1.map (Op_p'p p (G ⧸ M)).subtype : Subgroup (G ⧸ M)) =
          Op_p'p p (G ⧸ M) := by
      rw [hTtop]
      ext x
      constructor
      · rintro ⟨x', _hx', rfl⟩
        exact x'.2
      · intro hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
    calc
      Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M))
          = Subgroup.centralizer
              ((T.1.map (Op_p'p p (G ⧸ M)).subtype : Subgroup (G ⧸ M)) :
                Set (G ⧸ M)) := by
            rw [hTmap_eq, hOp_eq]
      _ ≤ Op_p'p p (G ⧸ M) := hcent
      _ = pCore p (G ⧸ M) := hOp_eq
  have hKbar_le_pCore : Kbar ≤ pCore p (G ⧸ M) :=
    hKbar_le_cent_pCore.trans hcent_pCore_le
  have hKbar_bot : Kbar = ⊥ := by
    calc
      Kbar = Kbar ⊓ pCore p (G ⧸ M) := (inf_eq_left.2 hKbar_le_pCore).symm
      _ = ⊥ := by simpa [inf_comm] using hpCore_inf_Kbar
  have hK_le_ker : K ≤ q.ker := by
    have hmap_bot : K.map q = ⊥ := by
      simpa [Kbar] using hKbar_bot
    exact (Subgroup.map_eq_bot_iff (H := K) (f := q)).1 hmap_bot
  simpa [q, M] using hK_le_ker

omit [IsMinCE G] in
private theorem CFSG.section9_generatedPPrimeFamily_le_pPrimeCore_map_of_sylow
    {p : ℕ} [Fact p.Prime] {M A : Subgroup G} (hMsolv : Group.IsSolvable M)
    (P : Sylow p M) (hAeq : A = (P : Subgroup M).map M.subtype)
    (hgen_le_M : section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p ≤ M) :
    section9GeneratedPPrimeFamily (⊤ : Subgroup G) A p ≤
      (pPrimeCore p M).map M.subtype := by
  classical
  refine sSup_le ?_
  intro K hK
  have hK_le_M : K ≤ M :=
    (le_sSup hK).trans hgen_le_M
  have hKπ_singleton :
      IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) K := by
    simpa [section9PPrimeFamily, section9PPrimeSet, section7HFamily] using hK.2.1
  have hKcop : Nat.Coprime p (Nat.card K) :=
    section9_coprime_card_of_isPiSubgroup_singleton_compl hKπ_singleton
  let K_M : Subgroup M := K.subgroupOf M
  have hK_M_cop : Nat.Coprime p (Nat.card K_M) := by
    have hcard : Nat.card K_M = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hK_le_M).toEquiv
    simpa [hcard] using hKcop
  have hPnorm_KM : (P : Subgroup M) ≤ Subgroup.normalizer (K_M : Set M) := by
    intro x hx
    have hxA : ((x : M) : G) ∈ A := by
      rw [hAeq]
      exact Subgroup.mem_map_of_mem M.subtype hx
    have hxNormG : ((x : M) : G) ∈ Subgroup.normalizer (K : Set G) :=
      hK.2.2 hxA
    have hnorm_eq :
        Subgroup.normalizer (K_M : Set M) =
          (Subgroup.normalizer (K : Set G)).subgroupOf M := by
      exact (Subgroup.subgroupOf_normalizer_eq (H := K) (N := M) hK_le_M).symm
    simpa [K_M, hnorm_eq, Subgroup.mem_subgroupOf] using hxNormG
  have hK_M_le_core : K_M ≤ pPrimeCore p M :=
    section9_pPrime_subgroup_le_pPrimeCore_of_sylow_normalizes
      (G := M) (p := p) hMsolv P hK_M_cop hPnorm_KM
  intro x hxK
  have hxM : x ∈ M := hK_le_M hxK
  exact ⟨⟨x, hxM⟩, hK_M_le_core (by simpa [K_M, Subgroup.mem_subgroupOf] using hxK), rfl⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_normal_of_derivedSubgroup_le
    {R : Type*} [Group R] (N : Subgroup R) (hder : derivedSubgroup R ≤ N) :
    N.Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hcomm : ⁅g, n⁆ ∈ derivedSubgroup R := by
    change ⁅g, n⁆ ∈ derivedSeries R 1
    rw [derivedSeries_one, _root_.commutator_def]
    exact
      Subgroup.commutator_mem_commutator
        (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))
        (by simp) (by simp)
  have hconj_eq : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [hconj_eq]
  exact N.mul_mem (hder hcomm) hn

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_generatorRank_le_natCard
    (R : Type*) [Group R] [Finite R] :
    generatorRank R ≤ Nat.card R := by
  let : Fintype R := Fintype.ofFinite R
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec R
  calc
    generatorRank R = Group.rank R := generatorRank_eq_group_rank R
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card R := by simpa using Finset.card_le_univ S
    _ = Nat.card R := by simp [Nat.card_eq_fintype_card]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_primeRank_le_natCard
    {p : ℕ} (R : Type*) [Group R] [Finite R] :
    primeRank p R ≤ Nat.card R := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section9_t91_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section9_t91_exists_pSubgroup_three_le_generatorRank_of_three_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ A : Subgroup R,
      IsPGroup p.val A ∧ IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 2 < sSup S := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section9_t91_primeRank_le_natCard (p := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 2 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 2 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hqrank' : 2 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section9_t91_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAq, hAcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, A, hAq, hAcomm,
    Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_elementaryAbelian_card_ge_pow_generatorRank
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [Finite R] [IsElementaryAbelian p R] :
    p ^ generatorRank R ≤ Nat.card R := by
  let : CommGroup R := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive R) := Additive.addCommGroup
  have hcard : Nat.card R = p ^ Module.finrank (ZMod p) (Additive R) := by
    calc
      Nat.card R = Nat.card (Additive R) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ Module.finrank (ZMod p) (Additive R) := by
        simpa using Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive R)
  have hgr_le_finrank : generatorRank R ≤ Module.finrank (ZMod p) (Additive R) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) R
  rw [hcard]
  exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hgr_le_finrank

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [IsMulCommutative R] :
    IsElementaryAbelian p (omega₁ (G := R) (p := p)) := by
  let : CommGroup R := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : R | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_omega1_card_eq_card_quotient_frattini_of_commutative
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [Finite R] [IsMulCommutative R] [Fact (IsPGroup p R)] :
    Nat.card (omega₁ (G := R) (p := p)) = Nat.card (R ⧸ frattini R) := by
  classical
  let : CommGroup R := IsMulCommutative.instCommGroup
  let φ : R →* R := powMonoidHom p
  have hφker : φ.ker = omega₁ (G := R) (p := p) := by
    ext x
    constructor
    · intro hx
      change x ∈ Subgroup.closure {y : R | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [φ, pow_one] using hx
    · intro hx
      refine
        Subgroup.closure_induction (k := {y : R | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ∈ φ.ker) (x := x) (by
            intro y hy
            simpa [φ, pow_one] using hy) (by simp [φ]) (by
            intro y z _ _ hy hz
            have hy' : y ^ p = 1 := by simpa [φ] using hy
            have hz' : z ^ p = 1 := by simpa [φ] using hz
            simp [φ, mul_pow, hy', hz']) (by
            intro y _ hy
            exact φ.ker.inv_mem hy) hx
  have hφrange : φ.range = frattini R := by
    have hcomm_top :
        (⊤ : Subgroup R) ≤ Subgroup.centralizer (((⊤ : Subgroup R) : Set R)) := by
      intro x _hx
      rw [Subgroup.mem_centralizer_iff]
      intro y _hy
      exact mul_comm y x
    have hcomm_bot : _root_.commutator R = ⊥ := by
      have htop_comm_bot : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcomm_top
      simpa [_root_.commutator_def] using htop_comm_bot
    have hderived_bot : derivedSubgroup R = ⊥ := by
      change derivedSeries R 1 = ⊥
      rw [derivedSeries_one]
      exact hcomm_bot
    have hrange :
        Set.range (fun x : R => x ^ p) = ((φ.range : Subgroup R) : Set R) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [φ]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa [φ] using hx⟩
    have hfrattini : frattini R = φ.range := by
      calc
        frattini R =
            Subgroup.closure ((derivedSubgroup R : Set R) ∪ Set.range (fun x : R => x ^ p)) := by
              simpa using (lemma_1_7_d (R := R) (p := p))
        _ = Subgroup.closure (Set.range (fun x : R => x ^ p)) := by
              rw [hderived_bot]
              simp
        _ = Subgroup.closure ((φ.range : Subgroup R) : Set R) := by rw [hrange]
        _ = φ.range := by simpa using (Subgroup.closure_eq (K := φ.range))
    exact hfrattini.symm
  have hcard_range :
      Nat.card (R ⧸ φ.ker) = Nat.card φ.range := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hmul_ker :
      Nat.card R = Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) := by
    calc
      Nat.card R = Nat.card (R ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hcard_range]
      _ = Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) := by
        rw [hφrange, hφker]
  have hmul_frattini :
      Nat.card R = Nat.card (frattini R) * Nat.card (R ⧸ frattini R) := by
    calc
      Nat.card R = Nat.card (R ⧸ frattini R) * Nat.card (frattini R) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := frattini R)
      _ = Nat.card (frattini R) * Nat.card (R ⧸ frattini R) := by
        rw [Nat.mul_comm]
  have hΦpos : 0 < Nat.card (frattini R) := Nat.card_pos (α := frattini R)
  have hmul_eq :
      Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) =
        Nat.card (frattini R) * Nat.card (R ⧸ frattini R) :=
    hmul_ker.symm.trans hmul_frattini
  exact Nat.eq_of_mul_eq_mul_left hΦpos hmul_eq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_isElementaryAbelian_map
    {p : ℕ} [Fact p.Prime]
    {R S : Type*} [Group R] [Group S] {A : Subgroup R}
    [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : S) = f y := by simpa using hyx.symm
  calc
    (x : S) ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section9_t91_generatorRank_map_injective_eq
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (A : Subgroup R) (f : R →* S) (hf : Function.Injective f) :
    generatorRank (A.map f) = generatorRank A := by
  rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
  let e : A ≃* A.map f := Subgroup.equivMapOfInjective (f := f) A hf
  exact (Group.rank_congr e).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : p ^ 3 ≤ Nat.card A) :
    3 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by
          simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  have hcard_le : Nat.card A ≤ p ^ Group.rank A :=
    Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hcard_dvd
  have hpow_le : p ^ 3 ≤ p ^ Group.rank A := hA.trans hcard_le
  have hrank : 3 ≤ Group.rank A :=
    (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le
  simpa [generatorRank_eq_group_rank] using hrank

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_exists_elementaryAbelian_three_le_generatorRank_of_three_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ E : Subgroup R, IsElementaryAbelian p.val E ∧
      3 ≤ generatorRank E := by
  classical
  obtain ⟨p, A, hAp, hAcomm, hAgen⟩ :=
    section9_t91_exists_pSubgroup_three_le_generatorRank_of_three_le_groupRank (R := R) hrank
  let : Fact p.val.Prime := ⟨p.property⟩
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p.val)
  have : Fact (IsPGroup p.val A) := ⟨hAp⟩
  have hΩelem : IsElementaryAbelian p.val Ωsub := by
    let : IsMulCommutative A := hAcomm
    simpa [Ωsub] using
      section9_t91_omega1_isElementaryAbelian_of_commutative (p := p.val) A
  have hΩcard :
      Nat.card Ωsub = Nat.card (A ⧸ frattini A) := by
    let : IsMulCommutative A := hAcomm
    simpa [Ωsub] using
      section9_t91_omega1_card_eq_card_quotient_frattini_of_commutative
        (p := p.val) A
  have hquot_rank : 3 ≤ generatorRank (A ⧸ frattini A) :=
    hAgen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p.val) A)
  have hpow_le_quot : p.val ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    let : IsElementaryAbelian p.val (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p.val)
    calc
      p.val ^ 3 ≤ p.val ^ generatorRank (A ⧸ frattini A) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p.val)) hquot_rank
      _ ≤ Nat.card (A ⧸ frattini A) := by
        exact section9_t91_elementaryAbelian_card_ge_pow_generatorRank
          (p := p.val) (A ⧸ frattini A)
  have hpow_le_Ω : p.val ^ 3 ≤ Nat.card Ωsub := by
    rw [hΩcard]
    exact hpow_le_quot
  have hΩgen : 3 ≤ generatorRank Ωsub := by
    let : IsElementaryAbelian p.val Ωsub := hΩelem
    exact
      section9_t91_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := p.val) hpow_le_Ω
  let f : A →* R := A.subtype
  let E : Subgroup R := Ωsub.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  have hEelem : IsElementaryAbelian p.val E := by
    let : IsElementaryAbelian p.val Ωsub := hΩelem
    simpa [E, f] using section9_t91_isElementaryAbelian_map (p := p.val) (A := Ωsub) f
  have hEgen : 3 ≤ generatorRank E := by
    have hgen_eq : generatorRank E = generatorRank Ωsub := by
      simpa [E, f] using
        section9_t91_generatorRank_map_injective_eq (A := Ωsub) f hf_inj
    simpa [hgen_eq] using hΩgen
  exact ⟨p, E, hEelem, hEgen⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_t91_exists_maximal_elementaryAbelianSubgroup_containing
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R] {E : Subgroup R}
    (hEelem : IsElementaryAbelian p E) :
    ∃ M : Subgroup R, E ≤ M ∧ M ∈ maximalElementaryAbelianSubgroups p R := by
  classical
  let s : Set (Subgroup R) := {A | E ≤ A ∧ IsElementaryAbelian p A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨E, le_rfl, hEelem⟩
  obtain ⟨M, hMmax⟩ := hsfin.exists_maximal hsne
  refine ⟨M, hMmax.1.1, ?_⟩
  refine ⟨hMmax.1.2, ?_⟩
  intro B hMB hBelem
  exact le_antisymm hMB (hMmax.2 ⟨hMmax.1.1.trans hMB, hBelem⟩ hMB)

omit [IsMinCE G] in
private theorem CFSG.section9_t91_primeRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} [Fact q.Prime] {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ primeRank q K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section9_t91_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩

omit [IsMinCE G] in
private theorem CFSG.section9_t91_groupRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ groupRank K := by
  let : Fact q.Prime := ⟨hq⟩
  have hqrankK : 3 ≤ primeRank q K :=
    section9_t91_primeRank_at_least_three_of_generatorRank_subgroup
      (q := q) hAK hAp hAcomm hAgen
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section9_t91_primeRank_le_natCard (p := r) K)
  · exact ⟨q, hq, hqrankK⟩

omit [IsMinCE G] in
private theorem CFSG.section9_t91_prime_dvd_card_of_nontrivial_pSubgroup
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hBp : IsPGroup p B) (hBnontrivial : Nontrivial B) :
    p ∣ Nat.card G := by
  obtain ⟨n, hn_pos, hBcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := B) (hG := hBp)).mp hBnontrivial
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hp_dvd_B : p ∣ Nat.card B := by
    rw [hBcard, pow_succ']
    exact dvd_mul_right p (p ^ m)
  exact hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)

private theorem CFSG.section9_t91_fitting_groupRank_le_two_of_no_unique
    {H : Subgroup G} (hH : H ∈ section9MaximalSubgroups G)
    (hNoUnique :
      ∀ Y : Subgroup G, Y ≤ (fittingSubgroup H).map H.subtype →
        Y ∉ section9UniqueSubgroups G) :
    groupRank (fittingSubgroup H) ≤ 2 := by
  classical
  by_contra hnot
  have hFrank : 3 ≤ groupRank (fittingSubgroup H) := by omega
  let F : Subgroup H := fittingSubgroup H
  let FG : Subgroup G := section8FittingSubgroup H
  obtain ⟨q, E, hEelem, hEgen⟩ :=
    section9_t91_exists_elementaryAbelian_three_le_generatorRank_of_three_le_groupRank
      (R := F) (by simpa [F] using hFrank)
  let : Fact q.val.Prime := ⟨q.property⟩
  let eF : F ≃* FG :=
    Subgroup.equivMapOfInjective (f := H.subtype) F H.subtype_injective
  let E₀ : Subgroup FG := E.map eF.toMonoidHom
  have hE₀elem : IsElementaryAbelian q.val E₀ := by
    let : IsElementaryAbelian q.val E := hEelem
    simpa [E₀] using
      section9_t91_isElementaryAbelian_map (p := q.val) (A := E) eF.toMonoidHom
  have hE₀gen : 3 ≤ generatorRank E₀ := by
    have hgen_eq : generatorRank E₀ = generatorRank E := by
      simpa [E₀] using
        section9_t91_generatorRank_map_injective_eq
          (A := E) eF.toMonoidHom eF.injective
    simpa [hgen_eq] using hEgen
  obtain ⟨A₀, hE₀_le_A₀, hA₀max⟩ :=
    section9_t91_exists_maximal_elementaryAbelianSubgroup_containing
      (p := q.val) (R := FG) (E := E₀) hE₀elem
  have hA₀elem : IsElementaryAbelian q.val A₀ := hA₀max.1
  have hE₀card_ge : q.val ^ 3 ≤ Nat.card E₀ := by
    let : IsElementaryAbelian q.val E₀ := hE₀elem
    calc
      q.val ^ 3 ≤ q.val ^ generatorRank E₀ := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime q.val)) hE₀gen
      _ ≤ Nat.card E₀ := by
        exact section9_t91_elementaryAbelian_card_ge_pow_generatorRank (p := q.val) E₀
  have hA₀card_ge : q.val ^ 3 ≤ Nat.card A₀ :=
    hE₀card_ge.trans (Subgroup.card_le_of_le hE₀_le_A₀)
  have hA₀rank : 3 ≤ generatorRank A₀ := by
    let : IsElementaryAbelian q.val A₀ := hA₀elem
    exact
      section9_t91_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := q.val) hA₀card_ge
  have hE₀nontrivial : Nontrivial E₀ := by
    by_contra hnt
    let : Subsingleton E₀ := not_nontrivial_iff_subsingleton.mp hnt
    have hcyc : IsCyclic E₀ := isCyclic_of_subsingleton (α := E₀)
    have hle : generatorRank E₀ ≤ 1 := generatorRank_le_one_of_isCyclic (G := E₀) hcyc
    omega
  have hqF : q ∈ subgroupPrimeSet FG := by
    let : IsElementaryAbelian q.val E₀ := hE₀elem
    have hdiv : q.val ∣ Nat.card FG :=
      section9_t91_prime_dvd_card_of_nontrivial_pSubgroup
        (G := FG) (p := q.val) (B := E₀)
        (IsElementaryAbelian.isPGroup q.val E₀) hE₀nontrivial
    simpa [FG, subgroupPrimeSet] using hdiv
  have hH8 : H ∈ section8MaximalSubgroups G := section8_maximal_of_section9_maximal hH
  by_cases hFGp : IsPGroup q.val FG
  · have hF_p : IsPGroup q.val F := by
      exact hFGp.of_equiv eF.symm
    obtain ⟨P, hF_le_P⟩ := IsPGroup.exists_le_sylow (G := H) (p := q.val) hF_p
    have h8 :=
      theorem_8_1 (G := G) (p := q.val) (M := H) hH8
        (by
          change (⟨q.val, Fact.out⟩ : Nat.Primes) ∈ subgroupPrimeSet FG
          exact hqF) (A₀ := A₀) hA₀max hA₀rank P
    rcases h8.2 (by simpa [FG] using hFGp) with ⟨_hPglobal, hscn_unique⟩
    let EH : Subgroup H := E.map F.subtype
    have hEH_le_P : EH ≤ (P : Subgroup H) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact hF_le_P y.2
    have hEHp : IsPGroup q.val EH := by
      let : IsElementaryAbelian q.val E := hEelem
      simpa [EH] using IsPGroup.map (p := q.val) (H := E)
        (IsElementaryAbelian.isPGroup q.val E) F.subtype
    have hEHcomm : IsMulCommutative EH := by
      let : IsElementaryAbelian q.val E := hEelem
      simpa [EH] using (Subgroup.map_isMulCommutative (f := F.subtype) (H := E))
    have hEHgen : 3 ≤ generatorRank EH := by
      have hgen_eq : generatorRank EH = generatorRank E := by
        simpa [EH] using
          section9_t91_generatorRank_map_injective_eq
            (A := E) F.subtype F.subtype_injective
      simpa [hgen_eq] using hEgen
    have hPrank : 3 ≤ groupRank (P : Subgroup H) :=
      section9_t91_groupRank_at_least_three_of_generatorRank_subgroup
        (G := H) (q := q.val) q.property
        (A := EH) (K := (P : Subgroup H)) hEH_le_P hEHp hEHcomm hEHgen
    have hqG : q.val ∣ Nat.card G := by
      have hqFG : q.val ∣ Nat.card FG := by
        simpa [FG, subgroupPrimeSet] using hqF
      exact hqFG.trans (Subgroup.card_subgroup_dvd_card FG)
    have hqodd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG
    obtain ⟨S, hSscn⟩ :=
      lemma_5_1_a (p := q.val) hqodd
        (R := ↥(P : Subgroup H)) P.isPGroup' hPrank
    have hSdata := hscn_unique S hSscn
    have hYunique : section8SylowSubgroupInAmbient H P S ∈ section9UniqueSubgroups G :=
      section9_unique_of_section8_unique hSdata.2
    have hYle : section8SylowSubgroupInAmbient H P S ≤ (fittingSubgroup H).map H.subtype := by
      change section8SylowSubgroupInAmbient H P S ≤ section8FittingSubgroup H
      exact hSdata.1
    exact hNoUnique (section8SylowSubgroupInAmbient H P S) hYle hYunique
  · let P : Sylow q.val H := default
    have h8 :=
      theorem_8_1 (G := G) (p := q.val) (M := H) hH8
        (by
          change (⟨q.val, Fact.out⟩ : Nat.Primes) ∈ subgroupPrimeSet FG
          exact hqF) (A₀ := A₀) hA₀max hA₀rank P
    let C : Subgroup G := section8CentralizerInFitting H A₀
    have hCunique : C ∈ section9UniqueSubgroups G :=
      section9_unique_of_section8_unique <| by
        simpa [C, FG] using h8.1 (by simpa [FG] using hFGp)
    have hCle : C ≤ (fittingSubgroup H).map H.subtype := by
      change section8CentralizerInFitting H A₀ ≤ section8FittingSubgroup H
      exact section8CentralizerInFitting_le H A₀
    exact hNoUnique C hCle hCunique

/-- Theorem 9.1. -/
public theorem CFSG.theorem_9_1
    {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hB : B ∈ section9ElementaryAbelianPSubgroupsIn p M)
    (hBnoncyclic : ¬ IsCyclic B)
    (hcond :
      (∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M) ∨
        section9GeneratedPPrimeFamily (⊤ : Subgroup G) B p ≤ M) :
    B ∈ section9UniqueSubgroups G := by
  classical
  have hgen_le_M : section9GeneratedPPrimeFamily (⊤ : Subgroup G) B p ≤ M := by
    rcases hcond with hcentralizers | hgenerated
    · exact section9_t91_generated_le_of_centralizers_le hB hBnoncyclic hcentralizers
    · exact hgenerated
  by_contra hBnot
  obtain ⟨H, hHmaxB, hH_ne_M, hHmax_pSylowCard⟩ :=
    section9_exists_maximal_pSylowCard_inf_overgroup_ne_of_not_unique
      (p := p) (H := B) (M := M) hM hB.1 hBnot
  have hHproper : H ≠ ⊤ := hHmaxB.1.1
  have hHsolv : Group.IsSolvable H := section9_solvable_of_proper_subgroup hHproper
  have hMsolv : Group.IsSolvable M := section9_solvable_of_proper_subgroup hM.1
  have hOpH_le_M : (pPrimeCore p H).map H.subtype ≤ M :=
    section9_pPrimeCore_map_le_of_generated_le hHmaxB.2 hgen_le_M
  have hOpH_le_H : (pPrimeCore p H).map H.subtype ≤ H :=
    section9_pPrimeCore_map_subtype_le (p := p) H
  have hNoUnique_le_OpH :
      ∀ Y : Subgroup G, Y ≤ (pPrimeCore p H).map H.subtype →
        Y ∉ section9UniqueSubgroups G := by
    intro Y hY
    exact
      section9_not_unique_of_le_two_distinct_maximal hM hHmaxB.1
        (hY.trans hOpH_le_M) (hY.trans hOpH_le_H) hH_ne_M
  let I : Subgroup G := H ⊓ M
  have hB_le_I : B ≤ I := le_inf hHmaxB.2 hB.1
  let B_I : Subgroup I := B.subgroupOf I
  have hBIp : IsPGroup p B_I := by
    let : IsElementaryAbelian p B := hB.2
    have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
    let e : B_I ≃* B := Subgroup.subgroupOfEquivOfLe (H := B) (K := I) hB_le_I
    exact hBp.of_equiv e.symm
  obtain ⟨R₀, hBI_le_R₀⟩ := IsPGroup.exists_le_sylow (p := p) hBIp
  let R : Subgroup G := (R₀ : Subgroup I).map I.subtype
  have hB_le_R : B ≤ R := by
    intro b hb
    refine ⟨⟨b, hB_le_I hb⟩, ?_, rfl⟩
    exact hBI_le_R₀ (by simpa [B_I, Subgroup.mem_subgroupOf] using hb)
  have hR_le_H : R ≤ H := by
    rintro x ⟨y, _hy, rfl⟩
    exact y.2.1
  have hR_le_M : R ≤ M := by
    rintro x ⟨y, _hy, rfl⟩
    exact y.2.2
  have hRp : IsPGroup p R := by
    exact IsPGroup.map (p := p) (H := (R₀ : Subgroup I)) R₀.isPGroup' I.subtype
  have hR_card_measure :
      section9SylowCardInf p H M = Nat.card R := by
    simpa [R, I] using
      section9SylowCardInf_eq_card_sylow_map (G := G) (p := p) H M R₀
  let R_M : Subgroup M := R.subgroupOf M
  have hRMp : IsPGroup p R_M := by
    let e : R_M ≃* R := Subgroup.subgroupOfEquivOfLe (H := R) (K := M) hR_le_M
    exact hRp.of_equiv e.symm
  obtain ⟨P, hRM_le_P⟩ := IsPGroup.exists_le_sylow (p := p) hRMp
  have hR_le_P : R ≤ (P : Subgroup M).map M.subtype := by
    intro r hr
    refine ⟨⟨r, hR_le_M hr⟩, ?_, rfl⟩
    exact hRM_le_P (by simpa [R_M, Subgroup.mem_subgroupOf] using hr)
  let P_G : Subgroup G := (P : Subgroup M).map M.subtype
  have hPGp : IsPGroup p P_G := by
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hB_le_PG : B ≤ P_G := hB_le_R.trans hR_le_P
  have hPG_le_M : P_G ≤ M := by
    rintro x ⟨y, _hy, rfl⟩
    exact y.2
  have hB_ne_bot : B ≠ ⊥ := by
    intro hBbot
    have : Subsingleton B := by
      rw [hBbot]
      infer_instance
    exact hBnoncyclic (isCyclic_of_subsingleton (α := B))
  have hPG_ne_bot : P_G ≠ ⊥ := by
    intro hPGbot
    apply hB_ne_bot
    exact le_bot_iff.mp (hB_le_PG.trans (le_of_eq hPGbot))
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ := by
    intro hPbot
    apply hPG_ne_bot
    have hmap_bot : ((P : Subgroup M).map M.subtype : Subgroup G) = ⊥ := by
      simp [hPbot]
    simpa [P_G] using hmap_bot
  have hgen_P_le_M : section9GeneratedPPrimeFamily (⊤ : Subgroup G) P_G p ≤ M := by
    refine sSup_le ?_
    intro K hK
    exact section9_family_member_le_of_generated_le_of_le_normalizer hB_le_PG hgen_le_M hK
  have hOpM_le_gen_P :
      (pPrimeCore p M).map M.subtype ≤
        section9GeneratedPPrimeFamily (⊤ : Subgroup G) P_G p :=
    section9_pPrimeCore_map_le_generatedPPrimeFamily_of_le hPG_le_M
  have hgen_P_le_OpM :
      section9GeneratedPPrimeFamily (⊤ : Subgroup G) P_G p ≤
        (pPrimeCore p M).map M.subtype := by
    exact
      section9_generatedPPrimeFamily_le_pPrimeCore_map_of_sylow
        (G := G) (p := p) (M := M) (A := P_G) hMsolv P rfl hgen_P_le_M
  have hgen_P_eq_OpM :
      section9GeneratedPPrimeFamily (⊤ : Subgroup G) P_G p =
        (pPrimeCore p M).map M.subtype :=
    le_antisymm hgen_P_le_OpM hOpM_le_gen_P
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hThompson_normal_M :
      (centerIn (thompsonSubgroup P) ⊔ pPrimeCore p M).Normal :=
    theorem_6_2 (G := M) hModd P
  have hNorm_OpM_eq_M :
      pPrimeCore p M ≠ ⊥ →
        Subgroup.normalizer
          ((((pPrimeCore p M : Subgroup M).map M.subtype : Subgroup G)) : Set G) = M := by
    intro hOpM_ne_bot
    exact
      section9_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
        hM (pPrimeCore p M) hOpM_ne_bot
  let T_M : Subgroup M := centerIn (thompsonSubgroup P) ⊔ pPrimeCore p M
  have hNorm_Thompson_join_eq_M :
      T_M ≠ ⊥ →
        Subgroup.normalizer (((T_M : Subgroup M).map M.subtype : Subgroup G) : Set G) = M := by
    intro hT_ne_bot
    have : T_M.Normal := by
      simpa [T_M] using hThompson_normal_M
    exact
      section9_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
        hM T_M hT_ne_bot
  have hCenter_Thompson_ne_bot : centerIn (G := M) (thompsonSubgroup P) ≠ ⊥ :=
    section9_centerIn_thompsonSubgroup_ne_bot_of_isPGroup_ne_bot
      (G := M) (p := p) (S := (P : Subgroup M)) P.isPGroup' hP_ne_bot
  have hT_M_ne_bot : T_M ≠ ⊥ := by
    exact section9_sup_ne_bot_of_left_ne_bot hCenter_Thompson_ne_bot
  have hNorm_Thompson_join_eq_M_unconditional :
      Subgroup.normalizer (((T_M : Subgroup M).map M.subtype : Subgroup G) : Set G) = M :=
    hNorm_Thompson_join_eq_M hT_M_ne_bot
  have hNorm_PG_le_norm_centerJ_PG :
      Subgroup.normalizer (P_G : Set G) ≤
        Subgroup.normalizer
          ((centerIn (G := G) (thompsonSubgroup P_G) : Subgroup G) : Set G) :=
    (section9_normalizer_le_normalizer_thompsonSubgroup (G := G) P_G).trans
      (section9_normalizer_le_normalizer_centerIn (G := G) (thompsonSubgroup P_G))
  have hCenter_Thompson_PG_ne_bot :
      centerIn (G := G) (thompsonSubgroup P_G) ≠ ⊥ :=
    section9_centerIn_thompsonSubgroup_ne_bot_of_isPGroup_ne_bot
      (G := G) (p := p) (S := P_G) hPGp hPG_ne_bot
  have hJ_map :
      thompsonSubgroup P_G =
        (thompsonSubgroup (P : Subgroup M)).map M.subtype := by
    simpa [P_G] using
      section9_thompsonSubgroup_map_injective
        (G := M) (G' := G) (S := (P : Subgroup M)) M.subtype M.subtype_injective
  have hCenterJ_map :
      centerIn (G := G) (thompsonSubgroup P_G) =
        (centerIn (G := M) (thompsonSubgroup (P : Subgroup M))).map M.subtype := by
    rw [hJ_map]
    exact
      section9_centerIn_map_injective
        (G := M) (G' := G) (H := thompsonSubgroup (P : Subgroup M))
        M.subtype M.subtype_injective
  have hNorm_PG_le_M_of_OpM_bot :
      pPrimeCore p M = ⊥ → Subgroup.normalizer (P_G : Set G) ≤ M := by
    intro hOpM_bot
    have hT_map_eq_centerJ :
        ((T_M : Subgroup M).map M.subtype : Subgroup G) =
          centerIn (G := G) (thompsonSubgroup P_G) := by
      rw [hCenterJ_map]
      simp [T_M, hOpM_bot]
    have hNorm_centerJ_eq_M :
        Subgroup.normalizer
            ((centerIn (G := G) (thompsonSubgroup P_G) : Subgroup G) : Set G) = M := by
      rw [← hT_map_eq_centerJ]
      exact hNorm_Thompson_join_eq_M_unconditional
    exact hNorm_PG_le_norm_centerJ_PG.trans (le_of_eq hNorm_centerJ_eq_M)
  have hNorm_PG_le_M_of_gen_eq :
      section9GeneratedPPrimeFamily (⊤ : Subgroup G) P_G p =
          (pPrimeCore p M).map M.subtype →
        pPrimeCore p M ≠ ⊥ →
          Subgroup.normalizer (P_G : Set G) ≤ M := by
    intro hgen_eq hOpM_ne_bot
    exact
      section9_normalizer_le_of_generatedPPrimeFamily_eq_pPrimeCore_map
        (G := G) (p := p) (M := M) (A := P_G)
        hNorm_OpM_eq_M hgen_eq hOpM_ne_bot
  have hPG_sylow_of_norm_le_M :
      Subgroup.normalizer (P_G : Set G) ≤ M →
        ∃ P₀ : Sylow p G, (P₀ : Subgroup G) = P_G := by
    intro hNorm_PG_le_M
    simpa [P_G] using
      section9_sylow_map_subtype_of_normalizer_le
        (G := G) (p := p) (M := M) P hNorm_PG_le_M
  have hPG_sylow_of_OpM_bot :
      pPrimeCore p M = ⊥ →
        ∃ P₀ : Sylow p G, (P₀ : Subgroup G) = P_G := by
    intro hOpM_bot
    exact hPG_sylow_of_norm_le_M (hNorm_PG_le_M_of_OpM_bot hOpM_bot)
  have hNorm_PG_le_M : Subgroup.normalizer (P_G : Set G) ≤ M := by
    by_cases hOpM_bot : pPrimeCore p M = ⊥
    · exact hNorm_PG_le_M_of_OpM_bot hOpM_bot
    · exact hNorm_PG_le_M_of_gen_eq hgen_P_eq_OpM hOpM_bot
  have hPG_sylow : ∃ P₀ : Sylow p G, (P₀ : Subgroup G) = P_G :=
    hPG_sylow_of_norm_le_M hNorm_PG_le_M
  have hHmax_factorization :
      ∀ K : Subgroup G, K ∈ section8MaximalSubgroupsContaining B → K ≠ M →
        Nat.factorization (Nat.card (K ⊓ M : Subgroup G)) p ≤
          Nat.factorization (Nat.card (H ⊓ M : Subgroup G)) p := by
    intro K hK hKM
    exact section9_factorization_le_of_sylowCardInf_le
      (hHmax_pSylowCard K ⟨section9_maximal_of_section8_maximal hK.1, hK.2⟩ hKM)
  have hNorm_R_le_M : Subgroup.normalizer (R : Set G) ≤ M := by
    by_cases hR_eq_PG : R = P_G
    · simpa [hR_eq_PG] using hNorm_PG_le_M
    · have hR_lt_PG : R < P_G := lt_of_le_of_ne hR_le_P hR_eq_PG
      have hcard_R_lt_PG : Nat.card R < Nat.card P_G :=
        natCard_lt_of_subgroup_lt hR_lt_PG
      have hcard_R₀_R : Nat.card (R₀ : Subgroup I) = Nat.card R := by
        simpa [R] using
          (Subgroup.card_map_of_injective (K := (R₀ : Subgroup I)) (f := I.subtype)
            I.subtype_injective).symm
      have hcard_P_PG : Nat.card (P : Subgroup M) = Nat.card P_G := by
        simpa [P_G] using
          (Subgroup.card_map_of_injective (K := (P : Subgroup M)) (f := M.subtype)
            M.subtype_injective).symm
      have hcard_lt :
          Nat.card (R₀ : Subgroup (H ⊓ M : Subgroup G)) < Nat.card (P : Subgroup M) := by
        simpa [I, hcard_R₀_R, hcard_P_PG] using hcard_R_lt_PG
      have hgt :
          Nat.factorization (Nat.card (H ⊓ M : Subgroup G)) p <
            Nat.factorization
              (Nat.card
                (Subgroup.normalizer
                  (section8SubgroupInAmbient (R₀ : Subgroup (H ⊓ M : Subgroup G)) :
                    Set G) ⊓ M : Subgroup G)) p :=
        section8_inf_sylow_normalizer_factorization_gt_of_card_lt
          (G := G) (p := p) (M := M) (N := H) P R₀ hcard_lt
      have hB_le_R8 :
          B ≤ section8SubgroupInAmbient (R₀ : Subgroup (H ⊓ M : Subgroup G)) := by
        simpa [section8SubgroupInAmbient, R, I] using hB_le_R
      have hR8_ne_bot :
          section8SubgroupInAmbient (R₀ : Subgroup (H ⊓ M : Subgroup G)) ≠ ⊥ := by
        intro hRbot
        exact hB_ne_bot (le_bot_iff.mp (hB_le_R8.trans (le_of_eq hRbot)))
      have hnorm8 :
          Subgroup.normalizer
              (section8SubgroupInAmbient (R₀ : Subgroup (H ⊓ M : Subgroup G)) : Set G) ≤ M :=
        section8_inf_sylow_normalizer_le_of_factorization_gt
          (G := G) (p := p) (M := M) (N := H) (A_G := B)
          (section8_maximal_of_section9_maximal hM) R₀ hB_le_R8 hR8_ne_bot
          hHmax_factorization hgt
      simpa [section8SubgroupInAmbient, R, I] using hnorm8
  have hNorm_R8_le_M :
      Subgroup.normalizer
          (section8SubgroupInAmbient (R₀ : Subgroup (H ⊓ M : Subgroup G)) : Set G) ≤ M := by
    simpa [section8SubgroupInAmbient, R, I] using hNorm_R_le_M
  obtain ⟨R_H, hR_H_eq_R⟩ :=
    section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
      (G := G) (p := p) (M := M) (N := H) R₀ hNorm_R8_le_M
  have hPcoreH_map_le_R :
      (pCore p H).map H.subtype ≤ R := by
    calc
      (pCore p H).map H.subtype ≤ (R_H : Subgroup H).map H.subtype :=
        Subgroup.map_mono (section9_pCore_le_sylow (G := H) (p := p) R_H)
      _ = R := by
        simpa [section8SubgroupInAmbient, R, I] using hR_H_eq_R
  have hFittingH_map_le_M :
      (fittingSubgroup H).map H.subtype ≤ M := by
    calc
      (fittingSubgroup H).map H.subtype ≤
          ((pCore p H ⊔ pPrimeCore p H : Subgroup H).map H.subtype) :=
        Subgroup.map_mono (section9_fitting_le_pCore_sup_pPrimeCore (G := H) (p := p))
      _ = (pCore p H).map H.subtype ⊔ (pPrimeCore p H).map H.subtype := by
        rw [Subgroup.map_sup]
      _ ≤ M := sup_le (hPcoreH_map_le_R.trans hR_le_M) hOpH_le_M
  exfalso
  have hFittingH_map_le_H :
      (fittingSubgroup H).map H.subtype ≤ H :=
    Subgroup.map_subtype_le (fittingSubgroup H)
  have hNoUnique_le_FittingH :
      ∀ Y : Subgroup G, Y ≤ (fittingSubgroup H).map H.subtype →
        Y ∉ section9UniqueSubgroups G := by
    intro Y hY
    exact
      section9_not_unique_of_le_two_distinct_maximal hM hHmaxB.1
        (hY.trans hFittingH_map_le_M) (hY.trans hFittingH_map_le_H) hH_ne_M
  have hFittingRank_le_two : groupRank (fittingSubgroup H) ≤ 2 :=
    section9_t91_fitting_groupRank_le_two_of_no_unique hHmaxB.1 hNoUnique_le_FittingH
  have hHodd : Odd (Nat.card H) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card H)
  have hDerived_nil : Group.IsNilpotent (derivedSubgroup H) :=
    theorem_4_20_a (G := H) hHsolv hHodd (Or.inr hFittingRank_le_two)
  have hDerived_le_fitting : derivedSubgroup H ≤ fittingSubgroup H :=
    le_sSup ⟨(inferInstance : (derivedSubgroup H).Normal), hDerived_nil⟩
  let N_H : Subgroup H := (R_H : Subgroup H) ⊔ pPrimeCore p H
  have hFitting_le_NH : fittingSubgroup H ≤ N_H := by
    calc
      fittingSubgroup H ≤ pCore p H ⊔ pPrimeCore p H :=
        section9_fitting_le_pCore_sup_pPrimeCore (G := H) (p := p)
      _ ≤ N_H := by
        exact sup_le
          ((section9_pCore_le_sylow (G := H) (p := p) R_H).trans le_sup_left)
          le_sup_right
  have hDerived_le_NH : derivedSubgroup H ≤ N_H :=
    hDerived_le_fitting.trans hFitting_le_NH
  have hNH_normal : N_H.Normal :=
    section9_t91_normal_of_derivedSubgroup_le N_H hDerived_le_NH
  let : N_H.Normal := hNH_normal
  have hR_H_ambient_eq_R : section8SubgroupInAmbient (R_H : Subgroup H) = R := by
    simpa [section8SubgroupInAmbient, R, I] using hR_H_eq_R
  have hR_H_map_eq_R : (R_H : Subgroup H).map H.subtype = R := by
    simpa [section8SubgroupInAmbient] using hR_H_ambient_eq_R
  have hNH_map_le_M : N_H.map H.subtype ≤ M := by
    calc
      N_H.map H.subtype =
          ((R_H : Subgroup H).map H.subtype) ⊔ (pPrimeCore p H).map H.subtype := by
        simp [N_H, Subgroup.map_sup]
      _ ≤ M := by
        refine sup_le ?_ hOpH_le_M
        simpa [hR_H_map_eq_R] using hR_le_M
  have hFrattini :
      Subgroup.normalizer ((R_H : Subgroup H) : Set H) ⊔ N_H = ⊤ :=
    R_H.normalizer_sup_eq_top' (N := N_H) (hP := le_sup_left)
  have hH_le_M : H ≤ M := by
    intro x hxH
    let xH : H := ⟨x, hxH⟩
    have hxTop :
        xH ∈ Subgroup.normalizer ((R_H : Subgroup H) : Set H) ⊔ N_H := by
      rw [hFrattini]
      exact trivial
    rcases (Subgroup.mem_sup_of_normal_right
        (s := Subgroup.normalizer ((R_H : Subgroup H) : Set H))
        (t := N_H) (x := xH)).1 hxTop with
      ⟨n, hnNorm, z, hzN, hnz⟩
    have hnMap :
        ((n : H) : G) ∈
          (Subgroup.normalizer ((R_H : Subgroup H) : Set H)).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hnNorm
    have hnNormAmbient :
        ((n : H) : G) ∈ Subgroup.normalizer (R : Set G) := by
      have hnNormAmbient' :
          ((n : H) : G) ∈
            Subgroup.normalizer
              (section8SubgroupInAmbient (R_H : Subgroup H) : Set G) :=
        section8_normalizer_subgroupInAmbient_le (G := G)
          (H := H) (K := (R_H : Subgroup H)) hnMap
      simpa [hR_H_ambient_eq_R] using hnNormAmbient'
    have hnM : ((n : H) : G) ∈ M := hNorm_R_le_M hnNormAmbient
    have hzMap : ((z : H) : G) ∈ N_H.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hzN
    have hzM : ((z : H) : G) ∈ M := hNH_map_le_M hzMap
    have hx_eq : ((n : H) : G) * ((z : H) : G) = x := by
      simpa [xH] using congrArg H.subtype hnz
    rw [← hx_eq]
    exact M.mul_mem hnM hzM
  have hM_eq_H : M = H := (hHmaxB.1.le_iff_eq hM.1).mp hH_le_M
  exact hH_ne_M hM_eq_H.symm


end Section9
