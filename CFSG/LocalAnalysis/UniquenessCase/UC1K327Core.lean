module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Setup
public import CFSG.GroupTheory.ElemThompsonTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.Foundations.KCoreOpen
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327

open CFSG.ABGLocalTools (IsSylowOf)
open UC326 (jOf)

variable {G : Type} [Group G] [Finite G] {P A : Subgroup G}

theorem inf_eq_bot_of_isPGroup_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ}
    {R O : Subgroup G} (hR : IsPGroup p R) (hcop : Nat.Coprime p (Nat.card O)) :
    R ⊓ O = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxR, hxO⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
  have hk' : orderOf x ∣ p ^ k := by
    rw [← Subgroup.orderOf_mk x hxR]
    exact orderOf_dvd_of_pow_eq_one hk
  have hxO' : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) hk' hxO')

theorem injOn_mk'_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (O : Subgroup G)
    [O.Normal] (hcop : Nat.Coprime p (Nat.card O)) {R : Subgroup G} (hR : IsPGroup p R) :
    Set.InjOn (QuotientGroup.mk' O) R := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ R ⊓ O := by
    refine Subgroup.mem_inf.mpr ⟨R.mul_mem (R.inv_mem hx) hy, ?_⟩
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  rw [inf_eq_bot_of_isPGroup_of_coprime hR hcop, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem card_map_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Subgroup G)
    (hf : Set.InjOn f (S : Set G)) : Nat.card (S.map f) = Nat.card S :=
  Nat.card_image_of_injOn hf

theorem isElemAbelian_of_injOn {G H : Type*} [Group G] [Group H] {p : ℕ} {φ : G →* H}
    {P E : Subgroup G} (h : Set.InjOn φ P) (hEP : E ≤ P)
    (hE : CFSG.Open.IsElemAbelian p (E.map φ)) : CFSG.Open.IsElemAbelian p E := by
  refine ⟨?_, ?_⟩
  · have hc := hE.1
    rw [isMulCommutative_iff] at hc ⊢
    intro a b
    have h1 := hc ⟨φ a, Subgroup.mem_map_of_mem φ a.2⟩
      ⟨φ b, Subgroup.mem_map_of_mem φ b.2⟩
    have h2 : φ ((a : G) * b) = φ ((b : G) * a) := by
      simpa [map_mul] using congrArg Subtype.val h1
    exact Subtype.ext (h (P.mul_mem (hEP a.2) (hEP b.2))
      (P.mul_mem (hEP b.2) (hEP a.2)) h2)
  · intro x hx
    have h1 : φ (x ^ p) = φ 1 := by
      rw [map_pow, map_one]
      exact hE.2 _ (Subgroup.mem_map_of_mem φ hx)
    exact h (P.pow_mem (hEP hx) p) P.one_mem h1

theorem pRank_map_of_injOn {p : ℕ} {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (S : Subgroup A) (hf : Set.InjOn f (S : Set A)) :
    CFSG.Open.pRank p (S.map f) = CFSG.Open.pRank p S := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hES, hE, hcard⟩
    have hmap : (E.comap f ⊓ S).map f = E := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx1, -⟩, rfl⟩
        exact hx1
      · intro y hy
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 (hES hy)
        exact ⟨s, ⟨hy, hs⟩, rfl⟩
    have hinj : Set.InjOn f ((E.comap f ⊓ S : Subgroup A) : Set A) :=
      hf.mono (by exact_mod_cast (inf_le_right : E.comap f ⊓ S ≤ S))
    refine ⟨E.comap f ⊓ S, inf_le_right, ?_, ?_⟩
    · exact isElemAbelian_of_injOn (φ := f) (P := S) hf inf_le_right (by rw [hmap]; exact hE)
    · rw [← card_map_of_injOn f _ hinj, hmap]
      exact hcard
  · rintro ⟨E, hES, hE, hcard⟩
    refine ⟨E.map f, Subgroup.map_mono hES, CFSG.SectionRank.isElemAbelian_map hE f, ?_⟩
    rw [card_map_of_injOn f E (hf.mono (by exact_mod_cast hES))]
    exact hcard

theorem isSylowOf_map {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
    {T K : Subgroup G} (f : G →* H) (h : IsSylowOf p T K) :
    IsSylowOf p (T.map f) (K.map f) := by
  obtain ⟨Q, hQ⟩ := h
  let φ : K →* K.map f :=
    (f.comp K.subtype).codRestrict (K.map f) (fun x => Subgroup.mem_map_of_mem f x.2)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcomp : (K.map f).subtype.comp φ = f.comp K.subtype := by
    ext x
    rfl
  refine ⟨Q.mapSurjective hφ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ]

theorem map_inf_comap_eq {G H : Type*} [Group G] [Group H] (φ : G →* H) {R : Subgroup G}
    {E : Subgroup H} (hE : E ≤ R.map φ) : (R ⊓ E.comap φ).map φ = E := by
  refine le_antisymm ?_ fun z hz => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_right
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hE hz)
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_inf.mpr ⟨hx, hz⟩)

noncomputable def equivOfInjectiveComp {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (hf : Function.Injective (f.comp K.subtype)) : K ≃* K.map f :=
  (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem map_jOf_of_injective {G H : Type} [Group G] [Group H] {P : Subgroup G} (f : G →* H)
    (hf : Function.Injective (f.comp P.subtype)) : (jOf P).map f = jOf (P.map f) := by
  let e : P ≃* P.map f := equivOfInjectiveComp f P hf
  have hcomp : (P.map f).subtype.comp e.toMonoidHom = f.comp P.subtype := by
    ext x
    rfl
  simp only [jOf, inSubgroup]
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, elemThompson_map_mulEquiv e 3]

theorem normalizer_map_quotient_eq {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (T O : Subgroup G) [O.Normal] [Fact (IsPGroup p T)] (hcop : Nat.Coprime p (Nat.card O)) :
    (Subgroup.normalizer (T : Set G)).map (QuotientGroup.mk' O) =
      Subgroup.normalizer
        ((T.map (QuotientGroup.mk' O) : Subgroup (G ⧸ O)) : Set (G ⧸ O)) :=
  (CFSG.normalizer_map_quotient_eq_map_normalizer p T O inferInstance hcop).symm

theorem map_sSup_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Set (Subgroup G)) :
    (sSup S).map f = sSup (Subgroup.map f '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨N, hN, rfl⟩
  · refine sSup_le fun N hN => ?_
    obtain ⟨M, hM, rfl⟩ := hN
    exact Subgroup.map_mono (le_sSup hM)

theorem GLBCore_map_quotient_eq (p : ℕ) [Fact p.Prime] (O A : Subgroup G) [O.Normal]
    (hcop : Nat.Coprime p (Nat.card O)) (hA : IsPGroup p A) :
    (CFSG.Open.GLBCore p 1 A).map (QuotientGroup.mk' O) =
      CFSG.Open.GLBCore p 1 (A.map (QuotientGroup.mk' O)) := by
  set π := QuotientGroup.mk' O
  have hinj : Set.InjOn π (A : Set G) := injOn_mk'_of_isPGroup O hcop hA
  have hset : Subgroup.map π ''
      {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ A ∧ 1 ≤ CFSG.Open.pRank p Q ∧
        N = Subgroup.normalizer (Q : Set G)} =
      {N' : Subgroup (G ⧸ O) | ∃ Q' : Subgroup (G ⧸ O), Q' ≤ A.map π ∧
        1 ≤ CFSG.Open.pRank p Q' ∧
        N' = Subgroup.normalizer (Q' : Set (G ⧸ O))} := by
    ext N'
    constructor
    · rintro ⟨N, ⟨Q, hQA, hQr, rfl⟩, rfl⟩
      haveI : Fact (IsPGroup p Q) := ⟨hA.to_le hQA⟩
      refine ⟨Q.map π, Subgroup.map_mono hQA, ?_, ?_⟩
      · rw [pRank_map_of_injOn π Q (hinj.mono hQA)]
        exact hQr
      · exact normalizer_map_quotient_eq p Q O hcop
    · rintro ⟨Q', hQ'A, hQ'r, rfl⟩
      let Q : Subgroup G := A ⊓ Q'.comap π
      have hQA : Q ≤ A := inf_le_left
      have hQmap : Q.map π = Q' := map_inf_comap_eq π hQ'A
      have hQr : 1 ≤ CFSG.Open.pRank p Q := by
        rw [← pRank_map_of_injOn π Q (hinj.mono hQA), hQmap]
        exact hQ'r
      haveI : Fact (IsPGroup p Q) := ⟨hA.to_le hQA⟩
      refine ⟨Subgroup.normalizer (Q : Set G), ⟨Q, hQA, hQr, rfl⟩, ?_⟩
      rw [normalizer_map_quotient_eq p Q O hcop, hQmap]
  unfold CFSG.Open.GLBCore
  rw [map_sSup_eq, hset]

theorem hyp_quotient (h : Hyp327 G P A) :
    Hyp327 (G ⧸ CFSG.pPrimeCore 3 G) (P.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)))
      (A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G))) := by
  set O := CFSG.pPrimeCore 3 G
  set π := QuotientGroup.mk' O
  have hP3 : IsPGroup 3 P := h.sylow.isPGroup
  have hfP : Function.Injective (π.comp P.subtype) := by
    intro x y hxy
    exact Subtype.ext (injOn_mk'_of_isPGroup O pPrimeCore_coprime_card hP3 x.2 y.2 hxy)
  have hA3 : IsPGroup 3 A := h.elem.isPGroup
  have hinjA : Set.InjOn π (A : Set G) :=
    injOn_mk'_of_isPGroup O pPrimeCore_coprime_card hA3
  refine ⟨h.kgroup.quotient O, ?_, ?_, ?_, ?_, ?_⟩
  · have hsyl := isSylowOf_map π h.sylow
    simpa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] using hsyl
  · rw [h.jA]
    exact map_jOf_of_injective π hfP
  · exact h.elem.map π
  · rw [card_map_of_injOn π A hinjA, h.card]
  · rcases h.shape with hAP | hne
    · exact Or.inl (by rw [hAP])
    · rcases hne with ⟨eP⟩
      exact Or.inr ⟨(equivOfInjectiveComp π P hfP).symm.trans eP⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327
