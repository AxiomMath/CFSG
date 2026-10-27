module

public import CFSG.Quasithin.Recognition.Kleidman.VBEven.Coord
public import CFSG.Quasithin.Recognition.Kleidman.VBEven.CaseA

public section

namespace CFSG.Quasithin.Kleidman.VBEven

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.SzVB
open CFSG.LieType.BorelTits
open scoped Pointwise symmDiff

namespace CaseB

variable {G : Type} [Group G] {P T V : Subgroup G} {z : G}

theorem smul_eq_of_mem_pCoreOf (hQT : pCoreOf 2 P ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {q : ↥P} (hq : (q : G) ∈ pCoreOf 2 P)
    (U : ConjSet P V) : q • U = U := by
  obtain ⟨g, hg, hU⟩ := U.2
  apply Subtype.ext
  rw [ConjSet.smul_val, hU]
  have hgq : g⁻¹ * q * g ∈ pCoreOf 2 P := by
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P (P.inv_mem hg)) q).mp hq
    rwa [inv_inv] at h
  have h1 : conjSub (g⁻¹ * q * g) V = V :=
    OddAux.conjSub_eq_of_mem_normalizer' (hTV (hQT hgq))
  calc conjSub (q : G) (conjSub g V) = conjSub ((q : G) * g) V := (conjSub_mul _ _ _).symm
    _ = conjSub (g * (g⁻¹ * q * g)) V := by congr 1; group
    _ = conjSub g (conjSub (g⁻¹ * q * g) V) := conjSub_mul _ _ _
    _ = conjSub g V := by rw [h1]

theorem exists_smul_eq_of_le_sup {Q₀ : Subgroup G} (hQ₀P : Q₀ ≤ P) (hQT : pCoreOf 2 P ≤ T)
    (hTQ : T ≤ Q₀ ⊔ pCoreOf 2 P) (hl24 : L24Facts P T V) {U U' : ConjSet P V}
    (hU : U ≠ ConjSet.base P V) (hU' : U' ≠ ConjSet.base P V) :
    ∃ r : ↥P, (r : G) ∈ Q₀ ∧ r • U = U' := by
  obtain ⟨x, hxT, hx⟩ := hl24.S_transitive U U' hU hU'
  have hle : Q₀ ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    hQ₀P.trans (le_normalizer_pCoreOf 2 P)
  have hmem : (x : G) ∈ ((Q₀ ⊔ pCoreOf 2 P : Subgroup G) : Set G) := hTQ hxT
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q₀ (pCoreOf 2 P) hle] at hmem
  obtain ⟨r, hr, q, hq, hrq⟩ := Set.mem_mul.mp hmem
  refine ⟨⟨r, hQ₀P hr⟩, hr, ?_⟩
  have hqP : q ∈ P := pCoreOf_le 2 P hq
  have hx' : x = ⟨r, hQ₀P hr⟩ * ⟨q, hqP⟩ := Subtype.ext hrq.symm
  rw [← hx, hx', mul_smul, smul_eq_of_mem_pCoreOf hQT hl24.S_le_normalizer (q := ⟨q, hqP⟩) hq]

variable [Finite G]

theorem eq_empty_of_fixedW [DecidableEq (ConjSet P V)] (E : Frame P V z) (F : A5Facts P T V z)
    (hB : A5FixedW P V z) {K : Finset (ConjSet P V)} (hK : E.prod K = 1 ∨ E.prod K = z) :
    K = ∅ := by
  obtain ⟨w, hwW, hwz, hwP⟩ := hB
  obtain ⟨I, hI⟩ := E.exists_of_mem hwW
  have hfix : ∀ g : ↥P, g • I = I := by
    intro g
    apply E.smul_eq_of_conj F g
    have hc := eq_one_or_eq_of_mem_zpowers E.tdata.z_sq (hwP g g.2)
    have hzc : (g : G) * z * (g : G)⁻¹ = z := by
      rw [E.tdata.z_cent g g.2, mul_assoc, mul_inv_cancel, mul_one]
    rcases hI with rfl | rfl
    · rcases hc with h | h
      · left
        calc (g : G) * E.prod I * (g : G)⁻¹
            = ((g : G) * E.prod I * (g : G)⁻¹ * (E.prod I)⁻¹) * E.prod I := by group
          _ = E.prod I := by rw [h, one_mul]
      · right
        calc (g : G) * E.prod I * (g : G)⁻¹
            = ((g : G) * E.prod I * (g : G)⁻¹ * (E.prod I)⁻¹) * E.prod I := by group
          _ = z * E.prod I := by rw [h]
          _ = E.prod I * z := E.z_comm I
    · have e : (g : G) * E.prod I * (g : G)⁻¹ =
          (g : G) * (E.prod I * z) * (g : G)⁻¹ * (E.prod I * z)⁻¹ * E.prod I := by
        calc (g : G) * E.prod I * (g : G)⁻¹
            = (g : G) * E.prod I * (g : G)⁻¹ * ((g : G) * z * (g : G)⁻¹) * z⁻¹ := by
              rw [hzc]; group
          _ = (g : G) * (E.prod I * z) * (g : G)⁻¹ * (E.prod I * z)⁻¹ * E.prod I := by group
      rcases hc with h | h
      · left
        rw [e, h, one_mul]
      · right
        rw [e, h, E.z_comm]
  have hIne : I ≠ ∅ := by
    rintro rfl
    apply hwz
    rcases hI with h | h
    · rw [h, E.prod_empty]
      exact one_mem _
    · rw [h, E.prod_empty, one_mul]
      exact Subgroup.mem_zpowers z
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hIne
  have hIall : ∀ U, U ∈ I := by
    intro U
    obtain ⟨g, hg⟩ := (OddAux.conjSet_isPretransitive P V).exists_smul_eq a U
    rw [← hfix g, ← hg]
    exact Finset.smul_mem_smul_finset ha
  rcases E.ker F hK with h0 | hKall
  · exact h0
  · exfalso
    have hKI : K = I := Finset.ext fun U => ⟨fun _ => hIall U, fun _ => hKall U⟩
    rw [hKI] at hK
    apply hwz
    rcases hI with h | h <;> rw [h] <;> rcases hK with hk | hk <;> rw [hk]
    · exact one_mem _
    · exact Subgroup.mem_zpowers z
    · rw [one_mul]
      exact Subgroup.mem_zpowers z
    · rw [E.tdata.z_sq]
      exact one_mem _

theorem eq_of_prod_mem_V [DecidableEq (ConjSet P V)] (E : Frame P V z) (F : A5Facts P T V z)
    (hB : A5FixedW P V z) {K : Finset (ConjSet P V)} (hK : E.prod K ∈ V) :
    K = ∅ ∨ K = {ConjSet.base P V} := by
  have hto : E.t (ConjSet.base P V) * E.t (ConjSet.base P V) = 1 := E.tdata.t_sq _
  have hzt : z * E.t (ConjSet.base P V) = E.t (ConjSet.base P V) * z :=
    E.comm E.tdata.z_mem (E.tdata.t_mem _)
  rcases E.V_cases F.klein hK with h | h | h | h
  · exact Or.inl (eq_empty_of_fixedW E F hB (Or.inl h))
  · exact Or.inl (eq_empty_of_fixedW E F hB (Or.inr h))
  · right
    have h1 : E.prod (K ∆ {ConjSet.base P V}) = 1 := by
      rw [← E.prod_mul, E.prod_singleton, h, hto]
    exact Finset.symmDiff_eq_empty.mp (eq_empty_of_fixedW E F hB (Or.inl h1))
  · right
    have h1 : E.prod (K ∆ {ConjSet.base P V}) = z := by
      rw [← E.prod_mul, E.prod_singleton, h, mul_assoc, hzt, ← mul_assoc, hto, one_mul]
    exact Finset.symmDiff_eq_empty.mp (eq_empty_of_fixedW E F hB (Or.inr h1))

end CaseB

open CaseB

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

theorem caseB_module (hC : GeoCtx G₀ G₁ G₂ T V z) (F : A5Facts G₂ T V z)
    (hTQ : T ≤ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂) (hB : A5FixedW G₂ V z) :
    (∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, ∀ r ∈ pCoreOf 2 G₁,
      r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z) ∧
    ∃ s ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, s ∉ V ∧
      ∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, a ∈ V ∨ a * s⁻¹ ∈ V := by
  classical
  have : Fintype (ConjSet G₂ V) := Fintype.ofFinite _
  obtain ⟨E⟩ := exists_frame F
  have hQ0T : pCoreOf 2 G₁ ≤ T := isSylowTwoOf_pCoreOf_le hC.hyp.sylow₁
  have hQ0G : pCoreOf 2 G₁ ≤ G₂ := hQ0T.trans F.l24.S_le
  have hQ2T : pCoreOf 2 G₂ ≤ T := isSylowTwoOf_pCoreOf_le hC.hyp.sylow₂
  have hεV : ∀ ε : G, (ε = 1 ∨ ε = z) → ε ∈ V := by
    rintro ε (rfl | rfl)
    · exact one_mem _
    · exact F.klein.z_mem
  have hcomm : ∀ (r : ↥G₂) (I : Finset (ConjSet G₂ V)) (c : G), (c = 1 ∨ c = z) →
      ∃ ε : G, (ε = 1 ∨ ε = z) ∧ (r : G) * (E.prod I * c) * (r : G)⁻¹ * (E.prod I * c)⁻¹ =
        E.prod ((r • I) ∆ I) * ε := by
    intro r I c hc
    obtain ⟨ε, hε, he⟩ := E.conj_prod r I
    refine ⟨ε, hε, ?_⟩
    have hεW : ε ∈ conjClosure V G₂ := le_conjClosure V G₂ (hεV ε hε)
    have hcz : (r : G) * c * (r : G)⁻¹ = c := by
      rcases hc with rfl | rfl
      · group
      · rw [E.tdata.z_cent r r.2, mul_assoc, mul_inv_cancel, mul_one]
    calc (r : G) * (E.prod I * c) * (r : G)⁻¹ * (E.prod I * c)⁻¹
        = ((r : G) * E.prod I * (r : G)⁻¹) * ((r : G) * c * (r : G)⁻¹) * c⁻¹ *
          (E.prod I)⁻¹ := by group
      _ = E.prod (r • I) * ε * (E.prod I)⁻¹ := by rw [he, hcz]; group
      _ = E.prod (r • I) * E.prod I * ε := by
          rw [E.inv_eq (E.prod_mem I), mul_assoc, E.comm hεW (E.prod_mem I), ← mul_assoc]
      _ = E.prod ((r • I) ∆ I) * ε := by rw [E.prod_mul]
  have hinv : ∀ (I : Finset (ConjSet G₂ V)) (c : G), (c = 1 ∨ c = z) →
      E.prod I * c ∈ secCentr (pCoreOf 2 G₁) V → ∀ r : ↥G₂, (r : G) ∈ pCoreOf 2 G₁ →
        r • I = I ∧ (r : G) * (E.prod I * c) * (r : G)⁻¹ * (E.prod I * c)⁻¹ ∈
          Subgroup.zpowers z := by
    intro I c hc ha r hr
    obtain ⟨ε, hε, he⟩ := hcomm r I c hc
    have hV := (mem_secCentr.mp ha).2 r hr
    rw [he] at hV
    have hK : E.prod ((r • I) ∆ I) ∈ V := by
      have := V.mul_mem hV (V.inv_mem (hεV ε hε))
      rwa [mul_inv_cancel_right] at this
    rcases eq_of_prod_mem_V E F hB hK with h0 | h0
    · refine ⟨Finset.symmDiff_eq_empty.mp h0, ?_⟩
      rw [he, h0, E.prod_empty, one_mul]
      rcases hε with h | h <;> rw [h]
      · exact one_mem _
      · exact Subgroup.mem_zpowers z
    · exfalso
      have heven := PermAux.even_card_symmDiff_of_card_eq (Finset.card_smul_finset r I)
      rw [h0, Finset.card_singleton] at heven
      exact (by decide : ¬ Even 1) heven
  have hcoord : ∀ a ∈ conjClosure V G₂, ∃ (I : Finset (ConjSet G₂ V)) (c : G),
      (c = 1 ∨ c = z) ∧ a = E.prod I * c := by
    intro a ha
    obtain ⟨I, hI⟩ := E.exists_of_mem ha
    rcases hI with h | h
    · exact ⟨I, 1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨I, z, Or.inr rfl, h⟩
  have hR : ∀ U U' : ConjSet G₂ V, U ≠ ConjSet.base G₂ V → U' ≠ ConjSet.base G₂ V →
      ∃ x ∈ {x : ↥G₂ | (x : G) ∈ pCoreOf 2 G₁}, x • U = U' := by
    intro U U' hU hU'
    obtain ⟨r, hr, hrU⟩ := exists_smul_eq_of_le_sup hQ0G hQ2T hTQ F.l24 hU hU'
    exact ⟨r, hr, hrU⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U : ConjSet G₂ V, U ≠ ConjSet.base G₂ V := by
    by_contra h
    push Not at h
    have h1 : Fintype.card (ConjSet G₂ V) ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
    rw [← Nat.card_eq_fintype_card, F.l24.card_five] at h1
    omega
  set s := E.prod Finset.univ with hs
  have hsW : s ∈ conjClosure V G₂ := E.prod_mem _
  have hsN : s ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      E.comm (le_conjClosure V G₂ hv) hsW)
  have hsC : s ∈ secCentr (pCoreOf 2 G₁) V := by
    refine mem_secCentr.mpr ⟨hsN, fun r hr => ?_⟩
    obtain ⟨ε, hε, he⟩ := hcomm ⟨r, hQ0G hr⟩ Finset.univ 1 (Or.inl rfl)
    rw [mul_one, Finset.smul_finset_univ, symmDiff_self, Finset.bot_eq_empty, E.prod_empty,
      one_mul] at he
    rw [hs, he]
    exact hεV ε hε
  have hsV : s ∉ V := by
    intro h
    rcases eq_of_prod_mem_V E F hB h with h0 | h0
    · exact (Finset.univ_eq_empty_iff.mp h0).false U₁
    · have hc := congrArg Finset.card h0
      rw [Finset.card_univ, Finset.card_singleton, ← Nat.card_eq_fintype_card,
        F.l24.card_five] at hc
      omega
  refine ⟨fun a ha r hr => ?_, s, ⟨hsC, hsW⟩, hsV, fun a ha => ?_⟩
  · obtain ⟨I, c, hc, rfl⟩ := hcoord a ha.2
    exact (hinv I c hc ha.1 ⟨r, hQ0G hr⟩ hr).2
  · obtain ⟨I, c, hc, rfl⟩ := hcoord a ha.2
    have hIfix : ∀ x ∈ {x : ↥G₂ | (x : G) ∈ pCoreOf 2 G₁}, x • I = I :=
      fun x hx => (hinv I c hc ha.1 x hx).1
    have hcV := hεV c hc
    by_cases h1 : U₁ ∈ I
    ·
      right
      have hsub : I ∆ Finset.univ ⊆ {ConjSet.base G₂ V} := by
        intro U hU
        rw [Finset.mem_singleton]
        by_contra hUo
        have hUI := (mem_iff_of_fixed hR hIfix hU₁ hUo).mp h1
        rw [Finset.mem_symmDiff] at hU
        rcases hU with ⟨_, h⟩ | ⟨_, h⟩
        · exact h (Finset.mem_univ U)
        · exact h hUI
      have hp : E.prod (I ∆ Finset.univ) ∈ V := by
        rcases Finset.subset_singleton_iff.mp hsub with h | h
        · rw [h, E.prod_empty]
          exact one_mem _
        · rw [h, E.prod_singleton]
          exact E.mem (ConjSet.base G₂ V)
      have hcW : c ∈ conjClosure V G₂ := le_conjClosure V G₂ hcV
      have e : E.prod I * c * s⁻¹ = E.prod (I ∆ Finset.univ) * c := by
        rw [E.inv_eq hsW, ← E.prod_mul, hs, mul_assoc, E.comm hcW (E.prod_mem _), ← mul_assoc]
      rw [e]
      exact V.mul_mem hp hcV
    ·
      left
      have hsub : I ⊆ {ConjSet.base G₂ V} := by
        intro U hU
        rw [Finset.mem_singleton]
        by_contra hUo
        exact h1 ((mem_iff_of_fixed hR hIfix hUo hU₁).mp hU)
      rcases Finset.subset_singleton_iff.mp hsub with h | h
      · rw [h, E.prod_empty, one_mul]
        exact hcV
      · rw [h, E.prod_singleton]
        exact V.mul_mem (E.mem (ConjSet.base G₂ V)) hcV

end CFSG.Quasithin.Kleidman.VBEven
