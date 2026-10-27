module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PairProj
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.SrSubgroup
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

theorem eq_of_le_of_coprime_relIndex [Finite G] {r : ℕ} (hr : r.Prime) {H P Q : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup r P) (hidx : Nat.Coprime (P.relIndex H) r) (hQH : Q ≤ H)
    (hQ : IsPGroup r Q) (hPQ : P ≤ Q) : Q = P := by
  have : Fact r.Prime := ⟨hr⟩
  have hnd : ¬ r ∣ (P.subgroupOf H).index := (Nat.Prime.coprime_iff_not_dvd hr).mp hidx.symm
  let S : Sylow r H := (hP.comap_subtype (K := H)).toSylow hnd
  have h1 : Q.subgroupOf H = P.subgroupOf H :=
    S.is_maximal' (hQ.comap_subtype (K := H)) (Subgroup.comap_mono hPQ)
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hQH, inf_eq_left.mpr hPH] at h1
  exact h1

theorem coprime_relIndex_of_maximal [Finite G] {r : ℕ} (hr : r.Prime) {H P : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup r P)
    (hmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup r Q → P ≤ Q → Q = P) :
    Nat.Coprime (P.relIndex H) r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  have hPS : P ≤ (S : Subgroup H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPH]
    exact Subgroup.map_mono hS
  have hSP : (S : Subgroup H).map H.subtype = P :=
    hmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) hPS
  have h2 : P.subgroupOf H = S := by
    rw [← hSP]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h3 : ¬ r ∣ (S : Subgroup H).index := S.not_dvd_index
  change Nat.Coprime (P.subgroupOf H).index r
  rw [h2]
  exact ((Nat.Prime.coprime_iff_not_dvd hr).mpr h3).symm

section DirectPair

variable {K L H P : Subgroup G} {r : ℕ}

theorem isPGroup_sup_of_isDirectPair (h : IsDirectPair K L H) {X Y : Subgroup G} (hX : X ≤ K)
    (hY : Y ≤ L) (hXp : IsPGroup r X) (hYp : IsPGroup r Y) : IsPGroup r (X ⊔ Y : Subgroup G) := by
  refine hXp.to_sup_of_normal_right' hYp fun x hx => ?_
  apply Subgroup.centralizer_le_normalizer (Y : Set G)
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => (h.commute x (hX hx) y (hY hy)).eq.symm

theorem isPGroup_proj_of_isDirectPair (h : IsDirectPair K L H) (hPH : P ≤ H) (hP : IsPGroup r P) :
    IsPGroup r (proj K L P) := by
  rw [proj_eq_map_pairProj h hPH]
  exact ((hP.comap_subtype (K := H)).map (pairProj h)).map K.subtype

private theorem isDirectPair_symm (h : IsDirectPair K L H) : IsDirectPair L K H :=
  ⟨fun x hx y hy => (h.commute y hy x hx).symm, by rw [inf_comm]; exact h.inf_eq_bot,
    by rw [sup_comm]; exact h.sup_eq⟩

theorem exists_mul_of_maximal_of_isDirectPair (h : IsDirectPair K L H) (hPH : P ≤ H)
    (hP : IsPGroup r P) (hmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup r Q → P ≤ Q → Q = P) :
    (∀ x ∈ P, ∃ k ∈ P ⊓ K, ∃ l ∈ P ⊓ L, x = k * l) ∧
      ∀ Q : Subgroup G, Q ≤ K → IsPGroup r Q → P ⊓ K ≤ Q → Q = P ⊓ K := by
  have hKH : K ≤ H := h.sup_eq ▸ le_sup_left
  have hLH : L ≤ H := h.sup_eq ▸ le_sup_right
  have hPKp : IsPGroup r (proj K L P) := isPGroup_proj_of_isDirectPair h hPH hP
  have hPLp : IsPGroup r (proj L K P) := isPGroup_proj_of_isDirectPair (isDirectPair_symm h) hPH hP
  have hPKK : proj K L P ≤ K := proj_le_left _ _ _
  have hPLL : proj L K P ≤ L := proj_le_left _ _ _
  have hdecomp : ∀ x ∈ P, ∃ k ∈ proj K L P, ∃ l ∈ proj L K P, x = k * l := by
    intro x hx
    obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_isDirectPair h (hPH hx)
    refine ⟨k, ?_, l, ?_, rfl⟩
    · rw [mem_proj_iff h.commute]
      exact ⟨hk, l, hl, hx⟩
    · rw [mem_proj_iff (isDirectPair_symm h).commute]
      exact ⟨hl, k, hk, by rwa [← (h.commute k hk l hl).eq]⟩
  have hle : P ≤ proj K L P ⊔ proj L K P := fun x hx => by
    obtain ⟨k, hk, l, hl, rfl⟩ := hdecomp x hx
    exact Subgroup.mul_mem_sup hk hl
  have hsup : proj K L P ⊔ proj L K P = P :=
    hmax _ (sup_le (hPKK.trans hKH) (hPLL.trans hLH))
      (isPGroup_sup_of_isDirectPair h hPKK hPLL hPKp hPLp) hle
  have hPKeq : proj K L P = P ⊓ K := by
    refine le_antisymm (le_inf (le_sup_left.trans hsup.le) hPKK) fun x hx => ?_
    rw [mem_proj_iff h.commute]
    exact ⟨hx.2, 1, one_mem L, by rw [mul_one]; exact hx.1⟩
  have hPLeq : proj L K P = P ⊓ L := by
    refine le_antisymm (le_inf (le_sup_right.trans hsup.le) hPLL) fun x hx => ?_
    rw [mem_proj_iff (isDirectPair_symm h).commute]
    exact ⟨hx.2, 1, one_mem K, by rw [mul_one]; exact hx.1⟩
  refine ⟨fun x hx => ?_, fun Q hQK hQ hPQ => ?_⟩
  · obtain ⟨k, hk, l, hl, rfl⟩ := hdecomp x hx
    rw [hPKeq] at hk
    rw [hPLeq] at hl
    exact ⟨k, hk, l, hl, rfl⟩
  · have hQp : IsPGroup r (Q ⊔ proj L K P : Subgroup G) :=
      isPGroup_sup_of_isDirectPair h hQK hPLL hQ hPLp
    have hPle : P ≤ Q ⊔ proj L K P :=
      calc P = proj K L P ⊔ proj L K P := hsup.symm
        _ ≤ Q ⊔ proj L K P := sup_le_sup_right (hPKeq.le.trans hPQ) _
    have hQP : Q ⊔ proj L K P = P :=
      hmax _ (sup_le (hQK.trans hKH) (hPLL.trans hLH)) hQp hPle
    exact le_antisymm (le_inf (le_sup_left.trans hQP.le) hQK) hPQ

end DirectPair

theorem IsDirectProduct.sylow_decomp [Finite G] {Ω : Set (Subgroup G)} {H P : Subgroup G}
    (hΩ : IsDirectProduct Ω H) {r : ℕ} (hr : r.Prime) (hPH : P ≤ H) (hP : IsPGroup r P)
    (hidx : Nat.Coprime (P.relIndex H) r) :
    IsDirectProduct {Y | ∃ L ∈ Ω, Y = P ⊓ L} P ∧
      ∀ L ∈ Ω, Nat.Coprime ((P ⊓ L).relIndex L) r := by
  have hmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup r Q → P ≤ Q → Q = P := fun Q hQH hQ hPQ =>
    eq_of_le_of_coprime_relIndex hr hPH hP hidx hQH hQ hPQ
  have key : ∀ L ∈ Ω, (∀ x ∈ P, ∃ k ∈ P ⊓ L, ∃ l ∈ P ⊓ sSup (Ω \ {L}), x = k * l) ∧
      ∀ Q : Subgroup G, Q ≤ L → IsPGroup r Q → P ⊓ L ≤ Q → Q = P ⊓ L := fun L hL =>
    exists_mul_of_maximal_of_isDirectPair (hΩ.isDirectPair hL) hPH hP hmax
  refine ⟨⟨?_, ?_, ?_⟩, fun L hL => ?_⟩
  · rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨L₂, hL₂, rfl⟩ hne x hx y hy
    exact hΩ.commute L₁ hL₁ L₂ hL₂ (fun h => hne (h ▸ rfl)) x (Subgroup.mem_inf.mp hx).2 y
      (Subgroup.mem_inf.mp hy).2
  · rintro _ ⟨L, hL, rfl⟩
    refine (hΩ.indep hL).mono inf_le_right (sSup_le ?_)
    rintro _ ⟨⟨L', hL', rfl⟩, hne⟩
    exact inf_le_right.trans (le_sSup ⟨hL', fun h => hne (by rw [h]; rfl)⟩)
  · refine le_antisymm (sSup_le ?_) fun x hx => ?_
    · rintro _ ⟨L, hL, rfl⟩
      exact inf_le_left
    · refine hΩ.mem_of_coord_mem (M := sSup {Y | ∃ L ∈ Ω, Y = P ⊓ L}) (hPH hx) fun L hL => ?_
      obtain ⟨k, hk, l, hl, hkl⟩ := (key L hL).1 x hx
      subst hkl
      have h1 := hΩ.coord_mul hL (Subgroup.mem_inf.mp hk).2 (Subgroup.mem_inf.mp hl).2
      rw [h1]
      have h2 : P ⊓ L ≤ sSup {Y | ∃ L ∈ Ω, Y = P ⊓ L} := le_sSup ⟨L, hL, rfl⟩
      exact h2 hk
  · exact coprime_relIndex_of_maximal hr inf_le_right hP.to_inf_left (key L hL).2

theorem isSylow_of_isSrSubgroupOf [Finite G] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (_hrp : r ≠ p) {A U P : Subgroup G} (hA : IsElemAbelian p A)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hU : Nat.Coprime p (Nat.card U))
    (hP : IsSrSubgroupOf A r U P) :
    P ≤ U ∧ IsPGroup r P ∧ Nat.Coprime (P.relIndex U) r := by
  obtain ⟨⟨hAP, hPr, hPU⟩, hmax⟩ := hP
  refine ⟨hPU, hPr, ?_⟩
  have hAp : IsPGroup p A := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A U hAU
  obtain ⟨Q, hPQ, hQ⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p r hp hr hAp
    hU (P.subgroupOf U) hPr.comap_subtype
    (CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A U P hAU hAP)
  have hQ' : A ≤ Subgroup.normalizer (((Q : Subgroup U).map U.subtype : Subgroup G) : Set G) := by
    apply CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A U hAU
    change ∀ a : A, ∀ x ∈ (Q : Subgroup U), a • x ∈ (Q : Subgroup U)
    intro a x hx
    have hmem := Subgroup.smul_mem_pointwise_smul x a (Q : Subgroup U) hx
    rwa [← Sylow.pointwise_smul_def, hQ a] at hmem
  have hPle : P ≤ (Q : Subgroup U).map U.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPU]
    exact Subgroup.map_mono hPQ
  have hle := hmax ⟨hQ', Q.isPGroup'.map U.subtype, Subgroup.map_subtype_le _⟩ hPle
  have h2 : P.subgroupOf U = Q := by
    have : (Q : Subgroup U).map U.subtype = P := le_antisymm hle hPle
    rw [← this]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  have : Fact r.Prime := ⟨hr⟩
  change Nat.Coprime (P.subgroupOf U).index r
  rw [h2]
  exact ((Nat.Prime.coprime_iff_not_dvd hr).mpr Q.not_dvd_index).symm

namespace IsRegFam

variable {A H N : Subgroup G} {Ω : Set (Subgroup G)}

theorem inf_family [Finite G] (hΩ : IsRegFam A H Ω N) {r : ℕ} (hr : r.Prime) {P : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup r P) (hidx : Nat.Coprime (P.relIndex H) r)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hne : ∀ L ∈ Ω, P ⊓ L ≠ ⊥) :
    IsRegFam A P {Y | ∃ L ∈ Ω, Y = P ⊓ L} N := by
  have hP' : ∀ a ∈ A, P.map (MulAut.conj a).toMonoidHom = P := fun a ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAP ha)
  have hmap : ∀ a ∈ A, ∀ L : Subgroup G, (P ⊓ L).map (MulAut.conj a).toMonoidHom =
      P ⊓ L.map (MulAut.conj a).toMonoidHom := by
    intro a ha L
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective, hP' a ha]
  have hnorm : ∀ (L : Subgroup G) (a : G), a ∈ Subgroup.normalizer (L : Set G) ↔
      L.map (MulAut.conj a).toMonoidHom = L := fun L a => Subgroup.mem_normalizer_iff_map_conj_eq
  refine ⟨(IsDirectProduct.sylow_decomp hΩ.isDirectProduct hr hPH hP hidx).1, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hΩ.nonempty
    exact ⟨P ⊓ L, L, hL, rfl⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact hne L hL
  · rintro a ha _ ⟨L, hL, rfl⟩
    exact ⟨_, hΩ.map_conj_mem a ha L hL, hmap a ha L⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive L hL L' hL'
    exact ⟨a, ha, (hmap a ha L).symm⟩
  · rintro _ ⟨L, hL, rfl⟩
    rw [← hΩ.stabilizer L hL]
    ext a
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun ha => ?_
    rw [hnorm, hnorm, hmap a ha L]
    constructor
    · intro h
      by_contra hne'
      have hL'' := hΩ.map_conj_mem a ha L hL
      have hle : P ⊓ L ≤ sSup (Ω \ {L}) := by
        rw [← h]
        exact inf_le_right.trans (le_sSup ⟨hL'', hne'⟩)
      exact hne L hL (le_bot_iff.mp ((hΩ.isDirectProduct.indep hL) inf_le_right hle))
    · intro h
      rw [h]

end IsRegFam

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
