module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S12.Sec12FusChoice

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec15FA

variable {G : Type} [Group G]

theorem exists_conj_of_isSylowOf [Finite G] {p : ℕ} (hp : p.Prime) {C P₁ P₂ : Subgroup G}
    (h₁ : IsSylowOf p P₁ C) (h₂ : IsSylowOf p P₂ C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup p (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup p (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow p ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow p ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : G)⁻¹ * x * g ∈ P₁ := by
      exact Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

theorem le_of_isSylowOf_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {T N R : Subgroup G}
    (hT : IsSylowOf p T N) (hR : IsPGroup p R) (hTR : T ≤ R) (hRN : R ≤ N) : R ≤ T := by
  obtain ⟨k, hk⟩ := hR.index (T.subgroupOf R)
  have hk' : T.relIndex R = p ^ k := hk
  have h1 := Subgroup.relIndex_mul_relIndex T R N hTR hRN
  by_contra hRT
  have hne : T.relIndex R ≠ 1 := fun h => hRT (Subgroup.relIndex_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by rw [hk', pow_zero])
  exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left (hk' ▸ dvd_pow_self p hk0) _)

theorem thompsonElem_conj_mem {p : ℕ} [Fact p.Prime] {Q : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) {y : G} (hy : y ∈ thompsonElem p Q) :
    x * y * x⁻¹ ∈ thompsonElem p Q := by
  classical
  have hx' : x⁻¹ ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.normalizer (Q : Set G)).inv_mem hx
  refine Subgroup.closure_induction
    (p := fun y _ => x * y * x⁻¹ ∈ thompsonElem p Q) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨F, hFQ, hFe, hFmax, hyF⟩
    have : IsElementaryAbelian p ↥F := hFe
    let F' : Subgroup G := F.map (MulAut.conj x).toMonoidHom
    have hF'Q : F' ≤ Q := by
      rintro _ ⟨f, hf, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hx f).1 (hFQ hf)
    have hF'e : IsElementaryAbelian p ↥F' := IsElementaryAbelian.map (A := F) (MulAut.conj x).toMonoidHom
    have hcard : Nat.card ↥F' = Nat.card ↥F :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hF'max : ∀ F'' : Subgroup G, F'' ≤ Q → IsElementaryAbelian p ↥F'' →
        Nat.card ↥F'' ≤ Nat.card ↥F' := by
      intro F'' hF''Q hF''e
      have : IsElementaryAbelian p ↥F'' := hF''e
      have h1 : F''.map (MulAut.conj x⁻¹).toMonoidHom ≤ Q := by
        rintro _ ⟨f, hf, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hx' f).1 (hF''Q hf)
      have h2 := hFmax _ h1 (IsElementaryAbelian.map (A := F'') (MulAut.conj x⁻¹).toMonoidHom)
      rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective] at h2
      rw [hcard]
      exact h2
    exact Subgroup.subset_closure ⟨F', hF'Q, hF'e, hF'max, ⟨y, hyF, rfl⟩⟩
  · simp
  · intro a b _ _ ha hb
    have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem mem_normalizer_thompsonElem {p : ℕ} [Fact p.Prime] {Q : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) :
    x ∈ Subgroup.normalizer (thompsonElem p Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => thompsonElem_conj_mem hx hy
  · intro hy
    have hx' : x⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hx
    have := thompsonElem_conj_mem (p := p) hx' hy
    simpa [mul_assoc] using this

theorem eq_of_card_le_of_thompson [Finite G] {p : ℕ} [Fact p.Prime] {E Q : Subgroup G}
    (hJ : thompsonElem p Q ≤ E) {F : Subgroup G} (hFQ : F ≤ Q) (hF : IsElementaryAbelian p ↥F)
    (hcard : Nat.card ↥E ≤ Nat.card ↥F) : F = E := by
  classical
  let S : Set (Subgroup G) :=
    {F' | F' ≤ Q ∧ IsElementaryAbelian p ↥F' ∧ Nat.card ↥E ≤ Nat.card ↥F'}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨F, hFQ, hF, hcard⟩
  obtain ⟨F₀, ⟨hF₀Q, hF₀e, hF₀c⟩, hF₀max⟩ :=
    Set.exists_max_image S (fun F' => Nat.card ↥F') hSfin hSne
  have hmaxall : ∀ F' : Subgroup G, F' ≤ Q → IsElementaryAbelian p ↥F' →
      Nat.card ↥F' ≤ Nat.card ↥F₀ := by
    intro F' hF'Q hF'e
    by_cases h : Nat.card ↥E ≤ Nat.card ↥F'
    · exact hF₀max F' ⟨hF'Q, hF'e, h⟩
    · exact (Nat.lt_of_not_le h).le.trans hF₀c
  have hle : ∀ F' : Subgroup G, F' ≤ Q → IsElementaryAbelian p ↥F' →
      Nat.card ↥F₀ ≤ Nat.card ↥F' → F' ≤ E := by
    intro F' hF'Q hF'e hc x hx
    exact hJ (Subgroup.subset_closure ⟨F', hF'Q, hF'e,
      fun F'' h1 h2 => (hmaxall F'' h1 h2).trans hc, hx⟩)
  have hF₀E : F₀ ≤ E := hle F₀ hF₀Q hF₀e le_rfl
  have hEF₀ : Nat.card ↥F₀ ≤ Nat.card ↥E := Subgroup.card_le_of_le hF₀E
  have hFE : F ≤ E := hle F hFQ hF (hEF₀.trans hcard)
  exact Subgroup.eq_of_le_of_card_ge hFE hcard

theorem thompson_eq_of_le [Finite G] {p : ℕ} [Fact p.Prime] {E P : Subgroup G}
    (hE : IsElementaryAbelian p ↥E) (hJ : thompsonElem p P ≤ E)
    {Q : Subgroup G} (hEQ : E ≤ Q) (hQP : Q ≤ P) : thompsonElem p Q = E := by
  classical
  have key : ∀ F : Subgroup G, F ≤ P → IsElementaryAbelian p ↥F → Nat.card ↥E ≤ Nat.card ↥F →
      F = E := fun F hFP hFe hc => eq_of_card_le_of_thompson hJ hFP hFe hc
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨F, hFQ, hFe, hFmax, hyF⟩
    have hEF : Nat.card ↥E ≤ Nat.card ↥F := hFmax E hEQ hE
    have : F = E := key F (hFQ.trans hQP) hFe hEF
    exact this ▸ hyF
  · intro x hx
    refine Subgroup.subset_closure ⟨E, hEQ, hE, fun F' hF'Q hF'e => ?_, hx⟩
    by_contra hlt
    have hlt' : Nat.card ↥E ≤ Nat.card ↥F' := (Nat.lt_of_not_le hlt).le
    have : F' = E := key F' (hF'Q.trans hQP) hF'e hlt'
    exact hlt (this ▸ le_rfl)

theorem sylow_of_torus_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {E H Q : Subgroup G}
    (hJ : ∀ Q' : Subgroup G, E ≤ Q' → Q' ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q' →
      thompsonElem p Q' = E)
    (hQ : IsSylowOf p Q (H ⊓ Subgroup.normalizer (E : Set G))) (hEQ : E ≤ Q) :
    IsSylowOf p Q H := by
  have hQH : Q ≤ H := hQ.1.trans inf_le_left
  have hJQ : thompsonElem p Q = E := hJ Q hEQ (hQ.1.trans inf_le_right) hQ.2.1
  obtain ⟨Q', hQ', hQQ'⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQH hQ.2.1
  by_cases heq : Q = Q'
  · exact heq ▸ hQ'
  · exfalso
    obtain ⟨y, hyQ', hyQ, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff hQQ' hQ'.2.1 heq
    have hyW : y ∈ Subgroup.normalizer (E : Set G) := by
      have := mem_normalizer_thompsonElem (p := p) hyN
      rwa [hJQ] at this
    have hyH : y ∈ H := hQ'.1 hyQ'
    have hR : Q ⊔ Subgroup.zpowers y ≤ H ⊓ Subgroup.normalizer (E : Set G) :=
      sup_le hQ.1 (Subgroup.zpowers_le.2 ⟨hyH, hyW⟩)
    have hRp : IsPGroup p ↥(Q ⊔ Subgroup.zpowers y) :=
      hQ'.2.1.to_le (sup_le hQQ' (Subgroup.zpowers_le.2 hyQ'))
    have := le_of_isSylowOf_of_isPGroup hQ hRp le_sup_left hR
    exact hyQ (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

theorem frattini_torus [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {H H₁ : Subgroup G} (hEH₁ : E ≤ H₁) (hH₁H : H₁ ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (H₁ : Set G)) :
    H ≤ H₁ ⊔ (H ⊓ Subgroup.normalizer (E : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p ↥E
  have hEW : E ≤ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer
  have hEHW : E ≤ H ⊓ Subgroup.normalizer (E : Set G) := le_inf (hEH₁.trans hH₁H) hEW
  obtain ⟨Q₀, hQ₀, hEQ₀⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hEHW hEp
  have hQ₀W : Q₀ ≤ Subgroup.normalizer (E : Set G) := hQ₀.1.trans inf_le_right
  have hJQ₀ : thompsonElem p Q₀ = E := hJ Q₀ hEQ₀ hQ₀W hQ₀.2.1
  have hQ₀syl : IsSylowOf p Q₀ H := sylow_of_torus_normalizer hJ hQ₀ hEQ₀
  have hQ₁ : IsSylowOf p (Q₀ ⊓ H₁) H₁ := by
    have hQ₁p : IsPGroup p ↥(Q₀ ⊓ H₁) := hQ₀.2.1.to_le inf_le_left
    obtain ⟨S, hS, hQ₁S⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (inf_le_right : Q₀ ⊓ H₁ ≤ H₁) hQ₁p
    obtain ⟨S', hS', hSS'⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (hS.1.trans hH₁H) hS.2.1
    obtain ⟨g, hgH, hg⟩ := exists_conj_of_isSylowOf hp hQ₀syl hS'
    have hg' : g⁻¹ ∈ Subgroup.normalizer (H₁ : Set G) :=
      (Subgroup.normalizer (H₁ : Set G)).inv_mem (hnorm hgH)
    have hmapS : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q₀ ⊓ H₁ := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, ?_⟩
      · have := (hg s).1 (hSS' hs)
        simpa [MulAut.conj_apply] using this
      · have := (Subgroup.mem_normalizer_iff.1 hg' s).1 (hS.1 hs)
        simpa [MulAut.conj_apply] using this
    have hcard : Nat.card ↥S ≤ Nat.card ↥(Q₀ ⊓ H₁) := by
      have h1 : Nat.card ↥(S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥S :=
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
      rw [← h1]
      exact Subgroup.card_le_of_le hmapS
    have heq : Q₀ ⊓ H₁ = S := Subgroup.eq_of_le_of_card_ge hQ₁S hcard
    exact heq ▸ hS
  intro z hz
  have hEz : E.map (MulAut.conj z).toMonoidHom ≤ H₁ := by
    rintro _ ⟨e, he, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hnorm hz) e).1 (hEH₁ he)
    simpa [MulAut.conj_apply] using this
  have hEzp : IsPGroup p ↥(E.map (MulAut.conj z).toMonoidHom) := hEp.map _
  obtain ⟨Q', hQ', hEzQ'⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hEz hEzp
  obtain ⟨h, hhH₁, hh⟩ := exists_conj_of_isSylowOf hp hQ₁ hQ'
  have hFQ₀ : E.map (MulAut.conj (h⁻¹ * z)).toMonoidHom ≤ Q₀ := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : z * e * z⁻¹ ∈ Q' := hEzQ' ⟨e, he, by simp [MulAut.conj_apply]⟩
    have h2 := (hh _).1 h1
    have h3 : (h⁻¹ * z) * e * (h⁻¹ * z)⁻¹ = h⁻¹ * (z * e * z⁻¹) * h := by group
    show (h⁻¹ * z) * e * (h⁻¹ * z)⁻¹ ∈ Q₀
    rw [h3]
    exact h2.1
  have hFe : IsElementaryAbelian p ↥(E.map (MulAut.conj (h⁻¹ * z)).toMonoidHom) :=
    IsElementaryAbelian.map (A := E) (MulAut.conj (h⁻¹ * z)).toMonoidHom
  have hFcard : Nat.card ↥(E.map (MulAut.conj (h⁻¹ * z)).toMonoidHom) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (MulAut.conj (h⁻¹ * z)).injective
  have hFE : E.map (MulAut.conj (h⁻¹ * z)).toMonoidHom = E :=
    eq_of_card_le_of_thompson hJQ₀.le hFQ₀ hFe hFcard.ge
  have hwW : h⁻¹ * z ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hFE
  have hwH : h⁻¹ * z ∈ H := H.mul_mem (H.inv_mem (hH₁H hhH₁)) hz
  have hz' : h * (h⁻¹ * z) = z := by group
  rw [← hz']
  exact Subgroup.mul_mem_sup hhH₁ ⟨hwH, hwW⟩

theorem frattini_torus_le [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {H H₁ N : Subgroup G} (hEH₁ : E ≤ H₁) (hH₁H : H₁ ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (H₁ : Set G)) (hH₁N : H₁ ≤ N)
    (hWN : Subgroup.normalizer (E : Set G) ≤ N) : H ≤ N :=
  (frattini_torus hp hE hJ hEH₁ hH₁H hnorm).trans (sup_le hH₁N (inf_le_right.trans hWN))

theorem normalizer_le_of_centralizer_le [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {B N₀ : Subgroup G} (hBE : B ≤ E) (hWN : Subgroup.normalizer (E : Set G) ≤ N₀)
    (hC : Subgroup.centralizer (B : Set G) ≤ N₀) : Subgroup.normalizer (B : Set G) ≤ N₀ := by
  have hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' => by
    have := hE
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨e, he⟩ : ↥E) ⟨e', he'⟩)
  have hEC : E ≤ Subgroup.centralizer (B : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm b (hBE hb) e he)
  refine frattini_torus_le hp hE hJ (H := Subgroup.normalizer (B : Set G))
    (H₁ := Subgroup.centralizer (B : Set G)) hEC (Subgroup.centralizer_le_normalizer _) ?_ hC hWN
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    have hxb : x⁻¹ * b * x ∈ B := by
      have hx' := (Subgroup.normalizer (B : Set G)).inv_mem hx
      have := (Subgroup.mem_normalizer_iff.1 hx' b).1 hb
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.1 hy _ hxb
    calc b * (x * y * x⁻¹) = x * ((x⁻¹ * b * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * b * x)) * x⁻¹ := by rw [h1]
      _ = (x * y * x⁻¹) * b := by group
  · intro hy
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    have hxb : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hx b).1 hb
    have h1 := Subgroup.mem_centralizer_iff.1 hy _ hxb
    have : x * (b * y) * x⁻¹ = x * (y * b) * x⁻¹ := by
      calc x * (b * y) * x⁻¹ = (x * b * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * y * x⁻¹) * (x * b * x⁻¹) := h1
        _ = x * (y * b) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

theorem thompson_eq_of_node155 (h155 : Node155) [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152 p E A (lieGenerated p E)) {Q : Subgroup G} (hEQ : E ≤ Q)
    (hQW : Q ≤ Subgroup.normalizer (E : Set G)) (hQ : IsPGroup p ↥Q) : thompsonElem p Q = E := by
  have h := h15.h12
  have : Fact p.Prime := ⟨h.prime⟩
  have hE := h.E_elem
  obtain ⟨P, hP, hQP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQW hQ
  have hJP : thompsonElem p P ≤ E := by
    rcases h155 G p A c L E h15 hF hout P hP with hΩ | ⟨-, -, -, hX⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨F, hFP, hFe, -, hyF⟩
      have : IsElementaryAbelian p ↥F := hFe
      have hy : y ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := F) y hyF
      rw [← hΩ]
      exact Subgroup.subset_closure ⟨hFP hyF, hy⟩
    · have hnormP : (P.subgroupOf P).Normal := by
        rw [Subgroup.subgroupOf_self]
        exact Subgroup.normal_top
      exact hX P le_rfl hnormP
  exact thompson_eq_of_le hE hJP hEQ hQP

end Sec15FA

end CFSG.RankThree.PartOne
