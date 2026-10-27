module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

end Counterexample

@[expose] def thetaTilde {G : Type*} [Group G] (θ : G → Subgroup G) (E : Subgroup G) :
    G → Subgroup G :=
  fun g => kOf (θ g) ⊓ thetaOf θ E

@[expose] def wTilde {G : Type*} [Group G] (θ : G → Subgroup G) (E B : Subgroup G) :
    Subgroup G :=
  thetaSup B (thetaTilde θ E)

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem isFunctor_thetaTilde
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    IsFunctor p B (thetaTilde θ E) := by
  have h2 := h.isFunctor_kOf S hB hEB
  have hN : B ≤ Subgroup.normalizer (thetaOf θ E : Set G) :=
    hB.1.trans (h.isFunctor.normalizes_thetaOf S.mem.1)
  refine ⟨fun a ha ha1 => inf_le_left.trans (h2.le_centralizer a ha ha1),
    fun a ha ha1 => (h2.coprime a ha ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left),
    fun a ha ha1 g hg => T517.mem_normalizer_inf (h2.normalized a ha ha1 hg) (hN hg),
    fun a ha ha1 b hb hb1 x hx => ?_⟩
  obtain ⟨⟨hxK, hxE⟩, hxc⟩ := hx
  exact ⟨h2.balance a ha ha1 b hb hb1 ⟨hxK, hxc⟩, hxE⟩

theorem thetaTilde_eq_inf_centralizer (h : Counterexample p A θ) (hE : E ≤ A) {b : G}
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    thetaTilde θ E b = kOf (θ b) ⊓ Subgroup.centralizer (E : Set G) := by
  have hle : thetaOf θ E ≤ Subgroup.centralizer (E : Set G) :=
    h.isFunctor.thetaOf_le_centralizer hE
  apply le_antisymm
  · exact inf_le_inf_left _ hle
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hx' : x ∈ θ b ⊓ Subgroup.centralizer (E : Set G) := ⟨kOf_le _ hx.1, hx.2⟩
    rw [h.isFunctor.inf_centralizer_eq_thetaOf hb hb1 hE] at hx'
    exact thetaOf_anti le_sup_right hx'

theorem thetaOf_thetaTilde
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    thetaOf (thetaTilde θ E) B = kOf (thetaOf θ B) ⊓ thetaOf θ E := by
  have key : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ∉ Subgroup.zpowers b →
      Subgroup.zpowers b ⊔ Subgroup.zpowers b' = B →
        kOf (θ b) ⊓ Subgroup.centralizer {b'} = kOf (thetaOf θ B) := by
    intro b hb hb1 b' hb' hb'n hbasis
    have hb'1 : b' ≠ 1 := fun e => hb'n (e ▸ one_mem _)
    rw [h.kOf_apply_inf_centralizer_eq S hB hEB hb hb' hb1 hb'1 hb'n, hbasis]
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, hb1⟩ := h.exists_ne_one_of_mem_E2 hB
    obtain ⟨b', hb', hb'n, hbasis⟩ := h.exists_basis hB hb hb1
    have hb'1 : b' ≠ 1 := fun e => hb'n (e ▸ one_mem _)
    have hxb : x ∈ thetaTilde θ E b := mem_thetaOf_iff.mp hx b hb hb1
    have hxb' : x ∈ thetaTilde θ E b' := mem_thetaOf_iff.mp hx b' hb' hb'1
    have hxc : x ∈ Subgroup.centralizer {b'} :=
      h.isFunctor.le_centralizer b' (hB.1 hb') hb'1 (kOf_le _ hxb'.1)
    refine ⟨?_, hxb.2⟩
    rw [← key b hb hb1 b' hb' hb'n hbasis]
    exact ⟨hxb.1, hxc⟩
  · rintro x ⟨hxK, hxE⟩
    refine mem_thetaOf_iff.mpr fun b hb hb1 => ⟨?_, hxE⟩
    obtain ⟨b', hb', hb'n, hbasis⟩ := h.exists_basis hB hb hb1
    rw [← key b hb hb1 b' hb' hb'n hbasis] at hxK
    exact hxK.1

theorem regular_lcal_thetaOf
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    (∀ J ∈ lcal (thetaOf θ E), ∀ J' ∈ lcal (thetaOf θ E),
      ∃ b ∈ B, J' = J.map (MulAut.conj b).toMonoidHom) ∧
    (∀ J ∈ lcal (thetaOf θ E), ∀ b ∈ B, b ≠ 1 → J.map (MulAut.conj b).toMonoidHom ≠ J) := by
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 S.mem
  have hbN := h.lemma_6_9_b S.mem.1 hE0
  refine ⟨fun J hJ J' hJ' => ?_, fun J hJ b hb hb1 hJb => ?_⟩
  · obtain ⟨a, haA, hJa⟩ := (h.lemma_6_9_d S.mem.1 hE0).1 J hJ J' hJ'
    have haEB : a ∈ E ⊔ B := (S.sup_eq h hB hEB).symm ▸ haA
    have hcomm : ∀ e ∈ E, ∀ β ∈ B, Commute e β := fun e he β hβ =>
      h.comm_of_mem_A (S.mem.1 he) (hB.1 hβ)
    obtain ⟨e, he, β, hβ, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp haEB
    have hJβ : J.map (MulAut.conj β).toMonoidHom ∈ lcal (thetaOf θ E) :=
      map_conj_mem_lcal hJ (h.isFunctor.normalizes_thetaOf S.mem.1 (hB.1 hβ))
    refine ⟨β, hβ, ?_⟩
    rw [hJa, ← T517.map_conj_map_conj]
    have heN : e ∈ Subgroup.normalizer ((J.map (MulAut.conj β).toMonoidHom : Subgroup G) :
        Set G) := by
      have := hbN _ hJβ
      rw [S.bN_E] at this
      exact (Subgroup.mem_inf.mp (this ▸ he)).2
    exact L69.map_conj_eq_self_iff.mpr heN
  · have hbN' := L69.map_conj_eq_self_iff.mp hJb
    have hbA : b ∈ A ⊓ Subgroup.normalizer (J : Set G) := ⟨hB.1 hb, hbN'⟩
    rw [← hbN J hJ, S.bN_E] at hbA
    have : b ∈ E ⊓ B := ⟨hbA, hb⟩
    rw [hEB, Subgroup.mem_bot] at this
    exact hb1 this

theorem kOf_thetaOf_inf_centralizer_le
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) :
    kOf (thetaOf θ E) ⊓ Subgroup.centralizer {b} ≤ thetaTilde θ E b := by
  have hbE : b ∉ E := not_mem_of_mem_complement hEB hb hb1
  rw [h.kOf_thetaOf_inf_centralizer_eq S (hB.1 hb) hbE, sup_comm,
    h.thetaTilde_eq_inf_centralizer S.mem.1 (hB.1 hb) hb1]
  exact h.kOf_thetaOf_sup_le (hB.1 hb) hb1 S.mem.1

theorem wTilde_le
    (h : Counterexample p A θ) (S : Setting614 p A θ E) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    wTilde θ E B ≤ thetaOf θ E ∧ A ≤ Subgroup.normalizer (wTilde θ E B : Set G) := by
  have hWE : wTilde θ E B ≤ thetaOf θ E := thetaSup_le fun _ _ _ => inf_le_right
  refine ⟨hWE, ?_⟩
  have hBN : B ≤ Subgroup.normalizer (wTilde θ E B : Set G) :=
    (h.isFunctor_thetaTilde S hB hEB).normalizes_thetaSup
  have hEC : wTilde θ E B ≤ Subgroup.centralizer (E : Set G) :=
    hWE.trans (h.isFunctor.thetaOf_le_centralizer S.mem.1)
  have hEN : E ≤ Subgroup.normalizer (wTilde θ E B : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hEC he)
  rw [← S.sup_eq h hB hEB]
  exact sup_le hEN hBN

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
