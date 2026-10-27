module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L71

variable {G : Type*} [Group G]

theorem zOf_eq_inf_centralizer (X : Subgroup G) :
    zOf X = X ⊓ Subgroup.centralizer (X : Set G) := by
  ext z
  rw [mem_zOf_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem zOf_bot : zOf (⊥ : Subgroup G) = ⊥ :=
  eq_bot_iff.mpr (zOf_le ⊥)

theorem zOf_inf_centralizer_eq [Finite G] {A H N P F : Subgroup G} {Ω : Set (Subgroup G)} {r : ℕ}
    (hΩ : IsRegFam A H Ω N) (hr : r.Prime) (hPH : P ≤ H) (hP : IsPGroup r P)
    (hidx : Nat.Coprime (P.relIndex H) r) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hFA : F ≤ A) (hFN : F ⊓ N = ⊥) :
    zOf (P ⊓ Subgroup.centralizer (F : Set G)) = zOf P ⊓ Subgroup.centralizer (F : Set G) := by
  by_cases hne : ∀ L ∈ Ω, P ⊓ L ≠ ⊥
  · have hΩP := hΩ.inf_family hr hPH hP hidx hAP hne
    have key := center_centralizer_eq hΩP.isDirectProduct (A := F)
      (fun a ha J hJ => hΩP.map_conj_mem a (hFA ha) J hJ) (fun a ha ha1 J hJ =>
        hΩP.map_conj_ne (hFA ha) (fun haN => ha1 (Subgroup.mem_bot.mp
          (hFN ▸ Subgroup.mem_inf.mpr ⟨ha, haN⟩))) hJ)
    rw [zOf_eq_inf_centralizer, zOf_eq_inf_centralizer]
    exact key
  · push Not at hne
    obtain ⟨L, hL, hPL⟩ := hne
    have hall : ∀ L' ∈ Ω, P ⊓ L' = ⊥ := by
      intro L' hL'
      obtain ⟨x, hx, rfl⟩ := hΩ.transitive L hL L' hL'
      have hP' : P.map (MulAut.conj x).toMonoidHom = P :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAP hx)
      have hmap : (P ⊓ L).map (MulAut.conj x).toMonoidHom =
          P ⊓ L.map (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, hP']
      rw [← hmap, hPL, Subgroup.map_bot]
    have hdp := (IsDirectProduct.sylow_decomp hΩ.isDirectProduct hr hPH hP hidx).1
    have hP0 : P = ⊥ := by
      rw [← hdp.sSup_eq]
      refine le_bot_iff.mp (sSup_le ?_)
      rintro _ ⟨L', hL', rfl⟩
      exact (hall L' hL').le
    subst hP0
    rw [bot_inf_eq, zOf_bot, bot_inf_eq]

end L71

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_7_1_a_gen (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A)
    (hfree : ∀ a ∈ B, a ≠ 1 → ∃ (Ω : Set (Subgroup G)) (N : Subgroup G),
      IsRegFam A (θ a) Ω N ∧ B ⊓ N = Subgroup.zpowers a)
    {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    zOf (S ⊓ Subgroup.centralizer {a}) ⊓ Subgroup.centralizer (B : Set G) =
      zOf (S ⊓ Subgroup.centralizer (B : Set G)) := by
  have haA : a ∈ A := hB.1 haB
  obtain ⟨hPθ, hPr, hidx, hAP⟩ := sylow_of_isSr h hr hS haA ha1
  obtain ⟨Ω, N, hΩ, hBN⟩ := hfree a haB ha1
  obtain ⟨b, hbB, hb⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers a := by
    by_contra! hcon
    have hle := Subgroup.card_le_of_le (fun b hb => hcon b hb : B ≤ Subgroup.zpowers a)
    rw [hB.2, h.card_zpowers haA ha1] at hle
    nlinarith [h.prime.one_lt]
  have hb1 : b ≠ 1 := fun h1 => hb (h1 ▸ one_mem _)
  have hbA : b ∈ A := hB.1 hbB
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers hbA hb1)
      (fun hle => hb (hle (Subgroup.mem_zpowers b)))
  have hBeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = B := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haB)
      (Subgroup.zpowers_le.mpr hbB)) ?_
    rw [hB.2, card_sup_of_le_elemAbelian h.elemAbelian (Subgroup.zpowers_le.mpr haA)
      (Subgroup.zpowers_le.mpr hbA) hdisj, h.card_zpowers haA ha1, h.card_zpowers hbA hb1, sq]
  have hFN : Subgroup.zpowers b ⊓ N = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxB : x ∈ B ⊓ N := ⟨Subgroup.zpowers_le.mpr hbB hx.1, hx.2⟩
    rw [hBN] at hxB
    have : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨hxB, hx.1⟩
    rwa [hdisj] at this
  have hCB : Subgroup.centralizer (B : Set G) =
      Subgroup.centralizer {a} ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [← hBeq, centralizer_sup, centralizer_zpowers_eq_singleton]
  have hkey := L71.zOf_inf_centralizer_eq hΩ hr.1 hPθ hPr hidx hAP
    (Subgroup.zpowers_le.mpr hbA) hFN
  have hPF : S ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) =
      S ⊓ Subgroup.centralizer (B : Set G) := by
    rw [hCB, inf_assoc]
  rw [← hPF, hkey]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hCB, Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, -, hxb⟩
    exact ⟨hx, hxb⟩
  · rintro ⟨hx, hxb⟩
    exact ⟨hx, (zOf_le _ hx).2, hxb⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
