module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem uc22p22v_conj_mem_conjClosure {N E : Subgroup G} {g : G}
    (hg : ∀ x ∈ N, ∀ z ∈ E, ∃ y ∈ N, ∃ z' ∈ E, g * (x * z * x⁻¹) * g⁻¹ = y * z' * y⁻¹) :
    ∀ w ∈ conjClosure N E, g * w * g⁻¹ ∈ conjClosure N E := by
  have key : conjClosure N E ≤ (conjClosure N E).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨x, hx, rfl⟩ := hK
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, z', hz', he⟩ := hg x hx z hz
    have hmem : y * z' * y⁻¹ ∈ E.map (MulAut.conj y).toMonoidHom :=
      ⟨z', hz', by simp [MulAut.conj_apply]⟩
    have hle : E.map (MulAut.conj y).toMonoidHom ≤ conjClosure N E :=
      le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf N E) => K) _ ⟨y, hy, rfl⟩ le_rfl
    simpa [MulAut.conj_apply, he] using hle hmem
  intro w hw
  exact key hw

omit [Finite G] in
theorem uc22p22v_mem_normalizer_conjClosure {N E : Subgroup G} {g : G}
    (hg : ∀ x ∈ N, ∀ z ∈ E, ∃ y ∈ N, ∃ z' ∈ E, g * (x * z * x⁻¹) * g⁻¹ = y * z' * y⁻¹)
    (hg' : ∀ x ∈ N, ∀ z ∈ E, ∃ y ∈ N, ∃ z' ∈ E, g⁻¹ * (x * z * x⁻¹) * g⁻¹⁻¹ = y * z' * y⁻¹) :
    g ∈ normalizer (conjClosure N E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨uc22p22v_conj_mem_conjClosure hg w, fun hw => ?_⟩
  have := uc22p22v_conj_mem_conjClosure hg' _ hw
  simpa [mul_assoc] using this

omit [Finite G] in
theorem uc22p22v_le_normalizer_conjClosure (N E : Subgroup G) :
    N ≤ normalizer (conjClosure N E : Set G) := by
  intro g hg
  refine uc22p22v_mem_normalizer_conjClosure (fun x hx z hz => ?_) (fun x hx z hz => ?_)
  · exact ⟨g * x, N.mul_mem hg hx, z, hz, by group⟩
  · exact ⟨g⁻¹ * x, N.mul_mem (N.inv_mem hg) hx, z, hz, by group⟩

omit [Finite G] in
theorem uc22p22v_le_conjClosure (N E : Subgroup G) : E ≤ conjClosure N E := by
  intro z hz
  have hle : E.map (MulAut.conj (1 : G)).toMonoidHom ≤ conjClosure N E :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf N E) => K) _ ⟨1, N.one_mem, rfl⟩ le_rfl
  exact hle ⟨z, hz, by simp [MulAut.conj_apply]⟩

omit [Finite G] in
theorem uc22p22v_conjClosure_mono {N₁ N₂ : Subgroup G} (h : N₁ ≤ N₂) (E : Subgroup G) :
    conjClosure N₁ E ≤ conjClosure N₂ E := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨x, hx, rfl⟩ := hK
  exact le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf N₂ E) => K) _ ⟨x, h hx, rfl⟩ le_rfl

omit [Finite G] in
theorem uc22p22v_conjClosure_le {N E F : Subgroup G} (hN : N ≤ normalizer (F : Set G)) (hE : E ≤ F) :
    conjClosure N E ≤ F := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨x, hx, rfl⟩ := hK
  rintro _ ⟨z, hz, rfl⟩
  have := (Subgroup.mem_normalizer_iff.1 (hN hx) z).1 (hE hz)
  simpa [MulAut.conj_apply] using this

omit [Finite G] in
theorem uc22p22v_internalDirect_conj {m : ℕ} {H : Subgroup G} {Hs : Fin m → Subgroup G}
    (hd : IsInternalDirect H Hs) (i : Fin m) : ∀ a ∈ H, ∀ y ∈ Hs i, a * y * a⁻¹ ∈ Hs i := by
  intro a ha
  rw [← hd.1] at ha
  refine Subgroup.iSup_induction Hs (C := fun a => ∀ y ∈ Hs i, a * y * a⁻¹ ∈ Hs i) ha
    (fun j a haj y hy => ?_) (fun y hy => by simpa using hy) (fun a b ha hb y hy => ?_)
  · by_cases hji : j = i
    · subst hji
      exact (Hs j).mul_mem ((Hs j).mul_mem haj hy) ((Hs j).inv_mem haj)
    · have hcomm := hd.2.1 j i hji a haj y hy
      have e : a * y * a⁻¹ = y := by rw [hcomm]; group
      rw [e]
      exact hy
  · have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb y hy)

theorem uc22p22v_preN_le (D : Data G) (Y : Subgroup (MBar D.M D.U)) : preN D Y ≤ proofN D :=
  inf_le_left

theorem uc22p22v_not_dvd_iSup {ι : Type} [DecidableEq ι] (K : ι → Subgroup G)
    (hK : ∀ i, (⨆ j, K j) ≤ normalizer (K i : Set G)) {p : ℕ} (hp : p.Prime)
    (hcard : ∀ i, ¬ p ∣ Nat.card (K i)) (s : Finset ι) :
    ¬ p ∣ Nat.card (⨆ i ∈ s, K i : Subgroup G) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), K i : Subgroup G) = ⊥ by simp, Subgroup.card_bot]
    exact hp.not_dvd_one
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_comm]
    intro hdvd
    have hle : (⨆ i ∈ s, K i : Subgroup G) ≤ normalizer (K a : Set G) :=
      (iSup₂_le fun i _ => le_iSup K i).trans (hK a)
    have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hle
    have hd : p ∣ Nat.card ↥(⨆ i ∈ s, K i : Subgroup G) * Nat.card ↥(K a) :=
      hprod ▸ Dvd.dvd.mul_right hdvd _
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact ih h
    · exact hcard a h

end CFSG.LocalAnalysis.UniquenessCase.UC22
