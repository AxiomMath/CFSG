module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.RankThree.GF2n.Smith81.S81XE7Mon
public import CFSG.RankThree.GF2n.Smith81.S81XD6Fin
public import CFSG.RankThree.GF2n.Smith81.S81D6Bruhat

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K]

private theorem d6mon_UL_le_Lam : UL K ≤ Lam K := by
  rw [UL, Subgroup.closure_le]
  rintro g ⟨β, hβ, hzero, -, c, rfl⟩
  exact xu_mem_Lam (show β ∈ Perp from ⟨hβ, hzero⟩) c

theorem ULG_le_LamG : ULG K ≤ LamG K := by
  intro g hg
  rw [mem_ULG] at hg
  rw [mem_LamG]
  exact d6mon_UL_le_Lam hg

theorem single_mem_Perp (i : Fin (Tag.rank .E7)) (hi : 1 ≤ i.val) :
    (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := by
  have hne : i ≠ (⟨0, by decide⟩ : Fin (Tag.rank .E7)) := by
    intro h
    subst h
    exact absurd hi (by decide)
  exact perp_iff.2 ⟨isRoot_single .E7 i, by rw [Pi.single_apply, if_neg (Ne.symm hne)]⟩

theorem nm_mem_LamG (i : Fin (Tag.rank .E7)) (hi : 1 ≤ i.val) : e7Data_valid.nm K i ∈ LamG K := by
  have hsP : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := single_mem_Perp i hi
  have hsN : -(Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := neg_mem_Perp hsP
  rw [mem_LamG]
  show ((e7Data_valid.xm K (Pi.single i 1) 1 * e7Data_valid.xm K (-Pi.single i 1)
      (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * e7Data_valid.xm K (Pi.single i 1) 1 :
      ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (xu_mem_Lam hsP 1) (xu_mem_Lam hsN _)) (xu_mem_Lam hsP 1)

variable [CharP K 2]

private theorem d6mon_orbit_actWord (ω : List ℕ) :
    (∀ i ∈ ω, 1 ≤ i % 7) → ∀ a : Fin e7Data.d,
    (∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)),
        n ∈ LamG K ∧ IsMon n σ ρ ∧ σ b0 = a) →
    ∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)),
        n ∈ LamG K ∧ IsMon n σ ρ ∧ ((σ b0 : Fin e7Data.d) : ℕ) = actWord ω (a : ℕ) := by
  induction ω with
  | nil =>
    intro _ a ha
    obtain ⟨n, σ, ρ, hn, hm, hσ⟩ := ha
    exact ⟨n, σ, ρ, hn, hm, congrArg Fin.val hσ⟩
  | cons i ω ih =>
    intro hω a ha
    obtain ⟨n, σ, ρ, hn, hm, hσ⟩ := ha
    have hL : 1 ≤ (letter i).val := hω i (by simp)
    have hn' : e7Data_valid.nm K (letter i) * n ∈ LamG K :=
      mul_mem (nm_mem_LamG (letter i) hL) hn
    have hm' : IsMon (e7Data_valid.nm K (letter i) * n)
        (e7Data_valid.sRefl (letter i) ∘ σ) (reflect .E7 (letter i) ∘ ρ) :=
      (IsMon.nm (K := K) (letter i)).mul hm
    have hfold : actWord (i :: ω) (a : ℕ) =
        actWord ω ((e7Data_valid.sRefl (letter i) a : Fin e7Data.d) : ℕ) := by
      rw [e7Data_valid.sRefl_val]
      try rfl
    obtain ⟨n', σ', ρ', hn'', hm'', hs⟩ := ih (fun j hj => hω j (List.mem_cons_of_mem i hj))
      (e7Data_valid.sRefl (letter i) a)
      ⟨_, _, _, hn', hm', congrArg (e7Data_valid.sRefl (letter i)) hσ⟩
    exact ⟨n', σ', ρ', hn'', hm'', hs.trans hfold.symm⟩

theorem exists_isMonL_of_weight (c : Fin e7Data.d) (hc : pr c theta = 0) :
    ∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)),
      n ∈ LamG K ∧ IsMon n σ ρ ∧ σ b0 = c := by
  obtain ⟨n, σ, ρ, hn, hm, hσ⟩ := d6mon_orbit_actWord (K := K) (weightWordsD6.getD c [])
    (weightWordsD6_letters c) b0 ⟨1, id, id, one_mem _, IsMon.one, rfl⟩
  exact ⟨n, σ, ρ, hn, hm, Fin.ext (hσ.trans (weightWordsD6_correct c hc))⟩

private theorem d6mon_tor_conj_UL {t : Gp K} (ht : t ∈ Tor K) :
    ∀ g ∈ UL K, (t : (Module.End K (V K))ˣ) * g * (t : (Module.End K (V K))ˣ)⁻¹ ∈ UL K := by
  intro g hg
  have key : UL K ≤ (UL K).comap (MulAut.conj (t : (Module.End K (V K))ˣ)).toMonoidHom := by
    rw [UL, Subgroup.closure_le]
    rintro g' ⟨β, hβ, hzero, hpos, c, rfl⟩
    obtain ⟨s, -, hs⟩ := tor_conj_xm ht hβ
    have hc : (t : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c *
        (t : (Module.End K (V K))ˣ)⁻¹ = e7Data_valid.xu K β (s * c) :=
      congrArg Subtype.val (hs c)
    have hmem : e7Data_valid.xu K β (s * c) ∈ UL K :=
      Subgroup.subset_closure ⟨β, hβ, hzero, hpos, s * c, rfl⟩
    show (t : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c *
        (t : (Module.End K (V K))ˣ)⁻¹ ∈ UL K
    rw [hc]
    exact hmem
  exact key hg

theorem tor_conj_ULG {t : Gp K} (ht : t ∈ Tor K) {u : Gp K} (hu : u ∈ ULG K) : t * u * t⁻¹ ∈ ULG K := by
  rw [mem_ULG] at hu ⊢
  exact d6mon_tor_conj_UL ht _ hu

theorem bruhat_L {g : Gp K} (hg : g ∈ LamG K) :
    ∃ u₁ ∈ ULG K, ∃ t₁ ∈ Tor K, ∃ t₂ ∈ Tor K, ∃ u₂ ∈ ULG K, ∃ (n : Gp K)
      (σ : Fin e7Data.d → Fin e7Data.d) (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)),
      IsMon n σ ρ ∧ g = u₁ * (t₁ * n * t₂) * u₂ := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg'⟩ := Lam_bruhat (K := K) (mem_LamG.1 hg)
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := mem_BorL_iff.1 hb₁
  obtain ⟨u₂, hu₂, t₂, ht₂, rfl⟩ := mem_BorL_iff.1 hb₂
  obtain ⟨σ, ρ, hm⟩ := isMon_nW (K := K) w
  have hu₂' : t₂⁻¹ * u₂ * t₂⁻¹⁻¹ ∈ ULG K := tor_conj_ULG (inv_mem ht₂) hu₂
  rw [inv_inv] at hu₂'
  refine ⟨u₁, hu₁, t₁, ht₁, t₂, ht₂, t₂⁻¹ * u₂ * t₂, hu₂', nW K w, σ, ρ, hm, ?_⟩
  rw [hg']
  group

end CFSG.RankThree.GF2n.Smith81.D6X
