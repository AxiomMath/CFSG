module

public import CFSG.Quasithin.EmptyFaithful.S1565L6
public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1565


section Acting

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem exists_sylow_borel_acting (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hker : kerIn (H ⊓ M) H = pCoreOf 2 H) {n : ℕ}
    (hshape : IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K) ∨ IsSz n ↥(E2.star (H ⊓ M) H K))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ S : Sylow 2 ↥(autIH V₁ I H K),
      ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
        ∃ k : ↥K, (k : G) ∈ M ∧ toAutI hF I k = b := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFact := factElem hF hIU
  have hsimple := isSimpleGroup_of_psl2_or_sz hshape
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have : Nontrivial ↥(autIH V₁ I H K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hker' : ∀ k : ↥K, Subgroup.inclusion hKH k ∈ (kerIn (H ⊓ M) H).subgroupOf H →
      toAutI hF I k = 1 := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, hker] at hk
    exact (toAutI_eq_one_iff hF I k).mpr (hF.actH_eq_one_of_mem_pCoreOf hIU hk)
  obtain ⟨S, hS⟩ := exists_sylow_borel_lift hKH (toAutI hF I) (toAutI_surjective hF I) hker'
    hsimple hB
  refine ⟨S, fun b hb => ?_⟩
  obtain ⟨k, hkM, hkb⟩ := hS b hb
  exact ⟨k, (Subgroup.mem_inf.mp hkM).2, hkb⟩

end Acting



section Sum

variable {W : Type} [CommGroup W]

theorem sum_good_element {C A : Subgroup W} {t s s' : MulAut W}
    (hsum : IsSumMod C A (A.map t.toMonoidHom) ⊤) (hts : s' * t = t * s)
    (hAs' : ∀ a ∈ A, s' a = a) (hBs : ∀ a ∈ A, s (t a) = t a)
    (hCs : ∀ c ∈ C, s c = c) (hCs' : ∀ c ∈ C, s' c = c)
    (hAinv : ∀ a ∈ A, s a ∈ A) (hCt : ∀ c ∈ C, t c ∈ C) (hCt' : ∀ c ∈ C, t⁻¹ c ∈ C)
    (hNat : ∀ a ∈ A, s a * a⁻¹ ∈ A ⊓ C → a ∈ C) :
    ∀ w : W, ((s * s') w) * w⁻¹ ∈ C → w ∈ C := by
  intro w hw
  have hwtop : w ∈ A ⊔ A.map t.toMonoidHom ⊔ C := by
    rw [← hsum.1]
    trivial
  obtain ⟨ab, hab, c, hc, rfl⟩ := Subgroup.mem_sup.mp hwtop
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hab
  obtain ⟨a₁, ha₁, hb₁⟩ := hb
  have hb₁' : t a₁ = b := hb₁
  subst hb₁'
  have hs'ta : s' (t a₁) = t (s a₁) := by
    have := congrArg (fun f : MulAut W => f a₁) hts
    simpa using this
  have hss : (s * s') (a * t a₁ * c) = s a * t (s a₁) * c := by
    calc (s * s') (a * t a₁ * c) = s (s' (a * t a₁ * c)) := rfl
      _ = s (s' a * s' (t a₁) * s' c) := by simp only [map_mul]
      _ = s (a * t (s a₁) * c) := by rw [hAs' a ha, hs'ta, hCs' c hc]
      _ = s a * s (t (s a₁)) * s c := by simp only [map_mul]
      _ = s a * t (s a₁) * c := by rw [hBs (s a₁) (hAinv a₁ ha₁), hCs c hc]
  set α : W := s a * a⁻¹ with hα
  set β : W := t (s a₁) * (t a₁)⁻¹ with hβ
  have hαA : α ∈ A := A.mul_mem (hAinv a ha) (A.inv_mem ha)
  have hβB : β ∈ A.map t.toMonoidHom :=
    ⟨s a₁ * a₁⁻¹, A.mul_mem (hAinv a₁ ha₁) (A.inv_mem ha₁), by simp [hβ]⟩
  have hprod : α * β ∈ C := by
    have e : (s * s') (a * t a₁ * c) * (a * t a₁ * c)⁻¹ = α * β := by
      rw [hss]
      apply Additive.ofMul.injective
      simp only [hα, hβ, ofMul_mul, ofMul_inv]
      abel
    rw [← e]
    exact hw
  have hαC : α ∈ C := by
    refine hsum.2 ⟨Subgroup.mem_sup_left hαA, ?_⟩
    have : α = (α * β) * β⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hprod)
      (Subgroup.mem_sup_left ((A.map t.toMonoidHom).inv_mem hβB))
  have hβC : β ∈ C := by
    refine hsum.2 ⟨?_, Subgroup.mem_sup_left hβB⟩
    have : β = (α * β) * α⁻¹ := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hprod)
      (Subgroup.mem_sup_left (A.inv_mem hαA))
  have haC : a ∈ C := hNat a ha ⟨hαA, hαC⟩
  have ha₁C : a₁ ∈ C := by
    have h1 : t⁻¹ β = s a₁ * a₁⁻¹ := by
      rw [hβ, map_mul, map_inv]
      simp
    refine hNat a₁ ha₁ ⟨A.mul_mem (hAinv a₁ ha₁) (A.inv_mem ha₁), ?_⟩
    rw [← h1]
    exact hCt' β hβC
  exact C.mul_mem (C.mul_mem haC (hCt a₁ ha₁C)) hc

end Sum

end CFSG.Quasithin
