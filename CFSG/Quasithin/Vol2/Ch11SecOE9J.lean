module

public import CFSG.Quasithin.Vol2.Ch11SecOE9I
public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Vol2.Ch11SecOE9H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.X6 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem map_parN_of_map_rootA (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {θ : MulAut (antiSp K)}
    {i j : Axis} (h : (rootA K i).map θ.toMonoidHom = rootA K j) :
    (parN K i).map θ.toMonoidHom = parN K j := by
  rw [parN_eq hK hn, parN_eq hK hn, Subgroup.map_equiv_normalizer_eq, h]

theorem map_parC_of_map_rootA (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {θ : MulAut (antiSp K)}
    {i j : Axis} (h : (rootA K i).map θ.toMonoidHom = rootA K j) :
    (parC K i).map θ.toMonoidHom = parC K j := by
  rw [← dInf_parN hK hn i, ← dInf_parN hK hn j, ← dInf_map_equiv,
    map_parN_of_map_rootA hK hn h]

theorem normalizer_U_le_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ≤ parN K i := by
  rw [← parN_inf_eq hK hn]
  cases i
  · exact inf_le_left
  · exact inf_le_right

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal] (ψ : antiSp K ≃* ↥L)

omit [Finite G] in
theorem fix_or_swap (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {t : G}
    (ht : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    ((radA1 K).map (autHom ψ t).toMonoidHom = radA1 K ∧
        (radA2 K).map (autHom ψ t).toMonoidHom = radA2 K) ∨
      ((radA1 K).map (autHom ψ t).toMonoidHom = radA2 K ∧
        (radA2 K).map (autHom ψ t).toMonoidHom = radA1 K) :=
  map_radA_of_map_U _ (map_autHom_antiUnipotent ψ hψ ht)

omit [Finite G] [Finite K] in
theorem inf_normalizer_eq (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) =
      (Subgroup.normalizer (antiUnipotent K : Set (antiSp K))).map (emb ψ) := by
  ext x
  constructor
  · rintro ⟨hxL, hxN⟩
    obtain ⟨g, rfl⟩ := exists_emb_eq ψ hxL
    refine ⟨g, ?_, rfl⟩
    have h := map_autHom_antiUnipotent ψ hψ hxN
    rw [autHom_emb] at h
    exact A1b.conjSub_eq_iff_mem_normalizer.mp h
  · rintro ⟨g, hg, rfl⟩
    refine ⟨emb_mem ψ g, ?_⟩
    show emb ψ g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
    rw [inf_eq_map_emb ψ hψ, mem_normalizer_map_emb_iff, autHom_emb]
    exact A1b.conjSub_eq_iff_mem_normalizer.mpr hg

theorem isSolvable_normalizer (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L)
    (htwo : ∀ x : G, ∃ k : ℕ, x ^ 2 ^ k ∈ L) :
    Group.IsSolvable ↥(Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) := by
  refine isSolvable_of_inf htwo ?_
  rw [inf_comm, inf_normalizer_eq ψ hψ]
  have := isSolvable_normalizer_U hK hn
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ _ (emb_injective ψ)).symm.toMonoidHom)
    (MulEquiv.injective _)

theorem isMaxParabolic2_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) (hT : IsSylowIn 2 T ⊤)
    (i : Axis) : IsMaxParabolic2 L ((parN K i).map (emb ψ)) ∧
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ (parN K i).map (emb ψ) := by
  have hLn : L.Normal := inferInstance
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
      le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hB : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ (parN K i).map (emb ψ) := by
    rw [inf_normalizer_eq ψ hψ]
    exact Subgroup.map_mono (normalizer_U_le_parN hK hn i)
  have hle : (parN K i).map (emb ψ) ≤ L := (Subgroup.map_le_range _ _).trans (range_emb ψ).le
  have hcoat : IsCoatom (parN K i) := by
    rw [coatom_iff hK hn (le_parN hK hn i)]
    cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨⟨⟨hle, T ⊓ L, hTL, hB⟩, fun h => parN_ne_top hK hn i ?_, ?_⟩, hB⟩
  · apply Subgroup.map_injective (emb_injective ψ)
    rw [h, ← MonoidHom.range_eq_map, range_emb]
  · rintro Q ⟨hQL, -⟩ hQ hPQ
    have hQ₀ : (Q.comap (emb ψ)).map (emb ψ) = Q :=
      Subgroup.map_comap_eq_self (by rw [range_emb]; exact hQL)
    rcases hcoat.le_iff.mp (Subgroup.map_le_iff_le_comap.mp hPQ) with h | h
    · exfalso
      apply hQ
      rw [← hQ₀, h, ← MonoidHom.range_eq_map, range_emb]
    · rw [← hQ₀, h]

theorem exists_swap (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) (hT : IsSylowIn 2 T ⊤)
    (htw : E2.IsDiagramNontrivial T L (T ⊓ L)) :
    ∃ t ∈ T, (radA1 K).map (autHom ψ t).toMonoidHom = radA2 K := by
  obtain ⟨hmax, hB⟩ := isMaxParabolic2_parN ψ hK hn hψ hT .one
  obtain ⟨t, htT, htN⟩ := IsConcreteLE.not_le_iff_exists.mp (htw _ hmax hB)
  refine ⟨t, htT, ?_⟩
  rcases fix_or_swap ψ hψ (SecE3.le_normalizer_inf htT) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso
    apply htN
    rw [mem_normalizer_map_emb_iff]
    exact map_parN_of_map_rootA hK hn (i := .one) (j := .one) h1
  · exact h1

omit [Finite G] in
theorem isCoatom_normalizer (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) (hLT : L ⊔ T = ⊤)
    (hsw : ∃ t ∈ T, (radA1 K).map (autHom ψ t).toMonoidHom = radA2 K) :
    IsCoatom (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) := by
  set D := Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) with hD
  have hTD : T ≤ D := SecE3.le_normalizer_inf
  obtain ⟨t₀, ht₀T, ht₀⟩ := hsw
  have ht₀' : (radA2 K).map (autHom ψ t₀).toMonoidHom = radA1 K := by
    rcases fix_or_swap ψ hψ (hTD ht₀T) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans ht₀) CFSG.QuasithinUnique.Fin257.Sp4.radA1_ne_radA2
    · exact h2
  have key : ∀ M : Subgroup G, D ≤ M → M ≠ ⊤ → M ≤ D := by
    intro M hDM hM
    set M₀ := M.comap (emb ψ) with hM₀
    have hUM₀ : antiUnipotent K ≤ M₀ := by
      rw [hM₀, ← Subgroup.map_le_iff_le_comap, ← inf_eq_map_emb ψ hψ]
      exact (inf_le_left.trans hTD).trans hDM
    have hM₀t : M₀ ≠ ⊤ := by
      intro h
      apply hM
      rw [eq_top_iff, ← hLT]
      refine sup_le (fun x hx => ?_) (hTD.trans hDM)
      obtain ⟨g, rfl⟩ := exists_emb_eq ψ hx
      have hg : g ∈ M₀ := h ▸ Subgroup.mem_top g
      exact hg
    have hθ : ∀ s ∈ M, ∀ g ∈ M₀, autHom ψ s g ∈ M₀ := by
      intro s hs g hg
      show emb ψ (autHom ψ s g) ∈ M
      rw [emb_autHom]
      exact M.mul_mem (M.mul_mem hs hg) (M.inv_mem hs)
    have hs₀ : t₀ ∈ M := hDM (hTD ht₀T)
    have hle : M₀ ≤ M₀.map (autHom ψ t₀).toMonoidHom := by
      intro g hg
      refine ⟨autHom ψ t₀⁻¹ g, hθ _ (M.inv_mem hs₀) g hg, ?_⟩
      show autHom ψ t₀ (autHom ψ t₀⁻¹ g) = g
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hswap : ∀ i j : Axis, (rootA K i).map (autHom ψ t₀).toMonoidHom = rootA K j →
        M₀ ≤ parN K i → M₀ ≤ parN K j := fun i j hij hi =>
      hle.trans ((Subgroup.map_mono hi).trans (map_parN_of_map_rootA hK hn hij).le)
    obtain ⟨M₁, hM₁, hM₀M₁⟩ := (eq_top_or_exists_le_coatom M₀).resolve_left hM₀t
    have hM₀N : M₀ ≤ parN K .one ⊓ parN K .two := by
      rcases (coatom_iff hK hn (hUM₀.trans hM₀M₁)).mp hM₁ with h | h
      · rw [h] at hM₀M₁
        exact le_inf hM₀M₁ (hswap .one .two ht₀ hM₀M₁)
      · rw [h] at hM₀M₁
        exact le_inf (hswap .two .one ht₀' hM₀M₁) hM₀M₁
    rw [parN_inf_eq hK hn] at hM₀N
    intro x hx
    have hxLT : x ∈ L ⊔ T := hLT ▸ Subgroup.mem_top x
    obtain ⟨l, hl, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxLT
    have hlM : l ∈ M := by
      have h := M.mul_mem hx (M.inv_mem (hDM (hTD hs)))
      rwa [mul_inv_cancel_right] at h
    obtain ⟨g, rfl⟩ := exists_emb_eq ψ hl
    have hgD : emb ψ g ∈ L ⊓ D := by
      rw [hD, inf_normalizer_eq ψ hψ]
      exact ⟨g, hM₀N hlM, rfl⟩
    exact D.mul_mem hgD.2 (hTD hs)
  refine ⟨fun hDt => ?_, fun M hDM => ?_⟩
  · have h := inf_normalizer_eq ψ hψ
    rw [← hD, hDt, inf_top_eq] at h
    have h2 : (⊤ : Subgroup (antiSp K)).map (emb ψ) =
        (Subgroup.normalizer (antiUnipotent K : Set (antiSp K))).map (emb ψ) := by
      rw [← MonoidHom.range_eq_map, range_emb]
      exact h
    have h' := (Subgroup.map_injective (emb_injective ψ) h2).symm
    exact parN_ne_top hK hn .one (eq_top_iff.mpr (h' ▸ normalizer_U_le_parN hK hn .one))
  · by_contra hMt
    exact lt_irrefl D (lt_of_lt_of_le hDM (key M hDM.le hMt))

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
