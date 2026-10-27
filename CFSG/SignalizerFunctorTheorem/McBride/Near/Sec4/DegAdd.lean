module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegLemma42

public section

open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

section Components

variable {Q : Type*} [Group Q]

theorem normal_of_mem_lcalOf (hDP : IsDirectProduct (lcalOf Q) (⊤ : Subgroup Q))
    {J : Subgroup Q} (hJ : J ∈ lcalOf Q) : J.Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hDP.le_normalizer hJ))

theorem le_or_le_centralizer (hDP : IsDirectProduct (lcalOf Q) (⊤ : Subgroup Q))
    (N : Subgroup Q) [N.Normal] {J : Subgroup Q} (hJ : J ∈ lcalOf Q) :
    J ≤ N ∨ J ≤ Subgroup.centralizer (N : Set Q) := by
  have hJn := normal_of_mem_lcalOf hDP hJ
  have hs : IsSimpleGroup J := hJ.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with h | h
  · right
    have hdis : Disjoint N J := Subgroup.subgroupOf_eq_bot.mp h
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ⁅y, x⁆ ∈ N := by
      rw [commutatorElement_def]
      have : x * y⁻¹ * x⁻¹ ∈ N := by
        have := Subgroup.Normal.conj_mem inferInstance y⁻¹ (N.inv_mem hy) x
        simpa using this
      simpa [mul_assoc] using N.mul_mem hy this
    have h2 : ⁅y, x⁆ ∈ J := by
      rw [commutatorElement_def]
      have : y * x * y⁻¹ ∈ J := Subgroup.Normal.conj_mem hJn x hx y
      exact J.mul_mem this (J.inv_mem hx)
    have h3 : ⁅y, x⁆ ∈ N ⊓ J := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hdis.eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  · left
    exact Subgroup.subgroupOf_eq_top.mp h

theorem isDirectProduct_of_subset {S T : Set (Subgroup Q)} {K K' : Subgroup Q}
    (hK : IsDirectProduct S K) (hT : T ⊆ S) (hsup : sSup T = K') : IsDirectProduct T K' where
  commute J hJ L hL hne x hx y hy := hK.commute J (hT hJ) L (hT hL) hne x hx y hy
  indep := hK.indep.mono hT
  sSup_eq := hsup

theorem isDirectProduct_lcalOf_le (hDP : IsDirectProduct (lcalOf Q) (⊤ : Subgroup Q))
    (N : Subgroup Q) [N.Normal] (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥) :
    IsDirectProduct {J | J ∈ lcalOf Q ∧ J ≤ N} N ∧
      IsDirectProduct {J | J ∈ lcalOf Q ∧ J ≤ Subgroup.centralizer (N : Set Q)}
        (Subgroup.centralizer (N : Set Q)) := by
  set C : Subgroup Q := Subgroup.centralizer (N : Set Q) with hCdef
  set M₁ : Subgroup Q := sSup {J | J ∈ lcalOf Q ∧ J ≤ N} with hM₁
  set M₂ : Subgroup Q := sSup {J | J ∈ lcalOf Q ∧ J ≤ C} with hM₂
  have hM₁N : M₁ ≤ N := sSup_le fun J hJ => hJ.2
  have hM₂C : M₂ ≤ C := sSup_le fun J hJ => hJ.2
  have hn₁ : M₁.Normal := Subgroup.sSup_normal _ fun J hJ => normal_of_mem_lcalOf hDP hJ.1
  have hn₂ : M₂.Normal := Subgroup.sSup_normal _ fun J hJ => normal_of_mem_lcalOf hDP hJ.1
  have htop : M₁ ⊔ M₂ = ⊤ := by
    rw [eq_top_iff, ← hDP.sSup_eq]
    refine sSup_le fun J hJ => ?_
    rcases le_or_le_centralizer hDP N hJ with h | h
    · exact le_sup_of_le_left (le_sSup ⟨hJ, h⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hJ, h⟩)
  have hN₁ : M₁ = N := by
    refine le_antisymm hM₁N fun x hx => ?_
    obtain ⟨m₁, hm₁, m₂, hm₂, hmx⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (htop ▸ Subgroup.mem_top x)
    have hm₂N : m₂ ∈ N := by
      have : m₂ = m₁⁻¹ * x := by rw [← hmx]; group
      rw [this]
      exact N.mul_mem (N.inv_mem (hM₁N hm₁)) hx
    have : m₂ ∈ N ⊓ C := Subgroup.mem_inf.mpr ⟨hm₂N, hM₂C hm₂⟩
    rw [h1, Subgroup.mem_bot] at this
    rw [this, mul_one] at hmx
    exact hmx ▸ hm₁
  have hC₂ : M₂ = C := by
    refine le_antisymm hM₂C fun x hx => ?_
    obtain ⟨m₁, hm₁, m₂, hm₂, hmx⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (htop ▸ Subgroup.mem_top x)
    have hm₁C : m₁ ∈ C := by
      have : m₁ = x * m₂⁻¹ := by rw [← hmx]; group
      rw [this]
      exact C.mul_mem hx (C.inv_mem (hM₂C hm₂))
    have : m₁ ∈ N ⊓ C := Subgroup.mem_inf.mpr ⟨hM₁N hm₁, hm₁C⟩
    rw [h1, Subgroup.mem_bot] at this
    rw [this, one_mul] at hmx
    exact hmx ▸ hm₂
  exact ⟨isDirectProduct_of_subset hDP (fun J hJ => hJ.1) hN₁,
    isDirectProduct_of_subset hDP (fun J hJ => hJ.1) hC₂⟩

theorem permDeg_le_finsum [Finite Q] {S : Set (Subgroup Q)} {K : Subgroup Q}
    (hK : IsDirectProduct S K) : permDeg ↥K ≤ ∑ᶠ J ∈ S, permDeg ↥J := by
  classical
  have hSfin : S.Finite := Set.toFinite S
  have : Fintype S := hSfin.fintype
  have hle : permDeg (∀ J : S, ↥(J : Subgroup Q)) ≤ ∑ J : S, permDeg ↥(J : Subgroup Q) :=
    permDeg_pi_le _
  rw [← finsum_subtype_eq_finsum_cond (f := fun J : Subgroup Q => permDeg ↥J) (fun J => J ∈ S),
    finsum_eq_sum_of_fintype]
  exact (permDeg_congr hK.equiv).symm.le.trans hle

theorem permDeg_eq_add [Finite Q] (hQ : IsSS Q) (hDP : IsDirectProduct (lcalOf Q) (⊤ : Subgroup Q))
    (hL : permDeg Q = ∑ᶠ J ∈ lcalOf Q, permDeg ↥J) (N : Subgroup Q) [N.Normal] :
    permDeg Q = permDeg ↥N + permDeg ↥(Subgroup.centralizer (N : Set Q)) := by
  obtain ⟨h1, h2⟩ := hQ N inferInstance
  obtain ⟨hN, hC⟩ := isDirectProduct_lcalOf_le hDP N h1
  have hle := permDeg_le_add N h1 h2
  have hN' := permDeg_le_finsum hN
  have hC' := permDeg_le_finsum hC
  have hunion : lcalOf Q = {J | J ∈ lcalOf Q ∧ J ≤ N} ∪
      {J | J ∈ lcalOf Q ∧ J ≤ Subgroup.centralizer (N : Set Q)} := by
    ext J
    constructor
    · intro hJ
      rcases le_or_le_centralizer hDP N hJ with h | h
      · exact Or.inl ⟨hJ, h⟩
      · exact Or.inr ⟨hJ, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint {J | J ∈ lcalOf Q ∧ J ≤ N}
      {J | J ∈ lcalOf Q ∧ J ≤ Subgroup.centralizer (N : Set Q)} := by
    rw [Set.disjoint_left]
    rintro J ⟨hJ, hJN⟩ ⟨-, hJC⟩
    have hJbot : J ≤ ⊥ := h1 ▸ le_inf hJN hJC
    have hnt : Nontrivial J := (hJ.2.1).toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot J).mp hnt (le_bot_iff.mp hJbot)
  have hsum : ∑ᶠ J ∈ lcalOf Q, permDeg ↥J = ∑ᶠ J ∈ {J | J ∈ lcalOf Q ∧ J ≤ N}, permDeg ↥J +
      ∑ᶠ J ∈ {J | J ∈ lcalOf Q ∧ J ≤ Subgroup.centralizer (N : Set Q)}, permDeg ↥J := by
    conv_lhs => rw [hunion]
    exact finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)
  omega

end Components

section Quotients

variable {H : Type*} [Group H] [Finite H]

theorem deg_add_of_oStar (hK : oStar H = ⊤) (N : Subgroup H) [N.Normal] :
    deg H = deg N + deg (H ⧸ N) := by
  set R : Subgroup H := CFSG.solvableRadical H with hR
  set π : H →* H ⧸ R := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hkerπ : π.ker = R := QuotientGroup.ker_mk' R
  have hRsol : Group.IsSolvable R := isSolvable_solvableRadical
  have hQ : IsSS (H ⧸ R) := isSS_of_oStar_eq_top hK
  have hsolQ : CFSG.solvableRadical (H ⧸ R) = ⊥ := solvableRadical_quotient
  have hDP : IsDirectProduct (lcalOf (H ⧸ R)) (⊤ : Subgroup (H ⧸ R)) := by
    have := isDirectProduct_lcalOf_layer hsolQ
    rwa [layer_quotient_eq_top hK] at this
  have hdegH : deg H = permDeg (H ⧸ R) := rfl
  have hL : permDeg (H ⧸ R) = ∑ᶠ J ∈ lcalOf (H ⧸ R), permDeg ↥J := by
    rw [← hdegH, deg_eq_sum_components hK]
    refine finsum_congr fun J => finsum_congr fun hJ => ?_
    have := hJ.2.1
    exact deg_eq_permDeg_of_isSimpleGroup J hJ.2.2
  set Nb : Subgroup (H ⧸ R) := N.map π with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hadd := permDeg_eq_add hQ hDP hL Nb
  obtain ⟨h1, h2⟩ := hQ Nb hNbn
  have hdegN : deg N = permDeg Nb := by
    have hNbSS : IsSS ↥Nb := hQ.subgroup_of_normal Nb
    have : Group.IsSolvable (CFSG.solvableRadical ↥Nb) := isSolvable_solvableRadical
    refine deg_eq_permDeg_of_surjective (π.subgroupMap N) (π.subgroupMap_surjective N) ?_ ?_
    · rw [ker_subgroupMap, hkerπ]
      exact isSolvable_subgroupOf R N
    · exact hNbSS.eq_bot_of_normal_solvable _
  have hdegQ : deg (H ⧸ N) = permDeg ↥(Subgroup.centralizer (Nb : Set (H ⧸ R))) := by
    set C : Subgroup (H ⧸ R) := Subgroup.centralizer (Nb : Set (H ⧸ R)) with hCdef
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hCSS : IsSS ↥C := hQ.subgroup_of_normal C
    have hker := ker_projC Nb h1 h2
    set pC : H ⧸ R →* ↥C := projC Nb h1 h2 with hpC
    have hψN : N ≤ (pC.comp π).ker := by
      intro n hn
      rw [MonoidHom.mem_ker]
      have : π n ∈ pC.ker := hker.symm ▸ Subgroup.mem_map_of_mem π hn
      exact this
    set φ : H ⧸ N →* ↥C := QuotientGroup.lift N (pC.comp π) hψN with hφ
    have hφs : Function.Surjective φ := by
      intro c
      obtain ⟨q, hq⟩ := projC_surjective Nb h1 h2 c
      obtain ⟨h, rfl⟩ := hπs q
      exact ⟨QuotientGroup.mk h, hq⟩
    have hφk : Group.IsSolvable φ.ker := by
      have hsolR' : Group.IsSolvable (R.map (QuotientGroup.mk' N)) :=
        Group.isSolvable_of_surjective ((QuotientGroup.mk' N).subgroupMap_surjective R)
      have hle : φ.ker ≤ R.map (QuotientGroup.mk' N) := by
        intro y hy
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
        have hψ : pC (π h) = 1 := hy
        have hπh : π h ∈ Nb := hker ▸ hψ
        obtain ⟨n, hn, hnh⟩ := hπh
        have hr : n⁻¹ * h ∈ R := by
          rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hnh, inv_mul_cancel]
        refine ⟨n⁻¹ * h, hr, ?_⟩
        show (QuotientGroup.mk (n⁻¹ * h) : H ⧸ N) = QuotientGroup.mk h
        rw [QuotientGroup.eq]
        have := Subgroup.Normal.conj_mem inferInstance n hn h⁻¹
        simpa [mul_assoc] using this
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have : Group.IsSolvable (CFSG.solvableRadical ↥C) := isSolvable_solvableRadical
    exact deg_eq_permDeg_of_surjective φ hφs hφk (hCSS.eq_bot_of_normal_solvable _)
  rw [hdegH, hadd, hdegN, hdegQ]

end Quotients

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
