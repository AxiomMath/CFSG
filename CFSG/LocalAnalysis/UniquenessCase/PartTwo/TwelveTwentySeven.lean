module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_of_mem_normalizer {N : Subgroup G} {g n : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N) : g * n * g⁻¹ ∈ N :=
  ((Subgroup.mem_normalizer_iff.mp hg) n).mp hn

private theorem conj_mem_centralizer {N : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G))
    (hc : c ∈ Subgroup.centralizer (N : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := ((Subgroup.mem_normalizer_iff''.mp hg) n).mp hn
  calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [hc _ hn']
    _ = (g * c * g⁻¹) * n := by group

private theorem normalizer_le_normalizer_centralizer (N : Subgroup G) :
    Subgroup.normalizer (N : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (N : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_centralizer hg
  · intro hc
    have := conj_mem_centralizer (N := N) (inv_mem hg) hc
    have h2 : g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c := by group
    rwa [h2] at this

private theorem exists_nontrivial_fixed_point_of_isPGroup
    {P Q : Type*} [Group P] [Finite P] [MulAction P Q] [Group Q] [Finite Q]
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hQn : Nontrivial Q)
    (a : Q) (ha : a ∈ MulAction.fixedPoints P Q) :
    ∃ q : Q, q ≠ a ∧ ∀ p : P, p • q = q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hnpos, hncard⟩ := hQ.nontrivial_iff_card.mp hQn
  have hdvd : 2 ∣ Nat.card Q := by
    rw [hncard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  obtain ⟨b, hb, hba⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hdvd ha
  exact ⟨b, fun h => hba h.symm, fun p => (MulAction.mem_fixedPoints.mp hb) p⟩

private theorem eq_bot_or_eq_of_closure_conj_eq {M V₀ V : Subgroup G}
    (hgen : ∀ v ∈ V, v ∉ V₀ →
      Subgroup.closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} = V)
    {U : Subgroup G} (hUV : U ≤ V) (hV₀U : V₀ ≤ U)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) : U = V₀ ∨ U = V := by
  by_cases hEq : U = V₀
  · exact Or.inl hEq
  · refine Or.inr ?_
    have hnot : ¬ U ≤ V₀ := fun hle => hEq (le_antisymm hle hV₀U)
    obtain ⟨u, huU, huV₀⟩ :=
      Set.not_subset.mp (show ¬ (U : Set G) ⊆ (V₀ : Set G) from hnot)
    have huV : u ∈ V := hUV huU
    have hcl := hgen u huV huV₀
    have hle : Subgroup.closure {x : G | ∃ m ∈ M, x = m * u * m⁻¹} ≤ U := by
      rw [Subgroup.closure_le]
      rintro x ⟨m, hmM, rfl⟩
      exact conj_mem_of_mem_normalizer (hMU hmM) huU
    rw [hcl] at hle
    exact le_antisymm hUV hle

private noncomputable def quotMap {X : Type*} [Group X] (H : Subgroup X) [H.Normal]
    (σ : MulAut X) (hσ : H ≤ H.comap σ.toMonoidHom) : X ⧸ H →* X ⧸ H :=
  QuotientGroup.map H H σ.toMonoidHom hσ

private theorem map_eq_self_of_le_comap {X : Type*} [Group X] (H : Subgroup X) [Finite H]
    (σ : MulAut X) (hσ : H ≤ H.comap σ.toMonoidHom) : H.map σ.toMonoidHom = H := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rwa [Subgroup.map_le_iff_le_comap]
  · rw [Subgroup.card_map_of_injective σ.injective]

private theorem quotMap_injective {X : Type*} [Group X] [Finite X] (H : Subgroup X) [H.Normal]
    (σ : MulAut X) (hσ : H ≤ H.comap σ.toMonoidHom) :
    Function.Injective (quotMap H σ hσ) := by
  intro a b hab
  revert hab
  refine QuotientGroup.induction_on a fun x => ?_
  refine QuotientGroup.induction_on b fun y => ?_
  intro hab
  rw [show quotMap H σ hσ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) from
        by simp [quotMap, QuotientGroup.map_mk],
      show quotMap H σ hσ (QuotientGroup.mk y) = QuotientGroup.mk (σ y) from
        by simp [quotMap, QuotientGroup.map_mk],
      QuotientGroup.eq_iff_div_mem] at hab
  rw [QuotientGroup.eq_iff_div_mem]
  have hmap : H.map σ.toMonoidHom = H := map_eq_self_of_le_comap H σ hσ
  have hσrev : H ≤ H.comap σ.symm.toMonoidHom := by
    intro h hh
    rw [Subgroup.mem_comap]
    have hh' : h ∈ H.map σ.toMonoidHom := hmap.symm ▸ hh
    obtain ⟨y, hyH, hy⟩ := Subgroup.mem_map.mp hh'
    rw [← hy]
    simpa using hyH
  have hσxy : σ (x / y) ∈ H := by
    simpa only [map_div] using hab
  have := hσrev hσxy
  simpa using this

private noncomputable def quotAut {X : Type*} [Group X] [Finite X] (H : Subgroup X) [H.Normal]
    (σ : MulAut X) (hσ : H ≤ H.comap σ.toMonoidHom) : MulAut (X ⧸ H) :=
  MulEquiv.ofBijective (quotMap H σ hσ)
    ⟨quotMap_injective H σ hσ, (Finite.injective_iff_surjective).mp (quotMap_injective H σ hσ)⟩

private theorem commMap_mul {V : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {k x y : G} (hk : k ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ V) (hy : y ∈ V) :
    k * (x * y) * k⁻¹ * (x * y)⁻¹ =
      (k * x * k⁻¹ * x⁻¹) * (k * y * k⁻¹ * y⁻¹) := by
  have hky : k * y * k⁻¹ ∈ V := conj_mem_of_mem_normalizer hk hy
  have hxinv : x⁻¹ ∈ V := V.inv_mem hx
  have hyinv : y⁻¹ ∈ V := V.inv_mem hy
  calc k * (x * y) * k⁻¹ * (x * y)⁻¹
      = (k * x * k⁻¹) * (k * y * k⁻¹) * (y⁻¹ * x⁻¹) := by group
    _ = (k * x * k⁻¹) * (k * y * k⁻¹) * (x⁻¹ * y⁻¹) := by
          rw [hcomm y⁻¹ hyinv x⁻¹ hxinv]
    _ = (k * x * k⁻¹) * (k * y * k⁻¹ * x⁻¹) * y⁻¹ := by group
    _ = (k * x * k⁻¹) * (x⁻¹ * (k * y * k⁻¹)) * y⁻¹ := by
          rw [hcomm (k * y * k⁻¹) hky x⁻¹ hxinv]
    _ = (k * x * k⁻¹ * x⁻¹) * (k * y * k⁻¹ * y⁻¹) := by group

private theorem commMap_inv {V : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {k x : G} (hk : k ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ V) :
    k * x⁻¹ * k⁻¹ * x = (k * x * k⁻¹ * x⁻¹)⁻¹ := by
  have hkx : k * x * k⁻¹ ∈ V := conj_mem_of_mem_normalizer hk hx
  calc k * x⁻¹ * k⁻¹ * x = (k * x * k⁻¹)⁻¹ * x := by group
    _ = x * (k * x * k⁻¹)⁻¹ := hcomm (k * x * k⁻¹)⁻¹ (V.inv_mem hkx) x hx
    _ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by group

private theorem mul_commMap_eq {V : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {q₁ q₂ v : G} (hc₁ : q₁ * v * q₁⁻¹ * v⁻¹ ∈ V)
    (hc₂V : q₂ * v * q₂⁻¹ * v⁻¹ ∈ V)
    (hq₁c₂ : q₁ * (q₂ * v * q₂⁻¹ * v⁻¹) * q₁⁻¹ = q₂ * v * q₂⁻¹ * v⁻¹) :
    (q₁ * q₂) * v * (q₁ * q₂)⁻¹ * v⁻¹ =
      (q₁ * v * q₁⁻¹ * v⁻¹) * (q₂ * v * q₂⁻¹ * v⁻¹) := by
  have hsub : q₂ * v * q₂⁻¹ = (q₂ * v * q₂⁻¹ * v⁻¹) * v := by group
  calc (q₁ * q₂) * v * (q₁ * q₂)⁻¹ * v⁻¹
      = q₁ * (q₂ * v * q₂⁻¹) * q₁⁻¹ * v⁻¹ := by group
    _ = q₁ * ((q₂ * v * q₂⁻¹ * v⁻¹) * v) * q₁⁻¹ * v⁻¹ := by
          conv_lhs => rw [hsub]
    _ = q₁ * (q₂ * v * q₂⁻¹ * v⁻¹) * q₁⁻¹ * (q₁ * v * q₁⁻¹ * v⁻¹) := by group
    _ = (q₂ * v * q₂⁻¹ * v⁻¹) * (q₁ * v * q₁⁻¹ * v⁻¹) := by rw [hq₁c₂]
    _ = (q₁ * v * q₁⁻¹ * v⁻¹) * (q₂ * v * q₂⁻¹ * v⁻¹) :=
          (hcomm (q₁ * v * q₁⁻¹ * v⁻¹) hc₁ (q₂ * v * q₂⁻¹ * v⁻¹) hc₂V).symm

private theorem conj_commMap_eq {V : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {x q v : G} (hdV : x * v * x⁻¹ * v⁻¹ ∈ V)
    (hc'V : (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ ∈ V)
    (hq'd : (x * q * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * (x * q * x⁻¹)⁻¹ =
      x * v * x⁻¹ * v⁻¹) :
    x * (q * v * q⁻¹ * v⁻¹) * x⁻¹ =
      (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ := by
  have hdv : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
  calc x * (q * v * q⁻¹ * v⁻¹) * x⁻¹
      = (x * q * x⁻¹) * (x * v * x⁻¹) * (x * q * x⁻¹)⁻¹ * (x * v * x⁻¹)⁻¹ := by group
    _ = (x * q * x⁻¹) * ((x * v * x⁻¹ * v⁻¹) * v) * (x * q * x⁻¹)⁻¹ *
          ((x * v * x⁻¹ * v⁻¹) * v)⁻¹ := by conv_lhs => rw [hdv]
    _ = (x * q * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * (x * q * x⁻¹)⁻¹ *
          ((x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹) *
          (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
    _ = (x * v * x⁻¹ * v⁻¹) * ((x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹) *
          (x * v * x⁻¹ * v⁻¹)⁻¹ := by rw [hq'd]
    _ = (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ := by
          rw [hcomm (x * v * x⁻¹ * v⁻¹) hdV _ hc'V]
          group

theorem exists_conj_eq_mul_of_inCalV0 {M V₀ V X : Subgroup G} (h : InCalV0 M V₀ V)
    (hX : ∀ m : G, m ∈ X ↔ m ∈ M ∧ CentralizesMod V₀ V m)
    (hirr : ∀ U : Subgroup G, U ≤ V₀ → X ≤ normalizer (U : Set G) → U = ⊥ ∨ U = V₀)
    {v : G} (hv : v ∈ V) (hvV₀ : v ∉ V₀) {d : G} (hd : d ∈ V₀) :
    ∃ x ∈ X ⊓ centralizer (V₀ : Set G), x * v * x⁻¹ = v * d := by
  obtain ⟨hV₀, hV, hV₀leV, -, -, hgen, hnot2red⟩ := h
  obtain ⟨hV₀ne, -, hMNV₀, hV₀E⟩ := hV₀
  obtain ⟨-, hVM, hMNV, hVE⟩ := hV
  haveI : IsMulCommutative V := hVE.1
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hVE.comm ha hb
  have hV_le_cent : V ≤ Subgroup.centralizer (V : Set G) := Subgroup.le_centralizer V
  have hXM : X ≤ M := fun x hx => ((hX x).mp hx).1
  have hXNV₀ : X ≤ Subgroup.normalizer (V₀ : Set G) := hXM.trans hMNV₀
  have hnotred := hnot2red
  rw [TwoReduced] at hnotred
  push Not at hnotred
  obtain ⟨K, hKM, hMNK, hCK, hKidx, hKnotcent⟩ := hnotred
  obtain ⟨n, hn⟩ := hKidx
  have hKNV : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMNV
  have hKNV₀ : K ≤ Subgroup.normalizer (V₀ : Set G) := hKM.trans hMNV₀
  have hKNC : K ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    hKNV.trans (normalizer_le_normalizer_centralizer V)
  have hVK : V ≤ K := (le_inf hVM hV_le_cent).trans hCK
  let Ck : Subgroup K := (Subgroup.centralizer (V : Set G)).subgroupOf K
  haveI : Ck.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKNC
  let P : Type _ := K ⧸ Ck
  have hPcard : Nat.card P = 2 ^ n := by
    show Nat.card (K ⧸ Ck) = 2 ^ n
    rw [← Subgroup.index_eq_card]
    exact hn
  have hPp : IsPGroup 2 P := IsPGroup.of_card hPcard
  let conjAutV : K →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hKNV)
  let conjAutV₀ : K →* MulAut V₀ :=
    V₀.normalizerMonoidHom.comp (Subgroup.inclusion hKNV₀)
  have normalizerMonoidHom_apply_coe {N : Subgroup G}
      (g : Subgroup.normalizer (N : Set G)) (x : N) :
      ((N.normalizerMonoidHom g x : N) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl
  have hCk_kerV : Ck ≤ conjAutV.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hcomm' := Subgroup.mem_centralizer_iff.mp hkcent (y : G) y.2
    show ((conjAutV k) y : G) = (y : G)
    simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    rw [← hcomm']
    group
  have hCk_kerV₀ : Ck ≤ conjAutV₀.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hyV : (y : G) ∈ V := hV₀leV y.2
    have hcomm' := Subgroup.mem_centralizer_iff.mp hkcent (y : G) hyV
    show ((conjAutV₀ k) y : G) = (y : G)
    simp only [conjAutV₀, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    rw [← hcomm']
    group
  let V0V : Subgroup V := V₀.subgroupOf V
  haveI : V0V.Normal := inferInstance
  let Q : Type _ := V ⧸ V0V
  have hpres : ∀ k : K, V0V ≤ V0V.comap (conjAutV k).toMonoidHom := by
    intro k x hx
    rw [Subgroup.mem_comap]
    have hxV₀ : (x : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp hx
    show ((conjAutV k) x : V) ∈ V0V
    rw [Subgroup.mem_subgroupOf]
    simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    exact conj_mem_of_mem_normalizer (hKNV₀ k.2) hxV₀
  let conjQuotAut : K →* MulAut Q :=
    { toFun := fun k => quotAut V0V (conjAutV k) (hpres k)
      map_one' := by
        apply MulEquiv.ext
        intro q
        refine QuotientGroup.induction_on q fun x => ?_
        simp [quotAut, quotMap, QuotientGroup.map_mk]
      map_mul' := by
        intro k₁ k₂
        apply MulEquiv.ext
        intro q
        refine QuotientGroup.induction_on q fun x => ?_
        simp [quotAut, quotMap, QuotientGroup.map_mk, MulAut.mul_apply] }
  have hCk_kerQ : Ck ≤ conjQuotAut.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hconjx : ∀ y : V, (conjAutV k) y = y := by
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hkcent (y : G) y.2
      show ((conjAutV k) y : G) = (y : G)
      simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
        Subgroup.coe_inclusion]
      rw [← this]
      group
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    show conjQuotAut k (QuotientGroup.mk x) = QuotientGroup.mk x
    change quotAut V0V (conjAutV k) (hpres k) (QuotientGroup.mk x) = QuotientGroup.mk x
    have h1 : quotAut V0V (conjAutV k) (hpres k) (QuotientGroup.mk x) =
        QuotientGroup.mk ((conjAutV k) x) := by
      simp [quotAut, quotMap, QuotientGroup.map_mk]
    rw [h1, hconjx x]
  have hQp : IsPGroup 2 Q := hVE.isPGroup.to_quotient V0V
  have hQnontriv : Nontrivial Q := by
    refine ⟨(QuotientGroup.mk (⟨v, hv⟩ : V) : Q), 1, ?_⟩
    intro hcontr
    rw [QuotientGroup.eq_one_iff] at hcontr
    exact hvV₀ (Subgroup.mem_subgroupOf.mp hcontr)
  let phiQ : P →* MulAut Q := QuotientGroup.lift Ck conjQuotAut hCk_kerQ
  letI : MulAction P Q := MulAction.compHom Q phiQ
  have h1fixQ : (1 : Q) ∈ MulAction.fixedPoints P Q := by
    rw [MulAction.mem_fixedPoints]
    intro p
    show phiQ p 1 = 1
    exact map_one (phiQ p)
  obtain ⟨q, hqne, hqfix⟩ :=
    exists_nontrivial_fixed_point_of_isPGroup hPp hQp hQnontriv 1 h1fixQ
  obtain ⟨w, hwq⟩ := Quotient.exists_rep q
  have hwV : (w : G) ∈ V := w.2
  have hwV₀ : (w : G) ∉ V₀ := by
    intro hw0
    exact hqne (by rw [← hwq, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr hw0)
  have hwfix : ∀ k' ∈ K, k' * (w : G) * k'⁻¹ * (w : G)⁻¹ ∈ V₀ := by
    intro k' hk'
    have h := hqfix (QuotientGroup.mk (⟨k', hk'⟩ : K))
    rw [← hwq] at h
    change phiQ (QuotientGroup.mk (⟨k', hk'⟩ : K)) (QuotientGroup.mk w) =
      QuotientGroup.mk w at h
    rw [show phiQ (QuotientGroup.mk (⟨k', hk'⟩ : K)) = conjQuotAut ⟨k', hk'⟩ from
      QuotientGroup.lift_mk _ _ _] at h
    change quotAut V0V (conjAutV ⟨k', hk'⟩) (hpres ⟨k', hk'⟩) (QuotientGroup.mk w) =
      QuotientGroup.mk w at h
    have h1 : quotAut V0V (conjAutV ⟨k', hk'⟩) (hpres ⟨k', hk'⟩) (QuotientGroup.mk w) =
        QuotientGroup.mk ((conjAutV ⟨k', hk'⟩) w) := by
      simp [quotAut, quotMap, QuotientGroup.map_mk]
    rw [h1, QuotientGroup.eq_iff_div_mem] at h
    have hmem : (((conjAutV ⟨k', hk'⟩) w / w : V) : G) ∈ V₀ :=
      Subgroup.mem_subgroupOf.mp h
    have hcoeeq : (((conjAutV ⟨k', hk'⟩) w / w : V) : G) =
        k' * (w : G) * k'⁻¹ * (w : G)⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv,
        conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe, Subgroup.coe_inclusion]
    rwa [hcoeeq] at hmem
  have hKleX : K ≤ X := by
    intro k hk
    rw [hX]
    refine ⟨hKM hk, ?_⟩
    intro u hu
    let Sk : Subgroup G :=
      { carrier := {x : G | x ∈ V ∧ k * x * k⁻¹ * x⁻¹ ∈ V₀}
        one_mem' := by
          refine ⟨V.one_mem, ?_⟩
          simpa using V₀.one_mem
        mul_mem' := by
          rintro x y ⟨hxV, hx0⟩ ⟨hyV, hy0⟩
          refine ⟨V.mul_mem hxV hyV, ?_⟩
          rw [commMap_mul hcomm (hKNV hk) hxV hyV]
          exact V₀.mul_mem hx0 hy0
        inv_mem' := by
          rintro x ⟨hxV, hx0⟩
          refine ⟨V.inv_mem hxV, ?_⟩
          have h := commMap_inv hcomm (hKNV hk) hxV
          rw [show (x⁻¹)⁻¹ = x from inv_inv x, h]
          exact V₀.inv_mem hx0 }
    have hSkclosure : Subgroup.closure {x : G | ∃ m ∈ M, x = m * w * m⁻¹} ≤ Sk := by
      rw [Subgroup.closure_le]
      rintro x ⟨m, hmM, rfl⟩
      refine ⟨conj_mem_of_mem_normalizer (hMNV hmM) hwV, ?_⟩
      have hk' : m⁻¹ * k * m ∈ K :=
        ((Subgroup.mem_normalizer_iff''.mp (hMNK hmM)) k).mp hk
      have hkw : (m⁻¹ * k * m) * (w : G) * (m⁻¹ * k * m)⁻¹ * (w : G)⁻¹ ∈ V₀ :=
        hwfix _ hk'
      have heq : k * (m * (w : G) * m⁻¹) * k⁻¹ * (m * (w : G) * m⁻¹)⁻¹ =
          m * ((m⁻¹ * k * m) * (w : G) * (m⁻¹ * k * m)⁻¹ * (w : G)⁻¹) * m⁻¹ := by group
      rw [heq]
      exact conj_mem_of_mem_normalizer (hMNV₀ hmM) hkw
    have hVleSk : V ≤ Sk := by
      rw [← hgen w hwV hwV₀]
      exact hSkclosure
    exact (hVleSk hu).2
  have hKleV₀ : K ≤ Subgroup.centralizer (V₀ : Set G) := by
    let phiV₀ : P →* MulAut V₀ := QuotientGroup.lift Ck conjAutV₀ hCk_kerV₀
    letI : MulAction P V₀ := MulAction.compHom V₀ phiV₀
    have hV₀nontriv : Nontrivial V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).mpr hV₀ne
    have h1fixV₀ : (1 : V₀) ∈ MulAction.fixedPoints P V₀ := by
      rw [MulAction.mem_fixedPoints]
      intro p
      show phiV₀ p 1 = 1
      exact map_one (phiV₀ p)
    obtain ⟨z, hzne, hzfix⟩ :=
      exists_nontrivial_fixed_point_of_isPGroup hPp hV₀E.isPGroup hV₀nontriv 1 h1fixV₀
    have hzC : (z : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := hzfix (QuotientGroup.mk (⟨k, hk⟩ : K))
      change phiV₀ (QuotientGroup.mk (⟨k, hk⟩ : K)) z = z at h
      rw [show phiV₀ (QuotientGroup.mk (⟨k, hk⟩ : K)) = conjAutV₀ ⟨k, hk⟩ from
        QuotientGroup.lift_mk _ _ _] at h
      have h2 : k * (z : G) * k⁻¹ = (z : G) := by
        have := congrArg (fun y : V₀ => (y : G)) h
        simpa only [conjAutV₀, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
          Subgroup.coe_inclusion] using this
      calc k * (z : G) = k * (z : G) * k⁻¹ * k := by group
        _ = (z : G) * k := by rw [h2]
    let Zsub : Subgroup G := V₀ ⊓ Subgroup.centralizer (K : Set G)
    have hZsub_le : Zsub ≤ V₀ := inf_le_left
    have hZsub_ne : Zsub ≠ ⊥ := by
      intro hbot
      have hzZ : (z : G) ∈ Zsub := ⟨z.2, hzC⟩
      rw [hbot] at hzZ
      exact hzne (Subtype.ext (Subgroup.mem_bot.mp hzZ))
    have hXZsub : X ≤ Subgroup.normalizer (Zsub : Set G) := by
      have hXNK : X ≤ Subgroup.normalizer (K : Set G) := hXM.trans hMNK
      have hXNC : X ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
        hXNK.trans (normalizer_le_normalizer_centralizer K)
      exact (le_inf hXNV₀ hXNC).trans inf_normalizer_le_normalizer_inf
    rcases hirr Zsub hZsub_le hXZsub with hbot | hV₀eq
    · exact absurd hbot hZsub_ne
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzZ : z ∈ Zsub := hV₀eq ▸ hz
      exact ((Subgroup.mem_centralizer_iff.mp hzZ.2) k hk).symm
  have hV₀K : V₀ ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hKleV₀
  have hC_V_K : V ⊓ Subgroup.centralizer (K : Set G) = V₀ := by
    have hMNV'' : M ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
      hMNK.trans (normalizer_le_normalizer_centralizer K)
    have hMNU : M ≤ Subgroup.normalizer (V ⊓ Subgroup.centralizer (K : Set G) : Set G) :=
      (le_inf hMNV hMNV'').trans inf_normalizer_le_normalizer_inf
    rcases eq_bot_or_eq_of_closure_conj_eq (M := M) (V₀ := V₀) (V := V) hgen
      (U := V ⊓ Subgroup.centralizer (K : Set G)) inf_le_left (le_inf hV₀leV hV₀K) hMNU with h | h
    · exact h
    · exfalso
      apply hKnotcent
      rw [Subgroup.le_centralizer_iff]
      intro x hx
      have hx' : x ∈ V ⊓ Subgroup.centralizer (K : Set G) := by rw [h]; exact hx
      exact hx'.2
  have hv_notC : (v : G) ∉ Subgroup.centralizer (K : Set G) := by
    intro hvc
    exact hvV₀ (hC_V_K ▸ (show v ∈ V ⊓ Subgroup.centralizer (K : Set G) from ⟨hv, hvc⟩))
  rw [Subgroup.mem_centralizer_iff] at hv_notC
  push Not at hv_notC
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := hv_notC
  have hk₀comm : k₀ * v * k₀⁻¹ * v⁻¹ ≠ 1 := by
    intro h1
    apply hk₀ne
    have hconj : k₀ * v * k₀⁻¹ = v := by
      calc k₀ * v * k₀⁻¹ = (k₀ * v * k₀⁻¹ * v⁻¹) * v := by group
        _ = 1 * v := by rw [h1]
        _ = v := by group
    calc k₀ * v = k₀ * v * k₀⁻¹ * k₀ := by group
      _ = v * k₀ := by rw [hconj]
  let φ : K →* V₀ :=
    { toFun := fun q => ⟨q * v * q⁻¹ * v⁻¹, ((hX q).mp (hKleX q.2)).2 v hv⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro q₁ q₂
        apply Subtype.ext
        refine mul_commMap_eq hcomm ?_ ?_ ?_
        · exact V.mul_mem (conj_mem_of_mem_normalizer (hKNV q₁.2) hv) (V.inv_mem hv)
        · exact V.mul_mem (conj_mem_of_mem_normalizer (hKNV q₂.2) hv) (V.inv_mem hv)
        · have hc₂ : (q₂ : G) * v * (q₂ : G)⁻¹ * v⁻¹ ∈ V₀ :=
            ((hX q₂).mp (hKleX q₂.2)).2 v hv
          have hcomm' : (q₂ : G) * v * (q₂ : G)⁻¹ * v⁻¹ * (q₁ : G) =
              (q₁ : G) * ((q₂ : G) * v * (q₂ : G)⁻¹ * v⁻¹) := by
            simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
              Subgroup.mem_centralizer_iff.mp (hKleV₀ q₁.2) (q₂ * v * q₂⁻¹ * v⁻¹) hc₂
          rw [← hcomm']
          group }
  let D : Subgroup G := φ.range.map V₀.subtype
  have hD_le : D ≤ V₀ := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hD_ne : D ≠ ⊥ := by
    intro hbot
    have hmem : φ ⟨k₀, hk₀K⟩ ∈ φ.range := ⟨⟨k₀, hk₀K⟩, rfl⟩
    have : k₀ * v * k₀⁻¹ * v⁻¹ ∈ D := ⟨_, hmem, rfl⟩
    rw [hbot] at this
    exact hk₀comm (Subgroup.mem_bot.mp this)
  have hforward : ∀ x ∈ X, ∀ y ∈ D, x * y * x⁻¹ ∈ D := by
    intro x hx y hy
    obtain ⟨y', hy'range, hy'eq⟩ := Subgroup.mem_map.mp hy
    obtain ⟨q, hqeq⟩ := MonoidHom.mem_range.mp hy'range
    rw [← hy'eq, ← hqeq]
    have hxqK : x * q * x⁻¹ ∈ K :=
      ((Subgroup.mem_normalizer_iff.mp (hMNK (hXM hx))) q).mp q.2
    have hd' : x * v * x⁻¹ * v⁻¹ ∈ V₀ := ((hX x).mp hx).2 v hv
    have hd'V : x * v * x⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem (conj_mem_of_mem_normalizer (hMNV (hXM hx)) hv) (V.inv_mem hv)
    have hq'd : (x * q * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * (x * q * x⁻¹)⁻¹ =
        x * v * x⁻¹ * v⁻¹ := by
      have hmem := hKleV₀ hxqK
      rw [Subgroup.mem_centralizer_iff] at hmem
      rw [← hmem _ hd']
      group
    have hc'V : (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem (conj_mem_of_mem_normalizer (hKNV hxqK) hv) (V.inv_mem hv)
    have key := conj_commMap_eq hcomm hd'V hc'V hq'd
    refine Subgroup.mem_map.mpr
      ⟨φ ⟨x * q * x⁻¹, hxqK⟩, ⟨⟨x * q * x⁻¹, hxqK⟩, rfl⟩, ?_⟩
    show ((φ ⟨x * q * x⁻¹, hxqK⟩ : V₀) : G) = x * ((φ q : V₀) : G) * x⁻¹
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    exact key.symm
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward x hx y
    · intro hy
      have h := hforward x⁻¹ (X.inv_mem hx) (x * y * x⁻¹) hy
      have heq : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [heq] at h
  rcases hirr D hD_le hXD with hbot | hD_eq
  · exact absurd hbot hD_ne
  ·
    have hdD : d ∈ D := hD_eq ▸ hd
    obtain ⟨y', hy'range, hy'eq⟩ := Subgroup.mem_map.mp hdD
    obtain ⟨q, hqeq⟩ := MonoidHom.mem_range.mp hy'range
    refine ⟨(q : K), ⟨hKleX q.2, hKleV₀ q.2⟩, ?_⟩
    have hval : q * v * q⁻¹ * v⁻¹ = d := by
      have hthis := congrArg (fun z : V₀ => (z : G)) hqeq
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk] at hthis
      rw [hthis]
      exact hy'eq
    calc (q : K) * v * (q : K)⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
      _ = d * v := by rw [hval]
      _ = v * d := (hcomm v hv d (hV₀leV hd)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo