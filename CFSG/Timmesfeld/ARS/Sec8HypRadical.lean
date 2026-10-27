module

public import CFSG.Timmesfeld.ARS.Sec8HypQuot
public import CFSG.Timmesfeld.ARS.Sec8HypLine
public import CFSG.Timmesfeld.ARS.Sec8LeviAction

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Levi

section Comp

variable (h : Hyp G R) {A A₀ E₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hE₀ : E₀ ∈ leviSet R A A₀)
include h hA hAne hA₀ hE₀

theorem comp_subset_R : comp R A A₀ E₀ ⊆ R := fun _ hX =>
  (comp_subset h hA hAne hA₀ hE₀ hX).1.1

theorem exists_opposite_mem_comp {X : Subgroup G} (hX : X ∈ comp R A A₀ E₀) :
    ∃ Y ∈ comp R A A₀ E₀, Opposite X Y := by
  obtain ⟨Y, hY, hXY⟩ :=
    exists_opposite_mem_leviSet h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE₀ hX)
  exact ⟨Y, hX.tail ⟨comp_subset h hA hAne hA₀ hE₀ hX, hY, hXY⟩, hXY⟩

theorem conjSub_mem_comp_of_mem_gen {X : Subgroup G} (hX : X ∈ comp R A A₀ E₀) {g : G}
    (hg : g ∈ gen (comp R A A₀ E₀)) : conjSub X g ∈ comp R A A₀ E₀ :=
  conjSub_mem_comp h hA hAne hA₀ hE₀ hX (gen_mono (comp_subset h hA hAne hA₀ hE₀) hg)

theorem exists_conjSub_eq_of_mem_comp {X : Subgroup G} (hX : X ∈ comp R A A₀ E₀) :
    ∃ g ∈ gen (comp R A A₀ E₀), conjSub E₀ g = X := by
  have := h.finite
  obtain ⟨-, h2, -, -⟩ := component_decomposition h.root h.noIsolated (leviSet R A A₀)
    (fun _ hX => hX.1.1) (fun g hg _ hB => conjSub_mem_leviSet_of_mem_levi h.root hB hg)
    (fun _ hB _ hC hs => commutator_mem_leviSet h.root hA hA₀ hB hC hs)
  exact (h2 E₀ hE₀ (exists_opposite_mem_leviSet h hA hAne hA₀ hE₀) X hX).1

theorem commutator_mem_comp {X Y : Subgroup G} (hX : X ∈ comp R A A₀ E₀)
    (hY : Y ∈ comp R A A₀ E₀) (hs : Special R X Y) : ⁅X, Y⁆ ∈ comp R A A₀ E₀ :=
  mem_comp_of_le h hA hAne hA₀ hE₀ hs.1 (QD.commutator_le_of_le (le_gen hX) (le_gen hY))

end Comp

theorem eq_of_commuting_iff (h : Hyp G R) {A A₀ E₀ E E' : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hnd : ∃ X ∈ comp R A A₀ E₀, ∃ Y ∈ comp R A A₀ E₀, Special R X Y)
    (hE : E ∈ comp R A A₀ E₀) (hE' : E' ∈ comp R A A₀ E₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) : E = E' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set Δ := comp R A A₀ E₀ with hΔdef
  set V := gen Δ with hVdef
  have hΔΛ : Δ ⊆ leviSet R A A₀ := comp_subset h hA hAne hA₀ hE₀
  have hΔR : Δ ⊆ R := comp_subset_R h hA hAne hA₀ hE₀
  have hΔV : ∀ X ∈ Δ, X ≤ V := fun X hX => le_gen hX
  have hΔopp := fun X (hX : X ∈ Δ) => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX
  have hΔconj := fun X (hX : X ∈ Δ) g (hg : g ∈ V) =>
    conjSub_mem_comp_of_mem_gen h hA hAne hA₀ hE₀ hX hg
  have hΔtrans := fun X (hX : X ∈ Δ) => exists_conjSub_eq_of_mem_comp h hA hAne hA₀ hE₀ hX
  have hΔcl := fun X (hX : X ∈ Δ) Y (hY : Y ∈ Δ) (hs : Special R X Y) =>
    commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs
  have hVlevi : V ≤ levi R A A₀ := gen_mono hΔΛ
  have hR' := LeviQuot.isRootClass_quotClass hR hiso hΔR hΔV hΔopp
    (Relation.ReflTransGen.refl : E₀ ∈ Δ) hΔconj hΔtrans hΔcl rfl
  have hiso' := LeviQuot.noIsolated_quotClass hR hiso hΔR hΔV hΔopp (V := V)
  have hnd' := LeviQuot.isNondegenerate_quotClass hΔV hΔcl hnd (V := V)
  have hZ' := LeviQuot.center_eq_bot hΔV hΔtrans hΔcl rfl hnd
  have hinj := LeviQuot.injOn_quotMap hR hiso hΔR hΔV hΔopp (V := V)
  have hEΛ := hΔΛ hE
  have hE'Λ := hΔΛ hE'
  have hER := hΔR hE
  have hE'R := hΔR hE'
  by_contra hne
  have hcl' : quotMap V E' ∈ rootClosure (quotClass V Δ) (quotMap V E) :=
    (LeviQuot.mem_rootClosure_quotMap_iff hR hΔR hΔV hΔopp hΔcl hE hE').2 fun Z hZ =>
      hEE' Z (hΔΛ hZ)
  have hoppbar : ∀ {F : Subgroup G}, F ∈ Δ → Opposite E F →
      Opposite (quotMap V E) (quotMap V F) := fun hF hEF =>
    LeviQuot.opposite_quotMap (hΔV E hE) (hΔV _ hF) hEF fun e => hEF.1 (hinj hE hF e)
  obtain ⟨F₀, hF₀, hEF₀⟩ := hΔopp E hE
  obtain ⟨e', he', he'1⟩ := hR.exists_ne_one hE'R
  obtain ⟨E₁, hE₁, hE'E₁⟩ := hΔopp E' hE'
  have he'1' : QuotientGroup.mk' (Subgroup.center ↥V) ⟨e', hΔV E' hE' he'⟩ ≠ 1 := fun e =>
    he'1 (congrArg Subtype.val (LeviQuot.eq_one_of_mk_eq_one hE'E₁ (hΔV E₁ hE₁) he' e))
  obtain ⟨a, ha, -, hxN⟩ := exists_inv_mul_mem_rootNorm hR' hiso' ⟨E, hE, rfl⟩ ⟨F₀, hF₀, rfl⟩
    (hoppbar hF₀ hEF₀) hcl' (LeviQuot.mk_mem_quotMap he') he'1'
  obtain ⟨e, he, rfl⟩ := LeviQuot.exists_of_mem_quotMap ha
  set x : G := (e : G)⁻¹ * e' with hxdef
  have hxV : x ∈ V := V.mul_mem (V.inv_mem e.2) (hΔV E' hE' he')
  have hxbar : QuotientGroup.mk' (Subgroup.center ↥V) ⟨x, hxV⟩ =
      (QuotientGroup.mk' (Subgroup.center ↥V) e)⁻¹ *
        QuotientGroup.mk' (Subgroup.center ↥V) ⟨e', hΔV E' hE' he'⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  have hxrad : QuotientGroup.mk' (Subgroup.center ↥V) ⟨x, hxV⟩ ∈
      radPart (quotClass V Δ) (quotMap V E) := by
    rw [hxbar, ← rootNorm_eq_radPart hR' hiso' hnd' hZ' ⟨E, hE, rfl⟩
      ⟨⟨F₀, hF₀, rfl⟩, hoppbar hF₀ hEF₀⟩]
    exact hxN
  have hFx : ∀ F ∈ Δ, Opposite E F → ∀ X ∈ leviSet R A A₀,
      (Commuting F X ↔ Commuting (conjSub F x) X) := by
    intro F hF hEF X hX
    have hmem : QuotientGroup.mk' (Subgroup.center ↥V) ⟨x, hxV⟩ ∈
        rootNorm (quotClass V Δ) (quotMap V E) (quotMap V F) := by
      rw [rootNorm_eq_radPart hR' hiso' hnd' hZ' ⟨E, hE, rfl⟩ ⟨⟨F, hF, rfl⟩, hoppbar hF hEF⟩]
      exact hxrad
    have h1 := conjSub_mem_of_mem_stabSet (Subgroup.mem_inf.1 hmem).2
      (mem_rootClosure_self (⟨F, hF, rfl⟩ : quotMap V F ∈ quotClass V Δ))
    rw [← LeviQuot.quotMap_conjSub F hxV] at h1
    have hFxΔ : conjSub F x ∈ Δ := hΔconj F hF x hxV
    have h2 := (LeviQuot.mem_rootClosure_quotMap_iff hR hΔR hΔV hΔopp hΔcl hF hFxΔ).1 h1
    by_cases hXΔ : X ∈ Δ
    · exact h2 X hXΔ
    · have hc : ∀ {Y : Subgroup G}, Y ∈ Δ → Commuting Y X := fun hY =>
        commuting_of_notMem_comp h hA hAne hA₀ (hΔΛ hY) hX (by
          rw [comp_eq_of_mem hY]
          exact hXΔ)
      exact ⟨fun _ => hc hFxΔ, fun _ => hc hF⟩
  have hxlevi : x ∈ levi R A A₀ := hVlevi hxV
  have hxA₀ : ∀ b ∈ A₀, Commute x b := fun b hb =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hxlevi) b hb).symm
  have hxB : ∀ B ∈ lambdaStar R A A₀, ∀ b ∈ B, Commute x b := by
    intro B hB b hb
    have hBR : B ∈ R := hB.1.1.1
    by_cases hBE : Commuting B E
    · have hBE' : Commuting B E' :=
        (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hEΛ hE'Λ hEE' hB).1 hBE
      exact ((hBE b hb e he).symm.inv_left).mul_left (hBE' b hb e' he').symm
    have hsBE : Special R B E :=
      (CentralOrbit.commutator_mem_lambdaSet h hA hEΛ.1 (fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hEΛ.2.2.2) hB.1
        fun hc => hBE hc.symm).1.symm
    obtain ⟨hline, F, hFΛ, hEF, hBF⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hEΛ hB hsBE
    have hF : F ∈ Δ := by
      have h1 : F ∈ comp R A A₀ E := Relation.ReflTransGen.single ⟨hEΛ, hFΛ, hEF⟩
      rw [comp_eq_of_mem hE] at h1
      exact h1
    have hFR : F ∈ R := hFΛ.1.1
    have hFxΛ : conjSub F x ∈ leviSet R A A₀ := conjSub_mem_leviSet_of_mem_levi hR hFΛ hxlevi
    have hFFx := hFx F hF hEF
    set D := ⁅B, E⁆ with hDdef
    have hDR : D ∈ R := hsBE.1
    have hDE' : D = ⁅B, E'⁆ :=
      commutator_eq_of_commuting_iff h hA hAne hA₀ hEΛ hE'Λ hEE' hB fun hc => hBE hc
    have hDst : D ∈ lambdaStar R A A₀ := hline D hDR le_sup_right
    obtain ⟨hBD, hED⟩ := mem_lambdaSet_commutator hR hiso hBR hER hsBE
    have hDEc : Commuting D E := hED.1.2.2
    have hDE'c : Commuting D E' :=
      (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hEΛ hE'Λ hEE' hDst).1 hDEc
    have hFD : ¬ Commuting D F := fun hc =>
      not_commuting_of_opposite_of_mem_lambdaSet hR hFR hEF.symm (mem_lambdaSet_comm hDR hED)
        hc.symm
    have hFxD : ¬ Commuting D (conjSub F x) := fun hc =>
      hFD ((commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hFΛ hFxΛ hFFx hDst).2 hc)
    have hBFc : Commuting B F := hBF.1.2.2.symm
    have hBFx : Commuting B (conjSub F x) :=
      (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hFΛ hFxΛ hFFx hB).1 hBFc
    have hxbD : ∀ b' ∈ B, ⁅x, b'⁆ ∈ D := by
      intro b' hb'
      have e1 : ⁅x, b'⁆ = ((e : G)⁻¹ * ⁅e', b'⁆ * e) * ⁅(e : G)⁻¹, b'⁆ := by
        simp only [hxdef, commutatorElement_def]
        group
      have hc1 : ⁅e', b'⁆ ∈ D := by
        rw [hDE', Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator he' hb'
      have hc2 : ⁅(e : G)⁻¹, b'⁆ ∈ D := by
        rw [hDdef, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (E.inv_mem he) hb'
      have hc3 : (e : G)⁻¹ * ⁅e', b'⁆ * e = ⁅e', b'⁆ := by
        rw [mul_assoc, (hDEc _ hc1 (e : G) he).eq, inv_mul_cancel_left]
      rw [e1, hc3]
      exact D.mul_mem hc1 hc2
    have hBDl : D ∈ lambdaSet R B := mem_lambdaSet_comm hDR hBD
    have hBxle : conjSub B x ≤ B ⊔ D := by
      rintro _ ⟨b', hb', rfl⟩
      change x * b' * x⁻¹ ∈ B ⊔ D
      rw [show x * b' * x⁻¹ = ⁅x, b'⁆ * b' by rw [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hxbD b' hb')) (Subgroup.mem_sup_left hb')
    have hBx : conjSub B x = B := by
      by_contra hne'
      have hBxR : conjSub B x ∈ R := hR.conjSub_mem hBR x
      obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hBR hBDl hBR le_sup_left hBxR hBxle
        (Ne.symm hne')
      have hBxFx : Commuting (conjSub B x) (conjSub F x) := hBFc.conjSub x
      have hLFx : Commuting (B ⊔ D) (conjSub F x) := hsup ▸ Commuting.sup_left hBFx hBxFx
      exact hFxD (hLFx.mono le_sup_right le_rfl)
    have hxbB : ⁅x, b⁆ ∈ B := by
      rw [commutatorElement_def]
      have hxb : x * b * x⁻¹ ∈ B := by
        rw [← hBx]
        exact conj_mem_conjSub x hb
      exact B.mul_mem hxb (B.inv_mem hb)
    have hmem : ⁅x, b⁆ ∈ B ⊓ D := ⟨hxbB, hxbD b hb⟩
    rw [inf_eq_bot hR hiso hBR hDR hBD.1.2.1, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hxM : ∀ m ∈ M R A, Commute x m := by
    have hle : M R A ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [M_eq_gen_lambdaStar h hA hA₀]
      refine gen_le fun B hB b hb => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (hxB B hB b hb).eq
    exact fun m hm => (Subgroup.mem_centralizer_iff.1 (hle hm) x rfl)
  have hx1 : x = 1 := eq_one_of_forall_commute_lambdaSet hR hiso h.nondeg h.center hA hA₀
    (fun E₁ hE₁ e₁ he₁ => hxM e₁ (QD.le_M hE₁ he₁)) hxA₀
  have hee : (e : G) = e' := by
    have := hx1
    rw [hxdef, inv_mul_eq_one] at this
    exact this
  exact hne (Sec3.eq_of_mem_of_mem hR hiso hER hE'R he (hee ▸ he') (hee ▸ he'1))

end Levi

end CFSG.Timmesfeld.ARS
