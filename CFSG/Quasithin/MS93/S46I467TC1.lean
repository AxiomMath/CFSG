module

public import CFSG.Quasithin.MS93.S46I467TDec
public import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S46Ker

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open scoped Matrix

section SplitT

variable {F : Type} [Field F] [Finite F] {n : ℕ} {H : Type} [Group H]
  {X : Type} [CommGroup X] [Finite X]

theorem natSplit_quot_t (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ψ : H →* SL3 F)
    (hψ : Function.Surjective ψ) {Q : Subgroup H} (hQ : ψ.ker = Q) (ρ : H →* MulAut X)
    {a : H} (ha1 : ψ a ≠ 1) (ha2 : ψ a * ψ a = 1)
    (hcomm : Nat.card (commV ((Subgroup.zpowers a).map ρ)) ≤ Nat.card F)
    (hnt : ¬ commV ρ.range ≤ commV (Q.map ρ)) :
    ∃ C : Subgroup X, commV (Q.map ρ) ≤ C ∧
      (∀ h, ∀ c ∈ C, ρ h c * c⁻¹ ∈ commV (Q.map ρ)) ∧
      commV ρ.range ⊔ C = ⊤ ∧ commV ρ.range ⊓ C = commV (Q.map ρ) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : H →* SL3 F') (β : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ Function.Surjective β ∧
          (∀ p : ↥(commV ρ.range), β p = 1 ↔ (p : X) ∈ commV (Q.map ρ)) ∧
          ∀ h (p : ↥(commV ρ.range)),
            β (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) h p) =
              Multiplicative.ofAdd ((τ h : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (β p)) := by
  have : Q.Normal := hQ ▸ MonoidHom.normal_ker ψ
  have hKinv : ∀ h, ∀ x ∈ commV (Q.map ρ), ρ h x ∈ commV (Q.map ρ) :=
    fun h x hx => commV_map_inv ρ h hx
  have htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X) :=
    fun _ _ _ => Subgroup.mem_top _
  have hker₀ := ker_le_ker_secRho hQ ρ htop hKinv fun q hq w _ =>
    G6.mem_commV_of_mem (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩) w
  have hnt₀ : ∃ h y, secRho ρ htop hKinv h y ≠ y :=
    secRho_nt_of_not_le (L := ⊤) ρ (by rw [← MonoidHom.range_eq_map]; exact hnt)
  have hcomm' : Nat.card (commV ((Subgroup.zpowers (ψ a)).map (liftRho ψ hψ _ hker₀))) ≤
      Nat.card F := by
    rw [← MonoidHom.map_zpowers, map_liftRho]
    exact (card_commV_sec_le ρ htop hKinv le_top (Subgroup.zpowers a)).trans hcomm
  exact natSplit_core ψ hψ ρ htop hKinv hker₀ (transvDecomp hF (sec_sq hX2) _
    (liftRho_nt hψ hker₀ hnt₀) ha1 ha2 hcomm')

end SplitT

end CFSG.Quasithin.MS93.S4A.F

namespace CFSG.Quasithin.MS93.S46.I467T

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A.F CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem isC1_of_transv {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) (hb : 2 < critDist (puAmalgam h.le))
    {δ β : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β)
    {A : Subgroup (puAmalgam h.le).Universal} (hAT : A ≤ Qv (puAmalgam h.le) β)
    (hA2 : ∀ a ∈ A, a ^ 2 ∈ Qv (puAmalgam h.le) δ) (hAQ : ¬ A ≤ Qv (puAmalgam h.le) δ)
    (hVab : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    (hVQ : ⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    (hsmall : (ZM (puAmalgam h.le) δ).relIndex (⁅Vv (puAmalgam h.le) δ, A⁆ ⊔
      ZM (puAmalgam h.le) δ) ≤ Fintype.card F) :
    IsC1 h.le L (Fintype.card F) δ (Vv (puAmalgam h.le) δ) (ZM (puAmalgam h.le) δ) := by
  have h20 := h.hyp20
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have hAs : A ≤ stab _ δ := hAT.trans (qv_le_stab_of_adj _ hδβ.symm)
  have hZV := zm_le_vv h hδ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have : Finite ↥(Vv (puAmalgam h.le) δ) := Finite.of_injective _
    (Subgroup.inclusion_injective ((vv_le_qv h hb hδ).trans hQs))
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hδ
  have hψs : Function.Surjective (toSL3 ψ₀) := toSL3_surjective hψ₀s
  set Q := (Qv (puAmalgam h.le) δ).subgroupOf (stab _ δ) with hQdef
  have hQ : (toSL3 ψ₀).ker = Q := by
    ext g
    rw [MonoidHom.mem_ker, hQdef, Subgroup.mem_subgroupOf]
    exact toSL3_eq_one_iff_mem_qv h hφ hδ hψ₀ g
  set Lh := (Ltil h.le L δ).subgroupOf (stab _ δ) with hLhdef
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := stab _ δ)
    (stab_le_normalizer_vv h δ) hZV (stab_le_normalizer_zm _ δ)
    (fun v hv w hw => hVab (Subgroup.commutator_mem_commutator hv hw))
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact sq_mem_zm_of_mem_vv h hfull hVab v.2
  set As := A.subgroupOf (stab _ δ) with hAsdef
  have hone : ∀ a : ↥(stab (puAmalgam h.le) δ), (a : (puAmalgam h.le).Universal) ∈
      Qv (puAmalgam h.le) δ → toSL3 ψ₀ a = 1 := fun a ha =>
    (toSL3_eq_one_iff_mem_qv h hφ hδ hψ₀ a).mpr ha
  have hcomm : Nat.card (commV (As.map ρ)) ≤ Nat.card F := by
    rw [← card_pre hπk hZV hπs, pre_commV hρ hπk hZV hπs hAs, Nat.card_eq_fintype_card]
    exact hsmall
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := Set.not_subset.mp hAQ
  have ha1 : toSL3 ψ₀ ⟨a₀, hAs ha₀A⟩ ≠ 1 := fun h1 =>
    ha₀Q ((toSL3_eq_one_iff_mem_qv h hφ hδ hψ₀ ⟨a₀, hAs ha₀A⟩).mp h1)
  have ha2 : toSL3 ψ₀ ⟨a₀, hAs ha₀A⟩ * toSL3 ψ₀ ⟨a₀, hAs ha₀A⟩ = 1 := by
    rw [← map_mul]
    refine hone _ ?_
    have := hA2 a₀ ha₀A
    rwa [pow_two] at this
  have hcomma : Nat.card (commV ((Subgroup.zpowers
      (⟨a₀, hAs ha₀A⟩ : ↥(stab (puAmalgam h.le) δ))).map ρ)) ≤ Nat.card F := by
    refine le_trans (Subgroup.card_le_of_le (G6.commV_mono (Subgroup.map_mono ?_))) hcomm
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.mpr ha₀A
  have hN : ¬ commV (Lh.map ρ) ≤ commV (Q.map ρ) := by
    intro hle
    apply not_commutator_ltil_le h hfull hb hδ hδβ hX2 hπs hπk hρ
    have h1 := pre_mono (π := π) hle
    rw [pre_commV hρ hπk hZV hπs (ltil_le_stab h δ), pre_commV hρ hπk hZV hπs hQs] at h1
    exact le_sup_left.trans h1
  obtain ⟨C, hKC, hCfix, hPC, hPiC, F', iF', fF', hFF', τ, β', hτs, hβ's, hβ'k, hβ'e⟩ :=
    natSplit_quot_t hFn hX2 (toSL3 ψ₀) hψs hQ ρ ha1 ha2 hcomma
      (fun h' => hN ((G6.commV_mono (Subgroup.map_le_range ρ Lh)).trans h'))
  have hKq := pre_commV hρ hπk hZV hπs hQs
  have hKP : pre π (commV ρ.range) =
      ⁅Vv (puAmalgam h.le) δ, stab (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ := by
    have := pre_commV hρ hπk hZV hπs (le_refl (stab (puAmalgam h.le) δ))
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  let _ : Fintype F' := Fintype.ofFinite F'
  refine ⟨?_, pre π C, ?_, pre_le C, ?_, ?_, ?_, F', iF', inferInstance,
    (specialLinearGroupEquivStatedSL 3 F').toMonoidHom.comp τ, ?_, ?_, ?_⟩
  · exact (Subgroup.commutator_mono hVQ le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h δ).trans (stab_le_normalizer_zm _ δ)))
  · rw [← hKq]
    exact pre_mono hKC
  · rw [← hKq]
    exact commutator_pre_le_of_fix hρ hCfix
  · rw [← hKP, ← pre_sup hπs, hPC, pre_top]
  · rw [← hKP, ← pre_inf, hPiC, hKq]
  · rw [Fintype.card_eq_nat_card, hFF', Nat.card_eq_fintype_card]
  · exact (specialLinearGroupEquivStatedSL 3 F').surjective.comp hτs
  · rw [← hKP, ← hKq]
    exact isSumOfNaturalModulesVia_pre hρ hπs (fun k x hx => commV_inv ρ k hx)
      (G6.commV_mono (Subgroup.map_le_range ρ Q)) τ β' hβ's hβ'k hβ'e

end CFSG.Quasithin.MS93.S46.I467T
