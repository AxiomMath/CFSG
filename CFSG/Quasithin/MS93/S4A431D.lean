module

public import CFSG.Quasithin.MS93.S4A431C
public import CFSG.Quasithin.MS93.S4A431

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section StarSmul

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem star_smul (g : X.Universal) (α α' : Vtx X) :
    Star X (g • α) (g • α') ↔ Star X α α' := by
  rw [Star, Star, isCritical_smul, geo_smul, show Vv X (g • α) = (Vv X α).map
    (MulAut.conj g).toMonoidHom from vi_smul X g α 2, qv_smul, map_conj_le_map_conj_iff]

theorem exists_star_at {α α' δ : Vtx X} (hs : Star X α α') (hδ : IsMVtx X δ) :
    ∃ δ' : Vtx X, Star X δ δ' := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx X hs.1.1 hδ
  exact ⟨g • α', (star_smul X g α α').mpr hs⟩

end StarSmul

section SecHom

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

theorem secVec_one (h : IsSumOfNaturalModulesVia K V Z φ false 1) : secVec h 1 = 0 := by
  have := secVec_mul h 1 1
  rw [mul_one] at this
  exact add_eq_left.mp this.symm

@[expose] noncomputable def secHom (h : IsSumOfNaturalModulesVia K V Z φ false 1) :
    ↥V →* Multiplicative (Fin 3 → F) where
  toFun v := Multiplicative.ofAdd (secVec h v)
  map_one' := by rw [secVec_one, ofAdd_zero]
  map_mul' v w := by rw [secVec_mul, ofAdd_add]

theorem secHom_apply (h : IsSumOfNaturalModulesVia K V Z φ false 1) (v : ↥V) :
    secHom h v = Multiplicative.ofAdd (secVec h v) :=
  rfl

end SecHom

section IV

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

omit hfull in
theorem zm_le_conjCl_zm {α δ : Vtx (puAmalgam h.le)}
    (hd : (puAmalgam h.le).treeGraph.dist α δ = 2) :
    ZM (puAmalgam h.le) α ≤ conjCl (stab _ α) (ZM (puAmalgam h.le) δ) := by
  have hα1 : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α δ 1) :=
    adj_geo_one _ (by omega)
  have h1δ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ 1) δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) α δ (1 + 1) = δ from geo_of_le _ (by omega)] at this
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul (puAmalgam h.le) hα1 hρ
  rw [← hgρ, zh_smul]
  refine (Subgroup.map_mono (zh_le_zm _ h1δ.symm)).trans ?_
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam h.le) α) =>
    (ZM (puAmalgam h.le) δ).map (MulAut.conj g).toMonoidHom) g hg le_rfl

theorem vcirc_le_conjCl (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {δ : Vtx (puAmalgam h.le)} (hδ : δ ∈ nablaSet h.le L α) :
    Vcirc h.le L α ≤ conjCl (stab _ α) (ZM (puAmalgam h.le) δ) := by
  obtain ⟨hd, hZB⟩ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have hev : Even ((puAmalgam h.le).treeGraph.dist α δ) := ⟨1, by rw [hd]⟩
    exact ((even_dist_iff (puAmalgam h.le) α δ).mp hev).1 hα
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hNn := le_normalizer_conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ)
  have hZδV : ZM (puAmalgam h.le) δ ≤ Vv _ α := by
    rw [← zv_of_isMVtx _ hδM]
    exact zv_le_vv h hd.le
  have hNV : conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ) ≤ Vv _ α := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hVn hg) z).mp (hZδV hz)
  have hNB : ¬ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ) ≤ Bloc h.le L α := by
    intro hle
    apply hZB
    rw [zv_of_isMVtx _ hδM]
    exact (le_conjCl _ _).trans hle
  have hNBV := (isC1_bloc h hfull hb hα hc).2.2 _ hNn hNV hNB
  have hZN := zm_le_conjCl_zm h hd
  have hBV : Bloc h.le L α ≤ Vv _ α := bloc_le_vv h α
  rw [Vcirc, ← hNBV]
  refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h α).trans hNn)
  · exact (commutator_bloc_le h hb hα).trans hZN
  · exact Subgroup.le_normalizer
  · exact (hBV.trans hVs).trans hNn

theorem not_commutator_vv_ltil_le_bloc (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ¬ ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ Bloc h.le L α := by
  intro hle
  obtain ⟨F', _, _, ψ', -, hsurj, hnat, hPiB, -, -, -⟩ := isC1_normal h hfull hb hα hc
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hQs : Qv (puAmalgam h.le) α ≤ stab _ α := qv_le_stab _ α
  have hQn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_qv _ α
  have hLs := ltil_le_stab h α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn hQn) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)
  have hfixK : ∀ p : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α),
      ∀ s ∈ stab (puAmalgam h.le) α, s * (p : (puAmalgam h.le).Universal) * s⁻¹ *
        (p : (puAmalgam h.le).Universal)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
    intro p s hs
    have hs' : s ∈ ((Ltil h.le L α ⊔ Qv (puAmalgam h.le) α : Subgroup _) : Set _) :=
      stab_eq_ltil_sup_qv h hfull hα ▸ hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hLs.trans hQn)] at hs'
    obtain ⟨l, hl, t, ht, rfl⟩ := hs'
    have hpV := hPV p.2
    have h1 : t * (p : (puAmalgam h.le).Universal) * t⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
      refine Subgroup.mem_sup_left ?_
      have : t * (p : (puAmalgam h.le).Universal) * t⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ =
          ⁅(p : (puAmalgam h.le).Universal), t⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hpV ht)
    have h2 : l * (p : (puAmalgam h.le).Universal) * l⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
      rw [← hPiB]
      refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hPn (hLs hl)) _).mp p.2)
        (Subgroup.inv_mem _ p.2), ?_⟩
      have : l * (p : (puAmalgam h.le).Universal) * l⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ =
          ⁅(p : (puAmalgam h.le).Universal), l⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.inv_mem _ (hle (Subgroup.commutator_mem_commutator hpV hl))
    have hrw : l * t * (p : (puAmalgam h.le).Universal) * (l * t)⁻¹ *
        (p : (puAmalgam h.le).Universal)⁻¹ =
        (l * (t * (p : (puAmalgam h.le).Universal) * t⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹) *
          l⁻¹) * (l * (p : (puAmalgam h.le).Universal) * l⁻¹ *
            (p : (puAmalgam h.le).Universal)⁻¹) := by group
    dsimp only
    rw [hrw]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hKn (hLs hl)) _).mp h1) h2
  obtain ⟨v, hv⟩ := secVec_surjective hnat ![1, 0, 0]
  have hfix : ∀ g : SL3 F', ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ secVec hnat v =
      secVec hnat v := by
    intro g
    obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
    have hsp : (s : (puAmalgam h.le).Universal) * v * (s : (puAmalgam h.le).Universal)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (hPn s.2) _).mp v.2
    rw [← secVec_conj hnat s v ⟨_, hsp⟩ rfl]
    have hdiff : secVec hnat (⟨_, hsp⟩ * v⁻¹) = 0 :=
      (secVec_eq_zero_iff hnat _).mpr (by simpa using hfixK v s s.2)
    rw [secVec_mul, secVec_inv, add_neg_eq_zero] at hdiff
    exact hdiff
  have h0 := eq_zero_of_forall_mulVec_eq hfix
  rw [hv] at h0
  have := congrFun h0 0
  simp at this

theorem sq_le_card_commutator_vv (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le)) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α) :
    Fintype.card F ^ 2 ≤ Nat.card ↥⁅Vv (puAmalgam h.le) α, X⁆ := by
  have h20 := h.hyp20
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hβ : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hXs : X ≤ stab (puAmalgam h.le) α := hXβ.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hVQ := vv_le_qv h hb hα
  have hfinβ : Finite ↥(Qv (puAmalgam h.le) β) := finite_qv _ h20 hβ
  have hVβ : Vv (puAmalgam h.le) α ≤ Qv _ β := hVQ.trans (qv_le_qv _ h20 hα hαβ)
  have hYV : ⁅Vv (puAmalgam h.le) α, X⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hXs.trans (stab_le_normalizer_vv h α))
  have hfinY : Finite ↥⁅Vv (puAmalgam h.le) α, X⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hYV.trans hVβ))
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hXU : natImage ψ X ≠ ⊥ := by
    intro hbot
    apply hXα
    rw [← hC α β hα hαβ]
    intro x hx
    refine ⟨hXβ hx, ?_⟩
    have h1 : toSL3 ψ ⟨x, hXs hx⟩ = 1 := by
      have : toSL3 ψ ⟨x, hXs hx⟩ ∈ natImage ψ X := mem_natImage.mpr ⟨_, hx, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    refine (mem_centralizer_zm_iff h hfull hα (hXs hx)).mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := (toSL3_eq_one_iff hψ _).mp h1 u hu
    calc u * x = x * u * x⁻¹ * x := by rw [show x * u * x⁻¹ = u from this]
      _ = x * u := by group
  have hU1 : Nat.card F ≤ Nat.card ↥⁅Uloc h.le L α, X⁆ := by
    rw [card_commutator_eq hψ hXs]
    exact card_le_commN hXU
  obtain ⟨F', _, _, ψ', hcard', hsurj, hnat, hPiB, hPB, -, -⟩ := isC1_normal h hfull hb hα hc
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Bloc h.le L α := hPiB ▸ inf_le_right
  have hBn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) α
  have hBs : Bloc h.le L α ≤ stab _ α := (bloc_le_vv h α).trans (hVQ.trans (qv_le_stab _ α))
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)
  have hPs : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      stab _ α :=
    (sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)).trans
      (hVQ.trans (qv_le_stab _ α))
  obtain ⟨x₀, hx₀, hg₀⟩ : ∃ x, ∃ hx : x ∈ X, toSL3 ψ' ⟨x, hXs hx⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply not_commutator_vv_ltil_le_bloc h hfull hb hα hc
    refine commutator_vv_ltil_le_of h hfull hα hαβ hXβ hXα hBn ?_
    have hPX : ⁅⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α, X⁆ ≤
        Bloc h.le L α := by
      rw [Subgroup.commutator_le]
      intro p hp x hx
      have h1 := hcon x hx
      have hsp : x * p * x⁻¹ ∈ ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α := (Subgroup.mem_normalizer_iff.mp (hPn (hXs hx)) _).mp hp
      have heq := secVec_conj hnat ⟨x, hXs hx⟩ ⟨p, hp⟩ ⟨_, hsp⟩ rfl
      rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at heq
      have hdiff : secVec hnat (⟨_, hsp⟩ * (⟨p, hp⟩ : ↥(⁅Vv (puAmalgam h.le) α,
          stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α))⁻¹) = 0 := by
        rw [secVec_mul, secVec_inv, heq, add_neg_cancel]
      have hK := (secVec_eq_zero_iff hnat _).mp hdiff
      have hrw : ⁅p, x⁆ = (x * p * x⁻¹ * p⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact hKB (Subgroup.inv_mem _ (by simpa using hK))
    calc ⁅Vv (puAmalgam h.le) α, X⁆ = ⁅(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α) ⊔ Bloc h.le L α, X⁆ := by rw [hPB]
      _ ≤ Bloc h.le L α := S4A.commutator_sup_le_of hPX
          (Subgroup.le_normalizer_iff_commutator_le_left.mp (hXs.trans hBn))
          (hPs.trans hBn) (hBs.trans hBn)
  set g₀ := toSL3 ψ' ⟨x₀, hXs hx₀⟩ with hg₀def
  have hfinYP : Finite ↥(⁅Vv (puAmalgam h.le) α, X⁆ ⊓
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans (hYV.trans hVβ)))
  let f : ↥(⁅Vv (puAmalgam h.le) α, X⁆ ⊓
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)) →*
      Multiplicative (Fin 3 → F') :=
    (secHom hnat).comp (Subgroup.inclusion inf_le_right)
  have hker : f.ker = (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α).subgroupOf (⁅Vv (puAmalgam h.le) α, X⁆ ⊓
        (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, secHom_apply,
      ofAdd_eq_one]
    exact secVec_eq_zero_iff hnat _
  have hrange : Nat.card F' ≤ Nat.card f.range := by
    set W : Submodule F' (Fin 3 → F') :=
      LinearMap.range (Matrix.toLin' ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') -
        LinearMap.id) with hW
    have hWne : W ≠ ⊥ := by
      intro hbot
      apply hg₀
      refine eq_one_of_mulVec_eq_self fun v => ?_
      have : ((Matrix.toLin' ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') - LinearMap.id :
          (Fin 3 → F') →ₗ[F'] (Fin 3 → F')) v) ∈ W := ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
        sub_eq_zero] at this
      exact this
    have hcardW := card_le_of_ne_bot hWne
    have hmem : ∀ w ∈ W, Multiplicative.ofAdd w ∈ f.range := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨p, hp⟩ := secVec_surjective hnat v
      have hsp : x₀ * p * x₀⁻¹ ∈ ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α := (Subgroup.mem_normalizer_iff.mp (hPn (hXs hx₀)) _).mp p.2
      have hyY : x₀ * p * x₀⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ ∈
          ⁅Vv (puAmalgam h.le) α, X⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hx₀ (hPV p.2)
      have hyP : x₀ * p * x₀⁻¹ * (p : (puAmalgam h.le).Universal)⁻¹ ∈
          ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
        Subgroup.mul_mem _ hsp (Subgroup.inv_mem _ p.2)
      refine ⟨⟨_, hyY, hyP⟩, ?_⟩
      rw [MonoidHom.comp_apply, secHom_apply]
      rw [show (Subgroup.inclusion inf_le_right ⟨_, hyY, hyP⟩ : ↥(⁅Vv (puAmalgam h.le) α,
          stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)) = ⟨_, hsp⟩ * p⁻¹ from rfl,
        secVec_mul, secVec_inv, secVec_conj hnat ⟨x₀, hXs hx₀⟩ p ⟨_, hsp⟩ rfl, hp,
        LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_add_neg]
    calc Nat.card F' ≤ Nat.card ↥W := hcardW
      _ ≤ Nat.card f.range :=
        Nat.card_le_card_of_injective (fun w : ↥W => (⟨_, hmem w w.2⟩ : ↥f.range))
          (fun w w' hww' => Subtype.ext (Multiplicative.ofAdd.injective
            (congrArg (Subtype.val : ↥f.range → Multiplicative (Fin 3 → F')) hww')))
  have hrel : Nat.card F' ≤ (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α).relIndex ⁅Vv (puAmalgam h.le) α, X⁆ := by
    refine hrange.trans ?_
    rw [← Subgroup.index_ker, hker]
    refine Subgroup.relIndex_le_of_le_right inf_le_left ?_
    exact Subgroup.index_ne_zero_of_finite
  have hUK : ⁅Uloc h.le L α, X⁆ ≤ (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α) ⊓ ⁅Vv (puAmalgam h.le) α, X⁆ := by
    refine le_inf ?_ (Subgroup.commutator_mono ((uloc_le_zm h hfull hα).trans (zm_le_vv h hα))
      le_rfl)
    refine le_sup_right.trans' ((Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hXs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α))).trans
        (uloc_le_zm h hfull hα))
  have hfinK : Finite ↥((⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α) ⊓ ⁅Vv (puAmalgam h.le) α, X⁆) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans (hYV.trans hVβ)))
  have hmul := relIndex_mul_card_inf (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
    ZM (puAmalgam h.le) α) ⁅Vv (puAmalgam h.le) α, X⁆
  rw [← hmul, sq]
  have hq' : Nat.card F' = Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard', Nat.card_eq_fintype_card]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.mul_le_mul (hq' ▸ hrel) (hU1.trans (Subgroup.card_le_of_le hUK))

end IV

end CFSG.Quasithin.MS93.S4A
