module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Three

theorem exists_fix_stab_four :
    ∃ w : orth.W, w ≠ 1 ∧ ∀ σ : Perm (Fin 5), σ 4 = 4 → orth.act σ w = w := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem dist_eq_two_of_mem_nbrs (hA : F53Amalgam H M S) (hs : Sit43 α) {ε ε' : Geo H M}
    (hε : ε ∈ nbrs α) (hε' : ε' ∈ nbrs α) (hne : ε ≠ ε') : dist ε ε' = 2 := by
  have h1 : dist ε α = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hε)
  have h2 : dist α ε' = 1 := dist_eq_one_iff_adj.mpr hε'
  have h3 := dist_triangle hA.amalgam.gen ε α ε'
  have h0 : dist ε ε' ≠ 0 := fun h => hne ((dist_eq_zero_iff hA.amalgam.gen).mp h)
  have h1' : dist ε ε' ≠ 1 := by
    intro h
    exact vtype_ne_of_adj (dist_eq_one_iff_adj.mp h)
      ((Sit43.vtype_true_of_adj hs.vα hε).trans (Sit43.vtype_true_of_adj hs.vα hε').symm)
  omega

theorem dist_le_two_of_mem_nbrs (hA : F53Amalgam H M S) {ε ε' : Geo H M}
    (hε : ε ∈ nbrs α) (hε' : ε' ∈ nbrs α) : dist ε ε' ≤ 2 := by
  have h1 : dist ε α = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hε)
  have h2 : dist α ε' = 1 := dist_eq_one_iff_adj.mpr hε'
  have h3 := dist_triangle hA.amalgam.gen ε α ε'
  omega

theorem exists_crit_elt (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {β : Geo H M} (hβ : β ∈ nbrs α) :
    ∃ γ ∈ nbrs β, γ ≠ α ∧ ∃ y : G, y ∈ stab γ ∧ y ∈ stab β ∧ y ∉ Qv β ∧
      ∀ c ∈ Cst β, ⁅c, y⁆ ∈ Vn β := by
  have ho : Odd (bMin H M) := by rw [h3]; decide
  have hb : 3 ≤ bMin H M := h3.ge
  obtain ⟨α₀, hc₀⟩ := hs.exists_crit_partner hA
  obtain ⟨β₀, ν₀, hβ₀, hν₀, hdβ₀, hdν₀, hdβν₀⟩ := Core.exists_crit_data hA hs hc₀
  obtain ⟨g, hg, hgβ⟩ := stab_transitive_on_nbrs hβ₀ hβ
  have hgα : g • α = α := smul_eq_of_mem_stab hg
  set α' := g • α₀ with hα'
  set γ := g • ν₀ with hγdef
  have hdist : ∀ u v : Geo H M, dist (g • u) (g • v) = dist u v := fun u v => dist_smul g u v
  have hc : IsCritPair₁ α α' := by
    refine ⟨fun h => hc₀.1 ?_, ?_⟩
    · have e : Zv α = conjSub (g : G) (Zv α) := by
        conv_lhs => rw [← hgα]
        exact Zv_smul g α
      rw [hα', Qv_smul, e, conjSub_le_iff, conjSub_conjSub_inv] at h
      exact h
    · have h1 := hdist α α₀
      rw [hgα] at h1
      rw [h1]
      exact hc₀.2
  have hν : γ ∈ nbrs α' := (smul_adj g).mpr hν₀
  have hdν : dist α γ + 1 = bMin H M := by
    have h1 := hdist α ν₀
    rw [hgα] at h1
    rw [h1]
    exact hdν₀
  have hγβ : γ ∈ nbrs β := by
    have h1 : ν₀ ∈ nbrs β₀ := dist_eq_one_iff_adj.mp (by omega)
    have h2 : g • ν₀ ∈ nbrs (g • β₀) := (smul_adj g).mpr h1
    rwa [hgβ] at h2
  have hdβ : dist β α' + 1 = bMin H M := by
    have h1 := hdist β₀ α₀
    rw [hgβ] at h1
    rw [h1]
    exact hdβ₀
  have hγα : γ ≠ α := by
    intro h
    rw [h, (dist_eq_zero_iff hA.amalgam.gen).mpr rfl] at hdν
    omega
  have hγv : vtype γ = false := Core.vtype_nu hA hs ho hc hν
  have hα'v : vtype α' = true := Core.vtype_crit hA hs ho hc
  have hα'γ : α' ∈ nbrs γ := nbrs_symm hν
  have hsym := crit3_symm hA h26 hs ho hb (Core.isCritPair₃_crit hA hs ho hc hβ hdβ)
  obtain ⟨y, hyV, hyQ⟩ : ∃ y ∈ Vn α', y ∉ Qv β := by
    by_contra hcon
    push Not at hcon
    exact hsym.2.2.2 fun x hx => hcon x hx
  have hVQ : Vn α' ≤ Qv γ := hs.Vn_le_Qv_of_nbr hA h26 hb hγv hα'γ
  have hyγ : y ∈ stab γ := pCoreOf_le 2 _ (hVQ hyV)
  have hyβ : y ∈ stab β := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hγβ) (hVQ hyV)
  refine ⟨γ, hγβ, hγα, y, hyγ, hyβ, hyQ, fun c hc' => ?_⟩
  have hcQ : c ∈ Qv β := hc'.1
  have hcC : c ∈ Subgroup.centralizer (Vn β : Set G) := hc'.2
  have hcγ : c ∈ stab γ := Qv_le_stab_of_mem_nbrs hA hγβ hcQ
  have hcZ : c ∈ Subgroup.centralizer (Zv γ : Set G) :=
    Subgroup.centralizer_le (Sit43.Zv_le_Vn_nbrs hγβ) hcC
  have hcQγ : c ∈ Qv γ := hs.centralizer_Zv hA hγv ▸ ⟨hcγ, hcZ⟩
  have hcE : c ∈ stab γ ⊓ stab α' := ⟨hcγ, Qv_le_stab_of_mem_nbrs hA hα'γ hcQγ⟩
  rw [← Core.Zv_sup_Qv_crit hA hs ho hc hν hdν, sup_comm] at hcE
  have hZn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    (Core.Zv_le_stab_crit hA hs hc).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨q, hq, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZn).mp hcE
  have hYV : Yv α' ≤ Vn β := (Yv_le_Zv hν).trans (Sit43.Zv_le_Vn_nbrs hγβ)
  have hzQ : z ∈ Qv β := hs.Vn_le_Qv hβ (Sit43.Zv_le_Vn hβ hz)
  have hqβ : q ∈ stab β := by
    have e : q = (q * z) * z⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (pCoreOf_le 2 _ hcQ) (Subgroup.inv_mem _ (pCoreOf_le 2 _ hzQ))
  have hzY : z ∈ Subgroup.centralizer (Yv α' : Set G) :=
    Subgroup.centralizer_le (Core.Yv_le_Qv hA hs ho hc hν hdν) (Zv_le_centerOf_Qv hA α hz).2
  have hqY : q ∈ Subgroup.centralizer (Yv α' : Set G) := by
    have e : q = (q * z) * z⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.centralizer_le hYV hcC) (Subgroup.inv_mem _ hzY)
  have hqst : q ∈ Qst α' := ⟨hq, hqY⟩
  have e : ⁅q * z, y⁆ = (q * ⁅z, y⁆ * q⁻¹) * ⁅y, q⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅z, y⁆ ∈ Vn β := by
    have e' : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e']
    exact Subgroup.mul_mem _ (Sit43.Zv_le_Vn hβ hz) ((Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Vn β hyβ) _).mp (Subgroup.inv_mem _ (Sit43.Zv_le_Vn hβ hz)))
  have h2 : ⁅y, q⁆ ∈ Yv α' := hs.comm_Vn_Qst hA h26 hα'v hν ▸
    Subgroup.commutator_mem_commutator hyV hqst
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hqβ) _).mp h1)
    (Subgroup.inv_mem _ (hYV h2))

theorem Vn_le_Cst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {β ε : Geo H M} (hβ : β ∈ nbrs α) (hε : ε ∈ nbrs α)
    (h : ⁅Vn ε, Vn β⁆ = ⊥) : Vn ε ≤ Cst β := by
  have hεv := Sit43.vtype_true_of_adj hs.vα hε
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hst : Vn ε ≤ stab β := Core.Vn_le_stab_of_dist hA hs hεv
    (by have := dist_le_two_of_mem_nbrs hA hε hβ; omega)
  have hcen : Vn ε ≤ Subgroup.centralizer (Vn β : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact fun v hv => ⟨mem_Qv_of_mem_centralizer hA h26 hs hβv (hst hv) (hcen hv), hcen hv⟩

theorem comm_Vn_eq_bot_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {β μ ν : Geo H M} (hβ : β ∈ nbrs α) (hμ : μ ∈ nbrs α)
    (hν : ν ∈ nbrs α) (hY : Yv β ⊓ Yv μ = ⊥) (hμβ : ⁅Vn μ, Vn β⁆ = ⊥)
    (hνβ : ⁅Vn ν, Vn β⁆ = ⊥) : ⁅Vn μ, Vn ν⁆ = ⊥ := by
  have ho : Odd (bMin H M) := by rw [h3]; decide
  have hb : 3 ≤ bMin H M := h3.ge
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hμv := Sit43.vtype_true_of_adj hs.vα hμ
  have hνv := Sit43.vtype_true_of_adj hs.vα hν
  obtain ⟨γ, hγ, hγα, y, hyγ, hyβ, hyQ, hyC⟩ := exists_crit_elt hA h26 hs h3 hβ
  have hVab : IsElemAbelian 2 (Vn β) := isElemAbelian_Vn hA hb β
  have hcomm : ∀ a ∈ Cst β, ∀ b ∈ Cst β, y * ⁅a, b⁆ * y⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb'
    have hu : ⁅a, y⁆⁻¹ ∈ Vn β := Subgroup.inv_mem _ (hyC a ha)
    have hw : ⁅b, y⁆⁻¹ ∈ Vn β := Subgroup.inv_mem _ (hyC b hb')
    have ea : y * a * y⁻¹ = ⁅a, y⁆⁻¹ * a := by simp only [commutatorElement_def]; group
    have eb : y * b * y⁻¹ = ⁅b, y⁆⁻¹ * b := by simp only [commutatorElement_def]; group
    have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, ea, eb]
    exact commutatorElement_mul_mul (Subgroup.mem_centralizer_iff.mp ha.2 _ hu)
      (Subgroup.mem_centralizer_iff.mp hb'.2 _ hu) (isElemAbelian_comm hVab hu hw)
      (Subgroup.mem_centralizer_iff.mp ha.2 _ hw) (Subgroup.mem_centralizer_iff.mp hb'.2 _ hw)
  have hRc : ∀ r ∈ ⁅Vn μ, Vn ν⁆, y * r = r * y := by
    have hle : ⁅Vn μ, Vn ν⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb'
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := hcomm a (Vn_le_Cst hA h26 hs h3 hβ hμ hμβ ha) b
        (Vn_le_Cst hA h26 hs h3 hβ hν hνβ hb')
      calc h * ⁅a, b⁆ = (h * ⁅a, b⁆ * h⁻¹) * h := by group
        _ = ⁅a, b⁆ * h := by rw [h1]
    intro r hr
    exact Subgroup.mem_centralizer_iff.mp (hle hr) y rfl
  have hR₁Z : ⁅Vn μ, Vn ν⁆ ⊓ Yv μ ≤ Zv α := inf_le_right.trans (Yv_le_Zv (nbrs_symm hμ))
  have hR₁c : conjSub y (⁅Vn μ, Vn ν⁆ ⊓ Yv μ) = ⁅Vn μ, Vn ν⁆ ⊓ Yv μ :=
    conjSub_eq_self fun r hr => hRc r hr.1
  have hR₁Y := hs.S14 hA h26 hβv hγ (nbrs_symm hβ) hγα hyγ hyβ hyQ hR₁Z hR₁c
  have hR₁ : ⁅Vn μ, Vn ν⁆ ⊓ Yv μ = ⊥ := le_bot_iff.mp (hY ▸ le_inf hR₁Y inf_le_right)
  by_cases hνμ : Vn ν ≤ Qv μ
  · have hst : Vn ν ≤ Qst μ := fun v hv => ⟨hνμ hv,
      Subgroup.centralizer_le (Yv_le_Zv (nbrs_symm hμ))
        (Qv_le_centralizer_Zv hA α (hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hν hv))⟩
    have hle : ⁅Vn μ, Vn ν⁆ ≤ Yv μ := hs.comm_Vn_Qst hA h26 hμv (nbrs_symm hμ) ▸
      Subgroup.commutator_mono le_rfl hst
    rw [← hR₁]
    exact (inf_eq_left.mpr hle).symm
  · exfalso
    have hne : ν ≠ μ := fun h => hνμ (by rw [h]; exact hs.Vn_le_Qv_of_true hμv)
    have hd := dist_eq_two_of_mem_nbrs hA hs hν hμ hne
    have hcp : IsCritPair₃ ν μ := ⟨hνv, hμv, by omega, hνμ⟩
    have h1 := comm_Vn_inf_Yv_ne_bot hA h26 hs ho hb hcp
    rw [Subgroup.commutator_comm] at h1
    exact h1 hR₁

theorem sup_stab_inf_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {β μ : Geo H M} (hβ : β ∈ nbrs α) (hμ : μ ∈ nbrs α) (hY : Yv β ⊓ Yv μ = ⊥) :
    (stab α ⊓ stab β) ⊔ (stab α ⊓ stab μ) = stab α := by
  by_contra hne
  have hle := le_Mab (sup_le inf_le_left inf_le_left) le_sup_left hne
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  obtain ⟨w, hw1, hw⟩ := exists_fix_stab_four
  have hz : D.φ w ∈ Zv α := D.φ_mem w
  have hzc : ∀ x ∈ Mab α β, x * D.φ w = D.φ w * x := by
    intro x hx
    have hxα : x ∈ stab α := Mab_le_stab α β hx
    have h4 := (Sit43.mem_Mab_iff D ⟨x, hxα⟩).mp hx
    have h1 := D.act_eq ⟨x, hxα⟩ w
    rw [hw _ h4] at h1
    calc x * D.φ w = (x * D.φ w * x⁻¹) * x := by group
      _ = D.φ w * x := by rw [← h1]
  have hmem : ∀ {ε : Geo H M}, ε ∈ nbrs α → stab α ⊓ stab ε ≤ Mab α β → D.φ w ∈ Yv ε := by
    intro ε hε hεM
    have hεv := Sit43.vtype_true_of_adj hs.vα hε
    have h1 : D.φ w ∈ Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab ε : Subgroup G) : Set G) :=
      ⟨hz, Subgroup.mem_centralizer_iff.mpr fun x hx => hzc x (hεM hx)⟩
    rw [hs.Zv_inf_centralizer hA h26 hεv (nbrs_symm hε)] at h1
    have hZY : Zv ε ≤ Yv ε := le_iInf₂ fun l hl => hs.Zv_le_Zv_nbr hA h26 hεv hl
    exact hZY h1
  have h3 : D.φ w ∈ Yv β ⊓ Yv μ :=
    ⟨hmem hβ (le_sup_left.trans hle), hmem hμ (le_sup_right.trans hle)⟩
  rw [hY, Subgroup.mem_bot] at h3
  exact hw1 (D.inj (h3.trans (map_one D.φ).symm))

theorem conjSub_iSup_Vn_le {β : Geo H M} {g : G} (hg : g ∈ stab α) (hgβ : g ∈ stab β) :
    conjSub g (⨆ (ν : Geo H M) (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥), Vn ν) ≤
      ⨆ (ν : Geo H M) (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥), Vn ν := by
  rw [conjSub_iSup]
  refine iSup_le fun ν => ?_
  rw [conjSub_iSup]
  refine iSup_le fun hν => ?_
  set g' : ↥(H ⊔ M) := ⟨g, stab_le α hg⟩
  have e : conjSub g (Vn ν) = Vn (g' • ν) := (Vn_smul g' ν).symm
  rw [e]
  refine le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥) => Vn ν)
    (g' • ν) ⟨smul_mem_nbrs_of_mem_stab g' hg hν.1, ?_⟩ le_rfl
  have eβ : Vn β = conjSub g (Vn β) :=
    (F1.conjSub_eq_of_mem_normalizer (stab_le_normalizer_Vn β hgβ)).symm
  rw [← e, eβ, conjSub_commutator, hν.2, conjSub_bot]


end Three

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

open Three in
theorem not_Vn_le_Qv_of_Yv_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {β μ : Geo H M} (hβ : β ∈ nbrs α) (hμ : μ ∈ nbrs α)
    (hY : Yv β ⊓ Yv μ = ⊥) : ¬ Vn μ ≤ Qv β := by
  intro hμβ
  have ho : Odd (bMin H M) := by rw [h3]; decide
  have hb : 3 ≤ bMin H M := h3.ge
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hμv := Sit43.vtype_true_of_adj hs.vα hμ
  have hne : β ≠ μ := by
    rintro rfl
    rw [inf_idem] at hY
    have h1 := hs.card_Yv hA h26 hβv
    rw [hY, Subgroup.card_bot] at h1
    omega
  have hd := dist_eq_two_of_mem_nbrs hA hs hβ hμ hne
  have hβμ : Vn β ≤ Qv μ := by
    by_contra h
    exact (crit3_symm hA h26 hs ho hb ⟨hβv, hμv, by omega, h⟩).2.2.2 hμβ
  have hst : ∀ {ε ε' : Geo H M}, ε ∈ nbrs α → ε' ∈ nbrs α → Vn ε ≤ Qv ε' → Vn ε ≤ Qst ε' :=
    fun hε hε' h v hv => ⟨h hv, Subgroup.centralizer_le (Yv_le_Zv (nbrs_symm hε'))
      (Qv_le_centralizer_Zv hA α (hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hε hv))⟩
  have hcomm : ⁅Vn μ, Vn β⁆ = ⊥ := by
    have h1 : ⁅Vn μ, Vn β⁆ ≤ Yv β := by
      rw [Subgroup.commutator_comm, ← hs.comm_Vn_Qst hA h26 hβv (nbrs_symm hβ)]
      exact Subgroup.commutator_mono le_rfl (hst hμ hβ hμβ)
    have h2 : ⁅Vn μ, Vn β⁆ ≤ Yv μ := by
      rw [← hs.comm_Vn_Qst hA h26 hμv (nbrs_symm hμ)]
      exact Subgroup.commutator_mono le_rfl (hst hβ hμ hβμ)
    exact le_bot_iff.mp (hY ▸ le_inf h1 h2)
  have hΩ : ∀ ν ∈ nbrs α, ⁅Vn ν, Vn β⁆ = ⊥ ↔ ⁅Vn ν, Vn μ⁆ = ⊥ := by
    intro ν hν
    constructor
    · intro h
      rw [Subgroup.commutator_comm]
      exact comm_Vn_eq_bot_of hA h26 hs h3 hβ hμ hν hY hcomm h
    · intro h
      rw [Subgroup.commutator_comm]
      exact comm_Vn_eq_bot_of hA h26 hs h3 hμ hβ hν (by rwa [inf_comm])
        (by rwa [Subgroup.commutator_comm]) h
  set W := ⨆ (ν : Geo H M) (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥), Vn ν with hW
  have hWW : W = ⨆ (ν : Geo H M) (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn μ⁆ = ⊥), Vn ν := by
    apply le_antisymm
    · exact iSup₂_le fun ν hν => le_iSup₂_of_le (f := fun (ν : Geo H M)
        (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn μ⁆ = ⊥) => Vn ν) ν ⟨hν.1, (hΩ ν hν.1).mp hν.2⟩ le_rfl
    · exact iSup₂_le fun ν hν => le_iSup₂_of_le (f := fun (ν : Geo H M)
        (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥) => Vn ν) ν ⟨hν.1, (hΩ ν hν.1).mpr hν.2⟩ le_rfl
  have hVab : IsElemAbelian 2 (Vn β) := isElemAbelian_Vn hA hb β
  have hββ : ⁅Vn β, Vn β⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => isElemAbelian_comm hVab hw hv
  have hVβW : Vn β ≤ W := le_iSup₂_of_le (f := fun (ν : Geo H M)
    (_ : ν ∈ nbrs α ∧ ⁅Vn ν, Vn β⁆ = ⊥) => Vn ν) β ⟨hβ, hββ⟩ le_rfl
  have hWC : W ≤ Cst β := iSup₂_le fun ν hν => Vn_le_Cst hA h26 hs h3 hβ hν.1 hν.2
  have hWE : W ≤ stab α ⊓ stab β := fun w hw =>
    have hwQ : w ∈ Qv β := (hWC hw).1
    ⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hwQ, pCoreOf_le 2 _ hwQ⟩
  have hNα : stab α ≤ Subgroup.normalizer (W : Set G) := by
    rw [← sup_stab_inf_eq hA h26 hs hβ hμ hY]
    refine sup_le (le_normalizer_of_conjSub_le fun g hg => conjSub_iSup_Vn_le hg.1 hg.2) ?_
    rw [hWW]
    exact le_normalizer_of_conjSub_le fun g hg => conjSub_iSup_Vn_le hg.1 hg.2
  have hNβ : stab β ≤ Subgroup.normalizer (W : Set G) := by
    obtain ⟨γ, hγ, hγα, y, hyγ, hyβ, hyQ, hyC⟩ := exists_crit_elt hA h26 hs h3 hβ
    have hCn : stab β ≤ Subgroup.normalizer (Cst β : Set G) := by
      have e : Cst β = Qv β ⊓ (stab β ⊓ Subgroup.centralizer (Vn β : Set G)) := by
        ext c
        exact ⟨fun h => ⟨h.1, pCoreOf_le 2 _ h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [e]
      exact le_normalizer_inf (le_normalizer_pCoreOf 2 _)
        (normalizer_inf_centralizer (stab_le_normalizer_Vn β))
    obtain ⟨K, hK, hKX, hKn⟩ := exists_centralizer_quotient (X := stab β) (N := Cst β)
      (Z := Vn β) (stab_le_normalizer_Vn β) hCn
    have hKQ : ¬ K ≤ pCoreOf 2 (stab β) := fun h => hyQ (h ((hK y).mpr ⟨hyβ, hyC⟩))
    have hup := sup_sylow_eq_of_normal_not_le (Or.inl rfl) (quot_stab_three hA hβv)
      (sylow_stab_inf_left hA (nbrs_symm hβ)) hKX hKn hKQ
    have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
      Sit43.le_normalizer_of_conj_mem fun k hk w hw => by
        have h1 : ⁅w, k⁆ ∈ Vn β := ((hK k).mp hk).2 w (hWC hw)
        have e : k * w * k⁻¹ = ⁅w, k⁆⁻¹ * w := by simp only [commutatorElement_def]; group
        rw [e]
        exact W.mul_mem (hVβW (Subgroup.inv_mem _ h1)) hw
    have hEW : stab β ⊓ stab α ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_of_conjSub_le fun g hg => conjSub_iSup_Vn_le hg.2 hg.1
    exact hup.trans (sup_le hKW hEW)
  have hbot := eq_bot_of_normalizes_both hA hβ hWE hNα hNβ
  exact Zv_ne_bot hA α (le_bot_iff.mp (hbot ▸ (Sit43.Zv_le_Vn hβ).trans hVβW))

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
