module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7DichFin

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod CFSG.LieType.BorelTits

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

namespace Gap7

namespace Dich

omit [Finite G] in
theorem Vst_le_Vn (δ : Geo H M) : Vst δ ≤ Vn δ :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((pCoreOf_le 2 (stab δ)).trans (stab_le_normalizer_Vn δ))

omit [Finite G] in
theorem comm_Zv_Qv_le_Vst {δ' ν : Geo H M} (hν : ν ∈ nbrs δ') : ⁅Zv ν, Qv δ'⁆ ≤ Vst δ' :=
  Subgroup.commutator_mono (Sit43.Zv_le_Vn_nbrs hν) le_rfl

theorem mem_Qv_of_centralizes (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ' ν : Geo H M} (hδ' : vtype δ' = true) (hν : ν ∈ nbrs δ') {a : G} (ha : a ∈ stab ν)
    (hc : ∀ u ∈ ⁅Zv ν, Qv δ'⁆, u * a = a * u) : a ∈ Qv ν := by
  have hνv : vtype ν = false := Sit43.vtype_false_of_adj hδ' hν
  obtain ⟨D⟩ := (hs.of_vtype_false hνv).exists_dict hA (nbrs_symm hν)
  have e : (commW orth S5Syl ⊤).map D.φ = ⁅Zv ν, Qv δ'⁆ := by
    rw [hs.comm_Qv_eq hA h26 hδ' hν, ← D.map_commW_top inf_le_left, D.bar_S]
  have h1 := (D.mem_centralizer_map_iff (commW orth S5Syl ⊤) ⟨a, ha⟩).mp
    (by rw [e]; exact Subgroup.mem_centralizer_iff.mpr hc)
  exact (D.ker_iff ⟨a, ha⟩).mp (eq_one_of_fix_commW _ h1)

end Dich

end Gap7

open Gap7.Dich in
theorem not_Vst_le_Qv_and (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {ρ δ δ' : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (hδ' : δ' ∈ nbrs ρ) (hY : Yv δ ⊓ Yv δ' = ⊥) : ¬ (Vst δ ≤ Qv δ' ∧ Vst δ' ≤ Qv δ) := by
  rintro ⟨h1, h2⟩
  have hb : 3 ≤ bMin H M := h3.ge
  have hδv := Sit43.vtype_true_of_adj hρ hδ
  have hδ'v := Sit43.vtype_true_of_adj hρ hδ'
  have hst : ∀ {ε ε' : Geo H M}, ε ∈ nbrs ρ → ε' ∈ nbrs ρ → Vst ε ≤ Qv ε' → Vst ε ≤ Qst ε' :=
    fun hε hε' h v hv => ⟨h hv, Subgroup.centralizer_le (Yv_le_Zv (nbrs_symm hε'))
      (Qv_le_centralizer_Zv hA ρ (hs.Vn_le_Qv_of_nbr hA h26 hb hρ hε (Vst_le_Vn _ hv)))⟩
  have hcomm : ⁅Vst δ, Vst δ'⁆ = ⊥ := by
    have e1 : ⁅Vst δ, Vst δ'⁆ ≤ Yv δ := by
      rw [← hs.comm_Vn_Qst hA h26 hδv (nbrs_symm hδ)]
      exact Subgroup.commutator_mono (Vst_le_Vn δ) (hst hδ' hδ h2)
    have e2 : ⁅Vst δ, Vst δ'⁆ ≤ Yv δ' := by
      rw [Subgroup.commutator_comm, ← hs.comm_Vn_Qst hA h26 hδ'v (nbrs_symm hδ')]
      exact Subgroup.commutator_mono (Vst_le_Vn δ') (hst hδ hδ' h1)
    exact le_bot_iff.mp (hY ▸ le_inf e1 e2)
  have hcen : Vst δ ≤ Subgroup.centralizer (Vst δ' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hQ : ∀ ν ∈ nbrs δ', Vst δ ≤ Qv ν := fun ν hν a ha =>
    mem_Qv_of_centralizes hA h26 hs hδ'v hν (Qv_le_stab_of_mem_nbrs hA hν (h1 ha))
      fun u hu => Subgroup.mem_centralizer_iff.mp (hcen ha) u (comm_Zv_Qv_le_Vst hν hu)
  have hVc : Vn δ' ≤ Subgroup.centralizer (Vst δ : Set G) :=
    iSup₂_le fun ν hν z hz => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA ν (hQ ν hν ha)) z hz).symm
  obtain ⟨x, hxV, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_Vn_le_Qv_of_Yv_inf hA h26 (hs.of_vtype_false hρ) h3 hδ hδ' hY)
  have hxρ : x ∈ Qv ρ := hs.Vn_le_Qv_of_nbr hA h26 hb hρ hδ' hxV
  have hxδ : x ∈ stab δ := Qv_le_stab_of_mem_nbrs hA hδ hxρ
  obtain ⟨l, l', h29⟩ := hs.exists_sit29 hA h26 hδv (nbrs_symm hδ)
  have hsw := h29.smul_swap ⟨x, stab_le δ hxδ⟩ (pCoreOf_le 2 _ hxρ) hxδ hxQ
  have hUZ : ⁅Zv l, Qv δ⁆ ≤ Zv l := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Qv_le_stab_of_mem_nbrs hA h29.n₂).trans (stab_le_normalizer_Zv hA l))
  have hxU : conjSub x ⁅Zv l, Qv δ⁆ = ⁅Zv l, Qv δ⁆ := Three.conjSub_eq_self fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (hVc hxV) u (comm_Zv_Qv_le_Vst h29.n₂ hu)).symm
  have hUY := hs.le_Yv_of_normalizes hA h26 hδv h29.n₂ hUZ hxδ
    (fun h => h29.ne₂₃ (h.symm.trans hsw.1)) hxU
  have h8 := hs.card_comm_Qv hA h26 hδv h29.n₂
  have h4 := hs.card_Yv hA h26 hδv
  have hle := Subgroup.card_le_of_le hUY
  omega

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
