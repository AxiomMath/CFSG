module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem four_le_relIndex_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {g : G}
    (hg : g ∈ stab δ) (hmov : (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ≠ l) :
    4 ≤ (Yv δ).relIndex (⁅Vn δ, Subgroup.zpowers g⁆ ⊔ Yv δ) := by
  classical
  have hV : IsElemAbelian 2 (Vn δ) := isElemAbelian_Vn hA hb δ
  have hcomm : ∀ x ∈ Vn δ, ∀ y ∈ Vn δ, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hV hx hy
  have hZV : Zv l ≤ Vn δ :=
    le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) l hl le_rfl
  have hYZ : Yv δ ≤ Zv l := Yv_le_Zv hl
  have hYV : Yv δ ≤ Vn δ := hYZ.trans hZV
  have hgV : g ∈ Subgroup.normalizer (Vn δ : Set G) := stab_le_normalizer_Vn δ hg
  have hgY : g ∈ Subgroup.normalizer (Yv δ : Set G) := hs.stab_le_normalizer_Yv hA h26 hδ hg
  have hcommV : ⁅Vn δ, Subgroup.zpowers g⁆ ≤ Vn δ := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    have hxn : x ∈ Subgroup.normalizer (Vn δ : Set G) :=
      (Subgroup.zpowers_le.mpr hgV) hx
    have h1 : x * v⁻¹ * x⁻¹ ∈ Vn δ := (Subgroup.mem_normalizer_iff.mp hxn v⁻¹).mp
      ((Vn δ).inv_mem hv)
    have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact (Vn δ).mul_mem hv h1
  set A := ⁅Vn δ, Subgroup.zpowers g⁆ ⊔ Yv δ with hA'
  have hAV : A ≤ Vn δ := sup_le hcommV hYV
  have hmemA : ∀ z : ↥(Zv l), ⁅(z : G), g⁆ ∈ A := fun z =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (hZV z.2)
      (Subgroup.mem_zpowers g))
  have hmemV : ∀ z : ↥(Zv l), ⁅(z : G), g⁆ ∈ Vn δ := fun z => hAV (hmemA z)
  let f : ↥(Zv l) →* ↥A :=
    { toFun := fun z => ⟨⁅(z : G), g⁆, hmemA z⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun z z' => Subtype.ext (by
        show ⁅((z : G) * z'), g⁆ = ⁅(z : G), g⁆ * ⁅(z' : G), g⁆
        have hc := hcomm _ (hZV z.2) _ (hmemV z')
        have e : ⁅((z : G) * z'), g⁆ = (z : G) * ⁅(z' : G), g⁆ * (z : G)⁻¹ * ⁅(z : G), g⁆ := by
          simp only [commutatorElement_def]; group
        have h1 : (z : G) * ⁅(z' : G), g⁆ * (z : G)⁻¹ = ⁅(z' : G), g⁆ := by
          rw [hc]; group
        rw [e, h1]
        exact hcomm _ (hmemV z') _ (hmemV z)) }
  have hnorm : (Yv δ).subgroupOf A |>.Normal := ⟨fun n hn x => by
    have h1 : (x : G) * (n : G) = (n : G) * (x : G) := hcomm _ (hAV x.2) _ (hAV n.2)
    have : x * n * x⁻¹ = n := by
      apply Subtype.ext
      show (x : G) * n * (x : G)⁻¹ = n
      rw [h1]; group
    rw [this]; exact hn⟩
  let ψ : ↥(Zv l) →* ↥A ⧸ (Yv δ).subgroupOf A := (QuotientGroup.mk' _).comp f
  have hker : ψ.ker = (Yv δ).subgroupOf (Zv l) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (f z) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show ⁅(z : G), g⁆ ∈ Yv δ ↔ (z : G) ∈ Yv δ
    have e : ⁅(z : G), g⁆ = (z : G) * (g * (z : G)⁻¹ * g⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    constructor
    · intro h
      have hgl : (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ∈ nbrs δ := by
        have := (smul_mem_nbrs_iff (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) (l := δ) (δ := l)).mpr hl
        rwa [smul_eq_of_mem_stab
          (show ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) : G) ∈ stab δ from hg)] at this
      have hYg : Yv δ ≤ Zv ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l) := Yv_le_Zv hgl
      have hzg : g * (z : G)⁻¹ * g⁻¹ ∈ Zv ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l) := by
        rw [← S29.Sit29.Zv_conj (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) l]
        exact mul_mem_conjSub ((Zv l).inv_mem z.2)
      have h2 : (z : G) ∈ Zv ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l) := by
        have h3 : (z : G) = ((z : G) * (g * (z : G)⁻¹ * g⁻¹)) * (g * (z : G) * g⁻¹) := by group
        rw [h3, ← e]
        refine Subgroup.mul_mem _ (hYg h) ?_
        rw [← S29.Sit29.Zv_conj (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) l]
        exact mul_mem_conjSub z.2
      rw [← hs.inf_Zv_eq_Yv hA h26 hδ hl hgl (Ne.symm hmov)]
      exact ⟨z.2, h2⟩
    · intro h
      rw [e]
      have : g * (z : G)⁻¹ * g⁻¹ ∈ Yv δ :=
        (Subgroup.mem_normalizer_iff.mp hgY _).mp ((Yv δ).inv_mem h)
      exact (Yv δ).mul_mem h this
  have h1 : (ψ.ker).index = 4 := by
    rw [hker]
    show (Yv δ).relIndex (Zv l) = 4
    have h2 := Subgroup.relIndex_mul_card (Yv δ) (Zv l)
    rw [inf_eq_left.mpr hYZ, hs.card_Yv hA h26 hδ, hs.card_Zv_false
      (vtype_false_of_adj hδ hl)] at h2
    omega
  have h2 := Subgroup.index_ker ψ
  rw [h1] at h2
  have h3 := Subgroup.card_subgroup_dvd_card ψ.range
  rw [← h2] at h3
  have h4 : (Yv δ).relIndex A = Nat.card (↥A ⧸ (Yv δ).subgroupOf A) := by
    unfold Subgroup.relIndex; exact Subgroup.index_eq_card _
  rw [h4]
  exact Nat.le_of_dvd Nat.card_pos h3

theorem Zv_le_Qv_crit_nbr (hA : F53Amalgam H M S) (hs : Sit43 α) {α' ν : Geo H M}
    (hν : ν ∈ nbrs α') (hd : dist α ν < bMin H M) :
    Zv α ≤ Qv ν ∧ Qv ν ≤ stab α' ⊓ stab ν := by
  refine ⟨hs.Zv_le_Qv_of_dist_lt_false hs.vα hd, ?_⟩
  rw [inf_comm]
  exact Qv_le_edge hA (nbrs_symm hν)

theorem claim2b (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) (hb : 3 ≤ bMin H M)
    {δ : Geo H M} (hδ : vtype δ = true) {g : G} (hg : g ∈ stab δ) (hgQ : g ∉ Qv δ) :
    4 ≤ (Yv δ).relIndex (⁅Vn δ, Subgroup.zpowers g⁆ ⊔ Yv δ) := by
  have hmov : ∃ l ∈ nbrs δ, (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ≠ l := by
    by_contra hcon
    push Not at hcon
    apply hgQ
    rw [Qv_eq_iInf hA δ]
    exact Subgroup.mem_iInf.mpr fun w => Subgroup.mem_iInf.mpr fun hw =>
      ⟨hg, mem_stab_of_smul_eq (hcon w hw)⟩
  obtain ⟨l, hl, hl'⟩ := hmov
  exact hs.four_le_relIndex_comm hA h26 hb hδ hl hg hl'

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
