module

public import CFSG.Quasithin.H13.AS91Sec8FixOct
public import CFSG.Quasithin.H13.AS91Sec5Todd
public import CFSG.Quasithin.H13.AS91Sec8Perm3
public import CFSG.Quasithin.H13.AS91Sec8FourPt

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code MulAction
open scoped Pointwise commutatorElement

theorem mem_smul_finset_iff_of_smul_eq {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    {s : Finset α} {δ : G} (hδ : δ • s = s) (x : α) : x ∈ s ↔ δ • x ∈ s := by
  constructor
  · intro hx
    have h' : δ • x ∈ δ • s := Finset.smul_mem_smul_finset (a := δ) hx
    rwa [hδ] at h'
  · intro hx
    have h' : δ • x ∈ δ • s := by rwa [hδ]
    rw [Finset.mem_smul_finset] at h'
    obtain ⟨y, hy, hxy⟩ := h'
    have hyx : y = x := by
      have := congrArg (fun z => δ⁻¹ • z) hxy
      simpa using this
    rwa [hyx] at hy

@[expose] noncomputable def finsetStabilizerAction {G α : Type*} [Group G] [MulAction G α]
    [DecidableEq α] (s : Finset α) : MulAction.stabilizer G s →* Equiv.Perm ↥s where
  toFun g :=
    { toFun := fun O => ⟨(g : G) • (O : α), (mem_smul_finset_iff_of_smul_eq g.2 O).mp O.2⟩
      invFun := fun O =>
        ⟨(g : G)⁻¹ • (O : α), by
          have hinv : (g : G)⁻¹ • s = s := by
            have h : (g : G)⁻¹ • ((g : G) • s) = (g : G)⁻¹ • s := by rw [g.2]
            have h' : s = (g : G)⁻¹ • s := by simpa using h
            exact h'.symm
          exact (mem_smul_finset_iff_of_smul_eq hinv O).mp O.2⟩
      left_inv := fun O => Subtype.ext (by simp)
      right_inv := fun O => Subtype.ext (by simp) }
  map_one' := by ext O; simp
  map_mul' _ _ := by ext O; simp [mul_smul]

theorem finsetStabilizerAction_apply_coe {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    (s : Finset α) (g : MulAction.stabilizer G s) (O : ↥s) :
    ((finsetStabilizerAction s g O : ↥s) : α) = (g : G) • (O : α) := rfl

theorem mem_ker_finsetStabilizerAction {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    (s : Finset α) {g : MulAction.stabilizer G s} :
    g ∈ (finsetStabilizerAction s).ker ↔ ∀ O ∈ s, (g : G) • O = O := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h O hO
    have := congrArg (fun σ : Equiv.Perm ↥s => ((σ ⟨O, hO⟩ : ↥s) : α)) h
    simpa [finsetStabilizerAction_apply_coe] using this
  · intro h
    ext O
    rw [finsetStabilizerAction_apply_coe]
    simpa using h O O.2

theorem fixOct_smul {l : Finset (Finset (Fin 24))} {σ : S24} (hσ : σ ∈ fixOct l) :
    σ • l = l := by
  rw [Finset.smul_finset_def]
  ext O
  rw [Finset.mem_image]
  constructor
  · rintro ⟨O', hO', rfl⟩
    rw [(mem_fixOct.mp hσ).2 O' hO']
    exact hO'
  · intro hO
    exact ⟨O, hO, (mem_fixOct.mp hσ).2 O hO⟩

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem G12_le_G1 : c.G12 ≤ c.G1 := by
  rw [c.G12_eq]; exact inf_le_right

theorem G12_le_G2 : c.G12 ≤ c.G2 := by
  rw [c.G12_eq]; exact inf_le_left

theorem E_le_G12 : c.E ≤ c.G12 := by
  rw [c.G12_eq]; exact le_inf c.E_le_G2 c.E_le_G1

theorem K_le_G12 : c.K ≤ c.G12 := c.K_le

theorem G12_eq_inf : c.G12 = c.G1 ⊓ c.G2 := by
  rw [c.G12_eq, inf_comm]

theorem index_K_G12 : c.K.relIndex c.G12 = 24 := by
  rw [c.G12_eq_inf]
  exact c.relIndex_K_G12

@[expose] noncomputable def resPermE : ↥c.E →* Equiv.Perm ↥c.ptsL :=
  (residuePerm c.G1 c.G2).comp (Subgroup.inclusion c.E_le_G2)

theorem resPermE_apply_val (e : ↥c.E) (p : ↥c.ptsL) :
    (c.resPermE e p : G ⧸ c.G1) = (e : G) • (p : G ⧸ c.G1) := by
  simp [resPermE, residuePerm_apply]

theorem ker_resPermE : c.resPermE.ker = (c.E ⊓ c.K).subgroupOf c.E := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hiff : c.resPermE e = 1 ↔
      ∀ p : ↥c.ptsL, (e : G) • (p : G ⧸ c.G1) = (p : G ⧸ c.G1) := by
    constructor
    · intro hh p
      have := congrArg (fun σ : Equiv.Perm ↥c.ptsL =>
        ((σ p : ↥c.ptsL) : G ⧸ c.G1)) hh
      simpa [c.resPermE_apply_val] using this
    · intro hh
      ext p
      simpa [c.resPermE_apply_val] using hh p
  rw [hiff]
  constructor
  · intro H
    refine ⟨e.2, ?_⟩
    exact (c.kernel_ptsL (e : G) (c.E_le_G2 e.2)).mp fun p hp => H ⟨p, hp⟩
  · rintro ⟨-, hk⟩ p
    exact (c.kernel_ptsL (e : G) (c.E_le_G2 e.2)).mpr hk p p.2

theorem card_E_mul_inf : Nat.card c.E = 4 * Nat.card ↥(c.E ⊓ c.K) := by
  classical
  letI : MulAction (↥c.E) (↥c.ptsL) := MulAction.compHom (↥c.ptsL) c.resPermE
  let X0 : ↥c.ptsL := ⟨c.x0, c.x0_mem_ptsL⟩
  obtain ⟨y, hy, hyx⟩ := c.exists_pt c.card_ptsL
  let Y : ↥c.ptsL := ⟨y, hy⟩
  have hYX : Y ≠ X0 := fun h => hyx (congrArg Subtype.val h)
  have hYX' : (Y : G ⧸ c.G1) ≠ c.x0 := fun h => hYX (Subtype.ext h)
  have horbit : MulAction.orbit ↥c.E Y = {p : ↥c.ptsL | p ≠ X0} := by
    ext p
    constructor
    · rintro ⟨e, rfl⟩
      intro hp
      apply hYX
      calc Y = (e⁻¹ * e) • Y := by simp
        _ = e⁻¹ • (e • Y) := by rw [mul_smul]
        _ = e⁻¹ • X0 := congrArg (fun Z => e⁻¹ • Z) hp
        _ = X0 := by
            apply Subtype.ext
            rw [MulAction.compHom_smul_def, Equiv.Perm.smul_def, c.resPermE_apply_val]
            have : ((e : ↥c.E)⁻¹ : G) ∈ stabilizer G c.x0 := by
              rw [c.stab_x0]
              exact c.E_le_G1 (inv_mem e.2)
            exact mem_stabilizer_iff.mp this
    · intro hp
      obtain ⟨e, he, hep⟩ := c.E_transitive Y.2 p.2 hYX' (fun h => hp (Subtype.ext h))
      refine ⟨(⟨e, he⟩ : ↥c.E), ?_⟩
      apply Subtype.ext
      simpa [MulAction.compHom_smul_def, Equiv.Perm.smul_def, c.resPermE_apply_val] using hep
  haveI : Fintype (↥c.ptsL) := Fintype.ofFinite _
  have hcardcompl : Nat.card {p : ↥c.ptsL // p ≠ X0} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have h5 : Fintype.card ↥c.ptsL = 5 := by
      rw [← Nat.card_eq_fintype_card]; exact c.card_ptsL
    rw [Fintype.card_subtype_eq, h5]
  have hset : ({p : ↥c.ptsL | p ≠ X0} : Set ↥c.ptsL).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcardcompl
  have hstab : MulAction.stabilizer ↥c.E Y = c.resPermE.ker := by
    ext e
    rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hey
      ext p
      have hsub : e • p = p := by
        by_cases hp : p = X0
        · subst hp
          apply Subtype.ext
          rw [MulAction.compHom_smul_def, Equiv.Perm.smul_def, c.resPermE_apply_val]
          have : (e : G) ∈ stabilizer G c.x0 := by
            rw [c.stab_x0]; exact c.E_le_G1 e.2
          exact mem_stabilizer_iff.mp this
        · obtain ⟨f, hfE, hfp⟩ := c.E_transitive Y.2 p.2 hYX' (fun h => hp (Subtype.ext h))
          let fE : ↥c.E := ⟨f, hfE⟩
          have hfY : fE • Y = p := by
            apply Subtype.ext
            simpa [MulAction.compHom_smul_def, Equiv.Perm.smul_def, c.resPermE_apply_val] using hfp
          have hcomm : e * fE = fE * e := c.E_elem.1.is_comm.comm e fE
          calc e • p = e • (fE • Y) := by rw [hfY]
            _ = (e * fE) • Y := by rw [mul_smul]
            _ = (fE * e) • Y := by rw [hcomm]
            _ = fE • (e • Y) := by rw [mul_smul]
            _ = fE • Y := by rw [hey]
            _ = p := hfY
      exact congrArg Subtype.val hsub
    · intro hfix
      have hY : c.resPermE e Y = Y := by rw [hfix]; rfl
      simpa [MulAction.compHom_smul_def, Equiv.Perm.smul_def] using hY
  have hidx : (c.resPermE.ker).index = 4 := by
    have hidx := MulAction.index_stabilizer ↥c.E Y
    rw [horbit, hset] at hidx
    rwa [hstab] at hidx
  rw [c.ker_resPermE] at hidx
  have hcard := Subgroup.card_mul_index ((c.E ⊓ c.K).subgroupOf c.E)
  rw [hidx] at hcard
  have hcardinf : Nat.card ((c.E ⊓ c.K).subgroupOf c.E) = Nat.card ↥(c.E ⊓ c.K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : c.E ⊓ c.K ≤ c.E))
  rw [hcardinf] at hcard
  rw [mul_comm] at hcard
  exact hcard.symm

theorem index_E_inf_K : (c.E ⊓ c.K).relIndex c.E = 4 := by
  change ((c.E ⊓ c.K).subgroupOf c.E).index = 4
  have h := Subgroup.relIndex_mul_card (H := c.E ⊓ c.K) (K := c.E)
  rw [inf_of_le_left (inf_le_left : c.E ⊓ c.K ≤ c.E)] at h
  change ((c.E ⊓ c.K).subgroupOf c.E).index * Nat.card ↥(c.E ⊓ c.K) = Nat.card c.E at h
  rw [c.card_E_mul_inf] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem commutator_E_K_le_inf : ⁅c.E, c.K⁆ ≤ c.E ⊓ c.K := by
  rw [Subgroup.commutator_le]
  intro e he k hk
  rw [Subgroup.mem_inf]
  constructor
  · have h2 : k * e⁻¹ * k⁻¹ ∈ c.E :=
      (Subgroup.mem_normalizer_iff.mp (c.K_le_G1 hk) e⁻¹).mp (inv_mem he)
    simpa [commutatorElement_def, mul_assoc] using mul_mem he h2
  · have h1 : e * k * e⁻¹ ∈ c.K :=
      (Subgroup.mem_normalizer_iff.mp (c.mem_normalizer_K (c.E_le_G2 he)) k).mp hk
    simpa [commutatorElement_def, mul_assoc] using mul_mem h1 (inv_mem hk)

theorem card_inf_E_K : Nat.card ↥(c.E ⊓ c.K) = 2 ^ 9 := by
  have h := c.card_E_mul_inf
  rw [c.card_E] at h
  norm_num at h ⊢
  omega

theorem le_normalizer_R_of_le_G2 {H : Subgroup G} (hH : H ≤ c.G2) :
    H ≤ normalizer (c.R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr; exact c.R_conj_G2 (hH hg) hr
  · intro hr
    have := c.R_conj_G2 (inv_mem (hH hg)) hr
    simpa [mul_assoc] using this

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

@[expose] noncomputable def preFixOct : Subgroup G :=
  ((fixOct ρ.l₀).comap ρ.φ).map c.G1.subtype

theorem mem_preFixOct {g : G} :
    g ∈ ρ.preFixOct ↔ ∃ h : g ∈ c.G1, ρ.φ ⟨g, h⟩ ∈ fixOct ρ.l₀ := by
  rw [preFixOct, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hgh⟩
    subst hgh
    exact ⟨h.2, hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨g, h⟩, hh, rfl⟩

theorem preFixOct_le_G1 : ρ.preFixOct ≤ c.G1 := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hg
  exact h.2

theorem preFixOct_le_G12 : ρ.preFixOct ≤ c.G12 := by
  intro g hg
  obtain ⟨hg1, hfix⟩ := ρ.mem_preFixOct.mp hg
  rw [c.G12_eq]
  exact Subgroup.mem_inf.mpr ⟨(ρ.stab₂ ⟨g, hg1⟩).mpr (fixOct_smul hfix), hg1⟩

theorem E_le_preFixOct : c.E ≤ ρ.preFixOct := by
  intro e he
  rw [mem_preFixOct]
  refine ⟨c.E_le_G1 he, ?_⟩
  have hker : ρ.φ ⟨e, c.E_le_G1 he⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ρ.ker_eq, Subgroup.mem_subgroupOf]
    exact he
  rw [hker]
  exact (fixOct ρ.l₀).one_mem

theorem card_l₀ : Nat.card ↥ρ.l₀ = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, ρ.isTrio_l₀.1]

@[expose] noncomputable def φG12 : ↥c.G12 →* MulAction.stabilizer S24 ρ.l₀ :=
  (ρ.φ.comp (Subgroup.inclusion c.G12_le_G1)).codRestrict _
    fun h => (ρ.stab₂ ⟨h, c.G12_le_G1 h.2⟩).mp (c.G12_le_G2 h.2)

@[expose] noncomputable def octadPerm : ↥c.G12 →* Equiv.Perm ↥ρ.l₀ :=
  (finsetStabilizerAction ρ.l₀).comp (φG12 ρ)

theorem φG12_apply (h : ↥c.G12) :
    (ρ.φG12 h : S24) = ρ.φ ⟨h, c.G12_le_G1 h.2⟩ := rfl

theorem octadPerm_apply_coe (h : ↥c.G12) (O : ↥ρ.l₀) :
    ((ρ.octadPerm h O : ↥ρ.l₀) : Finset (Fin 24)) =
      ρ.φ ⟨h, c.G12_le_G1 h.2⟩ • (O : Finset (Fin 24)) := rfl

theorem ker_octadPerm : ρ.octadPerm.ker = ρ.preFixOct.subgroupOf c.G12 := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ρ.mem_preFixOct]
  have h1 : ρ.octadPerm h = 1 ↔ ρ.φ ⟨h, c.G12_le_G1 h.2⟩ ∈ fixOct ρ.l₀ := by
    change finsetStabilizerAction ρ.l₀ (ρ.φG12 h) = 1 ↔ _
    rw [← MonoidHom.mem_ker, mem_ker_finsetStabilizerAction, mem_fixOct]
    constructor
    · intro hh
      exact ⟨ρ.φ_mem _, by simpa [φG12_apply] using hh⟩
    · rintro ⟨-, hh⟩ O hO
      simpa [φG12_apply] using hh O hO
  rw [h1]
  constructor
  · intro hfix
    exact ⟨c.G12_le_G1 h.2, hfix⟩
  · rintro ⟨_, hfix⟩
    exact hfix

theorem octadPerm_surjective (hS : FixOctSym) : Function.Surjective ρ.octadPerm := by
  intro π
  obtain ⟨σ, hσM, hσ⟩ := hS ρ.l₀ ρ.isTrio_l₀ π
  have hσl : σ • ρ.l₀ = ρ.l₀ := by
    rw [Finset.smul_finset_def]
    ext O
    rw [Finset.mem_image]
    constructor
    · rintro ⟨O', hO', rfl⟩
      rw [hσ ⟨O', hO'⟩]
      exact (π ⟨O', hO'⟩).2
    · intro hO
      refine ⟨(π.symm ⟨O, hO⟩ : ↥ρ.l₀), (π.symm ⟨O, hO⟩).2, ?_⟩
      simpa using hσ (π.symm ⟨O, hO⟩)
  obtain ⟨h, hhφ⟩ := ρ.exists_φ_eq hσM
  have hhG2 : (h : G) ∈ c.G2 := (ρ.stab₂ h).mpr (hhφ ▸ hσl)
  let h12 : ↥c.G12 := ⟨h, by rw [c.G12_eq]; exact ⟨hhG2, h.2⟩⟩
  refine ⟨h12, ?_⟩
  apply Equiv.ext
  intro O
  apply Subtype.ext
  rw [octadPerm_apply_coe]
  have hφ : ρ.φ ⟨(h12 : G), c.G12_le_G1 h12.2⟩ = σ := by simpa using hhφ
  rw [hφ]
  exact hσ O

theorem index_preFixOct (hS : FixOctSym) :
    (ρ.preFixOct.subgroupOf c.G12).index = 6 := by
  have h := Subgroup.index_ker ρ.octadPerm
  rw [ρ.ker_octadPerm, MonoidHom.range_eq_top.mpr (ρ.octadPerm_surjective hS),
    Subgroup.card_top, Nat.card_perm, ρ.card_l₀] at h
  norm_num at h ⊢
  exact h

@[expose] noncomputable def φK : ↥c.K →* S24 :=
  ρ.φ.comp (Subgroup.inclusion c.K_le_G1)

theorem φK_range_map : ρ.φK.range = (c.K.subgroupOf c.G1).map ρ.φ := by
  ext σ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, c.K_le_G1 k.2⟩, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩

theorem K_le_preFixOct (hS : FixOctSym) : c.K ≤ ρ.preFixOct := by
  classical
  have hRpre : c.R ≤ ρ.preFixOct := by
    let Rψ : Subgroup (Equiv.Perm ↥ρ.l₀) :=
      (c.R.subgroupOf c.G12).map ρ.octadPerm
    have hRsub_normal : (c.R.subgroupOf c.G12).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (c.R_le_K.trans c.K_le_G12)).2
        (c.le_normalizer_R_of_le_G2 c.G12_le_G2)
    have hRψ_normal : Rψ.Normal :=
      hRsub_normal.map ρ.octadPerm (ρ.octadPerm_surjective hS)
    have hRψ_pgroup : IsPGroup 2 Rψ := by
      have hR2 : IsPGroup 2 ↥(c.R.subgroupOf c.G12) := by
        refine IsPGroup.of_card (n := 15) ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (c.R_le_K.trans c.K_le_G12)).toEquiv, c.card_R]
      exact hR2.map ρ.octadPerm
    have hcard3 : Fintype.card ↥ρ.l₀ = 3 := by
      rw [← Nat.card_eq_fintype_card]; exact ρ.card_l₀
    have hRψ_eq_bot : Rψ = ⊥ := perm3_eq_bot_of_normal_pGroup hcard3 Rψ hRψ_pgroup
    intro r hr
    have hrG12 : r ∈ c.G12 := c.K_le_G12 (c.R_le_K hr)
    have himg : ρ.octadPerm ⟨r, hrG12⟩ ∈ Rψ :=
      Subgroup.mem_map_of_mem ρ.octadPerm (Subgroup.mem_subgroupOf.mpr hr)
    rw [hRψ_eq_bot, Subgroup.mem_bot] at himg
    have hk : (⟨r, hrG12⟩ : ↥c.G12) ∈ ρ.octadPerm.ker := himg
    rw [ρ.ker_octadPerm, Subgroup.mem_subgroupOf] at hk
    exact hk
  let ψK : ↥c.K →* Equiv.Perm ↥ρ.l₀ := ρ.octadPerm.comp (Subgroup.inclusion c.K_le_G12)
  have hRker : c.R.subgroupOf c.K ≤ ψK.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    change ρ.octadPerm ⟨(r : G), c.K_le_G12 r.2⟩ = 1
    have hrR : (r : G) ∈ c.R := Subgroup.mem_subgroupOf.mp hr
    have hpre : (r : G) ∈ ρ.preFixOct := hRpre hrR
    have hk : (⟨(r : G), c.K_le_G12 r.2⟩ : ↥c.G12) ∈ ρ.octadPerm.ker := by
      rw [ρ.ker_octadPerm, Subgroup.mem_subgroupOf]
      exact hpre
    exact MonoidHom.mem_ker.mp hk
  haveI hRnormK : (c.R.subgroupOf c.K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.R_le_K).2
      (c.le_normalizer_R_of_le_G2 c.K_le_G2)
  let ψbar : (↥c.K ⧸ c.R.subgroupOf c.K) →* Equiv.Perm ↥ρ.l₀ :=
    QuotientGroup.lift (c.R.subgroupOf c.K) ψK hRker
  have hsimple : IsSimpleGroup (↥c.K ⧸ c.R.subgroupOf c.K) := by
    obtain ⟨φ₀, hφ₀surj, hφ₀ker⟩ := c.K_quot
    have e : (↥c.K ⧸ c.R.subgroupOf c.K) ≃*
        Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq hφ₀ker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective φ₀ hφ₀surj)
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    exact MulEquiv.isSimpleGroup e
  haveI : ψbar.ker.Normal := MonoidHom.normal_ker ψbar
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψbar.ker with hbot | htop
  · exfalso
    have hinj : Function.Injective ψbar := (MonoidHom.ker_eq_bot_iff ψbar).mp hbot
    have hcardKbar : Nat.card (↥c.K ⧸ c.R.subgroupOf c.K) = 168 := by
      rw [← Subgroup.index_eq_card, c.index_R_K]
    have hcardPerm : Nat.card (Equiv.Perm ↥ρ.l₀) = 6 := by
      rw [Nat.card_perm, ρ.card_l₀]; norm_num
    have hle := Nat.card_le_card_of_injective ψbar hinj
    rw [hcardKbar, hcardPerm] at hle
    norm_num at hle
  · intro k hk
    let kK : ↥c.K := ⟨k, hk⟩
    have hkker : (QuotientGroup.mk' (c.R.subgroupOf c.K)) kK ∈ ψbar.ker := by
      rw [htop]; exact Subgroup.mem_top _
    have hψk : ψK kK = 1 := by
      rw [← QuotientGroup.lift_mk' (c.R.subgroupOf c.K) hRker kK]
      exact MonoidHom.mem_ker.mp hkker
    have hkpre : (⟨k, c.K_le_G12 hk⟩ : ↥c.G12) ∈ ρ.octadPerm.ker := by
      rw [MonoidHom.mem_ker]
      change ρ.octadPerm ⟨(kK : G), c.K_le_G12 hk⟩ = 1
      exact hψk
    rw [ρ.ker_octadPerm, Subgroup.mem_subgroupOf] at hkpre
    exact hkpre

theorem preFixOct_eq_sup (hS : FixOctSym) : ρ.preFixOct = c.K ⊔ c.E := by
  have hle : c.K ⊔ c.E ≤ ρ.preFixOct := sup_le (ρ.K_le_preFixOct hS) ρ.E_le_preFixOct
  have h4 : c.K.relIndex c.E = 4 := by
    change ((c.K).subgroupOf c.E).index = 4
    have hsub : (c.E ⊓ c.K).subgroupOf c.E = c.K.subgroupOf c.E := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← hsub]
    exact c.index_E_inf_K
  have hKE : c.K.relIndex (c.K ⊔ c.E) = 4 := by
    haveI : (c.K.subgroupOf c.G12).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.K_le_G12).2
        (fun g hg => c.mem_normalizer_K (c.G12_le_G2 hg))
    have h2 := Subgroup.relIndex_sup_right (H := c.E.subgroupOf c.G12)
      (K := c.K.subgroupOf c.G12)
    rw [← Subgroup.subgroupOf_sup c.E_le_G12 c.K_le_G12,
      Subgroup.relIndex_subgroupOf c.E_le_G12] at h2
    have h2' : (c.K.subgroupOf c.G12).relIndex
        ((c.E ⊔ c.K).subgroupOf c.G12) = 4 := by
      rw [h2, h4]
    have h1 := Subgroup.relIndex_subgroupOf (H := c.K) (K := c.E ⊔ c.K) (L := c.G12)
      (sup_le c.E_le_G12 c.K_le_G12)
    calc c.K.relIndex (c.K ⊔ c.E) = c.K.relIndex (c.E ⊔ c.K) := by rw [sup_comm]
      _ = (c.K.subgroupOf c.G12).relIndex ((c.E ⊔ c.K).subgroupOf c.G12) := h1.symm
      _ = 4 := h2'
  have hsupidx : (c.K ⊔ c.E).relIndex c.G12 = 6 := by
    have h := Subgroup.relIndex_mul_relIndex (H := c.K) (K := c.K ⊔ c.E) (L := c.G12)
      le_sup_left (sup_le c.K_le_G12 c.E_le_G12)
    rw [c.index_K_G12, hKE] at h
    omega
  have hcard : Nat.card ↥ρ.preFixOct = Nat.card ↥(c.K ⊔ c.E) := by
    have h1 := Subgroup.card_mul_index (ρ.preFixOct.subgroupOf c.G12)
    have h2 := Subgroup.card_mul_index ((c.K ⊔ c.E).subgroupOf c.G12)
    have hpre : Nat.card ↥(ρ.preFixOct.subgroupOf c.G12) = Nat.card ↥ρ.preFixOct :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ρ.preFixOct_le_G12).toEquiv
    have hsup : Nat.card ↥((c.K ⊔ c.E).subgroupOf c.G12) =
        Nat.card ↥(c.K ⊔ c.E) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (sup_le c.K_le_G12 c.E_le_G12)).toEquiv
    rw [hpre, ρ.index_preFixOct hS] at h1
    rw [hsup] at h2
    change Nat.card ↥(c.K ⊔ c.E) *
      (c.K ⊔ c.E).relIndex c.G12 = Nat.card ↥c.G12 at h2
    rw [hsupidx] at h2
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem exists_mul_of_mem_preFixOct (hPE : ρ.preFixOct = c.K ⊔ c.E) {x : G}
    (hx : x ∈ ρ.preFixOct) : ∃ k ∈ c.K, ∃ e ∈ c.E, x = k * e := by
  have hKP : c.K ≤ ρ.preFixOct := by rw [hPE]; exact le_sup_left
  have hEP : c.E ≤ ρ.preFixOct := by rw [hPE]; exact le_sup_right
  haveI : (c.K.subgroupOf ρ.preFixOct).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2
      (fun g hg => c.mem_normalizer_K (c.G12_le_G2 (ρ.preFixOct_le_G12 hg)))
  have hsup : (c.K.subgroupOf ρ.preFixOct) ⊔ (c.E.subgroupOf ρ.preFixOct) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKP hEP, hPE]
    exact Subgroup.subgroupOf_eq_top.mpr le_rfl
  have hxP : (⟨x, hx⟩ : ↥ρ.preFixOct) ∈
      (c.K.subgroupOf ρ.preFixOct) ⊔ (c.E.subgroupOf ρ.preFixOct) := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨k, hk, e, he, hke⟩ := Subgroup.mem_sup_of_normal_left.mp hxP
  refine ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, (e : G), Subgroup.mem_subgroupOf.mp he, ?_⟩
  exact (congrArg Subtype.val hke).symm

theorem subgroupOf_preFixOct_eq_comap :
    ρ.preFixOct.subgroupOf c.G1 = (fixOct ρ.l₀).comap ρ.φ := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, ρ.mem_preFixOct]
  constructor
  · rintro ⟨hh, hfix⟩; exact hfix
  · intro hfix; exact ⟨h.2, hfix⟩

theorem map_φ_E_eq_bot : (c.E.subgroupOf c.G1).map ρ.φ = ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  intro e he
  have hmem : e ∈ ρ.φ.ker := by
    rw [ρ.ker_eq]
    exact Subgroup.mem_subgroupOf.mp he
  exact MonoidHom.mem_ker.mp hmem

theorem φK_range (hS : FixOctSym) : ρ.φK.range = fixOct ρ.l₀ := by
  have hPE := ρ.preFixOct_eq_sup hS
  have hmap_pre : (ρ.preFixOct.subgroupOf c.G1).map ρ.φ = fixOct ρ.l₀ := by
    rw [ρ.subgroupOf_preFixOct_eq_comap, Subgroup.map_comap_eq, ρ.range_eq,
      inf_eq_right.mpr (fixOct_le_M24g ρ.l₀)]
  have hmap_sup : ((c.K ⊔ c.E).subgroupOf c.G1).map ρ.φ = fixOct ρ.l₀ := by
    rw [← hPE]; exact hmap_pre
  rw [Subgroup.subgroupOf_sup c.K_le_G1 c.E_le_G1, Subgroup.map_sup,
    ρ.map_φ_E_eq_bot, sup_bot_eq] at hmap_sup
  rw [ρ.φK_range_map]; exact hmap_sup

end ResM24

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (r : ResM24T c)

theorem commutator_E_K_ge_inf (r : ResM24T c) (hS : FixOctSym) (hW : FixOctCommW11) :
    c.E ⊓ c.K ≤ ⁅c.E, c.K⁆ := by
  classical
  let commEA : Subgroup G := ⁅c.E, c.K⁆
  have hcommE : commEA ≤ c.E := c.commutator_E_K_le_inf.trans inf_le_left
  let C : Subgroup ↥c.E := commEA.subgroupOf c.E
  have hCcard : Nat.card ↥C = Nat.card ↥commEA :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommE).toEquiv
  let Sset : Set W11 := {x | ∃ (w : W11) (σ : ↥AutPerm),
    (σ : S24) ∈ fixOct r.l₀ ∧ x = w * (rho11 AutPerm le_rfl σ w)⁻¹}
  have hWl : 2 ^ 9 ≤ Nat.card ↥(Subgroup.closure Sset) := hW r.l₀ r.isTrio_l₀
  have hTle : Subgroup.closure Sset ≤ C.map r.todd.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨w, σ, hσfix, rfl⟩ := hx
    have hσrange : (σ : S24) ∈ (r.toResM24.φK).range := by
      rw [r.toResM24.φK_range hS]
      exact hσfix
    obtain ⟨k, hkφ⟩ := MonoidHom.mem_range.mp hσrange
    let e : ↥c.E := r.todd.symm w
    have hew : r.todd e = w := r.todd.apply_symm_apply w
    let ke : ↥c.E := ⟨(k : G) * (e : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (c.K_le_G1 k.2) e).mp e.2⟩
    let z : ↥c.E := ⟨(e : G) * (ke : G)⁻¹, mul_mem e.2 (inv_mem ke.2)⟩
    have hzval : (z : G) = ⁅(e : G), (k : G)⁆ := by
      simp only [z, ke, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hzC : z ∈ C := by
      rw [Subgroup.mem_subgroupOf]
      rw [hzval]
      exact Subgroup.commutator_mem_commutator e.2 k.2
    have hke : r.todd ke = rho11 AutPerm le_rfl σ (r.todd e) := by
      have h := r.todd_equiv ⟨k, c.K_le_G1 k.2⟩ e
      have hσeq : (⟨r.φ ⟨k, c.K_le_G1 k.2⟩, r.φ_mem _⟩ : ↥AutPerm) = σ := by
        apply Subtype.ext
        have hcoe : Subgroup.inclusion c.K_le_G1 k =
            (⟨(k : G), c.K_le_G1 k.2⟩ : ↥c.G1) := rfl
        rw [← hcoe]
        simpa [ResM24.φK] using hkφ
      rw [hσeq] at h
      simpa [ke] using h
    have hztodd : r.todd z = w * (rho11 AutPerm le_rfl σ w)⁻¹ := by
      have hz : r.todd z = r.todd e * (r.todd ke)⁻¹ := by
        change r.todd (e * ke⁻¹) = _
        rw [map_mul, map_inv]
      rw [hz, hke, hew]
    refine Subgroup.mem_map.mpr ⟨z, hzC, ?_⟩
    change r.todd z = _
    exact hztodd
  have hTcard : Nat.card ↥(Subgroup.closure Sset) ≤ Nat.card ↥commEA := by
    calc Nat.card ↥(Subgroup.closure Sset) ≤ Nat.card ↥(C.map r.todd.toMonoidHom) :=
          Subgroup.card_le_of_le hTle
      _ = Nat.card ↥C := Subgroup.card_map_of_injective r.todd.injective
      _ = Nat.card ↥commEA := hCcard
  have hcommcard : 2 ^ 9 ≤ Nat.card ↥commEA := le_trans hWl hTcard
  have hle : commEA ≤ c.E ⊓ c.K := c.commutator_E_K_le_inf
  have hcard : Nat.card ↥(c.E ⊓ c.K) ≤ Nat.card ↥commEA := by
    rw [c.card_inf_E_K]; exact hcommcard
  rw [show c.E ⊓ c.K = commEA from (Subgroup.eq_of_le_of_card_ge hle hcard).symm]

theorem commutator_E_K_eq (r : ResM24T c) (hS : FixOctSym) (hW : FixOctCommW11) :
    ⁅c.E, c.K⁆ = c.E ⊓ c.K :=
  le_antisymm c.commutator_E_K_le_inf (commutator_E_K_ge_inf r hS hW)

theorem K_eq_commutator_sup (r : ResM24T c) (hS : FixOctSym) (hP : FixOctPerfect) :
    c.K = ⁅c.K, c.K⁆ ⊔ (c.E ⊓ c.K) := by
  apply le_antisymm
  · intro k hk
    let A : Subgroup ↥c.G1 := c.K.subgroupOf c.G1
    let B : Subgroup ↥c.G1 := ⁅A, A⁆
    have hBmap : B.map r.φ = fixOct r.l₀ := by
      have hmapA : A.map r.φ = fixOct r.l₀ := by
        rw [← r.φK_range_map]
        exact r.φK_range hS
      rw [show B = ⁅A, A⁆ from rfl, Subgroup.map_commutator, hmapA,
        hP r.l₀ r.isTrio_l₀]
    have hBA : B ≤ A := by
      rw [Subgroup.commutator_le]
      intro a ha b' hb'
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha hb') (A.inv_mem ha)) (A.inv_mem hb')
    let kg : ↥c.G1 := ⟨k, c.K_le_G1 hk⟩
    have hφkg : r.φ kg ∈ B.map r.φ := by
      rw [hBmap]
      rw [← r.φK_range hS]
      exact MonoidHom.mem_range.mpr ⟨(⟨k, hk⟩ : ↥c.K), rfl⟩
    obtain ⟨b, hbB, hbφ⟩ := Subgroup.mem_map.mp hφkg
    have hbA : b ∈ A := hBA hbB
    have hkgA : kg ∈ A := Subgroup.mem_subgroupOf.mpr hk
    have heA : b⁻¹ * kg ∈ A := A.mul_mem (A.inv_mem hbA) hkgA
    have hφe : r.φ (b⁻¹ * kg) = 1 := by
      rw [map_mul, map_inv, hbφ, inv_mul_cancel]
    have heE : ((b⁻¹ * kg : ↥c.G1) : G) ∈ c.E := by
      have hker : b⁻¹ * kg ∈ r.φ.ker := hφe
      rw [r.ker_eq, Subgroup.mem_subgroupOf] at hker
      exact hker
    have heK : ((b⁻¹ * kg : ↥c.G1) : G) ∈ c.K := by
      have hbK : (b : G) ∈ c.K := Subgroup.mem_subgroupOf.mp hbA
      have : (b : G)⁻¹ * (kg : G) ∈ c.K := mul_mem (inv_mem hbK) hk
      simpa using this
    have hBamb : B.map c.G1.subtype = ⁅c.K, c.K⁆ := by
      rw [show B = ⁅A, A⁆ from rfl, Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le c.K_le_G1]
    have hb_amb : (b : G) ∈ ⁅c.K, c.K⁆ := by
      have hb : (b : G) ∈ B.map c.G1.subtype :=
        Subgroup.mem_map_of_mem c.G1.subtype hbB
      rwa [hBamb] at hb
    have hk_eq : k = (b : G) * ((b⁻¹ * kg : ↥c.G1) : G) := by
      simp [kg, mul_assoc]
    rw [hk_eq]
    exact mul_mem (Subgroup.mem_sup_left hb_amb)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨heE, heK⟩))
  · apply sup_le
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · exact inf_le_right

theorem commutator_preFixOct_le (r : ResM24T c) (hS : FixOctSym) :
    ⁅r.preFixOct, r.preFixOct⁆ ≤ c.K := by
  have hPE : r.preFixOct = c.K ⊔ c.E := r.preFixOct_eq_sup hS
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨kx, hkx, ex, hex, rfl⟩ := r.exists_mul_of_mem_preFixOct hPE hx
  obtain ⟨ky, hky, ey, hey, rfl⟩ := r.exists_mul_of_mem_preFixOct hPE hy
  rw [commutatorElement_def]
  have h1 : ex * ky * ex⁻¹ ∈ c.K :=
    (Subgroup.mem_normalizer_iff.mp (c.mem_normalizer_K (c.E_le_G2 hex)) ky).mp hky
  have h2 : ey * kx⁻¹ * ey⁻¹ ∈ c.K :=
    (Subgroup.mem_normalizer_iff.mp (c.mem_normalizer_K (c.E_le_G2 hey)) kx⁻¹).mp
      (inv_mem hkx)
  have hcomm : ey * ex⁻¹ = ex⁻¹ * ey :=
    congrArg Subtype.val (c.E_elem.1.is_comm.comm ⟨ey, hey⟩ ⟨ex⁻¹, inv_mem hex⟩)
  have hstep : (kx * ex) * (ky * ey) * (kx * ex)⁻¹ * (ky * ey)⁻¹ =
      kx * ex * ky * (ey * ex⁻¹) * kx⁻¹ * ey⁻¹ * ky⁻¹ := by group
  have heq : (kx * ex) * (ky * ey) * (kx * ex)⁻¹ * (ky * ey)⁻¹ =
      kx * (ex * ky * ex⁻¹) * (ey * kx⁻¹ * ey⁻¹) * ky⁻¹ := by
    rw [hstep, hcomm]
    group
  rw [heq]
  exact mul_mem (mul_mem (mul_mem hkx h1) h2) (inv_mem hky)

theorem commutator_E_preFixOct_le (r : ResM24T c) (hS : FixOctSym) :
    ⁅c.E, r.preFixOct⁆ ≤ c.K := by
  have hPE : r.preFixOct = c.K ⊔ c.E := r.preFixOct_eq_sup hS
  rw [Subgroup.commutator_le]
  intro e he x hx
  obtain ⟨k, hk, e2, he2, rfl⟩ := r.exists_mul_of_mem_preFixOct hPE hx
  rw [commutatorElement_def]
  have h1 : e * k * e⁻¹ ∈ c.K :=
    (Subgroup.mem_normalizer_iff.mp (c.mem_normalizer_K (c.E_le_G2 he)) k).mp hk
  have hcommE : e * e2 * e⁻¹ * e2⁻¹ = 1 := by
    have hcomm : e * e2 = e2 * e :=
      congrArg Subtype.val (c.E_elem.1.is_comm.comm ⟨e, he⟩ ⟨e2, he2⟩)
    rw [hcomm]; group
  have heq : e * (k * e2) * e⁻¹ * (k * e2)⁻¹ =
      (e * k * e⁻¹) * (e * e2 * e⁻¹ * e2⁻¹) * k⁻¹ := by group
  rw [heq, hcommE]
  simpa using mul_mem h1 (inv_mem hk)

theorem K_eq (r : ResM24T c) (hP : FixOctPerfect) (hS : FixOctSym) (hW : FixOctCommW11) :
    c.K = ⁅r.preFixOct, r.preFixOct⁆ ⊔ ⁅c.E, r.preFixOct⁆ := by
  have hPE : r.preFixOct = c.K ⊔ c.E := r.preFixOct_eq_sup hS
  have hKpre : c.K ≤ r.preFixOct := by rw [hPE]; exact le_sup_left
  have hK7 := r.K_eq_commutator_sup hS hP
  have hK6 := r.commutator_E_K_eq hS hW
  apply le_antisymm
  ·
    rw [hK7]
    apply sup_le
    · exact (Subgroup.commutator_mono hKpre hKpre).trans (le_sup_left)
    · rw [← hK6]
      exact (Subgroup.commutator_mono (le_refl c.E) hKpre).trans le_sup_right
  ·
    exact sup_le (r.commutator_preFixOct_le hS) (r.commutator_E_preFixOct_le hS)

end ResM24T

end CFSG.Quasithin.H13.AS91

end
