module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9DictTor
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModOrb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5F
public import CFSG.Quasithin.EmptyFaithful.T1515C6Fin

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem vZ_mc_eq_vE {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (_hCE : IsCE1513 T M) (h5 : Ce15Six T Mc M 5) (hE9 : HasE9 T Mc M)
    (_h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M) :
    VZ T Mc = vE1516 T Mc M ∧ Mc = Subgroup.normalizer (vE1516 T Mc M : Set G) := by
  have hVZ : V154 T Mc M = VZ T M := V154_eq_VZ_of_six5 h5
  have hVe : IsElemAbelian 2 (V154 T Mc M) := by
    rw [hVZ]
    exact isElemAbelian_VZ hq hM.1.1
  obtain ⟨d, -⟩ := exists_six5Data hq hM h5 hVe
  obtain ⟨x₁, x₂, r⟩ := exists_reflData d h5 h113
  obtain ⟨ε₁, ε₂, ⟨hε₁M, hε₁3, hε₁₂, hε₁a, hε₁f, hε₁s1, hε₁s2⟩,
    ⟨hε₂M, hε₂3, hε₂₁, hε₂a, hε₂f, hε₂s1, hε₂s2⟩⟩ := exists_torus r hE9
  obtain ⟨hτM, hτsw, hτT⟩ := r.tau_mem_stab
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := d.hMN
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    rw [hVZ]
    exact le_conjClosure _ _
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    have hbot : V154 T Mc M ≤ ⊥ := by
      rw [hVZ]
      refine conjClosure_le fun h hh z hz => ?_
      have : z = 1 := by_contra fun hz1 => hcon ⟨z, hz, hz1⟩
      rw [this]
      simp
    have h256 := d.hcard
    have : Nat.card (IntMod (V154 T Mc M) hVe) = 1 := by
      change Nat.card (V154 T Mc M) = 1
      rw [Subgroup.card_eq_one]
      exact le_bot_iff.mp hbot
    omega
  have hord : OrdLE T Mc M := h19.two.2 Mc ⟨hq.mc_max, hq.t_le_mc⟩
  have hUV : VZ T Mc ≤ V154 T Mc M := by
    refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨a, ha, c, hc, rfl⟩ := hord h hh
    have hzU : z ∈ VZ T Mc := le_conjClosure _ _ hz
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hc.2 z hzU
      rw [← this]
      group
    have : a * c * z * (a * c)⁻¹ = a * z * a⁻¹ := by
      calc a * c * z * (a * c)⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by group
        _ = a * z * a⁻¹ := by rw [hcz]
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp (hMN ha.2) z).mp (hZV hz)
  have hUe : IsPGroup 2 ↥(VZ T Mc) := fun x =>
    ⟨1, Subtype.ext (by simpa using hVe.2 x.1 (hUV x.2))⟩
  have hUbot : VZ T Mc ≠ ⊥ := fun h => hz₀1 (by
    have : z₀ ∈ VZ T Mc := le_conjClosure _ _ hz₀Z
    rw [h] at this
    exact this)
  have hMcU : Subgroup.normalizer (VZ T Mc : Set G) = Mc :=
    hq.mc_max.2 _ ⟨VZ T Mc, hUbot, hUe, rfl⟩ (le_normalizer_conjClosure _ Mc)
  have hNVE : Subgroup.normalizer (vE1516 T Mc M : Set G) ≤ Mc :=
    (h14.two (Ce15.not_case3b (Or.inr (Or.inl ⟨5, Or.inr rfl, h5⟩)))).2
  have hinv : ∀ φ ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂),
      ∀ w : IntMod (V154 T Mc M) hVe, w.val ∈ VZ T Mc → (φ w).val ∈ VZ T Mc := by
    intro φ hφ w hw
    obtain ⟨γ, hγN, hγM, hγVE, rfl⟩ := r.exists_lift hφ
    have hγMc : γ ∈ Mc := hNVE (by rw [r.vE]; exact hγVE)
    rw [← conj_val hγN w]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ Mc hγMc) w.val).mp hw
  let Uc : Subgroup (IntMod (V154 T Mc M) hVe) := (VZ T Mc).comap (valHomI hVe)
  have hmemUc : ∀ w : IntMod (V154 T Mc M) hVe, w ∈ Uc ↔ w.val ∈ VZ T Mc := fun w => Iff.rfl
  have hz₀V : z₀ ∈ V154 T Mc M := hZV hz₀Z
  let w₀ : IntMod (V154 T Mc M) hVe := IntMod.mk hVe ⟨z₀, hz₀V⟩
  have hw₀val : w₀.val = z₀ := rfl
  have hw₀E : w₀ ∈ d.S.vEMod x₁ x₂ := by
    have hz : z₀ ∈ vE1516 T Mc M := by
      refine ⟨hz₀V, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
      have hjT : j ∈ T := (iSup₂_le fun _ hA => hA.1 : thompsonJi T 1 ≤ T) hj
      exact Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz₀Z).2 j hjT
    rw [r.vE] at hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
    have : w = w₀ := IntMod.val_injective hwz
    rw [← this]
    exact hw
  have hτw₀ : d.S.τ w₀ = w₀ := by
    obtain ⟨⟨t, htN⟩, htT, hteq⟩ := (mem_autI hVe).1 hτT
    rw [← hteq]
    apply IntMod.val_injective
    rw [← conj_val htN w₀, hw₀val]
    have := Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz₀Z).2 t htT
    show t * z₀ * t⁻¹ = z₀
    rw [this]
    group
  have hεW₁ : ∀ w ∈ d.S.W₁, ε₁ w ∈ d.S.W₁ := fun w hw => (hε₁s1 w).mp hw
  have hεW₂ : ∀ w ∈ d.S.W₂, ε₂ w ∈ d.S.W₂ := fun w hw => (hε₂s2 w).mp hw
  have hVEUc : d.S.vEMod x₁ x₂ ≤ Uc := by
    have h := d.S.eq_vEMod_of_orbit hW d.hcard r.x₁_mem.1 r.x₂_mem.1 r.x₁_two r.x₂_two hε₁f hε₁₂
      hεW₁ (fun w hw => (hε₁M.2 w).mp hw) hε₂f hε₂₁ hεW₂ (fun w hw => (hε₂M.2 w).mp hw) hτsw
      (U := Uc ⊓ d.S.vEMod x₁ x₂) inf_le_right
      (fun w hw => ⟨hinv ε₁ hε₁M w hw.1, (hε₁M.2 w).mp hw.2⟩)
      (fun w hw => ⟨hinv ε₂ hε₂M w hw.1, (hε₂M.2 w).mp hw.2⟩)
      (w₀ := w₀) ⟨(hmemUc w₀).2 (hw₀val ▸ le_conjClosure _ _ hz₀Z), hw₀E⟩
      (fun h => hz₀1 (by rw [← hw₀val, h]; rfl)) hτw₀
    rw [← h]
    exact inf_le_left
  have hVEU : vE1516 T Mc M ≤ VZ T Mc := by
    rw [r.vE]
    intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    exact (hmemUc w).1 (hVEUc hw)
  have hE4 := d.S.eq_vE_or_top hW d.hcard r.x₁_mem.1 r.x₂_mem.1 r.x₁_two r.x₂_two
    ⟨hε₂3, hε₂₁, hε₂f⟩ hεW₂ hτsw (U := Uc) hVEUc
    (fun w hw => (hmemUc _).2 (hinv ε₂ hε₂M w ((hmemUc w).1 hw)))
    (fun w hw => (hmemUc _).2 (hinv d.S.τ hτM w ((hmemUc w).1 hw)))
  have hUVE : VZ T Mc = vE1516 T Mc M := by
    rcases hE4 with h | h
    · refine le_antisymm ?_ hVEU
      intro g hg
      have hgV : g ∈ V154 T Mc M := hUV hg
      have hw : IntMod.mk hVe ⟨g, hgV⟩ ∈ Uc := (hmemUc _).2 hg
      rw [h] at hw
      rw [r.vE]
      exact Subgroup.mem_map.2 ⟨_, hw, rfl⟩
    · exfalso
      have hVU : V154 T Mc M ≤ VZ T Mc := by
        intro g hg
        have hw : IntMod.mk hVe ⟨g, hg⟩ ∈ Uc := by rw [h]; exact Subgroup.mem_top _
        exact (hmemUc _).1 hw
      have hUeq : VZ T Mc = V154 T Mc M := le_antisymm hUV hVU
      have hloc : IsTwoLocal (Subgroup.normalizer (V154 T Mc M : Set G)) := by
        refine ⟨V154 T Mc M, ?_, ?_, rfl⟩
        · intro hb
          have h256 := d.hcard
          have : Nat.card (IntMod (V154 T Mc M) hVe) = 1 := by
            change Nat.card (V154 T Mc M) = 1
            rw [hb, Subgroup.card_bot]
          omega
        · intro x
          exact ⟨1, by simpa using Subtype.ext (hVe.2 x x.2)⟩
      have hMcN : Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
        rw [← hUeq]
        exact le_normalizer_conjClosure _ Mc
      have heq := hq.mc_max.2 _ hloc hMcN
      exact not_le_mc_of_isMf hq hM (by rw [← heq]; exact hMN)
  refine ⟨hUVE, ?_⟩
  rw [← hUVE]
  exact hMcU.symm

end CFSG.Quasithin.E9
