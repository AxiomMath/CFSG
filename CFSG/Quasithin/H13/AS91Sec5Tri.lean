module

public import CFSG.Quasithin.H13.AS91Sec5TwoC
public import CFSG.Quasithin.H13.AS91Sec8Prod

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def Stmt3_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ k : G ⧸ c.G2, CInc c.G1 c.G2 c.x0 k →
      (¬ ∃ p : G ⧸ c.G3, CInc c.G2 c.G3 c.l0 p ∧ CInc c.G2 c.G3 k p) →
      4 < Set.ncard ((fun r : G => r • k) '' (c.R : Set G))

theorem ncard_image_le_of_factor {α β γ : Type*} [Nonempty α] {S : Set α} (hS : S.Finite) (f₁ : α → β)
    (f₂ : α → γ) (h : ∀ s ∈ S, ∀ s' ∈ S, f₂ s = f₂ s' → f₁ s = f₁ s') :
    (f₁ '' S).ncard ≤ (f₂ '' S).ncard := by
  classical
  have hne : ∀ y ∈ f₂ '' S, ∃ s ∈ S, f₂ s = y := fun y hy => hy
  let g : γ → β := fun y => f₁ (Function.invFunOn f₂ S y)
  have hsub : f₁ '' S = g '' (f₂ '' S) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨f₂ s, ⟨s, hs, rfl⟩, ?_⟩
      have h1 : Function.invFunOn f₂ S (f₂ s) ∈ S := Function.invFunOn_mem ⟨s, hs, rfl⟩
      have h2 : f₂ (Function.invFunOn f₂ S (f₂ s)) = f₂ s := Function.invFunOn_eq ⟨s, hs, rfl⟩
      exact h _ h1 s hs h2
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨Function.invFunOn f₂ S (f₂ s), Function.invFunOn_mem ⟨s, hs, rfl⟩, rfl⟩
  rw [hsub]
  exact Set.ncard_image_le (hS.image f₂)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem inc_pt_plane {q : G ⧸ c.G1} {m : G ⧸ c.G2} {p : G ⧸ c.G3} (hq : CInc c.G1 c.G2 q m)
    (hp : CInc c.G2 c.G3 m p) : CInc c.G1 c.G3 q p := by
  obtain ⟨g, hg1, hg2⟩ := hq
  obtain ⟨h, hh1, hh2⟩ := hp
  have h1 : g⁻¹ * h ∈ c.G2 := by
    have : (g : G ⧸ c.G2) = (h : G ⧸ c.G2) := hg2.trans hh1.symm
    rwa [QuotientGroup.eq] at this
  obtain ⟨k, hk, s, hs, hks⟩ := c.G2_eq_mul h1
  refine ⟨g * k, ?_, ?_⟩
  · rw [← hg1, QuotientGroup.eq]
    simpa using inv_mem (c.K_le_G1 hk)
  · rw [← hh2, QuotientGroup.eq]
    have : (g * k)⁻¹ * h = s := by
      calc (g * k)⁻¹ * h = k⁻¹ * (g⁻¹ * h) := by group
        _ = k⁻¹ * (k * s) := by rw [hks]
        _ = s := by group
    rw [this]
    exact c.CZ_le_G3 hs

theorem E_smul_line {m : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m) {e : G} (he : e ∈ c.E) :
    e • m = m := by
  obtain ⟨w, hw1, hw2⟩ := hm
  have hwG1 : w ∈ c.G1 := (mk_eq_one_iff c.G1 w).mp hw1
  rw [← hw2, ← mk_mul_eq_smul, QuotientGroup.eq]
  have : w⁻¹ * e⁻¹ * w ∈ c.E := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwG1) e⁻¹).mp (inv_mem he)
    simpa using this
  have h2 : (e * w)⁻¹ * w = w⁻¹ * e⁻¹ * w := by group
  rw [h2]
  exact c.E_le_G2 this

theorem conjE_smul_line {g₀ : G} {n : G ⧸ c.G2} (hn : CInc c.G1 c.G2 (g₀ • c.x0) n) {f : G}
    (hf : f ∈ c.E.map (MulAut.conj g₀).toMonoidHom) : f • n = n := by
  have hn' : CInc c.G1 c.G2 c.x0 (g₀⁻¹ • n) := by
    have := (cInc_smul c.G1 c.G2 g₀⁻¹ _ _).mpr hn
    rwa [inv_smul_smul] at this
  have hf' : g₀⁻¹ * f * g₀ ∈ c.E := (mem_conjSub_iff c.E g₀ f).mp hf
  have h1 := c.E_smul_line hn' hf'
  rw [mul_smul, mul_smul, smul_inv_smul] at h1
  exact smul_left_cancel g₀⁻¹ h1

theorem ncard_objOf_line (n : G ⧸ c.G2) : (objOf c.G1 c.G2 n).ncard = 5 := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective n
  have h1 : ((h : G) : G ⧸ c.G2) = h • c.l0 := by
    show _ = h • ((1 : G) : G ⧸ c.G2)
    rw [← mk_mul_eq_smul, mul_one]
  rw [h1, objOf_smul, Set.ncard_image_of_injective _ (MulAction.injective h)]
  have := c.card_ptsL
  rw [← Nat.card_coe_set_eq]
  exact this

theorem smul_line_eq_of_fix (hLU : ∀ y ∈ c.ptsL, y ≠ c.x0 → c.G1 ⊓ stabilizer G y ≤ c.G2)
    {k : G ⧸ c.G2} {d : G ⧸ c.G1} (hk : CInc c.G1 c.G2 c.x0 k) (hd : CInc c.G1 c.G2 d k)
    (hdx : d ≠ c.x0) {u : G} (hu1 : u ∈ c.G1) (hud : u • d = d) : u • k = k := by
  obtain ⟨w, hw1, hw2⟩ := hk
  have hwG1 : w ∈ c.G1 := (mk_eq_one_iff c.G1 w).mp hw1
  have hwx : w • c.x0 = c.x0 := by
    have : w ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact hwG1
    exact mem_stabilizer_iff.mp this
  have hkw : k = w • c.l0 := by
    rw [← hw2]
    show _ = w • ((1 : G) : G ⧸ c.G2)
    rw [← mk_mul_eq_smul, mul_one]
  have hk' : w⁻¹ • k = c.l0 := by rw [hkw, inv_smul_smul]
  have hd₀ : w⁻¹ • d ∈ c.ptsL := by
    have := (cInc_smul c.G1 c.G2 w⁻¹ d k).mpr hd
    rw [hk'] at this
    exact this
  have hd₀x : w⁻¹ • d ≠ c.x0 := by
    intro h
    apply hdx
    have : d = w • c.x0 := by rw [← h, smul_inv_smul]
    rw [this, hwx]
  have hn : w⁻¹ * u * w ∈ c.G1 ⊓ stabilizer G (w⁻¹ • d) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hwG1) hu1) hwG1, mem_stabilizer_iff.mpr ?_⟩
    rw [mul_smul, mul_smul, smul_inv_smul, hud]
  have h2 := hLU _ hd₀ hd₀x hn
  have h3 : (w⁻¹ * u * w) • c.l0 = c.l0 := by
    have : (w⁻¹ * u * w) ∈ stabilizer G c.l0 := by
      rw [show stabilizer G c.l0 = c.G2 from stabilizer_mk_one c.G2]
      exact h2
    exact mem_stabilizer_iff.mp this
  calc u • k = (w * (w⁻¹ * u * w)) • c.l0 := by
        rw [hkw, ← mul_smul]
        congr 1
        group
    _ = w • ((w⁻¹ * u * w) • c.l0) := mul_smul _ _ _
    _ = w • c.l0 := by rw [h3]
    _ = k := hkw.symm

theorem card_R_inf_E : Nat.card ↥(c.R ⊓ c.E) = 2 ^ 9 := by
  have hnorm : ∀ r ∈ c.R, ∀ e ∈ c.E, r * e * r⁻¹ ∈ c.E := fun r hr e he =>
    (Subgroup.mem_normalizer_iff.mp (c.K_le_G1 (c.R_le_K hr)) e).mp he
  have hset := coe_sup_eq_mul_of_normalizes c.R c.E hnorm
  have h1 := card_mul_set_mul_card_inf c.R c.E
  rw [← hset] at h1
  have h2 : Nat.card ((c.R ⊔ c.E : Subgroup G) : Set G) = 2 ^ 17 := by
    rw [← c.card_RE]
    rfl
  rw [h2, c.card_R, c.card_E] at h1
  have : (2 : ℕ) ^ 17 * Nat.card ↥(c.R ⊓ c.E) = 2 ^ 17 * 2 ^ 9 := by
    rw [h1]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

theorem R_inf_conjE_eq_map {g₀ : G} (hg₀ : g₀ ∈ c.G2) :
    c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom =
      (c.R ⊓ c.E).map (MulAut.conj g₀).toMonoidHom := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxR, hxF⟩
    obtain ⟨e, he, rfl⟩ := hxF
    refine ⟨e, Subgroup.mem_inf.mpr ⟨?_, he⟩, rfl⟩
    have := c.R_conj_G2 (inv_mem hg₀) hxR
    have e1 : g₀⁻¹ * ((MulAut.conj g₀).toMonoidHom e) * g₀⁻¹⁻¹ = e := by
      show g₀⁻¹ * (g₀ * e * g₀⁻¹) * g₀⁻¹⁻¹ = e
      group
    rwa [e1] at this
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyR, hyE⟩ := Subgroup.mem_inf.mp hy
    exact ⟨c.R_conj_G2 hg₀ hyR, y, hyE, rfl⟩

theorem R_eq_mul (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    {b : G ⧸ c.G1} (hb : b ∈ c.ptsL) (hbx : b ≠ c.x0) {g₀ : G} (hg₀ : g₀ ∈ c.G2)
    (hg₀b : g₀ • c.x0 = b) :
    ∀ r ∈ c.R, ∃ v ∈ c.R ⊓ c.E, ∃ u ∈ c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom, v * u = r := by
  have h2 := h2c b hb hbx g₀ hg₀ hg₀b
  have hinf : (c.R ⊓ c.E) ⊓ (c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom) = c.Z := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxR, hxE⟩, -, hxF⟩
      rw [← h2]
      exact Subgroup.mem_inf.mpr ⟨hxF, hxE⟩
    · intro hx
      rw [← h2] at hx
      obtain ⟨hxF, hxE⟩ := Subgroup.mem_inf.mp hx
      have hxZ : x ∈ c.Z := by rw [← h2]; exact Subgroup.mem_inf.mpr ⟨hxF, hxE⟩
      exact ⟨⟨c.Z_le_R hxZ, hxE⟩, c.Z_le_R hxZ, hxF⟩
  refine exists_mul_of_card_eq (c.R ⊓ c.E) (c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom) c.R
    inf_le_left inf_le_left ?_
  have hcard : Nat.card ↥(c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom) = 2 ^ 9 := by
    rw [c.R_inf_conjE_eq_map hg₀, Subgroup.card_map_of_injective
      (fun a b hab => (MulAut.conj g₀).injective hab), c.card_R_inf_E]
  rw [hinf, hcard, c.card_R_inf_E, c.card_Z, c.card_R]
  norm_num

theorem conjE_smul_pt {g₀ : G} {f : G} (hf : f ∈ c.E.map (MulAut.conj g₀).toMonoidHom) :
    f • (g₀ • c.x0) = g₀ • c.x0 := by
  have hf' : g₀⁻¹ * f * g₀ ∈ c.E := (mem_conjSub_iff c.E g₀ f).mp hf
  have hx : (g₀⁻¹ * f * g₀) • c.x0 = c.x0 := by
    have : (g₀⁻¹ * f * g₀) ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact c.E_le_G1 hf'
    exact mem_stabilizer_iff.mp this
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at hx
  exact hx

theorem ncard_orbit_R_le (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    {b d : G ⧸ c.G1} {k n : G ⧸ c.G2} (hb : b ∈ c.ptsL) (hbx : b ≠ c.x0) (hdx : d ≠ c.x0)
    (hdb : d ≠ b) (hxk : CInc c.G1 c.G2 c.x0 k) (hdk : CInc c.G1 c.G2 d k)
    (hbn : CInc c.G1 c.G2 b n) (hdn : CInc c.G1 c.G2 d n) :
    Set.ncard ((fun r : G => r • k) '' (c.R : Set G)) ≤ 4 := by
  classical
  obtain ⟨g₀, hg₀, hg₀b⟩ := (c.mem_ptsL_iff b).mp hb
  have hg₀x : g₀ • c.x0 = b := by
    rw [← hg₀b, ← mul_one g₀, mk_mul_eq_smul]
    simp
  have hmul := c.R_eq_mul h2c hb hbx hg₀ hg₀x
  have hLU := fun y (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) => c.lineU_of_2c h2c hy hyx
  have hRG1 : ∀ r ∈ c.R, r ∈ c.G1 := fun r hr => c.K_le_G1 (c.R_le_K hr)
  have hfixx : ∀ u ∈ c.G1, u • c.x0 = c.x0 := fun u hu =>
    mem_stabilizer_iff.mp (by rw [c.stab_x0]; exact hu)
  have hsub : (fun r : G => r • k) '' (c.R : Set G) ⊆
      (fun u : G => u • k) '' ((c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨v, hv, u, hu, rfl⟩ := hmul r hr
    refine ⟨u, hu, ?_⟩
    obtain ⟨huR, -⟩ := Subgroup.mem_inf.mp hu
    have hxuk : CInc c.G1 c.G2 c.x0 (u • k) := by
      have := (cInc_smul c.G1 c.G2 u c.x0 k).mpr hxk
      rwa [hfixx u (hRG1 u huR)] at this
    show u • k = (v * u) • k
    rw [mul_smul]
    exact (c.E_smul_line hxuk (Subgroup.mem_inf.mp hv).2).symm
  have hfac : ∀ u ∈ ((c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G),
      ∀ u' ∈ ((c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G),
      u • d = u' • d → u • k = u' • k := by
    intro u hu u' hu' hud
    have hw : u'⁻¹ * u ∈ c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom :=
      mul_mem (inv_mem hu') hu
    have hwd : (u'⁻¹ * u) • d = d := by
      rw [mul_smul, hud, inv_smul_smul]
    have := c.smul_line_eq_of_fix hLU hxk hdk hdx (hRG1 _ (Subgroup.mem_inf.mp hw).1) hwd
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  have hfin : ((c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G).Finite :=
    Set.toFinite _
  have h1 := ncard_image_le_of_factor hfin (fun u : G => u • k) (fun u : G => u • d) hfac
  have hn' : CInc c.G1 c.G2 (g₀ • c.x0) n := by rw [hg₀x]; exact hbn
  have hsub2 : (fun u : G => u • d) '' ((c.R ⊓ c.E.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G) ⊆
      objOf c.G1 c.G2 n \ {b} := by
    rintro _ ⟨u, hu, rfl⟩
    have huF := (Subgroup.mem_inf.mp hu).2
    refine ⟨?_, ?_⟩
    · have := (cInc_smul c.G1 c.G2 u d n).mpr hdn
      rwa [c.conjE_smul_line hn' huF] at this
    · intro h
      have hub : u • b = b := by
        rw [← hg₀x]
        exact c.conjE_smul_pt huF
      apply hdb
      exact smul_left_cancel u (h.trans hub.symm)
  have hb_mem : b ∈ objOf c.G1 c.G2 n := hbn
  have h4 : (objOf c.G1 c.G2 n \ {b}).ncard = 4 := by
    rw [Set.ncard_diff_singleton_of_mem hb_mem, c.ncard_objOf_line n]
  have h5 := Set.ncard_le_ncard hsub2 (Set.toFinite _)
  have h6 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem tri_base (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    (h312 : ∀ k : G ⧸ c.G2, CInc c.G1 c.G2 c.x0 k →
      (¬ ∃ p : G ⧸ c.G3, CInc c.G2 c.G3 c.l0 p ∧ CInc c.G2 c.G3 k p) →
      4 < Set.ncard ((fun r : G => r • k) '' (c.R : Set G)))
    {b d : G ⧸ c.G1} {k n : G ⧸ c.G2} (hb : b ∈ c.ptsL) (hbx : b ≠ c.x0) (hdx : d ≠ c.x0)
    (hdb : d ≠ b) (hxk : CInc c.G1 c.G2 c.x0 k) (hdk : CInc c.G1 c.G2 d k)
    (hbn : CInc c.G1 c.G2 b n) (hdn : CInc c.G1 c.G2 d n) :
    ∃ p : G ⧸ c.G3, CInc c.G1 c.G3 c.x0 p ∧ CInc c.G1 c.G3 b p ∧ CInc c.G1 c.G3 d p := by
  have hplane : ∃ p : G ⧸ c.G3, CInc c.G2 c.G3 c.l0 p ∧ CInc c.G2 c.G3 k p := by
    by_contra hno
    have h4 := h312 k hxk hno
    have hle := c.ncard_orbit_R_le h2c hb hbx hdx hdb hxk hdk hbn hdn
    omega
  obtain ⟨p, hp0, hpk⟩ := hplane
  exact ⟨p, c.inc_pt_plane (cInc_mk c.G1 c.G2 1) hp0, c.inc_pt_plane hb hp0,
    c.inc_pt_plane hdk hpk⟩

end Loc49

theorem stmt5_5_of (h2c : Stmt5_2c) (h312 : Stmt3_12) : Stmt5_5 := by
  intro G _ _ z hJ c a b d hab hbd had
  have h2c' := h2c G z hJ c
  have h312' := h312 G z hJ c
  obtain ⟨g, hga⟩ := MulAction.exists_smul_eq G c.x0 a
  have hadj : ∀ (t : G) (u v : G ⧸ c.G1), c.Delta.Adj (t • u) (t • v) ↔ c.Delta.Adj u v :=
    fun t u v => CFSG.Quasithin.GraphAction.adj_smul t u v
  have hab' : c.Delta.Adj c.x0 (g⁻¹ • b) := by
    have := (hadj g⁻¹ a b).mpr hab
    rwa [← hga, inv_smul_smul] at this
  have had' : c.Delta.Adj c.x0 (g⁻¹ • d) := by
    have := (hadj g⁻¹ a d).mpr had
    rwa [← hga, inv_smul_smul] at this
  have hbd' : c.Delta.Adj (g⁻¹ • b) (g⁻¹ • d) := (hadj g⁻¹ b d).mpr hbd
  obtain ⟨hne1, m, hxm, hbm⟩ := hab'
  obtain ⟨w, hw1, hw2⟩ := hxm
  have hwG1 : w ∈ c.G1 := (Loc49.mk_eq_one_iff c.G1 w).mp hw1
  have hwx : w⁻¹ • c.x0 = c.x0 := by
    have : w⁻¹ ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact inv_mem hwG1
    exact mem_stabilizer_iff.mp this
  have hwl : w⁻¹ • m = c.l0 := by
    rw [← hw2, ← mk_mul_eq_smul, inv_mul_cancel]
  have hb₂ : w⁻¹ • g⁻¹ • b ∈ c.ptsL := by
    have := (cInc_smul c.G1 c.G2 w⁻¹ _ _).mpr hbm
    rw [hwl] at this
    exact this
  have hb₂x : w⁻¹ • g⁻¹ • b ≠ c.x0 := by
    intro h
    apply hne1
    have : g⁻¹ • b = w • c.x0 := by rw [← h, smul_inv_smul]
    rw [this, ← hwx, smul_inv_smul, hwx]
  have hwx' : w • c.x0 = c.x0 := (inv_smul_eq_iff.mp hwx).symm
  have hxd₂ : c.Delta.Adj c.x0 (w⁻¹ • g⁻¹ • d) := by
    have := (hadj w⁻¹ c.x0 (g⁻¹ • d)).mpr had'
    rwa [hwx] at this
  have hbd₂ : c.Delta.Adj (w⁻¹ • g⁻¹ • b) (w⁻¹ • g⁻¹ • d) := (hadj w⁻¹ _ _).mpr hbd'
  obtain ⟨hne2, k, hxk, hdk⟩ := hxd₂
  obtain ⟨hne3, n, hbn, hdn⟩ := hbd₂
  have hdx : w⁻¹ • g⁻¹ • d ≠ c.x0 := fun h => hne2 h.symm
  have hdb : w⁻¹ • g⁻¹ • d ≠ w⁻¹ • g⁻¹ • b := fun h => hne3 h.symm
  obtain ⟨p, hpx, hpb, hpd⟩ := c.tri_base h2c' h312' hb₂ hb₂x hdx hdb hxk hdk hbn hdn
  have hax : (g * w) • c.x0 = a := by rw [mul_smul, hwx', hga]
  refine ⟨(g * w) • p, ?_, ?_, ?_⟩
  · have := (cInc_smul c.G1 c.G3 (g * w) _ _).mpr hpx
    rwa [hax] at this
  · have := (cInc_smul c.G1 c.G3 (g * w) _ _).mpr hpb
    rwa [mul_smul, smul_inv_smul, smul_inv_smul] at this
  · have := (cInc_smul c.G1 c.G3 (g * w) _ _).mpr hpd
    rwa [mul_smul, smul_inv_smul, smul_inv_smul] at this

end CFSG.Quasithin.H13.AS91
