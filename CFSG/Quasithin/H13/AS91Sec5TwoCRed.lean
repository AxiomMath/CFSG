module

public import CFSG.Quasithin.H13.AS91Sec5TwoC

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem E_comm {e e' : G} (he : e ∈ c.E) (he' : e' ∈ c.E) : e * e' = e' * e :=
  congrArg Subtype.val
    (c.E_elem.1.is_comm.comm (⟨e, he⟩ : ↥c.E) (⟨e', he'⟩ : ↥c.E))

theorem Z_le_E : c.Z ≤ c.E := by
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]
    exact one_mem _
  · obtain ⟨k, hkK, hk⟩ :=
      c.exists_K_conj c.z_mem_Z hb (fun h => c.S.z_ne_one (c.S_z.trans h)) hb1
    rw [← hk]
    exact (Subgroup.mem_normalizer_iff.mp (c.K_le_G1 hkK) z).mp c.z_mem_E

theorem Z_le_conj_inf_E {g : G} (hg : g ∈ c.G2) :
    c.Z ≤ c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E := by
  intro x hx
  rw [Subgroup.mem_inf, mem_conjSub_iff]
  refine ⟨c.Z_le_E ?_, c.Z_le_E hx⟩
  simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx

theorem conj_E_transitive {g : G} (hg : g ∈ c.G2) {a b : G ⧸ c.G1}
    (ha : a ∈ c.ptsL) (hb : b ∈ c.ptsL) (hay : a ≠ g • c.x0) (hby : b ≠ g • c.x0) :
    ∃ e ∈ c.E.map (MulAut.conj g).toMonoidHom, e • a = b := by
  have hga : g⁻¹ • a ∈ c.ptsL := smul_mem_objOf_base (inv_mem hg) ha
  have hgb : g⁻¹ • b ∈ c.ptsL := smul_mem_objOf_base (inv_mem hg) hb
  have hgax : g⁻¹ • a ≠ c.x0 := fun h => hay (by rw [← smul_inv_smul g a, h])
  have hgbx : g⁻¹ • b ≠ c.x0 := fun h => hby (by rw [← smul_inv_smul g b, h])
  obtain ⟨e, he, heq⟩ := c.E_transitive hga hgb hgax hgbx
  refine ⟨g * e * g⁻¹, Subgroup.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
  calc (g * e * g⁻¹) • a = g • (e • (g⁻¹ • a)) := by rw [mul_smul, mul_smul]
    _ = g • (g⁻¹ • b) := by rw [heq]
    _ = b := by rw [smul_inv_smul]

theorem G12_le_normalizer_conj_inf_E {g : G} (hg : g ∈ c.G2) (hgx : g • c.x0 ≠ c.x0) :
    c.G12 ≤
      normalizer
        ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) := by
  classical
  have hy : g • c.x0 ∈ c.ptsL := smul_mem_objOf_base hg c.x0_mem_ptsL
  have cent_I : ∀ e ∈ c.E, e ∈ normalizer
        ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (c.E_comm (e := e) (e' := x) he (Subgroup.mem_inf.mp hx).2).symm
  have norm_I_of : ∀ m : G, m ∈ c.G1 →
      m • (g • c.x0) = g • c.x0 → m ∈ normalizer
        ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) := by
    intro m hmG1 hmy
    have hmE : m ∈ normalizer (c.E : Set G) := hmG1
    have hmmap : m ∈ (c.G1).map (MulAut.conj g).toMonoidHom := by
      have hstab : m ∈ stabilizer G (g • c.x0) := mem_stabilizer_iff.mpr hmy
      rwa [MulAction.stabilizer_smul_eq_stabilizer_map_conj, c.stab_x0] at hstab
    have hmEg : m ∈ normalizer ((c.E.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      rwa [Subgroup.map_equiv_normalizer_eq c.E (MulAut.conj g)] at hmmap
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hmEg x).mp hx1,
        (Subgroup.mem_normalizer_iff.mp hmE x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hmEg x).mpr hx1,
        (Subgroup.mem_normalizer_iff.mp hmE x).mpr hx2⟩
  intro h hh
  rw [c.G12_eq, Subgroup.mem_inf] at hh
  obtain ⟨hhG2, hhG1⟩ := hh
  have hhG2' : h ∈ c.G2 := hhG2
  have hhx : h • c.x0 = c.x0 := by
    have : h ∈ stabilizer G c.x0 := by rwa [c.stab_x0]
    exact mem_stabilizer_iff.mp this
  have hhx' : h⁻¹ • c.x0 = c.x0 := by
    calc h⁻¹ • c.x0 = h⁻¹ • (h • c.x0) := by rw [hhx]
      _ = c.x0 := by rw [inv_smul_smul]
  have hhy : h • (g • c.x0) ∈ c.ptsL := smul_mem_objOf_base hhG2' hy
  have hhyx : h • (g • c.x0) ≠ c.x0 := by
    intro h'
    apply hgx
    calc g • c.x0 = h⁻¹ • (h • (g • c.x0)) := by rw [inv_smul_smul]
      _ = h⁻¹ • c.x0 := by rw [h']
      _ = c.x0 := hhx'
  obtain ⟨e, he, heq⟩ := c.E_transitive hy hhy hgx hhyx
  let m : G := e⁻¹ * h
  have hmy : m • (g • c.x0) = g • c.x0 := by
    show (e⁻¹ * h) • (g • c.x0) = g • c.x0
    rw [mul_smul, ← heq, inv_smul_smul]
  have hmG1 : m ∈ c.G1 := mul_mem (inv_mem (c.E_le_G1 he)) hhG1
  have hmn : m ∈ normalizer
      ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) :=
    norm_I_of m hmG1 hmy
  have hen : e ∈ normalizer
      ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) :=
    cent_I e he
  have heq' : h = e * m := by
    show h = e * (e⁻¹ * h)
    group
  rw [heq']
  exact mul_mem hen hmn

theorem G2_le_normalizer_conj_inf_E {g : G} (hg : g ∈ c.G2) (hgx : g • c.x0 ≠ c.x0) :
    c.G2 ≤
      normalizer
        ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) := by
  classical
  have hy : g • c.x0 ∈ c.ptsL := smul_mem_objOf_base hg c.x0_mem_ptsL
  have hconjG12 : c.G12.map (MulAut.conj g).toMonoidHom ≤ normalizer
      ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
    have hgx' : g⁻¹ • c.x0 ≠ c.x0 := by
      intro h'
      apply hgx
      calc g • c.x0 = g • (g⁻¹ • c.x0) := by rw [h']
        _ = c.x0 := by rw [smul_inv_smul]
    have hnorm : h ∈ normalizer
        ((c.E.map (MulAut.conj (g⁻¹)).toMonoidHom ⊓ c.E : Subgroup G) : Set G) :=
      c.G12_le_normalizer_conj_inf_E (g := g⁻¹) (inv_mem hg) hgx' hh
    have hmap1 : (c.E.map (MulAut.conj (g⁻¹)).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = c.E := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (g⁻¹)).toMonoidHom
          = MonoidHom.id G := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply, inv_inv]
        group
      rw [hcomp, Subgroup.map_id]
    have hmapI : ((c.E.map (MulAut.conj (g⁻¹)).toMonoidHom ⊓ c.E : Subgroup G).map
        (MulAut.conj g).toMonoidHom) =
        c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hmap1, inf_comm]
    have hnorm' : (MulAut.conj g).toMonoidHom h ∈ normalizer
        ((((c.E.map (MulAut.conj (g⁻¹)).toMonoidHom ⊓ c.E : Subgroup G).map
          (MulAut.conj g).toMonoidHom) : Subgroup G) : Set G) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.mem_map.mpr ⟨h, hnorm, rfl⟩
    rw [hmapI] at hnorm'
    exact hnorm'
  let L : Subgroup G := c.G12 ⊔ c.G12.map (MulAut.conj g).toMonoidHom
  have hG12 : c.G12 ≤ normalizer
      ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) :=
    c.G12_le_normalizer_conj_inf_E hg hgx
  have hG12L : c.G12 ≤ L := le_sup_left
  have hL_G2 : L ≤ c.G2 := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [c.G12_eq, Subgroup.mem_inf] at hx
      exact hx.1
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [c.G12_eq, Subgroup.mem_inf] at hy
      exact mul_mem (mul_mem hg hy.1) (inv_mem hg)
  have hLnorm : L ≤ normalizer
      ((c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E : Subgroup G) : Set G) :=
    sup_le hG12 hconjG12
  have hE_G12 : c.E ≤ c.G12 := by
    rw [c.G12_eq]
    exact le_inf c.E_le_G2 c.E_le_G1
  have hEgL : c.E.map (MulAut.conj g).toMonoidHom ≤ L :=
    (Subgroup.map_mono hE_G12).trans le_sup_right
  have hLnot : ¬ L ≤ c.G12 := by
    intro hLG12
    have hG12G1 : c.G12 ≤ c.G1 := by
      rw [c.G12_eq]
      exact inf_le_right
    have hEgG1 : c.E.map (MulAut.conj g).toMonoidHom ≤ c.G1 :=
      hEgL.trans (hLG12.trans hG12G1)
    obtain ⟨t, ht, -, -, u, hu, hux, huy, -⟩ := c.exists_swap_fix hy hgx
    obtain ⟨e', he', he'q⟩ := c.conj_E_transitive hg c.x0_mem_ptsL hu hgx.symm huy
    have hex : e' • c.x0 = c.x0 := by
      have : e' ∈ stabilizer G c.x0 := by
        rw [c.stab_x0]
        exact hEgG1 he'
      exact mem_stabilizer_iff.mp this
    exact hux (he'q.symm.trans hex)
  have hprod : c.G12.relIndex L * L.relIndex c.G2 = 5 := by
    rw [Subgroup.relIndex_mul_relIndex c.G12 L c.G2 hG12L hL_G2]
    exact c.relIndex_G12
  have hdvd : c.G12.relIndex L ∣ 5 := ⟨L.relIndex c.G2, hprod.symm⟩
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd (Subgroup.relIndex_eq_one.mp h1) hLnot
  · have hL2 : L.relIndex c.G2 = 1 := by
      rw [h1] at hprod
      omega
    exact (Subgroup.relIndex_eq_one.mp hL2).trans hLnorm

theorem le_Z_of_le_Q (W : Subgroup G) (hW : c.G2 ≤ normalizer (W : Set G))
    (hWQ : W ≤ Q z) : W ≤ c.Z := by
  have hconj : ∀ a : G, a * z * a⁻¹ ∈ c.Z → a * z * a⁻¹ ≠ 1 →
      W ≤ (Q z).map (MulAut.conj a).toMonoidHom := by
    intro a haZ ha1
    obtain ⟨k, hkK, hk⟩ :=
      c.exists_K_conj c.z_mem_Z haZ (fun h => c.S.z_ne_one (c.S_z.trans h)) ha1
    let m : G := k⁻¹ * a
    have ha_eq : a = k * m := by
      show a = k * (k⁻¹ * a)
      group
    have hmz : m * z * m⁻¹ = z := by
      calc m * z * m⁻¹ = k⁻¹ * ((k * m) * z * (k * m)⁻¹) * k := by group
        _ = k⁻¹ * (k * z * k⁻¹) * k := by rw [← ha_eq, ← hk]
        _ = z := by group
    have hcomm : z * m = m * z := by
      calc z * m = (m * z * m⁻¹) * m := by rw [hmz]
        _ = m * z := by group
    have hmG3 : m ∈ c.G3 := by
      rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hcomm
    have hmN : m ∈ normalizer (Q z : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H z) hmG3
    have hQeq : (Q z).map (MulAut.conj a).toMonoidHom =
        (Q z).map (MulAut.conj k).toMonoidHom := by
      ext x
      rw [mem_conjSub_iff, mem_conjSub_iff]
      have hconj' : (k * m)⁻¹ * x * (k * m) = m⁻¹ * (k⁻¹ * x * k) * m := by group
      rw [ha_eq, hconj']
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hmN) (k⁻¹ * x * k)).symm
    rw [hQeq]
    intro w hw
    rw [mem_conjSub_iff]
    exact hWQ (by simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem (hW (c.K_le_G2 hkK))) w).mp hw)
  have hg1Z : c.g₁ * z * c.g₁⁻¹ ∈ c.Z := by
    rw [c.Z_eq_closure]
    exact Subgroup.subset_closure (by simp)
  have hk1Z : c.k₁ * z * c.k₁⁻¹ ∈ c.Z := by
    rw [c.Z_eq_closure]
    exact Subgroup.subset_closure (by simp)
  have hg11 : c.g₁ * z * c.g₁⁻¹ ≠ 1 := by
    intro h
    have hz1 : z = 1 := by
      calc z = c.g₁⁻¹ * (c.g₁ * z * c.g₁⁻¹) * c.g₁ := by group
        _ = 1 := by rw [h]; group
    exact c.S.z_ne_one (c.S_z.trans hz1)
  have hk11 : c.k₁ * z * c.k₁⁻¹ ≠ 1 := by
    intro h
    have hz1 : z = 1 := by
      calc z = c.k₁⁻¹ * (c.k₁ * z * c.k₁⁻¹) * c.k₁ := by group
        _ = 1 := by rw [h]; group
    exact c.S.z_ne_one (c.S_z.trans hz1)
  have h1 := hconj c.g₁ hg1Z hg11
  have h2 := hconj c.k₁ hk1Z hk11
  rw [c.Z_eq_inf]
  exact le_inf (le_inf hWQ h1) h2

theorem conj_inf_E_eq_Z_of_le_Q {g : G} (hg : g ∈ c.G2) (hgx : g • c.x0 ≠ c.x0)
    (hQ : c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E ≤ Q z) :
    c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E = c.Z := by
  refine le_antisymm ?_ (c.Z_le_conj_inf_E hg)
  exact c.le_Z_of_le_Q _ (c.G2_le_normalizer_conj_inf_E hg hgx) hQ

end Loc49

end CFSG.Quasithin.H13.AS91
