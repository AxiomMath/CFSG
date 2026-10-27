module

public import CFSG.Quasithin.H13.AS91Sec5Stmt532
public import CFSG.Quasithin.H13.AS91Sec6Fuse
public import CFSG.Quasithin.H13.AS91Sec7Smul
public import CFSG.Quasithin.H13.AS91Sec5ToddRes

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

@[expose] def NormalTwoSextet : Prop :=
  ∀ {U : Finset (Finset (Fin 24))}, IsSextet U → ∀ N : Subgroup S24, N ≤ M24g → IsPGroup 2 N →
    (∀ σ ∈ N, σ • U = U) → (∀ σ ∈ M24g, σ • U = U → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) →
    N = ⊥ ∨ Nat.card N = 2 ^ 6

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem map_conj_E_eq {g h : G} (hgh : g • c.x0 = h • c.x0) :
    c.E.map (MulAut.conj g).toMonoidHom = c.E.map (MulAut.conj h).toMonoidHom := by
  have hk : g⁻¹ * h ∈ c.G1 := by
    rw [← c.stab_x0, mem_stabilizer_iff, mul_smul, ← hgh, inv_smul_smul]
  have hE : c.E.map (MulAut.conj (g⁻¹ * h)).toMonoidHom = c.E :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hk)
  calc c.E.map (MulAut.conj g).toMonoidHom
      = (c.E.map (MulAut.conj (g⁻¹ * h)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [hE]
    _ = c.E.map (MulAut.conj h).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]

theorem smul_eq_of_mem_map_conj {h y : G} (hy : y ∈ c.E.map (MulAut.conj h).toMonoidHom) :
    y • (h • c.x0) = h • c.x0 := by
  obtain ⟨e, he, rfl⟩ := hy
  have hex : e • c.x0 = c.x0 := c.smul_x0_of_mem (c.E_le_G1 he)
  show (h * e * h⁻¹) • (h • c.x0) = h • c.x0
  rw [mul_smul, mul_smul, inv_smul_smul, hex]

theorem z_mem_map_conj {h : G} (hh : h ∈ c.G3) : z ∈ c.E.map (MulAut.conj h).toMonoidHom := by
  refine ⟨z, c.z_mem_E, ?_⟩
  show h * z * h⁻¹ = z
  have := c.G3_comm_z (inv_mem hh)
  simpa [mul_assoc] using this

theorem exists_G3_map_conj_eq {g : G} (hg : c.E.map (MulAut.conj g).toMonoidHom ≤ c.G3) :
    ∃ h ∈ c.G3, c.E.map (MulAut.conj g).toMonoidHom = c.E.map (MulAut.conj h).toMonoidHom := by
  set P : Subgroup G := c.E.map (MulAut.conj g).toMonoidHom with hP
  have hP2 : IsPGroup 2 ↥P := c.E_elem.isPGroup.map (MulAut.conj g).toMonoidHom
  have hTH : (c.T : Subgroup G) ≤ c.G3 := c.T_le.trans (le_inf_iff.mp c.G13_le_inf).2
  obtain ⟨c₀, hc₀G3, hc₀P⟩ :=
    CFSG.QuasiDihedralFusion.exists_conj_le_sylow (K := c.G3) (S := c.T) hTH P hg hP2
  set A : Subgroup G := P.map (MulAut.conj c₀).toMonoidHom with hA
  have hAeq : A = c.E.map (MulAut.conj (c₀ * g)).toMonoidHom := by
    rw [hA, hP, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hAcomm : IsMulCommutative ↥A := by
    rw [hAeq]
    exact (CFSG.isMulCommutative_map_mulEquiv_iff (MulAut.conj (c₀ * g)) c.E).mpr c.E_elem.1
  have hAcard : Nat.card ↥A = Nat.card ↥(CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj (c₀ * g)).injective, c.E_eq]
  have hJcomm : IsMulCommutative (CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [← c.E_eq]
    exact c.E_elem.1
  have hAle : A ≤ c.E := by
    have h := CFSG.GroupTheory.le_thompsonSubgroup_of_isMulCommutative_of_card_eq
      (P := (c.T : Subgroup G)) (A := A) hc₀P hAcomm hJcomm hAcard
    rw [c.E_eq]
    exact h
  have hAE : A = c.E := Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, c.E_eq])
  refine ⟨c₀⁻¹, inv_mem hc₀G3, ?_⟩
  calc P = A.map (MulAut.conj c₀⁻¹).toMonoidHom := by
        rw [hA, Subgroup.map_map]
        conv_lhs => rw [← Subgroup.map_id P]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
    _ = c.E.map (MulAut.conj c₀⁻¹).toMonoidHom := by rw [hAE]

theorem map_conj_E_eq_of_le_G1 {g : G} (hg : c.E.map (MulAut.conj g).toMonoidHom ≤ c.G1) :
    c.E.map (MulAut.conj g).toMonoidHom = c.E := by
  set P : Subgroup G := c.E.map (MulAut.conj g).toMonoidHom with hP
  have hP2 : IsPGroup 2 ↥P := c.E_elem.isPGroup.map (MulAut.conj g).toMonoidHom
  have hTG1 : (c.T : Subgroup G) ≤ c.G1 := c.T_le.trans (le_inf_iff.mp c.G13_le_inf).1
  obtain ⟨c₀, hc₀G1, hc₀P⟩ :=
    CFSG.QuasiDihedralFusion.exists_conj_le_sylow (K := c.G1) (S := c.T) hTG1 P hg hP2
  set A : Subgroup G := P.map (MulAut.conj c₀).toMonoidHom with hA
  have hAeq : A = c.E.map (MulAut.conj (c₀ * g)).toMonoidHom := by
    rw [hA, hP, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hAcomm : IsMulCommutative ↥A := by
    rw [hAeq]
    exact (CFSG.isMulCommutative_map_mulEquiv_iff (MulAut.conj (c₀ * g)) c.E).mpr c.E_elem.1
  have hAcard : Nat.card ↥A = Nat.card ↥(CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj (c₀ * g)).injective, c.E_eq]
  have hJcomm : IsMulCommutative (CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [← c.E_eq]
    exact c.E_elem.1
  have hAle : A ≤ c.E := by
    have h := CFSG.GroupTheory.le_thompsonSubgroup_of_isMulCommutative_of_card_eq
      (P := (c.T : Subgroup G)) (A := A) hc₀P hAcomm hJcomm hAcard
    rw [c.E_eq]
    exact h
  have hAE : A = c.E := Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, c.E_eq])
  have hEc : c.E.map (MulAut.conj c₀⁻¹).toMonoidHom = c.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hc₀G1)
  calc P = A.map (MulAut.conj c₀⁻¹).toMonoidHom := by
        rw [hA, Subgroup.map_map]
        conv_lhs => rw [← Subgroup.map_id P]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
    _ = c.E := by rw [hAE, hEc]

theorem exists_inter_map_conj_eq_of_adj (h2c : Stmt5_2c) (hJ : HypJ4 G z) {h : G}
    (hadj : c.Delta.Adj c.x0 (h • c.x0)) :
    ∃ k ∈ c.G1, c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom =
      c.Z.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨hne, m, hxm, hym⟩ := colGraph_adj.mp hadj
  obtain ⟨k, hk⟩ := c.exists_G1_smul_l0 hxm
  have hkx : (k : G) • c.x0 = c.x0 := c.smul_x0_of_mem k.2
  set y' : G ⧸ c.G1 := (k : G)⁻¹ • (h • c.x0) with hy'
  have hy'L : y' ∈ c.ptsL := by
    have h1 : CInc c.G1 c.G2 y' ((k : G)⁻¹ • m) := (cInc_smul c.G1 c.G2 _ _ _).mpr hym
    rw [← hk, inv_smul_smul] at h1
    exact h1
  have hy'x : y' ≠ c.x0 := by
    intro h'
    apply hne
    rw [hy'] at h'
    rw [← smul_inv_smul (k : G) (h • c.x0), h', hkx]
  obtain ⟨g, hgG2, hgy⟩ := (c.mem_ptsL_iff y').mp hy'L
  have hgx : g • c.x0 = y' := by
    rw [← hgy]
    show g • ((1 : G) : G ⧸ c.G1) = (g : G ⧸ c.G1)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hZ := h2c G z hJ c y' hy'L hy'x g hgG2 hgx
  have hkg : ((k : G) * g) • c.x0 = h • c.x0 := by
    rw [mul_smul, hgx, hy', smul_inv_smul]
  refine ⟨k, k.2, ?_⟩
  rw [← c.map_conj_E_eq hkg]
  have hEk : c.E.map (MulAut.conj (k : G)).toMonoidHom = c.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp k.2
  have hmapg : c.E.map (MulAut.conj ((k : G) * g)).toMonoidHom =
      (c.E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (k : G)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hinj : Function.Injective (MulAut.conj (k : G)).toMonoidHom :=
    (MulAut.conj (k : G)).injective
  rw [hmapg, ← hZ, Subgroup.map_inf_eq _ _ _ hinj, hEk, inf_comm]

theorem card_inter_map_conj_of_adj (h2c : Stmt5_2c) (hJ : HypJ4 G z) {h : G}
    (hadj : c.Delta.Adj c.x0 (h • c.x0)) :
    Nat.card ↥(c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom) = 8 := by
  obtain ⟨k, -, hk⟩ := c.exists_inter_map_conj_eq_of_adj h2c hJ hadj
  rw [hk, Subgroup.card_map_of_injective (MulAut.conj k).injective, c.card_Z]

theorem inter_map_conj_of_adj (h2c : Stmt5_2c) (hJ : HypJ4 G z) {h : G}
    (hadj : c.Delta.Adj c.x0 (h • c.x0)) {e : G}
    (he : e ∈ c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom) :
    e = 1 ∨ ∃ m ∈ c.G1, m * z * m⁻¹ = e := by
  obtain ⟨k, hkG1, hk⟩ := c.exists_inter_map_conj_eq_of_adj h2c hJ hadj
  rw [hk] at he
  obtain ⟨a, haZ, rfl⟩ := he
  by_cases ha1 : a = 1
  · left
    rw [ha1, map_one]
  · right
    have hz1 : z ≠ 1 := fun h' => c.S.z_ne_one (c.S_z.trans h')
    obtain ⟨k', hk'K, hk'⟩ := c.exists_K_conj c.z_mem_Z haZ hz1 ha1
    refine ⟨k * k', c.G1.mul_mem hkG1 (c.K_le_G1 hk'K), ?_⟩
    show k * k' * z * (k * k')⁻¹ = k * a * k⁻¹
    rw [← hk']
    group

theorem smul_mem_farP_of_mem {g : G} (hg1 : g ∈ c.G1) (hg3 : g ∈ c.G3) {u : G ⧸ c.G1}
    (hu : u ∈ c.farP) : g • u ∈ c.farP := by
  obtain ⟨huP, hux, hnu⟩ := hu
  have hfix : g • c.x0 = c.x0 := c.smul_x0_of_mem hg1
  refine ⟨?_, ?_, ?_⟩
  · have h := (cInc_smul c.G1 c.G3 g u c.pi0).mpr huP
    rw [c.G3_smul_pi0 hg3] at h
    exact h
  · intro h
    exact hux (MulAction.injective g (h.trans hfix.symm))
  · intro h
    apply hnu
    rw [← hfix] at h
    exact (c.adj_smul_iff g).mp h

theorem inv_smul_x0_mem_farP {h : G} (hh : h ∈ c.G3) (hu : h • c.x0 ∈ c.farP) :
    h⁻¹ • c.x0 ∈ c.farP := by
  obtain ⟨-, hux, hnu⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · refine (c.mem_ptsP_iff _).mpr ⟨h⁻¹, inv_mem hh, ?_⟩
    show ((h⁻¹ : G) : G ⧸ c.G1) = h⁻¹ • ((1 : G) : G ⧸ c.G1)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  · intro h'
    apply hux
    calc h • c.x0 = h • (h⁻¹ • c.x0) := by rw [h']
      _ = c.x0 := smul_inv_smul h c.x0
  · intro h'
    apply hnu
    have h2 := (c.adj_smul_iff h).mpr h'
    rw [smul_inv_smul] at h2
    exact h2.symm

theorem card_map_mul_card_inf (r : ResM24T c) (A : Subgroup G) (hA : A ≤ c.G1) :
    Nat.card ↥((A.subgroupOf c.G1).map r.φ) * Nat.card ↥(A ⊓ c.E) = Nat.card A := by
  have h := Subgroup.card_ker_mul_card_range (r.φ.domRestrict (A.subgroupOf c.G1))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, r.ker_eq] at h
  have hk : Nat.card ↥((c.E.subgroupOf c.G1).subgroupOf (A.subgroupOf c.G1)) =
      Nat.card ↥(A ⊓ c.E) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥(A.subgroupOf c.G1)) : ↥c.G1),
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (x : ↥(A.subgroupOf c.G1)).2,
            Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp x.2)⟩⟩
        invFun := fun y => ⟨⟨⟨y, hA (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h
  rw [mul_comm]
  exact h


theorem ncard_farP (r : ResM24 c) (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) :
    c.farP.ncard = 16 :=
  r.ncard_far_onP hLU hG2 hJ c.x0_mem_ptsP

theorem inf_stab_eq_Epl (r : ResM24T c) (hI : Sec7Inputs) (hJ : HypJ4 G z) {u : G ⧸ c.G1}
    (hu : u ∈ c.farP) : c.E ⊓ stabilizer G u = c.Epl c.pi0 := by
  obtain ⟨huP, hux, hnu⟩ := hu
  have hle := c.inf_stab_le_Epl hI.s533 hJ hux hnu huP
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [r.card_Epl c.x0_mem_ptsP]
  exact c.card_inf_stab_ge (c.ncard_farP r.toResM24 hI.lineU hI.gamma2 hJ) ⟨huP, hux, hnu⟩

theorem exists_E_smul_eq (r : ResM24T c) (hI : Sec7Inputs) (hJ : HypJ4 G z) {u v : G ⧸ c.G1}
    (hu : u ∈ c.farP) (hv : v ∈ c.farP) : ∃ e ∈ c.E, e • u = v := by
  have hfar := c.ncard_farP r.toResM24 hI.lineU hI.gamma2 hJ
  have horb : MulAction.orbit ↥c.E u ⊆ c.farP := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    exact c.smul_mem_farP he hu
  have hidx : (stabilizer G u).relIndex c.E = (MulAction.orbit ↥c.E u).ncard := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hmul := Subgroup.relIndex_mul_card (H := stabilizer G u) (K := c.E)
  rw [hidx, c.card_E, inf_comm (stabilizer G u) c.E, c.inf_stab_eq_Epl r hI hJ hu,
    r.card_Epl c.x0_mem_ptsP] at hmul
  have hob : (MulAction.orbit ↥c.E u).ncard = 16 := by omega
  have heq : MulAction.orbit ↥c.E u = c.farP :=
    Set.eq_of_subset_of_ncard_le horb (by rw [hob, hfar]) (Set.toFinite _)
  rw [← heq] at hv
  obtain ⟨⟨e, he⟩, rfl⟩ := hv
  exact ⟨e, he, rfl⟩

theorem inter_map_conj_eq_of_far (r : ResM24T c) (hI : Sec7Inputs) (hJ : HypJ4 G z)
    (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet) {h : G} (hh : h ∈ c.G3)
    (hfar : h • c.x0 ∈ c.farP) :
    c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom = zpowers z := by
  have hw := c.inv_smul_x0_mem_farP hh hfar
  set P : Subgroup G := c.Epl c.pi0 with hP
  have hPw : c.E ⊓ stabilizer G (h⁻¹ • c.x0) = P := c.inf_stab_eq_Epl r hI hJ hw
  have hPu : c.E ⊓ stabilizer G (h • c.x0) = P := c.inf_stab_eq_Epl r hI hJ hfar
  have hPE : P ≤ c.E := hPu ▸ inf_le_left
  set Ph : Subgroup G := P.map (MulAut.conj h).toMonoidHom with hPh
  have hinjh : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have hEh : c.E.map (MulAut.conj h).toMonoidHom ⊓ stabilizer G c.x0 = Ph := by
    rw [hPh, ← hPw, Subgroup.map_inf_eq _ _ _ hinjh,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, smul_inv_smul]
  have h1 : c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom ≤ P := by
    intro x hx
    rw [← hPu]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
      mem_stabilizer_iff.mpr (c.smul_eq_of_mem_map_conj (Subgroup.mem_inf.mp hx).2)⟩
  have h2 : c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom ≤ Ph := by
    intro x hx
    rw [← hEh]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
    rw [c.stab_x0]
    exact c.E_le_G1 (Subgroup.mem_inf.mp hx).1
  have hPhE : Ph ⊓ c.E ≤ P := by
    intro x hx
    rw [← hPu]
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxEh : x ∈ c.E.map (MulAut.conj h).toMonoidHom := by
      rw [← hEh] at hx1
      exact (Subgroup.mem_inf.mp hx1).1
    exact Subgroup.mem_inf.mpr ⟨hx2, mem_stabilizer_iff.mpr (c.smul_eq_of_mem_map_conj hxEh)⟩
  have hPhG1 : Ph ≤ c.G1 := by
    have h' := (inf_le_right : c.E.map (MulAut.conj h).toMonoidHom ⊓ stabilizer G c.x0 ≤
      stabilizer G c.x0)
    rw [hEh, c.stab_x0] at h'
    exact h'
  have hPhG3 : Ph ≤ c.G3 := by
    rintro _ ⟨p, hp, rfl⟩
    exact c.G3.mul_mem (c.G3.mul_mem hh (c.E_le_G3 (hPE hp))) (inv_mem hh)
  have hcardP : Nat.card P = 2 ^ 7 := r.card_Epl c.x0_mem_ptsP
  have hcardPh : Nat.card Ph = 2 ^ 7 := by
    rw [hPh, Subgroup.card_map_of_injective hinjh, hcardP]
  set N : Subgroup S24 := (Ph.subgroupOf c.G1).map r.φ with hNdef
  have hNcard := c.card_map_mul_card_inf r Ph hPhG1
  rw [hcardPh] at hNcard
  have hNM : N ≤ M24g := by
    rw [hNdef, ← r.range_eq]
    exact Subgroup.map_le_range _ _
  have hN2 : IsPGroup 2 N := by
    have hc : Nat.card ↥(Ph.subgroupOf c.G1) = 2 ^ 7 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPhG1).toEquiv, hcardPh]
    exact (IsPGroup.of_card hc).map r.φ
  have hNU : ∀ σ ∈ N, σ • r.U₀ = r.U₀ := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
    exact (r.stab₃ x).mp (hPhG3 (Subgroup.mem_subgroupOf.mp hx))
  have hnorm : ∀ σ ∈ M24g, σ • r.U₀ = r.U₀ → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N := by
    intro σ hσ hσU n hn
    obtain ⟨m, hm⟩ := r.toResM24.exists_φ_eq hσ
    have hmG3 : (m : G) ∈ c.G3 := (r.stab₃ m).mpr (by rw [show r.φ m = σ from hm]; exact hσU)
    have hmu : (m : G) • (h • c.x0) ∈ c.farP := c.smul_mem_farP_of_mem m.2 hmG3 hfar
    obtain ⟨e, he, heu⟩ := c.exists_E_smul_eq r hI hJ hmu hfar
    set m' : ↥c.G1 := ⟨e * m, c.G1.mul_mem (c.E_le_G1 he) m.2⟩ with hm'
    have hφe : r.φ ⟨e, c.E_le_G1 he⟩ = 1 := by
      rw [← MonoidHom.mem_ker, r.ker_eq]
      exact Subgroup.mem_subgroupOf.mpr he
    have hφm' : r.φ m' = σ := by
      have : m' = ⟨e, c.E_le_G1 he⟩ * m := rfl
      rw [this, map_mul, hφe, one_mul]
      exact hm
    have hm'u : (m' : G) • (h • c.x0) = h • c.x0 := by
      show (e * m) • (h • c.x0) = h • c.x0
      rw [mul_smul, heu]
    have hm'Ph : ∀ x ∈ Ph, (m' : G) * x * (m' : G)⁻¹ ∈ Ph := by
      intro x hx
      rw [← hEh] at hx ⊢
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have heq : c.E.map (MulAut.conj ((m' : G) * h)).toMonoidHom =
            c.E.map (MulAut.conj h).toMonoidHom :=
          c.map_conj_E_eq (by rw [mul_smul]; exact hm'u)
        rw [← heq]
        obtain ⟨e', he', rfl⟩ := hx1
        exact ⟨e', he', by simp [MulAut.conj_apply, mul_assoc]⟩
      · rw [c.stab_x0] at hx2 ⊢
        exact c.G1.mul_mem (c.G1.mul_mem m'.2 hx2) (inv_mem m'.2)
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨m' * x * m'⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := hm'Ph _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
    · rw [map_mul, map_mul, map_inv, hφm']
  rcases hN r.isSextet_U₀ N hNM hN2 hNU hnorm with hbot | h64
  · exfalso
    have hN1 : Nat.card N = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hN1, one_mul] at hNcard
    have hPhle : Ph ≤ c.E := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Ph ⊓ c.E ≤ Ph)
        (by rw [hNcard, hcardPh])
      rw [← this]
      exact inf_le_right
    have hPhP : Ph = P :=
      Subgroup.eq_of_le_of_card_ge (fun x hx => hPhE (Subgroup.mem_inf.mpr ⟨hx, hPhle hx⟩))
        (by rw [hcardP, hcardPh])
    set L : Subgroup G := c.G3 ⊓ normalizer (P : Set G) with hL
    have hnormP : ∀ g ∈ c.G1, g ∈ c.G3 → g ∈ normalizer (P : Set G) := by
      intro g hg1 hg3
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hgu := c.smul_mem_farP_of_mem hg1 hg3 hfar
      have hinjg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
      calc P.map (MulAut.conj g).toMonoidHom
          = (c.E ⊓ stabilizer G (h • c.x0)).map (MulAut.conj g).toMonoidHom := by rw [hPu]
        _ = c.E ⊓ stabilizer G (g • (h • c.x0)) := by
            have hEg : c.E.map (MulAut.conj g).toMonoidHom = c.E :=
              Subgroup.mem_normalizer_iff_map_conj_eq.mp hg1
            rw [Subgroup.map_inf_eq _ _ _ hinjg,
              ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hEg]
        _ = P := c.inf_stab_eq_Epl r hI hJ hgu
    have hG13L : c.G3 ⊓ c.G1 ≤ L := fun g hg =>
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1,
        hnormP g (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hg).1⟩
    have hhL : h ∈ L := by
      refine Subgroup.mem_inf.mpr ⟨hh, ?_⟩
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hPhP
    rcases hmax G z hJ c L hG13L inf_le_left with hL1 | hL3
    · have hhG1 : h ∈ c.G1 := by
        rw [hL1] at hhL
        exact (Subgroup.mem_inf.mp hhL).2
      exact hfar.2.1 (c.smul_x0_of_mem hhG1)
    ·
      have h60 := r.toResM24.ncard_adj_onP hI.lineU hI.gamma2 hJ c.x0_mem_ptsP
      obtain ⟨b, hbP, hbadj⟩ : ∃ b, c.OnP b c.pi0 ∧ c.Delta.Adj c.x0 b := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have : {b | c.OnP b c.pi0 ∧ c.Delta.Adj c.x0 b} = ∅ := by
          ext b
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact hne b
        rw [this, Set.ncard_empty] at h60
        exact absurd h60 (by norm_num)
      obtain ⟨h', hh'G3, hh'b⟩ := (c.mem_ptsP_iff b).mp hbP
      have hh'x : h' • c.x0 = b := by
        rw [← hh'b]
        show h' • ((1 : G) : G ⧸ c.G1) = (h' : G ⧸ c.G1)
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      have hh'L : h' ∈ L := by rw [hL3]; exact hh'G3
      have hPmap : P.map (MulAut.conj h').toMonoidHom = P :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_inf.mp hh'L).2
      have hPle : P ≤ c.E ⊓ c.E.map (MulAut.conj h').toMonoidHom := by
        intro x hx
        refine Subgroup.mem_inf.mpr ⟨hPE hx, ?_⟩
        rw [← hPmap] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact ⟨p, hPE hp, rfl⟩
      have h8 := c.card_inter_map_conj_of_adj h2c hJ (h := h') (by rw [hh'x]; exact hbadj)
      have := Subgroup.card_le_of_le hPle
      rw [hcardP, h8] at this
      norm_num at this
  · have hcard2 : Nat.card ↥(Ph ⊓ c.E) = 2 := by
      rw [h64] at hNcard
      omega
    have hle : c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom ≤ Ph ⊓ c.E := le_inf h2 inf_le_left
    have hzle : zpowers z ≤ c.E ⊓ c.E.map (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨c.z_mem_E, c.z_mem_map_conj hh⟩
    have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hJ.orderOf_z]
    refine (Subgroup.eq_of_le_of_card_ge hzle ?_).symm
    rw [hzcard]
    exact (Subgroup.card_le_of_le hle).trans hcard2.le

theorem map_conj_inv_inter_map_conj {m g : G} (hm : m ∈ c.G1) :
    (c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom =
      c.E ⊓ c.E.map (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj m⁻¹).toMonoidHom := (MulAut.conj m⁻¹).injective
  have hEm : c.E.map (MulAut.conj m⁻¹).toMonoidHom = c.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hm)
  rw [Subgroup.map_inf_eq _ _ _ hinj, hEm, Subgroup.map_map]
  congr 2
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem inter_map_conj_of_isConj_z (r : ResM24T c) (hI : Sec7Inputs) (hJ : HypJ4 G z)
    (hmax : Stmt5_Max13) (h2c : Stmt5_2c) (hN : NormalTwoSextet) {g : G}
    (hne : c.E.map (MulAut.conj g).toMonoidHom ≠ c.E) {v : G}
    (hv : v ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) (hvz : IsConj v z) {w : G}
    (hw : w ∈ c.E ⊓ c.E.map (MulAut.conj g).toMonoidHom) :
    w = 1 ∨ ∃ m ∈ c.G1, m * z * m⁻¹ = w := by
  obtain ⟨m, hmG1, hmv⟩ := c.exists_G1_conj_of_isConj_z (Subgroup.mem_inf.mp hv).1 hvz
  set g' : G := m⁻¹ * g with hg'
  have hconj := c.map_conj_inv_inter_map_conj (g := g) hmG1
  have hzmem : z ∈ c.E ⊓ c.E.map (MulAut.conj g').toMonoidHom := by
    rw [← hconj]
    refine ⟨v, hv, ?_⟩
    show m⁻¹ * v * m⁻¹⁻¹ = z
    rw [← hmv]
    group
  have hwmem : m⁻¹ * w * m ∈ c.E ⊓ c.E.map (MulAut.conj g').toMonoidHom := by
    rw [← hconj]
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  have hEg'H : c.E.map (MulAut.conj g').toMonoidHom ≤ c.G3 := by
    intro x hx
    rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hzE := (Subgroup.mem_inf.mp hzmem).2
    obtain ⟨a, ha, rfl⟩ := hzE
    obtain ⟨b, hb, rfl⟩ := hx
    have hab : a * b = b * a := congrArg Subtype.val (c.E_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g' * a * g'⁻¹ * (g' * b * g'⁻¹) = g' * (a * b) * g'⁻¹ := by group
      _ = g' * (b * a) * g'⁻¹ := by rw [hab]
      _ = g' * b * g'⁻¹ * (g' * a * g'⁻¹) := by group
  obtain ⟨h, hhG3, hEh⟩ := c.exists_G3_map_conj_eq hEg'H
  rw [hEh] at hwmem
  have hhG1 : h ∉ c.G1 := by
    intro hh1
    apply hne
    have hE' : c.E.map (MulAut.conj h).toMonoidHom = c.E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hh1
    have hEg : c.E.map (MulAut.conj g).toMonoidHom =
        (c.E.map (MulAut.conj g').toMonoidHom).map (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [hg', MulAut.conj_apply, mul_assoc]
    rw [hEg, hEh, hE']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmG1
  have hux : h • c.x0 ≠ c.x0 := fun h' => hhG1 (by rw [← c.stab_x0]; exact h')
  have huP : h • c.x0 ∈ c.ptsP := by
    refine (c.mem_ptsP_iff _).mpr ⟨h, hhG3, ?_⟩
    show (h : G ⧸ c.G1) = h • ((1 : G) : G ⧸ c.G1)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hback : ∀ w' : G, (w' = 1 ∨ ∃ k ∈ c.G1, k * z * k⁻¹ = w') → m⁻¹ * w * m = w' →
      (w = 1 ∨ ∃ k ∈ c.G1, k * z * k⁻¹ = w) := by
    intro w' hw' hww'
    rcases hw' with rfl | ⟨k, hkG1, hk⟩
    · left
      have : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
      rw [this, hww']
      group
    · right
      refine ⟨m * k, c.G1.mul_mem hmG1 hkG1, ?_⟩
      have : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
      rw [this, hww', ← hk]
      group
  by_cases hadj : c.Delta.Adj c.x0 (h • c.x0)
  · exact hback _ (c.inter_map_conj_of_adj h2c hJ hadj hwmem) rfl
  · have hfar : h • c.x0 ∈ c.farP := ⟨huP, hux, hadj⟩
    rw [c.inter_map_conj_eq_of_far r hI hJ hmax h2c hN hhG3 hfar] at hwmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwmem
    have hmod : z ^ (n % 2) = m⁻¹ * w * m := by
      rw [← hn, show (2 : ℤ) = ((orderOf z : ℕ) : ℤ) by rw [hJ.orderOf_z]; rfl, zpow_mod_orderOf]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [h0, zpow_zero] at hmod
      exact hback 1 (Or.inl rfl) hmod.symm
    · rw [h1, zpow_one] at hmod
      exact hback z (Or.inr ⟨1, c.G1.one_mem, by group⟩) hmod.symm

end Loc49

end CFSG.Quasithin.H13.AS91
