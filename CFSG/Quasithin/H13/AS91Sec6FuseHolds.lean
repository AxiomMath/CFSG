module

public import CFSG.Quasithin.H13.AS91Sec6FuseQ
public import CFSG.Quasithin.H13.AS91Sec6FuseM24
public import CFSG.Quasithin.H13.AS91Sec6Three

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)
include c

theorem z_mem_Qz : z ∈ Q z := by
  have h := c.S.z_mem_QG
  rw [c.S_QG, c.S_z] at h
  exact h

theorem conj_mem_Q_of_mem_E {e : G} (he : e ∈ c.E) {q : G} (hq : q ∈ Q z) :
    e * q * e⁻¹ ∈ Q z :=
  c.conj_mem_Q (by rw [c.G3_eq_SM]; exact c.E_le_SM he) hq

end Loc49

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (r : ResM24T c)

theorem phi_eq_one_iff (h : ↥c.G1) : r.φ h = 1 ↔ (h : G) ∈ c.E := by
  rw [← MonoidHom.mem_ker, r.ker_eq, Subgroup.mem_subgroupOf]

theorem eq_one_of_mem_compl {l : G} (hl : l ∈ c.compl) (h1 : r.φ ⟨l, c.compl_le_G1 hl⟩ = 1) :
    l = 1 := by
  have h : l ∈ c.compl ⊓ c.E := Subgroup.mem_inf.mpr ⟨hl, (r.phi_eq_one_iff _).mp h1⟩
  rw [c.compl_inf_E] at h
  exact (Subgroup.mem_bot).mp h

theorem exists_lift_compl {σ : S24} (hσ : σ ∈ M24g) :
    ∃ l ∈ c.compl, ∃ hl : l ∈ c.G1, r.φ ⟨l, hl⟩ = σ := by
  obtain ⟨e, he⟩ := r.toResM24.exists_mulEquiv_compl c.compl_le_G1 c.compl_inf_E
    (by rw [sup_comm]; exact c.sup_compl_eq_G1)
  refine ⟨(e.symm ⟨σ, hσ⟩ : ↥c.compl), (e.symm ⟨σ, hσ⟩).2, c.compl_le_G1 (e.symm ⟨σ, hσ⟩).2, ?_⟩
  rw [← he, MulEquiv.apply_symm_apply]

@[expose] noncomputable def complQ : Subgroup G :=
  c.compl ⊓ (r.mapQ.comap r.φ).map c.G1.subtype

theorem mem_complQ {d : G} :
    d ∈ r.complQ ↔ d ∈ c.compl ∧ ∃ hd : d ∈ c.G1, r.φ ⟨d, hd⟩ ∈ r.mapQ := by
  rw [complQ, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hl, ⟨x, hx, rfl⟩⟩
    exact ⟨hl, x.2, hx⟩
  · rintro ⟨hl, hd, hx⟩
    exact ⟨hl, ⟨⟨d, hd⟩, hx, rfl⟩⟩


theorem mapQ_eq_K0base (hr : r.U₀ = M24G.sextFin 0) :
    r.mapQ = M24G.K0base :=
  M24G.eq_K0base_of_normal r.mapQ r.mapQ_le r.isPGroup_mapQ
    (fun σ hσ => by rw [← hr]; exact r.mapQ_smul_U₀ hσ)
    (fun σ hσ hσU n hn => r.mapQ_normal hσ (by rw [hr]; exact hσU) hn) r.card_mapQ

theorem mem_Q_of_mem_annOf
    (hr : r.U₀ = M24G.sextFin 0) {e : G} (he : e ∈ c.E)
    (ha : r.todd ⟨e, he⟩ ∈ M24G.annOf (M24G.octsOf (M24G.sextFin 0))) : e ∈ Q z := by
  have hle : Subgroup.closure {w | ∃ (k : S24) (hk : k ∈ M24G.K0base) (v : W11),
      w = rho11 AutPerm le_rfl ⟨k, M24G.K0base_le hk⟩ v * v⁻¹} ≤
        ((c.E ⊓ Q z).subgroupOf c.E).map r.todd.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, v, rfl⟩
    have hk' : k ∈ r.mapQ := by rw [r.mapQ_eq_K0base hr]; exact hk
    obtain ⟨q, hqQ, hqk⟩ := (r.mem_mapQ).mp hk'
    obtain ⟨⟨e', he'⟩, rfl⟩ := r.todd.surjective v
    have hkq : (⟨k, M24G.K0base_le hk⟩ : ↥AutPerm) = ⟨r.φ q, r.toResM24.φ_mem q⟩ :=
      Subtype.ext hqk.symm
    rw [SetLike.mem_coe, hkq, ← todd_conj r q he', ← map_inv, ← map_mul]
    refine Subgroup.mem_map.mpr ⟨⟨(q : G) * e' * (q : G)⁻¹, c.conj_mem_E q he'⟩ * ⟨e', he'⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨Subtype.prop _, ?_⟩), rfl⟩
    show (q : G) * e' * (q : G)⁻¹ * e'⁻¹ ∈ Q z
    have h := (Q z).mul_mem hqQ (c.conj_mem_Q_of_mem_E he' ((Q z).inv_mem hqQ))
    rwa [show (q : G) * (e' * (q : G)⁻¹ * e'⁻¹) = (q : G) * e' * (q : G)⁻¹ * e'⁻¹ by group] at h
  have hmem := hle (M24G.annOf_le_comm_K0base _ ha)
  obtain ⟨⟨x, hxE⟩, hx, hxe⟩ := Subgroup.mem_map.mp hmem
  rw [← r.eq_of_todd_eq hxE he hxe]
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2

theorem exists_conj_mem_Q_of_mem_E
    (hr : r.U₀ = M24G.sextFin 0)
    {m : G} (hm : m ∈ c.E) : ∃ g ∈ c.G1, g * m * g⁻¹ ∈ Q z := by
  by_cases hm1 : m = 1
  · refine ⟨1, c.G1.one_mem, ?_⟩
    rw [hm1, one_mul, inv_one, mul_one]
    exact (Q z).one_mem
  rcases r.exists_conj_z_or_tE hm hm1 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · refine ⟨a⁻¹, c.G1.inv_mem ha, ?_⟩
    rw [show a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ = z by group]
    exact c.z_mem_Qz
  · obtain ⟨w, hwA, hwd⟩ := M24G.exists_isDuadClass_mem_annOf
    have he := r.elemOf_mem w
    have heQ : r.elemOf w ∈ Q z :=
      r.mem_Q_of_mem_annOf hr he (by rw [r.todd_elemOf]; exact hwA)
    obtain ⟨b, hb, hbt⟩ := (r.isDuadClass_todd_iff he).1 (by rw [r.todd_elemOf]; exact hwd)
    refine ⟨b * a⁻¹, c.G1.mul_mem hb (c.G1.inv_mem ha), ?_⟩
    rw [show b * a⁻¹ * (a * r.tE * a⁻¹) * (b * a⁻¹)⁻¹ = b * r.tE * b⁻¹ by group, hbt]
    exact heQ

theorem complQ_le_Q
    (hr : r.U₀ = M24G.sextFin 0) : r.complQ ≤ Q z := by
  obtain ⟨x₀, hx₀, hx₀U, hfpf, htriv⟩ := M24G.exists_x0
  obtain ⟨y, hyL, hyG1, hyx⟩ := r.exists_lift_compl hx₀
  have hyG3 : y ∈ c.G3 := (r.stab₃ ⟨y, hyG1⟩).mpr (by rw [hyx, hr]; exact hx₀U)
  have hQ := r.mapQ_eq_K0base hr
  refine le_of_injOn_commutator (Q z) c.E r.complQ (fun a ha b hb => E_comm ha hb)
    (fun e he q hq => c.conj_mem_Q_of_mem_E he hq) ?_ (y := y) (fun q hq => c.conj_mem_Q hyG3 hq)
    (fun e he => c.conj_mem_E ⟨y, hyG1⟩ he) ?_ ?_ ?_
  · intro d hd
    obtain ⟨-, hdG1, hdQ⟩ := (r.mem_complQ).mp hd
    obtain ⟨q, hqQ, hqd⟩ := (r.mem_mapQ).mp hdQ
    refine ⟨q, hqQ, (q : G)⁻¹ * d, ?_, by group⟩
    have h : r.φ (q⁻¹ * ⟨d, hdG1⟩) = 1 := by rw [map_mul, map_inv, hqd, inv_mul_cancel]
    exact (r.phi_eq_one_iff _).mp h
  · intro d hd
    obtain ⟨hdL, hdG1, hdQ⟩ := (r.mem_complQ).mp hd
    have hmem : y * d * y⁻¹ ∈ c.G1 := c.G1.mul_mem (c.G1.mul_mem hyG1 hdG1) (c.G1.inv_mem hyG1)
    refine (r.mem_complQ).mpr ⟨c.compl.mul_mem (c.compl.mul_mem hyL hdL) (c.compl.inv_mem hyL),
      hmem, ?_⟩
    have h : r.φ (⟨y, hyG1⟩ * ⟨d, hdG1⟩ * ⟨y, hyG1⟩⁻¹) = x₀ * r.φ ⟨d, hdG1⟩ * x₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, hyx]
    rw [show (⟨y * d * y⁻¹, hmem⟩ : ↥c.G1) = ⟨y, hyG1⟩ * ⟨d, hdG1⟩ * ⟨y, hyG1⟩⁻¹ from rfl, h]
    exact r.mapQ_normal hx₀ (by rw [hr]; exact hx₀U) hdQ
  · intro e he
    have hye : y * e * y⁻¹ * e⁻¹ ∈ c.E := c.E.mul_mem (c.conj_mem_E ⟨y, hyG1⟩ he) (c.E.inv_mem he)
    apply r.mem_Q_of_mem_annOf hr hye
    have hσ : (⟨r.φ ⟨y, hyG1⟩, r.toResM24.φ_mem _⟩ : ↥AutPerm) = ⟨x₀, hx₀⟩ := Subtype.ext hyx
    have h1 : r.todd ⟨y * e * y⁻¹ * e⁻¹, hye⟩ =
        rho11 AutPerm le_rfl ⟨x₀, hx₀⟩ (r.todd ⟨e, he⟩) * (r.todd ⟨e, he⟩)⁻¹ := by
      rw [← hσ, ← todd_conj r ⟨y, hyG1⟩ he, ← map_inv, ← map_mul]
      rfl
    rw [h1]
    exact htriv hx₀ _
  · intro d hd d' hd' h
    have huD : d' * d⁻¹ ∈ r.complQ := r.complQ.mul_mem hd' (r.complQ.inv_mem hd)
    have hyu : y * (d' * d⁻¹) * y⁻¹ = d' * d⁻¹ := by
      calc y * (d' * d⁻¹) * y⁻¹
          = d' * (d'⁻¹ * (y * d' * y⁻¹)) * (d⁻¹ * (y * d * y⁻¹))⁻¹ * d⁻¹ := by group
        _ = d' * d⁻¹ := by rw [← h]; group
    obtain ⟨huL, huG1, huQ⟩ := (r.mem_complQ).mp huD
    have hφu : x₀ * r.φ ⟨d' * d⁻¹, huG1⟩ * x₀⁻¹ = r.φ ⟨d' * d⁻¹, huG1⟩ := by
      rw [← hyx, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg r.φ (Subtype.ext hyu)
    have h1 : r.φ ⟨d' * d⁻¹, huG1⟩ = 1 := hfpf _ (by rw [← hQ]; exact huQ) hφu
    exact (mul_inv_eq_one.mp (r.eq_one_of_mem_compl huL h1)).symm

theorem exists_conj_mem_Q_of_phi_eq
    (hr : r.U₀ = M24G.sextFin 0) {m : G} (hm : m ∈ c.G1)
    (hm2 : m * m = 1) (hπ : r.φ ⟨m, hm⟩ = M24G.piA ∨ r.φ ⟨m, hm⟩ = M24G.piB) :
    ∃ g ∈ c.G1, g * m * g⁻¹ ∈ Q z := by
  have hQ := r.mapQ_eq_K0base hr
  have hmm : (⟨m, hm⟩ : ↥c.G1) * ⟨m, hm⟩ = 1 := Subtype.ext hm2
  have hπK : r.φ ⟨m, hm⟩ ∈ M24G.K0base := by
    rcases hπ with h | h
    · rw [h]; exact M24G.piA_mem
    · rw [h]; exact M24G.piB_mem
  obtain ⟨k, hkL, hkG1, hkπ⟩ := r.exists_lift_compl (M24G.K0base_le hπK)
  have hkQ : k ∈ Q z :=
    r.complQ_le_Q hr ((r.mem_complQ).mpr ⟨hkL, hkG1, by rw [hkπ, hQ]; exact hπK⟩)
  have hk2 : k * k = 1 := by
    apply r.eq_one_of_mem_compl (c.compl.mul_mem hkL hkL)
    show r.φ (⟨k, hkG1⟩ * ⟨k, hkG1⟩) = 1
    rw [map_mul, hkπ, ← map_mul, hmm, map_one]
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hcE : k⁻¹ * m ∈ c.E := by
    have h : r.φ (⟨k, hkG1⟩⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hkπ, inv_mul_cancel]
    exact (r.phi_eq_one_iff _).mp h
  have hcomm : m * k = k * m := by
    have h1 : k⁻¹ * m * (k⁻¹ * m) = 1 := E_sq hcE
    rw [hkinv] at h1
    calc m * k = (k * m)⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hm2, hkinv]
      _ = k * m := inv_eq_of_mul_eq_one_right h1
  have hfix : rho11 AutPerm le_rfl ⟨r.φ ⟨m, hm⟩, r.toResM24.φ_mem _⟩ (r.todd ⟨k⁻¹ * m, hcE⟩) =
      r.todd ⟨k⁻¹ * m, hcE⟩ := by
    have hσ : (⟨r.φ ⟨m, hm⟩, r.toResM24.φ_mem _⟩ : ↥AutPerm) =
        ⟨r.φ ⟨k, hkG1⟩, r.toResM24.φ_mem _⟩ := Subtype.ext hkπ.symm
    rw [hσ, ← todd_conj r ⟨k, hkG1⟩ hcE]
    congr 1
    apply Subtype.ext
    show k * (k⁻¹ * m) * k⁻¹ = k⁻¹ * m
    rw [mul_inv_cancel_left, hkinv, hcomm]
  rcases hπ with h | h
  · have hσA : (⟨r.φ ⟨m, hm⟩, r.toResM24.φ_mem _⟩ : ↥AutPerm) =
        ⟨M24G.piA, M24G.K0base_le M24G.piA_mem⟩ := Subtype.ext h
    rw [hσA] at hfix
    obtain ⟨σ', hσ', hcommA, hA⟩ := M24G.fix_piA_mem_annOf hfix
    obtain ⟨l, hlL, hlG1, hlσ⟩ := r.exists_lift_compl hσ'
    have hlk : l * k * l⁻¹ = k := by
      have hmem : l * k * l⁻¹ * k⁻¹ ∈ c.compl :=
        c.compl.mul_mem (c.compl.mul_mem (c.compl.mul_mem hlL hkL) (c.compl.inv_mem hlL))
          (c.compl.inv_mem hkL)
      have h1 := r.eq_one_of_mem_compl hmem (by
        show r.φ (⟨l, hlG1⟩ * ⟨k, hkG1⟩ * ⟨l, hlG1⟩⁻¹ * ⟨k, hkG1⟩⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hlσ, hkπ, h, hcommA,
          mul_inv_cancel_right, mul_inv_cancel])
      exact mul_inv_eq_one.mp h1
    have hlcE : l * (k⁻¹ * m) * l⁻¹ ∈ c.E := c.conj_mem_E ⟨l, hlG1⟩ hcE
    have hlc : l * (k⁻¹ * m) * l⁻¹ ∈ Q z := by
      apply r.mem_Q_of_mem_annOf hr hlcE
      have hσl : (⟨r.φ ⟨l, hlG1⟩, r.toResM24.φ_mem _⟩ : ↥AutPerm) = ⟨σ', hσ'⟩ := Subtype.ext hlσ
      rw [show r.todd ⟨l * (k⁻¹ * m) * l⁻¹, hlcE⟩ = _ from todd_conj r ⟨l, hlG1⟩ hcE, hσl]
      exact hA
    refine ⟨l, hlG1, ?_⟩
    have h2 : l * m * l⁻¹ = k * (l * (k⁻¹ * m) * l⁻¹) := by
      calc l * m * l⁻¹ = (l * k * l⁻¹) * (l * (k⁻¹ * m) * l⁻¹) := by group
        _ = k * (l * (k⁻¹ * m) * l⁻¹) := by rw [hlk]
    rw [h2]
    exact (Q z).mul_mem hkQ hlc
  · have hσB : (⟨r.φ ⟨m, hm⟩, r.toResM24.φ_mem _⟩ : ↥AutPerm) =
        ⟨M24G.piB, M24G.K0base_le M24G.piB_mem⟩ := Subtype.ext h
    rw [hσB] at hfix
    refine ⟨1, c.G1.one_mem, ?_⟩
    rw [one_mul, inv_one, mul_one, show m = k * (k⁻¹ * m) by group]
    exact (Q z).mul_mem hkQ (r.mem_Q_of_mem_annOf hr hcE (M24G.fix_piB_mem_annOf hfix))

theorem exists_conj_mem_Q_of_not_mem_E
    (hr : r.U₀ = M24G.sextFin 0) {m : G} (hm : m ∈ c.G1)
    (hm2 : m * m = 1) (hmE : m ∉ c.E) : ∃ g ∈ c.G1, g * m * g⁻¹ ∈ Q z := by
  have hσ2 : r.φ ⟨m, hm⟩ * r.φ ⟨m, hm⟩ = 1 := by
    rw [← map_mul, show (⟨m, hm⟩ : ↥c.G1) * ⟨m, hm⟩ = 1 from Subtype.ext hm2, map_one]
  have hσ1 : r.φ ⟨m, hm⟩ ≠ 1 := fun h => hmE ((r.phi_eq_one_iff _).mp h)
  obtain ⟨τ, hτ, hτπ⟩ := M24G.exists_conj_piA_or_piB (r.toResM24.φ_mem _) hσ2 hσ1
  obtain ⟨s, hs⟩ := r.toResM24.exists_φ_eq hτ
  have hm₁ : (s : G) * m * (s : G)⁻¹ ∈ c.G1 := c.G1.mul_mem (c.G1.mul_mem s.2 hm) (c.G1.inv_mem s.2)
  have hφ : r.φ ⟨(s : G) * m * (s : G)⁻¹, hm₁⟩ = τ * r.φ ⟨m, hm⟩ * τ⁻¹ := by
    rw [show (⟨(s : G) * m * (s : G)⁻¹, hm₁⟩ : ↥c.G1) = s * ⟨m, hm⟩ * s⁻¹ from rfl, map_mul,
      map_mul, map_inv, show r.φ s = τ from hs]
  have hm₁2 : (s : G) * m * (s : G)⁻¹ * ((s : G) * m * (s : G)⁻¹) = 1 := by
    rw [show (s : G) * m * (s : G)⁻¹ * ((s : G) * m * (s : G)⁻¹) = (s : G) * (m * m) * (s : G)⁻¹ by
      group, hm2, mul_one, mul_inv_cancel]
  obtain ⟨g, hg, hgm⟩ := r.exists_conj_mem_Q_of_phi_eq hr hm₁ hm₁2 (by rw [hφ]; exact hτπ)
  refine ⟨g * s, c.G1.mul_mem hg s.2, ?_⟩
  rw [show g * (s : G) * m * (g * (s : G))⁻¹ = g * ((s : G) * m * (s : G)⁻¹) * g⁻¹ by group]
  exact hgm

end ResM24T

theorem stmt6_4Fuse_holds :
    Stmt6_4Fuse := by
  intro G _ _ z hJ c m hm hm2
  obtain ⟨r₀⟩ := resM24T_holds G z hJ c
  obtain ⟨r, hr⟩ := r₀.exists_U₀_eq (M24G.isSextet_sextFin (by norm_num : 0 < 1771))
  by_cases hmE : m ∈ c.E
  · exact r.exists_conj_mem_Q_of_mem_E hr hmE
  · exact r.exists_conj_mem_Q_of_not_mem_E hr hm hm2 hmE

theorem stmt6_5u_holds :
    Stmt6_5u :=
  stmt6_5u_of_fuse stmt6_3_holds stmt6_4Fuse_holds

end CFSG.Quasithin.H13.AS91
