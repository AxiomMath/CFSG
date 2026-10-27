module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTr
import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

namespace GGSFTr

variable {t : StatedLieTag} {n f p : ℕ} {M : GGKGModel t n f p} {G : Type} [Group G]
  {ψ : (ggU t n f).K →* G} {Bs : Subgroup G} (T : GGSFTr t n f p M ψ Bs)

private lemma mul_conj_inv_cancel {Q : Type*} [Group Q] (κ x : Q) :
    κ * (κ⁻¹ * x * κ) * κ⁻¹ = x := by
  rw [mul_assoc κ⁻¹ x κ, mul_inv_cancel_left κ (x * κ), mul_inv_cancel_right x κ]

private lemma orderOf_psi_eq (TT : GGSFTr t n f p M ψ Bs) (r : (ggU t n f).K) :
    orderOf (ψ r) = orderOf (ggPsiU t n f r) := by
  have h1 : orderOf (⟨ψ r, TT.psi_le ⟨r, rfl⟩⟩ : TT.N) = orderOf (ggPsiU t n f r) := by
    rw [← orderOf_injective TT.hom TT.hom_inj ⟨ψ r, TT.psi_le ⟨r, rfl⟩⟩, TT.hom_psi r]
    rw [show TT.kappa * ggPsiU t n f r * TT.kappa⁻¹ =
        (MulAut.conj TT.kappa) (ggPsiU t n f r) from by rw [MulAut.conj_apply]]
    exact MulEquiv.orderOf_eq (MulAut.conj TT.kappa) _
  calc orderOf (ψ r) = orderOf (⟨ψ r, TT.psi_le ⟨r, rfl⟩⟩ : TT.N) :=
        Subgroup.orderOf_coe (⟨ψ r, TT.psi_le ⟨r, rfl⟩⟩ : TT.N)
    _ = orderOf (ggPsiU t n f r) := h1

private lemma exists_mem_Bs_of_hom_eq (TT : GGSFTr t n f p M ψ Bs) {m : G}
    (hm : m ∈ TT.N) {a : GGAutU t n f} (haB : a ∈ M.Bfull)
    (hainn : a ∈ (ggPsiU t n f).range) (hmA : TT.hom ⟨m, hm⟩ = a) : m ∈ Bs := by
  have hmem : a ∈ (Bs.subgroupOf TT.N).map TT.hom := by
    rcases TT.img with h | h
    · rw [h]; exact haB
    · rw [h]; exact Subgroup.mem_inf.mpr ⟨haB, hainn⟩
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp hmem
  have hyy : y = ⟨m, hm⟩ := TT.hom_inj (by rw [hya, hmA])
  have hys : (y : G) ∈ Bs := Subgroup.mem_subgroupOf.mp hy
  rw [hyy] at hys
  exact hys

private lemma conj_mem_Bs (TT : GGSFTr t n f p M ψ Bs) {m : G} (hm : m ∈ TT.N)
    {a : GGAutU t n f} (hainn : a ∈ (ggPsiU t n f).range)
    (hanorm : a ∈ Subgroup.normalizer (M.Bfull : Set (GGAutU t n f)))
    (hmA : TT.hom ⟨m, hm⟩ = a) (b : Bs) : m * (b : G) * m⁻¹ ∈ Bs := by
  have hbN : (b : G) ∈ TT.N := TT.bs_le b.2
  have hmemN : m * (b : G) * m⁻¹ ∈ TT.N :=
    TT.N.mul_mem (TT.N.mul_mem hm hbN) (TT.N.inv_mem hm)
  have hhom : TT.hom ⟨m * (b : G) * m⁻¹, hmemN⟩ = a * TT.toHom b * a⁻¹ := by
    have h1 : (⟨m * (b : G) * m⁻¹, hmemN⟩ : TT.N) =
        ⟨m, hm⟩ * ⟨(b : G), hbN⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, hmA, ← TT.toHom_apply b]
  have hB : a * TT.toHom b * a⁻¹ ∈ M.Bfull :=
    (Subgroup.mem_normalizer_iff.mp hanorm (TT.toHom b)).mp (TT.toHom_mem b)
  have hmem : a * TT.toHom b * a⁻¹ ∈ (Bs.subgroupOf TT.N).map TT.hom := by
    rcases TT.img with h | h
    · rw [h]; exact hB
    · rw [h]; refine Subgroup.mem_inf.mpr ⟨hB, ?_⟩
      have hbinn : TT.toHom b ∈ (ggPsiU t n f).range := by
        have hb := TT.toHom_mem_img b
        rw [h] at hb
        exact (Subgroup.mem_inf.mp hb).2
      exact (ggPsiU t n f).range.mul_mem
        ((ggPsiU t n f).range.mul_mem hainn hbinn)
        ((ggPsiU t n f).range.inv_mem hainn)
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp hmem
  have hyy : y = ⟨m * (b : G) * m⁻¹, hmemN⟩ := TT.hom_inj (by rw [hya, hhom])
  have hys : (y : G) ∈ Bs := Subgroup.mem_subgroupOf.mp hy
  rw [hyy] at hys
  exact hys

theorem f5 : GGClauseF5 t n f p ψ Bs M.S M.π T.coord := by
  intro α hα hcl
  obtain ⟨h1, h2⟩ := M.f5 T.kappa T.kappa_diag α hα hcl
  constructor
  · obtain ⟨xA, hxA, hordA⟩ := h1
    have hxA' : xA ∈ ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
        (ggPsiU t n f) := hxA
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hxA'
    exact ⟨ψ r, Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, by
      rw [orderOf_psi_eq T r]; exact hordA⟩
  · intro x' hx' hordx'
    have hx'' : x' ∈ ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map ψ := hx'
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx''
    have hordxA : orderOf (ggPsiU t n f r) = p := by
      rw [← orderOf_psi_eq T r]; exact hordx'
    obtain ⟨hA, hhA, αB, hαB, hαBfix, k, hk, bA, hbAinn, hconj, hcoord⟩ :=
      h2 (ggPsiU t n f r) (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩) hordxA
    obtain ⟨kh, rfl⟩ := hhA
    have hyN : ψ (kh * r * kh⁻¹) ∈ T.N := T.psi_le ⟨kh * r * kh⁻¹, rfl⟩
    have hpsi : ggPsiU t n f (kh * r * kh⁻¹) =
        ggPsiU t n f kh * ggPsiU t n f r * (ggPsiU t n f kh)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hhom : T.hom ⟨ψ (kh * r * kh⁻¹), hyN⟩ = (bA : GGAutU t n f) := by
      rw [T.hom_psi, hpsi, ← hconj]
      exact mul_conj_inv_cancel T.kappa (bA : GGAutU t n f)
    have hBs : ψ (kh * r * kh⁻¹) ∈ Bs :=
      exists_mem_Bs_of_hom_eq T hyN bA.2 hbAinn hhom
    let b : Bs := ⟨ψ (kh * r * kh⁻¹), hBs⟩
    have hbval : (b : G) = ψ kh * ψ r * (ψ kh)⁻¹ := by
      show ψ (kh * r * kh⁻¹) = ψ kh * ψ r * (ψ kh)⁻¹
      rw [map_mul, map_mul, map_inv]
    have htoB : (T.toB b : GGAutU t n f) = (bA : GGAutU t n f) := by
      rw [T.toB_val, T.toHom_apply]
      rw [show (⟨(b : G), T.bs_le b.2⟩ : T.N) = ⟨ψ (kh * r * kh⁻¹), hyN⟩ from
        Subtype.ext rfl]
      exact hhom
    have hcoordT : Multiplicative.toAdd (T.coord b) = k • corootCoord p M.S αB := by
      rw [T.coord_apply b, show T.toB b = bA from Subtype.ext htoB]
      exact hcoord
    exact ⟨ψ kh, ⟨kh, rfl⟩, αB, hαB, hαBfix, k, hk, b, hbval, hcoordT⟩

theorem w : GGClauseW t n f p ψ Bs M.π T.coord := by
  intro u hu
  obtain ⟨mA, hmA, hcoord⟩ := M.w u hu
  obtain ⟨hmAinn, hmAnorm⟩ := Subgroup.mem_inf.mp hmA
  haveI : ((ggPsiU t n f).range).Normal := GGSFCore.normal_range_ggPsiU t n f
  have hconjinn : T.kappa⁻¹ * mA * T.kappa ∈ (ggPsiU t n f).range := by
    simpa using (this.conj_mem mA hmAinn T.kappa⁻¹)
  obtain ⟨k, hk⟩ := hconjinn
  have hkN : ψ k ∈ T.N := T.psi_le ⟨k, rfl⟩
  have hmA' : T.hom ⟨ψ k, hkN⟩ = mA := by
    rw [T.hom_psi k, hk]
    exact mul_conj_inv_cancel T.kappa mA
  have hmNorm : ψ k ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact conj_mem_Bs T hkN hmAinn hmAnorm hmA' ⟨g, hg⟩
    · intro hg
      have hkNi : (ψ k)⁻¹ ∈ T.N := T.N.inv_mem hkN
      have hminv : T.hom ⟨(ψ k)⁻¹, hkNi⟩ = mA⁻¹ := by
        have h1 : (⟨(ψ k)⁻¹, hkNi⟩ : T.N) = ⟨ψ k, hkN⟩⁻¹ := Subtype.ext rfl
        rw [h1, map_inv, hmA']
      have hinn' : mA⁻¹ ∈ (ggPsiU t n f).range := (ggPsiU t n f).range.inv_mem hmAinn
      have hnorm' : mA⁻¹ ∈ Subgroup.normalizer (M.Bfull : Set (GGAutU t n f)) :=
        (Subgroup.normalizer (M.Bfull : Set (GGAutU t n f))).inv_mem hmAnorm
      have hmem := conj_mem_Bs T hkNi hinn' hnorm' hminv ⟨(ψ k) * g * (ψ k)⁻¹, hg⟩
      have hgg : (ψ k)⁻¹ * ((ψ k) * g * (ψ k)⁻¹) * ((ψ k)⁻¹)⁻¹ = g := by
        simpa using mul_conj_inv_cancel (ψ k)⁻¹ g
      rwa [hgg] at hmem
  refine ⟨ψ k, Subgroup.mem_inf.mpr ⟨⟨k, rfl⟩, hmNorm⟩, ?_⟩
  intro b b' hbb' i
  have htoB : (T.toB b' : GGAutU t n f) = mA * (T.toB b : GGAutU t n f) * mA⁻¹ := by
    have heq : (⟨(b' : G), T.bs_le b'.2⟩ : T.N) =
        ⟨ψ k, hkN⟩ * ⟨(b : G), T.bs_le b.2⟩ * ⟨ψ k, hkN⟩⁻¹ := by
      ext
      simp [hbb']
    calc (T.toB b' : GGAutU t n f)
        = T.hom ⟨(b' : G), T.bs_le b'.2⟩ := T.toB_val b'
      _ = T.hom (⟨ψ k, hkN⟩ * ⟨(b : G), T.bs_le b.2⟩ * ⟨ψ k, hkN⟩⁻¹) := by rw [heq]
      _ = T.hom ⟨ψ k, hkN⟩ * T.hom ⟨(b : G), T.bs_le b.2⟩ *
            (T.hom ⟨ψ k, hkN⟩)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = mA * T.hom ⟨(b : G), T.bs_le b.2⟩ * mA⁻¹ := by rw [hmA']
      _ = mA * (T.toB b : GGAutU t n f) * mA⁻¹ := by
            rw [T.toB_val b, T.toHom_apply b]
  rw [T.coord_apply b', T.coord_apply b]
  exact hcoord (T.toB b) (T.toB b') htoB i

end GGSFTr

end Universal

end CFSG.StandardType
