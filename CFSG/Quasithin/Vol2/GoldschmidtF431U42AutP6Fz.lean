module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5b
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Fix
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Syl

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem fz_conj
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) (h6 : FusionTStmt) {n : G}
    (hn : n ∈ Subgroup.normalizer
      ((c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) : Subgroup G) : Set G))
    (hnz : n * z * n⁻¹ ≠ z) : IsConj (c.iso.toG fhB * z) z := by
  have hxz : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  have hzT : z ∈ c.iso.imgG That := by
    have : c.iso.toG xB ∈ c.iso.imgG That := c.iso.mem_imgG.2 ⟨xB, xA_mem_That, rfl⟩
    rwa [hxz] at this
  have hzF : z * c.iso.toG fhB = c.iso.toG fhB * z := (c.comm_z (c.iso.toG_mem fhB)).symm
  set Tf : Subgroup G := c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) with hTf
  have hzTf : z ∈ Tf := ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 hzF⟩
  have huTf : n * z * n⁻¹ ∈ Tf := (Subgroup.mem_normalizer_iff.1 hn z).1 hzTf
  have huz : IsConj (n * z * n⁻¹) z := (isConj_iff.2 ⟨n, rfl⟩ : IsConj z (n * z * n⁻¹)).symm
  have hucen : ∀ t ∈ Tf, t * (n * z * n⁻¹) = (n * z * n⁻¹) * t := by
    intro t ht
    have ht' : n⁻¹ * t * n ∈ Tf :=
      (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * t * n)).2 (by simpa [mul_assoc] using ht)
    have hzc : (n⁻¹ * t * n) * z = z * (n⁻¹ * t * n) :=
      c.comm_z ((c.iso.imgG_le That) ht'.1)
    calc t * (n * z * n⁻¹) = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by rw [hzc]
      _ = (n * z * n⁻¹) * t := by group
  have hu' : n * z * n⁻¹ ∈ c.iso.imgG (That ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) := by
    rw [c.iso.mem_imgG_Tf]
    exact huTf
  obtain ⟨b, hbK, hbu⟩ := c.iso.mem_imgG.1 hu'
  have hbT : (b : Ah) ∈ That := hbK.1
  have hbC : (b : Ah) ∈ Subgroup.centralizer ({fhatA} : Set Ah) := hbK.2
  have hbcen : ∀ m ∈ That, m * fhatA = fhatA * m → m * (b : Ah) = (b : Ah) * m := by
    intro m hm hmf
    have hmB : m ∈ Bh := That_le_Bh hm
    have hmT : c.iso.toG ⟨m, hmB⟩ ∈ Tf := by
      rw [hTf, ← c.iso.mem_imgG_Tf]
      exact c.iso.mem_imgG.2 ⟨⟨m, hmB⟩, ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 hmf⟩, rfl⟩
    have h1 := hucen _ hmT
    rw [← hbu] at h1
    have h2 : (⟨m, hmB⟩ : Bh) * b = b * ⟨m, hmB⟩ := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul]
      exact h1
    exact congrArg (fun x : Bh => (x : Ah)) h2
  have hb2 : (b : Ah) * b = 1 := by
    have : b * b = 1 := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, hbu, c.iso.toG_one]
      calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [← pow_two, c.z2]; group
    exact congrArg (fun x : Bh => (x : Ah)) this
  have hb1 : (b : Ah) ≠ 1 := by
    intro h
    have h1 : c.iso.toG b = 1 := by rw [(Subtype.ext h : b = 1), c.iso.toG_one]
    rw [hbu] at h1
    apply c.z1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hbx : (b : Ah) ≠ xA := by
    intro h
    apply hnz
    rw [← hbu, (Subtype.ext h : b = xB)]
    exact hxz
  have hbz : IsConj (c.iso.toG b) z := by
    rw [hbu]
    exact huz
  obtain ⟨lb, hlb, hrepb⟩ := (mem_That_iff (b : Ah)).1 hbT
  have hcF : comp lb fhatL = comp fhatL lb :=
    comp_comm_of_comm (v := fhatA) repL_fhat hrepb (Subgroup.mem_centralizer_singleton_iff.1 hbC)
  have hZ : lb ∈ Zl := by
    refine Zl_center lb hlb hcF ?_
    intro m hm hmc
    obtain ⟨m', hm', hmrep⟩ := exists_That_of_mem_Thl hm
    have hm'f : m' * fhatA = fhatA * m' :=
      comm_of_comp_comm (v := fhatA) repL_fhat hmrep hmc
    exact comp_comm_of_comm hrepb hmrep (hbcen m' hm' hm'f)
  obtain ⟨k, hk, hrepk, g, hg, hgeq⟩ := inv_type hbT hb2 hb1
  have hlbk : lb = invL k := repL_unique hrepb hrepk
  have hZk : invL k ∈ Zl := hlbk ▸ hZ
  have hne : invL k ≠ xL := by
    intro h
    have hx : RepL (invL k) (xA : P45) := by
      rw [h]
      exact repL_x
    exact hbx (Subtype.ext (eq_of_repL hrepk hx))
  have h0 := zf_types k hk hZk hne
  have h4 := inv_check.2.2 k hk
  generalize hj : invTgt.getD k 0 = j at h0 h4 hgeq
  interval_cases j
  · exact absurd rfl h0
  · exfalso
    have e : repA 1 = t0A := by simp [repA]
    rw [e] at hgeq
    have hc1 : IsConj (c.iso.toG b) (c.iso.toG t0B) := c.iso.isConj_toG hg hgeq
    exact h6 G M₁ M₂ z c t0B t0A_mem_TAh t0A_sq t0A_ne_one not_isConj_t0A_xA (hc1.symm.trans hbz)
  · exfalso
    have e : repA 2 = fhatA := by simp [repA]
    rw [e] at hgeq
    exact h5 G M₁ M₂ z c (c.iso.toG b) ⟨b, isGoodInv_of_conj_fhat (That_le_Bh hbT) hb2 hgeq, rfl⟩
      hbz
  · have e : repA 3 = e0A := by simp [repA]
    rw [e] at hgeq
    have hc1 : IsConj (c.iso.toG b) (c.iso.toG e0B) := c.iso.isConj_toG hg hgeq
    have h3 : c.iso.toG e0B = c.iso.toG fhB * z := by
      show c.iso.toG (fhB * xB) = _
      rw [AutIso.toG_mul, hxz]
    rw [h3] at hc1
    exact hc1.symm.trans hbz

end CFSG.Quasithin.H13.F431.U42Aut
