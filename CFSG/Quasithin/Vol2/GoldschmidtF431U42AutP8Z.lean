module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Fz
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Rad
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def uL : PL := Thl.getD 122 []

theorem u_check : uL ∈ Zl ∧ uL ∈ Thl ∧ comp uL uL = idL ∧ comp fhatL uL = dL ∧ uL ≠ idL ∧
    uL ≠ comp fhatL xL ∧ comp fhatL uL ∈ Thl ∧ comp (comp fhatL uL) (comp fhatL uL) = idL ∧
    comp fhatL uL ≠ idL := by
  decide +kernel

theorem Zl_e_types : ∀ k < 43, invL k ∈ Zl → invTgt.getD k 0 = 3 →
    invL k = comp fhatL xL ∨ invL k = uL := by
  decide +kernel

theorem fu_type_t : ∀ k < 43, invL k = comp fhatL uL → invTgt.getD k 0 = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem conj_z_cases
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) (h6 : FusionTStmt)
    (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)) {n : G}
    (hn : n ∈ Subgroup.normalizer
      ((c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) : Subgroup G) : Set G))
    (hnf : n * c.iso.toG fhB = c.iso.toG fhB * n) :
    n * z * n⁻¹ = z ∨ n * z * n⁻¹ = c.iso.toG fhB * z := by
  by_cases hnz : n * z * n⁻¹ = z
  · exact Or.inl hnz
  right
  have hfz : IsConj (c.iso.toG fhB * z) z := fz_conj c h5 h6 hn hnz
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
  · rcases Zl_e_types k hk hZk hj with he | he
    ·
      have hbe : b = fhB * xB := by
        apply Subtype.ext
        apply Subtype.ext
        refine eq_of_repL hrepb ?_
        rw [hlbk, he]
        exact repL_mul repL_fhat repL_x
      rw [← hbu, hbe, AutIso.toG_mul, hxz]
    · exfalso
      have hfu : n * (c.iso.toG fhB * z) * n⁻¹ = c.iso.toG fhB * c.iso.toG b := by
        rw [hbu]
        calc n * (c.iso.toG fhB * z) * n⁻¹ = (n * c.iso.toG fhB * n⁻¹) * (n * z * n⁻¹) := by group
          _ = c.iso.toG fhB * (n * z * n⁻¹) := by rw [hnf]; group
      have hfbz : IsConj (c.iso.toG fhB * c.iso.toG b) z := by
        rw [← hfu]
        exact (isConj_iff.2 ⟨n, rfl⟩ : IsConj (c.iso.toG fhB * z)
          (n * (c.iso.toG fhB * z) * n⁻¹)).symm.trans hfz
      set bf : Bh := fhB * b with hbf
      have hbfG : c.iso.toG bf = c.iso.toG fhB * c.iso.toG b := AutIso.toG_mul _ _ _
      have hlb_u : lb = uL := hlbk.trans he
      have hrepu : RepL (comp fhatL uL) ((bf : Ah) : P45) := by
        have := repL_mul repL_fhat hrepb
        rw [hlb_u] at this
        exact this
      have hbfT : (bf : Ah) ∈ That :=
        (mem_That_iff _).2 ⟨comp fhatL uL, u_check.2.2.2.2.2.2.1, hrepu⟩
      have hbf2 : (bf : Ah) * (bf : Ah) = 1 := by
        apply Subtype.ext
        apply eq_of_repL (l := comp (comp fhatL uL) (comp fhatL uL)) (repL_mul hrepu hrepu)
        rw [u_check.2.2.2.2.2.2.2.1]
        exact repL_one 45
      have hbf1 : (bf : Ah) ≠ 1 := by
        intro h
        apply u_check.2.2.2.2.2.2.2.2
        exact repL_unique hrepu (by rw [h]; exact repL_one 45)
      obtain ⟨k', hk', hrep', g', hg', hgeq'⟩ := inv_type hbfT hbf2 hbf1
      have hlk' : invL k' = comp fhatL uL := repL_unique hrep' hrepu
      have ht : invTgt.getD k' 0 = 1 := fu_type_t k' hk' hlk'
      rw [ht] at hgeq'
      have e : repA 1 = t0A := by simp [repA]
      rw [e] at hgeq'
      have hc1 : IsConj (c.iso.toG bf) (c.iso.toG t0B) := c.iso.isConj_toG hg' hgeq'
      have hc2 : IsConj (c.iso.toG bf) (c.iso.toG fhB) := hc1.trans ht0
      rw [hbfG] at hc2
      exact F_notConj c h5 (hc2.symm.trans hfbz)

end CFSG.Quasithin.H13.F431.U42Aut
