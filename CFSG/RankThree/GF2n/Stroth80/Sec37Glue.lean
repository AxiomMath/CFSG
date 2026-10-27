module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Geom
public import CFSG.RankThree.GF2n.Stroth80.Sec37Action
import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec37Inputs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem geom37 (h34 : Stroth34Statement)
    (hHKS : HKSNormalStatement) (hSL2 : SL2FixedLineDimStatement)
    (hOv : Ovoid37Statement) (hMod : Module37Statement) (hBr : Bridge37Statement) :
    Geom37Statement := by
  intro G _ _ M Q Z B _ hc n hw hn hno hgen horth
  obtain ⟨k, γ, M₀, hkZ, h⟩ := stroth_globalModelDataGF hc.hyp
  have hk : 2 ≤ k := by
    by_contra hlt
    have h4 := hc.hyp.q4
    rw [hkZ] at h4
    interval_cases k <;> simp at h4
  have hK : 1 < Nat.card (GaloisField 2 k) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim : Module.finrank (GaloisField 2 k) M₀.E = 2 * n := h.finrank_E hw hK
  obtain ⟨b, hb0, hbs, hB, -, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have hLB : LB M Q B ≤ H0 M Z := Gl37.LB_le_H0 hc
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  set X : Set (M₀.E ≃ₗ[GaloisField 2 k] M₀.E) :=
    {T | ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T}
  have hXr : Subgroup.closure X ≤ φ.range :=
    (Subgroup.closure_le _).mpr fun T ⟨_, _, x, _, hT⟩ => ⟨x, hT⟩
  have hHQ : ∀ T ∈ Subgroup.closure X, ∀ e, M₀.Qf (T e) = M₀.Qf e := by
    intro T hT e
    obtain ⟨x, rfl⟩ := hXr hT
    exact hφiso x e
  set Λ := (φ.comp (Subgroup.inclusion hLB)).range
  have hΛH : Λ ≤ Subgroup.closure X := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.subset_closure ⟨1, M.one_mem, Subgroup.inclusion hLB x, ?_, rfl⟩
    rw [conjSubgroup_one]
    exact x.2
  have hΛcomm : ∀ t ∈ Λ, ∀ t' ∈ Λ, t * t' = t' * t := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : ⁅(x : G), (y : G)⁆ ∈ Q :=
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator x.2 y.2)
    have h1 : (φ.comp (Subgroup.inclusion hLB)) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (hφker (Subgroup.inclusion hLB (x * y * x⁻¹ * y⁻¹))).mpr
        (by simpa [commutatorElement_def] using hxy)
    rw [← map_mul, ← map_mul]
    have e : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rw [e, map_mul, h1, one_mul]
  have hΛsq : ∀ t ∈ Λ, t * t = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    refine (hφker (Subgroup.inclusion hLB (x * x))).mpr ?_
    have := hc.sq_mem_Q_of_mem_LB x.2
    rw [pow_two] at this
    exact this
  have hΛb : ∀ t ∈ Λ, t b = b := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
    rw [← hu]
    show φ (Subgroup.inclusion hLB x) (M₀.π u) = M₀.π u
    rw [← hφπ _ u huQ]
    exact (M₀.comm_mem_iff huQ ((Gl37.conj_mem_Q hc (hc.LB_le_M x.2)).1 u huQ)).mp
      (hc.comm_B_mem_Z x.2 huB)
  have hΛnorm : ∀ T ∈ Subgroup.closure X,
      Submodule.map (T : M₀.E →ₗ[GaloisField 2 k] M₀.E) (Submodule.span (GaloisField 2 k) {b}) =
        Submodule.span (GaloisField 2 k) {b} → ∀ t ∈ Λ, T * t * T⁻¹ ∈ Λ := by
    intro T hT hmap t ht
    obtain ⟨a, rfl⟩ := hXr hT
    exact Gl37.conj_mem_range_LB hc hB hφπ hLB a hmap ht
  have hmoves : ∃ T ∈ Subgroup.closure X,
      Submodule.map (T : M₀.E →ₗ[GaloisField 2 k] M₀.E) (Submodule.span (GaloisField 2 k) {b}) ≠
        Submodule.span (GaloisField 2 k) {b} := by
    obtain ⟨m, hm, x, hx, hnot⟩ := Gl37.moves_aux h34 hc hw hn hno hgen horth hB hφπ
    refine ⟨φ x, Subgroup.subset_closure ⟨m, hm, x, hx, rfl⟩, fun hmap => hnot ?_⟩
    have := Submodule.mem_map_of_mem (f := (φ x : M₀.E →ₗ[GaloisField 2 k] M₀.E))
      (Submodule.mem_span_singleton_self b)
    rw [hmap] at this
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨μ, hμ.symm⟩
  obtain ⟨W, hWs, hWdim, hbW⟩ := Gl37.exists_tsing hc hw (by omega) hno h hB
  set P : Set M₀.E := {p | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)}
  have hbP : b ∈ P := ⟨hb0, 1, M.one_mem, by
    rw [conjSubgroup_one]
    exact (hB b).mpr ⟨1, (one_smul _ b).symm⟩⟩
  have hP0 : ∀ p ∈ P, p ≠ 0 ∧ M₀.Qf p = 0 := by
    rintro p ⟨hp0, m, hm, hp⟩
    have hc' := hc.conj_of_mem hm
    exact ⟨hp0, (M₀.isElemAbelian_iff h.reg hc'.le).mp hc'.isElemAbelian_B p hp⟩
  have hPsmul : ∀ p ∈ P, ∀ c : GaloisField 2 k, c ≠ 0 → c • p ∈ P := by
    rintro p ⟨hp0, m, hm, hp⟩ c hc0
    obtain ⟨b', -, -, hB', -, -⟩ := (hc.conj_of_mem hm).dictB h
    obtain ⟨s, rfl⟩ := (hB' _).mp hp
    exact ⟨smul_ne_zero hc0 hp0, m, hm, (hB' _).mpr ⟨c * s, by rw [smul_smul]⟩⟩
  have hPH : ∀ T ∈ Subgroup.closure X, ∀ p ∈ P, T p ∈ P := by
    intro T hT p hp
    obtain ⟨a, rfl⟩ := hXr hT
    obtain ⟨hp0, m, hm, hpm⟩ := hp
    exact ⟨(φ a).map_ne_zero_iff.mpr hp0, (a : G) * m,
      M.mul_mem (a.2 : (a : G) ∈ M ⊓ _).1 hm, Gl37.conj_mem_img_aux hc hφπ a hpm⟩
  have hPorth : ∀ p ∈ P, ∀ p' ∈ P, (∀ c : GaloisField 2 k, p' ≠ c • p) → M₀.B p p' ≠ 0 := by
    rintro p ⟨hp0, m₁, hm₁, hp⟩ p' ⟨-, m₂, hm₂, hp'⟩ hnp
    exact Gl37.orth_aux hc horth h hm₁ hm₂ hp0 hp hp' hnp
  have hΛsemi : ∀ t ∈ Λ, t ≠ 1 → ∀ p ∈ P, (∀ c : GaloisField 2 k, p ≠ c • b) →
      t p ∈ Submodule.span (GaloisField 2 k) {p} → False := by
    rintro _ ⟨x, rfl⟩ ht1 p ⟨hp0, m, hm, hpm⟩ hpb hfix
    exact Gl37.semi_aux h34 hc hw hn hno hgen horth h hB hφπ (x := Subgroup.inclusion hLB x)
      x.2 (fun hQ => ht1 ((hφker _).mpr hQ)) hm hp0 hpm hpb hfix
  have hcardΛ : Nat.card Λ = Nat.card (GaloisField 2 k) ^ (n - 1) :=
    Gl37.card_range_LB hc hw (by omega) hno h hφker hLB
  obtain ⟨L, hLH, hLn, hLs, hLiso, hΛL, hspan, hOrb⟩ := hOv hHKS k n hk hn M₀.E hdim M₀.B
    M₀.Qf M₀.Qf_smul M₀.Qf_add (Subgroup.closure X) hHQ b hbs W hWs hWdim hbW Λ hΛH hcardΛ
    hΛcomm hΛsq hΛb P hbP hP0 hPsmul hPH hPorth (Gl37.span_aux hc hgen) hΛsemi hΛnorm hmoves
  have hcardΛ' : Nat.card Λ = 2 ^ (k * (n - 1)) := by
    rw [hcardΛ, h.card, hkZ, ← pow_mul]
  have hn4 : n = 4 := hMod hSL2 k n hk hn M₀.E hdim L hLiso b hb0 hspan Λ hΛL hcardΛ' hΛb
    (Gl37.fixed_aux hc h hB h35 hφπ hLB)
  have hXL : X ⊆ L := by
    rintro _ ⟨m, hm, x, hx, rfl⟩
    obtain ⟨b', hb'0, -, hB', -, -⟩ := (hc.conj_of_mem hm).dictB h
    obtain ⟨g, hgH, hgmap⟩ := hOrb b' ⟨hb'0, m, hm, (hB' b').mpr ⟨1, (one_smul _ b').symm⟩⟩
    obtain ⟨a, rfl⟩ := hXr hgH
    have hmid : (φ a)⁻¹ * φ x * φ a ∈ L :=
      hΛL (Gl37.conj_mem_range_of_line hc hb0 hB hφπ hLB hm hB' a hgmap hx)
    have hconj := hLn.conj_mem ⟨_, hLH hmid⟩ (Subgroup.mem_subgroupOf.mpr hmid) ⟨φ a, hgH⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    have e : φ a * ((φ a)⁻¹ * φ x * φ a) * (φ a)⁻¹ = φ x := by group
    rw [← e]
    exact hconj
  have hHL : Subgroup.closure X = L := le_antisymm ((Subgroup.closure_le L).mpr hXL) hLH
  obtain ⟨eB⟩ := hBr G M Q Z B hc (GaloisField 2 k) γ M₀ φ hφker
  have e : ↥(bar M Q (Lgen M (LB M Q B))) ≃* ↥L := eB.trans (MulEquiv.subgroupCongr hHL)
  subst hn4
  obtain ⟨eL⟩ := hLiso
  haveI := hLs
  exact ⟨rfl, k, hkZ, e.isSimpleGroup, ⟨e.trans eL⟩⟩

end CFSG.RankThree.GF2n.Stroth80
