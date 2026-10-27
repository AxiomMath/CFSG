module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
import CFSG.RankThree.GF2n.Stroth80.Sec97YPartner
import CFSG.RankThree.GF2n.Smith81.Lin26Roots
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap HS9
open CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem sec97_polar_of_left {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hdet : (toMat K u).det = 0)
    {r : ↥(Rt M (LB M Q B) t)} (hleft : Ψ K (φ r) ∈ leftF K)
    {f : G} (hf : f ∈ conjSubgroup (r : G) B) :
    ∃ hfV : f ∈ Vt M (LB M Q B) B Z t,
      polar (quadPlus 2 K) u (secVec ψ ⟨f, hfV⟩) = 0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  set b0 : G := (r : G)⁻¹ * f * (r : G) with hb0
  have hb0B : b0 ∈ B := by
    rw [hb0]
    exact mem_conjSubgroup.mp hf
  have hb0V : b0 ∈ Vt M (LB M Q B) B Z t := hBV hb0B
  have hfV : f ∈ Vt M (LB M Q B) B Z t := by
    have hfe : f = (r : G) * b0 * (r : G)⁻¹ := by rw [hb0]; group
    rw [hfe]
    exact (Subgroup.mem_normalizer_iff.mp (hnorm r.2) b0).mp hb0V
  obtain ⟨c, hcvec⟩ := (hBiff (secVec ψ ⟨b0, hb0V⟩)).mp ⟨⟨b0, hb0V⟩, hb0B, rfl⟩
  have hwf : (f : G) = (r : G) * b0 * (r : G)⁻¹ := by rw [hb0]; group
  have hsec : secVec ψ ⟨f, hfV⟩ =
      (φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ ⟨b0, hb0V⟩ :=
    hψ r ⟨b0, hb0V⟩ ⟨f, hfV⟩ (by simpa using hwf)
  have hsecf : secVec ψ ⟨f, hfV⟩ =
      c • ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) := by
    rw [hsec, hcvec, Matrix.mulVec_smul]
  rw [leftF] at hleft
  obtain ⟨A, hA⟩ := hleft
  have hmat : toMat K (secVec ψ ⟨f, hfV⟩) =
      c • ((A : Matrix (Fin 2) (Fin 2) K) * toMat K u) := by
    rw [hsecf, map_smul]
    congr 1
    calc toMat K ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u)
        = toMat K ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            (toMat K).symm (toMat K u)) := by rw [LinearEquiv.symm_apply_apply]
      _ = Ψ K (φ r) (toMat K u) := (Ψ_apply K (φ r) (toMat K u)).symm
      _ = rho' K (A, 1) (toMat K u) := by
        rw [← hA]
        rfl
      _ = (A : Matrix (Fin 2) (Fin 2) K) * toMat K u := by
        simpa only [MonoidHom.comp_apply] using rho'_inl_apply A (toMat K u)
  have hdetf : (toMat K (secVec ψ ⟨f, hfV⟩)).det = 0 := by
    simp [hmat, hdet]
  have hU0 : quadPlus 2 K u = 0 := by
    rw [coe_quadPlus, ← det_toMat]
    exact hdet
  have hf0 : quadPlus 2 K (secVec ψ ⟨f, hfV⟩) = 0 := by
    rw [coe_quadPlus, ← det_toMat]
    exact hdetf
  have hsum : toMat K (u + secVec ψ ⟨f, hfV⟩) =
      (1 + c • (A : Matrix (Fin 2) (Fin 2) K)) * toMat K u := by
    rw [map_add, hmat]
    simp [Matrix.add_mul, Matrix.smul_mul]
  have hsum0 : quadPlus 2 K (u + secVec ψ ⟨f, hfV⟩) = 0 := by
    rw [coe_quadPlus, ← det_toMat, hsum, Matrix.det_mul, hdet, mul_zero]
  have hpol : polar (quadPlus 2 K) u (secVec ψ ⟨f, hfV⟩) = 0 := by
    simp only [QuadraticMap.polar, hU0, hf0, hsum0]
    ring
  exact ⟨hfV, hpol⟩

private theorem sec97_comm_conj_of_left {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hW : ∀ x : Fin 2 ⊕ Fin 2 → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
      (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔
      polar (quadPlus 2 K) u x = 0)
    {r : ↥(Rt M (LB M Q B) t)}
    (hpol : ∀ f ∈ conjSubgroup (r : G) B, ∃ hfV : f ∈ Vt M (LB M Q B) B Z t,
      polar (quadPlus 2 K) u (secVec ψ ⟨f, hfV⟩) = 0) :
    ∀ f ∈ conjSubgroup (r : G) B, ∀ b ∈ B, f * b = b * f := by
  intro f hf b hb
  obtain ⟨hfV, hpol'⟩ := hpol f hf
  obtain ⟨w, hwQB, hwsec⟩ := (hW (secVec ψ ⟨f, hfV⟩)).mpr hpol'
  have hz : f * (w : G)⁻¹ ∈ Z := by
    refine (secVec_eq_iff ψ ⟨f, hfV⟩ w).mp ?_
    exact hwsec.symm
  have hwB : w * b = b * w := (Ctx.B_central_QB hc hb hwQB.2).symm
  have hzB : b * (f * (w : G)⁻¹) = (f * (w : G)⁻¹) * b :=
    Ctx.Z_central hc hz (hc.le hb)
  have hfe : f = (f * (w : G)⁻¹) * w := by group
  rw [hfe]
  calc (f * (w : G)⁻¹) * w * b
      = (f * (w : G)⁻¹) * (w * b) := by group
    _ = (f * (w : G)⁻¹) * (b * w) := by rw [hwB]
    _ = ((f * (w : G)⁻¹) * b) * w := by group
    _ = (b * (f * (w : G)⁻¹)) * w := by rw [hzB]
    _ = b * ((f * (w : G)⁻¹) * w) := by group

theorem sec97Conn_of (h34 : Stroth34Statement) : Sec97ConnStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs P hPB hstep F hF
  obtain ⟨m, hm, rfl⟩ := hF
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    (Ψ K).toMonoidHom.comp φ
  let R₁ : Subgroup G := ((leftF K).comap φ'').map (Rt M (LB M Q B) t).subtype
  have hR₁R : R₁ ≤ Rt M (LB M Q B) t := Subgroup.map_subtype_le _
  have hR₁M : R₁ ≤ M := hR₁R.trans (Rt_le_M hc.LB_le_M t)
  have hR₁mem : ∀ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ R₁ ↔ φ'' s ∈ leftF K := by
    intro s
    constructor
    · intro hs
      obtain ⟨s', hs', hss'⟩ := Subgroup.mem_map.mp hs
      have hst : s' = s := Subtype.ext hss'
      rwa [hst] at hs'
    · intro hs
      exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hH : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ R₁ ∧ Ψ K (φ s) = h := by
    intro h
    constructor
    · intro hh
      have hmemRange : h ∈ φ''.range := by
        rw [hrange]
        exact leftF_le_range hh
      obtain ⟨s, hsh⟩ := MonoidHom.mem_range.mp hmemRange
      refine ⟨s, (hR₁mem s).mpr ?_, hsh⟩
      rw [hsh]
      exact hh
    · rintro ⟨s, hsR₁, hsh⟩
      rw [← hsh]
      exact (hR₁mem s).mp hsR₁
  obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
    natural_module_data (H := leftF K) (Or.inl rfl) hdet hu0
  have hcard : Nat.card ↥(Uline Z B R₁) = Nat.card Z ^ 3 := by
    rw [uline_card ψ φ hψ hnorm hR₁R sec39_Z_le_Vt (hc.B_le_Vt hs.toSec5.mem) u
      hBiff hH hA hw₀ hu, hK]
    ring
  have hcover : ∀ x ∈ Uline Z B R₁, x ∉ Z →
      ∃ y ∈ R₁, x ∈ (conjSubgroup y B ⊔ Z : Subgroup G) := by
    intro x hx _
    exact uline_cover ψ φ hψ hnorm hR₁R sec39_Z_le_Vt (hc.B_le_Vt hs.toSec5.mem) u
      hBiff hH hA hw₀ hu x hx
  have hcommR₁ : ∀ r ∈ R₁, ∀ f ∈ conjSubgroup r B, ∀ b ∈ B, f * b = b * f := by
    intro r hrR₁
    obtain ⟨s, hsmem, hsr⟩ := Subgroup.mem_map.mp hrR₁
    have hleft : Ψ K (φ s) ∈ leftF K := hsmem
    rw [← hsr]
    exact sec97_comm_conj_of_left (hc := hc) hW (fun f hf =>
      sec97_polar_of_left hs hψ hnorm u hBiff hdet hleft hf)
  obtain ⟨y, hyR₁, hycomm⟩ :=
    exists_comm_conj_of_cover (Y := R₁) hc hR₁M hcard hcover hm
  have hPBy : P (conjSubgroup y B) :=
    hstep B (conjSubgroup y B) (isConjB_self M B) ⟨y, hR₁M hyR₁, rfl⟩ hPB
      (fun f hf s hsB =>
        commutatorElement_eq_one_iff_mul_comm.mpr (hcommR₁ y hyR₁ f hf s hsB))
  exact hstep (conjSubgroup y B) (conjSubgroup m B) ⟨y, hR₁M hyR₁, rfl⟩ ⟨m, hm, rfl⟩ hPBy
    (fun f hf s hsB => commutatorElement_eq_one_iff_mul_comm.mpr (hycomm s hsB f hf).symm)

end CFSG.RankThree.GF2n.Stroth80
