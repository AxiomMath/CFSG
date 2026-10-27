module

public import CFSG.RankThree.GF2n.Stroth80.Sec312SLData
public import CFSG.RankThree.GF2n.Stroth80.Sec311SLTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClReprData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_smul_of_vecMulVec_eq_of_ne {m : ℕ} {K : Type} [Field K] {a a' b b' : Fin m → K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Matrix.vecMulVec a b = Matrix.vecMulVec a' b') :
    ∃ c : K, a' = c • a := by
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (funext hcon)
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hent : ∀ i, a i * b j = a' i * b' j := fun i => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply] using this
  have hb'j : b' j ≠ 0 := by
    intro h0
    have := hent i₀
    rw [h0, mul_zero] at this
    exact mul_ne_zero hi₀ hj this
  refine ⟨b j / b' j, funext fun i => ?_⟩
  have := hent i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -this

theorem exists_perp_ne_zero_vec {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] {u : Fin m → K}
    (hu : u ≠ 0) : ∃ f : Fin m → K, f ≠ 0 ∧ f ⬝ᵥ u = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (funext hcon)
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  refine ⟨Pi.single j (u i) - Pi.single i (u j), ?_, ?_⟩
  · intro h0
    have := congrFun h0 j
    simp [Pi.single_apply, hji] at this
    exact hi this
  · rw [sub_dotProduct, single_dotProduct, single_dotProduct]
    ring

theorem Ctx.mem_conj_LB_of_mem_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : t ∈ conjSubgroup r (LB M Q B) := by
  rw [mem_conjSubgroup]
  have h1 : ⁅r⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr)
  have e : r⁻¹ * t * r = ⁅r⁻¹, t⁆ * t := by simp only [commutatorElement_def]; group
  rw [e]
  exact (LB M Q B).mul_mem (sec39_Q_le_LB h1) ht

theorem Ctx.exists_conj_of_SL (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hR : Rt M (LB M Q B) t ≠ LB M Q B)
    (hV : Vt M (LB M Q B) B Z t ≤ QB B) {m : G} (hm : m ∈ M)
    (htm : t ∈ conjSubgroup m (LB M Q B)) :
    ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m (LB M Q B) = conjSubgroup r (LB M Q B) := by
  classical
  obtain ⟨K, fK, finK, chK, hK, m₁, hm₁, φ, hker, hsec, hrange, u, hu, hcross⟩ :=
    stroth310SLTransvConj_of_34 h34 G M Q Z B hc n t hs hR hV
  have h1M : (1 : G) ∈ M := M.one_mem
  have h1t : t ∈ conjSubgroup (1 : G) (LB M Q B) := by rw [conjSubgroup_one]; exact hs.mem
  obtain ⟨hu₁, -, hP2₁⟩ := hu 1 h1M h1t
  obtain ⟨hum, -, -⟩ := hu m hm htm
  obtain ⟨g, hg, hgu⟩ := exists_statedSL_mulVec_eq_of_ne_zero hm₁ hu₁ hum
  have hgr : g ∈ φ.range := by rw [hrange]; exact hg
  obtain ⟨r, hrg⟩ := hgr
  have hrM : (r : G) ∈ M := hc.Rt_le_M t r.2
  have htr : t ∈ conjSubgroup (r : G) (LB M Q B) := hc.mem_conj_LB_of_mem_Rt hs.mem r.2
  refine ⟨r, r.2, hcross m hm (r : G) hrM htm htr ?_⟩
  obtain ⟨f₀, hf₀, hf₀u⟩ := exists_perp_ne_zero_vec hm₁ hu₁
  obtain ⟨l, hl, hlf⟩ := hP2₁ f₀ hf₀u
  have hl' : (l : G) ∈ LB M Q B := by rwa [conjSubgroup_one] at hl
  have hy : ((r * l * r⁻¹ : ↥(Rt M (LB M Q B) t)) : G) ∈ conjSubgroup (r : G) (LB M Q B) := by
    rw [mem_conjSubgroup]
    have e : (r : G)⁻¹ * ((r * l * r⁻¹ : ↥(Rt M (LB M Q B) t)) : G) * (r : G) = (l : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hl'
  obtain ⟨f'', hf''0, hf''⟩ := (hu (r : G) hrM htr).2.1 (r * l * r⁻¹) hy
  have hφy : (φ (r * l * r⁻¹) : Matrix (Fin m₁) (Fin m₁) K) =
      1 + Matrix.vecMulVec ((g : Matrix (Fin m₁) (Fin m₁) K) *ᵥ u 1)
        (f₀ ᵥ* ((g⁻¹ : GL (Fin m₁) K) : Matrix (Fin m₁) (Fin m₁) K)) := by
    rw [map_mul, map_mul, map_inv, hrg, Units.val_mul, Units.val_mul, hlf, mul_add, mul_one,
      Matrix.mul_vecMulVec, add_mul, Units.mul_inv, Matrix.vecMulVec_mul]
  have heq : Matrix.vecMulVec (u m) (f₀ ᵥ* ((g⁻¹ : GL (Fin m₁) K) : Matrix (Fin m₁) (Fin m₁) K)) =
      Matrix.vecMulVec (u (r : G)) f'' := by
    rw [hφy, hgu] at hf''
    exact add_left_cancel hf''
  have hb0 : f₀ ᵥ* ((g⁻¹ : GL (Fin m₁) K) : Matrix (Fin m₁) (Fin m₁) K) ≠ 0 := by
    intro h0
    apply hf₀
    have := congrArg (fun v => v ᵥ* (g : Matrix (Fin m₁) (Fin m₁) K)) h0
    simpa [Matrix.vecMul_vecMul, Units.inv_mul] using this
  exact exists_smul_of_vecMulVec_eq_of_ne hum hb0 heq

theorem Ctx.img_conj_Rt_eq {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    (e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    (heB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • (e : M₀.E))
    (r : ↥(Rt M (LB M Q B) t)) :
    ∀ v : M₀.E, v ∈ M₀.img (conjSubgroup (r : G) B) ↔
      ∃ s : K, v = s • ((D.ρ r e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) := by
  classical
  have hrM : (r : G) ∈ M := hc.Rt_le_M t r.2
  have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 t r.2
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have hS' : ∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = φ₀ ⟨r, hrH⟩ (M₀.π x) :=
    fun x hx => hφπ ⟨r, hrH⟩ x hx
  obtain ⟨hw, hρ⟩ := D.ρ_apply r (φ₀ ⟨r, hrH⟩) hS' e
  have he' : ((D.ρ r e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) =
      φ₀ ⟨r, hrH⟩ (e : M₀.E) := by rw [hρ]
  intro v
  constructor
  · rintro ⟨b, hb, hbQ, rfl⟩
    have hb' : (r : G)⁻¹ * b * (r : G) ∈ B := mem_conjSubgroup.mp hb
    have hb'Q : (r : G)⁻¹ * b * (r : G) ∈ Q := hc.le hb'
    obtain ⟨s, hs'⟩ := (heB _).mp (M₀.pi_mem_img hb' hb'Q)
    refine ⟨s, ?_⟩
    have hbe : b = (r : G) * ((r : G)⁻¹ * b * (r : G)) * (r : G)⁻¹ := by group
    rw [hbe, hS' _ hb'Q, hs', map_smul, he']
  · rintro ⟨s, rfl⟩
    obtain ⟨b', hb', hb'Q, hπ⟩ := (heB (s • (e : M₀.E))).mpr ⟨s, rfl⟩
    have hbQ : (r : G) * b' * (r : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hrM).1 b' hb'Q
    refine ⟨(r : G) * b' * (r : G)⁻¹, ?_, hbQ, ?_⟩
    · rw [mem_conjSubgroup]
      have e2 : (r : G)⁻¹ * ((r : G) * b' * (r : G)⁻¹) * (r : G) = b' := by group
      rw [e2]
      exact hb'
    · rw [hS' _ hb'Q, hπ, map_smul, he']

end CFSG.RankThree.GF2n.Stroth80
