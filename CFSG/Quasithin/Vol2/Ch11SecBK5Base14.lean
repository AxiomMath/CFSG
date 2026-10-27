module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Borel
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base12

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
open Matrix

variable {K : Type} [Field K] [CharP K 2]


@[expose] def IsScalG2 (b : GL (Fin 6) K) : Prop :=
  ∃ (c : K) (g : ↥(cayleyGroup K)), c ≠ 0 ∧
    (b : Matrix (Fin 6) (Fin 6) K) = c • ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

noncomputable abbrev u0Six (K : Type) [Field K] [CharP K 2] : Subgroup (GL (Fin 6) K) :=
  (U0 K).map g2Six

omit [CharP K 2] in
theorem mem_flagStab_of_smul {b m : GL (Fin 6) K} {c : K} (hc : c ≠ 0)
    (hb : (b : Matrix (Fin 6) (Fin 6) K) = c • (m : Matrix (Fin 6) (Fin 6) K)) {h : ℕ} :
    b ∈ Tri.flagStab 6 h K ↔ m ∈ Tri.flagStab 6 h K := by
  rw [Tri.mem_flagStab, Tri.mem_flagStab, hb]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]

omit [CharP K 2] in
theorem commute_of_smul {b m x : GL (Fin 6) K} {c : K} (hc : c ≠ 0)
    (hb : (b : Matrix (Fin 6) (Fin 6) K) = c • (m : Matrix (Fin 6) (Fin 6) K))
    (h : x * b = b * x) : x * m = m * x := by
  apply Units.ext
  have h1 := congrArg (fun y : GL (Fin 6) K => (y : Matrix (Fin 6) (Fin 6) K)) h
  simp only [Units.val_mul, hb, Matrix.mul_smul, Matrix.smul_mul] at h1
  rw [Units.val_mul, Units.val_mul]
  exact smul_right_injective _ hc h1

omit [CharP K 2] in
theorem conj_of_smul {b m : GL (Fin 6) K} {c : K}
    (hb : (b : Matrix (Fin 6) (Fin 6) K) = c • (m : Matrix (Fin 6) (Fin 6) K))
    (x : GL (Fin 6) K) : b * x * b⁻¹ = m * x * m⁻¹ := by
  have e : ((b * m⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c • 1 := by
    rw [Units.val_mul, hb, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hs : ∀ y : GL (Fin 6) K, y * (b * m⁻¹) = (b * m⁻¹) * y := fun y => Units.ext (by
    rw [Units.val_mul y (b * m⁻¹), e, Units.val_mul (b * m⁻¹) y, e, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
  calc b * x * b⁻¹ = (b * m⁻¹) * (m * x * m⁻¹) * (b * m⁻¹)⁻¹ := by group
    _ = (m * x * m⁻¹) * (b * m⁻¹) * (b * m⁻¹)⁻¹ := by rw [hs]
    _ = m * x * m⁻¹ := by group

omit [CharP K 2] in
theorem mem_normalizer_of_smul {b m : GL (Fin 6) K} {c : K}
    (hb : (b : Matrix (Fin 6) (Fin 6) K) = c • (m : Matrix (Fin 6) (Fin 6) K))
    {O : Subgroup (GL (Fin 6) K)} (hbO : b ∈ Subgroup.normalizer (O : Set (GL (Fin 6) K))) :
    m ∈ Subgroup.normalizer (O : Set (GL (Fin 6) K)) :=
  Subgroup.mem_normalizer_iff.mpr fun x => by
    rw [← conj_of_smul hb x]
    exact Subgroup.mem_normalizer_iff.mp hbO x

theorem mem_flagStab_iff_of_isScalG2 {b : GL (Fin 6) K} {c : K} {g : ↥(cayleyGroup K)}
    (hc : c ≠ 0) (hbg : (b : Matrix (Fin 6) (Fin 6) K) =
      c • ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) {h : ℕ} :
    b ∈ Tri.flagStab 6 h K ↔ g ∈ stabQ (stdF K h) := by
  rw [mem_flagStab_of_smul hc hbg, g2Six_mem_flagStab_iff]

theorem stab_of_normal_g2 {B O : Subgroup (GL (Fin 6) K)} (hBG : ∀ b ∈ B, IsScalG2 b)
    (hO1 : O ≠ ⊥) (hOU : O ≤ (U0 K).map g2Six)
    (hON : B ⊔ (U0 K).map g2Six ≤ Subgroup.normalizer (O : Set (GL (Fin 6) K))) :
    ∃ h, 1 ≤ h ∧ h ≤ 5 ∧ B ≤ Tri.flagStab 6 h K := by
  classical
  set O' := O.comap g2Six with hO'
  have hO'U : O' ≤ U0 K := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hOU hx
    rwa [← g2Six_injective hux]
  have hnorm : ∀ g : ↥(cayleyGroup K),
      g2Six g ∈ Subgroup.normalizer (O : Set (GL (Fin 6) K)) → ∀ x ∈ O', g⁻¹ * x * g ∈ O' := by
    intro g hg x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (g2Six x)).mp hx
    rw [inv_inv] at this
    show g2Six (g⁻¹ * x * g) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact this
  let S : Submodule K (Ix3 → K) :=
    { carrier := {w | ∀ x ∈ O', g2Act x w = w}
      add_mem' := fun {v w} hv hw x hx => by rw [map_add, hv x hx, hw x hx]
      zero_mem' := fun x _ => map_zero _
      smul_mem' := fun c v hv x hx => by rw [JonesParshall.g2Act_smul, hv x hx] }
  have hmemS : ∀ {w : Ix3 → K}, w ∈ S ↔ ∀ x ∈ O', g2Act x w = w := Iff.rfl
  have hstab : ∀ g : ↥(cayleyGroup K), g2Six g ∈ Subgroup.normalizer (O : Set (GL (Fin 6) K)) →
      ∀ w ∈ S, g2Act g w ∈ S := by
    intro g hg w hw
    refine hmemS.mpr fun x hx => ?_
    have h1 := hmemS.mp hw _ (hnorm g hg x hx)
    rw [g2Act_mul_apply, g2Act_mul_apply] at h1
    calc g2Act x (g2Act g w) = g2Act g (g2Act g⁻¹ (g2Act x (g2Act g w))) :=
          (g2Act_apply_inv g _).symm
      _ = g2Act g w := by rw [h1]
  obtain ⟨h, h6, hSh⟩ := eq_stdF_of_stable (S := S) fun u hu w hw =>
    hstab u (hON (le_sup_right (a := B) ⟨u, hu, rfl⟩)) w hw
  have hv0 : (Pi.single (bv 0) 1 : Ix3 → K) ∈ S := fun x hx =>
    U0_fix_one (hO'U hx) (single_mem_stdF (by norm_num) (by norm_num))
  have hh1 : 1 ≤ h := by
    by_contra h0
    have : h = 0 := by omega
    rw [hSh, this, stdF_zero, Submodule.mem_bot] at hv0
    have := congrFun hv0 (bv 0)
    simp at this
  have hh5 : h ≤ 5 := by
    by_contra h5
    have : h = 6 := by omega
    rw [this, stdF_six] at hSh
    apply hO1
    rw [eq_bot_iff]
    intro o ho
    obtain ⟨x, -, rfl⟩ := hOU ho
    have hx : x ∈ O' := ho
    have hx1 : x = 1 := cayley_eq_one fun w => hmemS.mp (hSh ▸ Submodule.mem_top) x hx
    rw [hx1, map_one]
    exact (⊥ : Subgroup (GL (Fin 6) K)).one_mem
  refine ⟨h, hh1, hh5, fun b hb => ?_⟩
  obtain ⟨c, g, hc, hbg⟩ := hBG b hb
  have hgN := mem_normalizer_of_smul hbg (hON (le_sup_left (b := (U0 K).map g2Six) hb))
  have hgN' : g2Six g⁻¹ ∈ Subgroup.normalizer (O : Set (GL (Fin 6) K)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hgN
  rw [mem_flagStab_iff_of_isScalG2 hc hbg, ← hSh]
  refine mem_stabQ.mpr fun w => ⟨hstab g hgN w, fun hw => ?_⟩
  have := hstab g⁻¹ hgN' _ hw
  rwa [g2Act_inv_apply] at this

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
