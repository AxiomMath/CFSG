module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Star
public import CFSG.Quasithin.Vol2.Ch4Sec3L436NatAut

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436 L436NA
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_comm_of_exp_two {V : Subgroup G} (hV : ∀ v ∈ V, v ^ 2 = 1) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have h1 : a * a = 1 := by rw [← sq]; exact hV a ha
  have h2 : b * b = 1 := by rw [← sq]; exact hV b hb
  have h3 : a * b * (a * b) = 1 := by rw [← sq]; exact hV _ (mul_mem ha hb)
  calc a * b = a * b * (a * b) * (b * a) := by
        rw [h3, one_mul]
        have : b * a = (a * b)⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]
        rw [this, inv_eq_of_mul_eq_one_right h3]
    _ = b * a := by rw [h3, one_mul]

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem exists_mul_mem_centralizer {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (v432 T M L : Set G))
    (hxCZ : ∀ c ∈ sp4C (H ⊓ M ⊓ K) (v432 T M L) ⊔ sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
      x * c * x⁻¹ = c)
    (hxv : ∀ v ∈ v432 T M L, x * v * x⁻¹ * v⁻¹ ∈
      sp4C (H ⊓ M ⊓ K) (v432 T M L) ⊔ sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)) :
    ∃ y ∈ T ⊓ H ⊓ K, ∀ v ∈ v432 T M L, (x * y) * v * (x * y)⁻¹ = v := by
  classical
  set P := H ⊓ M ⊓ K with hP
  set S := T ⊓ H ⊓ K with hS
  set V := v432 T M L with hV
  set C := sp4C P V with hC
  set Z := sp4Z P S V with hZ
  have hLP : L = perfectCore P := s.L_eq
  obtain ⟨F, _, _, -, α, β, hαs, hαk, hβs, hβk, hβ, hSα, hΛ⟩ := s.concl.coord
  have hxL' : x ∈ Subgroup.normalizer ((perfectCore P : Subgroup G) : Set G) := hLP ▸ hxL
  have hLV : perfectCore P ≤ Subgroup.normalizer (V : Set G) := by
    have h := le_normalizer_pCoreOf 2 (perfectCore P)
    rwa [← s.concl.V_eq] at h
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := mul_comm_of_exp_two s.concl.V_sq
  have hCL : ∀ c ∈ C, ∀ ℓ ∈ perfectCore P, c * ℓ = ℓ * c := fun c hc ℓ hℓ =>
    ((Subgroup.mem_centralizer_iff.mp hc.2) ℓ hℓ).symm
  have hSCZ : ∀ y ∈ S, ∀ c ∈ C ⊔ Z, y * c * y⁻¹ = c := by
    intro y hy c hc
    have hc' : c ∈ V ⊓ Subgroup.centralizer (S : Set G) := by
      rw [s.concl.cent_S]; exact hc
    have := (Subgroup.mem_centralizer_iff.mp hc'.2) y hy
    rw [this, mul_inv_cancel_right]
  obtain ⟨v₂, hv₂⟩ := hβs (Multiplicative.ofAdd ![0, 1])
  have hv₂' : Multiplicative.toAdd (β v₂) = ![0, 1] := by rw [hv₂]; rfl
  have hxVm : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  set w : ↥V := ⟨x * v₂ * x⁻¹, hxVm v₂ v₂.2⟩ with hw
  have hwv : Multiplicative.toAdd (β (w * v₂⁻¹)) 1 = 0 :=
    (hΛ (w * v₂⁻¹)).mp (by simpa [hw] using hxv v₂ v₂.2)
  set r := Multiplicative.toAdd (β w) 0 with hr
  have hbw : Multiplicative.toAdd (β w) = ![r, 1] := by
    have h1 : Multiplicative.toAdd (β (w * v₂⁻¹)) =
        Multiplicative.toAdd (β w) - Multiplicative.toAdd (β v₂) := by
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rw [h1, hv₂'] at hwv
    ext i; fin_cases i
    · rfl
    · simpa [sub_eq_zero] using hwv
  obtain ⟨ℓ, hℓ⟩ := hαs (uT F r)
  have hℓS : (ℓ : G) ∈ S := (hSα ℓ).mpr ⟨r, hℓ⟩
  set x' := x * (ℓ : G)⁻¹ with hx'
  have hℓL : (ℓ : G) ∈ perfectCore P := ℓ.2
  have hx'L : x' ∈ Subgroup.normalizer ((perfectCore P : Subgroup G) : Set G) :=
    mul_mem hxL' (inv_mem (Subgroup.le_normalizer hℓL))
  have hx'V : x' ∈ Subgroup.normalizer (V : Set G) :=
    mul_mem hxV (inv_mem (hLV hℓL))
  have hx'CZ : ∀ c ∈ C ⊔ Z, x' * c * x'⁻¹ = c := by
    intro c hc
    have h1 : (ℓ : G)⁻¹ * c * ((ℓ : G)⁻¹)⁻¹ = c := hSCZ _ (inv_mem hℓS) c hc
    calc x' * c * x'⁻¹ = x * ((ℓ : G)⁻¹ * c * ((ℓ : G)⁻¹)⁻¹) * x⁻¹ := by rw [hx']; group
      _ = c := by rw [h1, hxCZ c hc]
  have hx'v₂ : ∀ u : ↥V, (u : G) = x' * v₂ * x'⁻¹ →
      Multiplicative.toAdd (β u) = ![0, 1] := by
    intro u hu
    have hlv : (ℓ : G)⁻¹ * v₂ * (ℓ : G) ∈ V := by
      have h := (Subgroup.mem_normalizer_iff.mp (hLV (inv_mem hℓL)) v₂).mp v₂.2
      simpa using h
    set c : ↥V := v₂⁻¹ * ⟨_, hlv⟩ with hc
    have hβl : Multiplicative.toAdd (β ⟨_, hlv⟩) = ![-r, 1] := by
      have := hβ ℓ⁻¹ v₂ ⟨_, hlv⟩ (by simp)
      rw [this, map_inv, hℓ, hv₂']
      show ((uT F r)⁻¹ : GL (Fin 2) F).val.mulVec ![0, 1] = _
      ext i; fin_cases i <;> simp [uT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hβc : Multiplicative.toAdd (β c) = ![-r, 0] := by
      rw [hc, map_mul, map_inv, toAdd_mul, toAdd_inv, hβl, hv₂']
      ext i; fin_cases i <;> simp
    have hcCZ : (c : G) ∈ C ⊔ Z := (hΛ c).mpr (by rw [hβc]; rfl)
    have hxc := hxCZ c hcCZ
    have hu' : u = w * c := by
      apply Subtype.ext
      have hxc' : x * ((v₂ : G)⁻¹ * ((ℓ : G)⁻¹ * v₂ * ℓ)) * x⁻¹ =
          (v₂ : G)⁻¹ * ((ℓ : G)⁻¹ * v₂ * ℓ) := hxc
      calc (u : G) = x' * v₂ * x'⁻¹ := hu
        _ = (x * v₂ * x⁻¹) * (x * ((v₂ : G)⁻¹ * ((ℓ : G)⁻¹ * v₂ * ℓ)) * x⁻¹) := by
            rw [hx']; group
        _ = (x * v₂ * x⁻¹) * ((v₂ : G)⁻¹ * ((ℓ : G)⁻¹ * v₂ * ℓ)) := by rw [hxc']
        _ = ((w * c : ↥V) : G) := rfl
    rw [hu', map_mul, toAdd_mul, hbw, hβc]
    ext i; fin_cases i <;> simp
  have hcent := centralizes_of_natural (Z := Z) α hαs (fun ℓ h => (hαk ℓ).mp h) β hβs hβk hβ hΛ
    hLV hVab inf_le_left hCL s.concl.comm_V hx'L hx'V hx'CZ v₂ hv₂' hx'v₂
  exact ⟨(ℓ : G)⁻¹, inv_mem hℓS, fun v hv => hcent v hv⟩

theorem starstar {x : G} (hx : x ∈ pCoreOf 2 (Subgroup.normalizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) :
    ∃ q ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
      ∀ v ∈ v432 T M L, (x * q) * v * (x * q)⁻¹ = v := by
  classical
  set P := H ⊓ M ⊓ K with hP
  set S := T ⊓ H ⊓ K with hS
  set V := v432 T M L with hV
  set C := sp4C P V with hC
  set Z := sp4Z P S V with hZ
  set Q₁ := sp4Q₁ K P S V with hQ₁
  set GZ := Subgroup.normalizer (Z : Set G) with hGZ
  have hxT : x ∈ T := s.pCoreOf_GZ_le_T hx
  have hQ₁Ω : Q₁ ≤ omegaOneCenterOf (pCoreOf 2 GZ) := s.star.1.trans s.star.2
  have hQ₁c : ∀ q ∈ Q₁, ∀ y ∈ pCoreOf 2 GZ, q * y = y * q := by
    intro q hq y hy
    have h1 : q ∈ omegaOneCenterOf (pCoreOf 2 GZ) := hQ₁Ω hq
    have h2 : omegaOneCenterOf (pCoreOf 2 GZ) ≤ centerOf (pCoreOf 2 GZ) :=
      (Subgroup.closure_le _).mpr fun z hz => hz.1
    exact ((Subgroup.mem_centralizer_iff.mp (h2 h1).2) y hy).symm
  have hCZQ : C ⊔ Z ≤ Q₁ := s.concl.V_inf_Q₁.symm.le.trans inf_le_right
  have hxCZ : ∀ c ∈ C ⊔ Z, x * c * x⁻¹ = c := fun c hc => by
    rw [← hQ₁c c (hCZQ hc) x hx, mul_inv_cancel_right]
  have hxv : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ C ⊔ Z := by
    intro v hv
    have hvGZ : v ∈ GZ :=
      (s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)) (s.concl.V_le_K₂ hv)
    have h1 : x * v * x⁻¹ * v⁻¹ ∈ V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (s.T_le_normalizer_V hxT) v).mp hv) (inv_mem hv)
    have h2 : x * v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 GZ := by
      have h3 : v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 GZ :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 GZ hvGZ) _).mp (inv_mem hx)
      have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
      rw [e]
      exact mul_mem hx h3
    have h4 : x * v * x⁻¹ * v⁻¹ ∈ V ⊓ Subgroup.centralizer (Q₁ : Set G) :=
      ⟨h1, Subgroup.mem_centralizer_iff.mpr fun q hq => hQ₁c q hq _ h2⟩
    rw [s.concl.V_cent_Q₁, s.concl.V_inf_Q₁] at h4
    exact h4
  obtain ⟨y, hyS, hy⟩ := s.exists_mul_mem_centralizer (s.T_le_normalizer_L hxT)
    (s.T_le_normalizer_V hxT) hxCZ hxv
  have hQ₁V : Q₁ ≤ Subgroup.normalizer (V : Set G) := by
    have h := s.concl.S_eq
    have hSV : S ≤ Subgroup.normalizer (V : Set G) := fun g hg => s.T_le_normalizer_V hg.1.1
    exact (le_sup_right.trans h.symm.le).trans hSV
  have hyVQ : y ∈ ((V : Set G) * (Q₁ : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V Q₁ hQ₁V, SetLike.mem_coe,
      ← s.concl.S_eq]
    exact hyS
  obtain ⟨v', hv', q, hq, rfl⟩ := hyVQ
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := mul_comm_of_exp_two s.concl.V_sq
  refine ⟨q, hq, fun v hv => ?_⟩
  have hw : q⁻¹ * v'⁻¹ * q ∈ V := by
    have h := (Subgroup.mem_normalizer_iff.mp (hQ₁V (inv_mem hq)) v'⁻¹).mp (inv_mem hv')
    simpa using h
  have h1 : (x * (v' * q)) * v * (x * (v' * q))⁻¹ = v := hy v hv
  have h2 : (q⁻¹ * v'⁻¹ * q) * v * (q⁻¹ * v'⁻¹ * q)⁻¹ = v := by
    rw [hVab _ hw v hv, mul_inv_cancel_right]
  calc (x * q) * v * (x * q)⁻¹
      = (x * (v' * q)) * ((q⁻¹ * v'⁻¹ * q) * v * (q⁻¹ * v'⁻¹ * q)⁻¹) * (x * (v' * q))⁻¹ := by
        group
    _ = v := by rw [h2, h1]

end Setting436Sp4

end CFSG.Quasithin.H13.Ch4
