module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138B

open CFSG CFSG.RankThree.PartTwo Matrix CFSG.PGLModel
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree qSubPi diagUnits torusHom diagTau
  cycThree coe_diagUnits coe_torusHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K]

theorem exists_fixed_subgroup_eightyOne {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (h9 : 9 ∣ qSubPi π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {s z g : GL (Fin 3) K} (hz : z ∈ CFSG.Open.StatedScalars (Fin 3) K)
    (hg : g ∈ glPi π 3 (p ^ f) K) (hD : g⁻¹ * (s * z) * g = diagTau hτ) :
    ∃ Q : Subgroup (projImage (slPi π 3 (p ^ f) K)), IsPGroup 3 Q ∧ 81 ≤ Nat.card Q ∧
      ∀ m ∈ Q, ProjGenLinGroup.mk s * (m : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk s)⁻¹ = m := by
  classical
  have : Finite K := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set T₉ := rootsOfUnity 9 K with hT₉
  have hT₉T : T₉ ≤ rootsOfUnity (qSubPi π (p ^ f)) K := rootsOfUnity_le_of_dvd h9
  have hT₉c : Nat.card T₉ = 9 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (h9.trans (Sec4.qSubPi_dvd hK))
  set φ : T₉ × T₉ →* GL (Fin 3) K := torusHom.comp (T₉.subtype.prodMap T₉.subtype) with hφ
  have hφinj : Function.Injective φ := by
    intro x y h
    have h' := Sec4.torusHom_injective h
    simp only [MonoidHom.coe_prodMap, Prod.map, Subgroup.coe_subtype] at h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  set D₉ := φ.range with hD₉
  have hD₉c : Nat.card D₉ = 81 := by
    rw [hD₉, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, hT₉c]
  have hD₉p : IsPGroup 3 D₉ := IsPGroup.of_card (n := 4) (by rw [hD₉c]; norm_num)
  have hD₉SL : D₉ ≤ slPi π 3 (p ^ f) K := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Sec4.torusHom_mem_slPi hK (hT₉T a.2) (hT₉T b.2)
  have hc₃SL : cycThree ∈ slPi π 3 (p ^ f) K := Sec4.cycThree_mem_slPi hπ
  have hc₃3 : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_apply, Fin.sum_univ_three]
  have hc₃p : IsPGroup 3 (Subgroup.zpowers (cycThree : GL (Fin 3) K)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime hc₃3 fun h1 => ?_
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [Sec4.coe_cycThree] at h2
  have hc₃N : Subgroup.zpowers (cycThree : GL (Fin 3) K) ≤
      Subgroup.normalizer (D₉ : Set (GL (Fin 3) K)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := hn
    refine ⟨⟨(a * b)⁻¹, a⟩, ?_⟩
    change torusHom ((((a * b)⁻¹ : T₉) : Kˣ), (a : Kˣ)) =
      cycThree * torusHom ((a : Kˣ), (b : Kˣ)) * cycThree⁻¹
    change diagUnits _ _ _ = cycThree * diagUnits _ _ _ * cycThree⁻¹
    rw [Sec4.cycThree_conj_diagUnits]
    congr 1
    all_goals (try simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    all_goals (try group)
  set X := Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ D₉ with hX
  have hXp : IsPGroup 3 X := IsPGroup.to_sup_of_normal_right' hc₃p hD₉p hc₃N
  have hXSL : X ≤ slPi π 3 (p ^ f) K := sup_le (Subgroup.zpowers_le.mpr hc₃SL) hD₉SL
  set dbar := ProjGenLinGroup.mk (diagTau hτ) with hdbar
  have hXC : X ≤ (Subgroup.centralizer {dbar}).comap ProjGenLinGroup.mk := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      set u : Kˣ := Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0) with hu
      have e1 : cycThree * diagTau hτ * cycThree⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ := by
        apply Units.ext
        rw [Sec4.cycThree_conj_diagTau hτ, Units.val_mul, GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, hu, Units.val_mk0, smul_eq_diagonal_mul]
      have e2 : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * dbar *
          (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ = dbar := by
        rw [hdbar, ← map_inv, ← map_mul, ← map_mul, e1, map_mul, ProjGenLinGroup.mk_scalar,
          one_mul]
      calc ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * dbar =
          ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * dbar *
            (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ *
              ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by group
        _ = dbar * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by rw [e2]
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hdbar, ← map_mul,
        ← map_mul]
      congr 1
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      change ((torusHom ((a : Kˣ), (b : Kˣ)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((torusHom ((a : Kˣ), (b : Kˣ)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [coe_torusHom, Sec4.coe_diagTau_eq_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
  set Y := X.map (MulAut.conj g).toMonoidHom with hY
  have hYSL : Y ≤ slPi π 3 (p ^ f) K := by
    rintro _ ⟨x, hx, rfl⟩
    exact Sec4.conj_mem_slPi hπ hg (hXSL hx)
  set Q₀ := Y.map ProjGenLinGroup.mk with hQ₀
  have hQ₀le : Q₀ ≤ projImage (slPi π 3 (p ^ f) K) := Subgroup.map_mono hYSL
  have hQ₀p : IsPGroup 3 Q₀ := (hXp.map _).map _
  set Xbar := X.map ProjGenLinGroup.mk with hXbar
  have hQ₀X : Q₀ = Xbar.map (MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom := by
    rw [hQ₀, hY, hXbar, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hXbarp : IsPGroup 3 Xbar := hXp.map _
  set Dbar := D₉.map ProjGenLinGroup.mk with hDbar
  have hDX : Dbar ≤ Xbar := Subgroup.map_mono le_sup_right
  have hker3 : Nat.card ↥((ProjGenLinGroup.mk : GL (Fin 3) K →* _).ker ⊓ D₉) ≤ 3 := by
    set τu : Kˣ := Units.mk0 τ hτ0 with hτu
    have hτp : IsPrimitiveRoot τ 3 := by
      refine IsPrimitiveRoot.mk_of_lt τ (by norm_num) hτ fun l hl0 hl3 hτl => ?_
      interval_cases l
      · exact hτ1 (by simpa using hτl)
      · apply hτ1
        have h2 : τ ^ 2 = 1 := hτl
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, h2, div_one]
    have hle : (ProjGenLinGroup.mk : GL (Fin 3) K →* _).ker ⊓ D₉ ≤
        Subgroup.zpowers (GeneralLinearGroup.scalar (Fin 3) τu) := by
      rintro x ⟨hxk, ⟨⟨a, b⟩, rfl⟩⟩
      have hxk' : ProjGenLinGroup.mk (φ (a, b)) = 1 := hxk
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hxk'
      obtain ⟨l, hl⟩ := hxk'
      have hm := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hl
      have h0 := congrFun (congrFun hm 0) 0
      have h1 := congrFun (congrFun hm 1) 1
      have h2 := congrFun (congrFun hm 2) 2
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h0 h1 h2
      change (l : K) = ((torusHom ((a : Kˣ), (b : Kˣ)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 0 at h0
      change (l : K) = ((torusHom ((a : Kˣ), (b : Kˣ)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 1 at h1
      change (l : K) = ((torusHom ((a : Kˣ), (b : Kˣ)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 2 2 at h2
      rw [coe_torusHom] at h0 h1 h2
      simp only [diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
      have hl3 : (l : K) ^ 3 = 1 := by
        have e : ((((a : Kˣ) * (b : Kˣ))⁻¹ : Kˣ) : K) * ((a : Kˣ) : K) * ((b : Kˣ) : K) = 1 := by
          rw [← Units.val_mul, ← Units.val_mul, mul_assoc, inv_mul_cancel, Units.val_one]
        rw [← h0, ← h1, ← h2] at e
        rw [pow_succ, pow_succ, pow_one]
        linear_combination e
      obtain ⟨i, -, hi⟩ := hτp.eq_pow_of_pow_eq_one hl3
      rw [← hl, Subgroup.mem_zpowers_iff]
      refine ⟨i, ?_⟩
      rw [zpow_natCast, ← map_pow]
      congr 1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hi])
    have hcz : Nat.card (Subgroup.zpowers (GeneralLinearGroup.scalar (Fin 3) τu)) ≤ 3 := by
      rw [Nat.card_zpowers]
      refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
      rw [← map_pow]
      have : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ,
        Units.val_one])
      rw [this, map_one]
    exact (Subgroup.card_le_of_le hle).trans hcz
  have hDbar : 27 ≤ Nat.card Dbar := by
    have h1 : Nat.card Dbar *
        Nat.card ↥((ProjGenLinGroup.mk : GL (Fin 3) K →* _).ker ⊓ D₉) = 81 := by
      rw [← hD₉c, ← Subgroup.relIndex_mul_card (ProjGenLinGroup.mk : GL (Fin 3) K →* _).ker D₉,
        Subgroup.relIndex_ker]
    have h2 := Nat.mul_le_mul_left (Nat.card Dbar) hker3
    omega
  have hcX : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ∈ Xbar :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hcD : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ∉ Dbar := by
    rintro ⟨x, ⟨⟨a, b⟩, rfl⟩, hx⟩
    have hk : (φ (a, b))⁻¹ * cycThree ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_inv, hx, inv_mul_cancel]
    rw [GeneralLinearGroup.center_eq_range_scalar] at hk
    obtain ⟨l, hl⟩ := hk
    have hm := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hl
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at hm
    change (l : K) = (((φ (a, b))⁻¹ * cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
      at hm
    rw [Units.val_mul, ← map_inv] at hm
    change (l : K) = ((torusHom (((a : Kˣ), (b : Kˣ))⁻¹) : GL (Fin 3) K) *
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 0 0 at hm
    rw [coe_torusHom, Sec4.coe_cycThree] at hm
    simp [mul_apply, Fin.sum_univ_three] at hm
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ (ProjGenLinGroup.mk_surjective (n := Fin 3) (R := K))
  have hXbar : 81 ≤ Nat.card Xbar := by
    have hlt : Dbar < Xbar := lt_of_le_of_ne hDX fun h => hcD (h ▸ hcX)
    obtain ⟨n, hn⟩ := hXbarp.exists_card_eq
    obtain ⟨m, hm⟩ := (hXbarp.to_le hDX).exists_card_eq
    have hdvd : Nat.card Dbar ∣ Nat.card Xbar := Subgroup.card_dvd_of_le hDX
    have hne : Nat.card Dbar ≠ Nat.card Xbar := fun h =>
      (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge hDX h.symm.le)
    rw [hn, hm] at hdvd hne
    have hmn : m < n := by
      have hle : m ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
      exact lt_of_le_of_ne hle fun h => hne (by rw [h])
    have h27 : 27 ≤ 3 ^ m := hm ▸ hDbar
    rw [hn]
    calc 81 = 27 * 3 := by norm_num
      _ ≤ 3 ^ m * 3 := Nat.mul_le_mul_right 3 h27
      _ = 3 ^ (m + 1) := by ring
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  have hsz : s * z = g * diagTau hτ * g⁻¹ := by rw [← hD]; group
  have hzmk : ProjGenLinGroup.mk z = 1 := by
    obtain ⟨u, rfl⟩ := hz
    exact ProjGenLinGroup.mk_scalar u
  have hs : ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk g * dbar * (ProjGenLinGroup.mk g)⁻¹ := by
    have := congrArg ProjGenLinGroup.mk hsz
    rw [map_mul, hzmk, mul_one, map_mul, map_mul, map_inv] at this
    exact this
  refine ⟨Q₀.subgroupOf (projImage (slPi π 3 (p ^ f) K)), ?_, ?_, ?_⟩
  · exact hQ₀p.comap_of_injective _ (Subgroup.subtype_injective _)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀le).toEquiv, hQ₀X,
      Subgroup.card_map_of_injective (MulAut.conj (ProjGenLinGroup.mk g)).injective]
    exact hXbar
  · intro m hm
    have hm' : (m : ProjGenLinGroup (Fin 3) K) ∈ Q₀ := hm
    rw [hQ₀X] at hm'
    obtain ⟨xb, hxb, hxbm⟩ := hm'
    obtain ⟨x, hx, rfl⟩ := hxb
    have hxd : ProjGenLinGroup.mk x * dbar = dbar * ProjGenLinGroup.mk x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hXC hx)
    rw [← hxbm, hs]
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc ProjGenLinGroup.mk g * dbar * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk x * (ProjGenLinGroup.mk g)⁻¹) *
          (ProjGenLinGroup.mk g * dbar * (ProjGenLinGroup.mk g)⁻¹)⁻¹ =
        ProjGenLinGroup.mk g * (dbar * ProjGenLinGroup.mk x) * dbar⁻¹ *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk x * dbar) * dbar⁻¹ *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [hxd]
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk x * (ProjGenLinGroup.mk g)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec13.Ronan138B
