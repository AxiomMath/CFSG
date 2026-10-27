module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsZ2Pure

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1915WProof

open CFSG.RankThree.PartTwo.Sec19.Step1917Steps

variable {X : Type} [Group X]

theorem mem_centralizer_pair_of_mem_closure {a b : X}
    (hca : (a * b * a⁻¹ * b⁻¹) * a = a * (a * b * a⁻¹ * b⁻¹))
    (hcb : (a * b * a⁻¹ * b⁻¹) * b = b * (a * b * a⁻¹ * b⁻¹)) {p : X}
    (hp : p ∈ Subgroup.closure ({a, b} : Set X)) :
    a * p * a⁻¹ * p⁻¹ ∈ Subgroup.centralizer ({a, b} : Set X) := by
  have hcomm : ∀ y ∈ Subgroup.centralizer ({a, b} : Set X),
      ∀ q ∈ Subgroup.closure ({a, b} : Set X), q * y = y * q := by
    intro y hy q hq
    have hle : Subgroup.closure ({a, b} : Set X) ≤
        Subgroup.centralizer (Subgroup.centralizer ({a, b} : Set X) : Set X) :=
      (Subgroup.closure_le _).mpr fun s hs => Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (Subgroup.mem_centralizer_iff.mp ht s hs).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hq) y hy).symm
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · rw [show x * x * x⁻¹ * x⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [Subgroup.mem_centralizer_iff]
      rintro t (rfl | ht)
      · exact hca.symm
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hcb.symm
  | one =>
    rw [show a * 1 * a⁻¹ * (1 : X)⁻¹ = 1 by group]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e, hcomm _ ihy x hx, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
    have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
    have h1 := hcomm _ (Subgroup.inv_mem _ ihx) x hx
    rw [e, mul_assoc, ← h1, inv_mul_cancel_left]
    exact Subgroup.inv_mem _ ihx

theorem mem_upperCentralSeries_two_closure_pair {a b : X}
    (hca : (a * b * a⁻¹ * b⁻¹) * a = a * (a * b * a⁻¹ * b⁻¹))
    (hcb : (a * b * a⁻¹ * b⁻¹) * b = b * (a * b * a⁻¹ * b⁻¹)) (hab : a * b ≠ b * a) :
    ∃ ha : a ∈ Subgroup.closure ({a, b} : Set X),
      (⟨a, ha⟩ : Subgroup.closure ({a, b} : Set X)) ∈
          Subgroup.upperCentralSeries (Subgroup.closure ({a, b} : Set X)) 2 ∧
        (⟨a, ha⟩ : Subgroup.closure ({a, b} : Set X)) ∉
          Subgroup.center (Subgroup.closure ({a, b} : Set X)) := by
  have ha : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  refine ⟨ha, (mem_upperCentralSeries_two_iff_of_mem ha).mpr fun p hp q hq => ?_, fun h => ?_⟩
  · have hc := mem_centralizer_pair_of_mem_closure hca hcb hp
    have hle : Subgroup.closure ({a, b} : Set X) ≤
        Subgroup.centralizer (Subgroup.centralizer ({a, b} : Set X) : Set X) :=
      (Subgroup.closure_le _).mpr fun s hs => Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (Subgroup.mem_centralizer_iff.mp ht s hs).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hq) _ hc).symm
  · exact hab ((mem_center_iff_of_mem ha).mp h b hb).symm

theorem conj_mem_upperCentralSeries_two {P : Subgroup X} {x : X} (hx : x ∈ P)
    (h2 : (⟨x, hx⟩ : P) ∈ Subgroup.upperCentralSeries P 2)
    (hZ : (⟨x, hx⟩ : P) ∉ Subgroup.center P) (k : X) :
    ∃ hkx : k * x * k⁻¹ ∈ P.map (MulAut.conj k).toMonoidHom,
      (⟨k * x * k⁻¹, hkx⟩ : P.map (MulAut.conj k).toMonoidHom) ∈
          Subgroup.upperCentralSeries (P.map (MulAut.conj k).toMonoidHom) 2 ∧
        (⟨k * x * k⁻¹, hkx⟩ : P.map (MulAut.conj k).toMonoidHom) ∉
          Subgroup.center (P.map (MulAut.conj k).toMonoidHom) := by
  have hinj : Set.InjOn (MulAut.conj k).toMonoidHom P := (MulAut.conj k).injective.injOn
  have hkx : (MulAut.conj k).toMonoidHom x ∈ P.map (MulAut.conj k).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  refine ⟨hkx, (mem_upperCentralSeries_two_map_iff _ rfl hinj hx hkx).mpr h2, fun h => hZ ?_⟩
  exact (mem_center_map_iff _ rfl hinj hx hkx).mp h

theorem threeCentralZ2_of_data [Finite X] {S₀ : Subgroup X} (hS₀ : IsPGroup 3 S₀)
    {u v z a b g : X} (hu : u ∈ S₀) (hv : v ∈ S₀)
    (hC : ∀ x : X, x * u = u * x → x * v = v * x → x = 1 ∨ x = z ∨ x = z⁻¹)
    (ha : a ∈ S₀) (hb : b ∈ S₀)
    (hca : (a * b * a⁻¹ * b⁻¹) * a = a * (a * b * a⁻¹ * b⁻¹))
    (hcb : (a * b * a⁻¹ * b⁻¹) * b = b * (a * b * a⁻¹ * b⁻¹)) (hab : a * b ≠ b * a)
    (hg : z * g = g * a) : ThreeCentralZ2 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro x hx1 ⟨S, hxS, hxc⟩
  set P₀ := Subgroup.closure ({a, b} : Set X) with hP₀
  have hP₀S : P₀ ≤ S₀ := (Subgroup.closure_le _).mpr (by
    rintro _ (rfl | h)
    · exact ha
    · rw [Set.mem_singleton_iff] at h
      exact h ▸ hb)
  have hP₀3 : IsPGroup 3 P₀ := hS₀.to_le hP₀S
  obtain ⟨haP, ha2, haZ⟩ := mem_upperCentralSeries_two_closure_pair hca hcb hab
  have haP' : a⁻¹ ∈ P₀ := P₀.inv_mem haP
  have ha2' : (⟨a⁻¹, haP'⟩ : P₀) ∈ Subgroup.upperCentralSeries P₀ 2 := by
    have := (Subgroup.upperCentralSeries P₀ 2).inv_mem ha2
    exact this
  have haZ' : (⟨a⁻¹, haP'⟩ : P₀) ∉ Subgroup.center P₀ := fun h => haZ (by
    have := (Subgroup.center P₀).inv_mem h
    have e : (⟨a⁻¹, haP'⟩ : P₀)⁻¹ = ⟨a, haP⟩ := Subtype.ext (inv_inv a)
    rw [e] at this
    exact this)
  obtain ⟨S₁, hS₀S₁⟩ := hS₀.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X S₁ S
  have hS : ∀ y : X, y ∈ (S : Subgroup X) ↔ ∃ w ∈ (S₁ : Subgroup X), k * w * k⁻¹ = y := by
    intro y
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.smul_def, MulAut.conj_apply]
  obtain ⟨x', hx'S₁, hx'⟩ := (hS x).1 hxS
  have hcomm : ∀ w ∈ (S₁ : Subgroup X), w * x' = x' * w := by
    intro w hw
    have := hxc _ ((hS _).2 ⟨w, hw, rfl⟩)
    rw [← hx'] at this
    have h2 := congrArg (fun y => k⁻¹ * y * k) this
    simpa [mul_assoc] using h2
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    exact hx1 (by simpa using hx'.symm)
  have hza : z = g * a * g⁻¹ := by rw [← hg]; group
  obtain ⟨y, hyP, hy2, hyZ, hxy⟩ : ∃ (y : X) (hyP : y ∈ P₀),
      (⟨y, hyP⟩ : P₀) ∈ Subgroup.upperCentralSeries P₀ 2 ∧ (⟨y, hyP⟩ : P₀) ∉ Subgroup.center P₀ ∧
        x = (k * g) * y * (k * g)⁻¹ := by
    rcases hC x' ((hcomm u (hS₀S₁ hu)).symm) ((hcomm v (hS₀S₁ hv)).symm) with h1 | h1 | h1
    · exact absurd h1 hx'1
    · refine ⟨a, haP, ha2, haZ, ?_⟩
      rw [← hx', h1, hza]
      group
    · refine ⟨a⁻¹, haP', ha2', haZ', ?_⟩
      rw [← hx', h1, hza]
      group
  obtain ⟨hkx, h2, hZ⟩ := conj_mem_upperCentralSeries_two hyP hy2 hyZ (k * g)
  subst hxy
  exact ⟨P₀.map (MulAut.conj (k * g)).toMonoidHom, hP₀3.map _, hkx, h2, hZ⟩

end CFSG.RankThree.PartTwo.Sec19.Step1915WProof
