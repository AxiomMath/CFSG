module

public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Quasithin.Background.D2Decomp

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Open

section SL2

variable {K : Type} [Field K] [CharP K 2]

theorem fin_two_mul_self_eq_one (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1)
    (htr : A 0 0 + A 1 1 = 0) : A * A = 1 := by
  rw [Matrix.det_fin_two] at hA
  rw [Matrix.eta_fin_two A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem exists_fin_two_inverting (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1)
    (htr : A 0 0 + A 1 1 ≠ 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, S.det = 1 ∧ S * S = 1 ∧ S * A * S * A = 1 := by
  rw [Matrix.det_fin_two] at hA
  rw [Matrix.eta_fin_two A]
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  by_cases hc : c = 0
  · obtain ⟨α, hα⟩ : ∃ α : K, α * (a + d) = b := ⟨b / (a + d), div_mul_cancel₀ b htr⟩
    refine ⟨!![α, 1 + α ^ 2; 1, α], ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · obtain ⟨β, hβ⟩ : ∃ β : K, β * c = a + d := ⟨(a + d) / c, div_mul_cancel₀ _ hc⟩
    refine ⟨!![1, β; 0, 1], ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem exists_statedSL_two_inverting (g : ↥(StatedSL 2 K)) (hg : g ^ 2 ≠ 1) :
    ∃ s : ↥(StatedSL 2 K), s * s = 1 ∧ s * g * s = g⁻¹ := by
  set A : Matrix (Fin 2) (Fin 2) K := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hdet : A.det = 1 := StatedAPI.det_of_mem_statedSL g.2
  have htr : A 0 0 + A 1 1 ≠ 0 := by
    intro h
    apply hg
    apply Subtype.ext
    apply Units.ext
    simpa [sq] using fin_two_mul_self_eq_one A hdet h
  obtain ⟨S, hS, hSS, hSA⟩ := exists_fin_two_inverting A hdet htr
  have hS0 : S.det ≠ 0 := by rw [hS]; exact one_ne_zero
  let s : ↥(StatedSL 2 K) := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero S hS0,
    StatedAPI.mem_statedSL_of_det (by simpa using hS)⟩
  refine ⟨s, ?_, eq_inv_of_mul_eq_one_left ?_⟩
  · apply Subtype.ext
    apply Units.ext
    simpa [s] using hSS
  · apply Subtype.ext
    apply Units.ext
    simpa [s] using hSA

end SL2

theorem exists_orderOf_eq_comm_of_mem_normalizer {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} [Finite H] {z : G} (hz : z ∈ Subgroup.normalizer (H : Set G))
    (hzp : z ^ p = 1) (hpH : p ∣ Nat.card H) :
    ∃ c ∈ H, orderOf c = p ∧ c * z = z * c := by
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (H : Set G) := Subgroup.zpowers_le.2 hz
  let _ := MulDistribMulAction.compHom H (H.normalizerMonoidHom.comp (Subgroup.inclusion hzN))
  have hP : IsPGroup p ↥(Subgroup.zpowers z) := IsPGroup.of_card_dvd_pow (n := 1)
    (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hzp)
  have hdvd : p ∣ Nat.card (FixedPoints.subgroup ↥(Subgroup.zpowers z) ↥H) :=
    Nat.modEq_zero_iff_dvd.1 ((hP.card_modEq_card_fixedPoints ↥H).symm.trans
      (Nat.modEq_zero_iff_dvd.2 hpH))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((c : ↥H) : G), (c : ↥H).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have h1 : (⟨z, Subgroup.mem_zpowers z⟩ : ↥(Subgroup.zpowers z)) • (c : ↥H) = c := c.2 _
    have h2 : z * ((c : ↥H) : G) * z⁻¹ = ((c : ↥H) : G) := congrArg Subtype.val h1
    calc ((c : ↥H) : G) * z = z * ((c : ↥H) : G) * z⁻¹ * z := by rw [h2]
      _ = z * ((c : ↥H) : G) := by group

theorem false_of_dihedral_mul_elemAbelian {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsQuotientOfSQTKTC ↥M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u s c z : G} (huM : u ∈ M) (hsM : s ∈ M) (hcM : c ∈ M) (hzM : z ∈ M)
    (hu : u ^ p = 1) (hu1 : u ≠ 1) (hc : c ^ p = 1) (hc1 : c ≠ 1) (hz : z ^ p = 1)
    (hss : s * s = 1) (hsu : s * u * s = u⁻¹)
    (huc : u * c = c * u) (huz : u * z = z * u) (hcz : c * z = z * c)
    (hsc : s * c = c * s) (hsz : s * z = z * s)
    (hzc : z ∉ Subgroup.zpowers c) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsinv : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
  have hu2 : u * u ≠ 1 := by
    intro h
    have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [orderOf_eq_prime hu hu1] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  set P : Subgroup G := Subgroup.closure {u, c, z}
  have hgen : ∀ x ∈ ({u, c, z} : Set G), ∀ y ∈ ({u, c, z} : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | assumption | exact huc.symm | exact huz.symm | exact hcz.symm
  have hPc : P ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact (Subgroup.closure_le _).2 fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun y hy => hgen y hy x hx
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hPc hy) x hx
  have hexp : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact hu
      · exact hc
      · exact hz
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hcomm x hx y hy) p), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hsP : ∀ x ∈ P, s * x * s ∈ P := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · rw [hsu]
        exact P.inv_mem (Subgroup.subset_closure (by simp))
      · rw [hsc, mul_assoc, hss, mul_one]
        exact Subgroup.subset_closure (by simp)
      · rw [hsz, mul_assoc, hss, mul_one]
        exact Subgroup.subset_closure (by simp)
    | one => rw [mul_one, hss]; exact P.one_mem
    | mul x y hx hy ihx ihy =>
      have e : s * (x * y) * s = (s * x * s) * (s * y * s) := by
        calc s * (x * y) * s = s * x * (s * s) * y * s := by rw [hss]; group
          _ = (s * x * s) * (s * y * s) := by group
      rw [e]
      exact P.mul_mem ihx ihy
    | inv x hx ih =>
      have e : s * x⁻¹ * s = (s * x * s)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, hsinv, mul_assoc]
      rw [e]
      exact P.inv_mem ih
  let X : Subgroup G :=
    { carrier := {x | x ∈ P ∨ s * x ∈ P}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · right
          have e : s * (x * y) = (s * x * s) * (s * y) := by
            calc s * (x * y) = s * x * (s * s) * y := by rw [hss]; group
              _ = (s * x * s) * (s * y) := by group
          rw [e]
          exact P.mul_mem (hsP x hx) hy
        · right
          rw [← mul_assoc]
          exact P.mul_mem hx hy
        · left
          have e : x * y = (s * (s * x) * s) * (s * y) := by
            calc x * y = (s * s) * x * (s * s) * y := by rw [hss]; group
              _ = (s * (s * x) * s) * (s * y) := by group
          rw [e]
          exact P.mul_mem (hsP _ hx) hy
      one_mem' := Or.inl P.one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · right
          have e : s * x⁻¹ = s * (s * x)⁻¹ * s := by
            simp only [mul_inv_rev, hsinv, mul_assoc, hss, mul_one]
          rw [e]
          exact hsP _ (P.inv_mem hx) }
  have hmemX : ∀ {x : G}, x ∈ X ↔ x ∈ P ∨ s * x ∈ P := Iff.rfl
  have hPM : P ≤ M := (Subgroup.closure_le _).2 (by
    rintro x (rfl | rfl | rfl)
    · exact huM
    · exact hcM
    · exact hzM)
  have hXM : X ≤ M := by
    rintro x (hx | hx)
    · exact hPM hx
    · have e : x = s * (s * x) := by rw [← mul_assoc, hss, one_mul]
      rw [e]
      exact M.mul_mem hsM (hPM hx)
  have hPX : P ≤ X := fun x hx => Or.inl hx
  have hsX : s ∈ X := Or.inr (by rw [hss]; exact P.one_mem)
  have huP : u ∈ P := Subgroup.subset_closure (by simp)
  have hcP : c ∈ P := Subgroup.subset_closure (by simp)
  have hzP : z ∈ P := Subgroup.subset_closure (by simp)
  have hPn : (P.subgroupOf X).Normal := by
    refine ⟨fun ⟨q, hqX⟩ hq ⟨x, hxX⟩ => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases (hmemX.1 hxX) with hx | hx
    · exact P.mul_mem (P.mul_mem hx hq) (P.inv_mem hx)
    · have e : x * q * x⁻¹ = s * ((s * x) * q * (s * x)⁻¹) * s := by
        rw [mul_inv_rev, hsinv]
        calc x * q * x⁻¹ = (s * s) * x * q * x⁻¹ * (s * s) := by rw [hss]; group
          _ = s * ((s * x) * q * (x⁻¹ * s)) * s := by group
      rw [e]
      exact hsP _ (P.mul_mem (P.mul_mem hx hq) (P.inv_mem hx))
  have hPp : IsPGroup p ↥(P.subgroupOf X) := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hexp _ (Subgroup.mem_subgroupOf.1 hx)
  have hPcore : P.subgroupOf X ≤ pCore p ↥X := by
    unfold CFSG.pCore
    exact le_sSup ⟨hPn, hPp⟩
  have hF : Subgroup.centralizer (pCore p ↥X : Set ↥X) ≤ pCore p ↥X := by
    rintro ⟨x, hxX⟩ hx
    apply hPcore
    rw [Subgroup.mem_subgroupOf]
    rcases (hmemX.1 hxX) with hxP | hxP
    · exact hxP
    · exfalso
      have hu' : (⟨u, hPX huP⟩ : ↥X) ∈ pCore p ↥X := hPcore (Subgroup.mem_subgroupOf.2 huP)
      have h1 : u * x = x * u := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx _ hu')
      have hq := hcomm _ hxP u huP
      apply hu2
      have h4 : s * u * x = u * s * x :=
        calc s * u * x = s * (u * x) := mul_assoc _ _ _
          _ = s * (x * u) := by rw [h1]
          _ = (s * x) * u := (mul_assoc _ _ _).symm
          _ = u * (s * x) := hq
          _ = u * s * x := (mul_assoc _ _ _).symm
      have h2 : s * u = u * s := mul_right_cancel h4
      have h5 : s * u * s = u := by rw [h2, mul_assoc, hss, mul_one]
      rw [hsu] at h5
      calc u * u = u * u⁻¹ := by rw [h5]
        _ = 1 := mul_inv_cancel u
  set s' : ↥X := ⟨s, hsX⟩
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hu2
    rw [one_mul, mul_one] at hsu
    calc u * u = u * u⁻¹ := by rw [← hsu]
      _ = 1 := mul_inv_cancel u
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers s') := IsPGroup.of_card_dvd_pow (n := 1)
    (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [s', sq, hss])))
  have hT1 : Subgroup.zpowers s' ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    exact hs1 (congrArg Subtype.val h)
  obtain ⟨S, _, _, hSQ, -, φ, hφ⟩ := hM
  set Gc : Subgroup S := (X.subgroupOf M).comap φ
  let φ' : ↥Gc →* ↥X :=
    (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom.comp (φ.subgroupComap (X.subgroupOf M))
  have hφ' : Function.Surjective φ' :=
    (Subgroup.subgroupOfEquivOfLe hXM).surjective.comp (φ.subgroupComap_surjective _ hφ)
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥Gc) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt Gc.subtype
      Gc.subtype_injective).trans (hSQ p hp hp2)
  have hcyc := (A1c.A131Concl_of_surjective hp2 hF _ ↥Gc φ' hφ' rfl hrk).1 _ hT2 hT1
  set C := pCore p ↥X ⊓ Subgroup.centralizer (Subgroup.zpowers s' : Set ↥X)
  have hcent : ∀ w : ↥X, (w : G) * s = s * w →
      w ∈ Subgroup.centralizer (Subgroup.zpowers s' : Set ↥X) := by
    intro w hw
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc' : Commute s' w := Subtype.ext hw.symm
    exact (hc'.zpow_left k).eq
  have hcC : (⟨c, hPX hcP⟩ : ↥X) ∈ C :=
    ⟨hPcore (Subgroup.mem_subgroupOf.2 hcP), hcent _ hsc.symm⟩
  have hzC : (⟨z, hPX hzP⟩ : ↥X) ∈ C :=
    ⟨hPcore (Subgroup.mem_subgroupOf.2 hzP), hcent _ hsz.symm⟩
  set c'' : ↥C := ⟨_, hcC⟩
  set z'' : ↥C := ⟨_, hzC⟩
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hoc : orderOf c'' = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc hc1
  have hoz : orderOf z'' = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz hz1
  have hle : Subgroup.zpowers z'' ≤ Subgroup.zpowers c'' := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hoc, hoz]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_zpowers z''))
  apply hzc
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have := congrArg Subtype.val (congrArg Subtype.val hk)
  simpa [c'', z''] using this

end CFSG.Quasithin.RonanD321
