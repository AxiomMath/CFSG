module

public import CFSG.Quasithin.MS93.S33XCoc
public import CFSG.Quasithin.MS93.S5BXZ

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Perfect

variable {G : Type} [Group G] {L B : Subgroup G}

theorem mem_centralizer_of_perfect (hL : ⁅L, L⁆ = L) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBL : B ≤ Subgroup.centralizer (L : Set G)) {y : G}
    (hy : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ B) : y ∈ Subgroup.centralizer (L : Set G) := by
  set ψ : G → G := fun l => l * y * l⁻¹ * y⁻¹ with hψ
  have hcent : ∀ g ∈ L, ∀ b ∈ B, g * b * g⁻¹ = b := fun g hg b hb => by
    rw [Subgroup.mem_centralizer_iff.mp (hBL hb) g hg, mul_inv_cancel_right]
  have hmul : ∀ g ∈ L, ∀ g' ∈ L, ψ (g * g') = ψ g * ψ g' := by
    intro g hg g' hg'
    calc ψ (g * g') = (g * ψ g' * g⁻¹) * ψ g := by simp only [hψ]; group
      _ = ψ g' * ψ g := by rw [hcent g hg _ (hy g' hg')]
      _ = ψ g * ψ g' := hBc _ (hy g' hg') _ (hy g hg)
  have hone : ψ 1 = 1 := by simp [hψ]
  have hinv : ∀ g ∈ L, ψ g⁻¹ = (ψ g)⁻¹ := by
    intro g hg
    have h1 := hmul g hg g⁻¹ (inv_mem hg)
    rw [mul_inv_cancel, hone] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have hle : L ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [← hL, Subgroup.commutator_le]
    intro g hg g' hg'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ψ ⁅g, g'⁆ = 1 := by
      rw [commutatorElement_def, hmul _ (mul_mem (mul_mem hg hg') (inv_mem hg)) _ (inv_mem hg'),
        hmul _ (mul_mem hg hg') _ (inv_mem hg), hmul _ hg _ hg', hinv g hg, hinv g' hg']
      have hc := hBc _ (hy g hg) _ (hy g' hg')
      calc ψ g * ψ g' * (ψ g)⁻¹ * (ψ g')⁻¹ = ψ g' * ψ g * (ψ g)⁻¹ * (ψ g')⁻¹ := by rw [hc]
        _ = 1 := by group
    have h2 : ⁅g, g'⁆ * y * ⁅g, g'⁆⁻¹ * y⁻¹ = 1 := h1
    calc ⁅g, g'⁆ * y = (⁅g, g'⁆ * y * ⁅g, g'⁆⁻¹ * y⁻¹) * (y * ⁅g, g'⁆) := by group
      _ = y * ⁅g, g'⁆ := by rw [h2, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl))

end Perfect

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem xq_comm {x y : G} (hx : x ∈ Xq M) (hy : y ∈ Xq M) : x * y = y * x := by
  have hc : Xq M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)).trans inf_le_right
  exact (Subgroup.mem_centralizer_iff.mp (hc hx) y (Xq_le_pCoreOf M hy)).symm

omit [Finite G] in
theorem pCoreOf_comm_xq {o x : G} (ho : o ∈ pCoreOf 2 M) (hx : x ∈ Xq M) : o * x = x * o := by
  have hc : Xq M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)).trans inf_le_right
  exact Subgroup.mem_centralizer_iff.mp (hc hx) o ho

theorem commutator_mem_uq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {x : G} (hx : x ∈ Xq M) {g : G} (hg : g ∈ M) :
    g * x * g⁻¹ * x⁻¹ ∈ Uq M T L := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  let S : Subgroup G :=
    { carrier := {g | g ∈ M ∧ g * x * g⁻¹ * x⁻¹ ∈ Uq M T L}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro g g' ⟨hg, hgu⟩ ⟨hg', hg'u⟩
        refine ⟨mul_mem hg hg', ?_⟩
        have e : g * g' * x * (g * g')⁻¹ * x⁻¹ =
            (g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hUn hg) _).1 hg'u) hgu
      inv_mem' := by
        rintro g ⟨hg, hgu⟩
        refine ⟨inv_mem hg, ?_⟩
        have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hUn (inv_mem hg)) _).1 (inv_mem hgu) }
  have hLS : L ≤ S := fun l hl => by
    refine ⟨h.L_le hl, hXL ?_⟩
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl hx
  have hOS : pCoreOf 2 M ≤ S := fun o ho => by
    refine ⟨pCoreOf_le' M ho, ?_⟩
    rw [pCoreOf_comm_xq ho hx, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hMS : M ≤ S := by
    rw [S5B.eq_sup_pCoreOf h hd hk]
    exact sup_le hLS hOS
  exact (hMS hg).2

theorem mem_sup_of_commute (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {Z : Subgroup G} {p : Submodule F (MSP.V4 F)}
    (hp : MSP.IsPoint p) (hZ : MSP.xPoint p ≤ (Z.subgroupOf M).map a) {x : G} (hx : x ∈ Xq M)
    (hxZ : ∀ z ∈ Z, z * x = x * z) : x ∈ Uq M T L ⊔ Zq M L := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hcomm := fun (g : ↥M) => commutator_mem_uq h hd hk hXL hx g.2
  set κ : ↥M → MSP.V4 F := fun g => c.vec ⟨_, hcomm g⟩ with hκ
  have hκmul : ∀ g g' : ↥M, κ (g * g') = κ g + MSP.mat (a g) *ᵥ κ g' := by
    intro g g'
    have hconj : (g : G) * ((g' : G) * x * (g' : G)⁻¹ * x⁻¹) * (g : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn g.2) _).1 (hcomm g')
    have e : (⟨_, hcomm (g * g')⟩ : ↥(Uq M T L)) = ⟨_, hconj⟩ * ⟨_, hcomm g⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    simp only [hκ]
    rw [e, c.vec_mul, c.vec_conj g ⟨_, hcomm g'⟩ hconj, add_comm]
  have hκker : ∀ g : ↥M, a g = 1 → κ g = 0 := by
    intro g hg
    have hadd : ∀ n : ℕ, κ (g ^ n) = n • κ g := by
      intro n
      induction n with
      | zero =>
        simp only [pow_zero, zero_smul]
        have h1 := hκmul 1 1
        rw [mul_one, map_one, MSP.mat_one, Matrix.one_mulVec] at h1
        simpa using h1
      | succ n ih =>
        rw [pow_succ, hκmul, ih, map_pow, hg, one_pow, MSP.mat_one, Matrix.one_mulVec, succ_nsmul]
    obtain ⟨e, j, hj, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hg2 : ((g ^ j : ↥M) : G) ^ 2 ^ e = 1 := by
      rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one, Subgroup.coe_one]
    have haj : a (g ^ j) = 1 := by rw [map_pow, hg, one_pow]
    have hO := S5B.mem_pCoreOf_of_ker h hd haj ⟨e, hg2⟩
    have hκj : κ (g ^ j) = 0 := by
      simp only [hκ]
      rw [c.vec_eq_zero_iff]
      have e1 : ((g ^ j : ↥M) : G) * x * ((g ^ j : ↥M) : G)⁻¹ * x⁻¹ = 1 := by
        rw [pCoreOf_comm_xq hO hx, mul_inv_cancel_right, mul_inv_cancel]
      show ((g ^ j : ↥M) : G) * x * ((g ^ j : ↥M) : G)⁻¹ * x⁻¹ ∈ _
      rw [e1]
      exact one_mem _
    rw [hadd] at hκj
    obtain ⟨i, rfl⟩ := hj
    have h2 : (2 * i) • κ g = 0 := by
      have : κ g + κ g = 0 := by
        funext t
        exact CharTwo.add_self_eq_zero _
      rw [mul_nsmul, two_nsmul, this, nsmul_zero]
    rwa [succ_nsmul, h2, zero_add] at hκj
  have hsurj : Function.Surjective a := hd.2.2.1
  set φ : MSP.Sp4 F → MSP.V4 F := fun γ => κ (Classical.choose (hsurj γ)) with hφ
  have hφκ : ∀ g : ↥M, φ (a g) = κ g := by
    intro g
    set g₀ := Classical.choose (hsurj (a g)) with hg₀
    have h₀ : a g₀ = a g := Classical.choose_spec (hsurj (a g))
    have hk0 : a (g₀⁻¹ * g) = 1 := by rw [map_mul, map_inv, h₀, inv_mul_cancel]
    have := hκmul g₀ (g₀⁻¹ * g)
    rw [mul_inv_cancel_left, hκker _ hk0, Matrix.mulVec_zero, add_zero] at this
    exact this.symm
  have hφc : ∀ γ γ', φ (γ * γ') = φ γ + MSP.mat γ *ᵥ φ γ' := by
    intro γ γ'
    obtain ⟨g, rfl⟩ := hsurj γ
    obtain ⟨g', rfl⟩ := hsurj γ'
    rw [← map_mul, hφκ, hφκ, hφκ, hκmul]
  have hφ0 : ∀ t ∈ MSP.xPoint p, φ t = 0 := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := hZ ht
    rw [hφκ]
    simp only [hκ]
    rw [c.vec_eq_zero_iff]
    have e1 : ((z : ↥M) : G) * x * ((z : ↥M) : G)⁻¹ * x⁻¹ = 1 := by
      rw [hxZ _ (Subgroup.mem_subgroupOf.1 hz), mul_inv_cancel_right, mul_inv_cancel]
    show ((z : ↥M) : G) * x * ((z : ↥M) : G)⁻¹ * x⁻¹ ∈ _
    rw [e1]
    exact one_mem _
  obtain ⟨v, hv⟩ := coboundary_of_vanish_xPoint hd.2.1 hk hp hφc hφ0
  obtain ⟨u, rfl⟩ := c.exists_vec_eq v
  have hxu : ∀ g : ↥M, (g : G) * (x * (u : G)⁻¹) * (g : G)⁻¹ * (x * (u : G)⁻¹)⁻¹ ∈
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    intro g
    have hgu : (g : G) * u * (g : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn g.2) u).1 u.2
    have h1 := hv (a g)
    rw [hφκ, ← c.vec_commutator g u hgu] at h1
    have h2 : c.vec (⟨_, hcomm g⟩ * (⟨_, mul_mem hgu (inv_mem u.2)⟩ : ↥(Uq M T L))⁻¹) = 0 := by
      rw [c.vec_mul, c.vec_inv, ← sub_eq_add_neg, sub_eq_zero]
      exact h1
    rw [c.vec_eq_zero_iff] at h2
    have hgxX : (g : G) * x * (g : G)⁻¹ ∈ Xq M :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_Xq M g.2) x).1 hx
    have hguX : (g : G) * u * (g : G)⁻¹ ∈ Xq M := h.Uq_le_Xq hgu
    have huX : (u : G) ∈ Xq M := h.Uq_le_Xq u.2
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : G) * (x * (u : G)⁻¹) * (g : G)⁻¹ * (x * (u : G)⁻¹)⁻¹
        = ((g : G) * x * (g : G)⁻¹) * (((g : G) * u * (g : G)⁻¹)⁻¹ * ((u : G) * x⁻¹)) := by
          group
      _ = ((g : G) * x * (g : G)⁻¹) * (((u : G) * x⁻¹) * ((g : G) * u * (g : G)⁻¹)⁻¹) := by
          rw [xq_comm (inv_mem hguX) (mul_mem huX (inv_mem hx))]
      _ = ((g : G) * x * (g : G)⁻¹) * ((x⁻¹ * (u : G)) * ((g : G) * u * (g : G)⁻¹)⁻¹) := by
          rw [xq_comm huX (inv_mem hx)]
      _ = (g : G) * x * (g : G)⁻¹ * x⁻¹ * ((g : G) * u * (g : G)⁻¹ * (u : G)⁻¹)⁻¹ := by group
  have hyC : x * (u : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    refine mem_centralizer_of_perfect h.perfect (B := Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      (fun b hb b' hb' => xq_comm (h.Uq_le_Xq hb.1) (h.Uq_le_Xq hb'.1)) inf_le_right
      fun l hl => hxu ⟨l, h.L_le hl⟩
  have hyZ : x * (u : G)⁻¹ ∈ Zq M L :=
    Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (h.Uq_le_Xq u.2)), hyC⟩
  have e : x = (x * (u : G)⁻¹) * (u : G) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right hyZ) (Subgroup.mem_sup_left u.2)

end CFSG.Quasithin.MS93.S33
