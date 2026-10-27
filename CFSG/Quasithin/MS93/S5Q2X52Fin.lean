module

public import CFSG.Quasithin.MS93.S5Q2X52Six
public import CFSG.Quasithin.MS93.S5Q2X52Eq
public import CFSG.Quasithin.MS93.S5Q2X52Cent
public import CFSG.Quasithin.MS93.S33Stmt5

public noncomputable section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

theorem exists_mem_of_index_eq {A : Type*} [Group A] [Finite A] {H : Subgroup A} {n : ℕ}
    (hH : H.index = n) (g : Fin n → A) (hg : ∀ i j, i ≠ j → (g i)⁻¹ * g j ∉ H) (w : A) :
    ∃ i, (g i)⁻¹ * w ∈ H := by
  have hinj : Function.Injective (fun i => (QuotientGroup.mk (g i) : A ⧸ H)) := by
    intro i j hij
    by_contra hne
    exact hg i j hne (QuotientGroup.eq.1 hij)
  have hcard : Nat.card (Fin n) = Nat.card (A ⧸ H) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← hH, Subgroup.index]
  have : Finite (A ⧸ H) := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  obtain ⟨i, hi⟩ := (hinj.bijective_of_nat_card_le hcard.ge).2 (QuotientGroup.mk w)
  exact ⟨i, QuotientGroup.eq.1 hi⟩

section Final

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem comm_mul_left_eq {x₁ x₂ y : G} (hx₁ : x₁ ∈ Xq M) (hx₂ : x₂ ∈ Xq M) (hy : y ∈ M) :
    ⁅x₁ * x₂, y⁆ = ⁅x₁, y⁆ * ⁅x₂, y⁆ := by
  have h1 : y * x₁⁻¹ * y⁻¹ ∈ Xq M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Xq M hy) _).1 ((Xq M).inv_mem hx₁)
  have h2 : ⁅x₂, y⁆ ∈ Xq M := by
    have e : ⁅x₂, y⁆ = x₂ * (y * x₂⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Xq M).mul_mem hx₂
      ((Subgroup.mem_normalizer_iff.1 (le_normalizer_Xq M hy) _).1 ((Xq M).inv_mem hx₂))
  have hc := S5.commute_of_mem_Xq h2 h1
  calc ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * (y * x₁⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = x₁ * (y * x₁⁻¹ * y⁻¹) * ⁅x₂, y⁆ := by rw [mul_assoc x₁, hc, ← mul_assoc]
    _ = ⁅x₁, y⁆ * ⁅x₂, y⁆ := by simp only [commutatorElement_def]; group

variable {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] [Fintype F] in
theorem comm_mul_right_eq {g e y₁ : G} (hg : g * y₁ = y₁ * g) : ⁅g, e * y₁⁆ = ⁅g, e⁆ := by
  have h0 : y₁ * g⁻¹ = g⁻¹ * y₁ := by
    calc y₁ * g⁻¹ = g⁻¹ * (g * y₁) * g⁻¹ := by group
      _ = g⁻¹ * (y₁ * g) * g⁻¹ := by rw [hg]
      _ = g⁻¹ * y₁ := by group
  have h1 : y₁ * g⁻¹ * y₁⁻¹ = g⁻¹ := by rw [h0]; group
  calc ⁅g, e * y₁⁆ = g * e * (y₁ * g⁻¹ * y₁⁻¹) * e⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅g, e⁆ := by rw [h1, commutatorElement_def]

theorem exists_ne_four : ∀ a b c d : Fin 6, ∃ i, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d := by
  decide

theorem commutator_le_of_central (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L)
    (hC : Zq M L ≤ Subgroup.centralizer (M : Set G)) {K : Subgroup G} (hKM : K ≤ M)
    (hE2 : IsPGroup 2 (S5.imSp a K))
    (hq : MSP.commSp (S5.imSp a K) ≤ MSP.fixSp (S5.imSp a K)) (hE1 : S5.imSp a K ≠ ⊥)
    (hidx : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) ≤ Nat.card (S5.imSp a K))
    {Y : Subgroup G} (hYM : Y ≤ M) (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) :
    ⁅Uq M T L, Y⁆ ≤ ⁅Xq M, K⁆ ⊔ ⁅Xq M ⊓ Subgroup.centralizer (K : Set G), Y⁆ := by
  have : CharP F 2 := hd.charP
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hNF
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨x, hx, hxN⟩ := exists_mem_xFix_not_mem h hXL hne
  obtain ⟨B, m₀, hB, hform⟩ := exists_cform_of_mem_xFix hd h nv hx hxN
  obtain ⟨hEr, hshape⟩ := card_le_card_range h nv hKM hd hx hB hform hE2 hq hE1
  have hrX := card_range_le_relIndex_xFix h nv hKM
  have heq : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) =
      Nat.card (Set.range (phiK h nv hKM)) := by omega
  have hidxE : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) =
      Nat.card (S5.imSp a K) := by omega
  have hlift : ∀ {w : G}, w ∈ xFix h → (∀ κ : ↥K, S5.uCoord nv ⁅(κ : G), w⁆ = 0) →
      w ∈ Subgroup.centralizer (K : Set G) := fun hw hw0 =>
    mem_centralizer_of_relIndex_eq h nv hKM heq hw hw0
  obtain ⟨d, hdX, hconj, hdne⟩ := exists_six h hd hXL hne c
  set N := ⁅Xq M, K⁆ ⊔ ⁅Xq M ⊓ Subgroup.centralizer (K : Set G), Y⁆ with hN
  have hP2 : ∀ {g u' y : G}, g ∈ Xq M → u' ∈ Xq M ⊓ Subgroup.centralizer (K : Set G) →
      y ∈ Y → ⁅g, y⁆ ∈ ⁅Xq M, K⁆ → ⁅g * u', y⁆ ∈ N := by
    intro g u' y hg hu' hy hgy
    rw [comm_mul_left_eq hg hu'.1 (hYM hy)]
    exact mul_mem (Subgroup.mem_sup_left hgy)
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hu' hy))
  have hP1 : ∀ {g e y₁ : G}, g ∈ Xq M → e ∈ K → g * y₁ = y₁ * g →
      ⁅g, e * y₁⁆ ∈ ⁅Xq M, K⁆ := by
    intro g e y₁ hg he hgy
    rw [comm_mul_right_eq hgy]
    exact Subgroup.commutator_mem_commutator hg he
  have hKd : ∀ i, (∀ κ (hκ : κ ∈ K), (B5FinSp.theta c).symm (a ⟨κ, hKM hκ⟩) i = i) →
      d i ∈ Subgroup.centralizer (K : Set G) := by
    intro i hi
    refine hlift (hdX i) fun κ => ?_
    have h1 := hconj κ (hKM κ.2) i
    rw [hi κ κ.2] at h1
    exact uCoord_of_mem_cXL nv (by rw [commutatorElement_def]; exact h1)
  have hσcomm : ∀ {y k : G} (hy : y ∈ Y) (hk : k ∈ K),
      (B5FinSp.theta c).symm (a ⟨y, hYM hy⟩) * (B5FinSp.theta c).symm (a ⟨k, hKM hk⟩) =
        (B5FinSp.theta c).symm (a ⟨k, hKM hk⟩) * (B5FinSp.theta c).symm (a ⟨y, hYM hy⟩) := by
    intro y k hy hk
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hYK y hy k hk)
  have hswap_fix : ∀ (σ : Equiv.Perm (Fin 6)) {a₀ b₀ : Fin 6}, a₀ ≠ b₀ →
      σ * Equiv.swap a₀ b₀ = Equiv.swap a₀ b₀ * σ → σ a₀ = a₀ ∨ σ a₀ = b₀ := by
    intro σ a₀ b₀ hab hσs
    have h1 := congrArg (fun π : Equiv.Perm (Fin 6) => π a₀) hσs
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
    by_contra hcon
    push Not at hcon
    rw [Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
    exact hab (σ.injective h1).symm
  have hθinv : ∀ {k y : G} (hk : k ∈ M) (hy : y ∈ M),
      (B5FinSp.theta c).symm (a ⟨k⁻¹ * y, M.mul_mem (M.inv_mem hk) hy⟩) =
        ((B5FinSp.theta c).symm (a ⟨k, hk⟩))⁻¹ * (B5FinSp.theta c).symm (a ⟨y, hy⟩) := by
    intro k y hk hy
    have e : (⟨k⁻¹ * y, M.mul_mem (M.inv_mem hk) hy⟩ : ↥M) = (⟨k, hk⟩)⁻¹ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, map_inv, map_mul, map_inv]
  have hmemH : ∀ (z : ↥(xFix h)), z ∈ (Subgroup.centralizer (K : Set G)).subgroupOf (xFix h) ↔
      (z : G) ∈ Subgroup.centralizer (K : Set G) := fun z => Subgroup.mem_subgroupOf
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have huX : u ∈ xFix h := uq_le_xFix h hu
  have hyM := hYM hy
  rcases hshape (by omega) with ⟨w, hw, hEw⟩ | ⟨w₁, w₂, hw₁, hw₂, hw12, hform12, hEw, hE4⟩ |
    ⟨l, hl, hEl⟩
  ·
    obtain ⟨a₀, b₀, hab, hθ, hE12⟩ := exists_swap_of_xPoint c hw
    have htE : MSP.transv w 1 ∈ S5.imSp a K := by rw [hEw]; exact MSP.transv_mem_xPoint w 1
    obtain ⟨⟨k₀, hk₀M⟩, hk₀K, hk₀a⟩ := htE
    have hk₀K' : k₀ ∈ K := Subgroup.mem_subgroupOf.1 hk₀K
    have hk₀σ : (B5FinSp.theta c).symm (a ⟨k₀, hk₀M⟩) = Equiv.swap a₀ b₀ := by
      rw [hk₀a, ← hθ, MulEquiv.symm_apply_apply]
    obtain ⟨i₀, hi₀a, hi₀b, -, -⟩ := exists_ne_four a₀ b₀ a₀ b₀
    have hdi₀ : d i₀ ∈ Subgroup.centralizer (K : Set G) := hKd i₀ fun κ hκ => by
      have hκE : a ⟨κ, hKM hκ⟩ ∈ S5.imSp a K :=
        ⟨⟨κ, hKM hκ⟩, Subgroup.mem_subgroupOf.2 hκ, rfl⟩
      rw [hEw] at hκE
      rcases hE12 _ hκE with h1 | h1
      · rw [h1, map_one]
        rfl
      · rw [h1, ← hθ, MulEquiv.symm_apply_apply, Equiv.swap_apply_of_ne_of_ne hi₀a hi₀b]
    have hk₀d : k₀ * d i₀ = d i₀ * k₀ := Subgroup.mem_centralizer_iff.1 hdi₀ k₀ hk₀K'
    have hsw : ∀ (m : G) (hm : m ∈ M) (a' b' i : Fin 6), a' ≠ b' → i ≠ a' → i ≠ b' →
        (B5FinSp.theta c).symm (a ⟨m, hm⟩) = Equiv.swap a' b' → m * d i = d i * m :=
      fun m hm a' b' i hab' hia' hib' hma =>
        commute_of_swap h hd hC c hdX hconj hk₀M hab hi₀a hi₀b hk₀σ hk₀d hm hab' hia' hib' hma
    have hk₀da : ¬ k₀ * d a₀ = d a₀ * k₀ := by
      intro hcomm
      have h1 := hconj k₀ hk₀M a₀
      rw [hk₀σ, Equiv.swap_apply_left, hcomm, mul_inv_cancel_right] at h1
      exact hdne a₀ b₀ hab h1
    have hda : d a₀ ∉ Subgroup.centralizer (K : Set G) := fun hm =>
      hk₀da (Subgroup.mem_centralizer_iff.1 hm k₀ hk₀K')
    have hE2' : Nat.card (S5.imSp a K) = 2 := by
      rw [hEw, MSP.card_xPoint (MSP.isPoint_span hw), hNF]
    have hidx2 : ((Subgroup.centralizer (K : Set G)).subgroupOf (xFix h)).index = 2 := by
      rw [← hE2', ← hidxE]
      rfl
    obtain ⟨i, hi⟩ := exists_mem_of_index_eq hidx2 ![1, ⟨d a₀, hdX a₀⟩] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa [hmemH] using hda
      · simpa [hmemH] using hda
      · exact absurd rfl hij) ⟨u, huX⟩
    have hσa := hswap_fix ((B5FinSp.theta c).symm (a ⟨y, hyM⟩)) hab (by
      rw [← hk₀σ]; exact hσcomm hy hk₀K')
    obtain ⟨e, heK, hy₁⟩ : ∃ e ∈ K, d a₀ * (e⁻¹ * y) = (e⁻¹ * y) * d a₀ := by
      rcases hσa with h1 | h1
      · refine ⟨1, one_mem _, ?_⟩
        rw [inv_one, one_mul]
        exact (commute_of_fix h hd hC c hdX hsw hyM h1).symm
      · refine ⟨k₀, hk₀K', (commute_of_fix h hd hC c hdX hsw
          (M.mul_mem (M.inv_mem hk₀M) hyM) ?_).symm⟩
        rw [hθinv hk₀M hyM, hk₀σ, Equiv.swap_inv, Equiv.Perm.mul_apply, h1,
          Equiv.swap_apply_right]
    have hyey : y = e * (e⁻¹ * y) := by group
    fin_cases i
    · have hu' : u ∈ Subgroup.centralizer (K : Set G) := by simpa [hmemH] using hi
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator ⟨huX.1, hu'⟩ hy)
    · have hu' : (d a₀)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa [hmemH] using hi
      have e1 : u = d a₀ * ((d a₀)⁻¹ * u) := by group
      rw [e1]
      refine hP2 (hdX a₀).1 ⟨(Xq M).mul_mem ((Xq M).inv_mem (hdX a₀).1) huX.1, hu'⟩ hy ?_
      rw [hyey]
      exact hP1 (hdX a₀).1 heK hy₁
  ·
    obtain ⟨a₁, b₁, hab₁, hθ₁, hE₁⟩ := exists_swap_of_xPoint c hw₁
    obtain ⟨a₂, b₂, hab₂, hθ₂, hE₂⟩ := exists_swap_of_xPoint c hw₂
    have hcomm12 : Equiv.swap a₁ b₁ * Equiv.swap a₂ b₂ = Equiv.swap a₂ b₂ * Equiv.swap a₁ b₁ := by
      apply (B5FinSp.theta c).injective
      rw [map_mul, map_mul, hθ₁, hθ₂]
      exact S33.transv_mul_comm hform12 1 1
    have hne12 : Equiv.swap a₁ b₁ ≠ Equiv.swap a₂ b₂ := by
      intro he
      have h1 : MSP.transv w₁ 1 = MSP.transv w₂ 1 := by rw [← hθ₁, ← hθ₂, he]
      exact hw12 (by rw [(MSP.transv_eq_transv_iff hw₂).1 h1])
    obtain ⟨h12a, h12b, h12c, h12d⟩ := swap_disjoint a₁ b₁ a₂ b₂ hab₁ hab₂ hcomm12 hne12
    have ht₁E : MSP.transv w₁ 1 ∈ S5.imSp a K := by
      rw [hEw]
      exact Subgroup.mem_sup_left (MSP.transv_mem_xPoint w₁ 1)
    have ht₂E : MSP.transv w₂ 1 ∈ S5.imSp a K := by
      rw [hEw]
      exact Subgroup.mem_sup_right (MSP.transv_mem_xPoint w₂ 1)
    obtain ⟨⟨k₁, hk₁M⟩, hk₁K, hk₁a⟩ := ht₁E
    obtain ⟨⟨k₂, hk₂M⟩, hk₂K, hk₂a⟩ := ht₂E
    have hk₁K' : k₁ ∈ K := Subgroup.mem_subgroupOf.1 hk₁K
    have hk₂K' : k₂ ∈ K := Subgroup.mem_subgroupOf.1 hk₂K
    have hk₁σ : (B5FinSp.theta c).symm (a ⟨k₁, hk₁M⟩) = Equiv.swap a₁ b₁ := by
      rw [hk₁a, ← hθ₁, MulEquiv.symm_apply_apply]
    have hk₂σ : (B5FinSp.theta c).symm (a ⟨k₂, hk₂M⟩) = Equiv.swap a₂ b₂ := by
      rw [hk₂a, ← hθ₂, MulEquiv.symm_apply_apply]
    obtain ⟨i₀, hi₀a₁, hi₀b₁, hi₀a₂, hi₀b₂⟩ := exists_ne_four a₁ b₁ a₂ b₂
    have hstab : (S5.imSp a K).map (B5FinSp.theta c).symm.toMonoidHom ≤
        MulAction.stabilizer (Equiv.Perm (Fin 6)) i₀ := by
      rw [hEw, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        rcases hE₁ g hg with h1 | h1
        · rw [h1, map_one]
          exact one_mem _
        · rw [MulAction.mem_stabilizer_iff, h1, MulEquiv.coe_toMonoidHom, ← hθ₁,
            MulEquiv.symm_apply_apply, Equiv.Perm.smul_def,
            Equiv.swap_apply_of_ne_of_ne hi₀a₁ hi₀b₁]
      · rintro _ ⟨g, hg, rfl⟩
        rcases hE₂ g hg with h1 | h1
        · rw [h1, map_one]
          exact one_mem _
        · rw [MulAction.mem_stabilizer_iff, h1, MulEquiv.coe_toMonoidHom, ← hθ₂,
            MulEquiv.symm_apply_apply, Equiv.Perm.smul_def,
            Equiv.swap_apply_of_ne_of_ne hi₀a₂ hi₀b₂]
    have hdi₀ : d i₀ ∈ Subgroup.centralizer (K : Set G) := hKd i₀ fun κ hκ => by
      have h1 := hstab ⟨a ⟨κ, hKM hκ⟩, ⟨⟨κ, hKM hκ⟩, Subgroup.mem_subgroupOf.2 hκ, rfl⟩, rfl⟩
      exact h1
    have hk₁d : k₁ * d i₀ = d i₀ * k₁ := Subgroup.mem_centralizer_iff.1 hdi₀ k₁ hk₁K'
    have hsw : ∀ (m : G) (hm : m ∈ M) (a' b' i : Fin 6), a' ≠ b' → i ≠ a' → i ≠ b' →
        (B5FinSp.theta c).symm (a ⟨m, hm⟩) = Equiv.swap a' b' → m * d i = d i * m :=
      fun m hm a' b' i hab' hia' hib' hma =>
        commute_of_swap h hd hC c hdX hconj hk₁M hab₁ hi₀a₁ hi₀b₁ hk₁σ hk₁d hm hab' hia' hib' hma
    have hk₁da : ¬ k₁ * d a₁ = d a₁ * k₁ := by
      intro hcomm
      have h1 := hconj k₁ hk₁M a₁
      rw [hk₁σ, Equiv.swap_apply_left, hcomm, mul_inv_cancel_right] at h1
      exact hdne a₁ b₁ hab₁ h1
    have hk₂da : ¬ k₂ * d a₂ = d a₂ * k₂ := by
      intro hcomm
      have h1 := hconj k₂ hk₂M a₂
      rw [hk₂σ, Equiv.swap_apply_left, hcomm, mul_inv_cancel_right] at h1
      exact hdne a₂ b₂ hab₂ h1
    have hk₁d₂ : k₁ * d a₂ = d a₂ * k₁ :=
      hsw k₁ hk₁M a₁ b₁ a₂ hab₁ (fun h' => h12a h'.symm) (fun h' => h12c h'.symm) hk₁σ
    have hk₂d₁ : k₂ * d a₁ = d a₁ * k₂ :=
      hsw k₂ hk₂M a₂ b₂ a₁ hab₂ h12a h12b hk₂σ
    have hdd : d a₁ * d a₂ = d a₂ * d a₁ := S5.commute_of_mem_Xq (hdX a₁).1 (hdX a₂).1
    have hd₁i : (d a₁)⁻¹ = d a₁ := by
      rw [inv_eq_iff_mul_eq_one, ← sq]
      exact S5Q2.sq_eq_one_of_mem_Xq (hdX a₁).1
    have hd₂i : (d a₂)⁻¹ = d a₂ := by
      rw [inv_eq_iff_mul_eq_one, ← sq]
      exact S5Q2.sq_eq_one_of_mem_Xq (hdX a₂).1
    have hn₁ : d a₁ ∉ Subgroup.centralizer (K : Set G) := fun hm =>
      hk₁da (Subgroup.mem_centralizer_iff.1 hm k₁ hk₁K')
    have hn₂ : d a₂ ∉ Subgroup.centralizer (K : Set G) := fun hm =>
      hk₂da (Subgroup.mem_centralizer_iff.1 hm k₂ hk₂K')
    have hn₁₂ : d a₁ * d a₂ ∉ Subgroup.centralizer (K : Set G) := by
      intro hm
      apply hk₁da
      have h1 : k₁ * (d a₁ * d a₂) = d a₁ * d a₂ * k₁ :=
        Subgroup.mem_centralizer_iff.1 hm k₁ hk₁K'
      calc k₁ * d a₁ = k₁ * (d a₁ * d a₂) * (d a₂)⁻¹ := by group
        _ = d a₁ * (d a₂ * k₁) * (d a₂)⁻¹ := by rw [h1]; group
        _ = d a₁ * (k₁ * d a₂) * (d a₂)⁻¹ := by rw [hk₁d₂]
        _ = d a₁ * k₁ := by group
    have hidx4 : ((Subgroup.centralizer (K : Set G)).subgroupOf (xFix h)).index = 4 := by
      rw [← hE4, ← hidxE]
      rfl
    obtain ⟨i, hi⟩ := exists_mem_of_index_eq hidx4
      ![1, ⟨d a₁, hdX a₁⟩, ⟨d a₂, hdX a₂⟩, ⟨d a₁ * d a₂, (xFix h).mul_mem (hdX a₁) (hdX a₂)⟩]
      (by
        intro i j hij
        rw [hmemH]
        have hsq : d a₂ * d a₂ = 1 := by rw [← sq]; exact S5Q2.sq_eq_one_of_mem_Xq (hdX a₂).1
        have e3 : d a₂ * (d a₁ * d a₂) = d a₁ := by
          rw [hdd, ← mul_assoc, hsq, one_mul]
        have e4 : d a₂ * d a₁ * d a₂ = d a₁ := by rw [mul_assoc, e3]
        fin_cases i <;> fin_cases j
        all_goals (try simp at hij ⊢)
        all_goals (try simp only [hd₁i, hd₂i])
        all_goals first
          | exact hn₁
          | exact hn₂
          | exact hn₁₂
          | (rw [← hdd]; exact hn₁₂)
          | (rw [e3]; exact hn₁)
          | (rw [e4]; exact hn₁)) ⟨u, huX⟩
    have hσ₁ := hswap_fix ((B5FinSp.theta c).symm (a ⟨y, hyM⟩)) hab₁ (by
      rw [← hk₁σ]; exact hσcomm hy hk₁K')
    have hσ₂ := hswap_fix ((B5FinSp.theta c).symm (a ⟨y, hyM⟩)) hab₂ (by
      rw [← hk₂σ]; exact hσcomm hy hk₂K')
    have hk₁₂M : k₁ * k₂ ∈ M := M.mul_mem hk₁M hk₂M
    have hk₁₂σ : (B5FinSp.theta c).symm (a ⟨k₁ * k₂, hk₁₂M⟩) =
        Equiv.swap a₁ b₁ * Equiv.swap a₂ b₂ := by
      have e : (⟨k₁ * k₂, hk₁₂M⟩ : ↥M) = ⟨k₁, hk₁M⟩ * ⟨k₂, hk₂M⟩ := rfl
      rw [e, map_mul, map_mul, hk₁σ, hk₂σ]
    obtain ⟨e, heK, hy₁⟩ : ∃ e ∈ K, ∃ hm : e⁻¹ * y ∈ M,
        (B5FinSp.theta c).symm (a ⟨e⁻¹ * y, hm⟩) a₁ = a₁ ∧
          (B5FinSp.theta c).symm (a ⟨e⁻¹ * y, hm⟩) a₂ = a₂ := by
      rcases hσ₁ with h1 | h1 <;> rcases hσ₂ with h2 | h2
      · refine ⟨1, one_mem _, by simpa using hyM, ?_⟩
        simp only [inv_one, one_mul]
        exact ⟨h1, h2⟩
      · refine ⟨k₂, hk₂K', M.mul_mem (M.inv_mem hk₂M) hyM, ?_⟩
        rw [hθinv hk₂M hyM, hk₂σ, Equiv.swap_inv]
        simp only [Equiv.Perm.mul_apply, h1, h2]
        constructor <;> simp [Equiv.swap_apply_def, h12a, h12b]
      · refine ⟨k₁, hk₁K', M.mul_mem (M.inv_mem hk₁M) hyM, ?_⟩
        rw [hθinv hk₁M hyM, hk₁σ, Equiv.swap_inv]
        simp only [Equiv.Perm.mul_apply, h1, h2]
        constructor <;> simp [Equiv.swap_apply_def, Ne.symm h12a, Ne.symm h12c]
      · refine ⟨k₁ * k₂, mul_mem hk₁K' hk₂K', M.mul_mem (M.inv_mem hk₁₂M) hyM, ?_⟩
        rw [hθinv hk₁₂M hyM, hk₁₂σ, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
        simp only [Equiv.Perm.mul_apply, h1, h2]
        constructor <;> simp [Equiv.swap_apply_def, h12a, h12b, Ne.symm h12b, Ne.symm h12d]
    obtain ⟨hm₁, hfa₁, hfa₂⟩ := hy₁
    have hc₁ := commute_of_fix h hd hC c hdX hsw hm₁ hfa₁
    have hc₂ := commute_of_fix h hd hC c hdX hsw hm₁ hfa₂
    have hyey : y = e * (e⁻¹ * y) := by group
    have hgen : ∀ {g : G}, g ∈ Xq M → g * (e⁻¹ * y) = (e⁻¹ * y) * g →
        ∀ {u' : G}, u' ∈ Xq M ⊓ Subgroup.centralizer (K : Set G) → ⁅g * u', y⁆ ∈ N := by
      intro g hg hgy u' hu'
      refine hP2 hg hu' hy ?_
      rw [hyey]
      exact hP1 hg heK hgy
    have hc₁₂ : d a₁ * d a₂ * (e⁻¹ * y) = (e⁻¹ * y) * (d a₁ * d a₂) := by
      rw [mul_assoc, ← hc₂, ← mul_assoc, ← hc₁, mul_assoc]
    fin_cases i
    · have hu' : u ∈ Subgroup.centralizer (K : Set G) := by simpa [hmemH] using hi
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator ⟨huX.1, hu'⟩ hy)
    · have hu' : (d a₁)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa [hmemH] using hi
      have e1 : u = d a₁ * ((d a₁)⁻¹ * u) := by group
      rw [e1]
      exact hgen (hdX a₁).1 hc₁.symm
        ⟨(Xq M).mul_mem ((Xq M).inv_mem (hdX a₁).1) huX.1, hu'⟩
    · have hu' : (d a₂)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa [hmemH] using hi
      have e1 : u = d a₂ * ((d a₂)⁻¹ * u) := by group
      rw [e1]
      exact hgen (hdX a₂).1 hc₂.symm
        ⟨(Xq M).mul_mem ((Xq M).inv_mem (hdX a₂).1) huX.1, hu'⟩
    · have hu' : (d a₁ * d a₂)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by
        simpa [hmemH] using hi
      have e1 : u = d a₁ * d a₂ * ((d a₁ * d a₂)⁻¹ * u) := by group
      rw [e1]
      exact hgen ((Xq M).mul_mem (hdX a₁).1 (hdX a₂).1) hc₁₂
        ⟨(Xq M).mul_mem ((Xq M).inv_mem ((Xq M).mul_mem (hdX a₁).1 (hdX a₂).1)) huX.1, hu'⟩
  ·
    have hyE : a ⟨y, hyM⟩ ∈ S5.imSp a K := by
      rw [hEl]
      intro v hv
      by_cases hv0 : v = 0
      · rw [hv0, Matrix.mulVec_zero]
      have htK : MSP.transv v 1 ∈ S5.imSp a K := by
        rw [hEl]
        exact MSP.xPoint_le_qLine hl ((Submodule.span_singleton_le_iff_mem v l).2 hv)
          (MSP.transv_mem_xPoint v 1)
      obtain ⟨⟨k, hkM⟩, hkK, hka⟩ := htK
      have hcomm := hYK y hy k (Subgroup.mem_subgroupOf.1 hkK)
      have h1 : a ⟨y, hyM⟩ * MSP.transv v 1 * (a ⟨y, hyM⟩)⁻¹ = MSP.transv v 1 := by
        rw [← hka, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcomm, mul_inv_cancel_right]
      rw [MSP.transv_conj] at h1
      exact (MSP.transv_eq_transv_iff hv0).1 h1
    obtain ⟨⟨e, heM⟩, heK, hea⟩ := hyE
    have heK' : e ∈ K := Subgroup.mem_subgroupOf.1 heK
    have hn : e⁻¹ * y ∈ M := M.mul_mem (M.inv_mem heM) hyM
    have hna : a ⟨e⁻¹ * y, hn⟩ = 1 := by
      have : (⟨e⁻¹ * y, hn⟩ : ↥M) = (⟨e, heM⟩)⁻¹ * ⟨y, hyM⟩ := rfl
      rw [this, map_mul, map_inv, hea, inv_mul_cancel]
    have hnu := commute_of_ker h hd hC hn hna huX
    have e1 : y = e * (e⁻¹ * y) := by group
    rw [e1]
    exact Subgroup.mem_sup_left (hP1 huX.1 heK' hnu.symm)

end Final

end CFSG.Quasithin.MS93.S5Q2.X52

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open S5Q2.X52

theorem s33X52_holds : S33X52 := by
  intro G _ _ M T L h F _ _ a hd hXL α' Y hS hYX _
  by_contra hne
  have hC := zq_le_centralizer_of_ne h hd hXL hne
  have : CharP F 2 := hd.charP
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hCH := h.centHyp
  obtain ⟨hc, hYT, -, hY⟩ := hS
  obtain ⟨g, hgα, hgβ, hμ, -⟩ := exists_conj_of_isCritical _ h20 hb hc
  set μ := g⁻¹ • baseA (puAmalgam h.le) with hμdef
  have hcμ : IsCritical _ (baseA (puAmalgam h.le)) μ := ms22_iii _ h20 hb hCH hμ
  have hgμ : g • μ = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hconj : ∀ H K : Subgroup (puAmalgam h.le).Universal,
      (H.map (MulAut.conj g).toMonoidHom).relIndex (K.map (MulAut.conj g).toMonoidHom) =
        H.relIndex K := fun H K =>
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  obtain ⟨hE2₁, hq₁, hE1₁, hidx₁, hcard₁⟩ := crit_image h hd hc
  obtain ⟨hE2₂, hq₂, hE1₂, hidx₂, hcard₂⟩ := crit_image h hd hcμ
  have e2 : (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex (XM _ μ) := by
    rw [← hconj (Qv _ (baseA _)) (XM _ μ), ← qv_smul, ← xm_smul, hgα, hgμ]
  have e3 : (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex (XM _ α') := by
    rw [← hconj (Qv _ μ) (XM _ (baseA _)), ← qv_smul, ← xm_smul, hgμ, hgα]
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨x, hx, hxN⟩ := exists_mem_xFix_not_mem h hXL hne
  obtain ⟨B, m₀, hB, hform⟩ := exists_cform_of_mem_xFix hd h nv hx hxN
  have r₁ := (card_le_card_range h nv (pre_le h.le (XM _ α')) hd hx hB hform hE2₁ hq₁ hE1₁).1
  have r₂ := (card_le_card_range h nv (pre_le h.le (XM _ μ)) hd hx hB hform hE2₂ hq₂ hE1₂).1
  have x₁ := card_range_le_relIndex_xFix h nv (pre_le h.le (XM (puAmalgam h.le) α'))
  have x₂ := card_range_le_relIndex_xFix h nv (pre_le h.le (XM (puAmalgam h.le) μ))
  have y₁ : (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) α') : Set G)).relIndex
      (xFix h) ≤ (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) α') : Set G)).relIndex
        (Xq M) := Subgroup.relIndex_le_of_le_right (xFix_le h) Subgroup.index_ne_zero_of_finite
  have y₂ : (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) μ) : Set G)).relIndex
      (xFix h) ≤ (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) μ) : Set G)).relIndex
        (Xq M) := Subgroup.relIndex_le_of_le_right (xFix_le h) Subgroup.index_ne_zero_of_finite
  have hidxE₂ : (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) μ) : Set G)).relIndex
      (xFix h) ≤ Nat.card (S5.imSp a (pre h.le (XM (puAmalgam h.le) μ))) := by omega
  have hidxμ : (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) μ) : Set G)).relIndex
      (Xq M) = (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) := by omega
  obtain ⟨hXs, -, -, -⟩ := crit_facts h hcμ
  have hXM : XM (puAmalgam h.le) μ ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  have eC : (Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) μ) : Set G)).relIndex (Xq M) =
      (Subgroup.centralizer (XM (puAmalgam h.le) μ : Set _)).relIndex
        (XM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.xm_baseA, h.normalCoreIn_eq,
      ← relIndex_centralizer_imM h.le (Xq_le M) (pre_le h.le _), imM_pre h.le hXM]
  have hfinX : Finite ↥(XM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.xm_baseA]
    exact finite_imM_of_finite h.le _
  have hAeq : XM (puAmalgam h.le) (baseA _) ⊓ Subgroup.centralizer (XM _ μ : Set _) =
      XM (puAmalgam h.le) (baseA _) ⊓ Qv _ μ := by
    refine le_antisymm ?_ (inf_le_inf_left _ (qv_le_centralizer_xm _ μ))
    have h1 : (XM (puAmalgam h.le) (baseA _) ⊓ Qv _ μ).relIndex
        (XM (puAmalgam h.le) (baseA _) ⊓ Subgroup.centralizer (XM _ μ : Set _)) *
        (XM (puAmalgam h.le) (baseA _) ⊓ Subgroup.centralizer (XM _ μ : Set _)).relIndex
          (XM (puAmalgam h.le) (baseA _)) =
        (XM (puAmalgam h.le) (baseA _) ⊓ Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) :=
      Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_left _ (qv_le_centralizer_xm _ μ))
        inf_le_left
    rw [inf_comm (XM _ (baseA _)) (Qv _ μ), Subgroup.inf_relIndex_right,
      inf_comm (XM _ (baseA _)) (Subgroup.centralizer _), Subgroup.inf_relIndex_right] at h1
    have h2 : (Subgroup.centralizer (XM (puAmalgam h.le) μ : Set _)).relIndex
        (XM (puAmalgam h.le) (baseA _)) = (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) := by
      rw [← eC, hidxμ]
    rw [h2] at h1
    have h3 : 0 < (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h4 := Subgroup.relIndex_eq_one.1 ((Nat.mul_eq_right h3.ne').1 h1)
    rw [inf_comm (XM _ (baseA _)) (Qv _ μ), inf_comm (XM _ (baseA _)) (Subgroup.centralizer _)]
    exact h4
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
  have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Y g).symm
  have hY'T : Y' ≤ imM h.le T := by
    rw [← puAmalgam.qv_baseB, ← map_conj_le_map_conj_iff g, ← hYY, ← qv_smul, hgβ]
    exact hYT
  have hY'X : Y' ≤ Subgroup.centralizer (XM (puAmalgam h.le) μ : Set _) := by
    rw [← map_conj_le_map_conj_iff g, ← hYY, ← PU.centralizer_map_mulEquiv, ← xm_smul, hgμ]
    exact hYX
  have hY'M : Y' ≤ imM h.le M := hY'T.trans (imM_mono h.le h.le)
  have hYK : ∀ y ∈ pre h.le Y', ∀ k ∈ pre h.le (XM (puAmalgam h.le) μ), y * k = k * y := by
    intro y hy k hk
    obtain ⟨my, hmy, rfl⟩ := (mem_pre_iff' h.le).1 hy
    obtain ⟨mk, hmk, rfl⟩ := (mem_pre_iff' h.le).1 hk
    have := Subgroup.mem_centralizer_iff.1 (hY'X hmy) _ hmk
    have e : my * mk = mk * my :=
      (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact this.symm)
    exact congrArg Subtype.val e
  have hM := commutator_le_of_central h hd hXL hne hC (pre_le h.le _) hE2₂ hq₂ hE1₂ hidxE₂
    (pre_le h.le Y') hYK
  have hcommM : ∀ {A B : Subgroup G}, A ≤ M → B ≤ M → ⁅A, B⁆ ≤ M := fun hA hB =>
    Subgroup.commutator_le.2 fun x hx y hy =>
      M.mul_mem (M.mul_mem (M.mul_mem (hA hx) (hB hy)) (M.inv_mem (hA hx))) (M.inv_mem (hB hy))
  have h1 : ⁅ZM (puAmalgam h.le) (baseA _), Y'⁆ ≤ ⁅XM (puAmalgam h.le) (baseA _), XM _ μ⁆ ⊔
      ⁅XM (puAmalgam h.le) (baseA _) ⊓ Qv _ μ, Y'⁆ := by
    have hpreT : pre h.le Y' ≤ T := pre_le_of_le_imM h hY'T
    rw [puAmalgam.zm_baseA, ← imM_pre h.le hY'M,
      ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _), commutator_Z0q_eq h hpreT,
      ← hAeq, puAmalgam.xm_baseA, h.normalCoreIn_eq, ← imM_pre h.le hXM,
      ← imM_inf_centralizer h.le (Xq M) (pre_le h.le _),
      ← imM_commutator h.le (Xq_le M) (pre_le h.le _),
      ← imM_commutator h.le (inf_le_left.trans (Xq_le M)) (pre_le h.le _),
      ← imM_sup h.le (hcommM (Xq_le M) (pre_le h.le _))
        (hcommM (inf_le_left.trans (Xq_le M)) (pre_le h.le _))]
    exact imM_mono h.le hM
  apply hY
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, ← hYY, ← zm_smul, ← xm_smul,
    ← xm_smul, ← qv_smul, hgα, hgμ] at hmap
  rw [Subgroup.commutator_comm (XM (puAmalgam h.le) α') (XM _ (baseA _))] at hmap
  exact hmap

end CFSG.Quasithin.MS93.S33
