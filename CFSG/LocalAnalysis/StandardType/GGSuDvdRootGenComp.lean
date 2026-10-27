module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG

public section

namespace CFSG.StandardType.SuDvdRootGen

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.LineU CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'} {A : Subgroup (MulAut L')}

theorem permSU_swap_mem_blockSU (hK : UnitaryFieldData 2 n K) (i j : Fin d) :
    permSU hK (Equiv.swap i j) ∈
      TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)) := by
  rw [TableBUE.mem_blockSU, coe_permSU]
  exact TableBUE.isBlockOn_permGL_swap (S := ({i, j} : Finset (Fin d))) (by simp) (by simp)

private theorem gl_commute_of_diagonal_const {Z W : GL (Fin d) K} {c : K}
    (hZ : (Z : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) : Z * W = W * Z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hZ]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem commute_of_diagonal_const {Z W : ↥(unitarySU 2 n K d)} {c : K}
    (hZ : ((Z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    Z * W = W * Z := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul] using gl_commute_of_diagonal_const hZ

theorem blockSU_pair_map_le_ggHypCent (hK : UnitaryFieldData 2 n K) {i j : Fin d}
    (hcomm : ∀ a ∈ A, MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a =
        a * MulAut.conj (φ (permSU hK (Equiv.swap i j))) →
      ∃ t : Fin d → K, ActsDiagU φ a t ∧ t i = t j) :
    (TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ ≤
      ggHypCent A (φ (permSU hK (Equiv.swap i j))) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  simp only [ggHypCent, Subgroup.mem_iInf, mem_ggFix]
  intro a ha
  obtain ⟨haA, hcommA⟩ := ha
  obtain ⟨t, ht, htij⟩ := hcomm a haA hcommA
  have hne : ∀ k, t k ≠ 0 := fun k => ht.ne_zero k
  obtain ⟨D, hD, hDt, hact⟩ := ht
  let τ : Fin d → Kˣ := fun k => Units.mk0 (t k) (hne k)
  have hτ : t = fun k => ((τ k : Kˣ) : K) := rfl
  have hDτ : D = diagHom d τ := by
    apply Units.ext
    rw [hDt, coe_diagHom]
    exact congrArg (fun f : Fin d → K => diagonal f) hτ
  have hconst : ∀ a ∈ ({i, j} : Finset (Fin d)), ∀ b ∈ ({i, j} : Finset (Fin d)),
      τ a = τ b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact Units.ext htij
    · exact Units.ext htij.symm
    · rfl
  have hcommD : (D : GL (Fin d) K) * (x : GL (Fin d) K) = (x : GL (Fin d) K) * D := by
    rw [hDτ]
    exact TableBUE.diagHom_mul_comm_of_isBlockOn hconst (TableBUE.mem_blockSU.mp hx)
  have hconj : conjN D hD x = x := by
    apply Subtype.ext
    rw [coe_conjN]
    calc D * (x : GL (Fin d) K) * D⁻¹ = (x : GL (Fin d) K) * D * D⁻¹ := by
          rw [← hcommD]
      _ = x := by group
  rw [hact x, hconj]

private theorem exists_separating_diag (hK : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {i j : Fin d} :
    ∀ k ∉ ({i, j} : Finset (Fin d)), ∀ l, l ≠ k →
      ∃ σ : Fin d → Kˣ, diagHom d σ ∈ unitarySU 2 n K d ∧ σ i = σ j ∧
        (∀ x, σ x ^ p = 1) ∧ σ k ≠ σ l := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  obtain ⟨u, huo, -⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hK hp hpq
  have hup : u ^ p = 1 := huo ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    exact hp.ne_one huo.symm
  have huinv : u ≠ u⁻¹ := by
    intro he
    have h2 : u ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [he]
      exact mul_inv_cancel u
    have hdvd : p ∣ 2 := by
      have := orderOf_dvd_of_pow_eq_one h2
      rwa [huo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  intro k hk l hkl
  have hki' : k ≠ i := fun h' => hk (by rw [h']; simp)
  have hkj' : k ≠ j := fun h' => hk (by rw [h']; simp)
  have key : ∀ m : Fin d, m ≠ i → m ≠ j → m ≠ k →
      ∃ σ : Fin d → Kˣ, diagHom d σ ∈ unitarySU 2 n K d ∧ σ i = σ j ∧
        (∀ x, σ x ^ p = 1) ∧ σ k = u ∧ σ m = u⁻¹ ∧
        (∀ x, x ≠ k → x ≠ m → σ x = 1) := by
    intro m hmi hmj hmk
    let σ : Fin d → Kˣ := Pi.mulSingle k u * Pi.mulSingle m u⁻¹
    have hkm : k ≠ m := hmk.symm
    have hσk : σ k = u := by simp [σ, hkm]
    have hσm : σ m = u⁻¹ := by simp [σ, hkm.symm]
    have hσi : σ i = 1 := by simp [σ, hki'.symm, hmi.symm]
    have hσj : σ j = 1 := by simp [σ, hkj'.symm, hmj.symm]
    have hσother : ∀ x, x ≠ k → x ≠ m → σ x = 1 := by
      intro x hxk hxm
      simp [σ, hxk, hxm]
    have hσpow : ∀ x, σ x ^ p = 1 := by
      intro x
      by_cases hxk : x = k
      · rw [hxk, hσk, hup]
      · by_cases hxm : x = m
        · rw [hxm, hσm, inv_pow, hup, inv_one]
        · rw [hσother x hxk hxm, one_pow]
    have hprod : ∏ x, σ x = 1 := by
      simp only [σ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel u
    have hnorm : ∀ x, σ x ^ (2 ^ n + 1) = 1 := by
      intro x
      obtain ⟨c, hc⟩ := hpq
      rw [hc, pow_mul, hσpow x, one_pow]
    have hdmem : diagHom d σ ∈ unitarySU 2 n K d :=
      TableBUE.diagHom_mem_unitarySU hK hnorm hprod
    exact ⟨σ, hdmem, by rw [hσi, hσj], hσpow, hσk, hσm, hσother⟩
  by_cases hl : l ∈ ({i, j} : Finset (Fin d))
  · obtain ⟨m, hmi, hmj, hmk⟩ := exists_not_mem_three hd i j k
    obtain ⟨σ, hdmem, hσij, hσpow, hσk, -, hσother⟩ := key m hmi hmj hmk
    have hlm : l ≠ m := by
      intro h'
      have hmS : m ∈ ({i, j} : Finset (Fin d)) := h' ▸ hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
      rcases hmS with h | h
      · exact hmi h
      · exact hmj h
    refine ⟨σ, hdmem, hσij, hσpow, ?_⟩
    rw [hσk, hσother l hkl hlm]
    exact hu1
  · have hli : l ≠ i := fun h' => hl (by rw [h']; simp)
    have hlj : l ≠ j := fun h' => hl (by rw [h']; simp)
    obtain ⟨σ, hdmem, hσij, hσpow, hσk, hσl, -⟩ := key l hli hlj hkl
    refine ⟨σ, hdmem, hσij, hσpow, ?_⟩
    rw [hσk, hσl]
    exact huinv

theorem isComponentOf_blockSU_pair_ggHypCent (hK : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hsc : GGTorusSelfCent p A)
    {i j : Fin d} (hij : i ≠ j)
    (hcomm : ∀ a ∈ A, MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a =
        a * MulAut.conj (φ (permSU hK (Equiv.swap i j))) →
      ∃ t : Fin d → K, ActsDiagU φ a t ∧ t i = t j) :
    IsComponentOf ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ)
      (ggHypCent A (φ (permSU hK (Equiv.swap i j)))) := by
  classical
  let S : Finset (Fin d) := {i, j}
  let J : Subgroup L' := (TableBUE.blockSU (K := K) (n := n) S).map φ
  let H : Subgroup L' := ggHypCent A (φ (permSU hK (Equiv.swap i j)))
  let T : Set (Fin d → Kˣ) := {σ | diagHom d σ ∈ unitarySU 2 n K d ∧ σ i = σ j ∧
    ∀ k, σ k ^ p = 1}
  let C₀ : Subgroup ↥(unitarySU 2 n K d) :=
    { carrier := {y | ∀ σ ∈ T, (y : GL (Fin d) K) * diagHom d σ = diagHom d σ * y}
      one_mem' := by
        intro σ _
        simp
      mul_mem' {x y} hx hy := by
        intro σ hσ
        change ((x : GL (Fin d) K) * (y : GL (Fin d) K)) * diagHom d σ =
          diagHom d σ * ((x : GL (Fin d) K) * (y : GL (Fin d) K))
        calc ((x : GL (Fin d) K) * (y : GL (Fin d) K)) * diagHom d σ
            = (x : GL (Fin d) K) * ((y : GL (Fin d) K) * diagHom d σ) := by group
          _ = (x : GL (Fin d) K) * (diagHom d σ * (y : GL (Fin d) K)) := by rw [hy σ hσ]
          _ = ((x : GL (Fin d) K) * diagHom d σ) * (y : GL (Fin d) K) := by group
          _ = (diagHom d σ * (x : GL (Fin d) K)) * (y : GL (Fin d) K) := by rw [hx σ hσ]
          _ = diagHom d σ * ((x : GL (Fin d) K) * (y : GL (Fin d) K)) := by group
      inv_mem' {x} hx := by
        intro σ hσ
        have h := hx σ hσ
        have h2 : ((x : GL (Fin d) K))⁻¹ * diagHom d σ =
            diagHom d σ * ((x : GL (Fin d) K))⁻¹ := by
          calc ((x : GL (Fin d) K))⁻¹ * diagHom d σ
              = ((x : GL (Fin d) K))⁻¹ * diagHom d σ *
                  ((x : GL (Fin d) K) * ((x : GL (Fin d) K))⁻¹) := by group
            _ = ((x : GL (Fin d) K))⁻¹ *
                  (diagHom d σ * (x : GL (Fin d) K)) * ((x : GL (Fin d) K))⁻¹ := by group
            _ = ((x : GL (Fin d) K))⁻¹ *
                  ((x : GL (Fin d) K) * diagHom d σ) * ((x : GL (Fin d) K))⁻¹ := by rw [← h]
            _ = diagHom d σ * ((x : GL (Fin d) K))⁻¹ := by group
        simpa only [Subgroup.coe_inv] using h2 }
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
    intro g hg
    exact TableBUE.ker_projMk_le_center (by
      rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      exact (mem_scalars_subgroupOf_iff hK (by omega)).mpr (hφker g hg))
  have hJH : J ≤ H := by
    simpa only [J, H, S] using blockSU_pair_map_le_ggHypCent (φ := φ) (A := A) hK hcomm
  have hJC : TableBUE.blockSU (K := K) (n := n) S ≤ C₀ := by
    intro x hx σ hσ
    have hconst : ∀ a ∈ S, ∀ b ∈ S, σ a = σ b := by
      intro a ha b hb
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hσ.2.1
      · exact hσ.2.1.symm
      · rfl
    exact (TableBUE.diagHom_mul_comm_of_isBlockOn hconst
      (TableBUE.mem_blockSU.mp hx)).symm
  have hsep : ∀ k ∉ S, ∀ l, l ≠ k → ∃ σ ∈ T, σ k ≠ σ l := by
    intro k hk l hkl
    obtain ⟨σ, hdmem, hσij, hσpow, hne⟩ :=
      exists_separating_diag (i := i) (j := j) hK hn hp hpq hd k (by simpa only [S] using hk) l
        hkl
    exact ⟨σ, ⟨hdmem, hσij, hσpow⟩, hne⟩
  have hcommC : ∀ g ∈ C₀, ∀ g' ∈ C₀, g * g' * g⁻¹ * g'⁻¹ ∈
      TableBUE.blockSU (K := K) (n := n) S := by
    intro g hg g' hg'
    exact SuNsRootGen.commutator_mem_blockSU_of_family (K := K) (n := n) hsep hg hg'
  have hstep : ∀ (gt y : ↥(unitarySU 2 n K d)), φ gt ∈ H → y ∈ C₀ →
      gt * y * gt⁻¹ ∈ C₀ := by
    intro gt y hgt hy σ hσ
    change φ gt ∈ ggHypCent A (φ (permSU hK (Equiv.swap i j))) at hgt
    have hfix_gen : ∀ a : MulAut L', a ∈ A →
        MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a =
          a * MulAut.conj (φ (permSU hK (Equiv.swap i j))) → a (φ gt) = φ gt := by
      intro a haA hacomm
      have h := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgt a) ⟨haA, hacomm⟩
      simpa only [mem_ggFix] using h
    let E : ↥(unitarySU 2 n K d) := ⟨diagHom d σ, hσ.1⟩
    have hEgl : (E : GL (Fin d) K) = diagHom d σ := rfl
    have hEmat : ((E : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun k => ((σ k : Kˣ) : K)) := by
      rw [hEgl, coe_diagHom]
    have hu : ∀ k, ((σ k : Kˣ) : K) ^ p = 1 := fun k => by
      rw [← Units.val_pow_eq_pow_val, hσ.2.2 k, Units.val_one]
    have hmemA : MulAut.conj (φ E) ∈ A :=
      conj_mem_of_selfCent_U hsc hdiag hEmat hu
    have hcommA : MulAut.conj (φ (permSU hK (Equiv.swap i j))) * MulAut.conj (φ E) =
        MulAut.conj (φ E) * MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by
      have hactE : ActsDiagU φ (MulAut.conj (φ E)) (fun k => ((σ k : Kˣ) : K)) :=
        actsDiagU_conj hEmat
      have hconj := ActsDiagU.conj_perm (φ := φ) hK hactE (Equiv.swap i j)
      have hswapK : (fun k => ((σ ((Equiv.swap i j)⁻¹ k) : Kˣ) : K)) =
          (fun k => ((σ k : Kˣ) : K)) := by
        funext k
        rw [Equiv.swap_inv]
        by_cases hki : k = i
        · rw [hki, Equiv.swap_apply_left, hσ.2.1]
        · by_cases hkj : k = j
          · rw [hkj, Equiv.swap_apply_right, hσ.2.1]
          · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      have hconj' : ActsDiagU φ (MulAut.conj (φ (permSU hK (Equiv.swap i j))) *
          MulAut.conj (φ E) * (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹)
          (fun k => ((σ k : Kˣ) : K)) := by
        simpa only [hswapK] using hconj
      have huniq := ActsDiagU.unique hφs hconj' hactE
      calc MulAut.conj (φ (permSU hK (Equiv.swap i j))) * MulAut.conj (φ E)
          = (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * MulAut.conj (φ E) *
              (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹) *
            MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by group
        _ = MulAut.conj (φ E) * MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by
              rw [huniq]
    have hfix : MulAut.conj (φ E) (φ gt) = φ gt := hfix_gen _ hmemA hcommA
    have hφconj : φ (E * gt * E⁻¹) = φ gt := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using hfix
    have hkerX : φ (E * gt * E⁻¹ * gt⁻¹) = 1 := by
      have h1 : φ (E * gt * E⁻¹ * gt⁻¹) = φ (E * gt * E⁻¹) * φ gt⁻¹ :=
        map_mul φ (E * gt * E⁻¹) gt⁻¹
      rw [h1, hφconj, map_inv, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hφker (E * gt * E⁻¹ * gt⁻¹) hkerX
    let Z : ↥(unitarySU 2 n K d) := E * gt * E⁻¹ * gt⁻¹
    have hZmat : ((Z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun _ => c) := by
      simpa only [Z] using hc
    have hZgt : Z * gt = gt * Z := commute_of_diagonal_const hZmat
    have hZy : Z * y = y * Z := commute_of_diagonal_const hZmat
    have hEq1 : Z * gt = E * gt * E⁻¹ := by
      change (E * gt * E⁻¹ * gt⁻¹) * gt = E * gt * E⁻¹
      group
    have hEq2 : E * gt = Z * gt * E := by
      calc E * gt = (E * gt * E⁻¹) * E := by group
        _ = (Z * gt) * E := by rw [← hEq1]
    have hEq3 : gt * E = Z⁻¹ * E * gt := by
      have h := congrArg (fun x => Z⁻¹ * x) hEq2
      rw [show Z⁻¹ * (E * gt) = Z⁻¹ * E * gt by group,
        show Z⁻¹ * (Z * gt * E) = gt * E by group] at h
      exact h.symm
    have hEq4 : gt * E * gt⁻¹ = Z⁻¹ * E := by
      rw [hEq3]
      group
    have hyE : y * E = E * y := by
      apply Subtype.ext
      have h := hy σ hσ
      simpa only [Subgroup.coe_mul, hEgl] using h
    have hZgtinv : Z * gt⁻¹ = gt⁻¹ * Z := by
      calc Z * gt⁻¹ = (gt⁻¹ * gt) * Z * gt⁻¹ := by group
        _ = gt⁻¹ * (gt * Z) * gt⁻¹ := by group
        _ = gt⁻¹ * (Z * gt) * gt⁻¹ := by rw [← hZgt]
        _ = gt⁻¹ * Z := by group
    have hZwy : Z * (gt * y * gt⁻¹) = (gt * y * gt⁻¹) * Z := by
      calc Z * (gt * y * gt⁻¹) = (Z * gt) * y * gt⁻¹ := by group
        _ = (gt * Z) * y * gt⁻¹ := by rw [hZgt]
        _ = gt * (Z * y) * gt⁻¹ := by group
        _ = gt * (y * Z) * gt⁻¹ := by rw [hZy]
        _ = (gt * y * gt⁻¹) * Z := by
              have h : gt * (y * Z) * gt⁻¹ = gt * y * (Z * gt⁻¹) := by group
              rw [h, hZgtinv]
              group
    have hwE : E * (gt * y * gt⁻¹) = (gt * y * gt⁻¹) * E := by
      calc E * (gt * y * gt⁻¹) = (E * gt) * y * gt⁻¹ := by group
        _ = (Z * gt * E) * y * gt⁻¹ := by rw [hEq2]
        _ = Z * gt * (E * y) * gt⁻¹ := by group
        _ = Z * gt * (y * E) * gt⁻¹ := by rw [← hyE]
        _ = Z * (gt * y * gt⁻¹) * (gt * E * gt⁻¹) := by group
        _ = Z * (gt * y * gt⁻¹) * (Z⁻¹ * E) := by rw [hEq4]
        _ = (gt * y * gt⁻¹) * E := by
              rw [hZwy]
              group
    have hwE' : ((gt * y * gt⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) *
        diagHom d σ = diagHom d σ *
          ((gt * y * gt⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
      have h := congrArg (fun z : ↥(unitarySU 2 n K d) => (z : GL (Fin d) K)) hwE
      simpa only [Subgroup.coe_mul, hEgl] using h.symm
    exact hwE'
  have hHnormC : H ≤ Subgroup.normalizer ((C₀.map φ : Subgroup L') : Set L') := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hyC, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨gt, rfl⟩ := hφs g
      refine Subgroup.mem_map.mpr ⟨gt * y * gt⁻¹, hstep gt y hg hyC, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hx
      obtain ⟨y, hyC, hyeq⟩ := Subgroup.mem_map.mp hx
      obtain ⟨gt, rfl⟩ := hφs g
      refine Subgroup.mem_map.mpr ⟨gt⁻¹ * y * gt, hstep gt⁻¹ y ?_ hyC, ?_⟩
      · simpa only [map_inv] using H.inv_mem hg
      · rw [map_mul, map_mul, map_inv, hyeq]
        group
  have hq : CFSG.Assembly.IsQuasisimple J :=
    SURepair.isQuasisimple_map_blockSU_of_two_le (f := n) (n := d) hK hn hker
      (S := S) (by rw [show S = ({i, j} : Finset (Fin d)) from rfl, Finset.card_pair hij])
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hJeq : J = ⁅C₀.map φ, C₀.map φ⁆ := by
    apply le_antisymm
    · rw [← hJperf]
      exact Subgroup.commutator_mono (Subgroup.map_mono hJC) (Subgroup.map_mono hJC)
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hb
      rw [← map_commutatorElement]
      exact Subgroup.mem_map_of_mem φ (by
        simpa only [commutatorElement_def] using hcommC g hg g' hg')
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set L') := by
    rw [hJeq]
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_commutator]
    have hC : Subgroup.map (↑(MulAut.conj g) : L' →* L') (Subgroup.map φ C₀) =
        Subgroup.map φ C₀ := by
      simpa only using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnormC hg)
    rw [hC]
  have hnorm : (J.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr hHnormJ
  exact ⟨hJH, IsSubnormal.step hJH hnorm (IsSubnormal.refl H), hq⟩

theorem dvd_card_blockSU_pair_map (hK : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {i j : Fin d} (hij : i ≠ j) :
    p ∣ Nat.card ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ) := by
  refine SuNsRootGen.dvd_card_blockSU_pair (K := K) (n := n) (d := d) (p := p) hK hp hpq hd
    (φ := φ) ?_ hij
  intro g hg
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  exact (mem_scalars_subgroupOf_iff hK (by omega)).mpr (hφker g hg)

end CFSG.StandardType.SuDvdRootGen

end
