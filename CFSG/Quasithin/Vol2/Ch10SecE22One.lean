module

public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10SecEL0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left [Finite G] (X K : Subgroup G) :
    X ≤ Subgroup.normalizer ((⁅X, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ X, ∀ x ∈ ⁅X, K⁆, h * x * h⁻¹ ∈ ⁅X, K⁆ := by
    intro h hh x hx
    have hle : ⁅X, K⁆ ≤ (⁅X, K⁆).comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : h * ⁅a, k⁆ * h⁻¹ = ⁅h * a, k⁆ * ⁅h, k⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (X.mul_mem hh ha) hk)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hh hk))
    have := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro h hh
  exact B6.mem_normalizer_of_forall_mem (key h hh) (fun x hx => by
    simpa using key h⁻¹ (X.inv_mem hh) x hx)

theorem mem_normalizer_sup_of_commutator_mem {J N : Subgroup G} {g : G}
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) (hgN : g ∈ Subgroup.normalizer (N : Set G))
    (hg : ∀ j ∈ J, g * j * g⁻¹ * j⁻¹ ∈ N) (hg' : ∀ j ∈ J, g⁻¹ * j * g * j⁻¹ ∈ N) :
    g ∈ Subgroup.normalizer ((J ⊔ N : Subgroup G) : Set G) := by
  have hcoe : (↑(J ⊔ N) : Set G) = (J : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right J N hJN
  have key : ∀ x ∈ Subgroup.normalizer (N : Set G), (∀ j ∈ J, x * j * x⁻¹ * j⁻¹ ∈ N) →
      ∀ y ∈ J ⊔ N, x * y * x⁻¹ ∈ J ⊔ N := by
    intro x hxN hx y hy
    have hy' : y ∈ (J : Set G) * (N : Set G) := by rw [← hcoe]; exact hy
    obtain ⟨j, hj, n, hn, rfl⟩ := Set.mem_mul.mp hy'
    have h1 : x * n * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hxN n).mp hn
    have h2 : j⁻¹ * (x * j * x⁻¹ * j⁻¹) * j ∈ N := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hJN (J.inv_mem hj)) _).mp (hx j hj)
      simpa [mul_assoc] using h3
    have e : x * (j * n) * x⁻¹ = j * ((j⁻¹ * (x * j * x⁻¹ * j⁻¹) * j) * (x * n * x⁻¹)) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
      (Subgroup.mem_sup_right (N.mul_mem h2 h1))
  exact B6.mem_normalizer_of_forall_mem (key g hgN hg) fun x hx => by
    simpa using key g⁻¹ (Subgroup.inv_mem _ hgN) (fun j hj => by simpa using hg' j hj) x hx

variable [Finite G] {T L I : Subgroup G}

theorem hyp318_fsuV (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨h1, h2, h3⟩ := h3228 G T L I hyp.fsu
  exact { inM := ⟨SecB.fsuM_isMaxTwoLocal h331 hyp, SecA.le_fsuM T L⟩
          nonempty := ⟨H, hH⟩
          perfect := eq_oTwoUpper_of_perfect (fsuL0_perfect h37 h38 hyp ht htn)
          le_M := SecA.fsuL0_le_fsuM T L
          normal := le_rfl
          unique := SecB.isUniqueM_L0T h331 hyp
          reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨h1, h2⟩
          centralizer := h3 }

theorem not_thompsonJ_le_of_commutator_ne_bot (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (hyp318_fsuV h37 h38 h331 h3228 hyp hH) with ⟨hJ, -⟩ | ⟨-, hZ, -⟩
  · exact fun h => hJ (le_inf (iSup₂_le fun _ hA => hA.1) h)
  · exfalso
    apply hZH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hZ H hH).trans inf_le_right

omit [Finite G] in
theorem commutator_le_of_le_normalizer {X J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (X : Set G)) : ⁅X, J⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx j hj
  have h1 : j * x⁻¹ * j⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hJ hj) _).mp (X.inv_mem hx)
  have h2 := X.mul_mem hx h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h2

end CFSG.Quasithin.Vol2.Ch10.SecE
