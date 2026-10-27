module

public import CFSG.RankThree.PartTwo.Sec21.Item226Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item229Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions IsThreeFourPlusTranspositions)

variable {G : Type} [Group G]

@[expose] def transp4 : Finset (Equiv.Perm (Fin 4)) :=
  {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 1 2, Equiv.swap 1 3,
    Equiv.swap 2 3}

@[expose] def dtransp4 : Finset (Equiv.Perm (Fin 4)) :=
  {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

theorem perm_four_involution : ∀ σ : Equiv.Perm (Fin 4), σ * σ = 1 → σ ≠ 1 →
    σ ∈ transp4 ∨ σ ∈ dtransp4 := by
  decide +kernel

theorem perm_four_dtransp_class : ∀ σ ∈ dtransp4, ∀ τ ∈ dtransp4,
    ∃ g : Equiv.Perm (Fin 4), g * σ * g⁻¹ = τ := by
  decide +kernel

theorem perm_four_transp_dtransp : ∀ σ ∈ transp4, ∀ τ ∈ dtransp4,
    ∃ τ' ∈ dtransp4, (σ * τ') ^ 2 ≠ 1 ∧ (σ * τ') ^ 3 ≠ 1 := by
  decide +kernel

theorem perm_four_transp_class : ∀ σ ∈ transp4, ∀ τ ∈ transp4,
    ∃ g : Equiv.Perm (Fin 4), g * σ * g⁻¹ = τ := by
  decide +kernel

theorem perm_four_dtransp_closed : ∀ σ ∈ insert 1 dtransp4, ∀ τ ∈ insert 1 dtransp4,
    σ * τ ∈ insert 1 dtransp4 := by
  decide +kernel

theorem false_of_orderOf_le_three {X : Type*} [Group X] [Finite X] {x : X} (hle : orderOf x ≤ 3)
    (h2 : x ^ 2 ≠ 1) (h3 : x ^ 3 ≠ 1) : False := by
  have hpos := orderOf_pos x
  have hpow := pow_orderOf_eq_one x
  interval_cases h : orderOf x
  · exact h2 (by rw [sq, pow_one] at *; rw [hpow, one_mul])
  · exact h2 hpow
  · exact h3 hpow

theorem perm_four_single_class {X : Set (Equiv.Perm (Fin 4))}
    (hinv : ∀ g : Equiv.Perm (Fin 4), ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, x * x = 1 ∧ x ≠ 1) (h3 : ∀ x ∈ X, ∀ y ∈ X, orderOf (x * y) ≤ 3)
    (hgen : Subgroup.closure X = ⊤) : ∀ x ∈ X, ∀ y ∈ X, ∃ g, g * x * g⁻¹ = y := by
  have hsub : ∀ x ∈ X, x ∈ transp4 := by
    intro x hx
    rcases perm_four_involution x (h2 x hx).1 (h2 x hx).2 with ht | hd
    · exact ht
    · exfalso
      have hV : ∀ τ ∈ dtransp4, τ ∈ X := fun τ hτ => by
        obtain ⟨g, rfl⟩ := perm_four_dtransp_class x hd τ hτ
        exact hinv g x hx
      by_cases hT : ∃ σ ∈ X, σ ∈ transp4
      · obtain ⟨σ, hσ, hσT⟩ := hT
        obtain ⟨τ', hτ', h2', h3'⟩ := perm_four_transp_dtransp σ hσT x hd
        exact false_of_orderOf_le_three (h3 σ hσ τ' (hV τ' hτ')) h2' h3'
      · push Not at hT
        let K : Subgroup (Equiv.Perm (Fin 4)) :=
          { carrier := ↑(insert 1 dtransp4)
            mul_mem' := fun ha hb => perm_four_dtransp_closed _ ha _ hb
            one_mem' := Finset.mem_insert_self _ _
            inv_mem' := fun {a} ha => by
              revert a
              decide +kernel }
        have hXK : Subgroup.closure X ≤ K := by
          rw [Subgroup.closure_le]
          intro y hy
          rcases perm_four_involution y (h2 y hy).1 (h2 y hy).2 with ht | hd'
          · exact (hT y hy ht).elim
          · exact Finset.mem_insert_of_mem hd'
        have h01 : Equiv.swap (0 : Fin 4) 1 ∈ K := hXK (hgen ▸ Subgroup.mem_top _)
        have h01' : Equiv.swap (0 : Fin 4) 1 ∈ insert 1 dtransp4 := h01
        revert h01'
        decide +kernel
  intro x hx y hy
  exact perm_four_transp_class x (hsub x hx) y (hsub y hy)

@[expose] def transp5 : Finset (Equiv.Perm (Fin 5)) :=
  {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 0 4, Equiv.swap 1 2,
    Equiv.swap 1 3, Equiv.swap 1 4, Equiv.swap 2 3, Equiv.swap 2 4, Equiv.swap 3 4}

@[expose] def dtransp5 : Finset (Equiv.Perm (Fin 5)) :=
  {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 4,
    Equiv.swap 0 1 * Equiv.swap 3 4, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 1 4, Equiv.swap 0 2 * Equiv.swap 3 4,
    Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.swap 0 3 * Equiv.swap 1 4,
    Equiv.swap 0 3 * Equiv.swap 2 4, Equiv.swap 0 4 * Equiv.swap 1 2,
    Equiv.swap 0 4 * Equiv.swap 1 3, Equiv.swap 0 4 * Equiv.swap 2 3,
    Equiv.swap 1 2 * Equiv.swap 3 4, Equiv.swap 1 3 * Equiv.swap 2 4,
    Equiv.swap 1 4 * Equiv.swap 2 3}

theorem perm_five_involution : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    σ ∈ transp5 ∨ σ ∈ dtransp5 := by
  decide +kernel

theorem perm_five_dtransp_bad : ∀ σ ∈ dtransp5, ∃ g : Equiv.Perm (Fin 5),
    (σ * (g * σ * g⁻¹)) ^ 2 ≠ 1 ∧ (σ * (g * σ * g⁻¹)) ^ 3 ≠ 1 := by
  decide +kernel

theorem perm_five_transp_class : ∀ σ ∈ transp5, ∃ g : Equiv.Perm (Fin 5),
    g * Equiv.swap 0 1 * g⁻¹ = σ := by
  decide +kernel

theorem perm_five_eq_transp {X : Set (Equiv.Perm (Fin 5))}
    (hinv : ∀ g : Equiv.Perm (Fin 5), ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, x * x = 1 ∧ x ≠ 1) (h3 : ∀ x ∈ X, ∀ y ∈ X, orderOf (x * y) ≤ 3)
    (hne : X.Nonempty) : X = ↑transp5 := by
  have hsub : ∀ x ∈ X, x ∈ transp5 := by
    intro x hx
    rcases perm_five_involution x (h2 x hx).1 (h2 x hx).2 with ht | hd
    · exact ht
    · obtain ⟨g, h2', h3'⟩ := perm_five_dtransp_bad x hd
      exact (false_of_orderOf_le_three (h3 x hx _ (hinv g x hx)) h2' h3').elim
  obtain ⟨x₀, hx₀⟩ := hne
  ext σ
  refine ⟨fun h => hsub σ h, fun h => ?_⟩
  obtain ⟨g, hg⟩ := perm_five_transp_class _ (hsub x₀ hx₀)
  obtain ⟨g', hg'⟩ := perm_five_transp_class σ h
  have : σ = (g' * g⁻¹) * x₀ * (g' * g⁻¹)⁻¹ := by
    rw [← hg', ← hg]
    group
  rw [this]
  exact hinv _ x₀ hx₀

theorem swap_castSucc_succ_mem_transp5 :
    ∀ i : Fin 4, Equiv.swap (Fin.castSucc i) (Fin.succ i) ∈ transp5 := by
  decide +kernel

theorem swap_castSucc_succ_zero :
    (Equiv.swap (Fin.castSucc (0 : Fin 4)) (Fin.succ 0) : Equiv.Perm (Fin 5)) =
      Equiv.swap 0 1 := by
  decide +kernel

theorem swap_castSucc_succ_commute : ∀ i j : Fin 4, i.val + 1 < j.val →
    (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 5)) *
        Equiv.swap (Fin.castSucc j) (Fin.succ j) =
      Equiv.swap (Fin.castSucc j) (Fin.succ j) * Equiv.swap (Fin.castSucc i) (Fin.succ i) := by
  decide +kernel

theorem swap_castSucc_succ_not_commute : ∀ i j : Fin 4, i.val + 1 = j.val →
    (Equiv.swap (Fin.castSucc j) (Fin.succ j) : Equiv.Perm (Fin 5)) *
        Equiv.swap (Fin.castSucc i) (Fin.succ i) ≠
      Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j) := by
  decide +kernel

theorem swap_castSucc_succ_injective : ∀ i j : Fin 4,
    (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 5)) =
      Equiv.swap (Fin.castSucc j) (Fin.succ j) → i = j := by
  decide +kernel

theorem closure_swap_castSucc_succ :
    Subgroup.closure (Set.range fun i : Fin 4 =>
      (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 5))) = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 4 =>
      (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 5))) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact (Submonoid.closure_le.mpr Subgroup.subset_closure :
    Submonoid.closure _ ≤ (Subgroup.closure _).toSubmonoid) hσ

theorem perm_three_involutions : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 →
    a * b ≠ b * a → (a * b) ^ 3 = 1 ∧ a * b ≠ 1 := by
  decide

theorem orderOf_mul_eq_three_of_closure_perm {X : Type*} [Group X] {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y ≠ y * x)
    (e : Subgroup.closure ({x, y} : Set X) ≃* Equiv.Perm (Fin 3)) : orderOf (x * y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxm : x ∈ Subgroup.closure ({x, y} : Set X) := Subgroup.subset_closure (by simp)
  have hym : y ∈ Subgroup.closure ({x, y} : Set X) := Subgroup.subset_closure (by simp)
  have hx' : e ⟨x, hxm⟩ * e ⟨x, hxm⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext hx)
  have hy' : e ⟨y, hym⟩ * e ⟨y, hym⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext hy)
  have hxy' : e ⟨x, hxm⟩ * e ⟨y, hym⟩ ≠ e ⟨y, hym⟩ * e ⟨x, hxm⟩ := by
    intro h
    apply hxy
    have h' : (⟨x, hxm⟩ * ⟨y, hym⟩ : Subgroup.closure ({x, y} : Set X)) = ⟨y, hym⟩ * ⟨x, hxm⟩ :=
      e.injective (by rw [map_mul, map_mul]; exact h)
    exact congrArg Subtype.val h'
  obtain ⟨h3, h1⟩ := perm_three_involutions _ _ hx' hy' hxy'
  have hord : orderOf (e ⟨x, hxm⟩ * e ⟨y, hym⟩) = 3 := orderOf_eq_prime h3 h1
  rw [← map_mul, MulEquiv.orderOf_eq] at hord
  rw [← hord, ← Subgroup.orderOf_coe]
  rfl

theorem single_class_of_perm_four {X : Type*} [Group X] {H : Subgroup X}
    (e : H ≃* Equiv.Perm (Fin 4)) {D : Set X}
    (hinv : ∀ h ∈ H, ∀ x ∈ D, h * x * h⁻¹ ∈ D) (h2 : ∀ x ∈ D, x * x = 1 ∧ x ≠ 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ≤ 3)
    (hgen : H = Subgroup.closure ((H : Set X) ∩ D)) :
    ∀ x ∈ (H : Set X) ∩ D, ∀ y ∈ (H : Set X) ∩ D, ∃ h ∈ H, h * x * h⁻¹ = y := by
  set S : Set H := {x | (x : X) ∈ D} with hS
  have hSgen : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map H.subtype = Subgroup.closure ((H : Set X) ∩ D) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxH, hxD⟩
        exact ⟨⟨x, hxH⟩, hxD, rfl⟩
    rw [← hgen] at hmap
    rw [eq_top_iff]
    intro y _
    have : (y : X) ∈ (Subgroup.closure S).map H.subtype := by
      rw [hmap]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [show y = z from Subtype.ext hzy.symm]
  have key := perm_four_single_class (X := e '' S)
    (by
      rintro g _ ⟨s, hs, rfl⟩
      refine ⟨e.symm g * s * (e.symm g)⁻¹, ?_, ?_⟩
      · exact hinv _ (e.symm g).2 _ hs
      · simp)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, fun h => (h2 _ hs).2 ?_⟩
      · rw [← map_mul, ← map_one e]
        exact congrArg e (Subtype.ext (h2 _ hs).1)
      · rw [MulEquiv.map_eq_one_iff] at h
        rw [h, OneMemClass.coe_one])
    (by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      rw [← map_mul, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact h3 _ hs _ hs')
    (by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, hSgen,
        Subgroup.map_top_of_surjective _ e.surjective])
  rintro x ⟨hxH, hxD⟩ y ⟨hyH, hyD⟩
  obtain ⟨g, hg⟩ := key _ ⟨⟨x, hxH⟩, hxD, rfl⟩ _ ⟨⟨y, hyH⟩, hyD, rfl⟩
  refine ⟨(e.symm g : X), (e.symm g).2, ?_⟩
  have : e.symm g * ⟨x, hxH⟩ * (e.symm g)⁻¹ = ⟨y, hyH⟩ := e.injective (by simp [hg])
  exact congrArg Subtype.val this

theorem mem_normalizer_of_map_conj_eq_self {K : Subgroup G} {g : G}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hx
    simpa [mul_assoc] using hx

theorem isPerfect_iSup {ι : Type*} (K : ι → Subgroup G) (h : ∀ i, Group.IsPerfect (K i)) :
    Group.IsPerfect (⨆ i, K i : Subgroup G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (iSup_le fun i => ?_)
  · rw [commutatorElement_def]
    exact (⨆ i, K i).mul_mem ((⨆ i, K i).mul_mem ((⨆ i, K i).mul_mem ha hb)
      ((⨆ i, K i).inv_mem ha)) ((⨆ i, K i).inv_mem hb)
  · calc K i = ⁅K i, K i⁆ := (Subgroup.isPerfect_iff.mp (h i)).symm
      _ ≤ ⁅⨆ i, K i, ⨆ i, K i⁆ := Subgroup.commutator_mono (le_iSup K i) (le_iSup K i)

theorem exists_case_five [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) :
    ∃ φ₀ ∈ starOf A L, φ₀ ∈ dStar A ∧ ∃ n : ℕ, 1 < n ∧ Odd n ∧
      Nonempty (L ≃* projSU 4 2 n) ∧ Nonempty (kOf A φ₀ ≃* projSL 2 (GaloisField 2 n)) ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨-, ⟨φ₀, hφ₀L, hφ₀D⟩, hcase⟩ := h222 G A E U c L hpair
  refine ⟨φ₀, hφ₀L, hφ₀D, ?_⟩
  rcases hcase φ₀ hφ₀L hφ₀D with ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨-, h⟩
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · exact h

theorem s3_of_item223 [Finite G] (h223 : Item223) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {n : ℕ}
    (eL : L ≃* projSU 4 2 n) :
    ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)) :=
  fun φ hφ ψ hψ hne => ((h223 G A E U c L hpair hA81 n ⟨eL⟩ φ hφ ψ hψ).2.2 hne).2

theorem s3_of_item223Print [Finite G] (hP : Item223Print) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) :
    ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)) :=
  fun φ hφ ψ hψ hne => ((hP G A E U c L hpair hA81 φ hφ ψ hψ).2.2 hne).2

theorem orderOf_mul_le_three_of_s3 {A : Subgroup G}
    (hS3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) : orderOf (φ * ψ) ≤ 3 := by
  have hφ2 := mul_self_of_mem_dStar hφ
  have hψ2 := mul_self_of_mem_dStar hψ
  by_cases hc : φ * ψ = ψ * φ
  · have h2 : (φ * ψ) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc ψ, ← hc, mul_assoc, hψ2, mul_one, hφ2]
    exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · obtain ⟨e⟩ := hS3 φ hφ ψ hψ (fun h => hc h.symm)
    exact (orderOf_mul_eq_three_of_closure_perm hφ2 hψ2 hc e).le

theorem orderOf_mul_le_three_of_four [Finite G] (h223 : Item223) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {n : ℕ}
    (eL : L ≃* projSU 4 2 n) {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) :
    orderOf (φ * ψ) ≤ 3 :=
  orderOf_mul_le_three_of_s3 (s3_of_item223 h223 hpair hA81 eL) hφ hψ

theorem isThreeTranspositions_dStarIn_of_s3 [Finite G] {A : Subgroup G}
    (hS3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3))) :
    IsThreeTranspositions (dStarIn A) := by
  have hord : ∀ x ∈ dStar A, ∀ y ∈ dStar A, orderOf (x * y) ≤ 3 :=
    fun x hx y hy => orderOf_mul_le_three_of_s3 hS3 hx hy
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g x hx
    exact conj_mem_dStar_of_mem_wStar (closure_dStar_le_wStar A g.2) hx
  · intro x hx
    rw [← Subgroup.orderOf_coe]
    exact hx.1.1
  · exact Subgroup.closure_closure_coe_preimage
  · intro x hx y hy
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact (hord _ hx _ hy).trans (by norm_num)
  · intro x hx y hy h4
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4
    have := hord _ hx _ hy
    omega
  · intro x hx y hy
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hord _ hx _ hy

theorem isThreeTranspositions_dStarIn_of_four [Finite G] (h223 : Item223) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {n : ℕ}
    (eL : L ≃* projSU 4 2 n) : IsThreeTranspositions (dStarIn A) :=
  isThreeTranspositions_dStarIn_of_s3 (s3_of_item223 h223 hpair hA81 eL)

theorem conj_mem_closure_dStar [Finite G] {A : Subgroup G} {w : MulAut A} (hw : w ∈ wStar A)
    {x : MulAut A} (hx : x ∈ Subgroup.closure (dStar A)) :
    w * x * w⁻¹ ∈ Subgroup.closure (dStar A) := by
  have hle : Subgroup.closure (dStar A) ≤
      (Subgroup.closure (dStar A)).comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro d hd
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure (conj_mem_dStar_of_mem_wStar hw hd)
  exact hle hx

theorem fixed_dStar_eq_one [Finite G] (h2130 : Item2130) (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) {a : A} (ha : ∀ φ ∈ dStar A, φ a = a) : a = 1 := by
  set C : Subgroup A := ⨅ φ ∈ dStar A, fixedSubgroupOf φ with hCdef
  have hmemC : ∀ b : A, b ∈ C ↔ ∀ φ ∈ dStar A, φ b = b := by
    intro b
    simp only [hCdef, Subgroup.mem_iInf, mem_fixedSubgroupOf]
  have hle : ∀ ψ ∈ wStar A, C.map ψ.toMonoidHom ≤ C := by
    rintro ψ hψ _ ⟨b, hb, rfl⟩
    have hb' := (hmemC b).mp hb
    refine (hmemC _).mpr fun φ hφ => ?_
    have hφ' : ψ⁻¹ * φ * ψ⁻¹⁻¹ ∈ dStar A :=
      conj_mem_dStar_of_mem_wStar ((wStar A).inv_mem hψ) hφ
    have h := congrArg ψ (hb' _ hφ')
    simp only [inv_inv, MulAut.mul_apply] at h
    simpa using h
  have hC : ∀ ψ ∈ wStar A, C.map ψ.toMonoidHom = C := fun ψ hψ =>
    Subgroup.eq_of_le_of_card_ge (hle ψ hψ)
      (le_of_eq (Subgroup.card_map_of_injective ψ.injective).symm)
  rcases h2130 G A E U c L hpair C hC with hbot | htop
  · have haC : a ∈ C := (hmemC a).mpr ha
    rw [hbot] at haC
    exact (Subgroup.mem_bot).mp haC
  · exfalso
    obtain ⟨-, ⟨φ, -, hφ⟩, -⟩ := h222 G A E U c L hpair
    have hφ1 : φ = 1 := MulEquiv.ext fun b => (hmemC b).mp (htop ▸ Subgroup.mem_top b) φ hφ
    have h2 := hφ.1.1
    rw [hφ1, orderOf_one] at h2
    norm_num at h2

theorem transitive_dStar_of_s3 [Finite G] (h2115 : Item2115) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    (hS3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))
    (hC : ∀ d ∈ dStar A, (∀ x ∈ starOf A L, x * d = d * x) →
      (commOf d).map A.subtype = Subgroup.zpowers c ∧
        ∀ d' ∈ dStar A, (∀ x ∈ starOf A L, x * d' = d' * x) → d' = d) :
    ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ := by
  obtain ⟨φ₀, hφ₀L, hφ₀D, -, -, -, -, -, ⟨eS⟩⟩ := exists_case_five h222 hpair hA81
  have hD3 := isThreeTranspositions_dStarIn_of_s3 hS3
  have hgen := (h222 G A E U c L hpair).1
  set Z := Subgroup.closure (dStar A) with hZ
  have hLZ : starOf A L ≤ Z := by
    rw [hgen]
    exact Subgroup.closure_mono Set.inter_subset_right
  have hcl := single_class_of_perm_four eS
    (fun h hh x hx => conj_mem_dStar_of_mem_wStar (starOf_le_wStar A L hh) hx)
    (fun x hx => ⟨mul_self_of_mem_dStar hx, fun h1 => by
      have h := hx.1.1
      rw [h1, orderOf_one] at h
      norm_num at h⟩)
    (fun x hx y hy => orderOf_mul_le_three_of_s3 hS3 hx hy) hgen
  set t₀ : Z := ⟨φ₀, Subgroup.subset_closure hφ₀D⟩ with ht₀
  set O : Set Z := {x | x ∈ dStarIn A ∧ ∃ g : Z, g * t₀ * g⁻¹ = x} with hO
  set B : Set Z := {x | x ∈ dStarIn A ∧ x ∉ O} with hB
  have hOB : dStarIn A = O ∪ B := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ O
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint O B := Set.disjoint_left.mpr fun x hxO hxB => hxB.2 hxO
  have hOinv : ∀ g : Z, ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
    rintro g x ⟨hx, h, rfl⟩
    exact ⟨hD3.1.1 g _ hx, g * h, by group⟩
  have h71 := Sec7.rank3II_7_1 hD3 hOB hdisj hOinv
  have hcomm : ∀ x ∈ B, ∀ y ∈ starOf A L, y * (x : MulAut A) = (x : MulAut A) * y := by
    intro x hx
    have hle : starOf A L ≤ Subgroup.centralizer {(x : MulAut A)} := by
      rw [hgen, Subgroup.closure_le]
      intro s hs
      obtain ⟨h, hhL, hh⟩ := hcl φ₀ ⟨hφ₀L, hφ₀D⟩ s hs
      have hsO : (⟨s, Subgroup.subset_closure hs.2⟩ : Z) ∈ O :=
        ⟨hs.2, ⟨h, hLZ hhL⟩, Subtype.ext hh⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (h71 _ hsO x hx)
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hBe : ∀ x ∈ dStarIn A, x ∈ O := by
    by_contra hne
    push Not at hne
    obtain ⟨b, hbD, hbO⟩ := hne
    have hbB : b ∈ B := ⟨hbD, hbO⟩
    obtain ⟨hcb, huniq⟩ := hC b hbD (hcomm b hbB)
    have hbD' : ∀ x ∈ dStar A, x * (b : MulAut A) = (b : MulAut A) * x := by
      intro x hx
      have hxZ : x ∈ Z := Subgroup.subset_closure hx
      by_cases hxO : (⟨x, hxZ⟩ : Z) ∈ O
      · exact congrArg Subtype.val (h71 _ hxO b hbB)
      · rw [huniq x hx (hcomm ⟨x, hxZ⟩ ⟨hx, hxO⟩)]
    have hbZ : Z ≤ Subgroup.centralizer {(b : MulAut A)} := by
      rw [hZ, Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hbD' x hx
    have hbW : ∀ w ∈ wStar A, w * (b : MulAut A) * w⁻¹ = b := by
      intro w hw
      refine huniq _ (conj_mem_dStar_of_mem_wStar hw hbD) fun x hx => ?_
      have hx' : w⁻¹ * x * w⁻¹⁻¹ ∈ Z := conj_mem_closure_dStar ((wStar A).inv_mem hw) (hLZ hx)
      rw [inv_inv] at hx'
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hbZ hx')
      calc x * (w * b * w⁻¹) = w * ((w⁻¹ * x * w) * b) * w⁻¹ := by group
        _ = w * (b * (w⁻¹ * x * w)) * w⁻¹ := by rw [h]
        _ = w * b * w⁻¹ * x := by group
    apply h2115 G A E U c L hpair
    intro g hg
    have hw := hbW _ (wConj_mem_wStar A ⟨g, hg⟩)
    have hcomp : (MulAut.conj g).toMonoidHom.comp A.subtype =
        A.subtype.comp (wConj A ⟨g, hg⟩).toMonoidHom := by
      ext a
      simp [wConj_apply]
    apply mem_normalizer_of_map_conj_eq_self
    rw [← hcb, Subgroup.map_map, hcomp, ← Subgroup.map_map, ← commOf_conj, hw]
  intro φ hφ ψ hψ
  obtain ⟨-, g₁, hg₁⟩ := hBe ⟨φ, Subgroup.subset_closure hφ⟩ hφ
  obtain ⟨-, g₂, hg₂⟩ := hBe ⟨ψ, Subgroup.subset_closure hψ⟩ hψ
  refine ⟨((g₂ * g₁⁻¹ : Z) : MulAut A), (g₂ * g₁⁻¹ : Z).2, ?_⟩
  have h1 : (g₁ : MulAut A) * φ₀ * (g₁ : MulAut A)⁻¹ = φ := congrArg Subtype.val hg₁
  have h2 : (g₂ : MulAut A) * φ₀ * (g₂ : MulAut A)⁻¹ = ψ := congrArg Subtype.val hg₂
  rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h1, ← h2]
  group

theorem transitive_dStar_of_four [Finite G] (h2115 : Item2115) (h222 : Item222)
    (h223 : Item223) (hC : Item226CentralReflection) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) :
    ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ := by
  obtain ⟨-, -, -, n, -, -, ⟨eL⟩, -, -⟩ := exists_case_five h222 hpair hA81
  exact transitive_dStar_of_s3 h2115 h222 hpair hA81 (s3_of_item223 h223 hpair hA81 eL)
    (hC G A E U c L hpair hA81)

theorem nonempty_closure_localSet_dStarIn {A : Subgroup G} (t : Subgroup.closure (dStar A))
    {Y : Type*} [Group Y]
    (e : Subgroup.closure (Sec7.localSet (dStar A) (t : MulAut A)) ≃* Y) :
    Nonempty (Subgroup.closure (Sec7.localSet (dStarIn A) t) ≃* Y) := by
  have himg : (Subgroup.closure (dStar A)).subtype '' Sec7.localSet (dStarIn A) t =
      Sec7.localSet (dStar A) (t : MulAut A) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyD, hyt, hne⟩, rfl⟩
      exact ⟨hyD, congrArg Subtype.val hyt, fun h => hne (Subtype.ext h)⟩
    · rintro ⟨hxD, hxt, hne⟩
      exact ⟨⟨x, Subgroup.subset_closure hxD⟩,
        ⟨hxD, Subtype.ext hxt, fun h => hne (congrArg Subtype.val h)⟩, rfl⟩
  have hmap : (Subgroup.closure (Sec7.localSet (dStarIn A) t)).map
      (Subgroup.closure (dStar A)).subtype =
      Subgroup.closure (Sec7.localSet (dStar A) (t : MulAut A)) := by
    rw [MonoidHom.map_closure, himg]
  exact ⟨((Subgroup.closure _).equivMapOfInjective _
    (Subgroup.closure (dStar A)).subtype_injective).trans
    ((MulEquiv.subgroupCongr hmap).trans e)⟩

theorem isChainSystem_of_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {r : ℕ} {t : Fin r → MulAut A}
    (ht : ∀ i, t i ∈ dStar A) (hinj : Function.Injective t) (hAI : A ≤ ⨆ i, kOf A (t i))
    (hc : ∀ i j : Fin r, i.val + 1 < j.val →
      ∀ x ∈ kOf A (t i), ∀ y ∈ kOf A (t j), x * y = y * x)
    (hinf : ∀ i j : Fin r, i.val + 1 < j.val → kOf A (t i) ⊓ kOf A (t j) = ⊥) :
    IsChainSystem r A (fun i => kOf A (t i)) where
  commute := hc
  inf_eq_bot := hinf
  elem := hpair.mem_S.1.1
  le := hAI
  split i := eq_sup_inf_centralizer_kOf h222 hpair hK (ht i)
  index i := card_eq_three_mul_inf_centralizer_kOf h222 hpair hK (ht i)
  index₂ i j hij := card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK (ht i) (ht j) (hinj.ne hij)

end CFSG.RankThree.PartTwo.Sec21
