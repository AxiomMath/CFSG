module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

section General

variable {G : Type} [Group G]

theorem le_normalizer_commutator_of {A B X : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  have hmap : (⁅A, B⁆).map (MulAut.conj g).toMonoidHom = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hA hg),
      map_conj_eq_of_mem_normalizer (hB hg)]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨k, hk, hkh⟩ := hh
    have hkh' : g * k * g⁻¹ = g * h * g⁻¹ := hkh
    have hkeq : k = h := by simpa using hkh'
    rw [← hkeq]
    exact hk

theorem exists_autOn_restrict {L V W : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hWV : W ≤ V) :
    ∃ r : ↥(autOn L V) →* ↥(autOn L W), Function.Surjective r ∧
      ∀ (a : ↥(autOn L V)) (w : ↥W),
        ((((r a : ↥(autOn L W)) : MulAut ↥W) w : ↥W) : G) =
          (((a : MulAut ↥V) ⟨w, hWV w.2⟩ : ↥V) : G) := by
  classical
  have hex : ∀ a : ↥(autOn L V), ∃ l : ↥L, A4.actionOn V L hLV l = a := fun a =>
    (A4.mem_autOn_iff hLV).mp a.2
  choose f hf using hex
  have hres : ∀ (l : ↥L) (w : ↥W), ((A4.actionOn W L hLW l w : ↥W) : G) =
      ((A4.actionOn V L hLV l ⟨w, hWV w.2⟩ : ↥V) : G) := by
    intro l w
    rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]
  have hdet : ∀ l₁ l₂ : ↥L, A4.actionOn V L hLV l₁ = A4.actionOn V L hLV l₂ →
      A4.actionOn W L hLW l₁ = A4.actionOn W L hLW l₂ := by
    intro l₁ l₂ he
    ext w
    rw [hres, hres, he]
  let r : ↥(autOn L V) →* ↥(autOn L W) :=
    MonoidHom.mk' (fun a => ⟨A4.actionOn W L hLW (f a), (A4.mem_autOn_iff hLW).mpr ⟨f a, rfl⟩⟩)
      (fun a b => by
        apply Subtype.ext
        show A4.actionOn W L hLW (f (a * b)) =
          A4.actionOn W L hLW (f a) * A4.actionOn W L hLW (f b)
        rw [← map_mul]
        apply hdet
        rw [map_mul, hf, hf, hf]
        rfl)
  refine ⟨r, ?_, ?_⟩
  · intro b
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLW).mp b.2
    refine ⟨⟨A4.actionOn V L hLV l, (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show A4.actionOn W L hLW (f _) = (b : MulAut ↥W)
    rw [← hl]
    apply hdet
    rw [hf]
  · intro a w
    show ((A4.actionOn W L hLW (f a) w : ↥W) : G) = _
    rw [hres, hf]

end General

section Transvection

variable {K : Type} [Field K]

theorem exists_natAct_single (i : Fin 2) (a : K) :
    ∃ (γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) (j : Fin 2),
      natAct (Assembly.LowTwoRank.StatedSL 2 K) γ (Multiplicative.ofAdd (Pi.single j 1)) =
        Multiplicative.ofAdd (Pi.single i a) * Multiplicative.ofAdd (Pi.single j 1) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · have hdet : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two_of]
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, a; 0, 1]
      (by rw [hdet]; exact one_ne_zero), Subgroup.subset_closure hdet⟩, 1, ?_⟩
    show Multiplicative.ofAdd
        ((!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 1 1)) = _
    rw [← ofAdd_add]
    congr 1
    ext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · have hdet : (!![1, 0; a, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two_of]
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; a, 1]
      (by rw [hdet]; exact one_ne_zero), Subgroup.subset_closure hdet⟩, 0, ?_⟩
    show Multiplicative.ofAdd
        ((!![1, 0; a, 1] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1)) = _
    rw [← ofAdd_add]
    congr 1
    ext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_single_add_single (x : Fin 2 → K) : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
  ext k
  fin_cases k <;> simp

end Transvection

section Natural

variable {G : Type} [Group G]

theorem IsNatQuotCh5.commutator {L V : Subgroup G} {n : ℕ} (h : IsNatQuotCh5 L V n) :
    IsNatQuotCh5 L ⁅V, L⁆ n := by
  obtain ⟨hLV, hc, K, hKf, hKfin, hK, π, hπs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hLV Subgroup.le_normalizer
  have hcW : IsMulCommutative ↥⁅V, L⁆ :=
    ⟨⟨fun a b => Subtype.ext (setLike_mul_comm (s := V) (hWV a.2) (hWV b.2))⟩⟩
  obtain ⟨r, hrs, hr⟩ := exists_autOn_restrict hLV hLW hWV
  let ι : ↥(⊤ : Subgroup ↥⁅V, L⁆) →* ↥(⊤ : Subgroup ↥V) :=
    ((Subgroup.inclusion hWV).comp (⊤ : Subgroup ↥⁅V, L⁆).subtype).codRestrict ⊤
      (fun _ => Subgroup.mem_top _)
  refine ⟨hLW, hcW, K, hKf, hKfin, hK, r.comp π, hrs.comp hπs, le_top, hks,
    fun _ _ _ => Subgroup.mem_top _, ?_, hsec, hker, β.comp ι, ?_, ?_, ?_⟩
  ·
    intro a z hz
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLW).mp a.2
    rw [Subgroup.mem_subgroupOf] at hz
    rw [← hl, Subgroup.mem_subgroupOf, A4.actionOn_apply_coe]
    have hcomm : (l : G) * (z : G) = (z : G) * l := Subgroup.mem_centralizer_iff.mp hz l l.2
    rw [hcomm, mul_inv_cancel_right]
    exact hz
  ·
    have hsingle : ∀ (i : Fin 2) (a : K),
        QuotientGroup.mk (⟨Multiplicative.ofAdd (Pi.single i a), Subgroup.mem_top _⟩ :
          ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec) ∈ (β.comp ι).range := by
      intro i a
      obtain ⟨γ, j, hγ⟩ := exists_natAct_single i a
      set m : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec :=
        ⟨Multiplicative.ofAdd (Pi.single j 1), Subgroup.mem_top _⟩ with hm
      obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
      have hu' : ((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) ∈ (⊤ : Subgroup ↥V) :=
        Subgroup.mem_top _
      have he := hβe γ u m hu' (Subgroup.mem_top _) hu
      obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (π γ).2
      set c : ↥(⊤ : Subgroup ↥V) :=
        (⟨((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V), hu'⟩ : ↥(⊤ : Subgroup ↥V)) * u⁻¹
        with hc
      have hcW : ((c : ↥V) : G) ∈ ⁅V, L⁆ := by
        have hval : ((c : ↥V) : G) = ⁅(l : G), ((u : ↥V) : G)⁆ := by
          rw [hc]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hl, A4.actionOn_apply_coe, commutatorElement_def]
        rw [hval, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator l.2 (u : ↥V).2
      refine ⟨⟨⟨((c : ↥V) : G), hcW⟩, Subgroup.mem_top _⟩, ?_⟩
      have hιc : ι ⟨⟨((c : ↥V) : G), hcW⟩, Subgroup.mem_top _⟩ = c := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [MonoidHom.comp_apply, hιc, hc, map_mul, map_inv, he, hu, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show natAct (Assembly.LowTwoRank.StatedSL 2 K) γ (Multiplicative.ofAdd (Pi.single j 1)) *
          (Multiplicative.ofAdd (Pi.single j 1))⁻¹ = Multiplicative.ofAdd (Pi.single i a)
      rw [hγ, mul_inv_cancel_right]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨v, hv⟩ : ∃ v : Fin 2 → K, Multiplicative.ofAdd v = x.1 := ⟨Multiplicative.toAdd x.1, rfl⟩
    have hx : x = (⟨Multiplicative.ofAdd (Pi.single 0 (v 0)), Subgroup.mem_top _⟩ :
          ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec) *
        ⟨Multiplicative.ofAdd (Pi.single 1 (v 1)), Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      rw [← hv]
      show (Multiplicative.ofAdd v : Multiplicative (Fin 2 → K)) =
        (Multiplicative.ofAdd (Pi.single 0 (v 0)) : Multiplicative (Fin 2 → K)) *
          Multiplicative.ofAdd (Pi.single 1 (v 1))
      rw [← ofAdd_add, ← eq_single_add_single]
    rw [hx, QuotientGroup.mk_mul]
    exact MonoidHom.mem_range.mp ((β.comp ι).range.mul_mem (hsingle 0 _) (hsingle 1 _))
  ·
    intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  ·
    intro γ u m hu hm hum
    have heq : ι ⟨(((r.comp π) γ : ↥(autOn L ⁅V, L⁆)) : MulAut ↥⁅V, L⁆) (u : ↥⁅V, L⁆), hu⟩ =
        ⟨((π γ : ↥(autOn L V)) : MulAut ↥V) (ι u : ↥V), Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hr (π γ) (u : ↥⁅V, L⁆)
    rw [MonoidHom.comp_apply, heq]
    exact hβe γ (ι u) m (Subgroup.mem_top _) hm hum

end Natural

end CFSG.Quasithin.H13
