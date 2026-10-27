module

public import CFSG.Quasithin.Vol2.Ch10SecD33B
public import CFSG.Quasithin.Vol2.Ch10SecD33D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem cV1_ne_bot (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hne : fsuCVM T L I ≠ ⊥) :
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  obtain ⟨⟨x, hxV, hxC⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hCL : Subgroup.centralizer (fsuL0 T L : Set G) ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (le_conjClosure L T)
  have hab : ∀ a ∈ fsuVM T L I, ∀ b ∈ fsuVM T L I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((SecA.isElemAbelian_fsuVM h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV1N : fsuUL T L I ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have haV := V1_le_V ha
    constructor
    · intro hb
      have hbV : b ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hb
      rw [show a * b * a⁻¹ = b by rw [hab a haV b hbV]; group]
      exact hb
    · intro hb
      have hbV : a * b * a⁻¹ ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hb
      have hb' : b ∈ fsuVM T L I := by
        have e1 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
        rw [e1]
        exact (fsuVM T L I).mul_mem ((fsuVM T L I).mul_mem ((fsuVM T L I).inv_mem haV) hbV) haV
      rwa [show a * b * a⁻¹ = b by rw [hab a haV b hb']; group] at hb
  have hxsup : x ∈ fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rw [← SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact hxV
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hV1N hxsup
  have hv₂C := V2_le_centralizer_L h37 h38 h ht htn hv₂
  by_cases hv₁1 : v₁ = 1
  ·
    subst hv₁1
    rw [one_mul] at hxC hx1'
    have hv₂' : v₂ ∈ CFSG.conjugate (fsuUL T L I) t := by
      rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
      exact hv₂
    have hy : t * v₂ * t⁻¹ ∈ fsuUL T L I := SecA.mem_conjugate_iff.mp hv₂'
    have hyC : t * v₂ * t⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : t⁻¹ * l * t ∈ fsuL0 T L := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure L T (T.inv_mem ht)) l).mp hl
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hl'
      calc l * (t * v₂ * t⁻¹) = t * ((t⁻¹ * l * t) * v₂) * t⁻¹ := by group
        _ = t * (v₂ * (t⁻¹ * l * t)) * t⁻¹ := by rw [hc]
        _ = t * v₂ * t⁻¹ * l := by group
    intro hbot
    have hmem : t * v₂ * t⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hy, hCL hyC⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hx1'
    have e1 : v₂ = t⁻¹ * (t * v₂ * t⁻¹) * t := by group
    rw [e1, hmem]
    group
  ·
    intro hbot
    have hv₁C : v₁ ∈ Subgroup.centralizer (L : Set G) := by
      have h1 : v₁ = v₁ * v₂ * v₂⁻¹ := by group
      rw [h1]
      exact (Subgroup.centralizer _).mul_mem (hCL hxC) ((Subgroup.centralizer _).inv_mem hv₂C)
    have hmem : v₁ ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) := ⟨hv₁, hv₁C⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hv₁1 hmem

theorem centralizer_Z_le_fsuM (h331 : Stmt3_3_1) (h1028 : Stmt10_2_8) (h : Hyp10 G T L I)
    (hL : LBarL32 L) (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZL := (h1028 G T L I h hL hV1).1
  have hLC : L ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hZL
    exact hZL
  have hTC : T ≤ Subgroup.centralizer (Z : Set G) := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_omegaOneCenter hz hs)).symm
  have hZT : Z ≤ T := (Subgroup.closure_le _).mpr fun x hx => hx.1.1
  have hZC : Z ≤ Subgroup.centralizer (Z : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_omegaOneCenter hz (hZT hw)))
  have hT1 : T ≠ ⊥ := by
    intro hbot
    apply SecA.commutator_fsuVM_ne_bot h.fsu
    rw [eq_bot_iff]
    intro x hx
    have := SecA.fsuVM_le_T h (V1_le_V hx)
    rw [hbot] at this
    exact this
  have hZ1 : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot h.fsu.sylow.1 hT1
  have hZO : Z ≤ pCoreOf 2 (Subgroup.centralizer (Z : Set G)) :=
    le_pCoreOf_of_normalizes hZC (Subgroup.centralizer_le_normalizer _) (h.fsu.sylow.1.to_le hZT)
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot fun hbot => hZ1 (le_bot_iff.mp (hbot ▸ hZO))
  have heq := (SecB.stmt331_B h331 h).1.2.2 M' hM'.1 ((sup_le hLC hTC).trans hM'.2)
  rw [← heq]
  exact hM'.2

theorem inf_centralizer_eq_pCoreOf (hW : FactSymFiveWrTwo) {H U M : Subgroup G}
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hTH : IsSylowTwoOf T H) (hTM : T ≤ M)
    (hHM : ¬ H ≤ M) (hred : IsTwoReducedIn H U) (hCM : H ⊓ Subgroup.centralizer (U : Set G) ≤ M) :
    H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := H ⊓ Subgroup.centralizer (U : Set G) with hNdef
  refine le_antisymm ?_ (le_inf (Subgroup.map_subtype_le _)
    (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hred))
  have hCN : ∀ g ∈ Subgroup.normalizer (U : Set G),
      g ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc u hu
      have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) u).mp hu
      have h1 := hc _ hu'
      calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g⁻¹⁻¹) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * u := by group
    · intro hc u hu
      have hu' : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
      have h1 := hc _ hu'
      have e1 : g * (u * c) * g⁻¹ = g * (c * u) * g⁻¹ := by
        calc g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
          _ = (g * c * g⁻¹) * (g * u * g⁻¹) := h1
          _ = g * (c * u) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e1)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := fun h hh =>
    mem_normalizer_inf (Subgroup.le_normalizer hh) (hCN h (hred.2.1 hh))
  have hodd : ∀ y ∈ N, Odd (orderOf y) → y = 1 := by
    intro y hy hyo
    by_contra hy1
    apply hHM
    rw [← oTwoUpper_sup_eq hTH]
    refine sup_le ((Subgroup.closure_le _).mpr fun x hx => hCM ?_) hTM
    exact forall_odd_mem_of_normal hW e inf_le_left hHN hy hyo hy1 hx.1 hx.2
  have hN2 : IsPGroup 2 N := by
    intro ⟨x, hx⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, Subtype.ext ?_⟩
    have hxk : x ^ 2 ^ k ∈ N := N.pow_mem hx _
    have hord : orderOf (x ^ 2 ^ k) = m := by
      rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm, Nat.gcd_eq_right (dvd_mul_right _ _),
        Nat.mul_div_cancel_left m (by positivity)]
    simpa using hodd _ hxk (hord ▸ hm)
  exact le_pCoreOf_of_normalizes inf_le_left hHN hN2

end CFSG.Quasithin.Vol2.Ch10.SecD
