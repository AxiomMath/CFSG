module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIso

public section

namespace CFSG.HardMathSupport.C14ExcIso

theorem pElt_mem_of_central_product {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (F : M →* M)
    (Z S : Subgroup M) (hZ : Z ≤ Subgroup.center M) (hZF : ∀ z ∈ Z, F z ∈ Z)
    (hSF : ∀ s ∈ S, F s ∈ S) (hZS : ∀ m : M, ∃ z ∈ Z, ∃ s ∈ S, m = z * s)
    [Finite (Z ⊓ S : Subgroup M)] (hK : ¬ p ∣ Nat.card (Z ⊓ S : Subgroup M))
    [Finite (fixG F ⊓ S : Subgroup M)] (hS : ¬ p ∣ Nat.card (fixG F ⊓ S : Subgroup M))
    (y : M) (hy : F y = y) (hyp : ∃ n : ℕ, y ^ p ^ n = 1) : y ∈ Z := by
  obtain ⟨z, hz, s, hs, rfl⟩ := hZS y
  obtain ⟨n, hn⟩ := hyp
  have hcen : ∀ c ∈ Z, ∀ g : M, c * g = g * c := fun c hc g =>
    (Subgroup.mem_center_iff.1 (hZ hc) g).symm
  let X : Subgroup M :=
    { carrier := {x | x ∈ S ∧ x⁻¹ * F x ∈ Z}
      mul_mem' := by
        rintro x w ⟨hxS, hxZ⟩ ⟨hwS, hwZ⟩
        refine ⟨mul_mem hxS hwS, ?_⟩
        have : (x * w)⁻¹ * F (x * w) = (x⁻¹ * F x) * (w⁻¹ * F w) := by
          rw [map_mul, mul_inv_rev]
          calc w⁻¹ * x⁻¹ * (F x * F w) = w⁻¹ * (x⁻¹ * F x) * F w := by group
            _ = (x⁻¹ * F x) * w⁻¹ * F w := by rw [← hcen _ hxZ w⁻¹]
            _ = _ := by group
        rw [this]
        exact mul_mem hxZ hwZ
      one_mem' := ⟨one_mem _, by simp [one_mem]⟩
      inv_mem' := by
        rintro x ⟨hxS, hxZ⟩
        refine ⟨inv_mem hxS, ?_⟩
        have : x⁻¹⁻¹ * F x⁻¹ = (x⁻¹ * F x)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
          have h := hcen _ (inv_mem hxZ) x
          rw [mul_inv_rev, inv_inv] at h
          calc x * (F x)⁻¹ = x * ((F x)⁻¹ * x) * x⁻¹ := by group
            _ = ((F x)⁻¹ * x) * x * x⁻¹ := by rw [h]
            _ = (F x)⁻¹ * x := by group
        rw [this]
        exact inv_mem hxZ }
  have hmemX : ∀ x, x ∈ X ↔ x ∈ S ∧ x⁻¹ * F x ∈ Z := fun x => Iff.rfl
  let ψ : X →* (Z ⊓ S : Subgroup M) :=
    { toFun := fun x => ⟨(x : M)⁻¹ * F x, Subgroup.mem_inf.2 ⟨((hmemX x).1 x.2).2,
        (show (x : M)⁻¹ * F x ∈ S from
          mul_mem (inv_mem ((hmemX x).1 x.2).1) (hSF _ ((hmemX x).1 x.2).1))⟩⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x w
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (w : M)⁻¹ * (x : M)⁻¹ * (F x * F w) = (w : M)⁻¹ * ((x : M)⁻¹ * F x) * F w := by
              group
          _ = ((x : M)⁻¹ * F x) * (w : M)⁻¹ * F w := by rw [← hcen _ ((hmemX x).1 x.2).2 (w : M)⁻¹]
          _ = _ := by group }
  have hker : Nat.card ψ.ker = Nat.card (fixG F ⊓ S : Subgroup M) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : X) : M), ?_, ((hmemX _).1 (x : X).2).1⟩
        invFun := fun w => ⟨⟨w, (hmemX _).2 ⟨w.2.2, ?_⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    · have h := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
      change ((x : X) : M)⁻¹ * F ((x : X) : M) = 1 at h
      exact mem_fixG.2 (inv_mul_eq_one.1 h).symm
    · rw [mem_fixG.1 w.2.1, inv_mul_cancel]; exact one_mem _
    · apply MonoidHom.mem_ker.2
      ext
      change (w : M)⁻¹ * F w = 1
      rw [mem_fixG.1 w.2.1, inv_mul_cancel]
  have hrange : Nat.card ψ.range ∣ Nat.card (Z ⊓ S : Subgroup M) :=
    Subgroup.card_subgroup_dvd_card _
  have hX : Nat.card X = Nat.card ψ.range * Nat.card (fixG F ⊓ S : Subgroup M) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hXp : ¬ p ∣ Nat.card X := by
    rw [hX]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hK (h.trans hrange)
    · exact hS h
  have hk : s⁻¹ * F s = (F z)⁻¹ * z := by
    have h1 : F z * F s = z * s := by rw [← map_mul, hy]
    have h2 : F s = ((F z)⁻¹ * z) * s := by rw [mul_assoc, ← h1]; group
    rw [h2, hcen _ (mul_mem (inv_mem (hZF z hz)) hz) s]
    group
  have hsX : s ∈ X := ⟨hs, by rw [hk]; exact mul_mem (inv_mem (hZF z hz)) hz⟩
  have hsp : s ^ p ^ n ∈ Z := by
    have h1 : (z * s) ^ p ^ n = z ^ p ^ n * s ^ p ^ n :=
      (Commute.mul_pow (hcen z hz s) _)
    rw [h1] at hn
    have : s ^ p ^ n = (z ^ p ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hn
    rw [this]
    exact inv_mem (pow_mem hz _)
  set K' : Subgroup X := (Z ⊓ S : Subgroup M).subgroupOf X with hK'
  haveI hK'n : K'.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hK', Subgroup.mem_subgroupOf] at hc ⊢
    have h : (g : M) * c * (g : M)⁻¹ = c := by
      rw [← hcen _ hc.1 (g : M), mul_inv_cancel_right]
    simpa [h] using hc
  have hidx : Nat.Coprime (p ^ n) K'.index := by
    refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hXp ?_)
    exact h.trans K'.index_dvd_card
  set sX : X := ⟨s, hsX⟩
  have hsK : sX ∈ K' := by
    have hx1 : (QuotientGroup.mk sX : X ⧸ K') ^ K'.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.pow_index_mem K' sX
    have hx2 : (QuotientGroup.mk sX : X ⧸ K') ^ p ^ n = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK', Subgroup.mem_subgroupOf]
      exact ⟨hsp, pow_mem hs _⟩
    have := pow_gcd_eq_one.2 ⟨hx2, hx1⟩
    rwa [hidx, pow_one, QuotientGroup.eq_one_iff] at this
  have hsZ : s ∈ Z := (Subgroup.mem_subgroupOf.1 hsK).1
  exact mul_mem hz hsZ

end CFSG.HardMathSupport.C14ExcIso
