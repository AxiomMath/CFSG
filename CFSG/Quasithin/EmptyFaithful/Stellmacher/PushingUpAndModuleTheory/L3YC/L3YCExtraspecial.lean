module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Extraspecial

variable {V : Type*} [Group V]

theorem comm_mem_center (p : ℕ) [CFSG.IsExtraspecial p V] (x y : V) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center V := by
  have h := (CFSG.IsExtraspecial.quotient_elementary_abelian p V).is_comm.comm
  have hc : (QuotientGroup.mk x : V ⧸ Subgroup.center V) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x := h _ _
  have : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : V ⧸ Subgroup.center V) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hc]
    group
  exact (QuotientGroup.eq_one_iff _).mp this

theorem pow_mem_center (p : ℕ) [CFSG.IsExtraspecial p V] (x : V) :
    x ^ p ∈ Subgroup.center V := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsExtraspecial.quotient_elementary_abelian p V).exponent_dvd_p
    (QuotientGroup.mk x : V ⧸ Subgroup.center V)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  exact h

theorem card_le_eight_of_abelian_index_le_two [Finite V] [CFSG.IsExtraspecial 2 V] (A : Subgroup V)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcard : Nat.card V ≤ 2 * Nat.card A) :
    Nat.card V ≤ 8 := by
  classical
  set Z : Subgroup V := Subgroup.center V with hZ
  have hZc : Nat.card Z = 2 := CFSG.IsExtraspecial.center_order_p 2 V
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ A := by
    by_contra hcon
    push Not at hcon
    have hZtop : Z = ⊤ := by
      refine top_unique fun v _ => ?_
      rw [hZ, Subgroup.mem_center_iff]
      intro g
      exact hA g (hcon g) v (hcon v)
    have hnt := CFSG.IsExtraspecial.quotient_nontrivial 2 V
    have : Subsingleton (V ⧸ Z) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, hZtop]
      exact Subgroup.mem_top _
    exact (not_subsingleton _) this
  have hS : A ⊔ Subgroup.zpowers x = ⊤ := by
    have hlt : A < A ⊔ Subgroup.zpowers x :=
      lt_of_le_of_ne le_sup_left fun h =>
        hx (h ▸ (le_sup_right : Subgroup.zpowers x ≤ A ⊔ Subgroup.zpowers x)
          (Subgroup.mem_zpowers x))
    have h1 : Nat.card A ∣ Nat.card ↥(A ⊔ Subgroup.zpowers x) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers x)
      exact this
    have h2 : Nat.card ↥(A ⊔ Subgroup.zpowers x) ∣ Nat.card V := Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card A < Nat.card ↥(A ⊔ Subgroup.zpowers x) := Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk⟩ := h1
    have hkpos : 2 ≤ k := by
      by_contra hk2
      have : k ≤ 1 := by omega
      interval_cases k
      · simp at hk; omega
      · simp at hk; omega
    have hApos : 0 < Nat.card A := Nat.card_pos
    have : Nat.card V ≤ Nat.card ↥(A ⊔ Subgroup.zpowers x) := by
      have : 2 * Nat.card A ≤ Nat.card ↥(A ⊔ Subgroup.zpowers x) := by rw [hk]; nlinarith
      omega
    exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Nat.le_of_dvd Nat.card_pos h2) this)
  let f : ↥A →* V :=
    { toFun := fun a => (a : V) * x * (a : V)⁻¹ * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        have hb : (b : V) * x * (b : V)⁻¹ * x⁻¹ ∈ Z := comm_mem_center 2 _ _
        rw [hZ, Subgroup.mem_center_iff] at hb
        have := hb ((a : V) * x * (a : V)⁻¹ * x⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have hba := hb (a : V)
        have hbb := hb ((a : V) * x * (a : V)⁻¹ * x⁻¹)
        calc (a : V) * (b : V) * x * ((b : V)⁻¹ * (a : V)⁻¹) * x⁻¹
            = ((a : V) * ((b : V) * x * (b : V)⁻¹ * x⁻¹)) * (x * (a : V)⁻¹ * x⁻¹) := by group
          _ = (((b : V) * x * (b : V)⁻¹ * x⁻¹) * (a : V)) * (x * (a : V)⁻¹ * x⁻¹) := by rw [hba]
          _ = ((b : V) * x * (b : V)⁻¹ * x⁻¹) * ((a : V) * x * (a : V)⁻¹ * x⁻¹) := by group
          _ = ((a : V) * x * (a : V)⁻¹ * x⁻¹) * ((b : V) * x * (b : V)⁻¹ * x⁻¹) := hbb.symm }
  have hrange : f.range ≤ Z := by
    rintro _ ⟨a, rfl⟩
    exact comm_mem_center 2 _ _
  have hkerZ : f.ker.map A.subtype ≤ Z := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (a : V) * x * (a : V)⁻¹ * x⁻¹ = 1 := ha
    have hax : (a : V) * x = x * (a : V) := by
      have := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({(a : V)} : Set V) := by
      have hle : A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({(a : V)} : Set V) := by
        refine sup_le (fun b hb => ?_) ((Subgroup.zpowers_le).mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hA (a : V) a.2 b hb).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hax.symm
      exact hle (hS ▸ Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  have hk : Nat.card f.ker ≤ 2 := by
    have := Subgroup.card_le_of_le hkerZ
    rwa [Subgroup.card_map_of_injective A.subtype_injective, hZc] at this
  have hr : Nat.card f.range ≤ 2 := by
    have := Subgroup.card_le_of_le hrange
    rwa [hZc] at this
  have hmul := Subgroup.card_ker_mul_card_range f
  have : Nat.card A ≤ 4 := by
    rw [← hmul]; nlinarith
  omega

end Extraspecial

end Stellmacher.PU.L3YC

end CFSG.Quasithin
