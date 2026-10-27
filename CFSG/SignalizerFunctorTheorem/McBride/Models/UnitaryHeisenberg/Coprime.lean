module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

variable {Y : Type*} [Group Y]

theorem mem_normalizer_of_forall {H : Subgroup Y} {c : Y} (h1 : ∀ x ∈ H, c * x * c⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, c⁻¹ * x * c ∈ H) : c ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem exists_abelian_normalized_subgroup [Finite Y] {C N : Subgroup Y} (hN : N ≠ ⊥)
    (hCN : C ≤ Subgroup.normalizer (N : Set Y)) (hCsolv : Group.IsSolvable C)
    (hCcop : Nat.Coprime (Nat.card C) (Nat.card N)) :
    ∃ V : Subgroup Y, V ≤ N ∧ V ≠ ⊥ ∧ (∀ x ∈ V, ∀ y ∈ V, Commute x y) ∧
      ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
  have hN1 : Nat.card N ≠ 1 := fun h => hN (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrN⟩ := Nat.exists_prime_and_dvd hN1
  have : Fact r.Prime := ⟨hr⟩
  let _inst := CFSG.SignalizerFunctor.Helpers.conjugationAction C N hCN
  obtain ⟨R, hR⟩ := CFSG.exists_invariant_sylow_of_solvable_operator_coprime (G := N) (A := C)
    hCcop (p := r)
  set R₁ : Subgroup Y := (R : Subgroup N).map N.subtype with hR₁
  have hR₁p : IsPGroup r R₁ := R.isPGroup'.map N.subtype
  have hR₁ne : R₁ ≠ ⊥ := by
    intro h
    have h1 : Nat.card R₁ = 1 := Subgroup.card_eq_one.mpr h
    rw [hR₁, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity] at h1
    have h2 : 0 < (Nat.card N).factorization r := hr.factorization_pos_of_dvd (Nat.card_pos.ne') hrN
    have : r ^ (Nat.card N).factorization r ≠ 1 := by
      intro h3
      exact (Nat.one_lt_pow h2.ne' hr.one_lt).ne' h3
    exact this h1
  have hR₁le : R₁ ≤ N := Subgroup.map_subtype_le _
  have hCR : ∀ c ∈ C, ∀ x ∈ R₁, c * x * c⁻¹ ∈ R₁ := by
    rintro c hc _ ⟨n, hn, rfl⟩
    have := (hR.invariant ⟨c, hc⟩ n).mp hn
    exact ⟨_, this, rfl⟩
  refine ⟨R₁ ⊓ Subgroup.centralizer (R₁ : Set Y), inf_le_left.trans hR₁le, ?_, ?_, ?_⟩
  · have hnt : Nontrivial R₁ := (Subgroup.nontrivial_iff_ne_bot R₁).mpr hR₁ne
    have hz := hR₁p.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center R₁)
    intro hbot
    apply hz1
    have hzV : ((z : R₁) : Y) ∈ R₁ ⊓ Subgroup.centralizer (R₁ : Set Y) := by
      refine ⟨(z : R₁).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩
      exact congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hzV
    apply Subtype.ext
    apply Subtype.ext
    exact hzV
  · intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  · intro c hc v hv
    refine ⟨hCR c hc v hv.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : c⁻¹ * w * c ∈ R₁ := by simpa using hCR c⁻¹ (inv_mem hc) w hw
    have := Subgroup.mem_centralizer_iff.mp hv.2 _ hw'
    calc w * (c * v * c⁻¹) = c * ((c⁻¹ * w * c) * v) * c⁻¹ := by group
      _ = c * (v * (c⁻¹ * w * c)) * c⁻¹ := by rw [this]
      _ = c * v * c⁻¹ * w := by group

theorem exists_commuting_pair [Finite Y] {P C N : Subgroup Y}
    (hPe : IsElemAbelian 3 P) (hP9 : 9 ≤ Nat.card P) (hPC : P ≤ C)
    (htrans : ∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y)
    (hN : N ≠ ⊥) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hCN : C ≤ Subgroup.normalizer (N : Set Y)) (hCsolv : Group.IsSolvable C)
    (hCcop : Nat.Coprime (Nat.card C) (Nat.card N))
    {u₁ u₂ : Y} (hu₁ : u₁ ∈ P) (hu₁1 : u₁ ≠ 1) (hu₂ : u₂ ∈ P) (hu₂1 : u₂ ≠ 1) :
    ∃ x y : Y, x ∈ N ∧ y ∈ N ∧ x ≠ 1 ∧ y ≠ 1 ∧ Commute x u₁ ∧ Commute y u₂ ∧ Commute x y := by
  obtain ⟨V, hVN, hV1, hVcomm, hCV⟩ := exists_abelian_normalized_subgroup hN hCN hCsolv hCcop
  have hPV : P ≤ Subgroup.normalizer (V : Set Y) := fun c hc =>
    mem_normalizer_of_forall (fun x hx => hCV c (hPC hc) x hx) (fun x hx => by
      simpa using hCV c⁻¹ (inv_mem (hPC hc)) x hx)
  have hVcop : Nat.Coprime 3 (Nat.card V) :=
    hN3.coprime_dvd_right (Subgroup.card_dvd_of_le hVN)
  have hgen := iSup_centralizer_nonidentity Nat.prime_three hPe (by simpa using hP9) hPV hVcop
  obtain ⟨u₀, hu₀, hu₀1, hne⟩ : ∃ u₀ ∈ P, u₀ ≠ 1 ∧ V ⊓ Subgroup.centralizer ({u₀} : Set Y) ≠ ⊥ := by
    by_contra! hall
    apply hV1
    rw [← hgen]
    exact iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun ha => iSup_eq_bot.mpr fun ha1 =>
      hall a ha ha1
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  have hx₀V : x₀ ∈ V := hx₀.1
  have hx₀u : u₀ * x₀ = x₀ * u₀ := (Subgroup.mem_centralizer_singleton_iff.mp hx₀.2).symm
  obtain ⟨c₁, hc₁, hc₁u⟩ := htrans u₀ hu₀ hu₀1 u₁ hu₁ hu₁1
  obtain ⟨c₂, hc₂, hc₂u⟩ := htrans u₀ hu₀ hu₀1 u₂ hu₂ hu₂1
  have hne1 : ∀ c : Y, c * x₀ * c⁻¹ ≠ 1 := fun c h => hx₀1 (by
    have := congrArg (fun z => c⁻¹ * z * c) h
    simpa [mul_assoc] using this)
  have hcomm : ∀ (c u : Y), c * u₀ * c⁻¹ = u → Commute (c * x₀ * c⁻¹) u := by
    intro c u hcu
    subst hcu
    show c * x₀ * c⁻¹ * (c * u₀ * c⁻¹) = c * u₀ * c⁻¹ * (c * x₀ * c⁻¹)
    calc c * x₀ * c⁻¹ * (c * u₀ * c⁻¹) = c * (x₀ * u₀) * c⁻¹ := by group
      _ = c * (u₀ * x₀) * c⁻¹ := by rw [hx₀u]
      _ = c * u₀ * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hV₁ := hCV c₁ hc₁ x₀ hx₀V
  have hV₂ := hCV c₂ hc₂ x₀ hx₀V
  exact ⟨c₁ * x₀ * c₁⁻¹, c₂ * x₀ * c₂⁻¹, hVN hV₁, hVN hV₂, hne1 c₁, hne1 c₂, hcomm c₁ u₁ hc₁u,
    hcomm c₂ u₂ hc₂u, hVcomm _ hV₁ _ hV₂⟩

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
