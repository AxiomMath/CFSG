module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem centralizes_of_perfect_action {Y : Type} [Group Y] [Finite Y] {T S X : Subgroup Y}
    [hSn : S.Normal] [IsSimpleGroup ↥X] (hTS : T ≤ S) (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hZ : Subgroup.center ↥S = ⊥)
    (hOut : ∀ P : Subgroup (MulAut ↥S), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : ↥S →* MulAut ↥S).range)
    (hCent : ∀ s ∈ S, (∀ t ∈ T, s * t = t * s) → s * s = 1 → s ∈ T)
    (hX4 : 4 ∣ Nat.card X) (hXT : ∀ x ∈ X, ∀ t ∈ T, x * t = t * x) :
    ∀ x ∈ X, ∀ s ∈ S, x * s = s * x := by
  classical
  have hXnc : ∃ a b : ↥X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative ↥X := ⟨⟨fun a b => hcon a b⟩⟩
    have hp : (Nat.card ↥X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rcases hp.eq_one_or_self_of_dvd 4 hX4 with h | h
    · omega
    · rw [← h] at hp
      exact absurd hp (by decide)
  have hperf : Group.IsPerfect ↥X := by
    refine ⟨?_⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator ↥X) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hXnc
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator ↥X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exact h0
  let φ : ↥X →* MulAut ↥S := (MulAut.conjNormal (H := S)).comp X.subtype
  have hφ : ∀ (x : ↥X) (y : ↥S), ((φ x y : ↥S) : Y) = (x : Y) * (y : Y) * (x : Y)⁻¹ :=
    fun x y => rfl
  haveI := hperf
  have hP : commutator ↥(φ.range) = ⊤ := (Group.IsPerfect.range φ).commutator_eq_top
  have hinner : ∀ x : ↥X, ∃ s : ↥S, ∀ y : ↥S,
      (s : Y) * (y : Y) * (s : Y)⁻¹ = (x : Y) * (y : Y) * (x : Y)⁻¹ := by
    intro x
    have hmem : φ x ∈ φ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hOut _ hP hmem)
    refine ⟨s, fun y => ?_⟩
    have h1 := congrArg (fun a : MulAut ↥S => ((a y : ↥S) : Y)) hs
    simpa [MulAut.conj_apply, hφ] using h1
  rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with hker | hker
  ·
    exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    have key : ∀ (w : ↥X) (sw : ↥S), w * w = 1 →
        (∀ y : ↥S, (sw : Y) * (y : Y) * (sw : Y)⁻¹ = (w : Y) * (y : Y) * (w : Y)⁻¹) →
        (sw : Y) ∈ T := by
      intro w sw hw hsw
      have hww : (w : Y) * (w : Y) = 1 := congrArg Subtype.val hw
      have hwinv : (w : Y)⁻¹ = (w : Y) := inv_eq_of_mul_eq_one_right hww
      have hsq : (sw : Y) * (sw : Y) = 1 := by
        have hc : sw * sw ∈ Subgroup.center ↥S := by
          rw [Subgroup.mem_center_iff]
          intro z
          apply Subtype.ext
          have hz' : (w : Y) * (z : Y) * (w : Y)⁻¹ ∈ S := hSn.conj_mem _ z.2 w
          have e1 : (sw : Y) * (z : Y) * (sw : Y)⁻¹ = (w : Y) * (z : Y) * (w : Y)⁻¹ := hsw z
          have e2 : (sw : Y) * ((w : Y) * (z : Y) * (w : Y)⁻¹) * (sw : Y)⁻¹ =
              (w : Y) * ((w : Y) * (z : Y) * (w : Y)⁻¹) * (w : Y)⁻¹ :=
            hsw ⟨(w : Y) * (z : Y) * (w : Y)⁻¹, hz'⟩
          have h5 : (sw : Y) * ((sw : Y) * (z : Y) * (sw : Y)⁻¹) * (sw : Y)⁻¹ = (z : Y) := by
            rw [e1, e2, hwinv]
            calc (w : Y) * ((w : Y) * (z : Y) * (w : Y)) * (w : Y)
                = ((w : Y) * (w : Y)) * (z : Y) * ((w : Y) * (w : Y)) := by group
              _ = (z : Y) := by rw [hww]; group
          show (z : Y) * ((sw : Y) * (sw : Y)) = ((sw : Y) * (sw : Y)) * (z : Y)
          calc (z : Y) * ((sw : Y) * (sw : Y))
              = ((sw : Y) * ((sw : Y) * (z : Y) * (sw : Y)⁻¹) * (sw : Y)⁻¹) *
                  ((sw : Y) * (sw : Y)) := by rw [h5]
            _ = ((sw : Y) * (sw : Y)) * (z : Y) := by group
        rw [hZ, Subgroup.mem_bot] at hc
        exact congrArg Subtype.val hc
      refine hCent (sw : Y) sw.2 (fun t ht => ?_) hsq
      have h3 : (sw : Y) * t * (sw : Y)⁻¹ = (w : Y) * t * (w : Y)⁻¹ := hsw ⟨t, hTS ht⟩
      have h4 : (w : Y) * t * (w : Y)⁻¹ = t := by
        rw [hXT (w : Y) w.2 t ht]
        group
      rw [h4] at h3
      calc (sw : Y) * t = ((sw : Y) * t * (sw : Y)⁻¹) * (sw : Y) := by group
        _ = t * (sw : Y) := by rw [h3]
    have hinv : ∀ u v : ↥X, u * u = 1 → v * v = 1 → u * v = v * u := by
      intro u v hu hv
      obtain ⟨su, hsu⟩ := hinner u
      obtain ⟨sv, hsv⟩ := hinner v
      have hsuT : (su : Y) ∈ T := key u su hu hsu
      have hsvT : (sv : Y) ∈ T := key v sv hv hsv
      have hcT : (su : Y) * (sv : Y) = (sv : Y) * (su : Y) := hTab _ hsuT _ hsvT
      have hL : ∀ y : ↥S, ((u * v : ↥X) : Y) * (y : Y) * ((u * v : ↥X) : Y)⁻¹ =
          ((su : Y) * (sv : Y)) * (y : Y) * ((su : Y) * (sv : Y))⁻¹ := by
        intro y
        have e1 := hsv y
        have hy1 : (v : Y) * (y : Y) * (v : Y)⁻¹ ∈ S := hSn.conj_mem _ y.2 v
        have e2 : (su : Y) * ((v : Y) * (y : Y) * (v : Y)⁻¹) * (su : Y)⁻¹ =
            (u : Y) * ((v : Y) * (y : Y) * (v : Y)⁻¹) * (u : Y)⁻¹ :=
          hsu ⟨(v : Y) * (y : Y) * (v : Y)⁻¹, hy1⟩
        calc ((u * v : ↥X) : Y) * (y : Y) * ((u * v : ↥X) : Y)⁻¹
            = (u : Y) * ((v : Y) * (y : Y) * (v : Y)⁻¹) * (u : Y)⁻¹ := by
              simp only [Subgroup.coe_mul]; group
          _ = (su : Y) * ((v : Y) * (y : Y) * (v : Y)⁻¹) * (su : Y)⁻¹ := e2.symm
          _ = (su : Y) * ((sv : Y) * (y : Y) * (sv : Y)⁻¹) * (su : Y)⁻¹ := by rw [e1]
          _ = ((su : Y) * (sv : Y)) * (y : Y) * ((su : Y) * (sv : Y))⁻¹ := by group
      have hR : ∀ y : ↥S, ((v * u : ↥X) : Y) * (y : Y) * ((v * u : ↥X) : Y)⁻¹ =
          ((sv : Y) * (su : Y)) * (y : Y) * ((sv : Y) * (su : Y))⁻¹ := by
        intro y
        have e1 := hsu y
        have hy1 : (u : Y) * (y : Y) * (u : Y)⁻¹ ∈ S := hSn.conj_mem _ y.2 u
        have e2 : (sv : Y) * ((u : Y) * (y : Y) * (u : Y)⁻¹) * (sv : Y)⁻¹ =
            (v : Y) * ((u : Y) * (y : Y) * (u : Y)⁻¹) * (v : Y)⁻¹ :=
          hsv ⟨(u : Y) * (y : Y) * (u : Y)⁻¹, hy1⟩
        calc ((v * u : ↥X) : Y) * (y : Y) * ((v * u : ↥X) : Y)⁻¹
            = (v : Y) * ((u : Y) * (y : Y) * (u : Y)⁻¹) * (v : Y)⁻¹ := by
              simp only [Subgroup.coe_mul]; group
          _ = (sv : Y) * ((u : Y) * (y : Y) * (u : Y)⁻¹) * (sv : Y)⁻¹ := e2.symm
          _ = (sv : Y) * ((su : Y) * (y : Y) * (su : Y)⁻¹) * (sv : Y)⁻¹ := by rw [e1]
          _ = ((sv : Y) * (su : Y)) * (y : Y) * ((sv : Y) * (su : Y))⁻¹ := by group
      apply hinj
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hφ, hφ, hL y, hR y, hcT]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (dvd_trans (by norm_num : 2 ∣ 4) hX4)
    have hu2 : u * u = 1 := by
      rw [← pow_two, ← hu]
      exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu
      norm_num at hu
    haveI hDn : (Subgroup.centralizer {v : ↥X | v * v = 1}).Normal := ⟨fun d hd g => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : (g⁻¹ * v * g) * (g⁻¹ * v * g) = 1 := by
        have : v * v = 1 := hv
        calc (g⁻¹ * v * g) * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
          _ = 1 := by rw [this]; group
      have h1 := Subgroup.mem_centralizer_iff.mp hd (g⁻¹ * v * g) hv'
      calc v * (g * d * g⁻¹) = g * ((g⁻¹ * v * g) * d) * g⁻¹ := by group
        _ = g * (d * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = (g * d * g⁻¹) * v := by group⟩
    have huD : u ∈ Subgroup.centralizer {v : ↥X | v * v = 1} :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => hinv v u hv hu2
    have hD : Subgroup.centralizer {v : ↥X | v * v = 1} = ⊤ :=
      (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left fun h => hu1 (by
        rw [h, Subgroup.mem_bot] at huD
        exact huD)
    have hcent : u ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer {v : ↥X | v * v = 1} := by
        rw [hD]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg u hu2).symm
    have hZX : Subgroup.center ↥X = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥X) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, b, hab⟩ := hXnc
        have ha : a ∈ Subgroup.center ↥X := by
          rw [h0]
          exact Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    rw [hZX, Subgroup.mem_bot] at hcent
    exact hu1 hcent
  ·
    intro x hx s hs
    have h1 : φ ⟨x, hx⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact Subgroup.mem_top _
    have h2 := congrArg (fun a : MulAut ↥S => ((a ⟨s, hs⟩ : ↥S) : Y)) h1
    have h3 : x * s * x⁻¹ = s := by simpa [hφ] using h2
    calc x * s = (x * s * x⁻¹) * x := by group
      _ = s * x := by rw [h3]

end CFSG.RankThree.GF2n.Stroth80
