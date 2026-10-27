module

public import CFSG.LinearAlgebra.SteinbergBQPerfectCentralizer
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.Quasithin.H13.L1293S

open Module CFSG.LinearAlgebra.SteinbergBQ

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def eNeg (z : V →ₗ[F] V) : Submodule F V := LinearMap.ker (z + LinearMap.id)

@[expose] def ePos (z : V →ₗ[F] V) : Submodule F V := LinearMap.ker (z - LinearMap.id)

theorem mem_eNeg {z : V →ₗ[F] V} {v : V} : v ∈ eNeg z ↔ z v = -v := by
  rw [eNeg, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

theorem mem_ePos {z : V →ₗ[F] V} {v : V} : v ∈ ePos z ↔ z v = v := by
  rw [ePos, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_eNeg_of_comm {g z : V →ₗ[F] V} (hc : ∀ v, g (z v) = z (g v)) {v : V}
    (hv : v ∈ eNeg z) : g v ∈ eNeg z := by
  rw [mem_eNeg] at hv ⊢
  rw [← hc, hv, map_neg]

theorem mem_ePos_of_comm {g z : V →ₗ[F] V} (hc : ∀ v, g (z v) = z (g v)) {v : V}
    (hv : v ∈ ePos z) : g v ∈ ePos z := by
  rw [mem_ePos] at hv ⊢
  rw [← hc, hv]

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply h2
  calc (2 : F) = 1 + 1 := by norm_num
    _ = -1 + 1 := by rw [h]
    _ = 0 := by ring

theorem eq_zero_of_eq_neg (h2 : (2 : F) ≠ 0) {v : V} (h : v = -v) : v = 0 := by
  have h' : (2 : F) • v = 0 := by
    rw [two_smul]
    calc v + v = v + -v := by rw [← h]
      _ = 0 := add_neg_cancel v
  exact (smul_eq_zero.1 h').resolve_left h2

section Involution

variable {z : V →ₗ[F] V}

theorem sub_mem_eNeg (hzz : ∀ v, z (z v) = v) (v : V) : z v - v ∈ eNeg z := by
  rw [mem_eNeg, map_sub, hzz, neg_sub]

theorem add_mem_ePos (hzz : ∀ v, z (z v) = v) (v : V) : z v + v ∈ ePos z := by
  rw [mem_ePos, map_add, hzz, add_comm]

theorem eNeg_inf_ePos (h2 : (2 : F) ≠ 0) : eNeg z ⊓ ePos z = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_eNeg, mem_ePos] at hv
  exact (Submodule.mem_bot F).2 (eq_zero_of_eq_neg h2 (hv.2.symm.trans hv.1))

theorem eNeg_sup_ePos (hzz : ∀ v, z (z v) = v) (h2 : (2 : F) ≠ 0) : eNeg z ⊔ ePos z = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : (2 : F)⁻¹ • (z v + v) - (2 : F)⁻¹ • (z v - v) = v := by
    have : (2 : F)⁻¹ • (z v + v) - (2 : F)⁻¹ • (z v - v) = (2 : F)⁻¹ • ((2 : F) • v) := by
      rw [← smul_sub, two_smul]
      congr 1
      abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [← hv]
  exact Submodule.sub_mem _
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (add_mem_ePos hzz v)))
    (Submodule.mem_sup_left (Submodule.smul_mem _ _ (sub_mem_eNeg hzz v)))

variable [FiniteDimensional F V]

theorem finrank_eNeg_add (hzz : ∀ v, z (z v) = v) (h2 : (2 : F) ≠ 0) :
    finrank F (eNeg z) + finrank F (ePos z) = finrank F V := by
  have := Submodule.finrank_sup_add_finrank_inf_eq (eNeg z) (ePos z)
  rw [eNeg_sup_ePos hzz h2, eNeg_inf_ePos h2, finrank_top, finrank_bot, add_zero] at this
  exact this.symm

theorem det_eq_neg_one_pow (hzz : ∀ v, z (z v) = v) :
    LinearMap.det z = (-1) ^ finrank F (eNeg z) := by
  have hinv : eNeg z ≤ (eNeg z).comap z := fun v hv =>
    mem_eNeg_of_comm (fun _ => rfl) hv
  rw [LinearMap.det_eq_det_mul_det (eNeg z) z hinv]
  have h1 : z.restrict (p := eNeg z) (q := eNeg z) hinv = (-1 : F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, mem_eNeg.1 v.2, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_smul, neg_one_smul]
  have h2 : (eNeg z).mapQ (eNeg z) z hinv = LinearMap.id := by
    refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun v => ?_
    rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
    exact sub_mem_eNeg hzz v
  rw [h1, h2, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

theorem finrank_eNeg (hV : finrank F V = 3) (h2 : (2 : F) ≠ 0) (hzz : ∀ v, z (z v) = v)
    (hz1 : z ≠ LinearMap.id) (hdet : LinearMap.det z = 1) : finrank F (eNeg z) = 2 := by
  have hadd := finrank_eNeg_add hzz h2
  have hd := det_eq_neg_one_pow hzz
  rw [hdet] at hd
  have hneg := neg_one_ne_one h2
  obtain ⟨d, hdd⟩ : ∃ d, finrank F (eNeg z) = d := ⟨_, rfl⟩
  rw [hdd] at hd hadd ⊢
  have hle : d ≤ 3 := by omega
  interval_cases d
  · exfalso
    apply hz1
    have htop : ePos z = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    refine LinearMap.ext fun v => ?_
    exact mem_ePos.1 (htop ▸ Submodule.mem_top)
  · exact (hneg ((pow_one (-1 : F)).symm.trans hd.symm)).elim
  · rfl
  · exact (hneg ((by ring : (-1 : F) = (-1) ^ 3).trans hd.symm)).elim

end Involution

section Perfect

variable [FiniteDimensional F V] {P : Subgroup (LinearMap.GeneralLinearGroup F V)}
  {z : LinearMap.GeneralLinearGroup F V}

omit [FiniteDimensional F V] in
theorem comm_apply {g h : LinearMap.GeneralLinearGroup F V} (hgh : g * h = h * g) (v : V) :
    (g : V →ₗ[F] V) ((h : V →ₗ[F] V) v) = (h : V →ₗ[F] V) ((g : V →ₗ[F] V) v) := by
  have := congrArg (fun k : LinearMap.GeneralLinearGroup F V => (k : V →ₗ[F] V) v) hgh
  simpa using this

omit [FiniteDimensional F V] in
theorem apply_apply_of_mul_self (hzz : z * z = 1) (v : V) :
    (z : V →ₗ[F] V) ((z : V →ₗ[F] V) v) = v := by
  have := congrArg (fun k : LinearMap.GeneralLinearGroup F V => (k : V →ₗ[F] V) v) hzz
  simpa using this

theorem eq_bot_or_eq_eNeg (h2 : (2 : F) ≠ 0) (hP : ⁅P, P⁆ = P) (hzP : z ∈ P)
    (hdim : finrank F (eNeg (z : V →ₗ[F] V)) = 2) (D : Submodule F V)
    (hDE : D ≤ eNeg (z : V →ₗ[F] V)) (hDinv : ∀ g ∈ P, ∀ d ∈ D, (g : V →ₗ[F] V) d ∈ D) :
    D = ⊥ ∨ D = eNeg (z : V →ₗ[F] V) := by
  have hle : finrank F D ≤ 2 := hdim ▸ Submodule.finrank_mono hDE
  obtain ⟨d, hd⟩ : ∃ d, finrank F D = d := ⟨_, rfl⟩
  rw [hd] at hle
  have hbot : ∀ g : LinearMap.GeneralLinearGroup F V, ∀ a ∈ (⊥ : Submodule F V),
      (g : V →ₗ[F] V) a ∈ (⊥ : Submodule F V) := fun g a ha => by
    rw [(Submodule.mem_bot F).1 ha, map_zero]
    exact Submodule.zero_mem _
  interval_cases d
  · exact Or.inl (Submodule.finrank_eq_zero.1 hd)
  · exfalso
    have hsc : ∀ g ∈ P, ∃ α : F, ∀ b ∈ D, (g : V →ₗ[F] V) b = α • b := fun g hg => by
      obtain ⟨α, hα⟩ := exists_scalar_of_finrank_succ (A := ⊥) (B := D) bot_le
        (by rw [finrank_bot, hd]) (hbot g) (hDinv g hg)
      exact ⟨α, fun b hb => sub_eq_zero.1 ((Submodule.mem_bot F).1 (hα b hb))⟩
    have hfix : ∀ b ∈ D, (z : V →ₗ[F] V) b - b ∈ (⊥ : Submodule F V) := fun b hb =>
      sub_mem_of_commute_mod hP (A := ⊥) (B := D) hDinv (fun g _ => hbot g)
        (fun g hg h hh b hb => by
          obtain ⟨α, hα⟩ := hsc g hg
          obtain ⟨β, hβ⟩ := hsc h hh
          have e1 : (g : V →ₗ[F] V) ((h : V →ₗ[F] V) b) = (β * α) • b := by
            rw [hβ b hb, map_smul, hα b hb, smul_smul]
          have e2 : (h : V →ₗ[F] V) ((g : V →ₗ[F] V) b) = (α * β) • b := by
            rw [hα b hb, map_smul, hβ b hb, smul_smul]
          rw [e1, e2, mul_comm, sub_self]
          exact Submodule.zero_mem _) hzP hb
    have hne : D ≠ ⊥ := fun h => by rw [h, finrank_bot] at hd; omega
    obtain ⟨b, hbD, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 : (z : V →ₗ[F] V) b = b := sub_eq_zero.1 ((Submodule.mem_bot F).1 (hfix b hbD))
    have h2' : (z : V →ₗ[F] V) b = -b := mem_eNeg.1 (hDE hbD)
    exact hb0 (eq_zero_of_eq_neg h2 (h1.symm.trans h2'))
  · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hDE (by rw [hd, hdim]))

theorem exists_scalar (h2 : (2 : F) ≠ 0) (hP : ⁅P, P⁆ = P) (hzP : z ∈ P)
    (hzc : ∀ g ∈ P, g * z = z * g) (hdim : finrank F (eNeg (z : V →ₗ[F] V)) = 2)
    {c : LinearMap.GeneralLinearGroup F V} (hcP : ∀ g ∈ P, c * g = g * c) :
    ∃ α : F, ∀ v ∈ eNeg (z : V →ₗ[F] V), (c : V →ₗ[F] V) v = α • v := by
  have hbot : ∀ a ∈ (⊥ : Submodule F V), (c : V →ₗ[F] V) a ∈ (⊥ : Submodule F V) := fun a ha => by
    rw [(Submodule.mem_bot F).1 ha, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨α, hα⟩ := exists_scalar_of_irreducible_segment hP (A := ⊥) (B := eNeg (z : V →ₗ[F] V))
    bot_le (Or.inl (by rw [finrank_bot, hdim]))
    (fun g hg b hb => mem_eNeg_of_comm (comm_apply (hzc g hg)) hb)
    (fun g _ a ha => by
      rw [(Submodule.mem_bot F).1 ha, map_zero]
      exact Submodule.zero_mem _)
    (fun D _ hDE hDinv => eq_bot_or_eq_eNeg h2 hP hzP hdim D hDE hDinv)
    (fun b hb => mem_eNeg_of_comm (comm_apply (hcP z hzP)) hb) hbot
    (fun g hg v => comm_apply (hcP g hg) v)
  exact ⟨α, fun v hv => sub_eq_zero.1 ((Submodule.mem_bot F).1 (hα v hv))⟩

theorem eq_one_of_scalar_eq_one (hV : finrank F V = 3) (h2 : (2 : F) ≠ 0) (hzz : z * z = 1)
    (hdim : finrank F (eNeg (z : V →ₗ[F] V)) = 2) {c : LinearMap.GeneralLinearGroup F V}
    (hcz : c * z = z * c) (hdet : LinearMap.det (c : V →ₗ[F] V) = 1)
    (hc1 : ∀ v ∈ eNeg (z : V →ₗ[F] V), (c : V →ₗ[F] V) v = v) : c = 1 := by
  set E := eNeg (z : V →ₗ[F] V) with hE
  have hzz' := apply_apply_of_mul_self hzz
  have hinv : E ≤ E.comap (c : V →ₗ[F] V) := fun v hv =>
    mem_eNeg_of_comm (comm_apply hcz) hv
  obtain ⟨β, hβ⟩ := exists_scalar_of_finrank_succ (A := E) (B := ⊤) le_top
    (by rw [finrank_top, hV, hdim]) (f := (c : V →ₗ[F] V)) hinv (fun _ _ => Submodule.mem_top)
  have hQ : finrank F (V ⧸ E) = 1 := by
    have := Submodule.finrank_quotient_add_finrank E
    omega
  have hr : (c : V →ₗ[F] V).restrict (p := E) (q := E) hinv = LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, hc1 v v.2, LinearMap.id_apply]
  have hq : E.mapQ E (c : V →ₗ[F] V) hinv = β • LinearMap.id := by
    refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun v => ?_
    rw [Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hβ v Submodule.mem_top
  have hd := LinearMap.det_eq_det_mul_det E (c : V →ₗ[F] V) hinv
  rw [hr, hq, LinearMap.det_id, LinearMap.det_smul, LinearMap.det_id, hQ, pow_one, mul_one,
    one_mul, hdet] at hd
  have hpos : ∀ v ∈ ePos (z : V →ₗ[F] V), (c : V →ₗ[F] V) v = v := by
    intro v hv
    have h1 : (c : V →ₗ[F] V) v - v ∈ E := by
      have := hβ v Submodule.mem_top
      rwa [← hd, one_smul] at this
    have h2' : (c : V →ₗ[F] V) v - v ∈ ePos (z : V →ₗ[F] V) :=
      Submodule.sub_mem _ (mem_ePos_of_comm (comm_apply hcz) hv) hv
    have h3 : (c : V →ₗ[F] V) v - v ∈ E ⊓ ePos (z : V →ₗ[F] V) := ⟨h1, h2'⟩
    rw [eNeg_inf_ePos h2] at h3
    exact sub_eq_zero.1 ((Submodule.mem_bot F).1 h3)
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ E ⊔ ePos (z : V →ₗ[F] V) := by
    rw [eNeg_sup_ePos hzz' h2]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hc1 a ha, hpos b hb]
  rfl

theorem exists_injective_hom (hV : finrank F V = 3) (h2 : (2 : F) ≠ 0) (hP : ⁅P, P⁆ = P)
    (hzP : z ∈ P) (hzz : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ g ∈ P, g * z = z * g)
    (hdetz : LinearMap.det (z : V →ₗ[F] V) = 1) (C : Subgroup (LinearMap.GeneralLinearGroup F V))
    (hC : ∀ c ∈ C, LinearMap.det (c : V →ₗ[F] V) = 1 ∧ ∀ g ∈ P, c * g = g * c) :
    ∃ α : ↥C →* Fˣ, Function.Injective α ∧ ∀ (c : ↥C), ∀ v ∈ eNeg (z : V →ₗ[F] V),
      ((c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v = ((α c : Fˣ) : F) • v := by
  classical
  have hzz' := apply_apply_of_mul_self hzz
  have hz1' : (z : V →ₗ[F] V) ≠ LinearMap.id := fun h => hz1 (Units.ext h)
  have hdim := finrank_eNeg hV h2 hzz' hz1' hdetz
  set E := eNeg (z : V →ₗ[F] V) with hE
  have hEne : E ≠ ⊥ := fun h => by rw [h, finrank_bot] at hdim; omega
  obtain ⟨v₀, hv₀E, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hEne
  have huniq : ∀ {c : V →ₗ[F] V} {a b : F}, (∀ v ∈ E, c v = a • v) → (∀ v ∈ E, c v = b • v) →
      a = b := fun ha hb => by
    have h := (ha v₀ hv₀E).symm.trans (hb v₀ hv₀E)
    rw [← sub_eq_zero, ← sub_smul] at h
    exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_right hv₀)
  have hex : ∀ c : ↥C, ∃ a : F, ∀ v ∈ E,
      ((c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v = a • v := fun c =>
    exists_scalar h2 hP hzP hzc hdim (hC c c.2).2
  let φ : ↥C →* F :=
    { toFun := fun c => Classical.choose (hex c)
      map_one' := huniq (Classical.choose_spec (hex 1)) fun v _ => by
        rw [one_smul]
        rfl
      map_mul' := fun c d => huniq (Classical.choose_spec (hex (c * d))) fun v hv => by
        show ((c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V)
          (((d : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v) = _
        rw [Classical.choose_spec (hex d) v hv, map_smul, Classical.choose_spec (hex c) v hv,
          smul_smul, mul_comm] }
  have hφ : ∀ (c : ↥C), ∀ v ∈ E, ((c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v =
      φ c • v := fun c => Classical.choose_spec (hex c)
  refine ⟨φ.toHomUnits, ?_, fun c v hv => hφ c v hv⟩
  refine (injective_iff_map_eq_one _).2 fun c hc => ?_
  have hc1 : φ c = 1 := by
    have := congrArg Units.val hc
    simpa using this
  apply Subtype.ext
  exact eq_one_of_scalar_eq_one hV h2 hzz hdim ((hC c c.2).2 z hzP) (hC c c.2).1
    fun v hv => by rw [hφ c v hv, hc1, one_smul]

end Perfect

theorem sigma_mul_eq_one (h2 : (2 : F) ≠ 0) {z : V →ₗ[F] V} (hzz : ∀ v, z (z v) = v)
    {h : V → V → F} (σ : F →+* F) (hadd : ∀ v w w', h v (w + w') = h v w + h v w')
    (hsmul : ∀ (a b : F) v w, h (a • v) (b • w) = σ a * b * h v w)
    (hnd : ∀ v, v ≠ 0 → ∃ w, h v w ≠ 0) (hz : ∀ v w, h (z v) (z w) = h v w)
    (hne : eNeg z ≠ ⊥) {c : V →ₗ[F] V} (hc : ∀ v w, h (c v) (c w) = h v w) {α : F}
    (hα : ∀ v ∈ eNeg z, c v = α • v) : σ α * α = 1 := by
  have horth : ∀ v ∈ eNeg z, ∀ w ∈ ePos z, h v w = 0 := by
    intro v hv w hw
    have h1 := hz v w
    rw [mem_eNeg.1 hv, mem_ePos.1 hw, ← neg_one_smul F v, ← one_smul F w, hsmul, map_neg,
      map_one, one_smul] at h1
    have h3 : h v w = -h v w := by
      calc h v w = -1 * 1 * h v w := h1.symm
        _ = -h v w := by ring
    exact eq_zero_of_eq_neg h2 h3
  obtain ⟨v₀, hv₀E, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw⟩ := hnd v₀ hv₀
  have hw' : w ∈ eNeg z ⊔ ePos z := by
    rw [eNeg_sup_ePos hzz h2]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw'
  rw [hadd, horth v₀ hv₀E b hb, add_zero] at hw
  have h1 := hc v₀ a
  rw [hα v₀ hv₀E, hα a ha, hsmul] at h1
  have h3 : (σ α * α - 1) * h v₀ a = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hw)

end CFSG.Quasithin.H13.L1293S
