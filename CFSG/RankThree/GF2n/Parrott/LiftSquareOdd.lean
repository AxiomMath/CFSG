module

public import CFSG.RankThree.GF2n.Parrott.LiftSquare

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem eq_one_of_odd_invariant (h : Tim79a.ParrottHyp z) {R : Subgroup G} (hRH : R ≤ H z)
    (hR : Odd (Nat.card R))
    (hRV : ∀ v : QuotientV.V z, (∀ (r : G) (hr : r ∈ R), conjV h ⟨r, hRH hr⟩ v = v) → v = 1)
    {X : Subgroup G} (hXJ : X ≤ J z) (hXR : ∀ r ∈ R, ∀ c ∈ X, r * c * r⁻¹ ∈ X)
    (φ : G → G) (hmul : ∀ c ∈ X, ∀ c' ∈ X, φ (c * c') = φ c * φ c')
    (hinv : ∀ r ∈ R, ∀ c ∈ X, φ (r * c * r⁻¹) = φ c) (hsq : ∀ c ∈ X, φ c * φ c = 1)
    (hker : ∀ c ∈ X, c ∈ centerIn (J z) → φ c = 1) : ∀ c ∈ X, φ c = 1 := by
  classical
  intro c hc
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  have _ : Fintype R := Fintype.ofFinite R
  let ρ : R →* MulAut (QuotientV.V z) := (conjV h).comp (Subgroup.inclusion hRH)
  have hρ : ∀ (r : R) (x : G) (hx : x ∈ J z),
      ρ r (QuotientV.pi z ⟨x, hx⟩) =
        QuotientV.pi z ⟨(r : G) * x * (r : G)⁻¹, H_conj_mem_J ⟨(r : G), hRH r.2⟩ hx⟩ :=
    fun r x hx => conjV_pi_conj h ⟨(r : G), hRH r.2⟩ hx
  have hφ1 : φ 1 = 1 := by
    have h1 := hmul 1 X.one_mem 1 X.one_mem
    rw [mul_one] at h1
    exact (mul_eq_left.mp h1.symm)
  have hnorm : ∀ S : Finset R, ∃ c' ∈ X, ∃ hc' : c' ∈ J z,
      QuotientV.pi z ⟨c', hc'⟩ = ∏ r ∈ S, ρ r (QuotientV.pi z ⟨c, hXJ hc⟩) ∧
        φ c' = φ c ^ S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, X.one_mem, (J z).one_mem, ?_, by simpa using hφ1⟩
      rw [Finset.prod_empty]
      exact map_one (QuotientV.pi z)
    | insert a S ha ih =>
      obtain ⟨c', hc'X, hc'J, hπ, hφ'⟩ := ih
      have hacX : (a : G) * c * (a : G)⁻¹ ∈ X := hXR a a.2 c hc
      refine ⟨((a : G) * c * (a : G)⁻¹) * c', X.mul_mem hacX hc'X,
        (J z).mul_mem (hXJ hacX) hc'J, ?_, ?_⟩
      · rw [Finset.prod_insert ha, hρ a c (hXJ hc), ← hπ]
        rfl
      · rw [hmul _ hacX _ hc'X, hinv a a.2 c hc, hφ', Finset.card_insert_of_notMem ha, pow_succ']
  obtain ⟨c', hc'X, hc'J, hπ, hφ'⟩ := hnorm Finset.univ
  have hfix : ∀ (r : G) (hr : r ∈ R), conjV h ⟨r, hRH hr⟩
      (∏ r' : R, ρ r' (QuotientV.pi z ⟨c, hXJ hc⟩)) =
        ∏ r' : R, ρ r' (QuotientV.pi z ⟨c, hXJ hc⟩) := by
    intro r hr
    have h1 : conjV h ⟨r, hRH hr⟩ = ρ ⟨r, hr⟩ := rfl
    rw [h1, map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨r, hr⟩ : R)) _ _ (fun r' => ?_)
    rw [← MulAut.mul_apply, ← map_mul]
    rfl
  have hone : QuotientV.pi z ⟨c', hc'J⟩ = 1 := by
    rw [hπ]
    exact hRV _ hfix
  have hφc' : φ c' = 1 := hker c' hc'X ((pi_eq_one_iff_mem_centerIn hc'J).mp hone)
  rw [hφ', Finset.card_univ, ← Nat.card_eq_fintype_card] at hφc'
  obtain ⟨k, hk⟩ := hR
  rw [hk, pow_succ, pow_mul] at hφc'
  have hsqc : φ c ^ 2 = 1 := by
    rw [pow_two]
    exact hsq c hc
  rw [hsqc, one_pow, one_mul] at hφc'
  exact hφc'

private noncomputable def fixPreimageJ (h : Tim79a.ParrottHyp z) (g : ↥(H z)) : Subgroup G :=
  ((autFixedSubgroup (conjV h g)).comap (QuotientV.pi z)).map (J z).subtype

private theorem mem_fixPreimageJ_iff (h : Tim79a.ParrottHyp z) (g : ↥(H z)) {c : G} :
    c ∈ fixPreimageJ h g ↔
      ∃ hc : c ∈ J z, conjV h g (QuotientV.pi z ⟨c, hc⟩) = QuotientV.pi z ⟨c, hc⟩ := by
  unfold fixPreimageJ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, mem_autFixedSubgroup.mp hx⟩
  · rintro ⟨hc, hfix⟩
    exact ⟨⟨c, hc⟩, mem_autFixedSubgroup.mpr hfix, rfl⟩

theorem mul_self_eq_of_sq_mem_centerIn_of_odd (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {s : G} (hsH : s ∈ H z) (hss : s * s ∈ J z)
    {R : Subgroup G} (hRH : R ≤ H z) (hR : Odd (Nat.card R)) (hRs : ∀ r ∈ R, r * s = s * r)
    (hRV : ∀ v : QuotientV.V z, (∀ (r : G) (hr : r ∈ R), conjV h ⟨r, hRH hr⟩ v = v) → v = 1) :
    ∀ j ∈ J z, (j * s) * (j * s) ∈ centerIn (J z) → (j * s) * (j * s) = (j * j) * (s * s) := by
  intro j hjJ hjs
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  have hinvV : ∀ v : QuotientV.V z, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  set S : ↥(H z) := ⟨s, hsH⟩ with hS
  have hssZ : s * s ∈ centerIn (J z) := by
    refine (pi_eq_one_iff_mem_centerIn hss).mp (hRV _ fun r hr => ?_)
    rw [conjV_pi_conj h ⟨r, hRH hr⟩ hss]
    congr 1
    apply Subtype.ext
    show r * (s * s) * r⁻¹ = s * s
    have h1 : r * (s * s) = (s * s) * r := by
      rw [← mul_assoc, hRs r hr, mul_assoc, hRs r hr, mul_assoc]
    rw [h1]
    group
  have hexp : (j * s) * (j * s) = (j * (s * j * s⁻¹)) * (s * s) := by group
  have hjsj : j * (s * j * s⁻¹) ∈ centerIn (J z) := by
    have h1 : j * (s * j * s⁻¹) = ((j * s) * (j * s)) * (s * s)⁻¹ := by
      rw [hexp]
      group
    rw [h1]
    exact Subgroup.mul_mem _ hjs (Subgroup.inv_mem _ hssZ)
  have hsjJ : s * j * s⁻¹ ∈ J z := H_conj_mem_J S hjJ
  have hjfix : conjV h S (QuotientV.pi z ⟨j, hjJ⟩) = QuotientV.pi z ⟨j, hjJ⟩ := by
    have h1 := (pi_eq_one_iff_mem_centerIn ((J z).mul_mem hjJ hsjJ)).mpr hjsj
    have h2 : QuotientV.pi z ⟨j, hjJ⟩ * QuotientV.pi z ⟨s * j * s⁻¹, hsjJ⟩ = 1 := by
      rw [← map_mul]
      exact h1
    rw [← conjV_pi_conj h S hjJ] at h2
    rw [eq_inv_of_mul_eq_one_right h2, hinvV]
  have hjX : j ∈ fixPreimageJ h S := (mem_fixPreimageJ_iff h S).mpr ⟨hjJ, hjfix⟩
  have hXJ : fixPreimageJ h S ≤ J z := fun c hc => ((mem_fixPreimageJ_iff h S).mp hc).1
  have hXR : ∀ r ∈ R, ∀ c ∈ fixPreimageJ h S, r * c * r⁻¹ ∈ fixPreimageJ h S := by
    intro r hr c hc
    obtain ⟨hcJ, hcfix⟩ := (mem_fixPreimageJ_iff h S).mp hc
    refine (mem_fixPreimageJ_iff h S).mpr ⟨H_conj_mem_J ⟨r, hRH hr⟩ hcJ, ?_⟩
    rw [← conjV_pi_conj h ⟨r, hRH hr⟩ hcJ]
    have hcomm : conjV h S * conjV h ⟨r, hRH hr⟩ = conjV h ⟨r, hRH hr⟩ * conjV h S := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (hRs r hr).symm
    calc conjV h S (conjV h ⟨r, hRH hr⟩ (QuotientV.pi z ⟨c, hcJ⟩))
        = (conjV h S * conjV h ⟨r, hRH hr⟩) (QuotientV.pi z ⟨c, hcJ⟩) := rfl
      _ = (conjV h ⟨r, hRH hr⟩ * conjV h S) (QuotientV.pi z ⟨c, hcJ⟩) := by rw [hcomm]
      _ = conjV h ⟨r, hRH hr⟩ (conjV h S (QuotientV.pi z ⟨c, hcJ⟩)) := rfl
      _ = conjV h ⟨r, hRH hr⟩ (QuotientV.pi z ⟨c, hcJ⟩) := by rw [hcfix]
  have hδZ : ∀ c ∈ fixPreimageJ h S, c⁻¹ * (s * c * s⁻¹) ∈ centerIn (J z) := by
    intro c hc
    obtain ⟨hcJ, hcfix⟩ := (mem_fixPreimageJ_iff h S).mp hc
    have hδJ : c⁻¹ * (s * c * s⁻¹) ∈ J z :=
      (J z).mul_mem ((J z).inv_mem hcJ) (H_conj_mem_J S hcJ)
    refine (pi_eq_one_iff_mem_centerIn hδJ).mp ?_
    have h1 : QuotientV.pi z ⟨c⁻¹ * (s * c * s⁻¹), hδJ⟩ =
        (QuotientV.pi z ⟨c, hcJ⟩)⁻¹ * conjV h S (QuotientV.pi z ⟨c, hcJ⟩) := by
      rw [conjV_pi_conj h S hcJ, ← map_inv, ← map_mul]
      rfl
    rw [h1, hcfix, inv_mul_cancel]
  have hmul : ∀ c ∈ fixPreimageJ h S, ∀ c' ∈ fixPreimageJ h S,
      (c * c')⁻¹ * (s * (c * c') * s⁻¹) = (c⁻¹ * (s * c * s⁻¹)) * (c'⁻¹ * (s * c' * s⁻¹)) := by
    intro c hc c' hc'
    have hc'J : c' ∈ J z := hXJ hc'
    have hcom : c'⁻¹ * (c⁻¹ * (s * c * s⁻¹)) = (c⁻¹ * (s * c * s⁻¹)) * c'⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hδZ c hc).2 c'⁻¹ ((J z).inv_mem hc'J)
    calc (c * c')⁻¹ * (s * (c * c') * s⁻¹)
        = c'⁻¹ * (c⁻¹ * (s * c * s⁻¹)) * (s * c' * s⁻¹) := by group
      _ = (c⁻¹ * (s * c * s⁻¹)) * c'⁻¹ * (s * c' * s⁻¹) := by rw [hcom]
      _ = (c⁻¹ * (s * c * s⁻¹)) * (c'⁻¹ * (s * c' * s⁻¹)) := by group
  have hinv : ∀ r ∈ R, ∀ c ∈ fixPreimageJ h S,
      (r * c * r⁻¹)⁻¹ * (s * (r * c * r⁻¹) * s⁻¹) = c⁻¹ * (s * c * s⁻¹) := by
    intro r hr c hc
    have hrδ : r * (c⁻¹ * (s * c * s⁻¹)) = (c⁻¹ * (s * c * s⁻¹)) * r :=
      Subgroup.mem_centralizer_iff.mp (hZ ▸ hδZ c hc).2 r (hRH hr)
    have hsr : s * r = r * s := (hRs r hr).symm
    have h1 : s * (r * c * r⁻¹) * s⁻¹ = r * (s * c * s⁻¹) * r⁻¹ := by
      calc s * (r * c * r⁻¹) * s⁻¹ = (s * r) * c * (s * r)⁻¹ := by group
        _ = (r * s) * c * (r * s)⁻¹ := by rw [hsr]
        _ = r * (s * c * s⁻¹) * r⁻¹ := by group
    calc (r * c * r⁻¹)⁻¹ * (s * (r * c * r⁻¹) * s⁻¹)
        = r * (c⁻¹ * (s * c * s⁻¹)) * r⁻¹ := by rw [h1]; group
      _ = c⁻¹ * (s * c * s⁻¹) := by rw [hrδ]; group
  have hδ := eq_one_of_odd_invariant h hRH hR hRV (X := fixPreimageJ h S) hXJ hXR
    (fun c => c⁻¹ * (s * c * s⁻¹)) hmul hinv
    (fun c hc => centerIn_J_sq h (hδZ c hc))
    (fun c hc hcZ => by
      have hsc : s * c = c * s := Subgroup.mem_centralizer_iff.mp (hZ ▸ hcZ).2 s hsH
      show c⁻¹ * (s * c * s⁻¹) = 1
      rw [hsc]
      group) j hjX
  have hsj : s * j * s⁻¹ = j := (inv_mul_eq_one.mp hδ).symm
  rw [hexp, hsj]

end CFSG.RankThree.GF2n.Parrott
