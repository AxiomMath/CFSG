module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem lay_le (H : Subgroup G) : Lay H ≤ H := Subgroup.map_subtype_le _

theorem lay_conj_mem {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Lay H) :
    g * z * g⁻¹ ∈ Lay H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  haveI := CFSG.LocalCores.layer_characteristic (G := ↥H)
  exact Subgroup.Normal.conj_mem (layer ↥H).normal_of_characteristic z' hz' ⟨g, hg⟩

theorem lay_mem_nor {H : Subgroup G} {g : G} (hg : g ∈ H) : g ∈ Nor (Lay H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => lay_conj_mem hg hx, fun hx => ?_⟩
  have := lay_conj_mem (H.inv_mem hg) hx
  simpa [mul_assoc] using this

theorem comp_kill {N : Subgroup G} {M : Type*} [Group M] (e : N ≃* M)
    (hKF : ∀ φ : MulAut M, φ * φ = 1 → ∀ w : M, orderOf w = 3 → φ w = w → ∀ k : M, φ k = k →
      k ≠ 1 → Is2El k → ∃ c : M, φ c = c ∧ ¬ Is2El (c * k * c⁻¹ * k⁻¹))
    {σ w k : G} (hσN : σ ∈ Nor N) (hσ2 : σ * σ = 1) (hwN : w ∈ N) (hw3 : orderOf w = 3)
    (hσw : σ * w = w * σ) (hkN : k ∈ N) (hk1 : k ≠ 1) (hk2 : Is2El k) (hσk : σ * k = k * σ)
    (hcomm : ∀ c ∈ N, σ * c = c * σ → Is2El (c * k * c⁻¹ * k⁻¹)) : False := by
  let ρ := normAut N e
  let σ' : Nor N := ⟨σ, hσN⟩
  have hφ2 : ρ σ' * ρ σ' = 1 := by
    rw [← map_mul, show σ' * σ' = 1 from Subtype.ext hσ2, map_one]
  have hfixσ : ∀ x : N, σ * x = x * σ → ρ σ' (e x) = e x := by
    intro x hx
    refine (normAut_eq_self_iff N e σ' x).mpr ?_
    show σ * x * σ⁻¹ = x
    calc σ * x * σ⁻¹ = (x * σ) * σ⁻¹ := by rw [hx]
      _ = x := by group
  have hw3' : orderOf (e ⟨w, hwN⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hw3
  obtain ⟨c, hcfix, hcnot⟩ := hKF (ρ σ') hφ2 (e ⟨w, hwN⟩) hw3' (hfixσ ⟨w, hwN⟩ hσw)
    (e ⟨k, hkN⟩) (hfixσ ⟨k, hkN⟩ hσk)
    (fun h => hk1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
    (Is2El.map e.toMonoidHom (is2El_subtype (⟨k, hkN⟩ : N) hk2))
  set s : N := e.symm c with hs
  have hcs : e s = c := e.apply_symm_apply c
  have hsσ : σ * (s : G) * σ⁻¹ = s :=
    (normAut_eq_self_iff N e σ' s).mp (by rw [hcs]; exact hcfix)
  have hsσ' : σ * (s : G) = (s : G) * σ := by
    calc σ * (s : G) = (σ * s * σ⁻¹) * σ := by group
      _ = s * σ := by rw [hsσ]
  have hsk : (s : G) * k * (s : G)⁻¹ * k⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem s.2 hkN) (N.inv_mem s.2)) (N.inv_mem hkN)
  have hw := is2El_subtype (⟨(s : G) * k * (s : G)⁻¹ * k⁻¹, hsk⟩ : N) (hcomm s s.2 hsσ')
  have hw' := Is2El.map e.toMonoidHom hw
  have hEq : e.toMonoidHom ⟨(s : G) * k * (s : G)⁻¹ * k⁻¹, hsk⟩ =
      c * e ⟨k, hkN⟩ * c⁻¹ * (e ⟨k, hkN⟩)⁻¹ := by
    have h1 : (⟨(s : G) * k * (s : G)⁻¹ * k⁻¹, hsk⟩ : N) =
        s * ⟨k, hkN⟩ * s⁻¹ * ⟨k, hkN⟩⁻¹ := rfl
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1]
    simp [hcs]
  rw [hEq] at hw'
  exact hcnot hw'

theorem card_dvd_of_inf_trivial {H M D R : Subgroup G} (hMn : ∀ g ∈ H, ∀ z ∈ M, g * z * g⁻¹ ∈ M)
    (hMH : M ≤ H) (hRH : R ≤ H) (hDH : D ≤ H)
    (hHD : ∀ h ∈ H, ∃ c ∈ D, ∃ m ∈ M, h = c * m) (hRM : ∀ r ∈ R, r ∈ M → r = 1) :
    Nat.card R ∣ Nat.card D := by
  let M' : Subgroup ↥H := M.subgroupOf H
  haveI : M'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hMn g g.2 n hn
    simpa using this⟩
  let f : ↥R →* ↥H ⧸ M' := (QuotientGroup.mk' M').comp (Subgroup.inclusion hRH)
  let g : ↥D →* ↥H ⧸ M' := (QuotientGroup.mk' M').comp (Subgroup.inclusion hDH)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    have h1 : (Subgroup.inclusion hRH r) ∈ M' := (QuotientGroup.eq_one_iff _).mp hr
    have h2 : (r : G) ∈ M := Subgroup.mem_subgroupOf.mp h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hRM r r.2 h2))
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, m, hm, hcm⟩ := hHD h h.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientGroup.mk (⟨c, hDH hc⟩ : ↥H) : ↥H ⧸ M') = QuotientGroup.mk h
    rw [QuotientGroup.eq]
    show ((⟨c, hDH hc⟩ : ↥H)⁻¹ * h) ∈ M'
    rw [Subgroup.mem_subgroupOf]
    have : (((⟨c, hDH hc⟩ : ↥H)⁻¹ * h : H) : G) = m := by
      simp [hcm]
    rw [this]; exact hm
  exact (Subgroup.card_dvd_of_injective f hf).trans (Subgroup.card_dvd_of_surjective hg)

end CFSG.RankThree.PartTwo.Sec21.FF79
