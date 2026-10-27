module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UPt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

section Glue1

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

theorem ob5_setup_of_c (c : S828Ctx T L I H h k) :
    Ob5PtSetup (ch82I (fsuV T I) h) (pCoreOf 2 (ch82I (fsuV T I) h)) (fsuV T I)
      (B6.conjSub h (fsuV T I)) (ch82U (fsuV T I) h) (ch82A (fsuV T I) h) (ch82B (fsuV T I) h) h := by
  classical
  set V := fsuV T I with hVdef
  set I' := ch82I V h with hI'def
  set P := pCoreOf 2 I' with hPdef
  set Vh := B6.conjSub h V with hVhdef
  set U := ch82U V h with hUdef
  set A := ch82A V h with hAdef
  set B := ch82B V h with hBdef
  have hI : ∀ x ∈ V, x ∈ I' := fun x hx => Subgroup.mem_sup_left hx
  have hUd : ∀ x, x ∈ U ↔ x ∈ V ∧ x ∈ Vh := by
    intro x
    rw [hUdef, c.hUZ]
    rfl
  have hPn : ∀ i ∈ I', ∀ p ∈ P, i * p * i⁻¹ ∈ P := fun i hi p hp =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hi) p).mp hp
  have hVh_mem : ∀ v ∈ V, h * v * h⁻¹ ∈ Vh := by
    intro v hv
    rw [hVhdef, B6.mem_conjSub]
    simpa [mul_assoc] using hv
  have hVh' : ∀ w ∈ Vh, ∃ v ∈ V, w = h * v * h⁻¹ := by
    intro w hw
    rw [hVhdef, B6.mem_conjSub] at hw
    refine ⟨h⁻¹ * w * h, hw, ?_⟩
    simp [mul_assoc]
  have hV2h : ∀ w ∈ Vh, w * w = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hVh' w hw
    have hv2 := c.hV.2 v hv
    rw [pow_two] at hv2
    calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hhI : h ∈ I' := c.hhI
  have hVhI : ∀ w ∈ Vh, w ∈ I' := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hVh' w hw
    exact I'.mul_mem (I'.mul_mem hhI (hI v hv)) (I'.inv_mem hhI)
  have hBV : ∀ x ∈ B, x ∈ V := fun x hx => ((Subgroup.mem_inf.mp hx).1)
  have hBP : ∀ x ∈ B, x ∈ P := fun x hx => ((Subgroup.mem_inf.mp hx).2)
  have hAVh : ∀ x ∈ A, x ∈ Vh := fun x hx => ((Subgroup.mem_inf.mp hx).1)
  have hAP : ∀ x ∈ A, x ∈ P := fun x hx => ((Subgroup.mem_inf.mp hx).2)
  have hVA : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ B := by
    intro v hv a ha
    have hmem : v * a * v⁻¹ * a⁻¹ ∈ ⁅V, A⁆ := Subgroup.commutator_mem_commutator hv ha
    have hBeq := c.hB
    rw [hBdef, hBeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
  have hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A := by
    intro b hb
    rw [hAdef, ch82A, Subgroup.mem_inf]
    refine ⟨hVh_mem b (hBV b hb), ?_⟩
    exact hPn h hhI b (hBP b hb)
  have hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B := by
    intro a ha
    have hav : h⁻¹ * a * h ∈ V := by
      have := hAVh a ha
      rw [hVhdef, B6.mem_conjSub] at this
      exact this
    refine Subgroup.mem_inf.mpr ⟨hav, ?_⟩
    have := hPn h⁻¹ (I'.inv_mem hhI) a (hAP a ha)
    simpa [mul_assoc] using this
  have hA5 : ∀ p ∈ P, (∀ w ∈ Vh, w * p * w⁻¹ * p⁻¹ ∈ U) → p ∈ A := by
    intro p hp hw
    have hp0 : h⁻¹ * p * h ∈ P := by
      have := hPn h⁻¹ (I'.inv_mem hhI) p hp
      simpa [mul_assoc] using this
    have hv0 : ∀ v ∈ V, v * (h⁻¹ * p * h) * v⁻¹ * (h⁻¹ * p * h)⁻¹ ∈ U := by
      intro v hv
      have h1 := hw (h * v * h⁻¹) (hVh_mem v hv)
      have e : h * v * h⁻¹ * p * (h * v * h⁻¹)⁻¹ * p⁻¹ =
          h * (v * (h⁻¹ * p * h) * v⁻¹ * (h⁻¹ * p * h)⁻¹) * h⁻¹ := by group
      rw [e] at h1
      have h2 := c.hcen _ h1 h⁻¹ (I'.inv_mem hhI)
      have e2 : h⁻¹ * (h * (v * (h⁻¹ * p * h) * v⁻¹ * (h⁻¹ * p * h)⁻¹) * h⁻¹) * h⁻¹⁻¹ =
          v * (h⁻¹ * p * h) * v⁻¹ * (h⁻¹ * p * h)⁻¹ := by group
      rw [e2] at h2
      rw [h2]
      exact h1
    have hpB : h⁻¹ * p * h ∈ B := c.hB5 _ hp0 hv0
    have := hhB _ hpB
    simpa [mul_assoc] using this
  exact
    { hhI := hhI
      hVI := hI
      hPn := hPn
      hVcomm := fun v hv w hw => by
        have := (inferInstance : IsMulCommutative ↥V).is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩
        exact congrArg Subtype.val this
      hV2 := fun v hv => by
        have := c.hV.2 v hv
        rw [pow_two] at this
        exact this
      hVh := hVh_mem
      hVh' := hVh'
      hV2h := hV2h
      hU := hUd
      hUB := fun u hu => c.hUB hu
      hUc := fun u hu i hi => c.hcen u hu i hi
      hBdef := fun x => Subgroup.mem_inf
      hAdef := fun x => Subgroup.mem_inf
      hPeq := c.hPeq
      hP2 := c.hP2
      hVA := hVA
      hhB := hhB
      hhA := hhA
      hB5 := fun p hp hw => c.hB5 p hp hw
      hA5 := hA5 }

end Glue1

end CFSG.Quasithin.H13
