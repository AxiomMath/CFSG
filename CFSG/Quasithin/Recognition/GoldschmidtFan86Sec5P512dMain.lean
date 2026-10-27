module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512dData
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Four

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan512d (F : FanTree Γ G) (h62 : Fan62 F) (h53b : Fan53b F) (h54 : Fan54 F)
    (hcen : Fan512cen F) : Fan512d F := by
  intro h40 T z a hT hz hz1 hcore g α' hα'
  subst hα'
  have hzc : z ∈ Cinv G (T.line.vert (a + 1)) := hcen h40 T z a hT hz hz1 hcore
  have hz2 : z * z = 1 := hzc.2.1
  have huniq : ∀ zh ∈ Cinv G (T.line.vert (a + 1)), zh = z := by
    intro zh hzh
    by_contra hne
    have hzh2 : zh * zh = 1 := hzh.2.1
    have hcomm : z * zh = zh * z := hzh.2.2.2 z hzc.2.2.1
    have hw : z * zh ∈ Cinv G (T.line.vert (a + 1)) := by
      refine ⟨fun h1 => hne ?_, ?_, ⟨(MulAction.stabilizer G _).mul_mem hzc.2.2.1 hzh.2.2.1,
        fun h hh => ?_⟩⟩
      · have h2 := inv_eq_of_mul_eq_one_right h1
        rw [inv_eq_of_mul_eq_one_right hz2] at h2
        exact h2.symm
      · calc z * zh * (z * zh) = z * (zh * z) * zh := by group
          _ = z * (z * zh) * zh := by rw [hcomm]
          _ = (z * z) * (zh * zh) := by group
          _ = 1 := by rw [hz2, hzh2, one_mul]
      · calc h * (z * zh) = (h * z) * zh := by group
          _ = (z * h) * zh := by rw [hzc.2.2.2 h hh]
          _ = z * (h * zh) := by group
          _ = z * (zh * h) := by rw [hzh.2.2.2 h hh]
          _ = z * zh * h := by group
    have hfz := P512d.fixIdx_eq F h62 h53b h54 h40 T hT hzc
    have hfzh := P512d.fixIdx_eq F h62 h53b h54 h40 T hT hzh
    have hfw := P512d.fixIdx_eq F h62 h53b h54 h40 T hT hw
    have hfix := P55.z2_right F T.line (ρ := a + 5) hz2 hzh2
      ((hfz _).2 ⟨by omega, by omega⟩) ((hfz _).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hfz _).1 h; omega)
      ((hfzh _).2 ⟨by omega, by omega⟩) ((hfzh _).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hfzh _).1 h; omega)
    have := (hfw _).1 hfix
    omega
  ext w
  constructor
  · intro hw
    have hw' : g⁻¹ * w * g ∈ Cinv G (T.line.vert (a + 1)) := by
      have := (P512d.cinv_conj_iff g (T.line.vert (a + 1)) (g⁻¹ * w * g)).1
      rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at this
      exact this hw
    have h1 := huniq _ hw'
    show w = g * z * g⁻¹
    rw [← h1]
    group
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (P512d.cinv_conj_iff g _ z).2 hzc

end CFSG.Quasithin.Fan86
