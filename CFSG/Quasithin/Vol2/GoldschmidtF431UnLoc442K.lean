module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442J
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QFix
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocDatum

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.Loc442Q

universe u

section Main


variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem loc442U (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I) (hzt : z * t = t * z)
    (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t))
    {Vb Ub Rb Kb : Subgroup Mb} (Lie : UnLoc442Lie T z t Vb Ub Rb Kb) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range := by
  have hzT : z ∈ T := D.mem_T z D.z_mem
  have hz2 : z ∈ M2 := D.T_le₂ hzT
  have ht2 : t ∈ M2 := D.T_le₂ (D.mem_T t ht)
  have hVM : Vb ≤ M2 := Lie.V_le.trans cent_t
  have hUM : Ub ≤ M2 := Lie.U_le.trans hVM
  have hRM : Rb ≤ M2 := Lie.R_le.trans hVM
  have hKM : Kb ≤ M2 := Lie.K_le.trans cent_t
  have hxt : xt b2 t = subImg b2 (Subgroup.centralizer ({t} : Set Mb)) := rfl
  have hz' : amalgamMap b1 b2 z = b2 ⟨z, hz2⟩ := amalgamMap_of_mem₂ b1 b2 C.agree hz2
  have hXY : xt b2 t ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) :=
    xt_le_centralizer C ht2
  have hzP : z ∈ T ⊓ Subgroup.centralizer ({t} : Set Mb) :=
    ⟨hzT, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩
  have core : Loc442UCore (xt b2 t) (Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M))
      (subImg b2 Vb) (subImg b2 Ub) (subImg b2 Rb) (subImg b2 Kb)
      (subImg b2 (T ⊓ Subgroup.centralizer ({t} : Set Mb))) (amalgamMap b1 b2 z)
      (amalgamMap b1 b2 t) :=
    { XY := hXY
      t_cent := fun y hy => Subgroup.mem_centralizer_singleton_iff.mp hy
      t_U := by
        rw [amalgamMap_of_mem₂ b1 b2 C.agree ht2]
        exact mem_subImg_of_mem b2 ht2 Lie.t_U
      H1 := by
        intro x hx g hg hgx
        have hg' : x⁻¹ * g ∈ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXY hx)) hg
        have hu' : (x⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * (x⁻¹ * g) ∈ xt b2 t := by
          have : (x⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * (x⁻¹ * g) =
              g⁻¹ * (x * amalgamMap b1 b2 z * x⁻¹) * g := by group
          rw [this]
          exact hgx
        have h2 := (xt b2 t).mul_mem hx (loc442Q_unique_fixed D C hI ht hzt cent_z cent_t hSylt
          hb hnf (Subgroup.mem_centralizer_singleton_iff.mp hg') hu')
        simpa using h2
      P_X := subImg_mono b2 inf_le_right
      P_syl := isSylowTwoOf_subImg C.inj₂ inf_le_right cent_t hSylt
      z_P := by
        rw [hz']
        exact mem_subImg_of_mem b2 hz2 hzP
      P_z := by
        intro y hy
        obtain ⟨y₀, hy₀M, hy₀P, rfl⟩ := mem_subImg.mp hy
        rw [hz', ← map_mul, ← map_mul]
        exact congrArg b2 (Subtype.ext (Lie.z_cent y₀ hy₀P.1))
      P_U := by
        intro y hy u hu
        obtain ⟨y₀, hy₀M, hy₀P, rfl⟩ := mem_subImg.mp hy
        obtain ⟨u₀, hu₀M, hu₀U, rfl⟩ := mem_subImg.mp hu
        rw [← map_mul, ← map_mul]
        exact congrArg b2 (Subtype.ext (Lie.P_U y₀ hy₀P u₀ hu₀U))
      V_X := subImg_mono b2 Lie.V_le
      V_norm := fun x hx v hv => (Subgroup.mem_normalizer_iff.mp (subImg_le_normalizer b2
        (le_normalizer_of_conj Lie.V_norm) hx) v).mp hv
      V_ab := subImg_comm Lie.V_ab
      V_sq := subImg_sq Lie.V_sq
      U_V := subImg_mono b2 Lie.U_le
      U_norm := fun x hx u hu => (Subgroup.mem_normalizer_iff.mp (subImg_le_normalizer b2
        (le_normalizer_of_conj Lie.U_norm) hx) u).mp hu
      K_X := subImg_mono b2 Lie.K_le
      K_perf := by rw [subImg_commutator hKM, Lie.K_perf]
      V_K := subImg_mono b2 Lie.V_K
      K_cent := by
        intro k hk u hu
        obtain ⟨k₀, hk₀M, hk₀K, rfl⟩ := mem_subImg.mp hk
        obtain ⟨u₀, hu₀M, hu₀U, rfl⟩ := mem_subImg.mp hu
        rw [← map_mul, ← map_mul]
        exact congrArg b2 (Subtype.ext (Lie.K_cent k₀ hk₀K u₀ hu₀U))
      coset := by
        intro v hv hvU
        obtain ⟨v₀, hv₀M, hv₀V, rfl⟩ := mem_subImg.mp hv
        have hv₀U : v₀ ∉ Ub := fun h => hvU (mem_subImg_of_mem b2 hv₀M h)
        obtain ⟨x, hx, u, hu, hvx⟩ := Lie.coset v₀ hv₀V hv₀U
        have hxM : x ∈ M2 := cent_t hx
        have huM : u ∈ M2 := hUM hu
        refine ⟨b2 ⟨x, hxM⟩, mem_xt.2 ⟨⟨x, hxM⟩, Subgroup.mem_centralizer_singleton_iff.1 hx, rfl⟩,
          b2 ⟨u, huM⟩, mem_subImg_of_mem b2 huM hu, ?_⟩
        have h1 : (⟨v₀, hv₀M⟩ : ↥M2) = ⟨x, hxM⟩ * ⟨z, hz2⟩ * ⟨x, hxM⟩⁻¹ * ⟨u, huM⟩ :=
          Subtype.ext hvx
        rw [h1, map_mul, map_mul, map_mul, map_inv, hz']
      nonsolv := nonsolv_img C.inj₂ cent_t hVM Lie.nonsolv
      R_V := subImg_mono b2 Lie.R_le
      R_two := by
        obtain ⟨a, ha, c, hc, ha1, hc1, hac⟩ := Lie.R_two
        exact ⟨b2 ⟨a, hRM ha⟩, mem_subImg_of_mem b2 (hRM ha) ha, b2 ⟨c, hRM hc⟩,
          mem_subImg_of_mem b2 (hRM hc) hc, img_ne_one C.inj₂ (hRM ha) ha1,
          img_ne_one C.inj₂ (hRM hc) hc1, fun h => hac ((img_eq_iff C.inj₂ (hRM ha) (hRM hc)).mp h)⟩
      R_cls := by
        intro r hr hr1
        obtain ⟨r₀, hr₀M, hr₀R, rfl⟩ := mem_subImg.mp hr
        have hr₀1 : r₀ ≠ 1 := fun h => hr1 (by subst h; exact map_one b2)
        obtain ⟨x, hx, hrx⟩ := Lie.R_cls r₀ hr₀R hr₀1
        have hxM : x ∈ M2 := cent_t hx
        refine ⟨b2 ⟨x, hxM⟩, mem_xt.2 ⟨⟨x, hxM⟩, Subgroup.mem_centralizer_singleton_iff.1 hx, rfl⟩,
          ?_⟩
        have h1 : (⟨r₀, hr₀M⟩ : ↥M2) = ⟨x, hxM⟩ * ⟨z, hz2⟩ * ⟨x, hxM⟩⁻¹ := Subtype.ext hrx
        rw [h1, map_mul, map_mul, map_inv, hz']
      R_U := by
        intro r hr hrU
        obtain ⟨r₀, hr₀M, hr₀R, rfl⟩ := mem_subImg.mp hr
        obtain ⟨u₀, hu₀M, hu₀U, hu⟩ := mem_subImg.mp hrU
        have hur : u₀ = r₀ := (img_eq_iff C.inj₂ hu₀M hr₀M).mp hu
        have h0 := Lie.R_U r₀ hr₀R (by rw [← hur]; exact hu₀U)
        subst h0
        exact map_one b2 }
  intro y hy
  obtain ⟨x, -, rfl⟩ := mem_xt.mp (core.le hy)
  exact ⟨x, rfl⟩

end Main

end CFSG.Quasithin.H13.F431.Un
