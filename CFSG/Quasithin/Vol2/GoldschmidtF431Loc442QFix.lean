module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QXt

public section

namespace CFSG.Quasithin.Loc442Q

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u v

section Fixed

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

omit [Finite Mb] [Finite M] in
theorem mem_xt_of_cent (C : F431Comp M1 M2 b1 b2)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2) (ht1 : t ∈ M1)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) {k : M}
    (hkz : k * amalgamMap b1 b2 z = amalgamMap b1 b2 z * k)
    (hkt : k * amalgamMap b1 b2 t = amalgamMap b1 b2 t * k) : k ∈ xt b2 t := by
  obtain ⟨w, rfl⟩ := hb (Subgroup.mem_centralizer_singleton_iff.mpr hkz)
  rw [amalgamMap_of_mem₁ b1 b2 ht1, ← map_mul, ← map_mul] at hkt
  have hw : (w : Mb) * t = t * (w : Mb) := congrArg Subtype.val (C.inj₁ hkt)
  have hw2 : (w : Mb) ∈ M2 := cent_t (Subgroup.mem_centralizer_singleton_iff.mpr hw)
  exact mem_xt.mpr ⟨⟨w, hw2⟩, hw, (C.agree w w.2 hw2).symm⟩

omit [Finite Mb] [Finite M] in
theorem timg_inf_le_xt (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2) (ht : t ∈ I) :
    timg T b1 ⊓ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ xt b2 t := by
  rintro y ⟨hy, hyc⟩
  obtain ⟨w, hwT, rfl⟩ := mem_timg.mp hy
  have ht1 : t ∈ M1 := D.T_le₁ (D.mem_T t ht)
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hyc
  rw [amalgamMap_of_mem₁ b1 b2 ht1, ← map_mul, ← map_mul] at hcomm
  have hw : (w : Mb) * t = t * (w : Mb) := congrArg Subtype.val (C.inj₁ hcomm)
  have hw2 : (w : Mb) ∈ M2 := D.T_le₂ hwT
  exact mem_xt.mpr ⟨⟨w, hw2⟩, hw, (C.agree w w.2 hw2).symm⟩

theorem loc442Q_unique_fixed_of_hnfI (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (ht : t ∈ I) (hzt : z * t = t * z) (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) {g : M}
    (hg : g * amalgamMap b1 b2 t = amalgamMap b1 b2 t * g)
    (hu : g⁻¹ * amalgamMap b1 b2 z * g ∈ xt b2 t) : g ∈ xt b2 t := by
  have hzT : z ∈ T := D.mem_T z D.z_mem
  have hz2 : z ∈ M2 := D.T_le₂ hzT
  have ht1 : t ∈ M1 := D.T_le₁ (D.mem_T t ht)
  have ht2 : t ∈ M2 := D.T_le₂ (D.mem_T t ht)
  have hxtle := xt_le_centralizer (b1 := b1) C ht2
  have hSsub : {c : M | IsConj (amalgamMap b1 b2 z) c ∧ c ∈ xt b2 t} ⊆
      sig (amalgamMap b1 b2 t) (amalgamMap b1 b2 z) := fun c hc =>
    ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mp (hxtle hc.2)⟩
  have hsurj : Function.Surjective (OrbSet.map hxtle hSsub) := by
    intro u
    obtain ⟨c, rfl⟩ := OrbSet.mk_surjective u
    obtain ⟨m, hm, hmc⟩ := loc442Q_exists_conj D C hnfI ht hSylt hb c.2.1 c.2.2
    have hc0 : m⁻¹ * (c : M) * m ∈ xt b2 t := timg_inf_le_xt D C ht hmc
    refine ⟨OrbSet.mk ⟨m⁻¹ * (c : M) * m, c.2.1.trans (isConj_iff.mpr ⟨m⁻¹, by simp⟩), hc0⟩, ?_⟩
    rw [OrbSet.map_mk, OrbSet.mk_eq_mk]
    exact ⟨m⁻¹, (Subgroup.inv_mem _ hm), by group⟩
  have hinj := OrbSet.map_injective_of_surjective hxtle hSsub hsurj
    (card_orb_xt D C hnfI ht cent_z cent_t hb).le
  have hzX : amalgamMap b1 b2 z ∈ xt b2 t :=
    mem_xt.mpr ⟨⟨z, hz2⟩, hzt, (amalgamMap_of_mem₂ b1 b2 C.agree hz2).symm⟩
  obtain ⟨x, hx, hgx⟩ := hinj ⟨amalgamMap b1 b2 z, IsConj.refl _, hzX⟩
    ⟨g⁻¹ * amalgamMap b1 b2 z * g, isConj_iff.mpr ⟨g⁻¹, by simp⟩, hu⟩
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg, rfl⟩
  have hgx' : g⁻¹ * amalgamMap b1 b2 z * g = x⁻¹ * amalgamMap b1 b2 z * x := hgx
  have hxinv : x⁻¹ ∈ xt b2 t := (xt b2 t).inv_mem hx
  have hxc' : x⁻¹ * amalgamMap b1 b2 t = amalgamMap b1 b2 t * x⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp (hxtle hxinv)
  have hk : g * x⁻¹ ∈ xt b2 t := by
    refine mem_xt_of_cent C cent_t ht1 hb ?_ ?_
    · calc g * x⁻¹ * amalgamMap b1 b2 z
          = g * (x⁻¹ * amalgamMap b1 b2 z * x) * x⁻¹ := by group
        _ = g * (g⁻¹ * amalgamMap b1 b2 z * g) * x⁻¹ := by rw [hgx']
        _ = amalgamMap b1 b2 z * (g * x⁻¹) := by group
    · calc g * x⁻¹ * amalgamMap b1 b2 t = g * (x⁻¹ * amalgamMap b1 b2 t) := by group
        _ = g * (amalgamMap b1 b2 t * x⁻¹) := by rw [hxc']
        _ = (g * amalgamMap b1 b2 t) * x⁻¹ := by group
        _ = (amalgamMap b1 b2 t * g) * x⁻¹ := by rw [hg]
        _ = amalgamMap b1 b2 t * (g * x⁻¹) := by group
  have := (xt b2 t).mul_mem hk hx
  simpa using this

theorem loc442Q_unique_fixed (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I) (hzt : z * t = t * z)
    (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {g : M}
    (hg : g * amalgamMap b1 b2 t = amalgamMap b1 b2 t * g)
    (hu : g⁻¹ * amalgamMap b1 b2 z * g ∈ xt b2 t) : g ∈ xt b2 t :=
  loc442Q_unique_fixed_of_hnfI D C (hnfI_of_zt hI hnf) ht hzt cent_z cent_t hSylt hb hg hu

end Fixed

end CFSG.Quasithin.Loc442Q
