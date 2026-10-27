module

public import CFSG.Quasithin.Recognition.RuTypeJ47Cert
public import CFSG.Quasithin.Recognition.RuTypeJ47a
public import CFSG.Quasithin.Background.F3

public section

namespace CFSG.Quasithin.RuType.J47

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits

section Hom

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

@[expose] noncomputable def phi1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : ↥twoF4H ≃* ↥F1 := e.φ1

@[expose] noncomputable def phi2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : ↥twoF4N ≃* ↥F2 := e.φ2

@[expose] noncomputable def phi12
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : ↥(twoF4H ⊓ twoF4N) ≃* ↥(F1 ⊓ F2) := e.φ12

@[expose] noncomputable def hom1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : ↥twoF4H →* G :=
  F1.subtype.comp (phi1 e).toMonoidHom

@[expose] noncomputable def hom2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : ↥twoF4N →* G :=
  F2.subtype.comp (phi2 e).toMonoidHom

theorem hom1_apply
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4H) : hom1 e x = ((phi1 e x : ↥F1) : G) := rfl

theorem hom2_apply
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4N) : hom2 e x = ((phi2 e x : ↥F2) : G) := rfl

theorem phi12_eq_phi1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (g : ↥(twoF4H ⊓ twoF4N)) :
    ((phi12 e g : ↥(F1 ⊓ F2)) : G) =
      ((phi1 e ⟨(g : Equiv.Perm (Fin 1755)), (Subgroup.mem_inf.mp g.2).1⟩ : ↥F1) : G) :=
  congrArg Subtype.val (e.comm1 g)

theorem phi12_eq_phi2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (g : ↥(twoF4H ⊓ twoF4N)) :
    ((phi12 e g : ↥(F1 ⊓ F2)) : G) =
      ((phi2 e ⟨(g : Equiv.Perm (Fin 1755)), (Subgroup.mem_inf.mp g.2).2⟩ : ↥F2) : G) :=
  congrArg Subtype.val (e.comm2 g)

theorem hom1_injective
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : Function.Injective (hom1 e) :=
  F1.subtype_injective.comp (phi1 e).injective

theorem hom2_injective
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : Function.Injective (hom2 e) :=
  F2.subtype_injective.comp (phi2 e).injective

theorem hom1_mem
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4H) : hom1 e x ∈ F1 :=
  (phi1 e x).2

theorem hom2_mem
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4N) : hom2 e x ∈ F2 :=
  (phi2 e x).2

theorem exists_hom1_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {g : G} (hg : g ∈ F1) : ∃ x : ↥twoF4H, hom1 e x = g :=
  ⟨(phi1 e).symm ⟨g, hg⟩, by rw [hom1_apply, MulEquiv.apply_symm_apply]⟩

theorem hom1_eq_hom2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {x : Equiv.Perm (Fin 1755)} (h1 : x ∈ twoF4H) (h2 : x ∈ twoF4N) :
    hom1 e ⟨x, h1⟩ = hom2 e ⟨x, h2⟩ := by
  rw [hom1_apply, hom2_apply, ← phi12_eq_phi1 e ⟨x, Subgroup.mem_inf.mpr ⟨h1, h2⟩⟩,
    phi12_eq_phi2 e ⟨x, Subgroup.mem_inf.mpr ⟨h1, h2⟩⟩]

theorem mem_N_of_hom1_mem_F2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4H) (hx : hom1 e x ∈ F2) : (x : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
  set g := (phi12 e).symm ⟨hom1 e x, Subgroup.mem_inf.mpr ⟨hom1_mem e x, hx⟩⟩ with hg
  have h1 := phi12_eq_phi1 e g
  have h2 : phi12 e g = ⟨hom1 e x, Subgroup.mem_inf.mpr ⟨hom1_mem e x, hx⟩⟩ := by
    rw [hg, MulEquiv.apply_symm_apply]
  rw [h2] at h1
  have hxs : x = ⟨(g : Equiv.Perm (Fin 1755)), (Subgroup.mem_inf.mp g.2).1⟩ := by
    apply hom1_injective e
    rw [hom1_apply, hom1_apply]
    exact h1
  rw [hxs]
  exact (Subgroup.mem_inf.mp g.2).2

end Hom

section Conj

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

theorem coe_conj {K : Subgroup (Equiv.Perm (Fin 1755))} (a x : ↥K) :
    ((a * x * a⁻¹ : ↥K) : Equiv.Perm (Fin 1755)) =
      (a : Equiv.Perm (Fin 1755)) * x * (a : Equiv.Perm (Fin 1755))⁻¹ := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem coe_conjInv {K : Subgroup (Equiv.Perm (Fin 1755))} (a x : ↥K) :
    ((a⁻¹ * x * a : ↥K) : Equiv.Perm (Fin 1755)) = (a : Equiv.Perm (Fin 1755))⁻¹ * x * a := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem hom1_conj
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (a x : ↥twoF4H) :
    hom1 e a * hom1 e x * (hom1 e a)⁻¹ = hom1 e (a * x * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem hom1_conjInv
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (a x : ↥twoF4H) :
    (hom1 e a)⁻¹ * hom1 e x * hom1 e a = hom1 e (a⁻¹ * x * a) := by
  rw [map_mul, map_mul, map_inv]

theorem hom2_conj
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (a x : ↥twoF4N) :
    hom2 e a * hom2 e x * (hom2 e a)⁻¹ = hom2 e (a * x * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem hom2_conjInv
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (a x : ↥twoF4N) :
    (hom2 e a)⁻¹ * hom2 e x * hom2 e a = hom2 e (a⁻¹ * x * a) := by
  rw [map_mul, map_mul, map_inv]

theorem hom1_congr
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {x y : ↥twoF4H} (h : (x : Equiv.Perm (Fin 1755)) = y) : hom1 e x = hom1 e y :=
  congrArg _ (Subtype.ext h)

theorem hom2_congr
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {x y : ↥twoF4N} (h : (x : Equiv.Perm (Fin 1755)) = y) : hom2 e x = hom2 e y :=
  congrArg _ (Subtype.ext h)

theorem hom2_conjInv_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {a x : ↥twoF4N} {y : Equiv.Perm (Fin 1755)} (hyH : y ∈ twoF4H) (hyN : y ∈ twoF4N)
    (h : (a : Equiv.Perm (Fin 1755))⁻¹ * x * a = y) :
    (hom2 e a)⁻¹ * hom2 e x * hom2 e a = hom1 e ⟨y, hyH⟩ := by
  rw [hom2_conjInv, hom1_eq_hom2 e hyH hyN]
  exact hom2_congr e (by rw [coe_conjInv]; exact h)

theorem hom2_conj_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {a x : ↥twoF4N} {y : Equiv.Perm (Fin 1755)} (hyH : y ∈ twoF4H) (hyN : y ∈ twoF4N)
    (h : (a : Equiv.Perm (Fin 1755)) * x * (a : Equiv.Perm (Fin 1755))⁻¹ = y) :
    hom2 e a * hom2 e x * (hom2 e a)⁻¹ = hom1 e ⟨y, hyH⟩ := by
  rw [hom2_conj, hom1_eq_hom2 e hyH hyN]
  exact hom2_congr e (by rw [coe_conj]; exact h)

theorem hom1_conj_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {a x : ↥twoF4H} {y : Equiv.Perm (Fin 1755)} (hyH : y ∈ twoF4H) (hyN : y ∈ twoF4N)
    (h : (a : Equiv.Perm (Fin 1755)) * x * (a : Equiv.Perm (Fin 1755))⁻¹ = y) :
    hom1 e a * hom1 e x * (hom1 e a)⁻¹ = hom2 e ⟨y, hyN⟩ := by
  rw [hom1_conj, ← hom1_eq_hom2 e hyH hyN]
  exact hom1_congr e (by rw [coe_conj]; exact h)

theorem hom1_conjInv_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {a x : ↥twoF4H} {y : Equiv.Perm (Fin 1755)} (hyH : y ∈ twoF4H) (hyN : y ∈ twoF4N)
    (h : (a : Equiv.Perm (Fin 1755))⁻¹ * x * a = y) :
    (hom1 e a)⁻¹ * hom1 e x * hom1 e a = hom2 e ⟨y, hyN⟩ := by
  rw [hom1_conjInv, ← hom1_eq_hom2 e hyH hyN]
  exact hom1_congr e (by rw [coe_conjInv]; exact h)

end Conj

section Elements

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

@[expose] noncomputable def a1G
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom2 e ⟨a1P, a1P_mem_N⟩

@[expose] noncomputable def eG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom1 e ⟨eP, eP_mem_H⟩

@[expose] noncomputable def f2G
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom1 e ⟨f2P, f2P_mem_H⟩

@[expose] noncomputable def cG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom2 e ⟨cP, cP_mem_N⟩

@[expose] noncomputable def jG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := a1G e * eG e * (a1G e)⁻¹

@[expose] noncomputable def zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom1 e ⟨titsZ, twoF4S_le_twoF4H titsZ_mem_S⟩

@[expose] noncomputable def uG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom1 e ⟨uP, twoF4S_le_twoF4H uP_mem_S⟩

@[expose] noncomputable def bG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := hom1 e ⟨b0P, b0P_mem_H⟩

@[expose] noncomputable def g3G
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := a1G e * f2G e

@[expose] noncomputable def yG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : G := g3G e * cG e * (g3G e)⁻¹

theorem zG_eq_hom2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : zG e = hom2 e ⟨titsZ, twoF4S_le_twoF4N titsZ_mem_S⟩ :=
  hom1_eq_hom2 e _ _

theorem a1G_conjInv_zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : (a1G e)⁻¹ * zG e * a1G e = hom1 e ⟨v1P, twoF4S_le_twoF4H v1P_mem_S⟩ := by
  rw [zG_eq_hom2, a1G]
  exact hom2_conjInv_eq e _ (twoF4S_le_twoF4N v1P_mem_S) v1P_def.symm

theorem jG_conj_zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : jG e * zG e * (jG e)⁻¹ = uG e := by
  have h2 : eG e * hom1 e ⟨v1P, twoF4S_le_twoF4H v1P_mem_S⟩ * (eG e)⁻¹ =
      hom2 e ⟨v2P, twoF4S_le_twoF4N v2P_mem_S⟩ := by
    rw [eG]
    exact hom1_conj_eq e (twoF4S_le_twoF4H v2P_mem_S) _ v2P_def.symm
  have h3 : a1G e * hom2 e ⟨v2P, twoF4S_le_twoF4N v2P_mem_S⟩ * (a1G e)⁻¹ = uG e := by
    rw [a1G, uG]
    exact hom2_conj_eq e _ (twoF4S_le_twoF4N uP_mem_S) uP_def.symm
  calc jG e * zG e * (jG e)⁻¹
      = a1G e * (eG e * ((a1G e)⁻¹ * zG e * a1G e) * (eG e)⁻¹) * (a1G e)⁻¹ := by
        rw [jG]; group
    _ = uG e := by rw [a1G_conjInv_zG, h2, h3]

theorem eG_mul_self
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : eG e * eG e = 1 := by
  rw [eG, ← map_mul, ← map_one (hom1 e)]
  exact hom1_congr e (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact eP_mul_self)

theorem jG_mul_self
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : jG e * jG e = 1 := by
  calc jG e * jG e = a1G e * (eG e * eG e) * (a1G e)⁻¹ := by rw [jG]; group
    _ = 1 := by rw [eG_mul_self]; group

theorem uG_mul_self
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : uG e * uG e = 1 := by
  rw [uG, ← map_mul, ← map_one (hom1 e)]
  exact hom1_congr e (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact uP_mul_self)

theorem bG_pow_five
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : bG e ^ 5 = 1 := by
  rw [bG, ← map_pow, ← map_one (hom1 e)]
  exact hom1_congr e (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact b0P_pow_five)

theorem bG_ne_one
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : bG e ≠ 1 := fun h => by
  apply b0P_ne_one
  have h1 : hom1 e ⟨b0P, b0P_mem_H⟩ = hom1 e 1 := by rw [map_one]; exact h
  have h2 := congrArg Subtype.val (hom1_injective e h1)
  rw [Subgroup.coe_one] at h2
  exact h2

theorem uG_inv_bG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : uG e * bG e * (uG e)⁻¹ = (bG e)⁻¹ := by
  rw [uG, bG, hom1_conj, ← map_inv]
  exact hom1_congr e (by rw [coe_conj, Subgroup.coe_inv]; exact uP_inv_b0P)

theorem jG_conj_mem_F1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {c : G} (hc : c ∈ F1) (hcu : c * uG e = uG e * c) : jG e * c * (jG e)⁻¹ ∈ F1 := by
  obtain ⟨x, rfl⟩ := exists_hom1_eq e hc
  have hxu : (x : Equiv.Perm (Fin 1755)) * uP = uP * x := by
    have h : hom1 e (x * ⟨uP, twoF4S_le_twoF4H uP_mem_S⟩) =
        hom1 e (⟨uP, twoF4S_le_twoF4H uP_mem_S⟩ * x) := by
      rw [map_mul, map_mul]
      exact hcu
    have h' := congrArg Subtype.val (hom1_injective e h)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    exact h'
  obtain ⟨hS0, hS1, hS2, hS3⟩ := chain_of_comm_uP x.2 hxu
  have h0 : hom1 e x = hom2 e ⟨x, twoF4S_le_twoF4N hS0⟩ := hom1_eq_hom2 e x.2 _
  have h1 : (a1G e)⁻¹ * hom1 e x * a1G e = hom1 e ⟨_, twoF4S_le_twoF4H hS1⟩ := by
    rw [h0, a1G]
    exact hom2_conjInv_eq e _ (twoF4S_le_twoF4N hS1) rfl
  have h2 : eG e * hom1 e ⟨_, twoF4S_le_twoF4H hS1⟩ * (eG e)⁻¹ =
      hom2 e ⟨_, twoF4S_le_twoF4N hS2⟩ := by
    rw [eG]
    exact hom1_conj_eq e (twoF4S_le_twoF4H hS2) _ rfl
  have h3 : a1G e * hom2 e ⟨_, twoF4S_le_twoF4N hS2⟩ * (a1G e)⁻¹ =
      hom1 e ⟨_, twoF4S_le_twoF4H hS3⟩ := by
    rw [a1G]
    refine hom2_conj_eq e _ (twoF4S_le_twoF4N hS3) ?_
    rw [jP_def]
    group
  have hcalc : jG e * hom1 e x * (jG e)⁻¹ =
      a1G e * (eG e * ((a1G e)⁻¹ * hom1 e x * a1G e) * (eG e)⁻¹) * (a1G e)⁻¹ := by
    rw [jG]; group
  rw [hcalc, h1, h2, h3]
  exact hom1_mem e _

end Elements

section Norm

variable {X : Type*} [Group X] {b : X}

theorem exists_conj_pow_mul {x y : X} (hx : ∃ k : ℕ, x * b * x⁻¹ = b ^ k)
    (hy : ∃ k : ℕ, y * b * y⁻¹ = b ^ k) : ∃ k : ℕ, (x * y) * b * (x * y)⁻¹ = b ^ k := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  refine ⟨k * l, ?_⟩
  calc (x * y) * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
    _ = (x * b * x⁻¹) ^ l := by rw [hl, conj_pow]
    _ = b ^ (k * l) := by rw [hk, ← pow_mul]

theorem exists_conj_pow_pow {x : X} (hx : ∃ k : ℕ, x * b * x⁻¹ = b ^ k) (n : ℕ) :
    ∃ k : ℕ, x ^ n * b * (x ^ n)⁻¹ = b ^ k := by
  induction n with
  | zero => exact ⟨1, by rw [pow_zero, pow_one, one_mul, inv_one, mul_one]⟩
  | succ n ih =>
    rw [pow_succ]
    exact exists_conj_pow_mul ih hx

end Norm

section Elements2

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

theorem g3G_conjInv_zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : (g3G e)⁻¹ * zG e * g3G e = hom2 e ⟨zpP, twoF4S_le_twoF4N zpP_mem_S⟩ := by
  have h2 : (f2G e)⁻¹ * hom1 e ⟨v1P, twoF4S_le_twoF4H v1P_mem_S⟩ * f2G e =
      hom2 e ⟨zpP, twoF4S_le_twoF4N zpP_mem_S⟩ := by
    rw [f2G]
    exact hom1_conjInv_eq e (twoF4S_le_twoF4H zpP_mem_S) _ zpP_def.symm
  calc (g3G e)⁻¹ * zG e * g3G e = (f2G e)⁻¹ * ((a1G e)⁻¹ * zG e * a1G e) * f2G e := by
        rw [g3G]; group
    _ = hom2 e ⟨zpP, twoF4S_le_twoF4N zpP_mem_S⟩ := by rw [a1G_conjInv_zG, h2]

theorem yG_conj_zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : yG e * zG e * (yG e)⁻¹ = jG e := by
  have h3 : cG e * hom2 e ⟨zpP, twoF4S_le_twoF4N zpP_mem_S⟩ * (cG e)⁻¹ =
      hom1 e ⟨jpP, twoF4S_le_twoF4H jpP_mem_S⟩ := by
    rw [cG]
    exact hom2_conj_eq e _ (twoF4S_le_twoF4N jpP_mem_S) cP_conj_zpP
  have h4 : f2G e * hom1 e ⟨jpP, twoF4S_le_twoF4H jpP_mem_S⟩ * (f2G e)⁻¹ = eG e := by
    rw [f2G, eG, hom1_conj]
    refine hom1_congr e ?_
    rw [coe_conj]
    show f2P * jpP * f2P⁻¹ = eP
    rw [jpP_def]
    group
  calc yG e * zG e * (yG e)⁻¹
      = a1G e * (f2G e * (cG e * ((g3G e)⁻¹ * zG e * g3G e) * (cG e)⁻¹) * (f2G e)⁻¹) *
          (a1G e)⁻¹ := by
        rw [yG, g3G]; group
    _ = jG e := by rw [g3G_conjInv_zG, h3, h4, jG]

theorem uG_mul_zG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : uG e * zG e = hom1 e ⟨tP, twoF4S_le_twoF4H tP_mem_S⟩ := by
  rw [uG, zG, ← map_mul]
  exact hom1_congr e (by rw [Subgroup.coe_mul]; exact tP_def.symm)

theorem g3G_conjInv_tG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : (g3G e)⁻¹ * (uG e * zG e) * g3G e = hom2 e ⟨tpP, twoF4S_le_twoF4N tpP_mem_S⟩ := by
  have h1 : (a1G e)⁻¹ * (uG e * zG e) * a1G e = hom1 e ⟨w1P, twoF4S_le_twoF4H w1P_mem_S⟩ := by
    rw [uG_mul_zG, hom1_eq_hom2 e (twoF4S_le_twoF4H tP_mem_S) (twoF4S_le_twoF4N tP_mem_S), a1G]
    exact hom2_conjInv_eq e _ (twoF4S_le_twoF4N w1P_mem_S) w1P_def.symm
  have h2 : (f2G e)⁻¹ * hom1 e ⟨w1P, twoF4S_le_twoF4H w1P_mem_S⟩ * f2G e =
      hom2 e ⟨tpP, twoF4S_le_twoF4N tpP_mem_S⟩ := by
    rw [f2G]
    exact hom1_conjInv_eq e (twoF4S_le_twoF4H tpP_mem_S) _ tpP_def.symm
  calc (g3G e)⁻¹ * (uG e * zG e) * g3G e = (f2G e)⁻¹ *
        ((a1G e)⁻¹ * (uG e * zG e) * a1G e) * f2G e := by rw [g3G]; group
    _ = hom2 e ⟨tpP, twoF4S_le_twoF4N tpP_mem_S⟩ := by rw [h1, h2]

theorem yG_comm_tG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : yG e * (uG e * zG e) = (uG e * zG e) * yG e := by
  have hc : cG e * hom2 e ⟨tpP, twoF4S_le_twoF4N tpP_mem_S⟩ =
      hom2 e ⟨tpP, twoF4S_le_twoF4N tpP_mem_S⟩ * cG e := by
    rw [cG, ← map_mul, ← map_mul]
    exact hom2_congr e (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact cP_comm_tpP)
  have key : (g3G e)⁻¹ * (yG e * (uG e * zG e) * (yG e)⁻¹) * g3G e =
      (g3G e)⁻¹ * (uG e * zG e) * g3G e := by
    calc (g3G e)⁻¹ * (yG e * (uG e * zG e) * (yG e)⁻¹) * g3G e
        = cG e * ((g3G e)⁻¹ * (uG e * zG e) * g3G e) * (cG e)⁻¹ := by rw [yG]; group
      _ = (g3G e)⁻¹ * (uG e * zG e) * g3G e := by
        rw [g3G_conjInv_tG, hc]; group
  have h := mul_left_cancel (mul_right_cancel key)
  calc yG e * (uG e * zG e) = (yG e * (uG e * zG e) * (yG e)⁻¹) * yG e := by group
    _ = (uG e * zG e) * yG e := by rw [h]

theorem yG_pow_three
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : yG e ^ 3 = 1 := by
  have hc : cG e ^ 3 = 1 := by
    rw [cG, ← map_pow, ← map_one (hom2 e)]
    exact hom2_congr e (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact cP_pow_three)
  rw [yG, conj_pow, hc]
  group

theorem yG_ne_one
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : yG e ≠ 1 := fun h => by
  apply cP_ne_one
  have h1 : hom2 e ⟨cP, cP_mem_N⟩ = hom2 e 1 := by
    rw [map_one]
    have h2 : cG e = (g3G e)⁻¹ * yG e * g3G e := by rw [yG]; group
    rw [← cG, h2, h]
    group
  have h3 := congrArg Subtype.val (hom2_injective e h1)
  rw [Subgroup.coe_one] at h3
  exact h3

theorem iEl_mem_H
    (p : ℕ) : iEl p ∈ twoF4H := by
  rw [iEl_def]
  exact mul_mem (pow_mem aaP_mem_H _) (pow_mem abP_mem_H _)

@[expose] noncomputable def iG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (p : ℕ) : G := hom1 e ⟨iEl p, iEl_mem_H p⟩

theorem iG_mem
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (p : ℕ) : iG e p ∈ F1 := hom1_mem e _

theorem iG_inj
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {p q : ℕ} (hp : p < 16) (hq : q < 16) (h : iG e p = iG e q) : p = q :=
  iEl_inj hp hq (congrArg Subtype.val (hom1_injective e h))

theorem iEl_comm_uP
    (p : ℕ) : iEl p * uP = uP * iEl p := by
  rw [iEl_def]
  have ha : Commute aaP uP := aaP_comm_uP
  have hb : Commute abP uP := abP_comm_uP
  exact ((ha.pow_left _).mul_left (hb.pow_left _)).eq

theorem iG_comm_uG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (p : ℕ) : iG e p * uG e = uG e * iG e p := by
  rw [iG, uG, ← map_mul, ← map_mul]
  exact hom1_congr e (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact iEl_comm_uP p)

theorem iEl_norm (p : ℕ) :
    ∃ k : ℕ, iEl p * b0P * (iEl p)⁻¹ = b0P ^ k := by
  rw [iEl_def]
  exact exists_conj_pow_mul (exists_conj_pow_pow aaP_norm _) (exists_conj_pow_pow abP_norm _)

theorem iG_norm_bG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (p : ℕ) : ∃ k : ℕ, iG e p * bG e * (iG e p)⁻¹ = bG e ^ k := by
  obtain ⟨k, hk⟩ := iEl_norm p
  refine ⟨k, ?_⟩
  rw [iG, bG, hom1_conj, ← map_pow]
  exact hom1_congr e (by rw [coe_conj, Subgroup.coe_pow]; exact hk)

theorem iG_inv
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {p : ℕ} (hp : p < 16) (h2 : iG e p * iG e p = 1) :
    iG e p = 1 ∨ iG e p = zG e ∨ iG e p = uG e ∨ iG e p = uG e * zG e := by
  have h2' : iEl p * iEl p = 1 := by
    have h : hom1 e (⟨iEl p, iEl_mem_H p⟩ * ⟨iEl p, iEl_mem_H p⟩) = hom1 e 1 := by
      rw [map_mul, map_one]
      exact h2
    have h' := congrArg Subtype.val (hom1_injective e h)
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
    exact h'
  rcases iEl_inv hp h2' with h | h | h | h
  · left
    rw [iG, ← map_one (hom1 e)]
    exact hom1_congr e (by rw [Subgroup.coe_one]; exact h)
  · right; left
    exact hom1_congr e h
  · right; right; left
    exact hom1_congr e h
  · right; right; right
    rw [uG_mul_zG]
    exact hom1_congr e h

theorem conj_uG_ne
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {g : G} (hg : g ∈ F1) : g * uG e * g⁻¹ ≠ uG e * zG e := by
  obtain ⟨x, rfl⟩ := exists_hom1_eq e hg
  intro h
  rw [uG_mul_zG, uG, hom1_conj] at h
  have h' := congrArg Subtype.val (hom1_injective e h)
  rw [coe_conj] at h'
  exact conj_uP_ne_tP x h'

theorem zG_eq
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    {w : G} (hw1 : w ∈ F1) (hw2 : w ∈ F2) (hww : w * w = 1) (hwne : w ≠ 1)
    (hwc : ∀ x ∈ F1, x * w = w * x) : zG e = w := by
  obtain ⟨x, rfl⟩ := exists_hom1_eq e hw1
  have hxN : (x : Equiv.Perm (Fin 1755)) ∈ twoF4N := mem_N_of_hom1_mem_F2 e x hw2
  have hxT : (x : Equiv.Perm (Fin 1755)) ∈ twoF4H ⊓ twoF4N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
  have hxc : ∀ s ∈ twoF4H ⊓ twoF4N, s * (x : Equiv.Perm (Fin 1755)) = x * s := by
    intro s hs
    have hsH := (Subgroup.mem_inf.mp hs).1
    have h := hwc (hom1 e ⟨s, hsH⟩) (hom1_mem e _)
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (hom1_injective e h)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    exact h'
  have hx2 : (x : Equiv.Perm (Fin 1755)) ^ 2 = 1 := by
    have h : hom1 e (x * x) = hom1 e 1 := by rw [map_mul, map_one]; exact hww
    have h' := congrArg Subtype.val (hom1_injective e h)
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
    rw [pow_two]
    exact h'
  have hmem : (x : Equiv.Perm (Fin 1755)) ∈ quasithinOmegaOneCenter (twoF4H ⊓ twoF4N) :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hxT, Subgroup.mem_centralizer_iff.mpr hxc, hx2⟩
  rcases (mem_omegaOneCenter_twoF4HN_iff _).mp hmem with h | h
  · exfalso
    apply hwne
    rw [← map_one (hom1 e)]
    exact hom1_congr e (by rw [Subgroup.coe_one]; exact h)
  · rw [zG]
    exact hom1_congr e h.symm

end Elements2

end CFSG.Quasithin.RuType.J47
