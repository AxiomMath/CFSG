module

public import CFSG.Quasithin.EmptyFaithful.S143FJ
public import CFSG.Quasithin.EmptyFaithful.S14117Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Normalizer

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.mem_normalizer_Ac_iff (h' : ↥(mcOf T)) :
    (h' : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ↔
      c.actK h' * c.alphaOf hrW hrV hr2 = c.alphaOf hrW hrV hr2 * c.actK h' := by
  constructor
  · intro hN
    have ha₀ := c.r1_mem_Ac hrW hrV hr2
    have h1 : (h' : G) * (g * r * g⁻¹) * (h' : G)⁻¹ ∈ c.Ac hrW hrV hr2 :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp ha₀
    have h1H := c.Ac_le_mcOf hrW hrV hr2 h1
    have hconj : c.actK ⟨(h' : G) * (g * r * g⁻¹) * (h' : G)⁻¹, h1H⟩ =
        c.actK h' * c.alphaOf hrW hrV hr2 * (c.actK h')⁻¹ := by
      have e : (⟨(h' : G) * (g * r * g⁻¹) * (h' : G)⁻¹, h1H⟩ : ↥(mcOf T)) =
          h' * ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ * h'⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      rfl
    rcases c.actK_Ac hrW hrV hr2 h1 with h2 | h2
    · exfalso
      rw [hconj] at h2
      apply c.alphaOf_ne_one hrW hrV hr2
      calc c.alphaOf hrW hrV hr2
          = (c.actK h')⁻¹ * (c.actK h' * c.alphaOf hrW hrV hr2 * (c.actK h')⁻¹) * c.actK h' := by
            group
        _ = 1 := by rw [h2]; group
    · rw [hconj] at h2
      calc c.actK h' * c.alphaOf hrW hrV hr2
          = (c.actK h' * c.alphaOf hrW hrV hr2 * (c.actK h')⁻¹) * c.actK h' := by group
        _ = c.alphaOf hrW hrV hr2 * c.actK h' := by rw [h2]
  · intro hcomm
    obtain ⟨-, ⟨e⟩⟩ := c.swap_facts hrW hrV hr2 (c.alphaOf_mem_T hrW hrV hr2)
      (c.alphaOf_ne_one hrW hrV hr2) (c.alphaOf_sq hrW hrV hr2) (c.alphaOf_tclsE hrW hrV hr2)
    set α := c.alphaOf hrW hrV hr2 with hα
    set C : Subgroup (MulAut (UT T M)) :=
      Subgroup.centralizer ({α} : Set (MulAut (UT T M))) ⊓ c.actK.range with hC
    set R'' : Subgroup (MulAut (UT T M)) :=
      ((rOf T M).subgroupOf (mcOf T)).map c.actK with hR''
    have hR''card : Nat.card R'' = 4 := by
      have h1 := card_map_mul_card_inf_ker (rOf_le_mcOf c) c.actK
      have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
      rw [c.actK_ker_map, rOf_inf_qOf c, hW, card_rOf c] at h1
      have h1' : Nat.card R'' * 16 = 64 := h1
      omega
    have hαR : α ∈ R'' := ⟨⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩,
      Subgroup.mem_subgroupOf.mpr (c.Ac_le_rOf hrW hrV hr2 (c.r1_mem_Ac hrW hrV hr2)), rfl⟩
    have hcomm' : ∀ s ∈ R'', s * α = α * s := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hab := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥R'')
        (by rw [hR''card]; norm_num)).is_comm.comm
      intro s hs
      exact congrArg Subtype.val (hab ⟨s, hs⟩ ⟨α, hαR⟩)
    have hR''C : R'' ≤ C := fun s hs => ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' s hs),
      Subgroup.map_le_range _ _ hs⟩
    have hyC : c.actK h' ∈ C :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm, ⟨h', rfl⟩⟩
    have hRC : Nat.card ↥(R''.subgroupOf C) = 4 := by
      rw [← hR''card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR''C).toEquiv
    obtain ⟨o, s, hodd, hs, hy⟩ := exists_odd_mul_of_card_four e (R''.subgroupOf C) hRC
      ⟨c.actK h', hyC⟩
    have hyo : c.actK h' = (o : MulAut (UT T M)) * (s : MulAut (UT T M)) := congrArg Subtype.val hy
    obtain ⟨s', hs'mem, hs'eq⟩ := Subgroup.mem_subgroupOf.mp hs
    have hs'R : (s' : G) ∈ rOf T M := Subgroup.mem_subgroupOf.mp hs'mem
    have hoodd : Odd (orderOf (o : MulAut (UT T M))) := by rw [Subgroup.orderOf_coe]; exact hodd
    obtain ⟨h₁, hh₁odd, hh₁⟩ := exists_odd_lift c.actK (c := (o : MulAut (UT T M))) o.2.2 hoodd
    have hocomm : c.actK h₁ * α = α * c.actK h₁ := by
      rw [hh₁]; exact Subgroup.mem_centralizer_singleton_iff.mp o.2.1
    have hocomm' : c.actK h₁⁻¹ * α = α * c.actK h₁⁻¹ := by
      rw [map_inv]
      calc (c.actK h₁)⁻¹ * α = (c.actK h₁)⁻¹ * (α * c.actK h₁) * (c.actK h₁)⁻¹ := by group
        _ = (c.actK h₁)⁻¹ * (c.actK h₁ * α) * (c.actK h₁)⁻¹ := by rw [hocomm]
        _ = α * (c.actK h₁)⁻¹ := by group
    have hN₁ : (h₁ : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      mem_normalizer_of_conj_mem (fun a ha => c.conj_mem_Ac_of_odd hrW hrV hr2 hh₁odd hocomm ha)
        (fun a ha => by
          have := c.conj_mem_Ac_of_odd hrW hrV hr2 (x := h₁⁻¹) (by rwa [orderOf_inv]) hocomm' ha
          simpa using this)
    have hN₂ : (s' : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      c.iTwo_le_normalizer_Ac hrW hrV hr2 (pCoreOf_le 2 (iTwo T M) hs'R)
    have hqeq : c.actK ((h₁ * s')⁻¹ * h') = 1 := by
      rw [map_mul, map_inv, map_mul, hh₁, hs'eq, hyo]
      group
    have hqQ : (((h₁ * s')⁻¹ * h' : ↥(mcOf T)) : G) ∈ qOf T := c.mem_qOf_of_actK_eq_one hqeq
    have hN₃ : (((h₁ * s')⁻¹ * h' : ↥(mcOf T)) : G) ∈
        Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      c.normal_Ac hrW hrV hr2 (Subgroup.mem_sup_right hqQ)
    have hdec : h₁ * s' * ((h₁ * s')⁻¹ * h') = h' := by group
    have hdecG : (h₁ : G) * (s' : G) * (((h₁ * s')⁻¹ * h' : ↥(mcOf T)) : G) = (h' : G) :=
      congrArg Subtype.val hdec
    rw [← hdecG]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hN₁ hN₂) hN₃

end Normalizer

section Transport

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.actK_ker : c.actK.ker = CFSG.Open.pCore 2 ↥(mcOf T) := by
  apply Subgroup.map_injective (mcOf T).subtype_injective
  rw [c.actK_ker_map]
  rfl

theorem Counter.actK_commute_iff (x y : ↥(mcOf T)) :
    c.actK x * c.actK y = c.actK y * c.actK x ↔
      ((x * y * x⁻¹ * y⁻¹ : ↥(mcOf T)) : G) ∈ qOf T := by
  constructor
  · intro h
    apply c.mem_qOf_of_actK_eq_one
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  · intro h
    have h1 := c.actK_eq_one_of_mem_qOf h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc c.actK x * c.actK y = (c.actK x * c.actK y * (c.actK x)⁻¹) * c.actK x := by group
      _ = c.actK y * c.actK x := by rw [h2]

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.nh_star : imageOTwoQuot (mcOf T)
    (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) =
      Subgroup.centralizer
        (imageOTwoQuot (mcOf T) (c.Ac hrW hrV hr2) : Set (OTwoQuot (mcOf T))) := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hxH, ⟨-, hxN⟩, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨a, haH, haA, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    have hxα := (c.mem_normalizer_Ac_iff hrW hrV hr2 ⟨x, hxH⟩).mp hxN
    have hcomm : c.actK ⟨x, hxH⟩ * c.actK ⟨a, haH⟩ = c.actK ⟨a, haH⟩ * c.actK ⟨x, hxH⟩ := by
      rcases c.actK_Ac hrW hrV hr2 haA with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hxα
    exact ((mk_commute_iff ⟨x, hxH⟩ ⟨a, haH⟩).mpr ((c.actK_commute_iff _ _).mp hcomm)).symm
  · intro hu
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective u
    rw [Subgroup.mem_centralizer_iff] at hu
    have hv : (QuotientGroup.mk ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ : OTwoQuot (mcOf T)) ∈
        imageOTwoQuot (mcOf T) (c.Ac hrW hrV hr2) :=
      mem_imageOTwoQuot_iff.mpr ⟨_, c.r1_mem_mcOf hrW hrV hr2, c.r1_mem_Ac hrW hrV hr2, rfl⟩
    have h1 := hu _ hv
    have h2 := (mk_commute_iff ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ h').mp h1
    have h3 := (c.actK_commute_iff _ h').mpr h2
    have hN : (h' : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      (c.mem_normalizer_Ac_iff hrW hrV hr2 h').mpr h3.symm
    exact mem_imageOTwoQuot_iff.mpr ⟨h', h'.2, ⟨h'.2, hN⟩, rfl⟩

theorem Counter.nh_iso : Nonempty (↥(imageOTwoQuot (mcOf T)
    (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) := by
  obtain ⟨-, ⟨e⟩⟩ := c.swap_facts hrW hrV hr2 (c.alphaOf_mem_T hrW hrV hr2)
    (c.alphaOf_ne_one hrW hrV hr2) (c.alphaOf_sq hrW hrV hr2) (c.alphaOf_tclsE hrW hrV hr2)
  set α := c.alphaOf hrW hrV hr2 with hα
  have hker := c.actK_ker
  let Ψ : OTwoQuot (mcOf T) →* MulAut (UT T M) :=
    QuotientGroup.lift (CFSG.Open.pCore 2 ↥(mcOf T)) c.actK (by rw [hker])
  have hΨmk : ∀ h' : ↥(mcOf T), Ψ (QuotientGroup.mk h') = c.actK h' := fun h' => rfl
  have hΨinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_one Ψ).mpr fun u hu => ?_
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective u
    rw [hΨmk] at hu
    have : h' ∈ CFSG.Open.pCore 2 ↥(mcOf T) := by rw [← hker]; exact MonoidHom.mem_ker.mpr hu
    exact (QuotientGroup.eq_one_iff _).mpr this
  set S := imageOTwoQuot (mcOf T) (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    with hS
  have hmap : S.map Ψ =
      Subgroup.centralizer ({α} : Set (MulAut (UT T M))) ⊓ c.actK.range := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hxH, ⟨-, hxN⟩, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ⟨⟨x, hxH⟩, rfl⟩⟩
      exact (c.mem_normalizer_Ac_iff hrW hrV hr2 ⟨x, hxH⟩).mp hxN
    · rintro ⟨hy1, ⟨h', rfl⟩⟩
      have hN : (h' : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
        (c.mem_normalizer_Ac_iff hrW hrV hr2 h').mpr (Subgroup.mem_centralizer_singleton_iff.mp hy1)
      exact ⟨QuotientGroup.mk h', mem_imageOTwoQuot_iff.mpr ⟨h', h'.2, ⟨h'.2, hN⟩, rfl⟩, rfl⟩
  exact ⟨((Subgroup.equivMapOfInjective S Ψ hΨinj).trans (MulEquiv.subgroupCongr hmap)).trans e⟩

theorem Counter.concl18c : Concl18c T (c.Ac hrW hrV hr2) where
  nh_star := c.nh_star hrW hrV hr2
  nh_iso := c.nh_iso hrW hrV hr2

end Transport

end S143

theorem lemma_14_3_18_c : S143.Lemma14318c := by
  intro G _ _ T M g A t c _ hb
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  exact c.concl18c hrW hrV hr2

end CFSG.Quasithin
