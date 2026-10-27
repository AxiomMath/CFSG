module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4d

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk h hZ in
theorem inf_le_centralizerMod (h621 : Stmt6_2_1) (h6211 : Stmt6_2_11) {x : G}
    (hx : x ∈ Subgroup.centralizer (V : Set G) ⊓ CHU T L V) :
    x ∈ centralizerMod (quasithinOmegaOneCenter T) (HH T) D := by
  obtain ⟨hxC, hxCHU⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ HH T := centralizerMod_le_left _ _ _ hxCHU
  refine ⟨hxH, HH_le_normalizer_Z T hxH, fun d hd => ?_⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := hk.exists_mul_V0_V1 h hZ h6211 d hd
  obtain ⟨k, hkK, hV1⟩ := hk.exists_conj_V1 h hZ h621
  have hkH : k ∈ HH T := hk.K_le_HH hkK
  have hwk : k * w * k⁻¹ ∈ V ⊓ CHU T L V := by
    have := hV1 ▸ hw
    exact mem_conjSubgroup_iff.mp this
  have hvV : k * w * k⁻¹ ∈ V := (Subgroup.mem_inf.mp hwk).1
  have hvD : k * w * k⁻¹ ∈ D := hk.V0_le_D hwk
  have huV : u ∈ V := (Subgroup.mem_inf.mp hu).1
  have huD : u ∈ D := hk.V0_le_D hu
  have hxu : x * u * x⁻¹ = u := by
    have := Subgroup.mem_centralizer_iff.mp hxC u huV
    rw [← this]
    group
  have hxv : x * (k * w * k⁻¹) * x⁻¹ = k * w * k⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hxC _ hvV
    rw [← this]
    group
  have he : k * x * k⁻¹ * x⁻¹ ∈ D := by
    rw [hk.D_eq]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxk : x * k⁻¹ * x⁻¹ ∈ V ⊔ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.mp (hk.H_le_normalizer_K hxH) k⁻¹).mp
          ((V ⊔ conjSubgroup V g).inv_mem hkK)
      have := (V ⊔ conjSubgroup V g).mul_mem hkK hxk
      simpa [mul_assoc] using this
    · have hkx : k * x * k⁻¹ ∈ CHU T L V :=
        (Subgroup.mem_normalizer_iff.mp (HH_le_normalizer_CHU h hZ hkH) x).mp hxCHU
      exact (CHU T L V).mul_mem hkx ((CHU T L V).inv_mem hxCHU)
  set e := k * x * k⁻¹ * x⁻¹ with hedef
  set v := k * w * k⁻¹ with hvdef
  have hcZ : e * v * e⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := hk.commutator_mem_Z he hvD
  have hck : k⁻¹ * (e * v * e⁻¹ * v⁻¹) = (e * v * e⁻¹ * v⁻¹) * k⁻¹ :=
    Z_central T ((HH T).inv_mem hkH) hcZ
  have hkx : k * x * k⁻¹ = e * x := by rw [hedef]; group
  have hwv : w = k⁻¹ * v * k := by rw [hvdef]; group
  have hxw : x * w * x⁻¹ = (e * v * e⁻¹ * v⁻¹) * w := by
    have := comm_identity_aux x k v e (e * v * e⁻¹ * v⁻¹) hkx hxv rfl hck
    rw [hwv]
    exact this
  have hcu : u * (e * v * e⁻¹ * v⁻¹) * u⁻¹ = e * v * e⁻¹ * v⁻¹ := by
    have := Z_central T (hk.D_le_HH huD) hcZ
    rw [this]
    group
  have e1 : x * (u * w) * x⁻¹ * (u * w)⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) * w⁻¹ * u⁻¹ := by group
  rw [e1, hxu, hxw]
  have e2 : u * ((e * v * e⁻¹ * v⁻¹) * w) * w⁻¹ * u⁻¹ = u * (e * v * e⁻¹ * v⁻¹) * u⁻¹ := by
    group
  rw [e2, hcu]
  exact hcZ

include hk in
theorem exists_mul_of_mem_centralizerMod {x : G}
    (hx : x ∈ centralizerMod (quasithinOmegaOneCenter T) (HH T) D) :
    ∃ d ∈ D, d⁻¹ * x ∈ Subgroup.centralizer (D : Set G) := by
  have : CFSG.IsExtraspecial 2 ↥D := hk.extra.1
  refine exists_mul_centralizer_of_acts_trivially (hk.H_le_normalizer_D hx.1) fun d hd => ?_
  rw [hk.center_eq]
  exact hx.2.2 d hd

include hk h in
theorem centralizer_inf_CHU_le_centralizer_V (h6110 : Stmt6_1_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) :
    Subgroup.centralizer (D : Set G) ⊓ CHU T L V ≤ Subgroup.centralizer (V : Set G) := by
  have hV := h.toHyp611.isElemAbelian
  have hs : sParam hV = 2 := ((h6110 G T M L V 2 h.toHyp611Nat).2.1 hV).1
  have hCHU : CHU T L V = pCoreOf 2 (HH T) := (h6212 G T M L V h).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 (CHU T L V) := hCHU ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (HH T)
  have hm : mQuot V (V ⊓ CHU T L V) = 1 := by
    unfold mQuot
    rw [relIndex_V_CHU h h6211]
    simp
  obtain ⟨-, h2⟩ := e3_6 hV (A := V ⊓ CHU T L V) (B := V ⊓ CHU T L V) le_rfl inf_le_left
    (by rw [hm, hs]; norm_num) hE
  intro x hx
  obtain ⟨hxD, hxCHU⟩ := Subgroup.mem_inf.mp hx
  have : x ∈ CHU T L V ⊓ Subgroup.centralizer ((V ⊓ CHU T L V : Subgroup G) : Set G) :=
    ⟨hxCHU, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hxD y (hk.V0_le_D hy)⟩
  rw [h2] at this
  exact (Subgroup.mem_inf.mp this).2

end KData

end CFSG.Quasithin.H13.GM22
