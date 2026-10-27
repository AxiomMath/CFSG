module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4c
public import CFSG.Quasithin.H13.GoldschmidtM22EndExtra

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

theorem comm_identity_aux {G : Type*} [Group G] (x k v e c : G) (hkx : k * x * k⁻¹ = e * x)
    (hxv : x * v * x⁻¹ = v) (hc : c = e * v * e⁻¹ * v⁻¹) (hck : k⁻¹ * c = c * k⁻¹) :
    x * (k⁻¹ * v * k) * x⁻¹ = c * (k⁻¹ * v * k) := by
  calc x * (k⁻¹ * v * k) * x⁻¹
      = k⁻¹ * (k * x * k⁻¹) * v * (k * x * k⁻¹)⁻¹ * k := by group
    _ = k⁻¹ * (e * x) * v * (e * x)⁻¹ * k := by rw [hkx]
    _ = k⁻¹ * e * (x * v * x⁻¹) * e⁻¹ * k := by group
    _ = k⁻¹ * (e * v * e⁻¹) * k := by rw [hxv]; group
    _ = k⁻¹ * (c * v) * k := by rw [hc]; group
    _ = (k⁻¹ * c) * v * k := by group
    _ = c * (k⁻¹ * v * k) := by rw [hck]; group

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem V_le_centralizer_V (h : Hyp6Sec2 G T M L V) : V ≤ Subgroup.centralizer (V : Set G) :=
  fun _ hu => Subgroup.mem_centralizer_iff.mpr fun _ hv =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hv hu

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk P h hZ in
theorem exists_a_noncomm (h6210 : Stmt6_2_10) :
    ∃ a : ↥(HH T), (a : G) ∈ V ∧ (a : G) ∉ CHU T L V ∧
      P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩ := by
  obtain ⟨a, haV, haC⟩ := PsiData.exists_a h hZ h6210
  exact ⟨a, haV, haC, fun hc => hk.g_not_mem (((P.swap_norm a haV haC).2 ⟨g, hk.g_mem⟩).mpr hc)⟩

include hk P h hZ in
theorem conj_inf_normalizer_le_CHU (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ CHU T L V := by
  obtain ⟨a, haV, haC, hg⟩ := exists_a_noncomm hk h P hZ h6210
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hτ2 : (P.ψ a).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  intro x hx
  obtain ⟨hxVg, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ HH T := hk.K_le_HH (Subgroup.mem_sup_right hxVg)
  have hv : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hxVg
  have hvH : g * x * g⁻¹ ∈ HH T := V_le_HH h hZ hv
  have hxx : (⟨x, hxH⟩ : ↥(HH T)) = (⟨g, hk.g_mem⟩ : ↥(HH T))⁻¹ * ⟨g * x * g⁻¹, hvH⟩ *
      ⟨g, hk.g_mem⟩ := by
    apply Subtype.ext
    simp [mul_assoc]
  have hψ : P.ψ ⟨x, hxH⟩ = (P.ψ ⟨g, hk.g_mem⟩)⁻¹ * P.ψ ⟨g * x * g⁻¹, hvH⟩ * P.ψ ⟨g, hk.g_mem⟩ := by
    rw [hxx, map_mul, map_mul, map_inv]
  rcases P.mem_V h h6211 a ⟨g * x * g⁻¹, hvH⟩ haV haC hv with h1 | h1
  · have : P.ψ ⟨x, hxH⟩ = 1 := by rw [hψ, h1]; group
    exact (P.ker _).mp this
  · exfalso
    have hcomm : P.ψ ⟨x, hxH⟩ * P.ψ a = P.ψ a * P.ψ ⟨x, hxH⟩ := (hNa ⟨x, hxH⟩).mp hxN
    rw [hψ, h1] at hcomm
    exact (perm3_noncomm_conj _ _ hτ2 hg).1 hcomm

include hk P h hZ in
theorem conj_inf_normalizer_eq (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = conjSubgroup V g ⊓ CHU T L V :=
  le_antisymm (le_inf inf_le_left (conj_inf_normalizer_le_CHU hk h P hZ h6210 h6211))
    (inf_le_inf_left _ (CHU_le_normalizer_V h h6210))

include hk P h hZ in
theorem V1_inf_centralizer (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) :
    conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G) =
      quasithinOmegaOneCenter T := by
  have hA := conj_inf_normalizer_eq hk h P hZ h6210 h6211
  have h4 := hk.case2.relIndex_four
  rw [hA] at h4
  have h1 := Subgroup.relIndex_mul_card
    (H := conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G))
    (K := conjSubgroup V g ⊓ CHU T L V)
  rw [inf_eq_left.mpr (inf_le_left : conjSubgroup V g ⊓ CHU T L V ⊓
    Subgroup.centralizer (V : Set G) ≤ conjSubgroup V g ⊓ CHU T L V), h4,
    hk.card_V1 h hZ h6211] at h1
  have hc : Nat.card ↥(conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G)) = 2 := by
    omega
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (V : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun v hv =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hv (Z_le_V h hZ hz)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf ?_ hZC) (by rw [hc, hZ])).symm
  exact (hk.V0_inf_V1 h hZ).symm.le.trans inf_le_right

include hk P h hZ in
theorem D_inf_centralizer_le (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) :
    D ⊓ Subgroup.centralizer (V : Set G) ≤ V ⊓ CHU T L V := by
  intro d hd
  obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
  obtain ⟨u, hu, w, hw, rfl⟩ := hk.exists_mul_V0_V1 h hZ h6211 d hdD
  have huC : u ∈ Subgroup.centralizer (V : Set G) :=
    V_le_centralizer_V h (Subgroup.mem_inf.mp hu).1
  have hwC : w ∈ Subgroup.centralizer (V : Set G) := by
    have := (Subgroup.centralizer (V : Set G)).mul_mem
      ((Subgroup.centralizer (V : Set G)).inv_mem huC) hdC
    simpa using this
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    rw [← V1_inf_centralizer hk h P hZ h6210 h6211]
    exact ⟨hw, hwC⟩
  exact (V ⊓ CHU T L V).mul_mem hu (hk.Z_le_V0 h hZ hwZ)

include hk in
theorem commutator_mem_Z {a b : G} (ha : a ∈ D) (hb : b ∈ D) :
    a * b * a⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsExtraspecial 2 ↥D := hk.extra.1
  have hc := extraspecial_commutator_mem_center (p := 2) (⟨a, ha⟩ : ↥D) ⟨b, hb⟩
  rw [← hk.center_eq]
  refine ⟨D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb),
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)

include hk h hZ in
theorem exists_conj_V1 (h621 : Stmt6_2_1) : ∃ k ∈ V ⊔ conjSubgroup V g,
    conjSubgroup V g ⊓ CHU T L V = conjSubgroup (V ⊓ CHU T L V) k := by
  obtain ⟨k, hkK, c, hc, hgkc⟩ := hk.H_eq g hk.g_mem
  have hkH : k ∈ HH T := hk.K_le_HH hkK
  refine ⟨k, hkK, ?_⟩
  have h1 : conjSubgroup V g = conjSubgroup V k := by
    rw [hgkc, ← conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr (CHU_le_normalizer_conj_V h hZ h621 hkH hc)
  rw [h1, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
    conjSubgroup_eq_iff_mem_normalizer.mpr (HH_le_normalizer_CHU h hZ hkH)]

end KData

end CFSG.Quasithin.H13.GM22
