module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.Quasithin.Vol2.Ch3E213MP6CB

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply uElt uMat glMat_uElt antiUnipotent antiUnipotentCenter
    mem_antiUnipotent_iff_upper uElt_mul uElt_mem_antiUnipotent uMat_inj antiUnipotentCenter_comm
    antiSp_ext uMat_zero minorJ_mul_self)
open CFSG.ABGLocalTools (IsSylowOf)

variable {k : Type} [Field k] [CharP k 2]

theorem mem_center_of_commute {y : antiSp k} (hy : y ∈ antiUnipotent k)
    (h1 : y * uElt 1 0 0 0 = uElt 1 0 0 0 * y) (h2 : y * uElt 0 0 0 1 = uElt 0 0 0 1 * y) :
    y ∈ antiUnipotentCenter k := by
  obtain ⟨a, b, c, d, rfl⟩ := hy
  rw [uElt_mul, uElt_mul] at h1 h2
  have h1' := congrArg (fun g : antiSp k => glMat (g : GL (Fin 4) k)) h1
  have h2' := congrArg (fun g : antiSp k => glMat (g : GL (Fin 4) k)) h2
  simp only [glMat_uElt] at h1' h2'
  have e1 := (uMat_inj h1').2.1
  have e2 := (uMat_inj h2').2.1
  have hd : d = 0 := by linear_combination -e1
  have ha : a = 0 := by linear_combination e2
  exact ⟨b, c, by rw [ha, hd]⟩

theorem conj_mem_center_of_isUpper {c z : antiSp k} (hc : IsUpper c)
    (hz : z ∈ antiUnipotentCenter k) : c * z * c⁻¹ ∈ antiUnipotentCenter k := by
  have hN := mem_normalizer_of_isUpper hc
  have hN' := Subgroup.inv_mem _ hN
  have hzU : z ∈ antiUnipotent k := by
    obtain ⟨b, d, rfl⟩ := hz
    exact uElt_mem_antiUnipotent 0 b d 0
  have hyU : c * z * c⁻¹ ∈ antiUnipotent k := (Subgroup.mem_normalizer_iff.mp hN z).mp hzU
  have hcomm : ∀ u ∈ antiUnipotent k, c * z * c⁻¹ * u = u * (c * z * c⁻¹) := by
    intro u hu
    have hu' : c⁻¹ * u * c⁻¹⁻¹ ∈ antiUnipotent k := (Subgroup.mem_normalizer_iff.mp hN' u).mp hu
    rw [inv_inv] at hu'
    have h := antiUnipotentCenter_comm hz hu'
    calc c * z * c⁻¹ * u = c * (z * (c⁻¹ * u * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * u * c) * z) * c⁻¹ := by rw [h]
      _ = u * (c * z * c⁻¹) := by group
  exact mem_center_of_commute hyU (hcomm _ (uElt_mem_antiUnipotent 1 0 0 0))
    (hcomm _ (uElt_mem_antiUnipotent 0 0 0 1))

omit [CharP k 2] in
theorem map_conj_inf_of_mem_normalizer {X A : Subgroup (antiSp k)} {c : antiSp k}
    (hc : c ∈ Subgroup.normalizer (A : Set (antiSp k))) :
    X.map (MulAut.conj c).toMonoidHom ⊓ A = (X ⊓ A).map (MulAut.conj c).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hc x).mpr hy
  · rintro ⟨x, ⟨hx, hxA⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (Subgroup.mem_normalizer_iff.mp hc x).mp hxA⟩

theorem isUpper_mem_normalizer_center {c : antiSp k} (hc : IsUpper c) :
    c ∈ Subgroup.normalizer (antiUnipotentCenter k : Set (antiSp k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_center_of_isUpper hc, fun h => ?_⟩
  have := conj_mem_center_of_isUpper (isUpper_inv hc) h
  rwa [inv_inv, show c⁻¹ * (c * z * c⁻¹) * c = z by group] at this

theorem card_inf_center_le [Finite k] {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c) :
    Nat.card ↥((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotentCenter k) ≤
      Nat.card F₀ ^ 2 := by
  rw [map_conj_inf_of_mem_normalizer (isUpper_mem_normalizer_center hc),
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact card_subfieldSp_inf_center_le F₀

theorem isSylowOf_inf_antiUnipotent [Finite k] {F₀ : Subfield k} {c : antiSp k}
    (hc : IsUpper c) :
    IsSylowOf 2 ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotent k)
      ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [map_conj_inf_of_mem_normalizer (mem_normalizer_of_isUpper hc)]
  exact CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective _ (MulAut.conj c).injective
    (isSylowOf_subfieldSp_inf F₀)

omit [CharP k 2] in
theorem wLong_mul_self : (wLong : antiSp k) * wLong = 1 :=
  Subtype.ext (Units.ext minorJ_mul_self)

omit [CharP k 2] in
theorem wLong_inv : (wLong : antiSp k)⁻¹ = wLong :=
  inv_eq_of_mul_eq_one_right wLong_mul_self

theorem eq_one_of_mem_of_conj_mem {u : antiSp k} (hu : u ∈ antiUnipotent k)
    (hJu : wLong * u * wLong⁻¹ ∈ antiUnipotent k) : u = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  have hlow := ((mem_antiUnipotent_iff_upper _).mp hJu).1
  have hM : glMat ((wLong * uElt a b c d * wLong⁻¹ : antiSp k) : GL (Fin 4) k) =
      minorJ k * uMat a b c d * minorJ k := rfl
  have h10 := hlow 1 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h30 := hlow 3 0 (by decide)
  have h31 := hlow 3 1 (by decide)
  rw [hM] at h10 h21 h30 h31
  simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, uMat] at h10 h21 h30 h31
  subst h10 h21 h30 h31
  exact antiSp_ext uMat_zero

omit [CharP k 2] in
theorem conj_mem_inSubgroup_pCore {G : Type} [Group G] {Y : Subgroup G} {x y : G} (hy : y ∈ Y)
    (hx : x ∈ CFSG.inSubgroup (CFSG.pCore 2) Y) :
    y * x * y⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore 2) Y := by
  rw [CFSG.inSubgroup, Subgroup.mem_map] at hx ⊢
  obtain ⟨x', hx', hxx⟩ := hx
  refine ⟨⟨y, hy⟩ * x' * ⟨y, hy⟩⁻¹, (CFSG.pCore_normal).conj_mem x' hx' ⟨y, hy⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, hxx, Subgroup.coe_subtype]

omit [CharP k 2] in
theorem inSubgroup_pCore_eq_pCoreOf (Y : Subgroup (antiSp k)) :
    CFSG.inSubgroup (CFSG.pCore 2) Y = CFSG.Open.pCoreOf 2 Y := by
  rw [CFSG.inSubgroup]
  rfl

theorem pCore_eq_bot [Finite k] {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c) :
    CFSG.inSubgroup (CFSG.pCore 2) ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) = ⊥ := by
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hY
  have hS := isSylowOf_inf_antiUnipotent (F₀ := F₀) hc
  rw [← CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at hS
  have hO : CFSG.inSubgroup (CFSG.pCore 2) Y ≤ Y ⊓ antiUnipotent k := by
    rw [inSubgroup_pCore_eq_pCoreOf]
    exact hS.pCoreOf_le
  have hg : c * wLong * c⁻¹ ∈ Y := ⟨wLong, wLong_mem_subfieldSp F₀, rfl⟩
  have hN := mem_normalizer_of_isUpper hc
  have hN' := mem_normalizer_of_isUpper (isUpper_inv hc)
  rw [eq_bot_iff]
  intro x hx
  have hxU : x ∈ antiUnipotent k := (hO hx).2
  have hx2 : (c * wLong * c⁻¹)⁻¹ * x * (c * wLong * c⁻¹)⁻¹⁻¹ ∈ antiUnipotent k :=
    (hO (conj_mem_inSubgroup_pCore (Y.inv_mem hg) hx)).2
  have hu : c⁻¹ * x * c⁻¹⁻¹ ∈ antiUnipotent k := (Subgroup.mem_normalizer_iff.mp hN' x).mp hxU
  rw [inv_inv] at hu
  have hJu : wLong * (c⁻¹ * x * c) * wLong⁻¹ ∈ antiUnipotent k := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hN' _).mp hx2
    have e : c⁻¹ * ((c * wLong * c⁻¹)⁻¹ * x * (c * wLong * c⁻¹)⁻¹⁻¹) * c⁻¹⁻¹ =
        wLong * (c⁻¹ * x * c) * wLong⁻¹ := by
      rw [inv_inv, inv_inv]
      calc c⁻¹ * ((c * wLong * c⁻¹)⁻¹ * x * (c * wLong * c⁻¹)) * c
          = wLong⁻¹ * (c⁻¹ * x * c) * wLong := by group
        _ = wLong * (c⁻¹ * x * c) * wLong⁻¹ := by rw [wLong_inv]
    rwa [e] at h1
  have h1 := eq_one_of_mem_of_conj_mem hu hJu
  rw [Subgroup.mem_bot]
  calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group

omit [CharP k 2] in
theorem le_inSubgroup_pCore {G : Type} [Group G] {P S : Subgroup G} (hSP : S ≤ P)
    (hN : P ≤ Subgroup.normalizer (S : Set G)) (h2 : IsPGroup 2 S) :
    S ≤ CFSG.inSubgroup (CFSG.pCore 2) P := by
  have hnormal : (S.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mpr hN
  have h2' : IsPGroup 2 (S.subgroupOf P) := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hle : S.subgroupOf P ≤ CFSG.pCore 2 P := by
    unfold CFSG.pCore
    exact le_sSup ⟨hnormal, h2'⟩
  intro s hs
  rw [CFSG.inSubgroup, Subgroup.mem_map]
  exact ⟨⟨s, hSP hs⟩, hle hs, rfl⟩

theorem pCore_inf_normalizer [Finite k] {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c) :
    CFSG.inSubgroup (CFSG.pCore 2) ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓
      Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotent k := by
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hY
  have hSP : Y ⊓ antiUnipotent k ≤ Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) :=
    inf_le_inf_left Y Subgroup.le_normalizer
  have hS := isSylowOf_inf_antiUnipotent (F₀ := F₀) hc
  rw [← CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at hS
  have hSP' : CFSG.QuasithinUnique.IsSylowTwoOf (Y ⊓ antiUnipotent k)
      (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) := by
    refine ⟨hSP, hS.2.1, fun h => hS.2.2 (dvd_trans h ?_)⟩
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hSP inf_le_left)
  refine le_antisymm ?_ (le_inSubgroup_pCore hSP ?_ hS.2.1)
  · rw [inSubgroup_pCore_eq_pCoreOf]
    exact hSP'.pCoreOf_le
  · intro p hp
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hp.1, hp.2⟩

end CFSG.Quasithin.Ch3E213M
