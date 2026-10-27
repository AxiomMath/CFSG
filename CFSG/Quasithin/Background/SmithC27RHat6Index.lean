module

public import CFSG.Quasithin.Background.SmithC27RHat6Coord
public import CFSG.Quasithin.Background.SmithC27RJ

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem mem_iff_starHom_mem (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hKC : K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K) (k : ↥K) :
    (k : G) ∈ M ↔
      ((starK hs k : ↥(autOn K V)) : MulAut ↥V) ∈ autOn (M ⊓ K) V := by
  refine ⟨fun hk => mem_autOn_iff'.2 ⟨⟨k, hs.K_le_normalizer_V k.2⟩, ⟨hk, k.2⟩, rfl⟩,
    fun hk => ?_⟩
  obtain ⟨n, hn, hne⟩ := mem_autOn_iff'.1 hk
  have hc : (n : G)⁻¹ * k ∈ K ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨K.mul_mem (K.inv_mem hn.2) k.2, ?_⟩
    have h1 : conjAct V (n⁻¹ * ⟨k, hs.K_le_normalizer_V k.2⟩) = 1 := by
      rw [map_mul, map_inv, hne, coe_starK, inv_mul_cancel]
    exact (conjAct_eq_one_iff' _).1 h1
  rw [hKC] at hc
  have e : (k : G) = n * ((n : G)⁻¹ * k) := by group
  rw [e]
  exact M.mul_mem hn.1 (pCore_K_le_M h hs hc)

theorem card_D_le_four (hs : StarHyp R K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hK : Nat.card ↥(autOn K V) = 1080) : Nat.card ↥(autOn (R ⊓ K) V) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDK : autOn (R ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  have hD2 : IsPGroup 2 ↥(autOn (R ⊓ K) V) := isPGroup_autOn (hs.pgroup.to_le inf_le_left)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hD2
  have hdvd : 2 ^ b ∣ 1080 := hb ▸ hK ▸ Subgroup.card_dvd_of_le hDK
  have h8 := two_pow_le_eight_of_dvd hdvd
  have hb3 : b ≤ 3 := by
    by_contra hb3
    have : 2 ^ 4 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hb]
  by_contra h4
  obtain rfl : b = 3 := by
    interval_cases b <;> first | rfl | (norm_num at h4)
  have hidx := card_eq_index_mul' hDK
  rw [hK, hb] at hidx
  apply hnS
  refine isSylowTwoOf_R_of_sylow_le hs ⟨hDK, hD2, fun h2 => ?_⟩ (autOn_mono' inf_le_left)
  obtain ⟨c, hc⟩ := h2
  omega

omit [Finite G] in
theorem coe_mem_inf_normalizer_of_mem_center {L S : Subgroup (MulAut ↥V)} (hSL : S ≤ L)
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) :
    (z : MulAut ↥V) ∈ L ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) := by
  refine ⟨z.2, Subgroup.centralizer_le_normalizer _ ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hSL hs⟩)

theorem relIndex_eq_fifteen (h : Hyp27 H R M K) (hs : StarHyp R K V) (hB : IsHatA6Block K)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (hP : IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V))
    (hO : pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V) : M.relIndex K = 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC := inf_centralizer_eq_of_hatA6 h hs hB
  have hHat := isHat_autOn_of_hatA6 h hs hB
  have hK := card_autOn_of_hatA6 h hs hB
  have hD4 := card_D_le_four hs hnS hK
  obtain ⟨⟨hPK, S, hS, hSN⟩, hPne, -⟩ := hP
  have hS8 : Nat.card ↥S = 8 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS.2.1
    have hidx := card_eq_index_mul' hS.1
    rw [hK, ha] at hidx
    rw [ha]
    exact two_pow_eq_eight_of_mul_odd (by rw [hidx, mul_comm]) hS.2.2
  have hZN := fun z (hz : z ∈ Subgroup.center ↥(autOn K V)) =>
    coe_mem_inf_normalizer_of_mem_center hS.1 hz
  have hZP : Subgroup.center ↥(autOn K V) ≤ (autOn (M ⊓ K) V).subgroupOf (autOn K V) :=
    fun z hz => Subgroup.mem_subgroupOf.2 (hSN (hZN z hz))
  have hZ3 : Nat.card ↥(Subgroup.center ↥(autOn K V)) = 3 := hHat.2.1
  have hZm : Nat.card ↥((Subgroup.center ↥(autOn K V)).map (autOn K V).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (autOn K V).subtype_injective, hZ3]
  have hZmN : (Subgroup.center ↥(autOn K V)).map (autOn K V).subtype ≤
      autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZN z hz
  have hSN' : S ≤ autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) :=
    le_inf hS.1 Subgroup.le_normalizer
  have h8 : 8 ∣ Nat.card ↥(autOn (M ⊓ K) V) := hS8 ▸ Subgroup.card_dvd_of_le (hSN'.trans hSN)
  have h3 : 3 ∣ Nat.card ↥(autOn (M ⊓ K) V) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, ← hZ3]
    exact Subgroup.card_dvd_of_le hZP
  have h24 : 24 ∣ Nat.card ↥(autOn (M ⊓ K) V) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  have hmul := card_eq_index_mul' hPK
  rw [hK] at hmul
  have hcases := index_cases_1080 (by rw [hmul, mul_comm]) h24
  have hi1 : ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).index ≠ 1 := by
    intro h1
    apply hPne
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact le_antisymm hPK h1
  have hi45 : ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).index ≠ 45 := by
    intro h45
    rw [h45] at hmul
    have hN8 : 8 ∣ Nat.card ↥(autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V))) :=
      hS8 ▸ Subgroup.card_dvd_of_le hSN'
    have hN3 : 3 ∣ Nat.card ↥(autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V))) :=
      hZm ▸ Subgroup.card_dvd_of_le hZmN
    have hN24 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) hN8 hN3
    have hNeq : autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) = autOn (M ⊓ K) V :=
      Subgroup.eq_of_le_of_card_ge hSN (by
        have := Nat.le_of_dvd Nat.card_pos hN24
        omega)
    have hSO : S ≤ pCoreOf 2 (autOn (M ⊓ K) V) :=
      le_pCoreOf_of_le_normalizer 2 (hSN'.trans hSN) (hNeq ▸ inf_le_right) hS.2.1
    rw [hO] at hSO
    have := Subgroup.card_le_of_le hSO
    omega
  have hi15 : ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).index = 15 := by
    rcases index_cases_of_isHat hHat hZP with h1 | ⟨h6, h9⟩ <;> omega
  have hcomap : M.subgroupOf K = ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).comap
      (starK hs) := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact mem_iff_starHom_mem h hs hKC k
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ (starK_surjective hs),
    hi15]

end CFSG.Quasithin.SmithC27
