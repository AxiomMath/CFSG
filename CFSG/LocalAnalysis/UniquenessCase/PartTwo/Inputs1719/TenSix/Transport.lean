module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Gamma
import CFSG.Holt.H78.Prelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix

open CFSG.Open Subgroup

variable {G X : Type*} [Group G] [Group X] [Finite G]

private theorem eq_bot_of_isPGroup_two_of_odd {Y : Type*} [Group Y] {A : Subgroup Y}
    (hA : IsPGroup 2 A) (hodd : Odd (Nat.card A)) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hA.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd h hodd.not_two_dvd_nat

private theorem normalizer_eq_comap_normalizer_map {F X : Type*} [Group F] [Group X]
    (ι : F →* X) (hι : Function.Injective ι) (T : Subgroup F) :
    Subgroup.normalizer (T : Set F) =
      (Subgroup.normalizer ((T.map ι : Subgroup X) : Set X)).comap ι := by
  refine le_antisymm (fun y hy => Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι hy))
    (fun y hy => ?_)
  rw [Subgroup.mem_comap, Subgroup.mem_normalizer_iff] at hy
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have h1 : t ∈ T ↔ ι t ∈ T.map ι := (Subgroup.mem_map_iff_mem hι (K := T) (x := t)).symm
  have h2 : y * t * y⁻¹ ∈ T ↔ ι (y * t * y⁻¹) ∈ T.map ι :=
    (Subgroup.mem_map_iff_mem hι (K := T) (x := y * t * y⁻¹)).symm
  rw [h1, h2, map_mul, map_mul, map_inv]
  exact hy (ι t)

private theorem centralizer_eq_comap_centralizer_map {F X : Type*} [Group F] [Group X]
    (ι : F →* X) (hι : Function.Injective ι) (T : Subgroup F) :
    Subgroup.centralizer (T : Set F) =
      (Subgroup.centralizer ((T.map ι : Subgroup X) : Set X)).comap ι := by
  ext y
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h z ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, h t ht]
  · intro h t ht
    apply hι
    rw [map_mul, map_mul]
    exact h (ι t) (Subgroup.mem_map_of_mem ι ht)

omit [Finite G] in
theorem card_map_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker)) {A : Subgroup G}
    (hA : IsPGroup 2 A) : Nat.card (A.map φ) = Nat.card A := by
  have hP : IsPGroup 2 ↥(A ⊓ φ.ker) := IsPGroup.to_le hA inf_le_left
  have hodd' : Odd (Nat.card ↥(A ⊓ φ.ker)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hbot : A ⊓ φ.ker = ⊥ := eq_bot_of_isPGroup_two_of_odd hP hodd'
  let f : ↥A →* ↥(A.map φ) :=
    (φ.comp A.subtype).codRestrict (A.map φ) fun x => Subgroup.mem_map_of_mem φ x.2
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  have hfi : Function.Injective f := by
    intro x y hxy
    have hφ : φ (x : G) = φ (y : G) := congrArg Subtype.val hxy
    have h1 : (x : G) * (y : G)⁻¹ ∈ A ⊓ φ.ker := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem x.2 (A.inv_mem y.2), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, mul_inv_cancel]
    rw [hbot] at h1
    refine Subtype.ext (mul_inv_eq_one.mp ?_)
    simpa using h1
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)).symm

theorem map_normalizer_eq_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker))
    {D : Subgroup G} (hD : IsPGroup 2 D) :
    (Subgroup.normalizer (D : Set G)).map φ =
      Subgroup.normalizer (D.map φ : Set X) ⊓ φ.range := by
  let q := QuotientGroup.mk' φ.ker
  let k := QuotientGroup.kerLift φ
  have hk : Function.Injective k := QuotientGroup.kerLift_injective φ
  have hcomp : k.comp q = φ := MonoidHom.ext fun g => QuotientGroup.kerLift_mk φ g
  have hkrange : k.range = φ.range := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective φ.ker y
      exact ⟨g, (QuotientGroup.kerLift_mk φ g).symm⟩
    · rintro x ⟨g, rfl⟩
      exact ⟨q g, QuotientGroup.kerLift_mk φ g⟩
  calc (Subgroup.normalizer (D : Set G)).map φ
      = ((Subgroup.normalizer (D : Set G)).map q).map k := by
        rw [Subgroup.map_map, hcomp]
    _ = (Subgroup.normalizer ((D.map q : Subgroup (G ⧸ φ.ker)) :
            Set (G ⧸ φ.ker))).map k := by
        rw [CFSG.Holt.H78.map_normalizer_eq_of_odd φ.ker hodd hD]
    _ = ((Subgroup.normalizer (((D.map q).map k : Subgroup X) : Set X)).comap k).map k := by
        rw [normalizer_eq_comap_normalizer_map k hk]
    _ = k.range ⊓ Subgroup.normalizer ((D.map q).map k : Set X) := Subgroup.map_comap_eq k _
    _ = Subgroup.normalizer (D.map φ : Set X) ⊓ φ.range := by
        rw [hkrange, Subgroup.map_map, hcomp, inf_comm]

theorem map_inf_normalizer_eq_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker))
    {D H : Subgroup G} (hD : IsPGroup 2 D) (hker : φ.ker ≤ H) :
    (H ⊓ Subgroup.normalizer (D : Set G)).map φ =
      H.map φ ⊓ Subgroup.normalizer (D.map φ : Set X) := by
  refine le_antisymm ?_ ?_
  · have hsub : H.map φ ≤ φ.range := by
      rintro _ ⟨h, hh, rfl⟩
      exact ⟨h, rfl⟩
    calc (H ⊓ Subgroup.normalizer (D : Set G)).map φ
        ≤ H.map φ ⊓ (Subgroup.normalizer (D : Set G)).map φ := Subgroup.map_inf_le _ _ _
      _ = H.map φ ⊓ (Subgroup.normalizer (D.map φ : Set X) ⊓ φ.range) := by
          rw [map_normalizer_eq_of_odd_ker φ hodd hD]
      _ = H.map φ ⊓ Subgroup.normalizer (D.map φ : Set X) := by
          rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hsub)]
  · rintro x ⟨hxH, hxN⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hxH
    have hx : φ h ∈ Subgroup.normalizer (D.map φ : Set X) ⊓ φ.range :=
      Subgroup.mem_inf.mpr ⟨hxN, ⟨h, rfl⟩⟩
    rw [← map_normalizer_eq_of_odd_ker φ hodd hD] at hx
    obtain ⟨k, hk, hkφ⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨k, Subgroup.mem_inf.mpr ⟨?_, hk⟩, hkφ⟩
    have hmem : k * h⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkφ, mul_inv_cancel]
    rw [show k = (k * h⁻¹) * h from by group]
    exact H.mul_mem (hker hmem) hh

theorem map_gammaRk_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker)) {m : ℕ}
    {A H : Subgroup G} (hA : IsPGroup 2 A) (hker : φ.ker ≤ H) :
    (gammaRk m A H).map φ = gammaRk m (A.map φ) (H.map φ) := by
  have hrel : ∀ D : Subgroup G, D ≤ A →
      (H ⊓ Subgroup.normalizer (D : Set G)).map φ =
        H.map φ ⊓ Subgroup.normalizer (D.map φ : Set X) :=
    fun D hDA => map_inf_normalizer_eq_of_odd_ker φ hodd (IsPGroup.to_le hA hDA) hker
  have hpre : ∀ D' : Subgroup X, D' ≤ A.map φ →
      ∃ D : Subgroup G, D ≤ A ∧ D.map φ = D' ∧ Nat.card D = Nat.card D' := by
    intro D' hD'
    have hAle : A.map φ ≤ φ.range := by
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
    have hmap : (A ⊓ D'.comap φ).map φ = D' := by
      refine le_antisymm ?_ ?_
      · calc (A ⊓ D'.comap φ).map φ
            ≤ A.map φ ⊓ (D'.comap φ).map φ := Subgroup.map_inf_le _ _ _
          _ = A.map φ ⊓ (φ.range ⊓ D') := by rw [Subgroup.map_comap_eq]
          _ = (A.map φ ⊓ φ.range) ⊓ D' := by rw [inf_assoc]
          _ = A.map φ ⊓ D' := by rw [inf_eq_left.mpr hAle]
          _ = D' := by rw [inf_eq_right.mpr hD']
      · rintro y hy
        obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp (hD' hy)
        exact ⟨a, Subgroup.mem_inf.mpr ⟨ha, by rw [Subgroup.mem_comap, hay]; exact hy⟩, hay⟩
    refine ⟨A ⊓ D'.comap φ, inf_le_left, hmap, ?_⟩
    rw [← card_map_of_odd_ker φ hodd (IsPGroup.to_le hA inf_le_left), hmap]
  refine le_antisymm ?_ ?_
  · rw [gammaRk]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun D => iSup_le fun hDA => iSup_le fun hD => ?_
    rw [hrel D hDA]
    refine le_iSup_of_le (D.map φ)
      (le_iSup_of_le (Subgroup.map_mono hDA) (le_iSup_of_le ?_ le_rfl))
    rw [card_map_of_odd_ker φ hodd (IsPGroup.to_le hA hDA)]
    exact hD
  · rw [gammaRk]
    refine iSup_le fun D' => iSup_le fun hD'A => iSup_le fun hD'card => ?_
    obtain ⟨D, hDA, hDmap, hDcard⟩ := hpre D' hD'A
    rw [← hDmap, ← hrel D hDA]
    refine Subgroup.map_mono (le_iSup_of_le D (le_iSup_of_le hDA (le_iSup_of_le ?_ le_rfl)))
    rw [hDcard]
    exact hD'card

theorem map_centralizer_eq_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker))
    {B : Subgroup G} (hB : IsPGroup 2 B) :
    (Subgroup.centralizer (B : Set G)).map φ =
      Subgroup.centralizer (B.map φ : Set X) ⊓ φ.range := by
  let q := QuotientGroup.mk' φ.ker
  let k := QuotientGroup.kerLift φ
  have hk : Function.Injective k := QuotientGroup.kerLift_injective φ
  have hcomp : k.comp q = φ := MonoidHom.ext fun g => QuotientGroup.kerLift_mk φ g
  have hkrange : k.range = φ.range := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective φ.ker y
      exact ⟨g, (QuotientGroup.kerLift_mk φ g).symm⟩
    · rintro x ⟨g, rfl⟩
      exact ⟨q g, QuotientGroup.kerLift_mk φ g⟩
  calc (Subgroup.centralizer (B : Set G)).map φ
      = ((Subgroup.centralizer (B : Set G)).map q).map k := by
        rw [Subgroup.map_map, hcomp]
    _ = (Subgroup.centralizer ((B.map q : Subgroup (G ⧸ φ.ker)) :
            Set (G ⧸ φ.ker))).map k := by
        rw [CFSG.Holt.H78.map_centralizer_eq_of_odd φ.ker hodd hB]
    _ = ((Subgroup.centralizer (((B.map q).map k : Subgroup X) : Set X)).comap k).map k := by
        rw [centralizer_eq_comap_centralizer_map k hk]
    _ = k.range ⊓ Subgroup.centralizer ((B.map q).map k : Set X) := Subgroup.map_comap_eq k _
    _ = Subgroup.centralizer (B.map φ : Set X) ⊓ φ.range := by
        rw [hkrange, Subgroup.map_map, hcomp, inf_comm]

theorem map_inf_centralizer_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker))
    {B H : Subgroup G} (hB : IsPGroup 2 B) (hBH : B ≤ H) :
    (H ⊓ centralizer (B : Set G)).map φ =
      H.map φ ⊓ centralizer ((B.map φ : Subgroup X) : Set X) := by
  let ψ : ↥H →* X := φ.comp H.subtype
  have hB' : IsPGroup 2 ↥(B.subgroupOf H) :=
    IsPGroup.comap_of_injective hB H.subtype H.subtype_injective
  have hker : ψ.ker = (φ.ker).subgroupOf H := by
    ext x
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hcard : Nat.card ↥((φ.ker).subgroupOf H) = Nat.card ↥(H ⊓ φ.ker) := by
    rw [show (φ.ker).subgroupOf H = (H ⊓ φ.ker).subgroupOf H from by
      ext x
      simp [Subgroup.mem_subgroupOf]]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hodd' : Odd (Nat.card ψ.ker) := by
    rw [hker, hcard]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hfull := map_centralizer_eq_of_odd_ker (G := ↥H) ψ hodd' hB'
  have hC : Subgroup.centralizer ((B.subgroupOf H) : Set ↥H) =
      (Subgroup.centralizer (B : Set G)).comap H.subtype := by
    rw [centralizer_eq_comap_centralizer_map H.subtype H.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le hBH]
  have hLHS : (Subgroup.centralizer ((B.subgroupOf H) : Set ↥H)).map ψ =
      (H ⊓ Subgroup.centralizer (B : Set G)).map φ := by
    rw [hC, ← Subgroup.map_map, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hmapB : (B.subgroupOf H).map ψ = B.map φ := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hBH]
  have hrange : ψ.range = H.map φ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hLHS, hmapB, hrange] at hfull
  exact hfull.trans (inf_comm _ _)

omit [Finite G] in
theorem map_pCoreOf_le (φ : G →* X) (p : ℕ) (H : Subgroup G) :
    (pCoreOf p H).map φ ≤ pCoreOf p (H.map φ) := by
  have hp : IsPGroup p ↥((pCoreOf p H).map φ) := by
    have h := (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map (φ.comp H.subtype)
    rwa [pCoreOf, Subgroup.map_map]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le p H)) ?_ hp
  exact (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p H)).trans
    (Subgroup.le_normalizer_map φ)

omit [Finite G] in
private theorem normalizer_map_subtype {Y : Subgroup G} (D' : Subgroup ↥Y) :
    (Subgroup.normalizer (D' : Set ↥Y)).map Y.subtype =
      Y ⊓ Subgroup.normalizer ((D'.map Y.subtype : Subgroup G) : Set G) := by
  have hle : D'.map Y.subtype ≤ Y := Subgroup.map_subtype_le D'
  have hsub : (D'.map Y.subtype).subgroupOf Y = D' := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  have hN : (Subgroup.normalizer ((D'.map Y.subtype : Subgroup G) : Set G)).subgroupOf Y =
      Subgroup.normalizer (D' : Set ↥Y) := by
    rw [Subgroup.subgroupOf_normalizer_eq hle, hsub]
  rw [← hN, Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]

omit [Finite G] in
theorem gammaRk_subgroupOf {m : ℕ} {A Y : Subgroup G} (hAY : A ≤ Y) :
    (gammaRk m A Y).subgroupOf Y = gammaRk m (A.subgroupOf Y) ⊤ := by
  have hmain : gammaRk m A Y = (gammaRk m (A.subgroupOf Y) ⊤).map Y.subtype := by
    refine le_antisymm ?_ ?_
    · conv_lhs => rw [gammaRk]
      refine iSup_le fun D => iSup_le fun hDA => iSup_le fun hD => ?_
      have hDY : D ≤ Y := hDA.trans hAY
      have hcardD : Nat.card (D.subgroupOf Y) = Nat.card D := by
        rw [← Subgroup.card_map_of_injective Y.subtype_injective (K := D.subgroupOf Y),
          Subgroup.map_subgroupOf_eq_of_le hDY]
      calc Y ⊓ Subgroup.normalizer (D : Set G)
          = (Subgroup.normalizer (D.subgroupOf Y : Set ↥Y)).map Y.subtype := by
            rw [normalizer_map_subtype, Subgroup.map_subgroupOf_eq_of_le hDY]
        _ ≤ (gammaRk m (A.subgroupOf Y) ⊤).map Y.subtype :=
            Subgroup.map_mono (le_iSup_of_le (D.subgroupOf Y) (le_iSup_of_le
              (Subgroup.comap_mono hDA) (le_iSup_of_le (by rw [hcardD]; exact hD)
                (le_inf le_top le_rfl))))
    · conv_lhs => rw [gammaRk]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun D' => iSup_le fun hD' => iSup_le fun hcard => ?_
      have hA' : D'.map Y.subtype ≤ A := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hAY]
        exact Subgroup.map_mono hD'
      have hcard' : 2 ^ m ≤ Nat.card (D'.map Y.subtype) := by
        rwa [Subgroup.card_map_of_injective Y.subtype_injective]
      calc (⊤ ⊓ Subgroup.normalizer (D' : Set ↥Y)).map Y.subtype
          = (Subgroup.normalizer (D' : Set ↥Y)).map Y.subtype := by rw [top_inf_eq]
        _ = Y ⊓ Subgroup.normalizer ((D'.map Y.subtype : Subgroup G) : Set G) :=
            normalizer_map_subtype D'
        _ ≤ gammaRk m A Y := le_iSup_of_le (D'.map Y.subtype) (le_iSup_of_le hA'
            (le_iSup_of_le hcard' le_rfl))
  rw [hmain]
  change Subgroup.comap Y.subtype (Subgroup.map Y.subtype (gammaRk m (A.subgroupOf Y) ⊤)) = _
  rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]

omit [Finite G] in
theorem pCoreOf_subgroupOf (p : ℕ) {H Y : Subgroup G} (hHY : H ≤ Y) :
    (pCoreOf p H).subgroupOf Y = pCoreOf p (H.subgroupOf Y) := by
  let K := H.subgroupOf Y
  let ι : ↥K ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHY
  have hsub : H.subtype = (Y.subtype.comp K.subtype).comp ι.symm.toMonoidHom := by
    ext x
    rfl
  have hmain : (CFSG.pCore p ↥H).map H.subtype =
      ((CFSG.pCore p ↥K).map K.subtype).map Y.subtype := by
    calc (CFSG.pCore p ↥H).map H.subtype
        = (CFSG.pCore p ↥H).map ((Y.subtype.comp K.subtype).comp ι.symm.toMonoidHom) := by
          rw [hsub]
      _ = ((CFSG.pCore p ↥H).map ι.symm.toMonoidHom).map (Y.subtype.comp K.subtype) := by
          rw [← Subgroup.map_map]
      _ = (((CFSG.pCore p ↥H).map ι.symm.toMonoidHom).map K.subtype).map Y.subtype := by
          rw [← Subgroup.map_map]
      _ = ((CFSG.pCore p ↥K).map K.subtype).map Y.subtype := by
          rw [CFSG.pCore_map_iso]
  rw [pCoreOf, pCoreOf, hmain]
  change Subgroup.comap Y.subtype
    (Subgroup.map Y.subtype ((CFSG.pCore p ↥K).map K.subtype)) = (CFSG.pCore p ↥K).map K.subtype
  rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix
