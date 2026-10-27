module

public import CFSG.Quasithin.Vol2.Ch9Sec3FFCLie
public import CFSG.Quasithin.EmptyFaithful.S1421QA21D4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain

public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem map_eq_of_le_normalizer {X : Type} [Group X] [Finite X] {U R : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hUR : U ≤ R) (hR : R ≤ Subgroup.normalizer (U : Set X))
    (α : MulAut X) (hαR : R.map α.toMonoidHom = R) : U.map α.toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : U.map α.toMonoidHom ≤ R := by
    rw [← hαR]
    exact Subgroup.map_mono hUR
  have hsup : U.map α.toMonoidHom ⊔ U = U :=
    hU.eq_of_le le_sup_right le_top ((hU.2.1.map _).to_sup_of_normal_right' hU.2.1 (hle.trans hR))
  exact Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hsup.le)
    (Subgroup.card_map_of_injective α.injective).ge

theorem bor_of_isSL3 {X : Type} [Group X] [Finite X] (h : IsSL3 4 X) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (A : Subgroup X) (hUA : U ≤ A) (hA : Group.IsSolvable ↥A) :
    A ≤ Subgroup.normalizer (U : Set X) := by
  obtain ⟨X', _, _, π, hπ, hker, hker3, hX'⟩ := FFC.exists_isPSL_of_isSL3 h
  obtain ⟨P, -, hE⟩ := Rk2.rank2PkgExt_exists_psl3 le_rfl hX'
    (FFC.isSylowTwoOf_map_of_surjective hU hπ)
  have hAs : Group.IsSolvable ↥(A.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective A)
  have hAN := hE.solvable_le_normalizer (A.map π) (Subgroup.map_mono hUA) hAs
  intro a ha
  have haN := hAN ⟨a, ha, rfl⟩
  have hle : U.map (MulAut.conj a).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    show a * u * a⁻¹ ∈ U
    have hw : π (a * u * a⁻¹) ∈ U.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp haN (π u)).mp ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hu'w⟩ := hw
    set k := u'⁻¹ * (a * u * a⁻¹) with hk
    have hkker : k ∈ π.ker := by
      rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hu'w, inv_mul_cancel]
    have hwk : a * u * a⁻¹ = u' * k := by rw [hk, mul_inv_cancel_left]
    obtain ⟨m, hm⟩ := hU.2.1 ⟨u, hu⟩
    obtain ⟨m', hm'⟩ := hU.2.1 ⟨u', hu'⟩
    have hum : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hu'm : u' ^ 2 ^ m' = 1 := by simpa using congrArg Subtype.val hm'
    have hcomm : Commute u' k := Subgroup.mem_center_iff.mp (hker hkker) u'
    have hN : (a * u * a⁻¹) ^ 2 ^ (m + m') = 1 := by
      rw [conj_pow, pow_add, pow_mul, hum, one_pow, mul_one, mul_inv_cancel]
    have hk2 : k ^ 2 ^ (m + m') = 1 := by
      have h1 : (u' * k) ^ 2 ^ (m + m') = 1 := hwk ▸ hN
      have h2 : u' ^ 2 ^ (m + m') = 1 := by
        rw [show 2 ^ (m + m') = 2 ^ m' * 2 ^ m by rw [pow_add, mul_comm], pow_mul, hu'm, one_pow]
      rwa [hcomm.mul_pow, h2, one_mul] at h1
    have hk1 : k = 1 := by
      have hcop : Nat.gcd 3 (2 ^ (m + m')) = 1 := Nat.Coprime.pow_right _ (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨hker3 k hkker, hk2⟩
      rwa [hcop, pow_one] at this
    rw [hwk, hk1, mul_one]
    exact hu'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj a).injective).ge

section Lie


theorem exists_res_bor {X : Type} [Group X] [Finite X]
    (h : IsPSL 3 2 2 X ∨ IsSL3 4 X ∨ IsPSp4 2 2 X ∨ IsG2 2 2 X ∨ Is3D4 2 2 X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup X, ResidualOvergroupsAt X U P ∧
      ∀ A : Subgroup X, U ≤ A → Group.IsSolvable ↥A → A ≤ Subgroup.normalizer (U : Set X) := by
  rcases h with h | h | h | h | h
  · obtain ⟨P, hP⟩ := FFC.exists_borelPkg (Or.inl h) hU
    exact ⟨P, hP.res, hP.solv⟩
  · obtain ⟨P, hP⟩ := Rk2.rank2Pkg_exists_sl3 (n := 2) le_rfl h hU
    exact ⟨P, hP.res, bor_of_isSL3 h hU⟩
  · obtain ⟨P, hP⟩ := FFC.exists_borelPkg (Or.inr (Or.inl h)) hU
    exact ⟨P, hP.res, hP.solv⟩
  · obtain ⟨P, hP⟩ := FFC.exists_borelPkg (Or.inr (Or.inr h)) hU
    exact ⟨P, hP.res, hP.solv⟩
  · obtain ⟨P, hP⟩ := QA21.borelPkg_3d4 le_rfl h hU
    exact ⟨P, hP.res, hP.solv⟩

theorem le_normalizer_of_three_lie {Y : Type} [Group Y] [Finite Y] {T B L D : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hL : L ∈ cComp ⊤) (hBL : B < L)
    (hLn : L.Normal)
    (hLie : IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L)
    (hD3 : IsPGroup 3 D) (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y))
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) : D ≤ Subgroup.normalizer (B : Set Y) := by
  obtain ⟨hU, hX, hBp, hBs, hBX, hUB⟩ := FFC.block_data hT hB hL hBL hLn hTB
  obtain ⟨P, hres, hbor⟩ := exists_res_bor hLie hU
  have hle : (((D ⊔ T) ⊓ L).subgroupOf L).map L.subtype ≤ D ⊔ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp hx).1
  have : Group.IsSolvable ↥(D ⊔ T) := FFC.isSolvable_sup_of_mul_comm hD3 hT.2.1 hDT
  have hRs : Group.IsSolvable ↥(((D ⊔ T) ⊓ L).subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hle).comp (Subgroup.equivMapOfInjective _ L.subtype
        L.subtype_injective).toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  have hUR : (T ⊓ L).subgroupOf L ≤ ((D ⊔ T) ⊓ L).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx).1,
      (Subgroup.mem_subgroupOf.mp hx).2⟩
  have hRN := hbor _ hUR hRs
  have := hLn
  intro d hd
  set α : MulAut ↥L := MulAut.conjNormal d with hα
  have hαx : ∀ x : ↥L, (α x : Y) = d * x * d⁻¹ := fun x => by
    rw [hα, MulAut.conjNormal_apply]
  have hfix : ∀ H : Subgroup Y, d ∈ Subgroup.normalizer (H : Set Y) →
      (H.subgroupOf L).map α.toMonoidHom = H.subgroupOf L := by
    intro H hdH
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective α.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : Y) ∈ H := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hαx]
    exact (Subgroup.mem_normalizer_iff.mp hdH x).mp hx'
  have hdR : d ∈ Subgroup.normalizer (((D ⊔ T) ⊓ L : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (Subgroup.mem_sup_left hd : d ∈ D ⊔ T)) x
    have h2 : x ∈ L ↔ d * x * d⁻¹ ∈ L := ⟨fun h => hLn.conj_mem x h d, fun h => by
      simpa [mul_assoc] using hLn.conj_mem _ h d⁻¹⟩
    simp only [Subgroup.mem_inf] at h1 ⊢
    exact and_congr h1 h2
  have hαU := map_eq_of_le_normalizer hU hUR hRN α (hfix _ hdR)
  have hodd : Odd (orderOf α) := by
    obtain ⟨k, hk⟩ := hD3 ⟨d, hd⟩
    have h1 : orderOf d ∣ 3 ^ k := by
      rw [← Subgroup.orderOf_mk d hd]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Odd.of_dvd_nat (Odd.pow (by decide)) ((orderOf_map_dvd _ d).trans h1)
  have hαB := FFC.map_eq_of_residual hres hU.2.1 hX hBp hBs hBX hUB α hodd hαU
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj d).injective).ge
  rintro _ ⟨b, hb, rfl⟩
  have h1 : α ⟨b, hBL.le hb⟩ ∈ (B.subgroupOf L).map α.toMonoidHom :=
    ⟨⟨b, hBL.le hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  rw [hαB, Subgroup.mem_subgroupOf, hαx] at h1
  exact h1

end Lie

end CFSG.Quasithin.H13.Ch9.TN
