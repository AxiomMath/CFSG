module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux3

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private theorem eq_one_of_mem_zTwo_of_pow_three
    {L' : Type} [Group L'] [Finite L'] {u : L'}
    (hu : u ∈ USixTwo.zTwo L') (h3 : u ^ 3 = 1) : u = 1 := by
  have h2 : orderOf u ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hu.2
  have h13 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 3 (2 ^ Nat.card L') := (by norm_num : Nat.Coprime 3 2).pow_right _
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h13 h2)

theorem e6QTwoSix_card_inf_L_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) ∧ (x ∈ L → 3 ^ 5 ≤ Nat.card ↥(Bs ⊓ L)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let conjHom : ↥Bs →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hNL)
  let A : Subgroup (MulAut ↥L) := (⊤ : Subgroup ↥Bs).map conjHom
  have hAab : IsElemAbelian 3 A := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hBs.1.is_comm.comm a.1 b.1)⟩⟩, fun a _ => ?_⟩
      exact Subtype.ext (hBs.2 a.1 a.2)
    simpa [A] using CFSG.SectionRank.isElemAbelian_map htop conjHom
  have hker : conjHom.ker = (Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hb
      have h1 : (Subgroup.inclusion hNL b) ∈ (Subgroup.normalizerMonoidHom L).ker := hb
      rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    · intro hb
      show (Subgroup.normalizerMonoidHom L) (Subgroup.inclusion hNL b) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact hb
  have hker3 : Nat.card conjHom.ker = 3 := by
    rw [hker, ← Subgroup.card_subtype Bs ((Subgroup.centralizer (L : Set G)).subgroupOf Bs),
      Subgroup.subgroupOf_map_subtype, inf_comm, hBL, Nat.card_zpowers]
    exact orderOf_eq_prime (hBs.2 x hx) hx1
  have hcardA : Nat.card A = 3 ^ 5 := by
    have h := Subgroup.card_ker_mul_card_range conjHom
    rw [hker3, hcard] at h
    have h' : Nat.card conjHom.range = 3 ^ 5 := by
      norm_num at h ⊢
      omega
    simpa [A, Subgroup.map_top] using h'
  let π : L →* UnitaryR K 1 6 := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      θ.injective (by simpa [π] using hl)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L, x (π l) = π (a l) := by
    intro a ha
    change a ∈ (⊤ : Subgroup ↥Bs).map conjHom at ha
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨ψ, hψI, hψ⟩ := hI b.1⁻¹ (Bs.inv_mem b.2)
    refine ⟨ψ, hψI, fun l => ?_⟩
    have happ : ((conjHom b) l : G) = b.1 * (l : G) * b.1⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b.1, hNL b.2⟩ l
    have h := hψ l ((conjHom b) l) (by simpa [inv_inv] using happ)
    simpa [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨ψb, hψbmk, hψbs, hψbker, hψbperf, hψbodd, hAb, hcardAb, hAIb⟩ :=
    USixTwo.six_package hK4 hπs hπker hperf hAab hAI
  have hAge : 3 ^ 4 ≤ Nat.card (A.map (USixTwo.qAutHom L)) := by
    rw [hcardAb, hcardA]
    norm_num
  obtain ⟨φ, hφM, hφdiag⟩ := USixTwo.exists_diagModel_odd hK4 hψbs hψbker hψbperf hψbodd
    hAb hAIb hAge
  have hSUcard : Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 3 * Nat.card R := by
    have h := Subgroup.card_ker_mul_card_range
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
        ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* R)
    have hsurj : Function.Surjective
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
          ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* R) :=
      QuotientGroup.mk'_surjective _
    rw [show (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).ker =
        (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) from
      QuotientGroup.ker_mk' _, USixTwo.card_scalars_subgroupOf_SU hK,
      MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top] at h
    rw [← h]
  have hQtcard : Nat.card (USixTwo.Qt L) = Nat.card R * Nat.card ψb.ker := by
    have h := Subgroup.card_ker_mul_card_of_surjective hψbs
    rw [mul_comm, h]
  have hφcard : Nat.card φ.ker * Nat.card (USixTwo.Qt L) =
      Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    have h := Subgroup.card_ker_mul_card_range φ
    rwa [MonoidHom.range_eq_top_of_surjective φ hφM.surj, Subgroup.card_top] at h
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hkey : Nat.card φ.ker * Nat.card ψb.ker = 3 := by
    have h1 : Nat.card φ.ker * Nat.card ψb.ker * Nat.card R = 3 * Nat.card R := by
      calc Nat.card φ.ker * Nat.card ψb.ker * Nat.card R
          = Nat.card φ.ker * (Nat.card R * Nat.card ψb.ker) := by ring
        _ = Nat.card φ.ker * Nat.card (USixTwo.Qt L) := by rw [← hQtcard]
        _ = Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := hφcard
        _ = 3 * Nat.card R := hSUcard
    exact Nat.eq_of_mul_eq_mul_right hRpos h1
  have htorSUelem : IsElemAbelian 3 (USixTwo.torSU K) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · refine USixTwo.torParamHom_injective (K := K) ?_
      rw [map_mul, map_mul]
      exact mul_comm _ _
    · have hpow : (⟨a, ha⟩ : ↥(USixTwo.torSU K)) ^ 3 = 1 := by
        refine USixTwo.torParamHom_injective (K := K) ?_
        rw [map_pow, map_one]
        funext i
        have h3 := pow_card_eq_one' (x := USixTwo.torParamHom (K := K) ⟨a, ha⟩ i)
        rwa [USixTwo.card_units_three hK] at h3
      exact congrArg Subtype.val hpow
  let e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSUGroup_eq_statedSU 6 (2 ^ 1))
  let T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    (USixTwo.torSU K).map e.toMonoidHom
  have hTelem : IsElemAbelian 3 T := by
    change IsElemAbelian 3 ((USixTwo.torSU K).map e.toMonoidHom)
    exact CFSG.SectionRank.isElemAbelian_map htorSUelem e.toMonoidHom
  have hTcard : Nat.card T = 3 ^ 5 := by
    change Nat.card ((USixTwo.torSU K).map e.toMonoidHom) = 3 ^ 5
    rw [Subgroup.card_map_of_injective e.injective, USixTwo.card_torSU hK]
  let Eb : Subgroup (USixTwo.Qt L) := T.map φ
  have hEbelem : IsElemAbelian 3 Eb := CFSG.SectionRank.isElemAbelian_map hTelem φ
  have hEbH : Eb ≤ (⊤ : Subgroup L).map (USixTwo.qmk L) := by
    rw [Subgroup.map_top_of_surjective _ USixTwo.qmk_surjective]
    exact le_top
  have hEbfix : ∀ a ∈ A, ∀ x ∈ Eb, USixTwo.qAutHom L a x = x := by
    intro a ha x hx
    obtain ⟨D, hD, rfl⟩ := hx
    obtain ⟨D', hD', rfl⟩ := Subgroup.mem_map.mp hD
    obtain ⟨t, ht⟩ := hφdiag (USixTwo.qAutHom L a) ⟨a, ha, rfl⟩
    have heD' : ((e D' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K) = (D' : GL (Fin 6) K) := rfl
    have hDdiag : (((e D' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K)) ∈ TauCeti.diagonalTorus K 6 := by
      rw [heD']
      exact hD'
    obtain ⟨v, hv⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hDdiag
    have hmat : (((e D' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = TauCeti.diagGL v := by
      rw [hv]
    exact ht.fix_of_diagonal (e D') (by
      rw [hmat, TauCeti.diagGL_coe])
  have hA3 : IsPGroup 3 A :=
    CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian hAab
  obtain ⟨E, hEL, hEelem, hEmap, hEfix, hEcard⟩ :=
    USixTwo.exists_elemAbelian_lift_fixed (L' := L) (A := A) hA3
      (H := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) hEbelem hEbH hEbfix
  have hEcent : E.map L.subtype ≤ Subgroup.centralizer (Bs : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbA : conjHom ⟨b, hb⟩ ∈ A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
    have hfix := hEfix (conjHom ⟨b, hb⟩) hbA e he
    have hcoe : (((conjHom ⟨b, hb⟩) e : ↥L) : G) = b * (e : L) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hNL hb⟩ e
    have hconj : b * (e : L) * b⁻¹ = (e : L) := by
      rw [← hcoe]; exact congrArg Subtype.val hfix
    change b * (e : L) = (e : L) * b
    calc b * (e : L) = b * (e : L) * b⁻¹ * b := by group
      _ = (e : L) * b := by rw [hconj]
  have hEsub : E.map L.subtype ≤ Bs := by
    rintro _ ⟨e, he, rfl⟩
    have he3 : ((e : L) : G) ^ 3 = 1 := by
      simpa using congrArg (fun x : L => (x : G)) (hEelem.2 e he)
    exact hstar (e : L) (hEcent (Subgroup.mem_map_of_mem L.subtype he)) he3
  have hEsubL : E.map L.subtype ≤ Bs ⊓ L := by
    refine le_inf hEsub ?_
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hEb_le : Nat.card Eb ≤ Nat.card ↥(Bs ⊓ L) := by
    calc Nat.card Eb = Nat.card E := hEcard.symm
      _ = Nat.card (E.map L.subtype) :=
        (Subgroup.card_map_of_injective L.subtype_injective).symm
      _ ≤ Nat.card ↥(Bs ⊓ L) := Subgroup.card_le_of_le hEsubL
  have hφkerle : Nat.card φ.ker ≤ 3 :=
    Nat.le_of_dvd (by norm_num) ⟨Nat.card ψb.ker, hkey.symm⟩
  have hrangeeq : (φ.comp T.subtype).range = Eb := by
    ext z
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨(t : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)), t.2, ht⟩
    · rintro ⟨t, ht, htz⟩
      exact ⟨⟨t, ht⟩, htz⟩
  have hrange : Nat.card (φ.comp T.subtype).range = Nat.card Eb := by rw [hrangeeq]
  have hkerinj : Nat.card (φ.comp T.subtype).ker ≤ Nat.card φ.ker := by
    apply Nat.card_le_card_of_injective (f := fun w : (φ.comp T.subtype).ker =>
      (⟨((w.1 : ↥T) : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)),
        w.2⟩ : φ.ker))
    intro u v huv
    exact Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker =>
      (z.1 : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6))) huv))
  have hEb4 : 3 ^ 4 ≤ Nat.card Eb := by
    have hTker := Subgroup.card_ker_mul_card_range (φ.comp T.subtype)
    have h1 : (3 : ℕ) ^ 5 ≤ 3 * Nat.card Eb := by
      calc (3 : ℕ) ^ 5 = Nat.card T := hTcard.symm
        _ = Nat.card (φ.comp T.subtype).ker * Nat.card (φ.comp T.subtype).range := hTker.symm
        _ = Nat.card (φ.comp T.subtype).ker * Nat.card Eb := by rw [hrange]
        _ ≤ 3 * Nat.card Eb := Nat.mul_le_mul_right _ (le_trans hkerinj hφkerle)
    have h2 : 3 * 3 ^ 4 ≤ 3 * Nat.card Eb := by
      rw [show (3 : ℕ) * 3 ^ 4 = 3 ^ 5 by norm_num]
      exact h1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  refine ⟨le_trans hEb4 hEb_le, ?_⟩
  intro hxL
  have hxcen : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx u.2)
  have hqmem : USixTwo.qmk ↥L ⟨x, hxL⟩ ∈ ψb.ker := by
    rw [MonoidHom.mem_ker, hψbmk]
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) ⟨x, hxL⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxcen
    show θ (QuotientGroup.mk' (Subgroup.center ↥L) ⟨x, hxL⟩) = 1
    rw [h1, map_one]
  have hqne : USixTwo.qmk ↥L ⟨x, hxL⟩ ≠ 1 := by
    intro h1
    have hz2 : (⟨x, hxL⟩ : ↥L) ∈ USixTwo.zTwo ↥L := (USixTwo.qmk_eq_one_iff).mp h1
    have hx3 : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hBs.2 x hx
    have hxe : (⟨x, hxL⟩ : ↥L) = 1 := eq_one_of_mem_zTwo_of_pow_three hz2 hx3
    exact hx1 (by simpa using congrArg Subtype.val hxe)
  have hbne : ψb.ker ≠ ⊥ := by
    intro hbot
    apply hqne
    have hmem : USixTwo.qmk ↥L ⟨x, hxL⟩ ∈ (⊥ : Subgroup (USixTwo.Qt ↥L)) := by
      rw [← hbot]
      exact hqmem
    simpa using hmem
  have hb3 : Nat.card ψb.ker = 3 := by
    rcases (Nat.prime_three.eq_one_or_self_of_dvd (Nat.card ψb.ker)
      ⟨Nat.card φ.ker, by rw [mul_comm]; exact hkey.symm⟩) with h | h
    · have := (Subgroup.one_lt_card_iff_ne_bot (H := ψb.ker)).mpr hbne
      omega
    · exact h
  have ha1 : Nat.card φ.ker = 1 := by rw [hb3] at hkey; omega
  have hφinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).mp (Subgroup.eq_bot_of_card_eq (H := φ.ker) ha1)
  have hEb5 : Nat.card Eb = 3 ^ 5 := by
    change Nat.card (Subgroup.map φ T) = 3 ^ 5
    rw [Subgroup.card_map_of_injective hφinj, hTcard]
  rw [← hEb5]
  exact hEb_le

end CFSG.StandardType.E6QTwo

end