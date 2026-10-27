module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDescent
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCoverTorusAux
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open CFSG.SeitzReduction.UnitaryPilot

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

omit [Finite G] [Finite K] in
private theorem conjAction_props {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    let conjHom : ↥Bs →* MulAut ↥L :=
      (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hNL)
    let A : Subgroup (MulAut ↥L) := (⊤ : Subgroup ↥Bs).map conjHom
    IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      (∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L,
        x (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
          θ (QuotientGroup.mk' (Subgroup.center L) (a l))) := by
  classical
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
  have hcardA : Nat.card A = 3 ^ 4 := by
    have h := Subgroup.card_ker_mul_card_range conjHom
    rw [hker3, hcard] at h
    have h' : Nat.card conjHom.range = 3 ^ 4 := by
      norm_num at h ⊢
      omega
    simpa [A, Subgroup.map_top] using h'
  have hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L,
      x (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
        θ (QuotientGroup.mk' (Subgroup.center L) (a l)) := by
    intro a ha
    change a ∈ (⊤ : Subgroup ↥Bs).map conjHom at ha
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨ψ, hψI, hψ⟩ := hI b.1⁻¹ (Bs.inv_mem b.2)
    refine ⟨ψ, hψI, fun l => ?_⟩
    have happ : ((conjHom b) l : G) = b.1 * (l : G) * b.1⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b.1, hNL b.2⟩ l
    have h := hψ l ((conjHom b) l) (by simpa [inv_inv] using happ)
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h
  exact ⟨hAab, hcardA, hAI⟩

private theorem exists_diagModel_of_action
    (hK : Nat.card K = 4) {L : Subgroup G} {A : Subgroup (MulAut ↥L)}
    (hperf : commutator ↥L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hAab : IsElemAbelian 3 A) (hcardA : Nat.card A = 3 ^ 4)
    (hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L,
        x (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
          θ (QuotientGroup.mk' (Subgroup.center L) (a l))) :
    ∃ (ψb : USixTwo.Qt L →* UnitaryR K 1 6)
      (φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L),
      Function.Surjective ψb ∧ UnitTB.Model φ ∧
        (∀ a ∈ A.map (USixTwo.qAutHom L), ∃ t : Fin 6 → K,
          CFSG.StandardType.LineU.ActsDiagU φ a t) := by
  classical
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let π : L →* UnitaryR K 1 6 := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      θ.injective (by simpa [π] using hl)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hAI' : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L, x (π l) = π (a l) := by
    intro a ha
    obtain ⟨x, hx, hxl⟩ := hAI a ha
    exact ⟨x, hx, fun l => by simpa [π] using hxl l⟩
  obtain ⟨ψb, -, hψbs, hψbker, hψbperf, hψbodd, hAb, hcardAb, hAIb⟩ :=
    USixTwo.six_package hK4 hπs hπker hperf hAab hAI'
  have hAge : 3 ^ 4 ≤ Nat.card (A.map (USixTwo.qAutHom L)) := by
    rw [hcardAb]
    exact le_of_eq hcardA.symm
  obtain ⟨φ, hφM, hφdiag⟩ := USixTwo.exists_diagModel_odd hK4 hψbs hψbker hψbperf hψbodd
    hAb hAIb hAge
  exact ⟨ψb, φ, hψbs, hφM, hφdiag⟩

private theorem ker_ne_bot_of_not_isPGroup_center
    (hK : Nat.card K = 4) {L : Subgroup G}
    {ψb : USixTwo.Qt L →* UnitaryR K 1 6} (hψbs : Function.Surjective ψb)
    (hZ : ¬ IsPGroup 2 (Subgroup.center L)) : ψb.ker ≠ ⊥ := by
  intro hbot
  apply hZ
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hinj : Function.Injective ψb := (MonoidHom.ker_eq_bot_iff ψb).mp hbot
  have hZQt : Subgroup.center (USixTwo.Qt L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzR : ψb z ∈ Subgroup.center (UnitaryR K 1 6) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨y, rfl⟩ := hψbs r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [USixTwo.six_center_eq_bot hK4, Subgroup.mem_bot] at hzR
    exact hinj (by rw [hzR, map_one])
  have hcenter_le : Subgroup.center L ≤ USixTwo.zTwo L := by
    intro z hz
    have hzQt : USixTwo.qmk L z ∈ Subgroup.center (USixTwo.Qt L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := USixTwo.qmk_surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
    rw [hZQt, Subgroup.mem_bot] at hzQt
    exact (USixTwo.qmk_eq_one_iff).mp hzQt
  exact USixTwo.isPGroup_zTwo.to_le hcenter_le

private theorem card_ker_eq_three_and_injective
    (hK : Nat.card K = 4) {L : Subgroup G}
    {ψb : USixTwo.Qt L →* UnitaryR K 1 6} (hψbs : Function.Surjective ψb)
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    (hφM : UnitTB.Model φ) (hkerne : ψb.ker ≠ ⊥) :
    Nat.card ψb.ker = 3 ∧ Function.Injective φ := by
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
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
  have hbpos : 1 < Nat.card ψb.ker := (Subgroup.one_lt_card_iff_ne_bot (H := ψb.ker)).mpr hkerne
  have hb3 : Nat.card ψb.ker = 3 := by
    rcases (Nat.prime_three.eq_one_or_self_of_dvd (Nat.card ψb.ker)
      ⟨Nat.card φ.ker, by rw [mul_comm]; exact hkey.symm⟩) with h | h
    · omega
    · exact h
  have ha1 : Nat.card φ.ker = 1 := by
    rw [hb3] at hkey
    omega
  exact ⟨hb3, (MonoidHom.ker_eq_bot_iff φ).mp (Subgroup.eq_bot_of_card_eq (H := φ.ker) ha1)⟩

private theorem torus_image_props (hK : Nat.card K = 4) {L : Subgroup G}
    {e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    {T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hT : T = (USixTwo.torSU K).map e.toMonoidHom)
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    (hφinj : Function.Injective φ)
    {Eb : Subgroup (USixTwo.Qt L)} (hEb : Eb = T.map φ) :
    IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 5 ∧ IsElemAbelian 3 Eb ∧
      Eb ≤ (⊤ : Subgroup L).map (USixTwo.qmk L) ∧ Nat.card Eb = 3 ^ 5 := by
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
  have hTelem : IsElemAbelian 3 T := by
    rw [hT]
    exact CFSG.SectionRank.isElemAbelian_map htorSUelem e.toMonoidHom
  have hTcard : Nat.card T = 3 ^ 5 := by
    rw [hT, Subgroup.card_map_of_injective e.injective, USixTwo.card_torSU hK]
  have hEbelem : IsElemAbelian 3 Eb := by
    rw [hEb]
    exact CFSG.SectionRank.isElemAbelian_map hTelem φ
  have hEbH : Eb ≤ (⊤ : Subgroup L).map (USixTwo.qmk L) := by
    rw [Subgroup.map_top_of_surjective _ USixTwo.qmk_surjective]
    exact le_top
  have hEbcard : Nat.card Eb = 3 ^ 5 := by
    rw [hEb, Subgroup.card_map_of_injective hφinj, hTcard]
  exact ⟨hTelem, hTcard, hEbelem, hEbH, hEbcard⟩

omit [Finite K] in
private theorem fixed_of_diagonal {L : Subgroup G}
    {e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    {T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hT : T = (USixTwo.torSU K).map e.toMonoidHom)
    (he : ∀ x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      ((e x : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K) = (x : GL (Fin 6) K))
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    {Eb : Subgroup (USixTwo.Qt L)} (hEb : Eb = T.map φ)
    {A : Subgroup (MulAut ↥L)}
    (hφdiag : ∀ a ∈ A.map (USixTwo.qAutHom L), ∃ t : Fin 6 → K,
      CFSG.StandardType.LineU.ActsDiagU φ a t) :
    ∀ a ∈ A, ∀ x ∈ Eb, USixTwo.qAutHom L a x = x := by
  intro a ha x hx
  rw [hEb] at hx
  obtain ⟨D, hD, rfl⟩ := hx
  rw [hT] at hD
  obtain ⟨D', hD', rfl⟩ := Subgroup.mem_map.mp hD
  obtain ⟨t, ht⟩ := hφdiag (USixTwo.qAutHom L a) ⟨a, ha, rfl⟩
  have heD' : ((e D' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
      GL (Fin 6) K) = (D' : GL (Fin 6) K) := he D'
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

omit [Finite K] in
private theorem exists_lift_eq_Bs {Bs L : Subgroup G}
    (hcard : Nat.card Bs = 3 ^ 5)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {A : Subgroup (MulAut ↥L)} (hAab : IsElemAbelian 3 A)
    (hA : A = (⊤ : Subgroup ↥Bs).map
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hNL)))
    {Eb : Subgroup (USixTwo.Qt L)}
    (hEbelem : IsElemAbelian 3 Eb)
    (hEbH : Eb ≤ (⊤ : Subgroup L).map (USixTwo.qmk L))
    (hEbfix : ∀ a ∈ A, ∀ x ∈ Eb, USixTwo.qAutHom L a x = x)
    (hEbcard : Nat.card Eb = 3 ^ 5) :
    ∃ E : Subgroup ↥L,
      IsElemAbelian 3 E ∧ E.map (USixTwo.qmk L) = Eb ∧
      (∀ a ∈ A, ∀ e ∈ E, a e = e) ∧ Nat.card E = 3 ^ 5 ∧
      E.map L.subtype = Bs := by
  have hA3 : IsPGroup 3 A :=
    CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian hAab
  obtain ⟨E, -, hEelem, hEmap, hEfix, hEcard⟩ :=
    USixTwo.exists_elemAbelian_lift_fixed (L' := L) (A := A) hA3
      (H := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) hEbelem hEbH hEbfix
  have hEcardE : Nat.card E = 3 ^ 5 := by rw [hEcard, hEbcard]
  let conjHom : ↥Bs →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hNL)
  have hEcent : E.map L.subtype ≤ Subgroup.centralizer (Bs : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbA : conjHom ⟨b, hb⟩ ∈ A := by
      rw [hA]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
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
  have hEeq : E.map L.subtype = Bs :=
    Subgroup.eq_of_le_of_card_ge hEsub (by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hEcardE, hcard])
  exact ⟨E, hEelem, hEmap, hEfix, hEcardE, hEeq⟩

private theorem qmk_inj_on_and_lift {L : Subgroup G}
    {E : Subgroup ↥L} (hEelem : IsElemAbelian 3 E)
    {Eb : Subgroup (USixTwo.Qt L)} (hEmap : E.map (USixTwo.qmk L) = Eb) :
    (∀ {e₁ e₂ : L}, e₁ ∈ E → e₂ ∈ E → USixTwo.qmk L e₁ = USixTwo.qmk L e₂ → e₁ = e₂) ∧
      (∀ z : L, USixTwo.qmk L z ∈ Eb → z ^ 3 = 1 → z ∈ E) := by
  have hZ3one : ∀ w ∈ USixTwo.zTwo L, w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have hord3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    obtain ⟨k, hk⟩ := USixTwo.isPGroup_zTwo (⟨w, hw⟩ : ↥(USixTwo.zTwo L))
    have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord2 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
    have hone : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hcop hord3 hord2
    exact orderOf_eq_one_iff.mp hone
  have hE_inj : ∀ {e₁ e₂ : L}, e₁ ∈ E → e₂ ∈ E →
      USixTwo.qmk L e₁ = USixTwo.qmk L e₂ → e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ hq
    have hmemE : e₁⁻¹ * e₂ ∈ E := E.mul_mem (E.inv_mem he₁) he₂
    have hmemZ : e₁⁻¹ * e₂ ∈ USixTwo.zTwo L := by
      rw [← USixTwo.qmk_eq_one_iff, map_mul, map_inv, hq, inv_mul_cancel]
    have h3 : (e₁⁻¹ * e₂) ^ 3 = 1 := hEelem.2 _ hmemE
    exact inv_mul_eq_one.mp (hZ3one _ hmemZ h3)
  have hE_lift3 : ∀ z : L, USixTwo.qmk L z ∈ Eb → z ^ 3 = 1 → z ∈ E := by
    intro z hzEb hz3
    have hzMap : USixTwo.qmk L z ∈ E.map (USixTwo.qmk L) := by rwa [hEmap]
    obtain ⟨e, heE, heq⟩ := Subgroup.mem_map.mp hzMap
    have hwZ : e⁻¹ * z ∈ USixTwo.zTwo L := by
      rw [← USixTwo.qmk_eq_one_iff, map_mul, map_inv, heq, inv_mul_cancel]
    have hz_eq : z = e * (e⁻¹ * z) := by group
    have hw3 : (e⁻¹ * z) ^ 3 = 1 := by
      have hmain : z ^ 3 = (e * (e⁻¹ * z)) ^ 3 :=
        congrArg (fun t : L => t ^ 3) hz_eq
      rw [hz3] at hmain
      have h' : (e * (e⁻¹ * z)) ^ 3 = 1 := hmain.symm
      rw [Commute.mul_pow (USixTwo.zTwo_comm hwZ e), hEelem.2 e heE, one_mul] at h'
      exact h'
    have hw1 : e⁻¹ * z = 1 := hZ3one _ hwZ hw3
    rw [hz_eq, hw1, mul_one]
    exact heE
  exact ⟨hE_inj, hE_lift3⟩

private theorem exists_permutation_matrices (hK : Nat.card K = 4)
    {e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (he : ∀ x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      ((e x : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K) = (x : GL (Fin 6) K))
    {T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hT : T = (USixTwo.torSU K).map e.toMonoidHom) :
    ∃ g p : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6),
      T = Subgroup.closure (Set.range g) ∧
      (∀ i, p i ∈ Subgroup.normalizer (T : Set _)) ∧
      (∀ i, p i * g i * (p i)⁻¹ = (g i)⁻¹) := by
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  let g : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    fun i => e (USixTwo.genT hK hω i)
  have hgenT : T = Subgroup.closure (Set.range g) := by
    rw [hT, ← USixTwo.closure_genT_eq_torSU hK hω, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  let p : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    fun i => permSU (USixTwo.fieldDataFour hK) (Equiv.swap 0 (Fin.succ i))
  have hpnorm : ∀ i, p i ∈ Subgroup.normalizer (T : Set _) := by
    intro i
    have hPe : e (USixTwo.permGLSU hK (Equiv.swap 0 (Fin.succ i))⁻¹) = p i := by
      apply Subtype.ext
      rw [he, USixTwo.coe_permGLSU, USixTwo.coe_permSU_eq_permutationGL]
    have hmem : p i ∈ (Subgroup.normalizer (USixTwo.torSU K : Set _)).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨USixTwo.permGLSU hK (Equiv.swap 0 (Fin.succ i))⁻¹,
        USixTwo.permGLSU_mem_normalizer_torSU hK _, hPe⟩
    rw [Subgroup.map_equiv_normalizer_eq] at hmem
    rwa [hT]
  have hconj : ∀ i, p i * g i * (p i)⁻¹ = (g i)⁻¹ := by
    intro i
    have hgdiag : g i = e (USixTwo.diagTwoSU hω (Fin.succ_ne_zero i).symm) := by
      apply congrArg e
      exact USixTwo.coe_diagTwoTor hω _
    rw [hgdiag]
    exact CFSG.StandardType.USixTwo.permSU_conj_image_diagTwoSU hK hω
      (Fin.succ_ne_zero i).symm e he
  exact ⟨g, p, hgenT, hpnorm, hconj⟩

omit [Finite K] in
private theorem exists_lifts {L : Subgroup G}
    {E : Subgroup L} {Eb : Subgroup (USixTwo.Qt L)}
    (hEelem : IsElemAbelian 3 E)
    (hEmap : E.map (USixTwo.qmk L) = Eb)
    (hE_lift3 : ∀ z : L, USixTwo.qmk L z ∈ Eb → z ^ 3 = 1 → z ∈ E)
    {T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    (hEb : Eb = T.map φ)
    {g p : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hgEb : ∀ i, φ (g i) ∈ Eb)
    (hpnorm : ∀ i, p i ∈ Subgroup.normalizer (T : Set _)) :
    ∃ b l : Fin 5 → L,
      (∀ i, b i ∈ E) ∧
      (∀ i, USixTwo.qmk L (b i) = φ (g i)) ∧
      (∀ i, USixTwo.qmk L (l i) = φ (p i)) ∧
      (∀ i y, y ∈ E → l i * y * (l i)⁻¹ ∈ E) := by
  choose b hbE hbq using fun i =>
    Subgroup.mem_map.mp (show φ (g i) ∈ E.map (USixTwo.qmk L) by
      rw [hEmap]
      exact hgEb i)
  choose l hlq using fun i => USixTwo.qmk_surjective (φ (p i))
  have hlE : ∀ i y, y ∈ E → l i * y * (l i)⁻¹ ∈ E := by
    intro i y hy
    have hyEb : USixTwo.qmk L y ∈ Eb := by
      rw [← hEmap]
      exact Subgroup.mem_map_of_mem _ hy
    have hz3 : (l i * y * (l i)⁻¹) ^ 3 = 1 := by
      rw [show l i * y * (l i)⁻¹ = (MulAut.conj (l i)) y from rfl]
      rw [← map_pow, hEelem.2 y hy, map_one]
    have hzq : USixTwo.qmk L (l i * y * (l i)⁻¹) ∈ Eb := by
      have hpn : φ (p i) ∈ Subgroup.normalizer (Eb : Set (USixTwo.Qt L)) := by
        rw [hEb]
        exact Subgroup.le_normalizer_map (f := φ) (H := T)
          (Subgroup.mem_map_of_mem φ (hpnorm i))
      have hq : USixTwo.qmk L (l i * y * (l i)⁻¹) =
          φ (p i) * USixTwo.qmk L y * (φ (p i))⁻¹ := by
        rw [map_mul, map_mul, map_inv, hlq i]
      rw [hq]
      exact (Subgroup.mem_normalizer_iff.mp hpn (USixTwo.qmk L y)).mp hyEb
    exact hE_lift3 _ hzq hz3
  exact ⟨b, l, hbE, hbq, hlq, hlE⟩

omit [Finite K] in
private theorem normalizer_and_inverse {Bs L : Subgroup G}
    {E : Subgroup L}
    (hEeq : E.map L.subtype = Bs)
    (hE_inj : ∀ {e₁ e₂ : L}, e₁ ∈ E → e₂ ∈ E →
      USixTwo.qmk L e₁ = USixTwo.qmk L e₂ → e₁ = e₂)
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    {b l : Fin 5 → L}
    {g p : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hbE : ∀ i, b i ∈ E)
    (hbq : ∀ i, USixTwo.qmk L (b i) = φ (g i))
    (hconj : ∀ i, p i * g i * (p i)⁻¹ = (g i)⁻¹)
    (hlq : ∀ i, USixTwo.qmk L (l i) = φ (p i))
    (hlE : ∀ i y, y ∈ E → l i * y * (l i)⁻¹ ∈ E) :
    (∀ i, ((l i : L) : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ i, ((l i : L) : G) * ((b i : L) : G) * (((l i : L) : G))⁻¹ =
        (((b i : L) : G))⁻¹) := by
  have hlN : ∀ i, ((l i : L) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨b, hb, rfl⟩
      rw [← hEeq] at hb
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hb
      have hmemE : l i * e * (l i)⁻¹ ∈ E := hlE i e he
      have hmemBs : (((l i * e * (l i)⁻¹ : L) : G) ∈ Bs) := by
        rw [← hEeq]
        exact Subgroup.mem_map_of_mem L.subtype hmemE
      simpa [MulAut.conj_apply] using hmemBs
    · rw [Subgroup.card_map_of_injective (MulAut.conj ((l i : L) : G)).injective]
  have hinv : ∀ i, ((l i : L) : G) * ((b i : L) : G) * (((l i : L) : G))⁻¹ =
      (((b i : L) : G))⁻¹ := by
    intro i
    have hleftE : l i * b i * (l i)⁻¹ ∈ E := hlE i _ (hbE i)
    have hrightE : (b i)⁻¹ ∈ E := E.inv_mem (hbE i)
    have hq : USixTwo.qmk L (l i * b i * (l i)⁻¹) = USixTwo.qmk L ((b i)⁻¹) := by
      have h := congrArg φ (hconj i)
      rw [map_mul, map_mul, map_inv] at h
      calc USixTwo.qmk L (l i * b i * (l i)⁻¹)
          = φ (p i) * USixTwo.qmk L (b i) * (φ (p i))⁻¹ := by
            rw [map_mul, map_mul, map_inv, hlq i]
        _ = φ (p i) * φ (g i) * (φ (p i))⁻¹ := by rw [hbq i]
        _ = (φ (g i))⁻¹ := by
          simpa only [map_mul, map_inv] using congrArg φ (hconj i)
        _ = (USixTwo.qmk L (b i))⁻¹ := by rw [hbq i]
    have heqL : l i * b i * (l i)⁻¹ = (b i)⁻¹ := hE_inj hleftE hrightE hq
    simpa using congrArg (fun x : L => (x : G)) heqL
  exact ⟨hlN, hinv⟩

omit [Finite K] in
private theorem closure_range_b {L : Subgroup G}
    {E : Subgroup L} {Eb : Subgroup (USixTwo.Qt L)}
    (hEmap : E.map (USixTwo.qmk L) = Eb)
    (hE_inj : ∀ {e₁ e₂ : L}, e₁ ∈ E → e₂ ∈ E →
      USixTwo.qmk L e₁ = USixTwo.qmk L e₂ → e₁ = e₂)
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* USixTwo.Qt L}
    {g : Fin 5 → ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    {b : Fin 5 → L}
    (hbE : ∀ i, b i ∈ E)
    (hbq : ∀ i, USixTwo.qmk L (b i) = φ (g i))
    {T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)}
    (hEb : Eb = T.map φ)
    (hgenT : T = Subgroup.closure (Set.range g)) :
    Subgroup.closure (Set.range b) = E := by
  have hEbgen : Eb = Subgroup.closure (Set.range (fun i => φ (g i))) := by
    rw [hEb, hgenT, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hE₀map : (Subgroup.closure (Set.range b)).map (USixTwo.qmk L) =
      Subgroup.closure (Set.range (fun i => φ (g i))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    change Subgroup.closure (Set.range (fun i => USixTwo.qmk L (b i))) =
      Subgroup.closure (Set.range (fun i => φ (g i)))
    rw [show (fun i => USixTwo.qmk L (b i)) = (fun i => φ (g i)) by
      funext i
      exact hbq i]
  have hE_le : E ≤ Subgroup.closure (Set.range b) := by
    intro e he
    have hq : USixTwo.qmk L e ∈ (Subgroup.closure (Set.range b)).map (USixTwo.qmk L) := by
      rw [hE₀map, ← hEbgen, ← hEmap]
      exact Subgroup.mem_map_of_mem _ he
    obtain ⟨e₀, he₀, hq₀⟩ := Subgroup.mem_map.mp hq
    have he₀E : e₀ ∈ E :=
      (Subgroup.closure_le (K := E)).mpr (by rintro _ ⟨i, rfl⟩; exact hbE i) he₀
    have heq : e₀ = e := hE_inj he₀E he hq₀
    simpa [heq] using he₀
  exact le_antisymm
    ((Subgroup.closure_le (K := E)).mpr (by rintro _ ⟨i, rfl⟩; exact hbE i)) hE_le

omit [Finite G] in
private theorem le_closure_inv_of_lifts {Bs L : Subgroup G}
    {E : Subgroup L} {b l : Fin 5 → L}
    (hEeq : E.map L.subtype = Bs)
    (hE_gen : Subgroup.closure (Set.range b) = E)
    (hbE : ∀ i, b i ∈ E)
    (hlN : ∀ i, ((l i : L) : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hinv : ∀ i, ((l i : L) : G) * ((b i : L) : G) * (((l i : L) : G))⁻¹ =
      (((b i : L) : G))⁻¹) :
    Bs ≤ Subgroup.closure
      {b | b ∈ Bs ∧ ∃ l ∈ L, l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹} := by
  have hBsgen : Bs = Subgroup.closure (Set.range (fun i => ((b i : L) : G))) := by
    rw [← hEeq, ← hE_gen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  conv_lhs => rw [hBsgen]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨?_, ((l i : L) : G), (l i).2, hlN i, hinv i⟩
  rw [← hEeq]
  exact Subgroup.mem_map_of_mem L.subtype (hbE i)

theorem le_closure_inv_aux
    (hK : Nat.card K = 4)
    {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hZ : ¬ IsPGroup 2 (Subgroup.center L)) :
    Bs ≤ Subgroup.closure
      {b | b ∈ Bs ∧ ∃ l ∈ L, l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹} := by
  classical
  let A : Subgroup (MulAut ↥L) :=
    (⊤ : Subgroup ↥Bs).map
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hNL))
  obtain ⟨hAab, hcardA, hAI⟩ := conjAction_props hBs hcard hx hx1 hBL hNL θ hI
  obtain ⟨ψb, φ, hψbs, hφM, hφdiag⟩ :=
    exists_diagModel_of_action (L := L) (A := A) hK hperf θ hAab hcardA hAI
  have hkerne : ψb.ker ≠ ⊥ := ker_ne_bot_of_not_isPGroup_center hK hψbs hZ
  obtain ⟨-, hφinj⟩ := card_ker_eq_three_and_injective hK hψbs hφM hkerne
  let e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSUGroup_eq_statedSU 6 (2 ^ 1))
  let T : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    (USixTwo.torSU K).map e.toMonoidHom
  let Eb : Subgroup (USixTwo.Qt L) := T.map φ
  have he : ∀ x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      ((e x : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
        GL (Fin 6) K) = (x : GL (Fin 6) K) := fun x => rfl
  obtain ⟨-, -, hEbelem, hEbH, hEbcard⟩ :=
    torus_image_props hK (e := e) (T := T) rfl (φ := φ) hφinj (Eb := Eb) rfl
  have hEbfix : ∀ a ∈ A, ∀ x ∈ Eb, USixTwo.qAutHom L a x = x :=
    fixed_of_diagonal (e := e) (T := T) rfl he (φ := φ) (Eb := Eb) rfl (A := A) hφdiag
  obtain ⟨E, hEelem, hEmap, -, -, hEeq⟩ :=
    exists_lift_eq_Bs hcard hstar hNL (A := A) hAab rfl (Eb := Eb)
      hEbelem hEbH hEbfix hEbcard
  obtain ⟨hE_inj, hE_lift3⟩ := qmk_inj_on_and_lift hEelem hEmap
  obtain ⟨g, p, hgenT, hpnorm, hconj⟩ :=
    exists_permutation_matrices hK (e := e) he (T := T) rfl
  have hgEb : ∀ i, φ (g i) ∈ Eb := fun i =>
    Subgroup.mem_map_of_mem φ (by
      rw [hgenT]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  obtain ⟨b, l, hbE, hbq, hlq, hlE⟩ :=
    exists_lifts hEelem hEmap hE_lift3 (T := T) (φ := φ) (Eb := Eb) rfl
      (g := g) (p := p) hgEb hpnorm
  obtain ⟨hlN, hinv⟩ :=
    normalizer_and_inverse hEeq hE_inj (b := b) (l := l) (g := g) (p := p)
      hbE hbq hconj hlq hlE
  have hE_gen : Subgroup.closure (Set.range b) = E :=
    closure_range_b hEmap hE_inj hbE hbq (T := T) rfl hgenT
  exact le_closure_inv_of_lifts hEeq hE_gen hbE hlN hinv

end CFSG.StandardType.E6QTwo
