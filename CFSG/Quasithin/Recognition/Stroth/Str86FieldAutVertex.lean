module

public import CFSG.Quasithin.Recognition.Stroth.BenderFieldAutCore
public import CFSG.Quasithin.Recognition.Stroth.Str86Props
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev fieldAutC (P L Q' : Subgroup G) : Subgroup G :=
  centralizerMod Q' P L

abbrev fieldAutK (P P' L Q' : Subgroup G) : Subgroup G :=
  fieldAutC P L Q' ⊓ P'

abbrev fieldAutN (P P' L Q' : Subgroup G) : Subgroup G :=
  centralizerMod Q' (fieldAutC P L Q') (fieldAutK P P' L Q')

theorem mem_fieldAutC {P L Q' : Subgroup G} {x : G} :
    x ∈ fieldAutC P L Q' ↔ x ∈ P ∧ x ∈ Subgroup.normalizer (Q' : Set G) ∧
      ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Q' :=
  Iff.rfl

theorem le_normalizer_fieldAutC {P L Q' : Subgroup G}
    (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G))
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer (fieldAutC P L Q' : Set G) :=
  CFSG.Quasithin.le_normalizer_centralizerMod hPQ' Subgroup.le_normalizer hPL

theorem le_normalizer_fieldAutK {P P' L Q' : Subgroup G}
    (hPP' : P ≤ Subgroup.normalizer (P' : Set G))
    (hPC : P ≤ Subgroup.normalizer (fieldAutC P L Q' : Set G)) :
    P ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G) :=
  fun x hx => CFSG.ABGLocalTools.mem_normalizer_inf (hPC hx) (hPP' hx)

theorem le_normalizer_fieldAutN {P P' L Q' : Subgroup G}
    (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G))
    (hPC : P ≤ Subgroup.normalizer (fieldAutC P L Q' : Set G))
    (hPK : P ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G)) :
    P ≤ Subgroup.normalizer (fieldAutN P P' L Q' : Set G) :=
  CFSG.Quasithin.le_normalizer_centralizerMod hPQ' hPC hPK

theorem pCoreOf_le_fieldAutC {P P' L Q' : Subgroup G} (hQ' : Q' = pCoreOf 2 P')
    (hP'P : P' ≤ P) (hLP' : L ≤ P')
    (hP'Q' : P' ≤ Subgroup.normalizer (Q' : Set G)) :
    Q' ≤ fieldAutC P L Q' := by
  intro q hq
  rw [mem_fieldAutC]
  refine ⟨hP'P (hQ'.le.trans (pCoreOf_le 2 P') hq), Subgroup.le_normalizer hq, ?_⟩
  intro l hl
  have hlP' : l ∈ P' := hLP' hl
  have hconj : l⁻¹ * q * l ∈ Q' := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hP'Q' (P'.inv_mem hlP')) q).mp hq
  have hmul : (l⁻¹ * q * l) * q⁻¹ ∈ Q' := Q'.mul_mem hconj (Q'.inv_mem hq)
  have hconj2 : l * ((l⁻¹ * q * l) * q⁻¹) * l⁻¹ ∈ Q' :=
    (Subgroup.mem_normalizer_iff.mp (hP'Q' hlP') _).mp hmul
  have e : q * l * q⁻¹ * l⁻¹ = l * ((l⁻¹ * q * l) * q⁻¹) * l⁻¹ := by group
  rwa [e]

theorem pCoreOf_le_fieldAutK {P P' L Q' : Subgroup G} (hQ' : Q' = pCoreOf 2 P')
    (hP'P : P' ≤ P) (hLP' : L ≤ P')
    (hP'Q' : P' ≤ Subgroup.normalizer (Q' : Set G)) :
    Q' ≤ fieldAutK P P' L Q' :=
  le_inf (pCoreOf_le_fieldAutC hQ' hP'P hLP' hP'Q')
    (hQ'.le.trans (pCoreOf_le 2 P'))

theorem pCoreOf_le_fieldAutN {P P' L Q' : Subgroup G} (hQ' : Q' = pCoreOf 2 P')
    (hP'P : P' ≤ P) (hLP' : L ≤ P')
    (hP'Q' : P' ≤ Subgroup.normalizer (Q' : Set G)) :
    Q' ≤ fieldAutN P P' L Q' := by
  intro q hq
  rw [mem_centralizerMod]
  refine ⟨pCoreOf_le_fieldAutC hQ' hP'P hLP' hP'Q' hq, Subgroup.le_normalizer hq, ?_⟩
  intro x hx
  have hxP' : x ∈ P' := (inf_le_right : fieldAutC P L Q' ⊓ P' ≤ P') hx
  have hconj : x⁻¹ * q * x ∈ Q' := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hP'Q' (P'.inv_mem hxP')) q).mp hq
  have hmul : (x⁻¹ * q * x) * q⁻¹ ∈ Q' := Q'.mul_mem hconj (Q'.inv_mem hq)
  have hconj2 : x * ((x⁻¹ * q * x) * q⁻¹) * x⁻¹ ∈ Q' :=
    (Subgroup.mem_normalizer_iff.mp (hP'Q' hxP') _).mp hmul
  have e : q * x * q⁻¹ * x⁻¹ = x * ((x⁻¹ * q * x) * q⁻¹) * x⁻¹ := by group
  rwa [e]

theorem inf_fieldAutK_eq_pCoreOf {P P' L S' Q' : Subgroup G}
    (hQ'S' : Q' ≤ S') (hQ'K : Q' ≤ fieldAutK P P' L Q')
    (hE2 : ∀ s ∈ S', (∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ Q') → s ∈ Q') :
    S' ⊓ fieldAutK P P' L Q' = Q' := by
  refine le_antisymm ?_ (le_inf hQ'S' hQ'K)
  intro s hs
  obtain ⟨hsS', hsK⟩ := Subgroup.mem_inf.mp hs
  exact hE2 s hsS' (mem_fieldAutC.mp hsK.1).2.2

theorem odd_relIndex_fieldAutK {P P' L S' Q' : Subgroup G}
    (hSK : S' ⊓ fieldAutK P P' L Q' = Q')
    (hQ'K : Q' ≤ fieldAutK P P' L Q')
    (hKP' : fieldAutK P P' L Q' ≤ P')
    (hS'P' : S' ≤ P')
    (hS'K : S' ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G))
    (hS'odd : Odd (S'.relIndex P')) :
    Odd (Q'.relIndex (fieldAutK P P' L Q')) := by
  have hB6 := CFSG.Quasithin.B6.relIndex_inf_eq_relIndex_sup hS'K
  rw [hSK] at hB6
  rw [hB6]
  have hmul := Subgroup.relIndex_mul_relIndex (H := S') (K := S' ⊔ fieldAutK P P' L Q')
    (L := P') le_sup_left (sup_le hS'P' hKP')
  exact Odd.of_dvd_nat hS'odd ⟨(S' ⊔ fieldAutK P P' L Q').relIndex P', hmul.symm⟩

theorem commutator_mem_of_fieldAut {P P' L T Q' Z' : Subgroup G}
    (hZ'Q' : Z' ≤ Q') (hQ'2 : IsPGroup 2 Q')
    (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G))
    (hPZ' : P ≤ Subgroup.normalizer (Z' : Set G))
    (hKP : fieldAutK P P' L Q' ≤ P) (hQ'K : Q' ≤ fieldAutK P P' L Q')
    (hQKn : fieldAutK P P' L Q' ≤ Subgroup.normalizer (Q' : Set G))
    (hKodd : Odd (Q'.relIndex (fieldAutK P P' L Q')))
    (hC7 : fieldAutK P P' L Q' ⊓ Subgroup.centralizer (Q' : Set G) ≤ Q')
    (hKn : P ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G))
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hNF : Str86NF L Q' Z')
    (hT2 : IsPGroup 2 T) (hTP : T ≤ P)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ Q') :
    ∀ t ∈ T, ∀ x ∈ fieldAutK P P' L Q', t * x * t⁻¹ * x⁻¹ ∈ Q' := by
  intro t ht x hx
  have htP : t ∈ P := hTP ht
  obtain ⟨n, hn⟩ := hT2.exists_orderOf_eq_pow ⟨t, ht⟩
  have hNFt := hNF t ⟨n, by simpa using hn⟩ (hPL htP) (hPQ' htP) (hTL t ht)
  exact commutator_mem_of_series hZ'Q' hQ'2 hPQ' hPZ' hKP hQ'K hQKn hKodd hC7 hKn
    htP hx (fun q hq => hNFt.1 q hq) (fun z hz => by
      have h := hNFt.2 z hz
      calc t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [h]
        _ = z := by group)

theorem ker_map_le_center_of_commutator_mem {N K Q' : Subgroup G}
    (hQN : (Q'.subgroupOf N).Normal) (hM : ((N ⊓ K).subgroupOf N).Normal)
    (hcomm : ∀ y ∈ N, ∀ x ∈ N ⊓ K, y * x * y⁻¹ * x⁻¹ ∈ Q')
    (hle : Q'.subgroupOf N ≤ (N ⊓ K).subgroupOf N) :
    (QuotientGroup.map (Q'.subgroupOf N) ((N ⊓ K).subgroupOf N)
      (MonoidHom.id ↥N) (by simpa [Subgroup.comap_id] using hle)).ker ≤
      Subgroup.center (↥N ⧸ Q'.subgroupOf N) := by
  classical
  haveI := hQN
  haveI := hM
  rw [QuotientGroup.ker_map]
  rintro z ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  have hxM : (x : G) ∈ N ⊓ K :=
    Subgroup.mem_subgroupOf.mp (by simpa [Subgroup.comap_id] using hx)
  change QuotientGroup.mk' (Q'.subgroupOf N) (y0 * x) =
    QuotientGroup.mk' (Q'.subgroupOf N) (x * y0)
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  change (y0 : G) * (x : G) / ((x : G) * (y0 : G)) ∈ Q'
  have hcomm' := hcomm (y0 : G) y0.2 (x : G) hxM
  have e : (y0 : G) * (x : G) / ((x : G) * (y0 : G)) =
      (y0 : G) * (x : G) * (y0 : G)⁻¹ * (x : G)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev]
    group
  rw [e]
  exact hcomm'

theorem le_pCoreOf_of_fieldAut {P P' L S S' T Q' Z' : Subgroup G}
    (hP : P = P' ⊔ S) (hSP' : S ≤ Subgroup.normalizer (P' : Set G)) (hS2 : IsPGroup 2 S)
    (hS'S : S' ≤ S) (hS'P' : S' ≤ P') (hS'odd : Odd (S'.relIndex P'))
    (hQ' : Q' = pCoreOf 2 P') (hZ'Q' : Z' ≤ Q')
    (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G))
    (hPZ' : P ≤ Subgroup.normalizer (Z' : Set G))
    (hLP' : L ≤ P') (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hTS : T ≤ S) (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ Q')
    (hE2 : ∀ s ∈ S', (∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ Q') → s ∈ Q')
    (hC7 : P' ⊓ Subgroup.centralizer (Q' : Set G) ≤ Q')
    (hNF : Str86NF L Q' Z') :
    T ≤ pCoreOf 2 P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP'P : P' ≤ P := hP.symm ▸ le_sup_left
  have hPnormP' : P ≤ Subgroup.normalizer (P' : Set G) :=
    hP.symm ▸ sup_le Subgroup.le_normalizer hSP'
  have hSleP : S ≤ P := hP.symm ▸ le_sup_right
  haveI hP'normal : (P'.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP'P).mpr hPnormP'
  have hquot2 : IsPGroup 2 (↥P ⧸ P'.subgroupOf P) :=
    isPGroup_quotient_sup_of_isPGroup hP hSP' hS2
  have hPC : P ≤ Subgroup.normalizer (fieldAutC P L Q' : Set G) :=
    le_normalizer_fieldAutC hPQ' hPL
  have hPK : P ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G) :=
    le_normalizer_fieldAutK hPnormP' hPC
  have hPN : P ≤ Subgroup.normalizer (fieldAutN P P' L Q' : Set G) :=
    le_normalizer_fieldAutN hPQ' hPC hPK
  have hP'Q' : P' ≤ Subgroup.normalizer (Q' : Set G) := by
    rw [hQ']; exact le_normalizer_pCoreOf 2 P'
  have hQ'2 : IsPGroup 2 Q' := by rw [hQ']; exact pCoreOf_isPGroup 2 P'
  have hQ'P : Q' ≤ P := (hQ'.le.trans (pCoreOf_le 2 P')).trans hP'P
  have hNleP : fieldAutN P P' L Q' ≤ P :=
    (centralizerMod_le_left _ _ _).trans (centralizerMod_le_left _ _ _)
  have hQ'K : Q' ≤ fieldAutK P P' L Q' :=
    pCoreOf_le_fieldAutK hQ' hP'P hLP' hP'Q'
  have hQ'N : Q' ≤ fieldAutN P P' L Q' :=
    pCoreOf_le_fieldAutN hQ' hP'P hLP' hP'Q'
  have hSyl' : IsSylowTwoOf S' P' := by
    refine ⟨hS'P', hS2.to_le hS'S, ?_⟩
    simpa only [Subgroup.relIndex] using hS'odd.not_two_dvd_nat
  have hQ'S' : Q' ≤ S' := by
    rw [hQ']; exact hSyl'.pCoreOf_le
  have hSK : S' ⊓ fieldAutK P P' L Q' = Q' :=
    inf_fieldAutK_eq_pCoreOf hQ'S' hQ'K hE2
  have hS'K : S' ≤ Subgroup.normalizer (fieldAutK P P' L Q' : Set G) :=
    (hS'S.trans hSleP).trans hPK
  have hKodd : Odd (Q'.relIndex (fieldAutK P P' L Q')) :=
    odd_relIndex_fieldAutK hSK hQ'K
      (inf_le_right : fieldAutK P P' L Q' ≤ P') hS'P' hS'K hS'odd
  have hC7K : fieldAutK P P' L Q' ⊓ Subgroup.centralizer (Q' : Set G) ≤ Q' := by
    intro x hx
    exact hC7 ⟨(inf_le_right : fieldAutK P P' L Q' ≤ P') hx.1, hx.2⟩
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hKP : fieldAutK P P' L Q' ≤ P :=
    (inf_le_right : fieldAutK P P' L Q' ≤ P').trans hP'P
  have hcommK := commutator_mem_of_fieldAut hZ'Q' hQ'2 hPQ' hPZ' hKP hQ'K
    (fun _ hx => hP'Q' hx.2) hKodd hC7K hPK hPL hNF hT2 (hTS.trans hSleP) hTL
  have hTN : T ≤ fieldAutN P P' L Q' := by
    intro t ht
    rw [mem_centralizerMod]
    refine ⟨mem_fieldAutC.mpr ⟨hTS.trans hSleP ht, hPQ' (hTS.trans hSleP ht), hTL t ht⟩,
      hPQ' (hTS.trans hSleP ht), fun x hx => hcommK t ht x hx⟩
  have hNQ' : fieldAutN P P' L Q' ≤ Subgroup.normalizer (Q' : Set G) :=
    centralizerMod_le_normalizer _ _ _
  haveI hQNnormal : (Q'.subgroupOf (fieldAutN P P' L Q')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'N).mpr hNQ'
  have hNn : fieldAutN P P' L Q' ≤
      Subgroup.normalizer ((fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q') : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hPN (hNleP hx), hPK (hNleP hx)⟩
  haveI hNKnormal :
      ((fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q').subgroupOf
        (fieldAutN P P' L Q')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hNn
  have hNK : fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q' =
      fieldAutN P P' L Q' ⊓ P' := by
    rw [fieldAutK, ← inf_assoc, inf_eq_left.mpr (centralizerMod_le_left _ _ _)]
  have hquotN : IsPGroup 2
      (↥(fieldAutN P P' L Q') ⧸
        (fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q').subgroupOf
          (fieldAutN P P' L Q')) :=
    isPGroup_quotient_inf_of_isPGroup_quotient hNleP inf_le_right hNK hquot2
  have hle : Q'.subgroupOf (fieldAutN P P' L Q') ≤
      (fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q').subgroupOf
        (fieldAutN P P' L Q') := by
    intro q hq
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hQ'N (Subgroup.mem_subgroupOf.mp hq), hQ'K (Subgroup.mem_subgroupOf.mp hq)⟩
  have hker := ker_map_le_center_of_commutator_mem hQNnormal hNKnormal
    (fun y hy x hx => (mem_centralizerMod.mp hy).2.2 x hx.2) hle
  haveI : Group.IsNilpotent
      (↥(fieldAutN P P' L Q') ⧸
        (fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q').subgroupOf
          (fieldAutN P P' L Q')) := hquotN.isNilpotent
  have hnil : Group.IsNilpotent
      (↥(fieldAutN P P' L Q') ⧸ (Q'.subgroupOf (fieldAutN P P' L Q'))) :=
    Subgroup.isNilpotent_of_ker_le_center
      (QuotientGroup.map (Q'.subgroupOf (fieldAutN P P' L Q'))
        ((fieldAutN P P' L Q' ⊓ fieldAutK P P' L Q').subgroupOf
          (fieldAutN P P' L Q')) (MonoidHom.id ↥(fieldAutN P P' L Q'))
        (by simpa [Subgroup.comap_id] using hle)) hker
  exact le_pCoreOf_of_nilpotent_quotient hNleP hPN hQ'N hQ'2 hPQ' hTN hT2 hnil

end CFSG.Quasithin.Stroth
