module

public import CFSG.Walter.AStar.Subnormal
public import CFSG.Quasithin.Background.RonanE42Defs

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RonanE42

variable {G : Type} [Group G] [Finite G]

theorem le_sup_normalizer_inf {T P Y : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTP : T ≤ P)
    (hYP : Y ≤ P) (hYn : ∀ h ∈ P, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) :
    P ≤ Y ⊔ (P ⊓ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : T.relIndex P ∣ T.relIndex ⊤ :=
    ⟨_, (Subgroup.relIndex_mul_relIndex T P ⊤ hTP le_top).symm⟩
  have hTP2 : IsSylowIn 2 T P := ⟨hTP, hT.isPGroup, fun h => hT.not_dvd_relIndex (h.trans hdiv)⟩
  haveI : Finite (Sylow 2 P) :=
    Finite.of_injective (fun Q : Sylow 2 P => (Q : Set P)) SetLike.coe_injective
  obtain ⟨PH, hPH⟩ : ∃ Q : Sylow 2 P, (Q : Subgroup P) = T.subgroupOf P :=
    ⟨hTP2.toSylow, IsSylowIn.coe_toSylow hTP2⟩
  have hYn' : (Y.subgroupOf P).Normal :=
    ⟨fun y hy h => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simpa using hYn h h.2 y hy⟩
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PH hYn'.isSubnormal
  have hN := Sylow.normalizer_sup_eq_top P'
  rw [hP'] at hN
  intro x hx
  have hmem : (⟨x, hx⟩ : P) ∈ Subgroup.normalizer
      (((PH : Subgroup P) ⊓ Y.subgroupOf P : Subgroup P) : Set P) ⊔ Y.subgroupOf P := by
    rw [hN]; exact Subgroup.mem_top _
  obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hxe : x = (h : G) * (m : G) := (congrArg Subtype.val hhm).symm
  have hb : (h : G) ∈ P ⊓ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G) := by
    refine ⟨h.2, ?_⟩
    show (h : G) ∈ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyP : y ∈ P := hTP hy.1
      have h1 : (⟨y, hyP⟩ : P) ∈ (PH : Subgroup P) ⊓ Y.subgroupOf P :=
        ⟨by rw [hPH]; exact hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) _).1 h1
      rw [hPH] at h2
      exact ⟨h2.1, h2.2⟩
    · intro hy
      have hyP : y ∈ P := by
        have := P.mul_mem (P.mul_mem (P.inv_mem h.2) (hTP hy.1)) h.2
        simpa [mul_assoc] using this
      have hc : h * (⟨y, hyP⟩ : P) * h⁻¹ ∈ (PH : Subgroup P) ⊓ Y.subgroupOf P := by
        rw [hPH]; exact ⟨hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) ⟨y, hyP⟩).2 hc
      rw [hPH] at h2
      exact ⟨h2.1, h2.2⟩
  have hm' : (m : G) ∈ Y := hm
  rw [hxe, sup_comm]
  exact Subgroup.mul_mem_sup hb hm'

theorem le_pCoreOf_of_normal {P S : Subgroup G} (hSP : S ≤ P) (hS2 : IsPGroup 2 S)
    (hSn : P ≤ Subgroup.normalizer (S : Set G)) : S ≤ pCoreOf 2 P := by
  have hn : (S.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mpr hSn
  have hp : IsPGroup 2 (S.subgroupOf P) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hle : S.subgroupOf P ≤ CFSG.pCore 2 ↥P := by
    unfold CFSG.pCore; exact le_sSup ⟨hn, hp⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hSP hx⟩, hle hx, rfl⟩

theorem good_of_minimalParabolic {T P M : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTP : T ≤ P)
    (hM : ∀ H : Subgroup G, T ≤ H → H ≤ P → H ≠ P → H ≤ M) (hPM : ¬ P ≤ M)
    {Y : Subgroup G} (hY : Y ≤ P) (hYn : ∀ h ∈ P, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 P)) :
    P ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  by_cases hTY : T ⊔ Y = P
  · rw [hTY]; exact le_sup_right
  exfalso
  have hYM : Y ≤ M := le_sup_right.trans (hM _ le_sup_left (sup_le hTP hY) hTY)
  set B := P ⊓ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G) with hB
  have hFr := le_sup_normalizer_inf hT hTP hY hYn
  have hTB : T ≤ B := by
    intro t ht
    refine ⟨hTP ht, ?_⟩
    show t ∈ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨T.mul_mem (T.mul_mem ht hy1) (T.inv_mem ht), hYn t (hTP ht) y hy2⟩
    · rintro ⟨hy1, hy2⟩
      have e : y = t⁻¹ * (t * y * t⁻¹) * t := by group
      refine ⟨?_, ?_⟩
      · rw [e]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hy1) ht
      · have := hYn t⁻¹ (P.inv_mem (hTP ht)) _ hy2
        rw [inv_inv] at this
        rw [e]; exact this
  by_cases hBP : B = P
  · apply hYT
    rw [inf_comm]
    refine le_pCoreOf_of_normal (inf_le_right.trans hY) hT.isPGroup.to_inf_left ?_
    rw [← hBP]; exact inf_le_right
  · exact hPM (hFr.trans (sup_le hYM (hM B hTB inf_le_left hBP)))

end CFSG.Quasithin.RonanE42.Gen
