module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4USyl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Syl

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem centralizer_le_centralizerMod (S : Setting146 G T M) (hH : IsHTM T M H) (u : G) :
    H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
    centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ≤
      Subgroup.normalizer ((H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) := by
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  refine ⟨?_, ?_⟩
  · rintro x ⟨hxH, hxc⟩
    refine ⟨hxH, S.normalizer_Z.ge (hHG hxH), fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute u x := Subgroup.mem_centralizer_iff.mp hxc u rfl
    have : x * u ^ k * x⁻¹ * (u ^ k)⁻¹ = 1 := by
      have h1 : Commute (u ^ k) x := hcomm.zpow_left k
      rw [← h1.eq]
      group
    rw [this]
    exact Subgroup.one_mem _
  · refine S146A.le_normalizer_of_forall_conj_mem fun a ha k hk => ?_
    obtain ⟨hkH, hkc⟩ := hk
    have haH : a ∈ H := ha.1
    have ha' := (centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u)).inv_mem ha
    have hz₂ : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T :=
      ha'.2.2 u (Subgroup.mem_zpowers u)
    refine ⟨H.mul_mem (H.mul_mem haH hkH) (H.inv_mem haH), ?_⟩
    show a * k * a⁻¹ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    set z₂ := a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ with hz₂def
    have hb : a⁻¹ * w * a = z₂ * w := by rw [hz₂def]; group
    have hkz : k * z₂ = z₂ * k := S146T.comm_Z (hHG hkH) hz₂
    have hwk : w * k = k * w := Subgroup.mem_centralizer_iff.mp hkc w rfl
    have hmid : (a⁻¹ * w * a) * k = k * (a⁻¹ * w * a) := by
      rw [hb]
      calc z₂ * w * k = z₂ * (w * k) := by group
        _ = z₂ * (k * w) := by rw [hwk]
        _ = (z₂ * k) * w := by group
        _ = (k * z₂) * w := by rw [hkz]
        _ = k * (z₂ * w) := by group
    calc w * (a * k * a⁻¹) = a * ((a⁻¹ * w * a) * k) * a⁻¹ := by group
      _ = a * (k * (a⁻¹ * w * a)) * a⁻¹ := by rw [hmid]
      _ = (a * k * a⁻¹) * w := by group

theorem isSylowTwoOf_tU_of_plane (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb)
    (hT4 : (pCoreOf 2 H).relIndex T = 4)
    (hidx : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex T = 2)
    {u : G} (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Qa)) (huZ : u ∉ quasithinOmegaOneCenter T)
    (hT0 : tZero T u = T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)) :
    IsSylowTwoOf (tU T u) (H ⊓ Subgroup.centralizer ({u} : Set G)) := by
  classical
  have hTH : T ≤ H := hH.1.1
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr hUu hu
  have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h hUu).mp (by rw [← hkc, e]; rfl))
  have hkns : k ∈ Nonsingular P := by
    rw [hstr.nonsingular_eq hp]
    exact ⟨hk1, Or.inl hk⟩
  have hstab6 := hstr.card_stabilizer_nonsingular hp hkns
  let Stab : Subgroup (MulAut ↥(kOf (rhoH h))) :=
    (MulAction.stabilizer ↥(resBeta (rhoH h)).range k).map (resBeta (rhoH h)).range.subtype
  have hStabr : Stab ≤ (resBeta (rhoH h)).range := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hcardStab : Nat.card Stab = 6 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hstab6
  have hrelA' : (pCoreOf 2 H).relIndex (HLb (resBeta (rhoH h)) Stab) = 6 := by
    rw [relIndex_pCoreOf_HLb h hsplit hStabr]
    exact hcardStab
  have hAA' : centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ≤
      HLb (resBeta (rhoH h)) Stab := by
    rintro x ⟨hxH, -, hx⟩
    have h1 := (rhoH_clsU_eq_iff h ⟨x, hxH⟩ hUu).mpr (hx u (Subgroup.mem_zpowers u))
    have hfix : resBeta (rhoH h) ⟨x, hxH⟩ k = k := by
      refine Subtype.ext ((resBeta_apply _ _ _).trans ?_)
      rw [hkc]
      exact h1
    refine (mem_HLb_iff hxH).mpr (Subgroup.mem_map.mpr
      ⟨⟨resBeta (rhoH h) ⟨x, hxH⟩, ⟨⟨x, hxH⟩, rfl⟩⟩, ?_, rfl⟩)
    exact (MulAction.mem_stabilizer_iff).mpr hfix
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT₀ : pCoreOf 2 H ≤ T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) :=
    le_inf hTsyl.pCoreOf_le ((pCoreOf_le_HLb h hsplit Qa).trans Subgroup.le_normalizer)
  have hT₀rel : (pCoreOf 2 H).relIndex
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)) = 2 := by
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hQT₀ inf_le_left
    rw [hidx, hT4] at hmul
    omega
  have hT₀A : T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) ≤
      centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) := by
    rw [← hT0]
    exact centralizerMod_mono_left _ hTH
  have hT₀A' := hT₀A.trans hAA'
  have hrel3 : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex
      (HLb (resBeta (rhoH h)) Stab) = 3 := by
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hQT₀ hT₀A'
    rw [hT₀rel, hrelA'] at hmul
    omega
  have hT₀syl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G))
      (HLb (resBeta (rhoH h)) Stab) :=
    ⟨hT₀A', S.hyp.sylow.1.to_le inf_le_left, by
      show ¬ 2 ∣ (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex _
      rw [hrel3]
      omega⟩
  have hTA := B6.isSylowTwoOf_mono hT₀syl hT₀A hAA'
  obtain ⟨hKA, hAK⟩ := centralizer_le_centralizerMod S hH u
  have hsyl := B6.isSylowTwoOf_inf_normal hTA hKA hAK
  have heq : T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) ⊓
      (H ⊓ Subgroup.centralizer ({u} : Set G)) = tU T u := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, -, hxc⟩
      exact ⟨hxT, hxc⟩
    · rintro ⟨hxT, hxc⟩
      have hx0 : x ∈ tZero T u := tU_le_tZero T u ⟨hxT, hxc⟩
      rw [hT0] at hx0
      exact ⟨hx0, hTH hxT, hxc⟩
  rwa [heq] at hsyl

end Syl

end CFSG.Quasithin
