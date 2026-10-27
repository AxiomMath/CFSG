module

public import CFSG.Quasithin.H13.L32A716e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_centralizer_le {U A Z : Subgroup G}
    (hD : (centralizerMod Z U A).relIndex U = 2) (hZ : Nat.card Z = 2) {s : G} (hs : s ∈ A) :
    (Subgroup.centralizer ({s} : Set G) ⊓ centralizerMod Z U A).relIndex U ≤ 4 := by
  set D := centralizerMod Z U A with hDdef
  have hDU : D ≤ U := centralizerMod_le_left _ _ _
  have hZc : Subgroup.normalizer (Z : Set G) = Subgroup.centralizer (Z : Set G) :=
    normalizer_eq_centralizer_of_card_eq_two hZ
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    have hab : a ∈ Subgroup.centralizer (Z : Set G) := by
      rw [← hZc]
      exact Subgroup.le_normalizer ha
    exact (Subgroup.mem_centralizer_iff.mp hab b hb).symm
  have hmemZ : ∀ d ∈ D, d * s * d⁻¹ * s⁻¹ ∈ Z := fun d hd => hd.2.2 s hs
  let f : ↥D →* ↥Z :=
    { toFun := fun d => ⟨(d : G) * s * (d : G)⁻¹ * s⁻¹, hmemZ d d.2⟩
      map_one' := by ext; simp
      map_mul' := fun d e => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hdN : (d : G) ∈ Subgroup.centralizer (Z : Set G) := by
          rw [← hZc]
          exact d.2.2.1
        have h1 : (d : G) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) * (d : G)⁻¹ =
            (e : G) * s * (e : G)⁻¹ * s⁻¹ := by
          rw [(Subgroup.mem_centralizer_iff.mp hdN _ (hmemZ e e.2)).symm, mul_inv_cancel_right]
        calc (d : G) * e * s * ((d : G) * e)⁻¹ * s⁻¹ =
            ((d : G) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) * (d : G)⁻¹) *
              ((d : G) * s * (d : G)⁻¹ * s⁻¹) := by group
          _ = ((e : G) * s * (e : G)⁻¹ * s⁻¹) * ((d : G) * s * (d : G)⁻¹ * s⁻¹) := by rw [h1]
          _ = ((d : G) * s * (d : G)⁻¹ * s⁻¹) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) :=
            hZcomm _ (hmemZ e e.2) _ (hmemZ d d.2) }
  have hker : (Subgroup.centralizer ({s} : Set G)).subgroupOf D = f.ker := by
    ext d
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_ker]
    constructor
    · intro hd
      apply Subtype.ext
      change (d : G) * s * (d : G)⁻¹ * s⁻¹ = 1
      rw [hd, mul_inv_cancel_right, mul_inv_cancel]
    · intro hd
      have h1 : (d : G) * s * (d : G)⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hd
      calc (d : G) * s = ((d : G) * s * (d : G)⁻¹ * s⁻¹) * (s * d) := by group
        _ = s * d := by rw [h1, one_mul]
  have h2 : (Subgroup.centralizer ({s} : Set G)).relIndex D ≤ 2 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker, ← hZ]
    exact Subgroup.card_le_card_group f.range
  have h3 := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer ({s} : Set G)) D U
  rw [inf_eq_left.mpr hDU, hD] at h3
  omega

end Index

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
  {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include E hF N

theorem comm_dalpha : ∀ d ∈ centralizerMod (Quasithin.conjSub ((k : G) * g) (fsuV1 T V))
    (fsuU T V) (Quasithin.conjSub ((k : G) * g) (fsuU T V)),
    ∀ x ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓ pCoreOf 2 (hz T V),
      d * x = x * d := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h7 := hF.F913_7 N.setup
  have hUk : Quasithin.conjSub (k : G) (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem)
  have hQk : Quasithin.conjSub (k : G) (pCoreOf 2 (hz T V)) = pCoreOf 2 (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ N.mem)
  have eD : centralizerMod (Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
      (Quasithin.conjSub ((k : G) * g) (fsuU T V)) =
      Quasithin.conjSub (k : G) (F8.DH V (fsuV1 T V) (hz T V) (g : G)) := by
    rw [F8.DH, conjSub_centralizerMod, F8.A₁, F8.Uγ, ← Quasithin.conjSub_mul,
      ← Quasithin.conjSub_mul, hUk, E.fsuU_eq]
  have eA : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓ pCoreOf 2 (hz T V) =
      Quasithin.conjSub (k : G) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) := by
    rw [hF.Dγ_eq_inf_pCoreOf N.setup, Quasithin.conjSub_inf, hQk]
  have hc : ⁅Quasithin.conjSub (k : G) (F8.DH V (fsuV1 T V) (hz T V) (g : G)),
      Quasithin.conjSub (k : G) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G))⁆ = ⊥ := by
    rw [Quasithin.conjSub, Quasithin.conjSub, ← Subgroup.map_commutator]
    change Quasithin.conjSub (k : G) _ = ⊥
    rw [h7]
    exact Subgroup.map_bot _
  intro d hd x hx
  rw [eD] at hd
  rw [eA] at hx
  have h1 : ⁅d, x⁆ = 1 := by
    rw [← Subgroup.mem_bot, ← hc]
    exact Subgroup.commutator_mem_commutator hd hx
  rw [commutatorElement_def] at h1
  calc d * x = (d * x * d⁻¹ * x⁻¹) * (x * d) := by group
    _ = x * d := by rw [h1, one_mul]

theorem centralizer_ualpha_eq :
    fsuU T V ⊓ Subgroup.centralizer
      (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) : Set G) =
      ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  set hh := hF.toHypF91 with hhdef
  obtain ⟨-, -, c, y, -, -, hcL, -, hc3, -, -, hyT, hyC, hy2, hy4, huniq, -, hfpf, -, -, h64, -,
    h4c⟩ := E.exists_frame hF
  obtain ⟨heqE, -⟩ := E.wsub_e_eq hF hcL hc3 hyT hyC hy2 hy4 huniq hfpf h64 h4c
  have heq := E.ualpha_eq hF N hy2 hy4 huniq
  have h2 := E.relIndex_uα hF N
  obtain ⟨s, hsA, hsQ, hsw⟩ := N.exists_mem_not_mem h hMod hF h2
  have hAeq := Not1471.uα_eq (g := g) (k := k) h hMod
  have hAhz : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ hz T V := by
    have hAR : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤
        pCoreOf 2 (l1 T L V ⊔ T) := by
      rw [← l1_eq_L₁Of]
      exact N.uα_le hF
    exact hAR.trans E.r1_le_hz
  have hsA' : s ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) := hAeq ▸ hsA
  have hshz := hAhz hsA'
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have hsy : QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) = y ^ 2 := by
    have hsm : QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) ∈ Subgroup.zpowers (y ^ 2) := by
      rw [← heq]
      exact mem_modO2Image_iff.mpr ⟨_, hsA', rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hsm
    have hs1 : (QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) :
        ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ≠ 1 := by
      intro e
      apply hsQ
      rw [QuotientGroup.eq_one_iff] at e
      exact ⟨_, e, rfl⟩
    rw [← hn] at hs1 ⊢
    have hsq : (y ^ 2) ^ 2 = 1 := by rw [sq]; exact hy22
    rcases zpow_eq_one_or_self hsq n with h0 | h0
    · exact absurd h0 hs1
    · exact h0
  set C := fsuU T V ⊓ Subgroup.centralizer
    (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) : Set G) with hC
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hEU : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ fsuU T V := commutator_fsuU_le E.S.hyp hMod
  have hCE : C ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
    intro u hu
    have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu.1
    have hus : s * u * s⁻¹ * u⁻¹ ∈ fsuV1 T V := by
      have : u * s = s * u := (Subgroup.mem_centralizer_iff.mp hu.2 s hsA').symm
      rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    have hfix : clsU hh huU ∈ fixV (Subgroup.zpowers (rhoDot hh (y ^ 2))) := by
      rw [HeisMod.mem_fixV_zpowers, ← hsy, rhoDot_mk, rhoH_clsU_eq_iff]
      exact hus
    rw [← heqE] at hfix
    obtain ⟨e, heU, heE, hee⟩ := exists_clsU_of_mem_Wsub hh (hUe ▸ hEU) hfix
    have h3 : e⁻¹ * u ∈ fsuV1 T V := (clsU_eq_iff _ heU huU).mp hee
    have e1 : u = e * (e⁻¹ * u) := by group
    rw [e1]
    exact Subgroup.mul_mem _ heE (E.v1_le_e hF N h3)
  have hD := N.relIndex_D h hMod hF h2
  have hcard : Nat.card ↥(Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact E.card_v1
  have hle4 := relIndex_inf_centralizer_le hD hcard hsA
  have hCD : Subgroup.centralizer ({s} : Set G) ⊓ centralizerMod
      (Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
      (Quasithin.conjSub ((k : G) * g) (fsuU T V)) ≤ C := by
    rintro d ⟨hds, hdD⟩
    refine ⟨centralizerMod_le_left _ _ _ hdD, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hdsc : d * s = s * d := Subgroup.mem_centralizer_singleton_iff.mp hds
    rcases hsw w (hAeq ▸ hw) with hwQ | hwQ
    · exact (E.comm_dalpha hF N d hdD w ⟨hw, hwQ⟩).symm
    · have hsw' : s⁻¹ * w ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hsA') hw
      have h4 := E.comm_dalpha hF N d hdD _ ⟨hsw', hwQ⟩
      calc w * d = s * (s⁻¹ * w) * d := by group
        _ = s * d * (s⁻¹ * w) := by rw [mul_assoc, ← h4, ← mul_assoc]
        _ = d * s * (s⁻¹ * w) := by rw [hdsc]
        _ = d * w := by group
  have hCU : C.relIndex (fsuU T V) ≤ 4 := by
    have hne : (Subgroup.centralizer ({s} : Set G) ⊓ centralizerMod
        (Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
        (Quasithin.conjSub ((k : G) * g) (fsuU T V))).relIndex (fsuU T V) ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.relIndex_dvd_of_le_left _ hCD)).trans
      hle4
  have hEU4 := (E.relIndex_ve_eu hF N).2
  have hmul := Subgroup.relIndex_mul_relIndex C ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ (fsuU T V) hCE hEU
  rw [hEU4] at hmul
  have hCE1 : C.relIndex ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 1 := by
    have hne : C.relIndex ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    omega
  exact le_antisymm hCE (Subgroup.relIndex_eq_one.mp hCE1)

end Ctx7153

end CFSG.Quasithin.H13.L32A
