module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape2
public import CFSG.LieType.Ree.SuzukiBorelHall

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open CFSG.QuasithinUnique.Setup.X7
open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_mem_x1_of_commutator_mem_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {y x : G} (hy : y ∈ d.D1) (hy1 : y ≠ 1)
    (hx : x ∈ str83X L1 L2 S) (hyx : y * x * y⁻¹ * x⁻¹ ∈ str83X1 L1 L2 S) :
    x ∈ str83X1 L1 L2 S := by
  classical
  have hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83X1 L1 L2 S)
      (str83X L1 L2 S) := str83G4_isChiefStep_x1_x hfr d hX hB
  have hZ1X1 : Z1 L1 L2 S ≤ str83X1 L1 L2 S := str83G4_z1_le_x1 hfr
  have hnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83X1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) :=
    str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB
  obtain ⟨hHL, hHN, hNL, hE, hO, e, he, hnt⟩ :=
    str83G4_exists_sectionSetup hfr hstep hZ1X1 hnc
  have hC := str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB
  have hquad := str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  letI : CommGroup (Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S)) :=
    l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod (str83X1 L1 L2 S)
      (str83X L1 L2 S))) := l2ChiefSectionModule hE
  let ρ : Representation (ZMod 2) (suzukiGroup a K)
      (Additive (Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S))) :=
    sectionRep hHL hHN hNL hE hO e
  have hρ : IsSzNatural ρ :=
    sectionRep_isSzNatural_of_quadratic hfr hC hquad hstep hHL hHN hNL hE hO e he hnt
  have hyH : y ∈ L1 ⊔ S :=
    Subgroup.mem_sup_left ((CFSG.Quasithin.F1.borelOf_le L1 S) (d.hD1hall.1 hy))
  let yH : ↥(L1 ⊔ S) := ⟨y, hyH⟩
  let g : suzukiGroup a K := e (QuotientGroup.mk yH)
  have hg1 : g ≠ 1 := by
    intro hg
    haveI : (pCore 2 ↥(L1 ⊔ S)).Normal := pCore_normal
    have hq : (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) yH = 1 := by
      apply e.injective
      simpa [g] using hg
    have hyCore : y ∈ pCoreOf 2 (L1 ⊔ S) := by
      have hmem : yH ∈ pCore 2 ↥(L1 ⊔ S) := by
        have hker : yH ∈ MonoidHom.ker (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) := by
          rw [MonoidHom.mem_ker]
          exact hq
        rwa [QuotientGroup.ker_mk'] at hker
      exact (CFSG.Quasithin.F1.mem_pCore_iff_coe yH).mp hmem
    rw [str83G4_pCoreOf_sup_left hfr] at hyCore
    have hbot : d.D1 ⊓ Q1 L1 L2 S = ⊥ := by
      rw [inf_comm]
      exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P1 L1 L2 S))
        d.hD1hall.2.1
    have hmem : y ∈ d.D1 ⊓ Q1 L1 L2 S := ⟨hy, hyCore⟩
    rw [hbot] at hmem
    exact hy1 (Subgroup.mem_bot.mp hmem)
  have hoddg : Odd (orderOf g) := by
    have hoddY : Odd (orderOf yH) := by
      rw [Subgroup.orderOf_mk]
      exact Odd.of_dvd_nat d.hD1hall.2.1
        (Subgroup.orderOf_mk y hy ▸ orderOf_dvd_natCard (⟨y, hy⟩ : ↥d.D1))
    have hdvd1 : orderOf ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) yH) ∣
        orderOf yH := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) yH
      simpa using h
    have hdvd2 : orderOf g ∣
        orderOf ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) yH) := by
      rw [show g = e ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) yH) from rfl,
        MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hoddY (hdvd2.trans hdvd1)
  have hyNS : y ∈ Subgroup.normalizer (S : Set G) :=
    hfr.2.1 ((d.hD1hall.1.trans (le_sup_left.trans le_sup_left)) hy)
  have hyNH : yH ∈ Subgroup.normalizer ((S.subgroupOf (L1 ⊔ S) : Subgroup ↥(L1 ⊔ S)) :
      Set ↥(L1 ⊔ S)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hysS : y * (s : G) * y⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hyNS (s : G)).mp hsS
      exact Subgroup.mem_subgroupOf.mpr hysS
    · intro hs
      have hsS : y * (s : G) * y⁻¹ ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hysS : y⁻¹ * (y * (s : G) * y⁻¹) * y ∈ S := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyNS) _).mp hsS
      have heq : y⁻¹ * (y * (s : G) * y⁻¹) * y = (s : G) := by group
      rw [heq] at hysS
      exact Subgroup.mem_subgroupOf.mpr hysS
  have hqN : QuotientGroup.mk yH ∈ Subgroup.normalizer
      (((S.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))) :
        Set (oTwoQuot ↥(L1 ⊔ S))) :=
    Subgroup.le_normalizer_map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))
      (Subgroup.mem_map_of_mem _ hyNH)
  have hgNU : g ∈ Subgroup.normalizer ((suzukiU a K) : Set (suzukiGroup a K)) := by
    have h := Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hqN)
    have hmap : Subgroup.map e.toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))
          (S.subgroupOf (L1 ⊔ S))) = suzukiU a K := by
      rw [Subgroup.map_map]
      have h' := he
      rw [Subgroup.map_map] at h'
      simpa [szSbar] using h'
    rwa [hmap] at h
  have hgB : g ∈ suzukiB a K := by
    have h := hgNU
    rwa [normalizer_suzukiU_e34 hK] at h
  obtain ⟨v, hvB, htT⟩ :=
    exists_conj_mem_suzukiT_of_mem_suzukiB_of_odd hK hgB hoddg
  let t : suzukiGroup a K := v * g * v⁻¹
  have ht1 : t ≠ 1 := by
    intro ht
    apply hg1
    have h := congrArg (fun z => v⁻¹ * z * v) ht
    simpa [t, mul_assoc] using h
  have hxyX : y * x * y⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hHN hyH) x).mp hx
  have hιeq : Ch3z.chiefIota hNL (⟨y * x * y⁻¹, hxyX⟩ : ↥(str83X L1 L2 S)) =
      Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S)) := by
    have hprod : (⟨y * x * y⁻¹, hxyX⟩ : ↥(str83X L1 L2 S)) =
        (⟨y * x * y⁻¹ * x⁻¹, str83G4_x1_le_x L1 L2 S hyx⟩ :
          ↥(str83X L1 L2 S)) * ⟨x, hx⟩ := by
      apply Subtype.ext
      change y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x
      group
    have hkill : Ch3z.chiefIota hNL
        (⟨y * x * y⁻¹ * x⁻¹, str83G4_x1_le_x L1 L2 S hyx⟩ :
          ↥(str83X L1 L2 S)) = 1 :=
      (Ch3z.chiefIota_eq_one_iff hNL _).mpr hyx
    calc Ch3z.chiefIota hNL (⟨y * x * y⁻¹, hxyX⟩ : ↥(str83X L1 L2 S))
        = Ch3z.chiefIota hNL ((⟨y * x * y⁻¹ * x⁻¹,
            str83G4_x1_le_x L1 L2 S hyx⟩ : ↥(str83X L1 L2 S)) * ⟨x, hx⟩) := by
          rw [hprod]
      _ = Ch3z.chiefIota hNL (⟨y * x * y⁻¹ * x⁻¹,
            str83G4_x1_le_x L1 L2 S hyx⟩ : ↥(str83X L1 L2 S)) *
          Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S)) := map_mul _ _ _
      _ = Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S)) := by rw [hkill, one_mul]
  have hw0 : ρ g (Additive.ofMul (Ch3z.chiefIota hNL (⟨x, hx⟩ :
      ↥(str83X L1 L2 S)))) =
      Additive.ofMul (Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S))) := by
    have h := sectionRep_chiefIota hHL hHN hNL hE hO e yH ⟨x, hx⟩ hxyX
    calc ρ g (Additive.ofMul (Ch3z.chiefIota hNL (⟨x, hx⟩ :
          ↥(str83X L1 L2 S))))
        = Additive.ofMul (Ch3z.chiefIota hNL (⟨y * x * y⁻¹, hxyX⟩ :
            ↥(str83X L1 L2 S))) := by simpa [g] using h
      _ = Additive.ofMul (Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S))) := by
          rw [hιeq]
  let w0 : Additive (Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S)) :=
    Additive.ofMul (Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S)))
  let w1 : Additive (Ch3z.chiefMod (str83X1 L1 L2 S) (str83X L1 L2 S)) := ρ v w0
  have hw1fix : ρ t w1 = w1 := by
    calc ρ t w1 = ρ (v * g * v⁻¹) (ρ v w0) := by rw [show t = v * g * v⁻¹ from rfl]
      _ = ρ v (ρ g (ρ v⁻¹ (ρ v w0))) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ v (ρ g w0) := by
          have hvinv : ρ v⁻¹ (ρ v w0) = w0 := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]
          rw [hvinv]
      _ = ρ v w0 := by rw [show w0 = Additive.ofMul (Ch3z.chiefIota hNL
          (⟨x, hx⟩ : ↥(str83X L1 L2 S))) from rfl, hw0]
      _ = w1 := rfl
  let Hfix : Subgroup (suzukiGroup a K) :=
    { carrier := {h | ρ h w1 = w1}
      one_mem' := by
        change ρ 1 w1 = w1
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        change ρ (a * b) w1 = w1
        rw [map_mul]
        change (ρ a * ρ b) w1 = w1
        rw [Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change ρ a⁻¹ w1 = w1
        have h1 : ρ a (ρ a⁻¹ w1) = w1 := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        have hinj : Function.Injective (ρ a) := by
          intro u v huv
          have h2 := congrArg (ρ a⁻¹) huv
          simpa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] using h2
        exact hinj (h1.trans ha.symm) }
  have htH : t ∈ Hfix := hw1fix
  have hle : Subgroup.zpowers t ≤ Hfix := Subgroup.zpowers_le.mpr htH
  have hmemfix : w1 ∈ fixedSub ρ (Subgroup.zpowers t) :=
    mem_fixedSub.mpr fun h hh => hle hh
  have hbot : fixedSub ρ (Subgroup.zpowers t) = ⊥ :=
    isSzNatural_mem_suzukiT_fixedSub_eq_bot hK ρ hρ htT ht1
  rw [hbot] at hmemfix
  have hw1zero : w1 = 0 := by simpa using hmemfix
  have hw0zero : w0 = 0 := by
    have hcomp : ρ v⁻¹ w1 = w0 := by
      rw [show w1 = ρ v w0 from rfl, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    calc w0 = ρ v⁻¹ w1 := hcomp.symm
      _ = ρ v⁻¹ 0 := by rw [hw1zero]
      _ = 0 := map_zero _
  have hix : Ch3z.chiefIota hNL (⟨x, hx⟩ : ↥(str83X L1 L2 S)) = 1 := by
    have h := congrArg Additive.toMul hw0zero
    simpa [w0] using h
  exact (Ch3z.chiefIota_eq_one_iff hNL _).mp hix

theorem str83G4_d1_inf_h2_eq_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    d.D1 ⊓ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 = ⊥ := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hBfr, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨V, hVZ, hcentral, hVNat⟩ :=
    str83G3Output_of_z2Central str83G4Z2Central_holds G L1 L2 S a
      ⟨hF, hBfr, ha, hSz, hL2, hZI⟩
  have hV : Str83G4V L1 L2 S V a := ⟨hVZ, hcentral, hVNat⟩
  obtain ⟨hstepV, -, hVea, -⟩ := hVNat
  have hVne : V ≠ ⊥ := by
    intro h
    have hlt := hstepV.2.2.1
    rw [h] at hlt
    exact (lt_irrefl ⊥) hlt
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := A4.omegaOneCenterOf_le (Q2 L1 L2 S)
  have hVS : V ≤ S := hVZ.trans (hZ2Q2.trans hQ2S)
  have hVX : V ≤ str83X L1 L2 S := hVZ.trans (z2_le_str83X L1 L2 S)
  have hQ2cent : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hpCoreL2_le_Q2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
    have h := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (le_sup_left : L2 ≤ L2 ⊔ S)
      (sup_le Subgroup.le_normalizer hF.1.h2.normalizes)
    rwa [str83G4_pCoreOf_sup_right hfr'] at h
  have hQ2N : L2 ⊓ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (inf_le_left : L2 ⊓ S ≤ L2).trans
      ((le_sup_left : L2 ≤ L2 ⊔ S).trans
        ((sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
          (le_normalizer_pCoreOf 2 (P2 L1 L2 S))))
  have hV_irr : ∀ W : Subgroup G, W ≤ V →
      (∀ l ∈ L2, ∀ w ∈ W, l * w * l⁻¹ ∈ W) → W = ⊥ ∨ W = V := by
    intro W hWV hinv
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hBfr
        (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
    have hSinv : ∀ s ∈ S, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
      intro s hs w hw
      have hs' : s ∈ Q2 L1 L2 S ⊔ (L2 ⊓ S) := by
        rw [inf_comm, sup_comm, ← hS2]
        exact hs
      obtain ⟨q, hq, l, hl, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ2N).mp hs'
      have hlZW : l * w * l⁻¹ ∈ W := hinv l hl.1 w hw
      have hZW : l * w * l⁻¹ ∈ Z2 L1 L2 S := hVZ (hWV hlZW)
      have hqcomm := (Subgroup.mem_centralizer_iff.mp (hQ2cent hq))
        (l * w * l⁻¹) hZW
      have hqW : q * (l * w * l⁻¹) * q⁻¹ = l * w * l⁻¹ := by
        calc q * (l * w * l⁻¹) * q⁻¹ = (l * w * l⁻¹) * q * q⁻¹ := by rw [hqcomm]
          _ = l * w * l⁻¹ := by group
      have hqW' : (q * l) * w * (q * l)⁻¹ = l * w * l⁻¹ := by
        calc (q * l) * w * (q * l)⁻¹ = q * (l * w * l⁻¹) * q⁻¹ := by group
          _ = l * w * l⁻¹ := hqW
      rw [hqW']
      exact hlZW
    have hWN : L2 ⊔ S ≤ Subgroup.normalizer (W : Set G) := by
      refine sup_le ?_ ?_
      · intro l hl
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · exact hinv l hl w
        · intro hw
          have h := hinv l⁻¹ (L2.inv_mem hl) (l * w * l⁻¹) hw
          simpa [mul_assoc] using h
      · intro s hs
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · exact hSinv s hs w
        · intro hw
          have h := hSinv s⁻¹ (S.inv_mem hs) (s * w * s⁻¹) hw
          simpa [mul_assoc] using h
    have hnorm : IsNormalIn (L2 ⊔ S) V W :=
      ⟨hWV, fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hWN hg) w).mp hw⟩
    exact hstepV.2.2.2 W hnorm bot_le hWV
  have hZ1eq : Z1 L1 L2 S = omegaOneCenterOf S :=
    (str83_caseI_basics hF hBfr ha hSz hL2 hZI).1
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str83_caseI_basics hF hBfr ha hSz hL2 hZI).2.1
  have hZ1V : Z1 L1 L2 S ≤ V := by
    have h := str83G4_z1_eq_inf_centralizer hfr' hV
    rw [h]
    exact inf_le_left
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hL2NZ2 : L2 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ L2 ⊔ S).trans
      ((sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)))
  have hSNV : S ≤ Subgroup.normalizer (V : Set G) :=
    (le_sup_right : S ≤ L2 ⊔ S).trans (D14.le_normalizer_of_isNormalIn hstepV.1)
  have hQ1NV : Q1 L1 L2 S ≤ Subgroup.normalizer (V : Set G) :=
    (str83G4_q1_le_s hfr').trans hSNV
  rw [eq_bot_iff]
  intro y hy
  by_cases hy1 : y = 1
  · exact Subgroup.mem_bot.mpr hy1
  exfalso
  have hyD1 : y ∈ d.D1 := hy.1
  have hyH2 : y ∈ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 := hy.2
  have hCinv : ∀ l ∈ L2, ∀ z ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G),
      l * z * l⁻¹ ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro l hl z hz
    obtain ⟨hzZ, hzC⟩ := hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hL2NZ2 hl) z).mp hzZ, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    have hay : a = y := Set.mem_singleton_iff.mp ha
    subst a
    have hq : y * l * y⁻¹ * l⁻¹ ∈ Q2 L1 L2 S := hpCoreL2_le_Q2 (hyH2.2.2 l hl)
    have hyl : y * l * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l := by group
    have hylinv : y * l⁻¹ * y⁻¹ = l⁻¹ * (y * l * y⁻¹ * l⁻¹)⁻¹ := by group
    have hyz : y * z * y⁻¹ = z := by
      have hzy : y * z = z * y :=
        (Subgroup.mem_centralizer_iff.mp hzC) y (Set.mem_singleton y)
      calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [hzy]
        _ = z := by group
    have hZl : l * z * l⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hL2NZ2 hl) z).mp hzZ
    have hqcomm : (l * z * l⁻¹) * (y * l * y⁻¹ * l⁻¹) =
        (y * l * y⁻¹ * l⁻¹) * (l * z * l⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hQ2cent hq)) (l * z * l⁻¹) hZl
    have hconj : y * (l * z * l⁻¹) * y⁻¹ =
        (y * l * y⁻¹) * (y * z * y⁻¹) * (y * l⁻¹ * y⁻¹) := by group
    have hconj_eq : y * (l * z * l⁻¹) * y⁻¹ = l * z * l⁻¹ := by
      rw [hconj, hyl, hyz, hylinv]
      rw [show ((y * l * y⁻¹ * l⁻¹) * l) * z *
          (l⁻¹ * (y * l * y⁻¹ * l⁻¹)⁻¹) =
          (y * l * y⁻¹ * l⁻¹) * (l * z * l⁻¹) *
            (y * l * y⁻¹ * l⁻¹)⁻¹ by group]
      rw [← hqcomm]
      group
    calc y * (l * z * l⁻¹) = (y * (l * z * l⁻¹) * y⁻¹) * y := by group
      _ = (l * z * l⁻¹) * y := by rw [hconj_eq]
  have hZ1C : Z1 L1 L2 S ≤ Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    refine ⟨hZ1Z2 hz, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    have hay : a = y := Set.mem_singleton_iff.mp ha
    subst a
    have hyL1Q1 : y ∈ L1 ⊔ Q1 L1 L2 S :=
      Subgroup.mem_sup_left ((CFSG.Quasithin.F1.borelOf_le L1 S) (d.hD1hall.1 hyD1))
    exact ((Subgroup.mem_centralizer_iff.mp (hZI hyL1Q1)) z hz).symm
  have hCVinv : ∀ l ∈ L2,
      ∀ z ∈ (Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V,
      l * z * l⁻¹ ∈ (Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V := by
    intro l hl z hz
    have hL2NV : L2 ≤ Subgroup.normalizer (V : Set G) :=
      (le_sup_left : L2 ≤ L2 ⊔ S).trans (D14.le_normalizer_of_isNormalIn hstepV.1)
    exact ⟨hCinv l hl z hz.1, (Subgroup.mem_normalizer_iff.mp (hL2NV hl) z).mp hz.2⟩
  have hCVeq : (Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V = V := by
    rcases hV_irr ((Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V)
      inf_le_right hCVinv with h | h
    · exfalso
      have hZ1bot : Z1 L1 L2 S ≤ ⊥ := (le_inf hZ1C hZ1V).trans (le_of_eq h)
      exact hZ1ne (le_bot_iff.mp hZ1bot)
    · exact h
  have hyCentV : ∀ v ∈ V, y * v * y⁻¹ = v := by
    intro v hv
    have hv' : v ∈ (Z2 L1 L2 S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V := by
      rw [hCVeq]
      exact hv
    have hvC : v ∈ Subgroup.centralizer ({y} : Set G) := hv'.1.2
    have hvy : y * v = v * y :=
      (Subgroup.mem_centralizer_iff.mp hvC) y (Set.mem_singleton y)
    calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [hvy]
      _ = v := by group
  have hVX1 : V ≤ str83X1 L1 L2 S := by
    intro v hv
    refine str83G4_mem_x1_of_commutator_mem_x1 hfr' d hX hB hyD1 hy1 (hVX hv) ?_
    have hcomm : y * v * y⁻¹ * v⁻¹ = 1 := by
      rw [hyCentV v hv]
      group
    rw [hcomm]
    exact (str83X1 L1 L2 S).one_mem
  have hVcommO2 : ∀ u ∈ oTwoUpper (L1 ⊔ S), ∀ v ∈ V,
      u * v * u⁻¹ * v⁻¹ = 1 := by
    intro u hu v hv
    have hvX1 : v ∈ str83X1 L1 L2 S := hVX1 hv
    have hmem : ⁅v, u⁆ ∈ ⁅str83X1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ :=
      Subgroup.commutator_mem_commutator hvX1 hu
    rw [str83G4_commutator_x1_oTwo_eq_bot hfr' hX, Subgroup.mem_bot] at hmem
    have hinv : ⁅u, v⁆ = ⁅v, u⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    change ⁅u, v⁆ = 1
    rw [hinv, hmem, inv_one]
  have hO2NV : oTwoUpper (L1 ⊔ S) ≤ Subgroup.normalizer (V : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h := hVcommO2 u hu v hv
      have huv : u * v * u⁻¹ = v := by
        calc u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v := by group
          _ = v := by rw [h, one_mul]
      rwa [huv]
    · intro hv
      have h := hVcommO2 u⁻¹ ((oTwoUpper (L1 ⊔ S)).inv_mem hu) (u * v * u⁻¹) hv
      have hveq : v = u * v * u⁻¹ := by
        calc v = (u⁻¹ * (u * v * u⁻¹) * (u⁻¹)⁻¹ * (u * v * u⁻¹)⁻¹) *
              (u * v * u⁻¹) := by group
          _ = 1 * (u * v * u⁻¹) := by rw [h]
          _ = u * v * u⁻¹ := one_mul _
      rw [hveq]
      exact hv
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (V : Set G) := by
    rw [← str83G4_oTwoUpper_sup_left hfr' d]
    exact sup_le hO2NV hQ1NV
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (sup_le ((le_sup_left : L1 ≤ L1 ⊔ S).trans hHN)
      ((le_sup_left : L2 ≤ L2 ⊔ S).trans
        (D14.le_normalizer_of_isNormalIn hstepV.1))) hSNV
  have hpc : V ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hVS.trans (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S)) hG0N hVea.isPGroup
  have hVleBot : V ≤ ⊥ := by
    rw [← hF.1.o2]
    exact hpc
  exact hVne (le_bot_iff.mp hVleBot)

theorem str83G4_eq_one_of_mem_d1_of_trivial_l2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1 := by
  intro x hx hcomm
  have hxB : x ∈ bigB L1 L2 S :=
    (d.hD1hall.1.trans (le_sup_left.trans le_sup_left)) hx
  have hxNL2 : x ∈ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 hfr.1.1.symm
    rw [← bigB_comm] at h
    exact h hxB
  have hxNQ2 : x ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    (normalizer_le_normalizer_pCoreOf 2 L2) hxNL2
  have hxH2 : x ∈ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 :=
    mem_centralizerMod.mpr ⟨Subgroup.mem_sup_left hx, hxNQ2, hcomm⟩
  have hmem : x ∈ d.D1 ⊓ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 :=
    ⟨hx, hxH2⟩
  rw [str83G4_d1_inf_h2_eq_bot hfr d hX hB] at hmem
  exact Subgroup.mem_bot.mp hmem

end CFSG.Quasithin.Stroth

end
