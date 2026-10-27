module

import CFSG.RankThree.GF2n.Tim79a34BigB
public import CFSG.RankThree.GF2n.Tim79a34BigPAct
import CFSG.RankThree.GF2n.Tim79a34BigAssembly
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
import CFSG.RankThree.GF2n.Tim79a34BigIWProof
public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
import CFSG.Algebra.FieldAddSubgroup
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.GroupTheory.SteinbergCBFTCores

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem BigEndHyp.exists_torus [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {l : GaloisField 2 f} (hl : l ≠ 0) :
    ∃ x : ↥(xOf V H), (x : G) ∈ M ∧ SpExtras.mat n (GaloisField 2 f)
      (Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x)) *ᵥ a = l • a := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero ha (smul_ne_zero hl ha)
  obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g)
  have hxΦ : Φ.symm (xToXbar hVH x) = g := by
    rw [hx]
    exact Φ.symm_apply_apply g
  refine ⟨x, ?_, ?_⟩
  · have hmemV : ψG a ∈ V := hNat.point a T ha hT hTV
    have hmemVa : ψG (l • a) ∈ V := bigB_psi_smul_mem hVH hNat ha hT hTV l
    have hconj : ψG (l • a) = (x : G) * ψG a * (x : G)⁻¹ := by
      have key := hNat.equiv x a
      rw [hxΦ, hg] at key
      exact key
    have hne : ψG (l • a) ≠ 1 := by
      intro h1
      have h2 : l • a = 0 := bigRW_psi_injective (by rw [h1, bigRW_psi_zero])
      exact (smul_ne_zero hl ha) h2
    have hnebot : V ⊓ conjSubgroup (x : G) V ≠ ⊥ := by
      intro hbot
      have hmem : ψG (l • a) ∈ V ⊓ conjSubgroup (x : G) V := by
        refine Subgroup.mem_inf.mpr ⟨hmemVa, ?_⟩
        rw [hconj]
        exact mem_conjSubgroup.mpr (by
          rw [show (x : G)⁻¹ * ((x : G) * ψG a * (x : G)⁻¹) * x = ψG a by group]
          exact hmemV)
      rw [hbot] at hmem
      exact hne (Subgroup.mem_bot.mp hmem)
    have hconjV : conjSubgroup (x : G) V = V := conjSubgroup_eq_of_isTI hc.ti hnebot
    rw [← hc.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hconjV
  · rw [hxΦ, hg]

theorem BigEndHyp.exists_param [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {v : G} (hv : v ∈ V) :
    ∃ c : GaloisField 2 f,
      SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat ⟨v, h.setup.mc.toMinCex.V_le_P hv⟩) =
        CaseM.spTrans a c := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv
  have hmemT : h.bigPAct hNat ⟨v, hc.V_le_P hv⟩ ∈ T := by
    rw [h.bigPAct_eq_of_mem_xOf hNat hvX]
    refine Subgroup.mem_map_equiv.mp ?_
    rw [hTV]
    exact Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hc.V_le_H) ⟨v, hvX⟩, hv, rfl⟩)
  exact (hT.1 _).mp hmemT

theorem BigEndHyp.mem_inf_of_bigPAct_eq_one [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {v : G} (hv : v ∈ V)
    (h1 : h.bigPAct hNat ⟨v, h.setup.mc.toMinCex.V_le_P hv⟩ = 1) :
    v ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv
  have hcomm : ∀ w ∈ wOf V H, v * w = w * v := by
    intro w hw
    obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) hw
    have hs := h.bigPAct_spec hNat ⟨v, hc.V_le_P hv⟩ u
    rw [h1, map_one, Matrix.one_mulVec] at hs
    calc v * ψG u = (v * ψG u * v⁻¹) * v := by group
      _ = ψG u * v := by rw [← hs]
  exact Subgroup.mem_inf.mpr ⟨hv, h.mem_wOf_of_commute hZ hvX hcomm⟩

private theorem gammaQ_addSubgroup [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H) :
    ∃ S : AddSubgroup (GaloisField 2 f),
      (∀ m, m ∈ S ↔ ψG (m • a) ∈ ⁅V ⊓ wOf V H, Q⁆) ∧
      (∀ l : GaloisField 2 f, l ≠ 0 → ∀ m ∈ S, l * m ∈ S) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  let D : Subgroup G := ⁅V ⊓ wOf V H, Q⁆
  let S : AddSubgroup (GaloisField 2 f) :=
    { carrier := {m | ψG (m • a) ∈ D}
      add_mem' := fun {m m'} hm hm' => by
        change ψG (m • a) ∈ D at hm
        change ψG (m' • a) ∈ D at hm'
        show ψG ((m + m') • a) ∈ D
        rw [add_smul, ← bigRW_psi_mul]
        exact D.mul_mem hm hm'
      zero_mem' := by
        show ψG ((0 : GaloisField 2 f) • a) ∈ D
        rw [zero_smul, bigRW_psi_zero]
        exact D.one_mem
      neg_mem' := fun {m} hm => by
        change ψG (m • a) ∈ D at hm
        show ψG ((-m) • a) ∈ D
        simpa only [neg_smul, CharTwo.neg_eq] using hm }
  have hmemS : ∀ m, m ∈ S ↔ ψG (m • a) ∈ D := fun m => Iff.rfl
  refine ⟨S, ?_, ?_⟩
  · exact hmemS
  · intro l hl m hm
    obtain ⟨y, hyM, hya⟩ := h.exists_torus hNat ha hT hTV hl
    have hyA : conjSubgroup (y : G) (V ⊓ wOf V H) = V ⊓ wOf V H :=
      conjSubgroup_eq_self_iff.mpr (BigEndHyp.M_le_normalizer_inf_wOf h hZ hyM)
    have hyQ : conjSubgroup (y : G) Q = Q :=
      conjSubgroup_eq_self_iff.mpr (hc.M_le_normalizer_Q hyM)
    have hyD : conjSubgroup (y : G) D = D := by
      change (⁅V ⊓ wOf V H, Q⁆).map (MulAut.conj (y : G)).toMonoidHom =
        ⁅V ⊓ wOf V H, Q⁆
      rw [Subgroup.map_commutator,
        show (V ⊓ wOf V H).map (MulAut.conj (y : G)).toMonoidHom = V ⊓ wOf V H from hyA,
        show Q.map (MulAut.conj (y : G)).toMonoidHom = Q from hyQ]
    have hyD' : (y : G) * ψG (m • a) * (y : G)⁻¹ ∈ D := by
      rw [← hyD]
      exact Subgroup.mem_map_of_mem _ ((hmemS m).mp hm)
    have hact : (y : G) * ψG (m • a) * (y : G)⁻¹ = ψG ((l * m) • a) := by
      have key := hNat.equiv y (m • a)
      rw [Matrix.mulVec_smul, hya, smul_smul, mul_comm m l] at key
      exact key.symm
    exact (hmemS _).mpr (hact ▸ hyD')

private theorem gammaQ_S_ne_top [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {S : AddSubgroup (GaloisField 2 f)}
    (hmemS : ∀ m, m ∈ S ↔ ψG (m • a) ∈ ⁅V ⊓ wOf V H, Q⁆)
    (hDlt : ⁅V ⊓ wOf V H, Q⁆ < V ⊓ wOf V H) :
    ¬ ∀ m, m ∈ S := by
  intro htop
  have hAleD : V ⊓ wOf V H ≤ ⁅V ⊓ wOf V H, Q⁆ := by
    intro y hy
    obtain ⟨v, hv⟩ := bigB_exists_psi (ψ := ψ) (Subgroup.mem_inf.mp hy).2
    obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V h hf hNat ha hT hTV
      (by rw [hv]; exact (Subgroup.mem_inf.mp hy).1)
    have hlD : ψG (l • a) ∈ ⁅V ⊓ wOf V H, Q⁆ := (hmemS l).mp (htop l)
    rw [← hv, hl]
    exact hlD
  exact (not_le_of_gt hDlt) hAleD

private theorem gammaQ_eq_bot [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hDlt : ⁅V ⊓ wOf V H, Q⁆ < V ⊓ wOf V H) :
    ⁅V ⊓ wOf V H, Q⁆ = ⊥ := by
  obtain ⟨S, hmemS, hS_smul⟩ := gammaQ_addSubgroup h hZ hNat ha hT hTV
  have hStop : ¬ ∀ m, m ∈ S := gammaQ_S_ne_top h hf hNat ha hT hTV hmemS hDlt
  have hSbot : S = ⊥ := by
    rcases CFSG.Algebra.addSubgroup_eq_bot_or_eq_top_of_mul_mem S hS_smul with h | h
    · exact h
    · exact absurd (fun m => h ▸ AddSubgroup.mem_top m) hStop
  rw [eq_bot_iff]
  intro d hd
  have hdA : d ∈ V ⊓ wOf V H := hDlt.le hd
  obtain ⟨v, hv⟩ := bigB_exists_psi (ψ := ψ) (Subgroup.mem_inf.mp hdA).2
  obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V h hf hNat ha hT hTV
    (by rw [hv]; exact (Subgroup.mem_inf.mp hdA).1)
  have hlS : l ∈ S := by
    rw [hl] at hv
    exact (hmemS l).mpr (by rw [hv]; exact hd)
  have hl0 : l = 0 := by
    have : l ∈ (⊥ : AddSubgroup (GaloisField 2 f)) := hSbot ▸ hlS
    simpa using this
  rw [← hv, hl, hl0, zero_smul, bigRW_psi_zero]
  simp

theorem BigEndHyp.commute_of_mem_Q_of_mem_inf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {x u : G} (hx : x ∈ Q) (hu : u ∈ V ⊓ wOf V H) :
    x * u = u * x := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hA : ⁅P, P⁆ = V ⊓ wOf V H :=
    (bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ
      (bigIWStatement_holds G M V Q P H h hZ)).1
  have hAleQ : V ⊓ wOf V H ≤ Q := by
    rw [← hA]
    refine (Subgroup.commutator_le.mpr ?_).trans hc.P_le_Q
    intro p₁ hp₁ p₂ hp₂
    exact P.mul_mem (P.mul_mem (P.mul_mem hp₁ hp₂) (P.inv_mem hp₁)) (P.inv_mem hp₂)
  have hAne : V ⊓ wOf V H ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(V ⊓ wOf V H) = 1 := by rw [hbot]; simp
    rw [h.module] at h1
    have hq := h.q_big
    omega
  have hDlt : ⁅V ⊓ wOf V H, Q⁆ < V ⊓ wOf V H := by
    have hQ2 : IsPGroup 2 ↥Q := hc.hQ ▸ (inSubgroup_pCore_two M).1
    have hQNA : Q ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      hc.Q_le_M.trans (BigEndHyp.M_le_normalizer_inf_wOf h hZ)
    have hQNbot : Q ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro a
      simp
    simpa using CFSG.GroupTheory.commutator_sup_lt_of_isPGroup hAleQ hQ2 hQNA hQNbot
      bot_le (Ne.symm hAne)
  have hDbot : ⁅V ⊓ wOf V H, Q⁆ = ⊥ := gammaQ_eq_bot h hZ hf hNat ha hT hTV hDlt
  exact Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDbot) hu) x hx

private theorem gammaV_conj_D [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {y : G} (hyM : y ∈ M) :
    conjSubgroup y (⁅V, Q⁆ ⊔ (V ⊓ wOf V H)) = ⁅V, Q⁆ ⊔ (V ⊓ wOf V H) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hyV : conjSubgroup y V = V :=
    conjSubgroup_eq_self_iff.mpr (hc.normalizer_eq ▸ hyM)
  have hyQ : conjSubgroup y Q = Q :=
    conjSubgroup_eq_self_iff.mpr (hc.M_le_normalizer_Q hyM)
  have hyA : conjSubgroup y (V ⊓ wOf V H) = V ⊓ wOf V H :=
    conjSubgroup_eq_self_iff.mpr (BigEndHyp.M_le_normalizer_inf_wOf h hZ hyM)
  change (⁅V, Q⁆ ⊔ (V ⊓ wOf V H)).map (MulAut.conj y).toMonoidHom =
    ⁅V, Q⁆ ⊔ (V ⊓ wOf V H)
  rw [Subgroup.map_sup, Subgroup.map_commutator,
    show V.map (MulAut.conj y).toMonoidHom = V from hyV,
    show Q.map (MulAut.conj y).toMonoidHom = Q from hyQ,
    show (V ⊓ wOf V H).map (MulAut.conj y).toMonoidHom = V ⊓ wOf V H from hyA]

private theorem gammaV_sq_mem [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {D : Subgroup G} (hDdef : D = ⁅V, Q⁆ ⊔ (V ⊓ wOf V H))
    {tau : GaloisField 2 f → ↥(StatedSp n (GaloisField 2 f))}
    (htau : ∀ c, SpExtras.mat n (GaloisField 2 f) (tau c) = CaseM.spTrans a c)
    {S : AddSubgroup (GaloisField 2 f)}
    (hmem : ∀ c, c ∈ S ↔ tau c ∈ (D.subgroupOf P).map (h.bigPAct hNat))
    {l c : GaloisField 2 f} (hl : l ≠ 0) (hc : c ∈ S) : l * l * c ∈ S := by
  have hmc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hDV : ⁅V, Q⁆ ⊔ (V ⊓ wOf V H) ≤ V :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hmc.Q_le_normalizer_V) inf_le_left
  obtain ⟨p, hpD, hpm⟩ := Subgroup.mem_map.mp ((hmem c).mp hc)
  rw [hDdef] at hpD
  have hpV : (p : G) ∈ V := hDV (Subgroup.mem_subgroupOf.mp hpD)
  obtain ⟨y, hyM, hya⟩ := h.exists_torus hNat ha hT hTV hl
  have hyP : (y : G) ∈ Subgroup.normalizer (P : Set G) := hmc.M_le_normalizer_P hyM
  have hqP : (y : G) * (p : G) * (y : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hyP p).mp p.2
  have hqD : (y : G) * (p : G) * (y : G)⁻¹ ∈ D := by
    rw [hDdef, ← gammaV_conj_D h hZ hyM]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hpD)
  have hq : (⟨(y : G) * (p : G) * (y : G)⁻¹, hqP⟩ : ↥P) ∈ D.subgroupOf P :=
    Subgroup.mem_subgroupOf.mpr hqD
  have hmats : SpExtras.mat n (GaloisField 2 f)
      (h.bigPAct hNat ⟨(y : G) * (p : G) * (y : G)⁻¹, hqP⟩) =
      CaseM.spTrans a (l * l * c) := by
    rw [h.bigPAct_conj hNat hyM p, hpm,
      CaseM.mat_conj_of_mat_eq (htau c) (Φ.symm (xToXbar hmc.V_le_H y)), hya,
      CaseM.spTrans_smul]
  have hbig : h.bigPAct hNat ⟨(y : G) * (p : G) * (y : G)⁻¹, hqP⟩ = tau (l * l * c) :=
    SpExtras.mat_injective (by rw [hmats, htau])
  exact (hmem _).mpr (Subgroup.mem_map.mpr ⟨⟨(y : G) * (p : G) * (y : G)⁻¹, hqP⟩, hq, hbig⟩)

private theorem gammaV_addSubgroup [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {D : Subgroup G} (hDdef : D = ⁅V, Q⁆ ⊔ (V ⊓ wOf V H)) :
    ∃ (tau : GaloisField 2 f → ↥(StatedSp n (GaloisField 2 f)))
      (S : AddSubgroup (GaloisField 2 f)),
      (∀ c, SpExtras.mat n (GaloisField 2 f) (tau c) = CaseM.spTrans a c) ∧
      tau 0 = 1 ∧
      (∀ c, c ∈ S ↔ tau c ∈ (D.subgroupOf P).map (h.bigPAct hNat)) ∧
      (∀ l : GaloisField 2 f, l ≠ 0 → ∀ c ∈ S, l * l * c ∈ S) := by
  let tau : GaloisField 2 f → ↥(StatedSp n (GaloisField 2 f)) :=
    fun c => Classical.choose (exists_mat_eq_spTrans a c)
  have htau : ∀ c, SpExtras.mat n (GaloisField 2 f) (tau c) = CaseM.spTrans a c :=
    fun c => Classical.choose_spec (exists_mat_eq_spTrans a c)
  have htau0 : tau 0 = 1 := by
    apply SpExtras.mat_injective
    rw [htau, spTrans_zero, map_one]
  let Msp : Subgroup ↥(StatedSp n (GaloisField 2 f)) := (D.subgroupOf P).map (h.bigPAct hNat)
  let S : AddSubgroup (GaloisField 2 f) :=
    { carrier := {c | tau c ∈ Msp}
      add_mem' := fun {c c'} hc hc' => by
        change tau c ∈ Msp at hc
        change tau c' ∈ Msp at hc'
        show tau (c + c') ∈ Msp
        have h : tau (c + c') = tau c * tau c' := by
          apply SpExtras.mat_injective
          rw [htau, map_mul, htau, htau, spTrans_mul_spTrans]
        rw [h]
        exact Msp.mul_mem hc hc'
      zero_mem' := by
        show tau 0 ∈ Msp
        rw [htau0]
        exact Msp.one_mem
      neg_mem' := fun {c} hc => by
        change tau c ∈ Msp at hc
        show tau (-c) ∈ Msp
        have h : tau (-c) = (tau c)⁻¹ := by
          have h1 : tau c * tau (-c) = 1 := by
            apply SpExtras.mat_injective
            rw [map_mul, htau, htau, spTrans_mul_spTrans, add_neg_cancel, spTrans_zero,
              map_one]
          calc tau (-c) = (tau c)⁻¹ * (tau c * tau (-c)) := by group
            _ = (tau c)⁻¹ * 1 := by rw [h1]
            _ = (tau c)⁻¹ := by rw [mul_one]
        rw [h]
        exact Msp.inv_mem hc }
  have hmem : ∀ c, c ∈ S ↔ tau c ∈ (D.subgroupOf P).map (h.bigPAct hNat) :=
    fun c => Iff.rfl
  exact ⟨tau, S, htau, htau0, hmem,
    fun l hl c hc => gammaV_sq_mem h hZ hNat ha hT hTV hDdef htau hmem hl hc⟩

private theorem gammaV_smul_mem {S : AddSubgroup (GaloisField 2 f)}
    (hS_sq : ∀ l : GaloisField 2 f, l ≠ 0 → ∀ c ∈ S, l * l * c ∈ S) :
    ∀ l : GaloisField 2 f, l ≠ 0 → ∀ c ∈ S, l * c ∈ S := by
  intro l hl c hc
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two
    (ringChar.eq (GaloisField 2 f) 2) l
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hl hs
  rw [hs]
  exact hS_sq s hs0 c hc

private theorem gammaV_S_ne_top [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {D : Subgroup G} (hDdef : D = ⁅V, Q⁆ ⊔ (V ⊓ wOf V H)) (hDlt : D < V)
    {tau : GaloisField 2 f → ↥(StatedSp n (GaloisField 2 f))}
    (htau : ∀ c, SpExtras.mat n (GaloisField 2 f) (tau c) = CaseM.spTrans a c)
    {S : AddSubgroup (GaloisField 2 f)}
    (hmem : ∀ c, c ∈ S ↔ tau c ∈ (D.subgroupOf P).map (h.bigPAct hNat)) :
    ¬ ∀ c, c ∈ S := by
  have hmc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hDV : D ≤ V :=
    hDdef ▸ sup_le
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hmc.Q_le_normalizer_V) inf_le_left
  intro htop
  have hVD : V ≤ D := by
    intro w hw
    obtain ⟨c, hpc⟩ := h.exists_param hNat hT hTV hw
    obtain ⟨p, hpD, hpm⟩ := Subgroup.mem_map.mp ((hmem c).mp (htop c))
    have hpD' : (p : G) ∈ D := Subgroup.mem_subgroupOf.mp hpD
    have hpV : (p : G) ∈ V := hDV hpD'
    have hpv : h.bigPAct hNat p = h.bigPAct hNat ⟨w, hmc.V_le_P hw⟩ := by
      apply SpExtras.mat_injective
      rw [hpm, htau, hpc]
    have huV : (p : G)⁻¹ * w ∈ V := V.mul_mem (V.inv_mem hpV) hw
    have huP : (p : G)⁻¹ * w ∈ P := hmc.V_le_P huV
    have hu1 : h.bigPAct hNat ⟨(p : G)⁻¹ * w, huP⟩ = 1 := by
      have hmul : (⟨(p : G)⁻¹ * w, huP⟩ : ↥P) = p⁻¹ * ⟨w, hmc.V_le_P hw⟩ :=
        Subtype.ext rfl
      rw [hmul, map_mul, map_inv, hpv, inv_mul_cancel]
    have huA : (p : G)⁻¹ * w ∈ V ⊓ wOf V H :=
      h.mem_inf_of_bigPAct_eq_one hZ hNat huV hu1
    have hw_eq : w = (p : G) * ((p : G)⁻¹ * w) := by group
    rw [hw_eq]
    exact D.mul_mem hpD' ((hDdef.symm ▸ le_sup_right : V ⊓ wOf V H ≤ D) huA)
  exact (not_le_of_gt hDlt) hVD

private theorem gammaV_D_le_inf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {D : Subgroup G} (hDdef : D = ⁅V, Q⁆ ⊔ (V ⊓ wOf V H)) (hDlt : D < V) :
    D ≤ V ⊓ wOf V H := by
  have hmc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨tau, S, htau, htau0, hmem, hS_sq⟩ :=
    gammaV_addSubgroup h hZ hNat ha hT hTV hDdef
  have hS_smul := gammaV_smul_mem hS_sq
  have hStop : ¬ ∀ c, c ∈ S :=
    gammaV_S_ne_top h hZ hNat ha hT hTV hDdef hDlt htau hmem
  have hSbot : S = ⊥ := by
    rcases CFSG.Algebra.addSubgroup_eq_bot_or_eq_top_of_mul_mem S hS_smul with h | h
    · exact h
    · exact absurd (fun c => h ▸ AddSubgroup.mem_top c) hStop
  have hDV : D ≤ V :=
    hDdef ▸ sup_le
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hmc.Q_le_normalizer_V) inf_le_left
  intro d hd
  have hdP : d ∈ P := hmc.V_le_P (hDV hd)
  obtain ⟨c, hpc⟩ := h.exists_param hNat hT hTV (hDV hd)
  have hbig : h.bigPAct hNat ⟨d, hdP⟩ = tau c := by
    apply SpExtras.mat_injective
    rw [hpc, htau]
  have hcS : c ∈ S := (hmem c).mpr (Subgroup.mem_map.mpr
    ⟨⟨d, hdP⟩, Subgroup.mem_subgroupOf.mpr hd, hbig⟩)
  have hc0 : c = 0 := by
    have : c ∈ (⊥ : AddSubgroup (GaloisField 2 f)) := hSbot ▸ hcS
    simpa using this
  have h1 : h.bigPAct hNat ⟨d, hdP⟩ = 1 := by rw [hbig, hc0, htau0]
  exact h.mem_inf_of_bigPAct_eq_one hZ hNat (hDV hd) h1

theorem BigEndHyp.commutator_mem_inf_of_mem_V_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {v x : G} (hv : v ∈ V) (hx : x ∈ Q) :
    ⁅v, x⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hAV : (V ⊓ wOf V H) ≠ V := by
    intro heq
    have h1 : Nat.card ↥(V ⊓ wOf V H) = Nat.card ↥V := by rw [heq]
    rw [h.module, h.card_V, pow_two] at h1
    nlinarith [h.q_big]
  let D : Subgroup G := ⁅V, Q⁆ ⊔ (V ⊓ wOf V H)
  have hDlt : D < V := by
    have hQ2 : IsPGroup 2 ↥Q := hc.hQ ▸ (inSubgroup_pCore_two M).1
    have hQNV : Q ≤ Subgroup.normalizer (V : Set G) := hc.Q_le_normalizer_V
    have hQNA : Q ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      hc.Q_le_M.trans (BigEndHyp.M_le_normalizer_inf_wOf h hZ)
    simpa [D] using CFSG.GroupTheory.commutator_sup_lt_of_isPGroup hc.V_le_Q hQ2 hQNV
      hQNA inf_le_left hAV
  have hDA : D ≤ V ⊓ wOf V H := gammaV_D_le_inf h hZ hNat ha hT hTV rfl hDlt
  have hVQ : ⁅V, Q⁆ ≤ V ⊓ wOf V H := (le_sup_left : ⁅V, Q⁆ ≤ D).trans hDA
  exact hVQ (Subgroup.commutator_mem_commutator hv hx)

theorem BigEndHyp.commutator_mem_P_of_mem_wOf_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {w x : G} (hw : w ∈ wOf V H) (hx : x ∈ Q) :
    ⁅w, x⁆ ∈ P := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVQ : ⁅V, Q⁆ ≤ V ⊓ wOf V H := by
    refine Subgroup.commutator_le.mpr ?_
    intro v hv q hq
    exact h.commutator_mem_inf_of_mem_V_of_mem_Q hZ hv hq
  have hQV : ⁅Q, V⁆ ≤ wOf V H := by
    rw [Subgroup.commutator_comm]
    exact hVQ.trans inf_le_right
  have hWab : ⁅wOf V H, wOf V H⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr hc.wOf_isElemAbelian.1
  have h1 : ⁅⁅Q, V⁆, wOf V H⁆ = ⊥ := by
    have hmono : ⁅⁅Q, V⁆, wOf V H⁆ ≤ ⁅wOf V H, wOf V H⁆ :=
      Subgroup.commutator_mono hQV le_rfl
    exact le_bot_iff.mp (hmono.trans (le_of_eq hWab))
  have hVW : ⁅V, wOf V H⁆ ≤ V ⊓ wOf V H := by
    refine Subgroup.commutator_le.mpr ?_
    intro v hv w hw'
    have hmem := hc.commutator_mem_conj_inf_wOf (y := (1 : G)) H.one_mem
      (v := v) (by rwa [conjSubgroup_one]) (w := w) hw'
    rwa [conjSubgroup_one] at hmem
  have hAQ : ⁅V ⊓ wOf V H, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact h.commute_of_mem_Q_of_mem_inf hZ hq ha
  have h2 : ⁅⁅V, wOf V H⁆, Q⁆ = ⊥ := by
    have hmono : ⁅⁅V, wOf V H⁆, Q⁆ ≤ ⁅V ⊓ wOf V H, Q⁆ :=
      Subgroup.commutator_mono hVW le_rfl
    rw [hAQ] at hmono
    exact le_bot_iff.mp hmono
  have h3 : ⁅⁅wOf V H, Q⁆, V⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hcen : ⁅wOf V H, Q⁆ ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hWQ : ⁅wOf V H, Q⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr ?_
    intro u hu q hq
    have huM : u ∈ M := wOf_le_M_of_minCex hc hu
    have huN : u ∈ Subgroup.normalizer (Q : Set G) := hc.M_le_normalizer_Q huM
    have h1' : u * q * u⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp huN q).mp hq
    exact Q.mul_mem h1' (Q.inv_mem hq)
  have hle : ⁅wOf V H, Q⁆ ≤ P := by
    rw [hc.hP]
    exact le_inf hWQ hcen
  exact hle (Subgroup.commutator_mem_commutator hw hx)

end CFSG.RankThree.GF2n.Tim79a
