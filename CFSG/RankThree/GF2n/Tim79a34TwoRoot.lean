module

public import CFSG.RankThree.GF2n.Tim79a34TwoCfg
public import CFSG.Sporadic.ThSchreier.Row

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoRoot

section Part1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
  CFSG.RankThree.GF2n.Tim79a.Gamma
  CFSG.RankThree.GF2n.Tim79a.TwoModel CFSG.RankThree.GF2n.Tim79a.TwoSpace
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
  {Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin 2 ⊕ Fin 2 → GaloisField 2 1} {T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem mem_Q_of_act_id (cfg : GCfg M V Q P H Φ ψ a T) {F : Subgroup G} {t0 t1 : G}
    (K : Coord P V M F t0 t1) (m : M) (h : ∀ x, K.act m x = x) : (m : G) ∈ Q := by
  refine (tim79a34_mem_Q_iff cfg.hyp cfg.centre (m : G)).mpr ⟨m.2, fun p hp => ?_⟩
  have hmp : (m : G) * p * (m : G)⁻¹ ∈ P := P_norm_of_cfg cfg m m.2 p hp
  have hc : ⁅(m : G), p⁆ ∈ P := by
    have e : ⁅(m : G), p⁆ = ((m : G) * p * (m : G)⁻¹) * p⁻¹ := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact P.mul_mem hmp (P.inv_mem hp)
  have h1 := K.θ_comm m ⟨p, hp⟩ hmp hc
  rw [h] at h1
  have h2 : K.θ ⟨⁅(m : G), p⁆, hc⟩ = 0 := by
    rw [h1]
    funext i
    have key : ∀ c : ZMod 2, c + c = 0 := by decide
    exact key _
  exact (K.coords.ker _).mp h2

theorem psi_not_mem_V (cfg : GCfg M V Q P H Φ ψ a T) {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1}
    (hy0 : y ≠ 0) (hya : y ≠ a) : ψG y ∉ V := by
  intro h
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  have hmem : ψG y ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨h, psi_mem_W y⟩
  rcases l12_two_elt hA2 haK haG1 _ hmem with h1 | h1
  · exact hy0 (psi_injective (h1.trans psi_zero.symm))
  · exact hya (psi_injective h1)

theorem comm_sq_eq_one (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {F : Subgroup G} {t0 t1 : G}
    (K : Coord P V M F t0 t1) {v₀ : G} (hv₀ : v₀ ∈ V)
    (LF : TwoGame.LocalFacts V M (ψG a) v₀) {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1}
    (hy0 : y ≠ 0) (hya : y ≠ a) {x s : G} (hxa : x * ψG a * x⁻¹ = ψG y)
    (hs : s = x * v₀ * x⁻¹) (hsM : s ∈ M) (hss : s * s = 1) (huP : ψG y ∈ P)
    (hfix : K.act ⟨s, hsM⟩ (K.θ ⟨ψG y, huP⟩) = K.θ ⟨ψG y, huP⟩)
    (p : P) : ⁅s, (p : G)⁆ * ⁅s, (p : G)⁆ = 1 := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsp : s * p * s⁻¹ ∈ P := P_norm_of_cfg cfg s hsM p p.2
  have hcP : ⁅s, (p : G)⁆ ∈ P := by
    have e : ⁅s, (p : G)⁆ = (s * p * s⁻¹) * (p : G)⁻¹ := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact P.mul_mem hsp (P.inv_mem p.2)
  set c : G := ⁅s, (p : G)⁆ with hcdef
  have hsc : s * c * s⁻¹ = c⁻¹ := by
    have e1 : c = s * p * s * (p : G)⁻¹ := by
      rw [hcdef, commutatorElement_def, hsi]
    have e2 : c⁻¹ = (p : G) * s * (p : G)⁻¹ * s := by
      rw [e1]
      simp only [mul_inv_rev, inv_inv, hsi, mul_assoc]
    rw [e2, hsi]
    calc s * c * s = s * (s * p * s * (p : G)⁻¹) * s := by rw [e1]
      _ = (s * s) * p * s * (p : G)⁻¹ * s := by simp only [mul_assoc]
      _ = (p : G) * s * (p : G)⁻¹ * s := by rw [hss, one_mul]
  have hcu : c * ψG y = ψG y * c := by
    have hθc : K.θ ⟨c, hcP⟩ = K.act ⟨s, hsM⟩ (K.θ p) + K.θ p := K.θ_comm ⟨s, hsM⟩ p hsp hcP
    have hbf : bf (K.θ ⟨c, hcP⟩) (K.θ ⟨ψG y, huP⟩) = 0 := by
      rw [hθc, bf_add_left]
      have h1 := isIsom4_bf (K.act_isom ⟨s, hsM⟩) (K.θ p) (K.θ ⟨ψG y, huP⟩)
      rw [hfix] at h1
      rw [h1]
      have key : ∀ c : ZMod 2, c + c = 0 := by decide
      exact key _
    have h2 := (K.coords.comm ⟨c, hcP⟩ ⟨ψG y, huP⟩).mpr hbf
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2)
  have hN : c ∈ Subgroup.normalizer ((conjSubgroup x V : Subgroup G) : Set G) :=
    LF.normalizes x c (by rw [hxa]; exact hcu)
  have hsV : s ∈ conjSubgroup x V := by
    rw [mem_conjSubgroup, hs]
    have : x⁻¹ * (x * v₀ * x⁻¹) * x = v₀ := by group
    rw [this]
    exact hv₀
  have hcomm : ⁅s, c⁆ ∈ conjSubgroup x V := by
    have e : ⁅s, c⁆ = s * (c * s⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    refine (conjSubgroup x V).mul_mem hsV ?_
    have h1 : c * s⁻¹ * c⁻¹ ∈ conjSubgroup x V :=
      (Subgroup.mem_normalizer_iff.mp hN s⁻¹).mp ((conjSubgroup x V).inv_mem hsV)
    exact h1
  have hcc : ⁅s, c⁆ = (c * c)⁻¹ := by
    rw [commutatorElement_def, hsc]
    simp only [mul_inv_rev]
  have hsq : c * c ∈ V ⊓ wOf V H := mul_self_mem_VW L.h11b cfg hcP
  rcases l12_two_elt hA2 haK haG1 _ hsq with h1 | h1
  · exact h1
  · exfalso
    have hbot : V ⊓ conjSubgroup x V = ⊥ := by
      have hne : conjSubgroup 1 V ≠ conjSubgroup x V := by
        rw [conjSubgroup_one]
        exact (LF.conj_eq x (by rw [hxa]; exact psi_not_mem_V cfg hy0 hya)).symm
      have := LF.inf_eq_bot 1 x hne
      rwa [conjSubgroup_one] at this
    have hV1 : ψG a ∈ conjSubgroup x V := by
      have h2 : ⁅s, c⁆ = ψG a := by
        rw [hcc, h1]
        have hai : (ψG a)⁻¹ = ψG a := inv_eq_of_mul_eq_one_right (elemAbelian_mul_self
          hc.elemAb (Subgroup.mem_inf.mp haK).1)
        exact hai
      rw [← h2]
      exact hcomm
    have : ψG a ∈ V ⊓ conjSubgroup x V := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp haK).1, hV1⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact haG1 this

theorem root_pair (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {t0 t1 : G}
    (K : Coord P V M (P ⊓ wOf V H) t0 t1) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H)
    (LF : TwoGame.LocalFacts V M (ψG a) v₀) (bM : M) {β : Fin 2 ⊕ Fin 2 → GaloisField 2 1}
    (hbβ : (bM : G) = ψG β) (hb : ⇑(K.act bM) = bS)
    {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1} (hy : spForm a y = 0) (hy0 : y ≠ 0) (hya : y ≠ a)
    {x : G} (hxX : x ∈ xOf V H) (hxa : x * ψG a * x⁻¹ = ψG y)
    (hact : ∀ w, (x * v₀ * x⁻¹) * ψG w * (x * v₀ * x⁻¹)⁻¹ = ψG (w + spForm y w • y)) :
    ∃ sM : M, (sM : G) = x * v₀ * x⁻¹ ∧ (sM : G) ∉ Q ∧ (sM : G) ∈ xOf V H ∧
      (∀ hu : ψG y ∈ P, K.θ ⟨ψG y, hu⟩ = e0 → ⇑(K.act sM) = tS0) ∧
      (∀ hu : ψG y ∈ P, K.θ ⟨ψG y, hu⟩ = e1 → ⇑(K.act sM) = tS1) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hZ := cfg.centre
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV : ψG a ∈ V := (Subgroup.mem_inf.mp haK).1
  have hVsq : ∀ z ∈ V, z * z = 1 := fun z hz => elemAbelian_mul_self hc.elemAb hz
  have hWab : ∀ z ∈ wOf V H, ∀ w ∈ wOf V H, z * w = w * z := fun z hz w hw =>
    elemAbelian_mul_comm hc.wOf_isElemAbelian hz hw
  have h12 := L.h12 G M V Q P H cfg.hyp hZ Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  have hv₀X : v₀ ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv₀
  have hsX : x * v₀ * x⁻¹ ∈ xOf V H :=
    (xOf V H).mul_mem ((xOf V H).mul_mem hxX hv₀X) ((xOf V H).inv_mem hxX)
  have hsa : (x * v₀ * x⁻¹) * ψG a * (x * v₀ * x⁻¹)⁻¹ = ψG a := by
    rw [hact a, spForm_eq_zero_comm hy, zero_smul, add_zero]
  have hsM : x * v₀ * x⁻¹ ∈ M := hc.mem_M_of_commute haV haG1 (mul_inv_eq_iff_eq_mul.mp hsa)
  have hss : (x * v₀ * x⁻¹) * (x * v₀ * x⁻¹) = 1 := by
    calc (x * v₀ * x⁻¹) * (x * v₀ * x⁻¹) = x * (v₀ * v₀) * x⁻¹ := by group
      _ = 1 := by rw [hVsq v₀ hv₀]; group
  have huP : ψG y ∈ P := (psi_mem_P_iff L.h11a cfg y).mpr hy
  have hsu : (x * v₀ * x⁻¹) * ψG y * (x * v₀ * x⁻¹)⁻¹ = ψG y := by
    rw [hact y, spForm_self, zero_smul, add_zero]
  have hsQ : x * v₀ * x⁻¹ ∉ Q := by
    intro hsQ
    have hsP : x * v₀ * x⁻¹ ∈ P := by
      rw [← h12.2.2.1]
      exact Subgroup.mem_inf.mpr ⟨hsQ, hsX⟩
    exact trans_not_mem_P L cfg hy0 hya hsP hact
  set s : G := x * v₀ * x⁻¹ with hs
  let sM : M := ⟨s, hsM⟩
  have hfix : K.act sM (K.θ ⟨ψG y, huP⟩) = K.θ ⟨ψG y, huP⟩ := by
    rw [← K.act_spec sM ⟨ψG y, huP⟩ (P_norm_of_cfg cfg s hsM _ huP)]
    exact congrArg K.θ (Subtype.ext hsu)
  have hinv : ∀ z, K.act sM (K.act sM z) = z := by
    have h1 : K.act (sM * sM) = 1 := by
      rw [show sM * sM = 1 from Subtype.ext hss, map_one]
    intro z
    have h2 := congrArg (fun g : Equiv.Perm Vec4 => g z) h1
    simpa [map_mul] using h2
  have hne : ∃ z, K.act sM z ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hsQ (mem_Q_of_act_id cfg K sM hcon)
  have hts : ∀ z, qf (K.act sM z + z) = 0 := by
    intro z
    obtain ⟨p, rfl⟩ := K.coords.surj z
    have hsp : s * p * s⁻¹ ∈ P := P_norm_of_cfg cfg s hsM p p.2
    have hcP : ⁅s, (p : G)⁆ ∈ P := by
      have e : ⁅s, (p : G)⁆ = (s * p * s⁻¹) * (p : G)⁻¹ := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e]
      exact P.mul_mem hsp (P.inv_mem p.2)
    rw [← K.θ_comm sM p hsp hcP]
    exact (K.coords.sq ⟨_, hcP⟩).mp (comm_sq_eq_one L cfg K hv₀ LF hy0 hya hxa hs hsM hss huP
      hfix p)
  have hbW : (bM : G) ∈ wOf V H := by rw [hbβ]; exact psi_mem_W β
  have hneb : ∃ z, K.act sM z ≠ bS z := by
    by_contra hcon
    push Not at hcon
    have heq : K.act sM = K.act bM := by
      ext z
      rw [hcon z, ← hb]
    have hid : ∀ z, K.act (bM⁻¹ * sM) z = z := by
      intro z
      rw [map_mul, map_inv, heq]
      simp
    have hkQ : ((bM⁻¹ * sM : M) : G) ∈ Q := mem_Q_of_act_id cfg K _ hid
    have hkX : ((bM⁻¹ * sM : M) : G) ∈ xOf V H := by
      have hbX : (bM : G) ∈ xOf V H := wOf_le_xOf V H hbW
      have : ((bM⁻¹ * sM : M) : G) = (bM : G)⁻¹ * s := rfl
      rw [this]
      exact (xOf V H).mul_mem ((xOf V H).inv_mem hbX) hsX
    have hkP : ((bM⁻¹ * sM : M) : G) ∈ P := by
      rw [← h12.2.2.1]
      exact Subgroup.mem_inf.mpr ⟨hkQ, hkX⟩
    refine trans_not_mem_P L cfg hy0 hya hkP (fun w => ?_)
    have e1 : ((bM⁻¹ * sM : M) : G) * ψG w * ((bM⁻¹ * sM : M) : G)⁻¹ =
        (bM : G)⁻¹ * (s * ψG w * s⁻¹) * (bM : G) := by
      have : ((bM⁻¹ * sM : M) : G) = (bM : G)⁻¹ * s := rfl
      rw [this]
      group
    rw [e1, hact w]
    have hz : ψG (w + spForm y w • y) ∈ wOf V H := psi_mem_W _
    have h3 := hWab _ hbW _ hz
    calc (bM : G)⁻¹ * ψG (w + spForm y w • y) * (bM : G)
        = (bM : G)⁻¹ * (ψG (w + spForm y w • y) * (bM : G)) := by rw [mul_assoc]
      _ = (bM : G)⁻¹ * ((bM : G) * ψG (w + spForm y w • y)) := by rw [h3]
      _ = ψG (w + spForm y w • y) := inv_mul_cancel_left _ _
  have hstab : Stab4 (K.act sM) := fun z hz => by
    obtain ⟨p, hpF, rfl⟩ := K.F_of z hz
    have hpn : s * p * s⁻¹ ∈ P := P_norm_of_cfg cfg s hsM p p.2
    rw [← K.act_spec sM p hpn]
    refine K.F_to _ (Subgroup.mem_inf.mpr ⟨hpn, ?_⟩)
    exact (Subgroup.mem_normalizer_iff.mp
      (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hsX)) _).mp (Subgroup.mem_inf.mp hpF).2
  refine ⟨sM, rfl, hsQ, hsX, fun hu hθu => ?_, fun hu hθu => ?_⟩
  · refine tS0_unique (K.act_isom sM) hstab ?_ hinv hne hts hneb
    rw [← hθu]
    exact hfix
  · refine tS1_unique (K.act_isom sM) hstab ?_ hinv hne hts hneb
    rw [← hθu]
    exact hfix

end Part1

section Part2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
  CFSG.RankThree.GF2n.Tim79a.Gamma
  CFSG.RankThree.GF2n.Tim79a.TwoModel CFSG.RankThree.GF2n.Tim79a.TwoSpace
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
  {Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin 2 ⊕ Fin 2 → GaloisField 2 1} {T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem act_b (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {t0 t1 : G}
    (K : Coord P V M (P ⊓ wOf V H) t0 t1) (bM : M) {β : Fin 2 ⊕ Fin 2 → GaloisField 2 1}
    (hβ : spForm a β = 1) (hbβ : (bM : G) = ψG β) : ⇑(K.act bM) = bS := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have h12 := L.h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  have hbW : (bM : G) ∈ wOf V H := by rw [hbβ]; exact psi_mem_W β
  have hWab : ∀ z ∈ wOf V H, ∀ w ∈ wOf V H, z * w = w * z := fun z hz w hw =>
    elemAbelian_mul_comm hc.wOf_isElemAbelian hz hw
  refine siegel_unique (K.act_isom bM) ?_ ?_ ?_
  · intro z hz
    obtain ⟨p, hpF, rfl⟩ := K.F_of z hz
    have hpn : (bM : G) * p * (bM : G)⁻¹ ∈ P := P_norm_of_cfg cfg _ bM.2 p p.2
    rw [← K.act_spec bM p hpn]
    refine congrArg K.θ (Subtype.ext ?_)
    have := hWab _ hbW _ (Subgroup.mem_inf.mp hpF).2
    exact mul_inv_eq_iff_eq_mul.mpr this
  · intro z
    obtain ⟨p, rfl⟩ := K.coords.surj z
    have hpn : (bM : G) * p * (bM : G)⁻¹ ∈ P := P_norm_of_cfg cfg _ bM.2 p p.2
    have hcF : ⁅(bM : G), (p : G)⁆ ∈ P ⊓ wOf V H := by
      have h1 := comm_psi_mem_PW L.h11a cfg hβ p.2
      have h2 := (P ⊓ wOf V H).inv_mem h1
      rw [commutatorElement_inv] at h2
      rwa [hbβ]
    have hcP : ⁅(bM : G), (p : G)⁆ ∈ P := (Subgroup.mem_inf.mp hcF).1
    rw [← K.θ_comm bM p hpn hcP]
    exact K.F_to _ hcF
  · by_contra hcon
    push Not at hcon
    have hbQ : (bM : G) ∈ Q := mem_Q_of_act_id cfg K bM (fun z => by
      by_contra hne
      exact absurd (hcon z) hne)
    have hbP : (bM : G) ∈ P ⊓ wOf V H := by
      rw [← h12.2.2.2.1]
      exact Subgroup.mem_inf.mpr ⟨hbW, hbQ⟩
    have := (psi_mem_P_iff L.h11a cfg β).mp (by rw [← hbβ]; exact (Subgroup.mem_inf.mp hbP).1)
    rw [hβ] at this
    exact one_ne_zero this

theorem exists_not_stab (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {t0 t1 : G}
    (K : Coord P V M (P ⊓ wOf V H) t0 t1) (bM s0 s1 : M) (hb : ⇑(K.act bM) = bS)
    (h0 : ⇑(K.act s0) = tS0) (h1 : ⇑(K.act s1) = tS1) (hbX : (bM : G) ∈ xOf V H)
    (hs0 : (s0 : G) ∈ xOf V H) (hs1 : (s1 : G) ∈ xOf V H) : ∃ g : M, ¬ Stab4 (K.act g) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have h12 := L.h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  by_contra hcon
  push Not at hcon
  set Y : Set (Vec4 → Vec4) := {f | ∃ m : M, (m : G) ∈ xOf V H ∧ ⇑(K.act m) = f} with hY
  have hid : id ∈ Y := ⟨1, (xOf V H).one_mem, by ext z; simp⟩
  have hcomp : ∀ f ∈ Y, ∀ g ∈ Y, f ∘ g ∈ Y := by
    rintro f ⟨m, hm, rfl⟩ g ⟨m', hm', rfl⟩
    refine ⟨m * m', (xOf V H).mul_mem hm hm', ?_⟩
    ext z
    simp [map_mul]
  have hY0 : tS0 ∈ Y := ⟨s0, hs0, h0⟩
  have hY1 : tS1 ∈ Y := ⟨s1, hs1, h1⟩
  have hYb : bS ∈ Y := ⟨bM, hbX, hb⟩
  apply h12.2.2.2.2
  intro g hg
  obtain ⟨m, hmX, hmg⟩ := stab_mem hid hcomp hY0 hY1 hYb (K.act_isom ⟨g, hg⟩) (hcon ⟨g, hg⟩)
  have heq : K.act m = K.act ⟨g, hg⟩ := Equiv.ext fun z => congrFun hmg z
  have hid' : ∀ z, K.act (m⁻¹ * ⟨g, hg⟩) z = z := by
    intro z
    rw [map_mul, map_inv, heq]
    simp
  have hkQ : ((m⁻¹ * ⟨g, hg⟩ : M) : G) ∈ Q := mem_Q_of_act_id cfg K _ hid'
  have hgm : g = (m : G) * ((m⁻¹ * ⟨g, hg⟩ : M) : G) := by
    show g = (m : G) * ((m : G)⁻¹ * g)
    group
  rw [hgm]
  exact Subgroup.mul_mem _ (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hmX))
    (Q_le_normalizer_W cfg hkQ)

theorem exists_rho_act (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {t0 t1 : G}
    (K : Coord P V M (P ⊓ wOf V H) t0 t1) (bM s0 s1 : M) (hb : ⇑(K.act bM) = bS)
    (h0 : ⇑(K.act s0) = tS0) (h1 : ⇑(K.act s1) = tS1)
    (hg : ∃ g : M, ¬ Stab4 (K.act g)) : ∃ m : M, ⇑(K.act m) = rho0 := by
  set Y : Set (Vec4 → Vec4) := {f | ∃ m : M, ⇑(K.act m) = f} with hY
  have hid : id ∈ Y := ⟨1, by ext z; simp⟩
  have hcomp : ∀ f ∈ Y, ∀ g ∈ Y, f ∘ g ∈ Y := by
    rintro f ⟨m, rfl⟩ g ⟨m', rfl⟩
    refine ⟨m * m', ?_⟩
    ext z
    simp [map_mul]
  obtain ⟨g, hgs⟩ := hg
  have := rho0_mem hid hcomp ⟨s0, h0⟩ ⟨s1, h1⟩ ⟨bM, hb⟩ ⟨⇑(K.act g), ⟨g, rfl⟩, K.act_isom g, hgs⟩
  exact this

end Part2

end CFSG.RankThree.GF2n.Tim79a.TwoRoot
