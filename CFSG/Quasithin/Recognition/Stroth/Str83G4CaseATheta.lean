module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseADefs2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABaseXR
public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Vertex
import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4
import CFSG.Quasithin.Recognition.Stroth.Str83G4C2
import CFSG.Quasithin.Background.HZ82Base
import CFSG.Quasithin.Background.F918Z8Ox3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

theorem _root_.CFSG.Quasithin.centralizerMod_map_of_injective {A B : Type*} [Group A] [Group B]
    {f : A →* B} (hf : Function.Injective f) (Z X U : Subgroup A) :
    (centralizerMod Z X U).map f = centralizerMod (Z.map f) (X.map f) (U.map f) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxX, hxN, hxc⟩ := mem_centralizerMod.mp hx
    refine mem_centralizerMod.mpr ⟨Subgroup.mem_map_of_mem f hxX, ?_, ?_⟩
    · exact Subgroup.le_normalizer_map f (Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩)
    · intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
      simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f (hxc u₀ hu₀)
  · rintro y hy
    obtain ⟨hyX, hyN, hyc⟩ := mem_centralizerMod.mp hy
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hyX
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    refine mem_centralizerMod.mpr ⟨hxX, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 : f x * f z * (f x)⁻¹ ∈ Z.map f :=
          (hyN (f z)).mp (Subgroup.mem_map_of_mem f hz)
        have h2 : f (x * z * x⁻¹) ∈ Z.map f := by
          simpa only [map_mul, map_inv] using h1
        exact (Subgroup.mem_map_iff_mem hf).mp h2
      · intro hz
        have h1 : f x * f z * (f x)⁻¹ ∈ Z.map f := by
          simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f hz
        exact (Subgroup.mem_map_iff_mem hf).mp ((hyN (f z)).mpr h1)
    · intro u hu
      have h1 : f x * f u * (f x)⁻¹ * (f u)⁻¹ ∈ Z.map f :=
        hyc (f u) (Subgroup.mem_map_of_mem f hu)
      have h2 : f (x * u * x⁻¹ * u⁻¹) ∈ Z.map f := by
        simpa only [map_mul, map_inv] using h1
      exact (Subgroup.mem_map_iff_mem hf).mp h2

section Theta

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseATheta_injOn_stab (L1 L2 S : Subgroup G) (v : f112Gamma L1 L2 S) :
    Set.InjOn (caseATheta L1 L2 S) (CosetGeom.stab v : Set (f112Amalgam L1 L2 S).Ghat) := by
  cases hv : CosetGeom.vtype v with
  | false =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hv
    rw [hg, CosetGeom.stab_smul]
    exact opx3_conj_inj (caseATheta L1 L2 S)
      (fun x hx y hy h =>
        (caseATheta_injOn_stab_γ₀ (L1 := L1) (L2 := L2) (S := S)) hx hy h)
      (g : (f112Amalgam L1 L2 S).Ghat)
  | true =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hv
    rw [hg, CosetGeom.stab_smul]
    exact opx3_conj_inj (caseATheta L1 L2 S)
      (fun x hx y hy h =>
        (caseATheta_injOn_stab_γ₁ (L1 := L1) (L2 := L2) (S := S)) hx hy h)
      (g : (f112Amalgam L1 L2 S).Ghat)

theorem caseA_finite_stab (L1 L2 S : Subgroup G) (v : f112Gamma L1 L2 S) :
    Finite ↥(CosetGeom.stab v) := by
  refine Finite.of_injective
    (fun x : ↥(CosetGeom.stab v) =>
      caseATheta L1 L2 S (x : (f112Amalgam L1 L2 S).Ghat)) ?_
  intro x y hxy
  exact Subtype.ext (caseATheta_injOn_stab L1 L2 S v x.2 y.2 hxy)

theorem caseATheta_map_stab_γ₀ (L1 L2 S : Subgroup G) :
    (CosetGeom.stab (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) = P1 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ P1 L1 L2 S :=
      (f112StabEquiv0 L1 L2 S ⟨h, hh⟩).2
    rwa [coe_f112StabEquiv0_caseATheta] at h1
  · intro p hp
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
      (f112StabEquiv0 L1 L2 S).symm ⟨p, hp⟩
    refine Subgroup.mem_map.mpr
      ⟨((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(h : f112Acting L1 L2 S), h.2, rfl⟩
    · rw [← coe_f112StabEquiv0_caseATheta]
      exact congrArg Subtype.val ((f112StabEquiv0 L1 L2 S).apply_symm_apply ⟨p, hp⟩)

theorem caseATheta_map_stab_γ₁ (L1 L2 S : Subgroup G) :
    (CosetGeom.stab (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = P2 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ P2 L1 L2 S :=
      (f112StabEquiv1 L1 L2 S ⟨h, hh⟩).2
    rwa [coe_f112StabEquiv1_caseATheta] at h1
  · intro p hp
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
      (f112StabEquiv1 L1 L2 S).symm ⟨p, hp⟩
    refine Subgroup.mem_map.mpr
      ⟨((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(h : f112Acting L1 L2 S), h.2, rfl⟩
    · rw [← coe_f112StabEquiv1_caseATheta]
      exact congrArg Subtype.val ((f112StabEquiv1 L1 L2 S).apply_symm_apply ⟨p, hp⟩)

theorem caseATheta_map_stab_inf {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    (CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓ CosetGeom.stab (f112Gamma1 L1 L2 S)).map
      (caseATheta L1 L2 S) = bigB L1 L2 S := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hinter := (RankTwoAmalgam.Completion.coverData (f112Completion L1 L2 S) hc).inter
  rw [← f112_parabolic_inf_eq_bigB hfr.1,
    CosetGeom.stab_γ₀ (G₁ := (f112Amalgam L1 L2 S).Ghat1)
      (G₂ := (f112Amalgam L1 L2 S).Ghat2) le_sup_left,
    CosetGeom.stab_γ₁ (G₁ := (f112Amalgam L1 L2 S).Ghat1)
      (G₂ := (f112Amalgam L1 L2 S).Ghat2) le_sup_right,
    show caseATheta L1 L2 S = (((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)).subtype).comp
      (f112Completion L1 L2 S).theta from rfl,
    ← Subgroup.map_map, hinter, (f112Completion L1 L2 S).inter]
  ext z
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact a.2
  · rintro ⟨hz1, hz2⟩
    exact ⟨_, ⟨⟨z, hz1, hz2⟩, rfl⟩, rfl⟩

theorem caseATheta_map_Qy_γ₀ (L1 L2 S : Subgroup G) :
    (CosetGeom.Qy (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) = Q1 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxstab : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := caseA_Qy_le_stab _ hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxstab
    have hQ : (f112StabEquiv0 L1 L2 S ⟨k, hk⟩ : G) ∈ Q1 L1 L2 S :=
      (caseA_mem_Qy_γ₀_iff ⟨k, hk⟩).mp hx
    rwa [coe_f112StabEquiv0_caseATheta] at hQ
  · intro q hq
    have hqP1 : q ∈ P1 L1 L2 S :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S)) hq
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
      (f112StabEquiv0 L1 L2 S).symm ⟨q, hqP1⟩
    have hh : (f112StabEquiv0 L1 L2 S h : G) = q :=
      congrArg Subtype.val ((f112StabEquiv0 L1 L2 S).apply_symm_apply ⟨q, hqP1⟩)
    refine Subgroup.mem_map.mpr
      ⟨((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact (caseA_mem_Qy_γ₀_iff h).mpr (by rw [hh]; exact hq)
    · rw [← coe_f112StabEquiv0_caseATheta]
      exact hh

theorem caseATheta_map_Qy_γ₁ (L1 L2 S : Subgroup G) :
    (CosetGeom.Qy (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = Q2 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxstab : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := caseA_Qy_le_stab _ hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxstab
    have hQ : (f112StabEquiv1 L1 L2 S ⟨k, hk⟩ : G) ∈ Q2 L1 L2 S :=
      (caseA_mem_Qy_γ₁_iff ⟨k, hk⟩).mp hx
    rwa [coe_f112StabEquiv1_caseATheta] at hQ
  · intro q hq
    have hqP2 : q ∈ P2 L1 L2 S :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)) hq
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
      (f112StabEquiv1 L1 L2 S).symm ⟨q, hqP2⟩
    have hh : (f112StabEquiv1 L1 L2 S h : G) = q :=
      congrArg Subtype.val ((f112StabEquiv1 L1 L2 S).apply_symm_apply ⟨q, hqP2⟩)
    refine Subgroup.mem_map.mpr
      ⟨((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact (caseA_mem_Qy_γ₁_iff h).mpr (by rw [hh]; exact hq)
    · rw [← coe_f112StabEquiv1_caseATheta]
      exact hh

theorem caseATheta_map_Z_γ₀ (L1 L2 S : Subgroup G) :
    (caseAZ (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) = Z1 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxstab : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) :=
      caseA_Qy_le_stab _ (caseA_Z_le_Qy _ hx)
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hxstab
    have hZ : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ Z1 L1 L2 S :=
      (caseA_mem_Z_γ₀_iff ⟨h, hh⟩).mp (by simpa using hx)
    rwa [coe_f112StabEquiv0_caseATheta] at hZ
  · intro z hz
    have hzP1 : z ∈ P1 L1 L2 S :=
      (A4.omegaOneCenterOf_le (Q1 L1 L2 S)).trans
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S)) hz
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
      (f112StabEquiv0 L1 L2 S).symm ⟨z, hzP1⟩
    have hh : (f112StabEquiv0 L1 L2 S h : G) = z :=
      congrArg Subtype.val ((f112StabEquiv0 L1 L2 S).apply_symm_apply ⟨z, hzP1⟩)
    refine Subgroup.mem_map.mpr
      ⟨((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact (caseA_mem_Z_γ₀_iff h).mpr (by rw [hh]; exact hz)
    · rw [← coe_f112StabEquiv0_caseATheta]
      exact hh

private theorem thetac_pCoreOf_bigB_eq_S {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) : pCoreOf 2 (bigB L1 L2 S) = S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hfr.1.1
  have hsylB : CFSG.QuasithinUnique.IsSylowTwoOf S (bigB L1 L2 S) := F112W.isSylowTwoOf_bigB hR
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
    hfr.2.1 hfr.1.1.h1.pgroup)
  refine A4.le_of_normal_of_isSylowTwoOf hsylB (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (bigB L1 L2 S))

theorem caseATheta_map_S {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = S := by
  let H := CosetGeom.stab (f112Gamma0 L1 L2 S)
  let P : Subgroup (f112Amalgam L1 L2 S).Ghat :=
    CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓ CosetGeom.stab (f112Gamma1 L1 L2 S)
  have hH : P ≤ H := inf_le_left
  let ψ : ↥H →* G := (caseATheta L1 L2 S).comp H.subtype
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext (caseATheta_injOn_stab_γ₀ x.2 y.2 hxy)
  have hmapP : (P.subgroupOf H).map ψ = P.map (caseATheta L1 L2 S) := by
    rw [show ψ = (caseATheta L1 L2 S).comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hH]
  have hkey : (pCoreOf 2 (P.subgroupOf H)).map ψ = (pCoreOf 2 P).map (caseATheta L1 L2 S) := by
    let e : ↥(P.subgroupOf H) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hH
    have hcomp : ψ.comp (P.subgroupOf H).subtype =
        ((caseATheta L1 L2 S).comp P.subtype).comp e.toMonoidHom := by
      ext x
      rfl
    calc (pCoreOf 2 (P.subgroupOf H)).map ψ
        = ((pCore 2 ↥(P.subgroupOf H)).map (P.subgroupOf H).subtype).map ψ := rfl
      _ = (pCore 2 ↥(P.subgroupOf H)).map (ψ.comp (P.subgroupOf H).subtype) := by
            rw [Subgroup.map_map]
      _ = (pCore 2 ↥(P.subgroupOf H)).map
            (((caseATheta L1 L2 S).comp P.subtype).comp e.toMonoidHom) := by rw [hcomp]
      _ = ((pCore 2 ↥(P.subgroupOf H)).map e.toMonoidHom).map
            ((caseATheta L1 L2 S).comp P.subtype) := by rw [Subgroup.map_map]
      _ = (pCore 2 ↥P).map ((caseATheta L1 L2 S).comp P.subtype) := by
            rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv]
      _ = ((pCore 2 ↥P).map P.subtype).map (caseATheta L1 L2 S) := by
            rw [Subgroup.map_map]
      _ = (pCoreOf 2 P).map (caseATheta L1 L2 S) := rfl
  have hpc := CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 ψ hψ (P.subgroupOf H)
  rw [hmapP] at hpc
  rw [caseATheta_map_stab_inf hfr, thetac_pCoreOf_bigB_eq_S hfr] at hpc
  rw [hkey] at hpc
  change (pCoreOf 2 P).map (caseATheta L1 L2 S) = S
  exact hpc.symm

private theorem thetac_caseALhat_γ₀_eq_conjClosure :
    caseALhat (f112Gamma0 L1 L2 S) =
      conjClosure (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S))
        (CosetGeom.stab (f112Gamma0 L1 L2 S)) := by
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    obtain ⟨g, hg, hgw⟩ := CosetGeom.stab_transitive_on_nbrs
      (γ := f112Gamma0 L1 L2 S) (δ := f112Gamma1 L1 L2 S) (δ' := w)
      (CosetGeom.adj_γ₀_γ₁) hw
    have hgfix : g • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
      CosetGeom.smul_eq_of_mem_stab hg
    have hS : caseAS (f112Gamma0 L1 L2 S) w =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat)
          (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) := by
      have h1 : caseAS (f112Gamma0 L1 L2 S) w =
          caseAS (g • f112Gamma0 L1 L2 S) (g • f112Gamma1 L1 L2 S) := by
        rw [hgfix, hgw]
      rw [h1]
      exact caseA_S_smul g (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)
    rw [hS]
    intro x hx
    have hx' : (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
        (g : (f112Amalgam L1 L2 S).Ghat) ∈
        caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) :=
      mem_conjSub.mp hx
    have h := mem_conjClosure (Z := caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S))
      (H := CosetGeom.stab (f112Gamma0 L1 L2 S)) hg hx'
    simpa [mul_assoc] using h
  · refine conjClosure_le fun x hx z hz => ?_
    obtain ⟨hxG, hxfix⟩ := CosetGeom.mem_stab.mp hx
    let g : f112Acting L1 L2 S := ⟨x, hxG⟩
    have hgfix : g • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := hxfix
    have hgγ₁ : g • f112Gamma1 L1 L2 S ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S) := by
      have h := (CosetGeom.smul_adj
        (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) g).mpr
        (CosetGeom.adj_γ₀_γ₁
          (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2))
      simpa [hgfix, CosetGeom.nbrs] using h
    have hS : caseAS (f112Gamma0 L1 L2 S) (g • f112Gamma1 L1 L2 S) =
        conjSub x (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) := by
      have h := caseA_S_smul g (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)
      rw [hgfix] at h
      simpa using h
    have hle : caseAS (f112Gamma0 L1 L2 S) (g • f112Gamma1 L1 L2 S) ≤
        caseALhat (f112Gamma0 L1 L2 S) :=
      le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S)) =>
        caseAS (f112Gamma0 L1 L2 S) w) (g • f112Gamma1 L1 L2 S) hgγ₁
    have h1 : x * z * x⁻¹ ∈
        conjSub x (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      mul_mem_conjSub hz
    rw [← hS] at h1
    exact hle h1

private theorem thetac_conjClosure_P1_eq {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    conjClosure S (P1 L1 L2 S) = conjClosure S (L1 ⊔ S) := by
  apply le_antisymm
  · refine conjClosure_le fun p hp z hz => ?_
    have hB : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
      bigB_le_normalizer_of_hyp111 hfr.1.1
    obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hB).mp hp
    have hbz : b * z * b⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hfr.2.1 hb) z).mp hz
    have hmem : l * (b * z * b⁻¹) * l⁻¹ ∈ conjClosure S (L1 ⊔ S) :=
      mem_conjClosure (Subgroup.mem_sup_left hl) hbz
    have heq : (l * b) * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ := by group
    rw [heq]
    exact hmem
  · refine conjClosure_mono le_rfl ?_
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)

private theorem thetac_conjClosure_S_sup_left {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) : conjClosure S (L1 ⊔ S) = L1 ⊔ S := by
  have ha : 1 ≤ a := hfr.2.2.1
  have hsim : IsSimpleGroup (oTwoQuot ↥(L1 ⊔ S)) := str83G4_isSimpleGroup_left hfr
  have hQH : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  have hnotle : ¬ S ≤ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQH]
    intro hle
    have hrel : (Q1 L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [str83G4_relIndex_q1_s hfr] at hrel
    have hge : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith [hge]
    omega
  have hNQ : ¬ conjClosure S (L1 ⊔ S) ≤ pCoreOf 2 (L1 ⊔ S) :=
    fun h => hnotle ((le_conjClosure S (L1 ⊔ S)).trans h)
  have hNH : conjClosure S (L1 ⊔ S) ≤ L1 ⊔ S :=
    conjClosure_le fun h hh z hz =>
      (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem hh (Subgroup.mem_sup_right hz)) ((L1 ⊔ S).inv_mem hh)
  have hN : (L1 ⊔ S) ≤ Subgroup.normalizer (conjClosure S (L1 ⊔ S) : Set G) :=
    le_normalizer_conjClosure S (L1 ⊔ S)
  have hsup := sup_pCoreOf_eq_of_normal_of_isSimple hsim hNH hN hNQ
  have hQK : pCoreOf 2 (L1 ⊔ S) ≤ conjClosure S (L1 ⊔ S) := by
    rw [hQH]
    exact (str83G4_q1_le_s hfr).trans (le_conjClosure S (L1 ⊔ S))
  rw [sup_eq_left.mpr hQK] at hsup
  exact hsup

theorem caseATheta_map_Lhat_γ₀ {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    (caseALhat (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) = L1 ⊔ S := by
  rw [thetac_caseALhat_γ₀_eq_conjClosure,
    CFSG.Quasithin.SmithC27.map_conjClosure' (caseATheta L1 L2 S),
    caseATheta_map_S hfr, caseATheta_map_stab_γ₀ L1 L2 S,
    thetac_conjClosure_P1_eq hfr]
  exact thetac_conjClosure_S_sup_left hfr

private theorem thetac_conjClosure_P2_eq {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    conjClosure S (P2 L1 L2 S) = conjClosure S (L2 ⊔ S) := by
  apply le_antisymm
  · refine conjClosure_le fun p hp z hz => ?_
    have hB : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
      simpa [bigB_comm] using bigB_le_normalizer_of_hyp111 hfr.1.1.symm
    obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hB).mp hp
    have hbz : b * z * b⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hfr.2.1 hb) z).mp hz
    have hmem : l * (b * z * b⁻¹) * l⁻¹ ∈ conjClosure S (L2 ⊔ S) :=
      mem_conjClosure (Subgroup.mem_sup_left hl) hbz
    have heq : (l * b) * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ := by group
    rw [heq]
    exact hmem
  · refine conjClosure_mono le_rfl ?_
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)

private theorem thetac_conjClosure_S_sup_right {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) : conjClosure S (L2 ⊔ S) = L2 ⊔ S := by
  have ha : 1 ≤ a := hfr.2.2.1
  have hsim : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ S)) := str83G4_isSimpleGroup_right hfr
  have hQH : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := str83G4_pCoreOf_sup_right hfr
  have hnotle : ¬ S ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hQH]
    intro hle
    have hrel : (Q2 L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [str86_relIndex_q2_s hfr.1 hfr.2.1 (by omega) hfr.2.2.2.2.1] at hrel
    have hge : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hNQ : ¬ conjClosure S (L2 ⊔ S) ≤ pCoreOf 2 (L2 ⊔ S) :=
    fun h => hnotle ((le_conjClosure S (L2 ⊔ S)).trans h)
  have hNH : conjClosure S (L2 ⊔ S) ≤ L2 ⊔ S :=
    conjClosure_le fun h hh z hz =>
      (L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hh (Subgroup.mem_sup_right hz)) ((L2 ⊔ S).inv_mem hh)
  have hN : (L2 ⊔ S) ≤ Subgroup.normalizer (conjClosure S (L2 ⊔ S) : Set G) :=
    le_normalizer_conjClosure S (L2 ⊔ S)
  have hsup := sup_pCoreOf_eq_of_normal_of_isSimple hsim hNH hN hNQ
  have hQK : pCoreOf 2 (L2 ⊔ S) ≤ conjClosure S (L2 ⊔ S) := by
    rw [hQH]
    exact (str83G4_q2_le_s hfr).trans (le_conjClosure S (L2 ⊔ S))
  rw [sup_eq_left.mpr hQK] at hsup
  exact hsup

private theorem thetac_caseALhat_γ₁_eq_conjClosure :
    caseALhat (f112Gamma1 L1 L2 S) =
      conjClosure (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S))
        (CosetGeom.stab (f112Gamma1 L1 L2 S)) := by
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    obtain ⟨g, hg, hgw⟩ := CosetGeom.stab_transitive_on_nbrs
      (γ := f112Gamma1 L1 L2 S) (δ := f112Gamma0 L1 L2 S) (δ' := w)
      (CosetGeom.adj_γ₀_γ₁.symm) hw
    have hgfix : g • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
      CosetGeom.smul_eq_of_mem_stab hg
    have hS : caseAS (f112Gamma1 L1 L2 S) w =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat)
          (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) := by
      have h1 : caseAS (f112Gamma1 L1 L2 S) w =
          caseAS (g • f112Gamma1 L1 L2 S) (g • f112Gamma0 L1 L2 S) := by
        rw [hgfix, hgw]
      rw [h1]
      exact caseA_S_smul g (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)
    rw [hS]
    intro x hx
    have hx' : (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
        (g : (f112Amalgam L1 L2 S).Ghat) ∈
        caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :=
      mem_conjSub.mp hx
    have h := mem_conjClosure (Z := caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S))
      (H := CosetGeom.stab (f112Gamma1 L1 L2 S)) hg hx'
    simpa [mul_assoc] using h
  · refine conjClosure_le fun x hx z hz => ?_
    obtain ⟨hxG, hxfix⟩ := CosetGeom.mem_stab.mp hx
    let g : f112Acting L1 L2 S := ⟨x, hxG⟩
    have hgfix : g • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := hxfix
    have hgγ₀ : g • f112Gamma0 L1 L2 S ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S) := by
      have h := (CosetGeom.smul_adj
        (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) g).mpr
        (CosetGeom.adj_γ₀_γ₁
          (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
      simpa [hgfix, CosetGeom.nbrs] using h
    have hS : caseAS (f112Gamma1 L1 L2 S) (g • f112Gamma0 L1 L2 S) =
        conjSub x (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) := by
      have h := caseA_S_smul g (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)
      rw [hgfix] at h
      simpa using h
    have hle : caseAS (f112Gamma1 L1 L2 S) (g • f112Gamma0 L1 L2 S) ≤
        caseALhat (f112Gamma1 L1 L2 S) :=
      le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S)) =>
        caseAS (f112Gamma1 L1 L2 S) w) (g • f112Gamma0 L1 L2 S) hgγ₀
    have h1 : x * z * x⁻¹ ∈
        conjSub x (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) :=
      mul_mem_conjSub hz
    rw [← hS] at h1
    exact hle h1

theorem caseATheta_map_Lhat_γ₁ {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    (caseALhat (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = L2 ⊔ S := by
  rw [thetac_caseALhat_γ₁_eq_conjClosure,
    CFSG.Quasithin.SmithC27.map_conjClosure' (caseATheta L1 L2 S),
    caseAS_comm (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S),
    caseATheta_map_S hfr, caseATheta_map_stab_γ₁ L1 L2 S,
    thetac_conjClosure_P2_eq hfr]
  exact thetac_conjClosure_S_sup_right hfr

private noncomputable def thetad_conj (g : f112Acting L1 L2 S) :
    (f112Amalgam L1 L2 S).Ghat →* G :=
  (caseATheta L1 L2 S).comp
    (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)).toMonoidHom

private theorem thetad_map_conjSub (g : f112Acting L1 L2 S)
    (H : Subgroup (f112Amalgam L1 L2 S).Ghat) :
    (conjSub (g : (f112Amalgam L1 L2 S).Ghat) H).map (thetad_conj g) =
      H.map (caseATheta L1 L2 S) := by
  have hcomp : (thetad_conj g).comp
        (MulAut.conj (g : (f112Amalgam L1 L2 S).Ghat)).toMonoidHom =
      caseATheta L1 L2 S := by
    ext x
    simp only [thetad_conj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    apply congrArg (caseATheta L1 L2 S)
    group
  rw [conjSub, Subgroup.map_map, hcomp]

private theorem thetad_injOn_conjSub (g : f112Acting L1 L2 S)
    {H : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (h : Set.InjOn (caseATheta L1 L2 S)
      (H : Set (f112Amalgam L1 L2 S).Ghat)) :
    Set.InjOn (thetad_conj g)
      (conjSub (g : (f112Amalgam L1 L2 S).Ghat) H :
        Set (f112Amalgam L1 L2 S).Ghat) := by
  intro x hx y hy hxy
  have hx' : (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)) x ∈ H := by
    simpa only [MulAut.conj_apply, inv_inv] using (mem_conjSub.mp hx)
  have hy' : (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)) y ∈ H := by
    simpa only [MulAut.conj_apply, inv_inv] using (mem_conjSub.mp hy)
  have hh : (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)) x =
      (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)) y :=
    h hx' hy' (by
      simpa only [thetad_conj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv] using hxy)
  exact (MulAut.conj (((g : (f112Amalgam L1 L2 S).Ghat))⁻¹)).injective hh

theorem caseA_exists_chart_edge
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hβ : β ∈ CosetGeom.nbrs α) :
    ∃ φ : (f112Amalgam L1 L2 S).Ghat →* G,
      Set.InjOn φ (CosetGeom.stab α : Set (f112Amalgam L1 L2 S).Ghat) ∧
      Set.InjOn φ (CosetGeom.stab β : Set (f112Amalgam L1 L2 S).Ghat) ∧
      (CosetGeom.stab α).map φ = P1 L1 L2 S ∧ (CosetGeom.stab β).map φ = P2 L1 L2 S ∧
      (CosetGeom.stab α ⊓ CosetGeom.stab β).map φ = bigB L1 L2 S ∧
      (CosetGeom.Qy α).map φ = Q1 L1 L2 S ∧ (CosetGeom.Qy β).map φ = Q2 L1 L2 S ∧
      (caseAZ α).map φ = Z1 L1 L2 S ∧ (caseAZ β).map φ = Z2 L1 L2 S ∧
      (caseAX α).map φ = str83X L1 L2 S ∧ (caseAR β).map φ = str83R L1 L2 S ∧
      (caseAS α β).map φ = S ∧ (caseALhat α).map φ = L1 ⊔ S ∧
      (caseALhat β).map φ = L2 ⊔ S := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge hβ
  · obtain ⟨hgα, hgβ⟩ := hg
    have hinjα : Set.InjOn (thetad_conj g)
        (CosetGeom.stab α : Set (f112Amalgam L1 L2 S).Ghat) := by
      rw [← hgα, CosetGeom.stab_smul g (f112Gamma0 L1 L2 S)]
      exact thetad_injOn_conjSub g caseATheta_injOn_stab_γ₀
    have hinjβ : Set.InjOn (thetad_conj g)
        (CosetGeom.stab β : Set (f112Amalgam L1 L2 S).Ghat) := by
      rw [← hgβ, CosetGeom.stab_smul g (f112Gamma1 L1 L2 S)]
      exact thetad_injOn_conjSub g caseATheta_injOn_stab_γ₁
    have hstabα : (CosetGeom.stab α).map (thetad_conj g) = P1 L1 L2 S := by
      rw [← hgα, CosetGeom.stab_smul g (f112Gamma0 L1 L2 S),
        thetad_map_conjSub g (CosetGeom.stab (f112Gamma0 L1 L2 S)),
        caseATheta_map_stab_γ₀ L1 L2 S]
    have hstabβ : (CosetGeom.stab β).map (thetad_conj g) = P2 L1 L2 S := by
      rw [← hgβ, CosetGeom.stab_smul g (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (CosetGeom.stab (f112Gamma1 L1 L2 S)),
        caseATheta_map_stab_γ₁ L1 L2 S]
    have hstabinf : (CosetGeom.stab α ⊓ CosetGeom.stab β).map (thetad_conj g) =
        bigB L1 L2 S := by
      rw [← hgα, ← hgβ, CosetGeom.stab_smul g (f112Gamma0 L1 L2 S),
        CosetGeom.stab_smul g (f112Gamma1 L1 L2 S),
        ← conjSub_inf (g : (f112Amalgam L1 L2 S).Ghat)
          (CosetGeom.stab (f112Gamma0 L1 L2 S))
          (CosetGeom.stab (f112Gamma1 L1 L2 S)),
        thetad_map_conjSub g
          (CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓ CosetGeom.stab (f112Gamma1 L1 L2 S)),
        caseATheta_map_stab_inf hfr]
    have hQyα : (CosetGeom.Qy α).map (thetad_conj g) = Q1 L1 L2 S := by
      rw [← hgα, caseA_Qy_smul g (f112Gamma0 L1 L2 S),
        thetad_map_conjSub g (CosetGeom.Qy (f112Gamma0 L1 L2 S)),
        caseATheta_map_Qy_γ₀ L1 L2 S]
    have hQyβ : (CosetGeom.Qy β).map (thetad_conj g) = Q2 L1 L2 S := by
      rw [← hgβ, caseA_Qy_smul g (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (CosetGeom.Qy (f112Gamma1 L1 L2 S)),
        caseATheta_map_Qy_γ₁ L1 L2 S]
    have hZα : (caseAZ α).map (thetad_conj g) = Z1 L1 L2 S := by
      rw [← hgα, caseA_Z_smul g (f112Gamma0 L1 L2 S),
        thetad_map_conjSub g (caseAZ (f112Gamma0 L1 L2 S)),
        caseATheta_map_Z_γ₀ L1 L2 S]
    have hZβ : (caseAZ β).map (thetad_conj g) = Z2 L1 L2 S := by
      rw [← hgβ, caseA_Z_smul g (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (caseAZ (f112Gamma1 L1 L2 S)),
        caseATheta_map_Z_γ₁]
    have hXα : (caseAX α).map (thetad_conj g) = str83X L1 L2 S := by
      rw [← hgα, caseA_X_smul g (f112Gamma0 L1 L2 S),
        thetad_map_conjSub g (caseAX (f112Gamma0 L1 L2 S)),
        caseATheta_map_X_γ₀]
    have hRβ : (caseAR β).map (thetad_conj g) = str83R L1 L2 S := by
      rw [← hgβ, caseA_R_smul g (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (caseAR (f112Gamma1 L1 L2 S)),
        caseATheta_map_R_γ₁]
    have hS : (caseAS α β).map (thetad_conj g) = S := by
      rw [← hgα, ← hgβ, caseA_S_smul g (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)),
        caseATheta_map_S hfr]
    have hLα : (caseALhat α).map (thetad_conj g) = L1 ⊔ S := by
      rw [← hgα, caseA_Lhat_smul g (f112Gamma0 L1 L2 S),
        thetad_map_conjSub g (caseALhat (f112Gamma0 L1 L2 S)),
        caseATheta_map_Lhat_γ₀ hfr]
    have hLβ : (caseALhat β).map (thetad_conj g) = L2 ⊔ S := by
      rw [← hgβ, caseA_Lhat_smul g (f112Gamma1 L1 L2 S),
        thetad_map_conjSub g (caseALhat (f112Gamma1 L1 L2 S)),
        caseATheta_map_Lhat_γ₁ hfr]
    exact ⟨thetad_conj g, hinjα, hinjβ, hstabα, hstabβ, hstabinf, hQyα, hQyβ, hZα, hZβ,
      hXα, hRβ, hS, hLα, hLβ⟩
  · obtain ⟨hgβ0, -⟩ := hg
    have hb : CosetGeom.vtype β = false := by
      rw [← hgβ0]
      exact CosetGeom.vtype_smul g (f112Gamma0 L1 L2 S)
    have hbtrue : CosetGeom.vtype β = true := by
      cases hv : CosetGeom.vtype β with
      | false => exact absurd (hα.trans hv.symm) (CosetGeom.vtype_ne_of_adj hβ)
      | true => rfl
    rw [hb] at hbtrue
    exact absurd hbtrue Bool.false_ne_true

theorem caseA_stab_sup_stab_eq_top {α β : f112Gamma L1 L2 S} (hβ : β ∈ CosetGeom.nbrs α) :
    CosetGeom.stab α ⊔ CosetGeom.stab β = ⊤ := by
  have hβadj : (f112Amalgam L1 L2 S).graphHat.Adj α β := by simpa [CosetGeom.nbrs] using hβ
  have htop : (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2 = ⊤ :=
    (f112Amalgam L1 L2 S).Ghat1_sup_Ghat2
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge hβadj
  · have e1 : CosetGeom.stab α =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab (f112Gamma0 L1 L2 S)) := by
      rw [← hg.1, CosetGeom.stab_smul]
    have e2 : CosetGeom.stab β =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab (f112Gamma1 L1 L2 S)) := by
      rw [← hg.2, CosetGeom.stab_smul]
    rw [e1, e2, ← conjSub_sup]
    generalize hgc : (g : (f112Amalgam L1 L2 S).Ghat) = gc
    rw [caseA_stab_γ₀ L1 L2 S, caseA_stab_γ₁ L1 L2 S, htop]
    exact (by simpa [conjSub] using Subgroup.map_equiv_top (MulAut.conj gc))
  · have e1 : CosetGeom.stab β =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab (f112Gamma0 L1 L2 S)) := by
      rw [← hg.1, CosetGeom.stab_smul]
    have e2 : CosetGeom.stab α =
        conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab (f112Gamma1 L1 L2 S)) := by
      rw [← hg.2, CosetGeom.stab_smul]
    rw [sup_comm, e1, e2, ← conjSub_sup]
    generalize hgc : (g : (f112Amalgam L1 L2 S).Ghat) = gc
    rw [caseA_stab_γ₀ L1 L2 S, caseA_stab_γ₁ L1 L2 S, htop]
    exact (by simpa [conjSub] using Subgroup.map_equiv_top (MulAut.conj gc))

private theorem thetac_exists_smul_eq_of_vtype_eq {u v : f112Gamma L1 L2 S}
    (h : CosetGeom.vtype u = CosetGeom.vtype v) :
    ∃ g : f112Acting L1 L2 S, g • u = v := by
  cases hu : CosetGeom.vtype u with
  | false =>
    have hv : CosetGeom.vtype v = false := by rw [← h, hu]
    obtain ⟨gu, hgu⟩ := CosetGeom.exists_smul_eq_γ₀ hu
    obtain ⟨gv, hgv⟩ := CosetGeom.exists_smul_eq_γ₀ hv
    refine ⟨gv * gu⁻¹, ?_⟩
    rw [mul_smul, hgu, inv_smul_smul, ← hgv]
  | true =>
    have hv : CosetGeom.vtype v = true := by rw [← h, hu]
    obtain ⟨gu, hgu⟩ := CosetGeom.exists_smul_eq_γ₁ hu
    obtain ⟨gv, hgv⟩ := CosetGeom.exists_smul_eq_γ₁ hv
    refine ⟨gv * gu⁻¹, ?_⟩
    rw [mul_smul, hgu, inv_smul_smul, ← hgv]

theorem caseA_eq_bot_of_le_normalizer {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S} (hβ : β ∈ CosetGeom.nbrs α)
    {U : Subgroup (f112Amalgam L1 L2 S).Ghat} (hUα : U ≤ CosetGeom.stab α)
    (hUβ : U ≤ CosetGeom.stab β)
    (hNα : CosetGeom.stab α ≤ Subgroup.normalizer (U : Set (f112Amalgam L1 L2 S).Ghat))
    (hNβ : CosetGeom.stab β ≤ Subgroup.normalizer (U : Set (f112Amalgam L1 L2 S).Ghat)) :
    U = ⊥ := by
  have htop : CosetGeom.stab α ⊔ CosetGeom.stab β = ⊤ := caseA_stab_sup_stab_eq_top hβ
  have hnormal : Subgroup.normalizer (U : Set (f112Amalgam L1 L2 S).Ghat) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = CosetGeom.stab α ⊔ CosetGeom.stab β := htop.symm
      _ ≤ Subgroup.normalizer (U : Set (f112Amalgam L1 L2 S).Ghat) := sup_le hNα hNβ
  have hconj (g : f112Acting L1 L2 S) :
      conjSub (g : (f112Amalgam L1 L2 S).Ghat) U = U := by
    have hmem : (g : (f112Amalgam L1 L2 S).Ghat) ∈
        Subgroup.normalizer (U : Set (f112Amalgam L1 L2 S).Ghat) := by
      rw [hnormal]
      exact Subgroup.mem_top _
    simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem)
  have hNle (v : f112Gamma L1 L2 S) : U ≤ CosetGeom.stab v := by
    have hv : CosetGeom.vtype v = CosetGeom.vtype α ∨
        CosetGeom.vtype v = CosetGeom.vtype β := by
      by_cases hva : CosetGeom.vtype v = CosetGeom.vtype α
      · exact Or.inl hva
      · right
        have hβadj : (f112Amalgam L1 L2 S).graphHat.Adj α β := by
          simpa [CosetGeom.nbrs] using hβ
        have hne := CosetGeom.vtype_ne_of_adj hβadj
        cases hαb : CosetGeom.vtype α <;> cases hβb : CosetGeom.vtype β <;>
          cases hvb : CosetGeom.vtype v <;> simp_all
    rcases hv with hv | hv
    · obtain ⟨g, hg⟩ := thetac_exists_smul_eq_of_vtype_eq (u := α) (v := v) hv.symm
      calc U = conjSub (g : (f112Amalgam L1 L2 S).Ghat) U := (hconj g).symm
        _ ≤ conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab α) := conjSub_mono _ hUα
        _ = CosetGeom.stab v := by rw [← hg, CosetGeom.stab_smul]
    · obtain ⟨g, hg⟩ := thetac_exists_smul_eq_of_vtype_eq (u := β) (v := v) hv.symm
      calc U = conjSub (g : (f112Amalgam L1 L2 S).Ghat) U := (hconj g).symm
        _ ≤ conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.stab β) := conjSub_mono _ hUβ
        _ = CosetGeom.stab v := by rw [← hg, CosetGeom.stab_smul]
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have hxG : n ∈ (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2 := by
    rw [(f112Amalgam L1 L2 S).Ghat1_sup_Ghat2]
    exact Subgroup.mem_top n
  have hfix : ∀ w, (⟨n, hxG⟩ : f112Acting L1 L2 S) • w = w := fun w =>
    CosetGeom.smul_eq_of_mem_stab (hNle w hn)
  have h1 := f112_eq_one_of_forall_smul_eq hfr.1 hfix
  have := congrArg (fun g : f112Acting L1 L2 S => (g : (f112Amalgam L1 L2 S).Ghat)) h1
  simpa using this

end Theta

end CFSG.Quasithin.Stroth

end
