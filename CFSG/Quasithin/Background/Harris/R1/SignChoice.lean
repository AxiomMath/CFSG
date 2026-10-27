module

public import CFSG.Quasithin.Background.Harris.R1.SignChoiceBit
public import CFSG.Quasithin.Background.Harris.R1.ParityPerm
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

@[expose] def IsSignChoice (C : FamCtx K1 L2 S Zs Ω) (z : G) (σ : Ω → G) : Prop :=
  ∀ ω, σ ω = C.zf ω ∨ σ ω = z * C.zf ω

section Basic

variable (C : FamCtx K1 L2 S Zs Ω) {z : G} {σ : Ω → G}

theorem IsSignChoice.exists_eq (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) (ω : Ω) :
    ∃ ζ ∈ Zs, σ ω = ζ * C.zf ω := by
  rcases hσ ω with h | h
  · exact ⟨1, Zs.one_mem, by rw [h, one_mul]⟩
  · exact ⟨z, hz, h⟩

theorem IsSignChoice.mem_vBeta (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) (ω : Ω) :
    σ ω ∈ vBeta K1 L2 S Zs := by
  obtain ⟨ζ, hζ, h⟩ := hσ.exists_eq C hz ω
  rw [h]
  exact (vBeta K1 L2 S Zs).mul_mem (F112J2.Zs_le_vBeta K1 L2 S Zs hζ) (C.zf_mem_U ω)

theorem IsSignChoice.conj_mem (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) (g : ↥(K1 ⊔ S)) (ω : Ω) :
    (g : G) * σ ω * (g : G)⁻¹ * (σ (permHom C g ω))⁻¹ ∈ Zs := by
  obtain ⟨ζ, hζ, h⟩ := hσ.exists_eq C hz ω
  obtain ⟨ζ', hζ', h'⟩ := hσ.exists_eq C hz (permHom C g ω)
  obtain ⟨ε, hε, hg⟩ := FamCtxLemmas.conj_zf_of_mem_sup C g.2 ω
  have hgc : (g : G) ∈ Subgroup.centralizer (Zs : Set G) := C.sup_le_centralizer_Zs g.2
  have hζc : (g : G) * ζ * (g : G)⁻¹ = ζ := by
    have := Subgroup.mem_centralizer_iff.mp hgc ζ hζ
    rw [← this]; group
  have hεc := C.Zs_central (C.zf_mem_U (permHom C g ω)) hε
  rw [h, h']
  have e : (g : G) * (ζ * C.zf ω) * (g : G)⁻¹ * (ζ' * C.zf (permHom C g ω))⁻¹ =
      ζ * (C.zf (permHom C g ω) * ε) * (C.zf (permHom C g ω))⁻¹ * ζ'⁻¹ := by
    have : (g : G) * (ζ * C.zf ω) * (g : G)⁻¹ =
        ((g : G) * ζ * (g : G)⁻¹) * ((g : G) * C.zf ω * (g : G)⁻¹) := by group
    rw [this, hζc, hg]
    group
  rw [e]
  have e2 : ζ * (C.zf (permHom C g ω) * ε) * (C.zf (permHom C g ω))⁻¹ * ζ'⁻¹ = ζ * ε * ζ'⁻¹ := by
    rw [hεc]
    group
  rw [e2]
  exact Zs.mul_mem (Zs.mul_mem hζ hε) (Zs.inv_mem hζ')

end Basic

section Cocycle

variable [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω) {z : G} {σ : Ω → G}

@[expose] noncomputable def dsig (σ : Ω → G) (g : ↥(K1 ⊔ S)) (ω : Ω) : ZMod 2 :=
  zbit ((g : G) * σ ω * (g : G)⁻¹ * (σ (permHom C g ω))⁻¹)

omit [Fintype Ω] [DecidableEq Ω] in
theorem dsig_mul (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ) (g h : ↥(K1 ⊔ S))
    (ω : Ω) : dsig C σ (g * h) ω = dsig C σ h ω + dsig C σ g (permHom C h ω) := by
  have hgc : (g : G) ∈ Subgroup.centralizer (Zs : Set G) := C.sup_le_centralizer_Zs g.2
  have hmem1 := hσ.conj_mem C hz h ω
  have hmem2 := hσ.conj_mem C hz g (permHom C h ω)
  have hconj : (g : G) * ((h : G) * σ ω * (h : G)⁻¹ * (σ (permHom C h ω))⁻¹) * (g : G)⁻¹ =
      (h : G) * σ ω * (h : G)⁻¹ * (σ (permHom C h ω))⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hgc _ hmem1
    rw [← this]; group
  have hperm : permHom C (g * h) ω = permHom C g (permHom C h ω) := by
    rw [map_mul]; rfl
  unfold dsig
  rw [hperm]
  have e : ((g * h : ↥(K1 ⊔ S)) : G) * σ ω * ((g * h : ↥(K1 ⊔ S)) : G)⁻¹ *
      (σ (permHom C g (permHom C h ω)))⁻¹ =
      ((h : G) * σ ω * (h : G)⁻¹ * (σ (permHom C h ω))⁻¹) *
        ((g : G) * σ (permHom C h ω) * (g : G)⁻¹ * (σ (permHom C g (permHom C h ω)))⁻¹) := by
    rw [← hconj]
    show (g : G) * (h : G) * σ ω * ((g : G) * (h : G))⁻¹ * _ = _
    group
  rw [e, zbit_mul (C.Zs_sq hz) hz1 (Zs_cases C hz hz1 hmem1) (Zs_cases C hz hz1 hmem2)]

omit [Fintype Ω] [DecidableEq Ω] in
theorem dsig_one (σ : Ω → G) (ω : Ω) : dsig C σ 1 ω = 0 := by
  unfold dsig
  have : permHom C 1 ω = ω := by simp
  rw [this]
  have e : ((1 : ↥(K1 ⊔ S)) : G) * σ ω * ((1 : ↥(K1 ⊔ S)) : G)⁻¹ * (σ ω)⁻¹ = 1 := by
    show (1 : G) * σ ω * (1 : G)⁻¹ * (σ ω)⁻¹ = 1
    group
  rw [e, zbit_one]

@[expose] noncomputable def epsHom (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ) :
    ↥K1 →* Multiplicative (ZMod 2) where
  toFun k := Multiplicative.ofAdd (∑ ω, dsig C σ ⟨(k : G), Subgroup.mem_sup_left k.2⟩ ω)
  map_one' := by
    have : ∀ ω, dsig C σ (⟨((1 : ↥K1) : G), Subgroup.mem_sup_left (1 : ↥K1).2⟩ : ↥(K1 ⊔ S)) ω =
        0 := fun ω => dsig_one C σ ω
    show Multiplicative.ofAdd _ = 1
    rw [Finset.sum_eq_zero (fun ω _ => this ω)]
    rfl
  map_mul' k l := by
    have hmul : (⟨((k * l : ↥K1) : G), Subgroup.mem_sup_left (k * l).2⟩ : ↥(K1 ⊔ S)) =
        ⟨(k : G), Subgroup.mem_sup_left k.2⟩ * ⟨(l : G), Subgroup.mem_sup_left l.2⟩ := rfl
    rw [← ofAdd_add]
    congr 1
    rw [hmul]
    simp only [dsig_mul C hz hz1 hσ, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    exact Equiv.sum_comp (permHom C ⟨(l : G), Subgroup.mem_sup_left l.2⟩)
      (fun ω => dsig C σ ⟨(k : G), Subgroup.mem_sup_left k.2⟩ ω)

omit [DecidableEq Ω] in
theorem sum_dsig_eq_zero (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ) (k : ↥K1) :
    ∑ ω, dsig C σ ⟨(k : G), Subgroup.mem_sup_left k.2⟩ ω = 0 := by
  have : Group.IsPerfect ↥K1 := A36A.isPerfect_of_mem_cComp C.h.cComp_mem
  have hker := Abelianization.commutator_subset_ker (epsHom C hz hz1 hσ)
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have h := hker (Subgroup.mem_top k)
  have h' : Multiplicative.ofAdd (∑ ω, dsig C σ ⟨(k : G), Subgroup.mem_sup_left k.2⟩ ω) = 1 :=
    MonoidHom.mem_ker.mp h
  exact ofAdd_eq_one.mp h'

end Cocycle

section Stab

variable (C : FamCtx K1 L2 S Zs Ω) (σ : Ω → G)

@[expose] noncomputable def signStab : Subgroup G where
  carrier := {k | ∃ hk : k ∈ K1, ∀ ω, k * σ ω * k⁻¹ = σ (C.D.act ⟨k, hk⟩ ω)}
  one_mem' := ⟨K1.one_mem, fun ω => by
    have : C.D.act (⟨1, K1.one_mem⟩ : ↥K1) ω = ω := by
      have h1 : (⟨1, K1.one_mem⟩ : ↥K1) = 1 := rfl
      rw [h1]; simp
    rw [this]; group⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K1.mul_mem ha hb, fun ω => ?_⟩
    have hmul : (⟨a * b, K1.mul_mem ha hb⟩ : ↥K1) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    have e : a * b * σ ω * (a * b)⁻¹ = a * (b * σ ω * b⁻¹) * a⁻¹ := by group
    rw [e, hb' ω, ha', hmul, map_mul]
    rfl
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K1.inv_mem ha, fun ω => ?_⟩
    have hinv : (⟨a⁻¹, K1.inv_mem ha⟩ : ↥K1) = (⟨a, ha⟩ : ↥K1)⁻¹ := rfl
    rw [hinv, map_inv]
    have h2 := ha' (C.D.act ⟨a, ha⟩⁻¹ ω)
    rw [map_inv] at h2
    have h3 : C.D.act ⟨a, ha⟩ (((C.D.act ⟨a, ha⟩)⁻¹) ω) = ω := by simp
    rw [h3] at h2
    calc a⁻¹ * σ ω * (a⁻¹)⁻¹ = a⁻¹ * (a * σ (((C.D.act ⟨a, ha⟩)⁻¹) ω) * a⁻¹) * (a⁻¹)⁻¹ := by
          rw [h2]
      _ = σ (((C.D.act ⟨a, ha⟩)⁻¹) ω) := by group

theorem mem_signStab_iff {k : G} :
    k ∈ signStab C σ ↔ ∃ hk : k ∈ K1, ∀ ω, k * σ ω * k⁻¹ = σ (C.D.act ⟨k, hk⟩ ω) := Iff.rfl

theorem signStab_le : signStab C σ ≤ K1 := fun _ h => (mem_signStab_iff C σ).1 h |>.1

variable {C σ}

theorem mem_signStab_of_dsig {k : G} (hk : k ∈ K1)
    (h : ∀ ω, dsig C σ ⟨k, Subgroup.mem_sup_left hk⟩ ω = 0) : k ∈ signStab C σ := by
  refine ⟨hk, fun ω => ?_⟩
  have h1 := zbit_eq_zero_iff.mp (h ω)
  have hp : permHom C ⟨k, Subgroup.mem_sup_left hk⟩ ω = C.D.act ⟨k, hk⟩ ω := by
    have := permHom_K1 C ⟨k, hk⟩
    exact congrArg (fun f => f ω) this
  rw [hp] at h1
  exact mul_inv_eq_one.mp h1

end Stab


section Main

variable [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω) {z : G} {σ : Ω → G}

omit [Fintype Ω] [DecidableEq Ω] in
theorem act_eq_one_of_mem_vBeta {q : G} (hq : q ∈ vBeta K1 L2 S Zs) (hk : q ∈ K1) :
    C.D.act ⟨q, hk⟩ = 1 := by
  have h := (permHom_eq_one_iff C ⟨q, Subgroup.mem_sup_left hk⟩).2 (C.vBeta_le_kerM hq)
  exact (permHom_K1 C ⟨q, hk⟩).symm.trans h

omit [Fintype Ω] [DecidableEq Ω] in
theorem dsig_vBeta (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) {q : G} (hq : q ∈ vBeta K1 L2 S Zs)
    (hk : q ∈ K1) (ω : Ω) :
    dsig C σ ⟨q, Subgroup.mem_sup_left hk⟩ ω = fb C q ω := by
  have h1 : permHom C ⟨q, Subgroup.mem_sup_left hk⟩ = 1 := by
    rw [permHom_K1 C ⟨q, hk⟩]
    exact act_eq_one_of_mem_vBeta C hq hk
  obtain ⟨ζ, hζ, hσω⟩ := hσ.exists_eq C hz ω
  unfold dsig fb
  rw [h1]
  show zbit (q * σ ω * q⁻¹ * (σ ω)⁻¹) = zbit (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹)
  rw [hσω]
  have hqz : q * ζ = ζ * q := C.Zs_central hq hζ
  have hc : q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹ ∈ Zs := C.U_comm_mem hq (C.zf_mem_U ω)
  have hcz : (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) * ζ = ζ * (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) :=
    C.Zs_central (F112J2.Zs_le_vBeta K1 L2 S Zs hc) hζ
  have e : q * (ζ * C.zf ω) * q⁻¹ * (ζ * C.zf ω)⁻¹ = q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹ := by
    calc q * (ζ * C.zf ω) * q⁻¹ * (ζ * C.zf ω)⁻¹
        = (q * ζ) * C.zf ω * q⁻¹ * (C.zf ω)⁻¹ * ζ⁻¹ := by group
      _ = ζ * (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) * ζ⁻¹ := by rw [hqz]; group
      _ = (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) * ζ * ζ⁻¹ := by rw [← hcz]
      _ = _ := by group
  rw [e]

omit [Fintype Ω] [DecidableEq Ω] in
theorem signStab_inf_vBeta (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hWK : vBeta K1 L2 S Zs ≤ K1) : vBeta K1 L2 S Zs ⊓ signStab C σ = Zs := by
  apply le_antisymm
  · rintro q ⟨hqW, hk, hq⟩
    have hact := act_eq_one_of_mem_vBeta C hqW hk
    have hcomm : ∀ ω, q * C.zf ω = C.zf ω * q := by
      intro ω
      obtain ⟨ζ, hζ, hσω⟩ := hσ.exists_eq C hz ω
      have h1 := hq ω
      rw [hact] at h1
      simp only [Equiv.Perm.one_apply] at h1
      rw [hσω] at h1
      have hqz : q * ζ = ζ * q := C.Zs_central hqW hζ
      have : q * (ζ * C.zf ω) = (ζ * C.zf ω) * q := by
        calc q * (ζ * C.zf ω) = (q * (ζ * C.zf ω) * q⁻¹) * q := by group
          _ = _ := by rw [h1]
      calc q * C.zf ω = ζ⁻¹ * (ζ * (q * C.zf ω)) := by group
        _ = ζ⁻¹ * (q * (ζ * C.zf ω)) := by rw [← mul_assoc ζ q, ← hqz, mul_assoc]
        _ = ζ⁻¹ * ((ζ * C.zf ω) * q) := by rw [this]
        _ = C.zf ω * q := by group
    refine hcen q hqW fun u hu => ?_
    have hgen : vBeta K1 L2 S Zs ≤ Subgroup.centralizer ({q} : Set G) := by
      refine (C.U_eq_closure hz hz1).le.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x (rfl | ⟨ω, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact C.Zs_central hqW hz
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcomm ω
    have := Subgroup.mem_centralizer_iff.mp (hgen hu) q (Set.mem_singleton _)
    exact this
  · intro x hx
    have hxW := F112J2.Zs_le_vBeta K1 L2 S Zs hx
    have hk := hWK hxW
    refine ⟨hxW, hk, fun ω => ?_⟩
    rw [act_eq_one_of_mem_vBeta C hxW hk]
    simp only [Equiv.Perm.one_apply]
    have := C.Zs_central (hσ.mem_vBeta C hz ω) hx
    rw [← this]
    group

theorem exists_mul_signStab (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hn : 1 < Fintype.card Ω) (hWK : vBeta K1 L2 S Zs ≤ K1) {k : G} (hk : k ∈ K1) :
    ∃ q ∈ vBeta K1 L2 S Zs, ∃ k' ∈ signStab C σ, k = q * k' := by
  set g : ↥(K1 ⊔ S) := ⟨k, Subgroup.mem_sup_left hk⟩ with hg
  set t : Ω → ZMod 2 := fun ω' => dsig C σ g ((permHom C g).symm ω') with ht
  have hsum : ∑ ω', t ω' = 0 := by
    have := Equiv.sum_comp (permHom C g).symm (fun ω => dsig C σ g ω)
    simp only [ht]
    rw [this]
    exact sum_dsig_eq_zero C hz hz1 hσ ⟨k, hk⟩
  obtain ⟨q, hqW, hq⟩ := exists_fb_eq C hz hz1 hn t hsum
  have hqK : q ∈ K1 := hWK hqW
  refine ⟨q, hqW, q⁻¹ * k, ?_, by group⟩
  have hqiW : q⁻¹ ∈ vBeta K1 L2 S Zs := (vBeta K1 L2 S Zs).inv_mem hqW
  have hqiK : q⁻¹ ∈ K1 := K1.inv_mem hqK
  apply mem_signStab_of_dsig (K1.mul_mem hqiK hk)
  intro ω
  have hmul : (⟨q⁻¹ * k, Subgroup.mem_sup_left (K1.mul_mem hqiK hk)⟩ : ↥(K1 ⊔ S)) =
      ⟨q⁻¹, Subgroup.mem_sup_left hqiK⟩ * g := rfl
  rw [hmul, dsig_mul C hz hz1 hσ, dsig_vBeta C hz hσ hqiW hqiK, fb_inv C hz hz1 hqW, hq]
  simp only [ht]
  have : (permHom C g).symm (permHom C g ω) = ω := Equiv.symm_apply_apply _ _
  rw [this]
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  exact key _

end Main

end CFSG.Quasithin.Background.Harris.R1
