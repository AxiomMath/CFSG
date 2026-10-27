module

public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Milestones.ASVolI.D2
public import CFSG.Milestones.ASVolI.D3a

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] noncomputable def o2Phi {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  ((frattini (↥H ⧸ CFSG.pCore 2 ↥H)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

structure HypD32 {Mdot : Type} [Group Mdot] [Finite Mdot] (Tdot Mdp Qm Qp QV : Subgroup Mdot) : Prop where
  sqt : tcStronglyQuasithin Mdot
  kgp : CFSG.SectionRank.IsKGroupCat Mdot
  sylow : IsSylowTwoOf Tdot ⊤
  perf : Mdp = twoResidual Mdp
  normal : ⊤ ≤ Subgroup.normalizer (Mdp : Set Mdot)
  cases : (∃ L : Subgroup Mdot, L ∈ cComp (⊤ : Subgroup Mdot) ∧
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ Mdp = conjClosure L Tdot) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (↥Mdp ⧸ CFSG.pCore 2 ↥Mdp) ∧ o2Phi Mdp < Mdp ∧
      ∀ N : Subgroup Mdot, N ≤ Mdp → o2Phi Mdp ≤ N → (∀ t ∈ Tdot, ∀ x ∈ N, t * x * t⁻¹ ∈ N) →
        N = o2Phi Mdp ∨ N = Mdp)
  sec_le : Qm ≤ Qp ∧ Qp ≤ pCoreOf 2 (⊤ : Subgroup Mdot)
  sec_normal : ⊤ ≤ Subgroup.normalizer (Qm : Set Mdot) ∧ ⊤ ≤ Subgroup.normalizer (Qp : Set Mdot)
  sec_elem : (∀ x ∈ Qp, ∀ y ∈ Qp, x * y * x⁻¹ * y⁻¹ ∈ Qm) ∧ ∀ x ∈ Qp, x ^ 2 ∈ Qm
  o2red : ∀ D : Subgroup Mdot, D ≤ Mdp → (∀ g ∈ Mdp, ∀ d ∈ D, g * d * g⁻¹ ∈ D) →
    (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ secFix Qp Mdp Qm) → D ≤ secFix Qp Mdp Qm
  v_le : Qm ≤ QV ∧ QV ≤ Qp
  v_inv : (∀ g ∈ Mdp ⊔ pCoreOf 2 (Mdp ⊔ Tdot), ∀ x ∈ QV, g * x * g⁻¹ ∈ QV)
  v_comm : QV = Qm ⊔ cmt QV Mdp
  v_irr : secFix Mdp QV Qm < QV ∧
    ∀ K : Subgroup Mdot, secFix Mdp QV Qm ≤ K → K ≤ QV → (∀ g ∈ Mdp, ∀ x ∈ K, g * x * g⁻¹ ∈ K) →
      K = secFix Mdp QV Qm ∨ K = QV

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_3_3 : Prop :=
  ∀ (Mdot : Type) [Group Mdot] [Finite Mdot] (Tdot Mdp Qm Qp QV : Subgroup Mdot),
    HypD32 Tdot Mdp Qm Qp QV →
    ∀ (W : Type) [CommGroup W] [Finite W] (ρ : Mdot →* MulAut W) (π : ↥(conjClosure QV ⊤) →* W),
      Function.Surjective π → π.ker = Qm.subgroupOf (conjClosure QV ⊤) →
      (∀ (g : Mdot) (x y : ↥(conjClosure QV ⊤)), (y : Mdot) = g * x * g⁻¹ → π y = ρ g (π x)) →
        HypD31 ((⊤ : Subgroup Mdot).map ρ) (Mdp.map ρ) (Tdot.map ρ)
          ((QV.subgroupOf (conjClosure QV ⊤)).map π) ∧
        (pCoreOf 2 Mdp ≤ Mdp ⊓ ρ.ker ∧ Mdp ⊓ ρ.ker ≤ o2Phi Mdp)

open scoped commutatorElement

private structure D33Data {Mdot : Type} [Group Mdot] (QV Qm : Subgroup Mdot) {W : Type}
    [CommGroup W] (ρ : Mdot →* MulAut W) (π : ↥(conjClosure QV ⊤) →* W) : Prop where
  surj : Function.Surjective π
  ker : π.ker = Qm.subgroupOf (conjClosure QV ⊤)
  int : ∀ (g : Mdot) (x y : ↥(conjClosure QV ⊤)), (y : Mdot) = g * x * g⁻¹ → π y = ρ g (π x)

section D33

variable {Mdot : Type} [Group Mdot] [Finite Mdot] {Tdot Mdp Qm Qp QV : Subgroup Mdot}
  {W : Type} [CommGroup W] [Finite W] {ρ : Mdot →* MulAut W} {π : ↥(conjClosure QV ⊤) →* W}

private theorem d33_qm_le (h : HypD32 Tdot Mdp Qm Qp QV) : conjClosure QV ⊤ ≤ Qp :=
  conjClosure_le fun g _ z hz =>
    (Subgroup.mem_normalizer_iff.mp (h.sec_normal.2 (Subgroup.mem_top g)) z).mp (h.v_le.2 hz)

private theorem d33_conj_mem (g : Mdot) (x : ↥(conjClosure QV ⊤)) :
    g * (x : Mdot) * g⁻¹ ∈ conjClosure QV ⊤ :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure QV ⊤ (Subgroup.mem_top g)) x).mp x.2

private theorem d33_act (d : D33Data QV Qm ρ π) (g : Mdot) (x : ↥(conjClosure QV ⊤)) :
    ρ g (π x) = π ⟨g * x * g⁻¹, d33_conj_mem g x⟩ :=
  (d.int g x ⟨g * x * g⁻¹, d33_conj_mem g x⟩ rfl).symm

private theorem d33_fix_iff (d : D33Data QV Qm ρ π) (g : Mdot) (x : ↥(conjClosure QV ⊤)) :
    ρ g (π x) = π x ↔ g * (x : Mdot) * g⁻¹ * (x : Mdot)⁻¹ ∈ Qm := by
  rw [d33_act d]
  constructor
  · intro h1
    have h2 : (⟨g * x * g⁻¹, d33_conj_mem g x⟩ * x⁻¹ : ↥(conjClosure QV ⊤)) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [d.ker, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · intro h1
    have h2 : (⟨g * x * g⁻¹, d33_conj_mem g x⟩ * x⁻¹ : ↥(conjClosure QV ⊤)) ∈ π.ker := by
      rw [d.ker, Subgroup.mem_subgroupOf]
      simpa using h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2

private theorem d33_pcore_le_ker (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    pCoreOf 2 Mdp ≤ ρ.ker := by
  have hD : pCoreOf 2 Mdp ≤ secFix Qp Mdp Qm := by
    refine h.o2red (pCoreOf 2 Mdp) (RonanD33.pCoreOf_le Mdp) ?_ ?_
    · intro g hg d' hd'
      exact (Subgroup.mem_normalizer_iff.mp (RonanD33.le_normalizer_pCoreOf Mdp hg) d').mp hd'
    · intro d' hd'
      obtain ⟨k, hk⟩ :=
        RonanD33.isPGroup_iff_forall_mem.mp (RonanD33.pCoreOf_isPGroup Mdp) d' hd'
      exact ⟨k, by rw [hk]; exact Subgroup.one_mem _⟩
  intro g hg
  obtain ⟨_, _, hcomm⟩ := hD hg
  rw [MonoidHom.mem_ker]
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := d.surj w
  show ρ g (π x) = π x
  rw [d33_fix_iff d]
  have h1 := Qm.inv_mem (hcomm (x : Mdot) (d33_qm_le h x.2))
  have e : ((x : Mdot) * g * (x : Mdot)⁻¹ * g⁻¹)⁻¹ = g * (x : Mdot) * g⁻¹ * (x : Mdot)⁻¹ := by
    group
  rwa [e] at h1

private theorem d33_not_le_ker (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    ¬ Mdp ≤ ρ.ker := by
  intro hle
  obtain ⟨x, hxQV, hxn⟩ := SetLike.exists_of_lt h.v_irr.1
  apply hxn
  refine ⟨hxQV, h.sec_normal.1 (Subgroup.mem_top x), fun a ha => ?_⟩
  have h1 : ρ a (π ⟨x, le_conjClosure QV ⊤ hxQV⟩) = π ⟨x, le_conjClosure QV ⊤ hxQV⟩ := by
    have : ρ a = 1 := hle ha
    rw [this]
    rfl
  exact (d33_fix_iff d a ⟨x, le_conjClosure QV ⊤ hxQV⟩).mp h1

private theorem d33_hres (h : HypD32 Tdot Mdp Qm Qp QV) :
    ∀ N : Subgroup Mdot, N ≤ Mdp → (∀ x ∈ Mdp, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      (∀ x ∈ Mdp, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = Mdp := by
  intro N hN hNn hNk
  have h1 : twoResidual Mdp ≤ N :=
    iInf₂_le N ⟨hN, RonanD33.le_normalizer_of_forall_conj_mem hNn, hNk⟩
  exact le_antisymm hN (h.perf.le.trans h1)

private theorem d33_kl (h : HypD32 Tdot Mdp Qm Qp QV) :
    ∀ K : Subgroup Mdot, K ≤ Mdp → (∀ g ∈ Mdp, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ t ∈ Tdot, ∀ k ∈ K, t * k * t⁻¹ ∈ K) → K ≠ Mdp → K ≤ o2Phi Mdp := by
  haveI : Mdp.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.normal)
  have hres := d33_hres h
  rcases h.cases with ⟨L, hL, hq, hX⟩ | ⟨p, hp, hp2, hpg, hlt, hirr⟩
  · intro K hKX hKn hKT hK
    exact RonanD33.kl_of_caseI hres hL.2.2.1 hL.2.1 hq hX hKX hKn hKT hK
  · intro K hKX hKn hKT hK
    exact RonanD33.kl_of_caseII hres hirr hKX hKn hKT hK

private theorem d33_two (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    pCoreOf 2 Mdp ≤ Mdp ⊓ ρ.ker ∧ Mdp ⊓ ρ.ker ≤ o2Phi Mdp := by
  haveI : Mdp.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.normal)
  refine ⟨le_inf (RonanD33.pCoreOf_le Mdp) (d33_pcore_le_ker h d), ?_⟩
  refine d33_kl h _ inf_le_left (fun g hg k hk => ?_) (fun t _ k hk => ?_) ?_
  · refine ⟨Mdp.mul_mem (Mdp.mul_mem hg hk.1) (Mdp.inv_mem hg), ?_⟩
    have hk2 : ρ k = 1 := hk.2
    show ρ (g * k * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hk2, mul_one, mul_inv_cancel]
  · refine ⟨Subgroup.Normal.conj_mem inferInstance k hk.1 t, ?_⟩
    have hk2 : ρ k = 1 := hk.2
    show ρ (t * k * t⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hk2, mul_one, mul_inv_cancel]
  · intro heq
    exact d33_not_le_ker h d (by rw [← heq]; exact inf_le_right)

private theorem d33_qm_le_secFix (h : HypD32 Tdot Mdp Qm Qp QV) : Qm ≤ secFix Mdp QV Qm := by
  intro q hq
  refine ⟨h.v_le.1 hq, h.sec_normal.1 (Subgroup.mem_top q), fun a _ => ?_⟩
  have h1 : a * q * a⁻¹ ∈ Qm :=
    (Subgroup.mem_normalizer_iff.mp (h.sec_normal.1 (Subgroup.mem_top a)) q).mp hq
  exact Qm.mul_mem h1 (Qm.inv_mem hq)

private theorem d33_secFix_le (h : HypD32 Tdot Mdp Qm Qp QV) : secFix Mdp QV Qm ≤ QV :=
  fun _ hx => hx.1

private theorem d33_exp (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    ∀ w : W, w ^ 2 = 1 := by
  intro w
  obtain ⟨x, rfl⟩ := d.surj w
  have hx2 : (x : Mdot) ^ 2 ∈ Qm := h.sec_elem.2 x (d33_qm_le h x.2)
  have : x ^ 2 ∈ π.ker := by
    rw [d.ker, Subgroup.mem_subgroupOf]
    exact hx2
  rw [← map_pow]
  exact MonoidHom.mem_ker.mp this

private theorem d33_qsqtk (h : HypD32 Tdot Mdp Qm Qp QV) :
    IsQuotientOfSQTKTC ↥((⊤ : Subgroup Mdot).map ρ) :=
  ⟨Mdot, inferInstance, inferInstance, h.sqt, h.kgp,
    (ρ.subgroupMap ⊤).comp Subgroup.topEquiv.symm.toMonoidHom, fun y => by
      obtain ⟨x, rfl⟩ := ρ.subgroupMap_surjective ⊤ y
      refine ⟨Subgroup.topEquiv x, ?_⟩
      show (ρ.subgroupMap ⊤) (Subgroup.topEquiv.symm (Subgroup.topEquiv x)) = _
      rw [MulEquiv.symm_apply_apply]⟩

private theorem d33_sylow (h : HypD32 Tdot Mdp Qm Qp QV) :
    IsSylowTwoOf (Tdot.map ρ) ((⊤ : Subgroup Mdot).map ρ) := by
  obtain ⟨_, hT2, hidx⟩ := h.sylow
  have hidx' : ¬ 2 ∣ Tdot.index := by
    have : (Tdot.subgroupOf ⊤).index = Tdot.index := Subgroup.relIndex_top_right Tdot
    rwa [this] at hidx
  obtain ⟨hp, hi⟩ := RonanD33.sylow_map ρ (le_top : Tdot ≤ ⊤) hT2 hidx'
  exact ⟨Subgroup.map_mono le_top, hp, hi⟩

private theorem d33_Mp_normal (h : HypD32 Tdot Mdp Qm Qp QV) :
    (⊤ : Subgroup Mdot).map ρ ≤ Subgroup.normalizer ((Mdp.map ρ : Subgroup (MulAut W)) : Set (MulAut W)) := by
  haveI : Mdp.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.normal)
  refine RonanD33.le_normalizer_of_forall_conj_mem ?_
  rintro _ ⟨g, -, rfl⟩ _ ⟨x, hx, rfl⟩
  exact ⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hx g, by simp⟩

private theorem d33_fixed_eq (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    XMod.fixed ↥(Mdp.map ρ) ((QV.subgroupOf (conjClosure QV ⊤)).map π) =
      ((secFix Mdp QV Qm).subgroupOf (conjClosure QV ⊤)).map π := by
  ext l
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hfix⟩
    refine ⟨x, ?_, rfl⟩
    refine ⟨hx, h.sec_normal.1 (Subgroup.mem_top _), fun g hg => ?_⟩
    have := hfix ⟨ρ g, Subgroup.mem_map_of_mem ρ hg⟩
    exact (d33_fix_iff d g x).mp this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, fun a => ?_⟩
    obtain ⟨a', ha', ha⟩ := a.2
    show (a : MulAut W) (π x) = π x
    rw [← ha]
    exact (d33_fix_iff d a' x).mpr (hx.2.2 a' ha')

private theorem d33_isInv (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    XMod.IsInv ↥(Mdp.map ρ) ((QV.subgroupOf (conjClosure QV ⊤)).map π) := by
  rintro ⟨a, ⟨g, hg, rfl⟩⟩ _ ⟨x, hx, rfl⟩
  show ρ g (π x) ∈ _
  rw [d33_act d]
  exact ⟨⟨g * x * g⁻¹, d33_conj_mem g x⟩, h.v_inv g (Subgroup.mem_sup_left hg) x hx, rfl⟩

private theorem d33_commOf (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    XMod.commOf ↥(Mdp.map ρ) ((QV.subgroupOf (conjClosure QV ⊤)).map π) =
      (QV.subgroupOf (conjClosure QV ⊤)).map π := by
  haveI : Qm.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.sec_normal.1)
  apply le_antisymm (XMod.commOf_le_of_isInv (d33_isInv h d))
  have hcomm : ∀ c ∈ cmt QV Mdp, ∃ hc' : c ∈ conjClosure QV ⊤,
      π ⟨c, hc'⟩ ∈ XMod.commOf ↥(Mdp.map ρ) ((QV.subgroupOf (conjClosure QV ⊤)).map π) := by
    intro c hc
    unfold cmt at hc
    rw [Subgroup.commutator_def] at hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨z, hz, g, hg, rfl⟩ := hc
      have hzQM : z ∈ conjClosure QV ⊤ := le_conjClosure QV ⊤ hz
      let y : ↥(conjClosure QV ⊤) := ⟨z, hzQM⟩
      let y' : ↥(conjClosure QV ⊤) := ⟨g * z * g⁻¹, d33_conj_mem g y⟩
      have e0 : ⁅z, g⁆ = ((y * y'⁻¹ : ↥(conjClosure QV ⊤)) : Mdot) := by
        show z * g * z⁻¹ * g⁻¹ = z * (g * z * g⁻¹)⁻¹
        group
      have hc' : ⁅z, g⁆ ∈ conjClosure QV ⊤ := by
        rw [e0]
        exact (y * y'⁻¹).2
      refine ⟨hc', ?_⟩
      have e : (⟨⁅z, g⁆, hc'⟩ : ↥(conjClosure QV ⊤)) = y * y'⁻¹ := Subtype.ext e0
      rw [e, map_mul, map_inv]
      have h1 : π y' = ρ g (π y) := (d33_act d g y).symm
      have hl : π y ∈ (QV.subgroupOf (conjClosure QV ⊤)).map π := ⟨y, hz, rfl⟩
      have h2 := XMod.mem_commOf_of_mem (A := ↥(Mdp.map ρ)) ⟨ρ g, Subgroup.mem_map_of_mem ρ hg⟩ hl
      have h3 := Subgroup.inv_mem _ h2
      rw [h1]
      have e2 : π y * (ρ g (π y))⁻¹ = ((ρ g (π y)) * (π y)⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
      rw [e2]
      exact h3
    | one =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      have : (⟨1, Subgroup.one_mem _⟩ : ↥(conjClosure QV ⊤)) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨h1, h1'⟩ := ih₁
      obtain ⟨h2, h2'⟩ := ih₂
      refine ⟨Subgroup.mul_mem _ h1 h2, ?_⟩
      have : (⟨c₁ * c₂, Subgroup.mul_mem _ h1 h2⟩ : ↥(conjClosure QV ⊤)) =
          ⟨c₁, h1⟩ * ⟨c₂, h2⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ h1' h2'
    | inv c _ ih =>
      obtain ⟨h1, h1'⟩ := ih
      refine ⟨Subgroup.inv_mem _ h1, ?_⟩
      have : (⟨c⁻¹, Subgroup.inv_mem _ h1⟩ : ↥(conjClosure QV ⊤)) = (⟨c, h1⟩ : ↥(conjClosure QV ⊤))⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ h1'
  rintro _ ⟨x, hx, rfl⟩
  have hxv : (x : Mdot) ∈ Qm ⊔ cmt QV Mdp := h.v_comm ▸ hx
  obtain ⟨q, hq, c, hc, hxqc⟩ := Subgroup.mem_sup_of_normal_left.mp hxv
  obtain ⟨hcQM, hcC⟩ := hcomm c hc
  have hqQM : q ∈ conjClosure QV ⊤ := le_conjClosure QV ⊤ (h.v_le.1 hq)
  have hq1 : π ⟨q, hqQM⟩ = 1 := by
    rw [← MonoidHom.mem_ker, d.ker, Subgroup.mem_subgroupOf]
    exact hq
  have : x = ⟨q, hqQM⟩ * ⟨c, hcQM⟩ := Subtype.ext hxqc.symm
  rw [this, map_mul, hq1, one_mul]
  exact hcC

private theorem d33_irrSec (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    XMod.IsIrrSec ↥(Mdp.map ρ) (XMod.fixed ↥(Mdp.map ρ) ((QV.subgroupOf (conjClosure QV ⊤)).map π))
      ((QV.subgroupOf (conjClosure QV ⊤)).map π) := by
  rw [d33_fixed_eq h d]
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono fun x hx => d33_secFix_le h hx) ?_
    obtain ⟨x, hxQV, hxn⟩ := SetLike.exists_of_lt h.v_irr.1
    intro heq
    have hmem : π ⟨x, le_conjClosure QV ⊤ hxQV⟩ ∈
        (QV.subgroupOf (conjClosure QV ⊤)).map π := ⟨⟨x, le_conjClosure QV ⊤ hxQV⟩, hxQV, rfl⟩
    rw [← heq] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hker' : y⁻¹ * ⟨x, le_conjClosure QV ⊤ hxQV⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [d.ker, Subgroup.mem_subgroupOf] at hker'
    apply hxn
    have h1 := (secFix Mdp QV Qm).mul_mem hy (d33_qm_le_secFix h hker')
    simpa using h1
  · intro J hJinv hJ1 hJ2
    let K : Subgroup Mdot := (J.comap π).map (conjClosure QV ⊤).subtype
    have hKQV : K ≤ QV := by
      rintro _ ⟨y, hy, rfl⟩
      have hyV : π y ∈ (QV.subgroupOf (conjClosure QV ⊤)).map π := hJ2 hy
      obtain ⟨x, hx, hxy⟩ := hyV
      have hker' : x⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      rw [d.ker, Subgroup.mem_subgroupOf] at hker'
      have := QV.mul_mem hx (h.v_le.1 hker')
      simpa using this
    have hsecK : secFix Mdp QV Qm ≤ K := by
      intro x hx
      have hxQM : x ∈ conjClosure QV ⊤ := le_conjClosure QV ⊤ hx.1
      exact ⟨⟨x, hxQM⟩, hJ1 ⟨⟨x, hxQM⟩, hx, rfl⟩, rfl⟩
    have hKinv : ∀ g ∈ Mdp, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
      rintro g hg _ ⟨y, hy, rfl⟩
      refine ⟨⟨g * y * g⁻¹, d33_conj_mem g y⟩, ?_, rfl⟩
      show π ⟨g * y * g⁻¹, d33_conj_mem g y⟩ ∈ J
      rw [← d33_act d]
      exact hJinv ⟨ρ g, Subgroup.mem_map_of_mem ρ hg⟩ (π y) hy
    rcases h.v_irr.2 K hsecK hKQV hKinv with hK | hK
    · left
      refine le_antisymm ?_ hJ1
      intro l hl
      obtain ⟨x, hx, rfl⟩ := hJ2 hl
      have hxK : (x : Mdot) ∈ K := ⟨x, hl, rfl⟩
      rw [hK] at hxK
      exact ⟨x, hxK, rfl⟩
    · right
      refine le_antisymm hJ2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxK : (x : Mdot) ∈ K := by rw [hK]; exact hx
      obtain ⟨y, hy, hyx⟩ := hxK
      have : y = x := Subtype.ext hyx
      subst this
      exact hy

private theorem d33_irr (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    (QV.subgroupOf (conjClosure QV ⊤)).map π ∈ IrrPlus (Mdp.map ρ) (⊤ : Subgroup W) :=
  ⟨le_top, d33_isInv h d, d33_commOf h d, d33_irrSec h d⟩

private theorem d33_o2inv (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    ∀ g ∈ pCoreOf 2 (Mdp.map ρ ⊔ Tdot.map ρ), ∀ v ∈ (QV.subgroupOf (conjClosure QV ⊤)).map π,
      g v ∈ (QV.subgroupOf (conjClosure QV ⊤)).map π := by
  haveI : Mdp.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.normal)
  intro g hg v hv
  rw [← Subgroup.map_sup] at hg
  obtain ⟨_, hT2, hidx⟩ := h.sylow
  have hidx' : ¬ 2 ∣ Tdot.index := by
    have : (Tdot.subgroupOf ⊤).index = Tdot.index := Subgroup.relIndex_top_right Tdot
    rwa [this] at hidx
  obtain ⟨hp, hi⟩ := RonanD33.sylow_map ρ (le_sup_right : Tdot ≤ Mdp ⊔ Tdot) hT2 hidx'
  have hg' : g ∈ Tdot.map ρ :=
    RonanD33.pCoreOf_le_of_sylow (Subgroup.map_mono le_sup_right) hp hi hg
  obtain ⟨t, ht, rfl⟩ := hg'
  have ht' : t ∈ pCoreOf 2 (Mdp ⊔ Tdot) :=
    RonanD33.o2_core_mem hT2 (d33_hres h) (d33_kl h) ρ (d33_pcore_le_ker h d)
      (d33_not_le_ker h d) t ht hg
  obtain ⟨x, hx, rfl⟩ := hv
  rw [d33_act d]
  exact ⟨⟨t * x * t⁻¹, d33_conj_mem t x⟩, h.v_inv t (Subgroup.mem_sup_right ht') x hx, rfl⟩

private theorem d33_gen (d : D33Data QV Qm ρ π) :
    (⨆ m ∈ (⊤ : Subgroup Mdot).map ρ,
      ((QV.subgroupOf (conjClosure QV ⊤)).map π).map m.toMonoidHom) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨x, rfl⟩ := d.surj w
  set U : Subgroup W := ⨆ m ∈ (⊤ : Subgroup Mdot).map ρ,
    ((QV.subgroupOf (conjClosure QV ⊤)).map π).map m.toMonoidHom with hU
  have hgen : conjClosure QV ⊤ ≤ (U.comap π).map (conjClosure QV ⊤).subtype := by
    refine conjClosure_le fun g _ z hz => ?_
    have hz' : z ∈ conjClosure QV ⊤ := le_conjClosure QV ⊤ hz
    refine ⟨⟨g * z * g⁻¹, d33_conj_mem g ⟨z, hz'⟩⟩, ?_, rfl⟩
    show π ⟨g * z * g⁻¹, d33_conj_mem g ⟨z, hz'⟩⟩ ∈ U
    rw [← d33_act d g ⟨z, hz'⟩]
    refine Subgroup.mem_iSup_of_mem (ρ g)
      (Subgroup.mem_iSup_of_mem (Subgroup.mem_map_of_mem ρ (Subgroup.mem_top g)) ?_)
    exact ⟨π ⟨z, hz'⟩, ⟨⟨z, hz'⟩, hz, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hgen x.2
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

private theorem d33_cases (h : HypD32 Tdot Mdp Qm Qp QV) (d : D33Data QV Qm ρ π) :
    (∃ L : Subgroup (MulAut W), D31CaseI ((⊤ : Subgroup Mdot).map ρ) (Mdp.map ρ) (Tdot.map ρ) L) ∨
      ∃ p : ℕ, D31CaseII (Mdp.map ρ) (Tdot.map ρ) p := by
  haveI : Mdp.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.normal)
  have hker := d33_pcore_le_ker h d
  have hnt := d33_not_le_ker h d
  rcases h.cases with ⟨L, hL, hq, hX⟩ | ⟨p, hp, hp2, hpg, hlt, hirr⟩
  · left
    have hLX : L ≤ Mdp := by rw [hX]; exact le_conjClosure L Tdot
    have hLsubM : CFSG.Open.IsSubnormal L Mdp := by
      have := hL.2.2.1.inf_of_le (le_top : Mdp ≤ ⊤)
      rwa [inf_eq_left.mpr hLX] at this
    have hLker : pCoreOf 2 L ≤ ρ.ker := (RonanD33.pCoreOf_le_of_isSubnormal hLsubM).trans hker
    have hLnt : ¬ L ≤ ρ.ker := by
      intro hle
      apply hnt
      rw [hX]
      refine conjClosure_le fun t _ z hz => ?_
      have hz1 : ρ z = 1 := hle hz
      show ρ (t * z * t⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hz1, mul_one, mul_inv_cancel]
    have hqL : CFSG.IsQuasisimple ↥(L.map ρ) :=
      RonanD33.isQuasisimple_map_of_pCore_le_ker hq hLker hLnt
    refine ⟨L.map ρ, ?_, hqL, ?_⟩
    · exact RonanD33.mem_cComp_of_isQuasisimple_of_isSubnormal hqL (hL.2.2.1.map ρ)
    · rw [hX]
      exact RonanD33.map_closure_conj ρ Tdot L
  · right
    haveI : Finite ↥(Mdp.map ρ) :=
      Finite.of_surjective (ρ.subgroupMap Mdp) (ρ.subgroupMap_surjective Mdp)
    have hMp_ne : Mdp.map ρ ≠ ⊥ := by
      intro hbot
      apply hnt
      intro x hx
      have : ρ x ∈ Mdp.map ρ := Subgroup.mem_map_of_mem ρ hx
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    refine ⟨p, hp, hp2, RonanD33.isPGroup_map_of_pCore_le_ker hpg hker,
      RonanD33.frattini_map_lt hMp_ne, ?_⟩
    intro N' hN' hΦ hT
    set N : Subgroup Mdot := Mdp ⊓ N'.comap ρ with hNdef
    have hNle : N ≤ Mdp := inf_le_left
    have hphiN : o2Phi Mdp ≤ N := by
      intro x hx
      exact ⟨RonanD33.phiPre_le Mdp hx, hΦ (RonanD33.phiPre_map_le hker ⟨x, hx, rfl⟩)⟩
    have hNT : ∀ t ∈ Tdot, ∀ x ∈ N, t * x * t⁻¹ ∈ N := by
      intro t ht x hx
      refine ⟨Subgroup.Normal.conj_mem inferInstance x hx.1 t, ?_⟩
      show ρ (t * x * t⁻¹) ∈ N'
      rw [map_mul, map_mul, map_inv]
      exact hT (ρ t) (Subgroup.mem_map_of_mem ρ ht) (ρ x) hx.2
    rcases hirr N hNle hphiN hNT with hN | hN
    · left
      refine le_antisymm ?_ hΦ
      intro y hy
      obtain ⟨x, hxM, rfl⟩ := hN' hy
      have hxN : x ∈ N := ⟨hxM, hy⟩
      rw [hN] at hxN
      exact RonanD33.phiPre_map_le hker ⟨x, hxN, rfl⟩
    · right
      refine le_antisymm hN' ?_
      rintro _ ⟨x, hxM, rfl⟩
      have : x ∈ N := by rw [hN]; exact hxM
      exact this.2

end D33

theorem as_D_3_3 : D_3_3 := by
  unfold D_3_3
  intro Mdot _ _ Tdot Mdp Qm Qp QV h W _ _ ρ π hπs hker hint
  have d : D33Data QV Qm ρ π := ⟨hπs, hker, hint⟩
  exact ⟨⟨⟨d33_exp h d, d33_qsqtk h, d33_sylow h, Subgroup.map_mono le_top, d33_Mp_normal h,
    d33_irr h d, d33_o2inv h d, d33_gen d⟩, d33_cases h d⟩, d33_two h d⟩

end CFSG.ASVolI
