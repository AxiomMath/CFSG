module

public import CFSG.Quasithin.Background.HSL3S77Blk
public import CFSG.Quasithin.Vol2.Ch7Sec77Vm

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem vec_add_self (b : Vec) : b + b = 0 :=
  funext fun i => (by decide : ∀ c : ZMod 2, c + c = 0) (b i)

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem exists_stab (hc : S.Coord θ e) {x : G} (hxM : x ∈ fsuM T L)
    (hx1 : x ∈ Subgroup.centralizer ({S.vec e a1} : Set G)) :
    ∃ g : SL32, act g e1 = e1 ∧ congrHom e (convI S.hV ⟨x, S.hMN hxM⟩) = SL3One.rho g := by
  have hxN := S.hMN hxM
  have hφN : congrHom e (convI S.hV ⟨x, hxN⟩) ∈ pairNorm (ZMod 2) := by
    rw [← S.map_autI_top_eq hc.he]
    exact ⟨_, convI_mem_autI S.hV (Subgroup.mem_top x) hxN, rfl⟩
  have ha := (mem_centralizer_vec_iff hxN a1).mp hx1
  obtain ⟨g, hg | hg⟩ := mem_pairNorm_iff.mp hφN
  · refine ⟨g, ?_, hg⟩
    rw [hg] at ha
    have h1 := congrArg (fun p => Multiplicative.toAdd p.1) ha
    change Multiplicative.toAdd (SL3One.rho g a1).1 = e1 at h1
    rwa [rho_fst] at h1
  · exfalso
    rw [hg] at ha
    have h1 := congrArg (fun p => Multiplicative.toAdd p.1) ha
    change Multiplicative.toAdd (SL3One.rho g a1).2 = e1 at h1
    rw [rho_snd] at h1
    change dact g 0 = e1 at h1
    rw [dact, Matrix.mulVec_zero] at h1
    exact absurd (congrFun h1 0) (by decide)

theorem exists_stabHom (hc : S.Coord θ e) {X : Subgroup G} (hXM : X ≤ fsuM T L)
    (hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G)) :
    ∃ φ : ↥X →* ↥stabE1, ∀ x : ↥X,
      SL3One.rho (φ x : SL32) = congrHom e (convI S.hV ⟨x, S.hMN (hXM x.2)⟩) := by
  set f : ↥stabE1 →* MulAut (PairMod (ZMod 2)) := SL3One.rho.comp stabE1.subtype with hf
  have hfi : Function.Injective f := SL3One.rho_injective.comp Subtype.val_injective
  set ψ₀ : ↥X →* MulAut (PairMod (ZMod 2)) :=
    (congrHom e).comp (convHom S.hV X (hXM.trans S.hMN)) with hψ₀
  have hψ : ∀ x, ψ₀ x ∈ f.range := fun x => by
    obtain ⟨g, hg1, hg⟩ := exists_stab hc (hXM x.2) (hX1 x.2)
    exact ⟨⟨g, hg1⟩, hg.symm⟩
  refine ⟨(MonoidHom.ofInjective hfi).symm.toMonoidHom.comp (ψ₀.codRestrict f.range hψ),
    fun x => ?_⟩
  have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hfi).apply_symm_apply
    (ψ₀.codRestrict f.range hψ x))
  rw [MonoidHom.ofInjective_apply] at h1
  exact h1

theorem exists_index_two (hc : S.Coord θ e) {X : Subgroup G} (hXM : X ≤ fsuM T L)
    (hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G)) (hX2 : IsPGroup 2 X) :
    ∃ R : Subgroup G, R ≤ X ∧ R.relIndex X ≤ 2 ∧ ∀ t ∈ R, ∃ g : SL32,
      act g e1 = e1 ∧ blk g = 1 ∧ ∀ htN : t ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI S.hV ⟨t, htN⟩) = SL3One.rho g := by
  obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
  set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
  refine ⟨χ.ker.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : (χ.ker.map X.subtype).relIndex X = χ.ker.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [h1, Subgroup.index_ker]
    have h2 : IsPGroup 2 χ.range := hX2.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    have h3 : Nat.card χ.range ∣ 6 := card_GL2 ▸ Subgroup.card_subgroup_dvd_card χ.range
    rw [hk] at h3 ⊢
    have h4 : k ≤ 1 := by
      by_contra hk1
      have h5 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := Nat.dvd_trans h5 h3
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h4
      _ = 2 := by norm_num
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨φ x, (φ x).2, ?_, fun htN => (hφ x).symm⟩
    have h1 : (χ x : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
      rw [MonoidHom.mem_ker.mp hx]
      rfl
    rwa [hχ, MonoidHom.comp_apply, coe_blkHom] at h1

theorem conj_mem_of_blk {t : G} {g : SL32} (htN : t ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hg1 : act g e1 = e1) (hgb : blk g = 1)
    (hg : congrHom e (convI S.hV ⟨t, htN⟩) = SL3One.rho g) {w : G} (hw : w ∈ S.vm e) :
    t * w * t⁻¹ * w⁻¹ ∈ Subgroup.zpowers (S.vec e a1) := by
  obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
  obtain ⟨hx, hy⟩ := blk_fix_H1 hg1 hgb
  have h2 : dact g (vp p).2 = (vp p).2 := (dact_eq_iff g _).mpr (hy _ hp.2)
  rw [conj_vec htN]
  rcases hx _ hp.1 with h1 | h1
  · have hq : SL3One.rho g p = p := by
      apply vp_injective
      rw [vp_rho]
      refine Prod.ext ?_ h2
      change act g (vp p).1 = (vp p).1
      calc act g (vp p).1 = act g (vp p).1 + ((vp p).1 + (vp p).1) := by
            rw [vec_add_self, add_zero]
        _ = (act g (vp p).1 + (vp p).1) + (vp p).1 := (add_assoc _ _ _).symm
        _ = (vp p).1 := by rw [h1, zero_add]
    have key : congrHom e (convI S.hV ⟨t, htN⟩) p = p := by rw [hg]; exact hq
    rw [key, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hq : SL3One.rho g p = p * a1 := by
      apply vp_injective
      rw [vp_rho]
      refine Prod.ext ?_ ?_
      · change act g (vp p).1 = (vp p).1 + e1
        calc act g (vp p).1 = act g (vp p).1 + ((vp p).1 + (vp p).1) := by
              rw [vec_add_self, add_zero]
          _ = (act g (vp p).1 + (vp p).1) + (vp p).1 := (add_assoc _ _ _).symm
          _ = (vp p).1 + e1 := by rw [h1, add_comm]
      · change dact g (vp p).2 = (vp p).2 + 0
        rw [add_zero, h2]
    have key : congrHom e (convI S.hV ⟨t, htN⟩) p = p * a1 := by rw [hg]; exact hq
    rw [key, vec_mul]
    have hcomm : S.vec e p * S.vec e a1 * (S.vec e p)⁻¹ = S.vec e a1 := by
      rw [← vec_mul, mul_comm p a1, vec_mul, mul_inv_cancel_right]
    rw [hcomm]
    exact Subgroup.mem_zpowers _

theorem mem_centralizer_of_blk {t : G} {g : SL32}
    (htN : t ∈ Subgroup.normalizer (fsuV T I : Set G)) (hg1 : act g e1 = e1) (hgb : blk g = 1)
    (hg : congrHom e (convI S.hV ⟨t, htN⟩) = SL3One.rho g)
    (hb : t ∈ Subgroup.centralizer ({S.vec e b1} : Set G)) :
    t ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hb' := (mem_centralizer_vec_iff htN b1).mp hb
  rw [hg] at hb'
  have h1 := congrArg (fun p => Multiplicative.toAdd p.2) hb'
  change Multiplicative.toAdd (SL3One.rho g b1).2 = e1 at h1
  rw [rho_snd] at h1
  have hd : (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ e1 = e1 := (dact_eq_iff g e1).mp h1
  have hg' : g = 1 := blk_fix_H0 hg1 hd hgb
  rw [hg', map_one] at hg
  exact (convI_eq_one_iff S.hV _).mp ((congrHom_injective e) (hg.trans (map_one _).symm))

theorem mem_centralizer_of_hyp (hc : S.Coord θ e) {x : G} (hxM : x ∈ fsuM T L)
    (hx1 : x ∈ Subgroup.centralizer ({S.vec e a1} : Set G))
    (hxm : x ∈ Subgroup.centralizer (S.vm e : Set G)) :
    x ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨g, hg1, hg⟩ := exists_stab hc hxM hx1
  have hfix : ∀ v : Vec, v 0 = 0 → act g v = v := by
    intro v hv
    have hmem : S.vec e (pv (v, 0)) ∈ S.vm e := vec_mem_vm ⟨hv, rfl⟩
    have h1 : x ∈ Subgroup.centralizer ({S.vec e (pv (v, 0))} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxm _ hmem).symm
    have h2 := (mem_centralizer_vec_iff (S.hMN hxM) _).mp h1
    rw [hg] at h2
    have h3 := congrArg (fun p => Multiplicative.toAdd p.1) h2
    change Multiplicative.toAdd (SL3One.rho g (pv (v, 0))).1 = v at h3
    rwa [rho_fst] at h3
  have hg' : g = 1 := hyp_fix hg1 hfix
  rw [hg', map_one] at hg
  exact (convI_eq_one_iff S.hV _).mp ((congrHom_injective e) (hg.trans (map_one _).symm))

end Setup

end CFSG.Quasithin.H13.Sec77
