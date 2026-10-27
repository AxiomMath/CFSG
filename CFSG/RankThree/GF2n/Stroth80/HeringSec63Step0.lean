module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec56Singular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS6

section Schur

variable {G : Type} [Group G] [Finite G] {Q R V Z : Subgroup G}
  {t : G} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [(Z.subgroupOf V).Normal]

theorem exists_scalar_of_chi (hχ : IsChiIso Q R V V Z t) (ψ : ↥V ⧸ Z.subgroupOf V ≃*
      Multiplicative (ι → K)) (φ : ↥R →* GL ι K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hQM : ∀ r ∈ R, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q) (hX : AddCommutantScalar φ.range)
    (κ : G → ι → K) (hadd : ∀ x ∈ Q, ∀ y ∈ Q, κ (x * y) = κ x + κ y)
    (hV : ∀ x ∈ V, κ x = 0)
    (hequi : ∀ (r : ↥R) (x : ↥Q), κ (r * x * r⁻¹) = (φ r : Matrix ι ι K) *ᵥ κ x) :
    ∃ c : K, ∀ x ∈ Q, κ x = c • vecOf ψ ⁅x, t⁆ := by
  classical
  let F : ↥Q →* Multiplicative (ι → K) := MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (chiVec hχ ψ x)) (fun x y => by
      show Multiplicative.ofAdd (chiVec hχ ψ (x * y)) = _
      rw [chiVec_mul]
      rfl)
  let Gm : ↥Q →* Multiplicative (ι → K) := MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (κ x)) (fun x y => by
      show Multiplicative.ofAdd (κ ((x * y : ↥Q) : G)) = _
      rw [Subgroup.coe_mul, hadd _ x.2 _ y.2]
      rfl)
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨v, hv⟩ := exists_secVec_eq ψ (Multiplicative.toAdd y)
    obtain ⟨x, hxQ, hxu⟩ := hχ.2.1 v v.2
    refine ⟨⟨x, hxQ⟩, ?_⟩
    show Multiplicative.ofAdd (chiVec hχ ψ ⟨x, hxQ⟩) = y
    have : chiVec hχ ψ ⟨x, hxQ⟩ = secVec ψ v := (secVec_eq_iff ψ _ v).mpr hxu
    rw [this, hv]
    rfl
  have hker : F.ker ≤ Gm.ker := by
    intro x hx
    have h0 : chiVec hχ ψ x = 0 := toAdd_eq_zero.mpr hx
    have hxV : (x : G) ∈ V := (chiVec_eq_zero_iff hχ ψ x).mp h0
    show Multiplicative.ofAdd (κ x) = 1
    rw [hV x hxV]
    rfl
  let lam : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    MonoidHom.liftOfSurjective F hFs ⟨Gm, hker⟩
  have hlam : ∀ x : ↥Q, lam (F x) = Gm x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply F (Function.surjInv hFs)
      (Function.rightInverse_surjInv hFs) ⟨Gm, hker⟩ x
  let L : (ι → K) →+ (ι → K) := AddMonoidHom.mk'
    (fun y => Multiplicative.toAdd (lam (Multiplicative.ofAdd y))) (fun a b => by
      show Multiplicative.toAdd (lam (Multiplicative.ofAdd (a + b))) = _
      rw [ofAdd_add, map_mul, toAdd_mul])
  have hL : ∀ x : ↥Q, L (chiVec hχ ψ x) = κ x := fun x => by
    have := hlam x
    exact congrArg Multiplicative.toAdd this
  obtain ⟨c, hc⟩ := hX L (fun A hA y => by
    obtain ⟨r, rfl⟩ := hA
    obtain ⟨x, hx⟩ := hFs (Multiplicative.ofAdd y)
    have hxy : chiVec hχ ψ x = y := congrArg Multiplicative.toAdd hx
    have h1 := chiVec_conj hχ ψ φ hψ hRV hQM r x
    have h2 := hL ⟨(r : G) * x * (r : G)⁻¹, hQM r r.2 x x.2⟩
    have h3 := hequi r x
    calc L ((φ r : Matrix ι ι K) *ᵥ y) = L ((φ r : Matrix ι ι K) *ᵥ chiVec hχ ψ x) := by
          rw [hxy]
      _ = L (chiVec hχ ψ ⟨(r : G) * x * (r : G)⁻¹, hQM r r.2 x x.2⟩) := by rw [h1]
      _ = κ ((r : G) * x * (r : G)⁻¹) := h2
      _ = (φ r : Matrix ι ι K) *ᵥ κ x := h3
      _ = (φ r : Matrix ι ι K) *ᵥ L (chiVec hχ ψ x) := by rw [hL x]
      _ = (φ r : Matrix ι ι K) *ᵥ L y := by rw [hxy])
  refine ⟨c, fun x hx => ?_⟩
  have h1 := hL ⟨x, hx⟩
  rw [hc] at h1
  rw [← h1]
  congr 1
  exact (vecOf_of_mem ψ (hχ.1 x hx)).symm

end Schur

section Step0

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.Q1_eq_V (I : Inputs) (e : Env hc n t m X) {a : G} (ha : a ∈ hc.CN t)
    (haQ : a ∉ Q) : Q1 hc a = Vt M (LB M Q B) B Z t := by
  obtain ⟨ι, _, _, K, _, _, hch, Xm, hX, -, φ, hφr, hφk, hRV, hn, ψ, hψ⟩ := e.exists_nat
  haveI := hn
  have hχ := e.chi I.h34
  have hNR : ∀ a ∈ hc.CN t, a ∈ Rt M (LB M Q B) t := fun a ha => (Ctx.mem_CN.mp ha).1
  have haR := hNR a ha
  have haM : a ∈ M := hc.Rt_le_M t haR
  have hQM : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hc1 : ∀ x ∈ Q, ⁅a, x⁆ ∈ Vt M (LB M Q B) B Z t := fun x hx => e.comm_mem_V I.h34 ha hx
  have hQQ : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z := fun x hx y hy =>
    hc.hyp.toHyp79.comm_mem_V hx hy
  have hQV : ∀ x ∈ Q, ∀ g ∈ Vt M (LB M Q B) B Z t,
      x * g * x⁻¹ ∈ Vt M (LB M Q B) B Z t ∧ vecOf ψ (x * g * x⁻¹) = vecOf ψ g := by
    intro x hx g hg
    have hxg : x * g * x⁻¹ = ⁅x, g⁆ * g := by
      simp only [commutatorElement_def]
      group
    have hz : ⁅x, g⁆ ∈ Z := hQQ x hx g (hVQ hg)
    rw [hxg]
    exact ⟨(Vt M (LB M Q B) B Z t).mul_mem (hZV hz) hg, by
      rw [vecOf_mul ψ (hZV hz) hg, vecOf_of_mem_Z ψ hz hZV, zero_add]⟩
  have hadd : ∀ x ∈ Q, ∀ y ∈ Q, vecOf ψ ⁅a, x * y⁆ = vecOf ψ ⁅a, x⁆ + vecOf ψ ⁅a, y⁆ := by
    intro x hx y hy
    have hid : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hid, vecOf_mul ψ (hc1 x hx) (hQV x hx _ (hc1 y hy)).1, (hQV x hx _ (hc1 y hy)).2]
  have hV0 : ∀ x ∈ Vt M (LB M Q B) B Z t, vecOf ψ ⁅a, x⁆ = 0 := fun x hx =>
    (vecOf_eq_zero_iff ψ (hc1 x (hVQ hx))).mpr ((Ctx.mem_CN.mp ha).2 x hx)
  have hequi : ∀ (r : ↥(Rt M (LB M Q B) t)) (x : ↥Q),
      vecOf ψ ⁅a, (r : G) * x * (r : G)⁻¹⁆ =
        (φ r : Matrix ι ι K) *ᵥ vecOf ψ ⁅a, (x : G)⁆ := by
    intro r x
    have hq1 : ⁅(r : G)⁻¹, a⁆ ∈ Q := e.N_central I.h34 _ ((Rt M (LB M Q B) t).inv_mem r.2) a ha
    have hid : ⁅a, (r : G) * x * (r : G)⁻¹⁆ =
        (r : G) * ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ * (r : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hid2 : ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ =
        (⁅(r : G)⁻¹, a⁆ * ⁅a, (x : G)⁆ * ⁅(r : G)⁻¹, a⁆⁻¹) * ⁅⁅(r : G)⁻¹, a⁆, (x : G)⁆ := by
      simp only [commutatorElement_def]
      group
    have hmemN : ⁅(r : G)⁻¹, a⁆ * a ∈ hc.CN t :=
      (hc.CN t).mul_mem (hc.Q_le_CN e.hs.toSec5.mem hq1) ha
    have hg : ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ ∈ Vt M (LB M Q B) B Z t :=
      e.comm_mem_V I.h34 hmemN x.2
    have hq1V : (⁅(r : G)⁻¹, a⁆ * ⁅a, (x : G)⁆ * ⁅(r : G)⁻¹, a⁆⁻¹) ∈ Vt M (LB M Q B) B Z t := by
      have := (hQV _ hq1 _ (hc1 x x.2)).1
      simpa [mul_assoc] using this
    have hzz : ⁅⁅(r : G)⁻¹, a⁆, (x : G)⁆ ∈ Z := hQQ _ hq1 _ x.2
    have hv : vecOf ψ ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ = vecOf ψ ⁅a, (x : G)⁆ := by
      rw [hid2, vecOf_mul_Z ψ hq1V hzz hZV]
      have := (hQV _ hq1 _ (hc1 x x.2)).2
      simpa [mul_assoc] using this
    rw [hid, vecOf_conj ψ φ hψ hRV r hg, hv]
  obtain ⟨c, hc'⟩ := exists_scalar_of_chi hχ ψ φ hψ hRV hQM (by rw [hφr]; exact hX)
    (fun x => vecOf ψ ⁅a, x⁆) hadd hV0 (fun r x => hequi r x)
  have hc0 : c ≠ 0 := by
    intro h0
    apply haQ
    refine hc.hyp.centralizer_Qt a haM fun x hx => ?_
    have := hc' x hx
    rw [h0, zero_smul] at this
    exact (vecOf_eq_zero_iff ψ (hc1 x hx)).mp this
  ext x
  rw [← SetLike.mem_coe, ← SetLike.mem_coe]
  show x ∈ Q1 hc a ↔ x ∈ Vt M (LB M Q B) B Z t
  rw [hc.mem_Q1_iff haM]
  constructor
  · rintro ⟨hxQ, hxz⟩
    have h1 : c • vecOf ψ ⁅x, t⁆ = 0 := by
      rw [← hc' x hxQ]
      exact (vecOf_eq_zero_iff ψ (hc1 x hxQ)).mpr hxz
    have h2 : vecOf ψ ⁅x, t⁆ = 0 := (smul_eq_zero.mp h1).resolve_left hc0
    exact (hχ.2.2.2.1 x hxQ).mp ((vecOf_eq_zero_iff ψ (hχ.1 x hxQ)).mp h2)
  · intro hx
    exact ⟨hVQ hx, (Ctx.mem_CN.mp ha).2 x hx⟩

end Step0


section Fusion

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Q1_conj (hc : Ctx M Q Z B) {k y : G} (hk : k ∈ M) (hy : y ∈ M) :
    Q1 hc (k * y * k⁻¹) = conjSubgroup k (Q1 hc y) := by
  have hkyM : k * y * k⁻¹ ∈ M := M.mul_mem (M.mul_mem hk hy) (M.inv_mem hk)
  have hZ : ∀ z : G, z ∈ Z ↔ k⁻¹ * z * k ∈ Z := fun z => by
    have := mem_conjSubgroup (g := k) (T := Z) (x := z)
    rwa [hc.conj_Z_eq hk] at this
  have hQ : ∀ z : G, z ∈ Q ↔ k⁻¹ * z * k ∈ Q := fun z => by
    have := mem_conjSubgroup (g := k) (T := Q) (x := z)
    rwa [hc.conj_Q_eq hk] at this
  ext x
  rw [mem_conjSubgroup, hc.mem_Q1_iff hkyM, hc.mem_Q1_iff hy, hQ x, hZ]
  refine and_congr Iff.rfl ?_
  have e : k⁻¹ * ⁅k * y * k⁻¹, x⁆ * k = ⁅y, k⁻¹ * x * k⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]

theorem Env.conj_orbit (I : Inputs) (e : Env hc n t m X) :
    ∀ g ∈ M, conjSubgroup g B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup g B ⊔ Z = conjSubgroup r B ⊔ Z := by
  rcases e.hΩ with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · exact hc.conj_orbit_omegaPlus I.h34 I.hRoot e.hs.toSec5 hK e.hm
      ((sec56SingularConj_of I.h34 I.hRoot).1 G M Q Z B hc n t e.hs.toSec5 K hK m e.hm) hnat
  · exact hc.conj_orbit_omegaMinus I.h34 I.hRoot e.hs.toSec5 hK e.hm hirr
      ((sec56SingularConj_of I.h34 I.hRoot).2 G M Q Z B hc n t e.hs.toSec5 K hK m b c e.hm hirr)
      hnat

theorem Env.fusion (I : Inputs) (e : Env hc n t m X) {x g : G} (hx : x ∈ hc.CN t)
    (hxQ : x ∉ Q) (hg : g ∈ M) (hy : g * x * g⁻¹ ∈ LB M Q B) :
    ∃ h ∈ M, conjSubgroup h (LB M Q B) = LB M Q B ∧
      ∃ q₀ ∈ Q, g * x * g⁻¹ = q₀ * (h * x * h⁻¹) := by
  have hxR : x ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hx).1
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hginv : g⁻¹ ∈ M := M.inv_mem hg
  have hyM : g * x * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hxM) hginv
  have hB1 : B ≤ Q1 hc (g * x * g⁻¹) := (hc.B_le_Vt hy).trans (hc.Vt_le_Q1 hy)
  have hQ1x : Q1 hc x = Vt M (LB M Q B) B Z t := e.Q1_eq_V I hx hxQ
  have hB' : conjSubgroup g⁻¹ B ≤ Vt M (LB M Q B) B Z t := by
    have h1 : conjSubgroup g⁻¹ B ≤ conjSubgroup g⁻¹ (Q1 hc (g * x * g⁻¹)) :=
      Subgroup.map_mono hB1
    have h2 : Q1 hc (g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹) = conjSubgroup g⁻¹ (Q1 hc (g * x * g⁻¹)) :=
      Q1_conj hc hginv hyM
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, hQ1x] at h2
    exact h1.trans h2.ge
  obtain ⟨r, hrR, hr⟩ := e.conj_orbit I g⁻¹ hginv (sup_le hB' sec39_Z_le_Vt)
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hkM : r⁻¹ * g⁻¹ ∈ M := M.mul_mem (M.inv_mem hrM) hginv
  have hkle : conjSubgroup (r⁻¹ * g⁻¹) B ≤ B ⊔ Z := by
    have h0 : conjSubgroup (r⁻¹ * g⁻¹) B = conjSubgroup r⁻¹ (conjSubgroup g⁻¹ B) :=
      conjSubgroup_mul _ _ _
    have h1 : conjSubgroup r⁻¹ (conjSubgroup g⁻¹ B) ≤
        conjSubgroup r⁻¹ (conjSubgroup g⁻¹ B ⊔ Z) := Subgroup.map_mono le_sup_left
    have e1 : conjSubgroup r⁻¹ (conjSubgroup r B) = B := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have e2 : conjSubgroup r⁻¹ Z = Z := hc.conj_Z_eq (M.inv_mem hrM)
    rw [h0]
    rw [hr, conjSubgroup_sup', e1, e2] at h1
    exact h1
  have hkL : conjSubgroup (r⁻¹ * g⁻¹) (LB M Q B) = LB M Q B :=
    hc.conj_LB_eq_of_le_sup_Z hkM hkle
  have hkn : r⁻¹ * g⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    conjSubgroup_eq_self_iff.mp hkL
  refine ⟨(r⁻¹ * g⁻¹)⁻¹, M.inv_mem hkM,
    conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem hkn), ?_⟩
  have hcom : ⁅r, x⁆ ∈ Q := e.N_central I.h34 r hrR x hx
  refine ⟨g * ⁅r, x⁆⁻¹ * g⁻¹, (hc.conj_mem_Q_of_mem_M hg).1 _ (Q.inv_mem hcom), ?_⟩
  simp only [commutatorElement_def]
  group

theorem Env.stronglyClosedMod_of (I : Inputs) (e : Env hc n t m X)
    (hC : ∀ h ∈ M, conjSubgroup h (LB M Q B) = LB M Q B →
      conjSubgroup h (hc.CN t) = hc.CN t) :
    StronglyClosedMod M (hc.CN t) (LB M Q B) := by
  intro x hx g hg hy
  by_cases hxQ : x ∈ Q
  · exact hc.Q_le_CN e.hs.toSec5.mem ((hc.conj_mem_Q_of_mem_M hg).1 x hxQ)
  · obtain ⟨h, hh, hhL, q₀, hq₀, heq⟩ := e.fusion I hx hxQ hg hy
    rw [heq]
    refine (hc.CN t).mul_mem (hc.Q_le_CN e.hs.toSec5.mem hq₀) ?_
    have h1 : h * x * h⁻¹ ∈ conjSubgroup h (hc.CN t) := by
      rw [mem_conjSubgroup, show h⁻¹ * (h * x * h⁻¹) * h = x by group]
      exact hx
    rwa [hC h hh hhL] at h1

end Fusion


end HS6

end CFSG.RankThree.GF2n.Stroth80
