module

public import CFSG.Milestones.ASVolI.B610.FamDef
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.B2FactorizationBaumannVar
public import CFSG.Milestones.ASVolI.B610.Nat
public import CFSG.Milestones.ASVolI.B610.NatFacts

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_cjSub_cjSub (s t : G) (K : Subgroup G) :
    cjSub s (cjSub t K) = cjSub (s * t) K := by
  ext x
  simp [mem_cjSub, mul_assoc]

theorem burnsideB610_cjSub_eq_of_mem_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) : cjSub t K = K := by
  ext x
  rw [mem_cjSub]
  simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) x).symm

theorem burnsideB610_act_eq_one_of_cent {L V : Subgroup G} {F : Type} [Field F]
    (D : NatData L V F) (a : ↥(nLV L V))
    (ha : (a : G) ∈ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) : D.act a = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := D.βsurj x
  show rho D.β D.βsurj D.βker a (D.β w) = D.β w
  rw [rho_apply]
  congr 1
  apply Subtype.ext
  rw [coe_cW]
  have h := Subgroup.mem_centralizer_iff.mp ha _ w.2
  rw [← h, mul_inv_cancel_right]

@[expose] def burnsideB610_famW {ι : Type} (S : Finset ι) (X : ι → Subgroup G) (V : Subgroup G) :
    Subgroup G :=
  ⨆ i ∈ S, ⁅V, X i⁆

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem le_normalizer (hFam : burnsideB610_Fam H T V hV F S X D) {i j : ι} (hi : i ∈ S)
    (hj : j ∈ S) : X j ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G) := by
  by_cases hij : i = j
  · subst hij
    exact Subgroup.le_normalizer
  have key : ∀ y ∈ X j, ∀ x ∈ X i, y * x * y⁻¹ ∈ X i := by
    intro y hy x hx
    have h1 := hFam.comm j hj i hi (Ne.symm hij) y hy x hx
    have hyH := hFam.le j hj hy
    have hxH := hFam.le i hi hx
    have h2 : y * x * y⁻¹ * x⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)) (H.inv_mem hxH)
    have h3 := hFam.cent i hi ⟨h2, h1⟩
    have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact (X i).mul_mem h3 hx
  intro y hy
  exact B6.mem_normalizer_of_forall_mem (fun x hx => key y hy x hx)
    (fun x hx => by simpa using key y⁻¹ ((X j).inv_mem hy) x hx)

theorem iSup_le_normalizer (hFam : burnsideB610_Fam H T V hV F S X D) {i : ι} (hi : i ∈ S) :
    (⨆ j ∈ S, X j) ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G) :=
  iSup₂_le fun _ hj => hFam.le_normalizer hi hj

theorem twoResidual_le_nLV (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {i : ι} (hi : i ∈ S) :
    twoResidual H ≤ nLV (X i) V :=
  fun k hk => ⟨hFam.iSup_le_normalizer hi (hFam.res hk), hHV (twoResidual_le H hk)⟩

theorem commutator_le (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {i : ι} (hi : i ∈ S) : ⁅V, X i⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp ((hFam.le i hi).trans hHV)

theorem famW_le (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) : burnsideB610_famW S X V ≤ V :=
  iSup₂_le fun _ hi => hFam.commutator_le hHV hi

theorem cjSub_famW_le (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {h : G} (hh : h ∈ H) :
    cjSub h (burnsideB610_famW S X V) ≤ burnsideB610_famW S X V := by
  rw [cjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun i hi => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨j, hj, hij⟩ := hFam.conj i hi h hh
  have e : (⁅V, X i⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅V, X j⁆ := by
    rw [← hij, burnsideB610_commutator_cjSub (hHV hh) (X i)]
    rfl
  rw [e]
  exact le_iSup₂_of_le (f := fun j (_ : j ∈ S) => (⁅V, X j⁆ : Subgroup G)) j hj le_rfl

theorem le_normalizer_famW (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer ((burnsideB610_famW S X V : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm (hFam.cjSub_famW_le hHV hh)
  have h1 := cjSub_mono (g := h) (hFam.cjSub_famW_le hHV (H.inv_mem hh))
  rw [cjSub_cjSub_inv] at h1
  exact h1

theorem iSup_le_stab (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    (⨆ i ∈ S, X i) ≤ burnsideB610_stab H V (burnsideB610_famW S X V) hV hHV
      (hFam.le_normalizer_famW hHV) (hFam.famW_le hHV) := by
  refine iSup₂_le fun i hi x hx => ⟨hFam.le i hi hx, fun v hv => ?_⟩
  have h1 : ⁅v, x⁆ ∈ ⁅V, X i⁆ := Subgroup.commutator_mem_commutator hv hx
  have h2 : x * v * x⁻¹ * v⁻¹ = ⁅v, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h2]
  exact (le_iSup₂_of_le (f := fun j (_ : j ∈ S) => (⁅V, X j⁆ : Subgroup G)) i hi le_rfl :
    ⁅V, X i⁆ ≤ burnsideB610_famW S X V) (Subgroup.inv_mem _ h1)

theorem _root_.CFSG.Quasithin.B610T.burnsideB610_pow_conj {b v w : G} (hw : b * v * b⁻¹ = w * v)
    (hbw : b * w = w * b) (hvw : v * w = w * v) :
    ∀ m : ℕ, b ^ m * v * (b ^ m)⁻¹ = w ^ m * v := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hbwm : b * w ^ m * b⁻¹ = w ^ m := by
      have : Commute b (w ^ m) := (Commute.pow_right hbw m)
      rw [this.eq, mul_inv_cancel_right]
    calc b ^ (m + 1) * v * (b ^ (m + 1))⁻¹ = b * (b ^ m * v * (b ^ m)⁻¹) * b⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
      _ = b * (w ^ m * v) * b⁻¹ := by rw [ih]
      _ = (b * w ^ m * b⁻¹) * (b * v * b⁻¹) := by group
      _ = w ^ m * (w * v) := by rw [hbwm, hw]
      _ = w ^ (m + 1) * v := by rw [pow_succ, mul_assoc]

theorem mem_centralizer_of_odd [Finite G] (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {b : G} (hbH : b ∈ H)
    (hbW : b ∈ Subgroup.centralizer ((burnsideB610_famW S X V : Subgroup G) : Set G))
    (hb : Odd (orderOf b)) : b ∈ Subgroup.centralizer (V : Set G) := by
  have hbK : b ∈ twoResidual H := F6.mem_twoResidual_of_odd hbH hb
  have hbst := hFam.iSup_le_stab hHV (hFam.res hbK)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  set w := b * v * b⁻¹ * v⁻¹ with hwdef
  have hwW : w ∈ burnsideB610_famW S X V := hbst.2 v hv
  have hwV : w ∈ V := hFam.famW_le hHV hwW
  have hw : b * v * b⁻¹ = w * v := by rw [hwdef]; group
  have hbw : b * w = w * b := (Subgroup.mem_centralizer_iff.mp hbW w hwW).symm
  have hvw : v * w = w * v := B2F.isElemAbelian_comm hV hv hwV
  have hm := burnsideB610_pow_conj hw hbw hvw (orderOf b)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
  have hwm : w ^ orderOf b = 1 := by
    have := congrArg (fun z => z * v⁻¹) hm
    simpa using this.symm
  obtain ⟨k, hk⟩ := hb
  have hw2 : w ^ 2 = 1 := hV.2 w hwV
  have hw1 : w = 1 := by
    rw [hk, pow_succ, pow_mul, hw2, one_pow, one_mul] at hwm
    exact hwm
  rw [hw1, one_mul] at hw
  calc v * b = b * v * b⁻¹ * b := by rw [hw]
    _ = b * v := by group

theorem faith [Finite G] (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) {g : G} (hg : g ∈ H)
    (hgc : ∀ i ∈ S, g ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) :
    g ∈ Subgroup.centralizer (V : Set G) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set W := burnsideB610_famW S X V with hWdef
  set C : Subgroup G := H ⊓ Subgroup.centralizer (W : Set G) with hCdef
  have hHW := hFam.le_normalizer_famW hHV
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHW hh⟩
  have hpow : ∀ x ∈ C, ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    obtain ⟨a, b, hab, ha, hb, ⟨k, hak⟩, hbodd⟩ := B2F.exists_two_part_odd_part x
    have hzC : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hx
    have hbV := hFam.mem_centralizer_of_odd hHV (hzC hb).1 (hzC hb).2 hbodd
    have hcomm : Commute b a := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Commute.zpow_zpow_self x j i
    refine ⟨k, ?_⟩
    rw [hab, hcomm.mul_pow, hak, mul_one]
    exact Subgroup.pow_mem _ hbV _
  have hCV := hred.2.2.2 C inf_le_left hHC hpow
  refine hCV ⟨hg, ?_⟩
  have hle : W ≤ Subgroup.centralizer ({g} : Set G) := by
    refine iSup₂_le fun i hi w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hgc i hi) w hw).symm
  show g ∈ Subgroup.centralizer (W : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hle hw) g rfl).symm

theorem orbitT [Finite G] {M : Subgroup G} (hFam : burnsideB610_Fam H T V hV F S X D)
    (hMP : MinParabolic H T M) {i j : ι} (hi : i ∈ S) (hj : j ∈ S) :
    ∃ t ∈ T, cjSub t (X i) = X j := by
  obtain ⟨h, hh, hij⟩ := hFam.orbit i hi j hj
  have hT := hMP.isSylow
  have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    hT.1.trans (le_normalizer_twoResidual H)
  have hh' : h ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by
    rw [sup_comm, sup_twoResidual_eq hT]
    exact hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hh'
  obtain ⟨k, hk, t, ht, rfl⟩ := hh'
  obtain ⟨l, hl, htl⟩ := hFam.conj i hi t (hT.1 ht)
  refine ⟨t, ht, ?_⟩
  rw [← hij, ← burnsideB610_cjSub_cjSub, htl,
    burnsideB610_cjSub_eq_of_mem_normalizer (hFam.iSup_le_normalizer hl (hFam.res hk))]

end burnsideB610_Fam

end CFSG.Quasithin.B610T
