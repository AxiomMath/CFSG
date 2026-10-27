module

public import CFSG.Quasithin.H13.L32AL2q

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V K H : Subgroup G}

theorem exists_not1471_of_setup (hF : HypF98 T V L (fsuV1 T V) V H) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G))) :
    ∃ h : ↥((L ⊔ T) ⊔ H), Not1471 T L V H γ γ' g h := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := hF.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic hF.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  obtain ⟨y, hy1, hy2⟩ := exists_stab_smul_eq (γ := F8.γ₁ T L H) hγ₂nb
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H) (G₁ := L ⊔ T) (G₂ := H)).symm
  have hyH : (y : G) ∈ H := by
    have := mem_stab_of_smul_eq hy1
    rwa [stab_γ₁ hF.amalgamHypV.le₂] at this
  exact ⟨y, s, hpos, hle, hyH, γ₂, hγ₂nb, hd, hy2⟩

theorem L2Red.inf_centralizer_qh (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6) (h33 : Lemma14_7_33)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14)
    (R : L2Red G T L V K) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hcase : L2CaseOne G T L V) :
    conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) =
      fsuV1 T V := by
  have hV1U : fsuV1 T V ≤ conjClosure V (A6.g1 T V) :=
    hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)
  have hle : fsuV1 T V ≤
      conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    le_inf hV1U fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer (pCoreOf_le 2 _ hq)) v hv).symm
  have hUN : A6.g1 T V ≤ Subgroup.normalizer (conjClosure V (A6.g1 T V) : Set G) :=
    le_normalizer_conjClosure V _
  have hQN : A6.g1 T V ≤ Subgroup.normalizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hN : A6.g1 T V ≤ Subgroup.normalizer ((conjClosure V (A6.g1 T V) ⊓
      Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_of_forall_conj
      (R := conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G))
      (fun k hk x hx => Subgroup.mem_inf.mpr ⟨
      (Subgroup.mem_normalizer_iff.mp (hUN hk) x).mp hx.1,
      Subgroup.mem_centralizer_iff.mpr fun q hq => by
        have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (A6.g1 T V) := by
          have := (Subgroup.mem_normalizer_iff.mp (hQN (inv_mem hk)) q).mp hq
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hq'
        calc q * (k * x * k⁻¹) = k * ((k⁻¹ * q * k) * x) * k⁻¹ := by group
          _ = k * (x * (k⁻¹ * q * k)) * k⁻¹ := by rw [h1]
          _ = k * x * k⁻¹ * q := by group⟩) hg
  rcases L2Red.irred hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 R hF hcase hle
      inf_le_left hN with h | h
  · exact h
  · exfalso
    have h13322 := stmt13_3_2_two_of h1332
    have hMod := stmtL32NModule_of_inputs h1332 h1334
    obtain ⟨V₂, hV2⟩ := R.S.hyp.exists_V2 h13322 hMod h1222
    have h741 := lemma14_7_4_one R.S.hyp h13322 hMod h13314 hV2
    have hV2C : V₂ ≤ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) := by
      intro v hv
      have : v ∈ conjClosure V (A6.g1 T V) ⊓
          Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) := by
        rw [h]
        exact le_conjClosure V _ (hV2.2.1 hv)
      exact this.2
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hV2C] at h741
    have := hF.card_V₁
    rw [← h741, Subgroup.card_bot] at this
    omega

theorem commutator_sup_eq (hF : HypF98 T V L (fsuV1 T V) V H)
    (hC : conjClosure V H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) = fsuV1 T V)
    {b : G} (hbU : b ∈ conjClosure V H) (hbV : b ∉ fsuV1 T V) :
    ⁅fsuV1 T V ⊔ Subgroup.zpowers b, pCoreOf 2 H⁆ = fsuV1 T V := by
  have hV1U : fsuV1 T V ≤ conjClosure V H := hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)
  have hcomm := hF.toHypF91.commutator_conjClosure_le
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx q hq
    have hxU : x ∈ conjClosure V H := sup_le hV1U (Subgroup.zpowers_le.mpr hbU) hx
    rw [commutatorElement_def]
    exact hcomm x hxU q hq
  · have hbC : b ∉ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun h =>
      hbV (hC ▸ Subgroup.mem_inf.mpr ⟨hbU, h⟩)
    obtain ⟨q, hq, hqb⟩ : ∃ q ∈ pCoreOf 2 H, q * b ≠ b * q := by
      by_contra hall
      push Not at hall
      exact hbC (Subgroup.mem_centralizer_iff.mpr hall)
    have hcm : ⁅b, q⁆ ∈ ⁅fsuV1 T V ⊔ Subgroup.zpowers b, pCoreOf 2 H⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hq
    have hcV : ⁅b, q⁆ ∈ fsuV1 T V := by
      rw [commutatorElement_def]
      exact hcomm b hbU q hq
    have hc1 : ⁅b, q⁆ ≠ 1 := fun h1 =>
      hqb (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact one_mem _
    rw [WrData.eq_of_card_le_two hF.card_V₁.le hv hcV hv1 hc1]
    exact hcm

omit [Finite G] in
theorem centralizer_singleton_eq (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) {z : G}
    (hz : Subgroup.zpowers z = fsuV1 T V) :
    Subgroup.centralizer ({z} : Set G) = A6.g1 T V := by
  have hg1 : A6.g1 T V = Subgroup.centralizer (fsuV1 T V : Set G) :=
    normalizer_eq_centralizer_of_card_eq_two hF.card_V₁
  rw [hg1, ← hz]
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute z x := h.symm
    exact (hc.zpow_left k).eq
  · intro h
    exact (h z (Subgroup.mem_zpowers z)).symm

omit [Finite G] in
theorem centralizer_singleton_conj (c x : G) :
    Subgroup.centralizer ({c * x * c⁻¹} : Set G) =
      Quasithin.conjSub c (Subgroup.centralizer ({x} : Set G)) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Quasithin.mem_conjSub,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [h]
      _ = x * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * y := by group

theorem a114Hyp_of (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hC : conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) =
      fsuV1 T V)
    {z : G} (hz : Subgroup.zpowers z = fsuV1 T V) {c : G}
    (hcU : Quasithin.conjSub c (fsuV1 T V) ≤ conjClosure V (A6.g1 T V))
    (hcU' : Quasithin.conjSub c⁻¹ (fsuV1 T V) ≤ conjClosure V (A6.g1 T V))
    (hne : Quasithin.conjSub c (fsuV1 T V) ≠ fsuV1 T V) :
    A114Hyp (fsuV1 T V ⊔ Quasithin.conjSub c (fsuV1 T V)) z (c * z * c⁻¹) := by
  set V₁ := fsuV1 T V with hV₁
  set U := conjClosure V (A6.g1 T V) with hU
  set Q := pCoreOf 2 (A6.g1 T V) with hQ
  have hV1U : V₁ ≤ U := hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)
  have hUe := hF.F911_3
  have hVYU : V₁ ⊔ Quasithin.conjSub c V₁ ≤ U := sup_le hV1U hcU
  have hzV : z ∈ V₁ := hz ▸ Subgroup.mem_zpowers z
  have hcard1 : Nat.card ↥(Quasithin.conjSub c V₁) = 2 := (card_conjSub _ _).trans hF.card_V₁
  have hz1 : z ≠ 1 := by
    intro h1
    have : V₁ = ⊥ := by rw [← hz, h1, Subgroup.zpowers_one_eq_bot]
    have h2 := hF.card_V₁
    rw [this, Subgroup.card_bot] at h2
    omega
  have hzc : Subgroup.zpowers (c * z * c⁻¹) = Quasithin.conjSub c V₁ := by
    rw [← hz]
    exact (MonoidHom.map_zpowers (MulAut.conj c).toMonoidHom z).symm
  have hinf : V₁ ⊓ Quasithin.conjSub c V₁ = ⊥ := by
    by_contra hb
    apply hne
    have h1 := le_of_card_eq_two_of_inf_ne_bot hF.card_V₁ hb
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard1, hF.card_V₁])).symm
  have haV : c * z * c⁻¹ ∈ Quasithin.conjSub c V₁ := hzc ▸ Subgroup.mem_zpowers _
  have ha1 : c * z * c⁻¹ ≠ 1 := fun h1 => hz1 (by
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group)
  have haV₁ : c * z * c⁻¹ ∉ V₁ := fun h1 => ha1 (by
    have : c * z * c⁻¹ ∈ V₁ ⊓ Quasithin.conjSub c V₁ := Subgroup.mem_inf.mpr ⟨h1, haV⟩
    rwa [hinf, Subgroup.mem_bot] at this)
  have hcard : Nat.card ↥(V₁ ⊔ Quasithin.conjSub c V₁) = 4 := by
    have hN : V₁ ≤ Subgroup.normalizer (Quasithin.conjSub c V₁ : Set G) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcomm : ∀ x ∈ Quasithin.conjSub c V₁, v * x * v⁻¹ = x := fun x hx => by
        rw [F7.isElemAbelian_comm hUe (hV1U hv) (hcU hx), mul_inv_cancel_right]
      constructor
      · intro hx; rw [hcomm x hx]; exact hx
      · intro hx
        have hxU : x ∈ U := by
          have h2 := hcU hx
          have h3 : v⁻¹ * (v * x * v⁻¹) * v = x := by group
          rw [← h3]
          exact mul_mem (mul_mem (inv_mem (hV1U hv)) h2) (hV1U hv)
        have e : v * x * v⁻¹ = x := by
          rw [F7.isElemAbelian_comm hUe (hV1U hv) hxU, mul_inv_cancel_right]
        rw [e] at hx
        exact hx
    have h1 := L32NSet14.card_sup_mul_card_inf hN
    rw [hinf, Subgroup.card_bot, mul_one, hF.card_V₁, hcard1] at h1
    exact h1
  have hQz : twoCoreCentralizer z = Q := by
    rw [twoCoreCentralizer, centralizer_singleton_eq hF hz]
  have hQa : twoCoreCentralizer (c * z * c⁻¹) = Quasithin.conjSub c Q := by
    rw [twoCoreCentralizer, centralizer_singleton_conj, pCoreOf_conjSub,
      centralizer_singleton_eq hF hz]
  have hcomm₁ : ⁅V₁ ⊔ Quasithin.conjSub c V₁, Q⁆ = V₁ := by
    rw [← hzc]
    exact commutator_sup_eq hF hC (hcU haV) haV₁
  have hcomm₂ : ⁅V₁ ⊔ Quasithin.conjSub c V₁, Quasithin.conjSub c Q⁆ = Quasithin.conjSub c V₁ := by
    have hb : c⁻¹ * z * c⁻¹⁻¹ ∈ Quasithin.conjSub c⁻¹ V₁ := by
      rw [Quasithin.mem_conjSub, inv_inv]
      simpa [mul_assoc] using hzV
    have hbV : c⁻¹ * z * c⁻¹⁻¹ ∉ V₁ := by
      intro h1
      apply hne
      have hcz : z ∈ Quasithin.conjSub c V₁ := by
        rw [Quasithin.mem_conjSub]
        simpa using h1
      have h2 : V₁ ⊓ Quasithin.conjSub c V₁ ≠ ⊥ := fun h3 => hz1 (by
        have : z ∈ V₁ ⊓ Quasithin.conjSub c V₁ := Subgroup.mem_inf.mpr ⟨hzV, hcz⟩
        rwa [h3, Subgroup.mem_bot] at this)
      have h4 := le_of_card_eq_two_of_inf_ne_bot hF.card_V₁ h2
      exact (Subgroup.eq_of_le_of_card_ge h4 (by rw [hcard1, hF.card_V₁])).symm
    have hzb : Subgroup.zpowers (c⁻¹ * z * c⁻¹⁻¹) = Quasithin.conjSub c⁻¹ V₁ := by
      rw [← hz]
      exact (MonoidHom.map_zpowers (MulAut.conj c⁻¹).toMonoidHom z).symm
    have h1 := commutator_sup_eq hF hC (hcU' hb) hbV
    rw [hzb] at h1
    have e : V₁ ⊔ Quasithin.conjSub c V₁ =
        Quasithin.conjSub c (V₁ ⊔ Quasithin.conjSub c⁻¹ V₁) := by
      rw [conjSub_sup]
      have e2 : Quasithin.conjSub c (Quasithin.conjSub c⁻¹ V₁) = V₁ := by
        have := conjSub_conjSub_inv c⁻¹ V₁
        rwa [inv_inv] at this
      rw [e2, sup_comm]
    rw [e, conjSub_commutator, h1]
  refine
    { isElemAbelian := F7.isElemAbelian_mono hUe hVYU
      card_eq := hcard
      mem₁ := Subgroup.mem_sup_left hzV
      mem₂ := Subgroup.mem_sup_right haV
      ne_one₁ := hz1
      ne_one₂ := ha1
      ne := fun h1 => haV₁ (h1 ▸ hzV)
      comm₁ := by rw [hQz, hcomm₁, hz]
      comm₂ := by rw [hQa, hcomm₂, hzc] }

end CFSG.Quasithin.H13.L32A.L2
