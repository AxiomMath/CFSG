module

public import CFSG.Quasithin.H13.A5S136l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem W4_mul_pact_c234 : W4 * pact c234 W4 * pact c234⁻¹ W4 = E12 := by decide +kernel

theorem W4_mul_pact_c234_inv : W4 * pact c234⁻¹ W4 * pact c234 W4 = E12 := by decide +kernel

theorem coe_conjAct_apply' {G : Type} [Group G] {U : Subgroup G}
    (g : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    ((conjAct U g u : ↥U) : G) = (g : G) * u * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U _ u

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Gv_le_normalizer_Uv :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Uv : Set G) :=
  le_normalizer_conjClosure _ _

theorem Lv_le_Gv : S.Lv ≤ Subgroup.centralizer ({S.v12} : Set G) := by
  rw [Lv, oTwoRes_eq_oTwoUpper]
  exact (oTwoUpper_le _).trans inf_le_right

theorem v12_mem_Uv : S.v12 ∈ S.Uv :=
  S.Vv_le_Uv (S.mem_Vv.2 ⟨S.v12_mem_V, by rw [S.psi_v12]; decide +kernel⟩)

@[expose] noncomputable def vU : ↥S.Uv := ⟨S.v12, S.v12_mem_Uv⟩

theorem apply_vU {a : MulAut ↥S.Uv}
    (ha : a ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) : a S.vU = S.vU := by
  obtain ⟨g, hg, rfl⟩ := ha
  have hgv : (g : G) ∈ Subgroup.centralizer ({S.v12} : Set G) := Subgroup.mem_subgroupOf.mp hg
  apply Subtype.ext
  rw [coe_conjAct_apply']
  have h := Subgroup.mem_centralizer_singleton_iff.mp hgv
  show (g : G) * S.v12 * (g : G)⁻¹ = S.v12
  rw [h, mul_inv_cancel_right]

theorem exists_apply_ne_zU_of_normal {X : Subgroup (MulAut ↥S.Uv)}
    (hXG : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (X : Set (MulAut ↥S.Uv))) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x S.zU ≠ S.zU := by
  by_contra hcon
  push Not at hcon
  apply hX
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  set E : Subgroup G :=
    (MonoidHom.eqLocus (x : ↥S.Uv ≃* ↥S.Uv).toMonoidHom (MonoidHom.id _)).map S.Uv.subtype
    with hE
  have hUE : S.Uv ≤ E := by
    refine conjClosure_le fun g hg w hw => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hgN := S.Gv_le_normalizer_Uv hg
    set c : MulAut ↥S.Uv := conjAct S.Uv ⟨g, hgN⟩ with hcdef
    have hc : c ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
      ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hcx : c⁻¹ * x * c ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hXG (Subgroup.inv_mem _ hc)) x).mp hx
      simpa using this
    have h1 : (c⁻¹ * x * c) S.zU = S.zU := hcon _ hcx
    have h2 : x (c S.zU) = c S.zU := by
      have h3 := congrArg c h1
      simpa [MulAut.mul_apply] using h3
    have h3 : ((c S.zU : ↥S.Uv) : G) = g * S.z * g⁻¹ := coe_conjAct_apply' _ _
    refine ⟨(c S.zU) ^ k, ?_, ?_⟩
    · show (x : ↥S.Uv ≃* ↥S.Uv).toMonoidHom ((c S.zU) ^ k) = (c S.zU) ^ k
      rw [map_zpow]
      exact congrArg (· ^ k) h2
    · show (((c S.zU) ^ k : ↥S.Uv) : G) = g * S.z ^ k * g⁻¹
      rw [Subgroup.coe_zpow, h3, conj_zpow]
  ext u
  obtain ⟨u', hu', hu'eq⟩ := hUE u.2
  have hu'u : u' = u := Subtype.ext hu'eq
  rw [← hu'u, MulAut.one_apply]
  exact congrArg Subtype.val (show x u' = u' from hu')

theorem v12_eq_mul (l : ↥(Subgroup.normalizer (V : Set G)))
    (hl : S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹) :
    S.v12 = S.z * ((l : G) * S.z * (l : G)⁻¹) * ((l : G)⁻¹ * S.z * (l : G)) := by
  have hm1 : (l : G) * S.z * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 _).mp S.z_mem_V
  have hm2 : (l : G)⁻¹ * S.z * (l : G) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (l⁻¹).2 S.z).mp S.z_mem_V
    simpa using this
  have h1 : S.frame.ψ ⟨(l : G) * S.z * (l : G)⁻¹, hm1⟩ = pact (S.frame.ρ l) W4 := by
    rw [← S.psi_z]
    exact S.psi_conj l ⟨S.z, S.z_mem_V⟩
  have h2 : S.frame.ψ ⟨(l : G)⁻¹ * S.z * (l : G), hm2⟩ = pact (S.frame.ρ l)⁻¹ W4 := by
    rw [← S.psi_z, ← map_inv]
    have := S.psi_conj l⁻¹ ⟨S.z, S.z_mem_V⟩
    convert this using 3
    simp
  have hmem : S.z * ((l : G) * S.z * (l : G)⁻¹) * ((l : G)⁻¹ * S.z * (l : G)) ∈ V :=
    V.mul_mem (V.mul_mem S.z_mem_V hm1) hm2
  have key : S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ = S.frame.ψ ⟨_, hmem⟩ := by
    have e : (⟨_, hmem⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ * ⟨_, hm1⟩ * ⟨_, hm2⟩ := rfl
    rw [e, map_mul, map_mul, h1, h2, S.psi_z, S.psi_v12]
    rcases hl with hl | hl
    · rw [hl, W4_mul_pact_c234]
    · rw [hl, inv_inv, W4_mul_pact_c234_inv]
  exact congrArg Subtype.val (S.frame.ψ.injective key)

theorem vU_eq_mul_conjAct (l₀ : ↥(Subgroup.normalizer (V : Set G)))
    (hl₀σ : S.frame.ρ l₀ = c234 ∨ S.frame.ρ l₀ = c234⁻¹)
    (hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G)) :
    S.vU = S.zU * conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU * (conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU := by
  apply Subtype.ext
  have h1 : ((conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU : ↥S.Uv) : G) = (l₀ : G) * S.z * (l₀ : G)⁻¹ :=
    coe_conjAct_apply' _ _
  have h2 : (((conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU : ↥S.Uv) : G) =
      (l₀ : G)⁻¹ * S.z * (l₀ : G) := by
    rw [← map_inv, coe_conjAct_apply']
    show (l₀ : G)⁻¹ * S.z * ((l₀ : G)⁻¹)⁻¹ = _
    rw [inv_inv]
  show S.v12 = S.z * ((conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU : ↥S.Uv) : G) *
    (((conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU : ↥S.Uv) : G)
  rw [h1, h2]
  exact S.v12_eq_mul l₀ hl₀σ

theorem apply_zU_of_odd (hUe : IsElemAbelian 2 S.Uv) {d : MulAut ↥S.Uv} (hd : Odd (orderOf d))
    (hfix : d (d S.zU * S.zU⁻¹) = d S.zU * S.zU⁻¹) : d S.zU = S.zU := by
  obtain ⟨c, hc⟩ : ∃ c, c = d S.zU * S.zU⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hfix
  have hdz : d S.zU = c * S.zU := by rw [hc, inv_mul_cancel_right]
  have hpow : ∀ k : ℕ, (d ^ k) S.zU = c ^ k * S.zU := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, hdz, pow_succ, mul_assoc]
  have hc2 : c ^ 2 = 1 := by
    have h := hUe.2 (c : G) c.2
    exact Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  obtain ⟨j, hj⟩ := hd
  have h1 := hpow (orderOf d)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
  have hc1 : c ^ orderOf d = 1 := by
    have := congrArg (· * S.zU⁻¹) h1
    simpa using this.symm
  have hcc : c = 1 := by
    rw [hj, pow_succ, pow_mul, hc2, one_pow, one_mul] at hc1
    exact hc1
  rw [hdz, hcc, one_mul]

theorem exists_apply_ne_comm_of_odd (hUe : IsElemAbelian 2 S.Uv) {X : Subgroup (MulAut ↥S.Uv)}
    (hXG : X ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hXL : autOn S.Lv S.Uv ≤ Subgroup.normalizer (X : Set (MulAut ↥S.Uv)))
    (hodd : ∀ x ∈ X, Odd (orderOf x)) (hz : ∃ x ∈ X, x S.zU ≠ S.zU) :
    ∃ l ∈ autOn S.Lv S.Uv, ∃ x ∈ X, l (x S.zU * S.zU⁻¹) ≠ x S.zU * S.zU⁻¹ := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : ↥S.Uv, a * b = b * a := fun a b => hUe.1.is_comm.comm a b
  obtain ⟨l₀, hl₀, hl₀σ⟩ := S.exists_Lv_c234
  have hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hl₀)
  set l : MulAut ↥S.Uv := conjAct S.Uv ⟨l₀, hl₀N⟩ with hldef
  have hl : l ∈ autOn S.Lv S.Uv := ⟨⟨l₀, hl₀N⟩, Subgroup.mem_subgroupOf.mpr hl₀, rfl⟩
  have hfixinv : ∀ m ∈ autOn S.Lv S.Uv, ∀ x ∈ X,
      m⁻¹ (x S.zU * S.zU⁻¹) = x S.zU * S.zU⁻¹ := by
    intro m hm x hx
    have h := hcon m hm x hx
    calc m⁻¹ (x S.zU * S.zU⁻¹) = m⁻¹ (m (x S.zU * S.zU⁻¹)) := by rw [h]
      _ = x S.zU * S.zU⁻¹ := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hstep : ∀ m ∈ autOn S.Lv S.Uv, ∀ x ∈ X,
      x (m S.zU) = (x S.zU * S.zU⁻¹) * m S.zU := by
    intro m hm x hx
    have hmX : m⁻¹ * x * m ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hXL (Subgroup.inv_mem _ hm)) x).mp hx
      simpa using this
    obtain ⟨d, hd⟩ : ∃ d, d = x⁻¹ * (m⁻¹ * x * m) := ⟨_, rfl⟩
    have hdX : d ∈ X := hd ▸ X.mul_mem (X.inv_mem hx) hmX
    have hxd : x * d ∈ X := X.mul_mem hx hdX
    have hfix : d (d S.zU * S.zU⁻¹) = d S.zU * S.zU⁻¹ := by
      have e1 : x (d S.zU * S.zU⁻¹) =
          ((x * d) S.zU * S.zU⁻¹) * (x S.zU * S.zU⁻¹)⁻¹ := by
        rw [map_mul, map_inv, MulAut.mul_apply]
        group
      have e2 := hcon m hm d hdX
      have e3 : m⁻¹ (((x * d) S.zU * S.zU⁻¹) * (x S.zU * S.zU⁻¹)⁻¹) =
          ((x * d) S.zU * S.zU⁻¹) * (x S.zU * S.zU⁻¹)⁻¹ := by
        rw [map_mul, map_inv, hfixinv m hm _ hxd, hfixinv m hm _ hx]
      calc d (d S.zU * S.zU⁻¹) = x⁻¹ (m⁻¹ (x (m (d S.zU * S.zU⁻¹)))) := by
            rw [hd]; simp only [MulAut.mul_apply]
        _ = x⁻¹ (m⁻¹ (x (d S.zU * S.zU⁻¹))) := by rw [e2]
        _ = x⁻¹ (x (d S.zU * S.zU⁻¹)) := by rw [e1, e3]
        _ = d S.zU * S.zU⁻¹ := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hdz := S.apply_zU_of_odd hUe (hodd d hdX) hfix
    have hxm : x (m S.zU) = m (x S.zU) := by
      have h1 : (m⁻¹ * x * m) S.zU = x S.zU := by
        have := congrArg x hdz
        rw [hd, MulAut.mul_apply] at this
        simpa [MulAut.mul_apply] using this
      have h2 := congrArg m h1
      simpa [MulAut.mul_apply] using h2
    rw [hxm]
    have e : x S.zU = (x S.zU * S.zU⁻¹) * S.zU := by rw [inv_mul_cancel_right]
    rw [e, map_mul, hcon m hm x hx, inv_mul_cancel_right]
  have hv : S.vU = S.zU * l S.zU * l⁻¹ S.zU := S.vU_eq_mul_conjAct l₀ hl₀σ hl₀N
  apply absurd hz
  push Not
  intro x hx
  have hxv : x S.vU = S.vU := S.apply_vU (hXG hx)
  obtain ⟨c, hc⟩ : ∃ c, c = x S.zU * S.zU⁻¹ := ⟨_, rfl⟩
  have hc2 : c * c = 1 := by
    have h := hUe.2 (c : G) c.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  have e1 := hstep l hl x hx
  have e2 := hstep l⁻¹ (Subgroup.inv_mem _ hl) x hx
  rw [← hc] at e1 e2
  have hxz : x S.zU = c * S.zU := by rw [hc, inv_mul_cancel_right]
  rw [hv, map_mul, map_mul, e1, e2, hxz] at hxv
  have hc1 : c = 1 := by
    let _ : CommGroup ↥S.Uv := { (inferInstance : Group ↥S.Uv) with mul_comm := hcomm }
    have e : c * S.zU * (c * l S.zU) * (c * l⁻¹ S.zU) =
        (c * c) * c * (S.zU * l S.zU * l⁻¹ S.zU) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [e, hc2, one_mul] at hxv
    simpa using hxv
  rw [hxz, hc1, one_mul]

end Setting

end CFSG.Quasithin.H13.A5
