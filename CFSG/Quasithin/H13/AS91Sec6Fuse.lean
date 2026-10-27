module

public import CFSG.Quasithin.H13.AS91Sec6More
public import CFSG.Quasithin.H13.AS91Sec5PlaneCount
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.SteinbergBWZJOvergroup
public import CFSG.Quasithin.Recognition.J2RecGlobal
public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson

public section

namespace CFSG.GroupTheory

open Subgroup

theorem thompsonSubgroup_mem_ambientMaxCardAbelianFamily {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (hcomm : IsMulCommutative (CFSG.Open.thompsonSubgroup P)) :
    CFSG.Open.thompsonSubgroup P ∈ CFSG.ambientMaxCardAbelianFamily P := by
  refine ⟨CFSG.Open.thompsonSubgroup_le_self P, hcomm, ?_⟩
  intro B hBP hB
  obtain ⟨A, hA⟩ := CFSG.maxOrderAbelianFamily_nonempty (G := ↥P)
  have hAmap_le : A.map P.subtype ≤ CFSG.Open.thompsonSubgroup P := by
    rw [CFSG.Open.thompsonSubgroup_eq_ambientOrderThompson P]
    exact Subgroup.map_mono (CFSG.le_orderThompson hA)
  have hAcard : Nat.card ↥(A.map P.subtype) = CFSG.maxAbelianOrder ↥P := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hA.2]
  have hB' : IsMulCommutative ↥(B.subgroupOf P) :=
    CFSG.GroupTheory.ZJ.isMulCommutative_subgroupOf hB
  have hBcard : Nat.card ↥B ≤ CFSG.maxAbelianOrder ↥P := by
    calc Nat.card ↥B = Nat.card ↥(B.subgroupOf P) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv).symm
      _ ≤ CFSG.maxAbelianOrder ↥P := CFSG.card_le_maxAbelianOrder_of_isMulCommutative hB'
  calc Nat.card ↥B ≤ CFSG.maxAbelianOrder ↥P := hBcard
    _ = Nat.card ↥(A.map P.subtype) := hAcard.symm
    _ ≤ Nat.card ↥(CFSG.Open.thompsonSubgroup P) := Subgroup.card_le_of_le hAmap_le

theorem le_thompsonSubgroup_of_isMulCommutative_of_card_eq {G : Type*} [Group G] [Finite G]
    {P A : Subgroup G} (hAP : A ≤ P) (hA : IsMulCommutative A)
    (hJ : IsMulCommutative (CFSG.Open.thompsonSubgroup P))
    (hcard : Nat.card ↥A = Nat.card ↥(CFSG.Open.thompsonSubgroup P)) :
    A ≤ CFSG.Open.thompsonSubgroup P := by
  have hJP := thompsonSubgroup_mem_ambientMaxCardAbelianFamily hJ
  have hAfam : A ∈ CFSG.ambientMaxCardAbelianFamily P := by
    refine ⟨hAP, hA, ?_⟩
    intro B hBP hB
    exact (hJP.2.2 B hBP hB).trans (le_of_eq hcard.symm)
  exact CFSG.le_ambientMaxCardThompson hAfam

theorem mem_normalizer_of_map_conj_inv_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g⁻¹).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc H.map (MulAut.conj g).toMonoidHom
      = (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [h]
    _ = H := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
            MonoidHom.id G := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [hcomp, Subgroup.map_id]

theorem centralizer_le_of_eq_conj {G : Type*} [Group G] {a y k : G} {K : Subgroup G}
    (hkK : k ∈ K) (hcent : Subgroup.centralizer ({a} : Set G) ≤ K)
    (hy : y = k * a * k⁻¹) :
    Subgroup.centralizer ({y} : Set G) ≤ K := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : k⁻¹ * x * k ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hy] at hx
    calc (k⁻¹ * x * k) * a = k⁻¹ * (x * (k * a * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * a * k⁻¹) * x) * k := by rw [hx]
      _ = a * (k⁻¹ * x * k) := by group
  have hxK := hcent hx'
  have hxeq : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  rw [hxeq]
  exact K.mul_mem (K.mul_mem hkK hxK) (K.inv_mem hkK)

end CFSG.GroupTheory

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.LargeExtraspecial CFSG.BenderSuzuki.PFAppendixIII

@[expose] def Stmt6_4Fuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ m ∈ c.G1, m * m = 1 → ∃ g ∈ c.G1, g * m * g⁻¹ ∈ Q z

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem T_le_G1 : (c.T : Subgroup G) ≤ c.G1 :=
  c.T_le.trans (le_inf_iff.mp c.G13_le_inf).1

theorem E_le_SM : c.E ≤ c.S.M := by
  have hG3 : c.G3 = c.S.M := by
    change centralizer ({z} : Set G) = centralizer ({c.S.z} : Set G)
    rw [c.S_z]
  rw [← hG3]
  exact c.E_le_G3

theorem card_Qz (c : Loc49 G z) : Nat.card ↥(Q z) = 2 ^ 13 := by
  have hQG : c.S.QG = Q z := c.S_QG
  rw [← hQG]
  exact (CFSG.LargeExtraspecial.Setting.card_QG_eq_card_Q c.S).trans c.card_Q

theorem card_E_inf_Q : Nat.card ↥(c.E ⊓ Q z) = 2 ^ 7 := by
  have hnorm : ∀ e ∈ c.E, ∀ q ∈ Q z, e * q * e⁻¹ ∈ Q z := by
    intro e he q hq
    have hQG : c.S.QG = Q z := c.S_QG
    exact hQG ▸ c.S.conj_mem_QG (c.E_le_SM he) (hQG.symm ▸ hq)
  have hset := coe_sup_eq_mul_of_normalizes c.E (Q z) hnorm
  have h1 := card_mul_set_mul_card_inf c.E (Q z)
  rw [← hset] at h1
  have h2 : Nat.card ((c.E ⊔ Q z : Subgroup G) : Set G) = 2 ^ 17 := by
    rw [sup_comm, ← c.card_QE]
    rfl
  rw [h2, c.card_E, c.card_Qz] at h1
  have h3 : (2 : ℕ) ^ 17 * Nat.card ↥(c.E ⊓ Q z) = 2 ^ 17 * 2 ^ 7 := by
    rw [h1]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

theorem r1_mem_E (hJ : HypJ4 G z) : c.r₁ ∈ c.E := by
  let W : Submodule (ZMod 2) c.S.Qt := c.S.clSub (c.E ⊓ Q z)
  haveI : Finite c.S.Qt := Finite.of_equiv _ c.ψ.symm.toEquiv
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hsub : c.E ⊓ Q z ≤ Subgroup.zpowers z := by
      intro x hx
      have hxQ : x ∈ c.S.QG := (show c.S.QG = Q z from c.S_QG).symm ▸ hx.2
      have hclW : c.S.cl x ∈ W := c.S.cl_mem_clSub hx hxQ
      have hcl0 : c.S.cl x = 0 := by
        rw [hbot] at hclW
        simpa using hclW
      rcases (c.S.cl_eq_zero_iff hxQ).mp hcl0 with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1, c.S_z]
        exact Subgroup.mem_zpowers z
    have hcard := Subgroup.card_le_of_le hsub
    rw [c.card_E_inf_Q, Nat.card_zpowers, hJ.orderOf_z] at hcard
    norm_num at hcard
  have hfinrank : Module.finrank (ZMod 2) ↥W ≠ 0 := by
    intro h0
    exact hWne (Submodule.finrank_eq_zero.mp h0)
  have hdvd : 2 ∣ Nat.card ↥W := by
    rw [c.S.card_submodule W]
    exact dvd_pow_self 2 hfinrank
  let T : Subgroup G := (c.T : Subgroup G)
  have hG3 : c.G3 = c.S.M := by
    change centralizer ({z} : Set G) = centralizer ({c.S.z} : Set G)
    rw [c.S_z]
  have hTSM : T ≤ c.S.M :=
    (c.T_le.trans (le_inf_iff.mp c.G13_le_inf).2).trans (le_of_eq hG3)
  let inc : ↥T →* ↥c.S.M := Subgroup.inclusion hTSM
  let ρT : ↥T →* ↥c.S.O := c.S.ρ.comp inc
  let act : ↥T → ↥W → ↥W := fun t w => ⟨(ρT t : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w.1, by
    obtain ⟨x, hxX, hxQ, hxw⟩ := c.S.mem_clSub_iff.mp w.2
    have hxE : x ∈ c.E := hxX.1
    rw [← hxw]
    change (c.S.ρ (inc t) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (c.S.cl x) ∈ W
    rw [c.S.ρ_cl (inc t) hxQ]
    have hQG : c.S.QG = Q z := c.S_QG
    refine c.S.cl_mem_clSub ?_ (c.S.conj_mem_QG (hTSM t.2) hxQ)
    exact Subgroup.mem_inf.mpr
      ⟨c.E_normal (t : G) (c.T_le t.2) x hxE, hQG ▸ c.S.conj_mem_QG (hTSM t.2) hxQ⟩⟩
  have hsmul_one : ∀ w : ↥W, act 1 w = w := by
    intro w
    apply Subtype.ext
    change (c.S.ρ (inc 1) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w.1 = w.1
    simp [inc]
  have hsmul_mul : ∀ (t₁ t₂ : ↥T) (w : ↥W), act (t₁ * t₂) w = act t₁ (act t₂ w) := by
    intro t₁ t₂ w
    apply Subtype.ext
    change (c.S.ρ (inc (t₁ * t₂)) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w.1 =
      (c.S.ρ (inc t₁) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
        ((c.S.ρ (inc t₂) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w.1)
    rw [map_mul, map_mul]
    rfl
  letI : MulAction ↥T ↥W :=
    { smul := act, one_smul := hsmul_one, mul_smul := hsmul_mul }
  have hT2 : IsPGroup 2 ↥T := c.T.isPGroup'
  obtain ⟨b, hbfix, hb0⟩ :=
    hT2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W hdvd (by
      intro t
      change act t 0 = 0
      apply Subtype.ext
      change (c.S.ρ (inc t) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (0 : c.S.Qt) = 0
      simp)
  have hvfix : ∀ t : c.S.M, (t : G) ∈ (c.T : Subgroup G) →
      (c.S.ρ t : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) b.1 = b.1 := by
    intro t htT
    let tT : ↥T := ⟨t, htT⟩
    have hb := hbfix tT
    change act tT b = b at hb
    have hinc : inc tT = t := Subtype.ext rfl
    have hval : (c.S.ρ (inc tT) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) b.1 = b.1 :=
      congrArg Subtype.val hb
    rwa [show c.S.ρ (inc tT) = c.S.ρ t from by rw [hinc]] at hval
  have hbne : b.1 ≠ 0 := by
    intro h0
    exact hb0 (Subtype.ext h0.symm)
  have hv : b.1 = c.S.cl c.r₁ := by
    rcases (c.fix_T b.1).mp hvfix with h0 | h1
    · exact absurd h0 hbne
    · exact h1
  have hclW : c.S.cl c.r₁ ∈ W := hv ▸ b.2
  obtain ⟨x, hxX, hxQ, hxcl⟩ := c.S.mem_clSub_iff.mp hclW
  have hr1QG : c.r₁ ∈ c.S.QG := (show c.S.QG = Q z from c.S_QG).symm ▸ c.r₁_mem
  rcases (c.S.cl_eq_cl_iff hxQ hr1QG).mp hxcl with h | h
  · rw [h]
    exact hxX.1
  · rw [h]
    exact c.E.mul_mem hxX.1 (by simpa [c.S_z] using c.z_mem_E)

theorem exists_G1_conj_of_conj_mem_E {g : G} (hg : g * z * g⁻¹ ∈ c.E) :
    ∃ m ∈ c.G1, m * z * m⁻¹ = g * z * g⁻¹ := by
  let P : Subgroup G := c.E.map (MulAut.conj g⁻¹).toMonoidHom
  have hPG3 : P ≤ c.G3 := by
    rintro _ ⟨e, he, rfl⟩
    rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hey : e * (g * z * g⁻¹) = (g * z * g⁻¹) * e :=
      congrArg Subtype.val (c.E_elem.1.is_comm.comm ⟨e, he⟩ ⟨g * z * g⁻¹, hg⟩)
    rw [eq_comm]
    change (MulAut.conj g⁻¹) e * z = z * (MulAut.conj g⁻¹) e
    rw [MulAut.conj_apply, inv_inv]
    calc (g⁻¹ * e * g) * z = g⁻¹ * (e * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * e) * g := by rw [hey]
      _ = z * (g⁻¹ * e * g) := by group
  have hP2 : IsPGroup 2 ↥P :=
    c.E_elem.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom
  have hTH : (c.T : Subgroup G) ≤ c.G3 :=
    c.T_le.trans (le_inf_iff.mp c.G13_le_inf).2
  obtain ⟨c₀, hc₀G3, hc₀P⟩ :=
    CFSG.QuasiDihedralFusion.exists_conj_le_sylow (K := c.G3) (S := c.T) hTH P hPG3 hP2
  let h : G := c₀⁻¹
  let A : Subgroup G := P.map (MulAut.conj c₀).toMonoidHom
  have hAeq : A = c.E.map (MulAut.conj (g * h)⁻¹).toMonoidHom := by
    change P.map (MulAut.conj c₀).toMonoidHom =
      c.E.map (MulAut.conj (g * h)⁻¹).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [P, h, MulAut.conj_apply, mul_assoc]
  have hAcomm : IsMulCommutative ↥A := by
    rw [hAeq]
    exact (CFSG.isMulCommutative_map_mulEquiv_iff (MulAut.conj (g * h)⁻¹) c.E).mpr
      c.E_elem.1
  have hAcard : Nat.card ↥A = Nat.card ↥(CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj (g * h)⁻¹).injective, c.E_eq]
  have hJcomm : IsMulCommutative (CFSG.Open.thompsonSubgroup (c.T : Subgroup G)) := by
    rw [← c.E_eq]
    exact c.E_elem.1
  have hAle : A ≤ c.E := by
    have h := CFSG.GroupTheory.le_thompsonSubgroup_of_isMulCommutative_of_card_eq
      (P := (c.T : Subgroup G)) (A := A) hc₀P hAcomm hJcomm hAcard
    rw [c.E_eq]
    exact h
  have hAE : A = c.E :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, c.E_eq])
  have hnorm : g * h ∈ c.G1 := by
    apply CFSG.GroupTheory.mem_normalizer_of_map_conj_inv_eq
    rw [← hAeq]
    exact hAE
  have hhG3 : h ∈ c.G3 := inv_mem hc₀G3
  have hhz : h * z * h⁻¹ = z := by
    calc h * z * h⁻¹ = h * (h⁻¹ * z * h) * h⁻¹ := by rw [c.G3_comm_z hhG3]
      _ = z := by group
  refine ⟨g * h, hnorm, ?_⟩
  calc (g * h) * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [hhz]

theorem exists_K_conj_z_or_r2 (hJ : HypJ4 G z) (hf : Stmt6_4Fuse)
    {y : G} (hyK : y ∈ c.G1 ⊔ c.G3) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    (∃ k ∈ c.G1 ⊔ c.G3, k * y * k⁻¹ = z) ∨
      ∃ k ∈ c.G1 ⊔ c.G3, k * y * k⁻¹ = c.r₂ := by
  let K : Subgroup G := c.G1 ⊔ c.G3
  have h1K : c.G1 ≤ K := le_sup_left
  have h3K : c.G3 ≤ K := le_sup_right
  have hTK : (c.T : Subgroup G) ≤ K := c.T_le_G1.trans h1K
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hy2)
  obtain ⟨k, hkK, hkW⟩ :=
    CFSG.QuasiDihedralFusion.exists_conj_le_sylow (K := K) (S := c.T) hTK
      (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyK) hW2
  let y' : G := k * y * k⁻¹
  have hy'T : y' ∈ (c.T : Subgroup G) :=
    hkW (Subgroup.mem_map.mpr ⟨y, Subgroup.mem_zpowers y, by simp [y', MulAut.conj_apply]⟩)
  have hy'G1 : y' ∈ c.G1 := c.T_le_G1 hy'T
  have hy'2 : y' * y' = 1 := by
    have h : y' * y' = k * (y * y) * k⁻¹ := by dsimp [y']; group
    rw [h, hy2]
    group
  have hy'1 : y' ≠ 1 := by
    intro h0
    apply hy1
    have h : y = k⁻¹ * y' * k := by dsimp [y']; group
    rw [h, h0]
    group
  obtain ⟨m, hmG1, hqQ⟩ := hf G z hJ c y' hy'G1 hy'2
  let q : G := m * y' * m⁻¹
  have hqform : q = (m * k) * y * (m * k)⁻¹ := by dsimp [q, y']; group
  have hq2 : q * q = 1 := by
    have h : q * q = m * (y' * y') * m⁻¹ := by dsimp [q]; group
    rw [h, hy'2]
    group
  have hq1 : q ≠ 1 := by
    intro h0
    apply hy'1
    have h : y' = m⁻¹ * q * m := by dsimp [q]; group
    rw [h, h0]
    group
  by_cases hqz : q = z
  · left
    refine ⟨m * k, K.mul_mem (h1K hmG1) hkK, ?_⟩
    rw [hqform.symm, hqz]
  · rcases c.conj_or q hqQ hq2 hq1 hqz with ⟨h, hhH, hhq⟩ | ⟨h, hhH, hhq⟩
    · left
      have hr1_mem : c.r₁ ∈ c.E := c.r1_mem_E hJ
      obtain ⟨m₁, hm₁G1, hm₁⟩ :=
        c.exists_G1_conj_of_conj_mem_E (g := c.g₁) (c.r₁_eq ▸ hr1_mem)
      have hm₁' : m₁ * z * m₁⁻¹ = c.r₁ := by rw [hm₁, c.r₁_eq]
      have hk'' : (h * (m * k)) * y * (h * (m * k))⁻¹ = c.r₁ := by
        calc (h * (m * k)) * y * (h * (m * k))⁻¹
            = h * ((m * k) * y * (m * k)⁻¹) * h⁻¹ := by group
          _ = h * q * h⁻¹ := by rw [hqform.symm]
          _ = c.r₁ := hhq
      refine ⟨m₁⁻¹ * (h * (m * k)), ?_, ?_⟩
      · exact K.mul_mem (K.inv_mem (h1K hm₁G1))
          (K.mul_mem (h3K hhH) (K.mul_mem (h1K hmG1) hkK))
      · calc (m₁⁻¹ * (h * (m * k))) * y * (m₁⁻¹ * (h * (m * k)))⁻¹
            = m₁⁻¹ * ((h * (m * k)) * y * (h * (m * k))⁻¹) * m₁ := by group
          _ = m₁⁻¹ * c.r₁ * m₁ := by rw [hk'']
          _ = z := by rw [← hm₁']; group
    · right
      have hk'' : (h * (m * k)) * y * (h * (m * k))⁻¹ = c.r₂ := by
        calc (h * (m * k)) * y * (h * (m * k))⁻¹
            = h * ((m * k) * y * (m * k)⁻¹) * h⁻¹ := by group
          _ = h * q * h⁻¹ := by rw [hqform.symm]
          _ = c.r₂ := hhq
      exact ⟨h * (m * k), K.mul_mem (h3K hhH) (K.mul_mem (h1K hmG1) hkK), hk''⟩

theorem exists_G1_conj_of_isConj_z {s : G} (hsE : s ∈ c.E) (hs : IsConj s z) :
    ∃ m ∈ c.G1, m * z * m⁻¹ = s := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hs
  have hks : k⁻¹ * z * k = s := by rw [← hk]; group
  have hconjE : k⁻¹ * z * (k⁻¹)⁻¹ ∈ c.E := by
    simpa [hks] using hsE
  obtain ⟨m, hmG1, hm⟩ := c.exists_G1_conj_of_conj_mem_E (g := k⁻¹) hconjE
  exact ⟨m, hmG1, by simpa [hks] using hm⟩

theorem not_isConj_z_r2 : ¬ IsConj z c.r₂ := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hgQ : g * z * g⁻¹ ∈ Q z := by
    rw [hg]
    exact c.r₂_mem
  rcases c.conj_z g hgQ with h | ⟨h, hh, hhconj⟩
  · exact c.r₂_ne_z (hg.symm.trans h)
  · exact c.not_conj h hh (hhconj.trans hg)

end Loc49

theorem stmt6_5u_of_fuse (h63 : Stmt6_3) (hf : Stmt6_4Fuse) : Stmt6_5u := by
  intro G _ _ z hJ c
  let K : Subgroup G := c.G1 ⊔ c.G3
  by_contra hKtop
  have hKne : K ≠ ⊤ := hKtop
  obtain ⟨t, htE, ht1, ht_not_conj, -, -, ht_cent⟩ := h63 G z hJ c
  have ht2 : t * t = 1 := by
    have := c.E_elem.2 t htE
    simpa [pow_two] using this
  have htG1 : t ∈ c.G1 := c.E_le_G1 htE
  obtain ⟨g, hgG1, hqQ⟩ := hf G z hJ c t htG1 ht2
  let q : G := g * t * g⁻¹
  have hqQ' : q ∈ Q z := hqQ
  have hq2 : q * q = 1 := by
    have h : q * q = g * (t * t) * g⁻¹ := by dsimp [q]; group
    rw [h, ht2]
    group
  have hq1 : q ≠ 1 := by
    intro h0
    apply ht1
    have h : t = g⁻¹ * q * g := by dsimp [q]; group
    rw [h, h0]
    group
  have hqz : q ≠ z := by
    intro h0
    apply ht_not_conj
    apply c.exists_G1_conj_of_isConj_z htE
    exact isConj_iff.mpr ⟨g, by dsimp [q] at h0; exact h0⟩
  rcases c.conj_or q hqQ' hq2 hq1 hqz with ⟨h, hhH, hhq⟩ | ⟨h, hhH, hhq⟩
  · apply ht_not_conj
    apply c.exists_G1_conj_of_isConj_z htE
    have hq_r1 : IsConj q c.r₁ := isConj_iff.mpr ⟨h, hhq⟩
    have ht_q : IsConj t q := isConj_iff.mpr ⟨g, rfl⟩
    have hr1_z : IsConj c.r₁ z := (isConj_iff.mpr ⟨c.g₁, c.r₁_eq⟩).symm
    exact ht_q.trans (hq_r1.trans hr1_z)
  · have hkK : h * g ∈ K := K.mul_mem (Subgroup.mem_sup_right hhH) (Subgroup.mem_sup_left hgG1)
    have ht_cent_le : Subgroup.centralizer ({t} : Set G) ≤ c.G1 := by
      rw [ht_cent]
      exact inf_le_left
    have hr2_eq : c.r₂ = (h * g) * t * (h * g)⁻¹ := by
      calc c.r₂ = h * q * h⁻¹ := by rw [← hhq]
        _ = h * (g * t * g⁻¹) * h⁻¹ := by dsimp [q]
        _ = (h * g) * t * (h * g)⁻¹ := by group
    have hcent_r2 : Subgroup.centralizer ({c.r₂} : Set G) ≤ K :=
      CFSG.GroupTheory.centralizer_le_of_eq_conj hkK (ht_cent_le.trans le_sup_left) hr2_eq
    have hzK : z ∈ K := Subgroup.mem_sup_left (c.E_le_G1 c.z_mem_E)
    have hzInv : IsInvolution z :=
      ⟨Loc49.z_ne_one hJ, by simpa [pow_two] using c.E_elem.2 z c.z_mem_E⟩
    have hcent : ∀ y ∈ K, IsInvolution y → Subgroup.centralizer ({y} : Set G) ≤ K := by
      intro y hyK hyInv
      have hy2 : y * y = 1 := by simpa [pow_two] using hyInv.2
      have hy1 : y ≠ 1 := hyInv.1
      rcases c.exists_K_conj_z_or_r2 hJ hf hyK hy2 hy1 with ⟨k, hkK', hky⟩ | ⟨k, hkK', hky⟩
      · exact CFSG.GroupTheory.centralizer_le_of_eq_conj (a := z) (K.inv_mem hkK')
          (by change c.G3 ≤ K; exact le_sup_right) (by rw [← hky]; group)
      · exact CFSG.GroupTheory.centralizer_le_of_eq_conj (a := c.r₂) (K.inv_mem hkK') hcent_r2
          (by rw [← hky]; group)
    have hfus : ∀ x ∈ K, ∀ y ∈ K, IsInvolution x → IsConj x y →
        ∃ k ∈ K, k * x * k⁻¹ = y := by
      intro x hxK y hyK hxInv hxy
      have hx2 : x * x = 1 := by simpa [pow_two] using hxInv.2
      have hx1 : x ≠ 1 := hxInv.1
      obtain ⟨kxy, hkxy⟩ := isConj_iff.mp hxy
      have hy2 : y * y = 1 := by
        have h : y * y = kxy * (x * x) * kxy⁻¹ := by rw [← hkxy]; group
        rw [h, hx2]
        group
      have hy1 : y ≠ 1 := by
        intro h0
        apply hx1
        have h : x = kxy⁻¹ * y * kxy := by rw [← hkxy]; group
        rw [h, h0]
        group
      rcases c.exists_K_conj_z_or_r2 hJ hf hxK hx2 hx1 with ⟨kx, hkxK, hkx⟩ | ⟨kx, hkxK, hkx⟩
      · rcases c.exists_K_conj_z_or_r2 hJ hf hyK hy2 hy1 with ⟨ky, hkyK, hky⟩ | ⟨ky, hkyK, hky⟩
        · refine ⟨ky⁻¹ * kx, K.mul_mem (K.inv_mem hkyK) hkxK, ?_⟩
          have hx_eq : x = kx⁻¹ * z * kx := by rw [← hkx]; group
          have hy_eq : y = ky⁻¹ * z * ky := by rw [← hky]; group
          rw [hx_eq, hy_eq]
          group
        · exact absurd ((isConj_iff.mpr ⟨kx, hkx⟩).symm.trans
            (hxy.trans (isConj_iff.mpr ⟨ky, hky⟩))) c.not_isConj_z_r2
      · rcases c.exists_K_conj_z_or_r2 hJ hf hyK hy2 hy1 with ⟨ky, hkyK, hky⟩ | ⟨ky, hkyK, hky⟩
        · exact absurd (((isConj_iff.mpr ⟨kx, hkx⟩).symm.trans
            (hxy.trans (isConj_iff.mpr ⟨ky, hky⟩))).symm) c.not_isConj_z_r2
        · refine ⟨ky⁻¹ * kx, K.mul_mem (K.inv_mem hkyK) hkxK, ?_⟩
          have hx_eq : x = kx⁻¹ * c.r₂ * kx := by rw [← hkx]; group
          have hy_eq : y = ky⁻¹ * c.r₂ * ky := by rw [← hky]; group
          rw [hx_eq, hy_eq]
          group
    have hSE := CFSG.Quasithin.isStronglyEmbedded_of_centralizer_le hKne hzK hzInv hcent hfus
    have hr2Inv : IsInvolution c.r₂ :=
      ⟨c.r₂_ne_one, by simpa [pow_two] using c.r₂_sq⟩
    obtain ⟨k, hk⟩ := hSE.involutions_conjugate (x := z) (y := c.r₂) hzInv hr2Inv
    exact c.not_isConj_z_r2 (isConj_iff.mpr ⟨k⁻¹, by
      simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using hk⟩)

end CFSG.Quasithin.H13.AS91
