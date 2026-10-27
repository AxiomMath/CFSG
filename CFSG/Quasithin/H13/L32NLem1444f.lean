module

public import CFSG.Quasithin.H13.L32NLem1444e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup3

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup3 G T L V V₂ g D Q₁ Q₂)
include S

theorem V_le_Q : V ≤ pCoreOf 2 (l32nH T V) := by
  intro v hv
  have hvH : v ∈ l32nH T V :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      S.comm_V (S.plane.1.1 (S.plane.2 hw)) hv)
  have hvN : v ∈ Subgroup.normalizer (fsuU T V : Set G) := L14332.l32nH_le_normalizer_fsuU T V hvH
  rw [← S.cHat]
  refine (L14332.rho_eq_one_iff_mem (D := D) hvH hvN).mp ?_
  exact L128A.HatU.rho_eq_one_of_mem D (comm_mem_centerOf S.ext) (V_le_U hv) hvN

theorem mem_V_of_comm {u : G} (hu : u ∈ fsuU T V) (hc : ∀ v ∈ V, u * v = v * u) : u ∈ V := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have hiso := D.isotropic_hat (V_le_U (T := T)) fun a ha b hb => S.comm_V ha hb
  have hle : D.hat V ≤ D.B.orthogonal (D.hat V) := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => hiso w hw y hy
  have hfr : Module.finrank (ZMod 2) ↥(D.hat V) = 2 := finrank_eq_two S.hatE.2
  have hfo : Module.finrank (ZMod 2) ↥(D.B.orthogonal (D.hat V)) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal D.nondegenerate, S.dim, hfr]
  have heq : D.hat V = D.B.orthogonal (D.hat V) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hfo])
  have hπ : D.π u ∈ D.hat V := by
    rw [heq]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => ?_
    have hspan : D.hat V ≤ LinearMap.ker (D.B.flip (D.π u)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨v, ⟨hv, hvU⟩, rfl⟩
      show D.B (D.π v) (D.π u) = 0
      rw [D.B_spec v hvU u hu]
      calc v * u * v⁻¹ * u⁻¹ = (u * v) * v⁻¹ * u⁻¹ := by rw [hc v hv]
        _ = 1 := by group
    have := hspan hw
    rw [LinearMap.mem_ker] at this
    exact this
  obtain ⟨v, hv, hvU, hvu⟩ := (L128A.HatU.mem_hat D).mp hπ
  have hz : v⁻¹ * u ∈ centerOf (fsuU T V) := (D.π_eq_iff v hvU u hu).mp hvu
  rw [S.zU] at hz
  have : u = v * (v⁻¹ * u) := by group
  rw [this]
  exact V.mul_mem hv (S.plane.1.1 (S.plane.2 hz))

theorem exists_invol {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hxQ : x ∉ pCoreOf 2 (l32nH T V)) : ∃ v ∈ V, (x * v) * (x * v) = 1 := by
  obtain ⟨w, hw, rfl⟩ := hxW
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxQ ⊢
  have hwU : w ∈ fsuU T V := hw.1
  have hgV := S.g_normV
  have hw2 : w * w ∈ centerOf (fsuU T V) := by
    rw [← L128A.HatU.π_eq_zero_iff D ((fsuU T V).mul_mem hwU hwU), D.π_mul _ hwU _ hwU]
    exact ZModModule.add_self _
  rcases S.mem_center_iff.mp hw2 with h1 | hz
  · refine ⟨1, V.one_mem, ?_⟩
    calc g⁻¹ * w * g * 1 * (g⁻¹ * w * g * 1) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [h1]; group
  have hnc : ∃ v ∈ V, w * v ≠ v * w := by
    by_contra hall
    push Not at hall
    apply hxQ
    have hwV := S.mem_V_of_comm hwU hall
    refine S.V_le_Q ?_
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgV) w).mp hwV
    simpa using this
  obtain ⟨v, hv, hwv⟩ := hnc
  have hvU : v ∈ fsuU T V := V_le_U hv
  have hc : w⁻¹ * v * w * v⁻¹ ∈ centerOf (fsuU T V) := by
    have := comm_mem_centerOf S.ext _ ((fsuU T V).inv_mem hwU) _ hvU
    rwa [inv_inv] at this
  rcases S.mem_center_iff.mp hc with h1 | hc'
  · exfalso
    apply hwv
    have : v * w = w * v := by
      calc v * w = w * (w⁻¹ * v * w * v⁻¹) * v := by group
        _ = w * v := by rw [h1]; group
    exact this.symm
  have hv2 : v * v = 1 := by rw [← pow_two]; exact S.elem.2 v hv
  have hz2 : S.cfg.z * S.cfg.z = 1 := S.cfg.z_mul_self
  refine ⟨g⁻¹ * v * g, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgV) v).mp hv
    simpa using this
  · have key : w * v * (w * v) = 1 := by
      calc w * v * (w * v) = (w * w) * (w⁻¹ * v * w * v⁻¹) * (v * v) := by group
        _ = 1 := by rw [hz, hc', hv2, hz2, one_mul]
    calc g⁻¹ * w * g * (g⁻¹ * v * g) * (g⁻¹ * w * g * (g⁻¹ * v * g)) =
        g⁻¹ * (w * v * (w * v)) * g := by group
      _ = 1 := by rw [key]; group

theorem V_le_H : V ≤ l32nH T V := fun _ hv =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ hw =>
    S.comm_V (S.plane.1.1 (S.plane.2 hw)) hv)

theorem U_le_H : fsuU T V ≤ l32nH T V :=
  conjClosure_le fun _ hh _ hv =>
    (l32nH T V).mul_mem ((l32nH T V).mul_mem hh (S.V_le_H hv)) ((l32nH T V).inv_mem hh)

theorem U_le_Q : fsuU T V ≤ pCoreOf 2 (l32nH T V) := by
  intro u hu
  have huH : u ∈ l32nH T V := S.U_le_H hu
  have huN : u ∈ Subgroup.normalizer (fsuU T V : Set G) := L14332.l32nH_le_normalizer_fsuU T V huH
  rw [← S.cHat]
  refine (L14332.rho_eq_one_iff_mem (D := D) huH huN).mp ?_
  exact L128A.HatU.rho_eq_one_of_mem D (comm_mem_centerOf S.ext) hu huN

theorem false_of_swap
    (h6 : ∀ A : Subgroup G, A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g →
      IsElemAbelian 2 A → Nat.card A ≤ 8)
    {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
    (hx2 : x * x = 1) (h12 : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₂) (h21 : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₁) :
    False := by
  set z := S.cfg.z with hzdef
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx2).symm
  have hcomm : ∀ q ∈ Q₁, ∀ r ∈ Q₂, q * r = r * q := fun q hq r hr =>
    (Subgroup.mem_centralizer_iff.mp (S.cfg.comm hq) r hr).symm
  have hback : ∀ q : G, x * (x * q * x⁻¹) * x⁻¹ = q := by
    intro q
    rw [hxinv]
    calc x * (x * q * x) * x = (x * x) * q * (x * x) := by group
      _ = q := by rw [hx2]; group
  have hxz : x * z * x⁻¹ = z := by
    have h1 := h12 z S.cfg.z_mem_A
    have h2 := h21 z S.cfg.z_mem_B
    rcases (S.cfg.mem_inf_iff _).mp ⟨h2, h1⟩ with h | h
    · exfalso
      apply S.cfg.z_ne_one
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hzz : z * z = 1 := S.cfg.z_mul_self
  have hq8 : ∀ q ∈ Q₁, q * q = 1 ∨ q * q = z := by
    intro q hq
    obtain ⟨u, rfl⟩ := S.cfg.exists_phiA hq
    have key : ∀ u : Q8SqE9.Q8, u * u = 1 ∨ u * u = QuaternionGroup.a 2 := by decide
    rcases key u with h | h
    · left; rw [← map_mul, h, map_one]
    · right; rw [← map_mul, h]; rfl
  let f : ↥Q₁ →* G :=
    { toFun := fun q => (q : G) * (x * q * x⁻¹)
      map_one' := by simp
      map_mul' := fun q r => by
        simp only [Subgroup.coe_mul]
        have h := hcomm r r.2 _ (h12 q q.2)
        calc (q : G) * r * (x * (q * r) * x⁻¹) = q * (r * (x * q * x⁻¹)) * (x * r * x⁻¹) := by
              group
          _ = q * ((x * q * x⁻¹) * r) * (x * r * x⁻¹) := by rw [h]
          _ = q * (x * q * x⁻¹) * (r * (x * r * x⁻¹)) := by group }
  have hf : ∀ q : ↥Q₁, f q = (q : G) * (x * q * x⁻¹) := fun _ => rfl
  have hfz : ∀ q : ↥Q₁, ((q : G) = 1 ∨ (q : G) = z) → f q = 1 := by
    rintro q (h | h) <;> rw [hf, h]
    · group
    · rw [hxz, hzz]
  have hfker : ∀ q : ↥Q₁, f q = 1 → (q : G) = 1 ∨ (q : G) = z := by
    intro q h1
    rw [hf] at h1
    have h2 : x * q * x⁻¹ = (q : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (q : G)⁻¹ ∈ Q₁ ⊓ Q₂ := ⟨Q₁.inv_mem q.2, h2 ▸ h12 q q.2⟩
    rcases (S.cfg.mem_inf_iff _).mp h3 with h | h
    · left; exact inv_eq_one.mp h
    · right
      calc (q : G) = ((q : G)⁻¹)⁻¹ := (inv_inv _).symm
        _ = z⁻¹ := by rw [h]
        _ = z := inv_eq_of_mul_eq_one_left hzz
  set D₀ := f.range with hD₀
  have hD₀U : D₀ ≤ fsuU T V := by
    rintro _ ⟨q, rfl⟩
    rw [hf]
    exact (fsuU T V).mul_mem (S.Q₁_le q.2) (S.Q₂_le (h12 q q.2))
  have hD₀x : ∀ d ∈ D₀, x * d = d * x := by
    rintro _ ⟨q, rfl⟩
    rw [hf]
    have h := hcomm q q.2 _ (h12 q q.2)
    calc x * (q * (x * q * x⁻¹)) = (x * q * x⁻¹) * (x * (x * q * x⁻¹) * x⁻¹) * x := by group
      _ = (x * q * x⁻¹) * q * x := by rw [hback]
      _ = q * (x * q * x⁻¹) * x := by rw [← h]
  have hD₀z : ∀ d ∈ D₀, z * d = d * z := by
    intro d hd
    exact (S.cfg.z_comm_sup (S.sup ▸ hD₀U hd)).symm
  have hD₀sq : ∀ d ∈ D₀, d * d = 1 := by
    rintro _ ⟨q, rfl⟩
    rw [hf]
    have h := hcomm q q.2 _ (h12 q q.2)
    have e : (q : G) * (x * q * x⁻¹) * (q * (x * q * x⁻¹)) =
        (q * q) * (x * (q * q) * x⁻¹) := by
      calc (q : G) * (x * q * x⁻¹) * (q * (x * q * x⁻¹)) =
          q * ((x * q * x⁻¹) * q) * (x * q * x⁻¹) := by group
        _ = q * (q * (x * q * x⁻¹)) * (x * q * x⁻¹) := by rw [← h]
        _ = (q * q) * (x * (q * q) * x⁻¹) := by group
    rw [e]
    rcases hq8 q q.2 with h1 | h1 <;> rw [h1]
    · group
    · rw [hxz, hzz]
  have hD₀comm : ∀ d ∈ D₀, ∀ d' ∈ D₀, d * d' = d' * d := by
    rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩
    rw [← map_mul, ← map_mul]
    have h1 := comm_mem_centerOf S.ext _ ((fsuU T V).inv_mem (S.Q₁_le q.2)) _
      ((fsuU T V).inv_mem (S.Q₁_le r.2))
    have e : (((r * q)⁻¹ * (q * r) : ↥Q₁) : G) =
        (q : G)⁻¹ * (r : G)⁻¹ * (q : G)⁻¹⁻¹ * (r : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev]
      group
    have hc := S.mem_center_iff.mp (e ▸ h1)
    have h2 : q * r = (r * q) * ((r * q)⁻¹ * (q * r)) := by group
    rw [h2, map_mul, hfz _ hc, mul_one]
  have hzD : z ∉ D₀ := by
    rintro ⟨q, hq⟩
    have hq' : (q : G) * (x * q * x⁻¹) = z := hq
    have h2 : x * q * x⁻¹ = (q : G)⁻¹ * z := by rw [← hq']; group
    have h3 : (q : G)⁻¹ * z ∈ Q₁ ⊓ Q₂ :=
      ⟨Q₁.mul_mem (Q₁.inv_mem q.2) S.cfg.z_mem_A, h2 ▸ h12 q q.2⟩
    have hq1 : (q : G) = 1 ∨ (q : G) = z := by
      rcases (S.cfg.mem_inf_iff _).mp h3 with h | h
      · right
        have h' : (q : G)⁻¹ * z = 1 := h
        calc (q : G) = (q : G) * ((q : G)⁻¹ * z) := by rw [h', mul_one]
          _ = z := by group
      · left
        have h' : (q : G)⁻¹ * z = z := h
        have h'' : (q : G)⁻¹ = 1 := by
          calc (q : G)⁻¹ = (q : G)⁻¹ * z * z⁻¹ := by group
            _ = 1 := by rw [h', mul_inv_cancel]
        exact inv_eq_one.mp h''
    have h4 := hfz q hq1
    exact S.cfg.z_ne_one (hq.symm.trans h4)
  have hker : (f.ker).map Q₁.subtype = centerOf (fsuU T V) := by
    ext a
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact S.mem_center_iff.mpr (hfker q hq)
    · intro ha
      have haQ : a ∈ Q₁ := S.center_le_Q₁ ha
      exact ⟨⟨a, haQ⟩, hfz ⟨a, haQ⟩ (S.mem_center_iff.mp ha), rfl⟩
  have hker2 : Nat.card f.ker = 2 := by
    rw [← Subgroup.card_map_of_injective Q₁.subtype_injective, hker, S.zU, S.card2]
  have hD4 : Nat.card D₀ = 4 := by
    have h : Nat.card f.ker * Nat.card D₀ = Nat.card Q₁ := Subgroup.card_ker_mul_card_range f
    rw [hker2, S.cfg.card_A] at h
    omega
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) S.cfg.z_ne_one
  have hzpow : ∀ a ∈ Subgroup.zpowers z, a = 1 ∨ a = z := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hzz, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hzz, one_zpow, one_mul, zpow_one]
  have hcommB : ∀ a ∈ Subgroup.zpowers z, ∀ d ∈ D₀, a * d = d * a := by
    intro a ha d hd
    rcases hzpow a ha with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hD₀z d hd
  have hinf : Subgroup.zpowers z ⊓ D₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, hd⟩
    rcases hzpow a ha with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hd hzD
  have hcardB := RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcommB
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hzo, hD4] at hcardB
  set A := Subgroup.closure (insert x (insert z (D₀ : Set G))) with hA
  have hmem : ∀ a ∈ insert x (insert z (D₀ : Set G)), a = x ∨ a = z ∨ a ∈ D₀ := by
    intro a ha
    rcases ha with rfl | rfl | ha
    · left; rfl
    · right; left; rfl
    · right; right; exact ha
  have hxz' : x * z = z * x := by
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxz]
  have hpair : (insert x (insert z (D₀ : Set G))).Pairwise Commute := by
    intro a ha b hb _
    show a * b = b * a
    rcases hmem a ha with rfl | rfl | hda <;> rcases hmem b hb with rfl | rfl | hdb
    · rfl
    · exact hxz'
    · exact hD₀x b hdb
    · exact hxz'.symm
    · rfl
    · exact hD₀z b hdb
    · exact (hD₀x a hda).symm
    · exact (hD₀z a hda).symm
    · exact hD₀comm a hda b hdb
  have hAc : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    have haA := ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rw [pow_two]
      rcases hmem a ha with rfl | rfl | hda
      · exact hx2
      · exact hzz
      · exact hD₀sq a hda
    | one => simp
    | mul a b ha hb iha ihb =>
      have ha' : a ∈ A := ha
      have hb' : b ∈ A := hb
      rw [pow_two, show a * b * (a * b) = a * (b * a) * b by group, ← hcommA a ha' b hb',
        show a * (a * b) * b = a ^ 2 * b ^ 2 by rw [pow_two, pow_two]; group, iha ha',
        ihb hb', one_mul]
    | inv a ha iha =>
      rw [inv_pow, iha ha, inv_one]
  have hAle : A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g := by
    rw [Subgroup.closure_le]
    intro a ha
    rcases hmem a ha with rfl | rfl | hda
    · exact Subgroup.mem_sup_right hxW
    · exact Subgroup.mem_sup_left (S.Q₁_le S.cfg.z_mem_A)
    · exact Subgroup.mem_sup_left (hD₀U hda)
  have hBA : Subgroup.zpowers z ⊔ D₀ ≤ A := by
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) ?_
    intro d hd
    exact Subgroup.subset_closure (by simp [hd])
  have hxA : x ∈ A := Subgroup.subset_closure (by simp)
  have hxB : x ∉ Subgroup.zpowers z ⊔ D₀ := fun h =>
    hxQ (S.U_le_Q ((sup_le (Subgroup.zpowers_le.mpr (S.Q₁_le S.cfg.z_mem_A)) hD₀U) h))
  have hcardA : 8 < Nat.card A := by
    have hle := Subgroup.card_le_of_le hBA
    rcases hle.lt_or_eq with h | h
    · omega
    · exfalso
      exact hxB ((Subgroup.eq_of_le_of_card_ge hBA h.symm.le) ▸ hxA)
  have := h6 A hAle ⟨hAc, hA2⟩
  omega

theorem not_swap
    (h6 : ∀ A : Subgroup G, A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g →
      IsElemAbelian 2 A → Nat.card A ≤ 8)
    {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V)) :
    x ∈ Subgroup.normalizer (Q₁ : Set G) ∧ x ∈ Subgroup.normalizer (Q₂ : Set G) := by
  have hxU : ∀ q ∈ Q₁ ⊔ Q₂, x * q * x⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hxW)) q).mp hq
  rcases S.cfg.map_conj_cases hxU with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Q8SqE9.mem_normalizer_of_map_eq h1, Q8SqE9.mem_normalizer_of_map_eq h2⟩
  exfalso
  have hx12 : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₂ := fun q hq => by
    rw [← h1]
    exact ⟨q, hq, by simp⟩
  have hx21 : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₁ := fun q hq => by
    rw [← h2]
    exact ⟨q, hq, by simp⟩
  obtain ⟨v, hv, hxv⟩ := S.exists_invol hxW hxQ
  have hvU : v ∈ Q₁ ⊔ Q₂ := S.sup ▸ V_le_U hv
  have hv₁ : v ∈ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.le_centralizer_iff.mp S.cfg.comm).trans
      (Subgroup.centralizer_le_normalizer _)) hvU
  have hv₂ : v ∈ Subgroup.normalizer (Q₂ : Set G) :=
    sup_le (S.cfg.comm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer hvU
  have hxvW : x * v ∈ CFSG.conjugate (l32nW T V V₂) g :=
    (CFSG.conjugate (l32nW T V V₂) g).mul_mem hxW (S.V_le_Wg hv)
  have hxvQ : x * v ∉ pCoreOf 2 (l32nH T V) := fun h => hxQ (by
    have := (pCoreOf 2 (l32nH T V)).mul_mem h ((pCoreOf 2 (l32nH T V)).inv_mem (S.V_le_Q hv))
    simpa using this)
  refine S.false_of_swap h6 hxvW hxvQ hxv (fun q hq => ?_) (fun q hq => ?_)
  · have h3 : v * q * v⁻¹ ∈ Q₁ := (Subgroup.mem_normalizer_iff.mp hv₁ q).mp hq
    have h4 := hx12 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4
  · have h3 : v * q * v⁻¹ ∈ Q₂ := (Subgroup.mem_normalizer_iff.mp hv₂ q).mp hq
    have h4 := hx21 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4

end Setup3

end L1444

open L1444 in
theorem lemma1444Two_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest) (h14446 : Lemma1444Six) : Lemma1444Two := by
  intro G _ _ T L V h hext h32 hG2 V₂ g hV₂ hgP hgH
  obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup3 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2
    hV₂ hgP hgH
  have h6 := (h14446 G T L V h hext h32 hG2).2 V₂ g hV₂ hgP hgH
  have hQ : ∀ {y : G} (hyH : y ∈ l32nH T V), y ∈ pCoreOf 2 (l32nH T V) →
      (⟨y, hyH⟩ : ↥(l32nH T V)) ∈ CFSG.Open.pCore 2 ↥(l32nH T V) := by
    intro y hyH hy
    obtain ⟨y', hy', hy'y⟩ := hy
    have : y' = ⟨y, hyH⟩ := Subtype.ext hy'y
    rwa [← this]
  refine ⟨S.eq_E, S.card_Wg, ?_, ?_⟩
  · rintro _ ⟨⟨x, hxH⟩, hxW, rfl⟩ hx1 _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hxW' : x ∈ CFSG.conjugate (l32nW T V V₂) g := hxW
    have hxQ : x ∉ pCoreOf 2 (l32nH T V) := fun h1 => hx1 (by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hQ hxH h1)
    obtain ⟨hx₁, hx₂⟩ := S.not_swap h6 hxW' hxQ
    have hinv := S.inv_of_normalizes hxW' hxQ hx₁ hx₂ (k := k) hkK
    have hcH : x * k * x⁻¹ * k ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem hxH hkH)
        ((l32nH T V).inv_mem hxH)) hkH
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V))
        ((⟨x, hxH⟩ : ↥(l32nH T V)) * ⟨k, hkH⟩ * ⟨x, hxH⟩⁻¹ * ⟨k, hkH⟩) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hQ hcH hinv
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  · intro x hxW hxQ
    obtain ⟨hx₁, hx₂⟩ := S.not_swap h6 hxW hxQ
    exact S.card_of_normalizes hxW hxQ hx₁ hx₂

end CFSG.Quasithin.H13
