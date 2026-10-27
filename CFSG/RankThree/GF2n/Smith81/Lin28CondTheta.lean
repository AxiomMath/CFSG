module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondRest

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

namespace RestModel

variable (R : RestModel M Q Z n V₁ V₂)

theorem comm_mem_Z_iff (hx : x ∈ H0 M Z) {q : G} (hq : q ∈ Q) :
    ⁅q, x⁆ ∈ Z ↔ R.φ ⟨x, hx⟩ (R.M₀.π q) = R.M₀.π q := by
  have h := (R.xact x hx).pi_comm R.hyp hx.1 hq
  rw [← R.M₀.π_ker _ (comm_mem_Q R.hyp hx.1 hq), h, sub_eq_zero]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem B_apply_self (hx : x ∈ H0 M Z) (hx2 : x * x = 1)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) (e : R.M₀.E) :
    R.M₀.B e (R.φ ⟨x, hx⟩ e) = 0 := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show e ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
  have h1 := R.φ_mem_W₁ ⟨x, hx⟩ hxn₁ hw₁
  have h2 := R.φ_mem_W₂ ⟨x, hx⟩ hxn₂ hw₂
  have h3 : R.M₀.B w₂ (R.φ ⟨x, hx⟩ w₁) = - R.M₀.B w₁ (R.φ ⟨x, hx⟩ w₂) := by
    have := R.B_inv ⟨x, hx⟩ w₂ (R.φ ⟨x, hx⟩ w₁)
    rw [R.φ_sq ⟨x, hx⟩ hx2] at this
    rw [← this, Tim79.QuadModel.B_comm]
  simp only [map_add, LinearMap.add_apply]
  rw [R.iso₁ _ hw₁ _ h1, R.iso₂ _ hw₂ _ h2, h3]
  ring

theorem comm_eq_of_mem_Nsp (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) {r : G} (hr : r ∈ Q)
    (hπ : R.M₀.π r ∈ R.Nsp hx) : x * r = r * x := by
  have H := R.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hT := smith_1_10 H hs.memM hs.notQ hxZ hx2
  have hA : ∃ k, IsTypeA Q Z k x := by
    refine ⟨Module.finrank R.K (commSpace (R.xact x hx)),
      ⟨H.Q_normal.2 hs.memM, hs.notQ, hxZ⟩,
      card_comm_sup R.gm.card (R.xact x hx) H hs.memM hx2, ?_⟩
    intro q hq
    rw [GM.comm_eq_one_iff R.gm hq (conj_mem_Q H hs.memM hq), (R.xact x hx).hπ q hq]
    exact R.B_apply_self hx hx2 hxn₁ hxn₂ _
  have hc := (hT.out 1 3).mp hA
  have hZle := Z_le_comm H hs.memM hs.notQ hx2 hxZ
  have hr' : r ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) :=
    (R.mem_comm_sup_iff hx hx2).mpr ⟨hr, hπ⟩
  rw [sup_eq_left.mpr hZle] at hr'
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hc hr')).symm

include R in
theorem exists_split (hx : x ∈ H0 M Z) (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) {q : G} (hq : q ∈ Q) (hqZ : ⁅q, x⁆ ∈ Z) :
    ∃ a ∈ V₁, ∃ b ∈ V₂, q = a * b ∧ ⁅a, x⁆ ∈ Z ∧ ⁅b, x⁆ ∈ Z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := R.dec q hq
  have haQ := R.V₁Q ha
  have hbQ := R.V₂Q hb
  have hfix := (R.comm_mem_Z_iff hx hq).mp hqZ
  rw [R.M₀.π_mul a haQ b hbQ, map_add] at hfix
  have hWa : R.M₀.π a ∈ R.W₁ := (R.memW₁ _).mpr (R.M₀.pi_mem_img ha haQ)
  have hWb : R.M₀.π b ∈ R.W₂ := (R.memW₂ _).mpr (R.M₀.pi_mem_img hb hbQ)
  have h1 : R.φ ⟨x, hx⟩ (R.M₀.π a) - R.M₀.π a ∈ R.W₁ :=
    R.W₁.sub_mem (R.φ_mem_W₁ ⟨x, hx⟩ hxn₁ hWa) hWa
  have h2 : R.φ ⟨x, hx⟩ (R.M₀.π b) - R.M₀.π b ∈ R.W₂ :=
    R.W₂.sub_mem (R.φ_mem_W₂ ⟨x, hx⟩ hxn₂ hWb) hWb
  have hsum : (R.φ ⟨x, hx⟩ (R.M₀.π a) - R.M₀.π a) +
      (R.φ ⟨x, hx⟩ (R.M₀.π b) - R.M₀.π b) = 0 := by
    have : (R.φ ⟨x, hx⟩ (R.M₀.π a) - R.M₀.π a) + (R.φ ⟨x, hx⟩ (R.M₀.π b) - R.M₀.π b) =
        (R.φ ⟨x, hx⟩ (R.M₀.π a) + R.φ ⟨x, hx⟩ (R.M₀.π b)) - (R.M₀.π a + R.M₀.π b) := by abel
    rw [this, hfix, sub_self]
  have h3 : R.φ ⟨x, hx⟩ (R.M₀.π a) - R.M₀.π a ∈ R.W₁ ⊓ R.W₂ := by
    refine ⟨h1, ?_⟩
    have : R.φ ⟨x, hx⟩ (R.M₀.π a) - R.M₀.π a = -(R.φ ⟨x, hx⟩ (R.M₀.π b) - R.M₀.π b) :=
      eq_neg_of_add_eq_zero_left hsum
    rw [this]
    exact R.W₂.neg_mem h2
  rw [R.hint, Submodule.mem_bot, sub_eq_zero] at h3
  have h4 : R.φ ⟨x, hx⟩ (R.M₀.π b) = R.M₀.π b := by
    have : R.φ ⟨x, hx⟩ (R.M₀.π b) - R.M₀.π b = 0 := by
      rw [h3, sub_self, zero_add] at hsum
      exact hsum
    exact sub_eq_zero.mp this
  exact ⟨a, ha, b, hb, rfl, (R.comm_mem_Z_iff hx haQ).mpr h3, (R.comm_mem_Z_iff hx hbQ).mpr h4⟩

theorem exists_moved (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    ∃ q ∈ V₁, R.φ ⟨x, hx⟩ (R.M₀.π q) ≠ R.M₀.π q := by
  by_contra hcon
  push Not at hcon
  apply hs.notQ
  refine (R.φker ⟨x, hx⟩).mp ?_
  apply LinearEquiv.ext
  intro e
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show e ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
  have hT1 : ∀ w ∈ R.W₁, R.φ ⟨x, hx⟩ w = w := by
    intro w hw
    obtain ⟨q, hqV, hqQ, rfl⟩ := (R.memW₁ w).mp hw
    exact hcon q hqV
  have hd : R.φ ⟨x, hx⟩ w₂ - w₂ = 0 := by
    have hdW : R.φ ⟨x, hx⟩ w₂ - w₂ ∈ R.W₂ := R.W₂.sub_mem (R.φ_mem_W₂ ⟨x, hx⟩ hxn₂ hw₂) hw₂
    have hall : ∀ f, R.M₀.B (R.φ ⟨x, hx⟩ w₂ - w₂) f = 0 := by
      intro f
      obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp
        (show f ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
      have e1 : R.M₀.B f₁ (R.φ ⟨x, hx⟩ w₂ - w₂) = 0 := by
        have := R.B_inv ⟨x, hx⟩ f₁ w₂
        rw [hT1 f₁ hf₁] at this
        rw [map_sub, this, sub_self]
      have e2 : R.M₀.B f₂ (R.φ ⟨x, hx⟩ w₂ - w₂) = 0 := R.iso₂ _ hf₂ _ hdW
      rw [map_add, Tim79.QuadModel.B_comm _ f₁, Tim79.QuadModel.B_comm _ f₂, e1, e2]
      simp
    exact R.M₀.nondeg _ hall
  rw [map_add, hT1 w₁ hw₁, sub_eq_zero.mp hd]
  rfl

theorem exists_comm_rep' (hx : x ∈ H0 M Z) {y : G} (hyQ : y ∈ Q)
    (hy : R.M₀.π y ∈ R.Nsp hx) : ∃ q ∈ Q, ∃ z₀ ∈ Z, y = ⁅q, x⁆ * z₀ := by
  obtain ⟨u, hu⟩ := (R.mem_Nsp hx _).mp hy
  obtain ⟨q, hq, hπq⟩ := R.M₀.π_surj (-u)
  have h1 : R.M₀.π ⁅q, x⁆ = R.M₀.π y := by
    rw [(R.xact x hx).pi_comm R.hyp hx.1 hq, hπq, ← hu]
    simp [xact, sub_eq_add_neg, add_comm]
  have h2 : y⁻¹ * ⁅q, x⁆ ∈ Z := by
    refine (R.M₀.π_ker _ (Q.mul_mem (Q.inv_mem hyQ) (comm_mem_Q R.hyp hx.1 hq))).mp ?_
    rw [R.M₀.π_mul _ (Q.inv_mem hyQ) _ (comm_mem_Q R.hyp hx.1 hq),
      Tim79.QuadModel.pi_inv R.M₀ hyQ, h1]
    exact neg_add_cancel _
  exact ⟨q, hq, (y⁻¹ * ⁅q, x⁆)⁻¹, Z.inv_mem h2, by group⟩

theorem pi_comm_mem_Nsp (hx : x ∈ H0 M Z) {q : G} (hq : q ∈ Q) :
    R.M₀.π ⁅q, x⁆ ∈ R.Nsp hx := by
  rw [(R.xact x hx).pi_comm R.hyp hx.1 hq]
  refine (R.mem_Nsp hx _).mpr ⟨-(R.M₀.π q), ?_⟩
  simp [xact, sub_eq_add_neg, add_comm]


end RestModel

theorem theta_surj_of_root {V V' : Subgroup G} (R : RestModel M Q Z n V V')
    (S : OddSetup M Q Z B V V')
    (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z) {v : G} (hvV : v ∈ V)
    (hvZ : ⁅v, x⁆ ∈ Z) (hv1 : ⁅v, x⁆ ≠ 1) : ∀ z ∈ Z, ∃ γ ∈ Q, ⁅γ, x⁆ = z := by
  have H := S.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hvQ : v ∈ Q := S.VQ hvV
  have hv1' : v ≠ 1 := by
    rintro rfl
    exact hv1 (by simp)
  have hvZ' : v ∉ Z := by
    intro hvz
    apply hv1
    have h1 : x * v = v * x := mul_inv_eq_iff_eq_mul.mp (hxZ v hvz)
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
  have hcl : InZClass Z v := (S.p31 v hvQ hv1').mpr (Or.inl hvV)
  obtain ⟨g, z₀, hz₀, -, hvg⟩ := hcl
  have hΓ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hvΓ : v ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, hvg]
    simpa [mul_assoc] using hz₀
  obtain ⟨-, hΓQ, hΓZ⟩ := S.root_le_V hΓ hvΓ hvV hvZ'
  have hcΓ : Ctx M Q Z (conjSubgroup g Z) := ⟨H, hΓ, hΓQ, hΓZ⟩
  obtain ⟨b, hb0, -, hline, -, -⟩ := hcΓ.dictB R.gm
  have hTv : R.φ ⟨x, hx⟩ (R.M₀.π v) = R.M₀.π v := (R.comm_mem_Z_iff hx hvQ).mp hvZ
  obtain ⟨s₀, hs₀⟩ := (hline _).mp (R.M₀.pi_mem_img hvΓ hvQ)
  have hπv0 : R.M₀.π v ≠ 0 := fun h => hvZ' ((R.M₀.π_ker v hvQ).mp h)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hπv0 (by rw [hs₀, zero_smul])
  have hTb : R.φ ⟨x, hx⟩ b = b := by
    have h1 : s₀ • R.φ ⟨x, hx⟩ b = s₀ • b := by
      rw [← map_smul, ← hs₀, hTv]
    exact smul_right_injective _ hs₀0 h1
  have hTΓ : ∀ γ ∈ conjSubgroup g Z, ⁅γ, x⁆ ∈ Z := by
    intro γ hγ
    obtain ⟨s, hs⟩ := (hline _).mp (R.M₀.pi_mem_img hγ (hΓQ hγ))
    refine (R.comm_mem_Z_iff hx (hΓQ hγ)).mpr ?_
    rw [hs, map_smul, hTb]
  let ψ : ↥(conjSubgroup g Z) →* ↥Z :=
    { toFun := fun γ => ⟨⁅(γ : G), x⁆, hTΓ γ γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun γ γ' => Subtype.ext (by
        have hγQ : (γ : G) ∈ Q := hΓQ γ.2
        have hw' : ⁅(γ' : G), x⁆ ∈ Z := hTΓ γ' γ'.2
        have hw : ⁅(γ : G), x⁆ ∈ Z := hTΓ γ γ.2
        show ⁅((γ * γ' : ↥(conjSubgroup g Z)) : G), x⁆ = ⁅(γ : G), x⁆ * ⁅(γ' : G), x⁆
        have h1 : (γ : G) * ⁅(γ' : G), x⁆ * (γ : G)⁻¹ = ⁅(γ' : G), x⁆ := by
          rw [← Z_central H hw' hγQ]; group
        have h2 : ⁅(γ : G) * (γ' : G), x⁆ =
            (γ : G) * ⁅(γ' : G), x⁆ * (γ : G)⁻¹ * ⁅(γ : G), x⁆ := by
          simp only [commutatorElement_def]; group
        rw [Subgroup.coe_mul, h2, h1, Z_central H hw' (hZQ hw)]) }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 : ⁅(γ : G), x⁆ = 1 := congrArg Subtype.val hγ
    by_contra hne
    have hγ1 : (γ : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hcomm : Commute x (γ : G) := (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hxN := hΓ.mem_normalizer_of_commute H hγ1 γ.2 hcomm
    have hxv : x * v * x⁻¹ ∈ conjSubgroup g Z := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvΓ
    have hinv : ⁅v, x⁆⁻¹ ∈ conjSubgroup g Z := by
      have e : ⁅v, x⁆⁻¹ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup g Z).mul_mem hxv ((conjSubgroup g Z).inv_mem hvΓ)
    have hbot : Z ⊓ conjSubgroup g Z = ⊥ := by
      refine inf_conjSubgroup_eq_bot_of_isTI H.ti ?_
      intro h
      exact hΓZ h
    have : ⁅v, x⁆⁻¹ ∈ Z ⊓ conjSubgroup g Z := ⟨Z.inv_mem hvZ, hinv⟩
    rw [hbot, Subgroup.mem_bot, inv_eq_one] at this
    exact hv1 this
  have hbij : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le hinj (by rw [hΓ.card_eq])
  intro z hz
  obtain ⟨γ, hγ⟩ := hbij.2 ⟨z, hz⟩
  exact ⟨γ, hΓQ γ.2, congrArg Subtype.val hγ⟩

theorem theta_dichotomy_comm (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x) :
    (∀ z ∈ Z, ∃ q ∈ Q, ⁅q, x⁆ = z) ∨ (∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1) := by
  by_cases hII : ∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1
  · exact Or.inr hII
  left
  push Not at hII
  obtain ⟨q, hq, hqZ, hq1⟩ := hII
  have h12 := smith_1_12 hs
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have hxL := lin_x_mem_Lgen_of_sit hb hc hS hn hs
  obtain ⟨-, -, -, -, -, -, hN₁, hN₂, -, -⟩ := hS.basic
  have hxn₁ := hN₁ hxL
  have hxn₂ := hN₂ hxL
  obtain ⟨R⟩ := exists_restModel hc hS hn
  have S := OddSetup.of_linSetup hc hS (p31_of hb hc hS hn)
  obtain ⟨a, ha, b, hb', rfl, haZ, hbZ⟩ := R.exists_split hx hxn₁ hxn₂ hq hqZ
  by_cases ha1 : ⁅a, x⁆ = 1
  · have hb1 : ⁅b, x⁆ ≠ 1 := by
      intro hb1
      apply hq1
      have e1 := commutatorElement_eq_one_iff_mul_comm.mp ha1
      have e2 := commutatorElement_eq_one_iff_mul_comm.mp hb1
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      calc a * b * x = a * (b * x) := by group
        _ = a * (x * b) := by rw [e2]
        _ = (a * x) * b := by group
        _ = (x * a) * b := by rw [e1]
        _ = x * (a * b) := by group
    exact theta_surj_of_root R.symm S.symm hs hx hb' hbZ hb1
  · exact theta_surj_of_root R S hs hx ha haZ ha1

theorem comm_eq_iff_conj {p z : G} (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hz : z ∈ Z) :
    ⁅p, x⁆ = z ↔ p * x * p⁻¹ = x * z := by
  have h1 : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hxZ z hz)
  rw [h1]
  constructor
  · intro h
    rw [← h]
    simp only [commutatorElement_def]
    group
  · intro h
    rw [commutatorElement_def, h]
    group

theorem sit_theta_dichotomy (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x) :
    (∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') ∨
    (∀ z' ∈ Z, ∀ q ∈ Q, q⁻¹ * x * q = x * z' → z' = 1) := by
  have hxZ := hs.x_cent (smith_1_12 hs)
  rcases theta_dichotomy_comm hb hc hS hn hs with h | h
  · left
    intro z' hz'
    obtain ⟨p, hp, hpz⟩ := h z' hz'
    refine ⟨p⁻¹, Q.inv_mem hp, ?_⟩
    have := (comm_eq_iff_conj hxZ hz').mp hpz
    simpa using this
  · right
    intro z' hz' q hq hqz
    have hp : ⁅q⁻¹, x⁆ = z' := by
      refine (comm_eq_iff_conj hxZ hz').mpr ?_
      simpa using hqz
    have := h q⁻¹ (Q.inv_mem hq) (hp ▸ hz')
    rw [hp] at this
    exact this

end CFSG.RankThree.GF2n.Smith81
