module

public import CFSG.Quasithin.H13.L32NLem1444i
public import CFSG.Quasithin.H13.L32NLem1444j
public import CFSG.Quasithin.H13.L32NItems144b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [Finite G]

structure Setup5 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G) : Prop
    extends Setup4 G T L V V₂ g D Q₁ Q₂ where
  set14 : ∃ _ : IsMulCommutative ↥V, L32NSet14.Setting G T L V V₂
  QU : fsuU T V = pCoreOf 2 (l32nH T V)
  K9 : Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) = 9

theorem exists_setup5 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest) (hCTL : Lemma1444CTL) {T L V V₂ : Subgroup G} {g : G}
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5) (hG2 : ¬ LieModel G .G2 0 3 1)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) :
    ∃ (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G), Setup5 G T L V V₂ g D Q₁ Q₂ := by
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  obtain ⟨-, hK9⟩ :=
    lemma1444One_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  exact ⟨D, Q₁, Q₂, S, L14332.exists_setting h1332 h1334 h1222 h hV₂,
    S.U_eq_Q (hCTL G T L V h hext h32 hG2), hK9⟩

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

theorem comm_V_of_basis {z a b x : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) (hxz : Commute x z) (hxa : Commute x a)
    (hxb : Commute x b) : ∀ v ∈ V, Commute x v := by
  obtain ⟨_, S'⟩ := S.set14
  have hV₁ : ∀ v ∈ fsuV1 T V, Commute x v := fun v hv => by
    rcases S'.eq_of_mem_V1 hz hz1 hv with rfl | rfl
    · exact Commute.one_right x
    · exact hxz
  have hV₂ : ∀ v ∈ V₂, Commute x v := fun v hv => by
    rcases S'.mem_V2 ha haV hv with h | h
    · exact hV₁ v h
    · have e : v = a⁻¹ * (a * v) := by group
      rw [e]
      exact hxa.inv_right.mul_right (hV₁ _ h)
  intro v hv
  rcases S'.mem_V hb hbV hv with h | h
  · exact hV₂ v h
  · have e : v = b⁻¹ * (b * v) := by group
    rw [e]
    exact hxb.inv_right.mul_right (hV₂ _ h)

theorem comm_mem_V1 {u v : G} (hu : u ∈ fsuU T V) (hv : v ∈ V) :
    u * v * u⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  rw [← S.zU]
  exact comm_mem_centerOf S.ext _ hu _ (V_le_U hv)

theorem mem_U_of_comm {l : G} (hl : l ∈ L) (hlV : ∀ v ∈ V, l * v * l⁻¹ * v⁻¹ ∈ fsuV1 T V) :
    l ∈ fsuU T V := by
  obtain ⟨_, S'⟩ := S.set14
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S'.exists_basis
  have haV' : a ∈ V := S.plane.1.1 ha
  obtain ⟨ψa, hψa⟩ := S.exists_hom_comm (V_le_U haV')
  obtain ⟨ψb, hψb⟩ := S.exists_hom_comm (V_le_U hb)
  set Ψ := ψa.prod ψb with hΨ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by rw [S.zU, S.card2]
  have hker : Nat.card Ψ.ker ≤ 8 := by
    rw [← S.card8]
    refine Nat.card_le_card_of_injective (fun q => ⟨((q : ↥(pCoreOf 2 (l32nH T V))) : G), ?_⟩) ?_
    · have hq : Ψ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := MonoidHom.mem_ker.mp q.2
      have h1 : ψa (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg Prod.fst hq
      have h2 : ψb (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg Prod.snd hq
      have hcomm : ∀ (ψ : ↥(pCoreOf 2 (l32nH T V)) →* ↥(centerOf (fsuU T V))) (x : G),
          (∀ q, ((ψ q : ↥(centerOf (fsuU T V))) : G) = q * x * (q : G)⁻¹ * x⁻¹) →
          ∀ q, ψ q = 1 → Commute (q : G) x := by
        intro ψ x hψ q hq
        have h := hψ q
        rw [hq] at h
        have h' : (q : G) * x * (q : G)⁻¹ * x⁻¹ = 1 := h.symm
        calc (q : G) * x = (q : G) * x * (q : G)⁻¹ * x⁻¹ * (x * q) := by group
          _ = x * q := by rw [h', one_mul]
      have hqU : ((q : ↥(pCoreOf 2 (l32nH T V))) : G) ∈ fsuU T V :=
        S.QU.ge (q : ↥(pCoreOf 2 (l32nH T V))).2
      have hqz : Commute ((q : ↥(pCoreOf 2 (l32nH T V))) : G) z := by
        have := S.comm_V1 (pCoreOf_le 2 _ (q : ↥(pCoreOf 2 (l32nH T V))).2) hz
        calc ((q : ↥(pCoreOf 2 (l32nH T V))) : G) * z =
            ((q : ↥(pCoreOf 2 (l32nH T V))) : G) * z *
              ((q : ↥(pCoreOf 2 (l32nH T V))) : G)⁻¹ * ((q : ↥(pCoreOf 2 (l32nH T V))) : G) := by
              group
          _ = z * ((q : ↥(pCoreOf 2 (l32nH T V))) : G) := by rw [this]
      exact S.mem_V_of_comm hqU fun v hv =>
        (S.comm_V_of_basis hz hz1 ha haV hb hbV hqz (hcomm ψa a hψa _ h1)
          (hcomm ψb b hψb _ h2) v hv).eq
    · intro x y hxy
      have h : ((x : ↥(pCoreOf 2 (l32nH T V))) : G) = ((y : ↥(pCoreOf 2 (l32nH T V))) : G) :=
        congrArg (fun w : ↥V => (w : G)) hxy
      exact Subtype.ext (Subtype.ext h)
  have hcardQ : Nat.card ↥(pCoreOf 2 (l32nH T V)) = 32 := by rw [← S.QU, S.card32]; norm_num
  have h1 := Subgroup.card_ker_mul_card_range Ψ
  rw [hcardQ] at h1
  have hrange : Ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hle := Subgroup.card_le_card_group Ψ.range
    rw [Nat.card_prod, hZ2] at hle ⊢
    have : 4 ≤ Nat.card Ψ.range := by
      by_contra h
      push Not at h
      have : Nat.card Ψ.ker * Nat.card Ψ.range ≤ 8 * 3 := Nat.mul_le_mul hker (by omega)
      omega
    omega
  have hlz : l * z * l⁻¹ = z := by
    have hz' : z ∈ V := (Subgroup.mem_inf.mp hz).1
    have h0 := hlV z hz'
    have hmem : l * z * l⁻¹ ∈ fsuV1 T V := by
      have : l * z * l⁻¹ = (l * z * l⁻¹ * z⁻¹) * z := by group
      rw [this]
      exact (fsuV1 T V).mul_mem h0 hz
    have hne : l * z * l⁻¹ ≠ 1 := fun h1 => hz1 (by
      calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h1]; group)
    exact S.eq_of_mem_V1 hmem hne hz hz1
  have hεa : l * a * l⁻¹ * a⁻¹ ∈ centerOf (fsuU T V) := by rw [S.zU]; exact hlV a haV'
  have hεb : l * b * l⁻¹ * b⁻¹ ∈ centerOf (fsuU T V) := by rw [S.zU]; exact hlV b hb
  obtain ⟨q, hq⟩ : (⟨⟨_, hεa⟩, ⟨_, hεb⟩⟩ : ↥(centerOf (fsuU T V)) × ↥(centerOf (fsuU T V))) ∈
      Ψ.range := hrange ▸ Subgroup.mem_top _
  have hqa : (q : G) * a * (q : G)⁻¹ * a⁻¹ = l * a * l⁻¹ * a⁻¹ := by
    rw [← hψa q]
    exact congrArg (fun x => ((x.1 : ↥(centerOf (fsuU T V))) : G)) hq
  have hqb : (q : G) * b * (q : G)⁻¹ * b⁻¹ = l * b * l⁻¹ * b⁻¹ := by
    rw [← hψb q]
    exact congrArg (fun x => ((x.2 : ↥(centerOf (fsuU T V))) : G)) hq
  have hqU : (q : G) ∈ fsuU T V := S.QU.ge q.2
  have hqz : (q : G) * z * (q : G)⁻¹ = z :=
    S.comm_V1 (pCoreOf_le 2 _ q.2) hz
  have hcomm : ∀ x : G, (q : G) * x * (q : G)⁻¹ = l * x * l⁻¹ → Commute ((q : G)⁻¹ * l) x := by
    intro x hx
    show (q : G)⁻¹ * l * x = x * ((q : G)⁻¹ * l)
    calc (q : G)⁻¹ * l * x = (q : G)⁻¹ * (l * x * l⁻¹) * l := by group
      _ = (q : G)⁻¹ * ((q : G) * x * (q : G)⁻¹) * l := by rw [hx]
      _ = x * ((q : G)⁻¹ * l) := by group
  have hca : (q : G) * a * (q : G)⁻¹ = l * a * l⁻¹ := by
    have := congrArg (· * a) hqa
    simpa using this
  have hcb : (q : G) * b * (q : G)⁻¹ = l * b * l⁻¹ := by
    have := congrArg (· * b) hqb
    simpa using this
  have hcV := S.comm_V_of_basis hz hz1 ha haV hb hbV (hcomm z (by rw [hqz, hlz]))
    (hcomm a hca) (hcomm b hcb)
  have hqlV : (q : G)⁻¹ * l ∈ V :=
    S.centL.le ⟨L.mul_mem (L.inv_mem (S.U_le_L hqU)) hl,
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hcV v hv).eq.symm⟩
  have e : l = (q : G) * ((q : G)⁻¹ * l) := by group
  rw [e]
  exact (fsuU T V).mul_mem hqU (V_le_U hqlV)

theorem exists_rho_ne {σ : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) :
    ∃ v ∈ V, D.ρ ⟨σ, S.xN hσW⟩ (D.π v) ≠ D.π v := by
  by_contra hall
  push Not at hall
  apply hσQ
  rw [← S.QU]
  refine S.mem_U_of_comm (S.Wg_le_L hσW) fun v hv => ?_
  have h1 := hall v hv
  rw [D.ρ_π _ v (V_le_U hv)] at h1
  have hσv : σ * v * σ⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem (S.xN hσW) (V_le_U hv)
  have h2 := (D.π_eq_iff _ hσv v (V_le_U hv)).mp h1
  have h3 : v⁻¹ * (σ * v * σ⁻¹) ∈ centerOf (fsuU T V) := by
    have := (centerOf (fsuU T V)).inv_mem h2
    simpa using this
  have h4 : (σ * v * σ⁻¹) * (v⁻¹ * (σ * v * σ⁻¹)) * (σ * v * σ⁻¹)⁻¹ = v⁻¹ * (σ * v * σ⁻¹) := by
    rw [Subgroup.mem_centralizer_iff.mp h3.2 _ hσv]
    group
  have h5 : σ * v * σ⁻¹ * v⁻¹ ∈ centerOf (fsuU T V) := by
    rw [show σ * v * σ⁻¹ * v⁻¹ = (σ * v * σ⁻¹) * (v⁻¹ * (σ * v * σ⁻¹)) * (σ * v * σ⁻¹)⁻¹ by group,
      h4]
    exact h3
  rw [← S.zU]
  exact h5

omit S in
theorem mat_no_six : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A ≠ 1 ∨ A = 1 ∨
    B * B * B ≠ 1 ∨ B = 1 ∨ A * B ≠ B * A := by
  decide

omit [Finite G] S in
theorem cN {c : G} (hcK : c ∈ oTwoUpper (l32nH T V)) :
    c ∈ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V (oTwoUpper_le _ hcK)

theorem rho_comm {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hcK : c ∈ oTwoUpper (l32nH T V)) (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    D.ρ ⟨σ, S.xN hσW⟩ * D.ρ ⟨c, cN hcK⟩ = D.ρ ⟨c, cN hcK⟩ * D.ρ ⟨σ, S.xN hσW⟩ := by
  have hcomN : σ * c * σ⁻¹ * c⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V (pCoreOf_le 2 _ hσc)
  have h1 := S.rho_eq_one_of_mem_Q hσc hcomN
  have h2 : D.ρ ⟨σ * c * σ⁻¹ * c⁻¹, hcomN⟩ = D.ρ ⟨σ, S.xN hσW⟩ * D.ρ ⟨c, cN hcK⟩ *
      (D.ρ ⟨σ, S.xN hσW⟩)⁻¹ * (D.ρ ⟨c, cN hcK⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [h2] at h1
  have := congrArg (· * D.ρ ⟨c, cN hcK⟩ * D.ρ ⟨σ, S.xN hσW⟩) h1
  simpa [mul_assoc] using this

theorem not_preserves {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    ¬ ∀ w ∈ D.hat V, D.ρ ⟨c, cN hcK⟩ w ∈ D.hat V := by
  intro hpres
  have : Module.Finite (ZMod 2) ↥(D.hat V) := Module.Finite.of_finite
  set bV : Module.Basis (Fin 2) (ZMod 2) ↥(D.hat V) :=
    Module.finBasisOfFinrankEq (ZMod 2) _ (Setup3.finrank_eq_two S.hatE.2)
  set ρσ := D.ρ ⟨σ, S.xN hσW⟩
  set ρc := D.ρ ⟨c, cN hcK⟩
  have hpσ : ∀ w ∈ D.hat V, ρσ w ∈ D.hat V := fun w hw => S.rho_x_V hσW hw
  set A := LinearMap.toMatrix bV bV (ρσ.toLinearMap.restrict hpσ)
  set B := LinearMap.toMatrix bV bV (ρc.toLinearMap.restrict hpres)
  have hone : ∀ N : ↥(D.hat V) →ₗ[ZMod 2] ↥(D.hat V), LinearMap.toMatrix bV bV N = 1 → N = 1 :=
    fun N hN => (LinearMap.toMatrix bV bV).injective (by rw [hN, LinearMap.toMatrix_one])
  have hσσ : ∀ w, ρσ (ρσ w) = w := S.rho_x_sq hσW
  have hAA : A * A = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one bV]
    congr 1
    ext x
    exact hσσ x
  have hBBB : B * B * B = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one bV]
    congr 1
    ext x
    exact S.rho_cube_of_mem_K hcK (cN hcK) x
  have hAB : A * B = B * A := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
    congr 1
    ext x
    exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ x) (S.rho_comm hσW hcK hσc)
  have hA1 : A ≠ 1 := by
    intro h
    obtain ⟨v, hv, hne⟩ := S.exists_rho_ne hσW hσQ
    have := congrArg (fun N : ↥(D.hat V) →ₗ[ZMod 2] ↥(D.hat V) =>
      ((N ⟨D.π v, L128A.HatU.π_mem_hat D hv (V_le_U hv)⟩ : ↥(D.hat V)) : D.V)) (hone _ h)
    exact hne this
  have hB1 : B ≠ 1 := by
    intro h
    obtain ⟨w, hw, hw0⟩ : ∃ w ∈ D.hat V, w ≠ 0 := by
      by_contra hall
      push Not at hall
      have : D.hat V = ⊥ := (Submodule.eq_bot_iff _).mpr hall
      have h4 := S.hatE.2
      rw [this] at h4
      simp at h4
    have := congrArg (fun N : ↥(D.hat V) →ₗ[ZMod 2] ↥(D.hat V) =>
      ((N ⟨w, hw⟩ : ↥(D.hat V)) : D.V)) (hone _ h)
    exact hw0 (hcfpf w this)
  rcases mat_no_six A B with h | h | h | h | h
  · exact h hAA
  · exact hA1 h
  · exact h hBBB
  · exact hB1 h
  · exact h hAB

theorem hat_inf_conj {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    D.hat V ⊓ D.hat (CFSG.conjugate V c⁻¹) = ⊥ := by
  set ρc := D.ρ ⟨c, cN hcK⟩ with hρc
  have h3 : ∀ w, ρc (ρc (ρc w)) = w := S.rho_cube_of_mem_K hcK (cN hcK)
  rw [eq_bot_iff]
  intro x ⟨hxV, hxc⟩
  rw [Submodule.mem_bot]
  by_contra hx0
  obtain ⟨w, hw, hwU, rfl⟩ := (L128A.HatU.mem_hat D).mp hxc
  obtain ⟨v, hv, rfl⟩ := hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hwU hxV hx0 ⊢
  have hvU : v ∈ fsuU T V := V_le_U hv
  have hx : D.π (c * v * c⁻¹) = ρc (D.π v) := (D.ρ_π ⟨c, cN hcK⟩ v hvU).symm
  rw [hx] at hxV hx0
  set x := ρc (D.π v) with hxdef
  set y := ρc (ρc x) with hydef
  have hy : y = D.π v := by rw [hydef, hxdef, h3]
  have hyV : y ∈ D.hat V := by rw [hy]; exact L128A.HatU.π_mem_hat D hv hvU
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx0
    have : ρc y = ρc 0 := by rw [h0]
    rwa [hydef, h3, map_zero] at this
  have hxy : x ≠ y := by
    intro hxy
    apply hx0
    apply hcfpf
    calc ρc x = ρc y := by rw [hxy]
      _ = x := by rw [hydef, h3]
  have hsum : x + ρc x + y = 0 := by
    apply hcfpf
    rw [map_add, map_add, hydef, h3]
    abel
  have hcx : ρc x = x + y := by
    have h1 : ρc x = -(x + y) := by
      rw [eq_neg_iff_add_eq_zero, ← hsum]
      abel
    rw [h1, neg_add, ZModModule.neg_eq_self x, ZModModule.neg_eq_self y]
  have hli : LinearIndependent (ZMod 2) ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h01 : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
    rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst hy0
    · simp at hst
      exact absurd hst hx0
    · simp only [one_smul] at hst
      exfalso
      apply hxy
      have := eq_neg_of_add_eq_zero_left hst
      rw [this, ZModModule.neg_eq_self]
  have hspan_le : Submodule.span (ZMod 2) (Set.range ![x, y]) ≤ D.hat V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hxV
    · exact hyV
  have : Module.Finite (ZMod 2) ↥(D.hat V) := Module.Finite.of_finite
  have hspan : Submodule.span (ZMod 2) (Set.range ![x, y]) = D.hat V := by
    refine Submodule.eq_of_le_of_finrank_eq hspan_le ?_
    rw [finrank_span_eq_card hli, Setup3.finrank_eq_two S.hatE.2]
    simp
  apply S.not_preserves hσW hσQ hcK hcfpf hσc
  intro u hu
  rw [← hspan] at hu
  have hu' : u ∈ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y := by
    have hle : Submodule.span (ZMod 2) (Set.range ![x, y]) ≤ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact hle hu
  rcases L32NSet14.mem_span_pair_zmod2 hu' with rfl | rfl | rfl | rfl
  · rw [map_zero]; exact (D.hat V).zero_mem
  · rw [hcx]; exact (D.hat V).add_mem hxV hyV
  · rw [hydef, h3]; exact hxV
  · have hcy : ρc y = x := by rw [hydef, h3]
    rw [map_add, hcx, hcy]
    have : x + y + x = y := by
      rw [add_comm x y, add_assoc, ZModModule.add_self, add_zero]
    rw [this]
    exact hyV

omit [Finite G] S in
theorem mem_zpowers_of_sq {w x : G} (hw2 : w * w = 1) (hx : x ∈ Subgroup.zpowers w) :
    x = 1 ∨ x = w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hw2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hw2, one_zpow, one_mul, zpow_one]

theorem exists_complement_U {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    ∃ C : Subgroup G, C ≤ fsuU T V ∧ C ⊓ V = ⊥ ∧ Nat.card C = 4 ∧
      ∀ x ∈ C, σ * x * σ⁻¹ ∈ C := by
  set ρσ := D.ρ ⟨σ, S.xN hσW⟩ with hρσ
  set ρc := D.ρ ⟨c, cN hcK⟩ with hρc
  have hcH : c ∈ l32nH T V := oTwoUpper_le _ hcK
  have hσH : σ ∈ l32nH T V := S.Wg_le_H hσW
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  obtain ⟨v, hv, hne⟩ := S.exists_rho_ne hσW hσQ
  have hvU : v ∈ fsuU T V := V_le_U hv
  set w := c * v * c⁻¹ with hwdef
  have hwU : w ∈ fsuU T V := L128A.HatU.conj_mem (cN hcK) hvU
  have hπw : D.π w = ρc (D.π v) := (D.ρ_π ⟨c, cN hcK⟩ v hvU).symm
  have hcomm := S.rho_comm hσW hcK hσc
  have hmove : ρσ (D.π w) ≠ D.π w := by
    rw [hπw]
    intro h
    apply hne
    have h1 : ρc (ρσ (D.π v)) = ρc (D.π v) := by
      rw [← h]
      exact (congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ (D.π v)) hcomm).symm
    exact ρc.injective h1
  set w' := σ * w * σ⁻¹ with hw'def
  have hw'U : w' ∈ fsuU T V := L128A.HatU.conj_mem (S.xN hσW) hwU
  have hπw' : D.π w' = ρσ (D.π w) := (D.ρ_π ⟨σ, S.xN hσW⟩ w hwU).symm
  have hcσ : c⁻¹ * σ * c ∈ Subgroup.normalizer (V : Set G) := by
    have h1 : c⁻¹ * (σ * c * σ⁻¹ * c⁻¹) * c ∈ pCoreOf 2 (l32nH T V) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf (r := 2) (l32nH T V) ((l32nH T V).inv_mem hcH)) _).mp hσc
      simpa using this
    have h2 : c⁻¹ * (σ * c * σ⁻¹ * c⁻¹) * c ∈ Subgroup.normalizer (V : Set G) := by
      rw [← S.QU] at h1
      exact S.L_le_normV (S.U_le_L h1)
    have e : c⁻¹ * σ * c = c⁻¹ * (σ * c * σ⁻¹ * c⁻¹) * c * σ := by group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem h2 (S.Wg_norm_V hσW)
  have hVc : ∀ x, x ∈ CFSG.conjugate V c⁻¹ ↔ c⁻¹ * x * c ∈ V := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hwVc : w ∈ CFSG.conjugate V c⁻¹ := (hVc w).mpr (by
    rw [hwdef, show c⁻¹ * (c * v * c⁻¹) * c = v by group]
    exact hv)
  have hw'Vc : w' ∈ CFSG.conjugate V c⁻¹ := by
    rw [hVc, hw'def]
    have h1 : c⁻¹ * (σ * w * σ⁻¹) * c = (c⁻¹ * σ * c) * v * (c⁻¹ * σ * c)⁻¹ := by
      rw [hwdef]
      group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hcσ v).mp hv
  have hVc2 : ∀ x ∈ CFSG.conjugate V c⁻¹, x * x = 1 := by
    intro x hx
    have h1 := S.comm_V ((hVc x).mp hx) ((hVc x).mp hx)
    have h2 : (c⁻¹ * x * c) * (c⁻¹ * x * c) = 1 := by
      rw [← pow_two]
      exact S.elem.2 _ ((hVc x).mp hx)
    calc x * x = c * ((c⁻¹ * x * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hVcc : ∀ x ∈ CFSG.conjugate V c⁻¹, ∀ y ∈ CFSG.conjugate V c⁻¹, x * y = y * x := by
    intro x hx y hy
    have h1 := S.comm_V ((hVc x).mp hx) ((hVc y).mp hy)
    calc x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by rw [h1]
      _ = y * x := by group
  have hw2 := hVc2 w hwVc
  have hw'2 := hVc2 w' hw'Vc
  have hww' := hVcc w hwVc w' hw'Vc
  have hπw0 : D.π w ≠ 0 := fun h0 => hmove (by rw [h0, map_zero])
  have hπw'0 : D.π w' ≠ 0 := by
    rw [hπw']
    intro h0
    apply hπw0
    have := congrArg ρσ h0
    rwa [S.rho_x_sq hσW, map_zero] at this
  have hπww' : D.π w ≠ D.π w' := by rw [hπw']; exact fun h => hmove h.symm
  have hw1 : w ≠ 1 := fun h => hπw0 (by rw [h, L128A.HatU.π_one])
  have hw'1 : w' ≠ 1 := fun h => hπw'0 (by rw [h, L128A.HatU.π_one])
  have hww'ne : w ≠ w' := fun h => hπww' (by rw [h])
  set C := Subgroup.zpowers w ⊔ Subgroup.zpowers w' with hCdef
  have hw'N : Subgroup.zpowers w' ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    constructor
    · intro hx
      rcases mem_zpowers_of_sq hw2 hx with rfl | rfl
      · simp
      · rw [show w' * w * w'⁻¹ = w by rw [← hww']; group]
        exact Subgroup.mem_zpowers w
    · intro hx
      have hx' : x = w'⁻¹ * (w' * x * w'⁻¹) * w' := by group
      rcases mem_zpowers_of_sq hw2 hx with h | h
      · rw [hx', h]
        simp
      · rw [hx', h, show w'⁻¹ * w * w' = w by
          rw [show w'⁻¹ = w' from (eq_inv_of_mul_eq_one_left hw'2).symm, ← hww']
          calc w * w' * w' = w * (w' * w') := by group
            _ = w := by rw [hw'2, mul_one]]
        exact Subgroup.mem_zpowers w
  have hmemC : ∀ x ∈ C, x = 1 ∨ x = w ∨ x = w' ∨ x = w * w' := by
    intro x hx
    rw [← SetLike.mem_coe, hCdef,
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hw'N] at hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
    rcases mem_zpowers_of_sq hw2 hx₁ with rfl | rfl <;>
      rcases mem_zpowers_of_sq hw'2 hx₂ with rfl | rfl
    · left; simp
    · right; right; left; simp
    · right; left; simp
    · right; right; right; rfl
  have hCU : C ≤ fsuU T V :=
    sup_le (Subgroup.zpowers_le.mpr hwU) (Subgroup.zpowers_le.mpr hw'U)
  have hww'Vc : w * w' ∈ CFSG.conjugate V c⁻¹ := (CFSG.conjugate V c⁻¹).mul_mem hwVc hw'Vc
  refine ⟨C, hCU, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxV⟩
    rw [Subgroup.mem_bot]
    have hinf := S.hat_inf_conj hσW hσQ hcK hcfpf hσc
    have hzero : ∀ y ∈ CFSG.conjugate V c⁻¹, y ∈ fsuU T V → y ∈ V → D.π y = 0 := by
      intro y hyc hyU hyV
      have h1 : D.π y ∈ D.hat V ⊓ D.hat (CFSG.conjugate V c⁻¹) :=
        ⟨L128A.HatU.π_mem_hat D hyV hyU, L128A.HatU.π_mem_hat D hyc hyU⟩
      rw [hinf] at h1
      exact h1
    rcases hmemC x hxC with h | h | h | h
    · exact h
    · exact absurd (hzero w hwVc hwU (h ▸ hxV)) hπw0
    · exact absurd (hzero w' hw'Vc hw'U (h ▸ hxV)) hπw'0
    · exfalso
      have h1 := hzero (w * w') hww'Vc ((fsuU T V).mul_mem hwU hw'U) (h ▸ hxV)
      rw [D.π_mul _ hwU _ hw'U] at h1
      apply hπww'
      have := eq_neg_of_add_eq_zero_left h1
      rw [this, ZModModule.neg_eq_self]
  ·
    have h := L32NSet14.card_sup_mul_card_inf hw'N
    have hinf : Subgroup.zpowers w' ⊓ Subgroup.zpowers w = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx', hx⟩
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_of_sq hw'2 hx' with h1 | h1
      · exact h1
      · rcases mem_zpowers_of_sq hw2 hx with h2 | h2
        · exact h2
        · exact absurd (h2.symm.trans h1) hww'ne
    have ho : ∀ y : G, y * y = 1 → y ≠ 1 → Nat.card (Subgroup.zpowers y) = 2 := by
      intro y hy2 hy1
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    rw [hinf, Subgroup.card_bot, ho w' hw'2 hw'1, ho w hw2 hw1, sup_comm] at h
    rw [hCdef]
    omega
  ·
    intro x hx
    have hσw' : σ * w' * σ⁻¹ = w := by
      rw [hw'def, hσinv]
      calc σ * (σ * w * σ) * σ = (σ * σ) * w * (σ * σ) := by group
        _ = w := by rw [hσ2]; group
    rcases hmemC x hx with rfl | rfl | rfl | rfl
    · simp
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w')
    · rw [hσw']
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
    · rw [show σ * (w * w') * σ⁻¹ = (σ * w * σ⁻¹) * (σ * w' * σ⁻¹) by group, hσw', ← hw'def,
        ← hww']
      exact C.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers w'))

theorem exists_complement_TL {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    ∃ X₀ : Subgroup G, X₀ ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g ∧ X₀ ⊓ V = ⊥ ∧
      X₀ ⊔ V = fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g := by
  obtain ⟨C, hCU, hCV, hC4, hσC⟩ := S.exists_complement_U hσW hσQ hσ2 hcK hcfpf hσc
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  have hσN : Subgroup.zpowers σ ≤ Subgroup.normalizer (C : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ⟨hσC x, fun hx => ?_⟩)
    have h1 := hσC _ hx
    rwa [show σ * (σ * x * σ⁻¹) * σ⁻¹ = x by
      rw [hσinv]
      calc σ * (σ * x * σ) * σ = (σ * σ) * x * (σ * σ) := by group
        _ = x := by rw [hσ2]; group] at h1
  have hσU : σ ∉ fsuU T V := fun h => hσQ (S.U_le_Q h)
  set X₀ := C ⊔ Subgroup.zpowers σ with hX₀
  have hmem : ∀ x ∈ X₀, ∃ c' ∈ C, x = c' ∨ x = c' * σ := by
    intro x hx
    rw [← SetLike.mem_coe, hX₀, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hσN] at hx
    obtain ⟨c', hc', s, hs, rfl⟩ := hx
    rcases mem_zpowers_of_sq hσ2 hs with rfl | rfl
    · exact ⟨c', hc', Or.inl (mul_one _)⟩
    · exact ⟨c', hc', Or.inr rfl⟩
  have hX₀V : X₀ ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxV⟩
    rw [Subgroup.mem_bot]
    obtain ⟨c', hc', h | h⟩ := hmem x hx
    · have : x ∈ C ⊓ V := ⟨h ▸ hc', hxV⟩
      rw [hCV] at this
      exact this
    · exfalso
      apply hσU
      have e : σ = c'⁻¹ * x := by rw [h]; group
      rw [e]
      exact (fsuU T V).mul_mem ((fsuU T V).inv_mem (hCU hc')) (V_le_U hxV)
  have hX₀T : X₀ ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g :=
    sup_le (hCU.trans le_sup_left) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hσW))
  have hcard8 : Nat.card X₀ = 8 := by
    have h := L32NSet14.card_sup_mul_card_inf hσN
    have hinf : Subgroup.zpowers σ ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxs, hxC⟩
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_of_sq hσ2 hxs with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hCU hxC) hσU
    have hσ1 : σ ≠ 1 := fun h1 => hσU (h1 ▸ (fsuU T V).one_mem)
    have ho : Nat.card (Subgroup.zpowers σ) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
    rw [hinf, Subgroup.card_bot, ho, hC4, sup_comm] at h
    rw [hX₀]
    omega
  refine ⟨X₀, hX₀T, hX₀V, ?_⟩
  have hX₀N : X₀ ≤ Subgroup.normalizer (V : Set G) := hX₀T.trans (S.TL_le_L.trans S.L_le_normV)
  have h := L32NSet14.card_sup_mul_card_inf hX₀N
  rw [hX₀V, Subgroup.card_bot, hcard8, S.card8] at h
  exact Subgroup.eq_of_le_of_card_ge (sup_le hX₀T (V_le_U.trans le_sup_left))
    (by rw [S.card_UWg]; omega)

theorem exists_complement_L {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X₀, hX₀T, hX₀V, hX₀sup⟩ := S.exists_complement_TL hσW hσQ hσ2 hcK hcfpf hσc
  set TL := fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g with hTLdef
  have hTL := S.TL_le_L
  have hVL := S.V_le_L
  have hX₀L : X₀ ≤ L := hX₀T.trans hTL
  set V' := V.subgroupOf L with hV'
  have : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVL).mpr S.L_le_normV
  have : IsMulCommutative ↥V' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (S.comm_V a.2 b.2))⟩⟩
  have hV2 : IsPGroup 2 ↥V' := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    have := S.elem.2 _ x.2
    simpa using this))⟩
  have hcardTL : Nat.card ↥(TL.subgroupOf L) = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, S.card_UWg]
    norm_num
  have hP : IsPGroup 2 ↥(TL.subgroupOf L) := IsPGroup.of_card hcardTL
  have hidx : ¬ 2 ∣ (TL.subgroupOf L).index := by
    have : (TL.subgroupOf L).index = 21 := S.relIndex_TL
    rw [this]
    decide
  set P := hP.toSylow hidx with hPdef
  have hPeq : (P : Subgroup ↥L) = TL.subgroupOf L := rfl
  obtain ⟨X', hX'V, hX'sup⟩ := (CFSG.Quasithin.gaschutz hV2 P).mpr ⟨X₀.subgroupOf L,
    by rw [hPeq]; exact fun x hx => hX₀T hx,
    by
      rw [eq_bot_iff]
      rintro x ⟨hxV, hxX⟩
      have h1 : (x : G) ∈ X₀ ⊓ V := ⟨hxX, hxV⟩
      rw [hX₀V, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext h1),
    by
      rw [hPeq, hV', ← Subgroup.subgroupOf_sup hVL hX₀L, sup_comm, hX₀sup]⟩
  refine ⟨X'.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨x', hx', rfl⟩, hxV⟩
    have h1 : x' ∈ V' ⊓ X' := ⟨hxV, hx'⟩
    rw [hX'V, Subgroup.mem_bot] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · have h1 : (V' ⊔ X').map L.subtype = L := by
      rw [hX'sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [Subgroup.map_sup, hV', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVL] at h1
    rw [sup_comm]
    exact h1

end Setup5

end L1444

end CFSG.Quasithin.H13
