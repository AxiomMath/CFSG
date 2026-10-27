module

public import CFSG.Quasithin.H13.L32NLem1444l
public import CFSG.Quasithin.H13.L32NLem1444m

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [Finite G]

@[expose] def SplitModel.e {T V V₂ : Subgroup G} {g : G} (M : SplitModel T V V₂ g) : Fin 4 → G :=
  ![M.z, M.a, M.tz, M.ta]

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_pow_eq_one {γ : G} (hγ : γ ∈ l32nH T V) : ∃ n : ℕ, γ ^ n = 1 ∧ ¬ 7 ∣ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos γ).ne'
  have hord : orderOf (γ ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hK : γ ^ 2 ^ k ∈ oTwoUpper (l32nH T V) :=
    mem_oTwoUpper_of_odd ((l32nH T V).pow_mem hγ _) (hord ▸ hm)
  obtain ⟨f, hf⟩ := (pCoreOf_isPGroup 2 (l32nH T V)) ⟨_, S.cube_mem_Q_of_mem_K hK⟩
  have hf' : ((γ ^ 2 ^ k) ^ 3) ^ 2 ^ f = 1 := by
    have := congrArg Subtype.val hf
    simpa using this
  refine ⟨2 ^ k * 3 * 2 ^ f, by rw [pow_mul, pow_mul]; exact hf', fun h7 => ?_⟩
  have hcop : Nat.Coprime 7 (2 ^ k * 3 * 2 ^ f) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
      (by norm_num)) (Nat.Coprime.pow_right _ (by norm_num))
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h7) (by norm_num)

omit [Finite G] S in
theorem comm_of_conj {x y : G} (h : x * y * x⁻¹ = y) : Commute x y := by
  show x * y = y * x
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h]

variable (M : SplitModel T V V₂ g)

theorem z_mem_V : M.z ∈ V := S.plane.1.1 (S.plane.2 M.hz)

theorem a_mem_V : M.a ∈ V := S.plane.1.1 M.ha

theorem e_comm : ∀ i j, Commute (M.e i) (M.e j) := by
  have hza : Commute M.z M.a := S.comm_V (S.z_mem_V M) (S.a_mem_V M)
  have htzz : Commute M.tz M.z := comm_of_conj (M.tz_V₂ _ (S.plane.2 M.hz))
  have htza : Commute M.tz M.a := comm_of_conj (M.tz_V₂ _ M.ha)
  have htaz : Commute M.ta M.z := comm_of_conj (M.ta_V₂ _ (S.plane.2 M.hz))
  have htaa : Commute M.ta M.a := comm_of_conj (M.ta_V₂ _ M.ha)
  have htt : Commute M.tz M.ta := M.tz_ta
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact hza
  · exact htzz.symm
  · exact htaz.symm
  · exact hza.symm
  · exact Commute.refl _
  · exact htza.symm
  · exact htaa.symm
  · exact htzz
  · exact htza
  · exact Commute.refl _
  · exact htt
  · exact htaz
  · exact htaa
  · exact htt.symm
  · exact Commute.refl _

theorem e_sq : ∀ i, M.e i * M.e i = 1 := by
  have hV : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact S.elem.2 v hv
  intro i
  fin_cases i
  · exact hV _ (S.z_mem_V M)
  · exact hV _ (S.a_mem_V M)
  · exact M.tz_sq
  · exact M.ta_sq

theorem e_ind : ∀ v, cp M.e v = 1 → v = 0 :=
  cp_eq_one (K₁ := fsuV1 T V) (K₂ := V) (K₃ := fsuU T V) M.hz1 M.hz M.haV (S.z_mem_V M)
    (S.a_mem_V M) M.htzV (V_le_U (S.z_mem_V M)) (V_le_U (S.a_mem_V M)) M.htz.1 M.htaU

theorem e_inj : Function.Injective (cp M.e) :=
  cp_injective (S.e_comm M) (S.e_sq M) (S.e_ind M)

theorem P_le_U : cpPlane M.e (S.e_comm M) (S.e_sq M) ≤ fsuU T V := by
  rintro _ ⟨v, hv, rfl⟩
  rw [cp_eq_vec _ _ hv, cp_vec, val_zero2, pow_zero, mul_one]
  exact (fsuU T V).mul_mem ((fsuU T V).mul_mem ((fsuU T V).pow_mem (V_le_U (S.z_mem_V M)) _)
    ((fsuU T V).pow_mem (V_le_U (S.a_mem_V M)) _)) ((fsuU T V).pow_mem M.htz.1 _)

theorem P_le_W : cpPlane M.e (S.e_comm M) (S.e_sq M) ≤ l32nW T V V₂ := by
  rintro _ ⟨v, hv, rfl⟩
  rw [cp_eq_vec _ _ hv, cp_vec, val_zero2, pow_zero, mul_one]
  exact (l32nW T V V₂).mul_mem ((l32nW T V V₂).mul_mem
    ((l32nW T V V₂).pow_mem (S.V_le_W (S.z_mem_V M)) _)
    ((l32nW T V V₂).pow_mem (S.V_le_W (S.a_mem_V M)) _)) ((l32nW T V V₂).pow_mem M.htz _)

theorem e_mem_P {i : Fin 4} (hi : i ≠ 3) : M.e i ∈ cpPlane M.e (S.e_comm M) (S.e_sq M) := by
  refine ⟨fun j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j i, ?_, cp_col_one _ _⟩
  simp [Ne.symm hi]

theorem V1_le_P : fsuV1 T V ≤ cpPlane M.e (S.e_comm M) (S.e_sq M) := by
  obtain ⟨_, S'⟩ := S.set14
  intro x hx
  rcases S'.eq_of_mem_V1 M.hz M.hz1 hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact S.e_mem_P M (i := 0) (by decide)

theorem comm_P {x y : G} (hx : x ∈ cpPlane M.e (S.e_comm M) (S.e_sq M))
    (hy : y ∈ cpPlane M.e (S.e_comm M) (S.e_sq M)) : x * y = y * x := by
  obtain ⟨v, -, rfl⟩ := hx
  obtain ⟨w, -, rfl⟩ := hy
  exact cp_comm (S.e_comm M) (S.e_sq M) v w

theorem comm_ta_P {x : G} (hx : x ∈ cpPlane M.e (S.e_comm M) (S.e_sq M)) :
    M.ta * x = x * M.ta := by
  obtain ⟨v, -, rfl⟩ := hx
  have h := cp_comm (S.e_comm M) (S.e_sq M) (fun j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 3) v
  rw [cp_col_one] at h
  exact h

theorem card_P : Nat.card (cpPlane M.e (S.e_comm M) (S.e_sq M)) = 8 :=
  le_antisymm (S.card_le_eight_of_comm (S.P_le_U M) fun _ hx _ hy => S.comm_P M hx hy)
    (card_cpPlane _ _ _ (S.e_inj M))

theorem mem_P_of_comm {u : G} (hu : u ∈ fsuU T V)
    (hc : ∀ p ∈ cpPlane M.e (S.e_comm M) (S.e_sq M), u * p = p * u) :
    u ∈ cpPlane M.e (S.e_comm M) (S.e_sq M) := by
  set P := cpPlane M.e (S.e_comm M) (S.e_sq M) with hPdef
  set B := Subgroup.closure (insert u (P : Set G)) with hBdef
  have hpair : (insert u (P : Set G)).Pairwise Commute := by
    refine Set.pairwise_insert.mpr ⟨fun x hx y hy _ => S.comm_P M hx hy, fun p hp _ =>
      ⟨hc p hp, (hc p hp).symm⟩⟩
  have hB := Subgroup.isMulCommutative_closure hpair
  have hBU : B ≤ fsuU T V := by
    rw [hBdef, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hu
    · exact S.P_le_U M hx
  have hPB : P ≤ B := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have h8 := S.card_le_eight_of_comm hBU fun a ha b hb =>
    congrArg Subtype.val (hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have heq : P = B := Subgroup.eq_of_le_of_card_ge hPB (by rw [S.card_P M]; exact h8)
  rw [heq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem card_hat_P : Nat.card ↥(D.hat (cpPlane M.e (S.e_comm M) (S.e_sq M))) = 4 := by
  have hcard := D.card_eq_mul_range (S.P_le_U M)
  rw [← L14323.card_hat_eq D (S.P_le_U M)] at hcard
  have hZ : cpPlane M.e (S.e_comm M) (S.e_sq M) ⊓ centerOf (fsuU T V) = centerOf (fsuU T V) :=
    inf_eq_right.mpr (by rw [S.zU]; exact S.V1_le_P M)
  rw [hZ, S.zU, S.card2, S.card_P M] at hcard
  omega

theorem ta_swap : (∀ q ∈ Q₁, M.ta * q * M.ta⁻¹ ∈ Q₂) ∧ (∀ q ∈ Q₂, M.ta * q * M.ta⁻¹ ∈ Q₁) := by
  have hc := S.e_comm M
  have h2 := S.e_sq M
  set A := cpRange M.e hc h2 with hAdef
  set UW := fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g with hUW
  have hAle : A ≤ UW := by
    rintro _ ⟨v, rfl⟩
    have hz : M.e 0 ∈ UW := Subgroup.mem_sup_left (V_le_U (S.z_mem_V M))
    have ha : M.e 1 ∈ UW := Subgroup.mem_sup_left (V_le_U (S.a_mem_V M))
    have htz : M.e 2 ∈ UW := Subgroup.mem_sup_left M.htz.1
    have hta : M.e 3 ∈ UW := Subgroup.mem_sup_right M.hta
    exact UW.mul_mem (UW.mul_mem (UW.mul_mem (UW.pow_mem hz _) (UW.pow_mem ha _))
      (UW.pow_mem htz _)) (UW.pow_mem hta _)
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, v, rfl⟩ := x
      obtain ⟨_, w, rfl⟩ := y
      exact cp_comm hc h2 v w
    · rintro _ ⟨v, rfl⟩
      rw [pow_two]
      exact cp_mul_self hc h2 v
  have hns : ¬ ∀ x ∈ CFSG.conjugate (l32nW T V V₂) g, x ∉ pCoreOf 2 (l32nH T V) →
      x ∈ Subgroup.normalizer (Q₁ : Set G) ∧ x ∈ Subgroup.normalizer (Q₂ : Set G) := fun h => by
    have h8 := S.card_le_eight_of_not_swap h hAle hAel
    have h16 : 16 ≤ Nat.card A := card_cpRange M.e hc h2 (S.e_inj M)
    omega
  push Not at hns
  obtain ⟨x, hxW, hxQ, hxN⟩ := hns
  have hxU : ∀ q ∈ Q₁ ⊔ Q₂, x * q * x⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hxW)) q).mp hq
  rcases S.cfg.map_conj_cases hxU with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · exact absurd (Q8SqE9.mem_normalizer_of_map_eq h2')
      (hxN (Q8SqE9.mem_normalizer_of_map_eq h1))
  have hx12 : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₂ := fun q hq => by
    rw [← h1]
    exact ⟨q, hq, by simp⟩
  have hx21 : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₁ := fun q hq => by
    rw [← h2']
    exact ⟨q, hq, by simp⟩
  have hxV : x⁻¹ ∉ V := fun h => hxQ (by
    have := S.V_le_Q ((V).inv_mem h)
    simpa using this)
  have htaV : M.ta ∉ V := fun h => M.htaU (V_le_U h)
  have hv : x⁻¹ * M.ta ∈ V :=
    L32NSet14.mul_mem_of_card_eq_two_mul (W := V) (X := CFSG.conjugate (l32nW T V V₂) g)
      S.V_le_Wg (by rw [S.card_Wg16, S.card8]) (by rw [S.card8]; norm_num)
      ((CFSG.conjugate (l32nW T V V₂) g).inv_mem hxW) M.hta hxV htaV
  set v := x⁻¹ * M.ta with hvdef
  have hvU : v ∈ Q₁ ⊔ Q₂ := S.sup ▸ V_le_U hv
  have hv₁ : v ∈ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.le_centralizer_iff.mp S.cfg.comm).trans
      (Subgroup.centralizer_le_normalizer _)) hvU
  have hv₂ : v ∈ Subgroup.normalizer (Q₂ : Set G) :=
    sup_le (S.cfg.comm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer hvU
  have hta : M.ta = x * v := by rw [hvdef]; group
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [hta, show x * v * q * (x * v)⁻¹ = x * (v * q * v⁻¹) * x⁻¹ by group]
    exact hx12 _ ((Subgroup.mem_normalizer_iff.mp hv₁ q).mp hq)
  · rw [hta, show x * v * q * (x * v)⁻¹ = x * (v * q * v⁻¹) * x⁻¹ by group]
    exact hx21 _ ((Subgroup.mem_normalizer_iff.mp hv₂ q).mp hq)

theorem conj_mem_P {c : G} (hcK : c ∈ oTwoUpper (l32nH T V))
    (hσc : M.ta * c * M.ta⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (h12 : ∀ q ∈ Q₁, M.ta * q * M.ta⁻¹ ∈ Q₂) {p : G}
    (hp : p ∈ cpPlane M.e (S.e_comm M) (S.e_sq M)) :
    c * p * c⁻¹ ∈ cpPlane M.e (S.e_comm M) (S.e_sq M) := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  set P := cpPlane M.e (S.e_comm M) (S.e_sq M) with hPdef
  have hσW := M.hta
  have hσN := S.xN hσW
  set ρσ := D.ρ ⟨M.ta, hσN⟩ with hρσ
  set ρc := D.ρ ⟨c, cN hcK⟩ with hρc
  set F := LinearMap.ker (ρσ.toLinearMap - LinearMap.id) with hFdef
  have hmemF : ∀ w, w ∈ F ↔ ρσ w = w := fun w => by
    rw [hFdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  have hPF : D.hat P ≤ F := fun w hw => by
    obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [hmemF, hρσ, D.ρ_π _ q hqU]
    show D.π (M.ta * q * M.ta⁻¹) = D.π q
    rw [S.comm_ta_P M hq, mul_inv_cancel_right]
  have hFQ : F ⊓ D.hat Q₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwF, hwQ⟩
    have h1 : ρσ w ∈ D.hat Q₂ := by
      obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hwQ
      rw [hρσ, D.ρ_π _ q hqU]
      exact L128A.HatU.π_mem_hat D (h12 q hq) (L128A.HatU.conj_mem hσN hqU)
    rw [(hmemF w).mp hwF] at h1
    have : w ∈ D.hat Q₁ ⊓ D.hat Q₂ := ⟨hwQ, h1⟩
    rwa [S.hat_Q_inf] at this
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq F (D.hat Q₁)
  rw [hFQ, finrank_bot, add_zero, Setup3.finrank_eq_two S.card_hat_Q₁] at hdim
  have hle := Submodule.finrank_le (F ⊔ D.hat Q₁)
  rw [S.dim] at hle
  have hPeq : D.hat P = F := Submodule.eq_of_le_of_finrank_le hPF (by
    rw [Setup3.finrank_eq_two (S.card_hat_P M)]
    omega)
  have hcomm := S.rho_comm hσW hcK hσc
  have hcF : ∀ w ∈ F, ρc w ∈ F := fun w hw => by
    rw [hmemF] at hw ⊢
    have := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) hcomm
    simp only [LinearEquiv.mul_apply] at this
    rw [← hρσ, ← hρc] at this
    rw [this, hw]
  have hpU := S.P_le_U M hp
  have hcpU : c * p * c⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem (cN hcK) hpU
  have h1 : D.π (c * p * c⁻¹) ∈ D.hat P := by
    rw [hPeq, ← D.ρ_π ⟨c, cN hcK⟩ p hpU]
    exact hcF _ (hPF (L128A.HatU.π_mem_hat D hp hpU))
  obtain ⟨p', hp', hp'U, hπ⟩ := (L128A.HatU.mem_hat D).mp h1
  have hz : p'⁻¹ * (c * p * c⁻¹) ∈ centerOf (fsuU T V) := (D.π_eq_iff p' hp'U _ hcpU).mp hπ
  rw [S.zU] at hz
  have := P.mul_mem hp' (S.V1_le_P M hz)
  simpa using this

theorem actsAs_b : ActsAs M.e M.b mB :=
  actsAs_B (S.e_comm M) (S.e_sq M)
    (by show M.b * M.z * M.b⁻¹ = M.z; rw [S.comm_V M.hb (S.z_mem_V M)]; group)
    (by show M.b * M.a * M.b⁻¹ = M.a; rw [S.comm_V M.hb (S.a_mem_V M)]; group) M.b_tz M.b_ta

theorem actsAs_of_mem_U {x : G} (hx : x ∈ fsuU T V) :
    ActsAs M.e x 1 ∨ ActsAs M.e x mB ∨ ActsAs M.e x mU ∨ ActsAs M.e x (mU * mB) := by
  have hc := S.e_comm M
  have h2 := S.e_sq M
  set P := cpPlane M.e hc h2 with hPdef
  have hP1 : ∀ p ∈ P, ActsAs M.e p 1 := fun p hp => actsAs_one_of_comm hc h2 fun i => by
    obtain ⟨v, -, rfl⟩ := hp
    rw [← cp_col_one M.e i]
    exact cp_comm hc h2 _ _
  have hb := S.actsAs_b M
  have hu : ActsAs M.e M.u mU := actsAs_U hc h2 M.u_z M.u_a M.u_tz M.u_ta
  have hbP : M.b⁻¹ ∉ P := fun h => by
    have h' : M.b ∈ P := by simpa using P.inv_mem h
    have hcomm := S.comm_P M h' (S.e_mem_P M (i := 2) (by decide))
    have h3 : M.b * M.tz * M.b⁻¹ = M.tz := by
      show M.b * M.e 2 * M.b⁻¹ = M.e 2
      rw [hcomm]
      group
    rw [M.b_tz] at h3
    exact M.hz1 (by simpa using congrArg (· * M.tz⁻¹) h3)
  have huW : M.u⁻¹ ∉ l32nW T V V₂ := fun h => M.huW (by simpa using (l32nW T V V₂).inv_mem h)
  have hW : Nat.card ↥(l32nW T V V₂) = 2 * Nat.card P := by rw [S.card_W, S.card_P M]
  have hU : Nat.card ↥(fsuU T V) = 2 * Nat.card ↥(l32nW T V V₂) := by
    rw [S.card32, S.card_W]
    norm_num
  have hWP : ∀ w ∈ l32nW T V V₂, ActsAs M.e w 1 ∨ ActsAs M.e w mB := fun w hw => by
    by_cases hwP : w ∈ P
    · exact Or.inl (hP1 w hwP)
    · have hbw := L32NSet14.mul_mem_of_card_eq_two_mul (S.P_le_W M) hW
        (by rw [S.card_P M]; norm_num) ((l32nW T V V₂).inv_mem (S.V_le_W M.hb)) hw hbP hwP
      right
      have h := hb.mul (hP1 _ hbw)
      rwa [mul_one, show M.b * (M.b⁻¹ * w) = w by group] at h
  by_cases hxW : x ∈ l32nW T V V₂
  · rcases hWP x hxW with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hux := L32NSet14.mul_mem_of_card_eq_two_mul (inf_le_left : l32nW T V V₂ ≤ fsuU T V) hU
      (by rw [S.card_W]; norm_num) ((fsuU T V).inv_mem M.huU) hx huW hxW
    have e : M.u * (M.u⁻¹ * x) = x := by group
    rcases hWP _ hux with h | h
    · right; right; left
      have h' := hu.mul h
      rwa [mul_one, e] at h'
    · right; right; right
      have h' := hu.mul h
      rwa [e] at h'

theorem fpf_coords {c : G} (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0) {v w : Fin 4 → ZMod 2} (hv3 : v 3 = 0)
    (hv : ¬ (v 1 = 0 ∧ v 2 = 0)) (hcv : c * cp M.e v * c⁻¹ = cp M.e w) (hw1 : w 1 = v 1)
    (hw2 : w 2 = v 2) (hw3 : w 3 = 0) : False := by
  obtain ⟨_, S'⟩ := S.set14
  have hc := S.e_comm M
  have h2 := S.e_sq M
  have hpU : cp M.e v ∈ fsuU T V := S.P_le_U M ⟨v, hv3, rfl⟩
  have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
  have hk : cp M.e (w + v) ∈ fsuV1 T V := by
    rw [cp_eq_vec _ _ (by simp [hw3, hv3])]
    simp only [Pi.add_apply, hw1, hw2, hxx, cp_vec, val_zero2, pow_zero, mul_one]
    exact (fsuV1 T V).pow_mem M.hz _
  have hkU : cp M.e (w + v) ∈ fsuU T V := by
    rw [← S.zU] at hk
    exact hk.1
  have hcw : cp M.e w = cp M.e (w + v) * cp M.e v := by
    rw [← cp_add hc h2]
    congr 1
    funext i
    simp only [Pi.add_apply, add_assoc, hxx, add_zero]
  have hπ : D.ρ ⟨c, cN hcK⟩ (D.π (cp M.e v)) = D.π (cp M.e v) := by
    rw [D.ρ_π _ _ hpU]
    show D.π (c * cp M.e v * c⁻¹) = D.π (cp M.e v)
    rw [hcv, hcw, D.π_mul _ hkU _ hpU,
      (L128A.HatU.π_eq_zero_iff D hkU).mpr (by rw [S.zU]; exact hk), zero_add]
  have hpZ : cp M.e v ∈ fsuV1 T V := by
    rw [← S.zU]
    exact (L128A.HatU.π_eq_zero_iff D hpU).mp (hcfpf _ hπ)
  rcases S'.eq_of_mem_V1 M.hz M.hz1 hpZ with h | h
  · apply hv
    rw [S.e_ind M v h]
    simp
  · have h' : cp M.e v = cp M.e ![1, 0, 0, 0] := by
      rw [h, cp_vec]
      simp [val_one2]
      rfl
    apply hv
    rw [S.e_inj M h']
    exact ⟨rfl, rfl⟩

theorem false_of_split {X : Subgroup G} (hXL : X ≤ L) (hXV : X ⊓ V = ⊥) (hXsup : X ⊔ V = L) :
    False := by
  obtain ⟨_, S'⟩ := S.set14
  obtain ⟨M⟩ := S.exists_splitModel hXL hXV hXsup
  have hc := S.e_comm M
  have h2 := S.e_sq M
  set P := cpPlane M.e hc h2 with hPdef
  obtain ⟨h12, h21⟩ := S.ta_swap M
  obtain ⟨c, hcK, hc3, hcfpf, hσc⟩ := S.exists_c0 S.K9 (S.Wg_le_H M.hta) M.ta_sq h12 h21
  have hcfpf' : ∀ w, D.ρ ⟨c, cN hcK⟩ w = w → w = 0 := hcfpf (cN hcK)
  have hcH : c ∈ l32nH T V := oTwoUpper_le _ hcK
  have hcz : c * M.e 0 * c⁻¹ = M.e 0 := S.comm_V1 hcH M.hz
  obtain ⟨x, hx3, hxe⟩ := S.conj_mem_P M hcK hσc h12 (S.e_mem_P M (i := 1) (by decide))
  obtain ⟨y, hy3, hye⟩ := S.conj_mem_P M hcK hσc h12 (S.e_mem_P M (i := 2) (by decide))
  have hqU : M.ta⁻¹ * (c * M.ta * c⁻¹) ∈ fsuU T V := by
    have hσ : M.ta⁻¹ = M.ta := (eq_inv_of_mul_eq_one_left M.ta_sq).symm
    have h' := hσc
    rw [hσ] at h'
    rw [S.QU, hσ]
    simpa [mul_assoc] using h'
  have hqP : M.ta⁻¹ * (c * M.ta * c⁻¹) ∈ P := by
    have hc3' : c⁻¹ = c * c := by
      calc c⁻¹ = c⁻¹ * c ^ 3 := by rw [hc3, mul_one]
        _ = c * c := by rw [pow_three]; group
    have hcinv : ∀ p ∈ P, c⁻¹ * p * c ∈ P := fun p hp => by
      have h1 := S.conj_mem_P M hcK hσc h12 hp
      have h2' := S.conj_mem_P M hcK hσc h12 h1
      rwa [show c * (c * p * c⁻¹) * c⁻¹ = c⁻¹ * p * c by
        rw [show c * (c * p * c⁻¹) * c⁻¹ = (c * c) * p * (c * c)⁻¹ by group, ← hc3', inv_inv]]
        at h2'
    refine S.mem_P_of_comm M hqU fun p hp => ?_
    have h1 := S.comm_ta_P M (hcinv p hp)
    have h2' := S.comm_ta_P M hp
    calc M.ta⁻¹ * (c * M.ta * c⁻¹) * p
        = M.ta⁻¹ * (c * (M.ta * (c⁻¹ * p * c)) * c⁻¹) := by group
      _ = M.ta⁻¹ * (c * ((c⁻¹ * p * c) * M.ta) * c⁻¹) := by rw [h1]
      _ = M.ta⁻¹ * p * (c * M.ta * c⁻¹) := by group
      _ = p * M.ta⁻¹ * (c * M.ta * c⁻¹) := by
        rw [show M.ta⁻¹ * p = p * M.ta⁻¹ by
          calc M.ta⁻¹ * p = M.ta⁻¹ * (p * M.ta) * M.ta⁻¹ := by group
            _ = M.ta⁻¹ * (M.ta * p) * M.ta⁻¹ := by rw [h2']
            _ = p * M.ta⁻¹ := by group]
      _ = p * (M.ta⁻¹ * (c * M.ta * c⁻¹)) := by group
  obtain ⟨w, hw3, hwe⟩ := id hqP
  have hcM : ActsAs M.e c (mC (x 0) (x 1) (x 2) (y 0) (y 1) (y 2) (w 0) (w 1) (w 2)) :=
    actsAs_C hc h2 hcz (by rw [← hxe, cp_eq_vec _ _ hx3]) (by rw [← hye, cp_eq_vec _ _ hy3]) (by
      rw [cp_vec_one, ← cp_eq_vec _ _ hw3, hwe]
      show c * M.ta * c⁻¹ = M.ta⁻¹ * (c * M.ta * c⁻¹) * M.ta
      rw [← S.comm_ta_P M hqP]
      group)
  have he1 : cp M.e ![0, 1, 0, 0] = M.e 1 := by simp [cp_vec, val_one2]
  have he2 : cp M.e ![0, 0, 1, 0] = M.e 2 := by simp [cp_vec, val_one2]
  have he12 : cp M.e ![0, 1, 1, 0] = M.e 1 * M.e 2 := by simp [cp_vec, val_one2]
  have hfx : ¬ (x 1 = 1 ∧ x 2 = 0) := fun ⟨h1, h2'⟩ =>
    S.fpf_coords M hcK hcfpf' (v := ![0, 1, 0, 0]) (w := x) rfl (by simp)
      (by rw [he1, hxe]) (by rw [h1]; rfl) (by rw [h2']; rfl) hx3
  have hfy : ¬ (y 1 = 0 ∧ y 2 = 1) := fun ⟨h1, h2'⟩ =>
    S.fpf_coords M hcK hcfpf' (v := ![0, 0, 1, 0]) (w := y) rfl (by simp)
      (by rw [he2, hye]) (by rw [h1]; rfl) (by rw [h2']; rfl) hy3
  have hfxy : ¬ (x 1 + y 1 = 1 ∧ x 2 + y 2 = 1) := fun ⟨h1, h2'⟩ =>
    S.fpf_coords M hcK hcfpf' (v := ![0, 1, 1, 0]) (w := x + y) rfl (by simp)
      (by rw [he12, cp_add hc h2, hxe, hye]; group) (by rw [Pi.add_apply, h1]; rfl)
      (by rw [Pi.add_apply, h2']; rfl) (by rw [Pi.add_apply, hx3, hy3, add_zero])
  have hcb := S.actsAs_of_mem_U M (L128A.HatU.conj_mem (cN hcK) (V_le_U M.hb))
  have hcu := S.actsAs_of_mem_U M (L128A.HatU.conj_mem (cN hcK) M.huU)
  have hr : ActsAs M.e M.r mR := actsAs_R hc h2 M.r_z M.r_a M.r_tz M.r_ta
  have hu : ActsAs M.e M.u mU := actsAs_U hc h2 M.u_z M.u_a M.u_tz M.u_ta
  obtain ⟨γ, hγz, hγ7⟩ := exists_seven hc h2 (S.e_ind M) hr (S.actsAs_b M) hu hcM hc3 hfx hfy
    hfxy hcb hcu
  have hγH : γ ∈ l32nH T V := S'.mem_g1 M.hz M.hz1 hγz
  obtain ⟨n, hn, h7⟩ := S.exists_pow_eq_one hγH
  exact h7 (hγ7 n hn)

theorem not_split : ¬ ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L :=
  fun ⟨_, hXL, hXV, hXsup⟩ => S.false_of_split hXL hXV hXsup

end Setup5

end L1444

end CFSG.Quasithin.H13
