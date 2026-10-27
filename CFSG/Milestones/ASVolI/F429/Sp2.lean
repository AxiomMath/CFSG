module

public import CFSG.Milestones.ASVolI.F429.Sp2Mat
public import CFSG.Milestones.ASVolI.F429.C8Small
public import CFSG.Quasithin.H13.U4ParSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix

public section

namespace CFSG.ASVolI

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a

section Generic

variable {G H : Type} [Group G] [Group H]

theorem burnsideF429_oTwoRes_map_eq (φ : G →* H) (hφ : Function.Injective φ) (P : Subgroup G) :
    oTwoRes (P.map φ) = (oTwoRes P).map φ := by
  refine le_antisymm ?_ (burnsideF429_oTwoRes_map_le φ P)
  unfold oTwoRes
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨x, hx, rfl⟩, m, hm, hxm⟩
  refine ⟨x, Subgroup.subset_closure ⟨hx, m, hm, ?_⟩, rfl⟩
  apply hφ
  rw [map_pow, hxm, map_one]

theorem burnsideF429_pCoreOf_eq_self {p : ℕ} {Y : Subgroup G} (hY : IsPGroup p Y) :
    pCoreOf p Y = Y := by
  refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le p Y) fun y hy => ?_
  have htop : (⊤ : Subgroup Y) ≤ CFSG.Open.pCore p Y :=
    CFSG.LieType.BorelTits.le_pCore p Subgroup.normal_top (hY.of_equiv Subgroup.topEquiv.symm)
  exact ⟨⟨y, hy⟩, htop (Subgroup.mem_top _), rfl⟩

end Generic

section SpTwo

variable {F : Type} [Field F]

noncomputable def burnsideF429_s_e (hF : Nat.card F = 2) : ZMod 2 ≃+* F :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  letI : Fintype F := Fintype.ofFinite F
  letI : CharP F 2 := charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hF])
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl 2) F)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(ZMod.castHom (dvd_refl 2) F).injective, by
        rw [ZMod.card, Fintype.card_eq_nat_card, hF]⟩)

variable (hF : Nat.card F = 2)

theorem burnsideF429_s_J_map :
    burnsideF429_s_J.map (burnsideF429_s_e hF) = CFSG.Quasithin.H13.U4Par.spJ F := by
  have hneg : ∀ x : ZMod 2, (burnsideF429_s_e hF) (-x) = -(burnsideF429_s_e hF) x :=
    fun x => map_neg _ x
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [burnsideF429_s_J, CFSG.Quasithin.H13.U4Par.spJ]
  · simp only [burnsideF429_s_J, CFSG.Quasithin.H13.U4Par.spJ, Matrix.map_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [burnsideF429_s_J, CFSG.Quasithin.H13.U4Par.spJ, Matrix.map_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · rw [hneg, map_one]
    · rw [hneg, map_zero, neg_zero]
  · simp [burnsideF429_s_J, CFSG.Quasithin.H13.U4Par.spJ]

theorem burnsideF429_s_J_map_symm :
    (CFSG.Quasithin.H13.U4Par.spJ F).map (burnsideF429_s_e hF).symm = burnsideF429_s_J := by
  rw [← burnsideF429_s_J_map hF, Matrix.map_map]
  ext a b
  simp

@[expose] noncomputable def burnsideF429_s_Φ :
    StatedSp 2 F →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  (burnsideF429_s_e hF).symm.toRingHom.mapMatrix.toMonoidHom.comp
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat 2 F)

theorem burnsideF429_s_Φ_apply (x : StatedSp 2 F) (a b : Fin 2 ⊕ Fin 2) :
    burnsideF429_s_Φ hF x a b =
      (burnsideF429_s_e hF).symm (((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2)
        (Fin 2 ⊕ Fin 2) F) a b) := rfl

theorem burnsideF429_s_entry (x : StatedSp 2 F) (a b : Fin 2 ⊕ Fin 2) :
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) a b =
      burnsideF429_s_e hF (burnsideF429_s_Φ hF x a b) := by
  rw [burnsideF429_s_Φ_apply, RingEquiv.apply_symm_apply]

theorem burnsideF429_s_Φ_injective : Function.Injective (burnsideF429_s_Φ hF) := by
  intro x y h
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  ext a b
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, burnsideF429_s_entry hF x,
    burnsideF429_s_entry hF y, h]

theorem burnsideF429_s_Φ_symp (x : StatedSp 2 F) :
    (burnsideF429_s_Φ hF x)ᵀ * burnsideF429_s_J * burnsideF429_s_Φ hF x = burnsideF429_s_J := by
  have h := CFSG.Quasithin.H13.U4Par.symp_of_mem_statedSp x.2
  have h2 := congrArg (fun M => M.map (burnsideF429_s_e hF).symm.toRingHom) h
  simp only [Matrix.map_mul, Matrix.transpose_map] at h2
  have hx : burnsideF429_s_Φ hF x =
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map
        (burnsideF429_s_e hF).symm.toRingHom := rfl
  have hJ : (CFSG.Quasithin.H13.U4Par.spJ F).map (burnsideF429_s_e hF).symm.toRingHom =
      burnsideF429_s_J := burnsideF429_s_J_map_symm hF
  rw [hx, ← hJ]
  exact h2

theorem burnsideF429_s_mem_flag_two (v : Fin 2 ⊕ Fin 2 → F) :
    v ∈ flag 2 F 2 ↔ ∀ j, v (Sum.inr j) = 0 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun j hj => ?_⟩
    have := j.2
    omega

omit hF in
theorem burnsideF429_s_Q1_bl {A : StatedSp 2 F} (hA : A ∈ Q2 F 1) (i j : Fin 2) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (Sum.inr i) (Sum.inl j) = 0 := by
  have hmem : (Pi.single (Sum.inl j) (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 2 := by
    rw [burnsideF429_s_mem_flag_two]
    intro k
    simp
  have hA' : A ∈ stabilizer 2 F (flag 2 F 2) := hA
  rw [mem_stabilizer] at hA'
  have himg : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      Pi.single (Sum.inl j) 1 ∈ flag 2 F 2 := by
    rw [← hA']
    exact ⟨_, hmem, rfl⟩
  rw [burnsideF429_s_mem_flag_two, mulVec_single_one] at himg
  exact himg i

omit hF in
theorem burnsideF429_s_Q1_of_bl {A : StatedSp 2 F}
    (h1 : ∀ i j, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (Sum.inr i) (Sum.inl j) = 0)
    (h2 : ∀ i j, (((A⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inr i) (Sum.inl j) = 0) : A ∈ Q2 F 1 := by
  have key : ∀ (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      (∀ i j, M (Sum.inr i) (Sum.inl j) = 0) → ∀ v ∈ flag 2 F 2, M *ᵥ v ∈ flag 2 F 2 := by
    intro M hM v hv
    rw [burnsideF429_s_mem_flag_two] at hv ⊢
    intro i
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp [hM, hv]
  exact mem_stabilizer_of_mulVec_mem (key _ h1) (key _ h2)

theorem burnsideF429_s_inQ0_of_mem {x : StatedSp 2 F} (hx : x ∈ Q2 F 0) :
    burnsideF429_s_inQ0 (burnsideF429_s_Φ hF x) := by
  have h := CFSG.Quasithin.H13.U4Par.col_of_mem_Q2_zero hx
  refine ⟨?_, ?_, ?_⟩ <;> rw [burnsideF429_s_Φ_apply, h _ (by decide), map_zero]

theorem burnsideF429_s_inQ1_of_mem {x : StatedSp 2 F} (hx : x ∈ Q2 F 1) :
    burnsideF429_s_inQ1 (burnsideF429_s_Φ hF x) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [burnsideF429_s_Φ_apply, burnsideF429_s_Q1_bl hx, map_zero]

theorem burnsideF429_s_mem_Q0 {x : StatedSp 2 F} (h : burnsideF429_s_inQ0 (burnsideF429_s_Φ hF x))
    (h' : burnsideF429_s_inQ0 (burnsideF429_s_Φ hF x⁻¹)) : x ∈ Q2 F 0 := by
  have key : ∀ y : StatedSp 2 F, burnsideF429_s_inQ0 (burnsideF429_s_Φ hF y) →
      ∀ b, b ≠ Sum.inl 0 → ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2)
        (Fin 2 ⊕ Fin 2) F) b (Sum.inl 0) = 0 := by
    intro y hy b hb
    obtain ⟨h10, h20, h30⟩ := hy
    rw [burnsideF429_s_entry hF]
    rcases b with j | j <;> fin_cases j
    · exact absurd rfl hb
    · rw [show (Sum.inl ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 from rfl, h10,
        map_zero]
    · rw [show (Sum.inr ((⟨0, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 from rfl, h20,
        map_zero]
    · rw [show (Sum.inr ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 from rfl, h30,
        map_zero]
  exact CFSG.Quasithin.H13.U4Par.mem_Q2_zero_of_col (key x h) (key x⁻¹ h')

theorem burnsideF429_s_mem_Q1 {x : StatedSp 2 F} (h : burnsideF429_s_inQ1 (burnsideF429_s_Φ hF x))
    (h' : burnsideF429_s_inQ1 (burnsideF429_s_Φ hF x⁻¹)) : x ∈ Q2 F 1 := by
  have key : ∀ y : StatedSp 2 F, burnsideF429_s_inQ1 (burnsideF429_s_Φ hF y) →
      ∀ i j, ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        (Sum.inr i) (Sum.inl j) = 0 := by
    intro y hy i j
    obtain ⟨h00, h01, h10, h11⟩ := hy
    rw [burnsideF429_s_entry hF]
    fin_cases i <;> fin_cases j
    · rw [show (Sum.inr ((⟨0, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 from rfl,
        show (Sum.inl ((⟨0, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 0 from rfl, h00,
        map_zero]
    · rw [show (Sum.inr ((⟨0, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 from rfl,
        show (Sum.inl ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 from rfl, h01,
        map_zero]
    · rw [show (Sum.inr ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 from rfl,
        show (Sum.inl ((⟨0, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 0 from rfl, h10,
        map_zero]
    · rw [show (Sum.inr ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 from rfl,
        show (Sum.inl ((⟨1, by decide⟩ : Fin 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 from rfl, h11,
        map_zero]
  exact burnsideF429_s_Q1_of_bl (key x h) (key x⁻¹ h')

@[expose] noncomputable def burnsideF429_s_elt
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Xᵀ * burnsideF429_s_J * X = burnsideF429_s_J) : StatedSp 2 F :=
  ⟨⟨(burnsideF429_s_e hF).toRingHom.mapMatrix X, (burnsideF429_s_e hF).toRingHom.mapMatrix Y,
      by rw [← map_mul, hXY, map_one], by rw [← map_mul, hYX, map_one]⟩, by
    apply Subgroup.subset_closure
    change ((burnsideF429_s_e hF).toRingHom.mapMatrix X)ᵀ *
        CFSG.Quasithin.H13.U4Par.spJ F * (burnsideF429_s_e hF).toRingHom.mapMatrix X =
      CFSG.Quasithin.H13.U4Par.spJ F
    rw [← burnsideF429_s_J_map hF]
    have ht : ((burnsideF429_s_e hF).toRingHom.mapMatrix X)ᵀ =
        (burnsideF429_s_e hF).toRingHom.mapMatrix Xᵀ := by
      simp only [RingHom.mapMatrix_apply, Matrix.transpose_map]
    have hJ : burnsideF429_s_J.map (burnsideF429_s_e hF) =
        (burnsideF429_s_e hF).toRingHom.mapMatrix burnsideF429_s_J := rfl
    rw [ht, hJ, ← map_mul, ← map_mul, hX]⟩

theorem burnsideF429_s_Φ_elt (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hXY : X * Y = 1) (hYX : Y * X = 1) (hX : Xᵀ * burnsideF429_s_J * X = burnsideF429_s_J) :
    burnsideF429_s_Φ hF (burnsideF429_s_elt hF X Y hXY hYX hX) = X := by
  ext a b
  exact (burnsideF429_s_e hF).symm_apply_apply (X a b)

theorem burnsideF429_s_Φ_elt_inv (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hXY : X * Y = 1) (hYX : Y * X = 1) (hX : Xᵀ * burnsideF429_s_J * X = burnsideF429_s_J) :
    burnsideF429_s_Φ hF (burnsideF429_s_elt hF X Y hXY hYX hX)⁻¹ = Y := by
  ext a b
  exact (burnsideF429_s_e hF).symm_apply_apply (Y a b)

theorem burnsideF429_s_Φ_t :
    burnsideF429_s_Φ hF (CFSG.LieType.Universal.Symplectic.SpExtras.elt
      (.positiveLong 1) (1 : F)) = burnsideF429_s_T := by
  have hm : ((CFSG.LieType.Universal.Symplectic.SpExtras.elt (.positiveLong 1) (1 : F) :
      StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      (1 + Matrix.single (Sum.inl 1) (Sum.inr 1) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
      CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt, one_smul]
    rfl
  ext a b
  rw [burnsideF429_s_Φ_apply, hm]
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [burnsideF429_s_T, Matrix.one_apply, Matrix.single_apply]

variable [Finite F]

@[expose] noncomputable def burnsideF429_s_χ : StatedSp 2 F →* ℤˣ :=
  Equiv.Perm.sign.comp (CFSG.SeitzReduction.F4Pilot.sp4EquivPerm hF).toMonoidHom

theorem burnsideF429_s_χ_t :
    burnsideF429_s_χ hF (CFSG.LieType.Universal.Symplectic.SpExtras.elt (.positiveLong 1) 1) =
      -1 := by
  rw [burnsideF429_s_χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    CFSG.SeitzReduction.F4Pilot.sp4EquivPerm_elt_long, Equiv.Perm.sign_swap (by decide)]

theorem burnsideF429_s_oTwoRes_le_ker :
    oTwoRes (⊤ : Subgroup (StatedSp 2 F)) ≤ (burnsideF429_s_χ hF).ker := by
  unfold oTwoRes
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨-, m, hm, hxm⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  have h1 : burnsideF429_s_χ hF x ^ m = 1 := by rw [← map_pow, hxm, map_one]
  rcases Int.units_eq_one_or (burnsideF429_s_χ hF x) with h | h
  · exact h
  · rw [h, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

include hF in
theorem burnsideF429_s_model :
    IsPGroup 2 ↥(Q2 F 0 ⊓ Q2 F 1) ∧
      (Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes ⊤ ≤
        ((Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes (Q2 F 0)) ⊔ ((Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes (Q2 F 1)) ∧
      ((Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes ⊤).relIndex (Q2 F 0 ⊓ Q2 F 1) = 2 := by
  obtain ⟨oU1, oU2, oT, oY1a, oY1b, oZ1a, oZ1b, oY2a, oY2b, oZ2a, oZ2b⟩ := burnsideF429_s_orders
  obtain ⟨sU1, sU2, sY1, sZ1, sY2, sZ2, eU1, eU2⟩ := burnsideF429_s_symp
  obtain ⟨cU1a, cU1b, cU2a, cU2b, cTa, cTb, cY1, cY1i, cZ1, cZ1i, cY2, cY2i, cZ2, cZ2i⟩ :=
    burnsideF429_s_shapes
  set Φ := burnsideF429_s_Φ hF with hΦ
  have hΦi := burnsideF429_s_Φ_injective hF
  set u1 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oU1 oU1 sU1 with hu1
  set u2 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oU2 oU2 sU2 with hu2
  set y1 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oY1a oY1b sY1 with hy1
  set z1 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oZ1a oZ1b sZ1 with hz1
  set y2 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oY2a oY2b sY2 with hy2
  set z2 : StatedSp 2 F := burnsideF429_s_elt hF _ _ oZ2a oZ2b sZ2 with hz2
  set t : StatedSp 2 F := CFSG.LieType.Universal.Symplectic.SpExtras.elt (.positiveLong 1) 1
    with ht
  have Φu1 : Φ u1 = burnsideF429_s_U1 := burnsideF429_s_Φ_elt hF _ _ _ _ _
  have Φu2 : Φ u2 = burnsideF429_s_U2 := burnsideF429_s_Φ_elt hF _ _ _ _ _
  have Φt : Φ t = burnsideF429_s_T := burnsideF429_s_Φ_t hF
  have htt : t * t = 1 := hΦi (by rw [map_mul, Φt, oT, map_one])
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have mu1 : u1 ∈ Q2 F 0 ⊓ Q2 F 1 :=
    ⟨burnsideF429_s_mem_Q0 hF (by rw [Φu1]; exact cU1a)
        (by rw [burnsideF429_s_Φ_elt_inv]; exact cU1a),
      burnsideF429_s_mem_Q1 hF (by rw [Φu1]; exact cU1b)
        (by rw [burnsideF429_s_Φ_elt_inv]; exact cU1b)⟩
  have mu2 : u2 ∈ Q2 F 0 ⊓ Q2 F 1 :=
    ⟨burnsideF429_s_mem_Q0 hF (by rw [Φu2]; exact cU2a)
        (by rw [burnsideF429_s_Φ_elt_inv]; exact cU2a),
      burnsideF429_s_mem_Q1 hF (by rw [Φu2]; exact cU2b)
        (by rw [burnsideF429_s_Φ_elt_inv]; exact cU2b)⟩
  have mt : t ∈ Q2 F 0 ⊓ Q2 F 1 :=
    ⟨burnsideF429_s_mem_Q0 hF (by rw [Φt]; exact cTa) (by rw [hti, Φt]; exact cTa),
      burnsideF429_s_mem_Q1 hF (by rw [Φt]; exact cTb) (by rw [hti, Φt]; exact cTb)⟩
  have my1 : y1 ∈ Q2 F 0 := burnsideF429_s_mem_Q0 hF
    (by rw [burnsideF429_s_Φ_elt]; exact cY1) (by rw [burnsideF429_s_Φ_elt_inv]; exact cY1i)
  have mz1 : z1 ∈ Q2 F 0 := burnsideF429_s_mem_Q0 hF
    (by rw [burnsideF429_s_Φ_elt]; exact cZ1) (by rw [burnsideF429_s_Φ_elt_inv]; exact cZ1i)
  have my2 : y2 ∈ Q2 F 1 := burnsideF429_s_mem_Q1 hF
    (by rw [burnsideF429_s_Φ_elt]; exact cY2) (by rw [burnsideF429_s_Φ_elt_inv]; exact cY2i)
  have mz2 : z2 ∈ Q2 F 1 := burnsideF429_s_mem_Q1 hF
    (by rw [burnsideF429_s_Φ_elt]; exact cZ2) (by rw [burnsideF429_s_Φ_elt_inv]; exact cZ2i)
  have hodd : Odd 3 := by decide
  have py1 : y1 ^ 3 = 1 := hΦi (by
    rw [pow_three', map_mul, map_mul, burnsideF429_s_Φ_elt, oY1b, map_one])
  have pz1 : z1 ^ 3 = 1 := hΦi (by
    rw [pow_three', map_mul, map_mul, burnsideF429_s_Φ_elt, oZ1b, map_one])
  have py2 : y2 ^ 3 = 1 := hΦi (by
    rw [pow_three', map_mul, map_mul, burnsideF429_s_Φ_elt, oY2b, map_one])
  have pz2 : z2 ^ 3 = 1 := hΦi (by
    rw [pow_three', map_mul, map_mul, burnsideF429_s_Φ_elt, oZ2b, map_one])
  have fu1 : u1 = y1 * z1 := hΦi (by
    rw [map_mul, Φu1, burnsideF429_s_Φ_elt, burnsideF429_s_Φ_elt, eU1])
  have fu2 : u2 = y2 * z2 := hΦi (by
    rw [map_mul, Φu2, burnsideF429_s_Φ_elt, burnsideF429_s_Φ_elt, eU2])
  set X : Subgroup (StatedSp 2 F) :=
    ((Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes (Q2 F 0)) ⊔ ((Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes (Q2 F 1)) with hX
  have xu1 : u1 ∈ X := Subgroup.mem_sup_left ⟨mu1, by
    rw [fu1]
    exact Subgroup.mul_mem _ (burnsideF429_mem_oTwoRes my1 hodd py1)
      (burnsideF429_mem_oTwoRes mz1 hodd pz1)⟩
  have xu2 : u2 ∈ X := Subgroup.mem_sup_right ⟨mu2, by
    rw [fu2]
    exact Subgroup.mul_mem _ (burnsideF429_mem_oTwoRes my2 hodd py2)
      (burnsideF429_mem_oTwoRes mz2 hodd pz2)⟩
  have hXO : X ≤ oTwoRes ⊤ := sup_le (inf_le_right.trans (burnsideF429_oTwoRes_mono le_top))
    (inf_le_right.trans (burnsideF429_oTwoRes_mono le_top))
  have htO : t ∉ oTwoRes (⊤ : Subgroup (StatedSp 2 F)) := fun h => by
    have := burnsideF429_s_oTwoRes_le_ker hF h
    rw [MonoidHom.mem_ker, ht, burnsideF429_s_χ_t] at this
    exact absurd this (by decide)
  have hU : ∀ x : StatedSp 2 F, burnsideF429_s_InU (Φ x) → x ∈ X := by
    intro x hx
    rcases hx with h | h | h | h | h | h | h | h
    · rw [show x = 1 from hΦi (by rw [h, map_one])]
      exact X.one_mem
    · rw [show x = u2 from hΦi (by rw [h, Φu2])]
      exact xu2
    · rw [show x = u1 from hΦi (by rw [h, Φu1])]
      exact xu1
    · rw [show x = u1 * u2 from hΦi (by rw [h, map_mul, Φu1, Φu2])]
      exact X.mul_mem xu1 xu2
    · rw [show x = u2 * u1 from hΦi (by rw [h, map_mul, Φu1, Φu2])]
      exact X.mul_mem xu2 xu1
    · rw [show x = u2 * u1 * u2 from hΦi (by rw [h, map_mul, map_mul, Φu1, Φu2])]
      exact X.mul_mem (X.mul_mem xu2 xu1) xu2
    · rw [show x = u1 * u2 * u1 from hΦi (by rw [h, map_mul, map_mul, Φu1, Φu2])]
      exact X.mul_mem (X.mul_mem xu1 xu2) xu1
    · rw [show x = u1 * u2 * u1 * u2 from hΦi (by rw [h, map_mul, map_mul, map_mul, Φu1, Φu2])]
      exact X.mul_mem (X.mul_mem (X.mul_mem xu1 xu2) xu1) xu2
  have hB : ∀ x ∈ Q2 F 0 ⊓ Q2 F 1, x * x * (x * x) = 1 ∧ (x ∈ X ∨ x * t ∈ X) := by
    intro x hx
    obtain ⟨h10, h20, h30⟩ := burnsideF429_s_inQ0_of_mem hF hx.1
    obtain ⟨-, h21, -, h31⟩ := burnsideF429_s_inQ1_of_mem hF hx.2
    rw [← hΦ] at h10 h20 h30 h21 h31
    have hshape : Φ x = burnsideF429_s_Bmat (Φ x (Sum.inl 0) (Sum.inl 0))
        (Φ x (Sum.inl 0) (Sum.inl 1)) (Φ x (Sum.inl 1) (Sum.inl 1))
        (Φ x (Sum.inl 0) (Sum.inr 0)) (Φ x (Sum.inl 0) (Sum.inr 1))
        (Φ x (Sum.inl 1) (Sum.inr 0)) (Φ x (Sum.inl 1) (Sum.inr 1))
        (Φ x (Sum.inr 0) (Sum.inr 0)) (Φ x (Sum.inr 0) (Sum.inr 1))
        (Φ x (Sum.inr 1) (Sum.inr 0)) (Φ x (Sum.inr 1) (Sum.inr 1)) := by
      ext a b
      rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [burnsideF429_s_Bmat, h10, h20, h30, h21, h31]
    have henum := burnsideF429_s_enum (Φ x (Sum.inl 0) (Sum.inl 0))
        (Φ x (Sum.inl 0) (Sum.inl 1)) (Φ x (Sum.inl 1) (Sum.inl 1))
        (Φ x (Sum.inl 0) (Sum.inr 0)) (Φ x (Sum.inl 0) (Sum.inr 1))
        (Φ x (Sum.inl 1) (Sum.inr 0)) (Φ x (Sum.inl 1) (Sum.inr 1))
        (Φ x (Sum.inr 0) (Sum.inr 0)) (Φ x (Sum.inr 0) (Sum.inr 1))
        (Φ x (Sum.inr 1) (Sum.inr 0)) (Φ x (Sum.inr 1) (Sum.inr 1))
    rw [← hshape] at henum
    obtain ⟨h4, hw⟩ := henum (burnsideF429_s_Φ_symp hF x)
    refine ⟨hΦi (by rw [map_mul, map_mul, h4, map_one]), ?_⟩
    rcases hw with hw | hw
    · exact Or.inl (hU x hw)
    · refine Or.inr (hU (x * t) ?_)
      rw [map_mul, Φt]
      exact hw
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, show (2 : ℕ) ^ 2 = 4 from rfl, show (x : StatedSp 2 F) ^ 4 =
      x * x * (x * x) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq], (hB x x.2).1, Subgroup.coe_one]
  · rintro x ⟨hxB, hxO⟩
    rcases (hB x hxB).2 with h | h
    · exact h
    · exfalso
      apply htO
      have h2 := hXO h
      have : t = x⁻¹ * (x * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxO) h2
  · rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, mt, fun b hb => ?_⟩
    rw [xor_iff_or_and_not_and]
    have hnot : ¬ (b * t ∈ (Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes ⊤ ∧ b ∈ (Q2 F 0 ⊓ Q2 F 1) ⊓ oTwoRes ⊤) := by
      rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      apply htO
      have : t = b⁻¹ * (b * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    refine ⟨?_, hnot⟩
    rcases (hB b hb).2 with h | h
    · exact Or.inr ⟨hb, hXO h⟩
    · exact Or.inl ⟨Subgroup.mul_mem _ hb mt, hXO h⟩

end SpTwo

section Clause

open CFSG.ASVolI.ChF

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_Sp4two_sbar (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp ≤
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) ∧
      (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).relIndex (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = 2 := by
  obtain ⟨K, _, _, _, θ, hK, hθ, hrange, h1, h2⟩ := burnsideF429_sp4_model_card hyp
  rw [pow_one] at hK
  obtain ⟨hp, ha, hidx⟩ := burnsideF429_s_model (F := K) hK
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (Q2 K 0 ⊓ Q2 K 1).map θ := by
    have e : Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) := by
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rw [e, h1, h2, Subgroup.map_inf_eq _ _ _ hθ]
  have hBM : (Q2 K 0 ⊓ Q2 K 1).map θ ≤ M₁ ⊓ M₂ := by
    rw [← hB]
    exact inf_le_right
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (Q2 K 0 ⊓ Q2 K 1).map θ := by
    rw [hB]
    exact burnsideF429_pCoreOf_eq_self (hp.map θ)
  have hG : Gp = (⊤ : Subgroup (StatedSp 2 K)).map θ := by
    rw [← hrange, MonoidHom.range_eq_map]
  have hO : oTwoRes Gp = (oTwoRes ⊤).map θ := by
    rw [hG, burnsideF429_oTwoRes_map_eq θ hθ]
  have hSO : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp =
      ((Q2 K 0 ⊓ Q2 K 1) ⊓ oTwoRes ⊤).map θ := by
    rw [hS, hO, ← Subgroup.map_inf_eq _ _ _ hθ]
  refine ⟨?_, ?_⟩
  · rw [hSO]
    refine (Subgroup.map_mono ha).trans ?_
    rw [Subgroup.map_sup]
    refine sup_le_sup (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact (Subgroup.map_mono inf_le_left).trans hBM
    · rw [h1]
      exact (Subgroup.map_mono inf_le_right).trans (burnsideF429_oTwoRes_map_le θ _)
    · exact (Subgroup.map_mono inf_le_left).trans hBM
    · rw [h2]
      exact (Subgroup.map_mono inf_le_right).trans (burnsideF429_oTwoRes_map_le θ _)
  · rw [hSO, hS, Subgroup.relIndex_map_map_of_injective _ _ hθ, hidx]

theorem burnsideF429_c8_Sp4two (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂) :
    burnsideF429_C8 .Sp4 1 Gp M₁ M₂ := by
  obtain ⟨ha, hb⟩ := burnsideF429_Sp4two_sbar hyp
  exact burnsideF429_c8_of (κ := .Sp4) (f := 1) ha (Or.inr ⟨rfl, Or.inl rfl, dvd_of_eq hb⟩)

end Clause

end CFSG.ASVolI
