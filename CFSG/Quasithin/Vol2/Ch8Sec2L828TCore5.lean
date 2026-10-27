module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMBApp
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCore5A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

section Core5

variable {G : Type} [Group G] [Finite G]

theorem s828_x_triv_B (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k) {x : G}
    (hxP : x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G))
    (hxU : x ∈ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hx5 : ∃ a : ℕ, x ^ 5 ^ a = 1)
    (hcLU : ∀ w ∈ ch82LU L (ch82U (fsuV T I) h), ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅⁅x, w⁆, p⁆ ∈ ch82U (fsuV T I) h)
    (hcI : ∀ w ∈ ch82I (fsuV T I) h, ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅⁅x, w⁆, p⁆ ∈ ch82U (fsuV T I) h) :
    ∀ b ∈ ch82B (fsuV T I) h, x * b * x⁻¹ * b⁻¹ ∈ ch82U (fsuV T I) h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hx5
  set V := fsuV T I with hVdef
  set Ih := ch82I V h with hIh
  set P := pCoreOf 2 Ih with hPdef
  set B := ch82B V h with hBdef
  set U := ch82U V h with hUdef
  set LU := ch82LU L U with hLUdef
  have hIP : Ih ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Ih
  have hBV : B ≤ V := inf_le_left
  have hBP : B ≤ P := inf_le_right
  have hVI : V ≤ Ih := le_sup_left
  have hPI : P ≤ Ih := CFSG.LieType.BorelTits.pCoreOf_le 2 Ih
  have hUB : U ≤ B := c.hUB
  have hLUV : LU ≤ Subgroup.normalizer (V : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans c.hLN)
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have := congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : ↥V) ⟨w, hw⟩)
    simpa using this
  have hLUP1 : ∀ l ∈ LU, ∀ p ∈ P, l * p * l⁻¹ ∈ P := by
    intro l hl p hp
    have h1 : ⁅p, l⁆ ∈ P := c.hILU (Subgroup.commutator_mem_commutator (hPI hp) hl)
    have e : l * p * l⁻¹ = (⁅p, l⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem (P.inv_mem h1) hp
  have hLUP : LU ≤ Subgroup.normalizer (P : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hLUP1 l hl p hp, fun hp => ?_⟩
    have := hLUP1 l⁻¹ (LU.inv_mem hl) _ hp
    simpa [mul_assoc] using this
  have hLUB : ∀ l ∈ LU, ∀ b ∈ B, l * b * l⁻¹ ∈ B := fun l hl b hb =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hLUV hl) b).mp (hBV hb), hLUP1 l hl b (hBP hb)⟩
  have hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun b hb =>
    x_norm_B hBV hBP hVI hVcomm hIP hxP c.hcen hcI c.hB5 hb
  let fx : ↥V → ↥V := fun v => if hv : x * (v : G) * x⁻¹ ∈ V then ⟨x * (v : G) * x⁻¹, hv⟩ else 1
  have hfx : ∀ v : ↥V, x * (v : G) * x⁻¹ ∈ V → ((fx v : ↥V) : G) = x * (v : G) * x⁻¹ :=
    fun v hv => by simp [fx, hv]
  have hfxB : ∀ v : ↥V, (v : G) ∈ B → ((fx v : ↥V) : G) = x * (v : G) * x⁻¹ :=
    fun v hv => hfx v (hBV (hxB _ hv))
  have hmemBw : ∀ v : ↥V, v ∈ B.subgroupOf V ↔ (v : G) ∈ B := fun v => Subgroup.mem_subgroupOf
  have hmemUw : ∀ v : ↥V, v ∈ U.subgroupOf V ↔ (v : G) ∈ U := fun v => Subgroup.mem_subgroupOf
  have hmul : ∀ u ∈ B.subgroupOf V, ∀ v ∈ B.subgroupOf V, fx (u * v) = fx u * fx v := by
    intro u hu v hv
    have hu' := (hmemBw u).mp hu
    have hv' := (hmemBw v).mp hv
    apply Subtype.ext
    have huv : ((u * v : ↥V) : G) ∈ B := B.mul_mem hu' hv'
    rw [hfxB _ huv, Subgroup.coe_mul, Subgroup.coe_mul, hfxB u hu', hfxB v hv']
    group
  have hBw : ∀ u ∈ B.subgroupOf V, fx u ∈ B.subgroupOf V := fun u hu => by
    have hu' := (hmemBw u).mp hu
    rw [hmemBw, hfxB u hu']
    exact hxB _ hu'
  have hUw : ∀ u ∈ U.subgroupOf V, fx u ∈ U.subgroupOf V := fun u hu => by
    have hu' := (hmemUw u).mp hu
    rw [hmemUw, hfxB u (hUB hu')]
    exact (Subgroup.mem_normalizer_iff.mp hxU u).mp hu'
  obtain ⟨Cx, hCx⟩ := exists_induces (B := B.subgroupOf V) (U := U.subgroupOf V) fx hmul hBw hUw
  have hCxcomm : Cx ∈ commutant (B.subgroupOf V) (U.subgroupOf V)
      ((autOn LU V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    rw [mem_commutant_iff]
    intro γ hγ0
    obtain ⟨g, hg, hγ⟩ := hγ0
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyLU : (y : G) ∈ LU := Subgroup.mem_subgroupOf.mp hy
    have h1 := Induces.mul hγ hCx
    have h2 := Induces.mul hCx hγ
    refine Induces.ext_of h2 h1 ?_
    intro b hb
    have hb' := (hmemBw b).mp hb
    have hyb : (((conjAct V y) b : ↥V) : G) = (y : G) * (b : G) * (y : G)⁻¹ :=
      CFSG.QuasithinUnique.Setup.coe_conjAct_apply y b
    have hyBB : ((y : G) * (b : G) * (y : G)⁻¹) ∈ B := hLUB _ hyLU _ hb'
    have hxbB : x * (b : G) * x⁻¹ ∈ B := hxB _ hb'
    have hfy : ((fx (conjAct V y b) : ↥V) : G) = x * ((y : G) * (b : G) * (y : G)⁻¹) * x⁻¹ := by
      rw [hfx _ (by rw [hyb]; exact hBV (hxB _ hyBB)), hyb]
    have hyf : (((conjAct V y) (fx b) : ↥V) : G) =
        (y : G) * (x * (b : G) * x⁻¹) * (y : G)⁻¹ := by
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply, hfxB b hb']
    rw [hmemUw]
    show ((((conjAct V y) (fx b) * (fx (conjAct V y b))⁻¹ : ↥V)) : G) ∈ U
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hfy, hyf]
    have hk := U.inv_mem (x_comm_LU (hLUP hyLU) hxP (hcLU _ hyLU) (hBP hb'))
    simpa only [mul_inv_rev, inv_inv] using hk
  have hiter : ∀ n : ℕ, ∀ v : ↥V, (v : G) ∈ B →
      (fx^[n] v : ↥V) ∈ B.subgroupOf V ∧ (((fx^[n] v : ↥V)) : G) = x ^ n * (v : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v hv; exact ⟨(hmemBw v).mpr hv, by simp⟩
    | succ n ih =>
      intro v hv
      rw [Function.iterate_succ_apply]
      have hfv : fx v ∈ B.subgroupOf V := hBw v ((hmemBw v).mpr hv)
      obtain ⟨h1, h2⟩ := ih (fx v) ((hmemBw _).mp hfv)
      refine ⟨h1, ?_⟩
      rw [h2, hfxB v hv]
      rw [pow_succ', mul_inv_rev]
      group
  have hpow : Cx ^ 5 ^ a = 1 := by
    have h1 := Induces.pow hCx (5 ^ a)
    refine Induces.ext_of h1 (induces_one _ _) ?_
    intro b hb
    have hb' := (hmemBw b).mp hb
    obtain ⟨-, h2⟩ := hiter (5 ^ a) b hb'
    rw [hmemUw]
    show ((fx^[5 ^ a] b * (id b)⁻¹ : ↥V) : G) ∈ U
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h2, ha]
    simp
  have hCx1 : Cx = 1 := s828_mb2_unit_five_G hMB2 hcard hrow c Cx hCxcomm a hpow
  intro b hb
  have h1 := hCx.mul_inv_mem_of_eq_one hCx1 ⟨b, hBV hb⟩ ((hmemBw _).mpr hb)
  have h2 := (hmemUw _).mp h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hfxB ⟨b, hBV hb⟩ hb] at h2
  exact h2

theorem s828_core5 (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k) {x : G}
    (hxP : x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G))
    (hxU : x ∈ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hx5 : ∃ a : ℕ, x ^ 5 ^ a = 1)
    (hcLU : ∀ w ∈ ch82LU L (ch82U (fsuV T I) h), ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅⁅x, w⁆, p⁆ ∈ ch82U (fsuV T I) h)
    (hcI : ∀ w ∈ ch82I (fsuV T I) h, ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅⁅x, w⁆, p⁆ ∈ ch82U (fsuV T I) h) :
    ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), x * p * x⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := s828_x_triv_B hMB2 hcard hrow c hxP hxU hx5 hcLU hcI
  have hIP : ch82I (fsuV T I) h ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hPI : pCoreOf 2 (ch82I (fsuV T I) h) ≤ ch82I (fsuV T I) h :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hAB : ∀ a ∈ ch82A (fsuV T I) h, h⁻¹ * a * h ∈ ch82B (fsuV T I) h := by
    intro a ha
    have ha' : a ∈ B6.conjSub h (fsuV T I) ⊓ pCoreOf 2 (ch82I (fsuV T I) h) := ha
    refine ⟨B6.mem_conjSub.mp (Subgroup.mem_inf.mp ha').1, ?_⟩
    have hPN : h⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) :=
      hIP (Subgroup.inv_mem _ c.hhI)
    have := (Subgroup.mem_normalizer_iff.mp hPN a).mp (Subgroup.mem_inf.mp ha').2
    simpa using this
  have hA : ∀ a ∈ ch82A (fsuV T I) h, x * a * x⁻¹ * a⁻¹ ∈ ch82U (fsuV T I) h := fun a ha =>
    x_triv_A (A := ch82A (fsuV T I) h) (B := ch82B (fsuV T I) h) inf_le_right inf_le_right
      c.hhI hIP hxP c.hcen hcI hAB hB ha
  exact x_triv_P hxP (fun u hu p hp => c.hcen u hu p (hPI hp)) c.hPeq inf_le_right inf_le_right
    hA hB

end Core5

end CFSG.Quasithin.H13
