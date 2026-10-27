module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigXfer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.BN CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F48Rig

variable {X : Type} [Group X] {n : ℕ} (R : RankTwoSystem X n)

theorem vtype_smul (y : X) (w : V R) :
    vtype R.B R.N R.w₁ R.w₂ (y • w) = vtype R.B R.N R.w₁ R.w₂ w :=
  R.rank2.vtype_action y w

theorem faithful_on_type [IsSimpleGroup X] (t : Bool) {y : X}
    (hy : ∀ w : V R, vtype R.B R.N R.w₁ R.w₂ w = t → y • w = w) : y = 1 := by
  let K : Subgroup X :=
    { carrier := {y | ∀ w : V R, vtype R.B R.N R.w₁ R.w₂ w = t → y • w = w}
      mul_mem' := fun {a b} ha hb w hw => by rw [mul_smul, hb w hw, ha w hw]
      one_mem' := fun w _ => one_smul X w
      inv_mem' := fun {a} ha w hw => inv_smul_eq_iff.2 (ha w hw).symm }
  have : K.Normal := ⟨fun k hk g w hw => by
    have h1 : vtype R.B R.N R.w₁ R.w₂ (g⁻¹ • w) = t := by rw [vtype_smul, hw]
    rw [mul_smul, mul_smul, hk (g⁻¹ • w) h1, smul_inv_smul]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · have hyK : y ∈ K := hy
    rw [h] at hyK
    exact Subgroup.mem_bot.1 hyK
  · exfalso
    have hv : vtype R.B R.N R.w₁ R.w₂ (v R t) = t := by rw [v_eq_vt, vtype_vt]
    refine P_ne_top R t (eq_top_iff.2 fun g _ => ?_)
    rw [← stabilizer_v_eq, MulAction.mem_stabilizer_iff]
    exact (h ▸ Subgroup.mem_top g : g ∈ K) (v R t) hv

variable [Finite X]

theorem cartanFPF_of_rankTwo_radical (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D]
    (hfin : Finite D) (hn : 3 ≤ n) (A : LieAmalgamExt D)
    {Φ : X →* (A.setting hfin n hn).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin n hn) Φ (Γ R) (v R b) (v R (!b))) {h : X}
    (hh : h ∈ R.B ⊓ R.N) (hc : ∀ y ∈ Q R b, h * y * h⁻¹ = y → y = 1) :
    (A.setting hfin n hn).CartanFPF := by
  have f₁ := (modelBase R hU b).flag (three_le_card_neighborSet R _) XD.adj12
  have f₂ := (modelBase R hU (!b)).flag (three_le_card_neighborSet R _) XD.adj12.symm
  obtain ⟨e, he1, -, heq, hadj⟩ :=
    XD.exists_equiv (cov_of_flags (isGenPolygon R).connected f₁ f₂) f₁
  obtain ⟨u₁, u₂, b₀, h₁, h₂, hne, hdist, hfix⟩ := torus_fixes_apartment R b
  obtain ⟨hv, hu₁, hu₂, hb₀⟩ := hfix h hh
  have hQ : pCoreOf 2 (MulAction.stabilizer X (v R b)) = Q R b := by
    rw [stabilizer_v_eq]
    rfl
  exact cartanFPF_of_model XD e he1 heq hadj (Q R b) hQ b₀ u₁ u₂ hdist h₁ h₂ hne h hv hb₀ hu₁ hu₂
    hc

theorem cartanFPF_of_rankTwo (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D] (hfin : Finite D)
    (hn : 3 ≤ n) (A : LieAmalgamExt D) {Φ : X →* (A.setting hfin n hn).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin n hn) Φ (Γ R) (v R b) (v R (!b))) {h : X}
    (hh : h ∈ R.B ⊓ R.N) (hc : ∀ y ∈ R.U, h * y * h⁻¹ = y → y = 1) :
    (A.setting hfin n hn).CartanFPF :=
  cartanFPF_of_rankTwo_radical R hU hfin hn A b XD hh fun y hy => hc y (Q_le_U R hU b hy)

theorem faithfulOnType_of_rankTwo [IsSimpleGroup X] (hU : IsSylowTwoOf R.U ⊤) {D : Type}
    [Group D] (hfin : Finite D) (hn : 3 ≤ n) (A : LieAmalgamExt D)
    {Φ : X →* (A.setting hfin n hn).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin n hn) Φ (Γ R) (v R b) (v R (!b)))
    (hcent : ∀ k : (A.setting hfin n hn).ι.G0, (∀ y : X, k * Φ y = Φ y * k) → k = 1) (s : Bool) :
    (A.setting hfin n hn).FaithfulOnType s := by
  have f₁ := (modelBase R hU b).flag (three_le_card_neighborSet R _) XD.adj12
  have f₂ := (modelBase R hU (!b)).flag (three_le_card_neighborSet R _) XD.adj12.symm
  obtain ⟨e, he1, he2, heq, -⟩ :=
    XD.exists_equiv (cov_of_flags (isGenPolygon R).connected f₁ f₂) f₁
  refine faithfulOnType_of_model XD e he1 he2 heq (vtype R.B R.N R.w₁ R.w₂) (vtype_smul R) ?_ s
    hcent fun y hy => faithful_on_type R _ hy
  rw [v_eq_vt, v_eq_vt, vtype_vt, vtype_vt]
  cases b <;> simp

end CFSG.Quasithin.H13.F431.D4q.F48
