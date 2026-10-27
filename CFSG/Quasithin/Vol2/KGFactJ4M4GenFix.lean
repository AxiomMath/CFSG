module

public import CFSG.Quasithin.Vol2.KGFactJ4M4GenSpec
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Fac
public import CFSG.Quasithin.Vol2.KGFactJ4M4Card

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L52

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.B5.Ln (mat)
open CFSG.Quasithin.KGC31.J4M4.Gen (z1Elt uElt uElt_def chkGen_facts)
open scoped Matrix

theorem eElt_fJ_nine : eElt fJ (codeVec 512) = fJ 9 := by
  rw [eElt_fJ]
  have hlow : ∀ n ≤ 9, eta fJn n 512 = 1 := by
    intro n hn
    induction n with
    | zero => simp [eta]
    | succ n ih =>
      rw [eta_succ, ih (by omega)]
      have : (512 : ℕ).testBit n = false := by
        have hn' : n < 9 := by omega
        interval_cases n <;> decide
      simp [this]
  rw [eta_succ, hlow 9 le_rfl]
  have : (512 : ℕ).testBit 9 = true := by decide
  simp [this]
  rfl

theorem fix_F_of_sylow_conj
    {S : Subgroup J}
    (hS : IsSylowTwoOf S CFSG.Quasithin.KGJ4.M4) :
    ∃ y ∈ CFSG.Quasithin.KGJ4.M4, ∀ x ∈ F4 j4Facts.mat chkF_true,
      x ∈ Subgroup.centralizer (S : Set J) → x = 1 ∨ x = y⁻¹ * eElt fJ (codeVec 512) * y := by
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := CFSG.Quasithin.KGJ4.M4 with hMdef
  set π := piM4 j4Facts.mat chkF_true with hπdef
  have hb := fJ_basis j4Facts.mat chkF_true
  have hFn := normal_F4 j4Facts.mat chkF_true
  have hker := ker_piM4 j4Facts.mat chkF_true J4M4Card.card_M4
  let T : Subgroup ↥M := unitri5.comap π
  have hU : IsPGroup 2 ↥unitri5 := IsPGroup.of_card card_unitri5
  have hT : IsPGroup 2 ↥T := by
    intro t
    obtain ⟨k, hk⟩ := hU ⟨π t, t.2⟩
    have hk' : π ((t : ↥M) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hkF : (t : ↥M) ^ 2 ^ k ∈ (F4 j4Facts.mat chkF_true).subgroupOf M := by
      rw [← hker]
      exact hk'
    rw [Subgroup.mem_subgroupOf] at hkF
    obtain ⟨k', hk''⟩ := isPGroup_F4 j4Facts.mat chkF_true ⟨_, hkF⟩
    refine ⟨k + k', Subtype.ext (Subtype.ext ?_)⟩
    have e := congrArg Subtype.val hk''
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at e
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
    simpa using e
  have hS0 : IsPGroup 2 ↥(S.subgroupOf M) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let PS : Sylow 2 ↥M := hS0.toSylow hS.2.2
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥M PS Q
  have hTy : ∀ t ∈ T, ∃ s ∈ S, ((t : ↥M) : J) = (y : J) * s * (y : J)⁻¹ := by
    intro t ht
    have h1 : t ∈ (Q : Subgroup ↥M) := hTQ ht
    rw [← hy, Sylow.coe_subgroup_smul] at h1
    obtain ⟨s, hs, hst⟩ := (Subgroup.mem_smul_pointwise_iff_exists t (MulAut.conj y) _).1 h1
    have hs' : s ∈ S.subgroupOf M := hs
    rw [Subgroup.mem_subgroupOf] at hs'
    refine ⟨(s : J), hs', ?_⟩
    rw [← hst]
    simp [MulAut.conj_apply]
  refine ⟨(y : J), y.2, fun x hxF hxS => ?_⟩
  have hx' : (y : J) * x * (y : J)⁻¹ ∈ F4 j4Facts.mat chkF_true := by
    have := hFn.conj_mem ⟨x, F4_le_M4 _ _ hxF⟩ (by rw [Subgroup.mem_subgroupOf]; exact hxF) y
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨v, hv⟩ := (mem_eSub_iff hb _).1 hx'
  obtain ⟨c, hc, rfl⟩ := exists_codeVec v
  have hfix : ∀ p : Fin 10, psiMat (tvEl p) *ᵥ codeVec c = codeVec c := by
    intro p
    obtain ⟨t, ht⟩ := piM4_surjective j4Facts.mat chkF_true (tvEl p)
    have htT : t ∈ T := by
      show π t ∈ unitri5
      rw [ht]
      exact tvEl_mem p
    obtain ⟨s, hs, hts⟩ := hTy t htT
    have hsx : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxS s hs
    have hcomm : (t : J) * ((y : J) * x * (y : J)⁻¹) * (t : J)⁻¹ =
        (y : J) * x * (y : J)⁻¹ := by
      have hts' : (t : J) = (y : J) * s * (y : J)⁻¹ := hts
      rw [hts']
      calc (y : J) * s * (y : J)⁻¹ * ((y : J) * x * (y : J)⁻¹) * ((y : J) * s * (y : J)⁻¹)⁻¹
          = (y : J) * (s * x) * s⁻¹ * (y : J)⁻¹ := by group
        _ = (y : J) * x * (y : J)⁻¹ := by rw [hsx]; group
    have h2 := piM4_conj j4Facts.mat chkF_true t (codeVec c)
    rw [hv, hcomm, ← hv, ht] at h2
    exact (eElt_injective hb h2).symm
  have hc' : c = 0 ∨ c = 512 := by
    refine fixU_chk c hc fun p => ?_
    have e2 := congrArg altV (hfix p)
    rw [altV_psiMat_codeVec (rfl : mat (tvEl p)⁻¹ = D35Chk.bm (tvU p)), altV_codeVec] at e2
    exact D35Chk.bm_inj (D35Chk.bmul_lt _ _) (D35Chk.colSum_lt D35Chk.altE_lt c) e2
  have hxe : x = (y : J)⁻¹ * ((y : J) * x * (y : J)⁻¹) * (y : J) := by group
  rcases hc' with rfl | rfl
  · left
    have h0 : codeVec 0 = 0 := by
      funext i
      simp [codeVec]
    rw [h0, eElt_zero] at hv
    rw [hxe, ← hv]
    group
  · right
    rw [hxe, ← hv]

theorem exists_M4_conj_z1
    {S : Subgroup J} (hS : IsSylowTwoOf S CFSG.Quasithin.KGJ4.M4) {z : J}
    (hzF : z ∈ F4 j4Facts.mat chkF_true) (hz1 : z ≠ 1)
    (hzS : z ∈ Subgroup.centralizer (S : Set J)) :
    ∃ m ∈ CFSG.Quasithin.KGJ4.M4, z = m * z1Elt * m⁻¹ := by
  obtain ⟨-, -, -, hu, -⟩ := chkGen_facts
  obtain ⟨y, hyM, hy⟩ := fix_F_of_sylow_conj hS
  rcases hy z hzF hzS with h | h
  · exact absurd h hz1
  · have huM : uElt ∈ CFSG.Quasithin.KGJ4.M4 := by
      rw [uElt_def]
      exact wordProd_mem _ m4gen_mem _
    refine ⟨y⁻¹ * uElt, CFSG.Quasithin.KGJ4.M4.mul_mem (CFSG.Quasithin.KGJ4.M4.inv_mem hyM) huM, ?_⟩
    rw [h, eElt_fJ_nine, ← hu]
    group

end L52

end CFSG.Quasithin.H13.Ch4.G443J4

end
