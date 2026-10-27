module

public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement
open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem GammaReg.eq_of_γ_eq (R : GammaReg QF V γ) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (h : γ a = γ b) : a = b := by
  have h1 : γ (a * b⁻¹) = γ a + γ b⁻¹ := R.add a ha b⁻¹ (V.inv_mem hb)
  have h2 : γ b + γ b⁻¹ = 0 := by
    rw [← R.add b hb b⁻¹ (V.inv_mem hb), mul_inv_cancel]
    exact R.one
  have h3 : a * b⁻¹ = 1 := R.inj _ (V.mul_mem ha (V.inv_mem hb)) (by rw [h1, h]; exact h2)
  exact mul_inv_eq_one.mp h3

namespace QuadModel

theorem exists_comm_eq_one (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ) {t x : G}
    (ht : t ∈ QF) (hx : x ∈ QF) (hx0 : M₀.π x ≠ 0) (hind : ∀ s : K, M₀.π t ≠ s • M₀.π x)
    {c : G} (hc : c ∈ V) : ∃ y ∈ QF, ⁅y, t⁆ = c ∧ ⁅y, x⁆ = 1 := by
  obtain ⟨h, hhx, hht⟩ : ∃ h, M₀.B h (M₀.π x) = 0 ∧ M₀.B h (M₀.π t) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs⟩ := exists_smul_of_orthogonal hx0 (v := M₀.π t) (fun h hh => by
      rw [B_comm, hcon h hh, neg_zero])
    exact hind s hs
  obtain ⟨y, hyQ, hy⟩ := M₀.π_surj ((γ c / M₀.B h (M₀.π t)) • h)
  refine ⟨y, hyQ, ?_, ?_⟩
  · refine R.eq_of_γ_eq (M₀.comm_mem y hyQ t ht) hc ?_
    rw [M₀.comm_eq y hyQ t ht, hy, map_smul, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hht]
  · refine R.inj _ (M₀.comm_mem y hyQ x hx) ?_
    rw [M₀.comm_eq y hyQ x hx, hy, map_smul, LinearMap.smul_apply, hhx, smul_zero]

end QuadModel

end CFSG.RankThree.GF2n.Tim79

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B C : Subgroup G}

theorem QB_Z_eq (hc : Ctx M Q Z B) : QB Z = Q := by
  unfold QB
  rw [hc.hyp.normalizer_Z.1, hc.hyp.hQ]
  unfold inSubgroup
  rw [hc.hyp.fitting]

theorem Ctx.exists_mem_comm_eq (hB : Ctx M Q Z B) {b c : G} (hb : b ∈ B) (hcQ : c ∈ Q)
    (hbc : b * c ≠ c * b) {t : G} (ht : t ∈ Z) : ∃ β ∈ B, ⁅β, c⁆ = t := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hB.hyp
  obtain ⟨b₀, -, -, hline, -⟩ := hB.dictB h
  obtain ⟨s₀, hs₀⟩ := (hline _).mp (M₀.pi_mem_img hb (hB.le hb))
  have hcomm : M₀.B (M₀.π b) (M₀.π c) ≠ 0 := fun h0 =>
    hbc ((M₀.comm_iff_B h.reg (hB.le hb) hcQ).mpr h0)
  have hbc0 : M₀.B b₀ (M₀.π c) ≠ 0 := by
    intro h0
    apply hcomm
    rw [hs₀, map_smul, LinearMap.smul_apply, h0, smul_zero]
  obtain ⟨β, hβB, hβQ, hβ⟩ := (hline ((γ t / M₀.B b₀ (M₀.π c)) • b₀)).mpr ⟨_, rfl⟩
  refine ⟨β, hβB, ?_⟩
  refine h.reg.eq_of_γ_eq (M₀.comm_mem β hβQ c hcQ) ht ?_
  rw [M₀.comm_eq β hβQ c hcQ, hβ, map_smul, LinearMap.smul_apply, smul_eq_mul,
    div_mul_cancel₀ _ hbc0]

theorem Ctx.exists_mem_QB_comm_eq_one (hC : Ctx M Q Z C) {t x c : G} (ht : t ∈ Z)
    (ht1 : t ≠ 1) (hc : c ∈ C) (hxC : x ∈ QB C) (hxQ : x ∉ Q) :
    ∃ y ∈ QB C, ⁅y, t⁆ = c ∧ ⁅y, x⁆ = 1 := by
  obtain ⟨g, hg⟩ := hC.conj
  obtain ⟨-, hQC⟩ := Ctx.QB_eq hC hg
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hC.hyp
  have hZC : Z ⊓ C = ⊥ := hC.inf_eq_bot
  have hZQC : Z ≤ conjSubgroup g Q := hQC ▸ hC.Z_le_QB.1
  have htQ : t ∈ conjSubgroup g Q := hZQC ht
  have hxQg : x ∈ conjSubgroup g Q := hQC ▸ hxC
  have hcg : c ∈ conjSubgroup g Z := hg ▸ hc
  have hZ' : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hne : conjSubgroup g⁻¹ (conjSubgroup g Z) ≠ conjSubgroup g Z := by
    rw [hZ', ← hg]
    exact hC.ne.symm
  have hle : conjSubgroup g⁻¹ (conjSubgroup g Z) ≤ conjSubgroup g Q := by
    rw [hZ']
    exact hZQC
  obtain ⟨e, he0, he⟩ := (h.conj g).line g⁻¹ hne hle
  rw [hZ'] at he
  set M₁ := M₀.conj g
  have hx0 : M₁.π x ≠ 0 := by
    intro h0
    have := (M₁.π_ker x hxQg).mp h0
    exact hxQ (hC.le (hg ▸ this))
  have hind : ∀ s : GaloisField 2 n, M₁.π t ≠ s • M₁.π x := by
    intro s hs
    have ht0 : M₁.π t ≠ 0 := by
      intro h0
      have h1 : t ∈ conjSubgroup g Z := (M₁.π_ker t htQ).mp h0
      have h2 : t ∈ Z ⊓ C := ⟨ht, hg ▸ h1⟩
      rw [hZC, Subgroup.mem_bot] at h2
      exact ht1 h2
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact ht0 (by rw [hs, zero_smul])
    obtain ⟨s₁, hs₁⟩ := (he _).mp (M₁.pi_mem_img ht htQ)
    have hxim : M₁.π x ∈ M₁.img Z := by
      rw [he]
      refine ⟨s⁻¹ * s₁, ?_⟩
      rw [mul_smul, ← hs₁, hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hxZC : M₁.π x ∈ M₁.img (Z ⊔ conjSubgroup g Z) := M₁.img_mono le_sup_left hxim
    have := (M₁.mem_img_iff le_sup_right hxQg).mp hxZC
    exact hxQ (sup_le hC.Z_le_Q (hg ▸ hC.le) this)
  obtain ⟨y, hy, h1, h2⟩ := M₁.exists_comm_eq_one (h.conj g).reg htQ hxQg hx0 hind hcg
  exact ⟨y, hQC ▸ hy, h1, h2⟩

theorem Ctx.core_3_6 (hB : Ctx M Q Z B) (hC : Ctx M Q Z C)
    (hBC : ∃ b ∈ B, ∃ c ∈ C, b * c ≠ c * b)
    {x : G} (hxC : x ∈ QB C) (hxM : x ∈ M) (hxQ : x ∉ Q) (hxB : ∀ b ∈ B, ⁅x, b⁆ ∈ Z) :
    False := by
  obtain ⟨b, hb, c, hc, hbc⟩ := hBC
  obtain ⟨g, hg⟩ := hC.conj
  obtain ⟨-, hQC⟩ := Ctx.QB_eq hC hg
  have hstep1 : ∀ β ∈ B, x ∈ QB (conjSubgroup β C) := by
    intro β hβ
    rw [QB_conj, mem_conjSubgroup]
    have hz : ⁅x, β⁆ ∈ Z := hxB β hβ
    have hzβ : ⁅x, β⁆ * β = β * ⁅x, β⁆ := hB.hyp.toHyp79.V_central hz (hB.le hβ)
    have h1 : β⁻¹ * x * β = ⁅x, β⁆ * x := by
      have h2 : β⁻¹ * (⁅x, β⁆ * β) = ⁅x, β⁆ := by rw [hzβ, inv_mul_cancel_left]
      calc β⁻¹ * x * β = β⁻¹ * (⁅x, β⁆ * β) * x := by
            rw [commutatorElement_def]; group
        _ = ⁅x, β⁆ * x := by rw [h2]
    rw [h1]
    exact (QB C).mul_mem (hC.Z_le_QB.1 hz) hxC
  obtain ⟨t, htZ, ht1⟩ : ∃ t ∈ Z, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hZ : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
    have h4 := hB.hyp.q4
    rw [hZ, Subgroup.card_bot] at h4
    omega
  obtain ⟨β, hβB, hβ⟩ := hB.exists_mem_comm_eq hb (hC.le hc) hbc htZ
  obtain ⟨y, hy, hyt, hyx⟩ := hC.exists_mem_QB_comm_eq_one htZ ht1 hc hxC hxQ
  have hcc : c * c = 1 := by
    have := hC.isElemAbelian_B.2 c hc
    rwa [pow_two] at this
  have hcentral : ∀ w ∈ QB C, c * w = w * c := fun w hw =>
    hC.hyp.toHyp79.conj_central g (hg ▸ hc) (hQC ▸ hw)
  have hkey : y * (β * c * β⁻¹) * y⁻¹ = t := by
    have e1 : β * c * β⁻¹ = t * c := by
      rw [← hβ, commutatorElement_def]; group
    have e2 : y * t * y⁻¹ = c * t := by
      rw [commutatorElement_def] at hyt
      rw [← hyt]; group
    have e3 : y * c * y⁻¹ = c := by
      rw [← hcentral y hy]; group
    calc y * (β * c * β⁻¹) * y⁻¹ = (y * t * y⁻¹) * (y * c * y⁻¹) := by rw [e1]; group
      _ = c * t * c := by rw [e2, e3]
      _ = t * (c * c) := by rw [hcentral t (hC.Z_le_QB.1 htZ)]; group
      _ = t := by rw [hcc, mul_one]
  have hC''eq : conjSubgroup y (conjSubgroup β C) = conjSubgroup (y * β * g) Z := by
    rw [hg, conjSubgroup_mul, conjSubgroup_mul]
  have htC'' : t ∈ conjSubgroup y (conjSubgroup β C) := by
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have : β⁻¹ * (y⁻¹ * t * y) * β = c := by
      rw [← hkey]; group
    rw [this]
    exact hc
  have hTI : conjSubgroup (y * β * g) Z = Z := by
    apply conjSubgroup_eq_of_isTI hB.hyp.ti
    intro hbot
    have h1 : t ∈ Z ⊓ conjSubgroup (y * β * g) Z := ⟨htZ, hC''eq ▸ htC''⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact ht1 h1
  have hxC'' : x ∈ QB (conjSubgroup y (conjSubgroup β C)) := by
    rw [QB_conj, mem_conjSubgroup]
    have hyx' : y⁻¹ * x * y = x := by
      have h2 : y * x = x * y := commutatorElement_eq_one_iff_mul_comm.mp hyx
      rw [mul_assoc, ← h2, inv_mul_cancel_left]
    rw [hyx']
    exact hstep1 β hβB
  rw [hC''eq, hTI, QB_Z_eq hB] at hxC''
  exact hxQ hxC''

theorem stroth_3_6_of_3_5 (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {h : G} (hh : h ∈ M)
    (hne : conjSubgroup h (LB M Q B) ⊓ Subgroup.normalizer (LB M Q B : Set G) ≠ Q) :
    ∀ b ∈ B, ∀ c ∈ conjSubgroup h B, b * c = c * b := by
  by_contra hnot
  push Not at hnot
  have hC := hc.conj_of_mem hh
  have hQle : Q ≤ conjSubgroup h (LB M Q B) ⊓ Subgroup.normalizer (LB M Q B : Set G) := by
    refine le_inf ((hc.conj_Q_eq hh).symm.le.trans (Subgroup.map_mono le_sup_left)) ?_
    exact fun y hy => Subgroup.le_normalizer (le_sup_left (a := Q) hy)
  obtain ⟨x, hx, hxQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQle (Ne.symm hne))
  have hxLC : x ∈ LB M Q (conjSubgroup h B) := by rw [hc.LB_conj hh]; exact hx.1
  obtain ⟨s, hs, y, hy, rfl⟩ := hC.exists_mul_of_mem_LB hxLC
  have hsQ : s ∉ Q := fun h' => hxQ (Q.mul_mem h' hy)
  have hyN : y ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    Subgroup.le_normalizer (le_sup_left (a := Q) hy)
  have hsN : s ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    have := Subgroup.mul_mem _ hx.2 (Subgroup.inv_mem _ hyN)
    simpa using this
  have hsV : ∀ u ∈ B, s * u * s⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
    intro u hu
    have huC : u ∈ CQt Q Z (LB M Q B) := by rw [h35]; exact Subgroup.mem_sup_left hu
    have := hc.conj_mem_CQt hs.2 hsN huC
    rw [h35] at this
    exact this
  obtain ⟨g, hg⟩ := hC.conj
  have hsQB : s ∈ conjSubgroup g Q := (Ctx.QB_eq hC hg).2 ▸ hs.1
  have hs2 : s ^ 2 ∈ Q := hC.le (hg ▸ hC.hyp.toHyp79.sq_mem_conj g hsQB)
  have hsc : ∀ z ∈ Z, s * z * s⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (hC.QB_inf_M_le hs) z hz
    rw [← this]
    group
  have hBZ := hc.comm_mem_Z_of_normalizes hs.2 hsc hs2 hsV
  exact hc.core_3_6 hC hnot hs.1 hs.2 hsQ hBZ

end CFSG.RankThree.GF2n.Stroth80
