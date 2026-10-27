module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Index
public import CFSG.RankThree.GF2n.Stroth80.Sec53CentralizerProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.relIndex_LB_CN_sp (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ (2 * m - 1) := by
  have hRoot : Stroth310RootStatement := stroth310Root_of_34 h34
  obtain ⟨K, iF, iFin, hK, φ, hφ, hker, hact⟩ := hV
  letI := iF
  letI := iFin
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  obtain ⟨u, hu0, -, hL, -⟩ :=
    Ctx.sp_points_core h34 hRoot hc hs hK hm φ hφ hker ψ hψ
  rw [← HS6.card_map_LB_eq_relIndex hc hs.mem φ hker, hL, CFSG.ClassicalGroups.Symplectic.card_LspGL hu0, hK]

theorem Ctx.card_LB_inf_CN_sp (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m) :
    Nat.card ↥(LB M Q B ⊓ hc.CN t) =
      Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 2 * m) := by
  have h35 := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) := h35.2.2.1
  have hrel : (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ (2 * m - 1) :=
    Ctx.relIndex_LB_CN_sp h34 hc hs hm hV
  have hrelmul := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  have hrelmulH : Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (2 * m - 1) =
      Nat.card (LB M Q B) := by
    rw [inf_comm, ← hrel, mul_comm]
    exact hrelmul
  have hQH : Q ≤ LB M Q B ⊓ hc.CN t := le_inf sec39_Q_le_LB (hc.Q_le_CN hs.mem)
  have hcardQH : Nat.card ↥Q ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) :=
    Nat.card_le_card_of_injective
      (fun x : ↥Q => (⟨x.1, hQH x.2⟩ : ↥(LB M Q B ⊓ hc.CN t)))
      (fun a b h => Subtype.ext
        (congrArg (fun x : ↥(LB M Q B ⊓ hc.CN t) => (x : G)) h))
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have h2mn : 2 * m ≤ n := by
    have hkey : Nat.card Z ^ (2 * m - 1) ≤ Nat.card Z ^ (n - 1) := by
      refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥Q))
      calc Nat.card Q * Nat.card Z ^ (2 * m - 1)
          ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (2 * m - 1) :=
            Nat.mul_le_mul_right _ hcardQH
        _ = Nat.card (LB M Q B) := hrelmulH
        _ = Nat.card Q * Nat.card Z ^ (n - 1) := hcardLB
    have := (Nat.pow_le_pow_iff_right hq2).mp hkey
    omega
  have hexp : Nat.card Z ^ (n - 2 * m) * Nat.card Z ^ (2 * m - 1) =
      Nat.card Z ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have htarget : Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 1) =
      Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 2 * m) *
        Nat.card Z ^ (2 * m - 1) := by
    rw [mul_assoc, hexp]
  refine Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := ↥Z)) (2 * m - 1)) ?_
  calc Nat.card Z ^ (2 * m - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t)
      = Nat.card (LB M Q B) := by rw [mul_comm]; exact hrelmulH
    _ = Nat.card Q * Nat.card Z ^ (n - 1) := hcardLB
    _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 1) := by rw [hs.width]
    _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 2 * m) *
        Nat.card Z ^ (2 * m - 1) := htarget
    _ = Nat.card Z ^ (2 * m - 1) *
        (Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 2 * m)) := by ring


theorem Ctx.elation_fixed_card_le (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (ht : t ∈ LB M Q B)
    {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ}
    {W : Submodule K M₀.E} [FiniteDimensional K W] {b : W}
    (θ : ↥(LB M Q B) →* (W ≃ₗ[K] W))
    (hkerθ : ∀ g, θ g = 1 ↔ (g : G) ∈ Q)
    (hb0 : b ≠ 0)
    (hKZ : Nat.card K = Nat.card Z)
    (hWdim : Module.finrank K W = n)
    (hHcard : Nat.card ↥(LB M Q B ⊓ hc.CN t) =
      Nat.card ↥(Q.subgroupOf (LB M Q B ⊓ hc.CN t)) * Nat.card K ^ (n - 2 * m))
    (Fd : ↥(LB M Q B) → Module.Dual K W)
    (hFd : ∀ g u, θ g u = u + Fd g u • b)
    (hadd : ∀ g h, Fd (g * h) = Fd g + Fd h)
    (hFd1 : Fd 1 = 0) :
    Nat.card ↥((Submodule.span K (Set.range (fun g : ↥(LB M Q B ⊓ hc.CN t) =>
      Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator)
      ≤ Nat.card K ^ (2 * m) := by
  classical
  set H : Subgroup G := LB M Q B ⊓ hc.CN t with hH
  let incl : ↥H →* ↥(LB M Q B) := Subgroup.inclusion inf_le_left
  let f : Additive ↥H →+ Module.Dual K W :=
    { toFun := fun g => Fd (incl (Additive.toMul g))
      map_zero' := by simp [hFd1]
      map_add' := by
        intro g h
        simpa using hadd (incl (Additive.toMul g)) (incl (Additive.toMul h)) }
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hK2 : 2 ≤ Nat.card K := by rw [hKZ]; exact hq2
  have hQH : Q ≤ H := le_inf sec39_Q_le_LB (hc.Q_le_CN ht)
  have hkerf : f.ker = Subgroup.toAddSubgroup (Q.subgroupOf H) := by
    ext g
    rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have hθ1 : θ (incl (Additive.toMul g)) = 1 := by
        refine LinearEquiv.ext fun u => ?_
        have hg' : Fd (incl (Additive.toMul g)) = 0 := hg
        have := hFd (incl (Additive.toMul g)) u
        rw [hg'] at this
        simpa using this
      exact (hkerθ (incl (Additive.toMul g))).mp hθ1
    · intro hg
      have hgQ : (incl (Additive.toMul g) : G) ∈ Q := hg
      have hθ1 : θ (incl (Additive.toMul g)) = 1 :=
        (hkerθ (incl (Additive.toMul g))).mpr hgQ
      refine LinearMap.ext fun u => ?_
      have h := hFd (incl (Additive.toMul g)) u
      rw [hθ1] at h
      have h' : u = u + Fd (incl (Additive.toMul g)) u • b := by simpa using h
      have h0 : Fd (incl (Additive.toMul g)) u • b = 0 := by
        have h'' : u + 0 = u + Fd (incl (Additive.toMul g)) u • b := by
          rw [add_zero]; exact h'
        exact (add_left_cancel h'').symm
      rcases smul_eq_zero.mp h0 with hc' | hb
      · exact hc'
      · exact absurd hb hb0
  have hsubQH : Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hkerCard : Nat.card ↥f.ker = Nat.card Q := by
    rw [hkerf]
    exact hsubQH
  have hrange : Nat.card ↥f.range = Nat.card K ^ (n - 2 * m) := by
    have hmain := AddSubgroup.card_ker_mul_card_range f
    rw [hkerCard] at hmain
    have hcardAdd : Nat.card (Additive ↥H) = Nat.card ↥H :=
      Nat.card_congr (Additive.ofMul (α := ↥H))
    have hH' : Nat.card ↥H = Nat.card Q * Nat.card K ^ (n - 2 * m) := by
      rw [hHcard, hsubQH]
    have hmain2 : Nat.card ↥Q * Nat.card ↥f.range =
        Nat.card Q * Nat.card K ^ (n - 2 * m) := by
      calc Nat.card ↥Q * Nat.card ↥f.range = Nat.card (Additive ↥H) := hmain
        _ = Nat.card ↥H := hcardAdd
        _ = Nat.card Q * Nat.card K ^ (n - 2 * m) := hH'
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Q)) hmain2
  let D : Submodule K (Module.Dual K W) :=
    Submodule.span K (f.range : Set (Module.Dual K W))
  have hdimD : n - 2 * m ≤ Module.finrank K ↥D := by
    haveI : Finite (Module.Dual K W) := Module.finite_of_finite K
    haveI : Finite ↥f.range :=
      Finite.of_injective (fun x : ↥f.range => (x : Module.Dual K W)) Subtype.val_injective
    haveI : Finite ↥D :=
      Finite.of_injective (fun x : ↥D => (x : Module.Dual K W)) Subtype.val_injective
    have hle : Nat.card ↥f.range ≤ Nat.card ↥D :=
      Nat.card_le_card_of_injective
        (fun x : ↥f.range => (⟨x.1, Submodule.subset_span x.2⟩ : ↥D))
        (fun a b h => Subtype.ext
          (congrArg (fun x : ↥D => (x : Module.Dual K W)) h))
    have hcardD : Nat.card ↥D = Nat.card K ^ Module.finrank K ↥D :=
      Module.natCard_eq_pow_finrank (K := K) (V := ↥D)
    rw [hrange, hcardD] at hle
    exact (Nat.pow_le_pow_iff_right hK2).mp hle
  have hdimF : Module.finrank K ↥D.dualCoannihilator ≤ 2 * m := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq D
    rw [hWdim] at h
    omega
  change Nat.card ↥D.dualCoannihilator ≤ Nat.card K ^ (2 * m)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥D.dualCoannihilator)]
  exact Nat.pow_le_pow_right (by omega : 1 ≤ Nat.card K) hdimF


theorem Ctx.card_inf_QB_S_le (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (S : Subgroup G) (hS : ∀ s, s ∈ S ↔ ∀ x ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅s, x⁆ ∈ Z) :
    Nat.card ↥((Q ⊓ QB B) ⊓ S) ≤ Nat.card Z ^ (2 * m + 1) := by
  classical
  have h35 := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := h35.2.2.2
  have hHcard := Ctx.card_LB_inf_CN_sp h34 hc hs hm hV
  obtain ⟨K, iF, iFin, iCh, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF
  letI := iFin
  letI := iCh
  obtain ⟨W, b, θ, hW, hb0, hB, hfix, hel, hkerθ, hWdim, hSθ, hSagree⟩ :=
    hc.exists_elation_action hs.width hs.n_gt hs.noA2 hcardL hD
  have hθker : θ.ker = Q.subgroupOf (LB M Q B) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hkerθ g
  have hcardθ : Nat.card ↥(LB M Q B) =
      Nat.card θ.ker * Nat.card K ^ (Module.finrank K W - 1) := by
    have hsubQ : Nat.card ↥(Q.subgroupOf (LB M Q B)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Q_le_LB).toEquiv
    rw [hθker, hWdim, hsubQ, h35.2.2.1, hD.card]
  obtain ⟨Fd, hFd, hadd, hFd1, hFdann, hFdsurj⟩ :=
    elation_dual_data (b := (b : W)) hb0 θ hfix hel hcardθ
  set H : Subgroup G := LB M Q B ⊓ hc.CN t with hHdef
  have hsubQH : Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_inf sec39_Q_le_LB (hc.Q_le_CN hs.mem))).toEquiv
  have hHcardK : Nat.card ↥H =
      Nat.card ↥(Q.subgroupOf H) * Nat.card K ^ (n - 2 * m) := by
    rw [hHcard, hsubQH, hs.width, hD.card]
  have hFbound : Nat.card ↥((Submodule.span K (Set.range
      (fun g : ↥H => Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator)
      ≤ Nat.card Z ^ (2 * m) := by
    have := Ctx.elation_fixed_card_le hc hs.mem θ hkerθ hb0 hD.card hWdim hHcardK
      Fd hFd hadd hFd1
    rwa [hD.card] at this
  have hZS : Z ≤ S := by
    intro z hz
    rw [hS z]
    intro x hx
    have hzx : ⁅z, x⁆ ∈ Z := by
      have hxz : ⁅x, z⁆ ∈ Z := (Ctx.mem_CN.mp hx.2).2 z (sec39_Z_le_Vt hz)
      have := Z.inv_mem hxz
      rwa [commutatorElement_inv] at this
    exact hzx
  have hcommHy : ∀ g : ↥H, ∀ y : G, y ∈ (Q ⊓ QB B) ⊓ S → ⁅(g : G), y⁆ ∈ Z := by
    intro g y hy
    obtain ⟨hyL, hyS⟩ := hy
    obtain ⟨s, hsQB, q, hq, hgsq⟩ := hc.exists_mul_of_mem_LB g.2.1
    have hqN : q ∈ hc.CN t := hc.Q_le_CN hs.mem hq
    have hsN : s ∈ hc.CN t := by
      have hseq : s = (g : G) * q⁻¹ := by rw [hgsq]; group
      rw [hseq]
      exact (hc.CN t).mul_mem g.2.2 ((hc.CN t).inv_mem hqN)
    have hys : ⁅y, s⁆ ∈ Z := (hS y).mp hyS s ⟨hsQB, hsN⟩
    have hsy : ⁅s, y⁆ ∈ Z := by
      have := Z.inv_mem hys
      rwa [commutatorElement_inv] at this
    have hqy : ⁅q, y⁆ ∈ Z := by
      have := Subgroup.commutator_mem_commutator hq hyL.1
      rwa [hc.hyp.special.1] at this
    have hconj : s * ⁅q, y⁆ * s⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsQB.2) ⁅q, y⁆).mp hqy
    show ⁅(g : G), y⁆ ∈ Z
    rw [hgsq, commutatorElement_mul_left_eq_conj_mul]
    exact Z.mul_mem hconj hsy
  have hFdfix : ∀ g : ↥H, ∀ y : G, y ∈ (Q ⊓ QB B) ⊓ S →
      ∀ hyW : M₀.π y ∈ W,
      Fd (Subgroup.inclusion inf_le_left g) ⟨M₀.π y, hyW⟩ = 0 := by
    intro g y hy hyW
    have hyL : y ∈ Q ⊓ QB B := hy.1
    have hcomm : ⁅((Subgroup.inclusion inf_le_left g : ↥(LB M Q B)) : G), y⁆ ∈ Z :=
      hcommHy g y hy
    have hfixθ : θ (Subgroup.inclusion inf_le_left g) ⟨M₀.π y, hyW⟩ =
        ⟨M₀.π y, hyW⟩ :=
      Subtype.ext ((hSθ (Subgroup.inclusion inf_le_left g) y hyL hyW).mpr hcomm)
    have h := hFd (Subgroup.inclusion inf_le_left g) ⟨M₀.π y, hyW⟩
    rw [hfixθ] at h
    have h0 : Fd (Subgroup.inclusion inf_le_left g) ⟨M₀.π y, hyW⟩ • b = 0 := by
      have h' : (⟨M₀.π y, hyW⟩ : W) + 0 =
          (⟨M₀.π y, hyW⟩ : W) +
            Fd (Subgroup.inclusion inf_le_left g) ⟨M₀.π y, hyW⟩ • b := by
        rw [add_zero]
        exact h
      exact (add_left_cancel h').symm
    rcases smul_eq_zero.mp h0 with hc' | hb
    · exact hc'
    · exact absurd hb hb0
  have hmemF : ∀ y : G, y ∈ (Q ⊓ QB B) ⊓ S → ∀ hyW : M₀.π y ∈ W,
      (⟨M₀.π y, hyW⟩ : W) ∈
        (Submodule.span K (Set.range (fun g : ↥H =>
          Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator := by
    intro y hy hyW
    rw [Submodule.mem_dualCoannihilator]
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro f ⟨g, rfl⟩
      exact hFdfix g y hy hyW
    · simp
    · intro f1 f2 _ _ h1 h2
      simp only [LinearMap.add_apply, h1, h2, add_zero]
    · intro c f _ hf'
      simp only [LinearMap.smul_apply, hf', smul_zero]
  have hXQ : (Q ⊓ QB B) ⊓ S ≤ Q := inf_le_left.trans inf_le_left
  have hZX : Z ≤ (Q ⊓ QB B) ⊓ S :=
    le_inf (le_inf hc.Z_le_Q hc.Z_le_QB.1) hZS
  have hXcard : Nat.card ↥((Q ⊓ QB B) ⊓ S) =
      Nat.card Z * Nat.card ↥(M₀.img ((Q ⊓ QB B) ⊓ S)) :=
    M₀.card_eq hXQ hZX
  have himgcard : Nat.card ↥(M₀.img ((Q ⊓ QB B) ⊓ S)) ≤
      Nat.card ↥((Submodule.span K (Set.range (fun g : ↥H =>
        Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator) := by
    haveI : Finite ↥((Submodule.span K (Set.range (fun g : ↥H =>
        Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator) :=
      Module.finite_of_finite K
    refine Nat.card_le_card_of_injective
      (fun e : ↥(M₀.img ((Q ⊓ QB B) ⊓ S)) =>
        let h : ∃ x, x ∈ ((Q ⊓ QB B) ⊓ S) ∧ x ∈ Q ∧ M₀.π x = e.1 :=
          (M₀.mem_img).mp e.2
        let heW : e.1 ∈ W := (hW e.1).mpr (by
          obtain ⟨y, hyX, hyQ, hyx⟩ := h
          rw [← hyx]
          exact M₀.pi_mem_img hyX.1 hyQ)
        ⟨⟨e.1, heW⟩, by
          obtain ⟨y, hyX, hyQ, hyx⟩ := h
          have hyW : M₀.π y ∈ W := (hW _).mpr (M₀.pi_mem_img hyX.1 hyQ)
          have hEq : (⟨M₀.π y, hyW⟩ : W) = ⟨e.1, heW⟩ := Subtype.ext hyx
          rw [← hEq]
          exact hmemF y hyX hyW⟩) ?_
    · intro a b hab
      exact Subtype.ext
        (congrArg (fun x : ↥((Submodule.span K (Set.range (fun g : ↥H =>
          Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator) =>
            ((x : W) : M₀.E)) hab)
  calc Nat.card ↥((Q ⊓ QB B) ⊓ S)
      = Nat.card Z * Nat.card ↥(M₀.img ((Q ⊓ QB B) ⊓ S)) := hXcard
    _ ≤ Nat.card Z * Nat.card ↥((Submodule.span K (Set.range (fun g : ↥H =>
        Fd (Subgroup.inclusion inf_le_left g)))).dualCoannihilator) :=
        Nat.mul_le_mul_left _ himgcard
    _ ≤ Nat.card Z * Nat.card Z ^ (2 * m) := Nat.mul_le_mul_left _ hFbound
    _ = Nat.card Z ^ (2 * m + 1) := by rw [mul_comm, ← pow_succ]


theorem Ctx.centLam_sp_vone
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E,
      e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓
      imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) := by
  have hZM : Z ≤ M := hc.Z_le_Q.trans hc.hyp.Q_normal.1
  have hZCN : Z ≤ hc.CN t := hc.Z_le_Q.trans (hc.Q_le_CN hs.mem)
  have hZN : Z ≤ (QB B ⊓ M) ⊓ hc.CN t :=
    le_inf (le_inf hc.Z_le_QB.1 hZM) hZCN
  obtain ⟨S, hS⟩ := sec51_exists_subgroup ((QB B ⊓ M) ⊓ hc.CN t) Z hZN
  exact Ctx.centLam_sp_vone_of_bound h34 hRoot h51 hc hs hm hV hr hplane hD T hTmem hBC
    S hS (Ctx.card_inf_QB_S_le h34 hc hs hm hV S hS)

end CFSG.RankThree.GF2n.Stroth80
