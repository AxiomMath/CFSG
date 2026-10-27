module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoTensor

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure TensorModel (M Q Z B : Subgroup G) where
  K : Type
  [instFieldK : Field K]
  [instFiniteK : Finite K]
  [instCharK : CharP K 2]
  γ : G → K
  M₀ : Tim79.QuadModel Q Z K γ
  gm : GlobalModelData M Q Z γ M₀
  F : Type
  [instFieldF : Field F]
  [instFiniteF : Finite F]
  [instCharF : CharP F 2]
  card_F : Nat.card F = Nat.card Z
  ε : K ≃+* F
  Φ : M₀.E ≃+ Matrix (Fin 2) (Fin 2) F
  φ : ↥(Lgen M (LB M Q B)) →* GL (Fin 2) F
  φ_range : φ.range = StatedSL 2 F
  φ_ker : φ.ker = Q.subgroupOf (Lgen M (LB M Q B))
  smul : ∀ (c : K) (e : M₀.E), Φ (c • e) = ε c • Φ e
  qf : ∀ e : M₀.E, ε (M₀.Qf e) = (Φ e).det
  act : ∀ (s : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
    Φ (M₀.π ((s : G) * x * (s : G)⁻¹)) = (φ s : Matrix (Fin 2) (Fin 2) F) * Φ (M₀.π x)

attribute [instance] TensorModel.instFieldK TensorModel.instFiniteK TensorModel.instCharK
  TensorModel.instFieldF TensorModel.instFiniteF TensorModel.instCharF

private theorem charP_two_of_natCard_eq_two_pow {K : Type} [Field K] [Finite K] {k : ℕ}
    (h : Nat.card K = 2 ^ k) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 2 ^ k := by
    rw [← h, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow hdvd
  have : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact ringChar.eq_iff.mp this

theorem exists_tensorModel (hc : Ctx M Q Z B) {V₁ V₂ : Subgroup G}
    (hS : LinSetup M Q Z B 2 V₁ V₂) : Nonempty (TensorModel M Q Z B) := by
  obtain ⟨n, γ, M₀, hn, gm⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨F, hF, hFfin, hFcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow (hFcard.trans hn)
  obtain ⟨ρH, hρπ, -, hρQ⟩ := exists_actionHom_H0 hc.hyp gm
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  let ρ := ρH.comp (Subgroup.inclusion hSH)
  have hρπ' : ∀ (s : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = ρ s (M₀.π x) := fun s x hx => hρπ ⟨s, hSH s.2⟩ x hx
  obtain ⟨Φ₀, hΦ₀, -, -⟩ := exists_equivariant_coord M₀ ρ hρπ' hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup
    φ hact₁ hact₂
  have hKF : Nat.card (GaloisField 2 n) = Nat.card F := gm.card.trans hFcard.symm
  have h4 : 4 ≤ Nat.card F := hFcard ▸ hc.hyp.q4
  obtain ⟨ε, Φ, hsmul, hact, hqf⟩ := tensor_structure hKF h4 M₀.Qf M₀.B M₀.Qf_smul M₀.Qf_add
    M₀.alt M₀.nondeg ρ (fun s e => hρQ _ e) φ
    (fun A hA => by rw [← hrange] at hA; exact hA)
    (fun s => CFSG.Open.StatedAPI.det_of_mem_statedSL (by rw [← hrange]; exact ⟨s, rfl⟩))
    Φ₀ hΦ₀
  exact ⟨{
    K := GaloisField 2 n
    γ := γ
    M₀ := M₀
    gm := gm
    F := F
    card_F := hFcard
    ε := ε
    Φ := Φ
    φ := φ
    φ_range := hrange
    φ_ker := hker
    smul := hsmul
    qf := hqf
    act := fun s x hx => by rw [hρπ' s x hx]; exact hact s _ }⟩

private theorem Q_le_Lgen_LB : Q ≤ Lgen M (LB M Q B) :=
  (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)).trans (le_Lgen_self M (LB M Q B))

namespace TensorModel

variable (TM : TensorModel M Q Z B)

@[expose] def plane (u : Fin 2 → TM.F) : Subgroup G :=
  TM.M₀.lift ((planeAdd u).comap TM.Φ.toAddMonoidHom)

variable {TM}

theorem mem_plane {u : Fin 2 → TM.F} {x : G} :
    x ∈ TM.plane u ↔ x ∈ Q ∧ ∃ n : Fin 2 → TM.F,
      TM.Φ (TM.M₀.π x) = Matrix.vecMulVec n u := Iff.rfl

theorem mem_plane_iff {u : Fin 2 → TM.F} {x : G} :
    x ∈ TM.plane u ↔ x ∈ Q ∧ TM.Φ (TM.M₀.π x) ∈ planeAdd u := Iff.rfl

theorem img_plane {u : Fin 2 → TM.F} {e : TM.M₀.E} :
    e ∈ TM.M₀.img (TM.plane u) ↔ TM.Φ e ∈ planeAdd u :=
  Tim79.QuadModel.mem_img_lift

theorem Z_le_plane (u : Fin 2 → TM.F) : Z ≤ TM.plane u := by
  intro z hz
  have hzQ : z ∈ Q := TM.gm.reg.V_le hz
  refine mem_plane_iff.mpr ⟨hzQ, ?_⟩
  rw [(TM.M₀.π_ker z hzQ).mpr hz, map_zero]
  exact (planeAdd u).zero_mem

theorem plane_le_Q (u : Fin 2 → TM.F) : TM.plane u ≤ Q := fun _ hx => hx.1

theorem plane_smul {u : Fin 2 → TM.F} {c : TM.F} (hc : c ≠ 0) : TM.plane (c • u) = TM.plane u := by
  unfold plane
  rw [planeAdd_smul hc]

theorem card_plane {u : Fin 2 → TM.F} (hu : u ≠ 0) : Nat.card (TM.plane u) = Nat.card Z ^ 3 := by
  have h1 := TM.M₀.card_eq (plane_le_Q u) (Z_le_plane u)
  have h2 : Nat.card (TM.M₀.img (TM.plane u)) = Nat.card (planeAdd u) :=
    Nat.card_congr (TM.Φ.toEquiv.subtypeEquiv fun _ => img_plane)
  rw [h1, h2, card_planeAdd hu, TM.card_F]
  ring

theorem plane_inf_plane {u u' : Fin 2 → TM.F} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hne : ∀ c : TM.F, u' ≠ c • u) : TM.plane u ⊓ TM.plane u' = Z := by
  refine le_antisymm (fun x hx => ?_) (le_inf (Z_le_plane u) (Z_le_plane u'))
  obtain ⟨hxQ, hx1⟩ := mem_plane_iff.mp hx.1
  have hx2 := (mem_plane_iff.mp hx.2).2
  have h0 : TM.Φ (TM.M₀.π x) ∈ planeAdd u ⊓ planeAdd u' := ⟨hx1, hx2⟩
  rw [planeAdd_inf hu hu' hne, AddSubgroup.mem_bot] at h0
  exact (TM.M₀.π_ker x hxQ).mp (TM.Φ.map_eq_zero_iff.mp h0)

theorem plane_sup_plane {u u' : Fin 2 → TM.F} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hne : ∀ c : TM.F, u' ≠ c • u) : TM.plane u ⊔ TM.plane u' = Q := by
  refine le_antisymm (sup_le (plane_le_Q u) (plane_le_Q u')) (fun x hxQ => ?_)
  have h : TM.Φ (TM.M₀.π x) ∈ planeAdd u ⊔ planeAdd u' := by
    rw [planeAdd_sup hu hu' hne]
    exact AddSubgroup.mem_top _
  obtain ⟨X, hX, Y, hY, hXY⟩ := AddSubgroup.mem_sup.mp h
  obtain ⟨a, haQ, ha⟩ := TM.M₀.π_surj (TM.Φ.symm X)
  obtain ⟨b, hbQ, hb⟩ := TM.M₀.π_surj (TM.Φ.symm Y)
  have haP : a ∈ TM.plane u :=
    mem_plane_iff.mpr ⟨haQ, by rw [ha, AddEquiv.apply_symm_apply]; exact hX⟩
  have hbP : b ∈ TM.plane u' :=
    mem_plane_iff.mpr ⟨hbQ, by rw [hb, AddEquiv.apply_symm_apply]; exact hY⟩
  have hz : (a * b)⁻¹ * x ∈ Z := by
    rw [← TM.M₀.pi_eq_iff (Q.mul_mem haQ hbQ) hxQ, TM.M₀.π_mul a haQ b hbQ, ha, hb]
    apply TM.Φ.injective
    rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hXY]
  have hx : x = a * b * ((a * b)⁻¹ * x) := by group
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left haP)
    (Subgroup.mem_sup_right hbP)) (Subgroup.mem_sup_left (Z_le_plane u hz))

theorem plane_comm {u : Fin 2 → TM.F} {x y : G} (hx : x ∈ TM.plane u) (hy : y ∈ TM.plane u) :
    x * y = y * x := by
  obtain ⟨hxQ, hx'⟩ := mem_plane_iff.mp hx
  obtain ⟨hyQ, hy'⟩ := mem_plane_iff.mp hy
  rw [Tim79.QuadModel.comm_iff_B TM.M₀ TM.gm.reg hxQ hyQ]
  have h1 := congrArg TM.ε (TM.M₀.Qf_add (TM.M₀.π x) (TM.M₀.π y))
  rw [map_add, map_add, TM.qf, TM.qf, TM.qf, map_add, det_add_of_mem_planeAdd hx' hy'] at h1
  have h3 : TM.ε (TM.M₀.B (TM.M₀.π x) (TM.M₀.π y)) = 0 := by
    linear_combination -h1
  exact TM.ε.injective (h3.trans (map_zero TM.ε).symm)

theorem conj_mem_Q (TM : TensorModel M Q Z B) {s x : G} (hs : s ∈ Lgen M (LB M Q B))
    (hx : x ∈ Q) : s * x * s⁻¹ ∈ Q := by
  have hk : (⟨x, Q_le_Lgen_LB hx⟩ : ↥(Lgen M (LB M Q B))) ∈ TM.φ.ker := by
    rw [TM.φ_ker]
    exact hx
  have h := (inferInstance : TM.φ.ker.Normal).conj_mem _ hk ⟨s, hs⟩
  rw [TM.φ_ker] at h
  exact h

theorem act_of_mem {s : G} (hs : s ∈ Lgen M (LB M Q B)) {x : G} (hx : x ∈ Q) :
    TM.Φ (TM.M₀.π (s * x * s⁻¹)) =
      (TM.φ ⟨s, hs⟩ : Matrix (Fin 2) (Fin 2) TM.F) * TM.Φ (TM.M₀.π x) :=
  TM.act ⟨s, hs⟩ x hx

theorem normalizes_plane (u : Fin 2 → TM.F) {s : G} (hs : s ∈ Lgen M (LB M Q B)) :
    s ∈ Subgroup.normalizer (TM.plane u : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨hxQ, hx'⟩ := mem_plane_iff.mp hx
  refine mem_plane_iff.mpr ⟨TM.conj_mem_Q hs hxQ, ?_⟩
  rw [act_of_mem hs hxQ]
  exact mul_mem_planeAdd hx' _

theorem conj_plane (hc : Ctx M Q Z B) {u : Fin 2 → TM.F} (hu : u ≠ 0) {m : G} (hm : m ∈ M) :
    ∃ u' : Fin 2 → TM.F, u' ≠ 0 ∧ conjSubgroup m (TM.plane u) = TM.plane u' := by
  obtain ⟨-, -, T, -, hTπ, -, -⟩ := TM.gm.act m hm
  have hmN := hc.hyp.Q_normal.2 hm
  have hmQ : ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmN x).mp hx
  have hmQ' : ∀ y ∈ Q, m⁻¹ * y * m ∈ Q := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) y).mp hy
    rwa [inv_inv] at h
  have hTs : ∀ y ∈ Q, T.symm (TM.M₀.π y) = TM.M₀.π (m⁻¹ * y * m) := by
    intro y hy
    rw [AddEquiv.symm_apply_eq, ← hTπ _ (hmQ' y hy)]
    congr 1
    group
  let Ψ : Matrix (Fin 2) (Fin 2) TM.F ≃+ Matrix (Fin 2) (Fin 2) TM.F :=
    TM.Φ.symm.trans (T.symm.trans TM.Φ)
  have hΨ : ∀ X, Ψ X = TM.Φ (T.symm (TM.Φ.symm X)) := fun X => rfl
  let Y : AddSubgroup (Matrix (Fin 2) (Fin 2) TM.F) := (planeAdd u).comap Ψ.toAddMonoidHom
  have hYmem : ∀ X, X ∈ Y ↔ Ψ X ∈ planeAdd u := fun X => Iff.rfl
  have hY : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 → ∀ X ∈ Y, g * X ∈ Y := by
    intro g hg X hX
    rw [hYmem] at hX ⊢
    have hgSL : Matrix.GeneralLinearGroup.mkOfDetNeZero g (by rw [hg]; exact one_ne_zero) ∈
        StatedSL 2 TM.F := CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    rw [← TM.φ_range] at hgSL
    obtain ⟨s, hs⟩ := hgSL
    have hsg : (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) = g := by rw [hs]; rfl
    obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (T.symm (TM.Φ.symm X))
    have hy : TM.M₀.π (m * x * m⁻¹) = TM.Φ.symm X := by
      rw [hTπ x hxQ, hx, AddEquiv.apply_symm_apply]
    have hX' : X = TM.Φ (TM.M₀.π (m * x * m⁻¹)) := by rw [hy, AddEquiv.apply_symm_apply]
    have hs' : m⁻¹ * (s : G) * m ∈ Lgen M (LB M Q B) := by
      have h := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B)
        (M.inv_mem hm)) (s : G)).mp s.2
      rwa [inv_inv] at h
    have hx'Q := TM.conj_mem_Q hs' hxQ
    have hconj : (s : G) * (m * x * m⁻¹) * (s : G)⁻¹ =
        m * ((m⁻¹ * (s : G) * m) * x * (m⁻¹ * (s : G) * m)⁻¹) * m⁻¹ := by group
    have hgX : g * X = TM.Φ (TM.M₀.π (m * ((m⁻¹ * (s : G) * m) * x *
        (m⁻¹ * (s : G) * m)⁻¹) * m⁻¹)) := by
      rw [← hconj, ← hsg, hX']
      exact (TM.act s _ (hmQ x hxQ)).symm
    rw [hgX, hΨ, AddEquiv.symm_apply_apply, hTπ _ hx'Q, AddEquiv.symm_apply_apply,
      act_of_mem hs' hxQ, hx]
    exact mul_mem_planeAdd hX _
  have hcard : Nat.card Y = Nat.card TM.F ^ 2 := by
    rw [← card_planeAdd hu]
    exact Nat.card_congr (Ψ.toEquiv.subtypeEquiv fun X => hYmem X)
  obtain ⟨u', hu', hYu'⟩ := eq_planeAdd_of_card Y hY hcard
  refine ⟨u', hu', ?_⟩
  ext y
  rw [mem_conjSubgroup, mem_plane_iff, mem_plane_iff, ← hYu', hYmem, hΨ,
    AddEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hyQ, hy⟩
    have hyQ' : y ∈ Q := by
      have h := hmQ _ hyQ
      rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h
    exact ⟨hyQ', by rw [hTs y hyQ']; exact hy⟩
  · rintro ⟨hyQ, hy⟩
    exact ⟨hmQ' y hyQ, by rw [← hTs y hyQ]; exact hy⟩

theorem exists_plane_of_ctx {C : Subgroup G} (hC : Ctx M Q Z C) :
    ∃ u : Fin 2 → TM.F, u ≠ 0 ∧ C ≤ TM.plane u := by
  obtain ⟨b, hb0, hbQ, hbC, -, -⟩ := hC.dictB TM.gm
  have hΦb : TM.Φ b ≠ 0 := fun h => hb0 (TM.Φ.map_eq_zero_iff.mp h)
  have hdet : (TM.Φ b).det = 0 := by rw [← TM.qf, hbQ, map_zero]
  obtain ⟨n, u, -, hu, hnu⟩ := exists_vecMulVec_of_det_eq_zero hΦb hdet
  refine ⟨u, hu, fun c hc => ?_⟩
  have hcQ : c ∈ Q := hC.le hc
  obtain ⟨t, ht⟩ := (hbC _).mp (TM.M₀.pi_mem_img hc hcQ)
  refine mem_plane_iff.mpr ⟨hcQ, ⟨TM.ε t • n, ?_⟩⟩
  rw [ht, TM.smul, hnu, Matrix.smul_vecMulVec]

@[expose] def Gamma : Subgroup (GL (Fin 2) TM.F) where
  carrier := {H | ∃ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) ∧
    (∀ s ∈ Lgen M (LB M Q B), ⁅m, s⁆ ∈ Q) ∧
    ∀ x ∈ Q, TM.Φ (TM.M₀.π (m * x * m⁻¹)) =
      TM.Φ (TM.M₀.π x) * (H : Matrix (Fin 2) (Fin 2) TM.F)}
  mul_mem' := by
    rintro H₁ H₂ ⟨m₁, hm₁, hN₁, hS₁, hH₁⟩ ⟨m₂, hm₂, hN₂, hS₂, hH₂⟩
    refine ⟨m₂ * m₁, M.mul_mem hm₂ hm₁, Subgroup.mul_mem _ hN₂ hN₁, fun s hs => ?_,
      fun x hx => ?_⟩
    · have h : ⁅m₂ * m₁, s⁆ = m₂ * ⁅m₁, s⁆ * m₂⁻¹ * ⁅m₂, s⁆ := by
        simp only [commutatorElement_def]
        group
      rw [h]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hN₂ _).mp (hS₁ s hs)) (hS₂ s hs)
    · have hx₁ : m₁ * x * m₁⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hN₁ x).mp hx
      have e : m₂ * m₁ * x * (m₂ * m₁)⁻¹ = m₂ * (m₁ * x * m₁⁻¹) * m₂⁻¹ := by group
      rw [e, hH₂ _ hx₁, hH₁ x hx, Units.val_mul, mul_assoc]
  one_mem' := by
    refine ⟨1, M.one_mem, Subgroup.one_mem _, fun s _ => ?_, fun x _ => ?_⟩
    · rw [commutatorElement_def]
      simpa using Q.one_mem
    · simp
  inv_mem' := by
    rintro H ⟨m, hm, hN, hS, hH⟩
    refine ⟨m⁻¹, M.inv_mem hm, Subgroup.inv_mem _ hN, fun s hs => ?_, fun x hx => ?_⟩
    · have h : ⁅m⁻¹, s⁆ = m⁻¹ * ⁅m, s⁆⁻¹ * m⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) _).mp
        (Q.inv_mem (hS s hs))
    · have hx' : m⁻¹ * x * m⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) x).mp hx
      have h := hH _ hx'
      rw [show m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x by group] at h
      rw [h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_centralizer_of_right_mul (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M)
    {H : Matrix (Fin 2) (Fin 2) TM.F} (hdet : H.det = 1)
    (hmH : ∀ x ∈ Q, TM.Φ (TM.M₀.π (m * x * m⁻¹)) = TM.Φ (TM.M₀.π x) * H) :
    m ∈ Subgroup.centralizer (Z : Set G) := by
  obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := TM.gm.act m hm
  have hTe : ∀ e, TM.Φ (T e) = TM.Φ e * H := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := TM.M₀.π_surj e
    rw [← hTπ x hxQ, hmH x hxQ]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : TM.M₀.E, TM.Φ e₁ = 1 := ⟨TM.Φ.symm 1, AddEquiv.apply_symm_apply _ _⟩
  have hQe₁ : TM.M₀.Qf e₁ = 1 := by
    apply TM.ε.injective
    rw [TM.qf, he₁, Matrix.det_one, map_one]
  have hQTe₁ : TM.M₀.Qf (T e₁) = 1 := by
    apply TM.ε.injective
    rw [TM.qf, hTe, he₁, Matrix.one_mul, hdet, map_one]
  have ha : (a : TM.K) = 1 := by
    have h := hTQ e₁
    rw [hQTe₁, hQe₁, map_one, mul_one] at h
    exact h.symm
  have hTe₁ : T e₁ ≠ 0 := by
    intro h0
    have h := hTe e₁
    rw [h0, map_zero, he₁, Matrix.one_mul] at h
    have h2 : H.det = 0 := by rw [← h, Matrix.det_zero]
    rw [hdet] at h2
    exact one_ne_zero h2
  have hσ : ∀ c, σ c = c := by
    intro c
    have h1 : T (c • e₁) = c • T e₁ := by
      apply TM.Φ.injective
      rw [hTe, TM.smul, TM.smul, hTe, Matrix.smul_mul]
    rw [hT1] at h1
    exact smul_left_injective TM.K hTe₁ h1
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzm : m * z * m⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hγ : TM.γ (m * z * m⁻¹) = TM.γ z := by rw [hTγ z hz, ha, hσ, one_mul]
  have heq : m * z * m⁻¹ = z := TM.gm.reg.eq_of_γ_eq hzm hz hγ
  calc z * m = m * z * m⁻¹ * m := by rw [heq]
    _ = m * z := by group

private theorem exists_right_mul_of_mem (hc : Ctx M Q Z B) {C₀ : Subgroup G}
    (hCH : C₀ ≤ H0 M Z)
    (hC : ∀ h, h ∈ C₀ ↔ h ∈ H0 M Z ∧ ∀ x ∈ Lgen M (LB M Q B), ⁅h, x⁆ ∈ Q)
    {ρH : ↥(H0 M Z) →* (TM.M₀.E ≃ₗ[TM.K] TM.M₀.E)}
    (hρ1 : ∀ m : ↥(H0 M Z), ρH m = 1 ↔ (m : G) ∈ Q)
    (hSact : ∀ (s : ↥(Lgen M (LB M Q B))) (e : TM.M₀.E),
      TM.Φ (ρH ⟨s, Lgen_le_H0 hc s.2⟩ e) =
        (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) * TM.Φ e)
    {ρ : ↥C₀ →* (TM.M₀.E ≃ₗ[TM.K] TM.M₀.E)}
    (hρdef : ∀ h : ↥C₀, ρ h = ρH (Subgroup.inclusion hCH h)) :
    ∀ h : ↥C₀, ∃ H : Matrix (Fin 2) (Fin 2) TM.F,
      ∀ e, TM.Φ (ρ h e) = TM.Φ e * H := by
  intro h
  have hcomm : ∀ (s : ↥(Lgen M (LB M Q B))) (e : TM.M₀.E),
      ρ h (ρH ⟨s, Lgen_le_H0 hc s.2⟩ e) = ρH ⟨s, Lgen_le_H0 hc s.2⟩ (ρ h e) := by
    intro s e
    obtain ⟨h', hh'⟩ : ∃ h' : ↥(H0 M Z), h' = Subgroup.inclusion hCH h := ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ : ∃ s' : ↥(H0 M Z), s' = ⟨s, Lgen_le_H0 hc s.2⟩ := ⟨_, rfl⟩
    have hk : ρH (h' * s' * h'⁻¹ * s'⁻¹) = 1 := by
      refine (hρ1 _).mpr ?_
      rw [hh', hs']
      exact ((hC h).mp h.2).2 s s.2
    have hρc : ρH (h' * s') = ρH (s' * h') := by
      rw [show h' * s' = (h' * s' * h'⁻¹ * s'⁻¹) * (s' * h') by group, map_mul, hk, one_mul]
    rw [hρdef, ← hh', ← hs', ← LinearEquiv.mul_apply, ← map_mul, hρc, map_mul,
      LinearEquiv.mul_apply]
  let T' : Matrix (Fin 2) (Fin 2) TM.F →+ Matrix (Fin 2) (Fin 2) TM.F :=
    AddMonoidHom.mk' (fun X => TM.Φ (ρ h (TM.Φ.symm X))) (fun X Y => by simp only [map_add])
  have hT' : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 → ∀ X, T' (g * X) = g * T' X := by
    intro g hg X
    have hgSL : Matrix.GeneralLinearGroup.mkOfDetNeZero g (by rw [hg]; exact one_ne_zero) ∈
        StatedSL 2 TM.F := CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    rw [← TM.φ_range] at hgSL
    obtain ⟨s, hs⟩ := hgSL
    have hsg : (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) = g := by rw [hs]; rfl
    have e1 : TM.Φ.symm (g * X) = ρH ⟨s, Lgen_le_H0 hc s.2⟩ (TM.Φ.symm X) := by
      rw [AddEquiv.symm_apply_eq, hSact s, AddEquiv.apply_symm_apply, hsg]
    show TM.Φ (ρ h (TM.Φ.symm (g * X))) = g * TM.Φ (ρ h (TM.Φ.symm X))
    rw [e1, hcomm s, hSact s, hsg]
  obtain ⟨H, hH⟩ := schur_right T' hT'
  refine ⟨H, fun e => ?_⟩
  have h1 := hH (TM.Φ e)
  simp only [T', AddMonoidHom.mk'_apply, AddEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_hom_Gamma_inf_SL (hc : Ctx M Q Z B) {C₀ : Subgroup G} (hCH : C₀ ≤ H0 M Z)
    (hC : ∀ h, h ∈ C₀ ↔ h ∈ H0 M Z ∧ ∀ x ∈ Lgen M (LB M Q B), ⁅h, x⁆ ∈ Q) :
    ∃ ψ : ↥C₀ →* GL (Fin 2) TM.F, ψ.ker = Q.subgroupOf C₀ ∧
      ψ.range = TM.Gamma ⊓ StatedSL 2 TM.F := by
  obtain ⟨ρH, hρπ, hρ1, hρQ⟩ := exists_actionHom_H0 hc.hyp TM.gm
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ↥C₀ →* (TM.M₀.E ≃ₗ[TM.K] TM.M₀.E),
      ∀ h, ρ h = ρH (Subgroup.inclusion hCH h) := ⟨ρH.comp (Subgroup.inclusion hCH), fun _ => rfl⟩
  have hρπC : ∀ (h : ↥C₀) (x : G), x ∈ Q →
      TM.M₀.π ((h : G) * x * (h : G)⁻¹) = ρ h (TM.M₀.π x) := fun h x hx => by
    rw [hρdef]
    exact hρπ (Subgroup.inclusion hCH h) x hx
  have hρ1C : ∀ h : ↥C₀, ρ h = 1 ↔ (h : G) ∈ Q := fun h => by
    rw [hρdef]
    exact hρ1 _
  have hρQC : ∀ (h : ↥C₀) e, TM.M₀.Qf (ρ h e) = TM.M₀.Qf e := fun h e => by
    rw [hρdef]
    exact hρQ _ e
  have hSact : ∀ (s : ↥(Lgen M (LB M Q B))) (e : TM.M₀.E),
      TM.Φ (ρH ⟨s, Lgen_le_H0 hc s.2⟩ e) = (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) * TM.Φ e := by
    intro s e
    obtain ⟨x, hxQ, rfl⟩ := TM.M₀.π_surj e
    rw [← hρπ ⟨s, Lgen_le_H0 hc s.2⟩ x hxQ]
    exact TM.act s x hxQ
  have hschur := exists_right_mul_of_mem (TM := TM) hc hCH hC hρ1 hSact hρdef
  obtain ⟨Hm, hHm⟩ : ∃ Hm : ↥C₀ → Matrix (Fin 2) (Fin 2) TM.F,
      ∀ h, Hm h = TM.Φ (ρ h (TM.Φ.symm 1)) := ⟨_, fun _ => rfl⟩
  have hKP : ∀ (h : ↥C₀) (e : TM.M₀.E), TM.Φ (ρ h e) = TM.Φ e * Hm h := by
    intro h e
    obtain ⟨H, hH⟩ := hschur h
    have h1 : Hm h = H := by rw [hHm, hH, AddEquiv.apply_symm_apply, Matrix.one_mul]
    rw [h1]
    exact hH e
  have hHm_mul : ∀ a b : ↥C₀, Hm (a * b) = Hm b * Hm a := by
    intro a b
    rw [hHm, map_mul, LinearEquiv.mul_apply, hKP a, ← hHm]
  have hHm_one : Hm 1 = 1 := by
    rw [hHm, map_one, LinearEquiv.coe_one, id, AddEquiv.apply_symm_apply]
  have hHm_det : ∀ h, (Hm h).det = 1 := by
    intro h
    rw [hHm, ← TM.qf, hρQC, TM.qf, AddEquiv.apply_symm_apply, Matrix.det_one]
  let ψ : ↥C₀ →* GL (Fin 2) TM.F :=
    { toFun := fun h => ⟨Hm h⁻¹, Hm h, by rw [← hHm_mul, mul_inv_cancel, hHm_one],
        by rw [← hHm_mul, inv_mul_cancel, hHm_one]⟩
      map_one' := Units.ext (show Hm 1⁻¹ = 1 by rw [inv_one, hHm_one])
      map_mul' := fun a b => Units.ext (show Hm (a * b)⁻¹ = Hm a⁻¹ * Hm b⁻¹ by
        rw [mul_inv_rev, hHm_mul]) }
  have hψ : ∀ h, (ψ h : Matrix (Fin 2) (Fin 2) TM.F) = Hm h⁻¹ := fun h => rfl
  have hker : ψ.ker = Q.subgroupOf C₀ := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff, hψ, Units.val_one]
    constructor
    · intro h1
      have hρ : ρ h⁻¹ = 1 := by
        refine LinearEquiv.ext fun e => TM.Φ.injective ?_
        rw [hKP, h1, Matrix.mul_one, LinearEquiv.coe_one, id]
      have h2 := Q.inv_mem ((hρ1C h⁻¹).mp hρ)
      rwa [Subgroup.coe_inv, inv_inv] at h2
    · intro hQ
      have hρ : ρ h⁻¹ = 1 := (hρ1C h⁻¹).mpr (by rw [Subgroup.coe_inv]; exact Q.inv_mem hQ)
      rw [hHm, hρ, LinearEquiv.coe_one, id, AddEquiv.apply_symm_apply]
  have hrange : ψ.range = TM.Gamma ⊓ StatedSL 2 TM.F := by
    ext H
    constructor
    · rintro ⟨h, rfl⟩
      have hm := hCH (h⁻¹).2
      refine ⟨⟨((h⁻¹ : ↥C₀) : G), hm.1, hc.hyp.Q_normal.2 hm.1, ((hC _).mp (h⁻¹).2).2,
        fun x hx => ?_⟩, ?_⟩
      · rw [hψ, hρπC h⁻¹ x hx, hKP]
      · exact CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [hψ]; exact hHm_det h⁻¹)
    · rintro ⟨⟨m, hmM, -, hmS, hmH⟩, hHSL⟩
      have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hHSL
      have hmZ := TM.mem_centralizer_of_right_mul hc hmM hdet hmH
      have hmC : m ∈ C₀ := (hC m).mpr ⟨⟨hmM, hmZ⟩, hmS⟩
      refine ⟨(⟨m, hmC⟩ : ↥C₀)⁻¹, Units.ext ?_⟩
      rw [hψ, inv_inv]
      obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (TM.Φ.symm 1)
      have h1 := hmH x hxQ
      rw [show m * x * m⁻¹ = ((⟨m, hmC⟩ : ↥C₀) : G) * x * ((⟨m, hmC⟩ : ↥C₀) : G)⁻¹ from rfl,
        hρπC _ x hxQ, hKP, hx, AddEquiv.apply_symm_apply, Matrix.one_mul,
        Matrix.one_mul] at h1
      exact h1
  exact ⟨ψ, hker, hrange⟩

theorem card_eq_mul_card_Gamma_inf_SL (hc : Ctx M Q Z B) {C₀ : Subgroup G} (hQC : Q ≤ C₀)
    (hCH : C₀ ≤ H0 M Z) (hC : ∀ h, h ∈ C₀ ↔ h ∈ H0 M Z ∧ ∀ x ∈ Lgen M (LB M Q B), ⁅h, x⁆ ∈ Q) :
    Nat.card ↥C₀ = Nat.card ↥Q * Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) := by
  obtain ⟨ψ, hker, hrange⟩ := exists_hom_Gamma_inf_SL (TM := TM) hc hCH hC
  rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.card_mul_index (Q.subgroupOf C₀)]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv

theorem card_Gamma_inf_SL (hc : Ctx M Q Z B)
    (hCD : CentDvdN 2 M Q Z (Lgen M (LB M Q B))) :
    Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) ∣ 2 * (Nat.card TM.F - 1) := by
  obtain ⟨C₀, hQC, hCH, hC, hdvd⟩ := hCD
  have hcardC := card_eq_mul_card_Gamma_inf_SL (TM := TM) hc hQC hCH hC
  haveI : Nonempty ↥Q := ⟨1⟩
  rw [hcardC, ← TM.card_F] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd

end TensorModel

end Model

end CFSG.RankThree.GF2n.Smith81
