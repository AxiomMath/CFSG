module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.SignalizerFunctorTheorem.NearModels.Main
public import CFSG.Walter.PSL2Facts.Even

namespace CFSG.RankThree.GF2n.Tim77

public section
theorem sec47_conj_of_odd {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hr : Odd (orderOf (a * b))) :
    ∃ g ∈ Subgroup.closure ({a, b} : Set G), g * a * g⁻¹ = b := by
  obtain ⟨k, hk⟩ := hr
  set ρ : G := a * b with hρdef
  have hρr : ρ ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one ρ
  have hρa : a * ρ * a = ρ⁻¹ := by
    rw [hρdef, mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha]
    calc a * (a * b) * a = (a * a) * b * a := by simp only [mul_assoc]
      _ = b * a := by rw [ha, one_mul]
  have hconj : ∀ n : ℕ, a * ρ ^ n * a = (ρ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp [ha]
    | succ n ih =>
      have e : a * ρ ^ (n + 1) * a = (a * ρ ^ n * a) * (a * ρ * a) := by
        calc a * ρ ^ (n + 1) * a = a * (ρ ^ n * ρ) * a := by rw [pow_succ]
          _ = a * ρ ^ n * ρ * a := by simp only [mul_assoc]
          _ = a * ρ ^ n * (a * a) * ρ * a := by rw [ha, mul_one]
          _ = (a * ρ ^ n * a) * (a * ρ * a) := by simp only [mul_assoc]
      rw [e, ih, hρa, ← mul_inv_rev, ← pow_succ']
  set s : G := ρ ^ k with hsdef
  have hss : s * s * ρ = 1 := by
    rw [hsdef, ← pow_add, ← pow_succ]
    convert hρr using 2
    ring
  have hss' : s * s = ρ⁻¹ := eq_inv_of_mul_eq_one_left hss
  have hinv2 : s⁻¹ * s⁻¹ = ρ := by
    rw [← mul_inv_rev, hss', inv_inv]
  refine ⟨s, Subgroup.pow_mem _ (Subgroup.mul_mem _
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) k, ?_⟩
  have h1 : a * s * a = s⁻¹ := hconj k
  have hsa : s * a = a * s⁻¹ := by
    calc s * a = (a * a) * s * a := by rw [ha, one_mul]
      _ = a * (a * s * a) := by simp only [mul_assoc]
      _ = a * s⁻¹ := by rw [h1]
  calc s * a * s⁻¹ = (a * s⁻¹) * s⁻¹ := by rw [hsa]
    _ = a * (s⁻¹ * s⁻¹) := by simp only [mul_assoc]
    _ = a * ρ := by rw [hinv2]
    _ = b := by
      rw [hρdef]
      calc a * (a * b) = (a * a) * b := by simp only [mul_assoc]
        _ = b := by rw [ha, one_mul]
end

public section
open scoped commutatorElement

theorem sec47_twist {G : Type} [Group G] {Z Q C : Subgroup G}
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hQle : Q ≤ Z)
    (hCQ : C ≤ Q) (hCZ : ∀ c ∈ C, ∀ z ∈ Z, c * z = z * c)
    (hZ' : ∀ u ∈ ⁅Z, Z⁆, ∀ q ∈ Q, ⁅q, u⁆ ∈ C)
    (hperf : ⁅(⁅Z, Z⁆ ⊔ Q), (⁅Z, Z⁆ ⊔ Q)⁆ ⊔ Q = ⁅Z, Z⁆ ⊔ Q) :
    ∀ m ∈ ⁅Z, Z⁆ ⊔ Q, ∀ q ∈ Q, m * q = q * m := by
  have hZZ : ⁅Z, Z⁆ ≤ Z := Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    Z.mul_mem (Z.mul_mem (Z.mul_mem hg₁ hg₂) (Z.inv_mem hg₁)) (Z.inv_mem hg₂)
  have hMZ : ⁅Z, Z⁆ ⊔ Q ≤ Z := sup_le hZZ hQle
  let T : Subgroup G :=
    { carrier := {m | m ∈ Z ∧ ∀ q ∈ Q, ⁅q, m⁆ ∈ C}
      mul_mem' := by
        rintro m n ⟨hm, hmC⟩ ⟨hn, hnC⟩
        refine ⟨Z.mul_mem hm hn, fun q hq => ?_⟩
        have e : ⁅q, m * n⁆ = ⁅q, m⁆ * (m * ⁅q, n⁆ * m⁻¹) := by
          simp only [commutatorElement_def]; group
        have hc : m * ⁅q, n⁆ * m⁻¹ = ⁅q, n⁆ := by
          have := hCZ _ (hnC q hq) m hm
          rw [← this]; group
        rw [e, hc]
        exact C.mul_mem (hmC q hq) (hnC q hq)
      one_mem' := by
        refine ⟨Z.one_mem, fun q _ => ?_⟩
        simp [commutatorElement_def]
      inv_mem' := by
        rintro m ⟨hm, hmC⟩
        refine ⟨Z.inv_mem hm, fun q hq => ?_⟩
        have hc := hmC q hq
        have hcm : ⁅q, m⁆ * m = m * ⁅q, m⁆ := hCZ _ hc m hm
        have hqm : q * m * q⁻¹ = ⁅q, m⁆ * m := by
          simp only [commutatorElement_def]; group
        have e : ⁅q, m⁻¹⁆ = (⁅q, m⁆)⁻¹ := by
          have e1 : ⁅q, m⁻¹⁆ = (q * m * q⁻¹)⁻¹ * m := by
            simp only [commutatorElement_def]; group
          have e2 : (⁅q, m⁆)⁻¹ * m = m * (⁅q, m⁆)⁻¹ := by
            calc (⁅q, m⁆)⁻¹ * m = (⁅q, m⁆)⁻¹ * (m * ⁅q, m⁆) * (⁅q, m⁆)⁻¹ := by group
              _ = (⁅q, m⁆)⁻¹ * (⁅q, m⁆ * m) * (⁅q, m⁆)⁻¹ := by rw [← hcm]
              _ = m * (⁅q, m⁆)⁻¹ := by group
          rw [e1, hqm, mul_inv_rev]
          calc (m⁻¹ * (⁅q, m⁆)⁻¹) * m = m⁻¹ * ((⁅q, m⁆)⁻¹ * m) := by group
            _ = m⁻¹ * (m * (⁅q, m⁆)⁻¹) := by rw [e2]
            _ = (⁅q, m⁆)⁻¹ := by group
        rw [e]
        exact C.inv_mem hc }
  have hT : ∀ m, m ∈ T ↔ m ∈ Z ∧ ∀ q ∈ Q, ⁅q, m⁆ ∈ C := fun m => Iff.rfl
  have hMT : ⁅Z, Z⁆ ⊔ Q ≤ T := by
    refine sup_le ?_ ?_
    · intro u hu
      exact (hT u).mpr ⟨hZZ hu, fun q hq => hZ' u hu q hq⟩
    · intro q hq
      refine (hT q).mpr ⟨hQle hq, fun q' hq' => ?_⟩
      have := hQab q' hq' q hq
      rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
      exact C.one_mem
  set M : Subgroup G := ⁅Z, Z⁆ ⊔ Q with hMdef
  have hQM : ⁅Q, M⁆ ≤ C := Subgroup.commutator_le.mpr fun q hq m hm => ((hT m).mp (hMT hm)).2 q hq
  have hCM : ⁅C, M⁆ ≤ ⊥ := by
    refine Subgroup.commutator_le.mpr fun c hc m hm => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hCZ c hc m (hMZ hm)
  have h1 : ⁅⁅M, Q⁆, M⁆ = ⊥ := by
    refine eq_bot_iff.mpr (le_trans (Subgroup.commutator_mono ?_ le_rfl) hCM)
    rw [Subgroup.commutator_comm]
    exact hQM
  have h2 : ⁅⁅Q, M⁆, M⁆ = ⊥ := by
    refine eq_bot_iff.mpr (le_trans (Subgroup.commutator_mono hQM le_rfl) hCM)
  have h3 : ⁅⁅M, M⁆, Q⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hCq : ⁅M, M⁆ ⊔ Q ≤ Subgroup.centralizer (Q : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hxq : ⁅x, q⁆ ∈ ⁅⁅M, M⁆, Q⁆ := Subgroup.commutator_mem_commutator hx hq
      rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxq
      exact hxq.symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      exact hQab q' hq' q hq
  intro m hm q hq
  have hmM : m ∈ ⁅M, M⁆ ⊔ Q := by
    rw [hperf]
    exact hm
  have := (Subgroup.mem_centralizer_iff.mp (hCq hmM)) q hq
  exact this.symm
end

public section
open scoped MatrixGroups

theorem sec47_psl2_facts {L : Type} [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    IsSimpleGroup L ∧ Group.IsPerfect L ∧ Nontrivial L := by
  have hf0 : f ≠ 0 := by omega
  have hq4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f hf0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by omega)
  haveI hs : IsSimpleGroup L := e.isSimpleGroup
  haveI hp : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact ⟨hs, hp, inferInstance⟩


theorem sec47_exists_noncomm_invol {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (hp : Group.IsPerfect L) {a : L} (ha : orderOf a = 2) :
    ∃ t : L, orderOf t = 2 ∧ ¬ Commute a t := by
  by_contra hcon
  push_neg at hcon
  set S : Set L := {t | orderOf t = 2} with hS
  set N : Subgroup L := Subgroup.closure S with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
      apply Subgroup.subset_closure
      show orderOf (g * t * g⁻¹) = 2
      have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
      exact h1.trans ht
    | one => simpa using N.one_mem
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact N.mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact N.inv_mem hx
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have haN : a ∈ N := Subgroup.subset_closure (show orderOf a = 2 from ha)
  have hNtop : N = ⊤ := by
    haveI := hNn
    refine (hs.eq_bot_or_eq_top_of_normal N).resolve_left fun h0 => ?_
    rw [h0] at haN
    exact ha1 (Subgroup.mem_bot.mp haN)
  have hcent : N ≤ Subgroup.centralizer ({a} : Set L) := by
    rw [hN]
    refine Subgroup.closure_le _ |>.mpr fun t ht => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact hcon t ht
  have hac : a ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_iff.mp (hcent (show g ∈ N from hNtop ▸ Subgroup.mem_top g))
      a (Set.mem_singleton a)
    exact this.symm
  have hZtop : Subgroup.center L = ⊤ := by
    refine (hs.eq_bot_or_eq_top_of_normal (Subgroup.center L)).resolve_left fun h0 => ?_
    rw [h0] at hac
    exact ha1 (Subgroup.mem_bot.mp hac)
  have hcomm : ∀ x y : L, x * y = y * x := fun x y => by
    have hx : x ∈ Subgroup.center L := hZtop ▸ Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcomm_bot : commutator L = ⊥ := by
    refine eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun x _ y _ => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x y
  have htop := hp.commutator_eq_top
  rw [hcomm_bot] at htop
  have hsub : Subsingleton L := by
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ (⊤ : Subgroup L) := Subgroup.mem_top x
    have hy : y ∈ (⊤ : Subgroup L) := Subgroup.mem_top y
    rw [← htop, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  exact not_subsingleton L hsub


open scoped commutatorElement

theorem sec47_commutatorElement_mul_central_left {K : Type} [Group K] {a b z : K}
    (hz : z ∈ Subgroup.center K) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hzb : z * b * z⁻¹ = b := by rw [← hc b, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹
      = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzb]

theorem sec47_commutatorElement_mul_central_right {K : Type} [Group K] {a b z : K}
    (hz : z ∈ Subgroup.center K) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hza : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← hc a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹
      = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hza]

theorem sec47_commutatorElement_mul_mul_central {K : Type} [Group K] {a b z₁ z₂ : K}
    (hz₁ : z₁ ∈ Subgroup.center K) (hz₂ : z₂ ∈ Subgroup.center K) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [sec47_commutatorElement_mul_central_left hz₁, sec47_commutatorElement_mul_central_right hz₂]

theorem sec47_comm_le_of_sup_center {K : Type} [Group K] (W : Subgroup K)
    (h : ∀ k : K, ∃ w ∈ W, w⁻¹ * k ∈ Subgroup.center K) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro k₁ _ k₂ _
  obtain ⟨w₁, hw₁, hz₁⟩ := h k₁
  obtain ⟨w₂, hw₂, hz₂⟩ := h k₂
  obtain ⟨z₁, hz₁', rfl⟩ : ∃ z ∈ Subgroup.center K, k₁ = w₁ * z :=
    ⟨w₁⁻¹ * k₁, hz₁, (mul_inv_cancel_left w₁ k₁).symm⟩
  obtain ⟨z₂, hz₂', rfl⟩ : ∃ z ∈ Subgroup.center K, k₂ = w₂ * z :=
    ⟨w₂⁻¹ * k₂, hz₂, (mul_inv_cancel_left w₂ k₂).symm⟩
  rw [sec47_commutatorElement_mul_mul_central hz₁' hz₂', commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)

theorem sec47_eq_top_of_gen {K : Type} [Group K] (W : Subgroup K) (E : Set K) (a : K)
    (hgen : Subgroup.closure E = ⊤) (haW : a ∈ W)
    (hEa : ∀ e ∈ E, ∃ c ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆, e = a * c)
    (hcomm : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ W) : W = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro e he
  obtain ⟨c, hc, rfl⟩ := hEa e he
  exact W.mul_mem haW (hcomm hc)

theorem sec47_index_le_card {Γ : Type} [Group Γ] [Finite Γ] (U T : Subgroup Γ)
    (hΓ : ∀ x y : Γ, x * y = y * x) (hUT : U ⊔ T = ⊤) :
    U.index ≤ Nat.card T := by
  haveI : T.Normal := ⟨fun n hn g => by
    rw [hΓ g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hsurj : Function.Surjective (fun t : T => (QuotientGroup.mk (s := U) (t : Γ))) := by
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    have hγ : γ ∈ U ⊔ T := by
      rw [hUT]
      exact Subgroup.mem_top γ
    obtain ⟨u, hu, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hγ
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk t : Γ ⧸ U) = QuotientGroup.mk (u * t)
    rw [QuotientGroup.eq]
    show t⁻¹ * (u * t) ∈ U
    rw [hΓ u t, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hu
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective _ hsurj
end

public section
@[expose] def sec47_conjN {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h : H) : N →* N where
  toFun n := ⟨h * n * h⁻¹, Subgroup.Normal.conj_mem inferInstance (n : H) n.2 h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem sec47_conjN_val {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h : H) (n : N) :
    ((sec47_conjN N h n : N) : H) = h * n * h⁻¹ :=
  rfl

theorem sec47_conjN_one {H : Type} [Group H] (N : Subgroup H) [N.Normal] (n : N) :
    sec47_conjN N 1 n = n :=
  Subtype.ext (by rw [sec47_conjN_val, one_mul, inv_one, mul_one])

theorem sec47_conjN_mul {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h k : H) (n : N) :
    sec47_conjN N (h * k) n = sec47_conjN N h (sec47_conjN N k n) :=
  Subtype.ext (by simp only [sec47_conjN_val]; group)

theorem sec47_conjN_inv_mul {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h : H) (n : N) :
    sec47_conjN N h⁻¹ (sec47_conjN N h n) = n := by
  rw [← sec47_conjN_mul, inv_mul_cancel, sec47_conjN_one]

theorem sec47_conjN_mul_inv {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h : H) (n : N) :
    sec47_conjN N h (sec47_conjN N h⁻¹ n) = n := by
  rw [← sec47_conjN_mul, mul_inv_cancel, sec47_conjN_one]

theorem sec47_conj_central {H : Type} [Group H] {C : Subgroup H}
    (hC : C ≤ Subgroup.center H) {c : H} (hc : c ∈ C) (h : H) : h * c * h⁻¹ = c := by
  have hcomm : h * c = c * h := Subgroup.mem_center_iff.mp (hC hc) h
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem sec47_conjN_mem {H : Type} [Group H] (N C : Subgroup H) [N.Normal]
    (hC : C ≤ Subgroup.center H) (h : H) :
    C.subgroupOf N ≤ (C.subgroupOf N).comap (sec47_conjN N h) := by
  intro x hx
  have hxC : (x : H) ∈ C := Subgroup.mem_subgroupOf.mp hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  show h * (x : H) * h⁻¹ ∈ C
  rw [sec47_conj_central hC hxC h]
  exact hxC

@[expose] def sec47_act {H : Type} [Group H] (N C : Subgroup H) [N.Normal] [C.Normal]
    (hC : C ≤ Subgroup.center H) (h : H) : (N ⧸ C.subgroupOf N) →* (N ⧸ C.subgroupOf N) :=
  QuotientGroup.map (C.subgroupOf N) (C.subgroupOf N) (sec47_conjN N h)
    (sec47_conjN_mem N C hC h)

theorem sec47_act_mk {H : Type} [Group H] (N C : Subgroup H) [N.Normal] [C.Normal]
    (hC : C ≤ Subgroup.center H) (h : H) (n : N) :
    sec47_act N C hC h (QuotientGroup.mk n) = QuotientGroup.mk (sec47_conjN N h n) :=
  rfl

@[expose] def sec47_aut {H : Type} [Group H] (N C : Subgroup H) [N.Normal] [C.Normal]
    (hC : C ≤ Subgroup.center H) (h : H) : MulAut (N ⧸ C.subgroupOf N) where
  toFun := sec47_act N C hC h
  invFun := sec47_act N C hC h⁻¹
  left_inv x := by
    show sec47_act N C hC h⁻¹ (sec47_act N C hC h x) = x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [sec47_act_mk, sec47_conjN_inv_mul]
  right_inv x := by
    show sec47_act N C hC h (sec47_act N C hC h⁻¹ x) = x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [sec47_act_mk, sec47_conjN_mul_inv]
  map_mul' := (sec47_act N C hC h).map_mul

@[expose] def sec47_hom {H : Type} [Group H] (N C : Subgroup H) [N.Normal] [C.Normal]
    (hC : C ≤ Subgroup.center H) : H →* MulAut (N ⧸ C.subgroupOf N) where
  toFun := sec47_aut N C hC
  map_one' := by
    ext x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    show sec47_act N C hC 1 (QuotientGroup.mk n) = QuotientGroup.mk n
    rw [sec47_act_mk, sec47_conjN_one]
  map_mul' h k := by
    ext x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    show sec47_act N C hC (h * k) (QuotientGroup.mk n) =
      sec47_act N C hC h (sec47_act N C hC k (QuotientGroup.mk n))
    simp only [sec47_act_mk, sec47_conjN_mul]

theorem sec47_quot_action {H : Type} [Group H] (N C : Subgroup H) [N.Normal] [C.Normal]
    (hN : CFSG.Open.IsElemAbelian 2 N) (hCN : C ≤ N) (hC : C ≤ Subgroup.center H) :
    ∃ ρ : (H ⧸ N) →* MulAut (N ⧸ C.subgroupOf N),
      (∀ (h : H) (n : N), ρ (QuotientGroup.mk h) (QuotientGroup.mk n) =
        QuotientGroup.mk ⟨h * n * h⁻¹, Subgroup.Normal.conj_mem inferInstance (n : H) n.2 h⟩) ∧
      CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (N ⧸ C.subgroupOf N)) := by
  obtain ⟨hcomm, hexp⟩ := hN
  have hcommN : ∀ a b : N, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  have key : ∀ (n : H) (hn : n ∈ N) (m : N), sec47_conjN N n m = m := by
    intro n hn m
    apply Subtype.ext
    rw [sec47_conjN_val]
    have hnm : n * (m : H) = (m : H) * n := congrArg Subtype.val (hcommN ⟨n, hn⟩ m)
    rw [hnm, mul_assoc, mul_inv_cancel, mul_one]
  have hker : N ≤ (sec47_hom N C hC).ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    show sec47_act N C hC n (QuotientGroup.mk m) = QuotientGroup.mk m
    rw [sec47_act_mk, key n hn m]
  have hquot_comm : ∀ x y : N ⧸ C.subgroupOf N, x * y = y * x := by
    intro x y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommN m n]
  refine ⟨QuotientGroup.lift N (sec47_hom N C hC) hker, fun h n => rfl, ?_⟩
  show IsMulCommutative (⊤ : Subgroup (N ⧸ C.subgroupOf N)) ∧
    ∀ x ∈ (⊤ : Subgroup (N ⧸ C.subgroupOf N)), x ^ 2 = 1
  refine ⟨⟨⟨fun a b => Subtype.ext (hquot_comm a.1 b.1)⟩⟩, ?_⟩
  intro x _
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  have hm2 : m ^ 2 = 1 := Subtype.ext (by simpa using hexp (m : H) m.2)
  rw [← QuotientGroup.mk_pow, hm2, QuotientGroup.mk_one]



def quotMulAutOf {H : Type} [Group H] (Y : Subgroup H) [Y.Normal] (e : MulAut H)
    (he : ∀ y ∈ Y, e y ∈ Y) (he' : ∀ y ∈ Y, e⁻¹ y ∈ Y) : MulAut (H ⧸ Y) where
  toFun := QuotientGroup.map Y Y (e.toMonoidHom) (by intro y hy; exact he y hy)
  invFun := QuotientGroup.map Y Y ((e⁻¹).toMonoidHom) (by intro y hy; exact he' y hy)
  left_inv q := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    simp [MulAut.inv_apply_self]
  right_inv q := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    simp [MulAut.apply_inv_self]
  map_mul' := (QuotientGroup.map Y Y (e.toMonoidHom) (by intro y hy; exact he y hy)).map_mul

theorem sec47_quot_hom {X H : Type} [Group X] [Group H] (Y : Subgroup H) [Y.Normal]
    (φ : X →* MulAut H) (hY : ∀ x : X, ∀ y ∈ Y, φ x y ∈ Y) :
    ∃ σ : X →* MulAut (H ⧸ Y), ∀ (x : X) (h : H),
      σ x (QuotientGroup.mk h) = QuotientGroup.mk (φ x h) := by
  have hinv : ∀ x : X, ∀ y ∈ Y, (φ x)⁻¹ y ∈ Y := by
    intro x y hy
    rw [← map_inv φ x]
    exact hY x⁻¹ y hy
  have hψ : ∀ (x : X) (h : H),
      quotMulAutOf Y (φ x) (hY x) (hinv x) (QuotientGroup.mk h) = QuotientGroup.mk (φ x h) :=
    fun _ _ => rfl
  refine ⟨{ toFun := fun x => quotMulAutOf Y (φ x) (hY x) (hinv x),
            map_one' := ?_,
            map_mul' := ?_ }, ?_⟩
  · ext q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [hψ, MulAut.one_apply]
    rw [map_one, MulAut.one_apply]
  · intro x x'
    ext q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [hψ, MulAut.mul_apply]
    rw [map_mul, MulAut.mul_apply]
  · intro x h
    exact hψ x h



theorem t47_card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have hsplit : Polynomial.IsSplittingField (ZMod 2) (GaloisField 2 0)
      (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) :=
    inferInstanceAs (Polynomial.IsSplittingField (ZMod 2)
      (Polynomial.SplittingField (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))) _)
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet (GaloisField 2 0)
    (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))
  have h0 : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) = 0 := by simp
  rw [h0, Polynomial.rootSet_zero, Algebra.adjoin_empty] at hadj
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := fun x =>
    Algebra.mem_bot.mp (hadj ▸ Algebra.mem_top)
  have he : ZMod 2 ≃ GaloisField 2 0 :=
    Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) (GaloisField 2 0)).injective, hsurj⟩
  rw [Nat.card_congr he.symm, Nat.card_zmod]

theorem t47_card_psl2_two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = 6 := by
  rw [Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula K, hK]
  norm_num

theorem t47_isSolvable_psl2_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have h6 := t47_card_psl2_two hK
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  exact CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_natCard (p := 2) (q := 3)
    (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (h6.trans (by norm_num))

theorem t47_card_sz_zero : Nat.card (CFSG.Open.Sz 0) = 20 := by
  obtain ⟨e⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  have hK : Nat.card (ZMod 2) = 2 ^ (2 * 0 + 1) := by simp [Nat.card_zmod]
  rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  norm_num

theorem t47_natCard_quotient_center_eq_one {K : Type} [Group K] [Finite K]
    (hrad : CFSG.solvableRadical K = Subgroup.center K)
    (hsol : Group.IsSolvable (K ⧸ Subgroup.center K)) :
    Nat.card (K ⧸ Subgroup.center K) = 1 := by
  have hK : Group.IsSolvable K :=
    Group.isSolvable_of_subgroup_quotient (Subgroup.center K)
  have htop : CFSG.solvableRadical K = ⊤ := by
    refine eq_top_iff.mpr ?_
    unfold CFSG.solvableRadical
    exact le_sSup ⟨inferInstance, inferInstance⟩
  have hc : Subgroup.center K = ⊤ := hrad.symm.trans htop
  have hidx : (Subgroup.center K).index = 1 := Subgroup.index_eq_one.mpr hc
  exact hidx

theorem sec47_f_two_le {K : Type} [Group K] [Finite K] {f : ℕ}
    (hrad : CFSG.solvableRadical K = Subgroup.center K)
    (hL : IsPSL2Model (K ⧸ Subgroup.center K) f) : 2 ≤ f := by
  by_contra h
  have hf : f < 2 := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 := by
    interval_cases f
    · exact t47_card_galoisField_two_zero
    · rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨e⟩ := hL
  have hPSL : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    t47_isSolvable_psl2_two hK
  have hsol : Group.IsSolvable (K ⧸ Subgroup.center K) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h1 := t47_natCard_quotient_center_eq_one hrad hsol
  rw [Nat.card_congr e.toEquiv, t47_card_psl2_two hK] at h1
  omega

theorem sec47_sz_one_le {K : Type} [Group K] [Finite K] {a : ℕ}
    (hrad : CFSG.solvableRadical K = Subgroup.center K)
    (hL : IsSzModel (K ⧸ Subgroup.center K) a) : 1 ≤ a := by
  by_contra h
  have ha : a = 0 := by omega
  subst ha
  obtain ⟨e⟩ := hL
  have hSz : Group.IsSolvable (CFSG.Open.Sz 0) :=
    CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_sz_zero
  have hsol : Group.IsSolvable (K ⧸ Subgroup.center K) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h1 := t47_natCard_quotient_center_eq_one hrad hsol
  rw [Nat.card_congr e.toEquiv, t47_card_sz_zero] at h1
  omega
end

end CFSG.RankThree.GF2n.Tim77
