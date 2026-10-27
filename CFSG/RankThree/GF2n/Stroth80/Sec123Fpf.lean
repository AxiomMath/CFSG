module

public import CFSG.RankThree.GF2n.Stroth80.Sec123Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec123LA
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.exists_unipotent_vector (hc : Ctx M Q Z B) (hw : Width Q Z 2)
    (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {x : G} (hxX : x ∈ Q ⊔ QB B) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) :
    ∃ d : M₀.E, (¬ ∃ s : K, d = s • b) ∧ M₀.Qf d = 0 ∧ M₀.B d b = 0 ∧
      ∃ κ : K, T d - d = κ • b := by
  classical
  have hlt := hc.card_LB_lt_of_width_two hw
  have hmul := hc.card_LB_mul hw
  have hZD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (hc.Z_le_QB).1
  have hBD : B ≤ Q ⊓ QB B := le_inf hc.le hc.B_le_QB
  have hDQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hDpos : 0 < Nat.card ↥(Q ⊓ QB B) := Nat.card_pos
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hbig : Nat.card Z ^ 2 < Nat.card ↥(Q ⊓ QB B) := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) <
        Nat.card Q * Nat.card Z ^ 2 * Nat.card ↥(Q ⊓ QB B) :=
      Nat.mul_lt_mul_of_pos_right hlt hDpos
    have h2 : Nat.card Q * Nat.card Z ^ 2 * Nat.card ↥(Q ⊓ QB B) ≤
        Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 := Nat.mul_le_mul_left _ hle
    have h3 : Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 = Nat.card Q * Nat.card Z ^ (2 * 2) := by
      ring
    rw [hmul, ← h3] at h1
    omega
  have hcard := M₀.card_eq hDQ hZD
  have himg : Nat.card Z < Nat.card (M₀.img (Q ⊓ QB B)) := by
    have : Nat.card Z * Nat.card Z < Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) := by
      rw [← hcard]
      calc Nat.card Z * Nat.card Z = Nat.card Z ^ 2 := by ring
        _ < _ := hbig
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hK : Nat.card K = Nat.card Z := h.card
  obtain ⟨d, hdD, hdb⟩ : ∃ d ∈ M₀.img (Q ⊓ QB B), ¬ ∃ s : K, d = s • b := by
    by_contra hcon
    push Not at hcon
    have hsub : ((M₀.img (Q ⊓ QB B) : AddSubgroup M₀.E) : Set M₀.E) ⊆
        Set.range fun s : K => s • b := fun d hd => by
      obtain ⟨s, hs⟩ := hcon d hd
      exact ⟨s, hs.symm⟩
    have h1 : ((M₀.img (Q ⊓ QB B) : AddSubgroup M₀.E) : Set M₀.E).ncard ≤
        (Set.range fun s : K => s • b).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (Set.range fun s : K => s • b).ncard ≤ Nat.card K := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le (Set.toFinite _)
    have h3 : Nat.card (M₀.img (Q ⊓ QB B)) =
        ((M₀.img (Q ⊓ QB B) : AddSubgroup M₀.E) : Set M₀.E).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    omega
  obtain ⟨d₀, hd₀D, hd₀Q, rfl⟩ := hdD
  obtain ⟨y₀, hy₀B, hy₀Q, hy₀b⟩ := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have hd₀sq : d₀ ^ 2 = 1 := hc.inf_QB_elemAbelian.2 d₀ hd₀D
  refine ⟨M₀.π d₀, hdb, ?_, ?_, ?_⟩
  · rw [← M₀.sq_eq d₀ hd₀Q, hd₀sq]
    exact h.reg.one
  · rw [← hy₀b, ← M₀.comm_iff_B h.reg hd₀Q hy₀Q]
    exact (Ctx.B_central_QB hc hy₀B hd₀D.2).symm
  · have hc1 := Ctx.sup_QB_comm_inf_mem hc hxX hd₀D
    obtain ⟨z, hz, y', hy', hzy⟩ := (Ctx.mem_sup_iff hc).mp hc1
    have hzQ : z ∈ Q := hc.Z_le_Q hz
    have hy'Q : y' ∈ Q := hc.le hy'
    have e1 : x * d₀ * x⁻¹ = ⁅x, d₀⁆ * d₀ := by simp only [commutatorElement_def]; group
    have hcQ : ⁅x, d₀⁆ ∈ Q := by rw [hzy]; exact Q.mul_mem hzQ hy'Q
    have h1 : M₀.π (x * d₀ * x⁻¹) = M₀.π ⁅x, d₀⁆ + M₀.π d₀ := by
      rw [e1]
      exact M₀.π_mul _ hcQ d₀ hd₀Q
    have h2 : M₀.π ⁅x, d₀⁆ = M₀.π y' := by
      rw [hzy, M₀.π_mul z hzQ y' hy'Q, (M₀.π_ker z hzQ).mpr hz, zero_add]
    obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hy' hy'Q)
    refine ⟨s, ?_⟩
    rw [← hT d₀ hd₀Q, h1, h2, add_sub_cancel_right, hs]


theorem pow_apply_eigen {E : Type} [AddCommGroup E] [Module K E] (T : E →ₗ[K] E) (ε : K) {v : E}
    (hv : T v = ε • v) (i : ℕ) : (T ^ i) v = ε ^ i • v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, ← pow_succ']

section Fpf

variable [CharP K 2]

theorem stroth123Fpf_holds : Stroth123FixedPointFreeStatement := by
  classical
  intro G _ _ M Q Z B hc hw
  obtain ⟨K, _, _, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  haveI := hchar
  obtain ⟨b, hb0, hbQ, hB, -, -⟩ := hc.dictB h
  obtain ⟨y, hyX, hyM, hyB, hyZ, hyord, hyreg⟩ := hc.exists_torusOrd
  obtain ⟨a, Tl, hTπ, hTγ, hTQ, hTb⟩ := hc.torus_model h hb0 hB hyX hyZ hyB
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hK : Nat.card K = Nat.card Z := h.card
  have hK1 : 1 < Nat.card K := by omega
  have hdim : Module.finrank K M₀.E = 4 := h.finrank_E hw hK1
  have hLnorm : ∀ g : G, g ∈ M → g ∈ Subgroup.normalizer (B : Set G) →
      ∀ l ∈ LB M Q B, g * l * g⁻¹ ∈ LB M Q B := by
    intro g hgM hgB l hl
    have h1 := hc.LB_conj hgM
    rw [conjSubgroup_eq_self_iff.mpr hgB] at h1
    have h2 : g * l * g⁻¹ ∈ conjSubgroup g (LB M Q B) :=
      mem_conjSubgroup.mpr (by
        have e : g⁻¹ * (g * l * g⁻¹) * g = l := by group
        rw [e]
        exact hl)
    rwa [← h1] at h2
  refine ⟨y, hyM, hyord, fun l hl => hLnorm y hyM hyB l hl, ?_⟩
  intro i hi0 hi l hl hcomm
  set T : M₀.E →ₗ[K] M₀.E := (Tl : M₀.E →ₗ[K] M₀.E) with hTdef
  have hQmem : ∀ (j : ℕ), ∀ x ∈ Q, y ^ j * x * (y ^ j)⁻¹ ∈ Q := fun j x hx =>
    (hc.conj_mem_Q_of_mem_M (Subgroup.pow_mem _ hyM j)).1 x hx
  have hTpow : ∀ (j : ℕ), ∀ x ∈ Q, M₀.π (y ^ j * x * (y ^ j)⁻¹) = (T ^ j) (M₀.π x) := by
    intro j
    induction j with
    | zero => intro x hx; simp
    | succ j ih =>
      intro x hx
      have e : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by
        rw [pow_succ']; group
      rw [e, hTπ _ (hQmem j x hx), ih x hx, pow_succ', Module.End.mul_apply]
      rfl
  have hα0 : (a : K) ≠ 0 := a.ne_zero
  obtain ⟨v₀, hv₀Z, hv₀⟩ : ∃ v ∈ Z, v ≠ 1 := by
    have h1 : 1 < Nat.card Z := by omega
    obtain ⟨⟨v, hv⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot Z).mp h1)
    exact ⟨v, hv, fun he => hne (Subtype.ext he)⟩
  have hγv₀ : γ v₀ ≠ 0 := fun h0 => hv₀ (h.gamma_inj hv₀Z Z.one_mem (h0.trans h.reg.one.symm))
  have hia : ∀ j : ℕ, 0 < j → j < Nat.card Z - 1 → (a : K) ^ j ≠ 1 := by
    intro j hj0 hj h1
    obtain ⟨hmem, hγ⟩ := torus_gamma_pow hyZ hTγ j v₀ hv₀Z
    rw [h1, one_mul] at hγ
    have h2 := h.gamma_inj hmem hv₀Z hγ
    have h3 : y ^ j * v₀ = v₀ * y ^ j := by
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    exact hv₀ (hyreg j hj0 hj v₀ hv₀Z h3)
  have hq1 : Nat.card Kˣ = Nat.card Z - 1 := by rw [Nat.card_units, h.card]
  have haqU : a ^ (Nat.card Z - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := a)
    rwa [hq1] at this
  have haord : orderOf a = Nat.card Z - 1 := by
    refine (orderOf_eq_iff (by omega)).mpr ⟨haqU, fun m hm hm0 hm1 => ?_⟩
    exact hia m hm0 hm (by simpa using congrArg Units.val hm1)
  have hdiv : ∀ j : ℕ, (a : K) ^ j = 1 → Nat.card Z - 1 ∣ j := by
    intro j hj
    rw [← haord]
    exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using hj))
  have hodd : Odd (Nat.card Z - 1) := by
    obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hr
      omega
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    obtain ⟨c, hc'⟩ := (Nat.even_pow.mpr ⟨even_two, hr0⟩ : Even (2 ^ r))
    exact ⟨c - 1, by omega⟩
  have hα2 : ∀ j : ℕ, 0 < j → j < Nat.card Z - 1 → (a : K) ^ (2 * j) ≠ 1 := by
    intro j hj0 hj h1
    have h2 := hdiv _ h1
    have h3 : Nat.card Z - 1 ∣ j :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) (by
        simpa [mul_comm] using h2)
    have := Nat.le_of_dvd hj0 h3
    omega
  have hTb' : T b = ((a : K)⁻¹) • b := by
    have := hTb
    rwa [Units.val_inv_eq_inv_val] at this
  have hTQ' : ∀ e, M₀.Qf (T e) = (a : K) * M₀.Qf e := hTQ
  have hTB : ∀ e f, M₀.B (T e) (T f) = (a : K) * M₀.B e f := by
    intro e f
    have h3 : M₀.Qf (Tl (e + f)) = (a : K) * M₀.Qf (e + f) := hTQ _
    rw [map_add, M₀.Qf_add (Tl e) (Tl f), M₀.Qf_add e f, hTQ e, hTQ f] at h3
    show M₀.B (Tl e) (Tl f) = _
    linear_combination h3
  have hTq : T ^ (Nat.card K - 1) = 1 := by
    refine LinearMap.ext fun e => ?_
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hTpow _ x hxQ, hK, ← hyord, pow_orderOf_eq_one]
    simp
  have hα1 : (a : K) ≠ 1 := by simpa using hia 1 one_pos (by omega)
  have hα2' : (a : K) ^ 2 ≠ 1 := by simpa using hα2 1 one_pos (by omega)
  obtain ⟨d, hdb, hdQ, hdB, κ, hκ⟩ := hc.exists_unipotent_vector hw h hB hyX (T := T) hTπ
  have hαinv1 : (a : K)⁻¹ ≠ 1 := fun h1 => hα1 (inv_eq_one.mp h1)
  have h1ma : (1 - (a : K)⁻¹) ≠ 0 := sub_ne_zero.mpr (Ne.symm hαinv1)
  set s : K := κ / (1 - (a : K)⁻¹) with hs
  have hss : s * (1 - (a : K)⁻¹) = κ := by rw [hs]; field_simp
  set u : M₀.E := d + s • b with hu
  have hTu : T u = u := by
    have e1 : T d = d + κ • b := by rw [← hκ]; abel
    calc T u = T d + s • T b := by rw [hu, map_add, map_smul]
      _ = (d + κ • b) + s • ((a : K)⁻¹ • b) := by rw [e1, hTb']
      _ = d + (κ + s * (a : K)⁻¹) • b := by rw [smul_smul, add_smul, add_assoc]
      _ = d + s • b := by
        congr 2
        linear_combination (-1 : K) * hss
  have hQu : M₀.Qf u = 0 := by
    rw [hu, M₀.Qf_add, M₀.Qf_smul, hbQ, hdQ, map_smul, hdB]
    simp
  have hBub : M₀.B u b = 0 := by
    rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hdB, M₀.alt b]
    simp
  have hu0 : u ≠ 0 := by
    intro hu0
    apply hdb
    refine ⟨-s, ?_⟩
    have : d = -(s • b) := eq_neg_of_add_eq_zero_left (by rw [hu] at hu0; exact hu0)
    rw [this, neg_smul]
  obtain ⟨u₂, c, hTu₂, hTc, hQu₂, hQc, hbc, huu₂, hbu₂, huc, hu₂c⟩ :=
    LA.exists_frame M₀.B M₀.Qf M₀.Qf_smul M₀.Qf_add M₀.alt M₀.nondeg hα0 hα1 hα2' T hTq hTB hTQ'
      b u hb0 hbQ hTb' hQu hBub hTu hu0
  have Bsymm : ∀ e f : M₀.E, M₀.B e f = M₀.B f e := fun e f => by
    rw [Tim79.QuadModel.B_comm (M₀ := M₀) e f]
    exact CharTwo.neg_eq _
  obtain ⟨hli, hspan⟩ := LA.gram_basis M₀.B hdim b u u₂ c hbc (by rw [Bsymm]; exact hbc) huu₂
    (by rw [Bsymm]; exact huu₂) (M₀.alt b) (M₀.alt u) (M₀.alt u₂) (M₀.alt c)
    (by rw [Bsymm]; exact hBub) hBub hbu₂ (by rw [Bsymm]; exact hbu₂) huc
    (by rw [Bsymm]; exact huc) hu₂c (by rw [Bsymm]; exact hu₂c)
  obtain ⟨Φ, hΦπ, hΦker, hΦiso⟩ := hc.exists_actionHom_LB h
  set r : ↥(LB M Q B) := ⟨l, hl⟩ with hr
  set S : M₀.E →ₗ[K] M₀.E := ((Φ r : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) with hSdef
  have hSπ : ∀ x ∈ Q, S (M₀.π x) = M₀.π (l * x * l⁻¹) := fun x hx => (hΦπ r x hx).symm
  have hSb : S b = b := (hc.LB_act_fix_line h hB hl (T := S) (fun x hx => hΦπ r x hx)).1
  have hSQ : ∀ x, M₀.Qf (S x) = M₀.Qf x := hΦiso r
  have hS2 : ∀ x, S (S x) = x := by
    intro x
    have h1 : Φ r * Φ r = 1 := by
      rw [← map_mul]
      refine (hΦker (r * r)).mpr ?_
      have := hc.sq_mem_Q_of_mem_LB hl
      simpa [hr, pow_two] using this
    have h2 : (Φ r * Φ r) x = x := by rw [h1]; rfl
    exact h2
  have hπconj : ∀ c' ∈ Q, ∀ v ∈ Q, M₀.π (c' * v * c'⁻¹) = M₀.π v := by
    intro c' hc' v hv
    have e : c' * v * c'⁻¹ = ⁅c', v⁆ * v := by simp only [commutatorElement_def]; group
    have hZ : ⁅c', v⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hc' hv
    rw [e, M₀.π_mul _ (hc.Z_le_Q hZ) v hv, (M₀.π_ker _ (hc.Z_le_Q hZ)).mpr hZ, zero_add]
  have hSP : ∀ x, S ((T ^ i) x) = (T ^ i) (S x) := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hu' := hQmem i x hxQ
    have hlM := hc.LB_le_M hl
    have hv' : l * x * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hlM).1 x hxQ
    have hw' : l * (y ^ i * x * (y ^ i)⁻¹) * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hlM).1 _ hu'
    rw [← hTpow i x hxQ, hSπ _ hu', hSπ x hxQ, ← hTpow i _ hv']
    have e : y ^ i * (l * x * l⁻¹) * (y ^ i)⁻¹ = (y ^ i * l * (y ^ i)⁻¹ * l⁻¹) *
        (l * (y ^ i * x * (y ^ i)⁻¹) * l⁻¹) * (y ^ i * l * (y ^ i)⁻¹ * l⁻¹)⁻¹ := by group
    rw [e, hπconj _ hcomm _ hw']
  have hP1 : (T ^ i) b = (((a : K)⁻¹) ^ i) • b := pow_apply_eigen T _ hTb' i
  have hP2 : (T ^ i) u = (1 : K) • u := by
    have := pow_apply_eigen T 1 (by rw [one_smul]; exact hTu) i
    rwa [one_pow] at this
  have hP3 : (T ^ i) u₂ = ((a : K) ^ i) • u₂ := pow_apply_eigen T _ hTu₂ i
  have hP4 : (T ^ i) c = (((a : K) ^ 2) ^ i) • c := pow_apply_eigen T _ hTc i
  have hai : (a : K) ^ i ≠ 1 := hia i hi0 hi
  have ha2i : (a : K) ^ (2 * i) ≠ 1 := hα2 i hi0 hi
  have h21 : (1 : K) ≠ ((a : K)⁻¹) ^ i := by
    intro h1
    apply hai
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1.symm
  have h23 : (1 : K) ≠ (a : K) ^ i := fun h1 => hai h1.symm
  have h24 : (1 : K) ≠ ((a : K) ^ 2) ^ i := by
    intro h1
    apply ha2i
    rw [← pow_mul] at h1
    exact h1.symm
  have h31 : (a : K) ^ i ≠ ((a : K)⁻¹) ^ i := by
    intro h1
    apply ha2i
    rw [inv_pow] at h1
    have h2 : (a : K) ^ i * (a : K) ^ i = 1 := by
      calc (a : K) ^ i * (a : K) ^ i = (a : K) ^ i * ((a : K) ^ i)⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hα0)
    rw [two_mul, pow_add]
    exact h2
  have h34 : (a : K) ^ i ≠ ((a : K) ^ 2) ^ i := by
    intro h1
    apply hai
    rw [← pow_mul, two_mul, pow_add] at h1
    have h2 : (a : K) ^ i * 1 = (a : K) ^ i * (a : K) ^ i := by rw [mul_one]; exact h1
    exact (mul_left_cancel₀ (pow_ne_zero i hα0) h2).symm
  have hall := LA.comm_involution_trivial M₀.B M₀.Qf M₀.Qf_smul M₀.Qf_add b u u₂ c hli hspan hbQ
    hQc hbc (by rw [Bsymm]; exact hbc) (((a : K)⁻¹) ^ i) 1 ((a : K) ^ i) (((a : K) ^ 2) ^ i)
    (T ^ i) hP1 hP2 hP3 hP4 h21 h23 h24 h31 h34 S hSQ hS2 hSb hSP
  have hΦ1 : Φ r = 1 := LinearEquiv.ext fun x => hall x
  exact (hΦker r).mp hΦ1

end Fpf

end CFSG.RankThree.GF2n.Stroth80
