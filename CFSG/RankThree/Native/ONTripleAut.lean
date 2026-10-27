module

public import CFSG.RankThree.Native.ONTripleAutLin
public import CFSG.RankThree.Native.ONTripleAutCheck
public import CFSG.RankThree.Native.ONTripleRed

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup Equiv
open CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
open CFSG.KC.Misc.F7

attribute [local irreducible] dotProduct

@[expose] def ySet : Set GM :=
  Set.range fun i : Fin 9 => (⟨eM (yRegs.getD i.val 0), eM_mem _⟩ : GM)

theorem M_eq_closure : M = Subgroup.closure (Set.range gM) := by
  rw [M, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  have : (⇑psiM ∘ PresentedGroup.of) = gM := funext fun k => psiM_of k
  rw [this]

theorem closure_Y : Subgroup.closure ySet = ⊤ := by
  set Kp : Subgroup Mat45ˣ := (Subgroup.closure ySet).map M.subtype with hKp
  have hY : Subgroup.closure (Set.range fun i : Fin 9 => eM (yRegs.getD i.val 0)) ≤ Kp := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨eM (yRegs.getD i.val 0), eM_mem _⟩, subset_closure ⟨i, rfl⟩, rfl⟩
  have hgen : ∀ k : Fin 8, gM k ∈ Kp := fun k => hY (aut_check.1 k)
  have hM : M ≤ Kp := by
    rw [M_eq_closure, closure_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, he⟩ := hM g.2
  have : h = g := Subtype.ext he
  rw [← this]
  exact hh

theorem eq_id_of_fix_Y (φ : GM ≃* GM) (h : ∀ y ∈ ySet, φ y = y) (x : GM) : φ x = x := by
  have heq : φ.toMonoidHom = MonoidHom.id GM :=
    MonoidHom.eq_of_eqOn_dense closure_Y fun y hy => h y hy
  exact congrArg (fun f : GM →* GM => f x) heq

@[expose] def coordG (g : GM) : Fin 4 → ZMod 3 := by
  classical
  exact if h : g ∈ P0G then relG.coord ⟨g, h⟩ else 0

theorem coordG_of {g : GM} (hg : g ∈ P0G) : coordG g = relG.coord ⟨g, hg⟩ := by
  unfold coordG
  simp only [hg, ↓reduceDIte]

@[expose] def restrictP0 (φ : GM →* GM) (h : ∀ g ∈ P0G, φ g ∈ P0G) : P0G →* P0G where
  toFun g := ⟨φ (g : GM), h g g.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a : GM) (b : GM))

theorem surj_P0 (φ : GM ≃* GM) (h : ∀ g ∈ P0G, φ g ∈ P0G) {y : GM} (hy : y ∈ P0G) :
    ∃ x ∈ P0G, φ x = y := by
  have hle : P0G.map φ.toMonoidHom ≤ P0G := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  have heq : P0G.map φ.toMonoidHom = P0G :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective φ.injective])
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

theorem matrix_eq_of_rows {A B : M4} (h : ∀ i, Matrix.vecMul (Pi.single i 1) A =
    Matrix.vecMul (Pi.single i 1) B) : A = B := by
  ext i j
  have := congrFun (h i) j
  rwa [single_vecMul, single_vecMul] at this

theorem exists_word_coord (φ : GM ≃* GM) (hz : φ zG = zG) (hP : ∀ g ∈ P0G, φ g ∈ P0G) :
    ∃ w : List ℕ, (∀ k ∈ w, k < 2) ∧ ∀ g ∈ P0G,
      wordN w * φ g * (wordN w)⁻¹ ∈ P0G ∧ coordG (wordN w * φ g * (wordN w)⁻¹) = coordG g := by
  set f := restrictP0 φ.toMonoidHom hP with hfdef
  set T := matOf f with hTdef
  have hzf : f ⟨zG, ThreeQRel.x_mem⟩ = ⟨zG, ThreeQRel.x_mem⟩ := Subtype.ext hz
  have hcoord : ∀ g : P0G, relG.coord (f g) = Matrix.vecMul (relG.coord g) T :=
    coord_map f (by rw [hzf, coord_zG])
  obtain ⟨hTS, hc, -⟩ := sp_facts T (matOf_sp f hzf)
  have hST : symInvM T * T = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin 4) (Fin 4) (ZMod 3)
    rfl).mp hTS
  have hφN : ∀ n ∈ NP0, φ n ∈ NP0 := by
    intro n hn
    apply mem_NP0_of
    intro h hh
    obtain ⟨x, hx, rfl⟩ := surj_P0 φ hP hh
    have := hP _ (conj_mem_P0_of hn hx)
    rwa [map_mul, map_mul, map_inv] at this
  have hrel : ∀ n : NP0, muN n * T = T * muN ⟨φ n, hφN n n.2⟩ := by
    intro n
    apply matrix_eq_of_rows
    intro i
    have e : f (conjN n ⟨xG i, ThreeQRel.v_mem i⟩) =
        conjN ⟨φ n, hφN n n.2⟩ (f ⟨xG i, ThreeQRel.v_mem i⟩) := by
      apply Subtype.ext
      show φ ((n : GM)⁻¹ * xG i * n) = (φ n)⁻¹ * φ (xG i) * φ n
      rw [map_mul, map_mul, map_inv]
    have e2 := congrArg relG.coord e
    rw [hcoord, coord_conjN, coord_conjN, hcoord, coord_xG] at e2
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    exact e2
  have hmem : ∀ k < 2, symInvM T * matNM k * T ∈ R0list := by
    intro k hk
    have h1 := hrel ⟨nG k, nG_mem_NP0 hk⟩
    rw [muN_nG hk] at h1
    have h2 : symInvM T * matNM k * T = muN ⟨φ (nG k), hφN _ (nG_mem_NP0 hk)⟩ := by
      rw [mul_assoc, h1, ← mul_assoc, hST, one_mul]
    rw [h2]
    exact muN_mem_R0 _
  have hTR := hc (hmem 0 (by norm_num)) (hmem 1 (by norm_num))
  obtain ⟨w, hw, hTw⟩ := exists_word_of_mem_R0 hTR
  have hNmem := wordN_mem_NP0 w hw
  have hTN : T = muN ⟨wordN w, hNmem⟩ := by rw [hTw, muN_wordN w hw]
  refine ⟨w, hw, fun g hg => ?_⟩
  have hφg := hP g hg
  have hin : wordN w * φ g * (wordN w)⁻¹ ∈ P0G := by
    have := conj_mem_P0_of (inv_mem hNmem) hφg
    simpa using this
  refine ⟨hin, ?_⟩
  rw [coordG_of hin, coordG_of hg]
  have e : (⟨wordN w * φ g * (wordN w)⁻¹, hin⟩ : P0G) =
      conjN ⟨(wordN w)⁻¹, inv_mem hNmem⟩ (f ⟨g, hg⟩) := by
    apply Subtype.ext
    rw [conjN_apply]
    show wordN w * φ g * (wordN w)⁻¹ = ((wordN w)⁻¹)⁻¹ * φ g * (wordN w)⁻¹
    rw [inv_inv]
  rw [e, coord_conjN, hcoord, Matrix.vecMul_vecMul, hTN, ← muN_mul]
  have h1 : (⟨wordN w, hNmem⟩ : NP0) * ⟨(wordN w)⁻¹, inv_mem hNmem⟩ = 1 :=
    Subtype.ext (mul_inv_cancel _)
  rw [h1, muN_one, Matrix.vecMul_one]

theorem threePair_single_right (v : Fin 4 → ZMod 3) (i : Fin 4) :
    ThreeQRel.threePair omegaZ v (Pi.single i 1) = ThreeQRel.threeForm omegaZ v i := by
  simp [ThreeQRel.threePair, Pi.single_apply]

theorem zG_pow_neg_val (c : ℕ) : zG ^ ((-(c : ZMod 3)).val + c) = 1 := by
  rw [relG.x_pow_eq_x_pow_val]
  have : (((-(c : ZMod 3)).val + c : ℕ) : ZMod 3) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id]
    exact neg_add_cancel _
  rw [this, ZMod.val_zero, pow_zero]

theorem zG_pow_central (m : ℕ) (g : GM) : zG ^ m * g = g * zG ^ m :=
  (Commute.pow_left (zG_central g) m).eq

theorem exists_P0_fix (ψ : GM ≃* GM) (hz : ψ zG = zG) (hP : ∀ g ∈ P0G, ψ g ∈ P0G)
    (hc : ∀ g ∈ P0G, coordG (ψ g) = coordG g) :
    ∃ p ∈ P0G, ∀ g ∈ P0G, p * ψ g * p⁻¹ = g := by
  have hx : ∀ i : Fin 4, ∃ c : ℕ, ψ (xG i) = xG i * zG ^ c := by
    intro i
    have h := hc (xG i) (ThreeQRel.v_mem i)
    rw [coordG_of (hP _ (ThreeQRel.v_mem i)), coordG_of (ThreeQRel.v_mem i)] at h
    exact eq_mul_zpow_of_coord _ _ h
  choose c hcx using hx
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 relG.threeForm_injective)
    (fun i => -((c i : ℕ) : ZMod 3))
  set p := threeNF zG xG 0 v with hpdef
  have hp : p ∈ P0G := ThreeQRel.nf_mem 0 v
  have hcp : relG.coord ⟨p, hp⟩ = v := relG.coord_nf 0 v
  have hfix : ∀ i : Fin 4, p * ψ (xG i) * p⁻¹ = xG i := by
    intro i
    have hcomm := relG.comm_coord_coord ⟨p, hp⟩ ⟨xG i, ThreeQRel.v_mem i⟩
    rw [hcp, coord_xG, threePair_single_right, congrFun hv i] at hcomm
    simp only [commutatorElement_def] at hcomm
    have h1 : p * xG i * p⁻¹ = zG ^ (-((c i : ℕ) : ZMod 3)).val * xG i := by
      rw [← hcomm]
      group
    calc p * ψ (xG i) * p⁻¹ = p * (xG i * zG ^ c i) * p⁻¹ := by rw [hcx]
      _ = p * xG i * p⁻¹ * zG ^ c i := by
          rw [show p * (xG i * zG ^ c i) * p⁻¹ = p * xG i * (zG ^ c i * p⁻¹) by group,
            zG_pow_central (c i) p⁻¹]
          group
      _ = zG ^ (-((c i : ℕ) : ZMod 3)).val * xG i * zG ^ c i := by rw [h1]
      _ = xG i * (zG ^ (-((c i : ℕ) : ZMod 3)).val * zG ^ c i) := by
          rw [zG_pow_central _ (xG i)]
          group
      _ = xG i := by rw [← pow_add, zG_pow_neg_val, mul_one]
  refine ⟨p, hp, fun g hg => ?_⟩
  have hle : P0G ≤
      MonoidHom.eqLocus ((ψ.trans (MulAut.conj p)).toMonoidHom) (MonoidHom.id GM) := by
    show threeQ zG xG ≤ _
    rw [threeQ, closure_le]
    rintro y (rfl | ⟨i, rfl⟩)
    · show p * ψ zG * p⁻¹ = zG
      rw [hz, mul_assoc, zG_central, ← mul_assoc, mul_inv_cancel, one_mul]
    · exact hfix i
  exact hle hg

theorem fix_NP0 (φ : GM ≃* GM) (hP : ∀ g ∈ P0G, φ g = g) : ∀ n ∈ NP0, φ n = n := by
  intro n hn
  have hcent : ∀ g ∈ P0G, (φ n * n⁻¹) * g = g * (φ n * n⁻¹) := by
    intro g hg
    have h1 := hP _ (conj_mem_P0_of hn hg)
    rw [map_mul, map_mul, map_inv, hP g hg] at h1
    calc φ n * n⁻¹ * g = φ n * (n⁻¹ * g * n) * n⁻¹ := by group
      _ = φ n * ((φ n)⁻¹ * g * φ n) * n⁻¹ := by rw [h1]
      _ = g * (φ n * n⁻¹) := by group
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).2 (mem_zpowers_of_centralizes_P0 hcent)
  have hm' : zG ^ m = φ n * n⁻¹ := hm
  have hφn : φ n = zG ^ m * n := by rw [hm', inv_mul_cancel_right]
  have hq := hP _ (pow_relIndex_mem ⟨n, hn⟩)
  rw [map_pow, hφn, (Commute.pow_left (zG_central n) m).mul_pow, ← pow_mul] at hq
  have hz1 : zG ^ (m * (P0G.subgroupOf NP0).index) = 1 := by
    have := congrArg (· * ((n : GM) ^ (P0G.subgroupOf NP0).index)⁻¹) hq
    simpa using this
  have h3 : 3 ∣ m * (P0G.subgroupOf NP0).index := by
    rw [← relG.orderOf_x]
    exact orderOf_dvd_of_pow_eq_one hz1
  have hcop : Nat.Coprime 3 (P0G.subgroupOf NP0).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 relIndex_not_dvd
  obtain ⟨d, rfl⟩ := hcop.dvd_of_dvd_mul_right h3
  rw [hφn, pow_mul, relG.xcube, one_pow, one_mul]

theorem comm_central {X Y k k' : GM} (hXk' : Commute X k') (hXY : Commute X Y)
    (hYk : Commute Y k) : (X * k)⁻¹ * (Y * k')⁻¹ * (X * k) * (Y * k') = k⁻¹ * k'⁻¹ * k * k' := by
  have e1 : X⁻¹ * k'⁻¹ = k'⁻¹ * X⁻¹ := (hXk'.inv_inv).eq
  have e2 : X⁻¹ * Y⁻¹ * X = Y⁻¹ := by
    rw [(hXY.inv_inv).eq, mul_assoc, inv_mul_cancel, mul_one]
  have e3 : Y⁻¹ * k * Y = k := by
    rw [mul_assoc, ← hYk.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (X * k)⁻¹ * (Y * k')⁻¹ * (X * k) * (Y * k') =
      k⁻¹ * (X⁻¹ * k'⁻¹) * Y⁻¹ * X * k * Y * k' := by group
    _ = k⁻¹ * k'⁻¹ * (X⁻¹ * Y⁻¹ * X) * k * Y * k' := by rw [e1]; group
    _ = k⁻¹ * k'⁻¹ * (Y⁻¹ * k * Y) * k' := by rw [e2]; group
    _ = k⁻¹ * k'⁻¹ * k * k' := by rw [e3]

theorem comm_mem_K0 {c d : GM} (hc : c ∈ centralizer {xG 0}) (hd : d ∈ centralizer {xG 0}) :
    c⁻¹ * d⁻¹ * c * d ∈ K0G := by
  obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hc
  obtain ⟨b, k', hk', rfl⟩ := mem_centralizer_x0_iff.1 hd
  have hk0 : Commute k (xG 0) := K0_comm hk
  have hk0' : Commute k' (xG 0) := K0_comm hk'
  rw [comm_central (hk0'.pow_right a).symm (Commute.pow_pow_self _ _ _) (hk0.pow_right b).symm]
  exact mul_mem (mul_mem (mul_mem (inv_mem hk) (inv_mem hk')) hk) hk'

@[expose] def t4G : GM := wordN [0, 1, 1] ^ 3

theorem t4G_mem_NP0 : t4G ∈ NP0 := pow_mem (wordN_mem_NP0 _ (by decide)) 3

theorem t4G_val :
    t4G.1 = ([0, 1, 1].map fun k => eM (if k = 0 then rN1 else rN2)).prod ^ 3 := by
  rw [t4G, SubgroupClass.coe_pow, wordN_val]

theorem t4_facts :
    t4G * xG 0 = xG 0 * t4G ∧ t4G ^ 4 = 1 ∧ MapsB t4G.1 [3, 4, 5, 2, 1, 0] := by
  obtain ⟨h1, h2, h3⟩ := aut_check.2.1
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · change t4G.1 * eM (rX.getD 0 0) = eM (rX.getD 0 0) * t4G.1
    rw [t4G_val]
    exact h1
  · rw [SubgroupClass.coe_pow, OneMemClass.coe_one, t4G_val]
    exact h2
  · rw [t4G_val]
    exact h3

theorem t4G_mem_K0 : t4G ∈ K0G :=
  mem_K0_of_two (n := 2) (mem_centralizer_singleton_iff.2 t4_facts.1) t4_facts.2.1

theorem s4_vals : ∀ b : Fin 6, (s4 b).val = [3, 4, 5, 2, 1, 0].getD b.val 6 := by
  decide

theorem actK_t4 : actK ⟨t4G, t4G_mem_K0⟩ = s4 :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps s4_vals t4_facts.2.2)

@[expose] def cG (i : ℕ) : GM := ⟨eM (rC.getD i 0), eM_mem _⟩

theorem c_facts : (∀ i < 3, cG i * xG 0 = xG 0 * cG i) ∧
    k1G = (cG 0)⁻¹ * (cG 1)⁻¹ * cG 0 * cG 1 ∧ k2G = (cG 0)⁻¹ * (cG 2)⁻¹ * cG 0 * cG 2 := by
  obtain ⟨-, -, h1, h2, h3⟩ := aut_check
  exact ⟨fun i hi => Subtype.ext (h1 i hi), Subtype.ext h2, Subtype.ext h3⟩

theorem evW_cube {X : Type*} [Monoid X] (a b : X) : evW a b [0, 0, 0] = a ^ 3 ∧
    evW a b [1, 1, 1] = b ^ 3 := by
  simp [evW, pow_three]

theorem evW_five {X : Type*} [Group X] (a b : X) :
    evW a b [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] = (a * b) ^ 5 := by
  simp only [evW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ↓reduceIte,
    one_ne_zero, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]

theorem map_C_x0 (φ : GM ≃* GM) (hx0 : φ (xG 0) = xG 0) :
    ∀ c ∈ centralizer {xG 0}, φ c ∈ centralizer {xG 0} := by
  intro c hc
  rw [mem_centralizer_singleton_iff] at hc ⊢
  rw [← hx0, ← map_mul, hc, map_mul]

theorem map_K0 (φ : GM ≃* GM) (hx0 : φ (xG 0) = xG 0) (hz : φ zG = zG) :
    ∀ k ∈ K0G, φ k ∈ K0G := by
  obtain ⟨hc, hk1, hk2⟩ := c_facts
  have hcC : ∀ i < 3, cG i ∈ centralizer {xG 0} := fun i hi =>
    mem_centralizer_singleton_iff.2 (hc i hi)
  have hC := map_C_x0 φ hx0
  intro k hk
  have hle : K0G ≤ K0G.comap φ.toMonoidHom := by
    refine (closure_le (K := K0G.comap φ.toMonoidHom)).2 ?_
    rintro y (rfl | rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hk1, map_mul, map_mul,
        map_mul, map_inv, map_inv]
      exact comm_mem_K0 (hC _ (hcC 0 (by norm_num))) (hC _ (hcC 1 (by norm_num)))
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hk2, map_mul, map_mul,
        map_mul, map_inv, map_inv]
      exact comm_mem_K0 (hC _ (hcC 0 (by norm_num))) (hC _ (hcC 2 (by norm_num)))
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hz]
      exact zG_mem_K0
  exact hle hk

@[expose] def restrictK0 (φ : GM ≃* GM) (h : ∀ k ∈ K0G, φ k ∈ K0G) : K0G →* K0G where
  toFun k := ⟨φ (k : GM), h k k.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a : GM) (b : GM))

theorem restrictK0_apply (φ : GM ≃* GM) (h : ∀ k ∈ K0G, φ k ∈ K0G) (k : K0G) :
    ((restrictK0 φ h k : K0G) : GM) = φ k := rfl

theorem evW_fixed (φ : GM ≃* GM) (hz : φ zG = zG) (h : ∀ k ∈ K0G, φ k ∈ K0G) (e : GM)
    (he : e ∈ K0G) (hφe : φ e = e) (w : List ℕ) (hw : evW sK1 sK2 w = actK ⟨e, he⟩) :
    evW (actK (restrictK0 φ h ⟨k1G, k1_mem⟩)) (actK (restrictK0 φ h ⟨k2G, k2_mem⟩)) w =
      actK ⟨e, he⟩ := by
  set E : K0G := evW ⟨k1G, k1_mem⟩ ⟨k2G, k2_mem⟩ w with hEdef
  have hE : actK E = actK ⟨e, he⟩ := by rw [hEdef, map_evW, actK_k1, actK_k2, hw]
  obtain ⟨c, hc'⟩ := zG_mem_ker (E * (⟨e, he⟩ : K0G)⁻¹)
    (by rw [map_mul, map_inv, hE, mul_inv_cancel])
  have hEe : (E : GM) = zG ^ c * e := by
    rw [← hc']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hφE : restrictK0 φ h E = E := by
    apply Subtype.ext
    rw [restrictK0_apply, hEe, map_mul, map_pow, hz, hφe]
  have key : evW (actK (restrictK0 φ h ⟨k1G, k1_mem⟩)) (actK (restrictK0 φ h ⟨k2G, k2_mem⟩)) w =
      actK (restrictK0 φ h E) := by
    rw [hEdef, ← map_evW actK, ← map_evW (restrictK0 φ h)]
  rw [key, hφE, hE]

theorem fix_K0_end (φ : GM ≃* GM) (hx0 : φ (xG 0) = xG 0) (hz : φ zG = zG)
    (hK : ∀ k ∈ K0G, φ k ∈ K0G) (hu1 : actK (restrictK0 φ hK ⟨k1G, k1_mem⟩) = sK1)
    (hu2 : actK (restrictK0 φ hK ⟨k2G, k2_mem⟩) = sK2) : φ k1G = k1G ∧ φ k2G = k2G := by
  obtain ⟨hc, hk1, hk2⟩ := c_facts
  have hcC : ∀ i < 3, cG i ∈ centralizer {xG 0} := fun i hi =>
    mem_centralizer_singleton_iff.2 (hc i hi)
  have hf : actK.comp (restrictK0 φ hK) = actK := by
    have htop : Subgroup.closure (((↑) : K0G → GM) ⁻¹' ({k1G, k2G, zG} : Set GM)) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    apply MonoidHom.eq_of_eqOn_dense htop
    rintro ⟨y, hy⟩ hyS
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hyS
    rcases hyS with rfl | rfl | rfl
    · rw [MonoidHom.comp_apply, hu1, actK_k1]
    · rw [MonoidHom.comp_apply, hu2, actK_k2]
    · rw [MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hz
  have hcz : ∀ c ∈ centralizer {xG 0}, ∃ e : ℕ, φ c = zG ^ e * c := by
    intro c hc
    obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hc
    have hk' : actK (restrictK0 φ hK ⟨k, hk⟩) = actK ⟨k, hk⟩ :=
      congrArg (fun F : K0G →* Perm (Fin 6) => F ⟨k, hk⟩) hf
    obtain ⟨e, he⟩ := zG_mem_ker (restrictK0 φ hK ⟨k, hk⟩ * (⟨k, hk⟩ : K0G)⁻¹)
      (by rw [map_mul, map_inv, hk', mul_inv_cancel])
    have hφk : φ k = zG ^ e * k := by
      have he' : φ k * k⁻¹ = zG ^ e := he
      rw [← he', inv_mul_cancel_right]
    refine ⟨e, ?_⟩
    rw [map_mul, map_pow, hx0, hφk, ← mul_assoc, ← zG_pow_central e, mul_assoc]
  have hcomm : ∀ {i j : ℕ}, i < 3 → j < 3 →
      φ ((cG i)⁻¹ * (cG j)⁻¹ * cG i * cG j) = (cG i)⁻¹ * (cG j)⁻¹ * cG i * cG j := by
    intro i j hi hj
    obtain ⟨a, ha⟩ := hcz _ (hcC i hi)
    obtain ⟨b, hb⟩ := hcz _ (hcC j hj)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]
    exact comm_central (Commute.pow_left (zG_central _) a)
      (Commute.pow_pow_self zG a b) (Commute.pow_left (zG_central _) b)
  exact ⟨by rw [hk1]; exact hcomm (by norm_num) (by norm_num),
    by rw [hk2]; exact hcomm (by norm_num) (by norm_num)⟩

theorem fix_K0 (φ : GM ≃* GM) (hP : ∀ g ∈ P0G, φ g = g) (hN : ∀ n ∈ NP0, φ n = n) :
    φ k1G = k1G ∧ φ k2G = k2G := by
  have hx0 : φ (xG 0) = xG 0 := hP _ (ThreeQRel.v_mem 0)
  have hz : φ zG = zG := hP _ ThreeQRel.x_mem
  have hK := map_K0 φ hx0 hz
  obtain ⟨hc, hk1, hk2⟩ := c_facts
  have hcC : ∀ i < 3, cG i ∈ centralizer {xG 0} := fun i hi =>
    mem_centralizer_singleton_iff.2 (hc i hi)
  set u₁ := actK (restrictK0 φ hK ⟨k1G, k1_mem⟩) with hu₁
  set u₂ := actK (restrictK0 φ hK ⟨k2G, k2_mem⟩) with hu₂
  obtain ⟨sw0, sw1, sw4, s1c, s2c, s12c⟩ := sK_words
  have hrel : ∀ w : List ℕ, evW sK1 sK2 w = 1 → evW u₁ u₂ w = 1 := by
    intro w hw
    have h1 : actK (⟨1, one_mem _⟩ : K0G) = 1 := map_one actK
    have := evW_fixed φ hz hK 1 (one_mem _) (map_one φ) w (by rw [hw, ← h1])
    rwa [h1] at this
  have hu1 : u₁ ^ 3 = 1 := by
    have := hrel [0, 0, 0] (by rw [(evW_cube _ _).1, s1c])
    rwa [(evW_cube _ _).1] at this
  have hu2 : u₂ ^ 3 = 1 := by
    have := hrel [1, 1, 1] (by rw [(evW_cube _ _).2, s2c])
    rwa [(evW_cube _ _).2] at this
  have hu12 : (u₁ * u₂) ^ 5 = 1 := by
    have := hrel [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (by rw [evW_five, s12c])
    rwa [evW_five] at this
  have hw0 : evW u₁ u₂ Wy0 = sY 0 := by
    have := evW_fixed φ hz hK (yG 0) (yG_mem_K0 (by norm_num)) (hP _ (yG_mem_P0 (by norm_num)))
      Wy0 (by rw [sw0, actK_yG (by norm_num)])
    rwa [actK_yG (by norm_num)] at this
  have hw1 : evW u₁ u₂ Wy1 = sY 1 := by
    have := evW_fixed φ hz hK (yG 1) (yG_mem_K0 (by norm_num)) (hP _ (yG_mem_P0 (by norm_num)))
      Wy1 (by rw [sw1, actK_yG (by norm_num)])
    rwa [actK_yG (by norm_num)] at this
  have hw4 : evW u₁ u₂ Wt4 = s4 := by
    have := evW_fixed φ hz hK t4G t4G_mem_K0 (hN _ t4G_mem_NP0) Wt4 (by rw [sw4, actK_t4])
    rwa [actK_t4] at this
  obtain ⟨hu1', hu2'⟩ := a6_rigid u₁ u₂ hu1 hu2 hu12 hw0 hw1 hw4
  exact fix_K0_end φ hx0 hz hK hu1' hu2'

theorem aut_fix_z_inner : AutFixZInner := by
  intro β hβz
  have hcard : Nat.card (P0G.map β.toMonoidHom) = 3 ^ (Nat.card GM).factorization 3 := by
    rw [card_map_of_injective β.injective, relG.card_threeQ, factorization_card_GM]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM (Sylow.ofCard _ hcard) P0Syl
  have hgP : ∀ x ∈ P0G, g * β x * g⁻¹ ∈ P0G := by
    intro x hx
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨β x, ⟨x, hx, rfl⟩, rfl⟩
  set β₁ : GM ≃* GM := β.trans (MulAut.conj g) with hβ₁
  have h₁ : ∀ x, β₁ x = g * β x * g⁻¹ := fun x => rfl
  have h₁z : β₁ zG = zG := by rw [h₁, hβz, mul_assoc, zG_central, ← mul_assoc, mul_inv_cancel,
    one_mul]
  have h₁P : ∀ x ∈ P0G, β₁ x ∈ P0G := fun x hx => by rw [h₁]; exact hgP x hx
  obtain ⟨w, hw, hwc⟩ := exists_word_coord β₁ h₁z h₁P
  set β₂ : GM ≃* GM := β₁.trans (MulAut.conj (wordN w)) with hβ₂
  have h₂ : ∀ x, β₂ x = wordN w * β₁ x * (wordN w)⁻¹ := fun x => rfl
  have h₂z : β₂ zG = zG := by rw [h₂, h₁z, mul_assoc, zG_central, ← mul_assoc, mul_inv_cancel,
    one_mul]
  obtain ⟨p, hp, hpfix⟩ := exists_P0_fix β₂ h₂z (fun x hx => by rw [h₂]; exact (hwc x hx).1)
    (fun x hx => by rw [h₂]; exact (hwc x hx).2)
  set β₃ : GM ≃* GM := β₂.trans (MulAut.conj p) with hβ₃
  have h₃ : ∀ x, β₃ x = p * β₂ x * p⁻¹ := fun x => rfl
  have h₃P : ∀ x ∈ P0G, β₃ x = x := fun x hx => by rw [h₃]; exact hpfix x hx
  have h₃N := fix_NP0 β₃ h₃P
  obtain ⟨h₃k1, h₃k2⟩ := fix_K0 β₃ h₃P h₃N
  have h₃Y : ∀ y ∈ ySet, β₃ y = y := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h₃P _ (ThreeQRel.v_mem 0)
    · exact h₃P _ (ThreeQRel.v_mem 1)
    · exact h₃P _ (ThreeQRel.v_mem 2)
    · exact h₃P _ (ThreeQRel.v_mem 3)
    · have e : (⟨eM (yRegs.getD 4 0), eM_mem _⟩ : GM) = zG := Subtype.ext zM_eq
      exact (congrArg β₃ e).trans ((h₃P _ ThreeQRel.x_mem).trans e.symm)
    · exact h₃N _ (nG_mem_NP0 (k := 0) (by norm_num))
    · exact h₃N _ (nG_mem_NP0 (k := 1) (by norm_num))
    · exact h₃k1
    · exact h₃k2
  have hid := eq_id_of_fix_Y β₃ h₃Y
  refine ⟨(p * wordN w * g)⁻¹, fun x => ?_⟩
  have hx := hid x
  rw [h₃, h₂, h₁] at hx
  calc β x = (p * wordN w * g)⁻¹ * (p * (wordN w * (g * β x * g⁻¹) * (wordN w)⁻¹) * p⁻¹) *
        (p * wordN w * g) := by group
    _ = (p * wordN w * g)⁻¹ * x * ((p * wordN w * g)⁻¹)⁻¹ := by rw [hx, inv_inv]

end CFSG.RankThree.Native.ONTriple
