module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ

public section

namespace CFSG.Quasithin.A7ZK

open CFSG.Quasithin Equiv Equiv.Perm

@[expose] def v56 : G6.PermMod 7 := Multiplicative.ofAdd (Pi.single 5 1 + Pi.single 6 1)

theorem v56_mem : v56 ∈ G6.coreMod 7 := by
  rw [G6.mem_coreMod]
  decide +kernel

theorem v56_apply : ∀ i : Fin 7,
    Multiplicative.toAdd v56 i = if i = 5 ∨ i = 6 then 1 else 0 := by
  decide +kernel

theorem v56_ne_one : v56 ≠ 1 := by
  intro h
  have h1 := v56_apply 5
  rw [h] at h1
  exact absurd h1 (by decide)

theorem permAct_v56 {σ : Perm (Fin 7)} (h : (σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5)) :
    G6.permAct 7 σ v56 = v56 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, v56_apply, v56_apply]
  have key : (σ⁻¹ i = 5 ∨ σ⁻¹ i = 6) ↔ (i = 5 ∨ i = 6) := by
    rw [Perm.inv_eq_iff_eq, Perm.inv_eq_iff_eq]
    rcases h with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · rw [h5, h6]
    · rw [h5, h6, or_comm]
  simp only [key]

theorem p0L_stab56_check :
    A7Std.p0L.all (fun a => decide ((a 5 = 5 ∧ a 6 = 6) ∨ (a 5 = 6 ∧ a 6 = 5))) = true := by
  decide +kernel

theorem p0L_stab56 : ∀ σ ∈ A7Std.p0L, (σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5) := by
  have h := p0L_stab56_check
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem eq_one_or_eq_v56 {v : G6.PermMod 7} (hs : ∑ i, Multiplicative.toAdd v i = 0)
    (h5 : G6.permAct 7 c5p v = v) (ha : G6.permAct 7 A7Std.p0a v = v) : v = 1 ∨ v = v56 := by
  have hc : ∀ i, Multiplicative.toAdd v (c5p⁻¹ i) = Multiplicative.toAdd v i := fun i => by
    rw [← G6.permAct_apply, h5]
  have hp : ∀ i, Multiplicative.toAdd v (A7Std.p0a⁻¹ i) = Multiplicative.toAdd v i := fun i => by
    rw [← G6.permAct_apply, ha]
  have e1 : c5p⁻¹ 1 = 0 := by decide
  have e2 : c5p⁻¹ 2 = 1 := by decide
  have e3 : c5p⁻¹ 3 = 2 := by decide
  have e4 : c5p⁻¹ 4 = 3 := by decide
  have e6 : A7Std.p0a⁻¹ 6 = 5 := by decide
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h6 := hp 6
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e6] at h6
  rw [Fin.sum_univ_seven, ← h6, ← h4, ← h3, ← h2, ← h1] at hs
  have key : ∀ a b : ZMod 2, a + a + a + a + a + b + b = 0 → a = 0 := by decide
  have h0 := key _ _ hs
  have hv1 : Multiplicative.toAdd v 1 = 0 := by rw [← h1]; exact h0
  have hv2 : Multiplicative.toAdd v 2 = 0 := by rw [← h2]; exact hv1
  have hv3 : Multiplicative.toAdd v 3 = 0 := by rw [← h3]; exact hv2
  have hv4 : Multiplicative.toAdd v 4 = 0 := by rw [← h4]; exact hv3
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hb (Multiplicative.toAdd v 5) with h50 | h51
  · left
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    exacts [h0, hv1, hv2, hv3, hv4, h50, h6.symm.trans h50]
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [v56_apply]
    fin_cases i
    exacts [h0, hv1, hv2, hv3, hv4, h51, h6.symm.trans h51]

theorem mem_r0_of_permAct_v56 {σ : alternatingGroup (Fin 7)}
    (h : G6.permAct 7 (σ : Perm (Fin 7)) v56 = v56) {r : alternatingGroup (Fin 7)}
    (hr : r ∈ A7Std.r0) : σ * r * σ⁻¹ ∈ A7Std.r0 := by
  have key : ∀ i : Fin 7, Multiplicative.toAdd v56 ((σ : Perm (Fin 7))⁻¹ i) =
      Multiplicative.toAdd v56 i := fun i => by
    rw [← G6.permAct_apply, h]
  have hv : ∀ j : Fin 7, Multiplicative.toAdd v56 j = 1 → j = 5 ∨ j = 6 := by decide +kernel
  have h5 : (σ : Perm (Fin 7))⁻¹ 5 = 5 ∨ (σ : Perm (Fin 7))⁻¹ 5 = 6 :=
    hv _ ((key 5).trans (by decide +kernel))
  have h6 : (σ : Perm (Fin 7))⁻¹ 6 = 5 ∨ (σ : Perm (Fin 7))⁻¹ 6 = 6 :=
    hv _ ((key 6).trans (by decide +kernel))
  obtain ⟨hr5, hr6⟩ := (A7Std.mem_r0 r).mp hr
  have hfix : ∀ j : Fin 7, j = 5 ∨ j = 6 → (r : Perm (Fin 7)) j = j := by
    rintro j (rfl | rfl)
    · exact hr5
    · exact hr6
  rw [A7Std.mem_r0]
  constructor
  · show (σ : Perm (Fin 7)) ((r : Perm (Fin 7)) ((σ : Perm (Fin 7))⁻¹ 5)) = 5
    rw [hfix _ h5]
    exact Equiv.apply_symm_apply _ _
  · show (σ : Perm (Fin 7)) ((r : Perm (Fin 7)) ((σ : Perm (Fin 7))⁻¹ 6)) = 6
    rw [hfix _ h6]
    exact Equiv.apply_symm_apply _ _

end CFSG.Quasithin.A7ZK

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

@[expose] def Stmt5_1_13_four_nA5_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      ⁅V', thompsonJ T⁆ ≠ ⊥ → n = 2 → IsCommCentralSplit L T V' → IsBarS5 L T V' →
      IsS5ModCh5 L T ⁅V', L⁆ →
      Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆ ≠ 2 ^ 4


section General

variable {G : Type} [Group G] [Finite G]

theorem borelL_le_centralizer_of_s5 {T L V Z : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hT2 : IsPGroup 2 ↥T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ L) L) (hV : IsTwoReducedIn (L ⊔ T) V)
    (hsplit : IsCommCentralSplit L T V) (hS5 : IsS5ModCh5 L T ⁅V, L⁆) (hZV : Z ≤ V)
    (hZT : Z ≤ Subgroup.centralizer (T : Set G)) :
    borelL T L ≤ Subgroup.centralizer (Z : Set G) := by
  have hA5 := isA5ModuleUnder_of_isS5ModCh5 hS5 hL hT2 hTL
  have hVc := hV.2.2.1.1
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVc.is_comm.comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hVL : ⁅V, L⁆ ≤ V := A7ZK.commutator_le_left_of_le_normalizer (le_sup_left.trans hV.2.1)
  have hUN : ⁅V, L⁆ ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hxc : ∀ c ∈ V, x * c * x⁻¹ = c := fun c hc => by
      rw [hcomm x (hVL hx) c hc, mul_inv_cancel_right]
    constructor
    · intro hc
      rw [hxc c hc.1]
      exact hc
    · intro hc
      have h1 : x * c * x⁻¹ ∈ V := hc.1
      have h2 : c ∈ V := by
        have h3 := V.mul_mem (V.mul_mem (V.inv_mem (hVL hx)) h1) (hVL hx)
        simpa [mul_assoc] using h3
      rw [hxc c h2] at hc
      exact hc
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzV : z ∈ ((⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)) :
      Subgroup G) : Set G) := by
    rw [hsplit.2]
    exact hZV hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at hzV
  obtain ⟨a, ha', c, hc', hac⟩ := hzV
  have ha : a ∈ ⁅V, L⁆ := ha'
  have hc : c ∈ V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) := hc'
  have hzac : z = a * c := hac.symm
  subst hzac
  have hcLT := (Subgroup.mem_inf.mp hc).2
  have haT : ∀ s ∈ T ⊓ L, s * a * s⁻¹ = a := by
    intro s hs
    have hsT : s ∈ T := (Subgroup.mem_inf.mp hs).1
    have h1 : s * (a * c) = (a * c) * s := Subgroup.mem_centralizer_iff.mp (hZT hz) s hsT
    have h2 : s * c = c * s :=
      Subgroup.mem_centralizer_iff.mp hcLT s (Subgroup.mem_sup_right hsT)
    calc s * a * s⁻¹ = s * (a * c) * s⁻¹ * (s * c * s⁻¹)⁻¹ := by group
      _ = a := by rw [h1, h2]; group
  have hdL : d ∈ L := (Subgroup.mem_inf.mp hd).1
  have hdN : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hd).2
  have hda : d * a * d⁻¹ = a :=
    A7.IsA5ModuleUnder.conj_eq_of_fixed hA5 (hT2.to_le inf_le_left) hsyl.2.2 hdL hdN ha haT
  have hdc : d * c = c * d :=
    Subgroup.mem_centralizer_iff.mp hcLT d (Subgroup.mem_sup_left hdL)
  calc a * c * d = a * (c * d) := by group
    _ = (d * a * d⁻¹) * (d * c) := by rw [hda, hdc]
    _ = d * (a * c) := by group

theorem mem_of_conj_mem_modO2Image {K Kh : Subgroup G} (hKKh : K ≤ Kh) (hK : ⁅K, K⁆ = K)
    (hON : pCoreOf 2 Kh ≤ Subgroup.normalizer (K : Set G)) {d : G} (hd : d ∈ Kh)
    (hdK : ∀ k : ↥Kh, (QuotientGroup.mk k : O2Q Kh) ∈ modO2Image Kh K →
      (QuotientGroup.mk (⟨d, hd⟩ * k * (⟨d, hd⟩ : ↥Kh)⁻¹) : O2Q Kh) ∈ modO2Image Kh K)
    {k : G} (hk : k ∈ K) : d * k * d⁻¹ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have hO : K = oTwoUpper (K ⊔ pCoreOf 2 Kh) :=
    eq_oTwoUpper_of_pow_mem le_sup_left
      (InternalSec.two_of_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kh) hON)
      (B1Red.oTwoUpper_eq_of_perfect hperf).symm
  set C := K.map (MulAut.conj d).toMonoidHom with hC
  have hCY : C ≤ K ⊔ pCoreOf 2 Kh := by
    rintro x ⟨k', hk', rfl⟩
    have hk'Kh : k' ∈ Kh := hKKh hk'
    have hm : (QuotientGroup.mk (⟨k', hk'Kh⟩ : ↥Kh) : O2Q Kh) ∈ modO2Image Kh K :=
      ⟨⟨k', hk'Kh⟩, Subgroup.mem_subgroupOf.mpr hk', rfl⟩
    obtain ⟨k₁, hk₁, hk₁e⟩ := hdK _ hm
    have h1 := QuotientGroup.eq.mp hk₁e
    have h2 : ((k₁⁻¹ * (⟨d, hd⟩ * ⟨k', hk'Kh⟩ * (⟨d, hd⟩ : ↥Kh)⁻¹) : ↥Kh) : G) ∈ pCoreOf 2 Kh := by
      rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
      exact ⟨_, h1, rfl⟩
    have h3 : (MulAut.conj d).toMonoidHom k' =
        (k₁ : G) * ((k₁⁻¹ * (⟨d, hd⟩ * ⟨k', hk'Kh⟩ * (⟨d, hd⟩ : ↥Kh)⁻¹) : ↥Kh) : G) := by
      simp [mul_assoc]
    rw [h3]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk₁) h2
  have hCperf : Group.IsPerfect ↥C := by
    rw [Subgroup.isPerfect_iff, hC, ← Subgroup.map_commutator, hK]
  have hCK : C ≤ K := by
    rw [hO]
    exact B1Red.perfect_le_oTwoUpper' hCY hCperf
  exact hCK ⟨k, hk, rfl⟩

end General

theorem stmt5_1_13_four_nA5_of (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51)
    (h4 : Stmt5_1_13_four_nA5_four) : Stmt5_1_13_four_nA5 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hJV hn2 hsplit hS5
    hmodS5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have h4' := h4 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hJV hn2 hsplit
    hS5 hmodS5
  obtain ⟨e, pk⟩ := m.exists_a7Pack h5171 h51 hc5 hmax hZ hA
  have h64 := pk.card.resolve_left h4'
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTLT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTLT le_sup_left (sup_le Subgroup.le_normalizer hTL)
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).2.1
  have hBZ := borelL_le_centralizer_of_s5 h.maximal.1.2.1.2.1 h.sylow.1 hTL hsyl
    hV'.isTwoReducedIn hsplit hmodS5 hZV' hZT
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -, -⟩ := ty
  obtain ⟨β, hβ⟩ := A7ZK.exists_coreMod_equiv e pk.le_normalizer pk.elemAbelian pk.pCoreOf_le
    pk.irr pk.not_le_centralizer h64
  set u := β.symm ⟨A7ZK.v56, A7ZK.v56_mem⟩ with hu
  have hβu : (β u : G6.PermMod 7) = A7ZK.v56 := by
    rw [hu, MulEquiv.apply_symm_apply]
  have hu1 : u ≠ 1 := by
    intro h1
    apply A7ZK.v56_ne_one
    rewrite [← hβu, h1, map_one]
    rfl
  have himK : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H →
      e (QuotientGroup.mk y) ∈ A7Std.r0 := fun y hy => by
    rw [← pk.r0]
    exact ⟨QuotientGroup.mk y, ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  have himT : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T →
      e (QuotientGroup.mk y) ∈ A7Std.p0 := fun y hy => by
    rw [← pk.p0]
    exact ⟨QuotientGroup.mk y, ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩, rfl⟩, rfl⟩
  have hfixσ : ∀ (y : ↥(conjClosure Kh₁ T)),
      G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7))
        A7ZK.v56 = A7ZK.v56 → A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    apply β.injective
    apply Subtype.ext
    rw [hβ y u, hβu, hy]
  have hfixK : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H →
      A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    refine hfixσ y (A7ZK.permAct_v56 (Or.inl ?_))
    exact (A7Std.mem_r0 _).mp (himK y hy)
  have hfixT : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T →
      A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    refine hfixσ y (A7ZK.permAct_v56 ?_)
    exact A7ZK.p0L_stab56 _ (A7Std.mem_p0.mp (himT y hy))
  have hyK : ∃ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H ∧
      e (QuotientGroup.mk y) = A7ZK.c5 := by
    have h1 : A7ZK.c5 ∈ (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom :=
      pk.r0 ▸ A7ZK.c5_mem
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := h1
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hq⟩
  obtain ⟨y5, hy5K, hy5⟩ := hyK
  have hyT : ∀ x ∈ A7Std.p0, ∃ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T ∧
      e (QuotientGroup.mk y) = x := by
    intro x hx
    rw [← pk.p0] at hx
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := hx
    exact ⟨y, (Subgroup.mem_subgroupOf.mp hy).1, hq⟩
  obtain ⟨ya, hyaT, hya⟩ := hyT _ A7ZK.eval7_p0aWord_mem
  have hya' : ((e (QuotientGroup.mk ya) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      A7Std.p0a := by
    rw [hya]
    exact Equiv.ext A7ZK.eval7_p0aWord
  have hone : ∀ u' : ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆, A7ZK.conjAut pk.le_normalizer y5 u' = u' →
      A7ZK.conjAut pk.le_normalizer ya u' = u' → u' = 1 ∨ u' = u := by
    intro u' h5 ha
    have k5 := hβ y5 u'
    have ka := hβ ya u'
    rw [h5, hy5] at k5
    rw [ha, hya'] at ka
    rcases A7ZK.eq_one_or_eq_v56 (G6.mem_coreMod.mp (β u').2) k5.symm ka.symm with
      h1 | h1
    · left
      apply β.injective
      rw [map_one]
      exact Subtype.ext h1
    · right
      apply β.injective
      exact Subtype.ext (h1.trans hβu.symm)
  have hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u := by
    intro t ht
    have htU : t * (u : G) * t⁻¹ ∈ ⁅conjClosure (quasithinOmegaOneCenter T)
        (conjClosure Kh₁ T ⊔ T), conjClosure Kh₁ T⁆ :=
      (Subgroup.mem_normalizer_iff.mp (pk.T_le_normalizer ht) u).mp u.2
    have hc : ∀ y : ↥(conjClosure Kh₁ T), ∀ hy' : (t⁻¹ * y * t : G) ∈ conjClosure Kh₁ T,
        A7ZK.conjAut pk.le_normalizer ⟨t⁻¹ * y * t, hy'⟩ u = u →
        A7ZK.conjAut pk.le_normalizer y ⟨_, htU⟩ = ⟨_, htU⟩ := by
      intro y hy' hfix
      have h1 : (t⁻¹ * y * t) * (u : G) * (t⁻¹ * y * t)⁻¹ = u := congrArg Subtype.val hfix
      apply Subtype.ext
      rw [A7ZK.coe_conjAut]
      show (y : G) * (t * u * t⁻¹) * (y : G)⁻¹ = t * u * t⁻¹
      calc (y : G) * (t * u * t⁻¹) * (y : G)⁻¹ =
            t * ((t⁻¹ * y * t) * u * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
        _ = t * u * t⁻¹ := by rw [h1]
    have hTK' : ∀ y : G, y ∈ conjClosure Kh₁ T → t⁻¹ * y * t ∈ conjClosure Kh₁ T := fun y hy => by
      have h1 := (Subgroup.mem_normalizer_iff.mp (pk.T_le (T.inv_mem ht)) y).mp hy
      simpa using h1
    have h5 : A7ZK.conjAut pk.le_normalizer y5 ⟨_, htU⟩ = ⟨_, htU⟩ := by
      refine hc y5 (hTK' _ y5.2) (hfixK _ ?_)
      have h1 := (Subgroup.mem_normalizer_iff.mp (pk.T_le_K (T.inv_mem ht)) _).mp hy5K
      simpa using h1
    have ha : A7ZK.conjAut pk.le_normalizer ya ⟨_, htU⟩ = ⟨_, htU⟩ := by
      refine hc ya (hTK' _ ya.2) (hfixT _ ?_)
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hyaT) ht
    rcases hone _ h5 ha with h1 | h1
    · exfalso
      apply hu1
      have h2 : t * (u : G) * t⁻¹ = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      have h3 : (u : G) = t⁻¹ * (t * u * t⁻¹) * t := by group
      rw [h3, h2]
      simp
    · exact congrArg Subtype.val h1
  have huZ : (u : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨pk.le_T (pk.U_le u.2),
      Subgroup.mem_centralizer_iff.mpr fun t ht => by
        calc t * (u : G) = t * u * t⁻¹ * t := by group
          _ = u * t := by rw [hTu t ht],
      pk.elemAbelian.2 _ u.2⟩
  have hON : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    refine le_trans ?_ ((F7.isSylowTwoOf_pCoreOf_le pk.sylow).trans pk.T_le_K)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (pk.T_le.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hconj : ∀ d ∈ D₃, ∀ k ∈ oTwoUpper H, d * k * d⁻¹ ∈ oTwoUpper H := by
    intro d hd k hk
    have hdKh : d ∈ conjClosure Kh₁ T := (hD₃ hd).2
    have hdZ := hBZ (m.nota.2.1.1 (hD₃ hd).1)
    have hdu : A7ZK.conjAut pk.le_normalizer ⟨d, hdKh⟩ u = u := by
      apply Subtype.ext
      rw [A7ZK.coe_conjAut]
      have h1 : (u : G) * d = d * u := Subgroup.mem_centralizer_iff.mp hdZ _ huZ
      show d * (u : G) * d⁻¹ = u
      rw [← h1, mul_inv_cancel_right]
    have hσ : G6.permAct 7 ((e (QuotientGroup.mk ⟨d, hdKh⟩) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) A7ZK.v56 = A7ZK.v56 := by
      have h1 := hβ ⟨d, hdKh⟩ u
      rw [hdu, hβu] at h1
      exact h1.symm
    refine mem_of_conj_mem_modO2Image pk.K_le
      (by rw [m.closure]; exact A3.conjClosure_perfect m.comp.2.1) hON hdKh ?_ hk
    intro k' hk'
    have hr : e (QuotientGroup.mk k') ∈ A7Std.r0 := by
      rw [← pk.r0]
      exact ⟨_, hk', rfl⟩
    have h1 := A7ZK.mem_r0_of_permAct_v56 hσ hr
    rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← pk.r0] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    rw [show x = _ from e.injective hxe] at hx
    exact hx
  apply hD₃K
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact hconj d hd k
  · intro hk
    have h1 := hconj d⁻¹ (D₃.inv_mem hd) _ hk
    simpa [mul_assoc] using h1

end CFSG.Quasithin.H13
