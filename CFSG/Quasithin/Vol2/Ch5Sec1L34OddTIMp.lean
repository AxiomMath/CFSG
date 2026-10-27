module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddTI
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddTIOut
public import CFSG.Quasithin.Background.B216Quotient

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_eq_of_isSylowTwoOf_normal {H N S : Subgroup G} (hHN :
    H ≤ Subgroup.normalizer (N : Set G)) (hS : IsSylowTwoOf S N) {g : G} (hg : g ∈ H) :
    ∃ c ∈ N, ∃ b ∈ Subgroup.normalizer (S : Set G), g = c * b := by
  have hcN : B6.conjSub g N = N := B6.conjSub_eq_self (hHN hg)
  have hS' : IsSylowTwoOf (B6.conjSub g S) N := by
    have := B6.isSylowTwoOf_conjSub hS g
    rwa [hcN] at this
  obtain ⟨n, hn, hnS⟩ := B6.isSylowTwoOf_exists_conj hS hS'
  refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have : B6.conjSub (n⁻¹ * g) S = S := by
    rw [B6.conjSub_mul, hnS, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  exact this

@[expose] def IntMod.valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem fix_of_card_four {V : Type*} [CommGroup V] {U : Subgroup V} (hU4 : Nat.card U = 4)
    [Finite U] {g : MulAut V} (hgU : U.map g.toMonoidHom = U) (hg : Nat.Coprime (orderOf g) 6)
    {u : V} (hu : u ∈ U) : g u = u := by
  have hiff : ∀ a : V, a ∈ U ↔ g a ∈ U := by
    intro a
    constructor
    · intro ha
      rw [← hgU]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← hgU] at ha
      obtain ⟨b, hb, hba⟩ := ha
      have : b = a := g.injective hba
      rwa [← this]
  let σ : Equiv.Perm ↥U := g.toEquiv.subtypeEquiv hiff
  have hσpow : ∀ k : ℕ, ∀ x : ↥U, ((σ ^ k) x : V) = (g ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, MulAut.mul_apply, ih (σ x)]
      rfl
  have h1 : orderOf σ ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    ext x
    rw [hσpow, pow_orderOf_eq_one, MulAut.one_apply]
    rfl
  have h2 : orderOf σ ∣ 24 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, hU4] at this
  have hc : Nat.Coprime (orderOf g) 24 := by
    have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3
      (Nat.Coprime.coprime_dvd_right (by norm_num) hg))
      (Nat.Coprime.coprime_dvd_right (by norm_num) hg)
  have hσ1 : σ = 1 := orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2)
  have := hσpow 1 ⟨u, hu⟩
  rw [hσ1, one_pow, pow_one] at this
  exact this.symm

end General

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem K_le_centralizer_W (h5114 : Stmt5_1_14_first) :
    oTwoUpper H ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (Subgroup.normalizer (oTwoUpper H : Set G)) :
        Set G) := by
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
  have hW : conjClosure (quasithinOmegaOneCenter T) (Subgroup.normalizer (oTwoUpper H : Set G)) ≤
      Subgroup.centralizer (oTwoUpper H : Set G) := by
    refine conjClosure_le fun m hm z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : m⁻¹ * k * m ∈ oTwoUpper H := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) k).mp hk
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hZC hz) _ (oTwoUpper_le H hk')
    calc k * (m * z * m⁻¹) = m * ((m⁻¹ * k * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * k * m)) * m⁻¹ := by rw [hc]
      _ = m * z * m⁻¹ * k := by group
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hW hw) k hk).symm

theorem autOn_W (h5114 : Stmt5_1_14_first) :
    Group.IsSolvable ↥(autOn (Subgroup.normalizer (oTwoUpper H : Set G))
        (conjClosure (quasithinOmegaOneCenter T) (Subgroup.normalizer (oTwoUpper H : Set G)))) ∧
      ¬ 9 ∣ Nat.card ↥(autOn (Subgroup.normalizer (oTwoUpper H : Set G))
        (conjClosure (quasithinOmegaOneCenter T) (Subgroup.normalizer (oTwoUpper H : Set G)))) := by
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  set W := conjClosure (quasithinOmegaOneCenter T) Mp with hW
  have hMW : Mp ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ Mp
  let α : ↥Mp →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hMW)
  have hrange : α.range = autOn Mp W := by
    ext φ
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨Subgroup.inclusion hMW m, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hα : ∀ k (hk : k ∈ oTwoUpper H), α ⟨k, Subgroup.le_normalizer hk⟩ = 1 := by
    intro k hk
    ext w
    show (Subgroup.normalizerMonoidHom W (Subgroup.inclusion le_rfl
      (Subgroup.inclusion hMW ⟨k, Subgroup.le_normalizer hk⟩)) w : G) = w
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp (s.K_le_centralizer_W h5114 hk) w w.2
    simp only [Subgroup.coe_inclusion]
    rw [← this, mul_inv_cancel_right]
  rw [← hrange]
  exact s.hyp.isSolvable_range_and_not_nine_dvd s.solvable s.three α hα

theorem exists_W₀ (hI : L2OddInnerFact) (hF : L2TorusFact) (h5114 : Stmt5_1_14_first) :
    ∃ W₀ : Subgroup G, W₀ ≤ T ∧ IsElemAbelian 2 W₀ ∧
      Subgroup.normalizer (oTwoUpper H : Set G) ≤ Subgroup.normalizer (W₀ : Set G) ∧
      quasithinOmegaOneCenter T ⊓ V ≤ W₀ ∧
      thompsonJ T ≤ T ⊓ Subgroup.centralizer (W₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  set W := conjClosure (quasithinOmegaOneCenter T) Mp with hWdef
  have hTMp : T ≤ Mp := s.hyp.T_le_Mp
  have hTsyl : IsSylowTwoOf T Mp := hh.isSylowTwoOf hTMp
  obtain ⟨hsolv, h9⟩ := s.autOn_W h5114
  obtain ⟨hU, hred, hcase, -, -⟩ :=
    B2_16_of_quot (s.hyp.charTwo_Mp h5114) hsolv hTsyl hWdef
  have hWT : W ≤ T :=
    (le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1 (isPGroup_of_isElemAbelian hU)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hZ₁W : quasithinOmegaOneCenter T ⊓ V ≤ W := inf_le_left.trans (le_conjClosure _ _)
  rcases hcase with ⟨hJ, -⟩ | ⟨-, I, hsylJ, hJI, hcomm, hindep, hnat, htop, -, -, hperm⟩
  · exact ⟨W, hWT, hU, le_normalizer_conjClosure _ Mp, hZ₁W, le_inf hJT hJ⟩
  set X := autI hU (thompsonJ Mp) with hXdef
  have hMW : Mp ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ Mp
  set W₀ := (fixV X).map (IntMod.valHom hU) with hW₀def
  have hmemW₀ : ∀ x : IntMod W hU, x ∈ fixV X → x.val ∈ W₀ := fun x hx => ⟨x, hx, rfl⟩
  have hW₀W : W₀ ≤ W := by
    rintro _ ⟨x, -, rfl⟩
    exact x.val_mem
  have hJN : Mp ≤ Subgroup.normalizer (thompsonJ Mp : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ Mp)
  have hJMp : thompsonJ Mp ≤ Mp := iSup₂_le fun _ hA => hA.1
  have hfixg : ∀ (m : Subgroup.normalizer (W : Set G)), (m : G) ∈ Mp →
      ∀ x ∈ fixV X, convI hU m x ∈ fixV X := by
    intro m hm x hx y hy
    obtain ⟨j, hj, rfl⟩ := (mem_autI hU).1 hy
    have hj' : (m : G)⁻¹ * j * m ∈ thompsonJ Mp := by
      have := (Subgroup.mem_normalizer_iff.mp (hJN (inv_mem hm)) j).mp hj
      simpa using this
    have hjN : (m : G)⁻¹ * j * m ∈ Subgroup.normalizer (W : Set G) :=
      hMW (hJMp hj')
    have h1 : convI hU m⁻¹ * convI hU j * convI hU m ∈ X := by
      rw [← map_mul, ← map_mul]
      exact convI_mem_autI hU (by simpa using hj') (by simpa using hjN)
    have h2 := hx _ h1
    simp only [MulAut.mul_apply] at h2
    have hmm : ∀ y, convI hU m (convI hU m⁻¹ y) = y := fun y => by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    calc convI hU j (convI hU m x) =
          convI hU m (convI hU m⁻¹ (convI hU j (convI hU m x))) := (hmm _).symm
      _ = convI hU m x := by rw [h2]
  refine ⟨W₀, hW₀W.trans hWT, ⟨⟨⟨fun a b => Subtype.ext
      (F7.isElemAbelian_comm hU (hW₀W a.2) (hW₀W b.2))⟩⟩, fun x hx => hU.2 x (hW₀W hx)⟩,
    ?_, ?_, ?_⟩
  ·
    intro m hm
    apply mem_normalizer_of_forall_conj_mem'
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hmemW₀ _ (hfixg ⟨m, hMW hm⟩ hm x hx)
    rwa [convI_apply_val] at h1
  ·
    have h9' : ¬ 9 ∣ Nat.card ↥(autI hU Mp) := h9
    have hXle : X ≤ autI hU Mp := autI_mono hU hJMp
    have hcard6 : ∀ L ∈ I, Nat.card ↥L = 6 := by
      intro L hL
      obtain ⟨e, -, -⟩ := hnat L hL
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
      norm_num
    have hI1 : ∀ L₁ ∈ I, ∀ L₂ ∈ I, L₁ = L₂ := by
      intro L₁ hL₁ L₂ hL₂
      by_contra hne
      have hL₁X : L₁ ≤ X := by rw [hJI]; exact le_iSup₂_of_le L₁ hL₁ le_rfl
      have hL₂X : L₂ ≤ X := by rw [hJI]; exact le_iSup₂_of_le L₂ hL₂ le_rfl
      have hbot : L₁ ⊓ L₂ = ⊥ := by
        refine le_bot_iff.mp ((inf_le_inf_left L₁ ?_).trans (hindep L₁ hL₁).le)
        exact le_iSup₂_of_le L₂ hL₂ (le_iSup_of_le (Ne.symm hne) le_rfl)
      let φ := L₁.subtype.noncommCoprod L₂.subtype fun a b =>
        hcomm L₁ hL₁ L₂ hL₂ hne a a.2 b b.2
      have hφi : Function.Injective φ := by
        rw [injective_iff_map_eq_one]
        rintro ⟨a, b⟩ hab
        have hab' : (a : MulAut (IntMod W hU)) * b = 1 := hab
        have ha : (a : MulAut (IntMod W hU)) = (b : MulAut (IntMod W hU))⁻¹ :=
          eq_inv_of_mul_eq_one_left hab'
        have hmem : (a : MulAut (IntMod W hU)) ∈ L₁ ⊓ L₂ := ⟨a.2, ha ▸ L₂.inv_mem b.2⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        have hb : (b : MulAut (IntMod W hU)) = 1 := by
          rw [hmem, one_mul] at hab'
          exact hab'
        exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
      have hφle : φ.range ≤ autI hU Mp := by
        rintro _ ⟨⟨a, b⟩, rfl⟩
        exact (autI hU Mp).mul_mem (hXle (hL₁X a.2)) (hXle (hL₂X b.2))
      have h36 : Nat.card ↥φ.range = 36 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_prod, hcard6 L₁ hL₁,
          hcard6 L₂ hL₂]
      apply h9'
      have := Subgroup.card_dvd_of_le hφle
      rw [h36] at this
      exact (by norm_num : (9 : ℕ) ∣ 36).trans this
    obtain ⟨c⟩ := s.nonempty_coord
    have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
    have hDMp : D ≤ Mp := s.D_le_normalizer
    have hfixD : ∀ d (hd : d ∈ D), ∀ u ∈ ⨆ L ∈ I, commV L, convI hU ⟨d, hMW (hDMp hd)⟩ u = u := by
      intro d hd u hu
      set g := convI hU ⟨d, hMW (hDMp hd)⟩ with hg
      have hgMp : g ∈ autI hU Mp := convI_mem_autI hU (hDMp hd) _
      have hgord : Nat.Coprime (orderOf g) 6 := by
        have h1 : orderOf g ∣ orderOf d := by
          have := orderOf_map_dvd (convI hU) ⟨d, hMW (hDMp hd)⟩
          rwa [Subgroup.orderOf_mk] at this
        have h2 : orderOf d ∣ 2 ^ n - 1 := by
          rw [← (s.hyp.hyp.toHyp5_0_1.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).2,
            ← Subgroup.orderOf_mk d hd]
          exact orderOf_dvd_natCard _
        have h6 : Nat.Coprime (2 ^ n - 1) 6 := by
          have h3 : Nat.Coprime (2 ^ n - 1) 3 :=
            Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
              s.not_three_dvd)
          have h2' : Nat.Coprime (2 ^ n - 1) 2 := by
            rw [Nat.coprime_two_right]
            have := Nat.one_le_two_pow (n := n)
            rcases Nat.even_or_odd (2 ^ n - 1) with he | ho
            · exfalso
              obtain ⟨r, hr⟩ := he
              have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := s.one_le_n; omega)
              omega
            · exact ho
          exact Nat.Coprime.mul_right h2' h3
        exact Nat.Coprime.coprime_dvd_left (h1.trans h2) h6
      have hle : (⨆ L ∈ I, commV L) ≤ fixV (Subgroup.zpowers g) := by
        refine iSup₂_le fun L hL => ?_
        obtain ⟨hgL, hmap⟩ := hperm g hgMp L hL
        have hgLL : B1.conjAut g L = L := hI1 _ hgL _ hL
        rw [hgLL] at hmap
        obtain ⟨-, φ, -⟩ := hnat L hL
        have hU4 : Nat.card ↥(commV L) = 4 := by
          rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
            Nat.card_zmod, Nat.card_fin]
          norm_num
        intro v hv x hx
        have hgv : g ∈ MulAction.stabilizer (MulAut (IntMod W hU)) v :=
          fix_of_card_four hU4 hmap hgord hv
        exact (Subgroup.zpowers_le.mpr hgv) hx
      exact hle hu g (Subgroup.mem_zpowers g)
    intro z hz
    obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : c.K, μ ≠ 0 ∧ μ ^ 2 ≠ 1 := by
      rcases CFSG.Quasithin.SL2Model.card_two_or_exists_sq_ne_one (F := c.K) with h2 | h
      · exfalso
        rw [c.card] at h2
        have hn2 : 2 ≤ n := hh.two_le
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      · exact h
    obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c hμ0
    obtain ⟨A, hA0, hA⟩ := s.exists_mat_of_normalizer hI c d (hDL hdD) (s.D_le_normalizer_Z₁ hI hdD)
    have hA11 : (A : Matrix (Fin 2) (Fin 2) c.K) 1 1 = μ := by
      have h1 := hd ![0, 1]
      rw [hA, mulVec_one_of_lower _ hA0] at h1
      simpa using h1
    set lam := (A : Matrix (Fin 2) (Fin 2) c.K) 0 0 with hlam
    have hlam1 : lam - 1 ≠ 0 := by
      intro h0
      have h1 : lam = 1 := by linear_combination h0
      have h2 := mul_eq_one_of_lower A hA0
      rw [← hlam, h1, one_mul, hA11] at h2
      exact hμ1 (by rw [h2, one_pow])
    obtain ⟨v', hv'⟩ := c.ε_bij.2 ![(lam - 1)⁻¹ * c.ε ⟨z, hz.2⟩ 0, 0]
    have hv'Z : (v' : G) ∈ quasithinOmegaOneCenter T :=
      (s.mem_Z_iff hI c v').mpr (by rw [hv']; rfl)
    have hdv' : (d : G) * v' * (d : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp d.2 v').mp v'.2
    have hε_inv : ∀ a b : ↥V, c.ε (a * b⁻¹) = c.ε a - c.ε b := fun a b => by
      have := c.ε_mul (a * b⁻¹) b
      rw [inv_mul_cancel_right] at this
      rw [this]
      abel
    have hkey : (d : G) * v' * (d : G)⁻¹ * (v' : G)⁻¹ = z := by
      have h1 : c.ε ⟨(d : G) * v' * (d : G)⁻¹, hdv'⟩ = c.act d (c.ε v') := by
        rw [c.act_ε]
        exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
      have h2 : c.ε (⟨(d : G) * v' * (d : G)⁻¹, hdv'⟩ * v'⁻¹) = c.ε ⟨z, hz.2⟩ := by
        rw [hε_inv, h1, hA, hv', s.ε_eq_of_mem_Z₁ hI c (z := ⟨z, hz.2⟩) hz.1]
        funext i
        fin_cases i
        · simp [← hlam]
          field_simp
        · simp [hA0]
      exact congrArg Subtype.val (c.ε_bij.1 h2)
    have hv'W : (v' : G) ∈ W := hZ₁W ⟨hv'Z, v'.2⟩
    set x' : IntMod W hU := IntMod.mk hU ⟨v', hv'W⟩ with hx'
    have hdN : (d : G) ∈ Subgroup.normalizer (W : Set G) := hMW (hDMp hdD)
    set g := convI hU ⟨(d : G), hdN⟩ with hg
    obtain ⟨f, hf, u, hu, hfu⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top x' :
      x' ∈ fixV X ⊔ ⨆ L ∈ I, commV L)
    have hgu : g u = u := hfixD d hdD u hu
    have hgf : g f ∈ fixV X := hfixg ⟨(d : G), hdN⟩ (hDMp hdD) f hf
    have hmem : g x' * x'⁻¹ ∈ fixV X := by
      rw [← hfu, map_mul, hgu]
      have e : g f * u * (f * u)⁻¹ = g f * f⁻¹ := by group
      rw [e]
      exact (fixV X).mul_mem hgf ((fixV X).inv_mem hf)
    have hval : (g x' * x'⁻¹).val = z := by
      rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
      exact hkey
    have := hmemW₀ _ hmem
    rwa [hval] at this
  ·
    refine le_inf hJT fun j hj => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hjN : j ∈ Subgroup.normalizer (W : Set G) := hMW (hTMp (hJT hj))
    have hjX : convI hU ⟨j, hjN⟩ ∈ X := hsylJ.1 (convI_mem_autI hU hj hjN)
    have h1 := hx _ hjX
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    show x.val * j = j * x.val
    calc x.val * j = (j * x.val * j⁻¹) * j := by rw [h2]
      _ = j * x.val := by group

theorem isTISetUnder_Mp (hI : L2OddInnerFact) (hF : L2TorusFact) (h5114 : Stmt5_1_14_first)
    (h517one : A5.Stmt5_1_7_one) :
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) (Subgroup.normalizer (oTwoUpper H : Set G)) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  obtain ⟨W₀, hW₀T, hW₀, hW₀N, hZ₁W₀, hJ⟩ := s.exists_W₀ hI hF h5114
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  have hTMp : T ≤ Mp := s.hyp.T_le_Mp
  have hTsyl : IsSylowTwoOf T Mp := hh.isSylowTwoOf hTMp
  set C := Mp ⊓ Subgroup.centralizer (W₀ : Set G) with hC
  have hMpC : Mp ≤ Subgroup.normalizer (C : Set G) := by
    intro m hm
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨Mp.mul_mem (Mp.mul_mem hm hx.1) (Mp.inv_mem hm),
      (Subgroup.mem_normalizer_iff.mp
        ((hW₀N.trans (normalizer_le_normalizer_centralizer'' W₀)) hm) x).mp hx.2⟩
  have hSsyl : IsSylowTwoOf (T ⊓ C) C := A4.isSylowTwoOf_inf_normal hTsyl inf_le_left hMpC
  have hTC : T ⊓ C = T ⊓ Subgroup.centralizer (W₀ : Set G) := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hTMp]
  have hbaum : baum T = baum (T ⊓ C) := by
    rw [hTC]
    exact baum_eq_baum_centralizer hW₀ hW₀T hJ
  have hNM : Subgroup.normalizer (baum T : Set G) ≤ M :=
    h517one G T L M hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal hh.faithful
      ⟨n, hh.two_le, hh.lie⟩ hh.maxTwoLocal hh.T_le hh.L_le hh.normal
  have hTIM := s.isTISetUnder_M hI
  intro g hg hgN
  obtain ⟨c', hc', b, hb, rfl⟩ := exists_mul_eq_of_isSylowTwoOf_normal hMpC hSsyl hg
  have hbN : b ∈ Subgroup.normalizer (baum T : Set G) := by
    rw [hbaum]
    exact normalizer_le_normalizer_baum _ hb
  have hbM : b ∈ M := hNM hbN
  have hc'N : c' ∈ Subgroup.normalizer (Z₁ : Set G) := by
    apply mem_normalizer_of_forall_conj_mem'
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp hc'.2 z (hZ₁W₀ hz)
    rw [← this, mul_inv_cancel_right]
    exact hz
  by_cases hbZ : b ∈ Subgroup.normalizer (Z₁ : Set G)
  · exact absurd (Subgroup.mul_mem _ hc'N hbZ) hgN
  have hbot := hTIM b hbM hbZ
  have h1 : CFSG.conjugate Z₁ (c' * b) = CFSG.conjugate Z₁ b := by
    show conjSub (c' * b)⁻¹ Z₁ = conjSub b⁻¹ Z₁
    rw [mul_inv_rev, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (inv_mem hc'N)]
  rw [h1]
  exact hbot

end Setup5_1_17Odd

theorem stmt5_1_17_TI_of (hI : L2OddInnerFact) (hF : L2TorusFact) (h5114 : Stmt5_1_14_first)
    (h517one : A5.Stmt5_1_7_one) : Stmt5_1_17_TI :=
  fun _ _ _ _ _ _ _ _ _ _ _ s =>
    s.isTISetUnder_top_of_Mp hI hF h5114 (s.isTISetUnder_Mp hI hF h5114 h517one)

end CFSG.Quasithin.H13
