module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11S
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {d u₁ z : G}

namespace Data611

variable (D : Data611 G T M L V d u₁ z)
include D

noncomputable abbrev line (p q : Fin 4 → ZMod 2) : Subgroup G :=
  @kapLineCh611 G _ (uCh611 T L V) D.isMulCommutative D.basis D.basis_sq p q

theorem line_eq_of_lineEq {p q p' q' : Fin 4 → ZMod 2} (h : LineEqCh611 p q p' q') :
    D.line p q = D.line p' q' := by
  have := D.isMulCommutative
  exact kapLineCh611_congr h.1 h.2

theorem lineEq_of_line_eq {p q p' q' : Fin 4 → ZMod 2} (h : D.line p q = D.line p' q') :
    LineEqCh611 p q p' q' := by
  have key : ∀ {p q p' q' : Fin 4 → ZMod 2}, D.line p q = D.line p' q' →
      LineLeCh611 p q p' q' := by
    intro p q p' q' h α β
    have hmem : D.kv (α • p + β • q) ∈ D.line p' q' := h ▸ ⟨α, β, rfl⟩
    obtain ⟨α', β', he⟩ := hmem
    exact ⟨α', β', (D.kv_injective he).symm⟩
  exact ⟨key h, key h.symm⟩

theorem map_line {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A)
    (p q : Fin 4 → ZMod 2) :
    (D.line p q).map (MulAut.conj g).toMonoidHom = D.line (A.mulVec p) (A.mulVec q) := by
  have := D.isMulCommutative
  exact IsMatCh611.map_kapLine h p q

theorem line_ZS : D.line ![0, 1, 0, 0] ![1, 0, 0, 0] = ch6ZS T L V := by
  ext x
  rw [D.mem_ZS_iff]
  constructor
  · rintro ⟨α, β, rfl⟩
    refine ⟨β, α, ?_⟩
    show D.kv (α • (![0, 1, 0, 0] : Fin 4 → ZMod 2) + β • ![1, 0, 0, 0]) = _
    rw [show α • (![0, 1, 0, 0] : Fin 4 → ZMod 2) + β • ![1, 0, 0, 0] = ![β, α, 0, 0] by
      ext i; fin_cases i <;> simp]
    rw [D.kv_vec, zv0, pow_zero, pow_zero, mul_one, mul_one]
  · rintro ⟨a, b, rfl⟩
    refine ⟨b, a, ?_⟩
    show D.kv (b • (![0, 1, 0, 0] : Fin 4 → ZMod 2) + a • ![1, 0, 0, 0]) = _
    rw [show b • (![0, 1, 0, 0] : Fin 4 → ZMod 2) + a • ![1, 0, 0, 0] = ![a, b, 0, 0] by
      ext i; fin_cases i <;> simp]
    rw [D.kv_vec, zv0, pow_zero, pow_zero, mul_one, mul_one]

omit [Finite G] D in
theorem mem_normalizer_of_map_eq {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj g).toMonoidHom x ∈ K.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at this
    exact this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    rwa [← this]

theorem U_le_T : uCh611 T L V ≤ T := by
  intro u hu
  have huH : u ∈ hCh611 T := Subgroup.mem_centralizer_iff.mpr fun x hx =>
    D.comm x (ZS_le_U (D.ZZS hx)) u hu
  have huC : u ∈ Subgroup.centralizer (uCh611 T L V : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => D.comm x hx u hu
  exact F7.isSylowTwoOf_pCoreOf_le (D.hyp.toHyp5_0_1.isSylowTwoOf (T_le_hCh611 T))
    (D.cq u huH huC)

@[expose] def formStab (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (uCh611 T L V : Set G) ∧
    ∃ A, D.IsMat g A ∧ Matrix.transpose A * B * A = B}
  mul_mem' := by
    rintro g g' ⟨hg, A, hA, hAB⟩ ⟨hg', A', hA', hA'B⟩
    refine ⟨Subgroup.mul_mem _ hg hg', A * A', D.isMat_mul hA hA', ?_⟩
    rw [Matrix.transpose_mul]
    calc Matrix.transpose A' * Matrix.transpose A * B * (A * A')
        = Matrix.transpose A' * (Matrix.transpose A * B * A) * A' := by
          simp only [Matrix.mul_assoc]
      _ = B := by rw [hAB, hA'B]
  one_mem' := ⟨Subgroup.one_mem _, 1, D.isMat_one, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, A, hA, hAB⟩
    have hgi := Subgroup.inv_mem _ hg
    obtain ⟨A', hA'⟩ := D.exists_isMat hgi
    have hAA' : A * A' = 1 := by
      have := D.isMat_mul hA hA'
      rw [mul_inv_cancel] at this
      exact D.isMat_unique this D.isMat_one
    refine ⟨hgi, A', hA', ?_⟩
    calc Matrix.transpose A' * B * A'
        = Matrix.transpose A' * (Matrix.transpose A * B * A) * A' := by rw [hAB]
      _ = Matrix.transpose (A * A') * B * (A * A') := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hAA']; simp

end Data611

theorem Data611.false (D : Data611 G T M L V d u₁ z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmc := D.isMulCommutative
  set H := hCh611 T with hHdef
  set U := uCh611 T L V with hUdef
  have hTH : T ≤ H := T_le_hCh611 T
  have hVH : V ≤ H := D.V_le_H
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V
  obtain ⟨t₁, ht₁, β, hβ⟩ := D.exists_t1
  obtain ⟨h₀, hh₀, γ, hγ⟩ := D.exists_h0
  obtain ⟨v₁, hv₁, hv₁m⟩ := D.exists_v 1
  obtain ⟨v₂, hv₂, hv₂m⟩ := D.exists_v 2
  have ht₁H := hTH ht₁
  have hv₁H := hVH hv₁
  have hv₂H := hVH hv₂
  obtain ⟨r1, r2, r3, r4⟩ := rels_sameMod_ch611 β γ
  have e1 := D.eq_of_sameMod (H.mul_mem ht₁H ht₁H) H.one_mem (D.isMat_mul hβ hβ) D.isMat_one r1
  have e2 := D.eq_of_sameMod (H.mul_mem hh₀ hh₀) H.one_mem (D.isMat_mul hγ hγ) D.isMat_one r2
  have e3 := D.eq_of_sameMod (H.mul_mem (H.mul_mem (H.mul_mem hv₁H ht₁H) hv₂H) ht₁H) H.one_mem
    (D.isMat_mul (D.isMat_mul (D.isMat_mul hv₁m hβ) hv₂m) hβ) D.isMat_one r3
  have e4 := D.eq_of_sameMod
    (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hv₁H hh₀) hv₁H) hh₀) hv₁H) hh₀)
    H.one_mem (D.isMat_mul (D.isMat_mul (D.isMat_mul (D.isMat_mul (D.isMat_mul hv₁m hγ) hv₁m) hγ)
      hv₁m) hγ) D.isMat_one r4
  have hgood := good_of_rels_ch611 β γ e1 e2 e3 e4
  have hCF := caseFacts_ch611 β γ hgood
  have hKF := kerFact_ch611 β γ hgood
  obtain ⟨cP1, cP2, cP3, cDist, cT1, cR4, cY4, cKl, cF1, cF2, cF3, cCol, cNV, cYY, cP4, cQ4⟩ :=
    hCF
  obtain ⟨w, hw, hwm⟩ := D.exists_v (wIdxCh611 β γ)
  set y := h₀ * w * d * h₀⁻¹ with hy
  have hh₀i := D.isMat_inv hγ e2
  have hym : D.IsMat y (matYCh611 β γ) :=
    D.isMat_mul (D.isMat_mul (D.isMat_mul hγ hwm) D.isMat_d) hh₀i
  have hyi : D.IsMat y⁻¹ (matYinvCh611 β γ) := D.isMat_inv hym cYY
  have hyU : y ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHU hh₀) (hHU (hVH hw))) D.dU)
      (Subgroup.inv_mem _ (hHU hh₀))
  have hTmat : ∀ t ∈ T, ∃ k : Fin 4, ∃ s : Bool,
      D.IsMat t (vhatCh611 k * (if s then matT1Ch611 β else 1)) := by
    intro t ht
    obtain ⟨x, hx⟩ := D.isMat_t ht
    obtain ⟨k, s, hks⟩ := uniCh611_sameMod_T x β
    obtain ⟨v, hv, hvm⟩ := D.exists_v k
    have hg' : ∃ g' ∈ H, D.IsMat g' (vhatCh611 k * (if s then matT1Ch611 β else 1)) := by
      cases s
      · exact ⟨v, hVH hv, by simpa using hvm⟩
      · exact ⟨v * t₁, H.mul_mem (hVH hv) ht₁H, by simpa using D.isMat_mul hvm hβ⟩
    obtain ⟨g', hg'H, hg'm⟩ := hg'
    refine ⟨k, s, ?_⟩
    rw [← D.eq_of_sameMod (hTH ht) hg'H hx hg'm hks]
    exact hx
  set Ω : Fin 5 → Subgroup G := fun i => D.line (omPCh611 β γ i) (omQCh611 β γ i) with hΩ
  have hΩinj : Function.Injective Ω := by
    intro i j hij
    by_contra hne
    obtain ⟨a, b, hab⟩ := cDist i j hne
    have := D.lineEq_of_line_eq hij
    obtain ⟨a', b', he⟩ := this.1 a b
    exact hab a' b' he
  have hperm : ∀ {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}, D.IsMat g A →
      (∀ i, ∃ j, LineEqCh611 (A.mulVec (omPCh611 β γ i)) (A.mulVec (omQCh611 β γ i))
        (omPCh611 β γ j) (omQCh611 β γ j)) → g ∈ permStabCh611 Ω := by
    intro g A hA hA'
    refine exists_permByCh611 hΩinj fun i => ?_
    obtain ⟨j, hj⟩ := hA' i
    exact ⟨j, (D.map_line hA _ _).trans (D.line_eq_of_lineEq hj)⟩
  have hpermBy : ∀ {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} {σ : Equiv.Perm (Fin 5)},
      D.IsMat g A → (∀ i, LineEqCh611 (A.mulVec (omPCh611 β γ i)) (A.mulVec (omQCh611 β γ i))
        (omPCh611 β γ (σ i)) (omQCh611 β γ (σ i))) → PermByCh611 Ω g σ := by
    intro g A σ hA hA' i
    exact (D.map_line hA _ _).trans (D.line_eq_of_lineEq (hA' i))
  have hTperm : T ≤ permStabCh611 Ω := by
    intro t ht
    obtain ⟨k, s, hks⟩ := hTmat t ht
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hks
      exact hperm hks (cP1 k)
    · simp only [↓reduceIte] at hks
      exact hperm hks (cP2 k)
  have hyperm : y ∈ permStabCh611 Ω := hperm hym cP3
  set Y := T ⊔ Subgroup.zpowers y with hYdef
  have hTY : T ≤ Y := le_sup_left
  have hyY : y ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hYP : Y ≤ permStabCh611 Ω := sup_le hTperm ((Subgroup.zpowers_le).mpr hyperm)
  have hTF : T ≤ D.formStab (formBCh611 β γ) := by
    intro t ht
    obtain ⟨k, s, hks⟩ := hTmat t ht
    refine ⟨hHU (hTH ht), _, hks, ?_⟩
    cases s
    · simpa using cF1 k
    · simpa using cF2 k
  have hYF : Y ≤ D.formStab (formBCh611 β γ) :=
    sup_le hTF ((Subgroup.zpowers_le).mpr ⟨hyU, _, hym, cF3⟩)
  set ψ : ↥Y →* Equiv.Perm (Fin 5) :=
    (permHomCh611 Ω hΩinj).comp (Subgroup.inclusion hYP) with hψ
  have hψval : ∀ (g : G) (hg : g ∈ Y) {σ : Equiv.Perm (Fin 5)}, PermByCh611 Ω g σ →
      ψ ⟨g, hg⟩ = σ := fun g hg σ hσ => permHomCh611_eq hΩinj (g := ⟨g, hYP hg⟩) hσ
  have hψt₁ : ψ ⟨t₁, hTY ht₁⟩ = Equiv.swap 0 2 := hψval _ _ (hpermBy hβ cT1)
  have hv₂t₁ : v₂ * t₁ ∈ Y := hTY (T.mul_mem (D.hyp.toHyp611.le_T hv₂) ht₁)
  have hψr4 : ψ ⟨v₂ * t₁, hv₂t₁⟩ = L619.r4 := hψval _ _ (hpermBy (D.isMat_mul hv₂m hβ) cR4)
  have hψy4 : ψ ⟨y, hyY⟩ 4 ≠ 4 := by
    have h1 := permHomCh611_spec Ω hΩinj ⟨y, hYP hyY⟩ 4
    have h2 : (Ω 4).map (MulAut.conj y).toMonoidHom = Ω 0 :=
      (D.map_line hym _ _).trans (D.line_eq_of_lineEq cY4)
    have h3 : Ω (ψ ⟨y, hyY⟩ 4) = Ω 0 := h1.symm.trans h2
    rw [hΩinj h3]
    decide
  have hd8 : L619.d8 ≤ (T.subgroupOf Y).map ψ := by
    have hs : Equiv.swap (0 : Fin 5) 2 ∈ (T.subgroupOf Y).map ψ :=
      ⟨⟨t₁, hTY ht₁⟩, Subgroup.mem_subgroupOf.mpr ht₁, hψt₁⟩
    have hr : L619.r4 ∈ (T.subgroupOf Y).map ψ :=
      ⟨⟨v₂ * t₁, hv₂t₁⟩, Subgroup.mem_subgroupOf.mpr (T.mul_mem (D.hyp.toHyp611.le_T hv₂) ht₁),
        hψr4⟩
    intro σ hσ
    rw [L619.mem_d8] at hσ
    simp only [L619.d8List, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hr
    · exact Subgroup.pow_mem _ hr 2
    · exact Subgroup.pow_mem _ hr 3
    · exact hs
    · exact Subgroup.mul_mem _ hr hs
    · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hr 2) hs
    · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hr 3) hs
  have hψsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    rcases L619.le_stab4_or_eq_top (hd8.trans (Subgroup.map_le_range _ _)) with hle | htop
    · exfalso
      exact hψy4 (L619.mem_stab4.mp (hle ⟨⟨y, hyY⟩, rfl⟩))
    · exact htop
  have hker : IsPGroup 2 ψ.ker := by
    refine fun g => ?_
    obtain ⟨⟨x, hxY⟩, hx⟩ := g
    have hx1 : ψ ⟨x, hxY⟩ = 1 := hx
    obtain ⟨hxU, A, hA, hAB⟩ := hYF hxY
    have hfix : ∀ i, LineEqCh611 (A.mulVec (omPCh611 β γ i)) (A.mulVec (omQCh611 β γ i))
        (omPCh611 β γ i) (omQCh611 β γ i) := by
      intro i
      have h1 := permHomCh611_spec Ω hΩinj ⟨x, hYP hxY⟩ i
      have h2 : permHomCh611 Ω hΩinj ⟨x, hYP hxY⟩ = 1 := hx1
      rw [h2] at h1
      exact D.lineEq_of_line_eq ((D.map_line hA _ _).symm.trans h1)
    have hcolc : ∀ j, ∃ p : ZMod 2 × ZMod 2, A.col j = p.1 • omPCh611 β γ (kIdxCh611 β γ j) +
        p.2 • omQCh611 β γ (kIdxCh611 β γ j) := by
      intro j
      obtain ⟨a, b, hab⟩ := cCol j
      obtain ⟨α, β', he⟩ := (hfix (kIdxCh611 β γ j)).1 a b
      refine ⟨(α, β'), ?_⟩
      rw [← Matrix.mulVec_single_one, hab, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul]
      exact he
    choose c hc using hcolc
    have hAc : A = candACh611 β γ c := matrix_eq_of_cols_ch611 fun j => (hc j).trans rfl
    rw [hAc] at hAB hfix
    have hA1 := hKF c hAB hfix
    rw [← hAc] at hA1
    have hxC := (D.mem_centralizer_iff_isMat hA).mpr hA1
    have hxH : x ∈ H := Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := Subgroup.mem_centralizer_iff.mp hxC w (ZS_le_U (D.ZZS hw))
      exact this
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨x, D.cq x hxH hxC⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hO : pCoreOf 2 Y ≠ ⊥ := by
    have hUY : U ≤ Y := D.U_le_T.trans hTY
    have hYU : Y ≤ Subgroup.normalizer (U : Set G) := sup_le (hTH.trans hHU)
      ((Subgroup.zpowers_le).mpr hyU)
    have hU2 : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa using D.sq u u.2)⟩
    have hle := le_pCoreOf_of_le_normalizer 2 hUY hYU hU2
    intro h0
    rw [h0] at hle
    have := Subgroup.card_le_of_le hle
    rw [D.card, Subgroup.card_bot] at this
    omega
  have hYM : ¬ Y ≤ M := by
    intro hYM
    have hyV : y ∈ Subgroup.normalizer (V : Set G) := D.mv (hYM hyY)
    obtain ⟨k, hk⟩ := cNV
    obtain ⟨v, hv, hvm⟩ := D.exists_v k
    have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
    obtain ⟨k', hk'⟩ := D.isMat_v hyv
    exact hk k' (D.isMat_unique (D.isMat_mul (D.isMat_mul hym hvm) hyi) hk')
  have hQM : ∀ x : ↥Y, ψ x ∈ L619.stab4 → (x : G) ∈ M := by
    intro x hx
    have h1 := permHomCh611_spec Ω hΩinj ⟨x, hYP x.2⟩ 4
    have h2 : ψ x 4 = 4 := L619.mem_stab4.mp hx
    have h3 : permHomCh611 Ω hΩinj ⟨x, hYP x.2⟩ 4 = 4 := h2
    rw [h3] at h1
    have h4 : Ω 4 = ch6ZS T L V := by
      show D.line (omPCh611 β γ 4) (omQCh611 β γ 4) = _
      rw [cP4, cQ4]
      exact D.line_ZS
    rw [h4] at h1
    exact D.nzs (Data611.mem_normalizer_of_map_eq h1)
  have hlift : IsHStar T M Y → E1.LiftS5.RootFourLift Y T
      ((MulEquiv.refl (Equiv.Perm (Fin 5))).toMonoidHom.comp ψ) := by
    intro _
    have hVψ : ∀ v (hv : v ∈ V), ∃ k, ψ ⟨v, hTY (D.hyp.toHyp611.le_T hv)⟩ = kleinCh611 k := by
      intro v hv
      obtain ⟨k, hk⟩ := D.isMat_v hv
      exact ⟨k, hψval _ _ (hpermBy hk (cKl k))⟩
    refine ⟨V, D.hyp.toHyp611.le_T, D.hyp.toHyp611.isElemAbelian, ?_, ?_⟩
    · rintro σ ⟨⟨v, hvY⟩, hv, rfl⟩
      obtain ⟨k, hk⟩ := hVψ v (Subgroup.mem_subgroupOf.mp hv)
      show ψ ⟨v, hvY⟩ ∈ alternatingGroup (Fin 5)
      rw [hk]
      exact kleinCh611_props.1 k
    · have himg : ((V.subgroupOf Y).map ((MulEquiv.refl (Equiv.Perm (Fin 5))).toMonoidHom.comp ψ) :
          Set (Equiv.Perm (Fin 5))) = Set.range kleinCh611 := by
        ext σ
        constructor
        · rintro ⟨⟨v, hvY⟩, hv, rfl⟩
          obtain ⟨k, hk⟩ := hVψ v (Subgroup.mem_subgroupOf.mp hv)
          exact ⟨k, hk.symm⟩
        · rintro ⟨k, rfl⟩
          obtain ⟨v, hv, hvm⟩ := D.exists_v k
          exact ⟨⟨v, hTY (D.hyp.toHyp611.le_T hv)⟩, Subgroup.mem_subgroupOf.mpr hv,
            hψval _ _ (hpermBy hvm (cKl k))⟩
      rw [← SetLike.coe_sort_coe, himg, Nat.card_range_of_injective kleinCh611_props.2,
        Nat.card_eq_fintype_card, Fintype.card_fin]
  exact false_of_s5_hStar D.hyp.toHyp611 (MulEquiv.refl (Equiv.Perm (Fin 5))) ψ hψsurj hker hTY hO
    hYM (fun R hR => L619.le_stab4_or_eq_top (hd8.trans hR)) hQM hlift

theorem stmt6_2_11_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (hG31 : Ch6G31O2) :
    Stmt6_2_11 := by
  intro G _ _ T M L V h
  show (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V = 2
  by_contra h4
  obtain ⟨d, u₁, z, D⟩ := h.exists_data611 h331 h432 h512 h614 h615 h6210 hG31 h4
  exact D.false

end CFSG.Quasithin.H13
