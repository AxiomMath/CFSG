module

public import CFSG.Quasithin.Background.SmithC27RHat6Index

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

omit [Finite G] in
private theorem conjAct_coe_apply (n : ↥(Subgroup.normalizer (V : Set G))) (x : ↥V) :
    ((conjAct V n x : ↥V) : G) = n * x * (n : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl n) x

omit [Finite G] in
theorem conj_eq_of_starK_eq (hs : StarHyp R K V) {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) {k : ↥K}
    (hka : ((starK hs k : ↥(autOn K V)) : MulAut ↥V) = conjAct V ⟨a, ha⟩) {u : G}
    (hu : u ∈ V) : (k : G) * u * (k : G)⁻¹ = a * u * a⁻¹ := by
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : G)) hka
  simp only [coe_starK, conjAct_coe_apply] at h1
  exact h1

section Coord

variable {F : Type} [Field F] {ψ : ↥(autOn K V) →* Matrix.GeneralLinearGroup (Fin 3) F}
  {e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)}

theorem card_inf_centralizer_eq (hs : StarHyp R K V) (hUV : blockU K ≤ V)
    (he : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (e v) = ((ψ (starK hs k) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)))
    {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAK : autOn A V ≤ autOn K V) :
    Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) := by
  have hconj : ∀ (k : ↥K) (u : ↥(blockU K)), (k : G) * u * (k : G)⁻¹ ∈ blockU K := fun k u =>
    (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU K k.2) u).1 u.2
  have h1 : ∀ u : ↥(blockU K), (u : G) ∈ Subgroup.centralizer (A : Set G) →
      Multiplicative.toAdd (e u) ∈ fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V} := by
    intro u hu φ hφ
    obtain ⟨k, rfl⟩ := starK_surjective hs φ
    obtain ⟨n, hnA, hn⟩ := mem_autOn_iff'.1 hφ
    have hkn := conj_eq_of_starK_eq hs n.2 (k := k) hn.symm (hUV u.2)
    have hv : (⟨_, hconj k u⟩ : ↥(blockU K)) = u := by
      refine Subtype.ext ?_
      change (k : G) * u * (k : G)⁻¹ = u
      rw [hkn, (Subgroup.mem_centralizer_iff.1 hu n hnA), mul_inv_cancel_right]
    have := he k u ⟨_, hconj k u⟩ rfl
    rw [hv] at this
    exact this.symm
  have h2 : ∀ y ∈ fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V},
      ((e.symm (Multiplicative.ofAdd y) : ↥(blockU K)) : G) ∈
        Subgroup.centralizer (A : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    set u := e.symm (Multiplicative.ofAdd y) with hu
    have hφ : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V := mem_autOn_iff'.2 ⟨_, ha, rfl⟩
    obtain ⟨k, hk⟩ := starK_surjective hs ⟨_, hAK hφ⟩
    have hka : ((starK hs k : ↥(autOn K V)) : MulAut ↥V) = conjAct V ⟨a, hAN ha⟩ :=
      congrArg Subtype.val hk
    have hfix := hy (starK hs k) (by
      change ((starK hs k : ↥(autOn K V)) : MulAut ↥V) ∈ autOn A V
      rw [hka]
      exact hφ)
    have heu : Multiplicative.toAdd (e u) = y := by rw [hu, MulEquiv.apply_symm_apply]; rfl
    have hev := he k u ⟨_, hconj k u⟩ rfl
    rw [heu, hfix] at hev
    have hvu : (⟨_, hconj k u⟩ : ↥(blockU K)) = u :=
      e.injective (Multiplicative.toAdd.injective (hev.trans heu.symm))
    have h3 : (k : G) * u * (k : G)⁻¹ = u := congrArg Subtype.val hvu
    rw [conj_eq_of_starK_eq hs (hAN ha) hka (hUV u.2)] at h3
    calc a * (u : G) = (a * u * a⁻¹) * a := by group
      _ = u * a := by rw [h3]
  exact Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (e ⟨x, x.2.1⟩), h1 ⟨x, x.2.1⟩ x.2.2⟩
      invFun := fun y => ⟨_, ⟨(e.symm (Multiplicative.ofAdd y)).2, h2 y y.2⟩⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem finrank_fixSub_D [Fintype F] (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hB : IsHatA6Block K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) (hUV : blockU K ≤ V) (hF : Fintype.card F = 4)
    (hψ : Function.Injective ψ)
    (he : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (e v) = ((ψ (starK hs k) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u))) :
    Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V}) = 2 := by
  have hV := hs.elemAbelian
  have hD4 := card_D_le_four hs hnS (card_autOn_of_hatA6 h hs hB)
  obtain ⟨A, hA, hAV⟩ : ∃ A : Subgroup G, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    apply not_thompsonJ_le_centralizer h hs
    refine iSup₂_le fun A hA => ?_
    by_contra hAV
    exact hcon ⟨A, hA, hAV⟩
  have hAJ : A ≤ thompsonJ R := le_iSup₂_of_le A hA le_rfl
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hs.R_le_normalizer_V
  have hAK : autOn A V ≤ autOn K V := (autOn_mono' hAJ).trans hJ
  have hAD : autOn A V ≤ autOn (R ⊓ K) V := by
    rw [← hs.autOn_inf_R]
    exact le_inf (autOn_mono' hA.1) hAK
  have hVR : V ≤ R := (C124.le_pCoreOf_of_reduced hs.red).trans hs.core
  have hoff := offenderImages_isFFStarOffender hV hVR hs.R_le_normalizer_V
    (B := autI hV A) ⟨A, ⟨hA, hAV⟩, rfl⟩
  have hFF : Nat.card ↥V ≤ Nat.card ↥(autOn A V) *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    have h1 := hoff.2.2.2 ⊥ bot_le
    rw [B1.card_bot_mul_card_fixV, card_fixV_autI hV hAN] at h1
    exact h1
  have hCN : V ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (blockU K : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hV.1
    exact setLike_mul_comm (hUV hu) hc.1
  have hprod := card_sup_mul_card_inf_of_le_normalizer' hCN
  have hsup : Nat.card ↥(blockU K ⊔ (V ⊓ Subgroup.centralizer (A : Set G))) ≤ Nat.card ↥V :=
    Subgroup.card_le_of_le (sup_le hUV inf_le_left)
  rw [← inf_assoc, inf_eq_left.2 hUV] at hprod
  have hCpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hU : Nat.card ↥(blockU K) ≤ Nat.card ↥(autOn A V) *
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Nat.le_of_mul_le_mul_right ?_ hCpos
    rw [← hprod]
    calc Nat.card ↥(blockU K ⊔ (V ⊓ Subgroup.centralizer (A : Set G))) *
          Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G))
        ≤ (Nat.card ↥(autOn A V) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) *
          Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul_right _ (hsup.trans hFF)
      _ = _ := by ring
  have hcard : Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) =
      4 ^ Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) := by
    rw [card_inf_centralizer_eq hs hUV he hAN hAK, Module.natCard_eq_pow_finrank (K := F),
      Nat.card_eq_fintype_card, hF]
  have hd3 : Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) ≤ 3 :=
    (Submodule.finrank_le _).trans (by simp)
  have hdne : Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) ≠ 3 := by
    intro h3
    have htop : fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V} = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3]; simp)
    have hbot : autOn A V = ⊥ := by
      refine eq_bot_iff.2 fun φ hφ => (Subgroup.mem_bot).2 ?_
      have h1 : ψ ⟨φ, hAK hφ⟩ = 1 := eq_one_of_fixSub_eq_top htop (t := ⟨φ, hAK hφ⟩) hφ
      exact congrArg Subtype.val (hψ (h1.trans (map_one ψ).symm))
    exact hAV ((autI_eq_bot_iff hV hAN).1 hbot)
  have hA4 : Nat.card ↥(autOn A V) ≤ 4 := (Subgroup.card_le_of_le hAD).trans hD4
  rw [hB.2.2.1, hcard] at hU
  have hd2 : Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) = 2 := by
    generalize Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn A V}) = d at hU hd3 hdne ⊢
    interval_cases d <;> first | rfl | omega
  rw [hd2] at hU
  have hAeq : autOn A V = autOn (R ⊓ K) V := Subgroup.eq_of_le_of_card_ge hAD (by
    norm_num at hU
    omega)
  rw [← hAeq]
  exact hd2

omit [Finite G] in
theorem fixSub_D_stable (hO : pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V)
    {φ₀ : ↥(autOn K V)}
    (hφ₀ : (φ₀ : MulAut ↥V) ∈ autOn (M ⊓ K) V) :
    ∀ w ∈ fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V},
      ((ψ φ₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈
        fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V} := by
  intro w hw φ hφ
  have hN : (φ₀ : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn (R ⊓ K) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    rw [← hO]
    exact le_normalizer_pCoreOf 2 _ hφ₀
  have hc : ((φ₀⁻¹ * φ * φ₀ : ↥(autOn K V)) : MulAut ↥V) ∈ autOn (R ⊓ K) V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hN) (φ : MulAut ↥V)).1 hφ
    simpa [mul_assoc] using this
  have h1 := hw _ hc
  rw [map_mul, map_mul, map_inv] at h1
  have key : ψ φ₀ * ((ψ φ₀)⁻¹ * ψ φ * ψ φ₀) = ψ φ * ψ φ₀ := by group
  change ((ψ φ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
    (((ψ φ₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w) = _
  calc ((ψ φ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (((ψ φ₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w)
      = ((ψ φ₀ * ((ψ φ₀)⁻¹ * ψ φ * ψ φ₀) : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).mulVec w := by
        rw [key, Units.val_mul, Matrix.mulVec_mulVec]
    _ = ((ψ φ₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]

theorem mem_of_stable [Finite F] (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hB : IsHatA6Block K) (hZ : blockZ K = ⊥)
    (hP : IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V))
    (hO : pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V)
    (he : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (e v) = ((ψ (starK hs k) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)))
    (hW : Module.finrank F (fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V}) = 2) (k : ↥K)
    (hk : ∀ w ∈ fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V},
      ((ψ (starK hs k) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec w ∈ fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V}) :
    (k : G) ∈ M := by
  set W := fixSub ψ {φ | (φ : MulAut ↥V) ∈ autOn (R ⊓ K) V} with hWdef
  have hKC := inf_centralizer_eq_of_hatA6 h hs hB
  set Q : Subgroup ↥K := (stabGL W).comap (ψ.comp (starK hs)) with hQ
  have hmemQ : ∀ k : ↥K, k ∈ Q ↔ ∀ w ∈ W, ((ψ (starK hs k) :
      Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W :=
    fun k => mem_stabGL_iff
  have hQK : autOn (Q.map K.subtype) V ≤ autOn K V := autOn_mono' (Subgroup.map_subtype_le Q)
  have hMQ : autOn (M ⊓ K) V ≤ autOn (Q.map K.subtype) V := autOn_mono' fun g hg =>
    ⟨⟨g, hg.2⟩, (hmemQ _).2 (fixSub_D_stable hO
      ((mem_iff_starHom_mem h hs hKC ⟨g, hg.2⟩).1 hg.1)), rfl⟩
  have hQne : autOn (Q.map K.subtype) V ≠ autOn K V := by
    intro hQeq
    have hall : ∀ k : ↥K, k ∈ Q := by
      intro k
      have hk' : ((starK hs k : ↥(autOn K V)) : MulAut ↥V) ∈ autOn (Q.map K.subtype) V := by
        rw [hQeq]
        exact (starK hs k).2
      obtain ⟨n, ⟨q, hq, hqn⟩, hn⟩ := mem_autOn_iff'.1 hk'
      have hsq : starK hs q = starK hs k := by
        apply Subtype.ext
        rw [coe_starK, ← hn]
        congr 1
        exact Subtype.ext hqn
      change ψ (starK hs k) ∈ stabGL W
      rw [← hsq]
      exact hq
    let WG : Subgroup G :=
      { carrier := {g | ∃ u : ↥(blockU K), (u : G) = g ∧ Multiplicative.toAdd (e u) ∈ W}
        mul_mem' := by
          rintro _ _ ⟨u₁, rfl, h₁⟩ ⟨u₂, rfl, h₂⟩
          exact ⟨u₁ * u₂, rfl, by rw [map_mul, toAdd_mul]; exact W.add_mem h₁ h₂⟩
        one_mem' := ⟨1, rfl, by rw [map_one, toAdd_one]; exact W.zero_mem⟩
        inv_mem' := by
          rintro _ ⟨u, rfl, hu⟩
          exact ⟨u⁻¹, rfl, by rw [map_inv, toAdd_inv]; exact W.neg_mem hu⟩ }
    have hWU : WG ≤ blockU K := by
      rintro _ ⟨u, rfl, -⟩
      exact u.2
    have hconj : ∀ (k : ↥K) (g : G), g ∈ WG → (k : G) * g * (k : G)⁻¹ ∈ WG := by
      rintro k _ ⟨u, rfl, hu⟩
      have hv : (k : G) * u * (k : G)⁻¹ ∈ blockU K :=
        (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU K k.2) u).1 u.2
      refine ⟨⟨_, hv⟩, rfl, ?_⟩
      rw [he k u ⟨_, hv⟩ rfl]
      exact (hmemQ k).1 (hall k) _ hu
    have hKN : K ≤ Subgroup.normalizer (WG : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨hconj ⟨k, hk⟩ g, fun hg => ?_⟩
      have := hconj ⟨k, hk⟩⁻¹ _ hg
      simpa [mul_assoc] using this
    rcases hB.1.2.2.2.2.2 WG (hZ ▸ bot_le) hWU hKN with h1 | h1
    ·
      have hbot : W = ⊥ := by
        refine eq_bot_iff.2 fun w hw => ?_
        have hmem : ((e.symm (Multiplicative.ofAdd w) : ↥(blockU K)) : G) ∈ WG :=
          ⟨_, rfl, by rw [MulEquiv.apply_symm_apply]; exact hw⟩
        rw [h1, hZ, Subgroup.mem_bot] at hmem
        have h2 : e.symm (Multiplicative.ofAdd w) = 1 := Subtype.ext hmem
        rw [MulEquiv.symm_apply_eq, map_one] at h2
        rw [Submodule.mem_bot]
        exact congrArg Multiplicative.toAdd h2
      rw [hbot, finrank_bot] at hW
      exact absurd hW (by norm_num)
    ·
      have htop : W = ⊤ := by
        refine eq_top_iff.2 fun x _ => ?_
        have hmem : ((e.symm (Multiplicative.ofAdd x) : ↥(blockU K)) : G) ∈ WG := by
          rw [h1]
          exact (e.symm (Multiplicative.ofAdd x)).2
        obtain ⟨u, hu, hxW⟩ := hmem
        have h2 : u = e.symm (Multiplicative.ofAdd x) := Subtype.ext hu
        rw [h2, MulEquiv.apply_symm_apply] at hxW
        exact hxW
      rw [htop, finrank_top] at hW
      simp at hW
  obtain ⟨⟨-, S, hS, hSN⟩, -, hmax⟩ := hP
  have hQeq := hmax _ ⟨hQK, S, hS, hSN.trans hMQ⟩ hQne hMQ
  rw [mem_iff_starHom_mem h hs hKC k, ← hQeq]
  exact mem_autOn_iff'.2 ⟨⟨k, hs.K_le_normalizer_V k.2⟩, ⟨k, (hmemQ k).2 hk, rfl⟩, rfl⟩

end Coord

theorem c27_hat6 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hB : IsHatA6Block K)
    (hT : ∃ hV : IsElemAbelian 2 V,
      TripleA6Six (autI hV K) (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)))
    (hP : IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V))
    (hO : pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V)
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) :
    IsHatA6Block K ∧ M.relIndex K = 15 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
        ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
          (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
          (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
            Multiplicative.toAdd (e v) =
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
                (Multiplicative.toAdd (e u))) ∧
          ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
            ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w
                ∈ W := by
  obtain ⟨hZ, hUV, F, _, _, hF, ψ, hψ, e, he⟩ := exists_coord_of_hatA6 h hs hB hT
  have hW := finrank_fixSub_D h hs hB hnS hJ hUV hF hψ he
  have hKC := inf_centralizer_eq_of_hatA6 h hs hB
  exact ⟨hB, relIndex_eq_fifteen h hs hB hnS hP hO, F, inferInstance, inferInstance, hF,
    ψ.comp (starK hs), e, he, _, hW, fun k =>
      ⟨fun hk => fixSub_D_stable hO ((mem_iff_starHom_mem h hs hKC k).1 hk),
        mem_of_stable h hs hB hZ hP hO he hW k⟩⟩

end CFSG.Quasithin.SmithC27
