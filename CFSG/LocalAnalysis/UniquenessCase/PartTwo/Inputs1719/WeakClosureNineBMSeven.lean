module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

@[expose] def prodC (w : List (List ℕ)) : List ℕ := w.foldl Core.cmul cid

theorem exists_prod_mem {G : Subgroup P16} {H : Subgroup ↥G} :
    ∀ (w : List (List ℕ)) (x0 : ↥G), x0 ∈ H →
      (∀ c ∈ w, ∃ x ∈ H, code x.1 = c) → ∃ x ∈ H, code x.1 = w.foldl Core.cmul (code x0.1)
  | [], x0, h0, _ => ⟨x0, h0, rfl⟩
  | c :: w, x0, h0, h => by
    obtain ⟨y, hy, rfl⟩ := h c List.mem_cons_self
    obtain ⟨x, hx, hxc⟩ := exists_prod_mem w (x0 * y) (mul_mem h0 hy)
      (fun d hd => h d (List.mem_cons_of_mem _ hd))
    refine ⟨x, hx, ?_⟩
    rw [hxc, List.foldl_cons, Subgroup.coe_mul, code_mul]

theorem exists_prodC_mem {G : Subgroup P16} {H : Subgroup ↥G} {w : List (List ℕ)}
    (h : ∀ c ∈ w, ∃ x ∈ H, code x.1 = c) : ∃ x ∈ H, code x.1 = prodC w := by
  obtain ⟨x, hx, hxc⟩ := exists_prod_mem w 1 (one_mem H) h
  exact ⟨x, hx, by rw [hxc, prodC, Subgroup.coe_one, code_one]⟩

theorem coreIn_mono {G : Type*} [Group G] {K K' H : Subgroup G} (h : K ≤ K') :
    coreIn K H ≤ coreIn K' H := fun _ hx => ⟨hx.1, fun g hg => h (hx.2 g hg)⟩

theorem sevenWit_mono {X : Type} [Group X] {L1 L2 T V A K Y : Subgroup X}
    (h : SevenWit L1 L2 T V K Y) (hVA : V ≤ A) (hAK : A ≤ K) : SevenWit L1 L2 T A K Y where
  le := hAK
  irr := h.irr
  core := (coreIn_mono (inf_le_inf_left _ (centralizer_le hVA))).trans h.core
  nonorm := fun R hAR hRK => h.nonorm R (hVA.trans hAR) hRK
  good := h.good

section Main

variable {i : Fin 4} {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
  (hC : KChk tLit D = true)
include hT hE hC

theorem exists_good_Kx : ∃ y ∈ Kx i D, IsGood915 (L1b i) (L2b i) y := by
  obtain ⟨c, hc, hc1, hcL⟩ := (kchk_parts hT hC).2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨σ, hσ, rfl⟩ := hE.y.surj c hc
  set y : ↥(GB i) := ⟨σ, kY_le_GB hT hC hσ⟩
  have h3 := (kchk_parts hT hC).2.2.2.2.2.2.1 _ hc
  have hy1 : y ≠ 1 := fun h => hc1 (by rw [show σ = 1 from congrArg Subtype.val h, code_one])
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    apply code_injective
    rw [Subgroup.coe_pow, pow_succ, pow_two, code_mul, code_mul, h3, Subgroup.coe_one, code_one]
  refine ⟨y, mem_sup_left hσ, orderOf_eq_prime hy3 hy1, ?_⟩
  rcases hcL with h1 | h2
  · exact Or.inl ((l1_desc.mem σ).2 h1)
  · exact Or.inr ((l2_desc.mem σ).2 h2)

theorem Qx_le_pCoreOf : Qx i D ≤ pCoreOf 2 (Kx i D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQK : Qx i D ≤ Kx i D := (Qx_le_Sx hT hE hC).trans le_sup_right
  have hQn : ((Qx i D).subgroupOf (Kx i D)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQK).2 (Kx_le_normQx hT hE hC)
  have hp : IsPGroup 2 ((Qx i D).subgroupOf (Kx i D)) := by
    refine IsPGroup.of_card (n := D.qn) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv, card_Qx hT hE hC]
  intro x hx
  exact ⟨⟨x, hQK hx⟩, CFSG.LieType.BorelTits.le_pCore 2 hQn hp hx, rfl⟩

omit hT hE hC in
theorem pCoreOf_le_Kx : pCoreOf 2 (Kx i D) ≤ Kx i D := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit hT hE hC in
theorem pCoreOf_conj_mem {x k : ↥(GB i)} (hx : x ∈ pCoreOf 2 (Kx i D)) (hk : k ∈ Kx i D) :
    k * x * k⁻¹ ∈ pCoreOf 2 (Kx i D) := by
  obtain ⟨x', hx', rfl⟩ := hx
  have hn := CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥(Kx i D))
  exact ⟨⟨k, hk⟩ * x' * ⟨k, hk⟩⁻¹, hn.conj_mem x' hx' ⟨k, hk⟩, rfl⟩

theorem pCoreOf_le_Sx (hTp : IsPGroup 2 (Tb i)) : pCoreOf 2 (Kx i D) ≤ Sx i D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := (twoPTwoIrred_Kx hT hE hC hTp).sylowTwo
  rw [Kx_inf_Tb hT hE hC hTp] at hsyl
  refine hsyl.le_of_normal (pCoreOf_le_Kx) ?_ ?_
  · have e : (pCoreOf 2 (Kx i D)).subgroupOf (Kx i D) = CFSG.pCore 2 ↥(Kx i D) := by
      ext x
      rw [pCoreOf, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [← Subtype.ext hyx]
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [e]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  · exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _

@[expose] def O2Chk (D : KData) (ws : List (List (List ℕ))) : Bool :=
  D.sLit.length == ws.length &&
  (D.sLit.zip ws).all fun p => D.qLit.contains p.1 ||
    (p.2.all (fun c => D.yLit.contains c || D.sLit.contains c) &&
      !(D.sLit.contains (cconj (prodC p.2) p.1)))

theorem pCoreOf_le_Qx (hTp : IsPGroup 2 (Tb i)) {ws : List (List (List ℕ))}
    (hw : O2Chk D ws = true) : pCoreOf 2 (Kx i D) ≤ Qx i D := by
  intro x hx
  have hxS := pCoreOf_le_Sx hT hE hC hTp hx
  have hxc : code x.1 ∈ D.sLit := (hE.s.mem _).1 hxS
  simp only [O2Chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, Bool.not_eq_true'] at hw
  obtain ⟨hlen, hall⟩ := hw
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxc
  have hk' : k < ws.length := hlen ▸ hk
  have hz : (code x.1, ws[k]) ∈ D.sLit.zip ws := by
    rw [← hkx]
    exact List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
  rcases hall _ hz with h | ⟨hlet, hout⟩
  · exact (hE.q.mem _).2 h
  · exfalso
    obtain ⟨j, hj, hjc⟩ := exists_prodC_mem (H := Kx i D) (w := ws[k]) fun c hc => by
      rcases hlet c hc with h1 | h1
      · obtain ⟨σ, hσ, rfl⟩ := hE.y.surj c h1
        exact ⟨⟨σ, kY_le_GB hT hC hσ⟩, mem_sup_left hσ, rfl⟩
      · obtain ⟨σ, hσ, rfl⟩ := hE.s.surj c h1
        exact ⟨⟨σ, kS_le_GB hT hE hC hσ⟩, mem_sup_right hσ, rfl⟩
    have h1 := pCoreOf_le_Sx hT hE hC hTp (pCoreOf_conj_mem hx hj)
    have h2 : code (j * x * j⁻¹).1 ∈ D.sLit := (hE.s.mem _).1 h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj, hjc] at h2
    rw [List.contains_iff_mem.2 h2] at hout
    exact Bool.noConfusion hout

@[expose] def NonormChk (tLit : List (List ℕ)) (D : KData) (w : List (List ℕ)) (e : List ℕ) :
    Bool :=
  w.all (fun c => D.yLit.contains c || D.sLit.contains c ||
    (tLit.contains c && D.sGen.all fun g => D.sLit.contains (cconj c g))) &&
  !(D.sLit.contains (cconj (prodC w) e))

theorem nonorm_of_chk (hTp : IsPGroup 2 (Tb i)) {A : Subgroup ↥(GB i)} {w : List (List ℕ)}
    {e : ↥(GB i)} (heA : e ∈ A) (hw : NonormChk tLit D w (code e.1) = true) :
    ∀ R : Subgroup ↥(GB i), A ≤ R → R ≤ Kx i D ⊓ Tb i →
      ¬ Kx i D ⊔ (Tb i ⊓ normalizer ((Kx i D ⊓ Tb i : Subgroup ↥(GB i)) : Set ↥(GB i))) ≤
        normalizer (R : Set ↥(GB i)) := by
  intro R hAR hRK hle
  rw [Kx_inf_Tb hT hE hC hTp] at hRK hle
  simp only [NonormChk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, Bool.not_eq_true'] at hw
  obtain ⟨hlet, hout⟩ := hw
  obtain ⟨j, hj, hjc⟩ := exists_prodC_mem
    (H := Kx i D ⊔ (Tb i ⊓ normalizer ((Sx i D : Subgroup ↥(GB i)) : Set ↥(GB i)))) (w := w)
    fun c hc => by
      rcases hlet c hc with (h1 | h1) | ⟨h1, h2⟩
      · obtain ⟨σ, hσ, rfl⟩ := hE.y.surj c h1
        exact ⟨⟨σ, kY_le_GB hT hC hσ⟩, mem_sup_left (mem_sup_left hσ), rfl⟩
      · obtain ⟨σ, hσ, rfl⟩ := hE.s.surj c h1
        exact ⟨⟨σ, kS_le_GB hT hE hC hσ⟩, mem_sup_left (mem_sup_right hσ), rfl⟩
      · obtain ⟨t, htT, rfl⟩ := exists_Tb i hT h1
        refine ⟨t, mem_sup_right ⟨htT, mem_normalizer_subgroupOf ?_⟩, rfl⟩
        apply mem_normalizer_of_map_le
        rw [closureC, MonoidHom.map_closure, closure_le]
        rintro _ ⟨g, hg, rfl⟩
        have := h2 _ hg
        rw [← code_conj] at this
        exact (hE.s.mem _).2 this
  have hjR := (mem_normalizer_iff.1 (hle hj) e).1 (hAR heA)
  have h1 : code (j * e * j⁻¹).1 ∈ D.sLit := (hE.s.mem _).1 (hRK hjR)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj, hjc] at h1
  rw [List.contains_iff_mem.2 h1] at hout
  exact Bool.noConfusion hout

theorem sevenWit_of_cover (hTp : IsPGroup 2 (Tb i)) {V : Subgroup ↥(GB i)}
    (hVS : V ≤ Sx i D) (hcent : Tb i ⊓ centralizer (V : Set ↥(GB i)) ≤ Sx i D)
    {w : List (List ℕ)} {e : ↥(GB i)} (heV : e ∈ V) (hw : NonormChk tLit D w (code e.1) = true)
    {A : Subgroup ↥(GB i)} (hAT : A ≤ Tb i) (hAe : IsElemAbelian 2 A) (hVA : V ≤ A) :
    SevenWit (L1b i) (L2b i) (Tb i) A (Kx i D) (Yx i D) := by
  have hAc : A ≤ Tb i ⊓ centralizer (V : Set ↥(GB i)) := by
    intro a ha
    refine ⟨hAT ha, mem_centralizer_iff.2 fun v hv => ?_⟩
    have := hAe.1
    exact congrArg Subtype.val (mul_comm' (⟨v, hVA hv⟩ : A) ⟨a, ha⟩)
  have hV : SevenWit (L1b i) (L2b i) (Tb i) V (Kx i D) (Yx i D) :=
    { le := hVS.trans le_sup_right
      irr := twoPTwoIrred_Kx hT hE hC hTp
      core := (coreIn_le_right _ _).trans (hcent.trans le_sup_right)
      nonorm := nonorm_of_chk hT hE hC hTp heV hw
      good := exists_good_Kx hT hE hC }
  exact sevenWit_mono hV hVA (hAc.trans (hcent.trans le_sup_right))

theorem sevenWit_of_top (hTp : IsPGroup 2 (Tb i)) (hST : Sx i D = Tb i)
    {ws : List (List (List ℕ))} (hw : O2Chk D ws = true) {A : Subgroup ↥(GB i)}
    (hAT : A ≤ Tb i) (hAQ : ¬ A ≤ Qx i D) :
    SevenWit (L1b i) (L2b i) (Tb i) A (Kx i D) (Yx i D) where
  le := hAT.trans (hST ▸ le_sup_right)
  irr := twoPTwoIrred_Kx hT hE hC hTp
  core := (coreIn_le_right _ _).trans (inf_le_left.trans (hST ▸ le_sup_right))
  nonorm := by
    intro R hAR hRK hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Kx_inf_Tb hT hE hC hTp] at hRK
    have hRK' : R ≤ Kx i D := hRK.trans le_sup_right
    have hRn : (R.subgroupOf (Kx i D)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hRK').2 (le_sup_left.trans hle)
    have hRp : IsPGroup 2 (R.subgroupOf (Kx i D)) :=
      (hTp.to_le (hRK.trans (Sx_le_Tb hT hE hC))).of_equiv (subgroupOfEquivOfLe hRK').symm
    have hRO : R ≤ pCoreOf 2 (Kx i D) := fun x hx =>
      ⟨⟨x, hRK' hx⟩, CFSG.LieType.BorelTits.le_pCore 2 hRn hRp hx, rfl⟩
    exact hAQ (hAR.trans (hRO.trans (pCoreOf_le_Qx hT hE hC hTp hw)))
  good := exists_good_Kx hT hE hC

end Main

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
