module

public import CFSG.Quasithin.H13.A7Nat1238NQ21
public import CFSG.Quasithin.H13.A7Nat1238NQ22Aux
public import CFSG.Quasithin.Background.C1PackC127Act
public import CFSG.Quasithin.EmptyFaithful.S146D1
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X3 CFSG.GorensteinWalter Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_surj_SL2_autI {H K₀ U : Subgroup G} (hK₀H : K₀ ≤ H) (hred : IsTwoReducedIn H U)
    (hcent : (CFSG.solvableRadical ↥K₀).map K₀.subtype ≤ centralizer (U : Set G)) {p : ℕ}
    (hSL : IsSL2 p (↥(modO2Image H K₀) ⧸ CFSG.oddCore ↥(modO2Image H K₀))) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* ↥(autI hred.2.2.1 K₀),
      Function.Surjective ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hU := hred.2.2.1 with hhU
  have hHN : H ≤ normalizer (U : Set G) := hred.2.1
  set P := CFSG.pCore 2 ↥H with hP
  set L := modO2Image H K₀ with hLdef
  set f := convHom hU H hHN with hf
  have hO : pCoreOf 2 H ≤ centralizer (U : Set G) := by
    refine hred.2.2.2 (pCoreOf 2 H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have hk' : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [hk']
    exact one_mem _
  have hPf : P ≤ f.ker := by
    intro x hx
    have hx' : x ∈ (pCoreOf 2 H).subgroupOf H := by
      rw [CFSG.Quasithin.subgroupOf_pCoreOf_eq]
      exact hx
    rw [MonoidHom.mem_ker, hf, convHom_apply, convI_eq_one_iff]
    exact hO (mem_subgroupOf.1 hx')
  set fbar := QuotientGroup.lift P f hPf with hfbar
  set g := fbar.comp L.subtype with hg
  have hgO : CFSG.oddCore ↥L ≤ g.ker := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := y.2
    have hxK : (x : G) ∈ K₀ := mem_subgroupOf.1 hx
    have hko : QuotientGroup.mk' P ⟨(x : G), hK₀H hxK⟩ ∈
        (CFSG.oddCore ↥L).map L.subtype := ⟨y, hy, hxy.symm⟩
    have hkU := hcent (mem_solvableRadical_of_mk_mem_oddCore hK₀H hxK hko)
    rw [MonoidHom.mem_ker]
    show fbar (y : ↥H ⧸ P) = 1
    rw [← hxy]
    show f x = 1
    rw [hf, convHom_apply, convI_eq_one_iff]
    exact hkU
  set gbar := QuotientGroup.lift (CFSG.oddCore ↥L) g hgO with hgbar
  obtain ⟨e₁⟩ := hSL
  set ψ₀ := gbar.comp e₁.symm.toMonoidHom with hψ₀
  have hrange : ψ₀.range = autI hU K₀ := by
    ext φ
    rw [autI_eq_map_convHom hU hHN hK₀H]
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e₁.symm s)
      obtain ⟨x, hx, hxy⟩ := y.2
      refine ⟨x, hx, ?_⟩
      show f x = gbar (e₁.symm s)
      rw [← hy]
      show f x = fbar (y : ↥H ⧸ P)
      rw [← hxy]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e₁ (QuotientGroup.mk (⟨QuotientGroup.mk' P x, x, hx, rfl⟩ : ↥L)), ?_⟩
      show gbar (e₁.symm (e₁ _)) = f x
      rw [MulEquiv.symm_apply_apply]
      rfl
  exact ⟨(MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict,
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective⟩

theorem card_sq_eq_one_le_two {F : Type*} [Field F] :
    Nat.card {r : F // r ^ 2 = 1} ≤ 2 := by
  classical
  have h : ∀ r : F, r ^ 2 = 1 → r = 1 ∨ r = -1 := fun r hr =>
    mul_self_eq_one_iff.1 (by rw [← pow_two]; exact hr)
  have hinj : Function.Injective fun r : {r : F // r ^ 2 = 1} => decide (r.1 = 1) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only at hab
    apply Subtype.ext
    show a = b
    rcases h a ha with rfl | rfl <;> rcases h b hb with rfl | rfl
    · rfl
    · simp at hab
      exact hab.symm
    · simp at hab
      exact hab
    · rfl
  calc Nat.card {r : F // r ^ 2 = 1} ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem false_of_case22
    (h3214 : Stmt3_2_14) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T K₀ : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀)
    (hTK₀ : T ≤ normalizer (K₀ : Set G)) (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))
    (hJ : K₀ = ⁅K₀, thompsonJ T⁆)
    (hZ : ¬ K₀ ≤ centralizer (quasithinOmegaOneCenter T : Set G)) {p : ℕ} (hp : p.Prime)
    (hp5 : p ^ 2 % 5 = 1) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hSL : IsSL2 p (↥(modO2Image (K₀ ⊔ T) K₀) ⧸ CFSG.oddCore ↥(modO2Image (K₀ ⊔ T) K₀))) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp5' : 5 ≤ p := by
    by_contra h
    push Not at h
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 by omega) with rfl | rfl | rfl
    · norm_num at hp5
    · norm_num at hp5
    · exact absurd hp (by decide)
  set H := K₀ ⊔ T with hH
  set Z := quasithinOmegaOneCenter T with hZdef
  set U := conjClosure Z H with hUdef
  obtain ⟨hred, -⟩ := isTwoReducedIn_conjClosure_omega hQ hT hK₀
  set hU := hred.2.2.1 with hhU
  have hUH : U ≤ H := hred.1
  have hHN : H ≤ normalizer (U : Set G) := hred.2.1
  have hK₀H : K₀ ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hK₀N : K₀ ≤ normalizer (U : Set G) := hK₀H.trans hHN
  have hTN : T ≤ normalizer (U : Set G) := hTH.trans hHN
  have hcent := solvableRadical_le_centralizer_conjClosure h3214 hs hnab hQ hT hK₀ hq
  set W := IntMod U hU with hW
  set Gs := autI hU H with hGsdef
  set Ls := autI hU K₀ with hLsdef
  set Ts := autI hU T with hTsdef
  obtain ⟨ψ, hψ⟩ := exists_surj_SL2_autI hK₀H hred hcent hSL
  have hGs : Gs = Ls ⊔ Ts := autI_sup hU hK₀N hTN
  have hTsN : Ts ≤ normalizer (Ls : Set (MulAut W)) := by
    intro φ hφ
    obtain ⟨t, htT, rfl⟩ := (mem_autI hU).1 hφ
    have ht : (t : G) ∈ normalizer (K₀ : Set G) := hTK₀ htT
    rw [mem_normalizer_iff]
    intro ψ'
    constructor
    · intro hψ'
      obtain ⟨k, hkK, rfl⟩ := (mem_autI hU).1 hψ'
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (mem_autI hU).2 ⟨_, ?_, rfl⟩
      exact (mem_normalizer_iff.1 ht _).1 hkK
    · intro hψ'
      obtain ⟨k, hkK, hk⟩ := (mem_autI hU).1 hψ'
      refine (mem_autI hU).2 ⟨t⁻¹ * k * t, ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.1 (inv_mem ht) _).1 hkK
        simpa using h1
      · rw [map_mul, map_mul, map_inv, hk]
        group
  have hTs2 : IsPGroup 2 Ts := B2F.isPGroup_autI hU hT.1 hTN
  have hO : pCoreOf 2 Gs = ⊥ := C1Pack.pCoreOf_autI_eq_bot hU hred
  have hLsG : Ls ≤ Gs := autI_mono hU hK₀H
  have hGsN : Gs ≤ normalizer (Ls : Set (MulAut W)) := by
    rw [hGs]
    exact sup_le le_normalizer hTsN
  have hLs1 : ∃ l ∈ Ls, l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hZ
    intro k hk
    have hkU : k ∈ centralizer (U : Set G) :=
      (convI_eq_one_iff hU ⟨k, hK₀N hk⟩).1 (hcon _ (convI_mem_autI hU hk (hK₀N hk)))
    exact centralizer_le (le_conjClosure Z H) hkU
  have h4 : ∃ s : Finset (ZMod p), s.card = 4 := by
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨t, ht⟩
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  have hker : ψ.ker ≤ center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSq ψ.normal_ker with h | h
    · exfalso
      obtain ⟨l, hl, hl1⟩ := hLs1
      obtain ⟨s, hs⟩ := hψ ⟨l, hl⟩
      apply hl1
      have hs1 : s ∈ ψ.ker := h ▸ mem_top s
      rw [MonoidHom.mem_ker, hs] at hs1
      exact congrArg Subtype.val hs1
    · exact h
  have hcen := CFSG.LocalCores.comap_center_eq_of_perfect hSq.1 ψ hψ hker
  have hZcard : Nat.card (center ↥Ls) ≤ 2 := by
    have hmap : center ↥Ls = (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map ψ := by
      rw [← hcen, Subgroup.map_comap_eq_self_of_surjective hψ]
    have h1 : Nat.card ↥((center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map ψ) ≤
        Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
      refine Nat.card_le_card_of_surjective
        (fun x => (⟨ψ x, x, x.2, rfl⟩ : ↥((center _).map ψ))) ?_
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [hmap]
    exact h1.trans ((CFSG.RankThree.Classical.card_center_SL2).le.trans card_sq_eq_one_le_two)
  have hZ1 : center ↥Ls = ⊥ := by
    have hZ2 : IsPGroup 2 ↥(center ↥Ls) := by
      have hpos : 0 < Nat.card ↥(center ↥Ls) := Nat.card_pos
      rcases (show Nat.card ↥(center ↥Ls) = 1 ∨ Nat.card ↥(center ↥Ls) = 2 by omega) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
      · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans hLsG) (le_normalizer_center_map hGsN) (hZ2.map Ls.subtype)
    rw [hO, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ Ls.subtype_injective).1 hle
  have hkerZ : center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = ψ.ker := by
    rw [← hcen, hZ1, MonoidHom.comap_bot]
  let θ : ↥Ls ≃* PSL2 (ZMod p) :=
    ((QuotientGroup.quotientMulEquivOfEq hkerZ).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm
  set N := Ls.subgroupOf Gs with hNdef
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hLsG).2 hGsN
  let θ' : ↥N ≃* PSL2 (ZMod p) := (Subgroup.subgroupOfEquivOfLe hLsG).trans θ
  have hC := eq_one_of_centralizes hGs hTsN hTs2 hO hZ1
  obtain ⟨Y, e, hY, he⟩ := aut_structure hp5' θ' hC
  have hN' : ∀ n ∈ N, ((e n : Y) : PGL2 (ZMod p)) ∈ pglS (ZMod p) := fun n hn => by
    rw [show n = ((⟨n, hn⟩ : ↥N) : ↥Gs) from rfl, he ⟨n, hn⟩]
    exact ⟨_, rfl⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w⟩
  let ρ : ↥Gs →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp Gs.subtype
  have hD : IsInvRep ρ (Family.commSub ρ N) := fun g =>
    commSub_inv ρ fun n hn => hNn.conj_mem n hn g
  have hLq : CFSG.IsQuasisimple ↥Ls := CFSG.LocalCores.isQuasisimple_of_surjective hSq ψ hψ hker
  have hNq : CFSG.IsQuasisimple ↥N :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLsG).symm hLq
  have hcomm := commSub_subRep_eq_top ρ hNq.1 hD
  have : Nontrivial ↥(Family.commSub ρ N) := by
    obtain ⟨l, hl, hl1⟩ := hLs1
    obtain ⟨w, hw⟩ : ∃ w : W, l w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hl1 (MulEquiv.ext hcon)
    have hlN : (⟨l, hLsG hl⟩ : ↥Gs) ∈ N := hl
    have hmem : ρ ⟨l, hLsG hl⟩ (Additive.ofMul w) - Additive.ofMul w ∈ Family.commSub ρ N :=
      Submodule.subset_span ⟨_, hlN, Additive.ofMul w, rfl⟩
    refine (Submodule.nontrivial_iff_ne_bot).2 fun hbot => hw ?_
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact congrArg Additive.toMul hmem
  obtain ⟨A, hAT, hAU⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ centralizer (U : Set G) := by
    by_contra hcon
    push Not at hcon
    have hJU : thompsonJ T ≤ centralizer (U : Set G) := iSup₂_le fun A hA => hcon A hA
    apply hZ
    have hcomm' : ⁅K₀, thompsonJ T⁆ ≤ centralizer (U : Set G) := by
      rw [Subgroup.commutator_le]
      intro k hk j hj
      have hjU := hJU hj
      have hkN := B2F.le_normalizer_centralizer hK₀N hk
      have h1 : k * j * k⁻¹ ∈ centralizer (U : Set G) := (mem_normalizer_iff.1 hkN j).1 hjU
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hjU)
    exact hJ.le.trans (hcomm'.trans (centralizer_le (le_conjClosure Z H)))
  have hSH : IsSylowTwoOf T H := ⟨hTH, hT.1, fun h2 => hT.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hAH : IsMaxElemAbelian H A := isMaxElemAbelian_of_isSylowTwoOf hSH hAT
  have hmem : autI hU A ∈ offenderImages hU H := ⟨A, ⟨hAH, hAU⟩, rfl⟩
  have hFF := offenderImages_isFFStarOffender hU hUH hHN hmem
  set As := autI hU A with hAsdef
  have hAsG : As ≤ Gs := hFF.1
  have hWcard : Nat.card W ≤ Nat.card As * Nat.card (fixV As) := by
    have h := hFF.2.2.2 ⊥ bot_le
    have hfix : fixV (⊥ : Subgroup (MulAut W)) = ⊤ :=
      eq_top_iff.2 fun v _ x hx => by rw [mem_bot.1 hx]; rfl
    rwa [Subgroup.card_bot, one_mul, hfix, Subgroup.card_top] at h
  set B := As.subgroupOf Gs with hB
  have hB1 : B ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFF.2.1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAsG a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext (congrArg (fun x : ↥B => ((x : ↥Gs) : MulAut W)) h)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hFF.2.2.1.1 _ ha _ hb)
  have hB2 : ∀ a ∈ B, a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hFF.2.2.1.2 _ ha
    rwa [pow_two] at this
  have hfixB : Nat.card (Family.fixedSub ρ B) = Nat.card (fixV As) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAsG ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ As := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card B = Nat.card As :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAsG).toEquiv
  have hpgrp : IsPGroup 2 B := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 a a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) -
      Module.finrank (ZMod 2) (Family.fixedSub ρ B) ≤ Nat.log 2 (Nat.card B) := by
    refine finrank_sub_le_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfixB]
    exact hWcard
  have hoffD := (finrank_sub_fixedSub_subRep_le ρ (Family.commSub ρ N) hD B).trans hoff
  have h57 := prime_le_seven_of_module_data hp5' (subRep ρ (Family.commSub ρ N) hD) e hY hN'
    hcomm hB1 hBc hB2 hoffD
  rcases h57 with rfl | rfl <;> norm_num at hp5

end CFSG.Quasithin.H13.A7
