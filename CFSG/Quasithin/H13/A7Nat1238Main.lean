module

public import CFSG.Quasithin.H13.A7Nat1238Inputs
public import CFSG.Quasithin.H13.A7Nat1238Out
public import CFSG.Quasithin.H13.A7Nat1236Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [Finite G]

theorem isFaithfulLocal_of_le_of_normalizes (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T L K : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsFaithfulLocal T L)
    (hK : quasithinIsLocal T K) (hLK : L ≤ K) (hTL : T ≤ normalizer (L : Set G)) :
    quasithinIsFaithfulLocal T K := by
  obtain ⟨-, hLX⟩ := isFaithfulLocal_iff_isXf.mp hL
  set R := T ⊓ normalizer (K : Set G) with hR
  have hRL : R ≤ normalizer (L : Set G) := inf_le_left.trans hTL
  have hKR : T ⊓ K ≤ R := le_inf inf_le_left (inf_le_right.trans le_normalizer)
  have hRsylK : QuasithinUnique.IsSylowTwoOf R (K ⊔ R) :=
    isSylowTwoOf_sup_of_isLocal hK inf_le_left inf_le_right hKR
  have hXK : IsXClass K := isXClass_of_isLocal hQ hT hK
  have hO2K : pCoreOf 2 (K ⊔ R) ≤ R :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsylK
  have hA : A410Hyp L K R :=
    { xclass := hLX.1
      yclass := hXK
      xy := hLK
      normalizes := inf_le_right
      sylowT := hRsylK
      o2le := le_inf hO2K (hO2K.trans hRL)
      sylowNT := by
        rw [inf_eq_left.mpr hRL]
        exact A4.isSylowTwoOf_mono hRsylK (le_inf le_sup_right hRL) inf_le_left }
  exact isFaithfulLocal_iff_isXf.mpr ⟨hK, a4_10_3 hA hLX⟩

theorem exists_maximalLocal_ge {T K : Subgroup G} (hK : quasithinIsLocal T K) :
    ∃ K₀, quasithinIsMaximalLocal T K₀ ∧ K ≤ K₀ := by
  obtain ⟨K₀, hK₀⟩ := (Set.toFinite {X : Subgroup G | quasithinIsLocal T X ∧ K ≤ X}).exists_maximal
    ⟨K, hK, le_rfl⟩
  refine ⟨K₀, ⟨hK₀.1.1, fun X hX hK₀X => ?_⟩, hK₀.1.2⟩
  exact le_antisymm (hK₀.2 ⟨hX, hK₀.1.2.trans hK₀X⟩ hK₀X) hK₀X

omit [Finite G] in
theorem omegaOneCenter_le_of_charTwo {T X : Subgroup G} (hTX : T ≤ X)
    (hPT : pCoreOf 2 X ≤ T) (hX : QuasithinUnique.CharTwo X) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (pCoreOf 2 X) := by
  refine (closure_le _).2 fun z hz => subset_closure ⟨?_, hz.2⟩
  obtain ⟨⟨hzT, hzC⟩, -⟩ := hz
  have hzc : z ∈ centralizer (pCoreOf 2 X : Set G) := centralizer_le hPT hzC
  exact ⟨hX ⟨hTX hzT, hzc⟩, hzc⟩

theorem eq_commutator_thompsonJ_of_le {T Ke K₀ : Subgroup G}
    (hK₀ : quasithinIsCComponent K₀ (K₀ ⊔ T)) (hTK₀ : T ≤ normalizer (K₀ : Set G))
    (hKe : Ke ≤ K₀) (hKe1 : Ke ≠ ⊥) (hKep : ⁅Ke, Ke⁆ = Ke) (hKeJ : Ke = ⁅Ke, thompsonJ T⁆) :
    K₀ = ⁅K₀, thompsonJ T⁆ := by
  set N := ⁅K₀, thompsonJ T⁆ with hN
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hNK₀ : N ≤ K₀ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).1 (hJT.trans hTK₀)
  have hKeN : Ke ≤ N := by
    rw [hKeJ]
    exact Subgroup.commutator_mono hKe le_rfl
  have hK₀N : K₀ ≤ normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left _ _
  set P := perfectCore N with hP
  have hKeP : Ke ≤ P := le_perfectCore_of_perfect hKeN hKep
  have hPK₀ : P ≤ K₀ := (perfectCore_le N).trans hNK₀
  have hK₀P : K₀ ≤ normalizer (P : Set G) := hK₀N.trans (normalizer_le_normalizer_perfectCore N)
  have hPeq : P = K₀ := by
    by_contra hne
    have hlt : P < K₀ := lt_of_le_of_ne hPK₀ hne
    refine hK₀.2.2.2 P hlt (fun h0 => hKe1 (le_bot_iff.1 (h0 ▸ hKeP))) (perfectCore_perfect N) ?_
    exact IsSubnormal.step hPK₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK₀).2 hK₀P)
      hK₀.2.2.1
  exact le_antisymm (hPeq ▸ perfectCore_le N) hNK₀

section Main

variable {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7_centralizer_le_two
    (h1225 : Stmt12_2_5)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hgap : Gap1237KeJ) (hNQ : Insp1238NonQ)
    (hIQ : Insp1238Q) (hIY : Insp1238Y) (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ)
    {e : V} (he : vec ψ e = vecFS) (hS : Setting1238 hyp ψ e)
    (hwt6 : ∀ x : V, hammingNorm (vec ψ x) = 6 →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {y : V} (hyZ : (y : G) ∈ quasithinOmegaOneCenter T) (hy4 : hammingNorm (vec ψ y) = 4) :
    centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.simple
  set M := normalizer (L : Set G) with hMdef
  set Ke := Kv hyp e with hKedef
  set H := hyp.Gv e with hHdef
  have he2 := orderOf_eq_two_of_vecFS he
  have he1 : (e : G) ≠ 1 := fun h1 => by simp [h1] at he2
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hS.mem) t ht))
  obtain ⟨-, hMeN, -, -, -⟩ := h1225 G T L V hyp e e.2 he1
  have hMeK : hyp.Mv e ≤ normalizer (Ke : Set G) :=
    hMeN.trans (normalizer_le_normalizer_perfectCore _)
  have hTK : T ≤ normalizer (Ke : Set G) := T_le_normalizer_Kv hyp h1225 e.2 he1 hS.mem
  obtain ⟨-, hKeA5⟩ := Kv_quasisimple hyp h he
  have hKeF := Kv_mem_lFamily hyp h he hTK
  have hKeloc := Kv_isLocal hyp h he hTK hS.mem
  have hKeFL := Kv_isFaithfulLocal hyp h he hTK hS.mem
  have hKeJ := hgap G T L V hyp ψ e hS
  have hKeH : Ke ≤ H := Kv_le_centralizer hyp e
  have hKeM : Ke ≤ M := (Kv_le_L hyp e).trans le_normalizer
  have hKep : ⁅Ke, Ke⁆ = Ke := Kv_perfect hyp e
  have hKe1 : Ke ≠ ⊥ := hKeF.1
  obtain ⟨v, hvW, hv⟩ := exists_weight_four_mem_commutator hyp h he
  have hev : centralizer ({((e * v : V) : G)} : Set G) ≤ M := hwt6 (e * v) (by
    rw [vec_mul, he, hv]
    exact hammingNorm_vecFS_add_vecQuad)
  have hCv : H ⊓ centralizer ({(v : G)} : Set G) ≤ M := by
    intro c hc
    apply hev
    have hce' : c * (e : G) = e * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1
    have hcv' : c * (v : G) = v * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
    refine mem_centralizer_singleton_iff.2 ?_
    show c * ((e : G) * v) = (e : G) * v * c
    rw [← mul_assoc, hce', mul_assoc, hcv', mul_assoc]
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hH2 : pCoreOf 2 H ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer he2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  have hSylH : QuasithinUnique.IsSylowTwoOf T H := isSylowTwoOf_of_le hyp.sylow hTe
  obtain ⟨K, ⟨hK, hKeK⟩, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_existsUnique hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h39 hH2 hSylH hKeH hKeF
  have hKn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds hH2 hSylH hKeF hKeK hK hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKeK' : Ke = K := by
    by_contra hne
    have hlt : Ke < K := lt_of_le_of_ne hKeK hne
    have hKM : ¬ K ≤ M := by
      intro hKM
      have hn : (Ke.subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKeK).2 ((le_inf hKM hKH).trans hMeK)
      exact hK.2.2.2 _ hlt hKe1 hKep (IsSubnormal.step hKeK hn (subnormal_of_mem_cComp hK))
    have hKloc : quasithinIsLocal T K :=
      ⟨hyp.sylow.1, cComp_mem_of_le hK le_sup_left (sup_le hKH hTe),
        (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
        pCoreOf_ne_bot_of_le_centralizer he2 ((le_sup_right : T ≤ K ⊔ T) (h.le_T e.2))
          (sup_le hKH hTe)⟩
    obtain ⟨K₀, hK₀max, hKK₀⟩ := exists_maximalLocal_ge hKloc
    have hK₀loc := hK₀max.1
    have hKeK₀ : Ke ≤ K₀ := hKeK.trans hKK₀
    have hK₀f : quasithinIsFaithfulLocal T K₀ :=
      isFaithfulLocal_of_le_of_normalizes hyp.qtke hyp.sylow hKeFL hK₀loc hKeK₀ hTK
    have hTK₀ : T ≤ normalizer (K₀ : Set G) := by
      have h1 := lemma_1_2_8_one_le hyp.qtke hyp.simple hyp.nonabelian
        (a37ForSQTK_of_cat QuasithinUnique.Vol2Native.a37ForSQTKCat_proved) hKeloc hK₀loc hKeK₀
      exact fun t ht => (h1 ⟨ht, hTK ht⟩).2
    set V₀ := omegaOneCenterOf (pCoreOf 2 (K₀ ⊔ T)) with hV₀def
    obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
      ⟨_, IsPGroup.toSylow_coe hyp.sylow.1 hyp.sylow.2⟩
    have hInH : InH (Ts : Subgroup G) (K₀ ⊔ T) := by
      rw [hTs]
      exact ⟨le_sup_right, hK₀loc.2.2.2⟩
    have hK₀T2 : QuasithinUnique.CharTwo (K₀ ⊔ T) := charTwo_of_inH hyp.qtke.2.1 Ts hInH
    have hZV₀ : quasithinOmegaOneCenter T ≤ V₀ :=
      omegaOneCenter_le_of_charTwo le_sup_right
        (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
          (isSylowTwoOf_of_le hyp.sylow le_sup_right)) hK₀T2
    have hV₀ : ¬ K₀ ≤ centralizer (V₀ : Set G) := by
      intro hc
      obtain ⟨k, hkK, hk⟩ := exists_commutator_ne_one_of_weight_four hyp h he hy4
      apply hk
      have h1 : (k : G) ∈ centralizer (V₀ : Set G) := hc (hKeK₀ hkK)
      have h2 : (y : G) * k = k * y := mem_centralizer_iff.1 h1 y (hZV₀ hyZ)
      rw [h2]
      group
    have hK₀J : K₀ = ⁅K₀, thompsonJ T⁆ :=
      eq_commutator_thompsonJ_of_le hK₀loc.2.1 hTK₀ hKeK₀ hKe1 hKep hKeJ
    by_cases hq : CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)
    · rcases hIQ G T L V hyp ψ e hS h he y hyZ hy4 K K₀ hK hKeK hKK₀ hK₀max hK₀f hq hK₀J hV₀ with
        h1 | ⟨-, hgen⟩
      · exact hne h1
      · apply hKM
        refine (hgen v hvW (by rw [hv]; decide)).trans ((closure_le M).2 ?_)
        rintro x (hx | ⟨hxK, hxv⟩)
        · exact hKeM hx
        · exact hCv ⟨hKH hxK, hxv⟩
    · have hK₀Z : ¬ K₀ ≤ centralizer (quasithinOmegaOneCenter T : Set G) := by
        intro hc
        obtain ⟨k, hkK, hk⟩ := exists_commutator_ne_one_of_weight_four hyp h he hy4
        apply hk
        have h1 : (k : G) ∈ centralizer (quasithinOmegaOneCenter T : Set G) := hc (hKeK₀ hkK)
        have h2 : (y : G) * k = k * y := mem_centralizer_iff.1 h1 y hyZ
        rw [h2]
        group
      have h1 := hNQ G T L V hyp ψ e hS hKeF K₀ hKeK₀ hK₀loc hTK₀ hq hK₀J hK₀Z
      have hC : K₀ ⊓ centralizer (quasithinOmegaOneCenter T : Set G) ≤
          normalizer (Ke : Set G) := by
        rintro c ⟨-, hcZ⟩
        have hce : c ∈ H := centralizer_le (Set.singleton_subset_iff.2 hS.mem) hcZ
        exact hMeK ⟨hS.cz hcZ, hce⟩
      have hK₀N : K₀ ≤ normalizer (Ke : Set G) := h1.trans (sup_le hC le_normalizer)
      have hn : (Ke.subgroupOf K₀).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKeK₀).2 hK₀N
      exact hK₀loc.2.1.2.2.2 Ke (lt_of_lt_of_le hlt hKK₀) hKe1 hKep
        (IsSubnormal.step hKeK₀ hn hK₀loc.2.1.2.2.1)
  rw [← hKeK'] at hKn
  set Y := centralizerSection H Ke (pCoreOf 2 Ke) with hYdef
  have hYW := hIY G T L V hyp ψ e hS h he y hyZ hy4 hTK hKn hKeJ
  have hYM : Y ≤ M := by
    intro c hc
    exact hCv (mem_inf.2 ⟨centralizerSection_le_left _ _ _ hc,
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hYW hc)) v hvW).symm⟩)
  have hHK : H ≤ normalizer (Ke : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKeH).1 hKn
  exact (le_sup_centralizerSection_sup_of_A5 hKeH hHK hKep hKeA5 hSylH).trans
    (sup_le (sup_le hKeM hYM) hyp.normalizes)

end Main

section Coords

variable {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

omit [Finite G] in
theorem hammingNorm_vec_eq_of_coords {ψ' : V ≃* Multiplicative (evenWeight 7)}
    (hLV : L ≤ normalizer (V : Set G))
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hLact' : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ' l σ) (x : V) :
    hammingNorm (vec ψ' x) = hammingNorm (vec ψ x) := by
  classical
  set f : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2 := fun u =>
    if hu : u ∈ evenWeight 7 then vec ψ' (ψ.symm (Multiplicative.ofAdd ⟨u, hu⟩)) else 0 with hf
  have hfv : ∀ y : V, f (vec ψ y) = vec ψ' y := by
    intro y
    rw [hf]
    dsimp only
    rw [dite_eq_left (vec_mem ψ y)]
    congr 1
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hfE : ∀ u ∈ evenWeight 7, f u ∈ evenWeight 7 := by
    intro u hu
    obtain ⟨y, rfl⟩ := exists_vec_eq ψ hu
    rw [hfv]
    exact vec_mem ψ' y
  have hfadd : ∀ u ∈ evenWeight 7, ∀ u' ∈ evenWeight 7, f (u + u') = f u + f u' := by
    intro u hu u' hu'
    obtain ⟨y, rfl⟩ := exists_vec_eq ψ hu
    obtain ⟨y', rfl⟩ := exists_vec_eq ψ hu'
    rw [← vec_mul, hfv, hfv, hfv, vec_mul]
  have hfinj : ∀ u ∈ evenWeight 7, f u = 0 → u = 0 := by
    intro u hu h0
    obtain ⟨y, rfl⟩ := exists_vec_eq ψ hu
    rw [hfv, vec_eq_zero_iff] at h0
    rw [h0, vec_one]
  have hfsurj : ∀ u ∈ evenWeight 7, ∃ u' ∈ evenWeight 7, f u' = u := by
    intro u hu
    obtain ⟨y, rfl⟩ := exists_vec_eq ψ' hu
    exact ⟨vec ψ y, vec_mem ψ y, hfv y⟩
  have hfn : ∀ σ ∈ alternatingGroup (Fin 7), ∃ σ' ∈ alternatingGroup (Fin 7),
      ∀ u ∈ evenWeight 7, f (permAct7 σ u) = permAct7 σ' (f u) := by
    intro σ hσ
    obtain ⟨l, hl, hlσ⟩ := hLonto σ hσ
    obtain ⟨σ', hσ', hlσ'⟩ := hLact' l hl
    refine ⟨σ', hσ', fun u hu => ?_⟩
    obtain ⟨y, rfl⟩ := exists_vec_eq ψ hu
    have hz : (l : G) * y * l⁻¹ ∈ V := (mem_normalizer_iff.1 (hLV hl) y).1 y.2
    rw [← hlσ y ⟨_, hz⟩ rfl, hfv, hfv, hlσ' y ⟨_, hz⟩ rfl]
  obtain ⟨τ, hτ⟩ := exists_perm_of_normalizes_alternating hfE hfadd hfinj hfsurj hfn
  rw [← hfv x, hτ _ (vec_mem ψ x), hammingNorm_permAct7]

theorem vecFS_eq : vecFS = Pi.single 5 1 + Pi.single 6 1 := by
  decide

theorem exists_perm_permAct7_eq_vecFS {w : Fin 7 → ZMod 2} (hw : hammingNorm w = 2) :
    ∃ τ : Perm (Fin 7), permAct7 τ w = vecFS := by
  classical
  have hw' : (Finset.univ.filter fun i => w i ≠ 0).card = 2 := hw
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.1 hw'
  have hmem : ∀ k, w k ≠ 0 ↔ k = i ∨ k = j := by
    intro k
    have := congrArg (k ∈ ·) hset
    simpa using this
  have hwij : w = Pi.single i 1 + Pi.single j 1 := by
    funext k
    by_cases hki : k = i
    · subst hki
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
      exact zmod_two_eq_one_of_ne_zero _ ((hmem k).2 (Or.inl rfl))
    · by_cases hkj : k = j
      · subst hkj
        rw [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_same, zero_add]
        exact zmod_two_eq_one_of_ne_zero _ ((hmem k).2 (Or.inr rfl))
      · rw [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero]
        by_contra hne
        rcases (hmem k).1 hne with h | h
        · exact hki h
        · exact hkj h
  have hpa : ∀ τ : Perm (Fin 7), permAct7 τ w = Pi.single (τ i) 1 + Pi.single (τ j) 1 := by
    intro τ
    rw [hwij, map_add, permAct7_single, permAct7_single]
  by_cases hj5 : j = 5
  · subst hj5
    refine ⟨swap i 6, ?_⟩
    rw [hpa, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hij) (by decide), vecFS_eq,
      add_comm]
  · refine ⟨swap j 6 * swap i 5, ?_⟩
    rw [hpa, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hj5) (by decide), swap_apply_of_ne_of_ne (Ne.symm hij) hj5,
      swap_apply_left, vecFS_eq]

omit [Finite G] in
theorem A7NatPre.exists_relabel_vecFS (h : A7NatPre T L V ψ) {e : V}
    (he : hammingNorm (vec ψ e) = 2) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7), A7NatPre T L V ψ' ∧ vec ψ' e = vecFS ∧
      ∀ x : V, hammingNorm (vec ψ' x) = hammingNorm (vec ψ x) := by
  obtain ⟨τ, hτ⟩ := exists_perm_permAct7_eq_vecFS he
  exact ⟨ψ.trans (relabelE τ), h.relabel τ, by rw [vec_trans_relabelE]; exact hτ,
    fun x => hammingNorm_vec_trans_relabelE ψ τ x⟩

end Coords

theorem stmt12_3_8_of_inputs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h1225 : Stmt12_2_5)
    (h1236 : Stmt12_3_6) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hgap : Gap1237KeJ)
    (hNQ : Insp1238NonQ) (hIQ : Insp1238Q) (hIY : Insp1238Y) : Stmt12_3_8 := by
  intro G _ _ T L V hyp hA7 ψ hLact hLonto e heZ hew
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ :=
    ⟨hVT, hLV, hTV, hLact, hLonto, nact_of_lact hLV hLact hLonto hNM, hNM, hTI⟩
  obtain ⟨ψa, ha, hcent⟩ := hpre.exists_aligned_central hyp.sylow
  have hZ : ∀ x : V, (x : G) ∈ centralizer (T : Set G) → (x : G) ∈ quasithinOmegaOneCenter T :=
    fun x hx => mem_omegaOneCenter_of_central hVT hx (by
      rw [pow_two]
      exact congrArg Subtype.val (sq_eq_one_of_vec ψ x))
  obtain ⟨x6, hx6, hx6c⟩ := hcent 6 (Or.inr (Or.inr rfl))
  obtain ⟨y4, hy4, hy4c⟩ := hcent 4 (Or.inr (Or.inl rfl))
  obtain ⟨ψ', h', he', hw'⟩ := hpre.exists_relabel_vecFS hew
  have hwt : ∀ x : V, hammingNorm (vec ψ' x) = hammingNorm (vec ψa x) := fun x =>
    hammingNorm_vec_eq_of_coords hLV ha.Lonto h'.Lact x
  have hx6' : hammingNorm (vec ψ' x6) = 6 := (hwt x6).trans hx6
  have hy4' : hammingNorm (vec ψ' y4) = 4 := (hwt y4).trans hy4
  have hC6 := h1236 G T L V hyp hA7 ψ' h'.Lact h'.Lonto x6 (hZ x6 hx6c) hx6'
  have hwt6 : ∀ x : V, hammingNorm (vec ψ' x) = 6 →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) :=
    fun x hx => h'.centralizer_le_of_weight hx6' hC6 hx
  have hcz : centralizer (quasithinOmegaOneCenter T : Set G) ≤ normalizer (L : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.2 (hZ x6 hx6c))).trans hC6
  have hS : Setting1238 hyp ψ' e :=
    ⟨hA7, h'.Lact, h'.Lonto, hcz, heZ, by rw [he']; exact hammingNorm_vecFS⟩
  exact A7_centralizer_le_two h1225 h39 hgap hNQ hIQ hIY hyp h' he' hS hwt6 (hZ y4 hy4c) hy4'

end CFSG.Quasithin.H13.A7
