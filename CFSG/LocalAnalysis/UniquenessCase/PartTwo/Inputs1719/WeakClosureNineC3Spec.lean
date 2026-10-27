module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CChkSpec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3Pull
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.ChkN

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core
  CFSG.LocalAnalysis.WeakClosure81

variable {n : ℕ}

local notation "PN" => Equiv.Perm (Fin n)

theorem powList_desc {y : PN} {p : ℕ} (hp : p.Prime) (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    DescN (zpowers y) (powList (codeN n y) p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hoy : orderOf y = p := orderOf_eq_prime hyp hy1
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image, powList, List.mem_map, hoy]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, List.mem_range.mpr (Finset.mem_range.mp hk), (codeN_pow y k).symm⟩
    · rintro ⟨k, hk, hkc⟩
      refine ⟨k, Finset.mem_range.mpr (List.mem_range.mp hk), codeN_injective ?_⟩
      rw [codeN_pow, hkc]
  · rw [powList, List.mem_map] at hc
    obtain ⟨k, -, rfl⟩ := hc
    exact ⟨y ^ k, pow_mem (mem_zpowers y) k, codeN_pow y k⟩

theorem pCoreOf_le_of_isSylowIn {G : Type*} [Group G] [Finite G] {K S : Subgroup G}
    (hS : IsSylowIn 2 S K) : pCoreOf 2 K ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hS.le_of_normal (map_subtype_le _) ?_ (CFSG.pCore_isPGroup.map K.subtype)
  have h1 : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 K := by
    unfold pCoreOf
    exact subgroupOf_map_subtype_eq_self _
  rw [h1]
  exact CFSG.pCore_normal

theorem conj_mem_pCoreOf {G : Type*} [Group G] {K : Subgroup G} {k e : G} (hk : k ∈ K)
    (he : e ∈ pCoreOf 2 K) : k * e * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨e', he', rfl⟩ := he
  have := CFSG.pCore_normal (p := 2) (G := K)
  exact ⟨⟨k, hk⟩ * e' * ⟨k, hk⟩⁻¹, this.conj_mem e' he' ⟨k, hk⟩, rfl⟩

variable {T₀ : Subgroup (Equiv.Perm (Fin n))} {TL TLinv : List (List ℕ)}

theorem conjProd_mem (hT : DescN T₀ TL) (hinv : invCheckN n TL TLinv = true) {y : PN}
    {w : List (ℕ × ℕ)} (hw : w.all (fun ij => decide (ij.1 < TL.length)) = true) :
    ∃ z ∈ Subgroup.closure ({z | ∃ d ∈ T₀, ∃ x ∈ Subgroup.zpowers y, z = d * x * d⁻¹} : Set PN),
      codeN n z = conjProd n TL TLinv (codeN n y) w := by
  have hlen : TL.length = TLinv.length := by
    simp only [invCheckN, Bool.and_eq_true, beq_iff_eq] at hinv
    exact hinv.1.1
  unfold conjProd
  suffices h : ∀ (w : List (ℕ × ℕ)), w.all (fun ij => decide (ij.1 < TL.length)) = true →
      ∀ x ∈ Subgroup.closure ({z | ∃ d ∈ T₀, ∃ x ∈ Subgroup.zpowers y, z = d * x * d⁻¹} : Set PN),
      ∃ z ∈ Subgroup.closure ({z | ∃ d ∈ T₀, ∃ x ∈ Subgroup.zpowers y, z = d * x * d⁻¹} : Set PN),
        codeN n z = w.foldl (fun acc ij => cmul acc (cmul (cmul (TL.getD ij.1 (List.range n))
          (cpow (codeN n y) ij.2)) (TLinv.getD ij.1 (List.range n)))) (codeN n x) by
    simpa [codeN_one] using h w hw 1 (one_mem _)
  intro w
  induction w with
  | nil => intro _ x hx; exact ⟨x, hx, rfl⟩
  | cons ij w ih =>
    intro hw x hx
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hi, hw⟩ := hw
    have hmem : (TL.getD ij.1 (List.range n), TLinv.getD ij.1 (List.range n)) ∈ TL.zip TLinv := by
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (hlen ▸ hi)]
      exact List.mem_iff_getElem.mpr ⟨ij.1, by simp [hi, hlen ▸ hi], by simp⟩
    obtain ⟨d, hd, hdc, hdic⟩ := invCheck_specN hT hinv hmem
    simp only [List.foldl_cons]
    rw [← hdc, ← hdic, ← codeN_pow, ← codeN_mul, ← codeN_mul, ← codeN_mul]
    refine ih hw _ (mul_mem hx (subset_closure ⟨d, hd, y ^ ij.2, pow_mem (mem_zpowers y) _, ?_⟩))
    rfl

theorem kdata_spec {G : Subgroup PN} (hT : DescN T₀ TL) (hT2 : IsPGroup 2 T₀) {D : KData}
    (hD : KData.checkN n D TL = true) (hgens : ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set PN), codeN n x = c) :
    ∃ K : Subgroup PN, K ≤ G ∧ DescN K D.K.lit ∧ ∃ y ∈ K, codeN n y = D.y ∧ D.p.Prime ∧
      y ^ D.p = 1 ∧ y ≠ 1 ∧ TwoPTwoIrred K (K ⊓ T₀) (zpowers y) D.p ∧
      Nat.card (zpowers y) = D.p ∧ ∃ N : Subgroup PN, DescN N D.N2.lit ∧ N ≤ pCoreOf 2 K := by
  obtain ⟨K, hKG, hK, -, ⟨y, hyK, hyc, h2, hZ⟩, N, hN, hNK⟩ := KData.specN hT hT2 hD hgens
  have hpr : D.p.Prime := h2.prime
  have : Fact D.p.Prime := ⟨hpr⟩
  have hoy : orderOf y = D.p := by rw [← Nat.card_zpowers, hZ]
  refine ⟨K, hKG, hK, y, hyK, hyc, hpr, by rw [← hoy, pow_orderOf_eq_one], ?_,
    ⟨h2, NFA6.irred_of_prime_card (by rw [hZ]; exact hpr)⟩, hZ, N, hN, hNK⟩
  intro h1
  rw [h1, orderOf_one] at hoy
  exact hpr.one_lt.ne hoy


theorem DescN.eq {H K : Subgroup (Equiv.Perm (Fin n))} {L : List (List ℕ)} (hH : DescN H L)
    (hK : DescN K L) : H = K := by
  ext x
  rw [hH.mem, hK.mem]

theorem card_le_length {A : Subgroup (Equiv.Perm (Fin n))} {E : List (List ℕ)}
    (h : ∀ x ∈ A, codeN n x ∈ E) : Nat.card A ≤ E.length := by
  classical
  have h1 : codeN n '' (A : Set PN) ⊆ ↑E.toFinset := by
    rintro c ⟨x, hx, rfl⟩
    simpa using h x hx
  calc Nat.card A = Nat.card (codeN n '' (A : Set PN)) :=
        (Nat.card_image_of_injective codeN_injective _).symm
    _ = (codeN n '' (A : Set PN)).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑E.toFinset : Set (List ℕ)).ncard := Set.ncard_le_ncard h1 (Finset.finite_toSet _)
    _ = E.toFinset.card := Set.ncard_coe_finset _
    _ ≤ E.length := List.toFinset_card_le E

theorem exists_descN_of_closed {Lc : List (List ℕ)} (h1 : List.range n ∈ Lc)
    (hmul : ∀ a ∈ Lc, ∀ b ∈ Lc, cmul a b ∈ Lc) (hsq : ∀ a ∈ Lc, cmul a a = List.range n)
    (hsurj : ∀ c ∈ Lc, ∃ x : PN, codeN n x = c) :
    ∃ H : Subgroup PN, DescN H Lc ∧ ∀ x ∈ H, x * x = 1 := by
  have hsq' : ∀ x : PN, codeN n x ∈ Lc → x * x = 1 := fun x hx => by
    rw [← codeN_eq_range_iff, codeN_mul]
    exact hsq _ hx
  refine ⟨{ carrier := {x | codeN n x ∈ Lc}
            mul_mem' := fun {a b} ha hb => by
              show codeN n (a * b) ∈ Lc
              rw [codeN_mul]
              exact hmul _ ha _ hb
            one_mem' := by
              show codeN n 1 ∈ Lc
              rw [codeN_one]
              exact h1
            inv_mem' := fun {a} ha => by
              show codeN n a⁻¹ ∈ Lc
              rw [inv_eq_of_mul_eq_one_right (hsq' a ha)]
              exact ha }, ⟨fun x => Iff.rfl, fun c hc => ?_⟩, fun x hx => hsq' x hx⟩
  obtain ⟨x, rfl⟩ := hsurj c hc
  exact ⟨x, hc, rfl⟩

theorem cmul_codeN_cancel {a b : List ℕ} (ha : a.length = n) (hb : b.length = n) (σ : PN)
    (h : cmul a (codeN n σ) = cmul b (codeN n σ)) : a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro j hja hjb
  have hj : j < n := ha ▸ hja
  have h1 := congrArg (fun c => c.getD (σ⁻¹ ⟨j, hj⟩ : ℕ) 0) h
  simp only [cmul, codeN, List.map_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Fin.is_lt, ↓reduceDIte, Option.getD_some, Function.comp_apply, Fin.eta,
    Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Fin.val_mk] at h1
  rw [List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb] at h1
  simpa using h1

structure Amb (G L₀ T₀ : Subgroup (Equiv.Perm (Fin n))) (M : ModelData) : Prop where
  lgens : ∃ l : List (Equiv.Perm (Fin n)), l.map (codeN n) = M.Lg ∧ L₀ = closure {x | x ∈ l}
  ggens : ∃ g : List (Equiv.Perm (Fin n)), g.map (codeN n) = M.Gg ∧ G = closure {x | x ∈ g}
  descT : DescN T₀ M.T
  two : IsPGroup 2 T₀
  T_le : T₀ ≤ G
  L_le : L₀ ≤ G
  inv : invCheckN n M.T M.Tinv = true

theorem mem_of_words {S : Subgroup PN} {gens : List PN} {gc : List (List ℕ)}
    (hS : S = closure {x | x ∈ gens}) (hgc : gens.map (codeN n) = gc) {cs : List (List ℕ)}
    {ws : List (List ℕ)} (h : cs = ws.map (evalWN n gc)) :
    ∀ c ∈ cs, ∃ x ∈ (S : Set PN), codeN n x = c := by
  intro c hc
  rw [h, List.mem_map] at hc
  obtain ⟨w, -, rfl⟩ := hc
  obtain ⟨x, hx, hxc⟩ := evalWN_spec hgc w
  exact ⟨x, by rw [SetLike.mem_coe, hS]; exact hx, hxc⟩

structure WitOut (G L₀ T₀ : Subgroup (Equiv.Perm (Fin n))) (D : KData) (inL : Bool)
    (K : Subgroup (Equiv.Perm (Fin n))) (y : Equiv.Perm (Fin n)) : Prop where
  le : K ≤ G
  leL : inL = true → K ≤ L₀
  desc : DescN K D.K.lit
  mem : y ∈ K
  code : codeN n y = D.y
  prime : D.p.Prime
  pow : y ^ D.p = 1
  ne : y ≠ 1
  irr : TwoPTwoIrred K (K ⊓ T₀) (zpowers y) D.p
  core : ∃ N : Subgroup (Equiv.Perm (Fin n)), DescN N D.N2.lit ∧ N ≤ pCoreOf 2 K

variable {G L₀ : Subgroup (Equiv.Perm (Fin n))} {M : ModelData}

theorem Amb.witOut (hA : Amb G L₀ T₀ M) {i : ℕ} (hw : witOkN n M i = true) :
    ∃ K y, WitOut G L₀ T₀ (M.Ks.getD i KData.dflt) (!(M.KwL.getD i []).isEmpty) K y := by
  simp only [witOkN, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hw
  obtain ⟨⟨hD, hwG⟩, hwL⟩ := hw
  obtain ⟨gl, hgl, hG⟩ := hA.ggens
  obtain ⟨ll, hll, hL⟩ := hA.lgens
  obtain ⟨K, hKG, hK, y, hyK, hyc, hpr, hyp, hy1, hirr, -, N, hN, hNK⟩ :=
    kdata_spec (G := G) hA.descT hA.two hD (mem_of_words hG hgl hwG)
  refine ⟨K, y, ⟨hKG, fun hin => ?_, hK, hyK, hyc, hpr, hyp, hy1, hirr, N, hN, hNK⟩⟩
  rcases hwL with h | h
  · rw [h] at hin
    exact absurd hin (by decide)
  · obtain ⟨K', hK'L, hK', -⟩ :=
      kdata_spec (G := L₀) hA.descT hA.two hD (mem_of_words hL hll h)
    rw [hK.eq hK']
    exact hK'L

theorem movWit_of_check (hA : Amb G L₀ T₀ M) {D : KData} {K : Subgroup PN} {y : PN}
    (hW : WitOut G L₀ T₀ D true K y) {E : List (List ℕ)} {w : List (ℕ × ℕ)}
    (h : movCheckN n M.T M.Tinv M.Lg D E w = true) {A : Subgroup PN}
    (hAE : ∀ x ∈ A, x = 1 ∨ codeN n x ∈ E) : MovWit914 L₀ T₀ A K (zpowers y) D.p := by
  simp only [movCheckN, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hcf, hnorm⟩, hnt⟩, h3⟩ := h
  obtain ⟨ll, hll, hL⟩ := hA.lgens
  refine ⟨hW.leL rfl, ?_, ?_, hW.irr, CFSG.Open.isElemAbelian_zpowers hW.pow, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    refine centFreeN_spec hW.desc hll hcf hx.1 fun l hl => ?_
    rw [← hL] at hl
    exact (mem_centralizer_iff.mp hx.2 l hl).symm
  · intro a ha
    rcases hAE a ha with rfl | hc
    · exact one_mem _
    · exact normT_specN hW.desc (List.all_eq_true.mp hnorm _ hc) rfl
  · rw [List.any_eq_true] at hnt
    obtain ⟨s, hs, hs2⟩ := hnt
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs2
    obtain ⟨hsn, hsc⟩ := hs2
    obtain ⟨σ, hσ, rfl⟩ := (hW.desc.inf hA.descT).surj s hs
    refine ⟨σ, ⟨hσ, ?_⟩, y, mem_zpowers y, fun heq => ?_⟩
    · rw [← hW.code] at hsn
      exact normT_specN (powList_desc hW.prime hW.pow hW.ne) hsn rfl
    · rw [← hW.code, ccomm_iffN.mpr (mul_inv_eq_iff_eq_mul.mp heq)] at hsc
      exact Bool.noConfusion hsc
  · rcases h3 with h3 | h3
    · exact Or.inl h3
    · right
      simp only [threeCheckN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h3
      obtain ⟨⟨hw, hcube⟩, hne⟩ := h3
      rw [← hW.code] at hcube hne
      obtain ⟨z, hz, hzc⟩ := conjProd_mem hA.descT hA.inv hw (y := y)
      refine ⟨z, hz, ?_⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [← hzc, ← codeN_pow, codeN_eq_range_iff] at hcube
        exact hcube
      · intro h1
        apply hne
        rw [← hzc, h1, codeN_one]

theorem fixWit_of_check (hA : Amb G L₀ T₀ M) {D : KData} {inL : Bool} {K : Subgroup PN}
    {y : PN} (hW : WitOut G L₀ T₀ D inL K y) {E : List (List ℕ)}
    (hET : E.all M.T.contains = true) (h : fixCheckN M.T D E = true) {A : Subgroup PN}
    (hAE : ∀ x, x ∈ A ↔ codeN n x ∈ E) : FixWit914 T₀ A K (zpowers y) 3 := by
  simp only [fixCheckN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hp, hEK⟩, e, he, k, hk, hne⟩ := h
  have hirr := hW.irr
  rw [hp] at hirr
  refine ⟨fun x hx => (hW.desc.mem x).mpr (List.contains_iff_mem.mp (hEK _ ((hAE x).mp hx))),
    fun hle => ?_, hirr, Or.inl rfl⟩
  obtain ⟨ε, -, rfl⟩ := hA.descT.surj e (List.contains_iff_mem.mp (List.all_eq_true.mp hET e he))
  obtain ⟨κ, hκ, rfl⟩ := hW.desc.surj k hk
  have h1 : κ⁻¹ * ε * κ ∈ pCoreOf 2 K := by
    simpa using conj_mem_pCoreOf (K.inv_mem hκ) (hle ((hAE ε).mpr he))
  have h2 : κ⁻¹ * ε * κ ∈ K ⊓ T₀ := pCoreOf_le_of_isSylowIn hirr.sylowTwo h1
  refine hne _ (List.mem_filter.mpr ⟨(hW.desc.mem _).mp h2.1,
    List.contains_iff_mem.mpr ((hA.descT.mem _).mp h2.2)⟩) ?_
  rw [← codeN_mul, ← codeN_mul]
  congr 1
  group

theorem pair_of_check (hA : Amb G L₀ T₀ M) {ξ : PN} {l lw y g gw : List ℕ}
    (h : pairCheckN n M.T M.Lg M.Gg (codeN n ξ) l lw y g gw = true) : PairProp914 L₀ ξ := by
  simp only [pairCheckN, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hg⟩, hylen⟩, hy⟩, ⟨t, ht, hxt⟩⟩, ⟨t', ht', hyt⟩⟩, hc⟩ := h
  obtain ⟨ll, hll, hL⟩ := hA.lgens
  obtain ⟨gl, hgl, -⟩ := hA.ggens
  obtain ⟨a, ha, hac⟩ := evalWN_spec hll lw
  obtain ⟨γ, -, hγc⟩ := evalWN_spec hgl gw
  rw [hl] at hac
  rw [hg] at hγc
  rw [← hL] at ha
  rw [← hac] at hy
  have hyc : y = codeN n (a * ξ * a⁻¹) := by
    refine cmul_codeN_cancel hylen (codeN_length _) a ?_
    rw [hy, ← codeN_mul, ← codeN_mul]
    congr 1
    group
  subst hyc
  obtain ⟨τ, hτ, rfl⟩ := hA.descT.surj t ht
  obtain ⟨τ', hτ', rfl⟩ := hA.descT.surj t' ht'
  rw [← hγc, ← codeN_mul, ← codeN_mul] at hxt hyt
  have hξ : ξ = γ * τ * γ⁻¹ := eq_mul_inv_of_mul_eq (codeN_injective hxt)
  have hη : a * ξ * a⁻¹ = γ * τ' * γ⁻¹ := eq_mul_inv_of_mul_eq (codeN_injective hyt)
  refine ⟨a, ha, ?_, fun heq => ?_⟩
  · refine (hA.two.map (MulAut.conj γ).toMonoidHom).to_le ?_
    rw [closure_le]
    rintro z (hz | hz)
    · rw [hz, hξ]
      exact ⟨τ, hτ, rfl⟩
    · rw [Set.mem_singleton_iff.mp hz, hη]
      exact ⟨τ', hτ', rfl⟩
  · rw [ccomm_iffN.mpr heq] at hc
    exact Bool.noConfusion hc

theorem movStar_of_check (hA : Amb G L₀ T₀ M) {D : KData} {K : Subgroup PN} {y : PN}
    (hW : WitOut G L₀ T₀ D true K y) {E : List (List ℕ)}
    (h : movStarCheckN n M.T M.Tinv M.Lg M.Es0 D E = true) {A Es : Subgroup PN}
    (hAE : ∀ x ∈ A, x = 1 ∨ codeN n x ∈ E) (hEs : DescN Es M.Es0)
    (hEs2 : ∀ x ∈ Es, x * x = 1) : MovStar914 L₀ T₀ Es A := by
  simp only [movStarCheckN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true]
    at h
  obtain ⟨⟨⟨hp, hmov⟩, hnorm⟩, hcomm⟩ := h
  have hmw := movWit_of_check hA hW hmov hAE
  rw [hp] at hmw
  obtain ⟨N, hN, hNK⟩ := hW.core
  refine ⟨K, zpowers y, hmw, fun e he => normT_specN hW.desc (hnorm _ ((hEs.mem e).mp he)) rfl,
    fun e he x hx => ?_⟩
  have hx' : codeN n x ∈ powList D.y 3 := by
    rw [← hp, ← hW.code]
    exact ((powList_desc hW.prime hW.pow hW.ne).mem x).mp hx
  obtain ⟨m, hm, hmc⟩ := hcomm _ hx' _ ((hEs.mem e).mp he)
  obtain ⟨μ, hμ, rfl⟩ := hN.surj m hm
  rw [← codeN_mul, ← codeN_mul, ← codeN_mul] at hmc
  rw [inv_eq_of_mul_eq_one_right (hEs2 e he), codeN_injective hmc, mul_inv_cancel_right]
  exact hNK hμ

theorem close_of_check (hA : Amb G L₀ T₀ M) {D : KData} {inL : Bool} {K : Subgroup PN}
    {y : PN} (hW : WitOut G L₀ T₀ D inL K y) (h : closeCheckN M.T M.Es0 D = true)
    {Es : Subgroup PN} (hEs : DescN Es M.Es0) :
    (∃ Y : Subgroup PN, TwoPTwoIrred K (K ⊓ T₀) Y 3) ∧ Es ≤ pCoreOf 2 K ∧
      T₀ ⊓ centralizer (Es : Set PN) ≤ K := by
  simp only [closeCheckN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hp, hEN⟩, hT⟩ := h
  obtain ⟨N, hN, hNK⟩ := hW.core
  refine ⟨⟨zpowers y, hp ▸ hW.irr⟩, fun e he => hNK ((hN.mem e).mpr
    (List.contains_iff_mem.mp (hEN _ ((hEs.mem e).mp he)))), fun t ht => ?_⟩
  rcases hT _ ((hA.descT.mem t).mp ht.1) with h1 | ⟨s, hs, hsc⟩
  · exact (hW.desc.mem t).mpr (List.contains_iff_mem.mp h1)
  · exfalso
    obtain ⟨σ, hσ, rfl⟩ := hEs.surj s hs
    rw [ccomm_iffN.mpr (mem_centralizer_iff.mp ht.2 σ hσ).symm] at hsc
    exact Bool.noConfusion hsc


theorem entry_facts (hA : Amb G L₀ T₀ M) (hwit : ∀ i < M.Ks.length, witOkN n M i = true)
    {en : CEntry} (hen : entOkN n M en = true) {A : Subgroup PN}
    (hAE : ∀ x, x ∈ A ↔ codeN n x ∈ en.E) :
    (∃ (H Xh : Subgroup PN) (p : ℕ), MovWit914 L₀ T₀ A H Xh p) ∧
    ((M.Es0.isEmpty = false ∧ ∀ x, x ∈ A ↔ codeN n x ∈ M.Es0) ∨
      ∃ (K Xh : Subgroup PN) (p : ℕ), K ≤ G ∧ FixWit914 T₀ A K Xh p) ∧
    (T₀ ≤ normalizer (A : Set PN) → (M.Es0.isEmpty = false ∧ ∀ x, x ∈ A ↔ codeN n x ∈ M.Es0) ∨
      (Nat.card A ≤ 2 ∧ ∀ x ∈ A, x ≠ 1 → PairProp914 L₀ x)) ∧
    (∀ Es : Subgroup PN, DescN Es M.Es0 → (∀ x ∈ Es, x * x = 1) → M.Es0.isEmpty = false →
      A ≤ centralizer (Es : Set PN) → MovStar914 L₀ T₀ Es A) := by
  simp only [entOkN, entryCheckN, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hen
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hET, hmov⟩, hfix⟩, hst⟩, hmc⟩, hfc⟩, hnc⟩, hsc⟩, hmL⟩, hsL⟩ := hen
  have hAE' : ∀ x ∈ A, x = 1 ∨ codeN n x ∈ en.E := fun x hx => Or.inr ((hAE x).mp hx)
  have hsurjA : ∀ c ∈ en.E, ∃ x ∈ A, codeN n x = c := fun c hc => by
    obtain ⟨x, -, rfl⟩ :=
      hA.descT.surj c (List.contains_iff_mem.mp (List.all_eq_true.mp hET c hc))
    exact ⟨x, (hAE x).mpr hc, rfl⟩
  have hsetEq : setEq en.E M.Es0 = true → ∀ x, x ∈ A ↔ codeN n x ∈ M.Es0 := fun h x => by
    rw [hAE, setEq_memN h]
  have hcent : ∀ Es : Subgroup PN, DescN Es M.Es0 → A ≤ centralizer (Es : Set PN) →
      (en.E.any fun e => M.Es0.any fun s => !ccomm e s) = true → False := by
    intro Es hEs hAc h1
    rw [List.any_eq_true] at h1
    obtain ⟨e, he, h2⟩ := h1
    rw [List.any_eq_true] at h2
    obtain ⟨s, hs, h3⟩ := h2
    obtain ⟨ε, hε, rfl⟩ := hsurjA e he
    obtain ⟨σ, hσ, rfl⟩ := hEs.surj s hs
    rw [Bool.not_eq_true', ccomm_iffN.mpr (mem_centralizer_iff.mp (hAc hε) σ hσ).symm] at h3
    exact Bool.noConfusion h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hmov)
    rw [hmL] at hW
    exact ⟨K, zpowers y, _, movWit_of_check hA hW hmc hAE'⟩
  · rcases hfc with ⟨hs, he⟩ | hf
    · exact Or.inl ⟨by simpa using hs, hsetEq he⟩
    · obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hfix)
      exact Or.inr ⟨K, zpowers y, 3, hW.le, fixWit_of_check hA hW hET hf hAE⟩
  · intro hTN
    rcases hnc with (⟨-, hnn⟩ | ⟨⟨-, hs⟩, he⟩) | ⟨⟨-, hlen⟩, hpair⟩
    · exact absurd hTN (nonNormal_specN hA.descT hA.inv hET hnn hAE)
    · exact Or.inl ⟨by simpa using hs, hsetEq he⟩
    · right
      refine ⟨?_, fun x hx hx1 => ?_⟩
      · have := card_le_length (A := A) (E := en.E) fun x hx => (hAE x).mp hx
        omega
      · have h1 := List.all_eq_true.mp hpair _ ((hAE x).mp hx)
        simp only [Bool.or_eq_true, beq_iff_eq] at h1
        rcases h1 with h1 | h1
        · exact absurd (codeN_eq_range_iff.mp h1) hx1
        · exact pair_of_check hA h1
  · intro Es hEs hEs2 hne hAc
    rcases hsc with (h1 | h1) | h1
    · simp [hne] at h1
    · exact (hcent Es hEs hAc h1).elim
    · rcases hsL with (h4 | h4) | h4
      · rw [hne] at h4
        exact Bool.noConfusion h4
      · exact (hcent Es hEs hAc h4).elim
      · obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hst)
        rw [h4] at hW
        exact movStar_of_check hA hW h1 hAE' hEs hEs2

theorem star_facts (hA : Amb G L₀ T₀ M) (hwit : ∀ i < M.Ks.length, witOkN n M i = true)
    (hent : ∀ en ∈ M.Es, entOkN n M en = true) (hseed : seedOkN n M = true)
    (hs : starOkN n M = true) (hne : M.Es0.isEmpty = false) {Es : Subgroup PN}
    (hEs : DescN Es M.Es0) (hEs2 : ∀ x ∈ Es, x * x = 1) :
    Es ≤ T₀ ∧ T₀ ≤ normalizer (Es : Set PN) ∧ IsElemAbelian 2 Es ∧
    (∀ E : Subgroup PN, E ≤ T₀ ⊓ centralizer (Es : Set PN) → IsElemAbelian 2 E →
      MovStar914 L₀ T₀ Es E) ∧
    ∃ K : Subgroup PN, K ≤ G ∧ (∃ Y : Subgroup PN, TwoPTwoIrred K (K ⊓ T₀) Y 3) ∧
      Es ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (Es : Set PN) ≤ K ∧ K ⊔ T₀ = G := by
  simp only [starOkN, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hcl⟩, hnorm⟩, hb⟩, hbL⟩, hbm⟩, hc⟩, hcc⟩, hcg⟩, hcw⟩ := hs
  simp only [seedOkN, Bool.and_eq_true] at hseed
  have hcl' : ∀ a ∈ M.Es0, M.T.contains a = true ∧ cinvolN n a = true ∧
      ∀ b ∈ M.Es0, ccomm a b = true ∧ M.Es0.contains (cmul a b) = true := by
    intro a ha
    have := List.all_eq_true.mp hcl a ha
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨fun x hx => ?_, fun t ht => ?_, ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩,
    fun E hE hEe => ?_, ?_⟩
  · exact (hA.descT.mem x).mpr (List.contains_iff_mem.mp (hcl' _ ((hEs.mem x).mp hx)).1)
  · exact normT_specN hEs (List.all_eq_true.mp hnorm _ ((hA.descT.mem t).mp ht)) rfl
  · apply Subtype.ext
    exact ccomm_iffN.mp ((hcl' _ ((hEs.mem a).mp a.2)).2.2 _ ((hEs.mem b).mp b.2)).1
  · rw [pow_two]
    exact hEs2 x hx
  · rcases seedAll_specN hA.descT hseed.1 hseed.2 (hE.trans inf_le_left) hEe with
      rfl | ⟨Ec, hEc, hEE⟩
    · obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hb)
      rw [hbL] at hW
      exact movStar_of_check hA hW hbm (fun x hx => Or.inl (mem_bot.mp hx)) hEs hEs2
    · obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hEc
      exact (entry_facts hA hwit (hent en hen) hEE).2.2.2 Es hEs hEs2 hne
        (hE.trans inf_le_right)
  · obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hc)
    obtain ⟨hY, hEK, hCK⟩ := close_of_check hA hW hcc hEs
    refine ⟨K, hW.le, hY, hEK, hCK, le_antisymm (sup_le hW.le hA.T_le) ?_⟩
    obtain ⟨gl, hgl, hG⟩ := hA.ggens
    obtain ⟨cl, hcl2, hclS⟩ := exists_list_of_codesN
      (S := ((K ⊔ T₀ : Subgroup PN) : Set PN)) (L := M.clsGens) (fun c hc' => by
        have h1 := List.all_eq_true.mp hcg c hc'
        rw [Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · obtain ⟨x, hx, rfl⟩ := hW.desc.surj c (List.contains_iff_mem.mp h1)
          exact ⟨x, mem_sup_left hx, rfl⟩
        · obtain ⟨x, hx, rfl⟩ := hA.descT.surj c (List.contains_iff_mem.mp h1)
          exact ⟨x, mem_sup_right hx, rfl⟩)
    rw [hG, closure_le]
    intro g hg
    have hgc : codeN n g ∈ M.Gg := by
      rw [← hgl]
      exact List.mem_map_of_mem hg
    rw [beq_iff_eq.mp hcw, List.mem_map] at hgc
    obtain ⟨w, -, hw⟩ := hgc
    obtain ⟨x, hx, hxc⟩ := evalWN_spec hcl2 w
    rw [← codeN_injective (hxc.trans hw)]
    exact ((closure_le _).mpr fun z hz => hclS z hz) hx

theorem coordModel_of_checks (hA : Amb G L₀ T₀ M) (h3 : 3 ∣ Nat.card L₀)
    (hwit : ∀ i < M.Ks.length, witOkN n M i = true) (hent : ∀ en ∈ M.Es, entOkN n M en = true)
    (hseed : seedOkN n M = true) (hbot : botOkN n M = true) (hsq : sqOkN n M = true)
    (hstar : M.Es0.isEmpty = false → starOkN n M = true) :
    ∃ Es : Subgroup PN, Coord3.CoordModel914 G L₀ T₀ Es ∧ (M.Es0.isEmpty = true → Es = ⊥) := by
  obtain ⟨Es, hEsD, hEs2, hEsB⟩ : ∃ Es : Subgroup PN, (M.Es0.isEmpty = false → DescN Es M.Es0) ∧
      (∀ x ∈ Es, x * x = 1) ∧ (M.Es0.isEmpty = true → Es = ⊥) := by
    cases h0 : M.Es0.isEmpty
    · have hs := hstar h0
      simp only [starOkN, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hcl⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
      have hcl' : ∀ a ∈ M.Es0, M.T.contains a = true ∧ cinvolN n a = true ∧
          ∀ b ∈ M.Es0, ccomm a b = true ∧ M.Es0.contains (cmul a b) = true := by
        intro a ha
        have := List.all_eq_true.mp hcl a ha
        simp only [Bool.and_eq_true, List.all_eq_true] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
      obtain ⟨H, hH, hH2⟩ := exists_descN_of_closed (List.contains_iff_mem.mp h1)
        (fun a ha b hb => List.contains_iff_mem.mp ((hcl' a ha).2.2 b hb).2)
        (fun a ha => beq_iff_eq.mp (hcl' a ha).2.1)
        (fun c hc => by
          obtain ⟨x, -, hx⟩ := hA.descT.surj c (List.contains_iff_mem.mp (hcl' c hc).1)
          exact ⟨x, hx⟩)
      exact ⟨H, fun _ => hH, hH2, fun h => Bool.noConfusion h⟩
    · exact ⟨⊥, fun h => Bool.noConfusion h, fun x hx => by rw [mem_bot.mp hx, one_mul],
        fun _ => rfl⟩
  have hseed' := hseed
  simp only [seedOkN, Bool.and_eq_true] at hseed'
  refine ⟨Es, ⟨hA.L_le, hA.T_le, h3, ?_, fun E hET hEe => ?_, fun E hET hEe hne => ?_,
    fun F hFT hFN hFe => ?_, fun hne => ?_⟩, hEsB⟩
  · simp only [sqOkN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsq
    obtain ⟨⟨hT, hw⟩, hne⟩ := hsq
    obtain ⟨d, hd, hdc⟩ := hA.descT.surj _ (List.contains_iff_mem.mp hT)
    obtain ⟨ll, hll, hL⟩ := hA.lgens
    obtain ⟨x, hx, hxc⟩ := evalWN_spec hll M.sqW
    rw [hw, ← hdc] at hxc
    refine ⟨d, ⟨hd, by rw [hL, ← codeN_injective hxc]; exact hx⟩, fun h => hne ?_⟩
    rw [← hdc, ← codeN_pow, h, codeN_one]
  · rcases seedAll_specN hA.descT hseed'.1 hseed'.2 hET hEe with rfl | ⟨Ec, hEc, hEE⟩
    · simp only [botOkN, Bool.and_eq_true, decide_eq_true_eq] at hbot
      obtain ⟨⟨hb, hbL⟩, hbm⟩ := hbot
      obtain ⟨K, y, hW⟩ := hA.witOut (hwit _ hb)
      rw [hbL] at hW
      exact ⟨K, zpowers y, _, movWit_of_check hA hW hbm fun x hx => Or.inl (mem_bot.mp hx)⟩
    · obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hEc
      exact (entry_facts hA hwit (hent en hen) hEE).1
  · rcases seedAll_specN hA.descT hseed'.1 hseed'.2 hET hEe with h | ⟨Ec, hEc, hEE⟩
    · exact absurd h hne
    · obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hEc
      rcases (entry_facts hA hwit (hent en hen) hEE).2.1 with ⟨h0, hx⟩ | hf
      · right
        ext x
        rw [hx, (hEsD h0).mem]
      · exact Or.inl hf
  · by_cases hF : F = ⊥
    · exact Or.inl hF
    rcases seedAll_specN hA.descT hseed'.1 hseed'.2 hFT hFe with h | ⟨Ec, hEc, hFE⟩
    · exact Or.inl h
    · obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hEc
      rcases (entry_facts hA hwit (hent en hen) hFE).2.2.1 hFN with ⟨h0, hx⟩ | ⟨hc, hp⟩
      · right
        left
        ext x
        rw [hx, (hEsD h0).mem]
      · right
        right
        refine ⟨?_, hp⟩
        rcases card_two_or_four_le hFe hF with h | h
        · exact h
        · omega
  · cases h0 : M.Es0.isEmpty
    · exact star_facts hA hwit hent hseed (hstar h0) h0 (hEsD h0) hEs2
    · exact absurd (hEsB h0) hne

end CFSG.LocalAnalysis.WeakClosure81.ChkN
