module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRest12RegSplitTorAUniv12

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

theorem kgLangLT1_decomp {p : ℕ} (hp : p.Prime) {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {J S : Subgroup (MulAut R)} (hJS : J ≤ S)
    (hN : (J.subgroupOf S).Normal) (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian p A) (hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S)
    {α₀ : MulAut K} (hα₀ : α₀ ∈ A) (hα₀J : kgInducedAut θ α₀ ∉ J) :
    ∀ α ∈ A, ∃ k : ℕ, kgInducedAut θ (α * (α₀ ^ k)⁻¹) ∈ J := by
  let f := kgInducedAut θ
  let U₁ : Subgroup (MulAut K) := A ⊓ J.comap f
  have hmain := ggCyclicSplit hp (G := MulAut K) (M := MulAut R) (U := A) (U₁ := U₁)
    inf_le_left (fun u hu => hA.2 u hu) (f.comp A.subtype) hN hcyc
    (fun u => hAS (u : MulAut K) u.2) (fun u => by
      show (u : MulAut K) ∈ A ⊓ J.comap f ↔ f (u : MulAut K) ∈ J
      rw [Subgroup.mem_inf, Subgroup.mem_comap, and_iff_right u.2])
  intro α hα
  obtain ⟨k, hk⟩ := hmain.2 α₀ hα₀ (fun h => hα₀J h.2) α hα
  have hkf : f (α * α₀ ^ k) ∈ J := hk.2
  have hzy : f α * (f α₀) ^ k ∈ J := by
    simpa only [map_mul, map_zpow] using hkf
  have hy_pow : (f α₀) ^ p = 1 := by
    rw [← map_pow, hA.2 α₀ hα₀, map_one]
  let m : ℕ := ((-k) % (p : ℤ)).toNat
  have hm : (m : ℤ) = (-k) % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (-k) (by exact_mod_cast hp.ne_zero))
  have hy_emod : (f α₀) ^ (-k) = (f α₀) ^ m := by
    rw [zpow_eq_zpow_emod' (-k) hy_pow, ← hm, zpow_natCast]
  have hkey : (f α₀) ^ k = ((f α₀) ^ m)⁻¹ := by
    rw [← hy_emod, zpow_neg, inv_inv]
  have hz : f α * ((f α₀) ^ m)⁻¹ ∈ J := by
    rwa [hkey] at hzy
  refine ⟨m, ?_⟩
  have hfinal : f (α * (α₀ ^ m)⁻¹) = f α * ((f α₀) ^ m)⁻¹ := by
    rw [map_mul, map_inv, map_pow]
  show f (α * (α₀ ^ m)⁻¹) ∈ J
  rw [hfinal]
  exact hz

private theorem kgLangDatumAux_fin_range_prod_eq_list {A : Type*} [CommMonoid A] (p : ℕ)
    (f : ℕ → A) : Finset.prod (Finset.range p) f = ((List.range p).map f).prod := by
  induction p with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, List.range_succ, List.map_append, List.prod_append, ih]
      simp

private theorem kgLangDatumAux_list_prod_shift {A : Type*} [CommMonoid A] (p : ℕ) (F : ℕ → A)
    (hp : F p = F 0) :
    ((List.range p).map (fun i => F (i + 1))).prod = ((List.range p).map F).prod := by
  rcases p with _ | n
  · simp
  · have hL : (List.range (n + 1)).map (fun i => F (i + 1))
        = ((List.range n).map (fun i => F (i + 1))) ++ [F (n + 1)] := by
      rw [List.range_succ, List.map_append]
      rfl
    have hR : (List.range (n + 1)).map F
        = F 0 :: ((List.range n).map (fun i => F (i + 1))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    rw [hL, hR, List.prod_append, List.prod_cons]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [hp]
    exact mul_comm _ _

theorem kgLangLT3_norms {p : ℕ} {K : Type} [Group K] [Finite K] {M : Subgroup K}
    (hM : ∀ a ∈ M, ∀ c ∈ M, a * c = c * a) {β : MulAut K} (hβp : β ^ p = 1)
    (hβM : ∀ t : K, β t ∈ M ↔ t ∈ M)
    (h90 : ∀ c ∈ M, ((List.range p).map fun i => (β ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * β s) :
    ∀ t ∈ M, β t = t → ∃ s ∈ M, t = ((List.range p).map fun i => (β ^ i) s).prod := by
  letI : CommGroup M := CommGroup.mk fun a b => Subtype.ext (hM a a.2 b b.2)
  have hβmem : ∀ (i : ℕ) {x : K}, x ∈ M → (β ^ i) x ∈ M := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih =>
        intro x hx
        rw [pow_succ', MulAut.mul_apply]
        exact (hβM ((β ^ i) x)).mpr (ih hx)
  let φ : ℕ → M →* M := fun i =>
    { toFun := fun s => ⟨(β ^ i) (s : K), hβmem i s.2⟩
      map_one' := Subtype.ext (map_one (β ^ i))
      map_mul' := fun s t => Subtype.ext (map_mul (β ^ i) (s : K) (t : K)) }
  let βM : M →* M :=
    { toFun := fun s => ⟨β (s : K), (hβM (s : K)).mpr s.2⟩
      map_one' := Subtype.ext (map_one β)
      map_mul' := fun s t => Subtype.ext (map_mul β (s : K) (t : K)) }
  let L : M →* M :=
    { toFun := fun s => s⁻¹ * βM s
      map_one' := by simp
      map_mul' := fun s t => by
        show (s * t)⁻¹ * βM (s * t) = (s⁻¹ * βM s) * (t⁻¹ * βM t)
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  let N : M →* M := Finset.prod (Finset.range p) φ
  have hFsucc : ∀ (s : M) (i : ℕ), βM (φ i s) = φ (i + 1) s := by
    intro s i
    apply Subtype.ext
    show β ((β ^ i) (s : K)) = (β ^ (i + 1)) (s : K)
    rw [pow_succ', MulAut.mul_apply]
  have hN_list : ∀ s : M, N s = ((List.range p).map (fun i => φ i s)).prod := by
    intro s
    show Finset.prod (Finset.range p) φ s = ((List.range p).map (fun i => φ i s)).prod
    rw [MonoidHom.finset_prod_apply]
    exact kgLangDatumAux_fin_range_prod_eq_list p (fun i => φ i s)
  have hN_eval : ∀ s : M,
      (N s : K) = ((List.range p).map fun i => (β ^ i) (s : K)).prod := by
    intro s
    rw [hN_list s, Subgroup.val_list_prod, List.map_map]
    rfl
  have hβN : ∀ s : M, βM (N s) = N s := by
    intro s
    have hFp : (fun i => φ i s) p = (fun i => φ i s) 0 := by
      show φ p s = φ 0 s
      apply Subtype.ext
      show (β ^ p) (s : K) = (β ^ 0) (s : K)
      rw [hβp]
      simp
    calc βM (N s)
        = βM (((List.range p).map (fun i => φ i s)).prod) := by rw [hN_list s]
      _ = ((List.range p).map (fun i => βM (φ i s))).prod := by
            rw [MonoidHom.map_list_prod βM ((List.range p).map (fun i => φ i s)), List.map_map]
            rfl
      _ = ((List.range p).map (fun i => φ (i + 1) s)).prod := by
            congr 1
            apply List.map_congr_left
            intro i _
            exact hFsucc s i
      _ = ((List.range p).map (fun i => φ i s)).prod :=
            kgLangDatumAux_list_prod_shift p (fun i => φ i s) hFp
      _ = N s := (hN_list s).symm
  have hImN_le : N.range ≤ L.ker := by
    rintro x ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    show (N s)⁻¹ * βM (N s) = 1
    rw [hβN s, inv_mul_cancel]
  have hkerN_le : N.ker ≤ L.range := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcK : ((List.range p).map fun i => (β ^ i) (c : K)).prod = 1 := by
      have h := congrArg Subtype.val hc
      rw [hN_eval c] at h
      simpa using h
    obtain ⟨s, hs, hsc⟩ := h90 (c : K) c.2 hcK
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    show s⁻¹ * β s = (c : K)
    exact hsc.symm
  have hcard_le : Nat.card L.ker ≤ Nat.card N.range := by
    have h1 : Nat.card L.ker * Nat.card L.range = Nat.card N.ker * Nat.card N.range := by
      rw [Subgroup.card_ker_mul_card_range L, Subgroup.card_ker_mul_card_range N]
    have h2 : Nat.card N.ker * Nat.card N.range ≤ Nat.card N.range * Nat.card L.range := by
      calc Nat.card N.ker * Nat.card N.range
          ≤ Nat.card L.range * Nat.card N.range :=
            Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hkerN_le)
        _ = Nat.card N.range * Nat.card L.range := mul_comm _ _
    have h3 : Nat.card L.ker * Nat.card L.range ≤ Nat.card N.range * Nat.card L.range := by
      rw [h1]; exact h2
    have hpos : 0 < Nat.card L.range := by
      have : Nonempty L.range := ⟨1, L.range.one_mem⟩
      exact Finite.card_pos
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hEq : N.range = L.ker := Subgroup.eq_of_le_of_card_ge hImN_le hcard_le
  intro t ht hβt
  have htL : (⟨t, ht⟩ : M) ∈ L.ker := by
    rw [MonoidHom.mem_ker]
    have hfixM : βM ⟨t, ht⟩ = ⟨t, ht⟩ := Subtype.ext hβt
    show (⟨t, ht⟩ : M)⁻¹ * βM ⟨t, ht⟩ = 1
    rw [hfixM, inv_mul_cancel]
  have htN : (⟨t, ht⟩ : M) ∈ N.range := hEq ▸ htL
  obtain ⟨s, hs⟩ := htN
  refine ⟨(s : K), s.2, ?_⟩
  have hev := hN_eval s
  rw [hs] at hev
  simpa using hev

@[expose] def KGLangTorusDatumCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
    commutator (HopfCover R) = ⊤ →
    ∀ A : Subgroup (MulAut (HopfCover R)), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      (∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
        (∀ α ∈ A, ∃ k : ℕ, kgInducedAut θ (α * (α₀ ^ k)⁻¹) ∈ I) ∧
        ∃ M : Subgroup (HopfCover R), (∀ a ∈ M, ∀ c ∈ M, a * c = c * a) ∧
          (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
          (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
          (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
          ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e

@[expose] def KGLangTorusDatumOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (KGLangTorusDatumCont p)

theorem kgLangTorusNTUnivCont_of_datum {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hD : KGLangTorusDatumCont p R I F) : KGLangTorusNTUnivCont p R I F := by
  intro _ θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  obtain ⟨hdec, M, hMab, hMst, hMfix, hM90, e, heM, he1, hep, hα₀e⟩ :=
    hD θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  refine ⟨M, hMab, hMst, hMfix, ?_, e, heM, he1, hep, ?_⟩
  · intro t ht hβt
    exact kgLangLT3_norms hMab (hA.2 α₀ hα₀) hMst hM90 t ht hβt
  · intro α hα
    obtain ⟨k, hk⟩ := hdec α hα
    have hγA : α * (α₀ ^ k)⁻¹ ∈ A :=
      A.mul_mem hα (A.inv_mem (A.pow_mem hα₀ k))
    have hγfix : (α * (α₀ ^ k)⁻¹) e = e := hMfix _ hγA hk e heM
    have hpowfix : ∀ j : ℕ, (α₀ ^ j) e = e := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hα₀e]
    calc α e = ((α * (α₀ ^ k)⁻¹) * α₀ ^ k) e := by
          congr 1
          group
      _ = (α * (α₀ ^ k)⁻¹) ((α₀ ^ k) e) := by rw [MulAut.mul_apply]
      _ = (α * (α₀ ^ k)⁻¹) e := by rw [hpowfix k]
      _ = e := hγfix

theorem kgLangTorusNTUnivOn_of_datumOn {S : ℕ → LargeEvenLabel → Prop} (h : KGLangTorusDatumOn S) :
    KGLangTorusNTUnivOn S := fun p lab hp hp2 hlab hS =>
  (h p lab hp hp2 hlab hS).mono fun _ _ _ _ hD => kgLangTorusNTUnivCont_of_datum hD

theorem kgLangTorusDatumOn_reg12_of_families
    (hL : KGLangTorusDatumOn fun p lab => GGNbrLangRegLinearLabel p lab ∧ GGNbrLangRest12Label p lab)
    (hC : KGLangTorusDatumOn fun p lab => GGNbrLangRegClassicalLabel lab ∧ GGNbrLangRest12Label p lab)
    (hE : KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab) :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegLabel p lab ∧ GGNbrLangRest12Label p lab := by
  rintro p lab hp hp2 hlab ⟨h | h | h, h12⟩
  · exact hL p lab hp hp2 hlab ⟨h, h12⟩
  · exact hC p lab hp hp2 hlab ⟨h, h12⟩
  · exact hE p lab hp hp2 hlab ⟨h, h12⟩

theorem kgLangTorusNTUnivOn_reg12_of_families
    (hL : KGLangTorusDatumOn fun p lab => GGNbrLangRegLinearLabel p lab ∧ GGNbrLangRest12Label p lab)
    (hC : KGLangTorusDatumOn fun p lab => GGNbrLangRegClassicalLabel lab ∧ GGNbrLangRest12Label p lab)
    (hE : KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab) :
    KGLangTorusNTUnivOn fun p lab => GGNbrLangRegLabel p lab ∧ GGNbrLangRest12Label p lab :=
  kgLangTorusNTUnivOn_of_datumOn (kgLangTorusDatumOn_reg12_of_families hL hC hE)

theorem ggNbrLangRest12RegSplitTorAUniv12_of_families
    (hL : KGLangTorusDatumOn fun p lab => GGNbrLangRegLinearLabel p lab ∧ GGNbrLangRest12Label p lab)
    (hC : KGLangTorusDatumOn fun p lab => GGNbrLangRegClassicalLabel lab ∧ GGNbrLangRest12Label p lab)
    (hE : KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab)
    (hA : KGLangAxisTorAInput) (hEl : GGNbrLangAxisOn GGNbrLangRest12NonRegNotRankLabel) :
    GGNbrLangRest12RegSplitTorAUniv12 :=
  ⟨kgLangTorusNTUnivOn_reg12_of_families hL hC hE, hA, hEl⟩

end CFSG.StandardType
