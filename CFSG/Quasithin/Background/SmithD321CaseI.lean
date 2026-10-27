module

public import CFSG.Quasithin.Background.SmithD321Q
public import CFSG.Quasithin.Background.SmithD321Fac
public import CFSG.Quasithin.Background.SmithD321NFT

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Quasithin.SmithD39Two
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise Matrix

section Count

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem two_mul_rk_lt_nB_top [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {N : Subgroup Γ}
    (hN : ∀ g : Γ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {V : Subgroup Q} (hV : XMod.IsIrr ↥N V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) (hne : V ≠ ⊤)
    {A : Subgroup Γ} (hA2 : ∀ a ∈ A, a * a = 1) (hA1 : A ≠ ⊥) (hAV : ∀ a ∈ A, a • V = V)
    (hH : ∀ J : Subgroup Q, XMod.IsIrr ↥N J → ∀ P : Subgroup Γ, P ≤ A →
      (∀ a ∈ P, a • J = J) → P ≠ ⊥ → rk ↥P < nB P J) :
    2 * rk ↥A < nB A (⊤ : Subgroup Q) := by
  have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa [sq] using hA2 x x.2)⟩
  have hVA : rk ↥A < nB A V := hH V hV A le_rfl hAV hA1
  have hVpos : 0 < rk ↥V := Nat.pos_of_ne_zero fun h => hV.2.1.ne' ((rk_eq_zero_iff hQ).1 h)
  by_cases hiso : isoSum N V = V
  · have hNw := normalizes_whole (Q := Q) N hN
    obtain ⟨g, hg⟩ : ∃ g : Γ, ¬ XMod.Iso ↥N (g • V) V := by
      by_contra hall
      apply hne
      rw [eq_top_iff, ← hgen]
      exact iSup_le fun g => (le_isoSum (Classical.byContradiction fun h => hall ⟨g, h⟩)).trans
        hiso.le
    have hAK : ∀ a ∈ A, ∀ k ∈ N, a * k * a⁻¹ ∈ N := fun a _ k hk => hN a k hk
    have hNA := SmithD39Two.normalizes_of_conj (Q := Q) hAK
    obtain ⟨J, -, hJ, hJiso, hhc⟩ :=
      XMod.exists_isHomComp_of_isIrr hQ hNA hAp (isIrr_smul hNw g hV)
    have hhom : ∀ t ∈ A, XMod.Iso ↥N (t • J) J → t • J = J := fun t ht hi =>
      (XMod.forall_iso_smul_eq_iff_isHomComp hNA hJ).2 hhc ⟨t, ht⟩ hi
    have hnot : ∀ t ∈ A, ¬ XMod.Iso ↥N (t • J) V := by
      intro t ht hi
      have h1 : XMod.Iso ↥N (t • J) (t • g • V) := XMod.iso_smul hNw t hJiso
      have h2 : XMod.Iso ↥N (t • g • V) V := (XMod.Iso.symm (isIrr_smul hNw t hJ).1 h1).trans hi
      have h3 := XMod.iso_smul hNw t⁻¹ h2
      rw [inv_smul_smul, hAV _ (A.inv_mem ht)] at h3
      exact hg h3
    have hdisj : V ⊓ orbSum A J = ⊥ := by
      have hinv : XMod.IsInv ↥N (V ⊓ orbSum A J) :=
        hV.1.inf (XMod.isInv_iSup fun t => XMod.isInv_smul_of_normalizes hNw (t : Γ) hJ.1)
      rcases hV.2.2 _ hinv bot_le inf_le_left with h | h
      · exact h
      · exfalso
        have hle : V ≤ orbSum A J := by
          rw [← h]
          exact inf_le_right
        obtain ⟨⟨t, ht⟩, hi⟩ := exists_iso_of_le_iSup (S := fun t : ↥A => (t : Γ) • J)
          (fun t => isIrr_smul hNw (t : Γ) hJ) hV hle
        exact hnot t ht (XMod.Iso.symm hV.1 hi)
    have hinvA : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_left (hA2 x hx)
    have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      intro x hx y hy
      have h := eq_inv_of_mul_eq_one_left (hA2 (x * y) (A.mul_mem hx hy))
      rw [h, mul_inv_rev, hinvA x hx, hinvA y hy]
    have hA2' : ∀ x ∈ A, x ^ 2 = 1 := fun x hx => by rw [sq]; exact hA2 x hx
    obtain ⟨-, horb⟩ := nB_orbit hAK hAc hA2' hJ hhom
    have hstab : rk ↥(stabIn A J) ≤ nB (stabIn A J) J := by
      by_cases hS : stabIn A J = ⊥
      · rw [hS, rk_bot]
        exact Nat.zero_le _
      · exact (hH J hJ (stabIn A J) inf_le_left (fun a ha => (mem_stabIn.1 ha).2) hS).le
    have hJpos : 0 < rk ↥J := Nat.pos_of_ne_zero fun h => hJ.2.1.ne' ((rk_eq_zero_iff hQ).1 h)
    have hSA : rk ↥(stabIn A J) ≤ rk ↥A := rk_mono inf_le_left
    have hpow : rk ↥A - rk ↥(stabIn A J) + 1 ≤ 2 ^ (rk ↥A - rk ↥(stabIn A J)) :=
      Nat.lt_two_pow_self
    have h1 : (rk ↥A - rk ↥(stabIn A J)) * rk ↥J + rk ↥J ≤
        2 ^ (rk ↥A - rk ↥(stabIn A J)) * rk ↥J := by
      have := Nat.mul_le_mul_right (rk ↥J) hpow
      rwa [add_mul, one_mul] at this
    have h2 : rk ↥A - rk ↥(stabIn A J) ≤ (rk ↥A - rk ↥(stabIn A J)) * rk ↥J :=
      Nat.le_mul_of_pos_right _ hJpos
    have hVinv : ∀ a ∈ A, ∀ v ∈ V, a • v ∈ V := fun a ha v hv => by
      rw [← hAV a ha]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
    have hsum := nB_sup_of_inf_eq_bot A hVinv (fun a ha q hq => smul_mem_orbSum ha hq) hdisj
    have hmono := nB_mono A (le_top : V ⊔ orbSum A J ≤ ⊤)
    omega
  · obtain ⟨k, hk1, hk2⟩ := count_isoSum hQ hN hV hAp hAV
    have hlt : rk ↥V < rk ↥(isoSum N V) := by
      by_contra hle
      exact hiso (eq_of_le_of_rk_le hQ self_le_isoSum (not_lt.1 hle)).symm
    have hk : 1 < k := by
      have : 1 * rk ↥V < k * rk ↥V := by
        rw [one_mul, ← hk1]
        exact hlt
      exact Nat.lt_of_mul_lt_mul_right this
    have h3 : 2 * nB A V ≤ k * nB A V := Nat.mul_le_mul_right _ hk
    have h4 := nB_mono A (le_top : isoSum N V ≤ ⊤)
    omega

end Count

section Tensor

variable {d : ℕ} {K : Type} [Field K]

private noncomputable def tvSL (i j : Fin d) (hij : i ≠ j) : ↥(StatedSL d K) :=
  specialLinearGroupEquivStatedSL d K
    ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩

theorem eq_one_of_forall_tensorAct (hd : 2 ≤ d) {X : Multiplicative (Matrix (Fin d) (Fin d) K)}
    (hX : ∀ γ, tensorAct d K γ X = X) : X = 1 := by
  have hnt : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  have key : ∀ j k : Fin d, Multiplicative.toAdd X j k = 0 := by
    intro j k
    obtain ⟨i, hij⟩ := exists_ne j
    have h := congrArg (fun Y : Multiplicative (Matrix (Fin d) (Fin d) K) =>
      (Multiplicative.toAdd Y : Matrix (Fin d) (Fin d) K) i k) (hX (tvSL i j hij, 1))
    change (Matrix.transvection i j (1 : K) * Multiplicative.toAdd X *
      (1 : Matrix (Fin d) (Fin d) K)ᵀ) i k = (Multiplicative.toAdd X : Matrix (Fin d) (Fin d) K) i k
      at h
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.transvection_mul_apply_same, one_mul,
      add_eq_left] at h
    exact h
  have h0 : Multiplicative.toAdd X = 0 := by
    ext j k
    exact key j k
  calc X = Multiplicative.ofAdd (Multiplicative.toAdd X) := rfl
    _ = 1 := by rw [h0]; rfl

theorem eq_one_of_fix_tensor {I : Type} [CommGroup I] {H : Subgroup (MulAut I)} (hd : 2 ≤ d)
    (hR : (FFModel.tensorNat d K).Realizes H ⊤ ⊥) {v : I} (hv : ∀ h ∈ H, h v = v) : v = 1 := by
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hfix : ∀ γ, tensorAct d K γ (β ⟨v, trivial⟩) = β ⟨v, trivial⟩ := by
    intro γ
    have h1 := hβe γ ⟨v, trivial⟩ trivial
    have h2 : (⟨((π γ : ↥H) : MulAut I) v, trivial⟩ : ↥(⊤ : Subgroup I)) = ⟨v, trivial⟩ :=
      Subtype.ext (hv _ (π γ).2)
    rw [h2] at h1
    exact h1.symm
  have h3 := (hβk ⟨v, trivial⟩).1 (eq_one_of_forall_tensorAct hd hfix)
  exact Subgroup.mem_bot.1 h3

theorem inf_fixV_eq_bot_of_tensor {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {V : Subgroup W} (hd : 2 ≤ d) (hR : (FFModel.tensorNat d K).Realizes (autSub X V) ⊤ ⊥) :
    V ⊓ fixV X = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwV, hwX⟩
  have h1 := eq_one_of_fix_tensor hd hR (v := ⟨w, hwV⟩) (fun h hh => by
    obtain ⟨g, hgX, rfl⟩ := mem_autSub.1 hh
    apply Subtype.ext
    rw [resHom_apply]
    exact (mem_fixV.1 hwX) _ hgX)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem sixteen_le_card_of_tensor [Finite K] {I : Type} [CommGroup I] {H : Subgroup (MulAut I)}
    (hd : 2 ≤ d) (hR : (FFModel.tensorNat d K).Realizes H ⊤ ⊥) : 16 ≤ Nat.card I := by
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨β, hβs, hβk, -⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have h1 := (hβk u).1 (MonoidHom.mem_ker.1 hu)
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1))
  have h1 := Nat.card_eq_of_bijective β ⟨hβi, hβs⟩
  rw [Subgroup.card_top] at h1
  rw [h1]
  have h2 : Nat.card (FFModel.tensorNat d K).Amb = (Nat.card K ^ d) ^ d := by
    show Nat.card (Multiplicative (Matrix (Fin d) (Fin d) K)) = _
    rw [Nat.card_congr Multiplicative.toAdd]
    show Nat.card (Fin d → Fin d → K) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin]
  rw [h2]
  have hK : 2 ≤ Nat.card K := Finite.one_lt_card
  calc 16 = (2 ^ 2) ^ 2 := by norm_num
    _ ≤ (Nat.card K ^ 2) ^ 2 := by gcongr
    _ ≤ (Nat.card K ^ d) ^ 2 := by gcongr
    _ ≤ (Nat.card K ^ d) ^ d := by
        apply Nat.pow_le_pow_right
        · positivity
        · exact hd

end Tensor

section Transport

theorem realizes_transport {D : FFModel} {I₁ I₂ : Type} [CommGroup I₁] [CommGroup I₂]
    {H₁ : Subgroup (MulAut I₁)} {H₂ : Subgroup (MulAut I₂)} (ψ : I₂ ≃* I₁) (θ : ↥H₁ →* ↥H₂)
    (hθ : Function.Surjective θ)
    (hc : ∀ (h : ↥H₁) (x : I₂), ψ (((θ h : ↥H₂) : MulAut I₂) x) = (h : MulAut I₁) (ψ x))
    (hR : D.Realizes H₁ ⊤ ⊥) : D.Realizes H₂ ⊤ ⊥ := by
  obtain ⟨π, hπ⟩ := hR
  refine ⟨θ.comp π, n4_realizesVia_transport (U := (⊤ : Subgroup I₂)) (Z := ⊥) θ hθ bot_le
    (fun _ _ _ => trivial) (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]) (ψ.toMonoidHom.comp (⊤ : Subgroup I₂).subtype) ?_ ?_ ?_ hπ⟩
  · intro y
    exact ⟨⟨ψ.symm y, trivial⟩, by simp⟩
  · intro u
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      Function.comp_apply, Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  · intro h u hu
    exact hc h u

end Transport

section SecI

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem isQuotientOfSQTKTC_of_surjective {X Y : Type*} [Group X] [Group Y]
    (hX : IsQuotientOfSQTKTC X) (f : X →* Y) (hf : Function.Surjective f) :
    IsQuotientOfSQTKTC Y := by
  obtain ⟨S, _, _, h1, h2, φ, hφ⟩ := hX
  exact ⟨S, inferInstance, inferInstance, h1, h2, f.comp φ, hf.comp hφ⟩

theorem smul_tilde_of_mem_T (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V) {x : MulAut W}
    (hxT : x ∈ T) :
    letI := qAct hB.hD.hyp.Mp_normal
    (⟨x, hB.T_le hxT⟩ : ↥M) • tilde Mp ⊤ V = tilde Mp ⊤ V := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [smul_tildeQ hB.hD.hyp.Mp_normal]
  congr 1
  have h1 : (orbSup T V).map x.toMonoidHom = orbSup T V :=
    mem_stabSub_iff_map_eq.1 (le_stabSub_orbSup T V hxT)
  rw [← hVT] at h1
  exact h1

private theorem faithful_of_simple (hB : D321Base M Mp T L V t) {Y : Subgroup (MulAut W)}
    (hYs : IsSimpleGroup ↥Y) (hYMp : Y ≤ Mp)
    (hnt : ¬ ∀ y (hy : y ∈ Y), ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hB.Mp_le (hYMp hy)⟩ : ↥M) • q = q)) :
    ∀ y (hy : y ∈ Y), (∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hB.Mp_le (hYMp hy)⟩ : ↥M) • q = q)) → y = 1 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hinv : ∀ l : ↥(Y.subgroupOf M), ∀ v ∈ tilde Mp ⊤ V, l • v ∈ tilde Mp ⊤ V :=
    fun l v hv => hB.irr.1 ⟨(l : ↥M), Subgroup.mem_subgroupOf.2
      (hYMp (Subgroup.mem_subgroupOf.1 l.2))⟩ v hv
  have hs : IsSimpleGroup ↥(Y.subgroupOf M) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe (hYMp.trans hB.Mp_le))
  set f := actAut (Y.subgroupOf M) (tilde Mp ⊤ V) hinv with hf
  have := f.normal_ker
  have hfix : ∀ y (hy : y ∈ Y), (∀ q ∈ tilde Mp ⊤ V, (⟨y, hB.Mp_le (hYMp hy)⟩ : ↥M) • q = q) →
      (⟨⟨y, hB.Mp_le (hYMp hy)⟩, hy⟩ : ↥(Y.subgroupOf M)) ∈ f.ker := by
    intro y hy hq
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun q => Subtype.ext ?_
    exact hq q q.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · intro y hy hq
    have h1 := hfix y hy hq
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg (fun x : ↥(Y.subgroupOf M) => ((x : ↥M) : MulAut W)) h1
  · exfalso
    apply hnt
    intro y hy q hq
    have hmem : (⟨⟨y, hB.Mp_le (hYMp hy)⟩, hy⟩ : ↥(Y.subgroupOf M)) ∈ f.ker := by
      rw [h]; trivial
    have h1 := congrArg (fun φ : MulAut ↥(tilde Mp ⊤ V) => ((φ ⟨q, hq⟩ : ↥(tilde Mp ⊤ V)) :
      W ⧸ modFix Mp (⊤ : Subgroup W))) (MonoidHom.mem_ker.1 hmem)
    exact h1

private theorem triv_conj (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V) {x : MulAut W}
    (hxT : x ∈ T) {Y : Subgroup (MulAut W)} (hYM : Y ≤ M)
    (hY : ∀ y (hy : y ∈ Y), ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hYM hy⟩ : ↥M) • q = q))
    (hYM' : conjAutSub x Y ≤ M) :
    ∀ y (hy : y ∈ conjAutSub x Y), ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hYM' hy⟩ : ↥M) • q = q) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro y hy q hq
  have hy' : x⁻¹ * y * x ∈ Y := mem_conjAutSub.1 hy
  set xM : ↥M := ⟨x, hB.T_le hxT⟩ with hxM
  have hx1 : xM⁻¹ • q ∈ tilde Mp ⊤ V := by
    have h1 := smul_tilde_of_mem_T hB hVT (T.inv_mem hxT)
    have h2 : (⟨x⁻¹, hB.T_le (T.inv_mem hxT)⟩ : ↥M) • q ∈
        (⟨x⁻¹, hB.T_le (T.inv_mem hxT)⟩ : ↥M) • tilde Mp ⊤ V :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hq
    rw [h1] at h2
    exact h2
  have e : (⟨y, hYM' hy⟩ : ↥M) = xM * ⟨x⁻¹ * y * x, hYM hy'⟩ * xM⁻¹ := by
    apply Subtype.ext
    show y = x * (x⁻¹ * y * x) * x⁻¹
    group
  rw [e, mul_smul, mul_smul, hY _ hy' _ hx1, smul_inv_smul]

private theorem not_triv_L (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V) :
    ¬ ∀ y (hy : y ∈ L), ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hB.Mp_le (hB.L_le_Mp hy)⟩ : ↥M) • q = q) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro hL
  have hLt := triv_conj hB hVT hB.htT (fun _ hy => hB.Mp_le (hB.L_le_Mp hy)) hL hB.Lt_le
  have hfix : tilde Mp ⊤ V ≤
      XMod.fixed ↥(Mp.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
    intro q hq
    refine ⟨trivial, fun a => ?_⟩
    obtain ⟨l, hl, l', hl', hll'⟩ := hB.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 a.2)
    have e : ((a : ↥(Mp.subgroupOf M)) : ↥M) = ⟨l, hB.L_le hl⟩ * ⟨l', hB.Lt_le hl'⟩ :=
      Subtype.ext hll'
    show ((a : ↥(Mp.subgroupOf M)) : ↥M) • q = q
    rw [e, mul_smul, hLt l' hl' q hq]
    exact hL l hl q hq
  rw [hB.fixed_eq_bot] at hfix
  exact hB.tilde_ne_bot (le_bot_iff.1 hfix)

private theorem not_triv_Lt (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V) :
    ¬ ∀ y (hy : y ∈ conjAutSub t L), ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨y, hB.Mp_le (hB.Lt_le_Mp hy)⟩ : ↥M) • q = q) := by
  intro hLt
  have hL := triv_conj hB hVT hB.htT (fun _ hy => hB.Mp_le (hB.Lt_le_Mp hy)) hLt
    (by rw [(hB.conj_swap hB.t_mem hB.htn).2]; exact hB.L_le)
  apply not_triv_L hB hVT
  intro y hy q hq
  have hy' : y ∈ conjAutSub t (conjAutSub t L) := by
    rw [(hB.conj_swap hB.t_mem hB.htn).2]; exact hy
  exact hL y hy' q hq

theorem faithful_tilde_caseI (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V) {x : MulAut W}
    (hx : x ∈ Mp) (hxq : ∀ q ∈ tilde Mp ⊤ V,
      (letI := qAct hB.hD.hyp.Mp_normal; (⟨x, hB.Mp_le hx⟩ : ↥M) • q = q)) : x = 1 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hfL := faithful_of_simple hB hB.hsimp hB.L_le_Mp (not_triv_L hB hVT)
  have hfLt := faithful_of_simple hB hB.Lt_simp hB.Lt_le_Mp (not_triv_Lt hB hVT)
  have hinv : ∀ y (hy : y ∈ Mp), ∀ q ∈ tilde Mp ⊤ V, (⟨y, hB.Mp_le hy⟩ : ↥M) • q ∈ tilde Mp ⊤ V :=
    fun y hy q hq => hB.irr.1 ⟨⟨y, hB.Mp_le hy⟩, hy⟩ q hq
  have hcomm : ∀ y (hyMp : y ∈ Mp), ∀ (Y : Subgroup (MulAut W)) (hYMp : Y ≤ Mp)
      (hfY : ∀ z (hz : z ∈ Y), (∀ q ∈ tilde Mp ⊤ V, (⟨z, hB.Mp_le (hYMp hz)⟩ : ↥M) • q = q) →
        z = 1)
      (hYn : ∀ l ∈ Y, x * l * x⁻¹ ∈ Y), y ∈ Y → x * y = y * x := by
    intro y hyMp Y hYMp hfY hYn hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ Y := Y.mul_mem (hYn y hy) (Y.inv_mem hy)
    have h1 := hfY _ hc (fun q hq => by
      have e : (⟨x * y * x⁻¹ * y⁻¹, hB.Mp_le (hYMp hc)⟩ : ↥M) =
          ⟨x, hB.Mp_le hx⟩ * ⟨y, hB.Mp_le hyMp⟩ * ⟨x, hB.Mp_le hx⟩⁻¹ *
            ⟨y, hB.Mp_le hyMp⟩⁻¹ := rfl
      have hq1 : (⟨y, hB.Mp_le hyMp⟩ : ↥M)⁻¹ • q ∈ tilde Mp ⊤ V :=
        hinv _ (Mp.inv_mem hyMp) q hq
      have hq2 : (⟨x, hB.Mp_le hx⟩ : ↥M)⁻¹ • ((⟨y, hB.Mp_le hyMp⟩ : ↥M)⁻¹ • q) =
          (⟨y, hB.Mp_le hyMp⟩ : ↥M)⁻¹ • q := by
        rw [inv_smul_eq_iff, hxq _ hq1]
      rw [e, mul_smul, mul_smul, mul_smul, hq2, smul_inv_smul, hxq q hq])
    calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
      _ = y * x := by rw [h1]; group
  refine hB.eq_one_of_mem_Mp hx fun y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hy
  have h1 := hcomm a (hB.L_le_Mp ha) L hB.L_le_Mp hfL (fun l hl => hB.conj_mem_L hx hl) ha
  have h2 := hcomm b (hB.Lt_le_Mp hb) (conjAutSub t L) hB.Lt_le_Mp hfLt
    (fun l hl => hB.conj_mem_Lt hx hl) hb
  calc x * (a * b) = (x * a) * b := (mul_assoc _ _ _).symm
    _ = (a * x) * b := by rw [h1]
    _ = a * (x * b) := mul_assoc _ _ _
    _ = a * (b * x) := by rw [h2]
    _ = a * b * x := (mul_assoc _ _ _).symm

private theorem Mp_le_stabSub (hB : D321Base M Mp T L V t) : Mp ≤ stabSub V := by
  intro x hx v
  refine ⟨fun h => ?_, fun h => hB.Mp_inv_V x hx v h⟩
  have := hB.Mp_inv_V x⁻¹ (Mp.inv_mem hx) _ h
  simpa using this

theorem realizes_resJ (hB : D321Base M Mp T L V t) (hVT : V = orbSup T V)
    (hVZ : V ⊓ fixV Mp = ⊥) {D : FFModel} (hR : D.Realizes (autSub Mp V) ⊤ ⊥)
    {J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hJX : letI := qAct hB.hD.hyp.Mp_normal; ∀ s ∈ Mp.subgroupOf M, ∀ j ∈ J, s • j ∈ J)
    (g : ↥M)
    (hiso : letI := qAct hB.hD.hyp.Mp_normal
      XMod.Iso ↥(Mp.subgroupOf M) J (g • tilde Mp ⊤ V)) :
    letI := qAct hB.hD.hyp.Mp_normal
    D.Realizes (resJ (Mp.subgroupOf M) J hJX).range ⊤ ⊥ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  set Vt := tilde Mp ⊤ V with hVt
  obtain ⟨φ, hφ⟩ := hiso
  set κ₀ : ↥V →* ↥Vt := (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap V with hκ₀
  have hκinj : Function.Injective κ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    have h1 : (QuotientGroup.mk (v : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
    rw [QuotientGroup.eq_one_iff, SmithD391.modFix_top_eq] at h1
    have h2 : (v : W) ∈ V ⊓ fixV Mp := ⟨v.2, h1⟩
    rw [hVZ, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  set κ : ↥V ≃* ↥Vt := MulEquiv.ofBijective κ₀ ⟨hκinj,
    (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap_surjective V⟩ with hκ
  set σ := (XMod.smulEquiv g Vt).symm with hσ
  set ψ : ↥J ≃* ↥V := φ.trans (σ.trans κ.symm) with hψ
  have hMpV := Mp_le_stabSub hB
  set ρ₁ : ↥Mp →* ↥(autSub Mp V) :=
    ((resHom V).comp (Subgroup.inclusion hMpV)).codRestrict _ (fun x =>
      mem_autSub.2 ⟨⟨x, hMpV x.2⟩, x.2, rfl⟩) with hρ₁
  have hρ₁s : Function.Surjective ρ₁ := by
    rintro ⟨h, hh⟩
    obtain ⟨x, hxMp, rfl⟩ := mem_autSub.1 hh
    exact ⟨⟨x, hxMp⟩, rfl⟩
  have hρ₁i : Function.Injective ρ₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : resHom V ⟨x, hMpV x.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxV : ∀ v ∈ V, (x : MulAut W) v = v := fun v hv => by
      have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) h1
      exact this
    have h2 := faithful_tilde_caseI hB hVT x.2 (fun q hq => by
      obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq
      change (QuotientGroup.mk ((x : MulAut W) v) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
        QuotientGroup.mk v
      rw [hxV v hv])
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  set e₁ := MulEquiv.ofBijective ρ₁ ⟨hρ₁i, hρ₁s⟩ with he₁
  have hgMp : ∀ x ∈ Mp, (g : MulAut W) * x * (g : MulAut W)⁻¹ ∈ Mp := fun x hx =>
    hB.conj_mem_Mp g.2 hx
  set cg : ↥Mp →* ↥(Mp.subgroupOf M) :=
    { toFun := fun x => ⟨g * ⟨x, hB.Mp_le x.2⟩ * g⁻¹, Subgroup.mem_subgroupOf.2 (hgMp x x.2)⟩
      map_one' := by
        apply Subtype.ext
        show g * (1 : ↥M) * g⁻¹ = 1
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show g * (⟨(x : MulAut W) * y, _⟩ : ↥M) * g⁻¹ =
          g * ⟨(x : MulAut W), _⟩ * g⁻¹ * (g * ⟨(y : MulAut W), _⟩ * g⁻¹)
        have e : (⟨(x : MulAut W) * y, hB.Mp_le (Mp.mul_mem x.2 y.2)⟩ : ↥M) =
            ⟨(x : MulAut W), hB.Mp_le x.2⟩ * ⟨(y : MulAut W), hB.Mp_le y.2⟩ := rfl
        rw [e]
        group } with hcg
  set ρ₂ : ↥Mp →* ↥(resJ (Mp.subgroupOf M) J hJX).range :=
    (resJ (Mp.subgroupOf M) J hJX).rangeRestrict.comp cg with hρ₂
  have hρ₂s : Function.Surjective ρ₂ := by
    rintro ⟨_, y, rfl⟩
    have hy : (g : MulAut W)⁻¹ * ((y : ↥M) : MulAut W) * g ∈ Mp := by
      have := hB.conj_mem_Mp (M.inv_mem g.2) (Subgroup.mem_subgroupOf.1 y.2)
      simpa using this
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    show resJ (Mp.subgroupOf M) J hJX (cg ⟨_, hy⟩) = resJ (Mp.subgroupOf M) J hJX y
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    show (g : MulAut W) * ((g : MulAut W)⁻¹ * ((y : ↥M) : MulAut W) * g) * (g : MulAut W)⁻¹ =
      ((y : ↥M) : MulAut W)
    group
  set θ := ρ₂.comp e₁.symm.toMonoidHom with hθ
  have hθs : Function.Surjective θ := hρ₂s.comp e₁.symm.surjective
  refine realizes_transport ψ θ hθs ?_ hR
  intro h j
  obtain ⟨x, rfl⟩ := e₁.surjective h
  have hθx : θ (e₁ x) = ρ₂ x := by
    rw [hθ, MonoidHom.comp_apply]
    simp
  rw [hθx]
  apply κ.injective
  apply Subtype.ext
  have hψj : ∀ y : ↥J, ((κ (ψ y) : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      g⁻¹ • ((φ y : ↥(g • Vt)) : W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    intro y
    rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hκx : ∀ v : ↥V, ((κ ((e₁ x : MulAut ↥V) v) : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      (⟨x, hB.Mp_le x.2⟩ : ↥M) • ((κ v : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    fun v => rfl
  have hφx : ((φ ((ρ₂ x : MulAut ↥J) j) : ↥(g • Vt)) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      (cg x : ↥M) • ((φ j : ↥(g • Vt)) : W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    (hφ (cg x) j ((ρ₂ x : MulAut ↥J) j) rfl).symm
  rw [hψj, hκx, hψj, hφx]
  have e2 : (cg x : ↥M) = g * ⟨x, hB.Mp_le x.2⟩ * g⁻¹ := rfl
  rw [e2, mul_smul, mul_smul, inv_smul_smul]

private theorem two_le_rk_of_model {I : Type} [CommGroup I] [Finite I] (hI : ∀ v : I, v ^ 2 = 1)
    {H : Subgroup (MulAut I)} (hT : (∃ n, 2 ≤ n ∧ Omega4PlusModule H n) ∨ TensorNatL32 H) :
    2 ≤ rk (⊤ : Subgroup I) := by
  have h16 : 16 ≤ Nat.card I := by
    rcases hT with ⟨n, -, K, _, _, -, hR⟩ | hR
    · exact sixteen_le_card_of_tensor (d := 2) le_rfl hR
    · exact sixteen_le_card_of_tensor (d := 3) (K := ZMod 2) (by norm_num) hR
  rw [← Subgroup.card_top, card_eq_two_pow hI] at h16
  by_contra hlt
  have : 2 ^ rk (⊤ : Subgroup I) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem rk_lt_nB_caseI (h56 : AsB56) {A : Subgroup (MulAut W)} {r : ℚ}
    (hS : D321Sit M Mp T L V t A r) (hVT : V = orbSup T V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hmod : (∃ n, 2 ≤ n ∧ Omega4PlusModule (autSub Mp V) n) ∨ TensorNatL32 (autSub Mp V)) :
    letI := qAct hS.hD.hyp.Mp_normal
    ∀ J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)), XMod.IsIrr ↥(Mp.subgroupOf M) J →
      ∀ P : Subgroup ↥M, P ≤ A.subgroupOf M → (∀ a ∈ P, a • J = J) → P ≠ ⊥ →
        rk ↥P < nB P J := by
  have hB := hS.toD321Base
  let _i := qAct hB.hD.hyp.Mp_normal
  intro J hJ P hPA hPJ hP1
  set X := Mp.subgroupOf M with hX
  have hQ := hB.quot_sq
  have hN := normalizes_whole (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) X hB.Λ_normal
  obtain ⟨g, hg⟩ := exists_iso_of_le_iSup (S := fun g : ↥M => g • tilde Mp ⊤ V)
    (fun g => isIrr_smul hN g hB.irr) hJ (by rw [hB.gen]; exact le_top)
  have hVZ : V ⊓ fixV Mp = ⊥ := by
    rcases hmod with ⟨n, -, K, _, _, -, hR⟩ | hR
    · exact inf_fixV_eq_bot_of_tensor (d := 2) le_rfl hR
    · exact inf_fixV_eq_bot_of_tensor (d := 3) (K := ZMod 2) (by norm_num) hR
  have hJX : ∀ s ∈ X, ∀ j ∈ J, s • j ∈ J := fun s hs j hj => hJ.1 ⟨s, hs⟩ j hj
  have hTJ : (∃ n, 2 ≤ n ∧ Omega4PlusModule (resJ X J hJX).range n) ∨
      TensorNatL32 (resJ X J hJX).range := by
    rcases hmod with ⟨n, hn, K, hKf, hKfin, hK, hR⟩ | hR
    · exact Or.inl ⟨n, hn, K, hKf, hKfin, hK, realizes_resJ hB hVT hVZ hR hJX g hg⟩
    · exact Or.inr (realizes_resJ hB hVT hVZ hR hJX g hg)
  have hPJ' : ∀ a ∈ P, ∀ j ∈ J, a • j ∈ J := fun a ha j hj => by
    rw [← hPJ a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hj
  have hJ' : ∀ g' ∈ X ⊔ P, ∀ j ∈ J, g' • j ∈ J := fun g' hg' =>
    smul_mem_of_mem_sup hJX hPJ' hg'
  have hXn : X ⊔ P ≤ Subgroup.normalizer (X : Set ↥M) := by
    refine sup_le Subgroup.le_normalizer fun a _ => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hB.Λ_normal a x hx, fun hx => by
      have := hB.Λ_normal a⁻¹ _ hx
      simpa [mul_assoc] using this⟩
  have hHG : (resJ X J hJX).range ≤ (resJ (X ⊔ P) J hJ').range := range_resJ_mono le_sup_left
  have hGH : (resJ (X ⊔ P) J hJ').range ≤
      Subgroup.normalizer ((resJ X J hJX).range : Set (MulAut ↥J)) := by
    rintro _ ⟨y, rfl⟩
    have hconj : ∀ x : ↥X, ((y : ↥M) * x * (y : ↥M)⁻¹) ∈ X := fun x =>
      (Subgroup.mem_normalizer_iff.1 (hXn y.2) x).1 x.2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨_, hconj x⟩, MulEquiv.ext fun j => Subtype.ext ?_⟩
      show ((y : ↥M) * x * (y : ↥M)⁻¹) • (j : W ⧸ modFix Mp (⊤ : Subgroup W)) =
        (y : ↥M) • (x : ↥M) • (y : ↥M)⁻¹ • (j : W ⧸ modFix Mp (⊤ : Subgroup W))
      rw [mul_smul, mul_smul]
    · rintro ⟨x, hx⟩
      have hconj' : ((y : ↥M)⁻¹ * x * (y : ↥M)) ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 (hXn ((X ⊔ P).inv_mem y.2)) x).1 x.2
        simpa using this
      refine ⟨⟨_, hconj'⟩, ?_⟩
      have hh : h = ((resJ (X ⊔ P) J hJ') y)⁻¹ * resJ X J hJX x * (resJ (X ⊔ P) J hJ') y := by
        rw [hx]
        group
      rw [hh, ← map_inv]
      refine MulEquiv.ext fun j => Subtype.ext ?_
      show ((y : ↥M)⁻¹ * x * (y : ↥M)) • (j : W ⧸ modFix Mp (⊤ : Subgroup W)) =
        ((y⁻¹ : ↥(X ⊔ P)) : ↥M) • (x : ↥M) • (y : ↥M) • (j : W ⧸ modFix Mp (⊤ : Subgroup W))
      rw [mul_smul, mul_smul]
      rfl
  have hsec : IsQuotientOfSQTKTC ↥(resJ (X ⊔ P) J hJ').range :=
    isQuotientOfSQTKTC_of_surjective
      (isQuotientOfSQTKTC_subgroup hB.hD.hyp.qsqtk (X ⊔ P)) _
      (resJ (X ⊔ P) J hJ').rangeRestrict_surjective
  have hJ2 : ∀ v : ↥J, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hQ v)
  have hnot := not_isFFModule_tensor h56 hJ2 hTJ hHG hGH hsec
  have hfaith : ∀ x ∈ X, (∀ j ∈ J, x • j = j) → x = 1 := by
    intro x hx hxj
    obtain ⟨φ, hφ⟩ := hg
    have h1 : ∀ q ∈ g • tilde Mp ⊤ V, x • q = q := by
      intro q hq
      obtain ⟨j, hj⟩ := φ.surjective ⟨q, hq⟩
      have h2 := hφ ⟨x, hx⟩ j j (hxj j j.2)
      rw [hj] at h2
      exact h2
    have hx' : (g⁻¹ * x * g : ↥M) ∈ X := by
      have := hB.Λ_normal g⁻¹ x hx
      simpa using this
    have h3 := faithful_tilde_caseI hB hVT (Subgroup.mem_subgroupOf.1 hx') (fun q hq => by
      have hgq : g • q ∈ g • tilde Mp ⊤ V := Subgroup.smul_mem_pointwise_smul _ _ _ hq
      have h4 := h1 _ hgq
      show (g⁻¹ * x * g) • q = q
      rw [mul_smul, mul_smul, h4, inv_smul_smul])
    have h5 : (g⁻¹ * x * g : ↥M) = 1 := Subtype.ext h3
    have h6 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h6, h5, mul_one, mul_inv_cancel]
  have hrkJ : 2 ≤ rk ↥J := by
    have h := two_le_rk_of_model hJ2 hTJ
    rwa [rk_top] at h
  obtain ⟨-, hlt, -⟩ := ratio_of_not_isFFModule hQ (X := X) (B := P)
    (fun a ha b hb => Subtype.ext (hS.elemAb.1 _ (hPA ha) _ (hPA hb)))
    (fun a ha => Subtype.ext (hS.elemAb.2 _ (hPA ha)))
    (fun a _ x hx => hB.Λ_normal a x hx) hJ' hrkJ hfaith hnot
  have hPC : P ⊓ Subgroup.centralizer (X : Set ↥M) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haP, hac⟩
    have haA : ((a : ↥M) : MulAut W) ∈ A := hPA haP
    have hac' : ((a : ↥M) : MulAut W) ∈ Subgroup.centralizer (Mp : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := (Subgroup.mem_centralizer_iff.1 hac) ⟨y, hB.Mp_le hy⟩ hy
      exact congrArg Subtype.val this
    have hmem : ((a : ↥M) : MulAut W) ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      ⟨haA, hac'⟩
    rw [hAC, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext hmem)
  have hm : mRel P X = rk ↥P := by
    unfold mRel
    rw [hPC, rk_bot, Nat.sub_zero]
  have hPp : IsPGroup 2 ↥P := isPGroup_two_of_sq_eq_one fun a =>
    Subtype.ext (Subtype.ext (hS.elemAb.2 _ (hPA a.2)))
  have hpos : 0 < rk ↥P := by
    rcases Nat.eq_zero_or_pos (rk ↥P) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hPp).1 h) hP1
    · exact h
  rw [hm] at hlt
  exact_mod_cast hlt hpos

theorem caseI_false (h56 : AsB56) (h37 : D37) {A : Subgroup (MulAut W)} {r : ℚ}
    (hS : D321Sit M Mp T L V t A r) (hVT : V = orbSup T V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) : False := by
  have hB := hS.toD321Base
  let _i := qAct hB.hD.hyp.Mp_normal
  have hmod : (∃ n, 2 ≤ n ∧ Omega4PlusModule (autSub Mp V) n) ∨ TensorNatL32 (autSub Mp V) := by
    rcases h37 W M Mp T L V hB.hD hVT t hB.htT hB.htn hB.hMp with ⟨n, hpsl, hO⟩ | ⟨-, hT3⟩
    · refine Or.inl ⟨n, ?_, hO⟩
      obtain ⟨⟨-, hn1, -, hn2, -⟩, -⟩ := hpsl
      by_contra hn
      apply hn2
      have : n = 1 := by omega
      subst this
      rfl
    · exact Or.inr hT3
  have hne : tilde Mp ⊤ V ≠ ⊤ := by
    intro htop
    apply hB.not_le_orbSup hS.htop
    intro w _
    have h1 : w ∈ (tilde Mp ⊤ V).comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) := by
      rw [htop]
      trivial
    rw [comap_tilde, SmithD391.modFix_top_eq] at h1
    rw [← hVT]
    exact h1
  have hAM := hS.A_le
  have hA2 : ∀ a ∈ A.subgroupOf M, a * a = 1 := fun a ha =>
    Subtype.ext (by rw [← sq]; exact hS.elemAb.2 _ ha)
  have hA1 : A.subgroupOf M ≠ ⊥ := by
    intro h
    have hpos := hS.rk_pos
    have h1 : rk ↥(A.subgroupOf M) = rk ↥A := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    rw [h, rk_bot] at h1
    omega
  have hAV : ∀ a ∈ A.subgroupOf M, a • tilde Mp ⊤ V = tilde Mp ⊤ V := fun a ha =>
    smul_tilde_of_mem_T hB hVT (hS.hAT (Subgroup.mem_subgroupOf.1 ha))
  have hcount := two_mul_rk_lt_nB_top hB.quot_sq hB.Λ_normal hB.irr hB.gen hne hA2 hA1 hAV
    (rk_lt_nB_caseI h56 hS hVT hAC hmod)
  have hle := hS.nB_le
  have h1 : rk ↥(A.subgroupOf M) = rk ↥A := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
  omega

end SecI

end CFSG.Quasithin.SmithD321
