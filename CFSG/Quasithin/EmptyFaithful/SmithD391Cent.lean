module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Nat
public import CFSG.Quasithin.EmptyFaithful.S1417Rank
public import CFSG.Quasithin.EmptyFaithful.SmithD391Hom

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section Abstract

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
  {Λ : Subgroup Γ} {V : Subgroup Q}

theorem iso_smul_of_comm (hV : XMod.IsInv ↥Λ V) {x : Γ} (hxΛ : ∀ l ∈ Λ, x * l = l * x) :
    XMod.Iso ↥Λ (x • V) V := by
  refine XMod.Iso.symm hV ⟨XMod.smulEquiv x V, fun a v v' hvv' => ?_⟩
  show (a : Γ) • x • (v : Q) = x • (v' : Q)
  rw [smul_smul, ← hxΛ a a.2, mul_smul]
  exact congrArg (x • ·) hvv'

theorem exists_second_summand [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hk : rk ↥(isoSum Λ V) = 2 * rk ↥V) :
    ∃ S : Subgroup Q, XMod.IsInv ↥Λ S ∧ V ⊓ S = ⊥ ∧ XMod.Iso ↥Λ V S ∧ V ⊔ S = isoSum Λ V := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have hrkV : 0 < rk ↥V := by
    by_contra h0
    exact hirr.2.1.ne' ((rk_eq_zero_iff hQ).1 (by omega))
  obtain ⟨g, hg, hgV⟩ : ∃ g : Γ, XMod.Iso ↥Λ (g • V) V ∧ ¬ g • V ≤ V := by
    by_contra hcon
    push Not at hcon
    have hle : isoSum Λ V ≤ V := iSup₂_le fun g hg => hcon g hg
    have := rk_mono hle
    omega
  have hSinv : XMod.IsInv ↥Λ (g • V) := XMod.isInv_smul_of_normalizes hN g hirr.1
  have hSirr : XMod.IsIrr ↥Λ (g • V) := isIrr_smul hN g hirr
  have hinf : V ⊓ g • V = ⊥ := by
    have hinv : XMod.IsInv ↥Λ (V ⊓ g • V) := fun a q hq => ⟨hirr.1 a q hq.1, hSinv a q hq.2⟩
    rcases hSirr.2.2 (V ⊓ g • V) hinv bot_le inf_le_right with h | h
    · exact h
    · exfalso
      apply hgV
      rw [← h]
      exact inf_le_left
  refine ⟨g • V, hSinv, hinf, XMod.Iso.symm hSinv hg, ?_⟩
  have hle : V ⊔ g • V ≤ isoSum Λ V := sup_le self_le_isoSum (le_isoSum hg)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := rk_sup_add_rk_inf V (g • V)
  rw [hinf, rk_bot, rk_smul] at h1
  rw [card_eq_two_pow hQ, card_eq_two_pow hQ, hk]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem fix_top_of_prime_ge_five [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hAut : ∀ ψ : ↥V ≃* ↥V, ∃ l : ↥Λ, ∀ v : ↥V, (l : Γ) • (v : Q) = ((ψ v : ↥V) : Q))
    (hinj : ∀ l : ↥Λ, (∀ v ∈ V, (l : Γ) • v = v) → l = 1)
    (hZ : ∀ l : ↥Λ, (∀ l' : ↥Λ, l * l' = l' * l) → l = 1)
    (hk : rk ↥(isoSum Λ V) = 2 * rk ↥V) {t : Γ} (hsup : isoSum Λ V ⊔ t • isoSum Λ V = ⊤)
    {x : Γ} (hxΛ : ∀ l ∈ Λ, x * l = l * x) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hxp : x ^ p = 1) : ∀ q : Q, x • q = q := by
  obtain ⟨S, hSinv, hVS, hiso, hQ₁⟩ := exists_second_summand hQ hΛ hirr hk
  have key : ∀ y : Γ, (∀ l ∈ Λ, y * l = l * y) → y ^ p = 1 → ∀ q ∈ isoSum Λ V, y • q = q := by
    intro y hyΛ hyp q hq
    have hyQ : y • isoSum Λ V = isoSum Λ V := smul_isoSum_eq hΛ (iso_smul_of_comm hirr.1 hyΛ)
    have hyQ' : ∀ q ∈ V ⊔ S, y • q ∈ V ⊔ S := by
      intro q hq
      rw [hQ₁] at hq ⊢
      rw [← hyQ]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
    rw [← hQ₁] at hq
    exact fix_of_prime_ge_five hirr hAut hinj hZ hSinv hVS hiso hyΛ hyQ' hp hp5 hyp q hq
  have hconj : ∀ l ∈ Λ, (t⁻¹ * x * t) * l = l * (t⁻¹ * x * t) := by
    intro l hl
    have h1 := hxΛ _ (hΛ t l hl)
    calc t⁻¹ * x * t * l = t⁻¹ * (x * (t * l * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * l * t⁻¹) * x) * t := by rw [h1]
      _ = l * (t⁻¹ * x * t) := by group
  have hpow : (t⁻¹ * x * t) ^ p = 1 := by
    have h1 : t⁻¹ * x * t = (MulAut.conj t⁻¹) x := by simp
    rw [h1, ← map_pow, hxp, map_one]
  have h1 := key x hxΛ hxp
  have h2 := key _ hconj hpow
  intro q
  have hq : q ∈ isoSum Λ V ⊔ t • isoSum Λ V := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hq
  have hc : t⁻¹ • b ∈ isoSum Λ V := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hb
  have hb' : x • b = b := by
    calc x • b = t • ((t⁻¹ * x * t) • t⁻¹ • b) := by
          rw [smul_smul, smul_smul, show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
      _ = t • t⁻¹ • b := by rw [h2 _ hc]
      _ = b := smul_inv_smul t b
  rw [smul_mul', h1 a ha, hb']

end Abstract

section Matrices

theorem mem_statedSL_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

theorem exists_e9_GL {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∃ y z i : GL (Fin n) (ZMod 2), y * z = z * y ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      i ^ 2 = 1 ∧ i ≠ 1 ∧ i * z = z * i ∧ i * y * i⁻¹ = y⁻¹ := by
  rcases hn with rfl | rfl
  · refine ⟨⟨!![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1], !![1,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
        by decide, by decide⟩,
      ⟨!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,1], !![1,0,0,0; 0,1,0,0; 0,0,1,1; 0,0,1,0],
        by decide, by decide⟩,
      ⟨!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1], !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
        by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (apply Units.ext; decide)
      | (intro h; have h' := congrArg Units.val h; revert h'; decide)
  · refine ⟨⟨!![0,1,0,0,0; 1,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1],
        !![1,1,0,0,0; 1,0,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1], by decide, by decide⟩,
      ⟨!![1,0,0,0,0; 0,1,0,0,0; 0,0,0,1,0; 0,0,1,1,0; 0,0,0,0,1],
        !![1,0,0,0,0; 0,1,0,0,0; 0,0,1,1,0; 0,0,1,0,0; 0,0,0,0,1], by decide, by decide⟩,
      ⟨!![0,1,0,0,0; 1,0,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1],
        !![0,1,0,0,0; 1,0,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1], by decide, by decide⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (apply Units.ext; decide)
      | (intro h; have h' := congrArg Units.val h; revert h'; decide)

theorem e9_map {H G : Type*} [Group H] [Group G] (f : H →* G) (hf : Function.Injective f)
    {y z i : H} (h : y * z = z * y ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ i ^ 2 = 1 ∧
      i ≠ 1 ∧ i * z = z * i ∧ i * y * i⁻¹ = y⁻¹) :
    f y * f z = f z * f y ∧ f y ^ 3 = 1 ∧ f z ^ 3 = 1 ∧ f y ≠ 1 ∧ f z ≠ 1 ∧ f i ^ 2 = 1 ∧
      f i ≠ 1 ∧ f i * f z = f z * f i ∧ f i * f y * (f i)⁻¹ = (f y)⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hne : ∀ a : H, a ≠ 1 → f a ≠ 1 := fun a ha h => ha (hf (h.trans (map_one f).symm))
  refine ⟨?_, ?_, ?_, hne y h4, hne z h5, ?_, hne i h7, ?_, ?_⟩
  · rw [← map_mul, h1, map_mul]
  · rw [← map_pow, h2, map_one]
  · rw [← map_pow, h3, map_one]
  · rw [← map_pow, h6, map_one]
  · rw [← map_mul, h8, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, h9, map_inv]

theorem exists_e9_of_equiv {n : ℕ} (hn : n = 4 ∨ n = 5) {G : Type*} [Group G] {L : Subgroup G}
    (eL : ↥(StatedSL n (ZMod 2)) ≃* ↥L) :
    ∃ y ∈ L, ∃ z ∈ L, ∃ i ∈ L, y * z = z * y ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      i ^ 2 = 1 ∧ i ≠ 1 ∧ i * z = z * i ∧ i * y * i⁻¹ = y⁻¹ := by
  obtain ⟨y, z, i, h⟩ := exists_e9_GL hn
  let f : GL (Fin n) (ZMod 2) →* G := L.subtype.comp (eL.toMonoidHom.comp
    ((MonoidHom.id _).codRestrict (StatedSL n (ZMod 2)) mem_statedSL_two))
  have hf : Function.Injective f := by
    intro a b hab
    have h2 := eL.injective (L.subtype_injective hab)
    exact congrArg Subtype.val h2
  exact ⟨f y, (eL _).2, f z, (eL _).2, f i, (eL _).2, e9_map f hf h⟩

end Matrices

section Situation

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem eq_one_of_fix_quot (hcomm : commV L = ⊤) {x : MulAut W} (hxL : ∀ l ∈ L, x * l = l * x)
    (hx : ∀ w : W, x w * w⁻¹ ∈ fixV L) : x = 1 := by
  have hfix : ∀ c ∈ commV L, x c = c := by
    intro c hc
    unfold commV at hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨l, hl, w, rfl⟩ := hc
      obtain ⟨d, hd'⟩ : ∃ d : W, d = x w * w⁻¹ := ⟨_, rfl⟩
      have hd : d ∈ fixV L := hd' ▸ hx w
      have hxw : x w = d * w := by rw [hd']; group
      have hld : l d = d := (mem_fixV.1 hd) l hl
      have hxl : x (l w) = l (x w) := by
        have h1 := congrArg (fun φ : MulAut W => φ w) (hxL l hl)
        simpa [MulAut.mul_apply] using h1
      rw [map_mul, map_inv, hxl, hxw, map_mul, hld, mul_inv, mul_comm d (l w), mul_assoc,
        mul_inv_cancel_left]
    | one => exact map_one x
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  ext w
  have h1 := hfix w (by rw [hcomm]; trivial)
  simpa using h1

theorem d391_eq_one_of_fix (hD : D3Std M L T L V) {x : MulAut W} (hxM : x ∈ M)
    (hxL : ∀ l ∈ L, x * l = l * x) :
    letI := qAct hD.hyp.Mp_normal
    (∀ q : W ⧸ modFix L (⊤ : Subgroup W), (⟨x, hxM⟩ : ↥M) • q = q) → x = 1 := by
  let _i := qAct hD.hyp.Mp_normal
  intro hq
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hcomm : commV L = ⊤ := Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  refine eq_one_of_fix_quot hcomm hxL fun w => ?_
  have h1 : (QuotientGroup.mk (x w) : W ⧸ modFix L (⊤ : Subgroup W)) = QuotientGroup.mk w :=
    hq (QuotientGroup.mk w)
  rw [QuotientGroup.eq, modFix_top_eq] at h1
  have h2 := (fixV L).inv_mem h1
  rwa [mul_inv_rev, inv_inv, mul_comm] at h2

theorem d391_eq_one_of_pow_three (hD : D3Std M L T L V) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥(StatedSL n (ZMod 2)) ≃* ↥L) {x : MulAut W} (hxM : x ∈ M)
    (hxL : ∀ l ∈ L, x * l = l * x) (hx3 : x ^ 3 = 1) : x = 1 := by
  by_contra hx1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : 0 < n := by rcases hn with rfl | rfl <;> norm_num
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  obtain ⟨y, hyL, z, hzL, i, hiL, hyz, hy3, hz3, hy1, hz1, hi2, hi1, hiz, hiy⟩ :=
    exists_e9_of_equiv hn eL
  have hxL' : ∀ g ∈ L, g ≠ x := by
    intro g hg hgx
    apply hx1
    rw [← hgx] at hxL ⊢
    exact eq_one_of_mem_center_of_equiv hn0 eL hg hxL
  set Sg : Set (MulAut W) := {y, z, x} with hSg
  have hcomm : ∀ a ∈ Sg, ∀ b ∈ Sg, a * b = b * a := by
    intro a ha b hb
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact hyz
    · exact (hxL _ hyL).symm
    · exact hyz.symm
    · rfl
    · exact (hxL _ hzL).symm
    · exact hxL _ hyL
    · exact hxL _ hzL
    · rfl
  have hS3 : ∀ a ∈ Sg, a ^ 3 = 1 := by
    intro a ha
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    exacts [hy3, hz3, hx3]
  set P : Subgroup (MulAut W) := Subgroup.closure Sg with hP
  set A : Subgroup (MulAut W) := Subgroup.zpowers i with hA
  have hyP : y ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hzP : z ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hxP : x ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hPp : IsPGroup 3 P := by
    intro g
    refine ⟨1, ?_⟩
    have h1 := S1417.pow_eq_one_of_mem_closure_comm hS3 hcomm g.2
    exact Subtype.ext (by simpa using h1)
  have hconj : ∀ g ∈ P, i * g * i⁻¹ ∈ P := by
    have hle : P ≤ P.comap (MulAut.conj i).toMonoidHom := by
      rw [hP, Subgroup.closure_le]
      intro g hg
      show i * g * i⁻¹ ∈ P
      simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · rw [hiy]
        exact P.inv_mem hyP
      · rw [hiz, mul_assoc, mul_inv_cancel, mul_one]
        exact hzP
      · rw [← hxL i hiL, mul_assoc, mul_inv_cancel, mul_one]
        exact hxP
    exact fun g hg => hle hg
  have hAn : ∀ a ∈ A, ∀ g ∈ P, a * g * a⁻¹ ∈ P := by
    intro a ha g hg
    rcases S1417.eq_or_of_mem_zpowers_two hi2 hi1 ha with h | h
    · rw [h]
      simpa using hg
    · rw [h]
      exact hconj g hg
  have hfaith : ∀ a ∈ A, (∀ g ∈ P, a * g = g * a) → a = 1 := by
    intro a ha hc
    rcases S1417.eq_or_of_mem_zpowers_two hi2 hi1 ha with h | h
    · exact h
    · exfalso
      have h1 : i * y = y * i := by
        rw [← h]
        exact hc y hyP
      have h2 : y = y⁻¹ := by
        rw [← hiy, h1]
        group
      have h3 : y * y = 1 := by
        nth_rewrite 2 [h2]
        exact mul_inv_cancel y
      have h4 : y ^ 3 = y := by rw [pow_succ, pow_two, h3, one_mul]
      exact hy1 (h4 ▸ hy3)
  have hA2 : IsElemAbelian2 A := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self i k l).eq
    · rcases S1417.eq_or_of_mem_zpowers_two hi2 hi1 ha with h | h
      · rw [h, one_pow]
      · rw [h]
        exact hi2
  have hPAM : P ⊔ A ≤ M := by
    refine sup_le ?_ ?_
    · rw [hP, Subgroup.closure_le]
      intro g hg
      simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      exacts [hLM hyL, hLM hzL, hxM]
    · rw [hA, Subgroup.zpowers_le]
      exact hLM hiL
  have hcov : ∃ (S : Type) (_ : Group S) (_ : Finite S),
      (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥(P ⊔ A), Function.Surjective φ := by
    obtain ⟨S, _, _, hSQT, -, φ, hφ⟩ := hD.hyp.qsqtk
    refine ⟨↥(((P ⊔ A).subgroupOf M).comap φ), inferInstance, inferInstance,
      fun q hq hq2 => ?_, ?_⟩
    · exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt _
        (((P ⊔ A).subgroupOf M).comap φ).subtype_injective).trans (hSQT q hq hq2)
    · refine ⟨(Subgroup.subgroupOfEquivOfLe hPAM).toMonoidHom.comp
        (φ.subgroupComap ((P ⊔ A).subgroupOf M)), fun g => ?_⟩
      obtain ⟨h, hh⟩ := hφ ⟨(g : MulAut W), hPAM g.2⟩
      have hmem : h ∈ ((P ⊔ A).subgroupOf M).comap φ := by
        rw [Subgroup.mem_comap, hh]
        exact g.2
      refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
      show ((φ h : ↥M) : MulAut W) = g
      rw [hh]
  have hcyc := S1417.isCyclic_of_faithful_cover (p := 3) (by norm_num) hPp hA2 hAn hfaith hcov
    (a := i) (Subgroup.mem_zpowers i) hi1
  have hzC : z ∈ P ⊓ Subgroup.centralizer ({i} : Set (MulAut W)) :=
    ⟨hzP, Subgroup.mem_centralizer_singleton_iff.mpr hiz.symm⟩
  have hxC : x ∈ P ⊓ Subgroup.centralizer ({i} : Set (MulAut W)) :=
    ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr (hxL i hiL)⟩
  refine S1417.not_isCyclic_of_four_cubes
    (α := (⟨z, hzC⟩ : ↥(P ⊓ Subgroup.centralizer ({i} : Set (MulAut W)))))
    (β := ⟨x, hxC⟩) ?_ ?_ ?_ ?_ ?_ ?_ hcyc
  · exact Subtype.ext (by simpa using hz3)
  · exact Subtype.ext (by simpa using hx3)
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · intro h
    exact hx1 (congrArg Subtype.val h)
  · intro h
    exact hxL' z hzL (congrArg Subtype.val h).symm
  · intro h
    have h' : x = z⁻¹ := by simpa using congrArg Subtype.val h
    exact hxL' z⁻¹ (L.inv_mem hzL) h'.symm

theorem d391_cent_eq_one (hD : D3Std M L T L V)
    (hodd : ∀ x ∈ M, (∀ l ∈ L, x * l = l * x) → ∀ p : ℕ, p.Prime → p ≠ 2 → x ^ p = 1 →
      x = 1) :
    ∀ x ∈ M, (∀ l ∈ L, x * l = l * x) → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (MulAut W) := M ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
  have hmemC : ∀ c : MulAut W, c ∈ C ↔ c ∈ M ∧ ∀ l ∈ L, c * l = l * c := by
    intro c
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact and_congr_right fun _ => ⟨fun h l hl => (h l hl).symm, fun h l hl => (h l hl).symm⟩
  have hC2 : IsPGroup 2 C := by
    intro c
    have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    refine ⟨(orderOf c).primeFactorsList.length, ?_⟩
    rw [← Nat.eq_prime_pow_of_unique_prime_dvd hc0 ?_]
    · exact pow_orderOf_eq_one c
    · intro d hd hdc
      by_contra hd2
      have h1 := orderOf_pow_orderOf_div hc0 hdc
      set c' := c ^ (orderOf c / d) with hc'
      have h2 : ((c' : ↥C) : MulAut W) = 1 := by
        have hc'C := (hmemC _).1 c'.2
        refine hodd _ hc'C.1 hc'C.2 d hd hd2 ?_
        have h3 := pow_orderOf_eq_one c'
        rw [h1] at h3
        have h4 := congrArg Subtype.val h3
        simpa using h4
      have h3 : c' = 1 := Subtype.ext h2
      rw [h3, orderOf_one] at h1
      exact hd.one_lt.ne h1
  have hconjC : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
    intro m hm c hc
    obtain ⟨hcM, hcL⟩ := (hmemC c).1 hc
    refine (hmemC _).2 ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal (M.inv_mem hm)) l).1 hl
      rwa [inv_inv] at h1
    have h1 := hcL _ hl'
    calc m * c * m⁻¹ * l = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by rw [h1]
      _ = l * (m * c * m⁻¹) := by group
  have hMN : M ≤ Subgroup.normalizer (C : Set (MulAut W)) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconjC m hm c hc, fun hc => ?_⟩
    have h1 := hconjC m⁻¹ (M.inv_mem hm) _ hc
    simpa [mul_assoc] using h1
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hMN hC2
  rw [hD.hyp.pCoreOf_eq_bot] at hle
  intro x hxM hxL
  exact Subgroup.mem_bot.1 (hle ((hmemC x).2 ⟨hxM, hxL⟩))

end Situation

end CFSG.Quasithin.SmithD391
