module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpLeviCover
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBSupported
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBTwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TypeBDatum SpCoord Multiplicative

theorem FrameBs.sectionFrameAut_eq_map_congr {G : Type} [Group G] [Finite G] {p r : ℕ}
    {X Bs : Subgroup G} {hBsN : Bs ≤ Subgroup.normalizer (X : Set G)}
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (κ : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hκ : ∀ f, ((κ f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hinj : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X))
    {H : Subgroup G} (hHX : H ≤ X) :
    FrameBs.sectionFrameAut (X.subtype.comp σ) H =
      (ggAutomizer ((H.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X))
        (ggGamma X hBsN).range).map (MulAut.congr κ.symm).toMonoidHom := by
  ext τ
  rw [mem_map_congr_ggAutomizer_iff]
  constructor
  · rintro ⟨n, hn, hact⟩
    refine ⟨MulAut.conj (⟨n, hHX hn⟩ : ↥X),
      Subgroup.mem_map.mpr ⟨⟨n, hHX hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩, fun c => ?_⟩
    rw [hκ c, hκ (τ c)]
    have h : (⟨n, hHX hn⟩ : ↥X) * σ c * (⟨n, hHX hn⟩ : ↥X)⁻¹ = σ (τ c) := Subtype.ext (hact c)
    rw [← h, map_mul, map_mul, map_inv]
  · rintro ⟨g, hg, hact⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hn, fun f => ?_⟩
    have h := hact f
    rw [hκ f, hκ (τ f), ← map_inv, ← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hinj h)

theorem card_le_of_forall_mem_eq_one {p m : ℕ} [NeZero p] (Z : Finset (Fin m))
    {P : (Fin m → Multiplicative (ZMod p)) → Prop} (hP : ∀ f, (∀ i ∈ Z, f i = 1) → P f) :
    p ^ (m - Z.card) ≤ Nat.card {f // P f} := by
  classical
  let e : ({i : Fin m // i ∉ Z} → Multiplicative (ZMod p)) → {f // P f} :=
    fun g => ⟨fun i => if h : i ∈ Z then 1 else g ⟨i, h⟩, hP _ fun i hi => by simp [hi]⟩
  have he : Function.Injective e := by
    intro g g' hgg
    funext i
    have hi := congrFun (congrArg Subtype.val hgg) i.1
    simpa [e, i.2] using hi
  have hcard : Nat.card ({i : Fin m // i ∉ Z} → Multiplicative (ZMod p)) = p ^ (m - Z.card) := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := {i : Fin m // i ∉ Z}), Fintype.card_subtype_compl,
      Fintype.card_coe, Fintype.card_fin]
  rw [← hcard]
  exact Nat.card_le_card_of_injective e he

theorem card_le_of_forall_mem_eq_smul {p m : ℕ} [NeZero p] (S : Finset (Fin m))
    (hS : S.Nonempty) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    {P : (Fin m → Multiplicative (ZMod p)) → Prop}
    (hP : ∀ f (a : ZMod p), (∀ i ∈ S, f i = ofAdd (s i * a)) → P f) :
    p ^ (m - S.card + 1) ≤ Nat.card {f // P f} := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let e : ZMod p × ({i : Fin m // i ∉ S} → Multiplicative (ZMod p)) → {f // P f} :=
    fun ag => ⟨fun i => if h : i ∈ S then ofAdd (s i * ag.1) else ag.2 ⟨i, h⟩,
      hP _ ag.1 fun i hi => by simp [hi]⟩
  have he : Function.Injective e := by
    rintro ⟨a, g⟩ ⟨a', g'⟩ hgg
    have h₁ := congrFun (congrArg Subtype.val hgg) i₀
    simp only [e, dif_pos hi₀] at h₁
    have ha : a = a' := by
      have h₂ := congrArg (fun z => s i₀ * toAdd z) h₁
      simpa only [toAdd_ofAdd, ← mul_assoc, hs i₀, one_mul] using h₂
    have hg : g = g' := by
      funext i
      have hi := congrFun (congrArg Subtype.val hgg) i.1
      simpa [e, i.2] using hi
    exact Prod.ext ha hg
  have hcard : Nat.card (ZMod p × ({i : Fin m // i ∉ S} → Multiplicative (ZMod p))) =
      p ^ (m - S.card + 1) := by
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_eq_fintype_card (α := {i : Fin m // i ∉ S}),
      Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, pow_succ, mul_comm]
  rw [← hcard]
  exact Nat.card_le_card_of_injective e he

private theorem ggTBJ_sp_sideDatum_of_cover_aux {G : Type} [Group G] [Finite G]
    {p m c : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hc : c ≤ 2) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ₀ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ↥X ψ₀ (ggGamma X hBsN).range)
    (y : MulAut ↥X) (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
      ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCX : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ (c + 1)) :
    GGResSideDatum p Bs X J ∨ (c = 2 ∧ GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨κ, hfull, hblock, -, hAinn⟩ :=
    ggTBJ_sp_cover_block_automizers hp hp2 hpq ψ₀ _ hA y hy hy1 hJ hcount
  have hinj : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) := by
    intro a b h
    have hc : a⁻¹ * b ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut ↥X => φ g) h
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  let eX : ↥X ≃* (MulAut.conj : ↥X →* MulAut ↥X).range := MonoidHom.ofInjective hinj
  let κ' : (Fin m → Multiplicative (ZMod p)) →* (MulAut.conj : ↥X →* MulAut ↥X).range :=
    ((ggGamma X hBsN).range.subtype.comp κ.toMonoidHom).codRestrict _ fun f => hAinn (κ f).2
  let σ : (Fin m → Multiplicative (ZMod p)) →* ↥X := eX.symm.toMonoidHom.comp κ'
  have hσ : ∀ f, ((κ f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f) := by
    intro f
    have h := congrArg Subtype.val (eX.apply_symm_apply (κ' f))
    exact h.symm
  have hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1 := by
    intro z hz _
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  obtain ⟨Θ, hΘ, hAut⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZp σ κ hσ
  have hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs := (FrameBs.sectionFrame_model hBs hSC hBsN σ κ hσ).1
  have hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ) := by
    rw [hAut X le_rfl, FrameBs.sectionFrameAut_eq_map_congr σ κ hσ hinj le_rfl,
      Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hfull]
  have hJaut := hAut J hJX
  rw [FrameBs.sectionFrameAut_eq_map_congr σ κ hσ hinj hJX] at hJaut
  have hcardJ := (FrameBs.card_centralizer_frame Θ σ hΘ hmem hJX).2
  have hcent : ∀ f, (∀ j ∈ J.subgroupOf X, (κ f : MulAut ↥X) j = j) →
      ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G) := by
    intro f hf j hj
    have h := hf ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
    rw [hσ f, MulAut.conj_apply] at h
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    calc ((σ f : ↥X) : G) * j = ((σ f : ↥X) : G) * j * ((σ f : ↥X) : G)⁻¹ *
        ((σ f : ↥X) : G) := by group
      _ = j * ((σ f : ↥X) : G) := by rw [h']
  rcases hblock with ⟨Z, hZ2, hZm, hZaut, hZfix⟩ | ⟨S, s, hs, hS3, hsgn, hSaut, hSfix⟩
  ·
    have hlow : p ^ (m - Z.card) ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} :=
      card_le_of_forall_mem_eq_one Z fun f hf => hcent f (hZfix f hf)
    have hcor : m - Z.card ≤ c := by
      have h1 : p ^ (m - Z.card) * p ≤ p ^ (c + 1) :=
        calc p ^ (m - Z.card) * p ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
              ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.mul_le_mul hlow hCX
          _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hcardJ.symm
          _ ≤ p ^ (c + 1) := hCJ
      rw [← pow_succ] at h1
      have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
      omega
    have hJform : ggAutomizer J Bs = (signedSupportedAut m p Z).map (liftBs Θ) := by
      rw [hJaut, hZaut]
    have hres := ggTBJTypeB_sideDatum_signedSupported hp2 (by omega) hBs Θ hX (S := Z)
      (by omega) (by omega) (by omega) hJform
    by_cases hdel : m - Z.card = 1
    · exact Or.inl (hres.1 hdel)
    · exact Or.inr ⟨by omega, hres.2 (by omega)⟩
  ·
    have hSm : S.card ≤ m := by simpa using Finset.card_le_univ S
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hlow : p ^ (m - S.card + 1) ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} :=
      card_le_of_forall_mem_eq_smul S hSne s hs fun f a hf => hcent f (hSfix f a hf)
    have hcor : m + 1 - S.card ≤ c := by
      have h1 : p ^ (m - S.card + 1) * p ≤ p ^ (c + 1) :=
        calc p ^ (m - S.card + 1) * p ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
              ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.mul_le_mul hlow hCX
          _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hcardJ.symm
          _ ≤ p ^ (c + 1) := hCJ
      rw [← pow_succ] at h1
      have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
      omega
    have hJform : ggAutomizer J Bs = (twistedPermAut m p S s hs).map (liftBs Θ) := by
      rw [hJaut, hSaut]
    have hres := ggTBJTypeB_sideDatum_twistedPerm hp2 (by omega) hBs Θ hX (S := S)
      (by omega) (by omega) hs hJform
    by_cases hdel : m + 1 - S.card = 1
    · exact Or.inl (hres.1 hdel)
    · exact Or.inr ⟨by omega, hres.2 (by omega)⟩

theorem ggTBJ_sp_sideDatum_of_cover {G : Type} [Group G] [Finite G]
    {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 2 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ₀ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ↥X ψ₀ (ggGamma X hBsN).range)
    (y : MulAut ↥X) (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
      ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCX : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  rcases ggTBJ_sp_sideDatum_of_cover_aux (c := 2) hp2 hm (by omega) hBs hSC hBsN hZ hpq ψ₀ hA
    y hy hy1 hJX hJ hcount hCX hCJ with h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem ggTBJ_sp_sideDatum_of_cover_of_centralizer_le_sq {G : Type} [Group G] [Finite G]
    {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 2 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ₀ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ↥X ψ₀ (ggGamma X hBsN).range)
    (y : MulAut ↥X) (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
      ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCX : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2) :
    GGResSideDatum p Bs X J := by
  rcases ggTBJ_sp_sideDatum_of_cover_aux (c := 1) hp2 hm (by omega) hBs hSC hBsN hZ hpq ψ₀ hA
    y hy hy1 hJX hJ hcount hCX hCJ with h | ⟨hc, _⟩
  · exact h
  · omega

end CFSG.StandardType

end
