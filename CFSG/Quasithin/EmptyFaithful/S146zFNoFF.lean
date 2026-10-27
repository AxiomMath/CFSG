module

public import CFSG.Quasithin.EmptyFaithful.S146zFTransv
public import CFSG.Quasithin.EmptyFaithful.S146zNCount
public import CFSG.Quasithin.EmptyFaithful.F918C18
public import CFSG.Quasithin.EmptyFaithful.S146xThreeA
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Range

variable {G : Type} [Group G] {Z U X : Subgroup G}

theorem autOn_tilde_le_range (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    autOn (tildeOf Z X) (tildeOf Z U) ≤ (secRho hXZ hXU).range := by
  intro a ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨x', hx', hxy⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨⟨(x' : G), hx'⟩, ?_⟩
  show conjAct (tildeOf Z U) _ = conjAct (tildeOf Z U) y
  congr 1
  exact Subtype.ext hxy

end Range


section HNo

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem noFF_of_hNo (hNo : NoFaithfulFFInput) (S : Setting146 G T M) (hB : HypB146 T M)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M) {K : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (hHeq : mcOf T = conjClosure K T ⊔ T) (hKL : KbarIsL3Two K ∨ KbarIsA6 K) {B : Subgroup G}
    (hBH : B ≤ mcOf T) (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 (mcOf T)) :
    (B ⊓ pCoreOf 2 (mcOf T)).relIndex B <
      (centralizerMod Zz (uOfL22 T M) B).relIndex (uOfL22 T M) := by
  classical
  by_contra hcon
  push Not at hcon
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  have hFF := isFFModule_tilde_of_offender hF98.toHypF91 hBH hBel hnt hcon
  have hNo' := hNo G T M S hB c19 c20 K hK hHeq hKL
  rw [← hHeq] at hNo'
  have hŨ : IsElemAbelian 2 (tildeOf Zz (uOfL22 T M)) := hF98.toHypF91.isElemAbelian_tilde
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun x hx => by
    rw [S.normalizer_Z]; exact hx
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hUZ : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  let _ : CommGroup ↥(tildeOf Zz (uOfL22 T M)) := commGroupOfElemAbelian hŨ
  have hker : ∀ x : ↥(mcOf T), secRho hHZ hHU x = 1 ↔ (x : G) ∈ pCoreOf 2 (mcOf T) := by
    intro x
    rw [← S.lemma_14_5_15_four hG]
    constructor
    · intro h1
      exact ⟨x.2, hHZ x.2, fun u hu => commutator_mem_of_secRho_eq_one hHZ hHU hUZ h1 hu⟩
    · rintro ⟨-, -, h2⟩
      exact ThreeC.secRho_eq_one_of_comm hHZ hHU hUZ h2
  refine hNo' ↥(tildeOf Zz (uOfL22 T M)) (fun w => Subtype.ext (by simpa using hŨ.2 w w.2))
    (secRho hHZ hHU) hker ?_
  obtain ⟨A, hAX, hA⟩ := hFF
  exact ⟨A, hAX.trans (autOn_tilde_le_range hHZ hHU), hA⟩

end HNo


section Count

variable {G : Type} [Group G] [Finite G]

theorem rank_lt_of_nonFF {Z U UK Up X C Dg : Subgroup G}
    (hUab : IsElemAbelian 2 U) (hXab : IsElemAbelian 2 X)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hUKU : UK ≤ U) (hUpU : Up ≤ U) (hZK : Z ≤ UK) (hZp : Z ≤ Up) (hinf : UK ⊓ Up = Z)
    (hCU : C ≤ U)
    (hdec : ∀ v ∈ U, ∃ a ∈ UK, ∃ b ∈ Up, ∃ c ∈ C, v = a * (b * c))
    (hCc : ∀ c ∈ C, ∀ e ∈ X, c * e * c⁻¹ * e⁻¹ ∈ Z)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hXK : ∀ e ∈ X, ∀ y ∈ UK, e * y * e⁻¹ ∈ UK) (hXp : ∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ ∈ Up)
    (hXU : ∀ e ∈ X, ∀ y ∈ U, e * y * e⁻¹ ∈ U)
    (hDgX : Dg ≤ X) (hDg : ∀ x ∈ Dg, ∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z)
    (hfaith : ∀ x ∈ X, (∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z) → x ∈ Dg)
    (hnt : ¬ X ≤ Dg)
    (hNK : ¬ X ≤ centralizerMod Z X UK →
      mIdx X (centralizerMod Z X UK) + 1 ≤ mIdx UK (centralizerMod Z UK X))
    (hNp : ¬ X ≤ centralizerMod Z X Up →
      mIdx X (centralizerMod Z X Up) + 1 ≤ mIdx Up (centralizerMod Z Up X)) :
    mIdx X Dg < mIdx U (centralizerMod Z U X) := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hXp2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => isElemAbelian_comm hXab hx hy
  set XK := centralizerMod Z X UK with hXK'
  set Xp := centralizerMod Z X Up with hXp'
  set CU := centralizerMod Z U X with hCU'
  have hXZ : ∀ e ∈ X, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := fun e he z hz =>
    (Subgroup.mem_normalizer_iff.mp (hXN he) z).mp hz
  have hDgXK : Dg ≤ XK := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUKU hy)⟩
  have hDgXp : Dg ≤ Xp := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUpU hy)⟩
  have hXKXp : XK ⊓ Xp = Dg := by
    apply le_antisymm
    · rintro x ⟨hxK, hxp⟩
      refine hfaith x hxK.1 fun v hv => ?_
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdec v hv
      have haU := hUKU ha
      have hbU := hUpU hb
      have hcU := hCU hc
      have hbcU : b * c ∈ U := U.mul_mem hbU hcU
      have hexp : x * (a * (b * c)) * x⁻¹ * (a * (b * c))⁻¹ =
          (x * a * x⁻¹ * a⁻¹) * ((x * b * x⁻¹ * b⁻¹) * (x * c * x⁻¹ * c⁻¹)) := by
        rw [comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) haU hbcU,
          comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) hbU hcU]
      rw [hexp]
      have h3 : x * c * x⁻¹ * c⁻¹ ∈ Z := by
        have := hCc c hc x hxK.1
        have e1 : x * c * x⁻¹ * c⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
        rw [e1]; exact Z.inv_mem this
      exact Z.mul_mem (hxK.2.2 a ha) (Z.mul_mem (hxp.2.2 b hb) h3)
    · exact le_inf hDgXK hDgXp
  have hXKX : XK ≤ X := centralizerMod_le_left _ _ _
  have hXpX : Xp ≤ X := centralizerMod_le_left _ _ _
  have hsupX : XK ⊔ Xp ≤ X := sup_le hXKX hXpX
  have hPsupX : IsPGroup 2 ↥(XK ⊔ Xp) := hXp2.to_le hsupX
  have hP2 : mIdx (XK ⊔ Xp) Dg = mIdx XK Dg + mIdx Xp Dg :=
    ThreeC.mIdx_sup_of_inf_eq (fun x hx y hy => hXc x (hXKX hx) y (hXpX hy)) hDgXK hDgXp hXKXp hPsupX
  have hm1 : mIdx X Dg = mIdx X (XK ⊔ Xp) + mIdx (XK ⊔ Xp) Dg :=
    ThreeC.mIdx_add hXp2 hsupX (hDgXK.trans le_sup_left)
  have hmXK : mIdx X Dg = mIdx X XK + mIdx XK Dg := ThreeC.mIdx_add hXp2 hXKX hDgXK
  have hmXp : mIdx X Dg = mIdx X Xp + mIdx Xp Dg := ThreeC.mIdx_add hXp2 hXpX hDgXp
  have hsum : mIdx UK (centralizerMod Z UK X) + mIdx Up (centralizerMod Z Up X) ≤ mIdx U CU :=
    ThreeC.mIdx_centralizerMod_sum_le hUp2 hUc hUKU hUpU hZK hZp hinf hUN hXZ hXK hXp hXU
  have hself : ∀ Y : Subgroup G, mIdx Y Y = 0 := by
    intro Y
    unfold mIdx
    rw [Subgroup.relIndex_self]
    simp
  by_cases hK : X ≤ XK
  · by_cases hp : X ≤ Xp
    · exact absurd (hXKXp ▸ le_inf hK hp) hnt
    · have hXKeq : XK = X := le_antisymm hXKX hK
      have hDgeq : Dg = Xp := by
        rw [← hXKXp, hXKeq]; exact inf_eq_right.mpr hXpX
      have hz : mIdx Xp Dg = 0 := by rw [hDgeq]; exact hself _
      have hNp' := hNp hp
      omega
  · by_cases hp : X ≤ Xp
    · have hXpeq : Xp = X := le_antisymm hXpX hp
      have hDgeq : Dg = XK := by
        rw [← hXKXp, hXpeq]; exact inf_eq_left.mpr hXKX
      have hz : mIdx XK Dg = 0 := by rw [hDgeq]; exact hself _
      have hNK' := hNK hK
      omega
    · have hNK' := hNK hK
      have hNp' := hNp hp
      omega

end Count


section Ctx

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem conjClosure_eq_perfectCore (S : Setting146 G T M) {K : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (hcase : perfectCore (mcOf T) = K ∨
      ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) ∧ perfectCore (mcOf T) = K ⊔ conjSub t K) :
    conjClosure K T = perfectCore (mcOf T) := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hcperf : perfectCore (mcOf T) ≤ mcOf T := perfectCore_le _
  have hHnorm : mcOf T ≤ Subgroup.normalizer ((perfectCore (mcOf T) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcperf).mp (perfectCore_normal _)
  apply le_antisymm
  · refine conjClosure_le fun t' ht' z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm (hTH ht')) z).mp
      (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK) hz)
  · rcases hcase with hper | ⟨t, htT, -, hper⟩
    · rw [hper]; exact le_conjClosure K T
    · rw [hper]
      refine sup_le (le_conjClosure K T) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact mem_conjClosure htT hz

theorem noFF_ctx (hNo : NoFaithfulFFInput) (h21 : Stage14621) (h22 : Stage14622)
    (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    (c23 : Conc14623 T M) {K U₁ U₂ : Subgroup G} {s : G} (hK : K ∈ cComp (mcOf T))
    (c21 : Conc14621 T K) (hdec : IsDecompUK T M K U₁ U₂ s) {B : Subgroup G} (hBH : B ≤ mcOf T)
    (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 (mcOf T)) :
    mIdx B (B ⊓ pCoreOf 2 (mcOf T)) <
      mIdx (uOfL22 T M) (centralizerMod Zz (uOfL22 T M) B) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hBp : IsPGroup 2 B := isPGroup_of_isElemAbelian hBel
  have conv : (B ⊓ pCoreOf 2 (mcOf T)).relIndex B <
      (centralizerMod Zz (uOfL22 T M) B).relIndex (uOfL22 T M) →
      mIdx B (B ⊓ pCoreOf 2 (mcOf T)) < mIdx (uOfL22 T M) (centralizerMod Zz (uOfL22 T M) B) := by
    intro hlt
    rw [HypF98.relIndex_eq_two_pow_mIdx hBp, HypF98.relIndex_eq_two_pow_mIdx hUp] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  rcases c21 with ⟨hper, hKL⟩ | ⟨⟨t, htT, htn, hper⟩, hL3⟩ | ⟨Kp, hKp, hne, hHK, hHKp, hper, hL3K, hL3Kp⟩
  · have hK₀ := conjClosure_eq_perfectCore S hK (Or.inl hper)
    have hHeq : mcOf T = conjClosure K T ⊔ T := by rw [hK₀]; exact c23.1.2
    exact conv (noFF_of_hNo hNo S hB c19 c20 hK hHeq hKL hBH hBel hnt)
  · have hK₀ := conjClosure_eq_perfectCore S hK (Or.inr ⟨t, htT, htn, hper⟩)
    have hHeq : mcOf T = conjClosure K T ⊔ T := by rw [hK₀]; exact c23.1.2
    exact conv (noFF_of_hNo hNo S hB c19 c20 hK hHeq (Or.inl hL3) hBH hBel hnt)
  ·
    have hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp := by
      intro L hL
      have hle : L ≤ perfectCore (mcOf T) :=
        le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
      exact cComp_eq_of_le_sup hL hK hKp (hper ▸ hle)
    obtain ⟨⟨U₁', U₂', s', hdecKp⟩, -⟩ := h22 G T M S hB c19 c20 Kp hKp
      (h21 G T M S hB c19 c20 Kp hKp)
    have cK : ThreeC.CCtx T M K U₁ U₂ s := ThreeC.CCtx.ofDecomp S c19 hK hL3K hdec
    have hXN : B ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
      rw [S.normalizer_Z]; exact hBH he
    have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
    have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hK)
    have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKp)
    have h4 : centralizerMod Zz (mcOf T) (uOfL22 T M) = pCoreOf 2 (mcOf T) :=
      S.lemma_14_5_15_four hG
    have hNK : ¬ B ≤ centralizerMod Zz B (⁅uOfL22 T M, K⁆ ⊔ Zz) →
        mIdx B (centralizerMod Zz B (⁅uOfL22 T M, K⁆ ⊔ Zz)) + 1 ≤
          mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz) (centralizerMod Zz (⁅uOfL22 T M, K⁆ ⊔ Zz) B) := fun hn =>
      input14624NonFF_proof G T M S hB c19 K U₁ U₂ s hK hL3K hdec B hBH (fun e he => hHK (hBH he))
        hBel hn
    have hNp : ¬ B ≤ centralizerMod Zz B (⁅uOfL22 T M, Kp⁆ ⊔ Zz) →
        mIdx B (centralizerMod Zz B (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) + 1 ≤
          mIdx (⁅uOfL22 T M, Kp⁆ ⊔ Zz) (centralizerMod Zz (⁅uOfL22 T M, Kp⁆ ⊔ Zz) B) := fun hn =>
      input14624NonFF_proof G T M S hB c19 Kp U₁' U₂' s' hKp hL3Kp hdecKp B hBH
        (fun e he => hHKp (hBH he)) hBel hn
    exact rank_lt_of_nonFF (Z := Zz) (U := uOfL22 T M) (UK := ⁅uOfL22 T M, K⁆ ⊔ Zz)
      (Up := ⁅uOfL22 T M, Kp⁆ ⊔ Zz) (X := B) (C := cuOf T M)
      (Dg := B ⊓ pCoreOf 2 (mcOf T)) hUab hBel hUN hUKU hUpU le_sup_right le_sup_right
      (inf_eq_Z_two S c23 hK hKp hne) (cuOf_le T M)
      (fun v hv => exists_decomp_two S c23 hcomps hK hKp hv)
      (fun c hc e he => (mem_cuOf.mp hc).2.2 e (hBH he)) hXN
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_sup (hHK (hBH he)) (le_normalizer_conjClosure _ _ (hBH he))
          (hXN he)) y).mp hy)
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_sup (hHKp (hBH he)) (le_normalizer_conjClosure _ _ (hBH he))
          (hXN he)) y).mp hy)
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hBH he)) y).mp hy)
      inf_le_left
      (fun x hx v hv => by
        have hxQ : x ∈ centralizerMod Zz (mcOf T) (uOfL22 T M) := by
          rw [h4]; exact hx.2
        exact hxQ.2.2 v hv)
      (fun x hx h => ⟨hx, by
        have : x ∈ centralizerMod Zz (mcOf T) (uOfL22 T M) := ⟨hBH hx, hXN hx, h⟩
        rwa [h4] at this⟩)
      (fun hle => hnt (hle.trans inf_le_right)) hNK hNp

end Ctx

end CFSG.Quasithin
