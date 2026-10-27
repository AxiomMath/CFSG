module

public import CFSG.RankThree.GF2n.Stroth80.Sec712
public import CFSG.RankThree.GF2n.Stroth80.Sec8Assembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Sp

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_isPGroup_CN (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    IsPGroup 2 ↥(hc.CN t) := by
  obtain ⟨r, hr, -, hopp, -⟩ := sec8_Z0_data h51 hA hc hs hZ0
  have hZL := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hL2 : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs.toSec5.width hs.toSec5.n_gt
    hs.toSec5.noA2 hs.toSec5.gen
  have hsq : ∀ x ∈ hc.CN t, x ^ 2 ∈ Z0 := hopp.2.2.2.2.2.2.2.1
  intro x
  obtain ⟨k, hk⟩ := hL2 ⟨(x : G) ^ 2, hZL (hsq x x.2)⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h1 : ((x : G) ^ 2) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  show (x : G) ^ (2 ^ (k + 1)) = 1
  rw [pow_succ, mul_comm, pow_mul]
  exact h1

theorem sec8_simple_quot (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) :
    ∃ (S : Type) (_ : Group S) (π : ↥(Rt M (LB M Q B) t) →* S), Function.Surjective π ∧
      (∀ r : ↥(Rt M (LB M Q B) t), π r = 1 ↔ (r : G) ∈ hc.CN t) ∧ IsSimpleGroup S := by
  classical
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨m, hm2, K', hF, hFin, hcard, hnat⟩ := hs.sp
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hcard.trans hZ2)
  have hK4 : 4 ≤ Nat.card K' := by rw [hcard]; exact hq4
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  obtain ⟨h1, -, -⟩ := endg_sp_facts hK4 hm2
  refine ⟨_, inferInstance,
    (MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict, ?_, ?_, h1⟩
  · exact (MulEquiv.subgroupCongr hφr).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  · intro r
    show (MulEquiv.subgroupCongr hφr) (φ.rangeRestrict r) = 1 ↔ _
    rw [map_eq_one_iff _ (MulEquiv.subgroupCongr hφr).injective]
    have : φ.rangeRestrict r = 1 ↔ φ r = 1 := by
      rw [← Subtype.coe_inj]; rfl
    rw [this, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]

theorem sec8_DR (h51 : Stroth51Statement) (hA : Sec8AExistsStatement) (h54 : Stroth54Statement)
    (hge : Stroth6NbarGeStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ x ∈ Rt M (LB M Q B) t, (∀ c ∈ hc.CN t, ⁅x, c⁆ ∈ Q) → x ∈ hc.CN t := by
  classical
  intro x hxR hxc
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr, hZcard, hopp, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  set R := Rt M (LB M Q B) t with hRdef
  set N := hc.CN t with hNdef
  obtain ⟨S, iS, π, hsurj, hker, hsimple⟩ := sec8_simple_quot hc hs
  have hRM : R ≤ M := hc.Rt_le_M t
  have hNR : N ≤ R := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hnormQ : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hNnorm : ∀ g ∈ R, ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
    intro g hg y hy
    refine mem_CN_conj_of_normalizes hc (hRM hg) ?_ ?_ hy
    · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
    · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)
  let D : Subgroup G :=
    { carrier := {y | y ∈ M ∧ ∀ c ∈ N, ⁅y, c⁆ ∈ Q}
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨M.mul_mem haM hbM, fun c hc' => ?_⟩
        have e : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Q.mul_mem (hnormQ a haM _ (hb c hc')) (ha c hc')
      one_mem' := ⟨M.one_mem, fun c _ => by simpa [commutatorElement_def] using Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨M.inv_mem haM, fun c hc' => ?_⟩
        have e : ⁅a⁻¹, c⁆ = a⁻¹ * ⁅a, c⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hnormQ a⁻¹ (M.inv_mem haM) _ (Q.inv_mem (ha c hc')) }
  have hD : ∀ g ∈ R, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    rintro g hg d ⟨hdM, hd⟩
    refine ⟨M.mul_mem (M.mul_mem (hRM hg) hdM) (M.inv_mem (hRM hg)), fun c hc' => ?_⟩
    have hc'' : g⁻¹ * c * g⁻¹⁻¹ ∈ N := hNnorm g⁻¹ (R.inv_mem hg) c hc'
    have e : ⁅g * d * g⁻¹, c⁆ = g * ⁅d, g⁻¹ * c * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hnormQ g (hRM hg) _ (hd _ hc'')
  have hxD : x ∈ D ⊓ R := ⟨⟨hRM hxR, hxc⟩, hxR⟩
  rcases simpleDichotomy_holds G R N D S π hNR hsurj hker hD with h1 | h2
  · exact h1 hxD
  · exfalso
    have hLR : LB M Q B ≤ R := le_Rt (M := M) (LB M Q B) ht
    have hL'R : LB M Q (conjSubgroup r B) ≤ R := by
      calc LB M Q (conjSubgroup r B) ≤ LB M Q B ⊔ LB M Q (conjSubgroup r B) := le_sup_right
        _ = R := hr.gen.symm
    have hDRn : D ⊓ R ≤ Subgroup.normalizer (N : Set G) := fun d hd =>
      Subgroup.mem_normalizer_fintype fun y hy => hNnorm d hd.2 y hy
    have hcZ0 : ∀ ρ ∈ R, ∀ c ∈ N, ⁅ρ, c⁆ ∈ Z0 := by
      intro ρ hρ c hc'
      obtain ⟨d, hd, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hDRn (h2 hρ)
      have e : ⁅d * k, c⁆ = (d * ⁅k, c⁆ * d⁻¹) * ⁅d, c⁆ := by
        simp only [commutatorElement_def]; group
      have hkc : ⁅k, c⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1 k hk c hc'
      have hdn : d ∈ Subgroup.normalizer (Z0 : Set G) :=
        hZ0.mem_normalizer (fun ρ' hρ' y hy => hnormQ ρ' (hRM hρ') y hy) hd.2
      rw [e]
      exact Z0.mul_mem ((Subgroup.mem_normalizer_iff.mp hdn _).mp hkc)
        (hQZ0 (hd.1.2 c hc'))
    have hNZ0 : N ≤ Z0 := by
      intro c hc'
      have hA1 : c ∈ LB M Q B ⊓ N := (hopp.2.2.2.2.2.2.2.2.1 c hc').mpr fun l hl =>
        hcZ0 l (hLR hl) c hc'
      have hA2 : c ∈ LB M Q (conjSubgroup r B) ⊓ N :=
        (hopp.2.2.2.2.2.2.2.2.2 c hc').mpr fun l hl => hcZ0 l (hL'R hl) c hc'
      have : c ∈ (LB M Q B ⊓ N) ⊓ (LB M Q (conjSubgroup r B) ⊓ N) := ⟨hA1, hA2⟩
      rw [hopp.2.2.2.2.2.1] at this
      exact this
    have hcard := Subgroup.card_le_of_le hNZ0
    have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z := by
      rw [← hIZ]; exact hZcard
    have hlarge : Nat.card Q * Nat.card Z < Nat.card N := Sec8Hyp.large h54 hge hs
    omega

end Sp

section F2


theorem step85F2_holds (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hZt : Sec8ZtStatement) (h54 : Stroth54Statement)
    (hge : Stroth6NbarGeStatement) :
    Step85F2Statement := by
  classical
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  set R := Rt M (LB M Q B) t with hRdef
  set N := hc.CN t with hNdef
  set X := NormH0 M Z Z0 with hXdef
  have hRM : R ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ R := le_Rt (M := M) (LB M Q B) ht
  have hQN : Q ≤ N := sec8_Q_le_CN hc ht
  have hNR : N ≤ R := fun y hy => (Ctx.mem_CN.1 hy).1
  have hRX : R ≤ X := sec8_Rt_le_NormH0 hc hZ0
  have hXH : X ≤ H0 M Z := fun x hx => hx.1
  have hXM : X ≤ M := fun x hx => (hx.1).1
  have hQR : Q ≤ R := hQN.trans hNR
  have hXRN : ∀ g ∈ X, conjSubgroup g R = R ∧ conjSubgroup g (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z t := fun g hg => sec8_normalizes_of_zt hZt h51 hA hc hs hZ0 hg
  have hXR : ∀ g ∈ X, ∀ y ∈ R, g * y * g⁻¹ ∈ R := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp (hXRN g hg).1) y).mp hy
  have hXN : ∀ g ∈ X, ∀ y ∈ N, g * y * g⁻¹ ∈ N := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp
      (conjSubgroup_CN_eq hc (hXM hg) (hXRN g hg).1 (hXRN g hg).2)) y).mp hy
  haveI hRn : ((bar M Q R).subgroupOf (bar M Q X)).Normal := sec712_bar_normal hXR
  haveI hNn : ((bar M Q N).subgroupOf (bar M Q X)).Normal := sec712_bar_normal hXN
  have hN2 : IsPGroup 2 ↥((bar M Q N).subgroupOf (bar M Q X)) :=
    sec712_isPGroup_bar (sec8_isPGroup_CN h34 h51 hA hc hs hZ0)
  have hDR := sec8_DR h51 hA h54 hge hc hs hZ0
  have hbarmono : ∀ {S T : Subgroup G}, S ≤ T → bar M Q S ≤ bar M Q T := fun h =>
    Subgroup.map_mono fun x hx => h hx
  have hkey : ∀ y c : ↥M, QuotientGroup.mk' (Q.subgroupOf M) c *
      QuotientGroup.mk' (Q.subgroupOf M) y = QuotientGroup.mk' (Q.subgroupOf M) y *
      QuotientGroup.mk' (Q.subgroupOf M) c → ⁅(y : G), (c : G)⁆ ∈ Q := by
    intro y c h
    have h3 : QuotientGroup.mk' (Q.subgroupOf M) ⁅y, c⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
    exact h3
  have hmkX : ∀ c : G, c ∈ X → ∀ hcM : c ∈ M, ∃ ĉ : ↥(bar M Q X),
      (ĉ : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hcM⟩ := fun c hcX hcM =>
    ⟨⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hcM⟩,
      Subgroup.mem_map.mpr ⟨⟨c, hcM⟩, Subgroup.mem_subgroupOf.mpr hcX, rfl⟩⟩, rfl⟩
  refine charTwo_of_centralizer_core ((bar M Q R).subgroupOf (bar M Q X))
    ((bar M Q N).subgroupOf (bar M Q X)) hN2 ?_
    ((bar M Q (LB M Q B)).subgroupOf (bar M Q X))
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hbarmono hLR (Subgroup.mem_subgroupOf.mp hx))) ?_
  · intro xh hxh
    obtain ⟨hcent, hxR⟩ := hxh
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp xh.2
    have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have hyR : (y : G) ∈ R := by
      have h1 : (xh : Mbar M Q) ∈ bar M Q R := Subgroup.mem_subgroupOf.mp hxR
      rw [← hyx] at h1
      exact (Tim37.mk_mem_bar_iff' hQR y).mp h1
    have hyc : ∀ c ∈ N, ⁅(y : G), c⁆ ∈ Q := by
      intro c hc'
      have hcM : c ∈ M := hRM (hNR hc')
      obtain ⟨ĉ, hĉ⟩ := hmkX c (hRX (hNR hc')) hcM
      have hĉN : ĉ ∈ (bar M Q N).subgroupOf (bar M Q X) := by
        rw [Subgroup.mem_subgroupOf, hĉ]
        exact (Tim37.mk_mem_bar_iff' hQN ⟨c, hcM⟩).mpr hc'
      have h1 := Subgroup.mem_centralizer_iff.mp hcent ĉ hĉN
      have h1' : QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hcM⟩ * (xh : Mbar M Q) =
          (xh : Mbar M Q) * QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hcM⟩ := by
        rw [← hĉ]; exact congrArg Subtype.val h1
      rw [← hyx] at h1'
      exact hkey y ⟨c, hcM⟩ h1'
    have hyN : (y : G) ∈ N := hDR _ hyR hyc
    rw [Subgroup.mem_subgroupOf, ← hyx]
    exact (Tim37.mk_mem_bar_iff' hQN y).mpr hyN
  · intro xh hcent hodd' hΛcomm
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp xh.2
    have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have hxm : xh ^ orderOf xh = 1 := pow_orderOf_eq_one xh
    have hym : (y : G) ^ orderOf xh ∈ Q := by
      have h1 : QuotientGroup.mk' (Q.subgroupOf M) (y ^ orderOf xh) = 1 := by
        rw [map_pow, hyx]; exact congrArg Subtype.val hxm
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hcomm : ∀ l ∈ LB M Q B, ⁅(y : G), l⁆ ∈ Q := by
      intro l hl
      have hlM : l ∈ M := hRM (hLR hl)
      obtain ⟨lh, hlh⟩ := hmkX l (hRX (hLR hl)) hlM
      have hlhΛ : lh ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q X) := by
        rw [Subgroup.mem_subgroupOf, hlh]
        exact (Tim37.mk_mem_bar_iff' sec39_Q_le_LB ⟨l, hlM⟩).mpr hl
      have h1 := hΛcomm lh hlhΛ
      have h1' : QuotientGroup.mk' (Q.subgroupOf M) ⟨l, hlM⟩ * (xh : Mbar M Q) =
          (xh : Mbar M Q) * QuotientGroup.mk' (Q.subgroupOf M) ⟨l, hlM⟩ := by
        rw [← hlh]; exact congrArg Subtype.val h1
      rw [← hyx] at h1'
      exact hkey y ⟨l, hlM⟩ h1'
    have hyQ : (y : G) ∈ Q :=
      mem_Q_of_comm_LB_of_odd h34 hc hs.toSec5 (hXH hyX) hodd' hym hcomm
    apply Subtype.ext
    rw [← hyx]
    show QuotientGroup.mk' (Q.subgroupOf M) y = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyQ

end F2

end CFSG.RankThree.GF2n.Stroth80
