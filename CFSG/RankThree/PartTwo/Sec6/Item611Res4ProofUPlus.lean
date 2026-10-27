module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofUPlusTools
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofUPlusL2
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KS611CentChar3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ (K : Subgroup X) (_ : K.Normal), Nat.card K = 3 ∧
        (Nonempty (X ⧸ K ≃* projSU 4 3 1) ∨ Nonempty (X ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
      Blueprint.ChevalleyExceptionalModel X .G2 3 1 ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (X ≃* projSU 4 3 1)) →
    ∀ Y : Subgroup X, CFSG.Assembly.IsElemAbelian 3 Y → 9 ≤ Nat.card Y →
      Subgroup.centralizer (Y : Set X) ⊓
          Subgroup.centralizer
            (inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) : Set X) ≤
        inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X))

namespace Res611Res4

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_thetaComponentFamily {A E L : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hEA : E ≤ A) {c : G} (hc1 : c ≠ 1)
    (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c)
    (hLE : L ∈ thetaComponentFamily 3 E) : c ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, heE, he1, hLe⟩ := mem_thetaComponentFamily_iff.mp hLE
  have heC : e ∈ Subgroup.zpowers c :=
    hCA ▸ ⟨hEA heE, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLe⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c (hCA ▸ Subgroup.mem_zpowers c).1) hc1
  have he3 : orderOf e = 3 := orderOf_eq_prime (hA.2 e (hEA heE)) he1
  have heq : Subgroup.zpowers e = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heC)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, he3])
  exact (Subgroup.zpowers_le.mpr heE) (heq ▸ Subgroup.mem_zpowers c)

omit [Finite G] in
theorem eq_sup_inf_of_eq_sup {A E L : Subgroup G} (hEA : E ≤ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {c : G} (hcE : c ∈ E)
    (hdec : A = Subgroup.zpowers c ⊔ (A ⊓ L)) : E = Subgroup.zpowers c ⊔ (E ⊓ L) := by
  have hcA : c ∈ A := hEA hcE
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    have hcN : c ∈ Subgroup.normalizer (A : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · exact A.mul_mem (A.mul_mem hcA hy) (A.inv_mem hcA)
      · have h1 := A.mul_mem (A.mul_mem (A.inv_mem hcA) hy) hcA
        simpa [mul_assoc] using h1
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcN, hAL hcA⟩
  apply le_antisymm
  · intro e he
    have heA : e ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hdec ▸ hEA he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at heA
    obtain ⟨x, hx, a, ha, rfl⟩ := heA
    have hxE : x ∈ E := (Subgroup.zpowers_le.mpr hcE) hx
    have haE : a ∈ E := by
      have h1 := E.mul_mem (E.inv_mem hxE) he
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem_sup hx ⟨haE, ha.2⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hcE) inf_le_left

theorem false_of_field {A E T L : Subgroup G} {c : G} (hEA : E ≤ A)
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hc1 : c ≠ 1)
    (hcA : c ∈ A) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (hTC : T ≤ Subgroup.centralizer (E : Set G))
    (hfin : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 P →
      81 ≤ Nat.card P → E ⊔ T ≤ invG L P → False)
    {m : ℕ} (hm : 2 < m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set ψ : L ⧸ θL ≃* CFSG.GorensteinWalter.PSL2 (GaloisField 3 (3 * m)) :=
    φ.trans (projSLEquivPSLn 2 (GaloisField 3 (3 * m))) with hψ
  set ρE : E →* MulAut (CFSG.GorensteinWalter.PSL2 (GaloisField 3 (3 * m))) :=
    (MulAut.congr ψ).toMonoidHom.comp ((thetaAct L).comp (Subgroup.inclusion hEL)) with hρE
  have hρEapp : ∀ e : E, ρE e = MulAut.congr ψ (thetaAct L ⟨e, hEL e.2⟩) := fun e => rfl
  have hker : Nat.card ρE.ker ≤ 3 := by
    have hmem : ∀ k : ρE.ker, ((k : E) : G) ∈ Subgroup.zpowers c := by
      intro k
      have hk : ρE (k : E) = 1 := k.2
      rw [hρEapp, map_eq_one_iff _ (MulAut.congr ψ).injective] at hk
      rw [← hCA]
      refine ⟨hEA (k : E).2, ⟨⟨(k : E), hEL (k : E).2⟩, hk, rfl⟩⟩
    have hinj : Function.Injective
        (fun k : ρE.ker => (⟨((k : E) : G), hmem k⟩ : Subgroup.zpowers c)) := by
      intro k k' h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1] at h1
  have h9 : 9 ≤ Nat.card ρE.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρE.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρE).toEquiv, hE27] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card ρE.range * Nat.card ρE.ker ≤ 8 * 3 := Nat.mul_le_mul (by omega) hker
    omega
  have hRe : CFSG.Assembly.IsElemAbelian 3 ρE.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      change ρE x * ρE y = ρE y * ρE x
      rw [← map_mul, ← map_mul, hEe.1.is_comm.comm x y]
    · obtain ⟨x, rfl⟩ := hy
      have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hEe.2 _ x.2)
      rw [← map_pow, hx3, map_one]
  obtain ⟨x, hx1, hxE, hCe, hCcard⟩ := exists_conj_mem_of_elemAbelian (e := 3 * m) (by omega)
    hRe h9
  obtain ⟨e0, he0⟩ := hxE
  have hconj : thetaAct L ⟨e0, hEL e0.2⟩ = MulAut.conj (ψ.symm x) := by
    apply (MulAut.congr ψ).injective
    rw [← hρEapp, he0]
    ext y
    simp [MulAut.congr_apply]
  set u := ψ.symm x with hu
  set P := Subgroup.centralizer ({u} : Set (L ⧸ θL)) with hP
  have hPmap : (Subgroup.centralizer ({x} : Set (CFSG.GorensteinWalter.PSL2
      (GaloisField 3 (3 * m))))).map ψ.symm.toMonoidHom = P :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_singleton_mulEquiv ψ.symm x
  have hPe : CFSG.Assembly.IsElemAbelian 3 P := by
    rw [← hPmap]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hCe
  have hP81 : 81 ≤ Nat.card P := by
    rw [← hPmap, Subgroup.card_map_of_injective ψ.symm.injective, hCcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinv : E ⊔ T ≤ invG L P := by
    have hC : E ⊔ T ≤ Subgroup.centralizer ({(e0 : G)} : Set G) := by
      apply sup_le
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨y, hy⟩ e0)
      · intro t ht
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hTC ht) _ e0.2).symm
    intro g hg
    have hgL := hETL hg
    have hge : g * (e0 : G) = e0 * g := Subgroup.mem_centralizer_singleton_iff.mp (hC hg)
    refine mem_invG_iff.mpr ⟨hgL, mem_stabAut_centralizer_of_commute ?_⟩
    rw [← hconj, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hge
  exact hfin P hPe hP81 hinv

theorem false_of_char3 {A E T L B : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hEA : E ≤ A) (hEe : CFSG.Assembly.IsElemAbelian 3 E)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (hTC : T ≤ Subgroup.centralizer (E : Set G)) (hTab : CFSG.Assembly.IsElemAbelian 2 T)
    (hfin : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 P →
      81 ≤ Nat.card P → E ⊔ T ≤ invG L P → False)
    (hfix : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsPGroup 3 P →
      E ⊔ T ≤ invG L P → T ≤ fixG L P)
    (hKX : ∀ Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 Y →
      9 ≤ Nat.card Y →
      Subgroup.centralizer (Y : Set (L ⧸ aschbacherSolvableCore 3 L)) ⊓
          Subgroup.centralizer (inSubgroup (CFSG.pCore 3)
            (Subgroup.centralizer (Y : Set (L ⧸ aschbacherSolvableCore 3 L))) :
              Set (L ⧸ aschbacherSolvableCore 3 L)) ≤
        inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set (L ⧸ aschbacherSolvableCore 3 L))))
    (hQ9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G)) (hBL : B ≤ L) (hBA : B ≤ A)
    (h81 : 81 ≤ Nat.card B) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set Q := E ⊓ L with hQdef
  have hQ3 : IsPGroup 3 Q := (Sec5.isPGroup_of_isElemAbelian hEe).to_le inf_le_left
  set Qb := (Q.subgroupOf L).map (QuotientGroup.mk' θL) with hQb
  have hQbe : CFSG.Assembly.IsElemAbelian 3 Qb := by
    refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ ?_
    refine Item434Kit.isElemAbelian_of_map_injective L.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact Sec5.isElemAbelian_of_le hEe inf_le_left
  have hQb9 : 9 ≤ Nat.card Qb := by
    rw [hQb, card_map_mk_of_isPGroup hQ3 inf_le_right]
    exact hQ9
  set Cb := Subgroup.centralizer (Qb : Set (L ⧸ θL)) with hCb
  set P0 := inSubgroup (CFSG.pCore 3) Cb with hP0
  have hKC : Cb ⊓ Subgroup.centralizer (P0 : Set (L ⧸ θL)) ≤ P0 := hKX Qb hQbe hQb9
  have hEN : E ⊔ T ≤ Subgroup.normalizer (E : Set G) :=
    sup_le Subgroup.le_normalizer (hTC.trans (Subgroup.centralizer_le_normalizer _))
  have hQN : E ⊔ T ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (Q : Set G) :=
    fun g hg => ⟨hETL hg, Subgroup.inf_normalizer_le_normalizer_inf ⟨hEN hg, hETL hg⟩⟩
  have hinvQ : E ⊔ T ≤ invG L Qb := hQN.trans (le_invG_map L Q)
  have hinvC : E ⊔ T ≤ invG L Cb := hinvQ.trans (invG_le_invG_centralizer L Qb)
  have hinvP : E ⊔ T ≤ invG L P0 := hinvC.trans (invG_le_invG_pCore L Cb)
  have hP03 : IsPGroup 3 P0 := CFSG.pCore_isPGroup.map _
  have hTP : T ≤ fixG L P0 := hfix P0 hP03 hinvP
  have hTCb : T ≤ fixG L Cb := by
    intro t ht
    have htL := hETL (Subgroup.mem_sup_right ht)
    obtain ⟨hg1, hstab⟩ := mem_invG_iff.mp (hinvC (Subgroup.mem_sup_right ht))
    obtain ⟨hg2, hfixP⟩ := mem_fixG_iff.mp (hTP ht)
    refine mem_fixG_iff.mpr ⟨htL, ?_⟩
    refine fix_of_fix_pCore (thetaAct L ⟨t, htL⟩) ?_ (fun x hx => (hstab x).mpr hx) hfixP hKC
    rw [← map_mul]
    have h1 : (⟨t, htL⟩ * ⟨t, htL⟩ : Subgroup.normalizer (L : Set G)) = 1 :=
      Subtype.ext (by simpa [pow_two] using hTab.2 t ht)
    rw [h1, map_one]
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hAe hBA
  have hB3 : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian hBe
  set Bb := (B.subgroupOf L).map (QuotientGroup.mk' θL) with hBb
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBbC : Bb ≤ Cb := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb hq
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc _ (hEA hq.1) _ (hBA hb))
  have hfixB : E ⊔ T ≤ fixG L Bb := by
    apply sup_le
    · intro e he
      refine le_fixG_map L B (Subgroup.mem_inf.mpr ⟨hEL he,
        Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩)
      exact hAc _ (hBA hb) _ (hEA he)
    · exact hTCb.trans (fixG_anti L hBbC)
  have hBbe : CFSG.Assembly.IsElemAbelian 3 Bb := by
    refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ ?_
    refine Item434Kit.isElemAbelian_of_map_injective L.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hBL]
    exact hBe
  have hBb81 : 81 ≤ Nat.card Bb := by
    rw [hBb, card_map_mk_of_isPGroup hB3 hBL]
    exact h81
  exact hfin Bb hBbe hBb81 (hfixB.trans (fixG_le_invG L Bb))

end Res611Res4

open Res611Res4

end CFSG.RankThree.PartTwo.Sec6
