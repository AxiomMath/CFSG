module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.Quasithin.Background.F918C0
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace L1295B

section Star

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem nonempty_mulEquiv_autIH (h : HypF918 T V L V₁ Vp H K) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autIH V₁ Vp H K)) := by
  have hF := factElem h (le_conjClosure Vp H)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hker : CFSG.pCore 2 ↥K ≤ (toAutI h Vp).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    apply h.actH_eq_one_of_mem_pCoreOf (le_conjClosure Vp H)
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hx1
  have hkerle : (toAutI h Vp).ker ≤ CFSG.pCore 2 ↥K := by
    set N : Subgroup ↥K := (pCoreOf 2 H).subgroupOf K with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      have hkH : (k : G) ∈ H := hKH k.2
      have := (Subgroup.mem_normalizer_iff.1
        (LieType.BorelTits.le_normalizer_pCoreOf 2 H hkH) n).1 hn
      simpa using this
    have hNp : IsPGroup 2 N := by
      intro x
      have hx : ((x : ↥K) : G) ∈ pCoreOf 2 H := x.2
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hx⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx
    have hxQ : (x : G) ∈ pCoreOf 2 H := mem_pCoreOf_of_actH_eq_one h hx
    have hxN : x ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact hxQ
    exact LieType.BorelTits.le_pCore 2 hNn hNp hxN
  let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autIH V₁ Vp H K) :=
    QuotientGroup.lift _ (toAutI h Vp) hker
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := toAutI_surjective h Vp y
    exact ⟨QuotientGroup.mk x, hx⟩
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : toAutI h Vp x = 1 := hq
    exact (QuotientGroup.eq_one_iff x).2 (hkerle hx)
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end Star

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {n : ℕ} {V₁ K₁ : Subgroup G}

omit [Finite G] in
theorem mem_cComp_sup (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hTK : T ≤ Subgroup.normalizer (K₁ : Set G)) : K₁ ∈ cComp (K₁ ⊔ T) := by
  refine ⟨hK.1, hK.2.1, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK)), ?_⟩
  intro J hJK hJ1 hJp hJX
  exact hK.2.2.2 J hJK hJ1 hJp
    (A3.subnormal_trans (A3.subnormal_of_le_of_le hJX hJK.le le_sup_left) hK.2.2.1)

theorem T_le_normalizer (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    T ≤ Subgroup.normalizer (K₁ : Set G) := by
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  exact hV₁.2.2.trans (normalizer_le_of_lOne_le h1222 h37 h38 hcx.hyp hn hV₁ hLK hK)

omit [Finite G] in
theorem conjClosure_eq (hTK : T ≤ Subgroup.normalizer (K₁ : Set G)) : conjClosure K₁ T = K₁ :=
  le_antisymm (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.1 (hTK ht) k).1 hk)
    (le_conjClosure K₁ T)

theorem hypF918 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hq : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    HypF918 T V L V₁ V (K₁ ⊔ T) K₁ := by
  have hTK := T_le_normalizer h1222 h37 h38 hcx hV₁ hLK hK
  have hq' : CFSG.IsQuasisimple (↥K₁ ⧸ (pCoreOf 2 K₁).subgroupOf K₁) := by
    have e : (pCoreOf 2 K₁).subgroupOf K₁ = CFSG.pCore 2 ↥K₁ := by
      rw [pCoreOf, map_subtype_subgroupOf']
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq e.symm) hq
  refine
    { toHypF98 := L1286.hypF98_of_abelian h1222 h37 h38 h39 hcx.hyp hV₁ hU hHz
      K_cComp := mem_cComp_sup hK hTK
      K_quasisimple := hq'
      H_eq := ?_
      K₀_normal := ?_ }
  · rw [conjClosure_eq hTK]
    exact le_antisymm (sup_le le_sup_left ((le_inf le_sup_right le_sup_right).trans le_sup_right))
      (sup_le le_sup_left inf_le_right)
  · rw [conjClosure_eq hTK]
    exact sup_le Subgroup.le_normalizer hTK

theorem sqtkGroup (hcx : Cx1291 G T L V n) (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) :
    SQTKGroup ↥(K₁ ⊔ T) := by
  have hyp := hcx.hyp.hyp
  obtain ⟨hk, hq⟩ := isSQTKSub_of_inH hyp.qtke hyp.simple hyp.nonabelian
    (T := T) ⟨le_sup_right, hHz.1.2⟩
  exact ⟨hq, hk⟩

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup Q) : (∃ a b : Q, a * b ≠ b * a) ∧ Subgroup.center Q = ⊥ := by
  have := hs
  have hnt : Nontrivial Q := hs.toNontrivial
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.2 fun y _ => hcon y x
    have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [_root_.commutator_def] at this
    rw [h1] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (Subgroup.mem_bot.1 (hc ▸ Subgroup.mem_top x))
  refine ⟨hnc, ?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup Q) : CFSG.IsQuasisimple Q := by
  obtain ⟨hnc, hZ⟩ := center_eq_bot_of_simple hperf hs
  let e : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩

theorem fourList_of_simple (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hcx : Cx1291 G T L V n)
    (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁)) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hS : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    FourList (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
  have hperf : Group.IsPerfect (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    have hK' : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr hK.2.1
    exact Group.IsPerfect.ofSurjective (G := ↥K₁) (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hF := hypF918 h1222 h37 h38 h39 hcx hV₁ hU hLK hK hHz (isQuasisimple_of_simple hperf hS)
  have hTK := T_le_normalizer h1222 h37 h38 hcx hV₁ hLK hK
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4' hF (sqtkGroup hcx hHz) (conjClosure_eq hTK) hV₁I hIU W hW hirrU hD310
    hD391 hI4).1
  obtain ⟨e⟩ := nonempty_mulEquiv_autIH hF
  have hSA : IsSimpleGroup ↥(autIH V₁ V (K₁ ⊔ T) K₁) := MulEquiv.isSimpleGroup e.symm
  have hperfA : Group.IsPerfect ↥(autIH V₁ V (K₁ ⊔ T) K₁) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : Subgroup.center ↥(autIH V₁ V (K₁ ⊔ T) K₁) = ⊥ :=
    (center_eq_bot_of_simple hperfA hSA).2
  exact fourList_congr ((e.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))).symm) h4

theorem false_of_hatA7 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hA7 : IsHatA7 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : False := by
  have hF := hypF918 h1222 h37 h38 h39 hcx hV₁ hU hLK hK hHz hA7.1
  have hTK := T_le_normalizer h1222 h37 h38 hcx hV₁ hLK hK
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4_fine' hF (sqtkGroup hcx hHz) (conjClosure_eq hTK) hV₁I hIU W hW hirrU hD310
    hD391 hI4 hFine).1
  obtain ⟨e⟩ := nonempty_mulEquiv_autIH hF
  have hhat : IsHat ↥(autIH V₁ V (K₁ ⊔ T) K₁) ↥(alternatingGroup (Fin 7)) :=
    IsHat.of_mulEquiv e hA7
  exact h4.2.1 hhat.2.2 hhat

end L1295B

end CFSG.Quasithin.H13
