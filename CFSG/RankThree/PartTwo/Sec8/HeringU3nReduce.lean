module

public import CFSG.RankThree.PartTwo.Sec6.Item641
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.PiecesContradiction

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def qOf (s : G) : Subgroup G :=
  inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({s} : Set G))

@[expose] def rOf (e s : G) : Subgroup G :=
  inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({e, s} : Set G))

@[expose] def omegaZ (P : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ (∀ y ∈ P, x * y = y * x) ∧ x ^ 2 = 1}
  mul_mem' := by
    rintro x y ⟨hxP, hxc, hx2⟩ ⟨hyP, hyc, hy2⟩
    refine ⟨P.mul_mem hxP hyP, fun z hz => ?_, ?_⟩
    · calc x * y * z = x * (y * z) := mul_assoc _ _ _
        _ = x * (z * y) := by rw [hyc z hz]
        _ = (x * z) * y := (mul_assoc _ _ _).symm
        _ = (z * x) * y := by rw [hxc z hz]
        _ = z * (x * y) := mul_assoc _ _ _
    · have hxy : Commute x y := hxc y hyP
      rw [hxy.mul_pow, hx2, hy2, one_mul]
  one_mem' := ⟨P.one_mem, fun y _ => by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨hxP, hxc, hx2⟩
    refine ⟨P.inv_mem hxP, fun y hy => ?_, by rw [inv_pow, hx2, inv_one]⟩
    have : Commute x y := hxc y hy
    exact this.inv_left.eq

theorem omegaZ_le (P : Subgroup G) : omegaZ P ≤ P := fun _ hx => hx.1

theorem isElemAbelian_omegaZ (P : Subgroup G) : CFSG.Assembly.IsElemAbelian 2 (omegaZ P) :=
  ⟨⟨⟨fun a b => Subtype.ext (a.2.2.1 b b.2.1)⟩⟩, fun x hx => hx.2.2⟩

theorem normalizer_le_normalizer_omegaZ (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (omegaZ P : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ x ∈ omegaZ P, g * x * g⁻¹ ∈ omegaZ P := by
    intro g hg x ⟨hxP, hxc, hx2⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxP, fun y hy => ?_, ?_⟩
    · have hy' : g⁻¹ * y * g ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
        simpa using this
      have := hxc _ hy'
      calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [this]
        _ = y * (g * x * g⁻¹) := by group
    · calc (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by simp only [sq]; group
        _ = 1 := by rw [hx2]; group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [e] at this

theorem qOf_le (s : G) : qOf s ≤ Subgroup.centralizer ({s} : Set G) :=
  Subgroup.map_subtype_le _

theorem isPGroup_qOf (s : G) : IsPGroup 2 (qOf s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.pCore_isPGroup.map _

theorem centralizer_le_normalizer_qOf (s : G) :
    Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (qOf s : Set G) :=
  Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 (Subgroup.centralizer ({s} : Set G))))

theorem inf_centralizer_le_rOf (e s : G) :
    qOf s ⊓ Subgroup.centralizer ({e} : Set G) ≤ rOf e s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : qOf s ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ({e, s} : Set G) := by
    rintro x ⟨hxq, hxe⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mp hxe y rfl
    · exact Subgroup.mem_centralizer_iff.mp (qOf_le y hxq) y rfl
  have hnorm : Subgroup.centralizer ({e, s} : Set G) ≤
      Subgroup.normalizer ((qOf s ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
    intro h hh
    have hhs : h ∈ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp hh y (by simp)
    have hhe : h ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp hh y (by simp)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨centralizer_le_normalizer_qOf s hhs, Subgroup.le_normalizer hhe⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm
    ((isPGroup_qOf s).to_le inf_le_left)

@[expose] def deltaPrime (B : Subgroup G) (c s : G) : Set G :=
  {e | e = c ∨ (e ∈ B ∧ e ≠ 1 ∧
    ⁅qOf s ⊓ Subgroup.centralizer ({e} : Set G), Subgroup.zpowers c⁆ ≠ ⊥)}

theorem exists_ne_one_mem_omegaZ {P : Subgroup G} (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    ∃ x ∈ omegaZ P, x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  haveI : Nontrivial (Subgroup.center P) := hP2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center P) := hP2.to_subgroup _
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (Subgroup.center P) = 1 := by rw [hk]; rfl
    have h2 : 1 < Nat.card (Subgroup.center P) := Finite.one_lt_card
    omega
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rw [hk]; exact dvd_pow_self 2 hk1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((z : P) : G), ⟨(z : P).2, fun y hy => ?_, ?_⟩, ?_⟩
  · have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 := congrArg (fun w : Subgroup.center P => ((w : P) : G)) this
    simpa using h2
  · intro h1
    have : (z : P) = 1 := Subtype.ext h1
    have : z = 1 := Subtype.ext this
    rw [this, orderOf_one] at hz
    omega

theorem isTwoLocal_centralizer_of_sq {t : G} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    CFSG.Assembly.IsTwoLocal (Subgroup.centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  refine ⟨Subgroup.zpowers t, ?_,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one]), ?_⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · refine le_antisymm ?_ ?_
    · rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    · intro g hg
      have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
        (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases (Source.mem_zpowers_of_sq_eq_one ht2).mp h1 with h | h
      · exfalso
        apply ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      · calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [h]

theorem coprime_three_card_of_isPGroup_two {V : Subgroup G} (hV : IsPGroup 2 V) :
    Nat.Coprime 3 (Nat.card V) := by
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem inCatalog_of_twoLocalData
    (h310 : Sec6.Item3_10) (hG : TheoremFourHyp G) {B S : Subgroup G} {c s : G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : 9 ≤ Nat.card B)
    (hS : CFSG.Assembly.IsElemAbelian 2 S) (hsS : s ∈ S) (hs1 : s ≠ 1)
    (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hBs : B ≤ Subgroup.centralizer ({s} : Set G))
    (hTrans : ∀ x ∈ S, x ≠ 1 → ∀ y ∈ S, y ≠ 1 →
      ∃ k ∈ Subgroup.normalizer (S : Set G), k * x * k⁻¹ = y)
    (h863 : ∀ e ∈ deltaPrime B c s, rOf e s ≤ Subgroup.centralizer (S : Set G))
    (h864 : ∀ e ∈ deltaPrime B c s, ∀ x ∈ rOf e s, x ^ 2 = 1 → x ∈ S) :
    CFSG.Assembly.InCatalog G := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9' : 3 ^ 2 ≤ Nat.card B := by simpa using hB9
  have hS2 : ∀ x ∈ S, x ^ 2 = 1 := hS.2
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSp : IsPGroup 2 S := Sec5.isPGroup_of_isElemAbelian hS
  have hS1 : S ≠ ⊥ := fun h => hs1 (by simpa [h] using hsS)
  have hs2 : s ^ 2 = 1 := hS2 s hsS
  have hQ2 : IsPGroup 2 (qOf s) := isPGroup_qOf s
  have hBQ : B ≤ Subgroup.normalizer (qOf s : Set G) :=
    hBs.trans (centralizer_le_normalizer_qOf s)
  have hcopQ : Nat.Coprime 3 (Nat.card (qOf s)) := coprime_three_card_of_isPGroup_two hQ2
  have key : ∀ v ∈ B, v ≠ 1 → ∃ e ∈ deltaPrime B c s,
      qOf s ⊓ Subgroup.centralizer ({v} : Set G) ≤ rOf e s := by
    intro v hvB hv1
    by_cases hcomm : ⁅qOf s ⊓ Subgroup.centralizer ({v} : Set G), Subgroup.zpowers c⁆ = ⊥
    · refine ⟨c, Or.inl rfl, fun x hx => ?_⟩
      have hxc : x ∈ Subgroup.centralizer (Subgroup.zpowers c : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
      have hxc' : x ∈ Subgroup.centralizer ({c} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact Subgroup.mem_centralizer_iff.mp hxc y (Subgroup.mem_zpowers y)
      exact inf_centralizer_le_rOf c s ⟨hx.1, hxc'⟩
    · exact ⟨v, Or.inr ⟨hvB, hv1, hcomm⟩, inf_centralizer_le_rOf v s⟩
  have hQS : qOf s ≤ Subgroup.centralizer (S : Set G) := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB hB9' hBQ hcopQ ?_
    intro v hv hv1
    obtain ⟨e, he, hle⟩ := key v hv hv1
    exact hle.trans (h863 e he)
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.centralizer ({s} : Set G)) :=
    isTwoLocal_centralizer_of_sq hs1 hs2
  have hSQ : S ≤ qOf s := by
    intro x hx
    have h1 : x ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hScomm x hx s hsS
    have h2' : x ∈ Subgroup.centralizer (qOf s : Set G) :=
      Subgroup.le_centralizer_iff.mpr hQS hx
    exact hG.charTwoType _ hloc ⟨h1, h2'⟩
  have hV : ∀ V : Subgroup G, V ≤ qOf s → CFSG.Assembly.IsElemAbelian 2 V →
      B ≤ Subgroup.normalizer (V : Set G) → V ≤ S := by
    intro V hVQ hVe hBV
    have hcop : Nat.Coprime 3 (Nat.card V) :=
      coprime_three_card_of_isPGroup_two (Sec5.isPGroup_of_isElemAbelian hVe)
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB hB9' hBV hcop ?_
    intro v hv hv1 x hx
    obtain ⟨e, he, hle⟩ := key v hv hv1
    exact h864 e he x (hle ⟨hVQ hx.1, hx.2⟩) (hVe.2 x hx.1)
  have hSΩ : S = omegaZ (qOf s) := by
    have h1 : S ≤ omegaZ (qOf s) := fun x hx =>
      ⟨hSQ hx, fun y hy => Subgroup.mem_centralizer_iff.mp (hQS hy) x hx, hS2 x hx⟩
    have h2 : omegaZ (qOf s) ≤ S := hV _ (omegaZ_le _) (isElemAbelian_omegaZ _)
      (hBQ.trans (normalizer_le_normalizer_omegaZ _))
    exact le_antisymm h1 h2
  have hCN : Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    rw [hSΩ]
    exact normalizer_le_normalizer_omegaZ _ (centralizer_le_normalizer_qOf s hg)
  have hNloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (S : Set G)) := ⟨S, hS1, hSp, rfl⟩
  obtain ⟨M, hM, hNM⟩ := exists_mem_scriptM_of_isTwoLocal
    (X := (Subgroup.normalizer (S : Set G) : Set G)) hNloc fun x hx => hx
  have hMloc : CFSG.Assembly.IsTwoLocal M := hM.1.1
  set P := CFSG.Assembly.pCoreOf 2 M with hPdef
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hP1 : P ≠ ⊥ := by
    obtain ⟨U, hU1, hU2, hUM⟩ := hMloc
    intro hP
    apply hU1
    have : U ≤ P := by
      rw [hPdef, hUM]
      exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 U hU2
    exact eq_bot_iff.mpr (hP ▸ this)
  have hSM : S ≤ M := Subgroup.le_normalizer.trans hNM
  have hBM : B ≤ M := hBS.trans hNM
  have hQM : qOf s ≤ M := (hQS.trans (Subgroup.centralizer_le_normalizer _)).trans hNM
  have hMZ : M ≤ Subgroup.normalizer (omegaZ P : Set G) :=
    hMP.trans (normalizer_le_normalizer_omegaZ P)
  obtain ⟨w, hwZ, hwC, hw1⟩ : ∃ w ∈ omegaZ P, w ∈ Subgroup.centralizer (qOf s : Set G) ∧ w ≠ 1 := by
    have hmod := Sec6.card_inf_centralizer_modEq (p := 2) hQ2 (hQM.trans hMZ)
    obtain ⟨x, hxZ, hx1⟩ := exists_ne_one_mem_omegaZ hP2 hP1
    have hZ2 : IsPGroup 2 (omegaZ P) := hP2.to_le (omegaZ_le P)
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl
      have h1 : Nat.card (omegaZ P) = 1 := by rw [hk]; rfl
      have hnt : Nontrivial (omegaZ P) := ⟨⟨⟨x, hxZ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
      have h2 : 1 < Nat.card (omegaZ P) := Finite.one_lt_card
      omega
    by_contra hno
    push Not at hno
    have hbot : omegaZ P ⊓ Subgroup.centralizer (qOf s : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      exact hy1 (hno y hy.1 hy.2)
    rw [hbot, Subgroup.card_bot, hk] at hmod
    have h0 : 2 ^ k ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr (dvd_pow_self 2 hk1)
    have : 1 ≡ 0 [MOD 2] := hmod.trans h0
    exact absurd this (by decide)
  have hws : w ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hwC s (hSQ hsS)).symm
  have hwQ : w ∈ qOf s := hG.charTwoType _ hloc ⟨hws, hwC⟩
  have hwS : w ∈ S := by
    rw [hSΩ]
    exact ⟨hwQ, fun y hy => (Subgroup.mem_centralizer_iff.mp hwC y hy).symm, hwZ.2.2⟩
  have hSZ : S ≤ omegaZ P := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact (omegaZ P).one_mem
    · obtain ⟨k, hk, hkt⟩ := hTrans w hwS hw1 t ht ht1
      rw [← hkt]
      exact (Subgroup.mem_normalizer_iff.mp (hMZ (hNM hk)) w).mp hwZ
  have hPQ : P ≤ qOf s := by
    have hPC : P ≤ Subgroup.centralizer ({s} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((hSZ hsS).2.1 y hy).symm
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC
      (fun g hg => hMP (hNM (hCN hg))) hP2
  have hZS : omegaZ P = S :=
    le_antisymm (hV _ ((omegaZ_le P).trans hPQ) (isElemAbelian_omegaZ P) (hBM.trans hMZ)) hSZ
  have hMS : M ≤ Subgroup.normalizer (S : Set G) := by rw [← hZS]; exact hMZ
  have hmax : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 W) S := by
    refine ⟨⟨hSM, hMS, hS⟩, ?_⟩
    rintro W ⟨hWM, hMW, hWe⟩ -
    have hWP : W ≤ P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWM hMW
        (Sec5.isPGroup_of_isElemAbelian hWe)
    exact hV W (hWP.trans hPQ) hWe (hBM.trans hMW)
  have hTI : ∀ g : G, S ⊓ S.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      S ⊓ S.map (MulAut.conj g).toMonoidHom = S := by
    intro g
    by_cases h : S ⊓ S.map (MulAut.conj g).toMonoidHom = ⊥
    · exact Or.inl h
    · right
      obtain ⟨⟨t, ht⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
      have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
      obtain ⟨u, huS, hut⟩ := Subgroup.mem_map.mp ht.2
      have hu1 : u ≠ 1 := by
        rintro rfl
        apply ht1
        simpa using hut.symm
      have hutg : g * u * g⁻¹ = t := by simpa using hut
      obtain ⟨n1, hn1, hn1t⟩ := hTrans s hsS hs1 t ht.1 ht1
      obtain ⟨n2, hn2, hn2u⟩ := hTrans s hsS hs1 u huS hu1
      have hx : n1⁻¹ * g * n2 ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : n1⁻¹ * g * n2 * s * (n1⁻¹ * g * n2)⁻¹ = s := by
          calc n1⁻¹ * g * n2 * s * (n1⁻¹ * g * n2)⁻¹
              = n1⁻¹ * g * (n2 * s * n2⁻¹) * g⁻¹ * n1 := by group
            _ = n1⁻¹ * (g * u * g⁻¹) * n1 := by rw [hn2u]; group
            _ = n1⁻¹ * (n1 * s * n1⁻¹) * n1 := by rw [hutg, hn1t]
            _ = s := by group
        calc n1⁻¹ * g * n2 * s = (n1⁻¹ * g * n2 * s * (n1⁻¹ * g * n2)⁻¹) * (n1⁻¹ * g * n2) := by
              group
          _ = s * (n1⁻¹ * g * n2) := by rw [this]
      have hxN := hCN hx
      have hgN : g ∈ Subgroup.normalizer (S : Set G) := by
        have : g = n1 * (n1⁻¹ * g * n2) * n2⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn1 hxN) (Subgroup.inv_mem _ hn2)
      have hmap : S.map (MulAut.conj g).toMonoidHom = S :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      rw [hmap, inf_idem]
  exact h310 G hG.isSimpleGroup hG.nonabelian hG.kProper hG.charTwoType M hM.1 S hmax hTI

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
