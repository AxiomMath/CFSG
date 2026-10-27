module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Weak
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Struct
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Base
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.FaithfulOdd
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSigma

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open scoped commutatorElement

theorem nineJ_inf_gLAPPrimeCoreOf_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    nineJ K (B.b 2) ⊓ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) = ⊥ := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let J : Subgroup G := nineJ K (B.b 2)
  have hJK : J ≤ K := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hJH : J ≤ H := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hOnorm : H ≤ Subgroup.normalizer (O : Set G) := by
    simpa only [O, GLAPPrimeCoreOf] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (gLAPPrimeCoreOf_normal 3 H)
  have hcopO : Nat.Coprime 3 (Nat.card O) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' Nat.prime_three H
  have hJnorm : ((J ⊓ O).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (H := J ⊓ O) (K := J) inf_le_left]
    exact (le_inf Subgroup.le_normalizer (hJH.trans hOnorm)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hJsimple : IsSimpleGroup ↥J := nineJ_simple_of_recOutTwD5 hstd hB hrec
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥J _ hJsimple
    ((J ⊓ O).subgroupOf J) hJnorm with hbot | htop
  · have hEq : (J ⊓ O) ⊓ J = (⊥ : Subgroup G) ⊓ J :=
      Subgroup.subgroupOf_inj.mp (by rw [hbot, Subgroup.bot_subgroupOf])
    simpa using hEq
  · have hJO : J ≤ O := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
    have hdvd : 3 ∣ Nat.card O :=
      (three_dvd_card_nineJ hstd hB hrec).trans (Subgroup.card_dvd_of_le hJO)
    exact absurd hdvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopO)

theorem commute_of_mem_gLAPPrimeCoreOf_of_mem_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {o x : G}
    (hoO : o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (hoC : o ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer ({B.b 2} : Set G))
    (hxJ : x ∈ nineJ K (B.b 2)) :
    o * x = x * o := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let J : Subgroup G := nineJ K (B.b 2)
  have hJK : J ≤ K := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hJH : J ≤ H := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hOnorm : H ≤ Subgroup.normalizer (O : Set G) := by
    simpa only [O, GLAPPrimeCoreOf] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (gLAPPrimeCoreOf_normal 3 H)
  have hJinfO : J ⊓ O = ⊥ := by
    simpa only [H, O, J] using nineJ_inf_gLAPPrimeCoreOf_eq_bot hstd hB hrec
  obtain ⟨d, hdD, k, hkKC, hok⟩ :=
    exists_mul_eq_of_mem_centralizer_inf_centralizer hstd hB hrec hoC
  have hdK : d ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hdD).2
  have hxK : x ∈ K := hJK hxJ
  have hkc' : k ∈ K ⊓ Subgroup.centralizer ({B.b 2} : Set G) := hkKC
  have hxc' : x ∈ K ⊓ Subgroup.centralizer ({B.b 2} : Set G) := ⟨hxK, hJH hxJ⟩
  have hcJ : k * x * k⁻¹ * x⁻¹ ∈ J := by
    show k * x * k⁻¹ * x⁻¹ ∈
      ⁅K ⊓ Subgroup.centralizer ({B.b 2} : Set G),
        K ⊓ Subgroup.centralizer ({B.b 2} : Set G)⁆
    exact Subgroup.commutator_mem_commutator hkc' hxc'
  have hcK : k * x * k⁻¹ * x⁻¹ ∈ K := hJK hcJ
  have hdc : Commute d (k * x * k⁻¹ * x⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hdK _ hcK).symm
  have hdeq : d * (k * x * k⁻¹ * x⁻¹) * d⁻¹ = k * x * k⁻¹ * x⁻¹ := by
    rw [hdc.eq]; group
  have hdxinv : d⁻¹ * x⁻¹ = x⁻¹ * d⁻¹ := by
    simpa [mul_inv_rev] using congrArg Inv.inv (Subgroup.mem_centralizer_iff.mp hdK x hxK)
  have ho_eq : o * x * o⁻¹ * x⁻¹ = d * (k * x * k⁻¹ * x⁻¹) * d⁻¹ := by
    rw [hok, mul_inv_rev]
    calc d * k * x * (k⁻¹ * d⁻¹) * x⁻¹
        = d * (k * x * k⁻¹) * (d⁻¹ * x⁻¹) := by group
      _ = d * (k * x * k⁻¹) * (x⁻¹ * d⁻¹) := by rw [hdxinv]
      _ = d * (k * x * k⁻¹ * x⁻¹) * d⁻¹ := by group
  have hoxJ : o * x * o⁻¹ * x⁻¹ ∈ J := by
    rw [ho_eq, hdeq]
    exact hcJ
  have hxoO : x * o * x⁻¹ * o⁻¹ ∈ O := by
    have hconjO : x * o * x⁻¹ ∈ O := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff''.mp (Subgroup.inv_mem _ (hOnorm (hJH hxJ))) o).mp hoO
    exact O.mul_mem hconjO (O.inv_mem hoO)
  have hoxO : o * x * o⁻¹ * x⁻¹ ∈ O := by
    have h := O.inv_mem hxoO
    rwa [show (x * o * x⁻¹ * o⁻¹)⁻¹ = o * x * o⁻¹ * x⁻¹ by group] at h
  have hmem : o * x * o⁻¹ * x⁻¹ ∈ J ⊓ O := ⟨hoxJ, hoxO⟩
  rw [hJinfO] at hmem
  have hone : o * x * o⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  calc o * x = (o * x * o⁻¹ * x⁻¹) * (x * o) := by group
    _ = x * o := by rw [hone, one_mul]

theorem conj_eq_self_of_mem_nineJ_of_orderOf_eq_pow_three {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {y x : G}
    (hy : y ∈ Subgroup.centralizer ({B.b 2} : Set G))
    (hyJ : ∀ z ∈ nineJ K (B.b 2),
      y * z * y⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (hyN : y ∈ Subgroup.normalizer
      ((Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) : Subgroup G) : Set G))
    (hxJ : x ∈ nineJ K (B.b 2)) (hxord : ∃ n : ℕ, orderOf x = 3 ^ n) :
    y * x * y⁻¹ = x := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let O : Subgroup G := GLAPPrimeCoreOf 3 H
  let J : Subgroup G := nineJ K (B.b 2)
  let P : Subgroup G := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  have hJK : J ≤ K := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hJH : J ≤ H := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hcopO : Nat.Coprime 3 (Nat.card O) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' Nat.prime_three H
  obtain ⟨n, hn⟩ := hxord
  set z : G := y * x * y⁻¹ with hz
  set o : G := x⁻¹ * z with ho
  have hxpow : x ^ 3 ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one x
  have hxC : x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ H :=
    ⟨(hJK.trans hstd.2.1.2.1) hxJ, hJH hxJ⟩
  have hxCenP : x ∈ Subgroup.centralizer (P : Set G) := by
    have hxb0 : Commute x b₀ := Subgroup.mem_centralizer_singleton_iff.mp hxC.1
    have hxb2 : Commute x (B.b 2) := Subgroup.mem_centralizer_singleton_iff.mp hxC.2
    refine CFSG.AGLEmbedding.le_centralizer_sup_zpowers (A := Subgroup.zpowers x) ?_ ?_
      (Subgroup.mem_zpowers x)
    · intro v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact hxb0.zpow_left m
    · intro v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact hxb2.zpow_left m
  have hz0 : z ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hp : y⁻¹ * b₀ * y ∈ P :=
      (Subgroup.mem_normalizer_iff''.mp hyN b₀).mp
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀))
    have hxp : Commute (y⁻¹ * b₀ * y) x :=
      Subgroup.mem_centralizer_iff.mp hxCenP _ hp
    calc z * b₀ = y * (x * (y⁻¹ * b₀ * y)) * y⁻¹ := by rw [hz]; group
      _ = y * ((y⁻¹ * b₀ * y) * x) * y⁻¹ := by rw [hxp.eq.symm]
      _ = b₀ * z := by rw [hz]; group
  have hzC : z ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ H :=
    ⟨hz0, H.mul_mem (H.mul_mem hy (hJH hxJ)) (H.inv_mem hy)⟩
  have hoO : o ∈ O := by
    have hxN : x ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (gLAPPrimeCoreOf_normal 3 H) (hJH hxJ)
    have hcommO : y * x * y⁻¹ * x⁻¹ ∈ O := hyJ x hxJ
    have hconjO : x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x ∈ O :=
      (Subgroup.mem_normalizer_iff''.mp hxN _).mp hcommO
    rw [show o = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x by rw [ho, hz]; group]
    exact hconjO
  have hoC : o ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ H := by
    rw [ho]
    exact (Subgroup.centralizer ({b₀} : Set G) ⊓ H).mul_mem
      ((Subgroup.centralizer ({b₀} : Set G) ⊓ H).inv_mem hxC) hzC
  have hox : o * x = x * o :=
    commute_of_mem_gLAPPrimeCoreOf_of_mem_centralizer hstd hB hrec hoO hoC hxJ
  have hzpow : z ^ 3 ^ n = 1 := by
    have hord : orderOf z = orderOf x := by
      rw [hz, show y * x * y⁻¹ = (MulAut.conj y) x from rfl, MulEquiv.orderOf_eq]
    have hzord : orderOf z = 3 ^ n := hord.trans hn
    rw [← hzord]
    exact pow_orderOf_eq_one z
  have hozpow : o ^ 3 ^ n = 1 := by
    have hzo : z = x * o := by rw [ho]; group
    have hmul := (Commute.mul_pow (show Commute x o from hox.symm) (3 ^ n))
    rw [← hzo, hzpow, hxpow] at hmul
    simpa using hmul.symm
  have ho_dvd : orderOf o ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hozpow
  have hcop : Nat.Coprime (orderOf o) (Nat.card O) :=
    (hcopO.pow_left n).coprime_dvd_left ho_dvd
  have hone : orderOf o = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl (orderOf o))
      (Subgroup.orderOf_dvd_natCard O hoO)
  have ho1 : o = 1 := orderOf_eq_one_iff.mp hone
  have hz_eq : z = x := by rw [show z = x * o by rw [ho]; group, ho1, mul_one]
  exact hz_eq

theorem centralizes_nineJ_of_forall_orderOf_eq_pow_three {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {y : G}
    (hy : y ∈ Subgroup.centralizer ({B.b 2} : Set G))
    (hyJ : ∀ z ∈ nineJ K (B.b 2),
      y * z * y⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (hyN : y ∈ Subgroup.normalizer
      ((Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) : Subgroup G) : Set G)) :
    ∀ x ∈ nineJ K (B.b 2), y * x * y⁻¹ = x := by
  classical
  let J : Subgroup G := nineJ K (B.b 2)
  obtain ⟨x₀, hx₀⟩ := @exists_prime_orderOf_dvd_card' ↥J _ _
    3 ⟨Nat.prime_three⟩ (three_dvd_card_nineJ hstd hB hrec)
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx₀
    omega
  have hgen : Subgroup.closure {z : ↥J | ∃ a : ℕ, orderOf z = 3 ^ a} = ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.closure_primePower_eq_top
      (nineJ_simple_of_recOutTwD5 hstd hB hrec) 3 ⟨x₀, hx₀ne, ⟨1, by simpa using hx₀⟩⟩
  let C : Subgroup ↥J := (Subgroup.centralizer ({y} : Set G)).comap J.subtype
  have hC : Subgroup.closure {z : ↥J | ∃ a : ℕ, orderOf z = 3 ^ a} ≤ C := by
    refine (Subgroup.closure_le C).mpr ?_
    rintro z ⟨a, ha⟩
    have hzord : ∃ m : ℕ, orderOf (z : G) = 3 ^ m := ⟨a, by rwa [Subgroup.orderOf_coe]⟩
    have hfix := conj_eq_self_of_mem_nineJ_of_orderOf_eq_pow_three hstd hB hrec hy hyJ hyN
      z.2 hzord
    change (z : G) ∈ Subgroup.centralizer ({y} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyz : Commute y (z : G) := by
      rw [Commute]
      calc y * (z : G) = (y * (z : G) * y⁻¹) * y := by group
        _ = (z : G) * y := by rw [hfix]
    exact hyz.symm
  rw [hgen] at hC
  intro x hxJ
  have hx' : x ∈ Subgroup.centralizer ({y} : Set G) := by
    have := hC (Subgroup.mem_top (⟨x, hxJ⟩ : ↥J))
    simpa using (Subgroup.mem_comap.mp this)
  have hxy : Commute y x := (Subgroup.mem_centralizer_singleton_iff.mp hx').symm
  calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [hxy.eq]
    _ = x := by group

theorem exists_zmod_eq_of_conj_mem_sup {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {y : G}
    (hy1 : y * B.b 1 * y⁻¹ = B.b 1)
    (hyP : y * b₀ * y⁻¹ ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)) :
    ∃ c : ZMod 3, c ≠ 0 ∧ y * b₀ * y⁻¹ = b₀ ^ c.val := by
  classical
  have hb0ord : orderOf b₀ = 3 := hstd.2.1.1
  have hb2ord : orderOf (B.b 2) = 3 := B.ord 2
  set e : G := y * b₀ * y⁻¹ with he
  have hcomm02 : Commute b₀ (B.b 2) := by
    rw [← hB.2.1]
    exact B.comm 0 2
  obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute (fun a ha b hb => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hcomm02.zpow_left m).zpow_right n)).mp hyP
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  let v : Coords (5 + 1) := Pi.single 0 (i : ZMod 3) + Pi.single 2 (j : ZMod 3)
  have hvvec : B.vec v = e := by
    dsimp only [v]
    rw [Basis3.vec_add, Basis3.vec_single_eq_pow, Basis3.vec_single_eq_pow, hB.2.1,
      ← E7Frame.zpow_eq_pow_val hb0ord i, ← E7Frame.zpow_eq_pow_val hb2ord j]
    exact hab
  have hline : IsConjLine b₀ (B.line v) := by
    refine ⟨y, ?_⟩
    rw [Basis3.line, hvvec, he]
  have he1 : e ≠ 1 := by
    intro h
    have hord : orderOf e = 3 := by
      rw [he, show y * b₀ * y⁻¹ = (MulAut.conj y) b₀ from rfl, MulEquiv.orderOf_eq, hb0ord]
    rw [h, orderOf_one] at hord
    omega
  have hvne : v ≠ 0 := by
    intro h
    exact he1 (by rw [← hvvec, h, Basis3.vec_zero])
  have hv0 : v 0 = (i : ZMod 3) := by simp [v]
  have hv1 : v 1 = 0 := by simp [v]
  have hv2 : v 2 = (j : ZMod 3) := by simp [v]
  have hi : (i : ZMod 3) ≠ 0 := by
    intro hi0
    rcases (hrec.2.2.2 v hvne).mp hline with ⟨-, h0⟩ | ⟨h6, -⟩
    · exact h0 (by rw [hv0, hi0])
    · exact ((wt_eq_iff_forall_ne_zero v).mp h6 0) (by rw [hv0, hi0])
  have hne01 : (Pi.single (0 : Fin (5 + 1)) 1 +
      Pi.single (1 : Fin (5 + 1)) 1 : Coords (5 + 1)) ≠ 0 := by decide
  have hgood01 : twD5Good (Pi.single (0 : Fin (5 + 1)) 1 +
      Pi.single (1 : Fin (5 + 1)) 1 : Coords (5 + 1)) := by
    refine Or.inl ⟨?_, ?_⟩
    · decide
    · decide
  have hline01 : IsConjLine b₀ (B.line (Pi.single (0 : Fin (5 + 1)) 1 +
      Pi.single (1 : Fin (5 + 1)) 1 : Coords (5 + 1))) :=
    (hrec.2.2.2 _ hne01).mpr hgood01
  have hlinew : IsConjLine b₀ (B.line (v + Pi.single (1 : Fin (5 + 1)) 1)) := by
    have hmap := isConjLine_map_conj hline01 y
    have heq : (B.line (Pi.single (0 : Fin (5 + 1)) 1 +
        Pi.single (1 : Fin (5 + 1)) 1)).map (MulAut.conj y).toMonoidHom =
        B.line (v + Pi.single (1 : Fin (5 + 1)) 1) := by
      rw [Basis3.line, MonoidHom.map_zpowers, Basis3.line]
      congr 1
      simp only [Basis3.vec_add, Basis3.vec_single, hvvec, hB.2.1]
      change (MulAut.conj y) (b₀ * B.b 1) = e * B.b 1
      rw [MulAut.conj_apply]
      calc y * (b₀ * B.b 1) * y⁻¹ = (y * b₀ * y⁻¹) * (y * B.b 1 * y⁻¹) := by group
        _ = e * B.b 1 := by rw [hy1, he]
    rwa [heq] at hmap
  have hwne : v + Pi.single (1 : Fin (5 + 1)) 1 ≠ 0 := by
    intro h
    exact hi (by simpa [hv0] using congrFun h 0)
  have hj0 : (j : ZMod 3) = 0 := by
    by_contra hj
    have hsub : ({0, 1, 2} : Finset (Fin (5 + 1))) ⊆
        wtSupport (v + Pi.single (1 : Fin (5 + 1)) 1) := by
      intro k hk
      fin_cases k <;> simp_all [v]
    have hwt3 : 3 ≤ wt (v + Pi.single (1 : Fin (5 + 1)) 1) := by
      have := Finset.card_le_card hsub
      norm_num at this
      rw [wt_eq_card_wtSupport]
      exact this
    rcases (hrec.2.2.2 _ hwne).mp hlinew with ⟨hle, -⟩ | ⟨h6, -⟩
    · omega
    · exact ((wt_eq_iff_forall_ne_zero _).mp h6 3) (by simp [v])
  have hb2j : B.b 2 ^ j = 1 := by
    rw [E7Frame.zpow_eq_pow_val hb2ord j, hj0, ZMod.val_zero, pow_zero]
  have he_eq : e = b₀ ^ (i : ZMod 3).val := by
    rw [← hab, hb2j, mul_one, E7Frame.zpow_eq_pow_val hb0ord i]
  exact ⟨(i : ZMod 3), hi, he_eq⟩

theorem conj_b₀_eq_self_of_exists_zmod {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀) (hrec : RecOutTwD5 B b₀) {y : G}
    {c : ZMod 3} (hcne : c ≠ 0) (he : y * b₀ * y⁻¹ = b₀ ^ c.val)
    (hfix : ∀ j : Fin (5 + 1), j ≠ 0 → y * B.b j * y⁻¹ = B.b j) :
    y * b₀ * y⁻¹ = b₀ := by
  classical
  have hc : c = 0 ∨ c = 1 ∨ c = -1 :=
    (show ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 by decide) c
  rcases hc with h0 | h1 | hneg
  · exact absurd h0 hcne
  · rw [he, h1, ZMod.val_one, pow_one]
  · exfalso
    let s : Fin (5 + 1) → ZMod 3 := fun i => if i = 0 then (-1 : ZMod 3) else 1
    have hs0 : s 0 = -1 := by simp [s]
    have hsj : ∀ j, j ≠ 0 → s j = 1 := by intro j hj; simp [s, hj]
    have hActs : B.Acts y (spMat (1 : Equiv.Perm (Fin (5 + 1))) s) := by
      rw [B.acts_spMat_iff]
      intro j
      by_cases hj : j = 0
      · subst hj
        simpa [hs0, hb0, hneg] using he
      · have hval : (1 : ZMod 3).val = 1 := rfl
        simpa [hsj j hj, hval, Equiv.Perm.one_apply] using hfix j hj
    let f : Coords (5 + 1) := fun _ => 1
    have hlinef : IsConjLine b₀ (B.line f) :=
      (hrec.2.2.2 f (by decide)).mpr (Or.inr ⟨by decide, by decide⟩)
    have hconj := isConjLine_map_conj hlinef y
    have hmap : (B.line f).map (MulAut.conj y).toMonoidHom = B.line s := by
      rw [Basis3.line, MonoidHom.map_zpowers]
      change Subgroup.zpowers (y * B.vec f * y⁻¹) = B.line s
      rw [B.acts_vec hActs, spMat_mulVec, Basis3.line]
      apply congrArg Subgroup.zpowers
      apply congrArg B.vec
      funext i
      simp [f, s, Equiv.Perm.one_symm]
    have hconj_s : IsConjLine b₀ (B.line s) := by rwa [hmap] at hconj
    have hsne : s ≠ 0 := by
      intro h
      have := congrFun h 0
      rw [hs0] at this
      exact (by decide : (-1 : ZMod 3) ≠ 0) this
    have hwts : wt s = 6 := by decide
    have hprods : ∏ i, s i = -1 := by decide
    have hnot : ¬ twD5Good s := by
      rw [twD5Good]
      rintro (⟨hle, -⟩ | ⟨-, hprod1⟩)
      · omega
      · rw [hprods] at hprod1
        exact absurd hprod1 (by decide)
    exact hnot ((hrec.2.2.2 s hsne).mp hconj_s)

theorem exists_eq_mul_zpow_of_mem_centralizer_inf {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {y : G}
    (hy : y ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer ({B.b 2} : Set G))
    (hyJ : ∀ x ∈ nineJ K (B.b 2), y * x * y⁻¹ = x) :
    ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
      ∃ k : ℤ, y = d * B.b 2 ^ k := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let J : Subgroup G := nineJ K (B.b 2)
  have hJK : J ≤ K := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hJH : J ≤ H := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  obtain ⟨d, hdD, k, hkKC, hy_eq⟩ :=
    exists_mul_eq_of_mem_centralizer_inf_centralizer hstd hB hrec hy
  have hdK : d ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hdD).2
  have hkC : ∀ x ∈ J, Commute k x := by
    intro x hxJ
    have hdx : Commute d x :=
      (Subgroup.mem_centralizer_iff.mp hdK x (hJK hxJ)).symm
    have hyx : Commute y x := by
      have h := hyJ x hxJ
      rw [Commute]
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [h]
    have hk_eq : k = d⁻¹ * y := by rw [hy_eq]; group
    rw [hk_eq]
    exact hdx.inv_left.mul_left hyx
  have hKCs : K ⊓ H = Subgroup.zpowers (B.b 2) ⊔ J := by
    simpa only [H, J] using inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec
  have hcomm : ∀ a ∈ Subgroup.zpowers (B.b 2), ∀ b ∈ J, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbH : b ∈ H := hJH hb
    have hcomm_b : Commute b (B.b 2) :=
      Subgroup.mem_centralizer_singleton_iff.mp hbH
    exact hcomm_b.symm.zpow_left m
  obtain ⟨a, ha, j, hjJ, hakj⟩ :=
    (CFSG.mem_sup_of_commute hcomm).mp (by rw [← hKCs]; exact hkKC)
  have haC : ∀ x ∈ J, Commute a x := by
    intro x hxJ
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hxH : x ∈ H := hJH hxJ
    have hcomm_x : Commute x (B.b 2) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxH
    exact hcomm_x.symm.zpow_left m
  have hjC : ∀ x ∈ J, Commute j x := by
    intro x hxJ
    have hj_eq : j = a⁻¹ * k := by rw [← hakj]; group
    rw [hj_eq]
    exact (haC x hxJ).inv_left.mul_left (hkC x hxJ)
  have hjZ : (⟨j, hjJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (hjC (w : G) w.2).symm
  have hj1 : j = 1 := by
    have h := hjZ
    rw [center_nineJ_eq_bot hstd hB hrec] at h
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp h)
  have hk_eqz : k = a := by
    calc k = a * j := hakj.symm
      _ = a * 1 := by rw [hj1]
      _ = a := mul_one a
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨d, hdD, m, ?_⟩
  rw [hy_eq, hk_eqz, ← hm]

end CFSG.StandardType.FrameRoute.FS81

end
