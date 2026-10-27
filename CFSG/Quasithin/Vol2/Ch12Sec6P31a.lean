module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126f
public import CFSG.Quasithin.Vol2.Ch12Sec6L33a
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Star

variable {H : Subgroup G}

theorem pCore_hStar : CFSG.pCore 2 (HStar H) = ⊥ := by
  set N : Subgroup ↥H := CFSG.pCore 2 ↥H with hN
  set K : Subgroup ↥H := (CFSG.pCore 2 (↥H ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := ↥H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := ↥H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hKN hx

theorem eq_bot_of_isPGroup {N : Subgroup (HStar H)} (hn : N.Normal) (hN : IsPGroup 2 N) :
    N = ⊥ := by
  have h : N ≤ CFSG.pCore 2 (HStar H) := le_sSup ⟨hn, hN⟩
  rw [pCore_hStar] at h
  exact le_bot_iff.1 h

theorem mk_mem_star {X : Subgroup G} {h : ↥H} (hx : (h : G) ∈ X) :
    (QuotientGroup.mk h : HStar H) ∈ star H X :=
  ⟨h, hx, rfl⟩

theorem star_mono {X Y : Subgroup G} (h : X ≤ Y) : star H X ≤ star H Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem star_self : star H H = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact mk_mem_star h.2

theorem star_sup {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    star H (X ⊔ Y) = star H X ⊔ star H Y := by
  unfold S126.star
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem normal_star {X : Subgroup G} (hX : H ≤ Subgroup.normalizer (X : Set G)) :
    (star H X).Normal := by
  have : (X.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hX g.2) n).1 hn⟩
  exact this.map _ (QuotientGroup.mk'_surjective _)

@[expose] def pre (H : Subgroup G) (X : Subgroup (HStar H)) : Subgroup G :=
  (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

theorem mem_pre {X : Subgroup (HStar H)} {g : G} :
    g ∈ pre H X ↔ ∃ hg : g ∈ H, (QuotientGroup.mk ⟨g, hg⟩ : HStar H) ∈ X := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hX⟩
    exact ⟨⟨g, hg⟩, hX, rfl⟩

theorem pre_le (X : Subgroup (HStar H)) : pre H X ≤ H :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_pre (X : Subgroup (HStar H)) : pCoreOf 2 H ≤ pre H X := by
  intro g hg
  have hgH : g ∈ H := pCoreOf_le 2 H hg
  refine mem_pre.2 ⟨hgH, ?_⟩
  rw [F126.mkH_eq_one_iff.2 hg]
  exact X.one_mem

theorem star_pre (X : Subgroup (HStar H)) : star H (pre H X) = X := by
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  constructor
  · rintro ⟨h', hh', he⟩
    obtain ⟨hgH, hX⟩ := mem_pre.1 (Subgroup.mem_subgroupOf.1 hh')
    rw [← he]
    exact hX
  · intro hx
    exact mk_mem_star (mem_pre.2 ⟨h.2, hx⟩)

variable [Finite G]

theorem isSolvable_pre {X : Subgroup (HStar H)} (hX : Group.IsSolvable X) :
    Group.IsSolvable (pre H X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup ↥H := X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hY
  have hPY : CFSG.pCore 2 ↥H ≤ Y := by
    intro q hq
    show QuotientGroup.mk' _ q ∈ X
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff q).2 hq]
    exact X.one_mem
  let g : ↥Y →* ↥X := ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp Y.subtype).codRestrict X
    fun y => y.2
  let f : ↥(CFSG.pCore 2 ↥H) →* ↥Y := Subgroup.inclusion hPY
  have hfg : g.ker ≤ f.range := by
    intro y hy
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (y : ↥H) = 1 := congrArg Subtype.val hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
    exact ⟨⟨y, hy'⟩, rfl⟩
  have hP : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  have hYs : Group.IsSolvable ↥Y := Group.isSolvable_of_ker_le_range f g hfg
  exact Group.isSolvable_of_surjective (f := (Y.equivMapOfInjective H.subtype
    H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

theorem le_star_M (h1229 : Lemma12_6_29) {T L V : Subgroup G} [IsMulCommutative ↥V]
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hTH : T ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥)
    {X : Subgroup (HStar H)} (hTX : star H T ≤ X) (hX : Group.IsSolvable X) :
    X ≤ star H (Subgroup.normalizer (L : Set G) ⊓ H) := by
  have hTp : T ≤ pre H X := fun t ht =>
    mem_pre.2 ⟨hTH ht, hTX (mk_mem_star (h := ⟨t, hTH ht⟩) ht)⟩
  have hO : pCoreOf 2 H ≤ pCoreOf 2 (pre H X) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_pre X)
      ((pre_le X).trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hInH : InH T (pre H X) := ⟨hTp, fun h0 => hO2 (le_bot_iff.1 (h0 ▸ hO))⟩
  have hle := h1229 G T L V F hH hZ (pre H X) hInH (Or.inr (isSolvable_pre hX))
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact mk_mem_star ⟨hle (mem_pre.2 ⟨h.2, hx⟩), h.2⟩

end Star

section TwoThree

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_pow_eq_one_of_mem (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {g : G} (hgL : g ∈ L) (hg1 : g ∈ Subgroup.normalizer (F.V1 : Set G)) :
    ∃ k : ℕ, g ^ (24 * 2 ^ k) = 1 := by
  set l : ↥L := ⟨g, hgL⟩
  have h24 : ((S126L19a.psi F hH l : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) ^ 24 =
      1 := S126L19a.pow_24 (S126L19a.blocks_of_mem_V1 F hg1 (S126L19a.actsAs_psi F hH l))
  have h1 : S126L19a.psi F hH (l ^ 24) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by rw [Subgroup.coe_pow, h24]; rfl)
  have hc := (S126L19a.psi_eq_one_iff F hH _).1 h1
  obtain ⟨k, hk⟩ := S126L19a.isPGroup_ker h1222 hH ⟨l ^ 24, hc⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) => ((z : ↥L) : G)) hk
  simpa [pow_mul] using this

theorem eq_one_of_coprime_of_L1T (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hT1 : T ≤ Subgroup.normalizer (F.V1 : Set G)) {x : G}
    (hx : x ∈ Li L F.V1 ⊔ T) {n : ℕ} (hn : x ^ n = 1) (hcop : Nat.Coprime n 6) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow
    (le_sup_right : T ≤ L ⊔ T)).2.1
  have hn2 : Nat.Coprime n 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  set W : Subgroup G := L ⊔ T with hW
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hxW : x ∈ W := (sup_le_sup_right F126.L1_le_L T) hx
  have hN : (L.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hWL
  have htop : L.subgroupOf W ⊔ T.subgroupOf W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hxs : (⟨x, hxW⟩ : ↥W) ∈ L.subgroupOf W ⊔ T.subgroupOf W := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hxs
  have hxL : x ∈ L := by
    set π := QuotientGroup.mk' (L.subgroupOf W) with hπ
    have hy1 : π y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    have h1 : π ⟨x, hxW⟩ = π z := by
      rw [← hyz, map_mul, hy1, one_mul]
    obtain ⟨a, ha⟩ := hT2 ⟨(z : G), hz⟩
    have hza : z ^ 2 ^ a = 1 := Subtype.ext (by
      have := congrArg Subtype.val ha
      simpa using this)
    have h2 : (π ⟨x, hxW⟩) ^ 2 ^ a = 1 := by rw [h1, ← map_pow, hza, map_one]
    have h3 : (π ⟨x, hxW⟩) ^ n = 1 := by
      rw [← map_pow]
      have : (⟨x, hxW⟩ : ↥W) ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [this, map_one]
    have h4 : orderOf (π ⟨x, hxW⟩) = 1 := by
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
      rwa [Nat.Coprime.gcd_eq_one (hn2.pow_right a), Nat.dvd_one] at hd
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
    exact h4
  have hL1 : Li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) := (oTwoRes_le _).trans inf_le_right
  have hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G) := (sup_le hL1 hT1) hx
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem h1222 F hH hxL hx1
  have hcop' : Nat.Coprime n (24 * 2 ^ k) := by
    refine Nat.Coprime.mul_right ?_ (hn2.pow_right k)
    exact Nat.Coprime.coprime_dvd_right (by norm_num : (24 : ℕ) ∣ 6 * 4)
      (Nat.Coprime.mul_right hcop (hn2.pow_right 2))
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hk)
  rw [Nat.Coprime.gcd_eq_one hcop', Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem coprime_card_L1T (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hT1 : T ≤ Subgroup.normalizer (F.V1 : Set G)) {n : ℕ} (hcop : Nat.Coprime n 6) :
    Nat.Coprime n (Nat.card ↥(Li L F.V1 ⊔ T)) := by
  refine Nat.coprime_of_dvd fun p hp hpn hpm => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpm
  have hp6 : Nat.Coprime p 6 := (Nat.Coprime.coprime_dvd_left hpn hcop)
  have h1 := eq_one_of_coprime_of_L1T h1222 F hH hT1 g.2
    (show (g : G) ^ p = 1 by rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one]; rfl) hp6
  have : g = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hg
  exact hp.one_lt.ne hg

theorem mem_star_of_coprime (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hT1 : T ≤ Subgroup.normalizer (F.V1 : Set G)) {H X : Subgroup G} (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hLTH : Li L F.V1 ⊔ T ≤ H)
    (hHe : H = X ⊔ (Li L F.V1 ⊔ T)) {x : HStar H} {n : ℕ} (hn : x ^ n = 1)
    (hcop : Nat.Coprime n 6) : x ∈ star H X := by
  have hN : (star H X).Normal := normal_star hHX
  have htop : star H X ⊔ star H (Li L F.V1 ⊔ T) = ⊤ := by
    rw [← star_sup hXH hLTH, ← hHe, star_self]
  have hx : x ∈ star H X ⊔ star H (Li L F.V1 ⊔ T) := htop ▸ Subgroup.mem_top x
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  obtain ⟨h, hh, rfl⟩ := hb
  set m := Nat.card ↥(Li L F.V1 ⊔ T) with hm
  have hbm : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) ^ m = 1 := by
    rw [← map_pow]
    have h1 : ((h : G) ^ m) = 1 := by
      have := pow_card_eq_one' (G := ↥(Li L F.V1 ⊔ T)) (x := ⟨h, hh⟩)
      exact congrArg Subtype.val this
    have h2 : h ^ m = 1 := Subtype.ext (by simpa using h1)
    rw [h2, map_one]
  set π := QuotientGroup.mk' (star H X) with hπ
  have ha1 : π a = 1 := (QuotientGroup.eq_one_iff a).2 ha
  have h1 : π (a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) ^ m = 1 := by
    rw [map_mul, ha1, one_mul, ← map_pow, hbm, map_one]
  have h2 : π (a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) ^ n = 1 := by
    rw [← map_pow, hn, map_one]
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [Nat.Coprime.gcd_eq_one (coprime_card_L1T h1222 F hH hT1 hcop), Nat.dvd_one,
    orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hd
  exact hd

end TwoThree

section Rank

variable {Q : Type*} [Group Q] [Finite Q]

theorem le_pRank_top {p : ℕ} (hp : 1 < p) {E : Subgroup Q} (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p (⊤ : Subgroup Q) := by
  refine le_csSup ⟨Nat.card Q, ?_⟩ ⟨E, le_top, hE, hk⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card Q := Subgroup.card_le_card_group B

theorem three_le_pRank {A B C : Subgroup Q} (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hC : Nat.card C = 3) (hAB : A ≤ Subgroup.centralizer (B : Set Q))
    (hAC : A ≤ Subgroup.centralizer (C : Set Q)) (hBC : B ≤ Subgroup.centralizer (C : Set Q))
    (hi : A ⊓ B = ⊥) (hi' : (A ⊔ B) ⊓ C = ⊥) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ {X : Subgroup Q}, Nat.card X = 3 → X ≤ Subgroup.centralizer (X : Set Q) :=
    fun hX => by
      have := isCyclic_of_prime_card hX
      exact Subgroup.le_centralizer_iff_isMulCommutative.2 inferInstance
  have hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  have hABC : A ⊔ B ≤ Subgroup.centralizer (C : Set Q) := sup_le hAC hBC
  have hcABC : ∀ a ∈ A ⊔ B, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (hABC ha) c hc).symm
  set E := (A ⊔ B) ⊔ C with hE
  have hcard : Nat.card E = 3 ^ 3 := by
    rw [hE, L1233.card_sup_of_commute hcABC hi', L1233.card_sup_of_commute hcAB hi, hA, hB, hC]
    norm_num
  have hBA : B ≤ Subgroup.centralizer (A : Set Q) := Subgroup.le_centralizer_iff.1 hAB
  have hCA : C ≤ Subgroup.centralizer (A : Set Q) := Subgroup.le_centralizer_iff.1 hAC
  have hCB : C ≤ Subgroup.centralizer (B : Set Q) := Subgroup.le_centralizer_iff.1 hBC
  have hEA : E ≤ Subgroup.centralizer (A : Set Q) := sup_le (sup_le (hcomm hA) hBA) hCA
  have hEB : E ≤ Subgroup.centralizer (B : Set Q) := sup_le (sup_le hAB (hcomm hB)) hCB
  have hEC : E ≤ Subgroup.centralizer (C : Set Q) := sup_le (sup_le hAC hBC) (hcomm hC)
  have hEE : E ≤ Subgroup.centralizer (E : Set Q) :=
    Subgroup.le_centralizer_iff.1 (sup_le (sup_le (Subgroup.le_centralizer_iff.1 hEA)
      (Subgroup.le_centralizer_iff.1 hEB)) (Subgroup.le_centralizer_iff.1 hEC))
  have h3 : ∀ {X : Subgroup Q}, Nat.card X = 3 → ∀ x ∈ X, x ^ 3 = 1 := by
    intro X hX x hx
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
    rw [hX] at this
    exact congrArg Subtype.val this
  let S : Subgroup Q :=
    { carrier := {x | x ∈ E ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (Subgroup.mem_centralizer_iff.1 (hEE hy.1) x hx.1) 3), hx.2,
          hy.2, one_mul]⟩
      one_mem' := ⟨E.one_mem, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hAS : A ≤ S := fun a ha => ⟨(le_sup_left.trans le_sup_left : A ≤ E) ha, h3 hA a ha⟩
  have hBS : B ≤ S := fun b hb => ⟨(le_sup_right.trans le_sup_left : B ≤ E) hb, h3 hB b hb⟩
  have hCS : C ≤ S := fun c hc => ⟨(le_sup_right : C ≤ E) hc, h3 hC c hc⟩
  have hES : E ≤ S := sup_le (sup_le hAS hBS) hCS
  refine le_pRank_top (by norm_num) ⟨Subgroup.le_centralizer_iff_isMulCommutative.1 hEE,
    fun x hx => (hES hx).2⟩ hcard

end Rank

section Setting

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem pCoreOf_ne_bot {V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H) : pCoreOf 2 H ≠ ⊥ :=
  fun h0 => h.V₁_ne_bot (le_bot_iff.1 (h0 ▸ h.V₁_le_pCoreOf))

omit [IsMulCommutative ↥V] in
theorem isSylowTwoOf_T {V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H) :
    QuasithinUnique.IsSylowTwoOf T H :=
  A4.isSylowTwoOf_mono h.sylow h.T_le_H le_top

omit [IsMulCommutative ↥V] in
theorem pRank_hStar_le (hH : Hyp126 G T L V) {H : Subgroup G} (hO2 : pCoreOf 2 H ≠ ⊥) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (HStar H)) ≤ 2 :=
  (sqtkHyp_quotient_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian hO2).sqt 3
    Nat.prime_three (by norm_num)

omit [IsMulCommutative ↥V] in
theorem false_of_three (hH : Hyp126 G T L V) {H : Subgroup G} (hO2 : pCoreOf 2 H ≠ ⊥)
    {A B C : Subgroup (HStar H)} (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hC : Nat.card C = 3) (hAB : A ≤ Subgroup.centralizer (B : Set (HStar H)))
    (hAC : A ≤ Subgroup.centralizer (C : Set (HStar H)))
    (hBC : B ≤ Subgroup.centralizer (C : Set (HStar H))) (hi : A ⊓ B = ⊥)
    (hi' : (A ⊔ B) ⊓ C = ⊥) : False := by
  have h1 := three_le_pRank hA hB hC hAB hAC hBC hi hi'
  have h2 := pRank_hStar_le hH hO2
  omega

theorem four_le_relIndex (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    4 ≤ (Ri T L F.V1).relIndex T := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  set R := Ri T L F.V1 with hR
  have hcT := S126L19a.card_eq F hH (inf_le_right : T ⊓ L ≤ L)
  have hcR := S126L19a.card_eq F hH (inf_le_right : R ⊓ L ≤ L)
  have hTbar : Nat.card ↥(((T ⊓ L).subgroupOf L).map (S126L19a.psi F hH)) = 64 :=
    S126L19c.card_Tbar F hH
  have hRbar : Nat.card ↥(((R ⊓ L).subgroupOf L).map (S126L19a.psi F hH)) ≤ 16 := by
    have hmem : ∀ y ∈ ((R ⊓ L).subgroupOf L).map (S126L19a.psi F hH),
        (y : Equiv.Perm (Fin 8)) ∈ S126E.E16 := by
      rintro _ ⟨l, hl, rfl⟩
      exact S126L1b.mem_E16 F hTV hR1T (Subgroup.mem_subgroupOf.1 hl).1
        (S126L19a.actsAs_psi F hH l)
    have hinj : Function.Injective fun y : ↥(((R ⊓ L).subgroupOf L).map (S126L19a.psi F hH)) =>
        (⟨((y : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)), hmem y y.2⟩ : ↥S126E.E16) := by
      intro y₁ y₂ h
      have h' : ((y₁ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) = y₂ :=
        congrArg (fun z : ↥S126E.E16 => (z : Equiv.Perm (Fin 8))) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.card_le_card_of_injective _ hinj).trans S126E.card_E16_le
  have hCle : Nat.card ↥(R ⊓ L ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ (inf_le_inf_right _ hR1T))
  have hpos : 0 < Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h1 := Subgroup.relIndex_mul_card (H := R) (K := T ⊓ L)
  have hRTL : R ⊓ (T ⊓ L) = R ⊓ L := by rw [← inf_assoc, inf_of_le_left hR1T]
  rw [hRTL] at h1
  have hne : R.relIndex T ≠ 0 := by
    intro h0
    have h3 := Subgroup.relIndex_mul_card (H := R) (K := T)
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := ↥T)).ne h3
  have h2 : R.relIndex (T ⊓ L) ≤ R.relIndex T :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  rw [hcT, hTbar] at h1
  rw [hcR] at h1
  nlinarith

end Setting

end CFSG.Quasithin.H13.S126P31
