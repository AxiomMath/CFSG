module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAbsorb
public import CFSG.LocalAnalysis.StandardType.GGQTwoTwoPart

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

open scoped commutatorElement

@[expose] def GGStdPair' {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (w : G)
    (X : Subgroup G) : Prop :=
  w ∈ Bs ∧ w ≠ 1 ∧ LargeEvenPComponent p (Subgroup.centralizer ({w} : Set G)) X ∧
    Bs ≤ Subgroup.normalizer (X : Set G) ∧
    Nat.card {b : ↥Bs // ⁅X, Subgroup.zpowers (b : G)⁆ ≤ LargeEvenPPrimeCoreOf p X} ≤ p ^ 2 ∧
    4 ∣ Nat.card ↥(ggAutomizer X Bs)

private theorem ggQ2nA_commutator_zpowers_le {G : Type} [Group G] {X P : Subgroup G} {c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (h : ∀ x ∈ X, ⁅x, c⁆ ∈ P) :
    ⁅X, Subgroup.zpowers c⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hT : ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ P := by
    let T : Subgroup G :=
      { carrier := {z : G | z ∈ Subgroup.normalizer (P : Set G) ∧ ⁅x, z⁆ ∈ P}
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          intro y z hy hz
          obtain ⟨hyN, hyP⟩ := hy
          obtain ⟨hzN, hzP⟩ := hz
          refine ⟨Subgroup.mul_mem _ hyN hzN, ?_⟩
          have h1 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          rw [h1]
          exact P.mul_mem hyP ((Subgroup.mem_normalizer_iff.mp hyN _).mp hzP)
        inv_mem' := by
          intro y hy
          obtain ⟨hyN, hyP⟩ := hy
          refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
          have h1 : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          have h2 : y⁻¹ * ⁅x, y⁆ * y ∈ P := by
            have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hyP
            simpa only [inv_inv] using h3
          rw [h1]
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using Subgroup.inv_mem _ h2 }
    have hcT : c ∈ T := ⟨hcP, h x hx⟩
    intro z hz
    exact (Subgroup.zpowers_le.mpr hcT hz).2
  exact hT z hz

private theorem ggQ2nA_commutator_le {G : Type} [Group G] {p : ℕ}
    {Bs Q X Y O : Subgroup G} {n b : G}
    (hnQ : n ∈ Q) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) (hb : b ∈ Bs)
    (hQY : Q ≤ Y) (hBsY : Bs ≤ Y) (hOn : Y ≤ Subgroup.normalizer (O : Set G))
    (hcommQ : ⁅Q, X⁆ ≤ O) (hXO : X ⊓ O ≤ LargeEvenPPrimeCoreOf p X)
    (hXBs : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ⁅n, b⁆ ∈ Bs ∧ ⁅X, Subgroup.zpowers ⁅n, b⁆⁆ ≤ LargeEvenPPrimeCoreOf p X := by
  have hnY : n ∈ Y := hQY hnQ
  set h : G := b * n * b⁻¹ with hhdef
  set c : G := n * h⁻¹ with hcdef
  have hc_eq : c = ⁅n, b⁆ := by
    rw [hcdef, hhdef, commutatorElement_def]
    group
  have hcBs : c ∈ Bs := by
    have h1 : n * b * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN b).mp hb
    rw [hc_eq, commutatorElement_def]
    exact Bs.mul_mem h1 (Bs.inv_mem hb)
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := hXBs hcBs
  have hcP : c ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p X : Set G) :=
    mem_normalizer_largeEvenPPrimeCoreOf hcN
  have hhY : h ∈ Y := by
    rw [hhdef]
    exact Y.mul_mem (Y.mul_mem (hBsY hb) hnY) (Y.inv_mem (hBsY hb))
  have hxc : ∀ z ∈ X, ⁅z, c⁆ ∈ LargeEvenPPrimeCoreOf p X := by
    intro z hz
    have hhz : ⁅h, z⁆ ∈ O := by
      have hbz : b⁻¹ * z * b ∈ X := by
        have hbN : b⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
          Subgroup.inv_mem _ (hXBs hb)
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbN z).mp hz
      have h1 : ⁅h, z⁆ = b * ⁅n, b⁻¹ * z * b⁆ * b⁻¹ := by
        rw [hhdef, commutatorElement_def, commutatorElement_def]
        group
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp (hOn (hBsY hb)) _).mp
        ((Subgroup.commutator_le.mp hcommQ) n hnQ (b⁻¹ * z * b) hbz)
    have hnz : ⁅n, z⁆ ∈ O := (Subgroup.commutator_le.mp hcommQ) n hnQ z hz
    set o3 : G := (n * ⁅h⁻¹, z⁆ * n⁻¹) * ⁅n, z⁆ with ho3def
    have hhinv : ⁅h⁻¹, z⁆ ∈ O := by
      have h1 : h⁻¹ * ⁅h, z⁆ * h ∈ O := by
        have h3 := (Subgroup.mem_normalizer_iff.mp (hOn (Y.inv_mem hhY)) _).mp hhz
        simpa only [inv_inv] using h3
      have h2 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ ∈ O := Subgroup.inv_mem _ h1
      have h3 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ = ⁅h⁻¹, z⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rwa [h3] at h2
    have ho3O : o3 ∈ O :=
      O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hOn hnY) _).mp hhinv) hnz
    have hcx : c * z * c⁻¹ = o3 * z := by
      rw [hcdef, ho3def, hhdef]
      simp only [commutatorElement_def]
      group
    have ho3X : o3 ∈ X := by
      have h1 : o3 = (c * z * c⁻¹) * z⁻¹ := by
        rw [hcx]
        group
      rw [h1]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN z).mp hz) (X.inv_mem hz)
    have ho3P : o3 ∈ LargeEvenPPrimeCoreOf p X := hXO ⟨ho3X, ho3O⟩
    have hcz : ⁅c, z⁆ = o3 := by
      rw [commutatorElement_def, hcx]
      group
    have hzc : ⁅z, c⁆ = o3⁻¹ := by
      rw [← commutatorElement_inv c z, hcz]
    rw [hzc]
    exact Subgroup.inv_mem _ ho3P
  have hcommzp : ⁅X, Subgroup.zpowers c⁆ ≤ LargeEvenPPrimeCoreOf p X :=
    ggQ2nA_commutator_zpowers_le hcP hxc
  exact ⟨hc_eq ▸ hcBs, hc_eq ▸ hcommzp⟩

theorem ggQ2n_absorb {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3) {w : G} {F X Q : Subgroup G}
    (hFBs : F ≤ Bs) (hwF : w ∈ F) (hX : GGStdPair' p Bs w X)
    (hQ : LargeEvenPComponent p (Subgroup.centralizer (F : Set G)) Q)
    (hQa : 4 ∣ Nat.card ↥(ggAutomizer Q Bs)) : Q ≤ X := by
  classical
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBs, -⟩ := hcfg
  haveI : IsSimpleGroup G := hI.1
  have hpp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hBsabel : IsElemAbelian p Bs := hBs.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hwBs : w ∈ Bs := hX.1
  let Y : Subgroup G := Subgroup.centralizer ({w} : Set G)
  have hQF : Q ≤ Subgroup.centralizer (F : Set G) :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (F : Set G)) Q).1 hQ).1
  have hQY : Q ≤ Y := hQF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF))
  have hBsY : Bs ≤ Y := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hwBs b hb).symm
  have hYne : Y ≠ ⊤ := centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hX.2.1
  have hYK : CFSG.Open.lBalanceIsKGroup ↥Y := lBalanceIsKGroup_of_kProper hI.2.2.1 hYne
  have hXpc : CFSG.Open.lBalanceIsPComponent p Y X :=
    ((largeEvenPComponent_iff_lBalance p Y X).1 hX.2.2.1).2
  have hTpc : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer (F : Set G)) Q :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (F : Set G)) Q).1 hQ).2
  rcases GGDichotomy.dichotomy_core hLB hpp hcomm hexp hFBs hwF hYK hX.2.2.2.1 hXpc hTpc with
    hQX | hcommQ
  · exact hQX
  · exfalso
    let O : Subgroup G := CFSG.Open.lBalancePrimeCore p Y
    have hXY : X ≤ Y := ((largeEvenPComponent_iff_lBalance p Y X).1 hX.2.2.1).1
    have hOn : Y ≤ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
        (LBalance.primeCore_normal p Y)
    have hXO : X ⊓ O ≤ LargeEvenPPrimeCoreOf p X := by
      have hK : ((X ⊓ O).subgroupOf X) ≤ CFSG.pPrimeCore p X := by
        apply le_sSup
        refine ⟨?_, ?_⟩
        · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
          intro y k hy hk
          obtain ⟨hyX, hyO⟩ := hy
          refine ⟨X.mul_mem (X.mul_mem hk hyX) (X.inv_mem hk), ?_⟩
          exact (Subgroup.mem_normalizer_iff.mp (hOn (hXY hk)) y).mp hyO
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
          exact (LBalance.primeCore_coprime p Y).of_dvd_right
            (Subgroup.card_dvd_of_le inf_le_right)
      calc X ⊓ O = ((X ⊓ O).subgroupOf X).map X.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
        _ ≤ (CFSG.pPrimeCore p X).map X.subtype := Subgroup.map_mono hK
    let Z : Subgroup G :=
      { carrier := {c : G | c ∈ Bs ∧ ⁅X, Subgroup.zpowers c⁆ ≤ LargeEvenPPrimeCoreOf p X}
        one_mem' := by
          refine ⟨Bs.one_mem, ?_⟩
          rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
          exact bot_le
        mul_mem' := by
          intro a b ha hb
          obtain ⟨haBs, haP⟩ := ha
          obtain ⟨hbBs, hbP⟩ := hb
          refine ⟨Bs.mul_mem haBs hbBs, ?_⟩
          have haN : a ∈ Subgroup.normalizer (X : Set G) := hX.2.2.2.1 haBs
          have hbN : b ∈ Subgroup.normalizer (X : Set G) := hX.2.2.2.1 hbBs
          have haON : a ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p X : Set G) :=
            mem_normalizer_largeEvenPPrimeCoreOf haN
          have hxa : ∀ x ∈ X, ⁅x, a⁆ ∈ LargeEvenPPrimeCoreOf p X := fun x hx =>
            (Subgroup.commutator_le.mp haP) x hx a (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
          have hxb : ∀ x ∈ X, ⁅x, b⁆ ∈ LargeEvenPPrimeCoreOf p X := fun x hx =>
            (Subgroup.commutator_le.mp hbP) x hx b (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
          have h : ∀ x ∈ X, ⁅x, a * b⁆ ∈ LargeEvenPPrimeCoreOf p X := by
            intro x hx
            have h1 : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
              rw [commutatorElement_def, commutatorElement_def]
              group
            rw [h1]
            exact (LargeEvenPPrimeCoreOf p X).mul_mem (hxa x hx)
              ((Subgroup.mem_normalizer_iff.mp haON _).mp (hxb x hx))
          exact ggQ2nA_commutator_zpowers_le
            (mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.mul_mem _ haN hbN)) h
        inv_mem' := by
          intro a ha
          obtain ⟨haBs, haP⟩ := ha
          refine ⟨Bs.inv_mem haBs, ?_⟩
          have haN : a ∈ Subgroup.normalizer (X : Set G) := hX.2.2.2.1 haBs
          have haON : a ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p X : Set G) :=
            mem_normalizer_largeEvenPPrimeCoreOf haN
          have h : ∀ x ∈ X, ⁅x, a⁻¹⁆ ∈ LargeEvenPPrimeCoreOf p X := by
            intro x hx
            have hxa : ⁅x, a⁆ ∈ LargeEvenPPrimeCoreOf p X :=
              (Subgroup.commutator_le.mp haP) x hx a (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
            have h1 : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
              rw [commutatorElement_def, commutatorElement_def]
              group
            have h3 : a⁻¹ * ⁅x, a⁆ * a ∈ LargeEvenPPrimeCoreOf p X := by
              simpa only [inv_inv] using
                (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haON) ⁅x, a⁆).mp hxa
            rw [h1]
            have h4 : (a⁻¹ * ⁅x, a⁆ * a)⁻¹ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by group
            rw [← h4]
            exact Subgroup.inv_mem _ h3
          exact ggQ2nA_commutator_zpowers_le
            (mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.inv_mem _ haN)) h }
    have hZBs : Z ≤ Bs := fun c hc => hc.1
    have hZcard : Nat.card ↥Z ≤ p ^ 2 := by
      have he : Nat.card ↥Z =
          Nat.card {b : ↥Bs // ⁅X, Subgroup.zpowers (b : G)⁆ ≤ LargeEvenPPrimeCoreOf p X} :=
        Nat.card_congr
          { toFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
            invFun := fun b => ⟨b.1.1, b.1.2, b.2⟩
            left_inv := fun z => rfl
            right_inv := fun b => rfl }
      rw [he]
      exact hX.2.2.2.2.1
    have hwZ : w ∈ Z := by
      refine ⟨hX.1, ?_⟩
      refine ggQ2nA_commutator_zpowers_le ?_ ?_
      · exact mem_normalizer_largeEvenPPrimeCoreOf (hX.2.2.2.1 hX.1)
      · intro t ht
        have htw : t * w = w * t := Subgroup.mem_centralizer_singleton_iff.mp (hXY ht)
        have h1 : ⁅t, w⁆ = 1 := by
          rw [commutatorElement_def, htw]
          group
        rw [h1]
        exact (LargeEvenPPrimeCoreOf p X).one_mem
    have hZF : Z ⊓ F ≠ ⊥ := by
      intro hbot
      have hmem : w ∈ Z ⊓ F := ⟨hwZ, hwF⟩
      rw [hbot] at hmem
      exact hX.2.1 (Subgroup.mem_bot.mp hmem)
    have hS : ∀ φ ∈ ggInduced Q Bs,
        (∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ Z) ∧
          ∀ f : ↥Bs, (f : G) ∈ F → φ f = f := by
      intro φ hφ
      obtain ⟨n, hnQ, hnN, hφg⟩ := hφ
      constructor
      · intro b
        obtain ⟨hcBs, hcP⟩ :=
          ggQ2nA_commutator_le (Bs := Bs) (Q := Q) (X := X) (Y := Y) (O := O)
            (n := n) (b := (b : G)) hnQ hnN b.2 hQY hBsY hOn hcommQ hXO hX.2.2.2.1
        have hb1 : ((b⁻¹ * φ b : ↥Bs) : G) = (b : G)⁻¹ * (n * (b : G) * n⁻¹) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hφg b]
        have hb2 : (b : G)⁻¹ * (n * (b : G) * n⁻¹) = ⁅n, (b : G)⁆ := by
          have hnb : n * (b : G) * n⁻¹ ∈ Bs :=
            (Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp b.2
          have hc := hcomm (b : G)⁻¹ (Bs.inv_mem b.2) (n * (b : G) * n⁻¹) hnb
          rw [commutatorElement_def, hc]
        rw [hb1, hb2]
        exact ⟨hcBs, hcP⟩
      · intro f hf
        apply Subtype.ext
        rw [hφg f]
        have hfn : (f : G) * n = n * (f : G) :=
          (Subgroup.mem_centralizer_iff.mp (hQF hnQ)) (f : G) hf
        rw [← hfn]
        group
    have hnot := ggQ2n_closure_two_part hp hBsabel hZBs hFBs hZcard hZF (ggInduced Q Bs) hS
    exact hnot (show 4 ∣ Nat.card ↥(Subgroup.closure (ggInduced Q Bs)) from hQa)

end CFSG.StandardType

end
