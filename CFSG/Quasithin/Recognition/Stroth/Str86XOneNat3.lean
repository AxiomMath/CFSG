module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOneChief
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat2
public import CFSG.Quasithin.Vol2.Ch3wPair
public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneUpper2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_of_binaryNaturalSU3 {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {k : ℕ} (h : BinaryNaturalSU3 L ⊤ ⊥ k) :
    Nat.card V = (2 ^ k) ^ 6 := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨-, -, -, -, -, -, -, β, hβsurj, hβker, -⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_bot]
    have h1 : ((a : ↥(⊤ : Subgroup V)) : V) ∈ (⊥ : Subgroup V) := (hβker a).mp ha
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hbij : Nat.card (↥(⊤ : Subgroup V)) =
      Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβsurj⟩)
  have htop : (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤ = ⊥ := by simp
  calc Nat.card V
      = Nat.card (↥(⊤ : Subgroup V)) :=
        (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    _ = Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
          (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) := hbij
    _ = Nat.card (Multiplicative (Fin 3 → K)) := by
        rw [htop]
        exact Nat.card_congr (QuotientGroup.quotientBot.trans Subgroup.topEquiv).toEquiv
    _ = Nat.card (Fin 3 → K) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card K ^ 3 := by
        rw [Nat.card_pi]
        simp
    _ = (2 ^ k) ^ 6 := by
        rw [hKcard, ← pow_mul]

theorem exists_chiefModEquiv {H L N Z X : Subgroup G}
    (hcomm : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n)
    (hNX : N ≤ X) (hZX : Z ≤ X) (hL : N ⊓ Z = L) (hX : N ⊔ Z = X)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hHX : H ≤ Subgroup.normalizer (X : Set G))
    [(Z.subgroupOf X).Normal] :
    ∃ j : ↥(Ch3z.chiefMod L N) ≃* (X ⧸ Z.subgroupOf X),
      (∀ n : ↥N, j (Ch3z.chiefIota hNL n) = QuotientGroup.mk ⟨n, hNX n.2⟩) ∧
      (Ch3z.chiefAut H L N).map (MulAut.congr j).toMonoidHom =
        (CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHX hHZ).range ∧
      (CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHX hHZ).range.map
          (MulAut.congr j.symm).toMonoidHom = Ch3z.chiefAut H L N := by
  classical
  haveI : (L.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNL
  let gN : ↥N →* (X ⧸ Z.subgroupOf X) :=
    (QuotientGroup.mk' (Z.subgroupOf X)).comp (Subgroup.inclusion hNX)
  have hgN : ∀ n : ↥N, gN n = QuotientGroup.mk ⟨n, hNX n.2⟩ := fun n => rfl
  have hkerL : L.subgroupOf N ≤ gN.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hgN, QuotientGroup.eq_one_iff]
    have hnNZ : (n : G) ∈ N ⊓ Z := hL.symm ▸ Subgroup.mem_subgroupOf.mp hn
    exact (Subgroup.mem_inf.mp hnNZ).2
  let gL : ↥N ⧸ L.subgroupOf N →* (X ⧸ Z.subgroupOf X) :=
    QuotientGroup.lift (L.subgroupOf N) gN hkerL
  have hgL : ∀ n : ↥N, gL (QuotientGroup.mk n) = QuotientGroup.mk ⟨n, hNX n.2⟩ := by
    intro n
    exact hgN n
  let jHom : ↥(Ch3z.chiefMod L N) →* (X ⧸ Z.subgroupOf X) :=
    gL.comp (Ch3z.chiefQuotEquiv hNL).symm.toMonoidHom
  have hj : ∀ n : ↥N, jHom (Ch3z.chiefIota hNL n) =
      QuotientGroup.mk ⟨n, hNX n.2⟩ := by
    intro n
    have h1 : (Ch3z.chiefQuotEquiv hNL).symm (Ch3z.chiefIota hNL n) =
        QuotientGroup.mk n := by
      rw [← Ch3z.chiefQuotEquiv_mk hNL n, MulEquiv.symm_apply_apply]
    show gL ((Ch3z.chiefQuotEquiv hNL).symm (Ch3z.chiefIota hNL n)) = _
    rw [h1, hgL]
  have hsurj : Function.Surjective jHom := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) y
    have hx : (x : G) ∈ N ⊔ Z := hX ▸ x.2
    obtain ⟨n, hn, z, hz, hnz⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
    refine ⟨Ch3z.chiefIota hNL ⟨n, hn⟩, ?_⟩
    rw [hj]
    have hxeq : x = (⟨n, hNX hn⟩ : ↥X) * ⟨z, hZX hz⟩ := by
      apply Subtype.ext
      show (x : G) = n * z
      rw [hnz]
    have hz1 : QuotientGroup.mk' (Z.subgroupOf X) ⟨z, hZX hz⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    rw [hxeq, map_mul, hz1, mul_one]
    rfl
  have hinj : Function.Injective jHom := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL a
    rw [Subgroup.mem_bot]
    have h1 : ((⟨n, hNX n.2⟩ : ↥X) : X ⧸ Z.subgroupOf X) = 1 := by
      rw [← hj n]
      exact ha
    have h2 : (⟨n, hNX n.2⟩ : ↥X) ∈ Z.subgroupOf X :=
      (QuotientGroup.eq_one_iff (⟨n, hNX n.2⟩ : ↥X)).mp h1
    have h1Z : (n : G) ∈ Z := Subgroup.mem_subgroupOf.mp h2
    refine (Ch3z.chiefIota_eq_one_iff hNL n).mpr ?_
    have hmem : (n : G) ∈ N ⊓ Z := Subgroup.mem_inf.mpr ⟨n.2, h1Z⟩
    rwa [hL] at hmem
  let j : ↥(Ch3z.chiefMod L N) ≃* (X ⧸ Z.subgroupOf X) :=
    MulEquiv.ofBijective jHom ⟨hinj, hsurj⟩
  have hj' : ∀ n : ↥N, j (Ch3z.chiefIota hNL n) =
      QuotientGroup.mk ⟨n, hNX n.2⟩ := fun n => hj n
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hL]
    exact (le_inf hHN hHZ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnat : ∀ (h : ↥H) (y : X ⧸ Z.subgroupOf X),
      (MulAut.congr j).toMonoidHom (Ch3z.chiefPsi hHL hHN h) y =
        CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHX hHZ h y := by
    intro h y
    obtain ⟨x, rfl⟩ := j.surjective y
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL x
    have hgn : (h : G) * (n : G) * (h : G)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hHN h.2) (n : G)).mp n.2
    have hLHS : (MulAut.congr j).toMonoidHom (Ch3z.chiefPsi hHL hHN h)
        (j (Ch3z.chiefIota hNL n)) =
        j (Ch3z.chiefPsi hHL hHN h (Ch3z.chiefIota hNL n)) := by
      show j ((Ch3z.chiefPsi hHL hHN h) (j.symm (j (Ch3z.chiefIota hNL n)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hLHS, Ch3z.chiefPsi_iota hHL hHN hNL h n hgn, hj']
    rw [hj', CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_mk]
    have hcz : (⟨(h : G) * (n : G) * (h : G)⁻¹, hNX hgn⟩ : ↥X) =
        CFSG.Quasithin.conjAct X ⟨(h : G), hHX h.2⟩ ⟨(n : G), hNX n.2⟩ := by
      apply Subtype.ext
      exact Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨(h : G), hHX h.2⟩ ⟨(n : G), hNX n.2⟩
    rw [hcz]
  have hcomp : (MulAut.congr j).toMonoidHom.comp (Ch3z.chiefPsi hHL hHN) =
      CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHX hHZ := by
    ext h y
    exact hnat h y
  have hsymm : (MulAut.congr j.symm).toMonoidHom.comp (MulAut.congr j).toMonoidHom =
      MonoidHom.id (MulAut ↥(Ch3z.chiefMod L N)) := by
    ext f w
    simp [MulAut.congr, MulEquiv.trans_apply]
  refine ⟨j, hj', ?_, ?_⟩
  · calc (Ch3z.chiefAut H L N).map (MulAut.congr j).toMonoidHom
        = (Ch3z.chiefPsi hHL hHN).range.map (MulAut.congr j).toMonoidHom := by
          rw [Ch3w.range_chiefPsi hHL hHN]
      _ = ((MulAut.congr j).toMonoidHom.comp (Ch3z.chiefPsi hHL hHN)).range := by
          rw [MonoidHom.range_comp]
      _ = (CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHX hHZ).range := by rw [hcomp]
  · rw [← hcomp, MonoidHom.range_comp, Subgroup.map_map, hsymm, Subgroup.map_id,
      Ch3w.range_chiefPsi hHL hHN]

theorem str86_X1Natural_holds
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    Str86X1Natural hF k hX1' := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSeq : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hSH : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hSeq
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hLS : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := u3LS_eq_sup_q1 hF hSB h1
  have hcent : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (sup_le le_sup_left hSH).trans hZI
  have hZH : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hZcentral : ∀ h ∈ (L1 ⊔ S : Subgroup G), ∀ z ∈ Z1 L1 L2 S, h * z = z * h := by
    intro h hh z hz
    exact (Subgroup.mem_centralizer_iff.mp (hcent hh) z hz).symm
  have hZX : Z1 L1 L2 S ≤ u3X1 L1 L2 S := u3Z1_le_u3X1 hF hSB h1 hB2 h2 hZI
  have hXH : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans (hQ1S.trans le_sup_right)
  have hNX : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF hg) x).mp hx⟩
  obtain ⟨c, hser⟩ :=
    D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S) (U := u3X1 L1 L2 S)
      (u3X1 L1 L2 S) hNX
  have hc : c = 1 := str86_chief_count_eq_one hF hSB hk hFc hU3 hL2 hZQ hser
  obtain ⟨L, N, hstep, hnc, hNleX⟩ := exists_noncentral_chiefStep hser hc
  have hZL : Z1 L1 L2 S ⊓ N ≤ L :=
    inf_le_lower_of_noncentral hXH hstep hnc hZX hZH hZcentral
  have hZL' : N ⊓ Z1 L1 L2 S ≤ L := by rw [inf_comm]; exact hZL
  obtain ⟨hE, hNat⟩ :=
    str86_X1_chiefFactor_natural hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
      hX1Q1 hstep hnc hZL
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  have hMcardChief : Nat.card (Ch3z.chiefMod L N) = (2 ^ k) ^ 6 :=
    card_of_binaryNaturalSU3 hNat
  have hLN : L ≤ N := hstep.2.2.1.le
  have hNXle : N ≤ u3X1 L1 L2 S := hNleX
  have hNH : N ≤ L1 ⊔ S := hNXle.trans hXH
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hNH.trans hHL
  have hsecBot : secImg (Subgroup.normalizer (L : Set G)) L L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hb
  have hcardChief : Nat.card (Ch3z.chiefMod L N) = L.relIndex N := by
    have hrel := relIndex_secImg (A := Subgroup.normalizer (L : Set G)) (B := L)
      (T := L) (H := N) le_rfl hLN hNL
    rw [hsecBot, Subgroup.relIndex_bot_left] at hrel
    exact hrel
  have hNZn : N ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := hNH.trans hZH
  have hsubEq : (N ⊓ Z1 L1 L2 S).subgroupOf N = (Z1 L1 L2 S).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨x.2, h⟩
  have hrelNZ : (N ⊓ Z1 L1 L2 S).relIndex N = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := by
    haveI : ((Z1 L1 L2 S).subgroupOf N).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNZn
    haveI : ((Z1 L1 L2 S).subgroupOf (N ⊔ Z1 L1 L2 S)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hNZn Subgroup.le_normalizer)
    have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient N (Z1 L1 L2 S) hNZn
    have hcard := Nat.card_congr (MulEquiv.toEquiv hiso)
    rw [Subgroup.relIndex, Subgroup.relIndex, hsubEq]
    exact hcard
  have hsupX : N ⊔ Z1 L1 L2 S ≤ u3X1 L1 L2 S := sup_le hNXle hZX
  have hrelMon : (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_right hsupX (D15Proof.relIndex_ne_zero _ _)
  have hub := str86_X1_upper_bound hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1
  have hq6 : Nat.card (u3M L1 L2 S) = (2 ^ k) ^ 6 := by
    have hge : (2 ^ k) ^ 6 ≤ Nat.card (u3M L1 L2 S) := by
      calc (2 ^ k) ^ 6 = Nat.card (Ch3z.chiefMod L N) := hMcardChief.symm
        _ = L.relIndex N := hcardChief
        _ ≤ (N ⊓ Z1 L1 L2 S).relIndex N :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
              (Subgroup.relIndex_dvd_of_le_left N hZL')
        _ = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := hrelNZ
        _ ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := hrelMon
        _ = Nat.card (u3M L1 L2 S) := rfl
    exact le_antisymm hub hge
  have h1' : L.relIndex N = (2 ^ k) ^ 6 := by rw [← hcardChief, hMcardChief]
  have h3' : (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = (2 ^ k) ^ 6 := by
    rw [show (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = Nat.card (u3M L1 L2 S) from rfl, hq6]
  have hEq13 : L.relIndex N = (N ⊓ Z1 L1 L2 S).relIndex N := by
    have hle : L.relIndex N ≤ (N ⊓ Z1 L1 L2 S).relIndex N :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
        (Subgroup.relIndex_dvd_of_le_left N hZL')
    refine le_antisymm hle ?_
    calc (N ⊓ Z1 L1 L2 S).relIndex N = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := hrelNZ
      _ ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := hrelMon
      _ = (2 ^ k) ^ 6 := h3'
      _ = L.relIndex N := h1'.symm
  have hLeq : N ⊓ Z1 L1 L2 S = L := by
    have h := Subgroup.relIndex_mul_relIndex (N ⊓ Z1 L1 L2 S) L N hZL' hLN
    rw [← hEq13] at h
    have hpos : 0 < L.relIndex N := Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    have hone : (N ⊓ Z1 L1 L2 S).relIndex L = 1 := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [one_mul]
      exact h
    exact le_antisymm hZL' (Subgroup.relIndex_eq_one.mp hone)
  have hXeq : N ⊔ Z1 L1 L2 S = u3X1 L1 L2 S := by
    have h34 : (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) =
        (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := by
      rw [← hrelNZ, ← hEq13, h1', h3']
    have h := Subgroup.relIndex_mul_relIndex (Z1 L1 L2 S) (N ⊔ Z1 L1 L2 S)
      (u3X1 L1 L2 S) le_sup_right hsupX
    rw [h34] at h
    have hpos : 0 < (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
      Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    have hone : (N ⊔ Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [mul_one]
      exact h
    exact le_antisymm hsupX (Subgroup.relIndex_eq_one.mp hone)
  have hcommNZ : ∀ n ∈ N, ∀ z ∈ Z1 L1 L2 S, n * z = z * n := fun n hn z hz =>
    hZcentral n (hNH hn) z hz
  have hHN' : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) := hLS ▸ hHN
  have hHZ' : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := hLS ▸ hZH
  have hHX' : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    hLS ▸ le_normalizer_u3X1_sup hF
  haveI : ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal := u3M_normal L1 L2 S
  obtain ⟨j, hj, hrange, hrange'⟩ :=
    exists_chiefModEquiv (H := L1 ⊔ Q1 L1 L2 S) (L := L) (N := N)
      (Z := Z1 L1 L2 S) (X := u3X1 L1 L2 S) hcommNZ hNXle hZX hLeq hXeq
      hNL hHN' hHZ' hHX'
  have hNat' : BinaryNaturalSU3 (Ch3z.chiefAut (L1 ⊔ Q1 L1 L2 S) L N) ⊤ ⊥ k := by
    rw [← hLS]
    exact hNat
  letI : CommGroup (u3M L1 L2 S) := u3MCommGroup hX1'
  have hbin : BinaryNaturalSU3
      (u3MAct (L1 := L1) (L2 := L2) (S := S) (hX := hHX') (hZ := hHZ')).range ⊤ ⊥ k := by
    obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ := hNat'
    exact ⟨K, hKfield, hKfin, hKcard,
      CFSG.Quasithin.B45Mat.M12.realizes_of_map_congrHom j.symm hrange' hreal⟩
  unfold Str86X1Natural
  exact ⟨hq6, hbin⟩

end CFSG.Quasithin.Stroth

end
